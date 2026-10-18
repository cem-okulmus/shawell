package main

import (
	"fmt"
	"math/rand"
	"sort"
	"strings"
	"testing"

	rdf "github.com/cem-okulmus/rdf2go-1"
)

// The tests in this file check SHACL property paths: shawell parses a path from the shapes graph
// (ExtractPropertyPath), turns it into SPARQL (PropertyString) to find value nodes, and back into
// RDF (PropertyRDF) for sh:resultPath in reports. The SPARQL form is compared with an independent
// evaluation of the path over the data graph, for many nested path expressions.

const pathNS = "http://example.org/path#"

// pathExpr is a SHACL property path, built independently of shawell's own representation.
type pathExpr struct {
	kind string // "pred", "inv", "seq", "alt", "star", "plus", "opt"
	pred string
	subs []pathExpr
}

func pPred(p string) pathExpr                 { return pathExpr{kind: "pred", pred: p} }
func pInv(e pathExpr) pathExpr                { return pathExpr{kind: "inv", subs: []pathExpr{e}} }
func pSeq(es ...pathExpr) pathExpr            { return pathExpr{kind: "seq", subs: es} }
func pAlt(es ...pathExpr) pathExpr            { return pathExpr{kind: "alt", subs: es} }
func pUnary(kind string, e pathExpr) pathExpr { return pathExpr{kind: kind, subs: []pathExpr{e}} }

func (e pathExpr) String() string {
	var subs []string
	for _, s := range e.subs {
		subs = append(subs, s.String())
	}
	switch e.kind {
	case "pred":
		return e.pred
	case "inv":
		return "inv(" + subs[0] + ")"
	case "seq":
		return "seq(" + strings.Join(subs, ",") + ")"
	case "alt":
		return "alt(" + strings.Join(subs, ",") + ")"
	default:
		return e.kind + "(" + subs[0] + ")"
	}
}

// turtle renders the path in SHACL's RDF syntax.
func (e pathExpr) turtle() string {
	var subs []string
	for _, s := range e.subs {
		subs = append(subs, s.turtle())
	}
	switch e.kind {
	case "pred":
		return "<" + pathNS + e.pred + ">"
	case "inv":
		return "[ sh:inversePath " + subs[0] + " ]"
	case "seq":
		return "( " + strings.Join(subs, " ") + " )"
	case "alt":
		return "[ sh:alternativePath ( " + strings.Join(subs, " ") + " ) ]"
	case "star":
		return "[ sh:zeroOrMorePath " + subs[0] + " ]"
	case "plus":
		return "[ sh:oneOrMorePath " + subs[0] + " ]"
	case "opt":
		return "[ sh:zeroOrOnePath " + subs[0] + " ]"
	}
	panic("unknown path kind " + e.kind)
}

type pair struct{ s, o string }

type relation map[pair]bool

// eval computes the pairs connected by the path, following the SPARQL 1.1 property path semantics.
// nodes are all nodes of the data graph, which zero-length paths connect to themselves.
func (e pathExpr) eval(edges map[string]relation, nodes []string) relation {
	out := make(relation)
	switch e.kind {
	case "pred":
		for p := range edges[e.pred] {
			out[p] = true
		}
	case "inv":
		for p := range e.subs[0].eval(edges, nodes) {
			out[pair{p.o, p.s}] = true
		}
	case "seq":
		out = e.subs[0].eval(edges, nodes)
		for _, sub := range e.subs[1:] {
			next := sub.eval(edges, nodes)
			composed := make(relation)
			for a := range out {
				for b := range next {
					if a.o == b.s {
						composed[pair{a.s, b.o}] = true
					}
				}
			}
			out = composed
		}
	case "alt":
		for _, sub := range e.subs {
			for p := range sub.eval(edges, nodes) {
				out[p] = true
			}
		}
	case "star", "plus", "opt":
		base := e.subs[0].eval(edges, nodes)
		for p := range base {
			out[p] = true
		}
		if e.kind != "opt" { // transitive closure
			for changed := true; changed; {
				changed = false
				for a := range out {
					for b := range base {
						if a.o == b.s && !out[pair{a.s, b.o}] {
							out[pair{a.s, b.o}] = true
							changed = true
						}
					}
				}
			}
		}
		if e.kind != "plus" { // zero-length paths
			for _, n := range nodes {
				out[pair{n, n}] = true
			}
		}
	}
	return out
}

// testPaths returns nested path expressions over the predicates p and q: every unary operator
// applied to every binary combination and vice versa, plus nested unary operators. These cover
// the cases where the SPARQL rendering needs parentheses to keep its meaning.
func testPaths() []pathExpr {
	p, q := pPred("p"), pPred("q")
	unaries := []string{"inv", "star", "plus", "opt"}
	mkUnary := func(kind string, e pathExpr) pathExpr {
		if kind == "inv" {
			return pInv(e)
		}
		return pUnary(kind, e)
	}
	binaries := []func(...pathExpr) pathExpr{pSeq, pAlt}

	paths := []pathExpr{p, pSeq(p, q), pAlt(p, q), pSeq(p, q, p)}
	for _, u := range unaries {
		paths = append(paths, mkUnary(u, p))
		for _, b := range binaries {
			paths = append(paths, mkUnary(u, b(p, q))) // e.g. ^(p/q), (p|q)*
			paths = append(paths, b(mkUnary(u, p), q)) // e.g. ^p/q, p*|q
			paths = append(paths, b(q, mkUnary(u, p))) // e.g. q/^p, q|p+
		}
		for _, u2 := range unaries {
			paths = append(paths, mkUnary(u, mkUnary(u2, p))) // e.g. ^(p*), (^p)+
		}
	}
	for _, b := range binaries {
		for _, b2 := range binaries {
			paths = append(paths, b(b2(p, q), p)) // e.g. (p|q)/p, (p/q)|p
			paths = append(paths, b(p, b2(q, p)))
		}
	}
	return paths
}

// parsePath parses a path given in SHACL's RDF syntax with shawell's ExtractPropertyPath.
func parsePath(t *testing.T, pathTurtle string) PropertyPath {
	t.Helper()
	g := rdf.NewGraph("")
	doc := "@prefix sh: <http://www.w3.org/ns/shacl#> .\n<urn:shape> sh:path " + pathTurtle + " ."
	if err := g.Parse(strings.NewReader(doc), "text/turtle"); err != nil {
		t.Fatalf("parsing path %s: %v", pathTurtle, err)
	}
	triple := g.One(rdf.NewResource("urn:shape"), rdf.NewResource(_sh+"path"), nil)
	path, err := ExtractPropertyPath(g, triple.Object)
	if err != nil {
		t.Fatalf("ExtractPropertyPath(%s): %v", pathTurtle, err)
	}
	if path == nil {
		t.Fatalf("ExtractPropertyPath(%s) returned no path", pathTurtle)
	}
	return path
}

// pathTestGraph builds a data graph over n0..n4 with random p and q edges, plus a p-cycle so that
// the closure operators have something to do.
func pathTestGraph(seed int64) (*rdf.Graph, map[string]relation, []string) {
	r := rand.New(rand.NewSource(seed))
	g := rdf.NewGraph("")
	edges := map[string]relation{"p": {}, "q": {}}
	nodeSet := make(map[string]bool)
	add := func(s, p, o int) {
		pred := []string{"p", "q"}[p]
		sIRI, oIRI := fmt.Sprintf("%sn%d", pathNS, s), fmt.Sprintf("%sn%d", pathNS, o)
		g.AddTriple(rdf.NewResource(sIRI), rdf.NewResource(pathNS+pred), rdf.NewResource(oIRI))
		edges[pred][pair{sIRI, oIRI}] = true
		nodeSet[sIRI], nodeSet[oIRI] = true, true
	}
	add(0, 0, 1)
	add(1, 0, 2)
	add(2, 0, 0)
	for i := 0; i < 8; i++ {
		add(r.Intn(5), r.Intn(2), r.Intn(5))
	}
	var nodes []string
	for n := range nodeSet {
		nodes = append(nodes, n)
	}
	return g, edges, nodes
}

func describePairs(rel relation) string {
	var out []string
	for p := range rel {
		out = append(out, strings.TrimPrefix(p.s, pathNS)+"→"+strings.TrimPrefix(p.o, pathNS))
	}
	sort.Strings(out)
	return "{" + strings.Join(out, " ") + "}"
}

// TestPropertyPathSparql checks that the SPARQL path shawell generates for each path expression
// connects exactly the node pairs that the path semantics demands.
func TestPropertyPathSparql(t *testing.T) {
	ep, cleanup, err := StartOxigraph(false)
	if err != nil {
		t.Skip("oxigraph not available:", err)
	}
	defer cleanup()

	for _, seed := range []int64{1, 2, 3} {
		g, edges, nodes := pathTestGraph(seed)
		graphName := fmt.Sprintf("<urn:path-test-%d>", seed)
		if err := ep.Insert(g, graphName, false); err != nil {
			t.Fatal(err)
		}

		for _, e := range testPaths() {
			t.Run(fmt.Sprintf("seed%d/%s", seed, e), func(t *testing.T) {
				path := parsePath(t, e.turtle())
				query := fmt.Sprintf("SELECT ?s ?o WHERE { GRAPH %s { ?s %s ?o } }", graphName, path.PropertyString())

				got := make(relation)
				var queryErr any
				func() {
					defer func() { queryErr = recover() }()
					for row := range ep.QueryString(query).IterRows() {
						got[pair{row[0].RawValue(), row[1].RawValue()}] = true
					}
				}()
				if queryErr != nil {
					t.Fatalf("query failed for SPARQL path %q: %v", path.PropertyString(), queryErr)
				}

				expected := e.eval(edges, nodes)
				if fmt.Sprint(describePairs(got)) != describePairs(expected) {
					t.Errorf("SPARQL path %q\n\tgot      %s\n\texpected %s", path.PropertyString(),
						describePairs(got), describePairs(expected))
				}
			})
		}
		_ = ep.ClearGraph(graphName)
	}
}

// TestPropertyPathRDFRoundTrip checks that the RDF form used for sh:resultPath in reports is valid
// SHACL path syntax that describes the same path: parsing it again must give the same path.
func TestPropertyPathRDFRoundTrip(t *testing.T) {
	for _, e := range testPaths() {
		t.Run(e.String(), func(t *testing.T) {
			defer func() {
				if r := recover(); r != nil {
					t.Errorf("panic: %v", r)
				}
			}()
			path := parsePath(t, e.turtle())
			again := parsePath(t, path.PropertyRDF())
			if again.PropertyRDF() != path.PropertyRDF() {
				t.Errorf("round trip changed the path:\n\tfirst  %s\n\tsecond %s", path.PropertyRDF(), again.PropertyRDF())
			}
			if !rdfTurtleIsomorphic(
				"@prefix sh: <http://www.w3.org/ns/shacl#> . <urn:s> sh:path "+e.turtle()+" .",
				"<urn:s> <"+_sh+"path> "+path.PropertyRDF()+" .") {
				t.Errorf("PropertyRDF %s does not describe the original path %s", path.PropertyRDF(), e.turtle())
			}
		})
	}
}
