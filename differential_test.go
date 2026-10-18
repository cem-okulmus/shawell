package main

import (
	"fmt"
	"math/rand"
	"os"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"testing"

	rdf "github.com/cem-okulmus/rdf2go-1"
)

// Differential tests: random small SHACL documents with their data graphs are validated by shawell,
// once by unwinding and once through the logic program, and compared per target node with an
// independent reference implementation of the SHACL semantics (fzRef below). The validation report
// is checked too: it must agree with the verdict and be valid Turtle.
//
// The documents are non-recursive (shape i only references shapes j > i), so the reference
// semantics is unambiguous. They combine the logical constraints, property shapes with inverse
// paths, min/max counts, nested property shapes and qualified value shapes (also disjoint), as well
// as value type, value range, string, property pair and closedness constraints. The data contains
// IRIs, blank nodes and literals; blank nodes and literals are reached as value nodes but never
// targeted. Set SHAWELL_FUZZ=<n> to run more documents than the default.

const fzNS = "http://example.org/fuzz#"

var (
	fzIRINodes   = []string{"n0", "n1", "n2", "n3"}
	fzBlankNodes = []string{"b0", "b1"}
	fzLiterals   = []string{"la", "lb", "lc", "l5", "l7", "s5"}
	fzClasses    = []string{"A", "B"}
	fzPreds      = []string{"p", "q"}
)

// literal values: lexical form, language, datatype
var fzLiteralValue = map[string][3]string{
	"la": {"a", "", _xsd + "string"},
	"lb": {"b", "en", _rdf + "langString"},
	"lc": {"c", "en", _rdf + "langString"},
	"l5": {"5", "", _xsd + "integer"},
	"l7": {"7", "", _xsd + "integer"},
	"s5": {"5", "", _xsd + "string"}, // a string that casts to a valid integer
}

type fzCons struct {
	kind  string // see fzGenCons
	class string
	value string   // hasValue
	list  []string // in, languageIn
	refs  []int    // node, not, and, or, xone: indices of named shapes
	str   string   // nodeKind, datatype, pattern
	num   int      // value ranges, lengths
	pred  string   // equals, disjoint
	flag  bool     // closed: ignore rdf:type
	prop  *fzProp
}

type fzProp struct {
	pred               string
	inverse            bool
	minCount, maxCount int // -1: absent
	cons               []fzCons
	qual               *fzQual
}

type fzQual struct {
	ref, min, max int // max -1: absent
	disjoint      bool
}

type fzShape struct {
	cons        []fzCons
	targetNodes []string
	targetClass string
}

type fzDoc struct {
	shapes []fzShape
	edges  map[string][][2]string // predicate -> (subject, object)
	types  map[string][]string    // node -> classes
}

func fzShapeName(i int) string { return fmt.Sprint("S", i) }

func fzTerm(n string) string {
	if strings.HasPrefix(n, "b") {
		return "_:" + n
	}
	if v, ok := fzLiteralValue[n]; ok {
		switch {
		case v[1] != "":
			return fmt.Sprintf("%q@%s", v[0], v[1])
		case v[2] == _xsd+"string":
			return fmt.Sprintf("%q", v[0])
		default:
			return fmt.Sprintf("%q^^<%s>", v[0], v[2])
		}
	}
	return "<" + fzNS + n + ">"
}

// generation

// constraint kinds that SHACL allows at most once per shape
var fzUniqueKinds = map[string]bool{
	"in": true, "nodeKind": true, "datatype": true, "minInclusive": true, "maxExclusive": true,
	"minLength": true, "maxLength": true, "languageIn": true, "uniqueLang": true, "closed": true,
}

func fzGenDoc(r *rand.Rand) fzDoc {
	doc := fzDoc{edges: map[string][][2]string{}, types: map[string][]string{}}
	subjects := append(append([]string{}, fzIRINodes...), fzBlankNodes...)
	objects := append(append([]string{}, subjects...), fzLiterals...)
	for _, p := range fzPreds {
		for _, s := range subjects {
			for _, o := range objects {
				if r.Float64() < 0.17 {
					doc.edges[p] = append(doc.edges[p], [2]string{s, o})
				}
			}
		}
	}
	for _, n := range fzIRINodes { // blank nodes stay untyped, so that they are never targets
		for _, c := range fzClasses {
			if r.Float64() < 0.4 {
				doc.types[n] = append(doc.types[n], c)
			}
		}
	}

	const numShapes = 3
	for i := 0; i < numShapes; i++ {
		var s fzShape
		n := 1 + r.Intn(3)
		for k := 0; k < n; k++ {
			s.cons = append(s.cons, fzGenCons(r, i, numShapes, 2, s.cons, false))
		}
		if r.Float64() < 0.15 {
			s.cons = append(s.cons, fzCons{kind: "closed", flag: r.Float64() < 0.6})
		}
		if i == 0 {
			s.targetNodes = append(s.targetNodes, fzIRINodes...)
		} else if r.Float64() < 0.3 {
			s.targetNodes = append(s.targetNodes, fzIRINodes[r.Intn(len(fzIRINodes))])
		}
		if r.Float64() < 0.25 {
			s.targetClass = fzClasses[r.Intn(len(fzClasses))]
		}
		doc.shapes = append(doc.shapes, s)
	}
	return doc
}

func fzRefs(r *rand.Rand, self, numShapes, n int) []int {
	var out []int
	for k := 0; k < n; k++ {
		out = append(out, self+1+r.Intn(numShapes-self-1))
	}
	return out
}

func fzSubset(r *rand.Rand, from []string) []string {
	var out []string
	for _, n := range from {
		if r.Float64() < 0.4 {
			out = append(out, n)
		}
	}
	if len(out) == 0 {
		out = append(out, from[r.Intn(len(from))])
	}
	return out
}

func pick[T any](r *rand.Rand, xs ...T) T { return xs[r.Intn(len(xs))] }

// fzGenCons generates a constraint for (the shape or property shape inside) shape self. siblings are
// the constraints generated so far for the same shape: they keep the kinds that SHACL allows only
// once unique, and the qualified value shapes of sibling property shapes distinct.
func fzGenCons(r *rand.Rand, self, numShapes, depth int, siblings []fzCons, inProperty bool) fzCons {
	kinds := []string{"class", "hasValue", "property", "property", "in", "nodeKind", "datatype",
		"minInclusive", "maxExclusive", "minLength", "maxLength", "pattern", "languageIn"}
	if inProperty {
		kinds = append(kinds, "uniqueLang", "equals", "disjoint")
	}
	if self < numShapes-1 {
		kinds = append(kinds, "node", "not", "and", "or", "xone", "or")
	}
	var allowed []string
	for _, k := range kinds {
		if (fzUniqueKinds[k] && fzHasKind(siblings, k)) || (k == "property" && depth == 0) {
			continue
		}
		allowed = append(allowed, k)
	}
	values := append(append([]string{}, fzIRINodes...), fzLiterals...)

	switch kind := pick(r, allowed...); kind {
	case "class":
		return fzCons{kind: kind, class: pick(r, fzClasses...)}
	case "hasValue":
		return fzCons{kind: kind, value: pick(r, values...)}
	case "in":
		return fzCons{kind: kind, list: fzSubset(r, values)}
	case "node", "not":
		return fzCons{kind: kind, refs: fzRefs(r, self, numShapes, 1)}
	case "and", "or", "xone":
		return fzCons{kind: kind, refs: fzRefs(r, self, numShapes, 1+r.Intn(3))}
	case "nodeKind":
		return fzCons{kind: kind, str: pick(r, "IRI", "BlankNode", "Literal", "BlankNodeOrIRI", "IRIOrLiteral", "BlankNodeOrLiteral")}
	case "datatype":
		return fzCons{kind: kind, str: pick(r, _xsd+"string", _xsd+"integer", _rdf+"langString")}
	case "minInclusive", "maxExclusive":
		return fzCons{kind: kind, num: 4 + r.Intn(5)}
	case "minLength", "maxLength":
		return fzCons{kind: kind, num: pick(r, 0, 1, 2, 30)}
	case "pattern":
		return fzCons{kind: kind, str: pick(r, "^a$", "n1$", "^[57]$", "[bc]")}
	case "languageIn":
		return fzCons{kind: kind, list: []string{pick(r, "en", "de")}}
	case "uniqueLang":
		return fzCons{kind: kind}
	case "equals", "disjoint":
		return fzCons{kind: kind, pred: pick(r, fzPreds...)}
	default:
		return fzCons{kind: "property", prop: fzGenProp(r, self, numShapes, depth-1, siblings)}
	}
}

func fzGenProp(r *rand.Rand, self, numShapes, depth int, siblings []fzCons) *fzProp {
	p := &fzProp{pred: pick(r, fzPreds...), inverse: r.Float64() < 0.2, minCount: -1, maxCount: -1}
	if r.Float64() < 0.4 {
		p.minCount = r.Intn(3)
	}
	if r.Float64() < 0.4 {
		p.maxCount = max(p.minCount, 0) + r.Intn(2)
	}
	n := r.Intn(3)
	for k := 0; k < n; k++ {
		p.cons = append(p.cons, fzGenCons(r, self, numShapes, depth, p.cons, true))
	}
	if self < numShapes-1 && r.Float64() < 0.35 {
		used := make(map[int]bool)
		for _, s := range siblings {
			if s.kind == "property" && s.prop.qual != nil {
				used[s.prop.qual.ref] = true
			}
		}
		ref := fzRefs(r, self, numShapes, 1)[0]
		if !used[ref] {
			q := &fzQual{ref: ref, min: r.Intn(3), max: -1, disjoint: r.Float64() < 0.5}
			if r.Float64() < 0.5 {
				q.max = q.min + r.Intn(2)
			}
			p.qual = q
		}
	}
	return p
}

func fzHasKind(cons []fzCons, kind string) bool {
	for _, c := range cons {
		if c.kind == kind {
			return true
		}
	}
	return false
}

// Turtle rendering

func (d fzDoc) turtle() string {
	var sb strings.Builder
	sb.WriteString("@prefix sh: <http://www.w3.org/ns/shacl#> .\n")
	sb.WriteString("@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .\n")
	sb.WriteString("@prefix ex: <" + fzNS + "> .\n\n")

	for i, s := range d.shapes {
		sb.WriteString(fmt.Sprintf("ex:%s a sh:NodeShape", fzShapeName(i)))
		for _, t := range s.targetNodes {
			sb.WriteString(" ;\n  sh:targetNode ")
			sb.WriteString(fzTerm(t))
		}
		if s.targetClass != "" {
			sb.WriteString(" ;\n  sh:targetClass ex:")
			sb.WriteString(s.targetClass)
		}
		for _, c := range s.cons {
			sb.WriteString(" ;\n  ")
			sb.WriteString(c.turtle("  "))
		}
		sb.WriteString(" .\n")
	}
	sb.WriteString("\n")
	for _, p := range fzPreds {
		for _, e := range d.edges[p] {
			sb.WriteString(fmt.Sprintf("%s ex:%s %s .\n", fzTerm(e[0]), p, fzTerm(e[1])))
		}
	}
	for _, n := range fzIRINodes {
		for _, c := range d.types[n] {
			sb.WriteString(fmt.Sprintf("%s rdf:type ex:%s .\n", fzTerm(n), c))
		}
	}
	return sb.String()
}

func (c fzCons) turtle(indent string) string {
	var refs []string
	for _, r := range c.refs {
		refs = append(refs, "ex:"+fzShapeName(r))
	}
	switch c.kind {
	case "class":
		return "sh:class ex:" + c.class
	case "hasValue":
		return "sh:hasValue " + fzTerm(c.value)
	case "in":
		var items []string
		for _, n := range c.list {
			items = append(items, fzTerm(n))
		}
		return "sh:in ( " + strings.Join(items, " ") + " )"
	case "node", "not":
		return "sh:" + c.kind + " " + refs[0]
	case "and", "or", "xone":
		return "sh:" + c.kind + " ( " + strings.Join(refs, " ") + " )"
	case "nodeKind":
		return "sh:nodeKind sh:" + c.str
	case "datatype":
		return "sh:datatype <" + c.str + ">"
	case "minInclusive", "maxExclusive", "minLength", "maxLength":
		return "sh:" + c.kind + " " + strconv.Itoa(c.num)
	case "pattern":
		return "sh:pattern " + strconv.Quote(c.str)
	case "languageIn":
		return "sh:languageIn ( " + strconv.Quote(c.list[0]) + " )"
	case "uniqueLang":
		return "sh:uniqueLang true"
	case "equals", "disjoint":
		return "sh:" + c.kind + " ex:" + c.pred
	case "closed":
		out := "sh:closed true"
		if c.flag {
			out += " ;\n" + indent + "sh:ignoredProperties ( rdf:type )"
		}
		return out
	}
	p := c.prop
	inner := indent + "  "
	path := "ex:" + p.pred
	if p.inverse {
		path = "[ sh:inversePath ex:" + p.pred + " ]"
	}
	parts := []string{"sh:path " + path}
	if p.minCount >= 0 {
		parts = append(parts, "sh:minCount "+strconv.Itoa(p.minCount))
	}
	if p.maxCount >= 0 {
		parts = append(parts, "sh:maxCount "+strconv.Itoa(p.maxCount))
	}
	if q := p.qual; q != nil {
		parts = append(parts, "sh:qualifiedValueShape ex:"+fzShapeName(q.ref), "sh:qualifiedMinCount "+strconv.Itoa(q.min))
		if q.max >= 0 {
			parts = append(parts, "sh:qualifiedMaxCount "+strconv.Itoa(q.max))
		}
		if q.disjoint {
			parts = append(parts, "sh:qualifiedValueShapesDisjoint true")
		}
	}
	for _, sub := range p.cons {
		parts = append(parts, sub.turtle(inner))
	}
	return "sh:property [\n" + inner + strings.Join(parts, " ;\n"+inner) + "\n" + indent + "]"
}

// reference semantics

type fzRef struct {
	doc  fzDoc
	memo map[string]bool
}

func (r *fzRef) values(focus string, pred string, inverse bool) []string {
	seen := make(map[string]bool)
	var out []string
	for _, e := range r.doc.edges[pred] {
		from, to := e[0], e[1]
		if inverse {
			from, to = to, from
		}
		if from == focus && !seen[to] {
			seen[to] = true
			out = append(out, to)
		}
	}
	return out
}

func (r *fzRef) hasType(n, class string) bool {
	for _, c := range r.doc.types[n] {
		if c == class {
			return true
		}
	}
	return false
}

func fzIsLiteral(n string) bool { _, ok := fzLiteralValue[n]; return ok }
func fzIsBlank(n string) bool   { return strings.HasPrefix(n, "b") }

// fzStr is the SPARQL str() of a node; blank nodes have none.
func fzStr(n string) (string, bool) {
	switch {
	case fzIsBlank(n):
		return "", false
	case fzIsLiteral(n):
		return fzLiteralValue[n][0], true
	}
	return fzNS + n, true
}

func fzNumber(n string) (int, bool) {
	if v, ok := fzLiteralValue[n]; ok && v[2] == _xsd+"integer" {
		i, _ := strconv.Atoi(v[0])
		return i, true
	}
	return 0, false
}

func (r *fzRef) conforms(focus string, shape int) bool {
	key := fmt.Sprint(focus, "@", shape)
	if v, ok := r.memo[key]; ok {
		return v
	}
	v := r.allHold(focus, r.doc.shapes[shape].cons)
	r.memo[key] = v
	return v
}

// allHold checks the constraints of a shape (whose constraints are cons) for one focus node.
func (r *fzRef) allHold(focus string, cons []fzCons) bool {
	for _, c := range cons {
		if !r.holds(focus, c, cons) {
			return false
		}
	}
	return true
}

// holds checks one constraint for a focus node; for constraints of a property shape it is called
// for each value node. parentCons are the constraints of the same shape.
func (r *fzRef) holds(n string, c fzCons, parentCons []fzCons) bool {
	switch c.kind {
	case "class":
		return r.hasType(n, c.class)
	case "hasValue":
		return n == c.value
	case "in":
		for _, m := range c.list {
			if m == n {
				return true
			}
		}
		return false
	case "node":
		return r.conforms(n, c.refs[0])
	case "not":
		return !r.conforms(n, c.refs[0])
	case "and", "or", "xone":
		count := 0
		for _, ref := range c.refs {
			if r.conforms(n, ref) {
				count++
			}
		}
		switch c.kind {
		case "and":
			return count == len(c.refs)
		case "or":
			return count > 0
		default:
			return count == 1
		}
	case "nodeKind":
		kind := "IRI"
		if fzIsBlank(n) {
			kind = "BlankNode"
		} else if fzIsLiteral(n) {
			kind = "Literal"
		}
		return strings.Contains(c.str, kind)
	case "datatype":
		v, ok := fzLiteralValue[n]
		return ok && v[2] == c.str
	case "minInclusive", "maxExclusive":
		num, ok := fzNumber(n)
		if c.kind == "minInclusive" {
			return ok && num >= c.num
		}
		return ok && num < c.num
	case "minLength", "maxLength", "pattern":
		s, ok := fzStr(n)
		switch {
		case !ok:
			return false
		case c.kind == "minLength":
			return len(s) >= c.num
		case c.kind == "maxLength":
			return len(s) <= c.num
		}
		return regexp.MustCompile(c.str).MatchString(s)
	case "languageIn":
		v, ok := fzLiteralValue[n]
		return ok && v[1] == c.list[0]
	case "closed":
		allowed := map[string]bool{}
		for _, s := range parentCons {
			if s.kind == "property" && !s.prop.inverse {
				allowed[s.prop.pred] = true
			}
		}
		if len(r.doc.types[n]) > 0 && !c.flag {
			return false // rdf:type is a property too, unless ignored
		}
		for _, p := range fzPreds {
			if !allowed[p] && len(r.values(n, p, false)) > 0 {
				return false
			}
		}
		return true
	}
	return r.propertyHolds(n, c.prop, parentCons)
}

// propertyHolds checks a property shape for a focus node. parentCons are the constraints of the
// shape that has this property shape, whose other qualified value shapes are the siblings.
func (r *fzRef) propertyHolds(focus string, p *fzProp, parentCons []fzCons) bool {
	vals := r.values(focus, p.pred, p.inverse)
	if p.minCount >= 0 && len(vals) < p.minCount {
		return false
	}
	if p.maxCount >= 0 && len(vals) > p.maxCount {
		return false
	}
	for _, c := range p.cons {
		switch c.kind {
		case "hasValue": // at least one value node is the given value
			found := false
			for _, v := range vals {
				found = found || v == c.value
			}
			if !found {
				return false
			}
		case "uniqueLang": // no two value nodes share a language tag
			seen := map[string]bool{}
			for _, v := range vals {
				if lang := fzLiteralValue[v][1]; lang != "" {
					if seen[lang] {
						return false
					}
					seen[lang] = true
				}
			}
		case "equals", "disjoint":
			other := map[string]bool{}
			for _, v := range r.values(focus, c.pred, false) {
				other[v] = true
			}
			common := 0
			for _, v := range vals {
				if other[v] {
					common++
				}
			}
			if c.kind == "disjoint" && common > 0 {
				return false
			}
			if c.kind == "equals" && (common != len(vals) || common != len(other)) {
				return false
			}
		default: // every value node satisfies the constraint
			for _, v := range vals {
				if !r.holds(v, c, p.cons) {
					return false
				}
			}
		}
	}
	if q := p.qual; q != nil {
		var siblings []int
		if q.disjoint {
			for _, s := range parentCons {
				if s.kind == "property" && s.prop != p && s.prop.qual != nil && s.prop.qual.ref != q.ref {
					siblings = append(siblings, s.prop.qual.ref)
				}
			}
		}
		count := 0
		for _, v := range vals {
			if !r.conforms(v, q.ref) {
				continue
			}
			inSibling := false
			for _, s := range siblings {
				inSibling = inSibling || r.conforms(v, s)
			}
			if !inSibling {
				count++
			}
		}
		if count < q.min || (q.max >= 0 && count > q.max) {
			return false
		}
	}
	return true
}

// expectedInvalid returns, for each shape with targets, its targets that do not conform.
func (d fzDoc) expectedInvalid() map[string]map[string]bool {
	ref := &fzRef{doc: d, memo: map[string]bool{}}
	out := make(map[string]map[string]bool)
	for i, s := range d.shapes {
		targets := map[string]bool{}
		for _, t := range s.targetNodes {
			targets[t] = true
		}
		if s.targetClass != "" {
			for _, n := range fzIRINodes {
				if ref.hasType(n, s.targetClass) {
					targets[n] = true
				}
			}
		}
		for t := range targets {
			if !ref.conforms(t, i) {
				if out[fzShapeName(i)] == nil {
					out[fzShapeName(i)] = map[string]bool{}
				}
				out[fzShapeName(i)][t] = true
			}
		}
	}
	return out
}

// running shawell

// shawellInvalid validates the document loaded into graphName the same way answerShacl does, and
// returns the verdict and the invalid targets per shape (by local name). A panic is returned as err.
func shawellInvalid(g *rdf.Graph, ep *SparqlEndpoint, graphName string, forceLP bool) (res bool, invalid map[string]map[string]bool, err any) {
	defer func() { err = recover() }()

	renameMap = make(map[rdf.Term]string)
	reverseMap = make(map[string]rdf.Term)
	doc := GetShaclDocument(g, graphName, false)
	activeDoc = &doc
	doc.AllCondAnswers(ep)

	var tables map[string]Table[rdf.Term]
	if forceLP || doc.IsRecursive() {
		lp := doc.GetAllLPs()
		lpTables, undefined := lp.Answer(false, false)
		if err := doc.AdoptLPAnswers(lpTables); err != nil {
			panic(err)
		}
		doc.AdoptLPUndefinedAnswers(undefined)
		res, tables = doc.ValidateLP(ep)
	} else {
		res, tables = doc.Validate(ep)
	}

	invalid = make(map[string]map[string]bool)
	for shape, table := range tables {
		name := strings.TrimPrefix(shape, fzNS)
		for row := range table.IterRows() {
			if invalid[name] == nil {
				invalid[name] = map[string]bool{}
			}
			invalid[name][strings.TrimPrefix(row[0].RawValue(), fzNS)] = true
		}
	}
	return res, invalid, nil
}

// shawellReport runs the full pipeline including the validation report, which also checks that
// the report agrees with the verdict.
func shawellReport(g *rdf.Graph, ep *SparqlEndpoint, graphName string, forceLP bool) (report *ValidationReport, err any) {
	defer func() { err = recover() }()
	doc := GetShaclDocument(g, graphName, false)
	activeDoc = &doc
	return answerShacl(ep, doc, config{silent: true, forceLP: forceLP}), nil
}

// noPanic runs f and returns a recovered panic, if any.
func noPanic(f func()) (err any) {
	defer func() { err = recover() }()
	f()
	return nil
}

func describeInvalid(m map[string]map[string]bool) string {
	var parts []string
	for shape, nodes := range m {
		var ns []string
		for n := range nodes {
			ns = append(ns, n)
		}
		sort.Strings(ns)
		parts = append(parts, shape+"={"+strings.Join(ns, ",")+"}")
	}
	sort.Strings(parts)
	return strings.Join(parts, " ")
}

func startTestOxigraph(t *testing.T) *SparqlEndpoint {
	t.Helper()
	if _, err := os.Stat(dlv); err != nil {
		t.Skipf("DLV binary not found at %s", dlv)
	}
	ep, cleanup, err := StartOxigraph(false)
	if err != nil {
		t.Skip("oxigraph not available:", err)
	}
	t.Cleanup(cleanup)
	prefixes = map[string]string{"sh:": _sh, "rdf:": _rdf, "rdfs:": _rdfs}
	return ep
}

// loadTurtle parses a document and inserts it into its own named graph. Graph names must be unique
// per document: shawell caches target queries by their text (targetCache).
func loadTurtle(t *testing.T, ep *SparqlEndpoint, graphName, turtle string) *rdf.Graph {
	t.Helper()
	g := rdf.NewGraph(_sh)
	if err := g.Parse(strings.NewReader(turtle), "text/turtle"); err != nil {
		t.Fatalf("parsing document: %v\n%s", err, turtle)
	}
	if err := ep.Insert(g, graphName, false); err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { _ = ep.ClearGraph(graphName) })
	return g
}

// checkReport checks a validation report against the expected verdict, and that it is valid Turtle
// with one sh:result per result. Duplicate results are allowed: the W3C test
// validation-reports/shared expects a result twice when its shape is reached through two parents.
func checkReport(report *ValidationReport, expectedRes bool) []string {
	var problems []string
	if report.conforms != expectedRes {
		problems = append(problems, fmt.Sprintf("conforms %v, expected %v", report.conforms, expectedRes))
	}
	if report.conforms != (len(report.results) == 0) {
		problems = append(problems, fmt.Sprintf("conforms %v with %d results", report.conforms, len(report.results)))
	}
	text := report.String()
	g := rdf.NewGraph("")
	if err := g.Parse(strings.NewReader(text), "text/turtle"); err != nil {
		problems = append(problems, fmt.Sprintf("report is not valid Turtle (%v):\n%s", err, text))
	} else if n := len(g.All(nil, rdf.NewResource(_sh+"result"), nil)); n != len(report.results) {
		problems = append(problems, fmt.Sprintf("report has %d sh:result triples for %d results", n, len(report.results)))
	}
	return problems
}

func TestDifferentialValidation(t *testing.T) {
	ep := startTestOxigraph(t)

	runs := 80
	if n, err := strconv.Atoi(os.Getenv("SHAWELL_FUZZ")); err == nil && n > 0 {
		runs = n
	}

	for seed := 1; seed <= runs; seed++ {
		t.Run(fmt.Sprint("seed", seed), func(t *testing.T) {
			doc := fzGenDoc(rand.New(rand.NewSource(int64(seed))))
			turtle := doc.turtle()
			graphName := fmt.Sprintf("<urn:fuzz:%d>", seed)
			g := loadTurtle(t, ep, graphName, turtle)

			expected := doc.expectedInvalid()
			expectedRes := len(expected) == 0
			var problems []string

			for _, forceLP := range []bool{false, true} {
				path := map[bool]string{false: "unwinding", true: "logic program"}[forceLP]

				res, invalid, err := shawellInvalid(g, ep, graphName, forceLP)
				if err != nil {
					problems = append(problems, fmt.Sprintf("%s: panic: %v", path, err))
					continue
				}
				if describeInvalid(invalid) != describeInvalid(expected) {
					problems = append(problems, fmt.Sprintf("%s: invalid targets %s, expected %s",
						path, describeInvalid(invalid), describeInvalid(expected)))
				}
				if res != expectedRes {
					problems = append(problems, fmt.Sprintf("%s: verdict %v, expected %v", path, res, expectedRes))
				}

				report, err := shawellReport(g, ep, graphName, forceLP)
				if err != nil {
					problems = append(problems, fmt.Sprintf("%s report: panic: %v", path, err))
					continue
				}
				for _, p := range checkReport(report, expectedRes) {
					problems = append(problems, path+" report: "+p)
				}
			}

			// printing the parsed document walks all nested shapes, with and without blank shapes
			for _, debug := range []bool{false, true} {
				parsed := GetShaclDocument(g, graphName, false)
				parsed.debug = debug
				if err := noPanic(func() { _ = parsed.String() }); err != nil {
					problems = append(problems, fmt.Sprintf("ShaclDocument.String (debug=%v): panic: %v", debug, err))
				}
			}

			if len(problems) > 0 {
				t.Errorf("%s\n\tdocument:\n%s", strings.Join(problems, "\n\t"), turtle)
			}
		})
	}
}
