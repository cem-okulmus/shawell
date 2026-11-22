package main

import (
	"sort"
	"strings"
	"testing"

	rdf "github.com/cem-okulmus/rdf2go-1"
)

type stubEndpoint struct {
	table Table[rdf.Term]
	graph string
}

func (s stubEndpoint) Answer(Shape, []SparqlQueryFlat) Table[rdf.Term] { return s.table }
func (s stubEndpoint) Query(SparqlQuery) Table[rdf.Term]               { return s.table }
func (s stubEndpoint) QueryFlat(SparqlQueryFlat) Table[rdf.Term]       { return s.table }
func (s stubEndpoint) QueryString(string) Table[rdf.Term]              { return s.table }
func (s stubEndpoint) Insert(*rdf.Graph, string, bool) error           { return nil }
func (s stubEndpoint) Delete(*rdf.Graph, string) error                 { return nil }
func (s stubEndpoint) ClearGraph(string) error                         { return nil }
func (s stubEndpoint) GetGraph() string                                { return s.graph }

func TestPropertyXoneReportsZeroMatchingShapes(t *testing.T) {
	oldTargetCache := targetCache
	defer func() {
		targetCache = oldTargetCache
	}()
	targetCache = make(map[string]Table[rdf.Term])

	focus := rdf.NewResource("http://example.com/focus")
	value := rdf.NewResource("http://example.com/value")
	shapeA := "http://example.com/shapeA"
	shapeB := "http://example.com/shapeB"

	propertyShape := &PropertyShape{
		id:       7,
		maxCount: -1,
		path:     SimplePath{path: rdf.NewResource("http://example.com/p")},
		shape: &NodeShape{
			IRI: rdf.NewResource("http://example.com/propShape"),
			xones: []XoneShapeConstraint{
				{
					shapes: []ShapeRef{
						{name: shapeA},
						{name: shapeB},
					},
				},
			},
		},
	}

	targets := []TargetExpression{TargetNode{node: focus}}
	table := &TableSimple[rdf.Term]{
		header: []string{"sub", propertyShape.GetQualName()},
		content: [][]rdf.Term{
			{focus, value},
		},
	}
	doc := ShaclDocument{
		answered:      true,
		uncondAnswers: make(map[string]Table[rdf.Term]),
	}

	valid, reports := doc.GetVRProperty(propertyShape, stubEndpoint{table: table}, &targets, "")
	if valid {
		t.Fatal("expected property xone with zero matching shapes to be invalid")
	}
	if len(reports) != 1 {
		t.Fatalf("expected one xone validation report, got %d", len(reports))
	}
	if got := reports[0].sourceConstraintComponent.RawValue(); got != _sh+"XoneConstraintComponent" {
		t.Fatalf("expected xone constraint component, got %s", got)
	}
}

// TestShapeParsingErrors checks that GetShaclDocument does not silently drop a malformed shape
// (known bug H), wherever the shape is defined.
func TestShapeParsingErrors(t *testing.T) {
	const prefixes = `@prefix ex: <http://example.org/parsing#> .
@prefix sh: <http://www.w3.org/ns/shacl#> .
`
	cases := []struct {
		name      string
		turtle    string
		malformed bool
	}{
		{"top-level property shape", `ex:P sh:targetNode ex:a ; sh:path [ ex:bogus ex:knows ] ; sh:minCount 1 .`, true},
		{"via sh:property", `ex:S a sh:NodeShape ; sh:targetNode ex:a ; sh:property [ sh:path [ ex:bogus ex:knows ] ; sh:minCount 1 ] .`, true},
		{"inside sh:not", `ex:S a sh:NodeShape ; sh:targetNode ex:a ; sh:not [ sh:path [ ex:bogus ex:knows ] ; sh:minCount 1 ] .`, true},
		{"valid", `ex:S a sh:NodeShape ; sh:targetNode ex:a ; sh:property [ sh:path ex:knows ; sh:minCount 1 ] .`, false},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			g := rdf.NewGraph(_sh)
			if err := g.Parse(strings.NewReader(prefixes+c.turtle), "text/turtle"); err != nil {
				t.Fatal(err)
			}
			var recovered any
			func() {
				defer func() { recovered = recover() }()
				GetShaclDocument(g, "<"+_sh+"parsing>", false, "well-founded")
			}()
			if c.malformed && recovered == nil {
				t.Fatal("malformed shape was parsed without an error")
			}
			if !c.malformed && recovered != nil {
				t.Fatalf("valid document failed to parse: %v", recovered)
			}
		})
	}
}

// TestDomainTargetsStayIndirect covers phase 3 step 2 of the stable semantics plan: in stable modes every shape gets
// the domain target and one target per constant in Const(C), all as indirect targets. They must ground the program
// (GetTargets(true), used by GetTargetShape) but never become validation targets (GetTargets(false), used by
// GetValidTargetShape and the reports), so the validation targets must be the same as under well-founded.
func TestDomainTargetsStayIndirect(t *testing.T) {
	const doc = `@prefix ex: <http://example.org/domain#> .
@prefix sh: <http://www.w3.org/ns/shacl#> .
ex:a ex:q ex:b .
ex:S a sh:NodeShape ; sh:targetNode ex:a ; sh:property [ sh:path ex:q ; sh:class ex:C ] .
ex:T a sh:NodeShape ; sh:or ( [ sh:hasValue ex:z ] [ sh:in ( ex:b "w" ) ] ) .
`
	parse := func(semantics string) ShaclDocument {
		g := rdf.NewGraph(_sh)
		if err := g.Parse(strings.NewReader(doc), "text/turtle"); err != nil {
			t.Fatal(err)
		}
		return GetShaclDocument(g, "<"+_sh+"domain>", false, semantics)
	}
	queries := func(targets []TargetExpression) []string {
		var out []string
		for _, target := range targets {
			out = append(out, GetTargetTerm(target))
		}
		sort.Strings(out)
		return out
	}
	// the constants a shape is grounded at: its TargetNode targets, direct or indirect without a path
	constants := func(targets []TargetExpression) map[string]bool {
		out := make(map[string]bool)
		for _, target := range targets {
			if indirect, ok := target.(TargetIndirect); ok && indirect.indirection == nil {
				target = indirect.actual
			}
			if node, ok := target.(TargetNode); ok {
				out[node.node.RawValue()] = true
			}
		}
		return out
	}
	hasDomain := func(targets []TargetExpression) bool {
		for _, target := range targets {
			if indirect, ok := target.(TargetIndirect); ok {
				if _, ok := indirect.actual.(TargetDomain); ok {
					return indirect.indirection == nil
				}
			}
		}
		return false
	}

	const ex = "http://example.org/domain#"
	constC := []string{ex + "a", ex + "z", ex + "b", "w", ex + "C"} // targetNode, hasValue, in (IRI and literal), class
	wf := parse("well-founded")
	for name, shape := range wf.shapeNames {
		if hasDomain(shape.GetTargets(true)) {
			t.Errorf("well-founded: shape %s has the domain target", name)
		}
	}

	for _, semantics := range []string{"stable-brave", "stable-cautious"} {
		t.Run(semantics, func(t *testing.T) {
			stable := parse(semantics)
			if len(stable.shapeNames) != len(wf.shapeNames) {
				t.Fatalf("got %d shapes, well-founded has %d", len(stable.shapeNames), len(wf.shapeNames))
			}
			for name, shape := range stable.shapeNames {
				all := shape.GetTargets(true)
				if !hasDomain(all) {
					t.Errorf("shape %s lacks the domain target", name)
				}
				got := constants(all)
				for _, c := range constC {
					if !got[c] {
						t.Errorf("shape %s is not grounded at constant %s", name, c)
					}
				}
				if got[ex+"q"] {
					t.Errorf("shape %s is grounded at the path predicate %s, which is not in Const(C)", name, ex+"q")
				}

				validation := queries(shape.GetTargets(false))
				want := queries(wf.shapeNames[name].GetTargets(false))
				if strings.Join(validation, "\n") != strings.Join(want, "\n") {
					t.Errorf("shape %s: validation targets differ from well-founded\n got: %q\nwant: %q", name, validation, want)
				}
				for _, target := range shape.GetTargets(false) {
					if _, ok := target.(TargetIndirect); ok {
						t.Errorf("shape %s: GetTargets(false) returned the indirect target %s", name, target)
					}
				}
			}
		})
	}
}
