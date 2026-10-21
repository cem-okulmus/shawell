package main

import (
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
				GetShaclDocument(g, "<"+_sh+"parsing>", false)
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
