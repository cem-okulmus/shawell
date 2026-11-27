package main

import (
	"strings"
	"testing"

	rdf "github.com/cem-okulmus/rdf2go-1"
)

// Phase 3 of the stable semantics plan makes blank nodes focus nodes far more often, through the domain target.
// The logic program identifies a node by the label the endpoint returns for it (see rewrite in logicProgram.go),
// so a blank node must come back with the same label from every query. If two queries label it differently, the
// program sees two unrelated constants and the verdict changes.
//
// Each case below is only valid if one blank node is matched across two queries. A mismatch turns the case into
// its negative control: under well-founded the target is no longer derived (invalid), and in the stable modes
// U(x) <- not U(x) fires at the unmatched node, so there is no model. The IRI variant of each case is the control
// that the case itself is valid.

const blankLabelPrefixes = `@prefix : <http://example.org/blanklabels#> .
@prefix sh: <http://www.w3.org/ns/shacl#> .
`

type blankLabelCase struct {
	name   string
	data   string
	shapes string
	want   ValidationStatus // in every mode
}

var blankLabelCases = []blankLabelCase{
	{
		// _:a as subject: from the domain query of :U and the query of the separate property shape :P
		name: "subject across shapes",
		data: `_:a :p _:a .`,
		shapes: `:U a sh:NodeShape ; sh:targetSubjectsOf :p ; sh:or ( :P [ sh:not :U ] ) .
:P a sh:PropertyShape ; sh:path :p ; sh:minCount 1 .`,
		want: Valid,
	},
	{
		// _:b as object: a value of :p in the query of :U, and a focus node in the query of :V
		name: "path value across shapes",
		data: `_:a :p _:b . _:b :q 1 .`,
		shapes: `:U a sh:NodeShape ; sh:targetSubjectsOf :p ; sh:or ( [ sh:path :p ; sh:node :V ] [ sh:not :U ] ) .
:V a sh:NodeShape ; sh:property [ sh:path :q ; sh:minCount 1 ] .`,
		want: Valid,
	},
	{
		// negative control: _:b has no :q, which is what a label mismatch in the case above looks like
		name: "path value across shapes, negative",
		data: `_:a :p _:b .`,
		shapes: `:U a sh:NodeShape ; sh:targetSubjectsOf :p ; sh:or ( [ sh:path :p ; sh:node :V ] [ sh:not :U ] ) .
:V a sh:NodeShape ; sh:property [ sh:path :q ; sh:minCount 1 ] .`,
		want: -1, // depends on the mode, see blankLabelWant
	},
}

// blankLabelWant returns the expected status of a case in the given mode.
func blankLabelWant(c blankLabelCase, semantics Semantics) ValidationStatus {
	if c.want >= 0 {
		return c.want
	}
	if _, ok := semantics.(WellFounded); ok {
		return Invalid
	}
	return NoModel
}

// iriVariant replaces the blank nodes _:x of a case's data by the IRIs :x.
func iriVariant(data string) string {
	return strings.ReplaceAll(data, "_:", ":")
}

// validateSeparateGraphs inserts the data into its own named graph and parses the shapes from a separate graph,
// as shawell does without --dataIncluded, so the shapes graph cannot reach the domain. data and shapes are
// complete Turtle documents, prefixes included. It returns the report of answerShacl.
func validateSeparateGraphs(t *testing.T, ep *SparqlEndpoint, name, data, shapes string, cfg config) *ValidationReport {
	t.Helper()
	dataGraph := rdf.NewGraph(_sh)
	if err := dataGraph.Parse(strings.NewReader(data), "text/turtle"); err != nil {
		t.Fatal(err)
	}
	shapesGraph := rdf.NewGraph(_sh)
	if err := shapesGraph.Parse(strings.NewReader(shapes), "text/turtle"); err != nil {
		t.Fatal(err)
	}
	prefixes = map[string]string{"sh:": _sh, "rdf:": _rdf, "rdfs:": _rdfs} // as in startTestOxigraph

	graphName := "<" + _sh + name + ">"
	if err := ep.ClearGraph(graphName); err != nil {
		t.Fatal(err)
	}
	if err := ep.Insert(dataGraph, graphName, false); err != nil {
		t.Fatal(err)
	}
	defer ep.ClearGraph(graphName) //nolint:errcheck

	doc := GetShaclDocument(shapesGraph, graphName, false, cfg.semantics)
	activeDoc = &doc
	return answerShacl(ep, doc, cfg)
}

func runBlankLabelCases(t *testing.T, ep *SparqlEndpoint) {
	cmd, err := findClingo("")
	if err != nil {
		t.Skip("clingo not available:", err)
	}
	clingoCmd = cmd

	for _, c := range blankLabelCases {
		for _, variant := range []struct{ name, data string }{{"blank", c.data}, {"iri", iriVariant(c.data)}} {
			for _, semantics := range []Semantics{WellFounded{}, StableBrave{}, StableCautious{}} {
				t.Run(c.name+"/"+variant.name+"/"+semantics.String(), func(t *testing.T) {
					got := validateSeparateGraphs(t, ep, "blanklabels", blankLabelPrefixes+variant.data,
						blankLabelPrefixes+c.shapes, config{silent: true, omitVR: true, semantics: semantics}).status
					if want := blankLabelWant(c, semantics); got != want {
						t.Errorf("got status %v, want %v", got, want)
					}
				})
			}
		}
	}
}

func TestBlankLabelsOxigraph(t *testing.T) {
	ensureDependencies(true, false)
	ep, cleanup, err := StartOxigraph(false)
	if err != nil {
		t.Skip("oxigraph not available:", err)
	}
	defer cleanup()
	runBlankLabelCases(t, ep)
}

// TestBlankLabelsGraphDB uses the same GraphDB repository as the compliance tests, and skips if it is not running.
func TestBlankLabelsGraphDB(t *testing.T) {
	ensureDependencies(false, false)
	ep := GetSparqlEndpoint(
		"http://localhost:7200/repositories/graphdb",
		"http://localhost:7200/repositories/graphdb/statements",
		"", "", false, true, "",
	)
	if err := ep.Ping(); err != nil {
		t.Skip("GraphDB not available:", err)
	}
	runBlankLabelCases(t, ep)
}
