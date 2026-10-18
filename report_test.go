package main

import (
	"fmt"
	"sort"
	"strings"
	"testing"

	rdf "github.com/cem-okulmus/rdf2go-1"
)

// TestReportRoundTrip checks that validation reports can be read back: the report must be valid
// Turtle, report exactly the violating values with their lexical form, language tag and datatype,
// and give each result an sh:resultPath that parses back into the path of the property shape.
// Every value reached by the path violates sh:in, so the expected values are the path's values,
// computed with the reference path evaluation of paths_test.go.
func TestReportRoundTrip(t *testing.T) {
	ep := startTestOxigraph(t)

	values := []string{
		`"say \"hi\"\n"@en`,
		`"tab\there"`,
		`"Unicode: é ✓"`,
		`"back\\slash"`,
		`"42"^^<http://www.w3.org/2001/XMLSchema#integer>`,
		`<` + pathNS + `other>`,
		`_:blank`,
	}
	p, q, r := pPred("p"), pPred("q"), pPred("r")
	paths := []pathExpr{p, pInv(q), pSeq(r, p), pAlt(p, q), pUnary("plus", p), pUnary("opt", p)}

	focus := "<" + pathNS + "focus>"
	var data strings.Builder
	data.WriteString(fmt.Sprintf("%s <%sr> <%smid> .\n", focus, pathNS, pathNS))
	for i, v := range values {
		data.WriteString(fmt.Sprintf("%s <%sp> %s .\n", focus, pathNS, v))
		data.WriteString(fmt.Sprintf("<%smid> <%sp> %s .\n", pathNS, pathNS, v))
		if !strings.HasPrefix(v, `"`) { // literals cannot be subjects
			data.WriteString(fmt.Sprintf("%s <%sq> %s .\n", v, pathNS, focus))
			data.WriteString(fmt.Sprintf("%s <%sp> <%schain%d> .\n", v, pathNS, pathNS, i))
		}
	}
	dataGraph := rdf.NewGraph("")
	if err := dataGraph.Parse(strings.NewReader(data.String()), "text/turtle"); err != nil {
		t.Fatal(err)
	}

	// edges of the data graph, with nodes written as Turtle terms, for the reference evaluation
	edges := map[string]relation{}
	nodeSet := map[string]bool{}
	for tr := range dataGraph.IterTriples() {
		pred := strings.TrimPrefix(tr.Predicate.RawValue(), pathNS)
		if edges[pred] == nil {
			edges[pred] = relation{}
		}
		edges[pred][pair{tr.Subject.String(), tr.Object.String()}] = true
		nodeSet[tr.Subject.String()], nodeSet[tr.Object.String()] = true, true
	}
	var nodes []string
	for n := range nodeSet {
		nodes = append(nodes, n)
	}

	for i, e := range paths {
		t.Run(e.String(), func(t *testing.T) {
			turtle := `@prefix sh: <http://www.w3.org/ns/shacl#> .
<` + pathNS + `S> a sh:NodeShape ; sh:targetNode ` + focus + ` ;
  sh:property [ sh:path ` + e.turtle() + ` ; sh:in ( <` + pathNS + `allowed> ) ] .
` + data.String()
			graphName := fmt.Sprintf("<urn:report-roundtrip:%d>", i)
			g := loadTurtle(t, ep, graphName, turtle)

			report, err := shawellReport(g, ep, graphName, false)
			if err != nil {
				t.Fatalf("panic: %v", err)
			}
			text := report.String()
			rg := rdf.NewGraph("")
			if err := rg.Parse(strings.NewReader(text), "text/turtle"); err != nil {
				t.Fatalf("report is not valid Turtle: %v\n%s", err, text)
			}

			var expected, reported []string
			for pr := range e.eval(edges, nodes) {
				if pr.s == focus && !strings.HasPrefix(pr.o, "_:") {
					expected = append(expected, pr.o)
				}
			}
			blankExpected := false
			for pr := range e.eval(edges, nodes) {
				blankExpected = blankExpected || (pr.s == focus && strings.HasPrefix(pr.o, "_:"))
			}
			blankReported := false
			for _, tr := range rg.All(nil, rdf.NewResource(_sh+"value"), nil) {
				if _, isBlank := tr.Object.(*rdf.BlankNode); isBlank {
					blankReported = true // blank node labels are not preserved, only compare presence
					continue
				}
				reported = append(reported, tr.Object.String())
			}
			sort.Strings(expected)
			sort.Strings(reported)
			reported = removeDuplicate(reported)
			if strings.Join(reported, "\n") != strings.Join(expected, "\n") {
				t.Errorf("reported values\n\t%s\nexpected\n\t%s", strings.Join(reported, "\n\t"), strings.Join(expected, "\n\t"))
			}
			if blankReported != blankExpected {
				t.Errorf("blank node value reported: %v, expected %v", blankReported, blankExpected)
			}

			want := parsePath(t, e.turtle()).PropertyRDF()
			results := rg.All(nil, rdf.NewResource(_sh+"resultPath"), nil)
			if len(results) == 0 {
				t.Errorf("no sh:resultPath in the report")
			}
			for _, tr := range results {
				var got PropertyPath
				if err := noPanic(func() { got, _ = ExtractPropertyPath(rg, tr.Object) }); err != nil || got == nil {
					t.Errorf("sh:resultPath cannot be parsed (%v)", err)
					continue
				}
				if gotRDF := got.PropertyRDF(); gotRDF != want {
					t.Errorf("sh:resultPath is %s, expected %s", gotRDF, want)
				}
			}
		})
	}
}
