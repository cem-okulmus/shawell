package main

import (
	"fmt"
	"sort"
	"strings"
	"testing"

	rdf "github.com/cem-okulmus/rdf2go-1"
	"github.com/knakk/sparql"
)

// Tests for the conversion of SPARQL results into tables, and for the grouped tables that the
// unwinding and the logic program translation are built on.

func parseResults(t *testing.T, json string) *sparql.Results {
	t.Helper()
	res, err := sparql.ParseJSON(strings.NewReader(json))
	if err != nil {
		t.Fatal(err)
	}
	return res
}

// validTurtleTerm reports whether a term's String() is usable in Turtle (and SPARQL) syntax.
func validTurtleTerm(term rdf.Term) bool {
	g := rdf.NewGraph("")
	return g.Parse(strings.NewReader("<urn:s> <urn:p> "+term.String()+" ."), "text/turtle") == nil && g.Len() == 1
}

// TestGetTableConvertsBindings checks the conversion of every kind of SPARQL binding: unbound
// variables become Unbound, while blank nodes from the data stay blank nodes, and literals keep
// their lexical form, language and datatype.
func TestGetTableConvertsBindings(t *testing.T) {
	res := parseResults(t, `{
	  "head": {"vars": ["s", "o"]},
	  "results": {"bindings": [
	    {"s": {"type": "uri", "value": "http://example.org/a"}},
	    {"s": {"type": "uri", "value": "http://example.org/a"}, "o": {"type": "bnode", "value": "b1"}},
	    {"s": {"type": "uri", "value": "http://example.org/a"}, "o": {"type": "literal", "value": "say \"hi\"\n", "xml:lang": "en"}},
	    {"s": {"type": "uri", "value": "http://example.org/a"}, "o": {"type": "literal", "value": "plain"}},
	    {"s": {"type": "uri", "value": "http://example.org/a"}, "o": {"type": "literal", "value": "5", "datatype": "http://www.w3.org/2001/XMLSchema#integer"}},
	    {"s": {"type": "uri", "value": "http://example.org/a"}, "o": {"type": "typed-literal", "value": "2.5", "datatype": "http://www.w3.org/2001/XMLSchema#decimal"}}
	  ]}
	}`)
	table := GetTable(res)

	if got := table.GetHeader(); strings.Join(got, ",") != "s,o" {
		t.Fatalf("header %v, expected [s o]", got)
	}
	if table.Len() != 6 {
		t.Fatalf("got %d rows, expected 6", table.Len())
	}

	o := func(i int) rdf.Term { return table.content[i][1] }

	if _, ok := o(0).(Unbound); !ok {
		t.Errorf("unbound variable became %#v, expected Unbound", o(0))
	}
	if b, ok := o(1).(rdf.BlankNode); !ok || b.ID != "b1" {
		t.Errorf("blank node became %#v, expected the blank node b1", o(1))
	}
	if l, ok := o(2).(rdf.Literal); !ok || l.Value != "say \"hi\"\n" || l.Language != "en" {
		t.Errorf("language literal became %#v", o(2))
	}
	if l, ok := o(4).(rdf.Literal); !ok || l.Value != "5" || l.Datatype == nil || l.Datatype.RawValue() != _xsd+"integer" {
		t.Errorf("typed literal became %#v", o(4))
	}
	if l, ok := o(5).(rdf.Literal); !ok || l.Value != "2.5" || l.Datatype == nil || l.Datatype.RawValue() != _xsd+"decimal" {
		t.Errorf("typed-literal (old JSON format) became %#v", o(5))
	}

	// result terms are printed into reports and queries, so their String() must be valid syntax
	for i := 1; i < table.Len(); i++ {
		if !validTurtleTerm(o(i)) {
			t.Errorf("row %d: term %#v prints as %s, which is not valid Turtle", i, o(i), o(i).String())
		}
	}
}

// TestGetTableKeepsUnusualIRIs checks that a bound value is never turned into Unbound: knakk's
// Solutions() silently drops bindings it cannot convert, such as IRIs it considers invalid.
func TestGetTableKeepsUnusualIRIs(t *testing.T) {
	res := parseResults(t, `{
	  "head": {"vars": ["s", "o"]},
	  "results": {"bindings": [
	    {"s": {"type": "uri", "value": "http://example.org/a"}, "o": {"type": "uri", "value": "http://example.org/with space"}}
	  ]}
	}`)
	table := GetTable(res)
	if _, ok := table.content[0][1].(Unbound); ok {
		t.Errorf("the bound IRI <http://example.org/with space> was turned into Unbound, so its value is lost")
	}
}

func res(uri string) rdf.Term { return rdf.Resource{URI: "http://example.org/" + uri} }

func groupedTestTable() *GroupedTable[rdf.Term] {
	simple := &TableSimple[rdf.Term]{
		header: []string{"S", "P1", "P2"},
		content: [][]rdf.Term{
			{res("a"), res("x"), Unbound{}},
			{res("a"), res("y"), Unbound{}},
			{res("a"), res("x"), Unbound{}}, // duplicate row
			{res("b"), Unbound{}, res("z")},
			{res("c"), Unbound{}, Unbound{}},
		},
	}
	return GetGroupedTable[rdf.Term](simple)
}

func termNames(terms []rdf.Term) string {
	var out []string
	for _, t := range terms {
		out = append(out, strings.TrimPrefix(t.RawValue(), "http://example.org/"))
	}
	sort.Strings(out)
	return "[" + strings.Join(out, " ") + "]"
}

func targetNames(t *GroupedTable[rdf.Term]) string {
	var out []rdf.Term
	for k := range t.IterTargets() {
		out = append(out, k)
	}
	return termNames(out)
}

// TestGroupedTableGroups checks the grouping: one key per focus node, duplicate values removed,
// Unbound values dropped, and every column present even when it has no values.
func TestGroupedTableGroups(t *testing.T) {
	table := groupedTestTable()

	if got := targetNames(table); got != "[a b c]" {
		t.Errorf("targets %s, expected [a b c]", got)
	}
	cases := []struct {
		key      string
		column   int
		expected string
	}{
		{"a", 0, "[a]"}, {"a", 1, "[x y]"}, {"a", 2, "[]"},
		{"b", 1, "[]"}, {"b", 2, "[z]"},
		{"c", 1, "[]"}, {"c", 2, "[]"},
	}
	for _, c := range cases {
		if got := termNames(table.GetGroupOfTarget(res(c.key), c.column)); got != c.expected {
			t.Errorf("group of %s in column %d is %s, expected %s", c.key, c.column, got, c.expected)
		}
	}
	for _, key := range []string{"a", "b", "c"} {
		group, present := table.group[res(key)]
		if !present || len(group) != 2 {
			t.Errorf("key %s should have both columns in its group, got %v", key, group)
		}
	}
}

// TestGroupedTableRemoveIndex checks that RemoveIndex removes exactly the rows of the given key.
func TestGroupedTableRemoveIndex(t *testing.T) {
	for _, key := range []string{"a", "b", "c"} {
		table := groupedTestTable()
		before := table.Len()
		var keyRows int
		for _, row := range table.content {
			if row[0] == res(key) {
				keyRows++
			}
		}
		if err := table.RemoveIndex(res(key)); err != nil {
			t.Fatal(err)
		}
		if table.Len() != before-keyRows {
			t.Errorf("RemoveIndex(%s): %d rows left, expected %d", key, table.Len(), before-keyRows)
		}
		for _, row := range table.content {
			if row[0] == res(key) {
				t.Errorf("RemoveIndex(%s): a row of %s is still there", key, key)
			}
		}
	}
}

// TestGroupedTableAddIndex checks that AddIndex copies exactly the rows of the given key, and
// rejects tables with a different header.
func TestGroupedTableAddIndex(t *testing.T) {
	source := groupedTestTable()
	target := &GroupedTable[rdf.Term]{header: source.header}
	if err := target.AddIndex(res("a"), source); err != nil {
		t.Fatal(err)
	}
	if target.Len() != 3 {
		t.Errorf("AddIndex(a) copied %d rows, expected the 3 rows of a", target.Len())
	}
	for _, row := range target.content {
		if row[0] != res("a") {
			t.Errorf("AddIndex(a) copied a row of %s", row[0])
		}
	}

	other := &GroupedTable[rdf.Term]{header: []string{"S", "Other", "P2"}}
	if err := other.AddIndex(res("a"), source); err == nil {
		t.Errorf("AddIndex accepted a table with a different header")
	}
}

// TestGroupedTableMergeKeepsGrouping checks that a merged grouped table is grouped over all of its
// rows: IterTargets and GetGroupOfTarget read the grouping, not the rows.
func TestGroupedTableMergeKeepsGrouping(t *testing.T) {
	left := GetGroupedTable[rdf.Term](&TableSimple[rdf.Term]{
		header: []string{"S", "P"}, content: [][]rdf.Term{{res("a"), res("x")}},
	})
	right := GetGroupedTable[rdf.Term](&TableSimple[rdf.Term]{
		header: []string{"S", "P"}, content: [][]rdf.Term{{res("b"), res("y")}, {res("a"), res("z")}},
	})
	if err := left.Merge(right); err != nil {
		t.Fatal(err)
	}
	if got := targetNames(left); got != "[a b]" {
		t.Errorf("targets after Merge are %s, expected [a b]", got)
	}
	if got := termNames(left.GetGroupOfTarget(res("a"), 1)); got != "[x z]" {
		t.Errorf("group of a after Merge is %s, expected [x z]", got)
	}

	mismatched := GetGroupedTable[rdf.Term](&TableSimple[rdf.Term]{header: []string{"S", "Q"}})
	if err := left.Merge(mismatched); err == nil {
		t.Errorf("Merge accepted a table with a different header")
	}
	if err := left.Merge(&TableSimple[rdf.Term]{header: []string{"S", "P"}}); err == nil {
		t.Errorf("Merge accepted a simple table")
	}
}

// TestTableAccessors checks column access by index and by attribute name, including the errors.
func TestTableAccessors(t *testing.T) {
	simple := &TableSimple[rdf.Term]{
		header:  []string{"S", "P"},
		content: [][]rdf.Term{{res("a"), res("x")}, {res("b"), res("y")}},
	}
	grouped := GetGroupedTable[rdf.Term](simple)

	for name, table := range map[string]Table[rdf.Term]{"simple": simple, "grouped": grouped} {
		col, err := table.GetColumn(1)
		if err != nil || termNames(col) != "[x y]" {
			t.Errorf("%s: GetColumn(1) = %s, %v", name, termNames(col), err)
		}
		col, err = table.GetAttribute("P")
		if err != nil || termNames(col) != "[x y]" {
			t.Errorf("%s: GetAttribute(P) = %s, %v", name, termNames(col), err)
		}
		if _, err := table.GetColumn(2); err == nil {
			t.Errorf("%s: GetColumn(2) succeeded on a table with two columns", name)
		}
		if _, err := table.GetColumn(-1); err == nil {
			t.Errorf("%s: GetColumn(-1) succeeded", name)
		}
		if _, err := table.GetAttribute("Missing"); err == nil {
			t.Errorf("%s: GetAttribute(Missing) succeeded", name)
		}
	}

	if i, err := grouped.GetIndex(res("b")); err != nil || i != 1 {
		t.Errorf("GetIndex(b) = %d, %v; expected 1", i, err)
	}
	if _, err := grouped.GetIndex(res("z")); err == nil {
		t.Errorf("GetIndex succeeded for a key that is not in the table")
	}
}

// TestLogicalConstraintTargetsAreNotShared checks that the target table of one shape does not
// leak into another. GetTableForLogicalConstraints caches each target query's result and then
// merges the results of several targets; the merge must not change the cached result.
func TestLogicalConstraintTargetsAreNotShared(t *testing.T) {
	ep := startTestOxigraph(t)
	turtle := `
@prefix sh: <http://www.w3.org/ns/shacl#> .
@prefix ex: <http://example.org/> .
ex:S1 a sh:NodeShape ; sh:targetNode ex:a ; sh:targetNode ex:b ; sh:node ex:T .
ex:S2 a sh:NodeShape ; sh:targetNode ex:a ; sh:node ex:T .
ex:T a sh:NodeShape ; sh:class ex:C .
ex:a a ex:C .
ex:b a ex:C .
`
	graphName := "<urn:target-cache-test>"
	g := loadTurtle(t, ep, graphName, turtle)
	doc := GetShaclDocument(g, graphName, false)

	targetsOf := func(shape string) string {
		// the queries GetValidationReport passes for a node shape
		queries := TargetsToQueries(doc.shapeNames["http://example.org/"+shape].GetTargets(false))
		table := GetTableForLogicalConstraints(ep, nil, "", queries)
		var nodes []rdf.Term
		for row := range table.IterRows() {
			nodes = append(nodes, row[0])
		}
		return termNames(nodes)
	}

	if got := targetsOf("S1"); got != "[a b]" {
		t.Fatalf("targets of S1: %s, expected [a b]", got)
	}
	if got := targetsOf("S2"); got != "[a]" {
		t.Errorf("targets of S2 after computing those of S1: %s, expected [a]", got)
	}
}

// TestTargetCacheDoesNotChangeReports checks the consequence for reports: S2 targets only a, but
// with a polluted cache its report also checks b, which violates S2. Shapes are reported in map
// order, so the document is validated several times.
func TestTargetCacheDoesNotChangeReports(t *testing.T) {
	ep := startTestOxigraph(t)
	turtle := `
@prefix sh: <http://www.w3.org/ns/shacl#> .
@prefix ex: <http://example.org/> .
ex:S1 a sh:NodeShape ; sh:targetNode ex:a ; sh:targetNode ex:b ; sh:node ex:T .
ex:S2 a sh:NodeShape ; sh:targetNode ex:a ; sh:node ex:U .
ex:T a sh:NodeShape ; sh:class ex:C .
ex:U a sh:NodeShape ; sh:class ex:D .
ex:a a ex:C , ex:D .
ex:b a ex:C .
`
	for i := 0; i < 8; i++ {
		graphName := fmt.Sprintf("<urn:target-cache-report-%d>", i)
		g := loadTurtle(t, ep, graphName, turtle)
		report, err := shawellReport(g, ep, graphName, false)
		if err != nil {
			t.Fatalf("run %d: panic: %v", i, err)
		}
		if !report.conforms || len(report.results) > 0 {
			t.Fatalf("run %d: conforms %v with %d results, expected a conforming report", i, report.conforms, len(report.results))
		}
	}
}
