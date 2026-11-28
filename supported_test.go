package main

import (
	"slices"
	"strings"
	"testing"
)

// Tests S4.1 and S4.2 of supported_semantics_plan.md: the completion as a program transformation, and its
// supported models as clingo computes them through runClingo.

// canonicalRule writes a rule without the whitespace differences of TableToLP and expandRules, with the body
// sorted, so that rules can be compared as text.
func canonicalRule(r serialisedRule) string {
	literal := func(l string) string {
		fields := strings.Fields(l)
		if len(fields) > 0 && fields[0] == "not" {
			return "not " + strings.Join(fields[1:], "")
		}
		return strings.Join(fields, "")
	}
	head := literal(r.head)
	if strings.HasPrefix(head, "{") { // a choice rule: "{ h }"
		head = "{ " + strings.Trim(head, "{}") + " }"
	}
	var body []string
	for _, l := range r.body {
		body = append(body, literal(l))
	}
	slices.Sort(body)
	if len(body) == 0 {
		return head + "."
	}
	return head + " :- " + strings.Join(body, ", ") + "."
}

func canonicalRules(p serialisedProgram) []string {
	var out []string
	for _, r := range p.rules {
		out = append(out, canonicalRule(r))
	}
	return out
}

// completionInput has the cases S2.2 lists: two rules for one atom written in both whitespace forms, an atom
// with one rule, a fact, a positive self-loop, the auxiliary predicate shape3intern, the predicate shape30
// that is no shape here, a constraint, and a non-ground counting rule.
var completionInput = serialisedProgram{rules: []serialisedRule{
	{head: "shape3 (  iri0 )", body: []string{"shape3intern(  iri0 )", "shape5( iri0 )"}},
	{head: "shape3intern(iri0)", body: []string{"shape5(iri1)"}},
	{head: "shape3(iri0)", body: []string{"shape30(iri0)"}},
	{head: "shape3 (  iri1 )", body: []string{"shape5( iri1 )"}},
	{head: "shape5(iri0)", body: []string{"shape5(iri0)"}},
	{head: "shape5(iri1)"},
	{head: "shape30(iri0)", body: []string{"not shape3(iri1)"}},
	{head: "", body: []string{"not shape3(iri0)"}},
	{head: "atLeast1(Y,Z+1)", body: []string{"qual1(X,Y) ", "atLeast1(X,Z)", "shape5(Y)"}},
}}

var completionShapes = map[string]bool{"shape3": true, "shape5": true}

func TestCompletion(t *testing.T) {
	got := completionInput.completion(completionShapes)

	want := []string{
		// kept as they are
		"shape3intern(iri0) :- shape5(iri1).",
		"shape30(iri0) :- not shape3(iri1).",
		" :- not shape3(iri0).",
		"atLeast1(Y,Z+1) :- atLeast1(X,Z), qual1(X,Y), shape5(Y).",
		// shape3(iri0): two rules, two support rules
		"sup_shape3(iri0) :- shape3intern(iri0), shape5(iri0).",
		"sup_shape3(iri0) :- shape30(iri0).",
		"{ shape3(iri0) }.",
		" :- not sup_shape3(iri0), shape3(iri0).",
		" :- not shape3(iri0), sup_shape3(iri0).",
		"sup_shape3(iri1) :- shape5(iri1).",
		"{ shape3(iri1) }.",
		" :- not sup_shape3(iri1), shape3(iri1).",
		" :- not shape3(iri1), sup_shape3(iri1).",
		"sup_shape5(iri0) :- shape5(iri0).",
		"{ shape5(iri0) }.",
		" :- not sup_shape5(iri0), shape5(iri0).",
		" :- not shape5(iri0), sup_shape5(iri0).",
		// a fact becomes a support fact
		"sup_shape5(iri1).",
		"{ shape5(iri1) }.",
		" :- not sup_shape5(iri1), shape5(iri1).",
		" :- not shape5(iri1), sup_shape5(iri1).",
	}

	gotRules := canonicalRules(got)
	sortedGot, sortedWant := slices.Sorted(slices.Values(gotRules)), slices.Sorted(slices.Values(want))
	if !slices.Equal(sortedGot, sortedWant) {
		var missing, extra []string
		for _, r := range sortedWant {
			if !slices.Contains(sortedGot, r) {
				missing = append(missing, r)
			}
		}
		for _, r := range sortedGot {
			if !slices.Contains(sortedWant, r) {
				extra = append(extra, r)
			}
		}
		t.Errorf("completion differs\nmissing:\n\t%s\nunexpected:\n\t%s",
			strings.Join(missing, "\n\t"), strings.Join(extra, "\n\t"))
	}

	// deterministic: the same program on every run, also as written to clingo
	for range 20 {
		if again := completionInput.completion(completionShapes); again.String() != got.String() {
			t.Fatalf("completion is not deterministic:\n%s\nversus\n%s", got, again)
		}
	}

	// the input is left alone
	if len(completionInput.rules) != 9 || completionInput.rules[0].head != "shape3 (  iri0 )" {
		t.Errorf("completion changed its input: %v", completionInput.rules)
	}
}

// The completion of a program without shape atoms is the program itself.
func TestCompletionNoShapes(t *testing.T) {
	got := completionInput.completion(map[string]bool{})
	if !slices.Equal(canonicalRules(got), canonicalRules(completionInput)) {
		t.Errorf("completion without shape predicates changed the program:\n%s", got)
	}
}

// completed returns the completion of the given rules, over the shape predicates shape1 to shape3, in the
// form solveWithClingo takes: head first, then the body. Rules for other predicates, such as the constraints
// a test adds, pass through unchanged.
func completed(rules ...[]string) [][]string {
	var p serialisedProgram
	for _, r := range rules {
		p.rules = append(p.rules, serialisedRule{head: r[0], body: r[1:]})
	}
	var out [][]string
	for _, r := range p.completion(map[string]bool{"shape1": true, "shape2": true, "shape3": true}).rules {
		out = append(out, append([]string{r.head}, r.body...))
	}
	return out
}

// TestClingoSupported solves completed programs through runClingo. Each case adds a constraint that asks for a
// model with or without a shape atom, as the brave and cautious calls do. That the shape atoms are in the
// returned model at all checks the #show fix of S2.3: after the completion, a shape atom is the head of a
// choice rule only.
func TestClingoSupported(t *testing.T) {
	selfLoop := []string{"shape1(c)", "shape1(c)"}
	for _, c := range []struct {
		name    string
		rules   [][]string
		status  solveStatus
		atoms   string
		comment string
	}{
		{"self-loop, holding", completed(selfLoop, []string{"", "not shape1(c)"}), satisfiable, "shape1(c)",
			"a positive loop supports itself"},
		{"self-loop, not holding", completed(selfLoop, []string{"", "shape1(c)"}), satisfiable, "",
			"the empty model is supported too"},
		{"self-loop, stable", [][]string{selfLoop, {"", "not shape1(c)"}}, unsatisfiable, "",
			"without the completion, the loop has only the empty stable model"},
		{"unsupported", completed([]string{"shape1(c)", "shape2(c)"}, []string{"", "not shape1(c)"}), unsatisfiable, "",
			"shape2(c) has no rule, so nothing supports shape1(c)"},
		{"fact", completed([]string{"shape1(c)"}, []string{"", "shape1(c)"}), unsatisfiable, "",
			"a fact cannot be false"},
		{"one of two bodies", completed(
			[]string{"shape1(c)", "shape2(c)"},
			[]string{"shape1(c)", "shape3(c)"},
			[]string{"shape2(c)", "shape2(c)"},
			[]string{"shape3(c)"},
			[]string{"", "shape1(c)"}), unsatisfiable, "",
			"shape1(c) holds iff some body holds; the body shape3(c) does, whether or not shape2(c) does"},
		{"even loop through negation", completed(
			[]string{"shape1(c)", "not shape2(c)"},
			[]string{"shape2(c)", "not shape1(c)"},
			[]string{"", "not shape1(c)"}), satisfiable, "shape1(c)",
			"a tight program keeps its stable models"},
		{"odd loop", completed([]string{"shape1(c)", "not shape1(c)"}), unsatisfiable, "",
			"an odd loop has no supported model either"},
	} {
		t.Run(c.name, func(t *testing.T) {
			out := solveWithClingo(t, c.rules...)
			if !out.returned || out.status != c.status || strings.Join(out.atoms, " ") != c.atoms {
				t.Errorf("%s: expected status %v with atoms %q, got: %v", c.comment, c.status, c.atoms, out)
			}
		})
	}
}
