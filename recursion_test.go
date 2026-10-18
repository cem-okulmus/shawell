package main

import (
	"fmt"
	"strings"
	"testing"
)

// Tests for recursive documents. Shawell evaluates them with the well-founded semantics, through the
// logic program: shape membership that is only supported by a positive cycle is false, and membership
// that depends on its own negation is undefined. A target conforms only if its membership is true, so
// an undefined membership is a violation, like a false one (see InvalidTargetLP). Each case lists the
// expected invalid targets per shape, and also checks that the validation report agrees with the verdict.

const recPrefixes = `
@prefix sh: <http://www.w3.org/ns/shacl#> .
@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .
@prefix ex: <` + fzNS + `> .
`

// recViaPath returns a shape S targeting n0, where a node conforms if it has class A, or if it has at
// least one value via the given path and all of them conform. sh:minCount keeps the nodes in between
// from conforming vacuously, so they have to be evaluated.
func recViaPath(path string) string {
	return `ex:S a sh:NodeShape ; sh:targetNode ex:n0 ;
	  sh:or ( [ sh:class ex:A ] [ sh:property [ sh:path ` + path + ` ; sh:minCount 1 ; sh:node ex:S ] ] ) .`
}

func TestRecursiveShapes(t *testing.T) {
	ep := startTestOxigraph(t)

	cases := []struct {
		name    string
		turtle  string
		invalid string // as printed by describeInvalid
	}{
		{
			name: "positive-cycle-is-unfounded",
			turtle: `ex:S a sh:NodeShape ; sh:targetNode ex:n0 ; sh:property [ sh:path ex:p ; sh:node ex:S ] .
			         ex:n0 ex:p ex:n1 . ex:n1 ex:p ex:n0 .`,
			invalid: "S={n0}",
		},
		{
			name: "positive-chain-with-exit",
			turtle: `ex:S a sh:NodeShape ; sh:targetNode ex:n0 ; sh:property [ sh:path ex:p ; sh:node ex:S ] .
			         ex:n0 ex:p ex:n1 . ex:n1 ex:p ex:n2 .`,
			invalid: "",
		},
		// The following cases target the indirect targets of recursive shapes (known bug T). They all use
		// recViaPath: n0 is the only target, and conforms only if the nodes that the path reaches from it,
		// two or more steps away, are evaluated as well. Each case exercises one rule for computing the
		// last edges of a path; the comments give the nodes the path reaches from each node.
		{
			name: "chain-via-inverse-path", // ^p: n0 → n1 → n2; the values are the subjects of p
			turtle: recViaPath(`[ sh:inversePath ex:p ]`) + `
			         ex:n1 ex:p ex:n0 . ex:n2 ex:p ex:n1 . ex:n2 a ex:A .`,
			invalid: "",
		},
		{
			name: "chain-via-sequence-path", // p/q: n0 → n1 → n2
			turtle: recViaPath(`( ex:p ex:q )`) + `
			         ex:n0 ex:p ex:m0 . ex:m0 ex:q ex:n1 . ex:n1 ex:p ex:m1 . ex:m1 ex:q ex:n2 . ex:n2 a ex:A .`,
			invalid: "",
		},
		{
			name: "chain-via-sequence-path-violated-at-the-end",
			turtle: recViaPath(`( ex:p ex:q )`) + `
			         ex:n0 ex:p ex:m0 . ex:m0 ex:q ex:n1 . ex:n1 ex:p ex:m1 . ex:m1 ex:q ex:n2 .`,
			invalid: "S={n0}", // n2 has neither class A nor values
		},
		{
			// ^(p/q) is ^q/^p: the values are the subjects of p's first edges, not the objects
			name: "chain-via-inverse-of-a-sequence", // n0 → n1 → n2
			turtle: recViaPath(`[ sh:inversePath ( ex:p ex:q ) ]`) + `
			         ex:n1 ex:p ex:m0 . ex:m0 ex:q ex:n0 . ex:n2 ex:p ex:m1 . ex:m1 ex:q ex:n1 . ex:n2 a ex:A .`,
			invalid: "",
		},
		{
			name: "chain-via-inverse-of-a-sequence-violated-at-the-end",
			turtle: recViaPath(`[ sh:inversePath ( ex:p ex:q ) ]`) + `
			         ex:n1 ex:p ex:m0 . ex:m0 ex:q ex:n0 . ex:n2 ex:p ex:m1 . ex:m1 ex:q ex:n1 .`,
			invalid: "S={n0}",
		},
		{
			// p/q*: when q* matches zero times, the last edge is p, so p's objects are values too
			name: "chain-via-sequence-ending-in-a-nullable-path", // n0 → {n1}, n1 → {n2, n3}
			turtle: recViaPath(`( ex:p [ sh:zeroOrMorePath ex:q ] )`) + `
			         ex:n0 ex:p ex:n1 . ex:n1 ex:p ex:n2 . ex:n2 ex:q ex:n3 . ex:n2 a ex:A . ex:n3 a ex:A .`,
			invalid: "",
		},
		{
			name: "chain-via-alternative-path", // p|q: n0 → n1 (via p) → n2 (via q)
			turtle: recViaPath(`[ sh:alternativePath ( ex:p ex:q ) ]`) + `
			         ex:n0 ex:p ex:n1 . ex:n1 ex:q ex:n2 . ex:n2 a ex:A .`,
			invalid: "",
		},
		{
			// T's values via p? include its focus node itself, so U must be checked on every node T is
			// checked on, including T's indirect target n2 (reached from U via q):
			// T(n0) needs U(n0), U(n1); U(n1) needs T(n2); T(n2) needs U(n2)
			name: "mutual-recursion-via-a-nullable-path",
			turtle: `ex:T a sh:NodeShape ; sh:targetNode ex:n0 ;
			           sh:property [ sh:path [ sh:zeroOrOnePath ex:p ] ; sh:node ex:U ] .
			         ex:U a sh:NodeShape ;
			           sh:or ( [ sh:class ex:A ] [ sh:property [ sh:path ex:q ; sh:minCount 1 ; sh:node ex:T ] ] ) .
			         ex:n0 a ex:A . ex:n0 ex:p ex:n1 . ex:n1 ex:q ex:n2 . ex:n2 a ex:A .`,
			invalid: "",
		},
		{
			name: "mutual-recursion-via-a-nullable-path-violated-at-the-end",
			turtle: `ex:T a sh:NodeShape ; sh:targetNode ex:n0 ;
			           sh:property [ sh:path [ sh:zeroOrOnePath ex:p ] ; sh:node ex:U ] .
			         ex:U a sh:NodeShape ;
			           sh:or ( [ sh:class ex:A ] [ sh:property [ sh:path ex:q ; sh:minCount 1 ; sh:node ex:T ] ] ) .
			         ex:n0 a ex:A . ex:n0 ex:p ex:n1 . ex:n1 ex:q ex:n2 .`,
			invalid: "T={n0}", // U(n2) fails, so T(n2), U(n1) and T(n0) fail
		},
		{
			name:    "self-negation-is-undefined",
			turtle:  `ex:S a sh:NodeShape ; sh:targetNode ex:n0 ; sh:not ex:S .`,
			invalid: "S={n0}", // undefined, hence a violation
		},
		{
			name: "negation-through-a-property-cycle",
			turtle: `ex:S a sh:NodeShape ; sh:targetNode ex:n0 ; sh:property [ sh:path ex:p ; sh:not ex:S ] .
			         ex:n0 ex:p ex:n0 .`,
			invalid: "S={n0}", // undefined
		},
		{
			name: "even-negative-cycle",
			turtle: `ex:S1 a sh:NodeShape ; sh:targetNode ex:n0 ; sh:not ex:S2 .
			         ex:S2 a sh:NodeShape ; sh:targetNode ex:n0 ; sh:not ex:S1 .`,
			invalid: "S1={n0} S2={n0}", // both undefined
		},
		{
			name: "negation-of-a-stratified-recursive-shape",
			turtle: `ex:S a sh:NodeShape ; sh:property [ sh:path ex:p ; sh:node ex:S ] ; sh:class ex:A .
			         ex:N a sh:NodeShape ; sh:targetNode ex:n0, ex:n1, ex:n2 ; sh:not ex:S .
			         ex:n0 ex:p ex:n1 . ex:n1 ex:p ex:n2 .
			         ex:n0 a ex:A . ex:n1 a ex:A . ex:n2 a ex:A .`,
			invalid: "N={n0,n1,n2}",
		},
		{
			name: "recursion-through-or",
			turtle: `ex:S a sh:NodeShape ; sh:targetNode ex:n0, ex:n1, ex:n2, ex:n3 ;
			           sh:or ( [ sh:class ex:A ] [ sh:property [ sh:path ex:p ; sh:minCount 1 ; sh:node ex:S ] ] ) .
			         ex:n0 ex:p ex:n1 . ex:n1 ex:p ex:n2 . ex:n2 a ex:A . ex:n3 ex:p ex:n3 .`,
			invalid: "S={n3}",
		},
		{
			name: "qualified-min-through-recursion",
			turtle: `ex:S a sh:NodeShape ; sh:targetNode ex:n0, ex:n1, ex:n2 ;
			           sh:property [ sh:path ex:p ; sh:qualifiedValueShape ex:S ; sh:qualifiedMinCount 1 ] .
			         ex:n0 ex:p ex:n1 . ex:n1 ex:p ex:n2 .`,
			invalid: "S={n0,n1,n2}",
		},
		{
			name: "qualified-max-through-recursion",
			turtle: `ex:S a sh:NodeShape ; sh:targetNode ex:n0, ex:n1, ex:n2 ;
			           sh:property [ sh:path ex:p ; sh:qualifiedValueShape ex:S ; sh:qualifiedMinCount 0 ; sh:qualifiedMaxCount 0 ] .
			         ex:n0 ex:p ex:n1 . ex:n1 ex:p ex:n2 .`,
			invalid: "S={n1}", // n2 has no values (conforms), n1's value n2 conforms (violates), n0's value n1 does not
		},
		{
			name: "mutual-recursion",
			turtle: `ex:S1 a sh:NodeShape ; sh:targetNode ex:n0 ; sh:property [ sh:path ex:p ; sh:node ex:S2 ] .
			         ex:S2 a sh:NodeShape ; sh:targetNode ex:n1 ; sh:property [ sh:path ex:q ; sh:node ex:S1 ] ; sh:class ex:A .
			         ex:n0 ex:p ex:n1 . ex:n1 ex:q ex:n2 . ex:n1 a ex:A .`,
			invalid: "",
		},
		{
			name: "mutual-recursion-violated-at-the-end",
			turtle: `ex:S1 a sh:NodeShape ; sh:targetNode ex:n0 ; sh:property [ sh:path ex:p ; sh:node ex:S2 ] .
			         ex:S2 a sh:NodeShape ; sh:property [ sh:path ex:q ; sh:node ex:S1 ] ; sh:class ex:A .
			         ex:n0 ex:p ex:n1 . ex:n1 ex:q ex:n2 .`,
			invalid: "S1={n0}", // n1 lacks class A
		},
	}

	for i, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			graphName := fmt.Sprintf("<urn:recursion:%d>", i)
			g := loadTurtle(t, ep, graphName, recPrefixes+c.turtle)

			res, invalid, err := shawellInvalid(g, ep, graphName, false)
			if err != nil {
				t.Fatalf("panic: %v", err)
			}
			if got := describeInvalid(invalid); got != c.invalid {
				t.Errorf("invalid targets %q, expected %q", got, c.invalid)
			}
			if res != (c.invalid == "") {
				t.Errorf("verdict %v, expected %v", res, c.invalid == "")
			}

			report, err := shawellReport(g, ep, graphName, false)
			if err != nil {
				t.Fatalf("report: panic: %v", err)
			}
			for _, p := range checkReport(report, c.invalid == "") {
				t.Errorf("report: %s", p)
			}
		})
	}
}

// TestUndefinedShapeReferences covers known bug U: a shape that is only referenced, and has no triples
// of its own, is a shape without constraints, so every node conforms to it. Each case references the
// undefined ex:Undefined in a different way, and is validated by unwinding and through the logic program.
func TestUndefinedShapeReferences(t *testing.T) {
	ep := startTestOxigraph(t)

	cases := []struct {
		name, constraint, invalid string
	}{
		{"node", `sh:node ex:Undefined`, ""},
		{"not", `sh:not ex:Undefined`, "S={n0}"},
		{"or", `sh:or ( ex:Undefined ex:Other )`, ""},
		{"and", `sh:and ( ex:Undefined )`, ""},
		{"xone", `sh:xone ( ex:Undefined )`, ""},
		{"node-in-property", `sh:property [ sh:path ex:p ; sh:node ex:Undefined ]`, ""},
		{"qualified", `sh:property [ sh:path ex:p ; sh:qualifiedValueShape ex:Undefined ; sh:qualifiedMinCount 1 ]`, ""},
		{"qualified-max", `sh:property [ sh:path ex:p ; sh:qualifiedValueShape ex:Undefined ; sh:qualifiedMinCount 0 ; sh:qualifiedMaxCount 0 ]`, "S={n0}"},
	}

	for i, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			turtle := recPrefixes + `
ex:S a sh:NodeShape ; sh:targetNode ex:n0 ; ` + c.constraint + ` .
ex:Other a sh:NodeShape ; sh:class ex:A .
ex:n0 ex:p ex:n1 .
`
			graphName := fmt.Sprintf("<urn:undefined-shape:%d>", i)
			g := loadTurtle(t, ep, graphName, turtle)

			for _, forceLP := range []bool{false, true} {
				res, invalid, err := shawellInvalid(g, ep, graphName, forceLP)
				if err != nil {
					t.Fatalf("forceLP=%v: panic: %v", forceLP, err)
				}
				if got := describeInvalid(invalid); got != c.invalid || res != (c.invalid == "") {
					t.Errorf("forceLP=%v: verdict %v with invalid targets %q, expected %q", forceLP, res, got, c.invalid)
				}

				report, err := shawellReport(g, ep, graphName, forceLP)
				if err != nil {
					t.Fatalf("forceLP=%v report: panic: %v", forceLP, err)
				}
				for _, p := range checkReport(report, c.invalid == "") {
					t.Errorf("forceLP=%v report: %s", forceLP, p)
				}
			}
		})
	}
}

// TestUndefinedMembershipInReports covers known bug V: under the well-founded semantics, the membership
// of a target can be undefined (here through cycles with sh:not). A target conforms only if its
// membership is true, so an undefined one is a violation, and the validation report has to say so too:
// each constraint must count as violated unless it is definitely satisfied, both for constraints that
// require a node to be in a shape (sh:node, sh:and, sh:or, sh:xone, sh:qualifiedMinCount) and for those
// that require it not to be (sh:not, sh:qualifiedMaxCount). The first cases are the inputs of the sheval
// tests (the "Common Foundations for Recursive Shape Languages" suite) that crashed; the others reach
// an undefined membership through each kind of shape reference. All memberships here are undefined.
func TestUndefinedMembershipInReports(t *testing.T) {
	ep := startTestOxigraph(t)

	cases := []struct{ name, turtle, invalid string }{
		{"sheval-cons1", `ex:S a sh:NodeShape ; sh:targetNode ex:a ;
		    sh:property [ sh:path ex:p ; sh:qualifiedMinCount 1 ; sh:qualifiedValueShape ex:S1 ] .
		  ex:S1 a sh:NodeShape ; sh:not ex:S ; sh:targetNode ex:a .
		  ex:a ex:p ex:a .`, "S1={a} S={a}"},
		{"sheval-cons2", `ex:S a sh:NodeShape ; sh:targetNode ex:a, ex:b ;
		    sh:property [ sh:path ex:p ; sh:qualifiedMinCount 1 ; sh:qualifiedValueShape ex:S1 ] .
		  ex:S1 a sh:NodeShape ; sh:not ex:S ; sh:targetNode ex:a, ex:b .
		  ex:a ex:p ex:b . ex:b ex:p ex:a .`, "S1={a,b} S={a,b}"},
		{"sheval-nstrat2", `ex:S a sh:NodeShape ; sh:targetNode ex:a, ex:b ;
		    sh:property [ sh:path ex:p ; sh:qualifiedMinCount 1 ; sh:qualifiedValueShape [ sh:not [ sh:node ex:S ] ] ] .
		  ex:a ex:p ex:b . ex:b ex:p ex:a .`, "S={a,b}"},
		{"sheval-example4", `ex:S a sh:NodeShape ; sh:targetNode ex:a, ex:b ;
		    sh:property [ sh:path ex:p ; sh:qualifiedMinCount 1 ; sh:qualifiedValueShape [ sh:not [ sh:node ex:S ] ] ] .
		  ex:a ex:p ex:b . ex:b ex:p ex:a ; ex:q "d" .`, "S={a,b}"},
		{"node", `ex:S a sh:NodeShape ; sh:targetNode ex:a ; sh:node ex:T . ex:T a sh:NodeShape ; sh:not ex:S .`, "S={a}"},
		{"and", `ex:S a sh:NodeShape ; sh:targetNode ex:a ; sh:and ( ex:T ) . ex:T a sh:NodeShape ; sh:not ex:S .`, "S={a}"},
		{"or", `ex:S a sh:NodeShape ; sh:targetNode ex:a ; sh:or ( ex:T ) . ex:T a sh:NodeShape ; sh:not ex:S .`, "S={a}"},
		{"xone", `ex:S a sh:NodeShape ; sh:targetNode ex:a ; sh:xone ( ex:T ) . ex:T a sh:NodeShape ; sh:not ex:S .`, "S={a}"},
		{"node-in-property", `ex:S a sh:NodeShape ; sh:targetNode ex:a ; sh:property [ sh:path ex:p ; sh:node ex:T ] .
		  ex:T a sh:NodeShape ; sh:not ex:S . ex:a ex:p ex:a .`, "S={a}"},
		{"qualified-min", `ex:S a sh:NodeShape ; sh:targetNode ex:a ;
		    sh:property [ sh:path ex:p ; sh:qualifiedValueShape ex:T ; sh:qualifiedMinCount 1 ] .
		  ex:T a sh:NodeShape ; sh:not ex:S . ex:a ex:p ex:a .`, "S={a}"},
		// S(a) holds iff T(a) does not, and T(a) iff S(a) does not: an even cycle through negation
		{"qualified-max", `ex:S a sh:NodeShape ; sh:targetNode ex:a ;
		    sh:property [ sh:path ex:p ; sh:qualifiedValueShape ex:T ; sh:qualifiedMinCount 0 ; sh:qualifiedMaxCount 0 ] .
		  ex:T a sh:NodeShape ; sh:not ex:S . ex:a ex:p ex:a .`, "S={a}"},
		{"not", `ex:S a sh:NodeShape ; sh:targetNode ex:a ; sh:not ex:S .`, "S={a}"},
		{"not-in-property", `ex:S a sh:NodeShape ; sh:targetNode ex:a ; sh:property [ sh:path ex:p ; sh:not ex:S ] .
		  ex:a ex:p ex:a .`, "S={a}"},
		// xone with an undefined and a false shape: exactly one shape must be definitely true
		{"xone-with-a-false-shape", `ex:S a sh:NodeShape ; sh:targetNode ex:a ; sh:xone ( ex:T ex:F ) .
		  ex:T a sh:NodeShape ; sh:not ex:S . ex:F a sh:NodeShape ; sh:class ex:Missing .`, "S={a}"},
		// xone with an undefined and a true shape: the undefined one might be true too
		{"xone-with-a-true-shape", `ex:S a sh:NodeShape ; sh:targetNode ex:a ; sh:xone ( ex:T ex:Any ) .
		  ex:T a sh:NodeShape ; sh:not ex:S . ex:Any a sh:NodeShape .`, "S={a}"},
		{"xone-with-a-true-shape-in-property", `ex:S a sh:NodeShape ; sh:targetNode ex:a ;
		    sh:property [ sh:path ex:p ; sh:xone ( ex:T ex:Any ) ] .
		  ex:T a sh:NodeShape ; sh:not ex:S . ex:Any a sh:NodeShape . ex:a ex:p ex:a .`, "S={a}"},
		// or with an undefined and a true shape: the true one decides
		{"or-with-a-true-shape", `ex:S a sh:NodeShape ; sh:targetNode ex:a ; sh:or ( ex:T ex:Any ) ; sh:not ex:N .
		  ex:T a sh:NodeShape ; sh:not ex:S . ex:Any a sh:NodeShape . ex:N a sh:NodeShape ; sh:class ex:Missing .`, ""},
	}

	for i, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			graphName := fmt.Sprintf("<urn:undefined-membership:%d>", i)
			g := loadTurtle(t, ep, graphName, recPrefixes+c.turtle)

			res, invalid, err := shawellInvalid(g, ep, graphName, false)
			if err != nil {
				t.Fatalf("panic: %v", err)
			}
			if got := describeInvalid(invalid); got != c.invalid || res != (c.invalid == "") {
				t.Errorf("verdict %v with invalid targets %q, expected %q", res, got, c.invalid)
			}

			report, err := shawellReport(g, ep, graphName, false)
			if err != nil {
				t.Fatalf("report: panic: %v", err)
			}
			for _, p := range checkReport(report, c.invalid == "") {
				t.Errorf("report: %s", p)
			}

			// every invalid target must have a result in the report
			reported := map[string]bool{}
			for _, r := range report.results {
				reported[strings.TrimPrefix(r.focusNode.RawValue(), fzNS)] = true
			}
			for _, nodes := range invalid {
				for n := range nodes {
					if !reported[n] {
						t.Errorf("invalid target %s has no result in the report", n)
					}
				}
			}
		})
	}
}
