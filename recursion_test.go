package main

import (
	"fmt"
	"testing"
)

// Tests for recursive documents. Shawell evaluates them with the well-founded semantics, through the
// logic program: shape membership that is only supported by a positive cycle is false, membership
// that depends on its own negation is undefined, and an undefined membership is not a violation
// (see InvalidTargetLP). Each case lists the expected invalid targets per shape, and also checks
// that the validation report agrees with the verdict.

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
			invalid: "",
		},
		{
			name: "negation-through-a-property-cycle",
			turtle: `ex:S a sh:NodeShape ; sh:targetNode ex:n0 ; sh:property [ sh:path ex:p ; sh:not ex:S ] .
			         ex:n0 ex:p ex:n0 .`,
			invalid: "",
		},
		{
			name: "even-negative-cycle",
			turtle: `ex:S1 a sh:NodeShape ; sh:targetNode ex:n0 ; sh:not ex:S2 .
			         ex:S2 a sh:NodeShape ; sh:targetNode ex:n0 ; sh:not ex:S1 .`,
			invalid: "",
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
