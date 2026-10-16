package main

import "testing"

func TestRDFTurtleIsomorphic(t *testing.T) {
	const (
		sh  = "http://www.w3.org/ns/shacl#"
		xsd = "http://www.w3.org/2001/XMLSchema#"
		ex  = "http://example.org/"
	)

	cases := []struct {
		name string
		t1   string
		t2   string
		want bool
	}{
		{
			name: "identical ground triples",
			t1:   `<` + ex + `s> <` + ex + `p> <` + ex + `o> .`,
			t2:   `<` + ex + `s> <` + ex + `p> <` + ex + `o> .`,
			want: true,
		},
		{
			name: "single blank node — relabeled",
			t1:   `_:a <` + ex + `p> <` + ex + `o> .`,
			t2:   `_:b <` + ex + `p> <` + ex + `o> .`,
			want: true,
		},
		{
			name: "different predicate",
			t1:   `_:a <` + ex + `p1> <` + ex + `o> .`,
			t2:   `_:a <` + ex + `p2> <` + ex + `o> .`,
			want: false,
		},
		{
			name: "different object",
			t1:   `_:a <` + ex + `p> <` + ex + `o1> .`,
			t2:   `_:a <` + ex + `p> <` + ex + `o2> .`,
			want: false,
		},
		{
			name: "blank node chain — relabeled",
			t1:   `_:b1 <` + ex + `p> _:b2 . _:b2 <` + ex + `q> <` + ex + `o> .`,
			t2:   `_:x  <` + ex + `p> _:y  . _:y  <` + ex + `q> <` + ex + `o> .`,
			want: true,
		},
		{
			name: "chain with swapped predicates",
			t1:   `_:b1 <` + ex + `p> _:b2 . _:b2 <` + ex + `q> <` + ex + `o> .`,
			t2:   `_:x  <` + ex + `q> _:y  . _:y  <` + ex + `p> <` + ex + `o> .`,
			want: false,
		},
		{
			name: "two structurally identical blank nodes (ambiguous — backtracking required)",
			t1:   `_:a <` + ex + `p> <` + ex + `o> . _:b <` + ex + `p> <` + ex + `o> .`,
			t2:   `_:x <` + ex + `p> <` + ex + `o> . _:y <` + ex + `p> <` + ex + `o> .`,
			want: true,
		},
		{
			name: "missing triple",
			t1: `<` + ex + `s> <` + ex + `p> <` + ex + `o1> .
			     <` + ex + `s> <` + ex + `p> <` + ex + `o2> .`,
			t2:   `<` + ex + `s> <` + ex + `p> <` + ex + `o1> .`,
			want: false,
		},
		{
			name: "conforming SHACL validation report",
			t1:   `[ <` + sh + `conforms> "true"^^<` + xsd + `boolean> ] .`,
			t2:   `[ <` + sh + `conforms> "true"^^<` + xsd + `boolean> ] .`,
			want: true,
		},
		{
			name: "conforms true vs false",
			t1:   `[ <` + sh + `conforms> "true"^^<` + xsd + `boolean>  ] .`,
			t2:   `[ <` + sh + `conforms> "false"^^<` + xsd + `boolean> ] .`,
			want: false,
		},
		{
			// Matches the shape of a real (non-conforming) SHACL validation report.
			name: "non-conforming report with one result — relabeled blank nodes",
			t1: `_:report <` + sh + `conforms> "false"^^<` + xsd + `boolean> .
			     _:report <` + sh + `result>   _:vr .
			     _:vr <` + sh + `focusNode>               <` + ex + `node> .
			     _:vr <` + sh + `sourceConstraintComponent> <` + sh + `ClassConstraintComponent> .`,
			t2: `_:r <` + sh + `conforms> "false"^^<` + xsd + `boolean> .
			     _:r <` + sh + `result>   _:v .
			     _:v <` + sh + `focusNode>               <` + ex + `node> .
			     _:v <` + sh + `sourceConstraintComponent> <` + sh + `ClassConstraintComponent> .`,
			want: true,
		},
		{
			// Two results that differ only in focusNode must NOT be considered isomorphic
			// when the focusNodes are swapped.
			name: "two results with different focus nodes — not isomorphic when swapped",
			t1: `_:r <` + sh + `result> _:v1 .
			     _:r <` + sh + `result> _:v2 .
			     _:v1 <` + sh + `focusNode> <` + ex + `A> .
			     _:v2 <` + sh + `focusNode> <` + ex + `B> .`,
			t2: `_:r <` + sh + `result> _:v1 .
			     _:r <` + sh + `result> _:v2 .
			     _:v1 <` + sh + `focusNode> <` + ex + `B> .
			     _:v2 <` + sh + `focusNode> <` + ex + `A> .`,
			want: true, // both orderings of results are isomorphic (set semantics)
		},
		{
			name: "extra result in second graph",
			t1: `_:r <` + sh + `result> _:v1 .
			     _:v1 <` + sh + `focusNode> <` + ex + `A> .`,
			t2: `_:r <` + sh + `result> _:v1 .
			     _:r <` + sh + `result> _:v2 .
			     _:v1 <` + sh + `focusNode> <` + ex + `A> .
			     _:v2 <` + sh + `focusNode> <` + ex + `B> .`,
			want: false,
		},
	}

	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			got := rdfTurtleIsomorphic(tc.t1, tc.t2)
			if got != tc.want {
				t.Errorf("rdfTurtleIsomorphic() = %v, want %v", got, tc.want)
			}
		})
	}
}
