package main

import (
	"encoding/json"
	"fmt"
	"math/rand"
	"os"
	"os/exec"
	"slices"
	"strconv"
	"strings"
	"testing"

	rdf "github.com/cem-okulmus/rdf2go-1"
)

// A solver-independent oracle for the stable model and well-founded semantics of SHACL (phase 5 of
// stable_semantics_plan.md), on the random documents of differential_test.go.
//
// An assignment is a set of atoms "node n conforms to shape i", over the stable domain of phase 3: the nodes of
// the data graph and the constants of the shapes. The constraints are those of fzRef, with every reference to a
// shape resolved by polarity (fzRef.member), following the normal form of Andreşel et al. (WWW20): sh:node,
// sh:and, sh:or and the chosen member of sh:xone occur positively, sh:not and the other members of sh:xone
// negatively, and a qualified value shape positively in its lower bound and negatively in its upper bound (its
// disjoint siblings the other way round).
//
// gamma(A) is the least fixpoint of the immediate consequence operator in which positive occurrences read the
// current iterate and negative occurrences read A. A is a stable model iff gamma(A) = A. The well-founded model
// is the alternating fixpoint of gamma: its true atoms are the least fixpoint of gamma∘gamma, and its true or
// undefined atoms are gamma of those. Every stable model lies between the two, so stable models are found by
// trying every assignment of the undefined atoms.
//
// Evaluating a constraint with pos and neg set to the lower and upper bound of a three-valued assignment gives
// its definite truth, and with the bounds swapped its possible truth, so the same evaluator also gives the
// three-valued semantics of WWW20 Table 3 that section 8 needs.

// fzAtom is the atom "node conforms to shape".
type fzAtom struct {
	shape int
	node  string
}

// fzInterp is a set of atoms.
type fzInterp map[fzAtom]bool

func (a fzInterp) equal(b fzInterp) bool {
	if len(a) != len(b) {
		return false
	}
	for k := range a {
		if !b[k] {
			return false
		}
	}
	return true
}

func (a fzInterp) subset(b fzInterp) bool {
	for k := range a {
		if !b[k] {
			return false
		}
	}
	return true
}

// fzSmallUniverse keeps recursive documents small enough to enumerate their stable models. Its constants are in
// the stable domain only as constants of the shapes (Const(C) of phase 3).
var fzSmallUniverse = fzUniverse{
	iris:      []string{"n0", "n1", "n2"},
	blanks:    []string{"b0"},
	literals:  []string{"la", "lb", "l5"},
	classes:   []string{"A"},
	constants: []string{"n9", "lc"},
}

// fzGenRecursiveDoc generates a document whose shapes may reference each other in cycles, also through negation.
func fzGenRecursiveDoc(r *rand.Rand) fzDoc { return fzGen{u: fzSmallUniverse, recursive: true}.doc(r) }

// fzOracle computes the semantics of one document.
type fzOracle struct {
	doc    fzDoc
	domain []string
	atoms  []fzAtom
}

func newFzOracle(d fzDoc) *fzOracle {
	o := &fzOracle{doc: d, domain: d.stableDomain()}
	for i := range d.shapes {
		for _, n := range o.domain {
			o.atoms = append(o.atoms, fzAtom{i, n})
		}
	}
	return o
}

// stableDomain returns the nodes that the stable modes ground the shapes on (phase 3 of the plan): the subjects
// and objects of the data, including the classes of rdf:type triples, and the constants of the shapes, which
// are the values of sh:hasValue, sh:in, sh:class, sh:targetNode and sh:targetClass.
func (d fzDoc) stableDomain() []string {
	seen := map[string]bool{}
	var out []string
	add := func(n string) {
		if !seen[n] {
			seen[n] = true
			out = append(out, n)
		}
	}
	for _, p := range fzPreds {
		for _, e := range d.edges[p] {
			add(e[0])
			add(e[1])
		}
	}
	for _, n := range d.universe.iris {
		for _, c := range d.types[n] {
			add(n)
			add(c)
		}
	}
	var constants func(cons []fzCons)
	constants = func(cons []fzCons) {
		for _, c := range cons {
			switch c.kind {
			case "hasValue":
				add(c.value)
			case "in":
				for _, n := range c.list {
					add(n)
				}
			case "class":
				add(c.class)
			case "property":
				constants(c.prop.cons)
			}
		}
	}
	for _, s := range d.shapes {
		for _, n := range s.targetNodes {
			add(n)
		}
		if s.targetClass != "" {
			add(s.targetClass)
		}
		constants(s.cons)
	}
	slices.Sort(out)
	return out
}

// hasData says whether the document has any data triple. Without one, shawell loses the targets (known bug W).
func (d fzDoc) hasData() bool {
	for _, p := range fzPreds {
		if len(d.edges[p]) > 0 {
			return true
		}
	}
	for _, n := range d.universe.iris {
		if len(d.types[n]) > 0 {
			return true
		}
	}
	return false
}

// targetAtoms returns the atoms that validation needs: every shape at each of its targets.
func (d fzDoc) targetAtoms() []fzAtom {
	var out []fzAtom
	for i, s := range d.shapes {
		targets := map[string]bool{}
		for _, t := range s.targetNodes {
			targets[t] = true
		}
		if s.targetClass != "" {
			for _, n := range d.universe.iris {
				if slices.Contains(d.types[n], s.targetClass) {
					targets[n] = true
				}
			}
		}
		for t := range targets {
			out = append(out, fzAtom{i, t})
		}
	}
	return out
}

// lfp returns the least fixpoint of the immediate consequence operator with negative occurrences read from neg.
// If bound is not nil, it stops as soon as it derives an atom outside bound, and then returns false.
func (o *fzOracle) lfp(neg, bound fzInterp) (fzInterp, bool) {
	I := fzInterp{}
	ref := &fzRef{doc: o.doc, pos: I, neg: neg}
	for changed := true; changed; {
		changed = false
		for _, a := range o.atoms {
			if I[a] || !ref.allHold(a.node, o.doc.shapes[a.shape].cons) {
				continue
			}
			if bound != nil && !bound[a] {
				return I, false
			}
			I[a] = true
			changed = true
		}
	}
	return I, true
}

// wellFounded returns the true atoms and the true or undefined atoms of the well-founded model.
func (o *fzOracle) wellFounded() (trueAtoms, possible fzInterp) {
	T := fzInterp{}
	for {
		U, _ := o.lfp(T, nil)
		T2, _ := o.lfp(U, nil)
		if T2.equal(T) {
			return T, U
		}
		T = T2
	}
}

// isStable says whether A is a stable model, that is, whether gamma(A) = A.
func (o *fzOracle) isStable(A fzInterp) bool {
	I, ok := o.lfp(A, A)
	return ok && len(I) == len(A)
}

// fzMaxUndefined bounds the number of undefined atoms whose assignments stableModels tries.
const fzMaxUndefined = 14

// stableModels returns the stable models, trying every assignment of the atoms that are undefined in the
// well-founded model. It returns false if there are more than fzMaxUndefined of them.
func (o *fzOracle) stableModels(T, U fzInterp) ([]fzInterp, bool) {
	var undefined []fzAtom
	for _, a := range o.atoms {
		if U[a] && !T[a] {
			undefined = append(undefined, a)
		}
	}
	if len(undefined) > fzMaxUndefined {
		return nil, false
	}
	return o.enumerate(T, undefined), true
}

// enumerate returns the stable models among the assignments that hold base and any subset of free.
func (o *fzOracle) enumerate(base fzInterp, free []fzAtom) []fzInterp {
	var models []fzInterp
	for mask := 0; mask < 1<<len(free); mask++ {
		A := fzInterp{}
		for a := range base {
			A[a] = true
		}
		for k, a := range free {
			if mask&(1<<k) != 0 {
				A[a] = true
			}
		}
		if o.isStable(A) {
			models = append(models, A)
		}
	}
	return models
}

// fzVerdicts are the statuses the oracle expects from shawell.
type fzVerdicts struct {
	wf, brave, cautious ValidationStatus
}

func fzStableVerdicts(models []fzInterp, targets []fzAtom) (brave, cautious ValidationStatus) {
	if len(models) == 0 {
		return NoModel, NoModel
	}
	brave, cautious = Invalid, Valid
	for _, m := range models {
		all := true
		for _, t := range targets {
			all = all && m[t]
		}
		if all {
			brave = Valid
		} else {
			cautious = Invalid
		}
	}
	return brave, cautious
}

// wfInvalid returns, per shape name, the targets that are not true in the well-founded model.
func wfInvalid(T fzInterp, targets []fzAtom) map[string]map[string]bool {
	out := map[string]map[string]bool{}
	for _, t := range targets {
		if !T[t] {
			name := fzShapeName(t.shape)
			if out[name] == nil {
				out[name] = map[string]bool{}
			}
			out[name][t.node] = true
		}
	}
	return out
}

// stratified says whether no cycle of shape references contains a negative occurrence (see the polarity rules
// above). sh:xone and qualified value shapes with an upper bound or disjoint siblings count as negative.
func (d fzDoc) stratified() bool {
	n := len(d.shapes)
	reach := make([][]bool, n) // reach[i][j]: shape i depends on shape j
	negative := make([][]bool, n)
	for i := range reach {
		reach[i], negative[i] = make([]bool, n), make([]bool, n)
	}
	var walk func(i int, cons []fzCons)
	walk = func(i int, cons []fzCons) {
		for _, c := range cons {
			for _, ref := range c.refs {
				reach[i][ref] = true
				if c.kind == "not" || c.kind == "xone" {
					negative[i][ref] = true
				}
			}
			if c.kind != "property" {
				continue
			}
			walk(i, c.prop.cons)
			if q := c.prop.qual; q != nil {
				reach[i][q.ref] = true
				if q.max >= 0 {
					negative[i][q.ref] = true
				}
				if q.disjoint { // the siblings occur negatively in the lower bound
					for _, s := range cons {
						if s.kind == "property" && s.prop.qual != nil {
							reach[i][s.prop.qual.ref] = true
							negative[i][s.prop.qual.ref] = true
						}
					}
				}
			}
		}
	}
	for i, s := range d.shapes {
		walk(i, s.cons)
	}
	// transitive closure (Floyd–Warshall), then look for a negative edge i→j with j reaching back to i
	closure := make([][]bool, n)
	for i := range closure {
		closure[i] = slices.Clone(reach[i])
	}
	for k := 0; k < n; k++ {
		for i := 0; i < n; i++ {
			for j := 0; j < n; j++ {
				closure[i][j] = closure[i][j] || (closure[i][k] && closure[k][j])
			}
		}
	}
	for i := 0; i < n; i++ {
		for j := 0; j < n; j++ {
			if negative[i][j] && (i == j || closure[j][i]) {
				return false
			}
		}
	}
	return true
}

// TestStableOracleAppendixB checks the oracle against the measured "Stable models", "Brave" and "Cautious"
// columns of Appendix B. The anonymous shapes of the Appendix B documents are named shapes here (S3 and up);
// they occur only positively, so this does not change the stable models. :a, :b and :z are n0, n1 and n2.
func TestStableOracleAppendixB(t *testing.T) {
	u := fzUniverse{iris: []string{"n0", "n1", "n2"}}
	q := map[string][][2]string{"q": {{"n0", "n1"}}} // :a :q :b
	not := func(i int) fzCons { return fzCons{kind: "not", refs: []int{i}} }
	or := func(refs ...int) fzCons { return fzCons{kind: "or", refs: refs} }
	hasValue := func(n string) fzCons { return fzCons{kind: "hasValue", value: n} }
	target := func(cons ...fzCons) fzShape { return fzShape{cons: cons, targetNodes: []string{"n0"}} }
	plain := func(cons ...fzCons) fzShape { return fzShape{cons: cons} }

	cases := []struct {
		name            string
		edges           map[string][][2]string
		shapes          []fzShape
		models          int
		brave, cautious ValidationStatus
	}{
		{"cx1", q, []fzShape{target(), plain(not(1))}, 0, NoModel, NoModel},
		{"cx2", q, []fzShape{target(or(1, 2)), plain(hasValue("n0")), plain(not(0))}, 0, NoModel, NoModel},
		{"cx3", q, []fzShape{target(not(1)), plain(not(0))}, 4, Valid, Invalid},
		{"cx4", q, []fzShape{plain(not(1)), plain(not(0)), target(or(0, 1))}, 4, Valid, Valid},
		{"cx5", q, []fzShape{target(not(1)), target(not(0))}, 4, Invalid, Invalid},
		{"cx6", q, []fzShape{plain(not(1)), target(not(0)), plain(or(3, 4)), plain(not(2)), plain(not(0))}, 1, Valid, Valid},
		{"cx7", map[string][][2]string{"p": {{"n0", "n0"}}}, []fzShape{target(or(1, 2)),
			plain(fzCons{kind: "property", prop: &fzProp{pred: "p", minCount: 1, maxCount: -1}}), plain(not(0))}, 1, Valid, Valid},
		{"cx8", q, []fzShape{target(or(2, 3, 4)), plain(hasValue("n2")), plain(hasValue("n0")), plain(hasValue("n1")), plain(not(0))},
			0, NoModel, NoModel},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			doc := fzDoc{shapes: c.shapes, edges: c.edges, types: map[string][]string{}, universe: u}
			o := newFzOracle(doc)
			T, U := o.wellFounded()
			models, ok := o.stableModels(T, U)
			if !ok {
				t.Fatal("too many undefined atoms")
			}
			brave, cautious := fzStableVerdicts(models, doc.targetAtoms())
			if len(models) != c.models || brave != c.brave || cautious != c.cautious {
				t.Errorf("got %d models, brave %v, cautious %v; want %d, %v, %v",
					len(models), brave, cautious, c.models, c.brave, c.cautious)
			}
		})
	}
}

// lpModels returns the stable models of a program as sorted lists of atoms, from DLV (-n=0) and from clingo
// (-n0), each model in canonical form.
func lpModels(t *testing.T, clingo []string, program string) (fromDLV, fromClingo []string) {
	t.Helper()
	dlvCmd := exec.Command(dlv, "-n=0")
	dlvCmd.Stdin = strings.NewReader(program)
	out, err := dlvCmd.CombinedOutput()
	if err != nil {
		t.Fatalf("DLV failed: %v\n%s\nprogram:\n%s", err, out, program)
	}
	for _, line := range strings.Split(string(out), "\n") {
		if strings.HasPrefix(line, "{") {
			var atoms []string
			for a := range parseDLVSet("M: "+line, "M") {
				atoms = append(atoms, a)
			}
			slices.Sort(atoms)
			fromDLV = append(fromDLV, strings.Join(atoms, " "))
		}
	}

	clingoCmd := exec.Command(clingo[0], append(clingo[1:], "--outf=2", "--warn=none", "-n0")...)
	clingoCmd.Stdin = strings.NewReader(program)
	var stderr strings.Builder
	clingoCmd.Stderr = &stderr
	stdout, _ := clingoCmd.Output() // a native clingo exits with 10, 20 or 30 on success
	var parsed struct {
		Call []struct {
			Witnesses []struct{ Value []string }
		}
		Result string
	}
	if err := json.Unmarshal(stdout, &parsed); err != nil || parsed.Result == "UNKNOWN" {
		t.Fatalf("clingo failed: %v\nstdout:\n%s\nstderr:\n%s\nprogram:\n%s", err, stdout, stderr.String(), program)
	}
	for _, call := range parsed.Call {
		for _, w := range call.Witnesses {
			atoms := slices.Clone(w.Value)
			slices.Sort(atoms)
			fromClingo = append(fromClingo, strings.Join(atoms, " "))
		}
	}
	slices.Sort(fromDLV)
	slices.Sort(fromClingo)
	return fromDLV, fromClingo
}

// fzRunShawell validates the document whose data is in graphName with the given semantics, and returns the
// report, or the recovered panic.
func fzRunShawell(shapes *rdf.Graph, ep *SparqlEndpoint, graphName string, semantics Semantics, forceLP bool) (report *ValidationReport, err any) {
	defer func() { err = recover() }()
	doc := GetShaclDocument(shapes, graphName, false, semantics)
	activeDoc = &doc
	return answerShacl(ep, doc, config{silent: true, forceLP: forceLP, semantics: semantics}), nil
}

// fzStableLP returns the logic program that the stable modes solve for the document, the predicate of each
// named shape (S0, S1, …), and the constants of the program with the terms they stand for. A panic is returned
// as err.
func fzStableLP(shapes *rdf.Graph, ep *SparqlEndpoint, graphName string) (program string, predicates map[string]int,
	constants map[string]rdf.Term, err any) {
	defer func() { err = recover() }()
	renameMap = make(map[rdf.Term]string)
	reverseMap = make(map[string]rdf.Term)
	doc := GetShaclDocument(shapes, graphName, false, StableBrave{})
	activeDoc = &doc
	doc.AllCondAnswers(ep)
	program = doc.GetAllLPs().String()

	predicates = map[string]int{}
	for iri, shape := range doc.shapeNames {
		if name, ok := strings.CutPrefix(iri, fzNS+"S"); ok {
			if i, err := strconv.Atoi(name); err == nil {
				predicates[shape.GetLogName()] = i
			}
		}
	}
	constants = map[string]rdf.Term{}
	for c, term := range reverseMap {
		constants[c] = term
	}
	return program, predicates, constants, nil
}

// fzNodeOf returns the generator's name for a term returned by the endpoint, or false. Blank nodes are named by
// blanks, which maps the endpoint's labels to the generator's names.
func fzNodeOf(term rdf.Term, blanks map[string]string) (string, bool) {
	switch v := term.(type) {
	case rdf.Resource:
		return strings.CutPrefix(v.URI, fzNS)
	case rdf.BlankNode:
		n, ok := blanks[v.ID]
		return n, ok
	case rdf.Literal:
		datatype := _xsd + "string"
		if v.Datatype != nil {
			datatype = v.Datatype.RawValue()
		}
		if v.Language != "" {
			datatype = _rdf + "langString"
		}
		for name, lit := range fzLiteralValue {
			if lit[0] == v.Value && lit[1] == v.Language && lit[2] == datatype {
				return name, true
			}
		}
	}
	return "", false
}

// fzBlankMappings returns every injective mapping from the blank nodes of the program to the blank nodes of the
// stable domain. The program names only the blank nodes it has rules for, and the labels come from the endpoint,
// so the test cannot tell which is which; with at most two blank nodes, it tries every way.
func fzBlankMappings(constants map[string]rdf.Term, doc fzDoc) []map[string]string {
	var labels []string
	for _, term := range constants {
		if b, ok := term.(rdf.BlankNode); ok && !slices.Contains(labels, b.ID) {
			labels = append(labels, b.ID)
		}
	}
	var names []string
	for _, n := range doc.stableDomain() {
		if fzIsBlank(n) {
			names = append(names, n)
		}
	}
	if len(labels) > len(names) {
		return nil
	}
	var out []map[string]string
	var permute func(k int, used []bool, current map[string]string)
	permute = func(k int, used []bool, current map[string]string) {
		if k == len(labels) {
			m := map[string]string{}
			for l, n := range current {
				m[l] = n
			}
			out = append(out, m)
			return
		}
		for i, n := range names {
			if !used[i] {
				used[i] = true
				current[labels[k]] = n
				permute(k+1, used, current)
				delete(current, labels[k])
				used[i] = false
			}
		}
	}
	permute(0, make([]bool, len(names)), map[string]string{})
	return out
}

// fzProject maps stable models of shawell's program, as lists of atoms, to the oracle's atoms "Si@node", keeping
// only the atoms of named shapes. It returns false if a constant does not map to a node of the document.
func fzProject(models []string, predicates map[string]int, constants map[string]rdf.Term, blanks map[string]string) ([]string, bool) {
	var out []string
	for _, m := range models {
		var atoms []string
		for _, a := range strings.Fields(m) {
			pred, arg, ok := strings.Cut(strings.TrimSuffix(a, ")"), "(")
			i, named := predicates[pred]
			if !ok || !named {
				continue
			}
			node, ok := fzNodeOf(constants[arg], blanks)
			if !ok {
				return nil, false
			}
			atoms = append(atoms, fmt.Sprint(fzShapeName(i), "@", node))
		}
		slices.Sort(atoms)
		out = append(out, strings.Join(atoms, " "))
	}
	slices.Sort(out)
	return out, true
}

// fzDescribeModels writes the oracle's models in the form of fzProject.
func fzDescribeModels(models []fzInterp) []string {
	var out []string
	for _, m := range models {
		var atoms []string
		for a := range m {
			atoms = append(atoms, fmt.Sprint(fzShapeName(a.shape), "@", a.node))
		}
		slices.Sort(atoms)
		out = append(out, strings.Join(atoms, " "))
	}
	slices.Sort(out)
	return out
}

// TestDifferentialStable compares shawell in all three modes with the oracle, on random documents that may be
// recursive (fzGenRecursiveDoc) and on the non-recursive ones of TestDifferentialValidation. Per document it
// checks (phase 5 of the plan):
//   - step 2: the well-founded verdict and invalid targets, and the brave and cautious verdicts, each with and
//     without forceLP, and that each report is consistent with its verdict and valid Turtle;
//   - step 3: that the well-founded model bounds every stable model (against a brute force over all atoms, on
//     documents small enough), that a total well-founded model gives exactly one stable model, and that a
//     stratified document has the same verdict in all three modes;
//   - step 4: that clingo and DLV find the same stable models of shawell's program, and as many as the oracle.
//
// Data and shapes go into separate graphs, as without --dataIncluded. Set SHAWELL_FUZZ=<n> to run more seeds.
func TestDifferentialStable(t *testing.T) {
	ep := startTestOxigraph(t)
	clingo, err := findClingo("")
	if err != nil {
		t.Skip("clingo not available:", err)
	}
	clingoCmd = clingo

	runs := 40
	if n, err := strconv.Atoi(os.Getenv("SHAWELL_FUZZ")); err == nil && n > 0 {
		runs = n
	}

	var skippedEnumeration, skippedNoData, recursiveDocs, stratifiedRecursive int
	for seed := 1; seed <= runs; seed++ {
		for _, kind := range []string{"recursive", "non-recursive"} {
			t.Run(fmt.Sprint(kind, "/seed", seed), func(t *testing.T) {
				var doc fzDoc
				if kind == "recursive" {
					doc = fzGenRecursiveDoc(rand.New(rand.NewSource(int64(seed))))
				} else {
					doc = fzGenDoc(rand.New(rand.NewSource(int64(seed))))
				}
				if !doc.hasData() {
					skippedNoData++
					return
				}
				problems := checkStableDoc(t, ep, clingo, doc, fmt.Sprintf("<urn:stable-fuzz:%s:%d>", kind, seed),
					&skippedEnumeration)
				if kind == "recursive" && !doc.stratified() {
					recursiveDocs++
				} else if kind == "recursive" {
					stratifiedRecursive++
				}
				if len(problems) > 0 {
					t.Errorf("%s\n\tshapes:\n%s\n\tdata:\n%s", strings.Join(problems, "\n\t"),
						doc.shapesBody(), doc.dataBody())
				}
			})
		}
	}
	t.Logf("%d seeds: %d recursive documents with a cycle through negation, %d stratified; stable models not "+
		"enumerated for %d documents (more than %d undefined atoms); %d documents without data skipped (bug W)",
		runs, recursiveDocs, stratifiedRecursive, skippedEnumeration, fzMaxUndefined, skippedNoData)
}

// checkStableDoc runs the checks of TestDifferentialStable on one document and returns the problems found.
func checkStableDoc(t *testing.T, ep *SparqlEndpoint, clingo []string, doc fzDoc, graphName string, skipped *int) []string {
	t.Helper()
	data := loadTurtle(t, ep, graphName, doc.dataTurtle())
	_ = data
	shapes := rdf.NewGraph(_sh)
	if err := shapes.Parse(strings.NewReader(doc.shapesTurtle()), "text/turtle"); err != nil {
		t.Fatalf("parsing shapes: %v\n%s", err, doc.shapesTurtle())
	}

	o := newFzOracle(doc)
	T, U := o.wellFounded()
	targets := doc.targetAtoms()
	var problems []string

	// the oracle itself (step 3)
	models, enumerated := o.stableModels(T, U)
	if !enumerated {
		*skipped++
	}
	if enumerated && len(o.atoms) <= 16 {
		all := o.enumerate(fzInterp{}, o.atoms)
		if len(all) != len(models) {
			problems = append(problems, fmt.Sprintf("oracle: %d stable models by brute force, %d from the well-founded model",
				len(all), len(models)))
		}
		for _, m := range all {
			if !T.subset(m) || !m.subset(U) {
				problems = append(problems, "oracle: a stable model outside the bounds of the well-founded model")
			}
		}
	}
	total := len(T) == len(U)
	if total && enumerated && len(models) != 1 {
		problems = append(problems, fmt.Sprintf("oracle: total well-founded model but %d stable models", len(models)))
	}
	if doc.stratified() && !total {
		problems = append(problems, "oracle: stratified document with a partial well-founded model")
	}

	// well-founded (step 2)
	wantInvalid := wfInvalid(T, targets)
	want := fzVerdicts{wf: Valid}
	if len(wantInvalid) > 0 {
		want.wf = Invalid
	}
	for _, forceLP := range []bool{false, true} {
		path := map[bool]string{false: "", true: " with forceLP"}[forceLP]
		_, invalid, err := shawellInvalid(shapes, ep, graphName, forceLP)
		if err != nil {
			problems = append(problems, fmt.Sprintf("well-founded%s: panic: %v", path, err))
		} else if describeInvalid(invalid) != describeInvalid(wantInvalid) {
			problems = append(problems, fmt.Sprintf("well-founded%s: invalid targets %s, expected %s",
				path, describeInvalid(invalid), describeInvalid(wantInvalid)))
		}
	}

	// stable modes (step 2), and stratified documents (step 3)
	semantics := []Semantics{WellFounded{}}
	if enumerated {
		want.brave, want.cautious = fzStableVerdicts(models, targets)
		semantics = append(semantics, StableBrave{}, StableCautious{})
		if doc.stratified() && (want.brave != want.wf || want.cautious != want.wf) {
			problems = append(problems, fmt.Sprintf("oracle: stratified document with verdicts %v (wf), %v (brave), %v (cautious)",
				want.wf, want.brave, want.cautious))
		}
	}
	for _, sem := range semantics {
		expected := map[Semantics]ValidationStatus{WellFounded{}: want.wf, StableBrave{}: want.brave, StableCautious{}: want.cautious}[sem]
		for _, forceLP := range []bool{false, true} {
			path := sem.String() + map[bool]string{false: "", true: " with forceLP"}[forceLP]
			report, err := fzRunShawell(shapes, ep, graphName, sem, forceLP)
			if err != nil {
				problems = append(problems, fmt.Sprintf("%s: panic: %v", path, err))
				continue
			}
			if report.status != expected {
				problems = append(problems, fmt.Sprintf("%s: status %v, expected %v", path, report.status, expected))
			}
			for _, p := range checkReport(report, expected == Valid) {
				problems = append(problems, path+" report: "+p)
			}
		}
	}

	// clingo against DLV, and both against the oracle (step 4). Projected onto the named shapes, the stable
	// models of shawell's program must be exactly the oracle's: this also compares the domains.
	if enumerated {
		program, predicates, constants, err := fzStableLP(shapes, ep, graphName)
		if err != nil {
			problems = append(problems, fmt.Sprintf("stable logic program: panic: %v", err))
		} else {
			fromDLV, fromClingo := lpModels(t, clingo, program)
			if !slices.Equal(fromDLV, fromClingo) {
				problems = append(problems, fmt.Sprintf("DLV and clingo find different stable models (%d and %d)\nprogram:\n%s",
					len(fromDLV), len(fromClingo), program))
			}
			want := fzDescribeModels(models)
			matched := false
			got := []string{"(no mapping of the blank nodes)"}
			for _, blanks := range fzBlankMappings(constants, doc) {
				projected, ok := fzProject(fromClingo, predicates, constants, blanks)
				if ok && slices.Equal(projected, want) {
					matched = true
					break
				}
				got = projected
			}
			if !matched {
				problems = append(problems, fmt.Sprintf("the stable models of shawell's program differ from the oracle's"+
					"\n\t  shawell: %q\n\t  oracle:  %q\nprogram:\n%s", got, want, DecodedString(program)))
			}
		}
	}
	return problems
}

// TestDifferentialStablePolarity runs the checks of TestDifferentialStable on documents where the polarity of a
// shape reference decides the result, and which random documents seldom produce. In each, a reference that
// occurs negatively would be satisfied if it read the current iterate of the fixpoint instead of the candidate
// model, because the referenced shape is derived only later in the fixpoint.
func TestDifferentialStablePolarity(t *testing.T) {
	ep := startTestOxigraph(t)
	clingo, err := findClingo("")
	if err != nil {
		t.Skip("clingo not available:", err)
	}
	clingoCmd = clingo

	u := fzUniverse{iris: []string{"n0", "n1"}}
	edges := map[string][][2]string{"p": {{"n0", "n1"}}}
	hasValue := func(n string) fzCons { return fzCons{kind: "hasValue", value: n} }
	qual := func(q fzQual) fzCons {
		return fzCons{kind: "property", prop: &fzProp{pred: "p", minCount: -1, maxCount: -1, qual: &q}}
	}
	cases := []struct {
		name   string
		shapes []fzShape
	}{
		{
			// n1, the only value of n0, conforms to S1, so S0 fails at n0: the upper bound reads S1 negatively
			name: "qualifiedMaxCount",
			shapes: []fzShape{
				{targetNodes: []string{"n0"}, cons: []fzCons{qual(fzQual{ref: 1, min: 0, max: 0})}},
				{cons: []fzCons{hasValue("n1")}},
			},
		},
		{
			// n0 conforms to both S1 and S2, so the sh:xone of S0 fails at n0; S2 is derived one step after S1
			name: "xone",
			shapes: []fzShape{
				{targetNodes: []string{"n0"}, cons: []fzCons{{kind: "xone", refs: []int{1, 2}}}},
				{cons: []fzCons{hasValue("n0")}},
				{cons: []fzCons{{kind: "node", refs: []int{3}}}},
				{cons: []fzCons{hasValue("n0")}},
			},
		},
		{
			// n1 conforms to S1 and to the disjoint sibling S2, so it does not count for S1, and S0 fails at n0
			name: "qualifiedValueShapesDisjoint",
			shapes: []fzShape{
				{targetNodes: []string{"n0"}, cons: []fzCons{
					qual(fzQual{ref: 1, min: 1, max: -1, disjoint: true}),
					qual(fzQual{ref: 2, min: 0, max: -1, disjoint: true}),
				}},
				{cons: []fzCons{hasValue("n1")}},
				{cons: []fzCons{{kind: "node", refs: []int{3}}}},
				{cons: []fzCons{hasValue("n1")}},
			},
		},
	}
	var skipped int
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			doc := fzDoc{shapes: c.shapes, edges: edges, types: map[string][]string{}, universe: u}
			if brave, _ := fzStableVerdicts(newFzOracle(doc).mustModels(t), doc.targetAtoms()); brave != Invalid {
				t.Fatalf("the oracle says %v, but the document is invalid", brave)
			}
			if problems := checkStableDoc(t, ep, clingo, doc, "<urn:stable-polarity:"+c.name+">", &skipped); len(problems) > 0 {
				t.Errorf("%s\n\tshapes:\n%s", strings.Join(problems, "\n\t"), doc.shapesBody())
			}
		})
	}
}

// mustModels returns the stable models, and fails the test if there are too many undefined atoms.
func (o *fzOracle) mustModels(t *testing.T) []fzInterp {
	t.Helper()
	T, U := o.wellFounded()
	models, ok := o.stableModels(T, U)
	if !ok {
		t.Fatal("too many undefined atoms")
	}
	return models
}
