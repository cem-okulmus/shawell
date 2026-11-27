package main

import (
	"encoding/json"
	"errors"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"runtime"
	"slices"
	"sort"
	"strings"
	"testing"

	rdf "github.com/cem-okulmus/rdf2go-1"
)

func TestExpandRulesOrKeepsExistingRules(t *testing.T) {
	oldRenameMap, oldReverseMap := renameMap, reverseMap
	oldCount, oldOrVar := theCount, orVar
	defer func() {
		renameMap, reverseMap = oldRenameMap, oldReverseMap
		theCount, orVar = oldCount, oldOrVar
	}()

	renameMap = make(map[rdf.Term]string)
	reverseMap = make(map[string]rdf.Term)
	theCount = 0
	orVar = 1

	value := rdf.Resource{URI: "http://example.com/value"}
	rules := expandRules(
		[]rdf.Term{value},
		[]int{0, 1},
		[]dependency{
			{
				mode: and,
				name: []ShapeRef{{ref: &NodeShape{id: 1}}},
			},
			{
				mode: or,
				name: []ShapeRef{
					{ref: &NodeShape{id: 2}},
					{ref: &NodeShape{id: 3}},
				},
			},
		},
		"head",
		"focus",
	)

	var headRule *serialisedRule
	for i := range rules {
		if rules[i].head == "head(focus)" {
			headRule = &rules[i]
			break
		}
	}
	if headRule == nil {
		t.Fatalf("expected expanded rules to keep the primary head rule, got %#v", rules)
	}

	body := strings.Join(headRule.body, ",")
	if !strings.Contains(body, "shape1(") {
		t.Fatalf("expected primary rule to keep existing dependency body, got %q", body)
	}
	if !strings.Contains(body, "orShape1(") {
		t.Fatalf("expected primary rule to include or dependency body, got %q", body)
	}
}

// The tests below check expandRules semantically: for every possible assignment of which value
// nodes conform to which referenced shape (a "world"), the generated rules plus the matching facts
// are solved by DLV, and the derived head atom is compared with what the SHACL semantics demands.
// All worlds of one test case are solved in a single DLV run, each world using its own focus node
// and value nodes, mirroring how TableToLP expands many focus nodes into one program.

var depModeNames = map[depMode]string{
	and: "and", or: "or", xone: "xone", not: "not", qualified: "qualified", node: "node", property: "property",
}

// depSpec describes a dependency in terms of the ids of the shapes it references.
type depSpec struct {
	mode     depMode
	refs     []int
	min, max int // only for qualified; max == -1 means unbounded
	disjoint bool
	siblings []int // only for disjoint qualified: the sibling shapes, as GetShaclDocument computes them
}

func (d depSpec) String() string {
	var refs []string
	for _, r := range d.refs {
		refs = append(refs, fmt.Sprint("shape", r))
	}
	if d.mode == qualified && d.disjoint {
		return fmt.Sprintf("qualified(%s, min=%d, max=%d, disjoint from %v)", strings.Join(refs, ","), d.min, d.max, d.siblings)
	}
	if d.mode == qualified {
		return fmt.Sprintf("qualified(%s, min=%d, max=%d, disjoint=%v)", strings.Join(refs, ","), d.min, d.max, d.disjoint)
	}
	return fmt.Sprintf("%s(%s)", depModeNames[d.mode], strings.Join(refs, ","))
}

func (d depSpec) dependency() dependency {
	var names []ShapeRef
	for _, id := range d.refs {
		names = append(names, ShapeRef{ref: &NodeShape{id: int64(id)}})
	}
	var siblings []ShapeRef
	for _, id := range d.siblings {
		siblings = append(siblings, ShapeRef{ref: &NodeShape{id: int64(id)}})
	}
	max := d.max
	if d.mode != qualified {
		max = -1
	}
	return dependency{mode: d.mode, name: names, min: d.min, max: max, disjoint: d.disjoint, siblings: siblings}
}

func qual1(ref, min, max int) depSpec {
	return depSpec{mode: qualified, refs: []int{ref}, min: min, max: max}
}

// expansion is one call of expandRules: a head predicate and the dependencies of the expanded column.
type expansion struct {
	header string
	deps   []depSpec
	cols   []int
}

// innerShape is a shape defined by expandRules itself, evaluated on each value node, so that outer
// dependencies can refer to shapes whose truth is derived instead of given as facts.
type innerShape struct {
	id  int
	dep depSpec
}

// world assigns to each shape id the set of value nodes (by index) that conform to it.
type world map[int]map[int]bool

// conforms evaluates the SHACL semantics of the dependencies in cols, for a focus node whose value
// nodes are 0..numValues-1.
func conforms(deps []depSpec, cols []int, numValues int, w world) bool {
	inCols := make(map[int]bool)
	for _, c := range cols {
		inCols[c] = true
	}

	for _, c := range cols {
		d := deps[c]
		switch d.mode {
		case and, node, property: // every value node conforms to every referenced shape
			for v := 0; v < numValues; v++ {
				for _, r := range d.refs {
					if !w[r][v] {
						return false
					}
				}
			}
		case or: // every value node conforms to at least one referenced shape
			for v := 0; v < numValues; v++ {
				any := false
				for _, r := range d.refs {
					any = any || w[r][v]
				}
				if !any {
					return false
				}
			}
		case not: // no value node conforms to the referenced shape
			for v := 0; v < numValues; v++ {
				if w[d.refs[0]][v] {
					return false
				}
			}
		case xone: // every value node conforms to exactly one referenced shape
			for v := 0; v < numValues; v++ {
				count := 0
				for _, r := range d.refs {
					if w[r][v] {
						count++
					}
				}
				if count != 1 {
					return false
				}
			}
		case qualified: // the number of conforming value nodes (not conforming to a sibling) is within bounds
			count := 0
			for v := 0; v < numValues; v++ {
				if !w[d.refs[0]][v] {
					continue
				}
				excluded := false
				if d.disjoint {
					for _, s := range d.siblings {
						if w[s][v] {
							excluded = true
						}
					}
				}
				if !excluded {
					count++
				}
			}
			if count < d.min || (d.max != -1 && count > d.max) {
				return false
			}
		}
	}
	return true
}

// valueWorld restricts w to a single value node, which becomes value 0.
func valueWorld(w world, v int) world {
	out := make(world)
	for s, vals := range w {
		out[s] = map[int]bool{0: vals[v]}
	}
	return out
}

// allWorlds enumerates every assignment of the given shapes over 0..maxValues value nodes.
func allWorlds(shapes []int, maxValues int) (worlds []world, sizes []int) {
	for n := 0; n <= maxValues; n++ {
		bits := len(shapes) * n
		for mask := 0; mask < 1<<bits; mask++ {
			w := make(world)
			for si, s := range shapes {
				w[s] = make(map[int]bool)
				for v := 0; v < n; v++ {
					w[s][v] = mask&(1<<(si*n+v)) != 0
				}
			}
			worlds = append(worlds, w)
			sizes = append(sizes, n)
		}
	}
	return worlds, sizes
}

func describeWorld(w world, n int) string {
	var shapes []int
	for s := range w {
		shapes = append(shapes, s)
	}
	sort.Ints(shapes)
	var parts []string
	for _, s := range shapes {
		var vals []string
		for v := 0; v < n; v++ {
			if w[s][v] {
				vals = append(vals, fmt.Sprint("v", v))
			}
		}
		parts = append(parts, fmt.Sprintf("shape%d={%s}", s, strings.Join(vals, ",")))
	}
	return fmt.Sprintf("%d value node(s): %s", n, strings.Join(parts, " "))
}

// resetLPState gives a test deterministic names in the generated program, and restores the global
// state afterwards.
func resetLPState(t *testing.T) {
	t.Helper()
	oldRename, oldReverse := renameMap, reverseMap
	oldCount, oldOr, oldXone, oldQual, oldDemo := theCount, orVar, xoneVar, qual, demoLP
	t.Cleanup(func() {
		renameMap, reverseMap = oldRename, oldReverse
		theCount, orVar, xoneVar, qual, demoLP = oldCount, oldOr, oldXone, oldQual, oldDemo
	})
	renameMap = make(map[rdf.Term]string)
	reverseMap = make(map[string]rdf.Term)
	theCount, orVar, xoneVar, qual, demoLP = 0, 1, 1, 1, false
}

// solveWithDLV runs DLV under well-founded semantics and returns the true and undefined atoms,
// with all whitespace removed.
func solveWithDLV(t *testing.T, program string) (trueAtoms, undefAtoms map[string]bool) {
	t.Helper()
	if _, err := os.Stat(dlv); err != nil {
		t.Skipf("DLV binary not found at %s", dlv)
	}
	cmd := exec.Command(dlv, "--wellfounded")
	cmd.Stdin = strings.NewReader(program)
	out, err := cmd.CombinedOutput()
	if err != nil || !strings.Contains(string(out), "True: {") {
		t.Fatalf("DLV failed: %v\n%s\nprogram:\n%s", err, out, program)
	}
	return parseDLVSet(string(out), "True"), parseDLVSet(string(out), "Undefined")
}

func parseDLVSet(output, label string) map[string]bool {
	set := make(map[string]bool)
	start := strings.Index(output, label+": {")
	if start < 0 {
		return set
	}
	rest := output[start+len(label)+3:]
	rest = rest[:strings.Index(rest, "}")]

	depth, last := 0, 0
	for i, c := range rest + "," {
		switch c {
		case '(':
			depth++
		case ')':
			depth--
		case ',':
			if depth == 0 {
				atom := strings.Join(strings.Fields(rest[last:min(i, len(rest))]), "")
				if atom != "" {
					set[atom] = true
				}
				last = i + 1
			}
		}
	}
	return set
}

// checkExpansions expands the given expansions for every world over the base shapes with up to
// maxValues value nodes, and reports every world where the derived head atoms disagree with the
// SHACL semantics. Inner shapes are expanded for each value node and may be referenced by the
// expansions in place of base shapes.
func checkExpansions(t *testing.T, exps []expansion, inner []innerShape, shapes []int, maxValues int) {
	t.Helper()
	resetLPState(t)

	worlds, sizes := allWorlds(shapes, maxValues)

	var program strings.Builder
	worldRules := make([][]serialisedRule, len(worlds))
	type check struct {
		atom     string
		expected bool
	}
	checks := make([][]check, len(worlds))

	for wi, w := range worlds {
		n := sizes[wi]
		var values []rdf.Term
		for v := 0; v < n; v++ {
			values = append(values, rdf.Resource{URI: fmt.Sprintf("http://example.com/w%d/v%d", wi, v)})
		}
		element := fmt.Sprint("focus", wi)

		// facts for the base shapes
		for _, s := range shapes {
			for v := 0; v < n; v++ {
				if w[s][v] {
					program.WriteString(fmt.Sprintf("shape%d(%s).\n", s, rewrite(values[v])))
				}
			}
		}

		// derived truth and rules for the inner shapes
		full := make(world)
		for s, vals := range w {
			full[s] = vals
		}
		for _, in := range inner {
			full[in.id] = make(map[int]bool)
			for v := 0; v < n; v++ {
				full[in.id][v] = conforms([]depSpec{in.dep}, []int{0}, 1, valueWorld(w, v))
				rules := expandRules([]rdf.Term{values[v]}, []int{0}, []dependency{in.dep.dependency()},
					fmt.Sprint("shape", in.id), rewrite(values[v]))
				worldRules[wi] = append(worldRules[wi], rules...)
			}
		}

		for _, e := range exps {
			var deps []dependency
			for _, d := range e.deps {
				deps = append(deps, d.dependency())
			}
			rules := expandRules(values, e.cols, deps, e.header, element)
			worldRules[wi] = append(worldRules[wi], rules...)
			checks[wi] = append(checks[wi], check{
				atom:     fmt.Sprintf("%s(%s)", e.header, element),
				expected: conforms(e.deps, e.cols, n, full),
			})
		}

		program.WriteString(serialisedProgram{rules: worldRules[wi]}.String())
	}

	trueAtoms, undefAtoms := solveWithDLV(t, program.String())

	var failures []string
	for wi := range worlds {
		for _, c := range checks[wi] {
			got := trueAtoms[c.atom]
			if undefAtoms[c.atom] {
				failures = append(failures, fmt.Sprintf("%s is undefined, expected %v", c.atom, c.expected))
			} else if got != c.expected {
				failures = append(failures, fmt.Sprintf("%s: got %v, expected %v\n\t\tworld: %s\n\t\trules:\n\t\t%s",
					c.atom, got, c.expected, describeWorld(worlds[wi], sizes[wi]),
					strings.ReplaceAll(serialisedProgram{rules: worldRules[wi]}.String(), "\n", "\n\t\t")))
			}
		}
	}
	if len(failures) > 0 {
		shown := failures
		if len(shown) > 3 {
			shown = shown[:3]
		}
		t.Errorf("%d of %d checks disagree with the SHACL semantics; first ones:\n\t%s",
			len(failures), len(worlds)*len(exps), strings.Join(shown, "\n\t"))
	}
}

func refsOf(deps []depSpec) []int {
	seen := make(map[int]bool)
	var out []int
	for _, d := range deps {
		for _, r := range append(slices.Clone(d.refs), d.siblings...) {
			if !seen[r] {
				seen[r] = true
				out = append(out, r)
			}
		}
	}
	sort.Ints(out)
	return out
}

func indicesOf(deps []depSpec) []int {
	var cols []int
	for i := range deps {
		cols = append(cols, i)
	}
	return cols
}

// TestExpandRulesSingleDependency checks each kind of dependency on its own.
func TestExpandRulesSingleDependency(t *testing.T) {
	cases := []depSpec{
		{mode: node, refs: []int{1}},
		{mode: property, refs: []int{1}},
		{mode: and, refs: []int{1, 2}},
		{mode: and, refs: []int{1, 2, 3}},
		{mode: or, refs: []int{1, 2}},
		{mode: or, refs: []int{1, 2, 3}},
		{mode: not, refs: []int{1}},
		{mode: xone, refs: []int{1}},
		{mode: xone, refs: []int{1, 2}},
		{mode: xone, refs: []int{1, 2, 3}},
		qual1(1, 1, -1),
		qual1(1, 2, -1),
		qual1(1, 0, 1),
		qual1(1, 0, 0),
		qual1(1, 1, 1),
		qual1(1, 2, 3),
		qual1(1, 0, -1),
	}
	for _, d := range cases {
		t.Run(d.String(), func(t *testing.T) {
			checkExpansions(t, []expansion{{header: "Head", deps: []depSpec{d}, cols: []int{0}}}, nil, d.refs, 3)
		})
	}
}

// Two variants per kind over a shared pool of shapes, so that combinations of the same kind
// reference different shapes, and different kinds overlap in the shapes they reference.
var variantsA = []depSpec{
	{mode: node, refs: []int{1}},
	{mode: and, refs: []int{1, 2}},
	{mode: or, refs: []int{1, 2}},
	{mode: not, refs: []int{1}},
	{mode: xone, refs: []int{1, 2}},
	qual1(1, 1, 1),
}

var variantsB = []depSpec{
	{mode: node, refs: []int{3}},
	{mode: and, refs: []int{2, 3}},
	{mode: or, refs: []int{2, 3}},
	{mode: not, refs: []int{3}},
	{mode: xone, refs: []int{2, 3}},
	qual1(3, 1, -1),
}

func depsName(deps []depSpec) string {
	var parts []string
	for _, d := range deps {
		parts = append(parts, d.String())
	}
	return strings.Join(parts, "+")
}

// TestExpandRulesTwoDependencies checks all ordered pairs of dependency kinds in one column, since
// expandRules attaches each dependency to the rules produced by the previous ones.
func TestExpandRulesTwoDependencies(t *testing.T) {
	for _, a := range variantsA {
		for _, b := range variantsB {
			deps := []depSpec{a, b}
			t.Run(depsName(deps), func(t *testing.T) {
				checkExpansions(t, []expansion{{header: "Head", deps: deps, cols: indicesOf(deps)}}, nil, refsOf(deps), 2)
			})
		}
	}
}

// TestExpandRulesThreeDependencies checks all ordered triples of dependency kinds in one column.
func TestExpandRulesThreeDependencies(t *testing.T) {
	for _, a := range variantsA {
		for _, b := range variantsB {
			for _, c := range variantsA {
				deps := []depSpec{a, b, c}
				t.Run(depsName(deps), func(t *testing.T) {
					checkExpansions(t, []expansion{{header: "Head", deps: deps, cols: indicesOf(deps)}}, nil, refsOf(deps), 2)
				})
			}
		}
	}
}

// TestExpandRulesQualifiedDisjoint checks sh:qualifiedValueShapesDisjoint, where value nodes
// conforming to a sibling shape are not counted. The siblings come with the dependency (computed by
// GetShaclDocument), so they count whether or not their own dependencies are expanded in the same call.
// The last two cases are the standalone encoding of a property shape (known bug Z): its dependency list
// holds only its own qualified value shape, and the sibling is not in it.
func TestExpandRulesQualifiedDisjoint(t *testing.T) {
	disjoint := func(min, max int, siblings ...int) depSpec {
		return depSpec{mode: qualified, refs: []int{1}, min: min, max: max, disjoint: true, siblings: siblings}
	}
	cases := [][]depSpec{
		{disjoint(1, -1, 2), qual1(2, 1, -1)},
		{disjoint(1, 1, 2, 3), qual1(2, 0, -1), qual1(3, 0, -1)},
		{disjoint(0, 1, 2), qual1(2, 1, -1)},
		{disjoint(2, -1, 2), qual1(2, 1, -1)},
		{disjoint(1, -1, 2)},
		{disjoint(1, 1, 2, 3)},
	}
	for _, deps := range cases {
		t.Run(depsName(deps), func(t *testing.T) {
			checkExpansions(t, []expansion{{header: "Head", deps: deps, cols: []int{0}}}, nil, refsOf(deps), 3)
		})
	}
}

// TestExpandRulesNestedShapes checks nesting: the outer dependency references shapes 10 and 11,
// which are themselves defined by logical constraints on the same value node (as in sh:and or
// sh:or lists whose members are shapes with their own sh:or, sh:not, ...).
func TestExpandRulesNestedShapes(t *testing.T) {
	inners := []depSpec{
		{mode: and, refs: []int{1, 2}},
		{mode: or, refs: []int{1, 2}},
		{mode: not, refs: []int{1}},
		{mode: xone, refs: []int{1, 2}},
		{mode: node, refs: []int{2}},
	}
	outers := []depSpec{
		{mode: and, refs: []int{10, 11}},
		{mode: or, refs: []int{10, 11}},
		{mode: not, refs: []int{10}},
		{mode: xone, refs: []int{10, 11}},
		{mode: node, refs: []int{11}},
		qual1(10, 1, 1),
	}
	for _, in10 := range inners {
		for _, in11 := range inners {
			// shape 11 uses shapes 2 and 3 where shape 10 uses 1 and 2, so the two overlap in one shape
			in11 := in11
			in11.refs = append([]int(nil), in11.refs...)
			for i := range in11.refs {
				in11.refs[i]++
			}
			for _, out := range outers {
				name := fmt.Sprintf("%s[Shape10=%s,Shape11=%s]", out, in10, in11)
				t.Run(name, func(t *testing.T) {
					checkExpansions(t,
						[]expansion{{header: "Head", deps: []depSpec{out}, cols: []int{0}}},
						[]innerShape{{id: 10, dep: in10}, {id: 11, dep: in11}},
						[]int{1, 2, 3}, 2)
				})
			}
		}
	}
}

// TestExpandRulesShapesShareValueNodes checks that two shapes expanded into the same program over
// the same value nodes do not influence each other, as happens when several shapes constrain the
// values of the same property.
func TestExpandRulesShapesShareValueNodes(t *testing.T) {
	pairs := [][2]depSpec{
		{{mode: or, refs: []int{1, 2}}, {mode: or, refs: []int{3, 4}}},
		{{mode: xone, refs: []int{1, 2}}, {mode: xone, refs: []int{3, 4}}},
		{qual1(1, 1, 1), qual1(2, 1, 1)},
		{{mode: or, refs: []int{1, 2}}, {mode: xone, refs: []int{3, 4}}},
	}
	for _, p := range pairs {
		t.Run(depsName(p[:]), func(t *testing.T) {
			checkExpansions(t, []expansion{
				{header: "HeadA", deps: []depSpec{p[0]}, cols: []int{0}},
				{header: "HeadB", deps: []depSpec{p[1]}, cols: []int{0}},
			}, nil, refsOf(p[:]), 2)
		})
	}
}

// validateDocument validates a SHACL document that includes its data graph against the given
// endpoint, and returns whether it conforms.
func validateDocument(t *testing.T, ep *SparqlEndpoint, name, turtle string, forceLP bool) bool {
	t.Helper()
	path := t.TempDir() + "/" + name + ".ttl"
	if err := os.WriteFile(path, []byte(turtle), 0o600); err != nil {
		t.Fatal(err)
	}
	file, err := os.Open(path)
	if err != nil {
		t.Fatal(err)
	}
	defer file.Close()

	g := rdf.NewGraph(_sh)
	if err := g.Parse(file, "text/turtle"); err != nil {
		t.Fatal(err)
	}
	prefixes = make(map[string]string)
	GetNameSpace(file)

	graphName := "<" + _sh + name + ">"
	if err := ep.ClearGraph(graphName); err != nil {
		t.Fatal(err)
	}
	if err := ep.Insert(g, graphName, false); err != nil {
		t.Fatal(err)
	}
	defer ep.ClearGraph(graphName) //nolint:errcheck

	doc := GetShaclDocument(g, graphName, false, WellFounded{})
	activeDoc = &doc
	report := answerShacl(ep, doc, config{silent: true, forceLP: forceLP, semantics: WellFounded{}})
	return report.conforms
}

const nestedPrefixes = `
@prefix ex: <http://example.org/nested#> .
@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .
@prefix sh: <http://www.w3.org/ns/shacl#> .
`

// TestNestedPropertyShapes covers a variation of the W3C test property/property-001
// reduced to just its first case with a valid person.
func TestNestedPropertyShapes(t *testing.T) {
	if _, err := os.Stat(dlv); err != nil {
		t.Skipf("DLV binary not found at %s", dlv)
	}
	ep, cleanup, err := StartOxigraph(false)
	if err != nil {
		t.Skip("oxigraph not available:", err)
	}
	defer cleanup()

	cases := []struct {
		name     string
		turtle   string
		conforms bool
	}{
		{
			name: "property-001-valid-person",
			turtle: nestedPrefixes + `
ex:PersonShape a sh:NodeShape ;
  sh:targetClass ex:Person ;
  sh:property [ sh:path ex:address ; sh:property ex:PersonShape-address-city ] .
ex:PersonShape-address-city sh:path ex:city ; sh:class ex:City .

ex:ValidPerson1 rdf:type ex:Person ; ex:address ex:ValidAddress .
ex:ValidAddress rdf:type ex:Address ; ex:city ex:ProperCity .
ex:ProperCity rdf:type ex:City .
`,
			conforms: true,
		},
		{
			name: "nested-mincount-valid",
			turtle: nestedPrefixes + `
ex:PersonShape a sh:NodeShape ; sh:targetNode ex:alice ;
  sh:property [ sh:path ex:pet ; sh:property [ sh:path ex:name ; sh:minCount 1 ] ] .

ex:alice ex:pet ex:rex .
ex:rex ex:name "Rex" .
`,
			conforms: true,
		},
		{
			name: "nested-mincount-invalid",
			turtle: nestedPrefixes + `
ex:PersonShape a sh:NodeShape ; sh:targetNode ex:alice ;
  sh:property [ sh:path ex:pet ; sh:property [ sh:path ex:name ; sh:minCount 1 ] ] .

ex:alice ex:pet ex:rex .
`,
			conforms: false,
		},
	}

	for _, c := range cases {
		for _, forceLP := range []bool{false, true} {
			path := "unwinding"
			if forceLP {
				path = "logic-program"
			}
			t.Run(c.name+"/"+path, func(t *testing.T) {
				if got := validateDocument(t, ep, c.name, c.turtle, forceLP); got != c.conforms {
					t.Errorf("conforms = %v, expected %v", got, c.conforms)
				}
			})
		}
	}
}

// The logical constraint tests share two shapes: SA accepts a and ab, SB accepts b and ab, and no
// shape accepts c.
const logicalShapes = `
ex:SA a sh:NodeShape ; sh:in ( ex:a ex:ab ) .
ex:SB a sh:NodeShape ; sh:in ( ex:b ex:ab ) .
`

type invalidTargetsCase struct {
	name    string
	turtle  string
	invalid string // as printed by describeInvalid
}

// checkInvalidTargets validates each case, together with logicalShapes, on both the unwinding and
// the logic program path, and compares the invalid targets and the verdict.
func checkInvalidTargets(t *testing.T, graphPrefix string, cases []invalidTargetsCase) {
	ep := startTestOxigraph(t)

	for i, c := range cases {
		for _, forceLP := range []bool{false, true} {
			path := map[bool]string{false: "unwinding", true: "logic-program"}[forceLP]
			t.Run(c.name+"/"+path, func(t *testing.T) {
				graphName := fmt.Sprintf("<urn:%s:%d>", graphPrefix, i)
				g := loadTurtle(t, ep, graphName, recPrefixes+logicalShapes+c.turtle)

				res, invalid, err := shawellInvalid(g, ep, graphName, forceLP)
				if err != nil {
					t.Fatalf("panic: %v", err)
				}
				if got := describeInvalid(invalid); got != c.invalid {
					t.Errorf("invalid targets %q, expected %q", got, c.invalid)
				}
				if res != (c.invalid == "") {
					t.Errorf("verdict %v, expected %v", res, c.invalid == "")
				}
			})
		}
	}
}

// TestXone checks that sh:xone requires each value node to conform to exactly one of the listed
// shapes (known bug J: the unwinding path accepted value nodes that conform to none of them).
func TestXone(t *testing.T) {
	checkInvalidTargets(t, "xone", []invalidTargetsCase{
		{
			name:    "node-shape",
			turtle:  `ex:S a sh:NodeShape ; sh:targetNode ex:a , ex:b , ex:ab , ex:c ; sh:xone ( ex:SA ex:SB ) .`,
			invalid: "S={ab,c}",
		},
		{
			name:    "single-shape-matching-none",
			turtle:  `ex:S a sh:NodeShape ; sh:targetNode ex:a , ex:c ; sh:xone ( ex:SA ) .`,
			invalid: "S={c}",
		},
		{
			// n0 has one value per shape, n1 has a value matching no shape, n2 one matching both
			name: "property-shape",
			turtle: `ex:S a sh:NodeShape ; sh:targetNode ex:n0 , ex:n1 , ex:n2 ;
			           sh:property [ sh:path ex:p ; sh:xone ( ex:SA ex:SB ) ] .
			         ex:n0 ex:p ex:a , ex:b . ex:n1 ex:p ex:a , ex:c . ex:n2 ex:p ex:a , ex:ab .`,
			invalid: "S={n1,n2}",
		},
	})
}

// TestXoneReport checks the validation report of sh:xone in a property shape (known bug X): it must report the
// value nodes that conform to none or to several of the shapes, and no others. The same document as the
// property-shape case of TestXone: n1 and n2 are invalid, n0 is valid.
func TestXoneReport(t *testing.T) {
	ep := startTestOxigraph(t)
	turtle := `ex:S a sh:NodeShape ; sh:targetNode ex:n0 , ex:n1 , ex:n2 ;
	             sh:property [ sh:path ex:p ; sh:xone ( ex:SA ex:SB ) ] .
	           ex:n0 ex:p ex:a , ex:b . ex:n1 ex:p ex:a , ex:c . ex:n2 ex:p ex:a , ex:ab .`
	for i, forceLP := range []bool{false, true} {
		path := map[bool]string{false: "unwinding", true: "logic-program"}[forceLP]
		t.Run(path, func(t *testing.T) {
			graphName := fmt.Sprintf("<urn:xone-report:%d>", i)
			g := loadTurtle(t, ep, graphName, recPrefixes+logicalShapes+turtle)
			report, err := shawellReport(g, ep, graphName, forceLP)
			if err != nil {
				t.Fatalf("panic: %v", err)
			}
			var got []string
			for _, r := range report.results {
				got = append(got, strings.TrimPrefix(r.focusNode.RawValue(), fzNS)+" "+
					strings.TrimPrefix(r.value.RawValue(), fzNS))
			}
			sort.Strings(got)
			if want := "n1 c, n2 ab"; strings.Join(got, ", ") != want {
				t.Errorf("results (focus node, value) %q, expected %q", strings.Join(got, ", "), want)
			}
		})
	}
}

// TestAnd checks that sh:and requires each value node to conform to all of the listed shapes (known
// bug K: from the second shape on, the unwinding path read an ungrouped table and dropped every target).
func TestAnd(t *testing.T) {
	checkInvalidTargets(t, "and", []invalidTargetsCase{
		{
			name:    "node-shape",
			turtle:  `ex:S a sh:NodeShape ; sh:targetNode ex:a , ex:b , ex:ab , ex:c ; sh:and ( ex:SA ex:SB ) .`,
			invalid: "S={a,b,c}",
		},
		{
			name:    "single-shape",
			turtle:  `ex:S a sh:NodeShape ; sh:targetNode ex:a , ex:c ; sh:and ( ex:SA ) .`,
			invalid: "S={c}",
		},
		{
			name:    "repeated-shape",
			turtle:  `ex:S a sh:NodeShape ; sh:targetNode ex:a , ex:c ; sh:and ( ex:SA ex:SA ) .`,
			invalid: "S={c}",
		},
		{
			name:    "three-shapes",
			turtle:  `ex:S a sh:NodeShape ; sh:targetNode ex:a , ex:ab ; sh:and ( ex:SA ex:SB ex:SA ) .`,
			invalid: "S={a}",
		},
		{
			// n0 has only values matching both shapes, n1 also one matching only SA, n2 one matching none
			name: "property-shape",
			turtle: `ex:S a sh:NodeShape ; sh:targetNode ex:n0 , ex:n1 , ex:n2 ;
			           sh:property [ sh:path ex:p ; sh:and ( ex:SA ex:SB ) ] .
			         ex:n0 ex:p ex:ab . ex:n1 ex:p ex:ab , ex:a . ex:n2 ex:p ex:ab , ex:c .`,
			invalid: "S={n1,n2}",
		},
	})
}

// TestLanguageIn checks sh:languageIn on property and node shapes, including the validation report
// (known bug N: on property shapes the satisfying condition was inside FILTER NOT EXISTS, so matching
// values failed and others passed, and non-literal values were never flagged).
func TestLanguageIn(t *testing.T) {
	ep := startTestOxigraph(t)

	cases := []invalidTargetsCase{
		{
			// n0 has an English value, n1 a German one, n2 one without a tag, n3 an IRI, n4 no value
			name: "property-shape-single-language",
			turtle: `ex:S a sh:NodeShape ; sh:targetNode ex:n0 , ex:n1 , ex:n2 , ex:n3 , ex:n4 ;
			           sh:property [ sh:path ex:p ; sh:languageIn ( "en" ) ] .
			         ex:n0 ex:p "hello"@en . ex:n1 ex:p "hallo"@de . ex:n2 ex:p "hello" . ex:n3 ex:p ex:a .`,
			invalid: "S={n1,n2,n3}",
		},
		{
			// a value only has to match one of the languages; n2 has one matching and one not
			name: "property-shape-two-languages",
			turtle: `ex:S a sh:NodeShape ; sh:targetNode ex:n0 , ex:n1 , ex:n2 , ex:n3 ;
			           sh:property [ sh:path ex:p ; sh:languageIn ( "en" "de" ) ] .
			         ex:n0 ex:p "hello"@en , "hallo"@de . ex:n1 ex:p "hello"@en-GB .
			         ex:n2 ex:p "hello"@en , "bonjour"@fr . ex:n3 ex:p ex:a .`,
			invalid: "S={n2,n3}",
		},
		{
			name: "node-shape",
			turtle: `ex:S a sh:NodeShape ; sh:targetNode "hello"@en , "hallo"@de , "bonjour"@fr , ex:a ;
			           sh:languageIn ( "en" "de" ) .`,
			invalid: "S={a,bonjour}",
		},
	}

	for i, c := range cases {
		for _, forceLP := range []bool{false, true} {
			path := map[bool]string{false: "unwinding", true: "logic-program"}[forceLP]
			t.Run(c.name+"/"+path, func(t *testing.T) {
				graphName := fmt.Sprintf("<urn:languageIn:%d>", i)
				g := loadTurtle(t, ep, graphName, recPrefixes+c.turtle)

				res, invalid, err := shawellInvalid(g, ep, graphName, forceLP)
				if err != nil {
					t.Fatalf("panic: %v", err)
				}
				if got := describeInvalid(invalid); got != c.invalid {
					t.Errorf("invalid targets %q, expected %q", got, c.invalid)
				}
				if res != (c.invalid == "") {
					t.Errorf("verdict %v, expected %v", res, c.invalid == "")
				}

				report, err := shawellReport(g, ep, graphName, forceLP)
				if err != nil {
					t.Fatalf("report: panic: %v", err)
				}
				for _, p := range checkReport(report, c.invalid == "") {
					t.Error("report: " + p)
				}
			})
		}
	}
}

// TestDatatype checks sh:datatype on property and node shapes, including the validation report.
// The documents do not declare xsd:, and datatypes are written as full IRIs (known bug M: the report
// query used the prefixed name xsd:string, which made the query invalid without that prefix). IRIs
// and blank nodes must violate the constraint (known bug O: for non-core datatypes, datatype() of a
// non-literal raised an error, so such values were never flagged; the report query for xsd:string on
// property shapes had the same problem).
func TestDatatype(t *testing.T) {
	ep := startTestOxigraph(t)

	const xsd = "<http://www.w3.org/2001/XMLSchema#"
	cases := []struct {
		invalidTargetsCase
		focusNodes string // focus nodes of the report results, sorted
	}{
		{
			// non-core datatype; n0 has a language-tagged value, n1 a plain one, n2 an IRI, n3 a blank node
			invalidTargetsCase: invalidTargetsCase{
				name: "property-shape-non-core",
				turtle: `ex:S a sh:NodeShape ; sh:targetNode ex:n0 , ex:n1 , ex:n2 , ex:n3 , ex:n4 ;
				           sh:property [ sh:path ex:p ; sh:datatype rdf:langString ] .
				         ex:n0 ex:p "hello"@en . ex:n1 ex:p "hello" . ex:n2 ex:p ex:a . ex:n3 ex:p [ ex:q ex:a ] .`,
				invalid: "S={n1,n2,n3}",
			},
			focusNodes: "n1,n2,n3",
		},
		{
			invalidTargetsCase: invalidTargetsCase{
				name: "node-shape-non-core",
				turtle: `ex:S a sh:NodeShape ; sh:targetNode "hello"@en , "plain" , ex:a ;
				           sh:datatype rdf:langString .`,
				invalid: "S={a,plain}",
			},
			focusNodes: "a,plain",
		},
		{
			invalidTargetsCase: invalidTargetsCase{
				name: "property-shape-string",
				turtle: `ex:S a sh:NodeShape ; sh:targetNode ex:n0 , ex:n1 , ex:n2 , ex:n3 , ex:n4 ;
				           sh:property [ sh:path ex:p ; sh:datatype ` + xsd + `string> ] .
				         ex:n0 ex:p "s" . ex:n1 ex:p 1 . ex:n2 ex:p ex:a . ex:n3 ex:p [ ex:q ex:a ] .`,
				invalid: "S={n1,n2,n3}",
			},
			focusNodes: "n1,n2,n3",
		},
		{
			invalidTargetsCase: invalidTargetsCase{
				name: "node-shape-string",
				turtle: `ex:S a sh:NodeShape ; sh:targetNode "s" , 1 , ex:a ;
				           sh:datatype ` + xsd + `string> .`,
				invalid: "S={1,a}",
			},
			focusNodes: "1,a",
		},
		{
			// core datatype other than xsd:string; the report query compares with xsd:string (bug M)
			invalidTargetsCase: invalidTargetsCase{
				name: "property-shape-integer",
				turtle: `ex:S a sh:NodeShape ; sh:targetNode ex:n0 , ex:n1 , ex:n2 , ex:n3 , ex:n4 ;
				           sh:property [ sh:path ex:p ; sh:datatype ` + xsd + `integer> ] .
				         ex:n0 ex:p 1 . ex:n1 ex:p "x" . ex:n2 ex:p ex:a . ex:n3 ex:p [ ex:q ex:a ] .`,
				invalid: "S={n1,n2,n3}",
			},
			focusNodes: "n1,n2,n3",
		},
		{
			invalidTargetsCase: invalidTargetsCase{
				name: "node-shape-integer",
				turtle: `ex:S a sh:NodeShape ; sh:targetNode 1 , "x" , ex:a ;
				           sh:datatype ` + xsd + `integer> .`,
				invalid: "S={a,x}",
			},
			focusNodes: "a,x",
		},
	}

	for i, c := range cases {
		for _, forceLP := range []bool{false, true} {
			path := map[bool]string{false: "unwinding", true: "logic-program"}[forceLP]
			t.Run(c.name+"/"+path, func(t *testing.T) {
				graphName := fmt.Sprintf("<urn:datatype:%d>", i)
				g := loadTurtle(t, ep, graphName, recPrefixes+c.turtle)

				res, invalid, err := shawellInvalid(g, ep, graphName, forceLP)
				if err != nil {
					t.Fatalf("panic: %v", err)
				}
				if got := describeInvalid(invalid); got != c.invalid {
					t.Errorf("invalid targets %q, expected %q", got, c.invalid)
				}
				if res != (c.invalid == "") {
					t.Errorf("verdict %v, expected %v", res, c.invalid == "")
				}

				report, err := shawellReport(g, ep, graphName, forceLP)
				if err != nil {
					t.Fatalf("report: panic: %v", err)
				}
				for _, p := range checkReport(report, c.invalid == "") {
					t.Error("report: " + p)
				}
				var focus []string
				for _, r := range report.results {
					focus = append(focus, strings.TrimPrefix(r.focusNode.RawValue(), fzNS))
				}
				sort.Strings(focus)
				if got := strings.Join(focus, ","); got != c.focusNodes {
					t.Errorf("report: focus nodes %q, expected %q", got, c.focusNodes)
				}
			})
		}
	}
}

// TestSerialiseDropsDuplicateLiterals covers known bug L: DLV 2.1.1 crashes on a rule that repeats a
// negated literal if the program also has a rule over an undefined predicate. String() must drop the
// duplicate, without changing the program, so that serialising it again gives the same output.
func TestSerialiseDropsDuplicateLiterals(t *testing.T) {
	p := serialisedProgram{rules: []serialisedRule{
		{head: "a(x)", body: []string{"not b(x)", "c(x)", "not b(x)"}},
		{head: "c(Y)", body: []string{"d(X,Y)"}}, // d is undefined
		{head: "e(x)"},
	}}
	bodyBefore := strings.Join(p.rules[0].body, "|")

	first := p.String()
	if strings.Count(first, "not b(x)") != 1 {
		t.Errorf("the duplicate literal was not dropped:\n%s", first)
	}
	if second := p.String(); second != first {
		t.Errorf("serialising twice gives different programs:\n%s\nand\n%s", first, second)
	}
	if got := strings.Join(p.rules[0].body, "|"); got != bodyBefore {
		t.Errorf("String() changed the rule body from %q to %q", bodyBefore, got)
	}

	if _, err := os.Stat(dlv); err != nil {
		t.Skipf("DLV binary not found at %s", dlv)
	}
	if err := noPanic(func() { p.runDLV(false, false) }); err != nil {
		t.Errorf("DLV failed on the serialised program: %v\n%s", err, first)
	}
}

// TestRepeatedNegation is the SHACL side of bug L: a shape that negates the same shape twice, which
// produces a rule with a repeated negated literal. No node conforms to S2, so its predicate is
// undefined in the logic program, while the rules for the qualified value shape still use it: the
// combination that crashed DLV.
func TestRepeatedNegation(t *testing.T) {
	ep := startTestOxigraph(t)
	turtle := recPrefixes + `
ex:S1 a sh:NodeShape ; sh:targetNode ex:n0, ex:n1 ; sh:not ex:S2 ; sh:not ex:S2 ;
  sh:property [ sh:path ex:p ; sh:qualifiedValueShape ex:S2 ; sh:qualifiedMinCount 0 ; sh:qualifiedMaxCount 1 ] .
ex:S2 a sh:NodeShape ; sh:class ex:A .
ex:n0 ex:p ex:n1 .
ex:n1 ex:p ex:n2 .
`
	graphName := "<urn:repeated-negation>"
	g := loadTurtle(t, ep, graphName, turtle)
	for _, forceLP := range []bool{false, true} {
		res, invalid, err := shawellInvalid(g, ep, graphName, forceLP)
		if err != nil {
			t.Fatalf("forceLP=%v: panic: %v", forceLP, err)
		}
		if got := describeInvalid(invalid); got != "" || !res {
			t.Errorf("forceLP=%v: verdict %v with invalid targets %q, expected true", forceLP, res, got)
		}
	}
}

// The tests below are those of step 1.8 of stable_semantics_plan.md, written against runClingo as
// it is implemented: a single plain solve that shows the shapeN/1 atoms only and returns a
// solveStatus. Solver errors still end the process, so each case runs runClingo in a copy of the
// test binary (TestClingoHelperProcess), so that an exit or a panic becomes an observable outcome
// instead of ending the test run.

const (
	clingoCaseEnv   = "SHAWELL_CLINGO_CASE"
	clingoResultTag = "CLINGO-RESULT "
)

// clingoCase is the input handed to the helper process.
type clingoCase struct {
	Rules     [][]string // each rule as head followed by its body atoms
	ExtraArgs []string   // appended to every clingo call, through a wrapper script (Unix only)
}

// clingoOutcome is what the helper process did with a clingoCase.
type clingoOutcome struct {
	returned bool        // runClingo came back, as opposed to ending the process
	status   solveStatus // the second return value of runClingo
	atoms    []string    // the true atoms, sorted, e.g. "shape1(c)"
	exitCode int
	stderr   string
}

func statusName(s solveStatus) string {
	switch s {
	case satisfiable:
		return "satisfiable"
	case unsatisfiable:
		return "unsatisfiable"
	case unknown:
		return "unknown"
	}
	return fmt.Sprintf("solveStatus(%d)", int(s))
}

func (o clingoOutcome) String() string {
	if o.returned {
		return fmt.Sprintf("returned status=%s atoms=%v", statusName(o.status), o.atoms)
	}
	return fmt.Sprintf("process ended with exit code %d\nstderr:\n%s", o.exitCode, o.stderr)
}

// requireClingo skips the test when no clingo can be found.
func requireClingo(t *testing.T) []string {
	t.Helper()
	cmd, err := findClingo("")
	if err != nil {
		t.Skipf("clingo not found: %v", err)
	}
	return cmd
}

// installClingoWrapper puts a script named clingo in front of PATH that runs the real clingo with
// extra appended to its arguments, and points clingoCmd at it as well. runClingo has no way to pass
// extra flags, and findClingo checks PATH first, so this is how a test imposes --time-limit or -n.
func installClingoWrapper(t *testing.T, extra []string) {
	t.Helper()
	real, err := findClingo("")
	if err != nil {
		t.Fatalf("clingo not found: %v", err)
	}
	if strings.ContainsRune(real[0], filepath.Separator) {
		if real[0], err = filepath.Abs(real[0]); err != nil {
			t.Fatal(err)
		}
	}
	quote := func(s string) string { return "'" + strings.ReplaceAll(s, "'", `'\''`) + "'" }
	var line []string
	for _, s := range real {
		line = append(line, quote(s))
	}
	line = append(line, `"$@"`)
	for _, s := range extra {
		line = append(line, quote(s))
	}
	dir := t.TempDir()
	wrapper := filepath.Join(dir, "clingo")
	script := "#!/bin/sh\nexec " + strings.Join(line, " ") + "\n"
	if err := os.WriteFile(wrapper, []byte(script), 0o755); err != nil {
		t.Fatal(err)
	}
	t.Setenv("PATH", dir+string(os.PathListSeparator)+os.Getenv("PATH"))
	clingoCmd = []string{wrapper}
}

// TestClingoHelperProcess is not a test: it is the body of the process started by solveWithClingo.
func TestClingoHelperProcess(t *testing.T) {
	encoded := os.Getenv(clingoCaseEnv)
	if encoded == "" {
		return
	}
	var c clingoCase
	if err := json.Unmarshal([]byte(encoded), &c); err != nil {
		fmt.Fprintln(os.Stderr, "bad clingo case:", err)
		os.Exit(3)
	}
	// runClingo uses the global clingoCmd, which main sets; the test binary has to set it itself.
	if len(c.ExtraArgs) > 0 {
		installClingoWrapper(t, c.ExtraArgs)
	} else {
		cmd, err := findClingo("")
		if err != nil {
			fmt.Fprintln(os.Stderr, "clingo not found:", err)
			os.Exit(3)
		}
		clingoCmd = cmd
	}
	var program serialisedProgram
	for _, r := range c.Rules {
		program.rules = append(program.rules, serialisedRule{head: r[0], body: r[1:]})
	}

	out, status := program.runClingo(false)

	atoms := []string{}
	for _, a := range out.Answers {
		atoms = append(atoms, fmt.Sprintf("%s%s(%s)", a.Negation, a.Predicate, strings.Join(a.Constant, ",")))
	}
	sort.Strings(atoms)
	result, _ := json.Marshal(map[string]any{"status": int(status), "atoms": atoms})
	fmt.Println(clingoResultTag + string(result))
	os.Exit(0)
}

// solveWithClingo runs runClingo on the given rules in a separate process and reports the outcome.
func solveWithClingo(t *testing.T, rules ...[]string) clingoOutcome {
	t.Helper()
	return solveWithClingoArgs(t, nil, rules...)
}

// solveWithClingoArgs is solveWithClingo with extra clingo arguments, e.g. --time-limit=1.
func solveWithClingoArgs(t *testing.T, extra []string, rules ...[]string) clingoOutcome {
	t.Helper()
	requireClingo(t)
	if len(extra) > 0 && runtime.GOOS == "windows" {
		t.Skip("extra clingo arguments need a shell wrapper script")
	}

	encoded, err := json.Marshal(clingoCase{Rules: rules, ExtraArgs: extra})
	if err != nil {
		t.Fatal(err)
	}
	cmd := exec.Command(os.Args[0], "-test.run=^TestClingoHelperProcess$")
	cmd.Env = append(os.Environ(), clingoCaseEnv+"="+string(encoded))
	var stderr strings.Builder
	cmd.Stderr = &stderr
	stdout, err := cmd.Output()

	out := clingoOutcome{stderr: stderr.String()}
	var exitErr *exec.ExitError
	if errors.As(err, &exitErr) {
		out.exitCode = exitErr.ExitCode()
	} else if err != nil {
		t.Fatalf("could not start the helper process: %v", err)
	}
	for _, line := range strings.Split(string(stdout), "\n") {
		if rest, found := strings.CutPrefix(line, clingoResultTag); found {
			var result struct {
				Status int
				Atoms  []string
			}
			if err := json.Unmarshal([]byte(rest), &result); err != nil {
				t.Fatalf("bad helper output %q: %v", line, err)
			}
			out.returned = true
			out.status, out.atoms = solveStatus(result.Status), result.Atoms
		}
	}
	if !out.returned && out.exitCode == 0 {
		t.Fatalf("helper process exited with code 0 but printed no result\nstdout:\n%s\nstderr:\n%s", stdout, out.stderr)
	}
	return out
}

// evenLoop has the two stable models {shape1(c)} and {shape2(c)}.
var evenLoop = [][]string{
	{"shape1(c)", "not shape2(c)"},
	{"shape2(c)", "not shape1(c)"},
}

// pigeonhole has no stable model, and clingo needs far more than a second to prove that (12
// pigeons, 11 holes). shape1(k) is shown so that the program has a #show line.
var pigeonhole = [][]string{
	{"pigeon(1..12)"},
	{"hole(1..11)"},
	{"shape1(k)"},
	{"{ at(P,H) : hole(H) } = 1", "pigeon(P)"},
	{"", "at(P1,H)", "at(P2,H)", "P1<P2"},
}

// Plan row 1: runClingo runs without a mode flag, so clingo stops at the first model, and that
// model is exactly one of the two.
func TestClingoEvenLoop(t *testing.T) {
	out := solveWithClingo(t, evenLoop...)
	got := strings.Join(out.atoms, " ")
	if !out.returned || out.status != satisfiable || (got != "shape1(c)" && got != "shape2(c)") {
		t.Errorf("expected one model, [shape1(c)] or [shape2(c)], got: %v", out)
	}
}

// Plan row 4: a program without a stable model is reported as unsatisfiable, never as a model.
func TestClingoUnsatisfiable(t *testing.T) {
	out := solveWithClingo(t, []string{"shape1(c)", "not shape1(c)"})
	if !out.returned || out.status != unsatisfiable {
		t.Errorf("expected an unsatisfiable run, got: %v", out)
	}
}

// Plan row 5: an upper-case predicate is a syntax error in clingo. That is an error, not a verdict:
// it must not look like a model, like "no stable model", or like an interrupted run.
func TestClingoSyntaxError(t *testing.T) {
	out := solveWithClingo(t, []string{"Shape1(a)"})
	if out.returned {
		t.Fatalf("a syntax error was returned as a solver result instead of an error: %v", out)
	}
	if !strings.Contains(out.stderr, "syntax error") {
		t.Errorf("expected clingo's syntax error message on stderr, got: %v", out)
	}
}

// Plan row 6: a body atom without any rule (a target that was never grounded) is simply false.
// Clingo warns about it, and about the #show line for a predicate without atoms; neither may break
// the parsing of the output. The plan runs this without --warn=none, which runClingo always passes.
func TestClingoUndefinedBodyAtom(t *testing.T) {
	out := solveWithClingo(t, []string{"shape1(c)", "shape2(c)"})
	if !out.returned || out.status != satisfiable || len(out.atoms) != 0 {
		t.Errorf("expected a model without atoms, got: %v", out)
	}
}

// The empty program has exactly one stable model, the empty one; runClingo answers without clingo.
func TestClingoEmptyProgram(t *testing.T) {
	out := solveWithClingo(t)
	if !out.returned || out.status != satisfiable || len(out.atoms) != 0 {
		t.Errorf("expected the empty model, got: %v", out)
	}
}

// Interrupted by the time limit before any model is found: unknown, which phase 2 turns into the
// Unknown verdict. It must neither end the process nor look like "no model".
func TestClingoTimeLimit(t *testing.T) {
	out := solveWithClingoArgs(t, []string{"--time-limit=1"}, pigeonhole...)
	if !out.returned || out.status != unknown {
		t.Errorf("expected an unknown run, got: %v", out)
	}
}

// The tests below check call 1 of the cautious mode (plan phase 2, step 4): the program merged with
// GetTargetConstraintsLPCautious is satisfiable exactly when some stable model fails some target,
// and such a model is the counter-model. The constraint program comes from the real function, on a
// document whose targets are set by hand; only the shapes' rules are written out here.

// cautiousShape describes one shape of the document handed to GetTargetConstraintsLPCautious.
type cautiousShape struct {
	id       int64
	targets  []string // focus nodes, as IRIs below http://example.org/cautious#
	inactive bool
}

// cautiousCall1 builds the target constraint program for the given shapes, merges it with rules,
// and solves the result. In rules, the constant $x stands for the encoding of the focus node x.
// It returns the solver outcome and the constraint program itself.
func cautiousCall1(t *testing.T, extra []string, shapes []cautiousShape, rules ...[]string) (clingoOutcome, serialisedProgram) {
	t.Helper()
	oldRenameMap, oldReverseMap, oldCount := renameMap, reverseMap, theCount
	defer func() { renameMap, reverseMap, theCount = oldRenameMap, oldReverseMap, oldCount }()
	renameMap = make(map[rdf.Term]string)
	reverseMap = make(map[string]rdf.Term)
	theCount = 0

	doc := ShaclDocument{
		shapeNames:   make(map[string]Shape),
		targets:      make(map[string]Table[rdf.Term]),
		materialised: true, // the targets below stand in for the endpoint's answers
	}
	for _, s := range shapes {
		name := fmt.Sprint("http://example.org/cautious#S", s.id)
		doc.shapeNames[name] = &NodeShape{id: s.id, deactivated: s.inactive}
		table := &TableSimple[rdf.Term]{header: []string{"target"}}
		for _, x := range s.targets {
			table.AddRow([]rdf.Term{rdf.Resource{URI: "http://example.org/cautious#" + x}})
		}
		doc.targets[name] = table
	}

	constraints := doc.GetTargetConstraintsLPCautious(nil)

	// replace $x in the given rules by the encoding of x, also for nodes that are no target
	placeholder := regexp.MustCompile(`\$(\w+)`)
	encode := func(m string) string { return rewrite(rdf.Resource{URI: "http://example.org/cautious#" + m[1:]}) }
	var all [][]string
	for _, r := range rules {
		rule := make([]string, len(r))
		for i := range r {
			rule[i] = placeholder.ReplaceAllStringFunc(r[i], encode)
		}
		all = append(all, rule)
	}
	for _, r := range constraints.rules {
		all = append(all, append([]string{r.head}, r.body...))
	}

	return solveWithClingoArgs(t, extra, all...), constraints
}

// shownOnlyShapes reports an error if the model shows anything but shape atoms, e.g. the auxiliary
// atoms of the constraint, which AdoptLPAnswers would then try to read as shapes.
func shownOnlyShapes(t *testing.T, out clingoOutcome) {
	t.Helper()
	for _, a := range out.atoms {
		if !strings.HasPrefix(a, "shape") {
			t.Errorf("the model shows %q, which is not a shape atom", a)
		}
	}
}

// A cx5-like document: the two targets of shape1 are in an even loop, so every stable model fails
// one of them. Call 1 must find such a model.
func TestCautiousCounterModel(t *testing.T) {
	out, _ := cautiousCall1(t, nil,
		[]cautiousShape{{id: 1, targets: []string{"a", "b"}}},
		[]string{"shape1($a)", "not shape1($b)"},
		[]string{"shape1($b)", "not shape1($a)"},
	)
	if !out.returned || out.status != satisfiable || len(out.atoms) != 1 {
		t.Errorf("expected a counter-model with exactly one of the two targets, got: %v", out)
	}
	shownOnlyShapes(t, out)
}

// The targets are spread over two shapes, each target holds in some model, and no model satisfies
// both. A counter-model needs only one shape to fail.
func TestCautiousCounterModelAcrossShapes(t *testing.T) {
	out, _ := cautiousCall1(t, nil,
		[]cautiousShape{{id: 1, targets: []string{"a"}}, {id: 2, targets: []string{"b"}}},
		[]string{"shape1($a)", "not shape2($b)"},
		[]string{"shape2($b)", "not shape1($a)"},
	)
	if !out.returned || out.status != satisfiable || len(out.atoms) != 1 {
		t.Errorf("expected a counter-model with exactly one of the two targets, got: %v", out)
	}
	shownOnlyShapes(t, out)
}

// A cx4-like document: there are two stable models, from an even loop between shape2 and shape3,
// and both satisfy the only target. Call 1 must be unsatisfiable. shape2 and shape3 have no targets,
// so this also checks that an untargeted shape does not keep the constraint from firing.
func TestCautiousNoCounterModel(t *testing.T) {
	out, _ := cautiousCall1(t, nil,
		[]cautiousShape{{id: 1, targets: []string{"a"}}, {id: 2}, {id: 3}},
		[]string{"shape1($a)"},
		[]string{"shape2($a)", "not shape3($a)"},
		[]string{"shape3($a)", "not shape2($a)"},
	)
	if !out.returned || out.status != unsatisfiable {
		t.Errorf("expected no counter-model, got: %v", out)
	}
}

// A target that was never grounded is false in every model, so every model is a counter-model.
func TestCautiousUngroundedTarget(t *testing.T) {
	out, _ := cautiousCall1(t, nil,
		[]cautiousShape{{id: 1, targets: []string{"a", "b"}}},
		[]string{"shape1($a)"},
	)
	if !out.returned || out.status != satisfiable {
		t.Errorf("expected a counter-model, got: %v", out)
	}
	shownOnlyShapes(t, out)
}

// An inactive shape is not validated, so its unsatisfied target must not produce a counter-model.
func TestCautiousInactiveShape(t *testing.T) {
	out, _ := cautiousCall1(t, nil,
		[]cautiousShape{{id: 1, targets: []string{"a"}}, {id: 2, targets: []string{"b"}, inactive: true}},
		[]string{"shape1($a)"},
	)
	if !out.returned || out.status != unsatisfiable {
		t.Errorf("expected no counter-model, got: %v", out)
	}
}

// Without targets nothing can fail, so call 1 must not find a counter-model, whether the document
// has shapes without targets or no active shape at all. If the constraint program is empty, the
// caller has to skip call 1 instead (plan phase 2, step 4); a merged run would then find the plain
// model and report it as a counter-model.
func TestCautiousNoTargets(t *testing.T) {
	for _, c := range []struct {
		name   string
		shapes []cautiousShape
	}{
		{"untargeted shapes", []cautiousShape{{id: 1}, {id: 2}}},
		{"inactive shapes", []cautiousShape{{id: 1, targets: []string{"a"}, inactive: true}}},
		{"no shapes", nil},
	} {
		t.Run(c.name, func(t *testing.T) {
			out, constraints := cautiousCall1(t, nil, c.shapes, []string{"shape1($a)"}, evenLoop[0], evenLoop[1])
			if constraints.IsEmpty() {
				return
			}
			if !out.returned || out.status != unsatisfiable {
				t.Errorf("expected no counter-model, got: %v\nconstraint program:\n%s", out, constraints)
			}
		})
	}
}

// Call 1 interrupted before any model is found: unknown, which the cautious branch turns into the
// Unknown verdict without running call 2. The program has no counter-model, and proving that needs
// the pigeonhole proof.
func TestCautiousTimeLimit(t *testing.T) {
	out, _ := cautiousCall1(t, []string{"--time-limit=1"},
		[]cautiousShape{{id: 1, targets: []string{"k"}}},
		[]string{"pigeon(1..12)"},
		[]string{"hole(1..11)"},
		[]string{"{aux}"},
		[]string{"shape1($k)", "not aux"},
		[]string{"{ at(P,H) : hole(H) } = 1", "pigeon(P)", "aux"},
		[]string{"", "at(P1,H)", "at(P2,H)", "P1<P2"},
	)
	if !out.returned || out.status != unknown {
		t.Errorf("expected an unknown run, got: %v", out)
	}
}

// Plan row 7: a qualified-count program from expandRules together with one even loop has the same
// number of stable models in clingo as in DLV. The solvers are called directly, since runClingo
// does not enumerate models.
func TestClingoModelCountMatchesDLV(t *testing.T) {
	clingo := requireClingo(t)
	if _, err := os.Stat(dlv); err != nil {
		t.Skipf("DLV binary not found at %s", dlv)
	}
	resetLPState(t)

	values := []rdf.Term{
		rdf.Resource{URI: "http://example.com/v0"},
		rdf.Resource{URI: "http://example.com/v1"},
	}
	v0, v1 := rewrite(values[0]), rewrite(values[1])

	// head(focus) holds iff exactly one value node conforms to shape1; shape1(v1) is a fact, and
	// shape1(v0) is decided by an even loop with shape2(v0).
	program := serialisedProgram{rules: expandRules(values, []int{0},
		[]dependency{qual1(1, 1, 1).dependency()}, "head", "focus")}
	program.rules = append(program.rules,
		serialisedRule{head: fmt.Sprintf("shape1(%s)", v1)},
		serialisedRule{head: fmt.Sprintf("shape1(%s)", v0), body: []string{fmt.Sprintf("not shape2(%s)", v0)}},
		serialisedRule{head: fmt.Sprintf("shape2(%s)", v0), body: []string{fmt.Sprintf("not shape1(%s)", v0)}},
	)
	text := program.String()

	dlvCmd := exec.Command(dlv, "-n=0")
	dlvCmd.Stdin = strings.NewReader(text)
	dlvOut, err := dlvCmd.CombinedOutput()
	if err != nil {
		t.Fatalf("DLV failed: %v\n%s\nprogram:\n%s", err, dlvOut, text)
	}
	var dlvModels, dlvWithHead int
	for _, line := range strings.Split(string(dlvOut), "\n") {
		if strings.HasPrefix(line, "{") {
			dlvModels++
			if parseDLVSet("M: "+line, "M")["head(focus)"] {
				dlvWithHead++
			}
		}
	}

	clingoCmd := exec.Command(clingo[0], append(clingo[1:], "--outf=2", "--warn=none", "-n0")...)
	clingoCmd.Stdin = strings.NewReader(text)
	var clingoErr strings.Builder
	clingoCmd.Stderr = &clingoErr
	clingoOut, _ := clingoCmd.Output() // a native clingo exits with 10, 20 or 30 on success
	var parsed struct {
		Call []struct {
			Witnesses []struct{ Value []string }
		}
		Result string
		Models struct{ Number int }
	}
	if err := json.Unmarshal(clingoOut, &parsed); err != nil || parsed.Result != "SATISFIABLE" {
		t.Fatalf("clingo failed: %v\nstdout:\n%s\nstderr:\n%s\nprogram:\n%s", err, clingoOut, clingoErr.String(), text)
	}
	var clingoWithHead int
	for _, call := range parsed.Call {
		for _, w := range call.Witnesses {
			for _, atom := range w.Value {
				if atom == "head(focus)" {
					clingoWithHead++
				}
			}
		}
	}

	if dlvModels != 2 || parsed.Models.Number != 2 {
		t.Errorf("expected 2 stable models from both solvers, got %d from DLV and %d from clingo\nprogram:\n%s",
			dlvModels, parsed.Models.Number, text)
	}
	if dlvWithHead != 1 || clingoWithHead != 1 {
		t.Errorf("expected head(focus) in exactly 1 model, got %d from DLV and %d from clingo\nprogram:\n%s",
			dlvWithHead, clingoWithHead, text)
	}
}
