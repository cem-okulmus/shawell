package main

import (
	"fmt"
	"os"
	"os/exec"
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
		"Head",
		"focus",
	)

	var headRule *serialisedRule
	for i := range rules {
		if rules[i].head == "Head(focus)" {
			headRule = &rules[i]
			break
		}
	}
	if headRule == nil {
		t.Fatalf("expected expanded rules to keep the primary head rule, got %#v", rules)
	}

	body := strings.Join(headRule.body, ",")
	if !strings.Contains(body, "Shape1(") {
		t.Fatalf("expected primary rule to keep existing dependency body, got %q", body)
	}
	if !strings.Contains(body, "OrShape1(") {
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
}

func (d depSpec) String() string {
	var refs []string
	for _, r := range d.refs {
		refs = append(refs, fmt.Sprint("Shape", r))
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
	max := d.max
	if d.mode != qualified {
		max = -1
	}
	return dependency{mode: d.mode, name: names, min: d.min, max: max, disjoint: d.disjoint}
}

func qual1(ref, min, max int) depSpec {
	return depSpec{mode: qualified, refs: []int{ref}, min: min, max: max}
}

// expansion is one call of expandRules: a head predicate and the dependencies of the expanded column.
// Dependencies in deps but not in cols act as siblings (relevant for sh:qualifiedValueShapesDisjoint).
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
					for si, s := range deps {
						if s.mode == qualified && !inCols[si] && w[s.refs[0]][v] {
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
		parts = append(parts, fmt.Sprintf("Shape%d={%s}", s, strings.Join(vals, ",")))
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
					program.WriteString(fmt.Sprintf("Shape%d(%s).\n", s, rewrite(values[v])))
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
					fmt.Sprint("Shape", in.id), rewrite(values[v]))
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
		for _, r := range d.refs {
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
// conforming to a sibling qualified shape (another column) are not counted.
func TestExpandRulesQualifiedDisjoint(t *testing.T) {
	cases := [][]depSpec{
		{{mode: qualified, refs: []int{1}, min: 1, max: -1, disjoint: true}, qual1(2, 1, -1)},
		{{mode: qualified, refs: []int{1}, min: 1, max: 1, disjoint: true}, qual1(2, 0, -1), qual1(3, 0, -1)},
		{{mode: qualified, refs: []int{1}, min: 0, max: 1, disjoint: true}, qual1(2, 1, -1)},
		{{mode: qualified, refs: []int{1}, min: 2, max: -1, disjoint: true}, qual1(2, 1, -1)},
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

	doc := GetShaclDocument(g, graphName, false)
	activeDoc = &doc
	report := answerShacl(ep, doc, config{silent: true, forceLP: forceLP})
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
