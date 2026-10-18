package main

import (
	"errors"
	"fmt"
	"log"
	"strings"

	"github.com/fatih/color"

	rdf "github.com/cem-okulmus/rdf2go-1"
)

type depMode int32

const (
	and depMode = iota
	or
	xone
	not
	qualified
	node
	property
)

type dependency struct {
	name      []ShapeRef    // the references used in a node-referring constraint inside a shape
	disjoint  bool          // used to indicate  we have a qualifiedValueShape constraint with disjointedness
	path      *PropertyPath // for external dep, store the path
	origin    string        // the (node or property) shape the dependency originates from
	originDep *dependency   // nil if not indirectDep
	external  bool          // whether the dep is refering to value nodes (external) or to focus node (internal)
	mode      depMode       // the type of reference that is used
	min       int           // used by qualifiedValueShape
	max       int           // used by qualifiedValueShape
}

type ShaclDocument struct {
	shapeNames       map[string]Shape           // used to unwind references to shapes
	condAnswers      map[string]Table[rdf.Term] // for each NodeShape, its (un)conditional answer
	uncondAnswers    map[string]Table[rdf.Term] // caches the results from unwinding
	undefinedAnswers map[string]Table[rdf.Term] // nodes whose shape membership is undefined under well-founded semantics
	targets          map[string]Table[rdf.Term] // the materialised targets of a given shape
	depMap           map[string][]dependency    // stores for each shape the dependant shapes
	answered         bool
	materialised     bool
	validated        bool
	debug            bool
	fromGraph        string
}

func (s ShaclDocument) String() string {
	var sb strings.Builder
	for _, t := range s.shapeNames {
		if t.IsBlank() && !s.debug {
			continue
		}
		sb.WriteString(fmt.Sprintln("\n", t.StringTab(0, false, s.debug)))
	}

	if s.debug {
		sb.WriteString("Deps: \n")

		for k := range s.shapeNames {

			deps := s.depMap[k]

			var sb2 strings.Builder

			var c *color.Color

			rec, _ := s.TransitiveClosure(k)
			// rec := false

			for _, d := range deps {

				if d.mode == not {
					c = color.New(color.FgRed).Add(color.Underline)
				} else {
					c = color.New(color.FgGreen).Add(color.Underline)
				}

				sb2.WriteString(" ")
				var namesString []string
				for _, sr := range d.name {
					namesString = append(namesString, sr.name)
				}
				if d.external {
					sb2.WriteString(c.Sprint(strings.Join(namesString, ", ")))
				} else {
					sb2.WriteString(c.Sprint("{", strings.Join(namesString, ", "), "}"))
				}

			}
			if len(deps) == 0 {
				sb.WriteString(fmt.Sprint(k, " is independent. \n"))
			} else {
				if rec {
					sb.WriteString(fmt.Sprint(k, "(rec.) depends on ", sb2.String(), ". \n"))
				} else {
					sb.WriteString(fmt.Sprint(k, " depends on ", sb2.String(), ". \n"))
				}
			}
		}
	}
	if s.debug || demoLP {
		sb.WriteString("\nQualnames: \n")
		for k, v := range s.shapeNames {
			sb.WriteString(fmt.Sprint(k, " : ", v.GetQualName(), " ", v.GetLogName(), "\n"))
		}
	}

	// fmt.Println("BEFORE ABBR", sb.String())

	return abbr(sb.String())
}

// GetSubjectFromTriples extracts all unique subject terms from a slice of RDF triples.
func GetSubjectFromTriples(triples []*rdf.Triple) (subjects []rdf.Term) {
	for i := range triples {
		subjects = append(subjects, triples[i].Subject)
	}
	return subjects
}

// GetShapeObjects returns the objects of the given triples that can be shapes, i.e. all but literals.
func GetShapeObjects(triples []*rdf.Triple) (objects []rdf.Term) {
	for i := range triples {
		if _, isLiteral := triples[i].Object.(*rdf.Literal); !isLiteral {
			objects = append(objects, triples[i].Object)
		}
	}
	return objects
}

// GetListMembers returns the members of an RDF list that can be shapes, i.e. all but literals.
func GetListMembers(graph *rdf.Graph, list rdf.Term) (members []rdf.Term) {
	visited := make(map[string]bool) // guards against malformed, cyclic lists
	for list != nil && list.RawValue() != _rdf+"nil" && !visited[list.String()] {
		visited[list.String()] = true
		if first := graph.One(list, rdf.NewResource(_rdf+"first"), nil); first != nil {
			if _, isLiteral := first.Object.(*rdf.Literal); !isLiteral {
				members = append(members, first.Object)
			}
		}
		rest := graph.One(list, rdf.NewResource(_rdf+"rest"), nil)
		if rest == nil {
			break
		}
		list = rest.Object
	}
	return members
}

// GetNodeTerms returns all terms that appear in the SHACL document as the subject of a triple
// appearing inside a SHACL node shape.
func GetNodeTerms(graph *rdf.Graph) []rdf.Term {
	out := GetSubjectFromTriples(graph.All(nil, rdf.NewResource(_rdf+"type"), rdf.NewResource(_sh+"NodeShape")))

	out = append(out, GetSubjectFromTriples(graph.All(nil, rdf.NewResource(_sh+"targetClass"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, rdf.NewResource(_sh+"targetNode"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, rdf.NewResource(_sh+"targetObjectsOf"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, rdf.NewResource(_sh+"targetSubjectsOf"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, rdf.NewResource(_sh+"class"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, rdf.NewResource(_sh+"datatype"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, rdf.NewResource(_sh+"nodeKind"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, rdf.NewResource(_sh+"minExclusive"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, rdf.NewResource(_sh+"maxExclusive"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, rdf.NewResource(_sh+"minInclusive"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, rdf.NewResource(_sh+"maxInclusive"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, rdf.NewResource(_sh+"minLength"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, rdf.NewResource(_sh+"maxLength"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, rdf.NewResource(_sh+"pattern"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, rdf.NewResource(_sh+"languageIn"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, rdf.NewResource(_sh+"equals"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, rdf.NewResource(_sh+"disjoint"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, rdf.NewResource(_sh+"lessThan"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, rdf.NewResource(_sh+"lessThanOrEquals"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, rdf.NewResource(_sh+"property"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, rdf.NewResource(_sh+"and"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, rdf.NewResource(_sh+"or"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, rdf.NewResource(_sh+"not"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, rdf.NewResource(_sh+"xone"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, rdf.NewResource(_sh+"node"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, rdf.NewResource(_sh+"qualifiedValueShape"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, rdf.NewResource(_sh+"closed"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, rdf.NewResource(_sh+"hasValue"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, rdf.NewResource(_sh+"in"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, rdf.NewResource(_sh+"severity"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, rdf.NewResource(_sh+"message"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, rdf.NewResource(_sh+"deactivated"), nil))...)

	// shapes that only appear as the value of a shape-referencing constraint, e.g. sh:node ex:S where ex:S
	// has no triples of its own, are shapes as well (without constraints)
	for _, p := range []string{"node", "not", "qualifiedValueShape"} {
		out = append(out, GetShapeObjects(graph.All(nil, rdf.NewResource(_sh+p), nil))...)
	}
	for _, p := range []string{"and", "or", "xone"} {
		for _, t := range graph.All(nil, rdf.NewResource(_sh+p), nil) {
			out = append(out, GetListMembers(graph, t.Object)...)
		}
	}

	out = removeDuplicate(out)

	// remove anything that has path

	pathStuff := GetSubjectFromTriples(graph.All(nil, rdf.NewResource(_sh+"path"), nil))

	var finalOut []rdf.Term

Outer:
	for i := range out {
		for j := range pathStuff {
			if out[i].String() == pathStuff[j].String() {
				continue Outer
			}
		}
		finalOut = append(finalOut, out[i])
	}

	return finalOut
}

// GetShaclDocument parses an RDF graph containing a SHACL document and extracts all defined shapes.
// It returns a fully initialized ShaclDocument with shapes indexed by their IRIs, ready for validation.
// Parameters:
//   - rdfGraph: RDF graph parsed from Turtle or other RDF format
//   - fromGraph: the named graph URI where the data is stored
//   - debug: enables debug output during parsing
func GetShaclDocument(rdfGraph *rdf.Graph, fromGraph string, debug bool) (out ShaclDocument) {
	// var detected bool = true
	out.shapeNames = make(map[string]Shape)
	out.condAnswers = make(map[string]Table[rdf.Term])
	out.uncondAnswers = make(map[string]Table[rdf.Term])
	out.undefinedAnswers = make(map[string]Table[rdf.Term])
	out.targets = make(map[string]Table[rdf.Term])
	out.depMap = make(map[string][]dependency)
	out.materialised = false
	out.fromGraph = fromGraph

	for _, t := range GetNodeTerms(rdfGraph) {
		name := t.RawValue()

		// check if already encountered; if so skip
		_, ok := out.shapeNames[name]
		if ok {
			continue
		}

		out.GetNodeShape(rdfGraph, t, nil)
	}

	PropertyShapeTriples := rdfGraph.All(nil, rdf.NewResource(_sh+"path"), nil)
	// fmt.Println(res(sh+"NodeShape"), " of node shapes, ", NodeShapeTriples)

	for _, t := range PropertyShapeTriples {
		// fmt.Println("Got Propert term", t.Subject.String())
		name := t.Subject.RawValue()

		// check if already encountered; if so skip
		_, ok := out.shapeNames[name]
		if ok {
			continue
		}

		out.GetPropertyShape(rdfGraph, t.Subject)
	}

	// compute transitive Closure of deps

	for name := range out.shapeNames {
		_, out.depMap[name] = out.TransitiveClosure(name)
	}

	// // attach indirect Targets (hope this pointer stuff works)
	// for k, v := range out.depMap {
	// 	tmp := out.shapeNames[k].GetTargets(true)

	// 	for _, dep := range v {
	// 		for _, s := range dep.name {
	// 			var indirects []TargetIndirect
	// 			for i := range tmp {
	// 				indirect := DepToIndirectTarget(dep, tmp[i])
	// 				indirects = append(indirects, indirect)
	// 			}
	// 			if debug {
	// 				fmt.Println("Gotten ", len(tmp), " targets from dependant. Path ", dep.path)

	// 				// fmt.Println("Number of dependant shapes: ", len(v))
	// 				fmt.Println("Adding ", len(indirects), " indirect targets to shape ", s.name, " from origin ", k)
	// 			}

	// 			out.shapeNames[s.name].AddIndirectTargets(indirects, nil) // don't change paths, as they were already defined abvoes
	// 		}
	// 	}
	// }

	// attach indirect targets: the targets of a shape S are its direct targets, the values of every
	// path through which some shape references S, and the targets of every shape that references S
	// without a path. The last part is computed as a fixpoint, since such references can form cycles.

	// the target expressions each shape already has, by their query, to detect new ones
	known := make(map[string]map[string]bool)
	for name, shape := range out.shapeNames {
		known[name] = make(map[string]bool)
		for _, t := range shape.GetTargets(true) {
			known[name][GetTargetTerm(t)] = true
		}
	}
	add := func(name string, targets []TargetIndirect) (added bool) {
		for _, t := range targets {
			key := GetTargetTerm(t)
			if known[name][key] {
				continue
			}
			known[name][key] = true
			out.shapeNames[name].AddIndirectTargets([]TargetIndirect{t}, nil)
			added = true
		}
		return added
	}

	// references through a path: the path's values from any node, independent of the referencing shape
	for _, shape := range out.shapeNames {
		for _, dep := range shape.GetDeps() {
			if dep.path == nil {
				continue
			}
			for _, ref := range dep.name {
				add(ref.name, []TargetIndirect{{actual: TargetAny{}, indirection: dep.path}})
			}
		}
	}

	// references without a path: the referencing shape's targets, until no shape gains a new one
	for changed := true; changed; {
		changed = false
		for _, shape := range out.shapeNames {
			for _, dep := range shape.GetDeps() {
				if dep.path != nil {
					continue
				}
				targets := append([]TargetExpression(nil), shape.GetTargets(true)...) // a copy, see below
				for _, ref := range dep.name {
					if add(ref.name, TransformToIndirect(targets)) {
						changed = true
					}
				}
			}
		}
	}

	return out
}

// mem checks if an integer b occurs inside a slice as
func mem(aas Table[rdf.Term], b rdf.Term) bool {
	for as := range aas.IterRows() {
		for _, a := range as {
			// fmt.Println("Comparing ", a.RawValue(), " with ", b.RawValue())
			if a.RawValue() == b.RawValue() {
				return true
			}
		}
	}

	return false
}

// memSibling checks if sibling terms of b occur in the table.
func memSibling(aas Table[rdf.Term], b rdf.Term, sib []rdf.Term) bool {
	for as := range aas.IterRows() {
	inner:
		for _, a := range as {
			for i := range sib {
				if a.RawValue() == sib[i].RawValue() {
					continue inner
				}
			}
			if a.RawValue() == b.RawValue() {
				return true
			}
		}
	}

	return false
}

// memListQual checks if a qualified constraint is satisfied for a list of terms with min/max cardinality bounds.
func memListQual(aas Table[rdf.Term], b []rdf.Term, minVal, maxVal int) bool {
	count := 0
	for _, e := range b {
		out := mem(aas, e)
		if out {
			count = count + 1
		}
	}

	var out bool
	if maxVal != -1 {
		out = (count >= minVal) && (count <= maxVal)
	} else {
		out = (count >= minVal)
	}

	return out
}

// memListQualSibling checks if qualified constraint is satisfied for a list with sibling terms and cardinality bounds.
func memListQualSibling(aas Table[rdf.Term], b []rdf.Term, minVal, maxVal int, siblings []rdf.Term) bool {
	// fmt.Println("Vals to CHeck", b)
	// fmt.Println("Siblings: ", siblings)
	// fmt.Println("Min: ", min, " ", "max: ", max)
	// fmt.Println("aas: ", aas)

	count := 0
	for _, e := range b {
		out := memSibling(aas, e, siblings)
		// fmt.Println("out for ", e, " is ", out)
		if out {
			count = count + 1
		}
	}

	var out bool
	if maxVal != -1 {
		out = (count >= minVal) && (count <= maxVal)
	} else {
		out = (count >= minVal)
	}

	return out
}

// memListXone checks if exactly one shape in the list of tables contains the term.
func memListXone(toCheck []Table[rdf.Term], b []rdf.Term) bool {
	// elements := strings.Split(b.RawValue(), " ")
	for _, e := range b {
		matchOne := false

		for i := range toCheck {
			out := mem(toCheck[i], e)
			if out && matchOne {
				return false
			}

			if out {
				matchOne = true
			}
		}
		if !matchOne {
			return false
		}
	}

	return true
}

// memListOr checks if at least one shape in the list of tables contains the term.
func memListOr(toCheck []Table[rdf.Term], b []rdf.Term) bool {
	// elements := strings.Split(b.RawValue(), " ")

	for _, e := range b {
		passed := false
		for i := range toCheck {
			out := mem(toCheck[i], e)
			if out {
				passed = true
			}
		}
		if !passed {
			return false
		}
	}

	return true
}

// memListOne returns true, if any one element is included
func memListOne(aas Table[rdf.Term], b []rdf.Term) bool {
	// elements := strings.Split(b.RawValue(), " ")

	for _, e := range b {
		out := mem(aas, e)
		if out {
			return true
		}
	}

	return false
}

// memListAll checks if all terms from list b occur in the table.
func memListAll(aas Table[rdf.Term], b []rdf.Term) bool {
	// elements := strings.Split(b.RawValue(), " ")

	for _, e := range b {
		out := mem(aas, e)
		if !out {
			return false
		}
	}

	return true
}

// TransitiveClosure computes the transitive closure of dependencies for a named shape,
// returning whether the shape has recursive dependencies and the full transitive closure.
func (s ShaclDocument) TransitiveClosure(name string) (bool, []dependency) {
	return s.TransitiveClosureRec(name, []string{})
}

// DepToIndirectTarget converts a single dependency into an indirect target expression
// for use in conditional answer computation.
func DepToIndirectTarget(dep dependency, actual TargetExpression) TargetIndirect {
	var out TargetIndirect

	if dep.originDep == nil {
		out = TargetIndirect{
			actual:      actual,
			indirection: dep.path,
			level:       0,
		}
	} else {
		inner := DepToIndirectTarget(*dep.originDep, actual)
		out = TargetIndirect{
			actual:      inner,
			indirection: dep.path,
			level:       inner.level + 1,
		}
	}

	return out
}

// TransitiveClosureRec recursively computes the transitive closure of dependencies,
// tracking visited shapes to avoid infinite recursion.
func (s ShaclDocument) TransitiveClosureRec(name string, visited []string) (bool, []dependency) {
	var out1, out2 []dependency

	visited = append(visited, name)

	// fmt.Println("Visited: ", visited)

	if _, ok := s.shapeNames[name]; ok {
		out1 = append(out1, s.shapeNames[name].GetDeps()...)
	}

	out2 = append(out2, out1...)

	// fmt.Println("new deps: ", out1)

	for i := range out1 {
		for j := range visited {
			for k := range out1[i].name {
				if out1[i].name[k].name == visited[j] {
					return true, out2 // in case of recursive deps, we quit once we hit loop
				}
			}
		}

		for k := range out1[i].name {
			isRec, newDeps := s.TransitiveClosureRec(out1[i].name[k].name, visited)

			if isRec {
				return true, append(newDeps, out2...)
			}
			for _, newDep := range newDeps {
				newDep.originDep = &out1[i]
				out2 = append(out2, newDep)
			}

		}
	}

	return false, out2
}

// func removeSimple[T stringer](s []T, i int) []T {
// 	s[i] = s[len(s)-1]
// 	return s[:len(s)-1]
// }

// removes the element at index i from a 2D slice.
func remove[T stringer](s [][]T, i int) [][]T {
	s[i] = s[len(s)-1]
	return s[:len(s)-1]
}

// AllCondAnswers computes conditional answers for all node shapes in the document.
// A conditional answer indicates which focus nodes satisfy a shape's constraints,
// conditioned on whether other shapes are satisfied.
func (s *ShaclDocument) AllCondAnswers(ep endpoint) {
	if s.debug {
		fmt.Println("Started AllCondAnswers")
	}

	// don't repeat this for the same document
	if s.answered {
		return
	}

	for k, v := range s.shapeNames {
		if s.debug {
			fmt.Println("Current shape ", k)
		}

		if !v.IsActive() {
			continue
		}
		// if no targets defined for a shape, then skip it (nothing to query, nothing to check)
		if len(v.GetTargets(true)) == 0 {
			continue
		}

		targetQueries, _ := s.GetTargetShape(k)

		out := ep.Answer(v, targetQueries)
		if s.debug {
			fmt.Println("For shape", k, " we got the Conditional Answers ", out.Limit(10))
		}
		s.condAnswers[k] = out
	}

	s.answered = true
}

// removeDuplicateVR removes duplicate validation results from a slice.
func removeDuplicateVR(sliceList []ValidationResult) []ValidationResult {
	allKeys := make(map[string]bool)
	list := []ValidationResult{}
	for _, item := range sliceList {
		stringRep := item.StringComp()
		if _, value := allKeys[stringRep]; !value {
			allKeys[stringRep] = true
			list = append(list, item)
		}
	}
	return list
}

// removeDuplicate removes duplicate elements from a comparable slice.
func removeDuplicate[T comparable](sliceList []T) []T {
	allKeys := make(map[T]bool)
	list := []T{}

	for _, item := range sliceList {
		if _, value := allKeys[item]; !value {
			allKeys[item] = true
			list = append(list, item)
		}
	}

	return list
}

// GetAffectedIndices returns the indices in uncondTable of nodes affected by a dependency,
// considering qualified value shape cardinality constraints (min/max) and sibling nodes.
func (s *ShaclDocument) GetAffectedIndices(ref ShapeRef, dep dependency, uncondTable Table[rdf.Term], minVal, maxVal int, siblings *[]Shape) []rdf.Term {
	var affectedIndices []rdf.Term
	var depTable Table[rdf.Term]

	if _, ok := s.uncondAnswers[ref.name]; ok {
		depTable = s.uncondAnswers[ref.name]
	} else {
		depTable = s.UnwindAnswer(ref.name) // recursively compute the needed uncond. answers
	}
	if s.debug {
		fmt.Println("Depending Table\n", depTable)
	}
	// NOTE: this only works for non-recursive shapes
	// we now know that we deal with unconditional (unary) answers
	if len(depTable.GetHeader()) > 1 {
		log.Panic("Received non-unary uncond. Answer! ", depTable)
	}

	var c int // column to compare

	if dep.external {
		found := false
		for i, h := range uncondTable.GetHeader() {

			if strings.HasPrefix(h, dep.origin) {
				found = true
				if s.debug {
					fmt.Println("Origin dap name: ", dep.origin)
				}
				c = i

				// fmt.Println("||||||||||--------  Header ", h, " to Compare with ", dep.origin, " c = ", i)

				// fmt.Println("Depending Table\n", depTable)

				// fmt.Println("other Table \n ", uncondTable)

				// fmt.Println("Depeche Mode: ", dep.mode)

				// fmt.Println("|||||||||--------")

			}
		}
		if !found {
			log.Panic("Couldn't find dep ", dep.name, " with origin ", dep.origin, " inside ", uncondTable.GetHeader())
		}
	} else {
		c = 0 // intrinsic checks are made against the node shape itself
	}

	// compute siblings for qualifiedValueShape
	var siblingValues []rdf.Term
	if dep.disjoint && siblings != nil {
		for _, shape := range *siblings {
			var sibTable Table[rdf.Term]
			name := shape.GetIRI()
			// fmt.Println("GEAFF: From Sibling: ", name)

			if _, ok := s.uncondAnswers[name]; ok {
				sibTable = s.uncondAnswers[name]
			} else {
				sibTable = s.UnwindAnswer(name) // recursively compute the needed uncond. answers
			}

			// fmt.Println("GEAFF: UnCondAnsers: ", sibTable)

			for row := range sibTable.IterRows() {
				siblingValues = append(siblingValues, row[0])
			}
		}
	}

	// check if uncondTable is grouped
	uncondTableGrouped, ok := uncondTable.(*GroupedTable[rdf.Term])

	if !ok {
		log.Panicln("Given a non-grouped Table for affected Index Check")
	}

	for target := range uncondTableGrouped.IterTargets() {
		switch dep.mode {
		case node, property:
			if memListAll(depTable, uncondTableGrouped.GetGroupOfTarget(target, c)) {
				// val, err := uncondTableGrouped.GetIndex(target)
				// check(err)
				affectedIndices = append(affectedIndices, target)
			}

		case not:
			// fmt.Println("CHecking target", target)
			if memListOne(depTable, uncondTableGrouped.GetGroupOfTarget(target, c)) {
				// val, err := uncondTableGrouped.GetIndex(target)
				// check(err)
				affectedIndices = append(affectedIndices, target)
				// fmt.Println("Adding target", target, " to affected indices")
			}
		case and:
			// fmt.Println("Checking affected pos for AND")
			if memListAll(depTable, uncondTableGrouped.GetGroupOfTarget(target, c)) {
				// fmt.Println("Keeping term ", uncondTableGrouped.GetGroupOfTarget(target, c))
				// val, err := uncondTableGrouped.GetIndex(target)
				// check(err)
				affectedIndices = append(affectedIndices, target)
			}
		case or:
			var depTableAll []Table[rdf.Term]

			for _, ref := range dep.name {
				var tmp Table[rdf.Term]
				if _, ok := s.uncondAnswers[ref.name]; ok {
					tmp = s.uncondAnswers[ref.name]
				} else {
					tmp = s.UnwindAnswer(ref.name) // recursively compute the needed uncond. answers
				}
				depTableAll = append(depTableAll, tmp)
			}

			// fmt.Println("Group gotten: ", uncondTableGrouped.GetGroupOfTarget(target, c))
			if memListOr(depTableAll, uncondTableGrouped.GetGroupOfTarget(target, c)) {
				if s.debug {
					fmt.Println("Keeping term ", target)
				}

				// val, err := uncondTableGrouped.GetIndex(target)
				// check(err)
				affectedIndices = append(affectedIndices, target)
			}
		case xone:
			var depTableAll []Table[rdf.Term]

			for _, ref := range dep.name {
				var tmp Table[rdf.Term]
				if _, ok := s.uncondAnswers[ref.name]; ok {
					tmp = s.uncondAnswers[ref.name]
				} else {
					tmp = s.UnwindAnswer(ref.name) // recursively compute the needed uncond. answers
				}
				depTableAll = append(depTableAll, tmp)
			}
			if memListXone(depTableAll, uncondTableGrouped.GetGroupOfTarget(target, c)) {
				// val, err := uncondTableGrouped.GetIndex(target)
				// check(err)
				affectedIndices = append(affectedIndices, target)
			}
		case qualified:
			if dep.disjoint {
				// fmt.Println("For Table ", uncondTableGrouped)

				// fmt.Println("Got group ", target, " ", c, " ", uncondTableGrouped.GetGroupOfTarget(target, c))
				// fmt.Println("Shape to CHeck", ref.name)

				if memListQualSibling(depTable, uncondTableGrouped.GetGroupOfTarget(target, c), minVal, maxVal, siblingValues) {
					// val, err := uncondTableGrouped.GetIndex(target)
					// check(err)
					// fmt.Println("Adding target ", target)
					affectedIndices = append(affectedIndices, target)
				}
			} else {
				if s.debug {
					fmt.Println("|||||||", " GOING INTO NON disjointedness  PATH")
				}
				if memListQual(depTable, uncondTableGrouped.GetGroupOfTarget(target, c), minVal, maxVal) {
					// val, err := uncondTableGrouped.GetIndex(target)
					// check(err)
					affectedIndices = append(affectedIndices, target)
				}
			}

		}
	}
	return affectedIndices
}

// IsRecursive checks for each shape whether it depends (in its transitive closure) on itself
func (s *ShaclDocument) IsRecursive() bool {
	for shape := range s.shapeNames {
		rec, _ := s.TransitiveClosure(shape)

		if rec {
			return true
		}
	}

	return false
}

type membership int

const (
	isIn membership = iota
	isOut
	isUndefined
)

// NodeMembership returns whether a node is in a shape, not in it, or (for recursive documents under
// the well-founded semantics) undefined.
func (s *ShaclDocument) NodeMembership(node rdf.Term, shape string) membership {
	if s.NodeIsShape(node, shape) {
		return isIn
	}
	if undefined, ok := s.undefinedAnswers[shape]; ok {
		for row := range undefined.IterRows() {
			if row[0].RawValue() == node.RawValue() {
				return isUndefined
			}
		}
	}
	return isOut
}

// NodeIsShape checks if a given node has a given shape, or not
func (s *ShaclDocument) NodeIsShape(node rdf.Term, shape string) bool {
	if !s.answered {
		log.Panicln("Called method NodeIsShape before document was answered")
	}

	table, found := s.uncondAnswers[shape]

	if !found { // empty shape contains no nodes
		return false
	}

	for row := range table.IterRows() {
		if row[0].RawValue() == node.RawValue() {
			return true
		}
	}

	if s.debug {
		fmt.Println("Node ", node, " is not in shape ", shape)
	}
	return false
}

// UnwindAnswer computes the unconditional answers
func (s *ShaclDocument) UnwindAnswer(name string) Table[rdf.Term] {
	if !s.answered {
		return s.uncondAnswers[name] // just return empty table if answers not computed yet
	}

	// for k, v := range s.condAnswers {

	// 	fmt.Println("For the shape ", k, " we got the uncond Table: \n", v)

	// }

	// check if result is already cached
	if out, ok := s.uncondAnswers[name]; ok {
		return out
	}

	shape, ok := s.shapeNames[name]

	if !ok {
		log.Panic(name, " is not a defined node  shape")
	}

	uncondTablePreCheck, found := s.condAnswers[name]
	// this means that, for various reasons, there is no table and thus no answer to this shape
	if !found {
		return &TableSimple[rdf.Term]{
			header: []string{name},
		}
	}

	uncondTable, ok := uncondTablePreCheck.(*GroupedTable[rdf.Term])
	if !ok {
		fmt.Println(uncondTablePreCheck)
		log.Panicln("Received uncondTable that is not grouped!")
	}

	if s.debug {
		fmt.Println("At Shape", name, " with Qualname ", s.shapeNames[name].GetQualName())
		fmt.Println("InUnWindANswer, HEader from saved CondAnswers ", len(uncondTable.GetHeader()), " len: ", len(uncondTable.content))
	}

	deps := shape.GetDeps()

	rec, _ := s.TransitiveClosure(name)
	// check if recursive shape
	if rec {
		log.Panic(name, " is a recursive SHACL node  shape, as it depends on itself.")
	}

	for _, dep := range deps {
		switch dep.mode {
		case node, property:

			ref := dep.name[0] // node has only single reference (current design)
			affectedIndices := s.GetAffectedIndices(ref, dep, uncondTable, dep.min, dep.max, nil)

			// only keep the affected indices in and case
			temp := GroupedTable[rdf.Term]{
				header: uncondTable.header,
			}

			for i := range affectedIndices {
				temp.AddIndex(affectedIndices[i], uncondTable)
			}

			uncondTable = &temp
		case and:
			for _, ref := range dep.name {
				// filtering out answers from uncondTable
				affectedIndices := s.GetAffectedIndices(ref, dep, uncondTable, dep.min, dep.max, nil)

				// only keep the affected indices in and case
				temp := GroupedTable[rdf.Term]{
					header: uncondTable.header,
				}

				for i := range affectedIndices {
					temp.AddIndex(affectedIndices[i], uncondTable)
				}

				uncondTable = &temp
				uncondTable.Regroup()
			}
		case not:
			ref := dep.name[0] // not has only single reference (current design)

			affectedIndices := s.GetAffectedIndices(ref, dep, uncondTable, dep.min, dep.max, nil)

			// using reverse sort to "safely" remove indices from slice while iterating over them
			// sort.Sort(sort.Reverse(sort.IntSlice(affectedIndices)))
			for i := range affectedIndices {
				uncondTable.RemoveIndex(affectedIndices[i]) // needs to be implem
			}

		case or:
			allAffected := s.GetAffectedIndices(dep.name[0], dep, uncondTable, dep.min, dep.max, nil)

			// wonder if this will workdepTableAll

			// only keep those that match at least one dep
			temp := GroupedTable[rdf.Term]{
				header: uncondTable.header,
			}
			for i := range allAffected {
				temp.AddIndex(allAffected[i], uncondTable)
			}

			uncondTable = &temp
		case xone:
			// similar to or, but compute the symmetric difference at every step
			allAffected := s.GetAffectedIndices(dep.name[0], dep, uncondTable, dep.min, dep.max, nil)

			// only keep those that match at least one dep
			temp := GroupedTable[rdf.Term]{
				header: uncondTable.header,
			}
			for i := range allAffected {
				temp.AddIndex(allAffected[i], uncondTable)
			}

			uncondTable = &temp

		case qualified:
			if !dep.external {
				continue // skip the check of qualified value shapes when defined in a node shape
				//  Technically this should even throw a panic, but SHACL Test Suite allows this for some reason
			}

			// compute Siblings

			ref := dep.name[0] // qualifiedValueShape too has only single reference

			siblings, err := s.DefineSiblingValues(name, ref.name)
			check(err)

			affectedIndices := s.GetAffectedIndices(ref, dep, uncondTable, dep.min, dep.max, siblings)

			// only keep the affected indices in and case
			temp := GroupedTable[rdf.Term]{
				header: uncondTable.header,
			}

			for i := range affectedIndices {
				temp.AddIndex(affectedIndices[i], uncondTable)
			}

			uncondTable = &temp
		}

		uncondTable.Regroup()
	}

	newTable := &GroupedTable[rdf.Term]{}
	newTable.header = uncondTable.header[:1]

	if len(uncondTable.group) > 0 {
		for k := range uncondTable.group {
			newTable.content = append(newTable.content, []rdf.Term{k})
		}
	} else {
		for i := range uncondTable.content {
			newTable.content = append(newTable.content, uncondTable.content[i][:1])
		}
	}

	// create the new mapping
	s.uncondAnswers[name] = newTable

	if s.debug {
		fmt.Println("UNCOND ANSWER:")
		fmt.Println("Shape ", name, "\n", newTable)
	}

	return s.uncondAnswers[name]
}

// GetTargetShape produces the subquery needed to reduce the focus nodes to those described
// in the target expressions, understood as the union overall target expressions.
func (s *ShaclDocument) GetTargetShape(name string) (out []SparqlQueryFlat, empty bool) {
	ns, ok := s.shapeNames[name]
	if !ok {
		log.Panic(name, " is not a defined node  shape")
	}

	targets := ns.GetTargets(true)

	out = TargetsToQueries(targets)

	return out, false
}

func (s *ShaclDocument) GetValidTargetShape(name string) (out []SparqlQueryFlat, empty bool) {
	ns, ok := s.shapeNames[name]
	if !ok {
		log.Panic(name, " is not a defined node  shape")
	}

	targets := ns.GetTargets(false)

	out = TargetsToQueries(targets)

	return out, false
}

func TargetsToQueries(targets []TargetExpression) (out []SparqlQueryFlat) {
	var queries []string

	for i := range targets {
		term := GetTargetTerm(targets[i])
		queries = append(queries, term)
	}

	for i := range queries {
		out = append(out, SparqlQueryFlat{
			head: "?sub ?indirect0",
			body: []string{queries[i]},
		})
	}

	return out
}

func (s *ShaclDocument) MaterialiseTargets(ep endpoint) {
	if s.materialised { // don't repeat this for same document
		return
	}

	for name := range s.shapeNames {
		// fmt.Println("Getting targetes for shape ", name)
		var out Table[rdf.Term]

		targetQueries, empty := s.GetValidTargetShape(name)
		if empty || len(targetQueries) == 0 {
			s.targets[name] = &TableSimple[rdf.Term]{}
			continue
		}

		for i := range targetQueries {
			targetQueries[i].graph = ep.GetGraph()
			tmp := ep.QueryFlat(targetQueries[i])

			// out.content = append(out.content, tmp.content...)
			if out == nil {
				out = tmp
			} else {
				err := out.Merge(tmp)
				check(err)
			}
		}

		if out == nil {
			s.targets[name] = &TableSimple[rdf.Term]{}
		} else {
			s.targets[name] = out
		}

	}

	s.materialised = true
}

// InvalidTargets compares the targets of a node shape against the decorated graph and
// returns those targets that do not have this shape
func (s *ShaclDocument) InvalidTargets(shape string, ep endpoint) Table[rdf.Term] {
	var out TableSimple[rdf.Term]
	if !s.answered {
		s.AllCondAnswers(ep)
	}

	if !s.materialised {
		s.MaterialiseTargets(ep)
	}

	nodesWithShape := s.UnwindAnswer(shape)
	// fmt.Println("All nodes with shape: ", shape)
	// fmt.Println(nodesWithShape)

	// fmt.Println("Answers: ", len(nodesWithShape.content))

	// targets := s.GetTargets(shape, ep)
	// if !hasTargets {
	// 	return out, false
	// }

	if strings.HasPrefix(shape, _sh) {
		out.header = append(out.header, "Not "+shape[len(_sh):])
	} else {
		out.header = append(out.header, "Not "+shape)
	}

	targets, ok := s.targets[shape]
	if !ok {
		log.Panicln("Cannot get Targets for undefined shape", shape)
	}
	// fmt.Println("Targets of shape: ", shape)
	// fmt.Println(targets)

outer:
	for tRow := range targets.IterRows() {
		for nRow := range nodesWithShape.IterRows() {
			if nRow[0].RawValue() == tRow[0].RawValue() {
				continue outer
			}
			// fmt.Println("Term ", n[0], " not equal to ", t[0])
		}
		out.content = append(out.content, tRow)
	}

	// fmt.Println("My invalid targets for: ", shape)
	// fmt.Println(out)

	return &out
}

// InvalidTargets compares the targets of a node shape against the decorated graph and
// returns those targets that do not have this shape
func (s *ShaclDocument) InvalidTargetLP(shape string, ep endpoint) Table[rdf.Term] {
	var out TableSimple[rdf.Term]
	if !s.materialised {
		s.MaterialiseTargets(ep)
	}

	shapeObj := s.shapeNames[shape]

	nodesWithShape, found := s.uncondAnswers[shape]
	if !found {
		nodesWithShape = &TableSimple[rdf.Term]{}
	}

	// undefinedNodes, _ := s.undefinedAnswers[shape]

	out.header = append(out.header, "Not "+shapeObj.GetIRI())

	targets := s.targets[shape]

outer:
	for tRow := range targets.IterRows() {

		for nRow := range nodesWithShape.IterRows() {
			if nRow[0].RawValue() == tRow[0].RawValue() {
				continue outer
			}
		}

		// if undefinedNodes != nil {
		// 	for nRow := range undefinedNodes.IterRows() {
		// 		if nRow[0].RawValue() == tRow[0].RawValue() {
		// 			continue outer // undefined membership is not a violation
		// 		}
		// 	}
		// }

		out.content = append(out.content, []rdf.Term{tRow[0]})
	}

	return &out
}

// Validate checks for each of the node shapes of a SHACL document, whether their target nodes
// occur in the decorated graph with the shapes they are supposed to. If not, it returns false
// as well as list of tables for each node shape of the nodes that fail validation.
func (s *ShaclDocument) Validate(ep endpoint) (bool, map[string]Table[rdf.Term]) {
	out := make(map[string]Table[rdf.Term])
	// var outExp map[string][]string = make(map[string][]string)
	result := true

	// Produce InvalidTargets for each node shape
	for _, shape := range s.shapeNames {
		if shape.IsActive() { // deactivated shapes do not factor the validation
			iri := shape.GetIRI()

			invalidTargets := s.InvalidTargets(iri, ep)
			if invalidTargets.Len() > 0 {
				out[iri] = invalidTargets
				// outExp[iri] = abbrAll(explanations)
				result = false
			}
		}
	}

	s.validated = true

	return result, out
}

// Validate checks for each of the node shapes of a SHACL document, whether their target nodes
// occur in the decorated graph with the shapes they are supposed to. If not, it returns false
// as well as list of tables for each node shape of the nodes that fail validation.
func (s *ShaclDocument) ValidateLP(ep endpoint) (bool, map[string]Table[rdf.Term]) {
	out := make(map[string]Table[rdf.Term])
	// var outExp map[string][]string = make(map[string][]string)
	result := true

	// Produce InvalidTargets for each node shape
	for _, shape := range s.shapeNames {
		if shape.IsActive() { // deactivated shapes do not factor the validation
			iri := shape.GetIRI()
			invalidTargets := s.InvalidTargetLP(iri, ep)
			if invalidTargets.Len() > 0 {
				out[iri] = invalidTargets
				// outExp[iri] = abbrAll(explanations)
				result = false
			}
		}
	}

	s.validated = true

	return result, out
}

// AdoptLPAnswers takes the computed answers from the logic program and populates
// uncondAnswers with per-shape unary tables. LPTables rows are [predicate, node] pairs.
func (s *ShaclDocument) AdoptLPAnswers(LPTables []Table[rdf.Term]) error {
	predRows := make(map[string][]rdf.Term)
	for _, t := range LPTables {
		for row := range t.IterRows() {
			if len(row) < 2 {
				continue
			}
			predRows[row[0].RawValue()] = append(predRows[row[0].RawValue()], row[1])
		}
	}

	for predName, nodes := range predRows {
		shapeFound := false
		for name, shape := range s.shapeNames {
			if shape.GetLogName() == predName {
				shapeFound = true
				var tmp TableSimple[rdf.Term]
				tmp.header = []string{shape.GetIRI()}
				for _, node := range nodes {
					tmp.content = append(tmp.content, []rdf.Term{node})
				}
				s.uncondAnswers[name] = &tmp
			}
		}
		if !shapeFound &&
			!strings.HasSuffix(predName, "INTERN") &&
			!strings.HasPrefix(predName, "XONE") &&
			!strings.HasPrefix(predName, "OrShape") &&
			!strings.HasPrefix(predName, "Qual") &&
			!strings.HasPrefix(predName, "AtLeast") &&
			!strings.HasPrefix(predName, "count") {
			fmt.Println("unmatched LP predicate: ", predName)
			return errors.New("could not match all lptables")
		}
	}

	return nil
}

// AdoptLPUndefinedAnswers populates undefinedAnswers from the Undefined set of a DLV well-founded model.
// Nodes whose shape membership is undefined are excluded from the "invalid target" list in InvalidTargetLP.
func (s *ShaclDocument) AdoptLPUndefinedAnswers(LPTables []Table[rdf.Term]) {
	predRows := make(map[string][]rdf.Term)
	for _, t := range LPTables {
		for row := range t.IterRows() {
			if len(row) < 2 {
				continue
			}
			predRows[row[0].RawValue()] = append(predRows[row[0].RawValue()], row[1])
		}
	}

	for predName, nodes := range predRows {
		for name, shape := range s.shapeNames {
			if shape.GetLogName() == predName {
				var tmp TableSimple[rdf.Term]
				tmp.header = []string{shape.GetIRI()}
				for _, node := range nodes {
					tmp.content = append(tmp.content, []rdf.Term{node})
				}
				s.undefinedAnswers[name] = &tmp
			}
		}
	}
}
