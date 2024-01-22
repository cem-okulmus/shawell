package main

import (
	"errors"
	"fmt"
	"log"
	"strings"

	"github.com/fatih/color"

	rdf "github.com/cem-okulmus/MyRDF2Go"
	rdf2go "github.com/cem-okulmus/MyRDF2Go"
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

var Empty struct{}

type ShaclDocument struct {
	shapeNames    map[string]Shape           // used to unwind references to shapes
	condAnswers   map[string]Table[rdf.Term] // for each NodeShape, its (un)conditional answer
	uncondAnswers map[string]Table[rdf.Term] // caches the results from unwinding
	targets       map[string]Table[rdf.Term] // the materialised targets of a given shape
	depMap        map[string][]dependency    // stores for each shape the dependant shapes
	answered      bool
	materialised  bool
	validated     bool
	debug         bool
	fromGraph     string
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
	if s.debug {
		sb.WriteString("\nQualnames: \n")
		for k, v := range s.shapeNames {
			sb.WriteString(fmt.Sprint(k, " : ", v.GetQualName(), " ", v.GetLogName(), "\n"))
		}
	}

	// fmt.Println("BEFORE ABBR", sb.String())

	return abbr(sb.String())
}

func GetSubjectFromTriples(triples []*rdf.Triple) (subjects []rdf.Term) {
	for i := range triples {
		subjects = append(subjects, triples[i].Subject)
	}
	return subjects
}

func GetNodeTerms(graph *rdf.Graph) []rdf.Term {
	out := GetSubjectFromTriples(graph.All(nil, ResA, res(_sh+"NodeShape")))

	out = append(out, GetSubjectFromTriples(graph.All(nil, res(_sh+"targetClass"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, res(_sh+"targetNode"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, res(_sh+"targetObjectsOf"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, res(_sh+"targetSubjectsOf"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, res(_sh+"class"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, res(_sh+"datatype"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, res(_sh+"nodeKind"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, res(_sh+"minExclusive"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, res(_sh+"maxExclusive"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, res(_sh+"minInclusive"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, res(_sh+"maxInclusive"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, res(_sh+"minLength"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, res(_sh+"maxLength"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, res(_sh+"pattern"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, res(_sh+"languageIn"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, res(_sh+"equals"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, res(_sh+"disjoint"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, res(_sh+"lessThan"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, res(_sh+"lessThanOrEquals"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, res(_sh+"property"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, res(_sh+"and"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, res(_sh+"or"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, res(_sh+"not"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, res(_sh+"xone"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, res(_sh+"node"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, res(_sh+"qualifiedValueShape"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, res(_sh+"closed"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, res(_sh+"hasValue"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, res(_sh+"in"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, res(_sh+"severity"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, res(_sh+"message"), nil))...)
	out = append(out, GetSubjectFromTriples(graph.All(nil, res(_sh+"deactivated"), nil))...)

	out = removeDuplicate(out)

	// remove anything that has path

	pathStuff := GetSubjectFromTriples(graph.All(nil, res(_sh+"path"), nil))

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

func GetShaclDocument(rdfGraph *rdf.Graph, fromGraph string, ep endpoint, debug bool) (out ShaclDocument) {
	// var detected bool = true
	out.shapeNames = make(map[string]Shape)
	out.condAnswers = make(map[string]Table[rdf.Term])
	out.uncondAnswers = make(map[string]Table[rdf.Term])
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

	PropertyShapeTriples := rdfGraph.All(nil, res(_sh+"path"), nil)
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

	// attach indirect Targets (hope this pointer stuff works)
	for k, v := range out.depMap {
		tmp := out.shapeNames[k].GetTargets()

		for _, dep := range v {
			for _, s := range dep.name {
				var indirects []TargetIndirect
				for i := range tmp {
					indirect := DepToIndirectTarget(dep, tmp[i])
					indirects = append(indirects, indirect)
				}
				if debug {
					fmt.Println("Gotten ", len(tmp), " targets from dependant. Path ", dep.path)

					// fmt.Println("Number of dependant shapes: ", len(v))
					fmt.Println("Adding ", len(indirects), " indirect targets to shape ", s.name, " from origin ", k)
				}

				out.shapeNames[s.name].AddIndirectTargets(indirects, nil) // don't change paths, as they were already defined abvoes
			}
		}
	}

	return out
}

// func GetTransitiveClosure(depMap map[string][]dependency) map[string][]dependency {
// 	somethingChanged := true

// 	for somethingChanged {
// 		somethingChanged = false

// 		for k, v := range depMap {

// 			existingDeps := v

// 			var newDeps []dependency

// 		outer:
// 			for i := range v {
// 				for j := range existingDeps {
// 					if reflect.DeepEqual(v[i], existingDeps[j]) {
// 						continue outer
// 					}
// 				}
// 				newDeps = append(newDeps, v[i])
// 			}

// 			if len(newDeps) > 0 {
// 				somethingChanged = true
// 			}

// 			depMap[k] = append(v, newDeps...)
// 		}
// 	}

// 	fmt.Println("DepMap after Closure ", depMap)

// 	return depMap
// }

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

// mem checks if an integer b occurs inside a slice as
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

// memListOne returns true, if exactly one element is included
func memListQual(aas Table[rdf.Term], b []rdf.Term, min, max int) bool {
	count := 0
	for _, e := range b {
		out := mem(aas, e)
		if out {
			count = count + 1
		}
	}

	var out bool
	if max != -1 {
		out = (count >= min) && (count <= max)
	} else {
		out = (count >= min)
	}

	return out
}

// memListOne returns true, if exactly one element is included
func memListQualSibling(aas Table[rdf.Term], b []rdf.Term, min, max int, siblings []rdf.Term) bool {
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
	if max != -1 {
		out = (count >= min) && (count <= max)
	} else {
		out = (count >= min)
	}

	return out
}

// memListOne returns true, if exactly one element is included
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
	}

	return true
}

// memListOne returns true, if any one element is included
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

// memList returns true, if all elements are included
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

// UnwindDependencies computes the trans. closure of deps among node shapes
func (s ShaclDocument) TransitiveClosure(name string) (bool, []dependency) {
	return s.TransitiveClosureRec(name, []string{})
}

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
			isRec, new_deps := s.TransitiveClosureRec(out1[i].name[k].name, visited)

			if isRec {
				return true, append(new_deps, out2...)
			}
			for _, newDep := range new_deps {
				newDep.originDep = &out1[i]
				out2 = append(out2, newDep)
			}

		}
	}

	return false, out2
}

func removeSimple[T stringer](s []T, i int) []T {
	s[i] = s[len(s)-1]
	return s[:len(s)-1]
}

func remove[T stringer](s [][]T, i int) [][]T {
	s[i] = s[len(s)-1]
	return s[:len(s)-1]
}

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
		if len(v.GetTargets()) == 0 {
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

type Kinds int8

const (
	inA Kinds = iota
	inB
	inBoth
)

func symmetricDiff[T comparable](sliceListA, sliceListB []T) []T {
	allKeys := make(map[T]Kinds)
	list := []T{}
	for _, item := range sliceListA { // map now knows all As
		if _, ok := allKeys[item]; !ok {
			allKeys[item] = inA
		}
	}
	for _, item := range sliceListB { // set all entries in map to false that are also in B
		value, ok := allKeys[item]
		if !ok {
			allKeys[item] = inB
		} else {
			switch value {
			case inA:
				allKeys[item] = inBoth
			case inB:
				// skip since duplicate
			}
		}
	}

	for k, v := range allKeys {
		if v != inBoth {
			list = append(list, k)
		}
	}

	return list
}

func (s *ShaclDocument) GetIndirectTargets(ref ShapeRef, dep dependency, condTable Table[rdf.Term]) (bool, int, bool) {
	// var indirectTargets []rdf.Term

	var c int // column to compare

	if dep.external {
		found := false
		for i, h := range condTable.GetHeader() {
			if strings.HasSuffix(h, dep.origin) {
				found = true
				c = i
			}
		}
		if !found {
			log.Panic("Couldn't find dep ", dep.name, " with origin ", dep.origin, " inside ", condTable.GetHeader())
		}
	} else {
		c = 0 // intrinsic checks are made against the node shape itself
	}

	existIndirectTargets := false

	// fmt.Println("Dep ", dep.name, " is of type list: ", isList)

	for row := range condTable.IterRows() {
		cont := row[c]
		splitCont := strings.Split(cont.RawValue(), " ")

		if len(splitCont) > 0 {
			existIndirectTargets = true

			// fmt.Println("||||||||||||||||||||||||||||||||||||||||||||||||||||||||||")
			// fmt.Println("||||||||||||||||||||||||||||||||||||||||||||||||||||||||||")
			// fmt.Println("CONTENT: \n", condTable)
			// fmt.Println("||||||||||||||||||||||||||||||||||||||||||||||||||||||||||")
			// fmt.Println("||||||||||||||||||||||||||||||||||||||||||||||||||||||||||")

			break
		}

	}

	return existIndirectTargets, c - 1, dep.external
}

func (s *ShaclDocument) GetAffectedIndices(ref ShapeRef, dep dependency, uncondTable Table[rdf.Term], min, max int, siblings *[]Shape) []rdf.Term {
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

				if memListQualSibling(depTable, uncondTableGrouped.GetGroupOfTarget(target, c), min, max, siblingValues) {
					// val, err := uncondTableGrouped.GetIndex(target)
					// check(err)
					// fmt.Println("Adding target ", target)
					affectedIndices = append(affectedIndices, target)
				}
			} else {
				if s.debug {
					fmt.Println("|||||||", " GOING INTO NON disjointedness  PATH")
				}
				if memListQual(depTable, uncondTableGrouped.GetGroupOfTarget(target, c), min, max) {
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

// NodeIsShape checks if a given node has a given shape, or not
func (s *ShaclDocument) NodeIsShape(node rdf2go.Term, shape string) bool {
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

func intersect(one []int, other []int) (out []int) {
	for i := range one {
		for j := range other {
			if one[i] == other[j] {
				out = append(out, one[i])
			}
		}
	}

	return removeDuplicate[int](out)
}

// UnwindAnswer computes the unconditional answers
func (s *ShaclDocument) UnwindAnswer(name string) Table[rdf.Term] {
	if !s.answered {
		return s.uncondAnswers[name] // just return empty table if answers not computed yet
	}

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

	targets := ns.GetTargets()

	out = TargetsToQueries(targets)

	return out, false
}

func (s *ShaclDocument) GetValidTargetShape(name string) (out []SparqlQueryFlat, empty bool) {
	ns, ok := s.shapeNames[name]
	if !ok {
		log.Panic(name, " is not a defined node  shape")
	}

	targets := ns.GetValidationTargets()

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
	for t_row := range targets.IterRows() {
		for n_row := range nodesWithShape.IterRows() {
			if n_row[0].RawValue() == t_row[0].RawValue() {
				continue outer
			}
			// fmt.Println("Term ", n[0], " not equal to ", t[0])
		}
		out.content = append(out.content, t_row)
	}

	// fmt.Println("My invalid targets for: ", shape)
	// fmt.Println(out)

	return &out
}

// InvalidTargets compares the targets of a node shape against the decorated graph and
// returns those targets that do not have this shape
func (s *ShaclDocument) InvalidTargetLP(shape string, LPTables []Table[rdf.Term], ep endpoint) Table[rdf.Term] {
	var out TableSimple[rdf.Term]
	if !s.materialised {
		s.MaterialiseTargets(ep)
	}

	var nodesWithShape Table[rdf.Term] = &TableSimple[rdf.Term]{}

	shapeObj := s.shapeNames[shape]

	// nodesWithShape , found :=

	for i := range LPTables {
		if len(LPTables[i].GetHeader()) != 1 {
			log.Panicln("Logic Table with more than one result returned, somehow!")
		}

		header := LPTables[i].GetHeader()[0]
		if strings.EqualFold(header, shape) {
			nodesWithShape = LPTables[i]
			// fmt.Println("For shape ", shape, ", found this LPTable", LPTables[i])
			break
		}
	}

	// fmt.Println("Answers: ", len(nodesWithShape.content))

	// targets := s.GetTargets(shape, ep)
	// if !hasTargets {
	// 	return out, false
	// }

	out.header = append(out.header, "Not "+shapeObj.GetIRI())

	targets := s.targets[shape]

outer:
	for t_row := range targets.IterRows() { // will this work?

		for n_row := range nodesWithShape.IterRows() {
			if n_row[0].RawValue() == t_row[0].RawValue() {
				// fmt.Println("Found ", term, " in the answer")
				continue outer
			}
		}
		// fmt.Println("Found ", t_row[0], " as invalid target of shape ", shape)
		// fmt.Println("nodesWithShape: ", nodesWithShape)
		out.content = append(out.content, []rdf.Term{t_row[0]})
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
func (s *ShaclDocument) ValidateLP(LPTables []Table[rdf.Term], ep endpoint) (bool, map[string]Table[rdf.Term]) {
	out := make(map[string]Table[rdf.Term])
	// var outExp map[string][]string = make(map[string][]string)
	result := true

	// Produce InvalidTargets for each node shape
	for _, shape := range s.shapeNames {
		if shape.IsActive() { // deactivated shapes do not factor the validation
			iri := shape.GetIRI()
			invalidTargets := s.InvalidTargetLP(iri, LPTables, ep)
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

// AdoptLPAnswers takes the computed answers from the logic program and replaces entries
// in uncondTables with them. If it cannot match any table, it returns an error
func (s *ShaclDocument) AdoptLPAnswers(LPTables []Table[rdf.Term]) error {
	for i := range LPTables {

		shapeFound := false
		// find matching shape
		for name, shape := range s.shapeNames {
			if shape.GetLogName() == LPTables[i].GetHeader()[0] {
				shapeFound = true
				LPTables[i].SetHeader([]string{shape.GetIRI()})
				s.uncondAnswers[name] = LPTables[i]
			}
		}
		if !shapeFound && !strings.HasSuffix(LPTables[i].GetHeader()[0], "INTERN") &&
			!strings.HasPrefix(LPTables[i].GetHeader()[0], "XONE") &&
			!strings.HasPrefix(LPTables[i].GetHeader()[0], "OrShape") &&
			!strings.HasPrefix(LPTables[i].GetHeader()[0], "Qual") &&
			!strings.HasPrefix(LPTables[i].GetHeader()[0], "count") {
			fmt.Println("LPTable in question ", LPTables[i])
			return errors.New("could not match all lptables")
		}

	}

	return nil
}
