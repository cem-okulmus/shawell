package main

import (
	"fmt"
	"log"
	"sort"
	"strings"

	rdf "github.com/deiu/rdf2go"
	"github.com/fatih/color"

	"golang.org/x/exp/maps"
)

type depMode int32

const (
	and depMode = iota
	or
	xone
	not
	qualified
)

type dependency struct {
	name     []ShapeRef // the references used in a node-referring constraint inside a shape
	origin   string     // the (node or property) shape the dependency originates from
	external bool       // whether the dep is refering to value nodes (external) or to focus node (internal)
	mode     depMode    // the type of reference that is used
	min      int        // used by qualifiedValueShape
	max      int        // used by qualifiedValueShape
}

var Empty struct{}

type ShaclDocument struct {
	nodeShapes     []Shape
	shapeNames     map[string]*Shape              // used to unwind references to shapes
	condAnswers    map[string]Table               // for each NodeShape, its (un)conditional answer
	uncondAnswers  map[string]Table               // caches the results from unwinding
	origTargets    map[string][]rdf.Term          // cache the original result for cache
	targets        map[string]map[string]struct{} // caches for targets
	indirectTarget map[string]map[string]struct{} // stores for each shape the indirect Targets, due to deps
	answered       bool
	validated      bool
}

func (s ShaclDocument) String() string {
	var sb strings.Builder
	for _, t := range s.nodeShapes {
		sb.WriteString(fmt.Sprintln("\n", t.String()))
	}

	sb.WriteString("Deps: \n")

	for k, v := range s.shapeNames {

		deps := (*v).GetDeps()

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

	return abbr(sb.String())
}

func GetShaclDocument(rdfGraph *rdf.Graph) (out ShaclDocument) {
	// var detected bool = true
	out.shapeNames = make(map[string]*Shape)
	out.condAnswers = make(map[string]Table)
	out.uncondAnswers = make(map[string]Table)
	out.origTargets = make(map[string][]rdf.Term)
	out.indirectTarget = make(map[string]map[string]struct{})
	out.targets = make(map[string]map[string]struct{})

	NodeShapeTriples := rdfGraph.All(nil, ResA, res(_sh+"NodeShape"))
	// fmt.Println(res(sh+"NodeShape"), " of node shapes, ", NodeShapeTriples)

	for _, t := range NodeShapeTriples {
		name := t.Subject.RawValue()

		// check if already encountered; if so skip
		_, ok := out.shapeNames[name]
		if ok {
			continue
		}

		var shape Shape
		shape = out.GetNodeShape(rdfGraph, t.Subject)
		out.nodeShapes = append(out.nodeShapes, shape)

		// if _, ok := out.shapeNames[name]; ok {
		// 	panic("Two shapes with same name, shape names must be unique!")
		// }

		out.shapeNames[name] = &shape // add a reference to newly extracted shape
	}

	PropertyShapeTriples := rdfGraph.All(nil, ResA, res(_sh+"PropertyShape"))
	// fmt.Println(res(sh+"NodeShape"), " of node shapes, ", NodeShapeTriples)

	for _, t := range PropertyShapeTriples {
		name := t.Subject.RawValue()

		// check if already encountered; if so skip
		_, ok := out.shapeNames[name]
		if ok {
			continue
		}

		var shape Shape
		shape = out.GetPropertyShape(rdfGraph, t.Subject)
		// if !ok {
		// 	detected = false
		// 	// fmt.Println("Failed during triple", t)
		// 	break
		// }
		out.nodeShapes = append(out.nodeShapes, shape)

		if _, ok := out.shapeNames[name]; ok {
			panic("Two shapes with same name, shape names must be unique!")
		}

		out.shapeNames[name] = &shape // add a reference to newly extracted shape
	}

	return out
}

// mem checks if an integer b occurs inside a slice as
func mem(aas [][]rdf.Term, b rdf.Term) bool {
	for _, as := range aas {
		for _, a := range as {
			if a.Equal(b) {
				return true
			}
		}
	}

	return false
}

// memListOne returns true, if exactly one element is included
func memListQual(aas [][]rdf.Term, b rdf.Term, min, max int) bool {
	elements := strings.Split(b.RawValue(), " ")

	count := 0
	for _, e := range elements {
		out := mem(aas, res(e))
		if out {
			count = count + 1
		}
	}

	return (count >= min) && (count <= max)
}

// memListOne returns true, if exactly one element is included
func memListXone(aas [][]rdf.Term, b rdf.Term) bool {
	elements := strings.Split(b.RawValue(), " ")

	first := false
	for _, e := range elements {
		out := mem(aas, res(e))
		if out && first {
			return false
		} else {
			first = true
		}
	}

	return true
}

// memListOne returns true, if any one element is included
func memListOne(aas [][]rdf.Term, b rdf.Term) bool {
	elements := strings.Split(b.RawValue(), " ")

	for _, e := range elements {
		out := mem(aas, res(e))
		if out {
			return true
		}
	}

	return false
}

// memList returns true, if all elements are included
func memListAll(aas [][]rdf.Term, b rdf.Term) bool {
	elements := strings.Split(b.RawValue(), " ")

	for _, e := range elements {
		out := mem(aas, res(e))
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

func (s ShaclDocument) TransitiveClosureRec(name string, visited []string) (bool, []dependency) {
	var out1, out2 []dependency

	visited = append(visited, name)

	// fmt.Println("Visited: ", visited)

	if _, ok := s.shapeNames[name]; ok {
		out1 = append(out1, (*s.shapeNames[name]).GetDeps()...)
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
			out2 = append(out2, new_deps...)
		}

	}

	return false, out2
}

// ToSparql transforms a SHACL document into a series of Sparql queries
// one for each node  shape
func (s ShaclDocument) ToSparql() (out []SparqlQuery) {
	for i := range s.nodeShapes {

		target := s.GetTargetShape(s.nodeShapes[i].GetIRI())

		out = append(out, s.nodeShapes[i].ToSparql(target))
	}

	return out
}

func remove(s [][]rdf.Term, i int) [][]rdf.Term {
	s[i] = s[len(s)-1]
	return s[:len(s)-1]
}

// func remove(slice [][]rdf.Term, s int) [][]rdf.Term {
// 	return append(slice[:s], slice[s+1:]...)
// }

func (s *ShaclDocument) AllCondAnswers(ep endpoint) {
	foundNewIndirect := true

	for foundNewIndirect { // to ensure at least one iteration of this process
		foundNewIndirect = false // can only enter a second iteration if new indirect targets found

	outer:
		for k, v := range s.shapeNames {

			fmt.Println("Current shape ", k)

			if !(*v).IsActive() {
				continue
			}

			// TODO: currently asking target query twice, optimise this to only send one
			_, ok := s.targets[k]
			if !ok {
				// compute targets before computing the query, if not already done
				s.GetTargets(k, ep)
			} else {
				if m, ok := s.indirectTarget[k]; ok {
					if len(m) == 0 {
						continue outer // don't query if no new indirect targets
					}
				}
			}

			target := s.GetTargetShape(k)
			out := ep.Answer(v, target)

			if m, ok := s.indirectTarget[k]; ok {

				for i := range m {
					s.targets[k][i] = Empty
				}

				maps.Clear(m)
				s.indirectTarget[k] = m
			}

			// fmt.Println(k, "  for dep ", v.name, " we got the uncond answers ", out.LimitString(5))

			if _, ok := s.condAnswers[k]; !ok {
				s.condAnswers[k] = out
			} else {
				tmpTable := s.condAnswers[k]

				tmpTable.content = append(tmpTable.content, out.content...)
				s.condAnswers[k] = tmpTable
			}

		}

		for k, v := range s.shapeNames {
			// extract indirect Targets
			out := s.condAnswers[k]

			deps := (*v).GetDeps()
			for i := range deps {
				// if !deps[i].external {
				// 	fmt.Println("Dep ", deps[i].name, " for shape ", k, " is internal. skip")
				// 	continue // no need to add targets for internal dependency
				// }

				for _, ref := range deps[i].name {

					fmt.Println("Checking dep on ", ref.name, " for shape ", k)

					indirectTargets := s.GetIndirectTargets(ref, deps[i], out)

					fmt.Println("Found ", len(indirectTargets), " targets")

					for i := range indirectTargets {
						indirectString := indirectTargets[i].RawValue()
						if _, ok := s.targets[ref.name][indirectString]; !ok {

							foundNewIndirect = true

							if _, ok := s.indirectTarget[ref.name]; !ok {
								s.indirectTarget[ref.name] = make(map[string]struct{})
							}
							s.indirectTarget[ref.name][indirectString] = Empty
						}
					}

					if foundNewIndirect {
						fmt.Println("-----------------------------")
						fmt.Println("Found new indirectTargets for shape ", ref.name)
						fmt.Println("-----------------------------")
					}

				}
			}
		}
	}

	s.answered = true
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

func (s *ShaclDocument) GetIndirectTargets(ref ShapeRef, dep dependency, condTable Table) []rdf.Term {
	var indirectTargets []rdf.Term

	var c int // column to compare

	if dep.external {
		found := false
		for i, h := range condTable.header {
			if strings.HasSuffix(h, dep.origin) {
				found = true
				c = i
			}
		}
		if !found {
			log.Panic("Couldn't find dep ", dep.name, " with origin ", dep.origin, " inside ", condTable.header)
		}
	} else {
		c = 0 // intrinsic checks are made against the node shape itself
	}

	// fmt.Println("Dep ", dep.name, " is of type list: ", isList)
	for i := range condTable.content {
		cont := condTable.content[i][c]
		splitCont := strings.Split(cont.RawValue(), " ")

		for j := range splitCont {
			indirectTargets = append(indirectTargets, res(splitCont[j]))
		}

	}

	return indirectTargets
}

func (s *ShaclDocument) GetAffectedIndices(ref ShapeRef, dep dependency, uncondTable Table, min, max int) []int {
	var affectedIndices []int
	var depTable Table

	if _, ok := s.uncondAnswers[ref.name]; ok {
		depTable = s.uncondAnswers[ref.name]
	} else {
		depTable = s.UnwindAnswer(ref.name) // recursively compute the needed uncond. answers
	}

	// NOTE: this only works for non-recursive shapes
	// we now know that we deal with unconditional (unary) answers
	if len(depTable.header) > 1 {
		log.Panic("Received non-unary uncond. Answer! ", depTable)
	}

	var c int // column to compare

	if dep.external {
		found := false
		for i, h := range uncondTable.header {
			if strings.HasSuffix(h, dep.origin) {
				found = true
				c = i
			}
		}
		if !found {
			log.Panic("Couldn't find dep ", dep.name, " with origin ", dep.origin, " inside ", uncondTable.header)
		}
	} else {
		c = 0 // intrinsic checks are made against the node shape itself
	}

	// fmt.Println("Dep ", dep.name, " is of type list: ", isList)
	for i := range uncondTable.content {
		switch dep.mode {
		case not:
			if memListOne(depTable.content, uncondTable.content[i][c]) {
				affectedIndices = append(affectedIndices, i)
			}
		case and:
			if memListAll(depTable.content, uncondTable.content[i][c]) {
				affectedIndices = append(affectedIndices, i)
			}
		case or:
			if memListOne(depTable.content, uncondTable.content[i][c]) {
				affectedIndices = append(affectedIndices, i)
			}
		case xone:
			if memListXone(depTable.content, uncondTable.content[i][c]) {
				affectedIndices = append(affectedIndices, i)
			}
		case qualified:
			if memListQual(depTable.content, uncondTable.content[i][c], min, max) {
				affectedIndices = append(affectedIndices, i)
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

// UnwindAnswer computes the unconditional answers
func (s *ShaclDocument) UnwindAnswer(name string) Table {
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
	uncondTable := s.condAnswers[name]

	deps := (*shape).GetDeps()

	rec, _ := s.TransitiveClosure(name)
	// check if recursive shape
	if rec {
		log.Panic(name, " is a recursive SHACL node  shape, as it depends on itself.")
	}

	for _, dep := range deps {
		switch dep.mode {
		case and:
			for _, ref := range dep.name {
				// filtering out answers from uncondTable
				var affectedIndices []int = s.GetAffectedIndices(ref, dep, uncondTable, dep.min, dep.max)

				// only keep the affected indices in and case
				var temp [][]rdf.Term
				for _, i := range affectedIndices {
					temp = append(temp, uncondTable.content[i])
				}

				uncondTable.content = temp
			}
		case not:
			ref := dep.name[0] // not has only single reference (current design)

			var affectedIndices []int = s.GetAffectedIndices(ref, dep, uncondTable, dep.min, dep.max)

			// using reverse sort to "safely" remove indices from slice while iterating over them
			sort.Sort(sort.Reverse(sort.IntSlice(affectedIndices)))
			for _, i := range affectedIndices {
				// fmt.Println("removing ", i, " ", uncondTable.content[i][columnToCompare])
				uncondTable.content = remove(uncondTable.content, i)
			}

		case or:
			var allAffected []int
			for _, ref := range dep.name {
				// filtering out answers from uncondTable
				allAffected = append(allAffected, s.GetAffectedIndices(ref, dep, uncondTable, dep.min, dep.max)...)
			}
			// wonder if this will work
			allAffected = removeDuplicate(allAffected)

			// only keep those that match at least one dep
			var temp [][]rdf.Term
			for _, i := range allAffected {
				temp = append(temp, uncondTable.content[i])
			}

			uncondTable.content = temp
		case xone:
			// similar to or, but compute the symmetric difference at every step
			var allAffected []int
			for _, ref := range dep.name {
				// filtering out answers from uncondTable
				temps := s.GetAffectedIndices(ref, dep, uncondTable, dep.min, dep.max)

				allAffected = symmetricDiff(allAffected, temps)
			}

			// only keep those that match at least one dep
			var temp [][]rdf.Term
			for _, i := range allAffected {
				temp = append(temp, uncondTable.content[i])
			}

			uncondTable.content = temp

		case qualified:
			ref := dep.name[0] // qualifiedValueShape too has only single reference

			var affectedIndices []int = s.GetAffectedIndices(ref, dep, uncondTable, dep.min, dep.max)

			// only keep the affected indices in and case
			var temp [][]rdf.Term
			for _, i := range affectedIndices {
				temp = append(temp, uncondTable.content[i])
			}

			uncondTable.content = temp
		}
	}

	var newTable Table

	newTable.header = uncondTable.header[:1]

	for i := range uncondTable.content {
		newTable.content = append(newTable.content, uncondTable.content[i][:1])
	}

	// create the new mapping
	s.uncondAnswers[name] = newTable

	return s.uncondAnswers[name]
}

// // FindReferentialFailureWitness produces a sentence explaining why the node does not fulfill the
// // referential constraints in the node shape. This does not cover any non-referential constraints
// // otherwise expressed in the node. (Future TODO to add that here too via Witness queries)
// func (s *ShaclDocument) FindReferentialFailureWitness(shape, node string) (string, bool) {
// 	// if !s.validated {
// 	// 	log.Panicln("Cannot call FindReferentialFailureWitness before validation.")
// 	// }

// 	_, ok := s.shapeNames[shape]
// 	if !ok {
// 		log.Panicln("Provided shape ", shape, " does not exist in this Shacl document.")
// 	}
// 	deps := (*s.shapeNames[shape]).GetDeps()

// 	var metDep []bool
// 	var objNames []string
// 	unmet := false

// 	condAns := s.condAnswers[shape]

// 	index, found := condAns.FindRow(0, node)
// 	if !found {
// 		return "", false
// 	}

// 	row := condAns.content[index]

// 	for i, d := range deps {

// 		// determine the column
// 		headIndex := 0
// 		if d.external {

// 			headerFound := false
// 			for j, h := range condAns.header {
// 				if strings.HasPrefix(h, d.name[len(_sh):]) {
// 					headIndex = j
// 					headerFound = true
// 				}
// 			}
// 			if !headerFound {
// 				fmt.Println("\n header: ", condAns.header)
// 				log.Panicln("For node, ", node, " cannot find the respect column in condAnswers for  ", d.name)
// 			}

// 		} else {
// 			headIndex = 0
// 		}

// 		metDep = append(metDep, false)
// 		objNames = append(objNames, "")

// 		depTable := s.uncondAnswers[d.name]

// 		if d.mode == not {
// 			metDep[i] = !mem(depTable.content, res(node[1:len(node)-1]))
// 		} else {
// 			metDep[i] = mem(depTable.content, res(node[1:len(node)-1]))
// 		}
// 		if !metDep[i] {
// 			// find the offending object name
// 			objNames[i] = row[headIndex].String()
// 			unmet = true
// 		}
// 	}

// 	var answers []string

// 	for i := range metDep {
// 		if !metDep[i] && deps[i].mode == not {
// 			answers = append(answers, objNames[i]+" does have shape "+deps[i].name)
// 		} else if !metDep[i] {
// 			answers = append(answers, objNames[i]+" does not have shape "+deps[i].name)
// 		}
// 	}

// 	return abbr(fmt.Sprint("For ", node, ": ", strings.Join(answers, ", and "), ".")), unmet
// }

func (s *ShaclDocument) GetTargetTerm(t TargetExpression) string {
	var queryBody string
	switch t.(type) {
	case TargetClass:
		t := t.(TargetClass)

		queryBody = "?sub <http://www.w3.org/1999/02/22-rdf-syntax-ns#type>/<http://www.w3.org/2000/01/rdf-schema#subClassOf>* NODE ."

		queryBody = strings.ReplaceAll(queryBody, "NODE", t.class.String())

	case TargetNode:
		t := t.(TargetNode)

		queryBody = " BIND (NODE AS ?this)"

		queryBody = strings.ReplaceAll(queryBody, "NODE", t.node.String())

	case TargetSubjectOf:
		t := t.(TargetSubjectOf)

		queryBody = "  ?sub NODE ?obj ."

		queryBody = strings.ReplaceAll(queryBody, "NODE", t.path.String())

	case TargetObjectsOf:
		t := t.(TargetObjectsOf)

		queryBody = " ?obj NODE ?sub ."

		queryBody = strings.ReplaceAll(queryBody, "NODE", t.path.String())
	case TargetIndirect:
		t := t.(TargetIndirect)

		queryBody = fmt.Sprint("VALUES ?sub {", strings.Join(t.terms, " "), "}")

	}

	return queryBody
}

// GetTargetShape produces the subquery needed to reduce the focus nodes to those described
// in the target expressions, understood as the union overall target expressions.
func (s *ShaclDocument) GetTargetShape(name string) (out SparqlQuery) {
	var targets []TargetExpression

	ns, ok := s.shapeNames[name]
	if !ok {
		log.Panic(name, " is not a defined node  shape")
	}

	switch (*ns).(type) {
	case NodeShape:
		targets = (*ns).(NodeShape).target
	case PropertyShape:
		targets = (*ns).(PropertyShape).shape.target
	}

	// handle implicit class targets

	if !(*ns).IsBlank() {
		targets = append(targets, TargetClass{class: res((*ns).GetIRI())})
	}

	// handle indirect targets:
	if v, ok := s.indirectTarget[name]; ok {
		keys := maps.Keys(v)
		targets = append(targets, TargetIndirect{terms: keys})
	}

	out.head = append(out.head, "?sub")

	var body string

	if len(targets) > 0 {
		var queries []string

		for i := range targets {
			term := s.GetTargetTerm(targets[i])
			term = strings.ReplaceAll(term, "(", "\\(")
			term = strings.ReplaceAll(term, ")", "\\)")
			queries = append(queries, term)
		}

		// doing a more complex UNION to improve compatbility with DBPedia Sparql endpoint

		var temps []string

		for i := range queries {
			temps = append(temps, fmt.Sprint("{SELECT ?sub {\n\t", queries[i], "\n}}"))
		}

		body = fmt.Sprint("\n", strings.Join(temps, "\nUNION\n"), "\n")

	}

	out.body = append(out.body, body)

	return out
}

func (s *ShaclDocument) GetTargets(name string, ep endpoint) {
	var out Table
	// check if result is already cached
	if _, ok := s.targets[name]; ok {
		return
	}

	query := s.GetTargetShape(name)

	// cache the result
	out = ep.Query(query)
	s.targets[name] = make(map[string]struct{})

	for _, row := range out.content {
		if _, ok := s.targets[name][row[0].RawValue()]; !ok {
			s.targets[name][row[0].RawValue()] = Empty
			s.origTargets[name] = append(s.origTargets[name], row[0])

		}
	}
	// fmt.Println("Orig Targets of shape ", name, " len: ", len(s.o))
}

// InvalidTargets compares the targets of a node shape against the decorated graph and
// returns those targets that do not have this shape
func (s *ShaclDocument) InvalidTargets(shape string, ep endpoint) Table {
	var out Table

	if !s.answered {
		s.AllCondAnswers(ep)
	}

	nodesWithShape := s.UnwindAnswer(shape)
	// fmt.Println("Answers: ", len(nodesWithShape.content))

	// targets := s.GetTargets(shape, ep)
	// if !hasTargets {
	// 	return out, false
	// }

	out.header = append(out.header, "Not "+shape[len(_sh):])

outer:
	for _, t := range s.origTargets[shape] {

		for _, n := range nodesWithShape.content {
			if n[0].Equal(t) {
				// fmt.Println("Found ", term, " in the answer")
				continue outer
			}
		}
		out.content = append(out.content, []rdf.Term{t})
	}

	return out
}

// InvalidTargetsWithExplanation returns the targets that do not match the shape they are supposed
// to, but in addition to that, also returns an explanation in the form of a witness table.
// func (s *ShaclDocument) InvalidTargetsWithExplanation(shape string, ep endpoint) (Table, []string) {
// 	var explanation []string
// 	results := s.InvalidTargets(shape, ep)

// 	var remaining []string

// 	// 1st look for refential explanations
// 	for i := range results.content {
// 		if len(results.content[i]) != 1 {
// 			log.Panicln("Resuls table not a unary relation.")
// 		}

// 		node := results.content[i][0].String()

// 		refExp, unmet := s.FindReferentialFailureWitness(shape, node)

// 		// look for answers from witness query instead
// 		if !unmet {
// 			remaining = append(remaining, node)
// 		} else {
// 			explanation = append(explanation, refExp)
// 		}

// 	}

// 	integExp, unmet2 := s.FindWitnessQueryFailures(shape, remaining, ep)

// 	// fail if there are still invalid targets left (indicating a problem in validation)
// 	if len(remaining) > 0 && unmet2 {
// 		log.Panic("There are still remaining invalid targets, without explanations!",
// 			"	remaining: ", remaining, " Exps so far: ", integExp, "\n\n refExps so far:", explanation)
// 	}
// 	explanation = append(explanation, integExp...)
// 	return results, explanation
// }

// Validate checks for each of the node shapes of a SHACL document, whether their target nodes
// occur in the decorated graph with the shapes they are supposed to. If not, it returns false
// as well as list of tables for each node shape of the nodes that fail validation.
func (s *ShaclDocument) Validate(ep endpoint) (bool, map[string]Table) {
	var out map[string]Table = make(map[string]Table)
	// var outExp map[string][]string = make(map[string][]string)
	var result bool = true

	// Produce InvalidTargets for each node shape
	for i := range s.nodeShapes {
		if s.nodeShapes[i].IsActive() { // deactivated shapes do not factor the validation
			iri := s.nodeShapes[i].GetIRI()
			invalidTargets := s.InvalidTargets(iri, ep)
			if len(invalidTargets.content) > 0 {
				out[iri] = invalidTargets
				// outExp[iri] = abbrAll(explanations)
				result = false
			}
		}
	}

	s.validated = true

	return result, out
}
