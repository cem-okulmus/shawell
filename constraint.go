package main

import (
	"fmt"
	"log"
	"sort"
	"strconv"
	"strings"

	"github.com/deiu/rdf2go"
	"github.com/fatih/color"
)

// TODO: maybe handle invertedPath more systematically in the future?

// PropertyConstraint expresses contstraints on properties that go out
// from the target node.
type PropertyConstraint struct {
	path     rdf2go.Term // the outgoing property that is being restricted
	inverse  bool        // indicates that the path is inverted
	class    rdf2go.Term // restrict the target to a class
	hasValue rdf2go.Term // restricts to the specified value
	node     rdf2go.Term // restrict the target to a shape
	minCount int         // 0 treated as non-defined
	maxCount int         // 0 treated as non-defined
}

func (p PropertyConstraint) String() string {
	var sb strings.Builder

	add := ""
	if p.inverse {
		add = "^"
	}

	sb.WriteString("on path " + add + p.path.RawValue())
	if p.class != nil {
		sb.WriteString(" restricted to class: " + p.class.RawValue())
	}

	if p.node != nil {
		sb.WriteString(" restricted to node shape: " + p.node.RawValue())
	}
	if p.hasValue != nil {
		sb.WriteString(" restricted to value: " + p.hasValue.RawValue())
	}
	sb.WriteString(fmt.Sprint(" (min:", p.minCount, ", max:", p.maxCount, ") \n"))

	return sb.String()
}

// TODO: if there are valid SHACL docs with collections of targets, then extend this to support it

type TargetExpression interface {
	String() string
}

type TargetClass struct {
	class rdf2go.Term // the class that is being targeted
}

func (t TargetClass) String() string {
	return t.class.RawValue()
}

type TargetObjectsOf struct {
	path rdf2go.Term // the property the target is the object of
}

func (t TargetObjectsOf) String() string {
	return t.path.RawValue()
}

type TargetSubjectOf struct {
	path rdf2go.Term // the property the target is the subject of
}

func (t TargetSubjectOf) String() string {
	return t.path.RawValue()
}

type TargetNode struct {
	node rdf2go.Term // the node that is selected
}

func (t TargetNode) String() string {
	return t.node.RawValue()
}

// NodeShape is one of the two basic shape expressions that form
type NodeShape struct {
	name          string
	properties    []PropertyConstraint
	positiveSlice []string // collection of positive shape references
	negativeSlice []string // collection of negative shape references
	target        TargetExpression
	closed        bool
}

func (n NodeShape) String() string {
	var sb strings.Builder

	sb.WriteString(n.name[len(sh):])
	sb.WriteString("\n\t\tTarget: " + fmt.Sprint(n.target))
	switch n.target.(type) {
	case TargetObjectsOf:
		sb.WriteString("(TargetObjectOf)")
	case TargetClass:
		sb.WriteString("(TargetClass)")
	}
	sb.WriteString(fmt.Sprint("\n\t\tProperties:", " ", len(n.properties), "\n"))
	for _, p := range n.properties {
		sb.WriteString("\t\t\t" + p.String())
	}

	if len(n.positiveSlice) > 0 {
		sb.WriteString(fmt.Sprint("\n\t\tSH And:", " ", len(n.positiveSlice), "\n\t\t\t{"))
		for i, ns := range n.positiveSlice {
			sb.WriteString(ns)
			if i < len(n.positiveSlice)-1 {
				sb.WriteString(",")
			}
		}
		sb.WriteString("}\n")
	}

	if len(n.negativeSlice) > 0 {
		sb.WriteString(fmt.Sprint("\n\t\tSH Not:", " ", len(n.negativeSlice), "\n\t\t\t{"))
		for i, ns := range n.negativeSlice {
			sb.WriteString(ns)
			if i < len(n.negativeSlice)-1 {
				sb.WriteString(",")
			}
		}
		sb.WriteString("}\n")
	}

	sb.WriteString("\n\t\tClosed: " + fmt.Sprint(n.closed))

	return sb.String()
}

// GetNodeShape takes as input and RDF graph and a term signifying a NodeShape
// and then iteratively queries the RDF graph to extract all its details
func GetNodeShape(rdf *rdf2go.Graph, name string) (bool, *NodeShape, []dependency) {
	subject := rdf2go.NewResource(name)
	triples := rdf.All(subject, nil, nil)
	var deps []dependency
	// fmt.Println("Found triples", triples)

	isNodeShape := false // determine if its a proper NodeShape at all
	var target TargetExpression
	target = nil
	var closed bool
	var properties []PropertyConstraint
	var positives []string
	var negatives []string

	// fmt.Println("Checking triples!")
	for _, t := range triples {
		// fmt.Println(res("a").RawValue())

		// fmt.Println("Looking at triple", t)

		if t.Object.Equal(res(sh+"NodeShape")) && t.Predicate.Equal(ResA) {
			isNodeShape = true
		}

		// determine the target
		if target == nil && t.Predicate.Equal(res(sh+"targetObjectsOf")) {
			target = TargetObjectsOf{path: t.Object}
		}
		if target == nil && t.Predicate.Equal(res(sh+"targetSubjectsOf")) {
			target = TargetSubjectOf{path: t.Object}
		}
		if target == nil && t.Predicate.Equal(res(sh+"targetClass")) {
			target = TargetClass{class: t.Object}
		}
		if target == nil && t.Predicate.Equal(res(sh+"targetNode")) {
			target = TargetNode{node: t.Object}
		}

		// handling property
		if t.Predicate.Equal(res(sh + "property")) {
			// fmt.Println("------------fire!-----------", t.Object.String())
			blank := t.Object
			propTriples := rdf.All(blank, nil, nil)
			// fmt.Println("Found blanks", propTriples)
			pc := PropertyConstraint{}
			for _, t2 := range propTriples {
				switch t2.Predicate.RawValue() {
				case sh + "path":
					// check for inverted path
					out := rdf.One(t2.Object, res(sh+"inversePath"), nil)

					if out == nil {
						pc.path = t2.Object
					} else {
						pc.path = out.Object
						pc.inverse = true
					}

				case sh + "class":
					pc.class = t2.Object
				case sh + "hasValue":
					pc.hasValue = t2.Object
				case sh + "node":
					pc.node = t2.Object
					deps = append(deps, dependency{name: pc.node.RawValue(), extrinsic: true})
				case sh + "minCount":
					i, err := strconv.Atoi(t2.Object.RawValue())
					check(err)
					pc.minCount = i
				case sh + "maxCount":
					i, err := strconv.Atoi(t2.Object.RawValue())
					check(err)
					pc.maxCount = i
				}
			}
			properties = append(properties, pc)

		}

		// handling SH AND list
		if t.Predicate.Equal(res(sh + "and")) {
			blank := t.Object

			listTriples := rdf.All(blank, nil, nil)
			for _, t2 := range listTriples {
				if !t2.Object.Equal(res(rdfs + "nil")) {
					positives = append(positives, t2.Object.RawValue())
				}
			}

		}

		// handling SH Not
		if t.Predicate.Equal(res(sh + "not")) {
			// check if object blank (if so, we need to parse a non-named shape)
			switch t.Object.(type) {
			case rdf2go.BlankNode:
				// TODO
				panic("complex NOT expressions not yet implemented!")
			default:
				negatives = append(negatives, t.Object.RawValue())
			}
		}

		if t.Predicate.Equal(res(sh + "closed")) {
			b, err := strconv.ParseBool(t.Object.RawValue())
			check(err)
			closed = b
		}

	}

	// add negatives and positives to deps
	for i := range positives {
		deps = append(deps, dependency{name: positives[i]})
	}
	for i := range negatives {
		deps = append(deps, dependency{name: negatives[i], negative: true})
	}

	return isNodeShape, &NodeShape{
		name:          name,
		properties:    properties,
		positiveSlice: positives,
		negativeSlice: negatives,
		target:        target,
		closed:        closed,
	}, deps
}

// ToSparql produces a Sparql query that when run against an endpoint returns
// the list of potential nodes satisying the shape, as well as a combination of
// other nodes expressiong a conditional shape dependency such that any
// potential node is only satisfied if and only if the conditional nodes have
// or do not have the specified shapes.
func (n NodeShape) ToSparql() string {
	var sb strings.Builder
	nonEmpty := false // used to deal with strange "empty" constraints

	sb.WriteString("PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> \n")
	sb.WriteString("PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#> \n")
	sb.WriteString("PREFIX dbo:  <https://dbpedia.org/ontology/>\n")
	sb.WriteString("PREFIX dbr:  <https://dbpedia.org/resource/>\n")
	sb.WriteString("PREFIX sh:   <http://www.w3.org/ns/shacl#>\n\n")

	sb.WriteString("SELECT distinct (?sub as ?" + n.name[len(sh):] + " )") // initial part

	// for each property constraint with recursive refs
	var outputAttributes []string

	// one for each property constraint and other constraints
	var outputWhereStatements []string

	var usedPaths []string // keep track of all (non-inverse) path constraints
	usedPaths = append(usedPaths, res(rdfs+"type").String())

	rN := 1 // running number, used to make the vars distinct

	for _, p := range n.properties {
		nonEmpty = false
		// check if counting constraints present or not
		var tb strings.Builder
		var output string

		if p.inverse {
			nonEmpty = true
			tb.WriteString(fmt.Sprint("?obj", rN, " ", p.path.String(), " ?sub .\n"))

			if p.minCount != 0 || p.maxCount != 0 {
				tb.WriteString("{\n")
				tb.WriteString(fmt.Sprint("SELECT ?InnerPred", rN, " ?InnerObj", rN))
				tb.WriteString(fmt.Sprint(" (COUNT (DISTINCT ?InnerSub", rN, ") AS ?countObj", rN, ")"))
				tb.WriteString(fmt.Sprint(" (GROUP_CONCAT (DISTINCT ?InnerSub", rN, ") AS ?listObjs", rN, ")\n"))
				tb.WriteString("WHERE {\n")
				tb.WriteString(fmt.Sprint("?InnerSub", rN, " ", p.path.String(), " ?InnerObj", rN, " .\n"))
				tb.WriteString("}\n")
				tb.WriteString(fmt.Sprint("GROUP BY ?InnerPred", rN, " ?InnerObj", rN, "\n"))
				tb.WriteString("}\n")
				tb.WriteString(fmt.Sprint("FILTER (?InnerObj", rN, " = ?sub)\n"))
				if p.maxCount != 0 {
					tb.WriteString(fmt.Sprint("FILTER ( ", p.minCount, " <= ?countObj", rN))
					tb.WriteString(fmt.Sprint(" && ?countObj", rN, " <= ", p.maxCount, " )"))
				} else {
					tb.WriteString(fmt.Sprint("FILTER ( ", p.minCount, " <= ?countObj", rN, ")"))
				}
			}

		} else {

			nonEmpty = true
			tb.WriteString(fmt.Sprint("?sub ", p.path.String(), " ?obj", rN, " .\n"))

			if p.minCount != 0 || p.maxCount != 0 {
				tb.WriteString("{\n")
				tb.WriteString(fmt.Sprint("SELECT ?InnerSub", rN, " ?InnerPred", rN))
				tb.WriteString(fmt.Sprint(" (COUNT (DISTINCT ?InnerObj", rN, ") AS ?countObj", rN, ")"))
				tb.WriteString(fmt.Sprint(" (GROUP_CONCAT (DISTINCT ?InnerObj", rN, ") AS ?listObjs", rN, ")\n"))
				tb.WriteString("WHERE {\n")
				tb.WriteString(fmt.Sprint("?InnerSub", rN, " ", p.path.String(), " ?InnerObj", rN, " .\n"))
				tb.WriteString("}\n")
				tb.WriteString(fmt.Sprint("GROUP BY ?InnerSub", rN, " ?InnerPred", rN, "\n"))
				tb.WriteString("}\n")
				tb.WriteString(fmt.Sprint("FILTER (?InnerSub", rN, " = ?sub)\n"))
				if p.maxCount != 0 {
					tb.WriteString(fmt.Sprint("FILTER ( ", p.minCount, " <= ?countObj", rN))
					tb.WriteString(fmt.Sprint(" && ?countObj", rN, " <= ", p.maxCount, " )"))
				} else {
					tb.WriteString(fmt.Sprint("FILTER ( ", p.minCount, " <= ?countObj", rN, ")"))
				}

			}
			usedPaths = append(usedPaths, p.path.String()) // adding to list of encountered

		}

		if p.class != nil {

			nonEmpty = true
			out := fmt.Sprint("?obj", rN, " rdfs:type/rdfs:subClassOf* ", p.class.String(), " .\n")
			outputWhereStatements = append(outputWhereStatements, out)
		}
		if p.hasValue != nil {
			out := fmt.Sprint("FILTER ( ?obj", rN, " =", p.hasValue.String(), " )\n")
			outputWhereStatements = append(outputWhereStatements, out)
		}

		outputWhereStatements = append(outputWhereStatements, tb.String())

		if p.node != nil { // recursive constraint, adding to head

			if p.minCount != 0 || p.maxCount != 0 {
				output = fmt.Sprint("(?listObjs", rN, " AS ?", p.node.RawValue()[28:], rN, " )")
			} else {
				output = fmt.Sprint("(?obj", rN, " AS ?", p.node.RawValue()[28:], rN, " )")
			}

			outputAttributes = append(outputAttributes, output)
		}
		rN++
	}
	if !nonEmpty {
		triple := "?sub ?pred ?obj .\n"
		outputWhereStatements = append(outputWhereStatements, triple)

	}

	// buildling the SELECT line
	for _, a := range outputAttributes {
		sb.WriteString(" " + a)
	}
	sb.WriteString("{ \n")

	// building the inside of the WHERE
	for _, w := range outputWhereStatements {
		sb.WriteString(w)
		sb.WriteString("\n")
	}

	// Building the line for closedness condition
	if n.closed {
		sb.WriteString("FILTER NOT EXISTS {?sub ?pred ?objClose FILTER ( ?pred NOT IN (")
		for i, p := range usedPaths {
			sb.WriteString(p)
			if i < len(usedPaths)-1 {
				sb.WriteString(", ")
			}
		}
		sb.WriteString(" )) }\n\n")
	}

	sb.WriteString("}\n")
	return sb.String()
}

type dependency struct {
	name      string // the name of the shape something depends on
	negative  bool   //  to look for the presence or instead for the absence of a shape
	extrinsic bool   // whether the dependency is on the shape of another node (extrinsic), or
	// instead if it is on the current node also (not) being of a certain other shape (intrinsic)
}

type ShaclDocument struct {
	nodeShapes    []*NodeShape
	shapeNames    map[string]*NodeShape   // used to unwind references to shapes
	dependency    map[string][]dependency // used to store the dependencies among shapes
	condAnswers   map[string]Table        // for each NodeShape, its (un)conditional answer
	uncondAnswers map[string]Table        // caches the results from unwinding
	answered      bool
}

func (s ShaclDocument) String() string {
	var sb strings.Builder
	for _, t := range s.nodeShapes {
		sb.WriteString(fmt.Sprintln("\n", t.String()))
	}

	sb.WriteString("Deps: \n")

	for k, v := range s.dependency {
		var sb2 strings.Builder

		var c *color.Color

		for _, d := range v {
			if d.negative {
				c = color.New(color.FgRed).Add(color.Underline)
			} else {
				c = color.New(color.FgGreen).Add(color.Underline)
			}

			sb2.WriteString(" ")
			if d.extrinsic {
				sb2.WriteString(c.Sprint(d.name))
			} else {
				sb2.WriteString(c.Sprint("<<", d.name, ">>"))
			}
		}
		if len(v) == 0 {
			sb.WriteString(fmt.Sprint(k, " depends on nobody. \n"))
		} else {
			sb.WriteString(fmt.Sprint(k, " depends on ", sb2.String(), ". \n"))
		}

	}

	return abbr(sb.String())
}

func GetShaclDocument(rdf *rdf2go.Graph) (bool, ShaclDocument) {
	var out ShaclDocument
	var detected bool = true
	out.shapeNames = make(map[string]*NodeShape)
	out.dependency = make(map[string][]dependency)
	out.condAnswers = make(map[string]Table)
	out.uncondAnswers = make(map[string]Table)

	NodeShapeTriples := rdf.All(nil, ResA, res(sh+"NodeShape"))
	// fmt.Println(res(sh+"NodeShape"), " of node shapes, ", NodeShapeTriples)

	for _, t := range NodeShapeTriples {
		name := t.Subject.RawValue()
		ok, ns, deps := GetNodeShape(rdf, name)
		if !ok {
			detected = false
			// fmt.Println("Failed during triple", t)
			break
		}
		out.nodeShapes = append(out.nodeShapes, ns)

		if _, ok := out.shapeNames[name]; ok {
			panic("Two NodeShapes with same name, NodeShapes must be unique!")
		}

		out.shapeNames[name] = ns // add a reference to newly extracted shape

		out.dependency[name] = deps // add the dependencies
	}

	return detected, out
}

// mem checks if an integer b occurs inside a slice as
func mem(aas [][]rdf2go.Term, b rdf2go.Term) bool {
	for _, as := range aas {
		for _, a := range as {
			if a.Equal(b) {
				return true
			}
		}
	}

	return false
}

// Subset returns true if as subset of bs, false otherwise
func Subset(as []string, bs []string) bool {
	if len(as) == 0 {
		return true
	}
	encounteredB := make(map[string]struct{})
	var Empty struct{}
	for _, b := range bs {
		encounteredB[b] = Empty
	}

	for _, a := range as {
		if _, ok := encounteredB[a]; !ok {
			return false
		}
	}

	return true
}

// RemoveDuplicates is using an algorithm from "SliceTricks" https://github.com/golang/go/wiki/SliceTricks
func RemoveDuplicates(elements []string) []string {
	if len(elements) == 0 {
		return elements
	}
	sort.Strings(elements)

	j := 0
	for i := 1; i < len(elements); i++ {
		if elements[j] == elements[i] {
			continue
		}
		j++

		// only set what is required
		elements[j] = elements[i]
	}

	return elements[:j+1]
}

// func flatten(content [][]rdf2go.Term) []rdf2go.Term {
// 	var out []rdf2go.Term

// 	for i := range content
// 		for j := range content[i][j] {
// 			out =
// 		}
// }

// UnwindDependencies computes the trans. closure of deps among node shapes
func UnwindDependencies(deps map[string][]string) map[string][]string {
	changed := true

	for changed {
		changed = false

		for k, v := range deps {
			for _, ns := range v {
				v_new, ok := deps[ns]
				if ok && !Subset(v, v_new) {
					changed = true
					deps[k] = RemoveDuplicates(append(v, v_new...))
				}
			}
		}

	}

	return deps
}

// ToSparql transforms a SHACL document into a series of Sparql queries
// one for each node  shape
func (s ShaclDocument) ToSparql() []string {
	var output []string

	for i := range s.nodeShapes {
		output = append(output, s.nodeShapes[i].ToSparql())
	}

	return output
}

func remove(s [][]rdf2go.Term, i int) [][]rdf2go.Term {
	s[i] = s[len(s)-1]
	return s[:len(s)-1]
}

// func remove(slice [][]rdf2go.Term, s int) [][]rdf2go.Term {
// 	return append(slice[:s], slice[s+1:]...)
// }

func (s *ShaclDocument) AllCondAnswers(ep endpoint) {
	for k, v := range s.shapeNames {

		out := ep.Answer(v)
		// fmt.Println(k, "  for dep ", v.name, " we got the uncond answers ", out.LimitString(5))

		s.condAnswers[k] = out
	}

	s.answered = true
}

// UnwindAnswer computes the unconditional answers
func (s *ShaclDocument) UnwindAnswer(name string) Table {
	// return empty slice if called before answers have been computed

	if s.answered {
		_, ok := s.shapeNames[name]
		if !ok {
			log.Panic(name, " is not a defined node  shape")
		}
		uncondTable := s.condAnswers[name]

		deps := s.dependency[name]

		for _, dep := range deps {

			// check if recursive shape
			if dep.name == name {
				log.Panic(name, " is a recursive SHACL node  shape, as it depends on itself.")
			}

			var depTable Table
			if _, ok := s.uncondAnswers[dep.name]; ok {
				depTable = s.uncondAnswers[dep.name]
			} else {
				depTable = s.UnwindAnswer(dep.name) // recursively compute the needed uncond. answers
			}
			// we now know that we deal with unconditional (unary) answers

			var columnToCompare int
			if dep.extrinsic {
				found := false
				for i, h := range uncondTable.header {
					if strings.HasPrefix(h, dep.name[28:]) {
						found = true
						columnToCompare = i
					}
				}
				if !found {
					log.Panic("Couldn't find dep ", dep.name, " inside ", uncondTable.header)
				}
			} else {
				columnToCompare = 0 // intrinsic checks are made against the node shape itself
			}

			// filtering out answers from uncondTable

			var affectedIndices []int // first iterate, _then_ remove!

			for i := range uncondTable.content {
				if mem(depTable.content, uncondTable.content[i][columnToCompare]) {
					// fmt.Print("At the position ", depTable.content)
					// if dep.negative {
					// fmt.Println("in  ", dep.name, ", found the term ", uncondTable.content[i][columnToCompare].String(), " ", i)
					// }

					affectedIndices = append(affectedIndices, i)
				}
				// else {
				// fmt.Println("for  ", dep.name, " NOT FOUND the term ", uncondTable.content[i][columnToCompare].String(), " ", i)
				// }
			}

			// fmt.Println("Size of working table before ", len(uncondTable.content))

			if dep.negative { //  for negative deps, we remove the  affected indices
				sort.Sort(sort.Reverse(sort.IntSlice(affectedIndices)))
				// sort.Ints(affectedIndices)
				// fmt.Println("affectedIndices ", affectedIndices)
				for _, i := range affectedIndices {
					// fmt.Println("removing ", i, " ", uncondTable.content[i][columnToCompare])
					uncondTable.content = remove(uncondTable.content, i)
				}
			} else { // inversely, for positive deps we only keep the affected  indices
				var temp [][]rdf2go.Term
				for _, i := range affectedIndices {
					temp = append(temp, uncondTable.content[i])
				}

				uncondTable.content = temp
			}

			// fmt.Println("Size of working table afters ", len(uncondTable.content), " cheking ", dep.negative, " dep ", dep.name)

			// fmt.Println("result \n", uncondTable.String())

		}

		var newTable Table

		newTable.header = uncondTable.header[:1]

		for i := range uncondTable.content {
			newTable.content = append(newTable.content, uncondTable.content[i][:1])
		}

		// create the new mapping
		s.uncondAnswers[name] = newTable
	}

	return s.uncondAnswers[name]
}

func (s ShaclDocument) GetTargets(name string, ep endpoint) Table {
	ns, ok := s.shapeNames[name]
	if !ok {
		log.Panic(name, " is not a defined node  shape")
	}
	var out Table

	switch ns.target.(type) {
	case TargetClass:
		t := ns.target.(TargetClass)

		query := "" +
			"PREFIX db: <http://dbpedia.org/>\n" +
			"PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n" +
			"PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n" +
			"PREFIX dbo:  <https://dbpedia.org/ontology/>\n" +
			"PREFIX dbr:  <https://dbpedia.org/resource/>\n" +
			"PREFIX sh:   <http://www.w3.org/ns/shacl#>\n\n" +
			"SELECT ?sub {\n" +
			"  ?sub ?a NODE .\n" +
			"}"

		query = strings.ReplaceAll(query, "NODE", t.class.String())

		fmt.Println(query)

		out = ep.Query(query)
	case TargetNode:
		t := ns.target.(TargetNode)

		query := "" +
			"PREFIX db: <http://dbpedia.org/>\n" +
			"PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n" +
			"PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n" +
			"PREFIX dbo:  <https://dbpedia.org/ontology/>\n" +
			"PREFIX dbr:  <https://dbpedia.org/resource/>\n" +
			"PREFIX sh:   <http://www.w3.org/ns/shacl#>\n\n" +
			"ASK {\n" +
			"  ?sub ?pred ?obj .\n" +
			"  FILTER (?sub = NODE || ?pred = NODE || ?obj = NODE) \n" +
			"}"

		query = strings.ReplaceAll(query, "NODE", t.node.String())

		out = ep.Query(query)
	case TargetSubjectOf:
		t := ns.target.(TargetSubjectOf)

		query := "" +
			"PREFIX db: <http://dbpedia.org/>\n" +
			"PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n" +
			"PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n" +
			"PREFIX dbo:  <https://dbpedia.org/ontology/>\n" +
			"PREFIX dbr:  <https://dbpedia.org/resource/>\n" +
			"PREFIX sh:   <http://www.w3.org/ns/shacl#>\n\n" +
			"SELECT ?sub {\n" +
			"  ?sub NODE ?obj .\n" +
			"}"

		query = strings.ReplaceAll(query, "NODE", t.path.String())

		out = ep.Query(query)
	case TargetObjectsOf:
		t := ns.target.(TargetObjectsOf)

		query := "" +
			"PREFIX db: <http://dbpedia.org/>\n" +
			"PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>\n" +
			"PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\n" +
			"PREFIX dbo:  <https://dbpedia.org/ontology/>\n" +
			"PREFIX dbr:  <https://dbpedia.org/resource/>\n" +
			"PREFIX sh:   <http://www.w3.org/ns/shacl#>\n\n" +
			"SELECT ?obj {\n" +
			"  ?sub NODE ?obj .\n" +
			"}"

		query = strings.ReplaceAll(query, "NODE", t.path.String())

		out = ep.Query(query)
	}

	return out
}
