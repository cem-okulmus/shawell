package main

import (
	"fmt"
	"strconv"
	"strings"

	"github.com/deiu/rdf2go"
)

// TODO: maybe handle invertedPath more systematically in the future?

// PropertyConstraint expresses contstraints on properties that go out
// from the target node.
type PropertyConstraint struct {
	path     rdf2go.Term // the outgoing property that is being restricted
	inverse  bool        // indicates that the path is inverted
	class    rdf2go.Term // restrict the target to a class
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
	} else {
		sb.WriteString(" restricted to node shape: " + p.node.RawValue())
	}
	sb.WriteString(fmt.Sprint("( ", p.minCount, ",", p.maxCount, " )\n"))

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

	sb.WriteString(n.name[28:])
	sb.WriteString("\nTarget: " + fmt.Sprint(n.target))
	switch n.target.(type) {
	case TargetObjectsOf:
		sb.WriteString("(TargetObjectOf)")
	case TargetClass:
		sb.WriteString("(TargetClass)")
	}
	sb.WriteString(fmt.Sprint("\nProperties:", " ", len(n.properties), "\n"))
	for _, p := range n.properties {
		sb.WriteString(p.String())
	}

	if len(n.positiveSlice) > 0 {
		sb.WriteString(fmt.Sprint("\n SH And:", " ", len(n.positiveSlice), "\n {"))
		for i, ns := range n.positiveSlice {
			sb.WriteString(ns)
			if i < len(n.positiveSlice)-1 {
				sb.WriteString(",")
			}
		}
		sb.WriteString("}\n")
	}

	if len(n.negativeSlice) > 0 {
		sb.WriteString(fmt.Sprint("\n SH Not:", " ", len(n.negativeSlice), "\n {"))
		for i, ns := range n.negativeSlice {
			sb.WriteString(ns)
			if i < len(n.negativeSlice)-1 {
				sb.WriteString(",")
			}
		}
		sb.WriteString("}\n")
	}

	sb.WriteString("\nClosed: " + fmt.Sprint(n.closed))

	return sb.String()
}

// GetNodeShape takes as input and RDF graph and a term signifying a NodeShape
// and then iteratively queries the RDF graph to extract all its details
func GetNodeShape(rdf *rdf2go.Graph, name string) (bool, NodeShape) {
	subject := rdf2go.NewResource(name)
	triples := rdf.All(subject, nil, nil)
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
				case sh + "node":
					pc.node = t2.Object
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
			blank := t.Object

			negTriple := rdf.One(blank, nil, nil)
			negatives = append(negatives, negTriple.Object.RawValue())
		}

		if t.Predicate.Equal(res(sh + "closed")) {
			b, err := strconv.ParseBool(t.Object.RawValue())
			check(err)
			closed = b
		}

	}

	return isNodeShape, NodeShape{
		name:          name,
		properties:    properties,
		positiveSlice: positives,
		negativeSlice: negatives,
		target:        target,
		closed:        closed,
	}
}

// ToSparql produces a Sparql query that when run against an endpoint returns
// the list of potential nodes satisying the shape, as well as a combination of
// other nodes expressiong a conditional shape dependency such that any
// potential node is only satisfied if and only if the conditional nodes have
// or do not have the specified shapes.
func (n NodeShape) ToSparql() string {
	var sb strings.Builder

	sb.WriteString("PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> \n")
	sb.WriteString("PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#> \n")
	sb.WriteString("PREFIX dbo:  <https://dbpedia.org/ontology/>\n")
	sb.WriteString("PREFIX dbr:  <https://dbpedia.org/resource/>\n")
	sb.WriteString("PREFIX sh:   <http://www.w3.org/ns/shacl#>\n\n")

	sb.WriteString("SELECT distinct (?sub as ?" + n.name[28:] + " )") // initial part

	// for each property constraint with recursive refs
	var outputAttributes []string

	// one for each property constraint and other constraints
	var outputWhereStatements []string

	var usedPaths []string // keep track of all (non-inverse) path constraints
	usedPaths = append(usedPaths, res(rdfs+"type").String())

	rN := 1 // running number, used to make the vars distinct

	for _, p := range n.properties {
		// check if counting constraints present or not
		var tb strings.Builder
		var output string

		if p.inverse {
			tb.WriteString(fmt.Sprint("?obj", rN, " ", p.path.String(), " ?sub .\n"))

			if p.minCount != 0 || p.maxCount != 0 {
				tb.WriteString("{\n")
				tb.WriteString(fmt.Sprint("SELECT ?InnerPred", rN, " ?InnerObj", rN))
				tb.WriteString(fmt.Sprint(" (COUNT (DISTINCT ?InnerSub", rN, ") AS ?countObj", rN, ")"))
				tb.WriteString(fmt.Sprint(" (GROUP_CONCAT (DISTINCT ?InnerSub", rN, ") AS ?listObjs", rN, ")\n"))
				tb.WriteString(fmt.Sprint("WHERE {\n"))
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
			tb.WriteString(fmt.Sprint("?sub ", p.path.String(), " ?obj", rN, " .\n"))

			if p.minCount != 0 || p.maxCount != 0 {
				tb.WriteString("{\n")
				tb.WriteString(fmt.Sprint("SELECT ?InnerSub", rN, " ?InnerPred", rN))
				tb.WriteString(fmt.Sprint(" (COUNT (DISTINCT ?InnerObj", rN, ") AS ?countObj", rN, ")"))
				tb.WriteString(fmt.Sprint(" (GROUP_CONCAT (DISTINCT ?InnerObj", rN, ") AS ?listObjs", rN, ")\n"))
				tb.WriteString(fmt.Sprint("WHERE {\n"))
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
			out := fmt.Sprint("?obj", rN, " (rdfs:type/rdfs:subClassOf)* ", p.class.String(), " .\n")
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
		sb.WriteString(fmt.Sprint("FILTER NOT EXISTS {?sub ?pred ?objClose FILTER ( ?pred NOT IN ("))
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

type ShaclDocument struct {
	nodeShapes []NodeShape
	shapeNames map[string]*NodeShape // used to unwind references to shapes
}

func (s ShaclDocument) String() string {
	var sb strings.Builder
	for _, t := range s.nodeShapes {
		sb.WriteString(fmt.Sprintln("\n", t.String()))
	}
	return sb.String()
}

func GetShaclDocument(rdf *rdf2go.Graph) (bool, ShaclDocument) {
	var out ShaclDocument
	var detected bool
	out.shapeNames = make(map[string]*NodeShape)

	NodeShapeTriples := rdf.All(nil, ResA, res(sh+"NodeShape"))

	for _, t := range NodeShapeTriples {
		name := t.Subject.RawValue()
		ok, ns := GetNodeShape(rdf, name)
		if !ok {
			detected = false
			break
		}
		out.nodeShapes = append(out.nodeShapes, ns)
		out.shapeNames[name] = &ns // add a reference to newly extracted shape
	}

	return detected, out
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
