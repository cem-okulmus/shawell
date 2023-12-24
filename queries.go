package main

import (
	"fmt"
	"strconv"
	"strings"
)

// ToSparql produces a stand-alone sparql query that produces the list of nodes satisfying the
// shape in the RDF graph
func (p *PropertyShape) ToSparql(fromGraph string, target SparqlQueryFlat) (out SparqlQuery) {
	// this will basically just call ToSubquery, but instead turn it into an object of type
	// SparqlQuery, corresponding to a single node shape only having this property as a constraint

	tmp := NodeShape{}
	tmp.id = p.id
	// tmp.insideProp = p

	tmp.IRI = p.shape.IRI
	tmp.properties = append(tmp.properties, p)

	return tmp.ToSparql(fromGraph, target)
}

// ToSubquery is used to embedd the property shape into a node shape by way of a subquery in the
// body, and number of variables in the head. The head variables are only included in the
// presence of referential constraints (and,or,xone,node,not, qualifiedValueShape)
func (p *PropertyShape) ToSubquery(num int) (head []string, body string, subquery *CountingSubQuery) {
	objName := "?InnerObj" + strconv.Itoa(num)
	path := p.path

	if p.minCount > 0 || p.maxCount > -1 {
		subquery = &CountingSubQuery{}
	}
	var bodyParts []string

	// NON-LOGICAL CONSTRAINTS

	for i := range p.shape.valuetypes {
		bodyParts = append(bodyParts, p.shape.valuetypes[i].SparqlBody(objName, path))
	}
	for i := range p.shape.valueranges {
		bodyParts = append(bodyParts, p.shape.valueranges[i].SparqlBody(objName, path))
	}
	for i := range p.shape.stringconts {
		bodyParts = append(bodyParts, p.shape.stringconts[i].SparqlBody(objName, path))
	}
	for i := range p.shape.propairconts {
		bodyParts = append(bodyParts, p.shape.propairconts[i].SparqlBody(objName, path))
	}
	for i := range p.shape.others {
		bodyParts = append(bodyParts, p.shape.others[i].SparqlBody(objName, path))
	}

	// Numerical Constraints

	if p.minCount > 0 {
		subquery.min = true
		subquery.numMin = p.minCount
		subquery.path = path
		subquery.id = num
	}

	if p.maxCount != -1 {
		subquery.max = true
		subquery.numMax = p.maxCount
		subquery.path = path
		subquery.id = num
	}

	// TODO: severity, message (not dealt here?)

	var sb strings.Builder

	// if output && universalOnly {
	if p.universalOnly {
		sb.WriteString("OPTIONAL { \n")
	}
	sb.WriteString(fmt.Sprint("?sub", " ", p.path.PropertyString(), " ?InnerObj", num, " .\n\t"))

	if p.universalOnly {
		sb.WriteString("} \n")
	}

	// inner body parts
	for i := range bodyParts {
		sb.WriteString(bodyParts[i])
		sb.WriteString("\n\t")
	}

	body = sb.String()

	return head, body, subquery
}

// ToSparql produces a Sparql query that when run against an endpoint returns
// the list of potential nodes satisying the shape, as well as a combination of
// other nodes expressiong a conditional shape dependency such that any
// potential node is only satisfied if and only if the conditional nodes have
// or do not have the specified shapes.
func (n *NodeShape) ToSparql(fromGraph string, target SparqlQueryFlat) (out SparqlQuery) {
	var head []string // variables and renamings appearing inside the SELECT statement
	var body []string // statements that form the inside of the WHERE clause
	// var group []string
	var subqueries []CountingSubQuery

	// var usedPaths []string // keep track of all (non-inverse) path constraints

	head = append(head, "(?sub as ?"+n.GetQualName()+" )")
	// vars = append(vars, "?sub")
	// group = append(group, "?sub")

	// initial := "{?sub ?pred ?obj. }\n\tUNION\n\t{?objI ?predI ?sub.}"
	// body = append(body, initial)
	targetLine := fmt.Sprint("{\n\t", target.StringPrefix(false), "\n\t}")

	out.target = targetLine
	// body = append(body, targetLine)

	// UNIVERSAL

	for i := range n.valuetypes {
		body = append(body, n.valuetypes[i].SparqlBody("?sub", nil))
	}
	for i := range n.valueranges {
		body = append(body, n.valueranges[i].SparqlBody("?sub", nil))
	}
	for i := range n.stringconts {
		body = append(body, n.stringconts[i].SparqlBody("?sub", nil))
	}
	for i := range n.others {
		body = append(body, n.others[i].SparqlBody("?sub", nil))
	}
	for i := range n.propairconts {
		body = append(body, n.propairconts[i].SparqlBody("?sub", nil))
	}

	// leaving out property pair constraints; cannot appear inside node shape

	for i, p := range n.properties {
		if p.Nested() {
			continue // don't produce a subquery for a nested query, as those are internal deps
		}

		// headP, bodyP, havingP := p.ToSubquery(i, len(p.shape.deps) > 0)
		headP, bodyP, subquery := p.ToSubquery(i)

		head = append(head, headP...)
		body = append(body, bodyP)

		if subquery != nil {

			subquery.target = targetLine
			subqueries = append(subqueries, *subquery)
		}

		// fmt.Println("The body atom for property: ", p.shape.IRI)
		// fmt.Println(p.ToSubquery(i))
		if len(p.shape.deps) > 0 { // add needed projections to later check dependencies
			nameOfRef := p.GetQualName()

			// head = append(head, fmt.Sprint("( GROUP_CONCAT(DISTINCT ?InnerObj", i, "; separator=' ') AS ?", nameOfRef, " )"))
			head = append(head, fmt.Sprint("( ?InnerObj", i, " AS ?", nameOfRef, " )"))
		}

	}

	out.head = head
	out.body = body
	// out.group = group
	out.subqueries = subqueries
	out.graph = fromGraph

	return out
}
