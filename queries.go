package main

import (
	"fmt"
	"log"
	"strconv"
	"strings"
)

// import (
// 	"fmt"
// 	"log"
// 	"strings"
// )

// ToSparql produces a stand-alone sparql query that produces the list of nodes satisfying the
// shape in the RDF graph
func (p *PropertyShape) ToSparql(fromGraph string, target SparqlQueryFlat) (out SparqlQuery) {
	// this will basically just call ToSubquery, but instead turn it into an object of type
	// SparqlQuery, corresponding to a single node shape only having this property as a constraint

	tmp := NodeShape{}
	tmp.id = p.id

	tmp.IRI = p.shape.IRI
	tmp.properties = append(tmp.properties, p)

	return tmp.ToSparql(fromGraph, target)
}

// // ToSparql produces a stand-alone sparql query that produces the list of nodes satisfying the
// // shape in the RDF graph
// func (p *PropertyShape) ToSparqlFlat(target SparqlQueryFlat) (out SparqlQueryFlat) {
// 	// this will basically just call ToSubquery, but instead turn it into an object of type
// 	// SparqlQuery, corresponding to a single node shape only having this property as a constraint

// 	tmp := NodeShape{}
// 	tmp.id = p.id
// 	tmp.IRI = p.shape.IRI
// 	tmp.properties = append(tmp.properties, p)

// 	return tmp.ToSparqlFlat(target)
// }

// ToSubquery is used to embedd the property shape into a node shape by way of a subquery in the
// body, and number of variables in the head. The head variables are only included in the
// presence of referential constraints (and,or,xone,node,not, qualifiedValueShape)
func (p *PropertyShape) ToSubquery(num int) (head []string, body string, subquery *CountingSubQuery) {
	objName := "?InnerObj" + strconv.Itoa(num)
	path := p.path.PropertyString()

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

	//
	// leave out property inclusion here, would require more thoughts on dependency passing
	//
	// more thoughts: 1) introduce ability to identify arbitrary shape with a string (pointer?)
	// 2) then simply use that string in attribute names 3) now pshapes can just pass on the
	// the header of their child pshapes 4) ... 5) profit
	//

	// Numerical Constraints

	if p.minCount > 0 {
		// tmp := fmt.Sprint("( ", p.minCount, " <= COUNT(DISTINCT ?InnerObj", num, ") )")

		subquery.min = true
		subquery.numMin = p.minCount
		subquery.path = path
		subquery.id = num

		// tmp := CountingSubQuery{
		// 	min:      true,
		// 	max: 		false
		// 	numeral:  p.minCount,
		// 	variable: fmt.Sprint("?InnerObj", num),
		// 	path:     path,
		// }
		// subquery = append(subquery, tmp)
	}

	if p.maxCount != -1 {

		subquery.max = true
		subquery.numMax = p.maxCount
		subquery.path = path
		subquery.id = num

		// // universalOnly = false
		// // tmp := fmt.Sprint("(", p.maxCount, " >= COUNT(DISTINCT ?InnerObj", num, ") )")

		// tmp := CountingSubQuery{
		// 	min:      false,
		// 	numeral:  p.maxCount,
		// 	variable: fmt.Sprint("?InnerObj", num),
		// 	path:     path,
		// }
		// subquery = append(subquery, tmp)
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

func GetFlatMinExpression(num, flatNum, minCount int, path string) (bodyParts []string) {
	objects := []string{}
	filterEquations := []string{}

	for i := 0; i < minCount; i++ {
		triple := fmt.Sprint("?sub ", path, " ?InnerObj", num, "_", flatNum, " .")
		objects = append(objects, fmt.Sprint("?InnerObj", num, "_", flatNum))
		bodyParts = append(bodyParts, triple)
		flatNum++
	}

	if len(bodyParts) != minCount {
		log.Panicln("Wtf")
	}

	for i := 0; i < len(objects); i++ {
		a := objects[i]
		for j := i + 1; j < len(objects); j++ {
			b := objects[j]

			filterEquations = append(filterEquations, fmt.Sprint(a, " != ", b))
		}
	}

	bodyParts = append(bodyParts, fmt.Sprint("FILTER ( ", strings.Join(filterEquations, " && "), " )\n"))
	return bodyParts
}

// ToSubqueryFlat produces a flattened version of the query, eschewing the use of aggregation
func (p *PropertyShape) ToSubqueryFlat(num int, output bool) (body string) {
	flatNum := 1

	countingCase := false
	// referentialConsPresent := false

	objName := "?InnerObj" + strconv.Itoa(num)
	path := p.path.PropertyString()

	var bodyParts []string

	// UNIVERSAL
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

	//
	// leave out property inclusion here, would require more thoughts on dependency passing
	//
	// more thoughts: 1) introduce ability to identify arbitrary shape with a string (pointer?)
	// 2) then simply use that string in attribute names 3) now pshapes can just pass on the
	// the header of their child pshapes 4) ... 5) profit
	//

	if p.minCount > 0 {
		countingCase = true

		if p.minCount > 1 {
			bodyParts = append(bodyParts, GetFlatMinExpression(num, flatNum, p.minCount, path)...)
		}

	}

	if p.maxCount != -1 {
		// tmp := fmt.Sprint("(", p.maxCount, " >= COUNT(DISTINCT ?InnerObj", num, ") )")

		// tmp := HavingClause{
		// 	min:      true,
		// 	numeral:  p.maxCount,
		// 	variable: fmt.Sprint("?InnerObj", num),
		// 	path:     path,
		// }
		// having = append(having, tmp)

		partsMax := GetFlatMinExpression(num, flatNum, p.maxCount+1, path)
		countingCase = true

		maxBody := fmt.Sprint("FILTER NOT EXISTS {\n", strings.Join(partsMax, "\n"), "\n}\n")

		bodyParts = append(bodyParts, maxBody)

	}

	// TODO: closed, ignoredProperties, severity, message, and deactivated (not dealt here?)

	var sb strings.Builder

	// add the headers nedded in outer query

	// head = append(head, fmt.Sprint("(COUNT(DISTINCT ?InnerObj", num, ") AS ?countObj", num, ")"))
	// head = append(head, fmt.Sprint("(GROUP_CONCAT(DISTINCT ?InnerObj", num, ") AS ?listObjs", num, ")"))

	// most important thing: The path expression

	if !countingCase {
		if output && p.universalOnly {
			if p.universalOnly {
				sb.WriteString("OPTIONAL { \n")
			}
			sb.WriteString(fmt.Sprint("?sub", " ", p.path.PropertyString(), " ?InnerObj", num, " .\n\t"))

			if p.universalOnly {
				sb.WriteString("} \n")
			}
		} else {
			if !p.universalOnly {
				sb.WriteString(fmt.Sprint("?sub", " ", p.path.PropertyString(), " ?InnerObj", num, " .\n\t"))
			}
		}
	}

	// inner body parts
	for i := range bodyParts {
		sb.WriteString(bodyParts[i])
		sb.WriteString("\n\t")
	}

	body = sb.String()

	return body
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

	body = append(body, targetLine)

	// UNIVERSAL

	for i := range n.valuetypes {
		body = append(body, n.valuetypes[i].SparqlBody("?sub", ""))
	}
	for i := range n.valueranges {
		body = append(body, n.valueranges[i].SparqlBody("?sub", ""))
	}
	for i := range n.stringconts {
		body = append(body, n.stringconts[i].SparqlBody("?sub", ""))
	}
	for i := range n.others {
		body = append(body, n.others[i].SparqlBody("?sub", ""))
	}
	for i := range n.propairconts {
		body = append(body, n.propairconts[i].SparqlBody("?sub", ""))
	}

	// leaving out property pair constraints; cannot appear inside node shape

	for i, p := range n.properties {
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
			head = append(head, fmt.Sprint("( ?InnerObj", i, " AS ?", nameOfRef, "group )"))
		}

	}

	out.head = head
	out.body = body
	// out.group = group
	out.subqueries = subqueries
	out.graph = fromGraph

	return out
}

// // ToSparqlFlat writes a flattened version of the SparqlQuery, which eschews the use of aggregation
// func (n *NodeShape) ToSparqlFlat(target SparqlQueryFlat) (out SparqlQueryFlat) {
// 	var head string   // variables and renamings appearing inside the SELECT statement
// 	var body []string // statements that form the inside of the WHERE clause

// 	// var usedPaths []string // keep track of all (non-inverse) path constraints

// 	head = target.head
// 	// initial := "{?sub ?pred ?obj. }\n\tUNION\n\t{?objI ?predI ?sub.}"
// 	// body = append(body, initial)

// 	body = append(body, fmt.Sprint("{\n\t", target.StringPrefix(false), "\n\t}"))

// 	// UNIVERSAL

// 	for i := range n.valuetypes {
// 		body = append(body, n.valuetypes[i].SparqlBody("?sub", ""))
// 	}
// 	for i := range n.valueranges {
// 		body = append(body, n.valueranges[i].SparqlBody("?sub", ""))
// 	}
// 	for i := range n.stringconts {
// 		body = append(body, n.stringconts[i].SparqlBody("?sub", ""))
// 	}
// 	for i := range n.others {
// 		body = append(body, n.others[i].SparqlBody("?sub", ""))
// 	}
// 	// leaving out property pair constraints; cannot appear inside node shape

// 	for i, p := range n.properties {
// 		bodyP := p.ToSubqueryFlat(i, false)

// 		body = append(body, bodyP)
// 	}

// 	// TODO:  severity, message

// 	out.head = head
// 	out.body = body

// 	return out
// }
