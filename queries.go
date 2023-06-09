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
func (p PropertyShape) ToSparql(target SparqlQueryFlat) (out SparqlQuery) {
	// this will basically just call ToSubquery, but instead turn it into an object of type
	// SparqlQuery, corresponding to a single node shape only having this property as a constraint

	tmp := NodeShape{}

	tmp.IRI = p.shape.IRI
	tmp.properties = append(tmp.properties, p)

	return tmp.ToSparql(target)
}

// ToSparql produces a stand-alone sparql query that produces the list of nodes satisfying the
// shape in the RDF graph
func (p PropertyShape) ToSparqlFlat(target SparqlQueryFlat) (out SparqlQueryFlat) {
	// this will basically just call ToSubquery, but instead turn it into an object of type
	// SparqlQuery, corresponding to a single node shape only having this property as a constraint

	tmp := NodeShape{}

	tmp.IRI = p.shape.IRI
	tmp.properties = append(tmp.properties, p)

	return tmp.ToSparqlFlat(target)
}

// ToSubquery is used to embedd the property shape into a node shape by way of a subquery in the
// body, and number of variables in the head. The head variables are only included in the
// presence of referential constraints (and,or,xone,node,not, qualifiedValueShape)
func (p PropertyShape) ToSubquery(num int, output bool) (head []string, body string, having []HavingClause) {
	universalOnly := true
	// referentialConsPresent := false

	objName := "?InnerObj" + strconv.Itoa(num)
	path := p.path.PropertyString()

	var bodyParts []string
	// var OuterBodyParts []string // to be used to for correlation and min/max counts

	// initial := fmt.Sprint("FILTER (!BOUND(?InnerSub", num, ")  || ?InnerSub", num, "  = ?sub) .")
	// OuterBodyParts = append(OuterBodyParts, initial)

	// EXISTENTIAL { hasValue, minCount, qualifiedMinCount}

	if p.shape.hasValue != nil {
		universalOnly = false
		out := fmt.Sprint("FILTER EXISTS { ?sub ", path, " ", (*p.shape.hasValue).String(), " } .")

		bodyParts = append(bodyParts, out)
	}

	if p.minCount > 0 {
		universalOnly = false
		// tmp := fmt.Sprint("( ", p.minCount, " <= COUNT(DISTINCT ?InnerObj", num, ") )")

		tmp := HavingClause{
			min:      false,
			numeral:  p.minCount,
			variable: fmt.Sprint("?InnerObj", num),
			path:     path,
		}
		having = append(having, tmp)
	}

	for i := range p.shape.qualifiedShapes {
		if p.shape.qualifiedShapes[i].min != 0 {
			universalOnly = false
		}
	}

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

	//
	// leave out property inclusion here, would require more thoughts on dependency passing
	//
	// more thoughts: 1) introduce ability to identify arbitrary shape with a string (pointer?)
	// 2) then simply use that string in attribute names 3) now pshapes can just pass on the
	// the header of their child pshapes 4) ... 5) profit
	//

	if len(p.shape.in) > 0 {
		var inList []string
		uniqObj := objName + "IN" + strconv.Itoa(len(p.shape.in))

		for i := range p.shape.in {
			inList = append(inList, p.shape.in[i].String())
		}

		inner := fmt.Sprint("FILTER ( ", uniqObj, " NOT IN (", strings.Join(inList, " "), ") ) .")
		out := fmt.Sprint("FILTER NOT EXISTS { ?sub ", path, " ", uniqObj, " . ", inner, "}")

		bodyParts = append(bodyParts, out)

	}

	if p.maxCount != 0 {
		// tmp := fmt.Sprint("(", p.maxCount, " >= COUNT(DISTINCT ?InnerObj", num, ") )")

		tmp := HavingClause{
			min:      true,
			numeral:  p.maxCount,
			variable: fmt.Sprint("?InnerObj", num),
			path:     path,
		}
		having = append(having, tmp)
	}

	// TODO: closed, ignoredProperties, severity, message, and deactivated (not dealt here?)

	var sb strings.Builder

	// add the headers nedded in outer query

	// head = append(head, fmt.Sprint("(COUNT(DISTINCT ?InnerObj", num, ") AS ?countObj", num, ")"))
	// head = append(head, fmt.Sprint("(GROUP_CONCAT(DISTINCT ?InnerObj", num, ") AS ?listObjs", num, ")"))

	// most important thing: The path expression

	if output && universalOnly {
		if universalOnly {
			sb.WriteString("OPTIONAL { \n")
		}
		sb.WriteString(fmt.Sprint("?sub", " ", p.path.PropertyString(), " ?InnerObj", num, " .\n\t"))

		if universalOnly {
			sb.WriteString("} \n")
		}
	} else {
		if !universalOnly {
			sb.WriteString(fmt.Sprint("?sub", " ", p.path.PropertyString(), " ?InnerObj", num, " .\n\t"))
		}
	}

	// inner body parts
	for i := range bodyParts {
		sb.WriteString(bodyParts[i])
		sb.WriteString("\n\t")
	}

	// {  # For every predicate expression with
	//   SELECT ?InnerSub (COUNT(DISTINCT ?InnerObj) AS ?countObj) (GROUP_CONCAT(DISTINCT ?InnerObj) AS ?listObjs)
	//   WHERE {
	//   	?InnerSub<path>?InnerObj
	//   }
	//   GROUP BY ?InnerSub
	// }

	body = sb.String()

	return head, body, having
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
func (p PropertyShape) ToSubqueryFlat(num int, output bool) (body string) {
	flatNum := 1
	universalOnly := true
	countingCase := false
	// referentialConsPresent := false

	objName := "?InnerObj" + strconv.Itoa(num)
	path := p.path.PropertyString()

	var bodyParts []string
	// var OuterBodyParts []string // to be used to for correlation and min/max counts

	// initial := fmt.Sprint("FILTER (!BOUND(?InnerSub", num, ")  || ?InnerSub", num, "  = ?sub) .")
	// OuterBodyParts = append(OuterBodyParts, initial)

	// EXISTENTIAL { hasValue, minCount, qualifiedMinCount}

	if p.shape.hasValue != nil {
		universalOnly = false
		out := fmt.Sprint("FILTER EXISTS { ?sub ", path, " ", (*p.shape.hasValue).String(), " } .")

		bodyParts = append(bodyParts, out)
	}

	if p.minCount > 0 {
		universalOnly = false
		countingCase = true

		if p.minCount > 1 {
			bodyParts = append(bodyParts, GetFlatMinExpression(num, flatNum, p.minCount, path)...)
		}

	}

	for i := range p.shape.qualifiedShapes {
		if p.shape.qualifiedShapes[i].min != 0 {
			universalOnly = false
		}
	}

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

	//
	// leave out property inclusion here, would require more thoughts on dependency passing
	//
	// more thoughts: 1) introduce ability to identify arbitrary shape with a string (pointer?)
	// 2) then simply use that string in attribute names 3) now pshapes can just pass on the
	// the header of their child pshapes 4) ... 5) profit
	//

	if len(p.shape.in) > 0 {
		var inList []string
		uniqObj := objName + "IN" + strconv.Itoa(len(p.shape.in))

		for i := range p.shape.in {
			inList = append(inList, p.shape.in[i].String())
		}

		inner := fmt.Sprint("FILTER ( ", uniqObj, " NOT IN (", strings.Join(inList, " "), ") ) .")
		out := fmt.Sprint("FILTER NOT EXISTS { ?sub ", path, " ", uniqObj, " . ", inner, "}")

		bodyParts = append(bodyParts, out)

	}

	if p.maxCount != 0 {
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
		if output && universalOnly {
			if universalOnly {
				sb.WriteString("OPTIONAL { \n")
			}
			sb.WriteString(fmt.Sprint("?sub", " ", p.path.PropertyString(), " ?InnerObj", num, " .\n\t"))

			if universalOnly {
				sb.WriteString("} \n")
			}
		} else {
			if !universalOnly {
				sb.WriteString(fmt.Sprint("?sub", " ", p.path.PropertyString(), " ?InnerObj", num, " .\n\t"))
			}
		}
	}

	// inner body parts
	for i := range bodyParts {
		sb.WriteString(bodyParts[i])
		sb.WriteString("\n\t")
	}

	// {  # For every predicate expression with
	//   SELECT ?InnerSub (COUNT(DISTINCT ?InnerObj) AS ?countObj) (GROUP_CONCAT(DISTINCT ?InnerObj) AS ?listObjs)
	//   WHERE {
	//   	?InnerSub<path>?InnerObj
	//   }
	//   GROUP BY ?InnerSub
	// }

	body = sb.String()

	return body
}

// ToSparql produces a Sparql query that when run against an endpoint returns
// the list of potential nodes satisying the shape, as well as a combination of
// other nodes expressiong a conditional shape dependency such that any
// potential node is only satisfied if and only if the conditional nodes have
// or do not have the specified shapes.
func (n NodeShape) ToSparql(target SparqlQueryFlat) (out SparqlQuery) {
	var head []string // variables and renamings appearing inside the SELECT statement
	var body []string // statements that form the inside of the WHERE clause
	var group []string
	var having []HavingClause

	// var usedPaths []string // keep track of all (non-inverse) path constraints

	head = append(head, "(?sub as ?"+removeAbbr(n.IRI.RawValue())+" )")
	// vars = append(vars, "?sub")
	group = append(group, "?sub")

	// initial := "{?sub ?pred ?obj. }\n\tUNION\n\t{?objI ?predI ?sub.}"
	// body = append(body, initial)

	body = append(body, fmt.Sprint("{\n\t", target.StringPrefix(false), "\n\t}"))

	if n.hasValue != nil {
		out := fmt.Sprint("FILTER ( ?sub = ", (*n.hasValue).String(), " ) .")

		body = append(body, out)
	}

	// UNIVERSAL

	for i := range n.valuetypes {
		body = append(body, n.valuetypes[i].SparqlBody("sub", ""))
	}
	for i := range n.valueranges {
		body = append(body, n.valueranges[i].SparqlBody("sub", ""))
	}
	for i := range n.stringconts {
		body = append(body, n.stringconts[i].SparqlBody("sub", ""))
	}
	// leaving out property pair constraints; cannot appear inside node shape

	for i, p := range n.properties {
		headP, bodyP, havingP := p.ToSubquery(i, len(p.shape.deps) > 0)

		head = append(head, headP...)
		body = append(body, bodyP)
		having = append(having, havingP...)

		// fmt.Println("The body atom for property: ", p.shape.IRI)
		// fmt.Println(p.ToSubquery(i))
		if len(p.shape.deps) > 0 { // add needed projections to later check dependencies
			nameOfRef := p.GetIRI()

			head = append(head, fmt.Sprint("( GROUP_CONCAT(DISTINCT ?InnerObj", i, "; separator=' ') AS ?", nameOfRef, " )"))
		}

	}

	// TODO: closed, ignoredProperties, severity, message
	// // Building the line for closedness condition
	// if n.closed {
	// 	sb.WriteString("FILTER NOT EXISTS {?sub ?pred ?objClose FILTER ( ?pred NOT IN (")
	// 	sb.WriteString(strings.Join(usedPaths, ", "))
	// 	sb.WriteString(" )) }\n\n")
	// }

	out.head = head
	out.body = body
	out.group = group
	out.having = having

	return out
}

// ToSparqlFlat writes a flattened version of the SparqlQuery, which eschews the use of aggregation
func (n NodeShape) ToSparqlFlat(target SparqlQueryFlat) (out SparqlQueryFlat) {
	var head string   // variables and renamings appearing inside the SELECT statement
	var body []string // statements that form the inside of the WHERE clause

	// var usedPaths []string // keep track of all (non-inverse) path constraints

	head = target.head
	// initial := "{?sub ?pred ?obj. }\n\tUNION\n\t{?objI ?predI ?sub.}"
	// body = append(body, initial)

	body = append(body, fmt.Sprint("{\n\t", target.StringPrefix(false), "\n\t}"))

	if n.hasValue != nil {
		out := fmt.Sprint("FILTER ( ?sub = ", (*n.hasValue).String(), " ) .")

		body = append(body, out)
	}

	// UNIVERSAL

	for i := range n.valuetypes {
		body = append(body, n.valuetypes[i].SparqlBody("sub", ""))
	}
	for i := range n.valueranges {
		body = append(body, n.valueranges[i].SparqlBody("sub", ""))
	}
	for i := range n.stringconts {
		body = append(body, n.stringconts[i].SparqlBody("sub", ""))
	}
	// leaving out property pair constraints; cannot appear inside node shape

	for i, p := range n.properties {
		bodyP := p.ToSubqueryFlat(i, false)

		body = append(body, bodyP)
	}

	// TODO: closed, ignoredProperties, severity, message
	// // Building the line for closedness condition
	// if n.closed {
	// 	sb.WriteString("FILTER NOT EXISTS {?sub ?pred ?objClose FILTER ( ?pred NOT IN (")
	// 	sb.WriteString(strings.Join(usedPaths, ", "))
	// 	sb.WriteString(" )) }\n\n")
	// }

	out.head = head
	out.body = body

	return out
}

// WitnessQuery returns a Sparql query that produces for a given list of nodes
// a witness query, which either shows why a given node satisfies or does not satisfy the
// query that is output in the method ToSparql()
func (n NodeShape) WitnessQuery(nodes []string) (out string) {
	return out

	// var sb strings.Builder

	// // Initial part
	// sb.WriteString("SELECT distinct (?sub as ?" + "Witness_of_" + n.name[len(_sh):] + " )")

	// // for each property constraint with recursive refs
	// var outputAttributes []string

	// // one for each property constraint and other constraints
	// var outputWhereStatements []string = []string{"{?sub ?pred ?obj.}\nUNION\n{?obj ?pred ?sub .}\n"}

	// var usedPaths []string // keep track of all (non-inverse) path constraints
	// usedPaths = append(usedPaths, res(_rdf+"type").String())

	// rN := 1 // running number, used to make the vars distinct

	// // limt to given list of nodes
	// out := fmt.Sprint("FILTER (?sub IN (", strings.Join(nodes, ", "), "))\n")
	// outputWhereStatements = append(outputWhereStatements, out)

	// for _, p := range n.properties {

	// 	var innerOutputAttributes []string
	// 	var innerWhereStatements []string

	// 	// check if counting constraints present or not
	// 	var tb strings.Builder
	// 	var tb2 strings.Builder

	// 	o := fmt.Sprint("OPTIONAL {\n \t{\n\t\tSELECT (?sub AS ?subcorrel", rN,
	// 		" ) ?obj", rN, " ")
	// 	tb.WriteString(o)

	// 	if p.inverse {
	// 		tb2.WriteString(fmt.Sprint("?obj", rN, " ", p.path.String(), " ?sub .\n\t"))

	// 		if p.minCount != 0 || p.maxCount != 0 {
	// 			tb2.WriteString("{\n\t")
	// 			tb2.WriteString(fmt.Sprint("SELECT ?InnerPred", rN, " ?InnerObj", rN))
	// 			tb2.WriteString(fmt.Sprint(" (COUNT (DISTINCT ?InnerSub", rN, ") AS ?countObj", rN, ")"))
	// 			tb2.WriteString(fmt.Sprint(" (GROUP_CONCAT (DISTINCT ?InnerSub", rN, ") AS ?listObjs", rN, ")\n\t"))
	// 			tb2.WriteString("WHERE {\n\t")
	// 			tb2.WriteString(fmt.Sprint("?InnerSub", rN, " ", p.path.String(), " ?InnerObj", rN, " .\n\t"))
	// 			tb2.WriteString("}\n\t")
	// 			tb2.WriteString(fmt.Sprint("GROUP BY ?InnerPred", rN, " ?InnerObj", rN, "\n\t"))
	// 			tb2.WriteString("}\n\t")
	// 			tb2.WriteString(fmt.Sprint("FILTER (?InnerObj", rN, " = ?sub)\n"))
	// 		}

	// 	} else {
	// 		tb2.WriteString(fmt.Sprint("?sub ", p.path.String(), " ?obj", rN, " .\n\t"))

	// 		if p.minCount != 0 || p.maxCount != 0 {
	// 			tb2.WriteString("{\n\t")
	// 			tb2.WriteString(fmt.Sprint("SELECT ?InnerSub", rN, " ?InnerPred", rN))
	// 			tb2.WriteString(fmt.Sprint(" (COUNT (DISTINCT ?InnerObj", rN, ") AS ?countObj", rN, ")"))
	// 			tb2.WriteString(fmt.Sprint(" (GROUP_CONCAT (DISTINCT ?InnerObj", rN, ") AS ?listObjs", rN, ")\n\t"))
	// 			tb2.WriteString("WHERE {\n\t")
	// 			tb2.WriteString(fmt.Sprint("?InnerSub", rN, " ", p.path.String(), " ?InnerObj", rN, " .\n\t"))
	// 			tb2.WriteString("}\n\t")
	// 			tb2.WriteString(fmt.Sprint("GROUP BY ?InnerSub", rN, " ?InnerPred", rN, "\n\t"))
	// 			tb2.WriteString("}\n\t")
	// 			tb2.WriteString(fmt.Sprint("FILTER (?InnerSub", rN, " = ?sub)\n"))

	// 		}
	// 		usedPaths = append(usedPaths, p.path.String()) // adding to list of encountered
	// 	}
	// 	innerWhereStatements = append(innerWhereStatements, tb2.String())

	// 	var pathOutputs []string

	// 	pathOutputs = append(pathOutputs, fmt.Sprint("(", p.path.String(), " AS ?", "path", rN, " )"))
	// 	// pathOutputs = append(pathOutputs, fmt.Sprint("( ?obj", rN, " AS ?", "obj", rN, " )"))

	// 	// innerOutputAttributes = append(innerOutputAttributes, fmt.Sprint("(?obj", rN, " AS ?ValueWitness,", rN, ")"))

	// 	if p.minCount != 0 || p.maxCount != 0 {
	// 		var o string
	// 		if p.maxCount != 0 {
	// 			o = fmt.Sprint("COALESCE(",
	// 				" IF(?countObj", rN, " < ", p.minCount, ", 1/0, ",
	// 				" IF(?countObj", rN, " > ", p.maxCount, ", 1/0, \"Object count matches constraint\" ))",
	// 				",\"Violation: Object count for path", rN, " not matching requirement.\")")
	// 		} else {
	// 			o = fmt.Sprint("COALESCE(",
	// 				" IF(?countObj", rN, " < ", p.minCount, ", 1/0, \"Object count matches constraint\" )",
	// 				",\"Violation: Object count for path", rN, " not matching requirement.\")")
	// 		}
	// 		// pathOutputs = append(pathOutputs, o)
	// 		pathOutputs = append(pathOutputs, fmt.Sprint("(", o, " AS ?CountWitness", rN, " ) "))

	// 		pathOutputs = append(pathOutputs, fmt.Sprint("( ?listObjs", rN, " AS ?listWitness", rN, " ) "))
	// 		innerOutputAttributes = append(innerOutputAttributes, fmt.Sprint("?countObj", rN, " "))
	// 		innerOutputAttributes = append(innerOutputAttributes, fmt.Sprint("?listObjs", rN, " "))
	// 	}
	// 	if p.class != nil {

	// 		pathOutputs = append(pathOutputs, fmt.Sprint("( COALESCE(?obj", rN,
	// 			", \"No ", p.path, "-connected node of class ", p.class.String(), "\") AS ?ClassWitness", rN, " ) "))
	// 		out := fmt.Sprint("?obj", rN, " rdf:type/rdfs:subClassOf* ", p.class.String(), " .\n")
	// 		innerWhereStatements = append(innerWhereStatements, out)
	// 	}
	// 	if p.hasValue != nil {

	// 		pathOutputs = append(pathOutputs, fmt.Sprint("( COALESCE(?obj", rN, ", \"Violation: No ",
	// 			p.path, "-connected node of value ", p.hasValue.String(), "\") AS ?ClassWitness", rN, " ) "))
	// 		out := fmt.Sprint("FILTER ( ?obj", rN, " = ", p.hasValue.String(), " )\n")
	// 		innerWhereStatements = append(innerWhereStatements, out)
	// 	}

	// 	outputAttributes = append(outputAttributes, pathOutputs...)

	// 	// outputWhereStatements = append(outputWhereStatements, tb.String())

	// 	tb.WriteString(strings.Join(innerOutputAttributes, " "))
	// 	tb.WriteString(" WHERE {\n\t")
	// 	tb.WriteString(strings.Join(innerWhereStatements, "\n\t"))
	// 	tb.WriteString(fmt.Sprint("\t}\n}\n FILTER(?subcorrel", rN, " = ?sub)\n}"))

	// 	outputWhereStatements = append(outputWhereStatements, tb.String())

	// 	rN++
	// }

	// // Building the line for closedness condition
	// if n.closed {
	// 	var tb strings.Builder

	// 	tb.WriteString("OPTIONAL { { SELECT (?sub AS ?subcorrel) (?pred AS ?closednessWitness) " +
	// 		"WHERE { ?sub ?pred ?obj2.  FILTER ( ?pred NOT IN (")
	// 	tb.WriteString(strings.Join(usedPaths, ", "))
	// 	tb.WriteString(" )) } } FILTER(?subcorrel = ?sub) } \n\n")

	// 	outputWhereStatements = append(outputWhereStatements, tb.String())
	// 	o := "(COALESCE(?closednessWitness,\"Closed constraint satisifed.\") as ?clos) "
	// 	outputAttributes = append(outputAttributes, o)
	// }

	// // buildling the SELECT line
	// for _, a := range outputAttributes {
	// 	sb.WriteString(" " + a)
	// }
	// sb.WriteString("{ \n")

	// // building the inside of the WHERE
	// for _, w := range outputWhereStatements {
	// 	sb.WriteString(w)
	// 	sb.WriteString("\n")
	// }

	// sb.WriteString("}\n")
	// return sb.String()
}

// FindWitnessQueryFailures returns for a given list of nodes, a list of explanations
// why they fail validation against the shape, and a boolean whether there is at least one node
// which does seem to satisfy the witness query
func (s ShaclDocument) FindWitnessQueryFailures(shape string, nodes []string, ep endpoint) ([]string, bool) {
	return []string{}, false

	// // if !s.validated {
	// // 	log.Panicln("Cannot call FindWitnessQueryFailures before validation")
	// // }

	// query := s.shapeNames[shape].WitnessQuery(nodes)
	// witTable := ep.Query(query)

	// var nodeMap map[string]*struct{} = make(map[string]*struct{})

	// for i := range nodes {
	// 	nodeMap[nodes[i]] = nil
	// }

	// // check  if we got a result for every node
	// if len(witTable.content) != len(nodes) {
	// 	log.Panicln("Witness query did not return a line for every checked node: ",
	// 		len(witTable.content), " instead of ", len(nodes))
	// }

	// var answers []string
	// metAll := false // indicates that there is a node that does meet all constraints

	// for i := range witTable.content {
	// 	node := witTable.content[i][0].String()
	// 	_, ok := nodeMap[node]
	// 	if !ok {
	// 		log.Panicln("Found a non-matching node in witness result ",
	// 			"node: ", node, " list of nodes: ", nodes)
	// 	}
	// 	violationFound := false

	// 	var violations []string

	// 	// look for violations in other columns

	// 	for j := range witTable.content[i][1:] {
	// 		text := witTable.content[i][j].RawValue()

	// 		if strings.HasPrefix(text, "Violation") {
	// 			violationFound = true
	// 			violations = append(violations, text)
	// 		}
	// 	}
	// 	if !violationFound {
	// 		metAll = true
	// 	} else {
	// 		answers = append(answers, fmt.Sprint("For node ", node, ": ",
	// 			strings.Join(violations, "; "), "."))
	// 	}

	// }

	// return answers, metAll
}
