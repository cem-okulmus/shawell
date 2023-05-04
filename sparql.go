package main

import (
	"strconv"
	"strings"
)

// // Projection keeps track of the variales to be output in a query
// type Projection struct {
// 	vars []string
// // }

// type QueryPart interface {
// 	Vars() string
// 	Head(a int) string
// 	Body(a int) string
// }

// // WhereStatements is a collection of the body of a Sparql Query
// // This data structure is meant to expose the internal structure of each statement, allowing for
// // composability into larger queries, and renaming variables as needed to preserve semantics
// type WhereStatement struct {
// 	content string
// }

// func (w WhereStatement) Body(a int) string { return w.content }

type SparqlQuery struct {
	vars   []string // the name of all used variables
	head   []string
	body   []string // positive expressions that check for existance of some objects
	group  []string
	having []string
	// subqueries []SparqlQuery
}

func (s SparqlQuery) String() string {
	var sb strings.Builder

	// attach prefixes

	for k, v := range prefixes {
		sb.WriteString("PREFIX " + k + " <" + v + ">\n")
	}

	sb.WriteString("\n\n")

	// // get extended header and body
	// for i := range s.subqueries {
	// 	renamedBody, renamedHead := s.subqueries[i].Rename(i)
	// 	s.head = append(s.head, renamedHead...)
	// 	s.body = append(s.body, renamedBody...)
	// }

	sb.WriteString("SELECT ")
	sb.WriteString(strings.Join(s.head, " "))
	sb.WriteString(" { \n\t")
	sb.WriteString(strings.Join(s.body, "\n\t"))

	sb.WriteString("} \n")
	sb.WriteString("GROUP BY ")
	sb.WriteString(strings.Join(s.group, " "))

	if len(s.having) > 0 {
		sb.WriteString("\nHAVING (")
		sb.WriteString(strings.Join(s.having, " && "))
		sb.WriteString(")\n")
	}

	return sb.String()
}

// // Body produces the needed where statements (combined into single string) to intersect one query
// // with another. This is meant to realise intrinsic dep. between shapes, i.e. restricting the
// // same value nodes further by conditions to be tested directly on those value nodes
// // This integration does not add any new variables to the projection, it only produces
// // further statements to be added to the body.
// func (s SparqlQuery) Body(a int) string {
// 	var sb strings.Builder

// 	s.Rename(a)

// 	sb.WriteString()

// 	return sb.String()
// }

func (s SparqlQuery) Rename(id int) (head []string, body []string) {
	for i := range s.vars {
		old := s.vars[i]
		new := old + "_" + strconv.Itoa(id)

		// rename head
		for j := range s.head {
			s.head[j] = strings.ReplaceAll(s.head[j], old, new)
		}

		// rename body
		for j := range s.body {
			s.body[j] = strings.ReplaceAll(s.body[j], old, new)
		}

	}

	return s.head, s.body
}
