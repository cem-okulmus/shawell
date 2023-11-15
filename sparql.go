package main

import (
	"fmt"
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

// type HavingClause struct {
// 	min      bool // false if min, true if max
// 	numeral  int
// 	variable string // the variable being restricted
// 	path     string // the path over with the var was reached
// }

// func (h HavingClause) String() string {
// 	var order string
// 	if h.min {
// 		order = "<="
// 	} else {
// 		order = ">="
// 	}

// 	return fmt.Sprint("(", h.numeral, " ", order, " COUNT(DISTINCT ", h.variable, ") )")
// }

type CountingSubQuery struct {
	graph  string
	target string
	id     int
	min    bool
	max    bool
	numMin int
	numMax int
	path   string
}

func (c CountingSubQuery) ProduceBody() string {
	var sb strings.Builder

	head := []string{"?sub", fmt.Sprint("( COUNT(?obj) AS ?count", c.id, ")")}
	core := "OPTIONAL {\n\t" + fmt.Sprint("?sub ", c.path, " ?obj. ") + "\n\t}"
	body := []string{c.target, core}
	group := []string{"?sub"}

	sb.WriteString("{\n")
	sb.WriteString("SELECT  ")
	sb.WriteString(strings.Join(head, " "))
	sb.WriteString(" { \n\t")
	if c.graph != "" {
		sb.WriteString(" GRAPH " + c.graph + " ")
	}
	sb.WriteString(strings.Join(body, "\n\t"))

	sb.WriteString("} \n")
	if len(group) > 0 {
		sb.WriteString("GROUP BY ")
		sb.WriteString(strings.Join(group, " "))
	}
	sb.WriteString("\n} ")

	var inner []string
	if c.min {
		inner = append(inner, fmt.Sprint("?count", c.id, " >= ", c.numMin))
	}
	if c.max {
		inner = append(inner, fmt.Sprint("?count", c.id, " <= ", c.numMax))
	}
	sb.WriteString(fmt.Sprint("FILTER (", strings.Join(inner, " && "), ") . "))

	return sb.String()
}

type SparqlQuery struct {
	head       []string
	body       []string // positive expressions that check for existance of some objects
	group      []string
	graph      string // if non-empty, then we query terms inside this named graph only
	subqueries []CountingSubQuery
}

// SparqlQueryFlat is used for the target restrictions, these need to be "flat"; meaning no form
// of aggregation is allowed, this is achieved by rewritten non-flattened SparqlQueries
type SparqlQueryFlat struct {
	head  string   // only a single attribute in the head
	body  []string // positive expressions that check for existance of some objects
	graph string   // if non-empty, then we query terms inside this named graph only
}

func (s SparqlQuery) String() string {
	return s.StringPrefix(true) // by default, always include prefixes
}

func (s SparqlQueryFlat) String() string {
	return s.StringPrefix(true) // by default, always include prefixes
}

func (s SparqlQuery) JustPrefix() string {
	var sb strings.Builder

	// attach prefixes

	for k, v := range prefixes {
		sb.WriteString("PREFIX " + k + " <" + v + ">\n")
	}

	return sb.String()
}

func (s SparqlQueryFlat) JustPrefix() string {
	var sb strings.Builder

	// attach prefixes

	for k, v := range prefixes {
		sb.WriteString("PREFIX " + k + " <" + v + ">\n")
	}

	return sb.String()
}

func (s SparqlQueryFlat) ProjectToVar(variable string, external bool) (out SparqlQueryFlat) {
	var head string

	s.head = "*" // "free" the head from projection
	newBody := s.StringPrefix(false)

	if external {
		newBody = strings.ReplaceAll(newBody, "?sub", "?OldSub")
		head = fmt.Sprint("( ?", variable, " as ?sub)")
	} else {
		head = "?sub"
	}

	out.head = head
	out.body = []string{newBody}

	return out
}

func (s SparqlQuery) StringPrefix(attachPrefix bool) string {
	var sb strings.Builder

	// attach prefixes

	if attachPrefix {
		for k, v := range prefixes {
			sb.WriteString("PREFIX " + k + " <" + v + ">\n")
		}
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
	if s.graph != "" {
		sb.WriteString(" GRAPH " + s.graph + " ")
	}
	sb.WriteString(strings.Join(s.body, "\n\t"))

	if len(s.subqueries) > 0 {
		for _, c := range s.subqueries {
			sb.WriteString(c.ProduceBody())
		}
	}

	sb.WriteString("} \n")
	if len(s.group) > 0 {
		sb.WriteString("GROUP BY ")
		sb.WriteString(strings.Join(s.group, " "))
	}

	return sb.String()
}

func (s SparqlQueryFlat) StringPrefix(attachPrefix bool) string {
	var sb strings.Builder

	// attach prefixes

	if attachPrefix {
		for k, v := range prefixes {
			sb.WriteString("PREFIX " + k + " <" + v + ">\n")
		}
	}

	sb.WriteString("\n\n")

	// // get extended header and body
	// for i := range s.subqueries {
	// 	renamedBody, renamedHead := s.subqueries[i].Rename(i)
	// 	s.head = append(s.head, renamedHead...)
	// 	s.body = append(s.body, renamedBody...)
	// }

	sb.WriteString("SELECT ")
	sb.WriteString(s.head)
	sb.WriteString(" { \n\t")
	if attachPrefix && s.graph != "" { // only attach if query used stand-alone
		sb.WriteString(" GRAPH " + s.graph + " { \n\t")
	}
	sb.WriteString(strings.Join(s.body, "\n\t"))

	if attachPrefix && s.graph != "" { // only attach if query used stand-alone
		sb.WriteString("} \n } \n")
	} else {
		sb.WriteString("} \n ")
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
