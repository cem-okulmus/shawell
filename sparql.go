package main

import (
	"fmt"
	"strings"
)

type CountingSubQuery struct {
	graph  string
	target string
	id     int
	min    bool
	max    bool
	numMin int
	numMax int
	path   PropertyPath
}

// ProduceBody generates the SPARQL subquery body for counting constraints with cardinality bounds.
// Produces an optional graph pattern with COUNT aggregation and FILTER for min/max constraints.
func (c CountingSubQuery) ProduceBody() string {
	var sb strings.Builder

	head := []string{"?sub", fmt.Sprint("( COUNT(DISTINCT ?obj) AS ?count", c.id, ")")}
	core := "OPTIONAL {\n\t" + fmt.Sprint("?sub ", c.path.PropertyString(), " ?obj. ") + "\n\t}"
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
	target     string   // make target explicit
	body       []string // positive expressions that check for existence of some objects
	group      []string
	graph      string // if non-empty, then we query terms inside this named graph only
	subqueries []CountingSubQuery
}

// SparqlQueryFlat is used for the target restrictions, these need to be "flat"; meaning no form
// of aggregation is allowed, this is achieved by rewriting non-flattened SparqlQueries
type SparqlQueryFlat struct {
	head  string   // only a single attribute in the head
	body  []string // positive expressions that check for existence of some objects
	graph string   // if non-empty, then we query terms inside this named graph only
}

// String converts a SparqlQuery to its full SPARQL string representation with prefixes.
func (s SparqlQuery) String() string {
	return s.StringPrefix(true) // by default, always include prefixes
}

// String converts a SparqlQueryFlat to its full SPARQL string representation with prefixes.
func (s SparqlQueryFlat) String() string {
	return s.StringPrefix(true) // by default, always include prefixes
}

// JustPrefix returns only the PREFIX declarations for a SparqlQuery without the query body.
func (s SparqlQuery) JustPrefix() string {
	var sb strings.Builder

	// attach prefixes

	for k, v := range prefixes {
		sb.WriteString("PREFIX " + k + " <" + v + ">\n")
	}

	return sb.String()
}

// JustPrefix returns only the PREFIX declarations for a SparqlQueryFlat without the query body.
func (s SparqlQueryFlat) JustPrefix() string {
	var sb strings.Builder

	// attach prefixes

	for k, v := range prefixes {
		sb.WriteString("PREFIX " + k + " <" + v + ">\n")
	}

	return sb.String()
}

// Unused target option, to remove restriction to fixed targets
//
// UniversalTarget returns a SparqlQueryFlat that matches every node in the graph,
// used by AllCondAnswers when rules are present to evaluate shapes against all nodes
// rather than restricting to declared SHACL targets.
// func UniversalTarget() SparqlQueryFlat {
// 	return SparqlQueryFlat{
// 		head: "?sub ?indirect0",
// 		body: []string{"{ ?sub ?p ?obj . } UNION { ?obj ?p ?sub . }"},
// 	}
// }

// ProjectToVar transforms a flat query by reprojecting its results to a different variable.
// If external is true, treats the query as targeting property values; otherwise targets the focus node.
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

// StringPrefix renders a SparqlQuery as a SPARQL SELECT string.
// If attachPrefix is true, includes PREFIX declarations; otherwise produces a subquery.
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

	if len(s.subqueries) == 0 {
		if s.graph != "" {
			sb.WriteString(" GRAPH " + s.graph + " { \n\t")
		}
		sb.WriteString(s.target + "\n\t")
		sb.WriteString(strings.Join(s.body, "\n\t"))
		if s.graph != "" {
			sb.WriteString("\n\t} \n\t")
		}
	} else {
		if s.graph != "" {
			sb.WriteString(" GRAPH " + s.graph + " { \n\t")
			sb.WriteString(s.target + "\n\t")
			if len(s.body) > 0 {
				sb.WriteString(strings.Join(s.body, "\n\t"))
			}
			sb.WriteString("\n\t} \n\t")
		} else {
			sb.WriteString(s.target + "\n\t")
			sb.WriteString(strings.Join(s.body, "\n\t"))
		}
		for _, c := range s.subqueries {
			if s.graph != "" {
				sb.WriteString(" GRAPH " + s.graph + " ")
			}
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

// StringPrefix renders a SparqlQueryFlat as a SPARQL SELECT string.
// If attachPrefix is true, includes PREFIX declarations; otherwise produces a subquery body.
func (s SparqlQueryFlat) StringPrefix(attachPrefix bool) string {
	var sb strings.Builder

	// attach prefixes

	if attachPrefix {
		for k, v := range prefixes {
			sb.WriteString("PREFIX " + k + " <" + v + ">\n")
		}
	}

	sb.WriteString("\n\n")

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
