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

type HavingClause struct {
	min      bool // false if min, true if max
	numeral  int
	variable string // the variable being restricted
	path     string // the path over with the var was reached
}

func (h HavingClause) String() string {
	var order string
	if h.min {
		order = "<="
	} else {
		order = ">="
	}

	return fmt.Sprint("(", h.numeral, " ", order, " COUNT(DISTINCT ", h.variable, ") )")
}

type SparqlQuery struct {
	head   []string
	body   []string // positive expressions that check for existance of some objects
	group  []string
	having []HavingClause
}

// SparqlQueryFlat is used for the target restrictions, these need to be "flat"; meaning no form
// of aggregation is allowed, this is achieved by rewritten non-flattened SparqlQueries
type SparqlQueryFlat struct {
	head string   // only a single attribute in the head
	body []string // positive expressions that check for existance of some objects
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

// func MergeGeneral(this, other *SparqlQueryFlat) (out *SparqlQueryFlat) {
// 	if this == nil {
// 		if other == nil {
// 			log.Panicln("Cannot merge two nil queries")
// 		}
// 		return other
// 	} else {
// 		if other == nil {
// 			return this
// 		}
// 	}
// 	tmp := this.Merge(*other)
// 	return &tmp
// }

// // Merge assumes that the two queries share the same head and only one body element
// func (s SparqlQueryFlat) Merge(other SparqlQueryFlat) (out SparqlQueryFlat) {
// 	if len(s.body) != 1 || len(other.body) != 1 {
// 		log.Panicln("Target query with more than one body!")
// 	}

// 	tmp := other.StringPrefix(false)
// 	combinedBody := "{\n" + s.body[0] + "\n}\nUNION\n{\n" + tmp + "\n}\n"

// 	out.head = s.head
// 	out.body = []string{combinedBody}

// 	return out
// }

// Assumes both s and other to be monadic target queries; returns yes if other is contained in s
func (s SparqlQueryFlat) Contained(other SparqlQueryFlat, ep endpoint) bool {
	// test if other is non-empty

	contentThis := ep.QueryFlat(s).content
	contentOther := ep.QueryFlat(other).content

	for i := range contentOther {
		otherElement := contentOther[i][0].String()

		found := false
		for j := range contentThis {
			thisElement := contentThis[j][0].String()

			if otherElement == thisElement {
				found = true
			}
		}

		if !found {
			return false
		}

	}

	return true
	// if len( == 0 || len(ep.QueryFlat(other).content[0]) == 0 {
	// 	return true // empty query contained in everything
	// }

	// var sb strings.Builder

	// for k, v := range prefixes {
	// 	sb.WriteString("PREFIX " + k + " <" + v + ">\n")
	// }

	// sb.WriteString("\n\n")

	// sb.WriteString("ASK {\n")

	// sb.WriteString("{\n" + other.StringPrefix(false) + "\n}\n")

	// sb.WriteString("FILTER NOT EXISTS { " + s.StringPrefix(false) + " }\n } \n")

	// return !ep.QueryAsk(sb.String())
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

	sb.WriteString("SELECT DISTINCT ")
	sb.WriteString(strings.Join(abbrAll(s.head), " "))
	sb.WriteString(" { \n\t")
	sb.WriteString(strings.Join(abbrAll(s.body), "\n\t"))

	sb.WriteString("} \n")
	if len(s.group) > 0 {
		sb.WriteString("GROUP BY ")
		sb.WriteString(strings.Join(abbrAll(s.group), " "))
	}
	if len(s.having) > 0 {
		sb.WriteString("\nHAVING (")

		var havings []string
		for i := range s.having {
			havings = append(havings, s.having[i].String())
		}

		sb.WriteString(strings.Join(abbrAll(havings), " && "))
		sb.WriteString(")\n")
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

	sb.WriteString("SELECT DISTINCT ")
	sb.WriteString(s.head)
	sb.WriteString(" { \n\t")
	sb.WriteString(strings.Join(abbrAll(s.body), "\n\t"))

	sb.WriteString("} \n")

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
