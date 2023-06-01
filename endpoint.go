package main

import (
	"fmt"
	"sort"
	"strings"
	"text/tabwriter"
	"time"

	rdf "github.com/deiu/rdf2go"

	"github.com/knakk/sparql"
	"golang.org/x/exp/constraints"
)

// GetTable returns from a query result a table, and a header of shape names

type Table struct {
	query   SparqlQueryFlat // the _flattened_ query  which generated the Table
	header  []string
	content [][]rdf.Term
	cache   []string
}

func (t Table) String() string {
	return t.Limit(len(t.content))
}

func (t Table) GetColumn(column int) []string {
	var out []string

	for i := range t.content {
		out = append(out, t.content[i][column].String())
	}

	return out
}

// Sorted has complexity: O(n * log(n)), a needs to be sorted
func SortedGeneric[T constraints.Ordered](a []T, b []T) []T {
	set := make([]T, 0)

	for _, v := range a {
		idx := sort.Search(len(b), func(i int) bool {
			return b[i] >= v
		})
		if idx < len(b) && b[idx] == v {
			set = append(set, v)
		}
	}

	return set
}

// CheckInclusion checks for a given column of another table whether it's contained
// fully in the first column of this row. (TODO could be generalised a bit if needed)
func (t *Table) CheckInclusion(other []rdf.Term) bool {
	if len(t.content) == 0 && len(other) != 0 {
		return false // empty Table contains nothing non-empty
	}
	if len(other) == 0 {
		return true // empty list is contained in anything
	}

	if len(t.cache) == 0 {
		for i := range t.content {
			t.cache = append(t.cache, t.content[i][0].RawValue())
		}
	}

	var otherString []string

	for i := range other {
		otherString = append(otherString, other[i].RawValue())
	}

	intersectSize := len(SortedGeneric(t.cache, otherString))

	fmt.Println("This: ", t.cache)
	fmt.Println("Other: ", otherString)

	fmt.Println("Intersect Size: ", intersectSize)

	return intersectSize == len((otherString))
}

func (t Table) FindRow(column int, value string) (int, bool) {
	var found bool
	var foundRow int

	for i := range t.content {
		if t.content[i][column].String() == value {
			foundRow = i
			found = true
			break
		}
	}

	return foundRow, found
}

func (t Table) Limit(n int) string {
	if n > len(t.content) {
		n = len(t.content)
	}
	var sb strings.Builder
	const padding = 4
	w := tabwriter.NewWriter(&sb, 0, 0, padding, ' ', tabwriter.TabIndent)

	fmt.Fprint(w, "\n", strings.Join(t.header, "\t"), "\t\n")

	for i := range t.content[:n] {

		for j := range t.content[i] {
			fmt.Fprint(w, abbr(t.content[i][j].String()))
			fmt.Fprint(w, "\t ")
		}
		fmt.Fprint(w, "\n")
	}

	if n < len(t.content) {
		fmt.Fprint(w, "\n\n\t\t⋮ (showing first ",
			n, " lines from ", len(t.content), " total) \n")
	} else {
		fmt.Fprint(w, "\n\t\t ( Total: ", len(t.content), " lines) \n")
	}

	err := w.Flush()
	check(err)
	return sb.String()
}

func GetTable(r *sparql.Results) Table {
	var resultTable [][]rdf.Term

	var ordering map[string]int = make(map[string]int)

	for i, s := range r.Head.Vars {
		ordering[s] = i
	}

	for _, t := range r.Solutions() {
		var tupleOrdered []rdf.Term = make([]rdf.Term, len(t))

		for k, v := range t {
			if v.String() == "" {
				continue
			}

			tupleOrdered[ordering[k]] = res(v.String()) // needed since range over map unsorted
		}

		if len(tupleOrdered) == 0 {
			continue
		}

		resultTable = append(resultTable, tupleOrdered)
	}

	return Table{header: r.Head.Vars, content: resultTable}
}

type endpoint interface {
	Answer(ns *Shape, target SparqlQueryFlat) Table
	Query(s SparqlQuery) Table
	QueryFlat(s SparqlQueryFlat) Table
	QueryAsk(s string) bool
}

type SparqlEndpoint struct {
	repo *sparql.Repo
}

func GetSparqlEndpoint(address, username, password string) SparqlEndpoint {
	repo, err := sparql.NewRepo(address,
		sparql.DigestAuth(username, password),
		sparql.Timeout(time.Second*600),
	)
	check(err)

	return SparqlEndpoint{repo: repo}
}

// Answer takes as input a NodeShape, and runs its Sparql query against the endpoint
func (s SparqlEndpoint) Answer(ns *Shape, target SparqlQueryFlat) Table {
	query := (*ns).ToSparql(target)
	// fmt.Println("Query: \n", query.String())
	res, err := s.repo.Query(query.String())
	if err != nil {
		fmt.Println("Query in question:\n ", query)
		panic(err)
	}

	// fmt.Println("Query:  \n", query)

	out := GetTable(res)

	out.query = (*ns).ToSparqlFlat(target)
	return out
}

func (s SparqlEndpoint) Query(query SparqlQuery) Table {
	// query := ns.ToSparql()
	res, err := s.repo.Query(query.String())
	if err != nil {
		fmt.Println("Query in question:\n ", query.String())
		panic(err)
	}
	// fmt.Println("Query:  \n", query)

	out := GetTable(res)

	// out.query = query
	return out
}

func (s SparqlEndpoint) QueryFlat(query SparqlQueryFlat) Table {
	// query := ns.ToSparql()
	res, err := s.repo.Query(query.String())
	if err != nil {
		fmt.Println("Query in question:\n ", query.String())
		panic(err)
	}
	// fmt.Println("QueryFLAT:  \n", query)

	out := GetTable(res)
	// fmt.Println("Result: \n", out)

	// out.query = query
	return out
}

func (s SparqlEndpoint) QueryAsk(query string) bool {
	// query := ns.ToSparql()
	res, err := s.repo.Query(query)
	if err != nil {
		fmt.Println("Query in question:\n ", query)
		panic(err)
	}
	// fmt.Println("Query:  \n", query)

	return res.Boolean
}
