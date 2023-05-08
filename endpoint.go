package main

import (
	"fmt"
	"strings"
	"text/tabwriter"
	"time"

	rdf "github.com/deiu/rdf2go"
	"github.com/knakk/sparql"
)

// GetTable returns from a query result a table, and a header of shape names

type Table struct {
	header  []string
	content [][]rdf.Term
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
			tupleOrdered[ordering[k]] = res(v.String()) // needed since range over map unsorted
		}

		resultTable = append(resultTable, tupleOrdered)
	}

	return Table{r.Head.Vars, resultTable}
}

type endpoint interface {
	Answer(ns *Shape) Table
	Query(s string) Table
}

type SparqlEndpoint struct {
	repo *sparql.Repo
}

func GetSparqlEndpoint(address, username, password string) SparqlEndpoint {
	repo, err := sparql.NewRepo(address,
		sparql.DigestAuth(username, password),
		sparql.Timeout(time.Millisecond*1500),
	)
	check(err)

	return SparqlEndpoint{repo: repo}
}

// Answer takes as input a NodeShape, and runs its Sparql query against the endpoint
func (s SparqlEndpoint) Answer(ns *Shape) Table {
	query := (*ns).ToSparql()
	fmt.Println("Query: \n", query.String())
	res, err := s.repo.Query(query.String())
	check(err)

	return GetTable(res)
}

// Answer takes as input a NodeShape, and runs its Sparql query against the endpoint
func (s SparqlEndpoint) Query(query string) Table {
	// query := ns.ToSparql()
	res, err := s.repo.Query(query)
	check(err)

	// fmt.Println("Query:  \n", query)

	return GetTable(res)
}
