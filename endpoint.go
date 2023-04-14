package main

import (
	"fmt"
	"strings"
	"time"

	"github.com/deiu/rdf2go"
	"github.com/knakk/sparql"
)

// GetTable returns from a query result a table, and a header of shape names

type Table struct {
	header  []string
	content [][]rdf2go.Term
}

func (t Table) String() string {
	var sb strings.Builder

	sb.WriteString(fmt.Sprintln(t.header))

	for i := range t.content {
		for j := range t.content[i] {
			sb.WriteString(fmt.Sprint(t.content[i][j]))
			if j <= len(t.content[i])-1 {
				sb.WriteString("\t")
			}
		}
		sb.WriteString("\n")
	}

	return sb.String()
}

func (t Table) Limit(n int) string {
	if n > len(t.content) {
		n = len(t.content)
	}
	var sb strings.Builder

	sb.WriteString(fmt.Sprintln(t.header))

	for i := range t.content[:n] {
		for j := range t.content[i] {
			sb.WriteString(fmt.Sprint(t.content[i][j]))
			if j <= len(t.content[i])-1 {
				sb.WriteString("\t")
			}
		}
		sb.WriteString("\n")
	}

	if n < len(t.content) {
		sb.WriteString(fmt.Sprint("\t\t⋮ (showing first ", n, " lines from ", len(t.content), " total) \n"))
	}

	return sb.String()
}

func GetTable(r *sparql.Results) Table {
	var resultTable [][]rdf2go.Term

	var ordering map[string]int = make(map[string]int)

	for i, s := range r.Head.Vars {
		ordering[s] = i
	}

	for _, t := range r.Solutions() {
		var tupleOrdered []rdf2go.Term = make([]rdf2go.Term, len(t))

		for k, v := range t {
			tupleOrdered[ordering[k]] = res(v.String()) // needed since range over map unsorted
		}

		resultTable = append(resultTable, tupleOrdered)
	}

	return Table{r.Head.Vars, resultTable}
}

type endpoint interface {
	Answer(ns *NodeShape) Table
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
func (s SparqlEndpoint) Answer(ns *NodeShape) Table {
	query := ns.ToSparql()
	res, err := s.repo.Query(query)
	check(err)

	return GetTable(res)
}

// Answer takes as input a NodeShape, and runs its Sparql query against the endpoint
func (s SparqlEndpoint) Query(query string) Table {
	// query := ns.ToSparql()
	res, err := s.repo.Query(query)
	check(err)

	return GetTable(res)
}
