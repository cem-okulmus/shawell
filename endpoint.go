package main

import (
	"errors"
	"fmt"
	"sort"
	"strings"
	"time"

	rdf "github.com/cem-okulmus/rdf2go-1"

	"golang.org/x/exp/constraints"

	"github.com/knakk/sparql"
)

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

type endpoint interface {
	Answer(ns Shape, target []SparqlQueryFlat) Table[rdf.Term]
	Query(s SparqlQuery) Table[rdf.Term]
	QueryFlat(s SparqlQueryFlat) Table[rdf.Term]
	QueryString(s string) Table[rdf.Term]
	Insert(input *rdf.Graph, fromGraph string) error
	ClearGraph(fromGraph string) error
	GetGraph() string
}

type SparqlEndpoint struct {
	repo           *sparql.Repo
	repoUpdate     *sparql.Repo
	fromGraph      string
	debug          bool
	updateEndpoint bool
}

func GetSparqlEndpoint(address, updateAddr, username, password string, debug, update bool, graph string) *SparqlEndpoint {
	repo, err := sparql.NewRepo(address,
		sparql.DigestAuth(username, password),
		sparql.Timeout(time.Second*600),
	)
	check(err)

	var repoUpdate *sparql.Repo

	if update {
		repoUpdate, err = sparql.NewRepo(updateAddr,
			sparql.DigestAuth(username, password),
			sparql.Timeout(time.Second*600),
		)
		check(err)
	}

	return &SparqlEndpoint{
		repo:           repo,
		repoUpdate:     repoUpdate,
		debug:          debug,
		updateEndpoint: update,
		fromGraph:      graph,
	}
}

func (s *SparqlEndpoint) GetGraph() string { return s.fromGraph }

func (s *SparqlEndpoint) ClearGraph(fromGraph string) (out error) {
	if fromGraph == "" {
		out = errors.New("need to provide a graph for the Clear command")
		return out
	}

	if s.updateEndpoint {
		out = s.repoUpdate.Update(fmt.Sprint("CLEAR GRAPH ", fromGraph))
	} else {
		_, out = s.repo.Query(fmt.Sprint("CLEAR GRAPH ", fromGraph))
	}

	return out
}

// Insert takes as input an RDF graph, and inserts it into the Sparql Endpoint
func (s *SparqlEndpoint) Insert(input *rdf.Graph, fromGraph string) (out error) {
	// extract graph name (this assumes we only use this for W3C test suites w/ fixed format)

	if fromGraph != "" {
		s.fromGraph = fromGraph
	}

	// clear graph first

	// fmt.Println("Attempting clear: ", s.fromGraph)
	err := s.ClearGraph(s.fromGraph)
	if err != nil {
		return err
	}
	// fmt.Println("Passed Clear")

	var sb strings.Builder

	for k, v := range prefixes {
		sb.WriteString("PREFIX " + k + " <" + v + ">\n")
	}

	sb.WriteString("INSERT  DATA { \n")

	sb.WriteString(fmt.Sprint("GRAPH ", s.fromGraph, " { \n"))

	for triple := range input.IterTriples() {
		sb.WriteString(fmt.Sprint(triple.Subject, " ", triple.Predicate, " ", triple.Object, ". \n"))
	}

	sb.WriteString("} \n }")

	insertString := sb.String()

	// fmt.Println(de)
	if s.debug {
		fmt.Println("INSERT String \n ", insertString)
	}

	if s.updateEndpoint {
		err = s.repoUpdate.Update(insertString)
	} else {
		_, err = s.repo.Query(insertString)
	}

	if err != nil {
		out = err
	} else {
		out = nil
	}

	return out
}

// Answer takes as input a NodeShape, and runs its Sparql query against the endpoint
// In case of multiple targets, each target produces its own query, and results are concatenated
func (s *SparqlEndpoint) Answer(ns Shape, targets []SparqlQueryFlat) Table[rdf.Term] {
	var out Table[rdf.Term]

	// repeat this for each individual target, and collect the results
	for i := range targets {
		query := ns.ToSparql(s.fromGraph, targets[i])

		if s.debug {
			fmt.Println("Answer query:  \n", query)
		}

		// fmt.Sprint("adding the query ", query.String())
		QueryStore = append(QueryStore, query.String())
		res, err := s.repo.Query(query.String())
		if err != nil {
			fmt.Println("Query in question:\n ", query)
			panic(err)
		}

		tmp := GetTable(res)

		if s.debug {
			fmt.Println("Output : \n, ", tmp)
		}

		if out == nil {
			out = tmp
		} else {
			err := out.Merge(tmp)
			check(err)
		}
	}

	tmp := GetGroupedTable(out)
	if s.debug {
		fmt.Println("Output Final : \n, ", tmp)
	}

	return tmp
}

func (s *SparqlEndpoint) Query(query SparqlQuery) Table[rdf.Term] {
	// query := ns.ToSparql()
	res, err := s.repo.Query(query.String())
	if err != nil {
		fmt.Println("Query in question:\n ", query.String())
		panic(err)
	}

	if s.debug {
		fmt.Println("Query:  \n", query)
	}

	out := GetTable(res)

	if s.debug {
		fmt.Println("Output: \n, ", out)
	}

	// out.query = query
	return out
}

func (s *SparqlEndpoint) QueryFlat(query SparqlQueryFlat) Table[rdf.Term] {
	// query := ns.ToSparql()
	res, err := s.repo.Query(query.String())
	if err != nil {
		fmt.Println("Query in question:\n ", query.String())
		panic(err)
	}
	if s.debug {
		fmt.Println("QueryFlat:  \n", query)
	}

	out := GetTable(res)

	if s.debug {
		fmt.Println("Output: \n, ", out)
	}

	// out.query = query
	return out
}

func (s *SparqlEndpoint) QueryString(query string) Table[rdf.Term] {
	// query := ns.ToSparql()
	res, err := s.repo.Query(query)
	if err != nil {
		fmt.Println("Query in question:\n ", query)
		panic(err)
	}
	out := GetTable(res)

	if s.debug {
		fmt.Println("Output: \n, ", out)
	}

	return out
}
