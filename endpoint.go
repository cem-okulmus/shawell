package main

import (
	"errors"
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
	header  []string
	content [][]rdf.Term
	cache   []string
	merged  bool // indicates the table generate by merger, thus one query does not capture contents
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

func (t *Table) Merge(other Table) error {
	// check if the two tables share the same header

	for i := range t.header {
		if t.header[i] != other.header[i] {
			return errors.New("Incompatible tables to merge")
		}
	}

	t.content = append(t.content, other.content...)
	t.merged = true
	return nil
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
	Answer(ns *Shape, target []SparqlQueryFlat) Table
	Query(s SparqlQuery) Table
	QueryFlat(s SparqlQueryFlat) Table
	QueryAsk(s string) bool
	Insert(input *rdf.Graph) error
}

type SparqlEndpoint struct {
	repo           *sparql.Repo
	repoUpdate     *sparql.Repo
	fromGraph      string
	debug          bool
	updateEndpoint bool
}

func GetSparqlEndpoint(address, updateAddr, username, password string, debug, update bool, graph string) SparqlEndpoint {
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

	return SparqlEndpoint{
		repo:           repo,
		repoUpdate:     repoUpdate,
		debug:          debug,
		updateEndpoint: update,
		fromGraph:      graph,
	}
}

// Insert takes as input an RDF graph, and inserts it into the Sparql Endpoint
func (s SparqlEndpoint) Insert(input *rdf.Graph) (out error) {
	// extract graph name (this assumes we only use this for W3C test suites w/ fixed format)

	_sht := prefixes["sht:"] // living dangerously

	found := input.One(nil, res(_rdf+"type"), res(_sht+"Validate"))

	if found == nil {
		fmt.Println("Prefixes: ", prefixes)
		return errors.New("not a valid test suite file")
	}

	graphName := found.Subject

	// clear graph first

	var err error
	if s.updateEndpoint {
		err = s.repoUpdate.Update(fmt.Sprint("CLEAR GRAPH ", graphName.String()))
	} else {
		_, err = s.repo.Query(fmt.Sprint("CLEAR GRAPH ", graphName.String()))
	}

	if err != nil {
		return err
	}

	var sb strings.Builder

	for k, v := range prefixes {
		sb.WriteString("PREFIX " + k + " <" + v + ">\n")
	}

	sb.WriteString("INSERT  DATA { \n")

	sb.WriteString(fmt.Sprint("GRAPH ", graphName.String(), " { \n"))

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
func (s SparqlEndpoint) Answer(ns *Shape, targets []SparqlQueryFlat) Table {
	var out *Table = nil

	// repeat this for each individual target, and collect the results
	for i := range targets {
		query := (*ns).ToSparql(targets[i])

		if s.debug {
			fmt.Println("Answer query:  \n", query)
		}

		res, err := s.repo.Query(query.String())
		if err != nil {
			fmt.Println("Query in question:\n ", query)
			panic(err)
		}

		if s.debug {
			fmt.Println("Output: \n, ", out)
		}

		tmp := GetTable(res)
		if out == nil {
			out = &tmp
		} else {
			out.Merge(tmp)
		}
	}

	return *out
}

func (s SparqlEndpoint) Query(query SparqlQuery) Table {
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

func (s SparqlEndpoint) QueryFlat(query SparqlQueryFlat) Table {
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
