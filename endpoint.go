package main

import (
	"errors"
	"fmt"
	"io"
	"net/http"
	"strings"
	"time"

	rdf "github.com/cem-okulmus/rdf2go-1"

	"github.com/knakk/digest"
	"github.com/knakk/sparql"
)

type endpoint interface {
	Answer(ns Shape, target []SparqlQueryFlat) Table[rdf.Term]
	Query(s SparqlQuery) Table[rdf.Term]
	QueryFlat(s SparqlQueryFlat) Table[rdf.Term]
	QueryString(s string) Table[rdf.Term]
	Insert(input *rdf.Graph, fromGraph string, additive bool) error
	Delete(input *rdf.Graph, fromGraph string) error
	ClearGraph(fromGraph string) error
	GetGraph() string
}

type SparqlEndpoint struct {
	repo           *sparql.Repo
	fromGraph      string
	debug          bool
	updateEndpoint bool
	updateAddr     string
	updateClient   *http.Client
}

// GetSparqlEndpoint creates and returns a new SparqlEndpoint connected to a SPARQL repository.
// Parameters:
//   - address: the URL of the SPARQL query endpoint
//   - updateAddr: the URL of the SPARQL update endpoint (only used if update is true)
//   - username: optional username for digest authentication
//   - password: optional password for digest authentication
//   - debug: enables debug output
//   - update: if true, enables write operations via UpdateEndpoint
//   - graph: the named graph URI to use for all queries
func GetSparqlEndpoint(address, updateAddr, username, password string, debug, update bool, graph string) *SparqlEndpoint {
	repo, err := sparql.NewRepo(address,
		sparql.DigestAuth(username, password),
		sparql.Timeout(time.Second*600),
	)
	check(err)

	var updateClient *http.Client

	if update {
		updateClient = &http.Client{
			Transport: digest.NewTransport(username, password),
			Timeout:   time.Second * 600,
		}
	}

	return &SparqlEndpoint{
		repo:           repo,
		debug:          debug,
		updateEndpoint: update,
		fromGraph:      graph,
		updateAddr:     updateAddr,
		updateClient:   updateClient,
	}
}

// GetGraph returns the named graph URI currently associated with this endpoint.
func (s *SparqlEndpoint) GetGraph() string { return s.fromGraph }

// Ping checks whether the SPARQL endpoint is reachable by issuing a minimal ASK query.
func (s *SparqlEndpoint) Ping() error {
	_, err := s.repo.Query("ASK { }")
	return err
}

// ClearGraph clears all triples from the specified named graph on the SPARQL endpoint.
// If fromGraph is empty, returns an error.
func (s *SparqlEndpoint) ClearGraph(fromGraph string) (out error) {
	if fromGraph == "" {
		out = errors.New("need to provide a graph for the Clear command")
		return out
	}

	if s.updateEndpoint {
		out = s.doUpdate(fmt.Sprintf("DROP SILENT GRAPH %s", fromGraph))
	} else {
		_, out = s.repo.Query(fmt.Sprintf("DROP SILENT GRAPH %s", fromGraph))
	}

	return out
}

// doUpdate sends a SPARQL 1.1 Update request with Content-Type:
// application/sparql-update and the update text as a raw request body,
// rather than going through sparql.Repo.Update's
// application/x-www-form-urlencoded encoding.
//
// RDF4J-based servers (confirmed against GraphDB 10.x) parse
// x-www-form-urlencoded bodies through their servlet container's form
// parameter parser, which caps the parseable body size (Tomcat's default
// maxPostSize is 2MB). Past that size the "update" parameter silently fails
// to parse and the server responds with a misleading "Unsupported MIME
// type: application/x-www-form-urlencoded" 415, even though the content
// type itself is fine. The raw-body application/sparql-update form is read
// as a plain input stream and isn't subject to that limit.
func (s *SparqlEndpoint) doUpdate(updateString string) error {
	req, err := http.NewRequest("POST", s.updateAddr, strings.NewReader(updateString))
	if err != nil {
		return err
	}
	req.Header.Set("Content-Type", "application/sparql-update")

	resp, err := s.updateClient.Do(req)
	if err != nil {
		return err
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK && resp.StatusCode != http.StatusNoContent {
		body, readErr := io.ReadAll(resp.Body)
		msg := ""
		if readErr == nil {
			msg = strings.TrimSpace(string(body))
		}
		if msg != "" {
			return fmt.Errorf("update: SPARQL request failed: %s. Response body: \n%s", resp.Status, msg)
		}
		return fmt.Errorf("update: SPARQL request failed: %s", resp.Status)
	}

	return nil
}

// Insert loads an RDF graph into the SPARQL endpoint under the specified named graph.
// If fromGraph is empty the endpoint's current graph is used.
// When additive is false the target graph is cleared first; when true existing
// triples are preserved and the new ones are simply appended.
func (s *SparqlEndpoint) Insert(input *rdf.Graph, fromGraph string, additive bool) (out error) {
	if fromGraph != "" {
		s.fromGraph = fromGraph
	}

	if !additive {
		if err := s.ClearGraph(s.fromGraph); err != nil {
			return err
		}
	}

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

	if s.debug {
		fmt.Println("INSERT String \n ", insertString)
	}

	var err error
	if s.updateEndpoint {
		err = s.doUpdate(insertString)
	} else {
		_, err = s.repo.Query(insertString)
	}

	return err
}

// Delete removes the triples in input from the specified named graph on the SPARQL endpoint.
// If fromGraph is empty the endpoint's current graph is used.
func (s *SparqlEndpoint) Delete(input *rdf.Graph, fromGraph string) (out error) {
	if fromGraph != "" {
		s.fromGraph = fromGraph
	}

	var sb strings.Builder

	for k, v := range prefixes {
		sb.WriteString("PREFIX " + k + " <" + v + ">\n")
	}

	sb.WriteString("DELETE DATA { \n")
	sb.WriteString(fmt.Sprint("GRAPH ", s.fromGraph, " { \n"))

	for triple := range input.IterTriples() {
		sb.WriteString(fmt.Sprint(triple.Subject, " ", triple.Predicate, " ", triple.Object, ". \n"))
	}

	sb.WriteString("} \n }")

	deleteString := sb.String()

	if s.debug {
		fmt.Println("DELETE String \n ", deleteString)
	}

	if s.updateEndpoint {
		out = s.doUpdate(deleteString)
	} else {
		_, out = s.repo.Query(deleteString)
	}

	return out
}

// Answer executes shape validation queries against the endpoint for a given shape.
// Queries are executed for each target expression, and results are merged together.
// Results are grouped with the first column (subject) as the key.
// Returns a grouped table with the query results.
func (s *SparqlEndpoint) Answer(ns Shape, targets []SparqlQueryFlat) Table[rdf.Term] {
	var out Table[rdf.Term]

	// repeat this for each individual target, and collect the results
	for i := range targets {
		query := ns.ToSparql(s.fromGraph, targets[i])

		if s.debug {
			fmt.Println("Answer query:  \n", query)
		}

		// fmt.Print("adding the query ", query.String())
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

// Query executes a SPARQL SELECT query against the endpoint and returns the result as a table.
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

// QueryFlat executes a flat SPARQL query (without aggregation or grouping) against the endpoint.
// Used for target expression queries that must not produce grouped results.
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

// QueryString executes an arbitrary SPARQL query string against the endpoint and returns results as a table.
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
