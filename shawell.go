// shawell - SHAcl (with) WELLfounded (semantics)
// A research prototype for validating SHACL documents under well-founded
// semantics.

package main

import (
	"fmt"
	"os"
	"strings"

	"github.com/deiu/rdf2go"
)

func check(e error) {
	if e != nil {
		panic(e)
	}
}

func res(s string) rdf2go.Term {
	return rdf2go.NewResource(s)
}

// making it easier to define proper terms
var (
	sh   = "http://www.w3.org/ns/shacl#"
	dbo  = "https://dbpedia.org/ontology/"
	dbr  = "https://dbpedia.org/resource/"
	rdfs = "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
)

func abbr(in string) string {
	in = strings.ReplaceAll(in, sh, "sh:")
	in = strings.ReplaceAll(in, dbo, "dbo:")
	in = strings.ReplaceAll(in, dbr, "dbr:")
	in = strings.ReplaceAll(in, rdfs, "rdfs:")

	return in
}

var ResA = res(rdfs + "type")

// Done:
//  *  get a better understanding of SHACL documents
//      - how to read complex property elements
//      -
//      -> Transform the weird ad-hoc constraints in resources into "proper" SHACL
//  *  Use rdf2go to parse (full) SHACL documents
//      - Initially only support NodeShapes
//      - Supported Features
//			* sh:property constraints
//			  + sh:path
//            + support for sh:inversePath
//			  + sh:node (with shape or class as value)
//            + sh:minCount, sh:maxCount
//      - sh:and  & sh:not support
//      - sh:targetClass & sh:targetObjectOf support
//

// TODO:
// * consider actual benchmarks to cover, before developing further towards integration with dlv
// * implement rewriting of conditional answers into logic programs
// * implement integration with dlv:
// 		- being able to send programs to dlv
//		- being able to parse output from dlv back to unconditional answers
// * consider if target extraction could not be merged into DLV program, to directly get validation
// report of sorts

func main() {
	// Set a base URI
	baseUri := "http://dbpedia.org/ontology"

	carwheel, err := os.Open("resources/carwheel.ttl")
	check(err)

	g := rdf2go.NewGraph(baseUri)

	g.Parse(carwheel, "text/turtle")

	// triple := g.All(nil, res(dbo+"part"), nil)

	// fmt.Println("here are all triples with 'hasPart' as the role:", len(triple))
	// fmt.Println("Here is a turtle RDF graph: ", g.Len())
	shaclDoc, err := os.Open("resources/carwheel_constraints_nonrecursive.ttl")
	check(err)

	g2 := rdf2go.NewGraph(sh)
	g2.Parse(shaclDoc, "text/turtle")
	// fmt.Println("Here is a turtle RDF graph: ", abbr(g2.String()), g2.Len())

	var parsedDoc ShaclDocument

	found, parsedDoc := GetShaclDocument(g2)

	fmt.Println("Found a ShaclDoc: ", found)
	fmt.Println("The parsed Shacl Doc", parsedDoc.String())

	endpoint := GetSparqlEndpoint("http://localhost:3030/Cartwheel/", "", "")

	// var results []Table

	// for _, n := range parsedDoc.nodeShapes[:1] {
	// 	results = append(results, endpoint.Answer(n))
	// }

	// for i := range results {
	// 	fmt.Println("Result table of query ", i)

	// 	fmt.Println(results[i].LimitString(5))
	// }

	parsedDoc.AllCondAnswers(endpoint)

	fmt.Println("CondAnswers for ", sh+"CarShape", "  : ", parsedDoc.condAnswers[sh+"CarShape"].Limit(5))
	fmt.Println("CondAnswers for ", sh+"WheelShape", "  : ", parsedDoc.condAnswers[sh+"WheelShape"].Limit(5))

	fmt.Println("UncondAnswers for CarShape: ", parsedDoc.UnwindAnswer(sh+"CarShape").Limit(10))
	fmt.Println("UncondAnswers for WheelShape: ", parsedDoc.UnwindAnswer(sh+"WheelShape").Limit(13))

	fmt.Println("Tarets of CarShape ", parsedDoc.GetTargets(sh+"CarShape", endpoint).Limit(5))
	fmt.Println("Tarets of WheelShape ", parsedDoc.GetTargets(sh+"WheelShape", endpoint).Limit(5))
}
