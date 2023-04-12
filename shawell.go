// shawell - SHAcl (with) WELLfounded (semantics)
// A research prototype for validating SHACL documents under well-founded
// semantics.

package main

import (
	"fmt"
	"os"
	// "strconv"

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
	sh   = "https://www.w3.org/ns/shacl#"
	dbo  = "https://dbpedia.org/ontology/"
	dbr  = "https://dbpedia.org/resource/"
	rdfs = "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
)

var ResA = res(rdfs + "type")

// Done:
//  *  get a better understanding of SHACL documents
//      - how to read complex property elements
//      -
//      -> Transform the weird ad-hoc constraints in resources into "proper" SHACL
//

// TODO:
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

func main() {
	// Set a base URI
	baseUri := "http://dbpedia.org/ontology"

	carwheel, err := os.Open("resources/carwheel.ttl")
	check(err)

	g := rdf2go.NewGraph(baseUri)

	g.Parse(carwheel, "text/turtle")

	fmt.Println("Hello world!")

	triple := g.All(nil, res(dbo+"part"), nil)

	fmt.Println("here are all triples with 'hasPart' as the role:", len(triple))
	fmt.Println("Here is a turtle RDF graph: ", g.Len())
	shaclDoc, err := os.Open("resources/carwheel_constraints.ttl")
	check(err)

	g2 := rdf2go.NewGraph(sh)
	g2.Parse(shaclDoc, "text/turtle")
	fmt.Println("Here is a turtle RDF graph: ", g2, g2.Len())

	var parsedDoc ShaclDocument

	found, parsedDoc := GetShaclDocument(g2)

	fmt.Println("Found a ShaclDoc: ", found)
	fmt.Println("The parsed Shacl Doc", parsedDoc)
	fmt.Println("\n \n As a Sparql query ", parsedDoc.nodeShapes[0].ToSparql())
}
