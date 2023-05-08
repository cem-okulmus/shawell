// shawell - SHAcl (with) WELLfounded (semantics)
// A research prototype for validating SHACL documents under well-founded
// semantics.

package main

import (
	"bufio"
	"flag"
	"fmt"
	"io"
	"os"
	"regexp"
	"strings"

	rdf "github.com/deiu/rdf2go"
)

func check(e error) {
	if e != nil {
		panic(e)
	}
}

func res(s string) rdf.Term {
	return rdf.NewResource(s)
}

var prefixes map[string]string = make(map[string]string)

// making it easier to define proper terms
var (
	_sh   = "http://www.w3.org/ns/shacl#"
	_dbo  = "https://dbpedia.org/ontology/"
	_dbr  = "https://dbpedia.org/resource/"
	_rdf  = "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
	_rdfs = "http://www.w3.org/2000/01/rdf-schema#"
)

func GetNameSpace(file *os.File) {
	// call the Seek method first
	_, err := file.Seek(0, io.SeekStart)
	check(err)

	scanner := bufio.NewScanner(file)
	validID := regexp.MustCompile(`<.*?>`)

	// iterate over each line in the file
	for scanner.Scan() {
		line := scanner.Text()
		ps := "@prefix "
		if strings.HasPrefix(line, ps) {
			abbr, _ := strings.CutPrefix(line, ps)
			getStart := 0
			abbrOut := ""
			for i, c := range abbr {
				if c == ':' {
					getStart = i
					break
				}
			}
			abbrOut = abbr[:getStart+1]
			fullPath := validID.FindString(line)
			_, ok := prefixes[abbrOut]
			if !ok {
				prefixes[abbrOut] = fullPath[1 : len(fullPath)-1]
			}
		}
	}
}

func abbr(in string) string {
	for k, v := range prefixes {
		in = strings.ReplaceAll(in, ">", "")
		in = strings.ReplaceAll(in, "<", "")
		in = strings.ReplaceAll(in, v, k)
	}

	// in = strings.ReplaceAll(in, _dbo, "dbo:")
	// in = strings.ReplaceAll(in, _dbr, "dbr:")
	// in = strings.ReplaceAll(in, _rdf, "rdf:")

	return in
}

func removeAbbr(in string) string {
	for _, v := range prefixes {
		new, found := strings.CutPrefix(in, v)
		if found {
			return new
		}
	}

	// in = strings.ReplaceAll(in, _dbo, "dbo:")
	// in = strings.ReplaceAll(in, _dbr, "dbr:")
	// in = strings.ReplaceAll(in, _rdf, "rdf:")

	return in
}

func abbrAll(in []string) []string {
	var out []string

	for i := range in {
		out = append(out, abbr(in[i]))
	}

	return out
}

var ResA = res(_rdf + "type")

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
// * support more of basic SHACL
//   - (if it comes in tests) explicit property shapes
//   - sh:name
//   - sh:datatype
//   - sh:pattern (reg expressions sigh)
//   - sh:nodeKind
//   - sh:alternativePath
//   - sh:zeroOrMorePath (plus all these related ones)
//   - sh:in
//   - sh:equals, disjoint, lessThan, lessThanOrEquals
//   - sh:minLength, sh:maxLength, sh:languageIn, sh:uniqueLang
//   - sh:minExclusive, sh:maxExclusive, sh:minInclusive, sh:maxInclusive//

// TODO:
// * implement rewriting of conditional answers into logic programs
// * implement integration with dlv:
// 		- being able to send programs to dlv
//		- being able to parse output from dlv back to unconditional answers
// * consider if target extraction could not be merged into DLV program, to directly get validation
// report of sorts
// * support more of basic SHACL
//   - sh:qualifiedValue (min + max)
//   - sh:ignoredProperties (for sh:closed)
//   - sh:closed
//   - sh:xone
//   - sh:or

// LOW PRIORITY TODO:
//  * Produce proper validation reports in RDF
//   - support severity
//   - result message
//   - the various properties (value, source, path, focus, constraint)
//  * deactivating a shape (should be easy)

func main() {
	// ==============================================
	// Command-Line Argument Parsing

	flagSet := flag.NewFlagSet("shawell", flag.ExitOnError)

	// input flags
	endpointAddress := flagSet.String("endpoint", "", "The URL to a SPARQL endpoint.")
	shaclDocPath := flagSet.String("shaclDoc", "", "The file path to a SHACL document.")

	flagSet.Parse(os.Args[1:])

	if *endpointAddress == "" || *shaclDocPath == "" {
		flagSet.Usage()
		os.Exit(-1)
	}

	// END Command-Line Argument Parsing
	// ==============================================

	shaclDoc, err := os.Open(*shaclDocPath)
	check(err)

	g2 := rdf.NewGraph(_sh)
	g2.Parse(shaclDoc, "text/turtle")

	GetNameSpace(shaclDoc)

	var parsedDoc ShaclDocument = GetShaclDocument(g2)
	fmt.Println("The parsed Shacl Doc", parsedDoc.String())

	// if len(parsedDoc.nodeShapes) > 0 {
	// 	fmt.Println("Chosen Shape: ", parsedDoc.nodeShapes[0])

	// 	fmt.Println("\n Sparql Query:")
	// 	fmt.Print("\n\n")

	// 	query := parsedDoc.nodeShapes[0].ToSparql()

	// 	fmt.Println(query.String())
	// }

	endpoint := GetSparqlEndpoint(*endpointAddress, "", "")

	// var results []Table

	// for _, n := range parsedDoc.nodeShapes[:1] {
	// 	results = append(results, endpoint.Answer(n))
	// }

	// for i := range results {
	// 	fmt.Println("Result table of query ", i)

	// 	fmt.Println(results[i].LimitString(5))
	// }

	parsedDoc.AllCondAnswers(endpoint)

	fmt.Println("CondAnswers for ",
		_sh+"WheelShape", "  : ", parsedDoc.condAnswers[_sh+"WheelShape"].Limit(7))

	fmt.Println("Logic Program for ",
		_sh+"WheelShape", "  : ", parsedDoc.ToLP(_sh+"WheelShape"))

	// fmt.Println("CondAnswers for ",
	// 	_sh+"Car2Shape", "  : ", parsedDoc.condAnswers[_sh+"Car2Shape"].Limit(5))
	// fmt.Println("CondAnswers for ",
	// 	_sh+"CarShape", "  : ", parsedDoc.condAnswers[_sh+"CarShape"].Limit(5))

	// fmt.Println("Query for Car1Shape: \n", parsedDoc.shapeNames[_sh+"Car1Shape"].ToSparql())
	// fmt.Println("CondAnswers for ", sh+"WheelShape", "  : ",
	// 	parsedDoc.condAnswers[sh+"WheelShape"].Limit(5))

	// fmt.Println("UncondAnswers for CarShape: ",
	// 	parsedDoc.UnwindAnswer(sh+"CarShape").Limit(10))
	// fmt.Println("UncondAnswers for WheelShape: ",
	// 	parsedDoc.UnwindAnswer(sh+"WheelShape").Limit(13))

	// fmt.Println("Query for CarShape\n ", parsedDoc.shapeNames[sh+"Car2Shape"].ToSparql())

	// fmt.Println("Targets of CarShape ",
	// 	parsedDoc.GetTargets(sh+"CarShape", endpoint).Limit(5))
	// fmt.Println("Targets of WheelShape ",
	// 	parsedDoc.GetTargets(sh+"WheelShape", endpoint).Limit(5))

	// fmt.Println("Invalid Targets of CarShape ",
	// 	parsedDoc.InvalidTargets(sh+"CarShape", endpoint).Limit(5))

	res, invalidTargets := parsedDoc.Validate(endpoint)

	fmt.Println("Shacl Document valid: ", res)

	// // print all shapes
	// for k, v := range parsedDoc.uncondAnswers {

	// 	fmt.Println("Shape ", k)
	// 	fmt.Println(v.Limit(5))

	// }

	for k, v := range invalidTargets {
		fmt.Println("For node shape: ", k, " -- Invalid Targets: \n\n ", v.Limit(5))

		// fmt.Println("For node shape: ", k, " -- Explanations: ")
		// for _, s := range expMap[k][:5] {
		// 	fmt.Println(s)
		// }
	}

	// 	// var nodes []string = v.GetColumn(0)

	// 	// targets, explanation := parsedDoc.InvalidTargetsWithExplanation(name, endpoint)

	// 	// if k != sh+"WheelShape" { // extend Get Failure Witness to give proper answers based on dep
	// 	// 	for _, n := range nodes {
	// 	// 		fmt.Println(parsedDoc.FindReferentialFailureWitness(k, n))
	// 	// 	}
	// 	// } else {
	// 	// 	fmt.Print("Witness query on targets: \n", endpoint.Query(query).Limit(10))
	// 	// }

	// 	// fmt.Println("Witness query on targets:\n\n ", query)
	// }

	// nodes := []string{"<https://dbpedia.org/resource/V41>", "<https://dbpedia.org/resource/V19>"}
	// fmt.Println("Failure Witness WheelShape:\n", parsedDoc.shapeNames[sh+"WheelShape"].WitnessQuery(nodes))
}
