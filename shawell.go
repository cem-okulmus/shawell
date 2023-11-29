// shawell - SHAcl (with) WELLfounded (semantics)
// A research prototype for validating SHACL documents under well-founded
// semantics.

package main

import (
	"bufio"
	"flag"
	"fmt"
	"io"
	"log"
	"os"
	"regexp"
	"strings"

	rdf "github.com/cem-okulmus/MyRDF2Go"
)

var theCount int64 // lord of all things counting

func getCount() int64 {
	theCount++
	return theCount
}

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
	_rdf  = "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
	_rdfs = "http://www.w3.org/2000/01/rdf-schema#"
	_xsd  = "http://www.w3.org/2001/XMLSchema#"
)

func GetNameSpace(file *os.File) {
	// TODO: make this less crazy and ugly

	// fix standard prefixes
	prefixes["sh:"] = _sh
	prefixes["rdf:"] = _rdf
	prefixes["rdfs:"] = _rdfs

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
		in = strings.ReplaceAll(in, " > ", "🐭️")
		in = strings.ReplaceAll(in, " < ", "🧀️")
		in = strings.ReplaceAll(in, ">=", "🤔️")
		in = strings.ReplaceAll(in, "<=", "😀️")
		in = strings.ReplaceAll(in, "_:", "")
		in = strings.ReplaceAll(in, ">", "")
		in = strings.ReplaceAll(in, "<", "")
		in = strings.ReplaceAll(in, "🤔️", ">=")
		in = strings.ReplaceAll(in, "😀️", "<=")
		in = strings.ReplaceAll(in, "🐭️", " > ")
		in = strings.ReplaceAll(in, "🧀️", " < ")
		in = strings.ReplaceAll(in, v, k)
	}

	return in
}

func removeAbbr(in string) string {
	for _, v := range prefixes {
		in = strings.ReplaceAll(in, v, "")
	}
	return in
}

func abbrAll(in []string) []string {
	var out []string

	for i := range in {
		out = append(out, abbr(in[i]))
	}

	return out
}

func removeAbbrAll(in []string) []string {
	var out []string

	for i := range in {
		out = append(out, removeAbbr(in[i]))
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
//   - sh:ignoredProperties (for sh:closed)
//   - sh:closed
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
// * implement rewriting of conditional answers into logic programs
// * implement integration with dlv:
// 		- being able to send programs to dlv
//		- being able to parse output from dlv back to unconditional answers
// * Implement the restriction of Sparql queries to target nodes and indirect target nodes
//    - incorporate the implicit target semantics
//    - introduce indirect targets as a data structure
//    - extraction of indirect targets from a Table
// * Test out recursion, and compare behaviour with other solvers
//   - recreate the (s <- s; s <- not not s) case in shacl and check the behaviour
//   - find a list of validators out there supporting recursion
// * Implement the restriction of Sparql queries to target nodes and indirect target nodes
//    - support for recursion, and iterated indirect target passing
// * support more of basic SHACL
//   - sh:qualifiedValue (min + max)
//   - sh:xone
//   - sh:or
//  * support of deactivating a shape (should be easy)
// * Getting solver into shape for JELIA
//   - test maxCount when empty value set (use !BOUND || )
//  * Produce proper validation reports in RDF
//   - support severity
//   - result message
//   - the various properties (value, source, path, focus, constraint)

func main() {
	// ==============================================
	// Command-Line Argument Parsing

	flagSet := flag.NewFlagSet("shawell", flag.ExitOnError)

	// input flags
	endpointAddress := flagSet.String("endpoint", "", "The URL to a SPARQL endpoint.")
	endpointUpdateAddress := flagSet.String("endpointUpdate", "",
		"The URL to a SPARQL endpoint used for updating the data.")
	shaclDocPath := flagSet.String("shaclDoc", "", "The file path to a SHACL document.")
	dlvLoc := flagSet.String("dlv", "bin/dlv",
		"The location of the DLV binary used to evaluate recursive SHACL.")
	dataIncluded := flagSet.Bool("dataIncluded", false,
		"Set this to true if the SHACL document also contains the data to be checked.")
	username := flagSet.String("user", "", "The username needed to access endpoint.")
	password := flagSet.String("password", "", "The password needed to access endpoint.")
	debug := flagSet.Bool("debug", false, "Activacting debugging features.")

	usingUpdateEndpoint := false

	flagSet.Parse(os.Args[1:])

	if *endpointAddress == "" || *shaclDocPath == "" {
		flagSet.Usage()
		os.Exit(-1)
	}

	if *endpointUpdateAddress != "" {
		usingUpdateEndpoint = true // using a system like GraphDB that expects different endpoints
	}

	// END Command-Line Argument Parsing
	// ==============================================

	// set DLV
	dlv = *dlvLoc

	shaclDoc, err := os.Open(*shaclDocPath)
	check(err)

	g2 := rdf.NewGraph(_sh)

	err = g2.Parse(shaclDoc, "text/turtle")
	check(err)

	// fmt.Println("Parsed Graph: ", g2)

	endpoint := GetSparqlEndpoint(
		*endpointAddress,
		*endpointUpdateAddress,
		*username,
		*password,
		*debug,
		usingUpdateEndpoint,
		"",
	)

	GetNameSpace(shaclDoc)

	var VR *ValidationReport

	var graphName string

	// check if data needs to be inserted into Endpoint
	if *dataIncluded {

		VR, err = ExtractValidationReport(g2)
		check(err)

		// fmt.Println("Extracted VR\n", VR)

		res := endpoint.Insert(g2, VR.testName.String())
		check(res)
		graphName = VR.testName.String()
	}

	var parsedDoc ShaclDocument = GetShaclDocument(g2, graphName, endpoint)
	fmt.Println("The parsed Shacl Doc", parsedDoc.String())

	parsedDoc.AllCondAnswers(endpoint)

	// for k, v := range parsedDoc.condAnswers {
	// 	fmt.Println("TABLE: ", k)
	// 	fmt.Println(v.Limit(5))
	// }

	var res bool
	var invalidTargets map[string]Table[rdf.Term]

	if parsedDoc.IsRecursive() {
		fmt.Println("Recursive document parsed, tranforming to LP and sending off to DLV.")

		lp := parsedDoc.GetAllLPs()
		// fmt.Println("Get LP for document: ", lp)
		lpTables := lp.Answer()

		// fmt.Println("Answer from DLV: ")
		// for i := range lpTables {
		// 	fmt.Println(lpTables[i].Limit(5))
		// }
		res, invalidTargets = parsedDoc.ValidateLP(lpTables, endpoint)

	} else {
		res, invalidTargets = parsedDoc.Validate(endpoint)
	}

	for _, v := range invalidTargets {
		if v.Len() > 0 {
			fmt.Println(" Found a shape with invalid targets: \n", v)
		}
	}

	fmt.Println("----------------------------------")
	fmt.Println("RESULT: --------------------------")
	fmt.Println("Shacl Document valid: ", res)
	fmt.Println("----------------------------------")

	// Producing a Validation Repot in case of failure

	if VR != nil {
		// fmt.Println("ValidationResult in XML form: ")

		var reports []ValidationResult

		allValid := true

		for _, v := range parsedDoc.shapeNames {
			// var reportsFromShape []ValidationResult

			switch t := v.(type) {
			case *NodeShape:
				if t.deactivated {
					continue
				}
				valid, reportsFromShape := parsedDoc.GetValidationReport(t, endpoint)
				if !valid {
					allValid = false
				}
				if !valid && len(reportsFromShape) == 0 {
					log.Panic("Reporting not valid for NodeSHape ", t.IRI, " but no reports returned!")
				}

				reports = append(reports, reportsFromShape...)
			case *PropertyShape:
				if t.shape.deactivated {
					continue
				}
				valid, reportsFromShape := parsedDoc.GetValidationReportProperty(t, endpoint, &[]TargetExpression{}, "")
				if !valid {
					allValid = false
				}

				if !valid && len(reportsFromShape) == 0 {
					log.Panic("Reporting not valid for PropertyShape ", t.name, " but no reports returned!")
				}

				reports = append(reports, reportsFromShape...)
			}
		}

		VR.results = reports
		VR.result = res

		if allValid != res {

			fmt.Println("Number of reports: ", len(reports))

			fmt.Println("VALIDATION REPORT: \n", VR)
			log.Panicln("Reported shacl as Invalid, but no ValidationResult produced! ", allValid, res)
		}

		fmt.Println("VALIDATION REPORT: \n", VR)
	}

	// Clean up the named graph afterwards
	if *dataIncluded {
		endpoint.ClearGraph(VR.testName.String())
	}

	// for k, v := range invalidTargets {
	// 	fmt.Println("For node shape: ", k, " -- Invalid Targets: \n\n ", v.Limit(100))
	// }
}
