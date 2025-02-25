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
	"net/url"
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"text/tabwriter"
	"time"

	"github.com/fatih/color"

	rdf "github.com/cem-okulmus/rdf2go-1"
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

var activeDoc *ShaclDocument

func abbr(in string) string {
	for k, v := range prefixes {

		in = strings.ReplaceAll(in, " <> ", "👨‍🍳️")
		in = strings.ReplaceAll(in, " > ", "🐭️")
		in = strings.ReplaceAll(in, " < ", "🧀️")
		in = strings.ReplaceAll(in, ">=", "🤔️")
		in = strings.ReplaceAll(in, "<=", "😀️")
		// in = strings.ReplaceAll(in, "_:", "")
		in = strings.ReplaceAll(in, ">", "")
		in = strings.ReplaceAll(in, "<", "")
		in = strings.ReplaceAll(in, "🤔️", ">=")
		in = strings.ReplaceAll(in, "😀️", "<=")
		in = strings.ReplaceAll(in, "🐭️", " > ")
		in = strings.ReplaceAll(in, "🧀️", " < ")
		in = strings.ReplaceAll(in, "👨‍🍳️", " <> ")
		in = strings.ReplaceAll(in, v, k)
	}

	if activeDoc != nil {
		for name, shape := range activeDoc.shapeNames {
			in = strings.ReplaceAll(in, shape.GetQualName(), name)
		}
	}

	return in
}

func removeAbbr(in string) string {
	for _, v := range prefixes {
		in = strings.ReplaceAll(in, v, "")
	}
	return in
}

func addAbbr() string {
	var sb strings.Builder

	for k, v := range prefixes {
		sb.WriteString(fmt.Sprint("@prefix ", k, " <", v, "> .\n"))
	}
	sb.WriteString("\n")
	return sb.String()
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

type timeComposer struct {
	times []labelTime
}

func (t timeComposer) String() string {
	var sb strings.Builder
	const padding = 4
	w := tabwriter.NewWriter(&sb, 0, 0, padding, ' ', tabwriter.TabIndent)
	for _, time := range t.times {
		fmt.Fprint(w, time.String(), "\n")
	}
	err := w.Flush()
	check(err)
	return sb.String()
}

type labelTime struct {
	time  float64
	label string
}

func (l labelTime) String() string {
	return fmt.Sprintf("%s \t: %.5f ms", l.label, l.time)
}

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

var QueryStore []string

// the main validation function, extracted here to be used for easy testing
func answerShacl(ep *SparqlEndpoint, parsedDoc ShaclDocument, dataIncluded *bool, debug,
	omitVR bool, vrOutFile *os.File, silent bool, forceLP bool, onlyLP bool, onlyQueries bool,
) *ValidationReport {
	// if onlyLP || onlyQueries {
	// 	silent = true
	// }
	if !debug {
		log.SetOutput(io.Discard)
	} else {
		log.SetOutput(os.Stderr)
	}

	var c timeComposer
	if !silent {
		fmt.Println("Checking conditional answers ... ")
	}

	start := time.Now()
	parsedDoc.AllCondAnswers(ep)
	d := time.Since(start)
	msec := d.Seconds() * float64(time.Second/time.Millisecond)
	c.times = append(c.times, labelTime{time: msec, label: "Conditional Table computation"})
	if !silent {
		fmt.Println("All conditinal answers found.")
	}

	// for k, v := range parsedDoc.condAnswers {
	// 	fmt.Println("TABLE: ", k)
	// 	fmt.Println(v.Limit(5))
	// }

	if onlyQueries {
		fmt.Println("The produced SPAQRL queries:  \n\n")

		for _, query := range QueryStore {
			fmt.Println(abbr(query))
		}

		return nil

	}



	var res bool
	var invalidTargets map[string]Table[rdf.Term]
	var lp program
	var lpTables []Table[rdf.Term]

	if parsedDoc.IsRecursive() || forceLP {
		if !silent {
			fmt.Println("Recursive document parsed, tranforming to LP and sending off to DLV.")
		}
		renameMap = make(map[string]string)
		reverseMap = make(map[string]string)
		start := time.Now()
		lp = parsedDoc.GetAllLPs()
		d := time.Since(start)
		msec := d.Seconds() * float64(time.Second/time.Millisecond)
		c.times = append(c.times, labelTime{time: msec, label: "Logic Program generation"})

		if debug || onlyLP {
			fmt.Println("The produced Logic Program:  \n\n")
			fmt.Println(abbr(lp.String()))
			if onlyLP {
				return nil
			}
		}

		start = time.Now()
		lpTables = lp.Answer(debug)
		d = time.Since(start)
		msec = d.Seconds() * float64(time.Second/time.Millisecond)
		c.times = append(c.times, labelTime{time: msec, label: "DLV solving"})

		err := parsedDoc.AdoptLPAnswers(lpTables)
		check(err)

		if debug {
			fmt.Println("Answer from DLV: ")
			for i := range lpTables {
				fmt.Println(lpTables[i].Limit(5))
			}
		}

		start = time.Now()
		res, invalidTargets = parsedDoc.ValidateLP(lpTables, ep)
		d = time.Since(start)
		msec = d.Seconds() * float64(time.Second/time.Millisecond)
		c.times = append(c.times, labelTime{time: msec, label: "Extracing answers from DLV"})
	} else {
		start := time.Now()
		res, invalidTargets = parsedDoc.Validate(ep)
		d := time.Since(start)
		msec := d.Seconds() * float64(time.Second/time.Millisecond)
		c.times = append(c.times, labelTime{time: msec, label: "Unwinding acyclic cond. tables"})
	}

	if !silent {
		for _, v := range invalidTargets {
			if v.Len() > 0 {
				fmt.Println("Found a shape with invalid targets: \n", v.Limit(20))
			}
		}
	}

	green := color.New(color.FgGreen)
	red := color.New(color.FgRed)

	if !silent {
		fmt.Println("----------------------------------")
		fmt.Println("RESULT: --------------------------")

		if res {
			fmt.Println("Shacl Document valid: ", green.Sprint(res))
		} else {
			fmt.Println("Shacl Document valid: ", red.Sprint(res))
		}

		fmt.Println("----------------------------------")
	}
	// Producing a Validation Repot in case of failure

	// fmt.Println("ValidationResult in XML form: ")

	var actual *ValidationReport
	var reports []ValidationResult

	allValid := true

	if !omitVR {
		actual = &ValidationReport{}

		start = time.Now()
		for _, v := range parsedDoc.shapeNames {
			// var reportsFromShape []ValidationResult

			switch t := v.(type) {
			case *NodeShape:
				if t.deactivated {
					continue
				}
				// fmt.Println("Computing VRs for shape ", t.GetIRI())
				valid, reportsOfShape := parsedDoc.GetValidationReport(t, ep)
				if !valid {
					allValid = false
				}
				if !valid && len(reportsOfShape) == 0 {
					log.Panic("Reporting not valid for NodeSHape ", t.IRI,
						" but no reports returned!")
				}

				reports = append(reports, reportsOfShape...)
			case *PropertyShape:
				if t.shape.deactivated {
					continue
				}
				// fmt.Println("Computing VRs for shape ", t.GetIRI())
				valid, repsOfShape := parsedDoc.GetVRProperty(t, ep, nil, "")
				if !valid {
					allValid = false
				}

				if !valid && len(repsOfShape) == 0 {
					log.Panic("Reporting not valid for PropertyShape ", t.name,
						" but no reports returned!")
				}

				reports = append(reports, repsOfShape...)
			}
		}
		// reports = removeDuplicateVR(reports)
		d = time.Since(start)
		msec = d.Seconds() * float64(time.Second/time.Millisecond)
		c.times = append(c.times, labelTime{time: msec, label: "Validation Report creation"})

		actual.results = reports
		actual.conforms = res
	}

	if !omitVR && allValid != res {

		if parsedDoc.IsRecursive() || forceLP {
			fmt.Println("\nGenerated LP: ", lp)

			fmt.Println("LP Tables: ")
			for i := range lpTables {
				fmt.Println(lpTables[i].Limit(10))
			}

			fmt.Println("log names of shapes")
			for name, shape := range parsedDoc.shapeNames {
				fmt.Println(shape.GetLogName())
				fmt.Println(parsedDoc.uncondAnswers[name])
				fmt.Println("Invalid Targets: ", invalidTargets[name])
			}
		}

		fmt.Println("Number of reports: ", len(reports))

		fmt.Println("VALIDATION REPORT: \n", actual)
		log.Panicln("Mismatch between ValidationResult & ValidationReports result! ", allValid, res)
	}

	if !silent && !omitVR && vrOutFile == nil {
		fmt.Println("VALIDATION REPORT: \n", abbr(actual.String()))
	} else if vrOutFile != nil {
		vrOutFile.WriteString(actual.String())
	}

	// Clean up the named graph afterwards
	if *dataIncluded {
		ep.ClearGraph(parsedDoc.fromGraph)
	}

	if !silent {
		fmt.Println("\n\nTime Composition:")
		fmt.Println(c)
	}
	return actual
}

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
	poseQuery := flagSet.String("poseTestQuery", "",
		"A query to run and return the results. Used for testing/debug purposes.")
	omitVR := flagSet.Bool("omitVR", false,
		"Omits outputting the Validation Report. Note that it will still be produced internally.")
	outputVR := flagSet.String("outputVR", "",
		"A filepath used to export the Validation Report in turtle notation. "+
			"Using this and -omitVR at same time is superflous.")
	forceLP := flagSet.Bool("forceLP", false, "Force the translation into logic programs.")

	// input flags demo purposes

	demoOutputOnlyLP := flagSet.Bool("demoOutputLP", false, "Outputs only the produced LPs.")

	demoOutputQueries := flagSet.Bool("demoOutputQueries", false, "Outputs only the produced SPARQL queries.")

	usingUpdateEndpoint := false

	flagSet.Parse(os.Args[1:])

	if *endpointAddress == "" || *shaclDocPath == "" {
		fmt.Println("Input args: " + strings.Join(os.Args, " "))
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
	defer shaclDoc.Close()

	var vrOUtFile *os.File
	if *outputVR != "" {
		vrOUtFile, err = os.OpenFile(*outputVR, os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0o644)
		check(err)
		defer vrOUtFile.Close()
	}

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

	// Test Query routine
	if *poseQuery != "" {
		queryFile, err := os.ReadFile(*poseQuery)
		check(err)

		endpoint.QueryString(string(queryFile))

		form := url.Values{}
		form.Set("query", string(queryFile))
		arg := form.Encode()

		fmt.Println("Argument: ", arg)

		os.Exit(0)
	}

	GetNameSpace(shaclDoc)

	// var VR *ValidationReport

	var graphName string

	// check if data needs to be inserted into Endpoint
	if *dataIncluded {
		// VR, err = ExtractValidationReport(g2)
		// check(err)

		// fmt.Println("Extracted VR\n", VR)

		basename := filepath.Base(*shaclDocPath)
		fileName := strings.TrimSuffix(basename, filepath.Ext(basename))
		res := endpoint.Insert(g2, "<"+_sh+fileName+">")
		check(res)
		graphName = "<" + _sh + fileName + ">"
	}



	parsedDoc := GetShaclDocument(g2, graphName, endpoint, *debug)

	if *forceLP || *demoOutputOnlyLP {
		demoLP = true
	}


	parsedDoc.debug = *debug
	var addedText string
	if !*debug {
		it := color.New(color.Italic)
		addedText = it.Sprint("(use -debug to also show blank Shapes)")
	}
	fmt.Println("The parsed SHACL Document:", addedText, parsedDoc.String())



	// set set active
	activeDoc = &parsedDoc

	// Main Routine
	answerShacl(endpoint, parsedDoc, dataIncluded, *debug, *omitVR, vrOUtFile, false, *forceLP, *demoOutputOnlyLP, *demoOutputQueries)
}
