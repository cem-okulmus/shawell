package main

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/fatih/color"

	rdf "github.com/cem-okulmus/rdf2go-1"
)

type EARLReport struct {
	validatorName       rdf.Term         // IRI (URL to the Github page, pretty much)
	validatorNameString string           // human-readable name
	developer           rdf.Term         // IRI identifying the dev (via github?)
	testResult          []EARLTestResult // individual testResults
}
type Result int64

const (
	failed Result = iota
	partial
	passed
)

type EARLTestResult struct {
	name      string
	result    Result
	info      string // info to add to the test result
	dev       rdf.Term
	validator rdf.Term
}

// String renders an EARLReport in Turtle format conforming to the EARL ontology.
func (e *EARLReport) String() string {
	var sb strings.Builder

	sb.WriteString("@prefix sht:   <http://www.w3.org/ns/shacl-test#> .\n")
	sb.WriteString("@prefix doap: <http://usefulinc.com/ns/doap#> .\n")
	sb.WriteString("@prefix earl: <http://www.w3.org/ns/earl#>  .\n")
	sb.WriteString("@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .\n\n")

	sb.WriteString(fmt.Sprint(e.validatorName, " rdf:type doap:Project .\n"))
	sb.WriteString(fmt.Sprint(e.validatorName, " rdf:type earl:Software .\n"))
	sb.WriteString(fmt.Sprint(e.validatorName, " rdf:type earl:TextSubject .\n"))
	sb.WriteString(fmt.Sprint(e.validatorName, " doap:developer ", e.developer, " .\n"))
	sb.WriteString(fmt.Sprint(e.validatorName, " doap:name \"", e.validatorNameString, "\" .\n"))

	for i := range e.testResult {
		sb.WriteString(e.testResult[i].String())
	}

	return sb.String()
}

// AddTestResult appends a new test result to the EARL report.
func (e *EARLReport) AddTestResult(name, info string, result Result) {
	e.testResult = append(e.testResult, EARLTestResult{
		name:      name,
		info:      info,
		result:    result,
		dev:       e.developer,
		validator: e.validatorName,
	})
}

// String renders an individual test result assertion in EARL Turtle format.
func (t EARLTestResult) String() string {
	var sb strings.Builder

	sb.WriteString("[\n")

	sb.WriteString(fmt.Sprint("  ", "rdf:type earl:Assertion ;\n"))
	sb.WriteString(fmt.Sprint("  ", "earl:assertedBy ", t.dev, " ;\n"))
	sb.WriteString(fmt.Sprint("  ", "earl:result [\n"))
	sb.WriteString(fmt.Sprint("     ", "rdf:type earl:TestResult ;\n"))
	if t.info != "" {
		sb.WriteString(fmt.Sprint("     ", "earl:info \"", t.info, "\" ;\n"))
	}
	sb.WriteString(fmt.Sprint("     ", "earl:mode earl:automatic ;\n"))
	switch t.result {
	case failed:
		sb.WriteString(fmt.Sprint("     ", "earl:outcome earl:failed ;\n"))
	case partial:
		sb.WriteString(fmt.Sprint("     ", "earl:outcome sht:partial ;\n"))
	case passed:
		sb.WriteString(fmt.Sprint("     ", "earl:outcome earl:passed ;\n"))
	}
	sb.WriteString(fmt.Sprint("  ", "];\n"))
	sb.WriteString(fmt.Sprint("  ", "earl:subject ", t.validator, " ;\n"))
	sb.WriteString(fmt.Sprint("  ", "earl:test <urn:x-shacl-test:", t.name, "> ;\n"))

	sb.WriteString("].\n")

	return sb.String()
}

func CoreTests() (tests []string) {

	// Complex:
	tests = append(tests, "/complex/personexample")
	tests = append(tests, "/complex/shacl-shacl")

	// misc:
	tests = append(tests, "/misc/deactivated-001")
	tests = append(tests, "/misc/deactivated-002")
	tests = append(tests, "/misc/message-001")
	tests = append(tests, "/misc/severity-001")
	tests = append(tests, "/misc/severity-002")

	// node:
	tests = append(tests, "/node/and-001")
	tests = append(tests, "/node/and-002")
	tests = append(tests, "/node/class-001")
	tests = append(tests, "/node/class-002")
	tests = append(tests, "/node/class-003")
	tests = append(tests, "/node/closed-001")
	tests = append(tests, "/node/closed-002")
	tests = append(tests, "/node/datatype-001")
	tests = append(tests, "/node/datatype-002")
	tests = append(tests, "/node/disjoint-001")
	tests = append(tests, "/node/equals-001")
	tests = append(tests, "/node/equals-path-001")
	tests = append(tests, "/node/hasValue-001")
	tests = append(tests, "/node/in-001")
	tests = append(tests, "/node/languageIn-001")
	tests = append(tests, "/node/maxExclusive-001")
	tests = append(tests, "/node/maxInclusive-001")
	tests = append(tests, "/node/maxLength-001")
	tests = append(tests, "/node/minExclusive-001")
	tests = append(tests, "/node/minInclusive-001")
	tests = append(tests, "/node/minInclusive-002")
	tests = append(tests, "/node/minInclusive-003")
	tests = append(tests, "/node/minLength-001")
	tests = append(tests, "/node/node-001")
	tests = append(tests, "/node/nodeKind-001")
	tests = append(tests, "/node/not-001")
	tests = append(tests, "/node/not-002")
	tests = append(tests, "/node/or-001")
	tests = append(tests, "/node/pattern-001")
	tests = append(tests, "/node/pattern-002")
	tests = append(tests, "/node/xone-001")
	tests = append(tests, "/node/xone-duplicate")
	tests = append(tests, "/node/qualified-001")

	// path:
	tests = append(tests, "/path/path-alternative-001")
	tests = append(tests, "/path/path-complex-001")
	tests = append(tests, "/path/path-complex-002")
	tests = append(tests, "/path/path-inverse-001")
	tests = append(tests, "/path/path-oneOrMore-001")
	tests = append(tests, "/path/path-sequence-001")
	tests = append(tests, "/path/path-sequence-002")
	tests = append(tests, "/path/path-sequence-duplicate-001")
	tests = append(tests, "/path/path-strange-001")
	tests = append(tests, "/path/path-strange-002")
	tests = append(tests, "/path/path-zeroOrMore-001")
	tests = append(tests, "/path/path-zeroOrOne-001")
	tests = append(tests, "/path/path-unused-001")

	// property:
	tests = append(tests, "/property/and-001")
	tests = append(tests, "/property/class-001")
	tests = append(tests, "/property/datatype-001")
	tests = append(tests, "/property/datatype-002")
	tests = append(tests, "/property/datatype-003")
	tests = append(tests, "/property/datatype-ill-formed")
	tests = append(tests, "/property/disjoint-001")
	tests = append(tests, "/property/equals-001")
	tests = append(tests, "/property/equals-path-001")
	tests = append(tests, "/property/hasValue-001")
	tests = append(tests, "/property/in-001")
	tests = append(tests, "/property/languageIn-001")
	tests = append(tests, "/property/lessThan-001")
	tests = append(tests, "/property/lessThan-002")
	tests = append(tests, "/property/lessThanOrEquals-001")
	tests = append(tests, "/property/maxCount-001")
	tests = append(tests, "/property/maxCount-002")
	tests = append(tests, "/property/maxExclusive-001")
	tests = append(tests, "/property/maxInclusive-001")
	tests = append(tests, "/property/maxLength-001")
	tests = append(tests, "/property/minCount-001")
	tests = append(tests, "/property/minCount-002")
	tests = append(tests, "/property/minExclusive-001")
	tests = append(tests, "/property/minExclusive-002")
	tests = append(tests, "/property/minLength-001")
	tests = append(tests, "/property/node-001")
	tests = append(tests, "/property/node-002")
	tests = append(tests, "/property/nodeKind-001")
	tests = append(tests, "/property/not-001")
	tests = append(tests, "/property/or-001")
	tests = append(tests, "/property/or-datatypes-001")
	tests = append(tests, "/property/pattern-001")
	tests = append(tests, "/property/pattern-002")
	tests = append(tests, "/property/property-001")
	tests = append(tests, "/property/qualifiedMinCountDisjoint-001")
	tests = append(tests, "/property/qualifiedValueShape-001")
	tests = append(tests, "/property/qualifiedValueShapesDisjoint-001")
	tests = append(tests, "/property/uniqueLang-001")
	tests = append(tests, "/property/uniqueLang-002")

	// targets
	tests = append(tests, "/targets/multipleTargets-001")
	tests = append(tests, "/targets/targetClass-001")
	tests = append(tests, "/targets/targetClassImplicit-001")
	tests = append(tests, "/targets/targetNode-001")
	tests = append(tests, "/targets/targetObjectsOf-001")
	tests = append(tests, "/targets/targetSubjectsOf-001")
	tests = append(tests, "/targets/targetSubjectsOf-002")

	// validation-reports
	tests = append(tests, "/validation-reports/shared")

	return tests
}

// TestCompliance runs through the [insert number] tests that make up the
// SHACL Test Suite Core and checks for compliance. An error is reported only
// in case of no compliance. Partial Compliance is reported, but not treated
// as an error for the purposes of this test. An EARL report is also output.
func TestCompliance(t *testing.T) {
	Compliance(t, false)
}

// TestLogicProgram tests whether the translation to logic programs is compliant
// with SHACL core, producing an EARL report of the test findings
func TestLogicProgram(t *testing.T) {
	Compliance(t, true)
}

// TestComplianceOxigraph runs the SHACL Test Suite Core using a local Oxigraph instance.
func TestComplianceOxigraph(t *testing.T) {
	ComplianceOxigraph(t, false)
}

// TestLogicProgramOxigraph tests the LP translation for compliance using a local Oxigraph instance.
func TestLogicProgramOxigraph(t *testing.T) {
	ComplianceOxigraph(t, true)
}

func Compliance(t *testing.T, forceLP bool) EARLReport {
	ensureDependencies(false)

	dlv = "bin/dlv"

	ep := GetSparqlEndpoint(
		"http://localhost:7200/repositories/graphdb",
		"http://localhost:7200/repositories/graphdb/statements",
		"",
		"",
		false,
		true,
		"",
	)

	if err := ep.Ping(); err != nil {
		t.Skip("GraphDB not available:", err)
		return EARLReport{}
	}

	return ComplianceWithEndpoint(t, forceLP, false, ep, "Sparql engine being used: GraphDB 10.3.3")
}

func ComplianceOxigraph(t *testing.T, forceLP bool) EARLReport {
	ensureDependencies(true)

	dlv = "bin/dlv"

	ep, cleanup, err := StartOxigraph(false)
	if err != nil {
		t.Skip("oxigraph not available:", err)
		return EARLReport{}
	}
	defer cleanup()

	return ComplianceWithEndpoint(t, forceLP, false, ep, "Sparql engine being used: Oxigraph")
}

func ComplianceWithEndpoint(t *testing.T, forceLP, earlOutput bool, ep *SparqlEndpoint, earlInfo string) EARLReport {
	var tests []string = CoreTests()

	countPassed := 0
	countPartial := 0

	var basedir string = "resources/W3_SHACL_Test_Suite_Core"

	earl := EARLReport{
		validatorName:       rdf.NewResource("https://github.com/cem-okulmus/shawell"),
		validatorNameString: "shaWell",
		developer:           rdf.NewResource("https://github.com/cem-okulmus"),
	}

	for _, testStringCompact := range tests {

		testString := basedir + testStringCompact + ".ttl"
		fmt.Print("Testing: ", testString, " ... ")

		shaclDoc, err := os.Open(testString)
		check(err)
		defer shaclDoc.Close()

		g2 := rdf.NewGraph(_sh)

		err = g2.Parse(shaclDoc, "text/turtle")
		check(err)

		prefixes = make(map[string]string) // reset
		GetNameSpace(shaclDoc)

		var VR *ValidationReport
		var isomorph bool
		var graphName string

		VR, err = ExtractValidationReport(g2)
		check(err)

		// fmt.Println("Extracted VR\n", VR)

		basename := filepath.Base(testString)
		fileName := strings.TrimSuffix(basename, filepath.Ext(basename))

		//ClearData

		err = ep.ClearGraph("<" + _sh + fileName + ">")
		check(err)

		res := ep.Insert(g2, "<"+_sh+fileName+">", false)
		check(res)
		graphName = "<" + _sh + fileName + ">"
		parsedDoc := GetShaclDocument(g2, graphName, ep, false)
		parsedDoc.debug = false
		activeDoc = &parsedDoc

		config := config{
			debug:       false,
			omitVR:      false,
			vrOutFile:   nil,
			silent:      true,
			forceLP:     forceLP,
			onlyLP:      false,
			onlyQueries: false,
		}

		actual := answerShacl(ep, parsedDoc, config)

		//ClearData

		err = ep.ClearGraph("<" + _sh + fileName + ">")
		check(err)

		result := actual.conforms == VR.conforms

		VR.dataGraph = nil
		VR.shapesGraph = nil
		VR.testName = nil
		VR.label = nil
		isomorph = rdfTurtleIsomorphic(actual.String(), VR.String())

		green := color.New(color.FgGreen)
		yellow := color.New(color.FgYellow)
		red := color.New(color.FgRed)

		if !result {
			t.Error(red.Sprint("For test: ", testString, " did not pass."))
		}
		var addText string

		if !result {
			addText = red.Sprint("Failed")
			earl.AddTestResult("/core"+testStringCompact, earlInfo, failed)
		} else if isomorph {
			addText = green.Sprint("Full")
			countPassed++
			earl.AddTestResult("/core"+testStringCompact, earlInfo, passed)
		} else if result && !isomorph {
			addText = yellow.Sprint("Partial")
			countPartial++
			earl.AddTestResult("/core"+testStringCompact, earlInfo, partial)
		}
		fmt.Print("passed; Compliance: ", addText, "\n")
	}

	fmt.Println("\n\n Partial Tests: ", countPartial, " Passed Tests: ", countPassed)

	if earlOutput {
		fmt.Println("EARL report: \n\n ", earl.String())
	}

	return earl
}

func TestLPMatchesUnwinding(t *testing.T) {
	// get earl from unwinding:

	earlUnwind := Compliance(t, false)

	earlLP := Compliance(t, true)

	green := color.New(color.FgGreen)
	red := color.New(color.FgRed)

	if earlLP.String() != earlUnwind.String() {
		t.Error(red.Sprint(" Logic Program Translation and Unwinding do not produce same EARL."))
	}

	green.Println("Logic Program and Unwinding produce _exactly_ same result.")
}

func TestLPMatchesUnwindingOxigraph(t *testing.T) {
	earlUnwind := ComplianceOxigraph(t, false)

	earlLP := ComplianceOxigraph(t, true)

	green := color.New(color.FgGreen)
	red := color.New(color.FgRed)

	if earlLP.String() != earlUnwind.String() {
		t.Error(red.Sprint(" Logic Program Translation and Unwinding do not produce same EARL (Oxigraph)."))
	}

	green.Println("Logic Program and Unwinding produce _exactly_ same result (Oxigraph).")
}