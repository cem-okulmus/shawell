package main

import (
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"

	"github.com/fatih/color"

	rdf "github.com/cem-okulmus/MyRDF2Go"
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

func (e *EARLReport) AddTestResult(name, info string, result Result) {
	e.testResult = append(e.testResult, EARLTestResult{
		name:      name,
		info:      info,
		result:    result,
		dev:       e.developer,
		validator: e.validatorName,
	})
}

// ADD EARL INFO to indicate the currently used SPAQRL engine
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
	Compliance(t)
}

func Compliance(t *testing.T) EARLReport {
	var tests []string = CoreTests()

	dlv = "bin/dlv"

	endpoint := GetSparqlEndpoint(
		"http://localhost:7200/repositories/graphdb",
		"http://localhost:7200/repositories/graphdb/statements",
		"",
		"",
		false,
		true,
		"",
	)

	countPassed := 0
	countPartial := 0

	var basedir string = "resources/W3_SHACL_Test_Suite_Core"

	earl := EARLReport{
		validatorName:       res("https://github.com/cem-okulmus/shawell"),
		validatorNameString: "shaWell",
		developer:           res("https://github.com/cem-okulmus"),
	}

	earlInfo := "Sparql engine being used: GraphDB 10.3.3"

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

		var graphName string

		VR, err = ExtractValidationReport(g2)
		check(err)

		// fmt.Println("Extracted VR\n", VR)

		basename := filepath.Base(testString)
		fileName := strings.TrimSuffix(basename, filepath.Ext(basename))
		res := endpoint.Insert(g2, "<"+_sh+fileName+">")
		check(res)
		graphName = "<" + _sh + fileName + ">"
		parsedDoc := GetShaclDocument(g2, graphName, endpoint, false)
		parsedDoc.debug = false
		activeDoc = &parsedDoc

		var isomorph bool
		dataincluded := true
		actual := answerShacl(endpoint, parsedDoc,
			&dataincluded, false, false, nil, true, false)

		result := actual.conforms == VR.conforms

		jena_path := "bin/apache-jena-4.10.0/bin/rdfcompare"

		// Open the files for writing
		actualFile, err := os.Create("/tmp/actual.ttl")
		check(err)
		defer actualFile.Close()
		_, err = actualFile.WriteString(actual.String())
		check(err)

		expectedFile, err := os.Create("/tmp/expected.ttl")
		check(err)
		defer expectedFile.Close()
		VR.dataGraph = nil
		VR.shapesGraph = nil
		VR.testName = nil
		VR.label = nil
		_, err = expectedFile.WriteString(VR.String())
		check(err)

		// check isomorphism

		cmd := exec.Command("/bin/sh", jena_path, "/tmp/actual.ttl", "/tmp/expected.ttl")

		out, _ := cmd.Output()
		outString := string(out)

		isomorph = strings.HasPrefix(outString, "models are equal")

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

	fmt.Println("EARL report: \n\n ", earl.String())

	return earl
}

// TestLogicProgram tests whether the translation to logic programs is compliant
// with SHACL core, producing an EARL report of the test findings
func TestLogicProgram(t *testing.T) {
	LogicProgram(t)
}

func LogicProgram(t *testing.T) EARLReport {
	var tests []string = CoreTests()

	dlv = "bin/dlv"

	endpoint := GetSparqlEndpoint(
		"http://localhost:7200/repositories/graphdb",
		"http://localhost:7200/repositories/graphdb/statements",
		"",
		"",
		false,
		true,
		"",
	)

	countPassed := 0
	countPartial := 0

	var basedir string = "resources/W3_SHACL_Test_Suite_Core"

	earl := EARLReport{
		validatorName:       res("https://github.com/cem-okulmus/shawell"),
		validatorNameString: "shaWell",
		developer:           res("https://github.com/cem-okulmus"),
	}

	earlInfo := "Sparql engine being used: GraphDB 10.3.3"

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
		res := endpoint.Insert(g2, "<"+_sh+fileName+">")
		check(res)
		graphName = "<" + _sh + fileName + ">"
		parsedDoc := GetShaclDocument(g2, graphName, endpoint, false)
		parsedDoc.debug = false
		activeDoc = &parsedDoc

		dataincluded := true
		actual := answerShacl(endpoint, parsedDoc,
			&dataincluded, false, false, nil, true, true)

		result := actual.conforms == VR.conforms

		jena_path := "bin/apache-jena-4.10.0/bin/rdfcompare"

		// Open the files for writing
		actualFile, err := os.Create("/tmp/actual.ttl")
		check(err)
		defer actualFile.Close()
		_, err = actualFile.WriteString(actual.String())
		check(err)

		expectedFile, err := os.Create("/tmp/expected.ttl")
		check(err)
		defer expectedFile.Close()
		defer expectedFile.Close()
		VR.dataGraph = nil
		VR.shapesGraph = nil
		VR.testName = nil
		VR.label = nil
		_, err = expectedFile.WriteString(VR.String())
		check(err)

		// check isomorphism

		cmd := exec.Command("/bin/sh", jena_path, "/tmp/actual.ttl", "/tmp/expected.ttl")

		out, _ := cmd.Output()
		// check(err)

		outString := string(out)

		isomorph = strings.HasPrefix(outString, "models are equal")

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

	fmt.Println("EARL report: \n\n ", earl.String())

	return earl
}

func TestLPMatchesUnwinding(t *testing.T) {
	// get earl from unwinding:

	earlUnwind := Compliance(t)

	earlLP := LogicProgram(t)

	green := color.New(color.FgGreen)
	red := color.New(color.FgRed)

	if earlLP.String() != earlUnwind.String() {
		t.Error(red.Sprint(" Logic Program Translation and Unwinding do not produce same EARL."))
	}

	green.Println("Logic Program and Unwinding produce _exactly_ same result.")
}
