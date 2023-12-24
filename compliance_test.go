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

func SetupTests() (tests []string) {
	var basedir string = "resources/W3_SHACL_Test_Suite_Core"

	// Complex:
	tests = append(tests, basedir+"/complex/personexample.ttl")
	tests = append(tests, basedir+"/complex/shacl-shacl.ttl")

	// misc:
	tests = append(tests, basedir+"/misc/deactivated-001.ttl")
	tests = append(tests, basedir+"/misc/deactivated-002.ttl")
	tests = append(tests, basedir+"/misc/message-001.ttl")
	tests = append(tests, basedir+"/misc/severity-001.ttl")
	tests = append(tests, basedir+"/misc/severity-002.ttl")

	// node:
	tests = append(tests, basedir+"/node/and-001.ttl")
	tests = append(tests, basedir+"/node/and-002.ttl")
	tests = append(tests, basedir+"/node/class-001.ttl")
	tests = append(tests, basedir+"/node/class-002.ttl")
	tests = append(tests, basedir+"/node/class-003.ttl")
	tests = append(tests, basedir+"/node/closed-001.ttl")
	tests = append(tests, basedir+"/node/closed-002.ttl")
	tests = append(tests, basedir+"/node/datatype-001.ttl")
	tests = append(tests, basedir+"/node/datatype-002.ttl")
	tests = append(tests, basedir+"/node/disjoint-001.ttl")
	tests = append(tests, basedir+"/node/equals-001.ttl")
	tests = append(tests, basedir+"/node/hasValue-001.ttl")
	tests = append(tests, basedir+"/node/in-001.ttl")
	tests = append(tests, basedir+"/node/languageIn-001.ttl")
	tests = append(tests, basedir+"/node/maxExclusive-001.ttl")
	tests = append(tests, basedir+"/node/maxInclusive-001.ttl")
	tests = append(tests, basedir+"/node/maxLength-001.ttl")
	tests = append(tests, basedir+"/node/minExclusive-001.ttl")
	tests = append(tests, basedir+"/node/minInclusive-001.ttl")
	tests = append(tests, basedir+"/node/minInclusive-002.ttl")
	tests = append(tests, basedir+"/node/minInclusive-003.ttl")
	tests = append(tests, basedir+"/node/minLength-001.ttl")
	tests = append(tests, basedir+"/node/node-001.ttl")
	tests = append(tests, basedir+"/node/nodeKind-001.ttl")
	tests = append(tests, basedir+"/node/not-001.ttl")
	tests = append(tests, basedir+"/node/not-002.ttl")
	tests = append(tests, basedir+"/node/or-001.ttl")
	tests = append(tests, basedir+"/node/pattern-001.ttl")
	tests = append(tests, basedir+"/node/pattern-002.ttl")
	tests = append(tests, basedir+"/node/xone-001.ttl")
	tests = append(tests, basedir+"/node/xone-duplicate.ttl")
	tests = append(tests, basedir+"/node/qualified-001.ttl")

	// path:
	tests = append(tests, basedir+"/path/path-alternative-001.ttl")
	tests = append(tests, basedir+"/path/path-complex-001.ttl")
	tests = append(tests, basedir+"/path/path-complex-002.ttl")
	tests = append(tests, basedir+"/path/path-inverse-001.ttl")
	tests = append(tests, basedir+"/path/path-oneOrMore-001.ttl")
	tests = append(tests, basedir+"/path/path-sequence-001.ttl")
	tests = append(tests, basedir+"/path/path-sequence-002.ttl")
	tests = append(tests, basedir+"/path/path-sequence-duplicate-001.ttl")
	tests = append(tests, basedir+"/path/path-strange-001.ttl")
	tests = append(tests, basedir+"/path/path-strange-002.ttl")
	tests = append(tests, basedir+"/path/path-zeroOrMore-001.ttl")
	tests = append(tests, basedir+"/path/path-zeroOrOne-001.ttl")
	tests = append(tests, basedir+"/path/path-unused-001.ttl")

	// property:
	tests = append(tests, basedir+"/property/and-001.ttl")
	tests = append(tests, basedir+"/property/class-001.ttl")
	tests = append(tests, basedir+"/property/datatype-001.ttl")
	tests = append(tests, basedir+"/property/datatype-002.ttl")
	tests = append(tests, basedir+"/property/datatype-003.ttl")
	tests = append(tests, basedir+"/property/datatype-ill-formed.ttl")
	tests = append(tests, basedir+"/property/disjoint-001.ttl")
	tests = append(tests, basedir+"/property/equals-001.ttl")
	tests = append(tests, basedir+"/property/hasValue-001.ttl")
	tests = append(tests, basedir+"/property/in-001.ttl")
	tests = append(tests, basedir+"/property/languageIn-001.ttl")
	tests = append(tests, basedir+"/property/lessThan-001.ttl")
	tests = append(tests, basedir+"/property/lessThan-002.ttl")
	tests = append(tests, basedir+"/property/lessThanOrEquals-001.ttl")
	tests = append(tests, basedir+"/property/maxCount-001.ttl")
	tests = append(tests, basedir+"/property/maxCount-002.ttl")
	tests = append(tests, basedir+"/property/maxExclusive-001.ttl")
	tests = append(tests, basedir+"/property/maxInclusive-001.ttl")
	tests = append(tests, basedir+"/property/maxLength-001.ttl")
	tests = append(tests, basedir+"/property/minCount-001.ttl")
	tests = append(tests, basedir+"/property/minCount-002.ttl")
	tests = append(tests, basedir+"/property/minExclusive-001.ttl")
	tests = append(tests, basedir+"/property/minExclusive-002.ttl")
	tests = append(tests, basedir+"/property/minLength-001.ttl")
	tests = append(tests, basedir+"/property/node-001.ttl")
	tests = append(tests, basedir+"/property/node-002.ttl")
	tests = append(tests, basedir+"/property/nodeKind-001.ttl")
	tests = append(tests, basedir+"/property/not-001.ttl")
	tests = append(tests, basedir+"/property/or-001.ttl")
	tests = append(tests, basedir+"/property/or-datatypes-001.ttl")
	tests = append(tests, basedir+"/property/pattern-001.ttl")
	tests = append(tests, basedir+"/property/pattern-002.ttl")
	tests = append(tests, basedir+"/property/property-001.ttl")
	tests = append(tests, basedir+"/property/qualifiedMinCountDisjoint-001.ttl")
	tests = append(tests, basedir+"/property/qualifiedValueShape-001.ttl")
	tests = append(tests, basedir+"/property/qualifiedValueShapesDisjoint-001.ttl")
	tests = append(tests, basedir+"/property/uniqueLang-001.ttl")
	tests = append(tests, basedir+"/property/uniqueLang-002.ttl")

	// targets
	tests = append(tests, basedir+"/targets/multipleTargets-001.ttl")
	tests = append(tests, basedir+"/targets/targetClass-001.ttl")
	tests = append(tests, basedir+"/targets/targetClassImplicit-001.ttl")
	tests = append(tests, basedir+"/targets/targetNode-001.ttl")
	tests = append(tests, basedir+"/targets/targetObjectsOf-001.ttl")
	tests = append(tests, basedir+"/targets/targetSubjectsOf-001.ttl")
	tests = append(tests, basedir+"/targets/targetSubjectsOf-002.ttl")

	// validation-reports
	tests = append(tests, basedir+"/validation-reports/shared.ttl")

	return tests
}

// TestCompliance runs through the [insert number] tests that make up the
// SHACL Test Suite and checks for compliance. An error is reported only
// in case of no compliance. Partial Compliance is reported, but not treated
// as an error for the purposes of this test.
func TestCompliance(t *testing.T) {
	var tests []string = SetupTests()

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

	for _, testString := range tests {
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

		jena_path := "/home/okulmus/Desktop/scripts/shawell/bin/apache-jena-4.10.0/bin/rdfcompare"

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

		{

			cmd := exec.Command("/bin/sh", jena_path, "/tmp/actual.ttl", "/tmp/expected.ttl")

			// stderr, err := cmd.StderrPipe()
			// stdin, err := cmd.StdinPipe()
			// if err != nil {
			// 	log.Fatal(err)
			// }
			// fmt.Println("Setup stderr")
			// if err := cmd.Start(); err != nil {
			// 	log.Fatal(err)
			// }

			// slurp, _ := io.ReadAll(stderr)
			// fmt.Printf("%s\n", slurp)

			// if err := cmd.Wait(); err != nil {
			// 	log.Fatal(err)

			out, _ := cmd.Output()
			outString := string(out)

			// fmt.Println("out: ", outString)
			// check(err)

			isomorph = strings.HasPrefix(outString, "models are equal")

		}

		green := color.New(color.FgGreen)
		yellow := color.New(color.FgYellow)
		red := color.New(color.FgRed)

		if !result {
			t.Error(red.Sprint("For test: ", testString, " did not pass."))
		}
		var addText string

		if !result {
			addText = red.Sprint("Failed")
		} else if isomorph {
			addText = green.Sprint("Full")
			countPassed++
		} else if result && !isomorph {
			addText = yellow.Sprint("Partial")
			countPartial++
		}
		fmt.Print("passed; Compliance: ", addText, "\n")
	}

	fmt.Println("\n\n Partial Tests: ", countPartial, " Passed Tests: ", countPassed)
}

// TestLogicProgram tests whether the translation to logic programs is compliant
// with SHACL core, and ideally produces the same compliancy as the programmatic unwinding
func TestLogicProgram(t *testing.T) {
	var tests []string = SetupTests()

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

	for _, testString := range tests {
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
		defer expectedFile.Close()
		VR.dataGraph = nil
		VR.shapesGraph = nil
		VR.testName = nil
		VR.label = nil
		_, err = expectedFile.WriteString(VR.String())
		check(err)

		// check isomorphism

		{
			cmd := exec.Command("/bin/sh", jena_path, "/tmp/actual.ttl", "/tmp/expected.ttl")

			out, _ := cmd.Output()
			// check(err)

			outString := string(out)

			isomorph = strings.HasPrefix(outString, "models are equal")

		}

		green := color.New(color.FgGreen)
		yellow := color.New(color.FgYellow)
		red := color.New(color.FgRed)

		if !result {
			t.Error(red.Sprint("For test: ", testString, " did not pass."))
		}
		var addText string

		if !result {
			addText = red.Sprint("Failed")
		} else if isomorph {
			addText = green.Sprint("Full")
			countPassed++
		} else if result && !isomorph {
			addText = yellow.Sprint("Partial")
			countPartial++
		}
		fmt.Print("passed; Compliance: ", addText, "\n")
	}

	fmt.Println("\n\n Partial Tests: ", countPartial, " Passed Tests: ", countPassed)
}
