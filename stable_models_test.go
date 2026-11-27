package main

import (
	"os"
	"path/filepath"
	"runtime"
	"slices"
	"strings"
	"testing"
)

// Appendix B of stable_semantics_plan.md as a table test, together with edge cases of the cautious rework and of
// phase 4. Each case gives the expected status and validation report under well-founded, brave and cautious
// semantics. Under well-founded an undefined target counts as a violation, so a case whose target is undefined is
// invalid. Every document here is recursive, so the stable modes go through the clingo calls of answerShacl, and
// the stable verdicts are those of the "Stable models", "Brave" and "Cautious" columns of Appendix B.
//
// A report is written as the sorted results "Shape@node", one per result, separated by spaces; "" is the empty
// report. Where several models can decide the verdict, the report depends on which one clingo returns (phase 4,
// step 5), so the expectation lists the possible reports separated by "|".
//
// The data goes into its own named graph and the shapes are parsed separately (validateSeparateGraphs), so the
// domain of the stable modes is the data's nodes plus the constants of the shapes. This does not cover the removal
// of the shapes graph from the data under --dataIncluded, which happens in main.

const stableModelsPrefixes = `@prefix : <http://example.org/> .
@prefix sh: <http://www.w3.org/ns/shacl#> .
`

// stableModelsData is the data of every Appendix B case except cx7.
const stableModelsData = `:a :q :b .`

// stableModelsExpectation is the expected outcome of a case in one mode.
type stableModelsExpectation struct {
	status ValidationStatus
	report string
}

type stableModelsCase struct {
	name     string
	data     string
	shapes   string
	wf       stableModelsExpectation
	brave    stableModelsExpectation
	cautious stableModelsExpectation
}

var stableModelsCases = []stableModelsCase{
	{
		// the no-model report lists the target of :S, though :S holds there: the odd loop is elsewhere
		name: "cx1 odd loop on an unrelated, untargeted shape",
		data: stableModelsData,
		shapes: `:S a sh:NodeShape ; sh:targetNode :a .
:U a sh:NodeShape ; sh:not :U .`,
		wf:       stableModelsExpectation{Valid, ""},
		brave:    stableModelsExpectation{NoModel, "S@a"},
		cautious: stableModelsExpectation{NoModel, "S@a"},
	},
	{
		name:     "cx2 fine at the target, odd loop at an untargeted node",
		data:     stableModelsData,
		shapes:   `:U a sh:NodeShape ; sh:targetNode :a ; sh:or ( [ sh:hasValue :a ] [ sh:not :U ] ) .`,
		wf:       stableModelsExpectation{Valid, ""},
		brave:    stableModelsExpectation{NoModel, "U@a"},
		cautious: stableModelsExpectation{NoModel, "U@a"},
	},
	{
		// every counter-model fails :A at :a; the models differ only at :b, which is no target
		name: "cx3 even loop, one target",
		data: stableModelsData,
		shapes: `:A a sh:NodeShape ; sh:targetNode :a ; sh:not :B .
:B a sh:NodeShape ; sh:not :A .`,
		wf:       stableModelsExpectation{Invalid, "A@a"},
		brave:    stableModelsExpectation{Valid, ""},
		cautious: stableModelsExpectation{Invalid, "A@a"},
	},
	{
		name: "cx4 true in every model by case split",
		data: stableModelsData,
		shapes: `:A a sh:NodeShape ; sh:not :B .
:B a sh:NodeShape ; sh:not :A .
:S a sh:NodeShape ; sh:targetNode :a ; sh:or ( :A :B ) .`,
		wf:       stableModelsExpectation{Invalid, "S@a"},
		brave:    stableModelsExpectation{Valid, ""},
		cautious: stableModelsExpectation{Valid, ""},
	},
	{
		// every model fails exactly one of the two targets, so both reports list one of them
		name: "cx5 each target brave individually, not jointly",
		data: stableModelsData,
		shapes: `:A a sh:NodeShape ; sh:targetNode :a ; sh:not :B .
:B a sh:NodeShape ; sh:targetNode :a ; sh:not :A .`,
		wf:       stableModelsExpectation{Invalid, "A@a B@a"},
		brave:    stableModelsExpectation{Invalid, "A@a|B@a"},
		cautious: stableModelsExpectation{Invalid, "A@a|B@a"},
	},
	{
		name: "cx6 odd loop acting as a constraint",
		data: stableModelsData,
		shapes: `:A a sh:NodeShape ; sh:not :B .
:B a sh:NodeShape ; sh:targetNode :a ; sh:not :A .
:K a sh:NodeShape ; sh:or ( [ sh:not :K ] [ sh:not :A ] ) .`,
		wf:       stableModelsExpectation{Invalid, "B@a"},
		brave:    stableModelsExpectation{Valid, ""},
		cautious: stableModelsExpectation{Valid, ""},
	},
	{
		name:     "cx7 odd loop only at nodes without :p",
		data:     `:a :p :a .`,
		shapes:   `:U a sh:NodeShape ; sh:targetNode :a ; sh:or ( [ sh:path :p ; sh:minCount 1 ] [ sh:not :U ] ) .`,
		wf:       stableModelsExpectation{Valid, ""},
		brave:    stableModelsExpectation{Valid, ""},
		cautious: stableModelsExpectation{Valid, ""},
	},
	{
		// :C has no targets of its own, so the no-model report lists only the target of :U
		name: "cx8 odd loop only at a constant in no data triple",
		data: stableModelsData,
		shapes: `:U a sh:NodeShape ; sh:targetNode :a ; sh:or ( [ sh:hasValue :a ] [ sh:hasValue :b ] [ sh:not :U ] ) .
:C a sh:NodeShape ; sh:hasValue :z .`,
		wf:       stableModelsExpectation{Valid, ""},
		brave:    stableModelsExpectation{NoModel, "U@a"},
		cautious: stableModelsExpectation{NoModel, "U@a"},
	},

	// Edge cases of the cautious rework: without targets nothing can fail, so a document with a stable model
	// is valid in both stable modes. Brave call 1 is then the plain program, and cautious skips call 1.
	{
		name:     "no data, so the domain target is empty and no shape has targets",
		data:     ``,
		shapes:   `:S a sh:NodeShape ; sh:property [ sh:path :p ; sh:node :S ] .`,
		wf:       stableModelsExpectation{Valid, ""},
		brave:    stableModelsExpectation{Valid, ""},
		cautious: stableModelsExpectation{Valid, ""},
	},
	{
		name:     "deactivated node shape, its property shape stays active",
		data:     `:a :p :a .`,
		shapes:   `:S a sh:NodeShape ; sh:deactivated true ; sh:targetNode :a ; sh:property [ sh:path :p ; sh:node :S ] .`,
		wf:       stableModelsExpectation{Valid, ""},
		brave:    stableModelsExpectation{Valid, ""},
		cautious: stableModelsExpectation{Valid, ""},
	},
	{
		name:     "no active shape at all",
		data:     `:a :p :a .`,
		shapes:   `:S a sh:NodeShape ; sh:deactivated true ; sh:targetNode :a ; sh:not :S .`,
		wf:       stableModelsExpectation{Valid, ""},
		brave:    stableModelsExpectation{Valid, ""},
		cautious: stableModelsExpectation{Valid, ""},
	},

	// Edge cases of the no-model report (phase 4, steps 3 and 4).
	{
		name: "no model, a shape with two targets",
		data: stableModelsData,
		shapes: `:S a sh:NodeShape ; sh:targetNode :a, :b .
:U a sh:NodeShape ; sh:not :U .`,
		wf:       stableModelsExpectation{Valid, ""},
		brave:    stableModelsExpectation{NoModel, "S@a S@b"},
		cautious: stableModelsExpectation{NoModel, "S@a S@b"},
	},
	{
		// an empty report that does not conform; the mismatch guard must not fire
		name:     "no model and no targets",
		data:     `:x :y :x .`,
		shapes:   `:U a sh:NodeShape ; sh:not :U .`,
		wf:       stableModelsExpectation{Valid, ""},
		brave:    stableModelsExpectation{NoModel, ""},
		cautious: stableModelsExpectation{NoModel, ""},
	},
}

// describeReport writes the results of a report as sorted "Shape@node" entries, with the example namespace
// removed, separated by spaces.
func describeReport(report *ValidationReport) string {
	var results []string
	for _, r := range report.results {
		shape := strings.TrimPrefix(r.sourceShape.RawValue(), "http://example.org/")
		node := strings.TrimPrefix(r.focusNode.RawValue(), "http://example.org/")
		results = append(results, shape+"@"+node)
	}
	slices.Sort(results)
	return strings.Join(results, " ")
}

// checkStableModelsReport compares a report with the expected outcome. Besides status and results, it checks
// that the report conforms exactly when the status is valid, and that the results of a no-model or unknown
// report, and only those, carry shawell's own constraint components.
func checkStableModelsReport(t *testing.T, report *ValidationReport, want stableModelsExpectation) {
	t.Helper()
	if report.status != want.status {
		t.Errorf("got status %v, want %v", report.status, want.status)
	}
	if report.conforms != (want.status == Valid) {
		t.Errorf("conforms is %v with status %v", report.conforms, report.status)
	}
	if got := describeReport(report); !slices.Contains(strings.Split(want.report, "|"), got) {
		t.Errorf("got report %q, want %q", got, want.report)
	}

	var wantComponent string
	switch want.status {
	case NoModel:
		wantComponent = _shawell + "NoStableModelConstraintComponent"
	case Unknown:
		wantComponent = _shawell + "UnknownStableModelConstraintComponent"
	}
	for _, r := range report.results {
		component := r.sourceConstraintComponent.RawValue()
		if wantComponent != "" && component != wantComponent {
			t.Errorf("result %v has component %s, want %s", r.focusNode, component, wantComponent)
		}
		if wantComponent == "" && strings.HasPrefix(component, _shawell) {
			t.Errorf("result %v has component %s, which is only for reports without a model", r.focusNode, component)
		}
	}
}

func TestStableModels(t *testing.T) {
	ep := startTestOxigraph(t)
	cmd, err := findClingo("")
	if err != nil {
		t.Skip("clingo not available:", err)
	}
	clingoCmd = cmd

	for _, c := range stableModelsCases {
		for _, mode := range []struct {
			semantics Semantics
			want      stableModelsExpectation
		}{{WellFounded{}, c.wf}, {StableBrave{}, c.brave}, {StableCautious{}, c.cautious}} {
			t.Run(c.name+"/"+mode.semantics.String(), func(t *testing.T) {
				report := validateSeparateGraphs(t, ep, "stablemodels", stableModelsPrefixes+c.data,
					stableModelsPrefixes+c.shapes, config{silent: true, semantics: mode.semantics})
				checkStableModelsReport(t, report, mode.want)
			})
		}
	}
}

// clingoUnknownOutput is what clingo 5.8.0 prints when --time-limit interrupts it before it finds a model.
const clingoUnknownOutput = `clingo version 5.8.0
Reading from stdin
Solving...
*** Info : (clingo): INTERRUPTED by signal!
UNKNOWN

TIME LIMIT   : 1
Models       : 0+
Calls        : 1
Time         : 1.000s (Solving: 1.00s 1st Model: 0.00s Unsat: 0.00s)
CPU Time     : 0.999s
`

// TestStableModelsUnknownReport runs cx5 with a fake clingo that always answers UNKNOWN, as an interrupted run
// does. Both stable modes then report unknown, with one result per target (phase 4, step 3).
func TestStableModelsUnknownReport(t *testing.T) {
	if runtime.GOOS == "windows" {
		t.Skip("the fake clingo is a shell script")
	}
	ep := startTestOxigraph(t)

	dir := t.TempDir()
	output := filepath.Join(dir, "unknown.out")
	if err := os.WriteFile(output, []byte(clingoUnknownOutput), 0o644); err != nil {
		t.Fatal(err)
	}
	fake := filepath.Join(dir, "clingo")
	script := "#!/bin/sh\ncat >/dev/null\ncat '" + output + "'\nexit 1\n" // clingo exits with 1 when interrupted
	if err := os.WriteFile(fake, []byte(script), 0o755); err != nil {
		t.Fatal(err)
	}
	oldCmd := clingoCmd
	defer func() { clingoCmd = oldCmd }()
	clingoCmd = []string{fake}

	cx5 := stableModelsCases[slices.IndexFunc(stableModelsCases, func(c stableModelsCase) bool {
		return strings.HasPrefix(c.name, "cx5 ")
	})]
	for _, semantics := range []Semantics{StableBrave{}, StableCautious{}} {
		t.Run(semantics.String(), func(t *testing.T) {
			report := validateSeparateGraphs(t, ep, "stablemodels", stableModelsPrefixes+cx5.data,
				stableModelsPrefixes+cx5.shapes, config{silent: true, semantics: semantics})
			checkStableModelsReport(t, report, stableModelsExpectation{Unknown, "A@a B@a"})
		})
	}
}

// TestStableModelsFiles checks that resources/stable_models/cxN.ttl, the Appendix B cases as single documents
// for the command line (data and shapes together, for --dataIncluded), hold the same triples as the case cxN
// of TestStableModels, and that every such case has its file.
func TestStableModelsFiles(t *testing.T) {
	for _, c := range stableModelsCases {
		name, _, _ := strings.Cut(c.name, " ")
		if !strings.HasPrefix(name, "cx") {
			continue
		}
		t.Run(name, func(t *testing.T) {
			file, err := os.ReadFile(filepath.Join("resources", "stable_models", name+".ttl"))
			if err != nil {
				t.Fatal(err)
			}
			want := stableModelsPrefixes + c.data + "\n" + c.shapes
			if !rdfTurtleIsomorphic(string(file), want) {
				t.Errorf("the file differs from the test case; the test case is:\n%s", want)
			}
		})
	}
}
