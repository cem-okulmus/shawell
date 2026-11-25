package main

import (
	"testing"
)

// Appendix B of stable_semantics_plan.md as a table test, together with the edge cases of the cautious
// rework. Each case gives the expected status under well-founded, brave and cautious semantics. Under
// well-founded an undefined target counts as a violation, so a case whose target is undefined is invalid.
// Every document here is recursive, so the stable modes go through the clingo calls of answerShacl, and the
// stable verdicts are those of the "Stable models", "Brave" and "Cautious" columns of Appendix B.
//
// The data goes into its own named graph and the shapes are parsed separately (validateSeparateGraphs), so
// the domain of the stable modes is the data's nodes plus the constants of the shapes. This does not cover
// the removal of the shapes graph from the data under --dataIncluded, which happens in main.

const stableModelsPrefixes = `@prefix : <http://example.org/> .
@prefix sh: <http://www.w3.org/ns/shacl#> .
`

// stableModelsData is the data of every Appendix B case except cx7.
const stableModelsData = `:a :q :b .`

type stableModelsCase struct {
	name     string
	data     string
	shapes   string
	wf       ValidationStatus
	brave    ValidationStatus
	cautious ValidationStatus
}

var stableModelsCases = []stableModelsCase{
	{
		name: "cx1 odd loop on an unrelated, untargeted shape",
		data: stableModelsData,
		shapes: `:S a sh:NodeShape ; sh:targetNode :a .
:U a sh:NodeShape ; sh:not :U .`,
		wf: Valid, brave: NoModel, cautious: NoModel,
	},
	{
		name:   "cx2 fine at the target, odd loop at an untargeted node",
		data:   stableModelsData,
		shapes: `:U a sh:NodeShape ; sh:targetNode :a ; sh:or ( [ sh:hasValue :a ] [ sh:not :U ] ) .`,
		wf:     Valid, brave: NoModel, cautious: NoModel,
	},
	{
		name: "cx3 even loop, one target",
		data: stableModelsData,
		shapes: `:A a sh:NodeShape ; sh:targetNode :a ; sh:not :B .
:B a sh:NodeShape ; sh:not :A .`,
		wf: Invalid, brave: Valid, cautious: Invalid,
	},
	{
		name: "cx4 true in every model by case split",
		data: stableModelsData,
		shapes: `:A a sh:NodeShape ; sh:not :B .
:B a sh:NodeShape ; sh:not :A .
:S a sh:NodeShape ; sh:targetNode :a ; sh:or ( :A :B ) .`,
		wf: Invalid, brave: Valid, cautious: Valid,
	},
	{
		name: "cx5 each target brave individually, not jointly",
		data: stableModelsData,
		shapes: `:A a sh:NodeShape ; sh:targetNode :a ; sh:not :B .
:B a sh:NodeShape ; sh:targetNode :a ; sh:not :A .`,
		wf: Invalid, brave: Invalid, cautious: Invalid,
	},
	{
		name: "cx6 odd loop acting as a constraint",
		data: stableModelsData,
		shapes: `:A a sh:NodeShape ; sh:not :B .
:B a sh:NodeShape ; sh:targetNode :a ; sh:not :A .
:K a sh:NodeShape ; sh:or ( [ sh:not :K ] [ sh:not :A ] ) .`,
		wf: Invalid, brave: Valid, cautious: Valid,
	},
	{
		name:   "cx7 odd loop only at nodes without :p",
		data:   `:a :p :a .`,
		shapes: `:U a sh:NodeShape ; sh:targetNode :a ; sh:or ( [ sh:path :p ; sh:minCount 1 ] [ sh:not :U ] ) .`,
		wf:     Valid, brave: Valid, cautious: Valid,
	},
	{
		name: "cx8 odd loop only at a constant in no data triple",
		data: stableModelsData,
		shapes: `:U a sh:NodeShape ; sh:targetNode :a ; sh:or ( [ sh:hasValue :a ] [ sh:hasValue :b ] [ sh:not :U ] ) .
:C a sh:NodeShape ; sh:hasValue :z .`,
		wf: Valid, brave: NoModel, cautious: NoModel,
	},

	// Edge cases of the cautious rework: without targets nothing can fail, so a document with a stable model
	// is valid in both stable modes. Brave call 1 is then the plain program, and cautious skips call 1.
	{
		name:   "no data, so the domain target is empty and no shape has targets",
		data:   ``,
		shapes: `:S a sh:NodeShape ; sh:property [ sh:path :p ; sh:node :S ] .`,
		wf:     Valid, brave: Valid, cautious: Valid,
	},
	{
		name:   "deactivated node shape, its property shape stays active",
		data:   `:a :p :a .`,
		shapes: `:S a sh:NodeShape ; sh:deactivated true ; sh:targetNode :a ; sh:property [ sh:path :p ; sh:node :S ] .`,
		wf:     Valid, brave: Valid, cautious: Valid,
	},
	{
		name:   "no active shape at all",
		data:   `:a :p :a .`,
		shapes: `:S a sh:NodeShape ; sh:deactivated true ; sh:targetNode :a ; sh:not :S .`,
		wf:     Valid, brave: Valid, cautious: Valid,
	},
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
			semantics string
			want      ValidationStatus
		}{{"well-founded", c.wf}, {"stable-brave", c.brave}, {"stable-cautious", c.cautious}} {
			t.Run(c.name+"/"+mode.semantics, func(t *testing.T) {
				got := validateSeparateGraphs(t, ep, "stablemodels", stableModelsPrefixes+c.data,
					stableModelsPrefixes+c.shapes, config{silent: true, omitVR: true, semantics: mode.semantics})
				if got != mode.want {
					t.Errorf("got status %v, want %v", got, mode.want)
				}
			})
		}
	}
}
