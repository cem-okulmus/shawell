package main

import (
	"strings"
	"testing"

	rdf "github.com/cem-okulmus/rdf2go-1"
)

func TestExpandRulesOrKeepsExistingRules(t *testing.T) {
	oldRenameMap, oldReverseMap := renameMap, reverseMap
	oldCount, oldOrVar := theCount, orVar
	defer func() {
		renameMap, reverseMap = oldRenameMap, oldReverseMap
		theCount, orVar = oldCount, oldOrVar
	}()

	renameMap = make(map[rdf.Term]string)
	reverseMap = make(map[string]rdf.Term)
	theCount = 0
	orVar = 1

	value := rdf.Resource{URI: "http://example.com/value"}
	rules := expandRules(
		[]rdf.Term{value},
		[]int{0, 1},
		[]dependency{
			{
				mode: and,
				name: []ShapeRef{{ref: &NodeShape{id: 1}}},
			},
			{
				mode: or,
				name: []ShapeRef{
					{ref: &NodeShape{id: 2}},
					{ref: &NodeShape{id: 3}},
				},
			},
		},
		"Head",
		"focus",
	)

	var headRule *serialisedRule
	for i := range rules {
		if rules[i].head == "Head(focus)" {
			headRule = &rules[i]
			break
		}
	}
	if headRule == nil {
		t.Fatalf("expected expanded rules to keep the primary head rule, got %#v", rules)
	}

	body := strings.Join(headRule.body, ",")
	if !strings.Contains(body, "Shape1(") {
		t.Fatalf("expected primary rule to keep existing dependency body, got %q", body)
	}
	if !strings.Contains(body, "OrShape1(") {
		t.Fatalf("expected primary rule to include or dependency body, got %q", body)
	}
}
