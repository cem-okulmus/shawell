package main

import (
	"io"
	"log"
	"reflect"
	"regexp"
	"slices"
	"testing"
)

// allSemantics lists every Semantics, with the helper methods expected of it (section S1.2 of
// supported_semantics_plan.md).
var allSemantics = []struct {
	semantics                      Semantics
	twoValued, supported, cautious bool
}{
	{WellFounded{}, false, false, false},
	{StableBrave{}, true, false, false},
	{StableCautious{}, true, false, true},
	{SupportedBrave{}, true, true, false},
	{SupportedCautious{}, true, true, true},
}

// TestSemanticsMethods checks the helper methods of every Semantics, and that the names returned by String are
// exactly the choices of the --semantics flag, so that every choice selects a semantics and none is missing.
func TestSemanticsMethods(t *testing.T) {
	var names []string
	for _, c := range allSemantics {
		s := c.semantics
		names = append(names, s.String())
		if s.twoValued() != c.twoValued || s.supported() != c.supported || s.cautious() != c.cautious {
			t.Errorf("%s: got twoValued %v, supported %v, cautious %v; want %v, %v, %v", s,
				s.twoValued(), s.supported(), s.cautious(), c.twoValued, c.supported, c.cautious)
		}
	}

	choices := semanticsChoices(t)
	slices.Sort(names)
	slices.Sort(choices)
	if !slices.Equal(names, choices) {
		t.Errorf("String() gives %v, but the --semantics choices are %v", names, choices)
	}
}

// semanticsChoices returns the choices of the --semantics flag, read from the struct tag of cliOptions.
func semanticsChoices(t *testing.T) []string {
	t.Helper()
	field, ok := reflect.TypeOf(cliOptions{}).FieldByName("Semantics")
	if !ok {
		t.Fatal("cliOptions has no field Semantics")
	}
	var choices []string
	for _, m := range regexp.MustCompile(`choice:"([^"]*)"`).FindAllStringSubmatch(string(field.Tag), -1) {
		choices = append(choices, m[1])
	}
	return choices
}

// TestParseSemantics checks that every choice of the --semantics flag, the default included, parses to the
// semantics of that name, and that any other string panics.
func TestParseSemantics(t *testing.T) {
	choices := semanticsChoices(t)
	field, _ := reflect.TypeOf(cliOptions{}).FieldByName("Semantics")
	if def := field.Tag.Get("default"); !slices.Contains(choices, def) {
		t.Errorf("the default %q is not a choice of --semantics", def)
	}
	for _, choice := range choices {
		if s := parseSemantics(choice); s.String() != choice {
			t.Errorf("parseSemantics(%q) returns %s", choice, s)
		}
	}

	// log.Panicln writes the message before it panics; keep it out of the test output
	defer log.SetOutput(log.Writer())
	log.SetOutput(io.Discard)
	for _, bad := range []string{"", "bogus", "stable", "Stable-Brave", "wellfounded", " well-founded"} {
		func() {
			defer func() {
				if recover() == nil {
					t.Errorf("parseSemantics(%q) does not panic", bad)
				}
			}()
			parseSemantics(bad)
		}()
	}
}
