package main

import (
	"fmt"
	"strings"

	"github.com/deiu/rdf2go"
	"github.com/fatih/color"
)

type Shape interface {
	IsShape()
	String() string
	ToSparql(target SparqlQueryFlat) SparqlQuery
	ToSparqlFlat(target SparqlQueryFlat) SparqlQueryFlat
	GetIRI() string
	GetDeps() []dependency
	GetTargets() []TargetExpression
	IsActive() bool
	IsBlank() bool
}

// NodeShape
type NodeShape struct {
	IRI             rdf2go.Term             // the IRI of the subject term defining the shape
	valuetypes      []ValueTypeConstraint   // list of value type const`raints (sh:class, ...)
	valueranges     []ValueRangeConstraint  // constraints on value ranges of matched values
	stringconts     []StringBasedConstraint // for matched values, string-based constraints
	propairconts    []PropertyPairConstraint
	properties      []PropertyShape       // list of property shapes the node must satisfy
	ands            AndListConstraint     // matched node must pos. match the given lists of shapes
	ors             []OrShapeConstraint   // matched node must conform to one of the given list of shpes
	nots            []NotShapeConstraint  // matched node must not have the given shape
	xones           []XoneShapeConstraint // [look up what the semantics here were]
	nodes           []ShapeRef            // restrict the property universally to a shape
	qualifiedShapes []QSConstraint        // restrict the property existentially to a given number of nodes to be matched
	target          []TargetExpression    // the target expression on which to test the shape
	hasValue        *rdf2go.Term          // restricts to the specified value
	in              []rdf2go.Term         // restricts to the list of values (replace hasValue with this!)
	closed          bool                  // specifies that the node shape must not have properties other than tested ones
	ignored         []rdf2go.Term         // list of terms to ignore in closed
	severity        *rdf2go.Term          // used in validation
	message         *rdf2go.Term          // used in validation
	deactivated     bool                  // if true, then shape is ignored in validation
	deps            []dependency
}

func (n NodeShape) GetTargets() []TargetExpression { return n.target }

func (n NodeShape) IsActive() bool { return !n.deactivated }

func (n NodeShape) IsBlank() bool {
	_, ok := n.IRI.(*rdf2go.BlankNode)
	return ok
}

func (n NodeShape) GetDeps() []dependency { return n.deps }

func (n NodeShape) GetIRI() string { return n.IRI.RawValue() }

func (n NodeShape) IsShape() {}

func (n NodeShape) String() string {
	return n.StringTab(0)
}

func (n NodeShape) StringTab(a int) string {
	tab := "\n" + strings.Repeat("\t", a+2)

	var sb strings.Builder

	bold := color.New(color.Bold)

	switch n.IRI.(type) {
	case *rdf2go.BlankNode:
		if a == 0 {
			sb.WriteString(bold.Sprint(n.IRI))
			sb.WriteString("(blank)")
		}
	default:
		sb.WriteString(bold.Sprint(n.IRI))
	}

	if len(n.target) > 0 {
		sb.WriteString(tab)
		sb.WriteString("Targets: ")
		for i := range n.target {
			switch n.target[i].(type) {
			case TargetSubjectOf:
				sb.WriteString("(TargetSubjectOf) ")
			case TargetObjectsOf:
				sb.WriteString("(TargetObjectOf) ")
			case TargetClass:
				sb.WriteString("(TargetClass) ")
			case TargetNode:
				sb.WriteString("(TargetNode) ")
			}
			sb.WriteString(n.target[i].String())
		}
	}
	sb.WriteString(tab)

	for i := range n.valuetypes {
		sb.WriteString(n.valuetypes[i].String() + tab)
	}
	for i := range n.valueranges {
		sb.WriteString(n.valueranges[i].String() + tab)
	}
	for i := range n.stringconts {
		sb.WriteString(n.stringconts[i].String() + tab)
	}
	for i := range n.propairconts {
		sb.WriteString(n.propairconts[i].String() + tab)
	}

	if len(n.ands.shapes) > 0 {
		sb.WriteString(n.ands.String() + tab)
	}

	for i := range n.nots {
		sb.WriteString(n.nots[i].String() + tab)
	}

	if len(n.ors) > 0 {
		for i := range n.ors {
			sb.WriteString(n.ors[i].String() + tab)
		}
	}

	if len(n.xones) > 0 {
		for i := range n.xones {
			sb.WriteString(n.xones[i].String() + tab)
		}
	}

	// shape based ones

	var c *color.Color

	red := color.New(color.FgRed).Add(color.Underline)
	green := color.New(color.FgGreen).Add(color.Underline)

	var shapeStrings []string

	for i := range n.nodes {
		if n.nodes[i].negative {
			c = red
		} else {
			c = green
		}

		shapeStrings = append(shapeStrings, c.Sprint(n.nodes[i].name))
	}

	if len(shapeStrings) == 1 {
		sb.WriteString(fmt.Sprint(_sh, "node ", shapeStrings[0], tab))
	} else if len(shapeStrings) > 0 {
		sb.WriteString(fmt.Sprint(_sh, "node (", strings.Join(shapeStrings, " "), ")"))
	}

	for i := range n.properties {
		sb.WriteString(fmt.Sprint(_sh, "property "))
		sb.WriteString(n.properties[i].StringTab(a + 1))
		sb.WriteString(tab)
	}

	for i := range n.qualifiedShapes {
		sb.WriteString(n.qualifiedShapes[i].String())
		sb.WriteString(tab)
	}

	// and the rest ...

	if n.closed {
		sb.WriteString(fmt.Sprint(_sh, "closed ", n.closed, tab))
		var ignoredStrings []string
		for i := range n.ignored {
			ignoredStrings = append(ignoredStrings, n.ignored[i].String())
		}

		sb.WriteString(fmt.Sprint(_sh, "ignoredProperties (", strings.Join(ignoredStrings, " "), ")", tab))
	}

	if n.hasValue != nil {
		sb.WriteString(fmt.Sprint(_sh, "hasValue ", *n.hasValue, tab))
	}

	if !n.IsActive() {
		sb.WriteString(red.Sprint(_sh, "deactivated true", tab))
	}

	var inStrings []string
	for i := range n.in {
		inStrings = append(inStrings, n.in[i].String())
	}

	if len(inStrings) > 0 {
		sb.WriteString(fmt.Sprint(_sh, "in (", strings.Join(inStrings, " "), ")", tab))
	}

	return sb.String()
}

// PropertyShape expresses contstraints on properties that go out
// from the target node.
// Note that path can be inverted, encode alternative paths, transitive closure,
// and concatenation of multiple paths, as defined in standard
type PropertyShape struct {
	name     string       // optional name that can be provided via sh:name
	path     PropertyPath // the outgoing property that is being restricted
	minCount int          // 0 treated as non-defined
	maxCount int          // 0 treated as non-defined
	shape    NodeShape    // underlying struct, used in both types of Shape
}

func (p PropertyShape) GetTargets() []TargetExpression { return p.shape.GetTargets() }

func (p PropertyShape) IsActive() bool { return p.shape.IsActive() }

func (p PropertyShape) GetDeps() []dependency { return p.shape.deps }

func (p PropertyShape) IsShape() {}

func (p PropertyShape) String() string {
	return p.StringTab(0)
}

func (p PropertyShape) StringTab(a int) string {
	tab := "\n" + strings.Repeat("\t", a+2)
	var sb strings.Builder

	bold := color.New(color.Bold)
	if !p.IsBlank() {
		if p.name != "" {
			sb.WriteString(bold.Sprint("<", p.name, ">"))
		} else {
			sb.WriteString(bold.Sprint("Property "))
			sb.WriteString(p.shape.IRI.String())
		}
	}
	sb.WriteString(tab)
	sb.WriteString(_sh + "path " + p.path.PropertyString())
	if p.minCount != 0 {
		sb.WriteString(fmt.Sprint(" [ min: ", p.minCount))

		if p.maxCount != 0 {
			sb.WriteString(fmt.Sprint("  max: ", p.maxCount))
		}
		sb.WriteString(" ]")
	} else if p.maxCount != 0 {
		sb.WriteString(fmt.Sprint(" [ min: 0  max: ", p.maxCount, " ]"))
	}

	// sb.WriteString("Rest of PropShape:")
	// sb.WriteString(tab)
	sb.WriteString(p.shape.StringTab(a))

	return sb.String()
}

func (p PropertyShape) GetIRI() string { return p.shape.GetIRI() }

func (p PropertyShape) IsBlank() bool {
	return p.shape.IsBlank()
}
