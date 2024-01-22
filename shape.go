package main

import (
	"fmt"
	"log"
	"strings"

	"github.com/fatih/color"

	"github.com/cem-okulmus/rdf2go-1"
)

type Shape interface {
	IsShape()
	String() string
	StringTab(int, bool, bool) string
	ToSparql(fromGraph string, target SparqlQueryFlat) SparqlQuery
	GetIRI() string
	GetDeps() []dependency
	GetTargets() []TargetExpression
	GetValidationTargets() []TargetExpression
	AddIndirectTargets([]TargetIndirect, *PropertyPath)
	IsActive() bool
	IsBlank() bool
	GetQualName() string
	GetLogName() string
}

func TransformToIndirect(input []TargetExpression) (out []TargetIndirect) {
	for i := range input {
		switch typ := input[i].(type) {
		case TargetIndirect:
			out = append(out, typ)
		default:
			out = append(out, TargetIndirect{actual: typ})
		}
	}

	return out
}

// NodeShape
type NodeShape struct {
	id int64 // used for qualified Name
	// NAME OF SHAPE
	IRI rdf2go.Term // the IRI of the subject term defining the shape
	// TARGET EXPRESSION
	target []TargetExpression // the target expression on which to test the shape
	// DATA CONSTRAINTS
	valuetypes   []ValueTypeConstraint    // list of value type const`raints (sh:class, ...)
	valueranges  []ValueRangeConstraint   // constraints on value ranges of matched values
	stringconts  []StringBasedConstraint  // for matched values, string-based constraints
	propairconts []PropertyPairConstraint // propertyConstraints
	properties   []*PropertyShape         // list of property shapes the node must satisfy
	others       []OtherConstraint        // hasValue, in, and closed Constraints
	// LOGICAL CONSTRAINTS
	ands            AndListConstraint     // matched node must pos. match the given lists of shapes
	ors             []OrShapeConstraint   // matched node must conform to one of the given list of shpes
	nots            []NotShapeConstraint  // matched node must not have the given shape
	xones           []XoneShapeConstraint // [look up what the semantics here were]
	nodes           []ShapeRef            // restrict the property universally to a shape
	qualifiedShapes []QSConstraint        // restrict the property existentially to a given number of nodes to be matched
	// MINOR STUFF
	severity    rdf2go.Term            // used in validation
	message     map[string]rdf2go.Term // used in validation
	deactivated bool                   // if true, then shape is ignored in validation
	// DEPENDECY TO OTHER SHAPES
	deps []dependency
	// insideProp
	insideProp *PropertyShape
}

func (n *NodeShape) GetLogName() string {
	return fmt.Sprint("Shape", n.id)
}

func (n *NodeShape) GetQualName() string {
	if n.insideProp != nil {
		return n.insideProp.GetQualName()
	}
	return fmt.Sprint("NodeShape", n.id)
}

func (n *NodeShape) AddIndirectTargets(indirect []TargetIndirect, viaPath *PropertyPath) {
	for i := range indirect {
		tmp := indirect[i]
		if viaPath != nil {
			tmp.indirection = viaPath
		}
		n.target = append(n.target, tmp)
	}
}

func (n *NodeShape) GetConstraints(propertyName string, path PropertyPath, obj string, targetsFromParent *[]TargetExpression) (out []ConstraintInstantiation) {
	var shapeName rdf2go.Term = n.IRI
	// if propertyName != "" {
	// 	shapeName = propertyName
	// } else {
	// 	if n.IsBlank() {
	// 		shapeName = "_:" + n.IRI
	// 	} else {
	// 		shapeName = n.GetIRI()
	// 	}
	// }

	// fmt.Println("Using shapename: ", shapeName)

	var targets []TargetExpression

	if targetsFromParent != nil {
		targets = *targetsFromParent // include the targets inherited from parent
	} else {
		targets = n.GetValidationTargets()
	}

	for i := range n.valuetypes {
		// fmt.Println("ValueType: ", shapeName)
		tmp := ConstraintInstantiation{
			constraint: n.valuetypes[i],
			path:       path,
			obj:        obj,
			shapeName:  shapeName,
			targets:    targets,
			severity:   n.severity,
			message:    n.message,
		}
		out = append(out, tmp)
	}

	for i := range n.valueranges {
		tmp := ConstraintInstantiation{
			constraint: n.valueranges[i],
			path:       path,
			obj:        obj,
			shapeName:  shapeName,
			targets:    targets,
			severity:   n.severity,
			message:    n.message,
		}
		out = append(out, tmp)
	}

	for i := range n.stringconts {
		tmp := ConstraintInstantiation{
			constraint: n.stringconts[i],
			path:       path,
			obj:        obj,
			shapeName:  shapeName,
			targets:    targets,
			severity:   n.severity,
			message:    n.message,
		}
		out = append(out, tmp)
	}

	for i := range n.propairconts {
		tmp := ConstraintInstantiation{
			constraint: n.propairconts[i],
			path:       path,
			obj:        obj,
			shapeName:  shapeName,
			targets:    targets,
			severity:   n.severity,
			message:    n.message,
		}
		out = append(out, tmp)
	}

	for i := range n.others {
		tmp := ConstraintInstantiation{
			constraint: n.others[i],
			path:       path,
			obj:        obj,
			shapeName:  shapeName,
			targets:    targets,
			severity:   n.severity,
			message:    n.message,
		}
		out = append(out, tmp)
	}

	// // propertyShape Constraints
	// for i, p := range n.properties {
	// 	propertyConst := p.GetConstraints(i)
	// 	out = append(out, propertyConst...)
	// }

	return out
}

func (s ShaclDocument) GetValidationReport(n *NodeShape, ep endpoint) (result bool, reports []ValidationResult) {
	constraints := n.GetConstraints("", nil, "?sub", nil)

	if s.debug {
		fmt.Println("NodeShape: ", n.IRI, " number of constraints ", len(constraints))
	}

	// fmt.Println("Started computing all ValidationTargets")

	targets := n.GetValidationTargets()

	// fmt.Println("Computed all ValidationTargets")

	result = true

	// fmt.Println("Started to Compute all Constraints")
	// handle non-logical constraints
	for i := range constraints {
		out, report := constraints[i].SparqlCheck(ep)

		// fmt.Println("Have a constraint of type ", reflect.TypeOf(constraints[i].constraint))
		// fmt.Println("Number of reports produced: ", len(report))

		if !out {
			result = false
		}
		reports = append(reports, report...)
	}

	// fmt.Println("Computed all Constraints")

	// Get Reports for Properties

	// fmt.Println("Computing VRs from Properties")
	for i := range n.properties {
		if s.debug {
			fmt.Println("Passing on targets: ")
		}

		// for i := range targets {
		// 	fmt.Println(targets[i])
		// }

		if s.debug {
			fmt.Println("\n To Property ", n.properties[i].GetIRI())
		}

		out, report := s.GetVRProperty(n.properties[i], ep, &targets, n.GetIRI())
		// fmt.Println("Got VRs from property, ", n.properties[i].shape.GetIRI())

		if s.debug {
			fmt.Println("Checking Reports for Property: ", n.properties[i].name, " num of repoorts ", len(report))
		}

		if !out {
			result = false
		}
		reports = append(reports, report...)
	}

	// fmt.Println("Done Computing VRs from Properties")

	// DO the stuff for logical constraitns

	// fmt.Println("Computing needed Table")
	// TODO: get rid of this and just use condTable, plus searching for the right attribute
	targetQueries := TargetsToQueries(targets)
	neededTable := GetTableForLogicalConstraints(ep, nil, "", targetQueries)

	// fmt.Println("Done Computing needed Table")

	if s.debug {
		fmt.Println("Needed Table", neededTable)
	}

	// AND

	// fmt.Println("Computing Logical VRs for AND")

and:
	for row := range neededTable.IterRows() {
		targetNode := row[0]
		if s.debug {
			fmt.Println("Checking target ", targetNode, " with ", len(n.ors))
		}
		for k := range n.ands.shapes {
			if s.debug {
				fmt.Println("Cheking if target is of shape ", n.ands.shapes[k].name)
			}
			if !s.NodeIsShape(targetNode, n.ands.shapes[k].name) {
				report := ValidationResult{
					focusNode:                 targetNode,
					pathName:                  nil,
					value:                     targetNode,
					sourceShape:               n.IRI,
					sourceConstraintComponent: res(_sh + "AndConstraintComponent"),
					severity:                  n.severity,
					message:                   n.message,
				}

				result = false
				reports = append(reports, report)
				continue and // don't produce multiple entries for the same term
			}
		}
	}

	// fmt.Println("Computing Logical VRs for OR")

	// OR
or:
	for row := range neededTable.IterRows() {
		targetNode := row[0]
		// fmt.Println("Cheking target ", targetNode, " with ", len(n.ors))
		for k := range n.ors {
			currOr := n.ors[k]
			// fmt.Println("At curr Or ", currOr)

			satisfyAtLeastOne := false

			for j := range currOr.shapes {
				// fmt.Println("Cheking if target is of shape ", currOr.shapes[j].name)
				if s.NodeIsShape(targetNode, currOr.shapes[j].name) {
					satisfyAtLeastOne = true
					break // skip early if one is already satisfied
					// fmt.Println("TargetNode ", targetNode, " has shape ", currOr.shapes[j].name)
				}
			}

			if !satisfyAtLeastOne {
				report := ValidationResult{
					focusNode:                 targetNode,
					pathName:                  nil,
					value:                     targetNode,
					sourceShape:               n.IRI,
					sourceConstraintComponent: res(_sh + "OrConstraintComponent"),
					severity:                  n.severity,
					message:                   n.message,
				}

				result = false
				reports = append(reports, report)
				continue or // don't produce multiple entries for the same term
			}
		}
	}

	// NOT

	// fmt.Println("Computing Logical VRs for NOT")

not:
	for row := range neededTable.IterRows() {
		targetNode := row[0]
		for k := range n.nots {
			if s.NodeIsShape(targetNode, n.nots[k].shape.name) {
				report := ValidationResult{
					focusNode:                 targetNode,
					pathName:                  nil,
					value:                     targetNode,
					sourceShape:               n.IRI,
					sourceConstraintComponent: res(_sh + "NotConstraintComponent"),
					severity:                  n.severity,
					message:                   n.message,
				}

				result = false
				reports = append(reports, report)
				continue not // don't produce multile entries for the same term
			}
		}
	}

	// fmt.Println("Computing Logical VRs for XONE")

	// XONE

xone:
	for row := range neededTable.IterRows() {
		targetNode := row[0]
		for k := range n.xones {
			currXone := n.xones[k]

			numSatisfied := 0

			for j := range currXone.shapes {
				if s.NodeIsShape(targetNode, currXone.shapes[j].name) {
					numSatisfied++
				}

				if numSatisfied > 1 {
					break
				}
			}

			if numSatisfied != 1 {
				report := ValidationResult{
					focusNode:                 targetNode,
					pathName:                  nil,
					value:                     targetNode,
					sourceShape:               n.IRI,
					sourceConstraintComponent: res(_sh + "XoneConstraintComponent"),
					severity:                  n.severity,
					message:                   n.message,
				}

				result = false
				reports = append(reports, report)
				continue xone // don't produce multile entries for the same term
			}
		}
	}

	// fmt.Println("Computing Logical VRs for NODE")

	// NODE

node:
	for row := range neededTable.IterRows() {
		targetNode := row[0]
		for k := range n.nodes {
			if !s.NodeIsShape(targetNode, n.nodes[k].name) {

				report := ValidationResult{
					focusNode:                 targetNode,
					pathName:                  nil,
					value:                     targetNode,
					sourceShape:               n.IRI,
					sourceConstraintComponent: res(_sh + "NodeConstraintComponent"),
					severity:                  n.severity,
					message:                   n.message,
				}

				result = false
				reports = append(reports, report)
				continue node // don't produce multile entries for the same term
			}
		}
	}

	return result, reports
}

func (n *NodeShape) GetValidationTargets() []TargetExpression {
	var targets []TargetExpression

	for i := range n.target {
		switch vt := n.target[i].(type) {
		case TargetIndirect:
			// skip
		default:
			targets = append(targets, vt)
		}
	}
	// targets = n.target

	// handle implicit class targets
	if !n.IsBlank() {
		targets = append(targets, TargetClass{class: res(n.GetIRI())})
	}

	return targets
}

func (n *NodeShape) GetTargets() []TargetExpression {
	var targets []TargetExpression

	targets = n.target

	// handle implicit class targets
	if !n.IsBlank() {
		targets = append(targets, TargetClass{class: res(n.GetIRI())})
	}

	return targets
}

func (n *NodeShape) IsActive() bool { return !n.deactivated }

func (n *NodeShape) IsBlank() bool {
	_, ok := n.IRI.(*rdf2go.BlankNode)
	return ok
}

func (n *NodeShape) GetDeps() []dependency { return n.deps }

func (n *NodeShape) GetIRI() string { return n.IRI.RawValue() }

func (n *NodeShape) IsShape() {}

func (n *NodeShape) String() string {
	return n.StringTab(0, false, false)
}

func (n *NodeShape) StringTab(a int, insideProperty bool, debug bool) string {
	tab := "\n" + strings.Repeat("\t", a+2)

	var sb strings.Builder

	bold := color.New(color.Bold)

	if !insideProperty {
		switch n.IRI.(type) {
		case *rdf2go.BlankNode:
			if a == 0 {
				sb.WriteString(bold.Sprint(n.IRI))
				sb.WriteString("(blank)")
			}
		default:
			sb.WriteString(bold.Sprint(n.IRI))
		}
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
			case TargetIndirect:
				if !debug {
					continue
				}
				sb.WriteString("(Indirect)")
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
		sb.WriteString(n.properties[i].StringTab(a+1, true, debug))
		sb.WriteString(tab)
	}

	for i := range n.qualifiedShapes {
		sb.WriteString(n.qualifiedShapes[i].String())
		sb.WriteString(tab)
	}

	// OTHER constraints
	for i := range n.others {
		sb.WriteString(n.others[i].String() + tab)
	}

	// and the rest ...

	if !n.IsActive() {
		sb.WriteString(red.Sprint(_sh, "deactivated true", tab))
	}

	for _, v := range n.message {
		sb.WriteString(fmt.Sprint(_sh, "message ", v.String(), tab))
	}

	return sb.String()
}

// PropertyShape expresses contstraints on properties that go out
// from the target node.
// Note that path can be inverted, encode alternative paths, transitive closure,
// and concatenation of multiple paths, as defined in standard
type PropertyShape struct {
	id            int64        // used for qualifiedName
	name          string       // optional name that can be provided via sh:name
	path          PropertyPath // the outgoing property that is being restricted
	minCount      int          // 0 treated as non-defined
	maxCount      int          // 0 treated as non-defined
	shape         *NodeShape   // underlying struct, used in both types of Shape
	universalOnly bool         // whether the PropertyShape carries only universal constraints
}

func (p *PropertyShape) Nested() bool {
	return len(p.shape.properties) != 0
}

func (p *PropertyShape) GetLogName() string {
	return fmt.Sprint("Shape", p.id)
}

func (p *PropertyShape) GetQualName() string {
	return fmt.Sprint("Property", p.id)
}

func (p *PropertyShape) AddIndirectTargets(indirect []TargetIndirect, viaPath *PropertyPath) {
	p.shape.AddIndirectTargets(indirect, viaPath)
}

func (p *PropertyShape) GetConstraints(num int, targetsFromParent *[]TargetExpression) (out []ConstraintInstantiation) {
	uniqObj := fmt.Sprint("?InnerObj", num)

	// Constraints inherited from NodeShape
	out = append(out, p.shape.GetConstraints(p.name, p.path, uniqObj, targetsFromParent)...)

	return out
}

// var someCount int = 1

func (s ShaclDocument) GetVRProperty(p *PropertyShape, ep endpoint, targetsFromParent *[]TargetExpression, parent string) (result bool, reports []ValidationResult) {
	constraints := p.GetConstraints(0, targetsFromParent)

	var targets []TargetExpression
	if targetsFromParent != nil {
		targets = *targetsFromParent
	} else {
		targets = p.GetValidationTargets()
	}
	// fmt.Println("Started computing all ValidationTargets")

	// fmt.Println("Computed all ValidationTargets")

	// targets = append(targets, *targetsFromParent...)

	// fmt.Println("Started to Compute all Constraints")

	// Adding CardinalityConstraints

	if p.minCount > 0 {
		minConstraint := CardinalityConstraints{
			min: true,
			num: p.minCount,
		}

		minConstraintInstant := ConstraintInstantiation{
			constraint: minConstraint,
			obj:        "?obj",
			path:       p.path,
			shapeName:  p.shape.IRI,
			targets:    targets,
			severity:   p.shape.severity,
			message:    p.shape.message,
		}

		constraints = append(constraints, minConstraintInstant)
	}

	if p.maxCount > -1 {
		maxConstraint := CardinalityConstraints{
			min: false,
			num: p.maxCount,
		}

		maxConstraintInstant := ConstraintInstantiation{
			constraint: maxConstraint,
			obj:        "?obj",
			path:       p.path,
			shapeName:  p.shape.IRI,
			targets:    targets,
			severity:   p.shape.severity,
			message:    p.shape.message,
		}

		constraints = append(constraints, maxConstraintInstant)
	}

	// fmt.Println("Computed all Constraints")

	result = true

	// handle non-logical constraints
	for i := range constraints {

		out, report := constraints[i].SparqlCheck(ep)
		// for k := range report {
		// 	fmt.Println("IN VR Report Property, ", report[k].sourceShape)
		// 	fmt.Println("Strigner: ", report[k])
		// }

		if !out {
			result = false
		}
		reports = append(reports, report...)
	}

	// fmt.Println("Computing VRs from Properties")

	// Get Reports for Properties

	for i := range p.shape.properties {
		if s.debug {
			fmt.Println("Passing on targets: ")
		}

		var newTargets []TargetExpression

		for i := range targets {
			var tmp TargetExpression
			switch tarTyp := targets[i].(type) {
			case TargetIndirect:
				tmp = TargetIndirect{
					indirection: &p.path,
					actual:      targets[i],
					level:       tarTyp.level + 1,
				}
			default:
				tmp = TargetIndirect{
					indirection: &p.path,
					actual:      targets[i],
					level:       0,
				}
			}
			newTargets = append(newTargets, tmp)
			// fmt.Println(targets[i])
		}

		if s.debug {
			fmt.Println("\n To Property ", p.shape.properties[i].GetIRI())
		}
		out, report := s.GetVRProperty(p.shape.properties[i], ep, &newTargets, p.GetIRI())

		// fmt.Println("Got VRs from property, ", p.shape.properties[i].shape.GetIRI())

		if !out {
			result = false
		}
		reports = append(reports, report...)
	}

	// fmt.Println("Done Computing VRs from Properties")

	// DO the stuff for logical constraitns

	// fmt.Println("Property: ", p.name, " AFter removeAbbr")

	// fmt.Println("Computing needed Table")

	targetQueries := TargetsToQueries(targets)
	neededTableBeforeCheck := GetTableForLogicalConstraints(ep, p.path, p.GetQualName(), targetQueries)

	neededTable, ok := neededTableBeforeCheck.(*GroupedTable[rdf2go.Term])
	if !ok {
		log.Panicln("Received non-grouped table from GetTableForLogicalConstraints")
	}

	if s.debug {
		fmt.Println("Needed Table Prop", neededTable)
	}

	// fmt.Println("Done Computing needed Table")

	// fmt.Println("Computing Logical VRs for AND")

	// AND
	for target := range neededTable.IterTargets() {

		// values := strings.Split(neededTable.content[i][1].RawValue(), " ")
		values := neededTable.GetGroupOfTarget(target, 1)

	valuesAND:
		for _, v := range values {
			for k := range p.shape.ands.shapes {
				if s.debug {
					fmt.Println("For the value ", v, " checking if it is shape ", p.shape.ands.shapes[k].ref.GetQualName())
				}
				if !s.NodeIsShape(v, p.shape.ands.shapes[k].name) {
					report := ValidationResult{
						focusNode:                 target,
						pathName:                  p.path,
						value:                     v,
						sourceShape:               p.shape.IRI,
						sourceConstraintComponent: res(_sh + "AndConstraintComponent"),
						severity:                  p.shape.severity,
						message:                   p.shape.message,
					}
					result = false
					reports = append(reports, report)
					continue valuesAND // only one entry per value
				}
			}
		}
	}

	// fmt.Println("Computing Logical VRs for OR")

	// OR
	for target := range neededTable.IterTargets() {
		if s.debug {
			fmt.Println("Cheking target ", target, " with ", len(p.shape.ors))
		}

		values := neededTable.GetGroupOfTarget(target, 1)

	valuesOR:
		for _, v := range values {
			for k := range p.shape.ors {
				currOr := p.shape.ors[k]

				if s.debug {
					fmt.Println("At curr Or ", currOr, " with ", len(values))
				}

				satisfyAtLeastOne := false

				for j := range currOr.shapes {
					if s.debug {
						fmt.Println("Cheking if,", v, " , is of shape ", currOr.shapes[j].name)
					}
					if s.NodeIsShape(v, currOr.shapes[j].name) {
						satisfyAtLeastOne = true
					}
				}

				if !satisfyAtLeastOne {
					report := ValidationResult{
						focusNode:                 target,
						pathName:                  p.path,
						value:                     v,
						sourceShape:               p.shape.IRI,
						sourceConstraintComponent: res(_sh + "OrConstraintComponent"),
						severity:                  p.shape.severity,
						message:                   p.shape.message,
					}

					result = false
					reports = append(reports, report)
					continue valuesOR
				}
			}
		}
	}

	// fmt.Println("Computing Logical VRs for NOT")
	// NOT
	for target := range neededTable.IterTargets() {
		for k := range p.shape.nots {

			values := neededTable.GetGroupOfTarget(target, 1)

			for _, v := range values {
				if s.NodeIsShape(v, p.shape.nots[k].shape.name) {
					report := ValidationResult{
						focusNode:                 target,
						pathName:                  p.path,
						value:                     v,
						sourceShape:               p.shape.IRI,
						sourceConstraintComponent: res(_sh + "NotConstraintComponent"),
						severity:                  p.shape.severity,
						message:                   p.shape.message,
					}

					result = false
					reports = append(reports, report)
				}
			}
		}
	}

	// fmt.Println("Computing Logical VRs for XONE")

	// XONE
	for target := range neededTable.IterTargets() {

		values := neededTable.GetGroupOfTarget(target, 1)

	valuesXOR:
		for _, v := range values {
			for k := range p.shape.xones {
				currXone := p.shape.xones[k]

				numSatisfied := 0
				for j := range currXone.shapes {
					if s.NodeIsShape(v, currXone.shapes[j].name) {
						numSatisfied++
					}

					if numSatisfied > 1 {
						break
					}
				}

				if numSatisfied > 1 {
					report := ValidationResult{
						focusNode:                 target,
						pathName:                  p.path,
						value:                     v,
						sourceShape:               p.shape.IRI,
						sourceConstraintComponent: res(_sh + "XoneConstraintComponent"),
						severity:                  p.shape.severity,
						message:                   p.shape.message,
					}

					result = false
					reports = append(reports, report)
					continue valuesXOR
				}
			}
		}
	}
	// fmt.Println("Computing Logical VRs for NODE")

	// NODE
	// someCount++
	for target := range neededTable.IterTargets() {
		for k := range p.shape.nodes {
			values := neededTable.GetGroupOfTarget(target, 1)

			// fmt.Println("In ", p.GetLogName(), "Lengh of vlues", len(values), "targert", target, "at shape", p.shape.nodes[k].name, " some", someCount)
			for _, v := range values {
				if !s.NodeIsShape(v, p.shape.nodes[k].name) {
					report := ValidationResult{
						focusNode:                 target,
						pathName:                  p.path,
						value:                     v,
						sourceShape:               p.shape.IRI,
						sourceConstraintComponent: res(_sh + "NodeConstraintComponent"),
						severity:                  p.shape.severity,
						message:                   p.shape.message,
					}

					result = false
					reports = append(reports, report)
				}
			}
		}
	}

	// fmt.Println("Computing Logical VRs for QUALIFIED")

	// Qualified
	for target := range neededTable.IterTargets() {
		for k := range p.shape.qualifiedShapes {
			currQS := p.shape.qualifiedShapes[k]
			values := neededTable.GetGroupOfTarget(target, 1)

			numSatisfied := 0

			var siblingsNames []string

			if parent != "" {
				siblings, err := s.DefineSiblingValues(parent, currQS.shape.name)
				check(err)
				if siblings != nil {
					for _, s := range *siblings {
						siblingsNames = append(siblingsNames, s.GetIRI())
					}
				}

			} else {
				siblings, err := s.DefineSiblingValues(p.GetIRI(), currQS.shape.name)
				check(err)
				if siblings != nil {
					for _, s := range *siblings {
						siblingsNames = append(siblingsNames, s.GetIRI())
					}
				}
			}

		outer:
			for _, v := range values {
				if s.NodeIsShape(v, currQS.shape.name) {
					if currQS.disjoint { // for disjoint QSConstraints, first check if not a sibling value
						for _, sib := range siblingsNames {
							if s.NodeIsShape(v, sib) {
								continue outer // don't count any value that satisfies
							}
						}
					}

					numSatisfied++
				}
			}

			if currQS.max != -1 && numSatisfied > currQS.max {
				report := ValidationResult{
					focusNode:                 target,
					pathName:                  p.path,
					sourceShape:               p.shape.IRI,
					sourceConstraintComponent: res(_sh + "QualifiedMaxCountConstraintComponent"),
					severity:                  p.shape.severity,
					message:                   p.shape.message,
				}

				result = false
				reports = append(reports, report)
			}

			if numSatisfied < currQS.min {

				report := ValidationResult{
					focusNode:                 target,
					pathName:                  p.path,
					sourceShape:               p.shape.IRI,
					sourceConstraintComponent: res(_sh + "QualifiedMinCountConstraintComponent"),
					severity:                  p.shape.severity,
					message:                   p.shape.message,
				}

				result = false
				reports = append(reports, report)
			}
		}
	}

	return result, reports
}

func (p *PropertyShape) GetTargets() []TargetExpression { return p.shape.GetTargets() }

func (p *PropertyShape) GetValidationTargets() []TargetExpression {
	return p.shape.GetValidationTargets()
}

func (p *PropertyShape) IsActive() bool { return p.shape.IsActive() }

func (p *PropertyShape) GetDeps() []dependency { return p.shape.deps }

func (p *PropertyShape) IsShape() {}

func (p *PropertyShape) String() string {
	return p.StringTab(0, false, false)
}

func (p *PropertyShape) StringTab(a int, insideNode bool, debug bool) string {
	tab := "\n" + strings.Repeat("\t", a+2)
	var sb strings.Builder

	bold := color.New(color.Bold)
	if !insideNode || !p.IsBlank() {
		if p.name != "" {
			sb.WriteString(bold.Sprint("<", p.name, ">"))
		} else {
			sb.WriteString(bold.Sprint("Property "))
			sb.WriteString(p.shape.IRI.String())
		}
		if p.IsBlank() {
			sb.WriteString("(blank)")
		}
	}
	sb.WriteString(tab)
	sb.WriteString(_sh + "path " + p.path.PropertyString())
	if p.minCount != 0 {
		sb.WriteString(fmt.Sprint(" [ min: ", p.minCount))

		if p.maxCount != -1 {
			sb.WriteString(fmt.Sprint("  max: ", p.maxCount))
		}
		sb.WriteString(" ]")
	} else if p.maxCount != -1 {
		sb.WriteString(fmt.Sprint(" [ min: 0  max: ", p.maxCount, " ]"))
	}

	// sb.WriteString("Rest of PropShape:")
	// sb.WriteString(tab)
	sb.WriteString(p.shape.StringTab(a, true, debug))

	return sb.String()
}

func (p *PropertyShape) GetIRI() string { return p.shape.GetIRI() }

func (p *PropertyShape) IsBlank() bool {
	return p.shape.IsBlank()
}
