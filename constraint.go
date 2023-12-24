package main

import (
	"errors"
	"fmt"
	"log"
	"strconv"
	"strings"

	"github.com/fatih/color"

	"github.com/cem-okulmus/MyRDF2Go"
)

type ValidationReport struct {
	testName    rdf2go.Term // the top-level name of the test
	label       rdf2go.Term // human-readable description of test
	dataGraph   rdf2go.Term // location of datagraph info
	shapesGraph rdf2go.Term //  location of shapesGraph info
	conforms    bool
	results     []ValidationResult // resutls
}

func ExtractValidationReport(graph *rdf2go.Graph) (out *ValidationReport, err error) {
	var tmp ValidationReport
	var parsedResults []ValidationResult
	out = &tmp

	// this part only works for test suite stuff
	_sht := prefixes["sht:"] // living dangerously
	found := graph.One(nil, res(_rdf+"type"), res(_sht+"Validate"))
	if found != nil {
		// fmt.Println("Prefixes: ", prefixes)
		// return nil, errors.New("not a valid test suite file")
		out.testName = found.Subject
	}

	LabelFound := graph.One(found.Subject, res(_rdfs+"label"), nil)
	if LabelFound != nil {
		// fmt.Println("Prefixes: ", prefixes)
		// return nil, errors.New("not a valid test suite file")
		out.label = LabelFound.Object
	}

	dataGraphFound := graph.One(nil, res(_sht+"dataGraph"), nil)
	shapesGraphFound := graph.One(nil, res(_sht+"shapesGraph"), nil)

	if dataGraphFound != nil {
		out.dataGraph = dataGraphFound.Object
	}
	if shapesGraphFound != nil {
		// fmt.Println("Prefixes: ", prefixes)
		// return nil, errors.New("not a valid test suite file")
		out.shapesGraph = shapesGraphFound.Object
	}

	// parse generic ValidationReports

	vr := graph.One(nil, res(_rdf+"type"), res(_sh+"ValidationReport"))
	if vr == nil {
		return nil, errors.New("no validation report defined")
	}

	conformTriple := graph.One(vr.Subject, res(_sh+"conforms"), nil)
	if conformTriple == nil {
		return nil, errors.New("missing sh:conforms in ValidationReport")
	}

	results := graph.All(vr.Subject, res(_sh+"result"), nil)

	for i := range results {
		rTriple := results[i]

		result, err := ExtractValidationResult(rTriple.Object, graph)
		if err != nil {
			return out, err
		}

		parsedResults = append(parsedResults, *result)
	}

	// putting it all together

	out.conforms, err = strconv.ParseBool(conformTriple.Object.RawValue())
	if err != nil {
		return out, err
	}

	out.results = parsedResults

	return out, nil
}

func ExtractValidationResult(sub rdf2go.Term, graph *rdf2go.Graph) (out *ValidationResult, err error) {
	out = &ValidationResult{}
	focusBindings := graph.All(sub, res(_sh+"focusNode"), nil)
	if len(focusBindings) != 1 {
		allBindings := graph.All(sub, nil, nil)
		return out, errors.New(fmt.Sprint(" invalid number of sh:focusNode tripes: ", len(focusBindings), " at sub ", sub, " all bindings ", allBindings))
	}
	out.focusNode = focusBindings[0].Object

	pathBinding := graph.All(sub, res(_sh+"resultPath"), nil)
	if len(pathBinding) > 1 {
		return out, errors.New(fmt.Sprint(" invalid number of sh:resultPath tripes: ", len(focusBindings)))
	} else if len(pathBinding) == 1 {
		out.pathName, err = ExtractPropertyPath(graph, pathBinding[0].Object)
		if err != nil {
			return out, err
		}
	}

	valueBinding := graph.All(sub, res(_sh+"value"), nil)
	if len(valueBinding) > 1 {
		return out, errors.New(fmt.Sprint(" invalid number of sh:value tripes: ", len(focusBindings)))
	} else if len(valueBinding) == 1 {
		out.value = valueBinding[0].Object
	}

	sourceCCBinding := graph.All(sub, res(_sh+"sourceConstraintComponent"), nil)
	if len(sourceCCBinding) != 1 {
		return out, errors.New(fmt.Sprint(" invalid number of sh:sourceConstraintComponent tripes: ", len(sourceCCBinding)))
	}
	out.sourceConstraintComponent = sourceCCBinding[0].Object

	sourceShapeBinding := graph.All(sub, res(_sh+"sourceShape"), nil)
	if len(sourceShapeBinding) > 1 {
		return out, errors.New(fmt.Sprint(" invalid number of sh:sourceShape tripes: ", len(sourceShapeBinding)))
	} else if len(sourceShapeBinding) == 1 {
		out.sourceShape = sourceShapeBinding[0].Object
	}

	// TODO extract Details

	out.message = make(map[string]rdf2go.Term)

	messageBindings := graph.All(sub, res(_sh+"resultMessage"), nil)
	for i := range messageBindings {
		messageLiteral, ok := messageBindings[i].Object.(*rdf2go.Literal)
		if !ok {
			return out, errors.New("invalid value (not a literal) in sh:resultMessage: " + messageBindings[i].Object.String())
		}

		messageVal := messageLiteral
		messageLang := messageLiteral.Language

		if _, ok := out.message[messageLang]; ok {
			return out, errors.New("multiple messages of same lang for sh:message")
		}

		out.message[messageLang] = messageVal
	}

	severityBinding := graph.All(sub, res(_sh+"resultSeverity"), nil)
	if len(severityBinding) != 1 {
		return out, errors.New(fmt.Sprint(" invalid number of sh:resultSeverity tripes: ", len(severityBinding)))
	}
	out.severity = severityBinding[0].Object

	return out, nil
}

func (v ValidationReport) String() string {
	var sb strings.Builder
	_sht := prefixes["sht:"] // living dangerously
	_mf := prefixes["mf:"]   // continuing to live dangerously
	_xsd := prefixes["xsd:"] // continuing to live dangerously

	if v.testName != nil {
		sb.WriteString(v.testName.String() + " \n")
		sb.WriteString("\t<" + _rdf + "type> <" + _sht + "Validate> ;\n")
		sb.WriteString("\t<" + _rdfs + "label> " + v.label.String() + " ;\n")
		sb.WriteString("\t<" + _mf + "action> [\n")

		var dg string
		var sg string

		if v.dataGraph.String() == "<http://www.w3.org/ns/shacl>" {
			dg = "<>"
		} else {
			dg = v.dataGraph.String()
		}

		if v.shapesGraph.String() == "<http://www.w3.org/ns/shacl>" {
			sg = "<>"
		} else {
			sg = v.shapesGraph.String()
		}

		sb.WriteString("\t\t<" + _sht + "dataGraph> " + dg + " ;\n")
		sb.WriteString("\t\t<" + _sht + "shapesGraph> " + sg + " ;\n")
		sb.WriteString("\t] ;\n")

		sb.WriteString("\t<" + _mf + "result> [ \n")
	} else {
		sb.WriteString("[ \n")
	}

	sb.WriteString("\t\t<" + _rdf + "type> <" + _sh + "ValidationReport" + "> ;\n")

	resTerm := rdf2go.NewLiteralWithDatatype(fmt.Sprint(v.conforms), res(_xsd+"boolean"))
	sb.WriteString("\t\t<" + _sh + "conforms> " + resTerm.String() + " ;\n")

	for i := range v.results {
		sb.WriteString(v.results[i].String())
	}
	sb.WriteString("\t] . \n")

	return sb.String()
}

type ValidationResult struct {
	focusNode                 rdf2go.Term
	pathName                  PropertyPath
	value                     rdf2go.Term
	sourceShape               rdf2go.Term
	sourceConstraintComponent rdf2go.Term
	severity                  rdf2go.Term
	message                   map[string]rdf2go.Term // support language tags
	otherValue                rdf2go.Term
	detail                    *ComplexResult
}

type ComplexResult struct{}

func QuotedString(input string) (out bool) {
	if len(input) == 0 {
		return false
	}
	firstChar := string(input[0])
	lastChar := string(input[len(input)-1])
	if lastChar == firstChar && lastChar == "\"" {
		out = true
	}
	return out
}

func (vr ValidationResult) String() string {
	return vr.StringGeneric(false)
}

func (vr ValidationResult) StringComp() string {
	return vr.StringGeneric(true)
}

func (vr ValidationResult) StringGeneric(comparison bool) string {
	var sb strings.Builder

	sb.WriteString("\t\t<" + _sh + "result> [\n")

	sb.WriteString("\t\t\t<" + _rdf + "type> <" + _sh + "ValidationResult> ;\n")

	switch vrType := vr.focusNode.(type) {
	case *rdf2go.Literal:
		if vrType.Datatype != nil {
			switch {
			case vrType.Datatype.RawValue() == _xsd+"string":
				vrType.Datatype = nil
				if !QuotedString(vrType.String()) {
					vrType.Datatype = res(_xsd + "string")
				}

			case vrType.Datatype.RawValue() == _rdf+"langString":
				vrType.Datatype = nil
			}
		}
		sb.WriteString(fmt.Sprint("\t\t\t<", _sh, "focusNode> ", vrType, "; \n"))
	case rdf2go.Literal:
		if vrType.Datatype != nil {
			switch {
			case vrType.Datatype.RawValue() == _xsd+"string":
				vrType.Datatype = nil
				if !QuotedString(vrType.String()) {
					vrType.Datatype = res(_xsd + "string")
				}

			case vrType.Datatype.RawValue() == _rdf+"langString":
				vrType.Datatype = nil
			}
		}
		sb.WriteString(fmt.Sprint("\t\t\t<", _sh, "focusNode> ", vrType, "; \n"))
	default:
		// fmt.Println("Type is actually: ", reflect.TypeOf(vrType))
		sb.WriteString(fmt.Sprint("\t\t\t<", _sh, "focusNode> ", vr.focusNode, "; \n"))
	}
	// sb.WriteString(fmt.Sprint("\t\t\t", _sh, "focusNode ", vr.focusNode, "; \n"))

	if vr.pathName != nil {
		sb.WriteString(fmt.Sprint("\t\t\t<", _sh, "resultPath> ", vr.pathName.PropertyRDF(), "; \n"))
	}

	for _, v := range vr.message {
		sb.WriteString("\t\t\t<" + _sh + "resultMessage> " + v.String() + " ;\n")
	}

	if comparison && vr.otherValue != nil {
		sb.WriteString(fmt.Sprint("\t\t\t<", _sh, "otherValue> ", vr.otherValue.String(), "; \n"))
	}

	// if vr.message != "" {
	// 	sb.WriteString("\t\t\t" + _sh + "resultMessage " + vr.message + " ;\n")
	// }

	if vr.severity == nil {
		sb.WriteString("\t\t\t<" + _sh + "resultSeverity> <" + _sh + "Violation> ;\n")
	} else {
		sb.WriteString("\t\t\t<" + _sh + "resultSeverity> " + vr.severity.String() + " ;\n")
	}
	sb.WriteString(fmt.Sprint("\t\t\t<", _sh, "sourceConstraintComponent> ", vr.sourceConstraintComponent, "; \n"))
	sb.WriteString(fmt.Sprint("\t\t\t<", _sh, "sourceShape> ", vr.sourceShape, "; \n"))

	// fmt.Println("In VR Stringer ", vr.sourceShape)
	if vr.value != nil {
		switch vrType := vr.value.(type) {
		case *rdf2go.BlankNode, rdf2go.BlankNode:
			sb.WriteString(fmt.Sprint("\t\t\t<", _sh, "value> ", vr.value, "; \n"))
		case *rdf2go.Literal:
			if vrType.Datatype != nil {
				switch {
				case vrType.Datatype.RawValue() == _xsd+"string":
					vrType.Datatype = nil
					if !QuotedString(vrType.String()) {
						vrType.Datatype = res(_xsd + "string")
					}

				case vrType.Datatype.RawValue() == _rdf+"langString":
					vrType.Datatype = nil
				}
			}
			sb.WriteString(fmt.Sprint("\t\t\t<", _sh, "value> ", vrType, "; \n"))
		case rdf2go.Literal:
			if vrType.Datatype != nil {
				switch {
				case vrType.Datatype.RawValue() == _xsd+"string":
					vrType.Datatype = nil
					if !QuotedString(vrType.String()) {
						vrType.Datatype = res(_xsd + "string")
					}

				case vrType.Datatype.RawValue() == _rdf+"langString":
					vrType.Datatype = nil
				}
			}
			sb.WriteString(fmt.Sprint("\t\t\t<", _sh, "value> ", vrType, "; \n"))
		default:
			// fmt.Println("Type is actually: ", reflect.TypeOf(vrType))
			sb.WriteString(fmt.Sprint("\t\t\t<", _sh, "value> ", vr.value, "; \n"))
		}
	}
	sb.WriteString("\t\t]; \n")

	return sb.String()
}

// Constraint are used for validation, to allow checking if individual constraints are satisfied
type Constraint interface {
	SparqlCheck(ep endpoint, obj string, path PropertyPath, shapeName rdf2go.Term, target SparqlQueryFlat) (bool, []ValidationResult)
}

type ConstraintInstantiation struct {
	constraint Constraint
	obj        string
	path       PropertyPath
	shapeName  rdf2go.Term
	targets    []TargetExpression
	severity   rdf2go.Term
	message    map[string]rdf2go.Term
}

func (c ConstraintInstantiation) SparqlCheck(ep endpoint) (allValid bool, out []ValidationResult) {
	allValid = true

	for i := range c.targets {

		// fmt.Println("@@@@@@@@@@@@@@@@@@@")
		// fmt.Println("Target:", c.targets[i])
		// fmt.Println("@@@@@@@@@@@@@@@@@@@")

		targetQuery := TargetsToQueries([]TargetExpression{c.targets[i]})
		valid, report := c.constraint.SparqlCheck(ep, c.obj, c.path, c.shapeName, targetQuery[0])
		if !valid {
			allValid = false
			out = append(out, report...)
		}
	}

	for i := range out { // pass on the message and severity
		out[i].message = c.message
		out[i].severity = c.severity
	}

	out = removeDuplicateVR(out)

	return allValid, out
}

// GetShape determins which kind of shape (if at all) the given term is,
// and returns the extracted Shape
func (s *ShaclDocument) GetShape(graph *rdf2go.Graph, term rdf2go.Term) (shape Shape, err error) {
	// check if shape is already known
	if v, ok := s.shapeNames[term.RawValue()]; ok {
		return v, nil
	}

	if IsPropertyShape(graph, term) {
		shape, err = s.GetPropertyShape(graph, term)
	} else {
		shape, err = s.GetNodeShape(graph, term, nil)
	}

	return shape, err
}

// A ShapeRef is used to capture the abilty of Shacl Documents to point to shapes
// even before they are defined. Via lazy dereferencing, we can easily parse these
// and get the pointer to an actual shape at time of translation to Sparql
type ShapeRef struct {
	doc      *ShaclDocument
	name     string //
	ref      Shape
	negative bool // if true, then the reference is on the negation of this shape
}

func (s ShapeRef) GetLogName() string {
	if s.ref != nil {
		return s.ref.GetLogName()
	} else {
		shape := s.doc.shapeNames[s.name]
		return shape.GetLogName()
	}
}

func (s ShapeRef) GetQualName() string {
	if s.ref != nil {
		return s.ref.GetQualName()
	} else {
		shape := s.doc.shapeNames[s.name]
		return shape.GetQualName()
	}
}

func (s ShapeRef) IsBlank() bool {
	if s.ref == nil {
		return false
	}

	return s.ref.IsBlank()
}

var constDatatypes = []string{
	"string",
	"boolean",
	"decimal",
	"integer",
	"double",
	"float",
	"date",
	"time",
	"dateTime",
	"dateTimeStamp",
	"gYear",
	"gMonth",
	"gDay",
	"gYearMonth",
	"gMonthDay",
	"duration",
	"yearMonthDuration",
	"dayTimeDuration",
	"byte",
	"short",
	"int",
	"long",
	"unsignedByte",
	"unsignedShort",
	"unsignedInt",
	"unsignedLong",
	"positiveInteger",
	"nonNegativeInteger",
	"negativeInteger",
	"nonPositiveInteger",
	"hexBinary",
	"base64Binary",
	"anyURI",
	"language",
	"normalizedString",
	"token",
	"NMTOKEN",
	"Name",
	"NCName",
}

// RecognisedDatatype returns true if the term is one of the 36 datatypes that are recognised
// by the RDF 1.1 standard
func RecognisedDatatype(term rdf2go.Term) bool {
	for i := range constDatatypes {
		if term.RawValue() == _xsd+constDatatypes[i] {
			return true
		}
	}
	return false
}

type ValueType int64

const (
	class ValueType = iota
	nodeKind
	datatype
)

type ValueTypeConstraint struct {
	vt   ValueType   // denotes what kind of value type we are dealing with
	term rdf2go.Term // the associated term
	id   int64       // used to create unique references in Sparql translation
}

func (v ValueTypeConstraint) SparqlCheck(ep endpoint, obj string, path PropertyPath, shapeNames rdf2go.Term, target SparqlQueryFlat) (result bool, reports []ValidationResult) {
	// focusNode = obj
	// path = path
	// value .. must be extracted from query
	// sourceShape ... Unkown
	// sourceConstraintComponent .. known

	// fmt.Println("||||||||||||||||||||||||||||||||||||")
	// fmt.Println("RUNNING VALUETYPE SPARQLCHECK")
	// fmt.Println("||||||||||||||||||||||||||||||||||||")

	targetLine := fmt.Sprint("{\n\t", target.StringPrefix(false), "\n\t}")
	result = true
	body := v.SparqlBodyValidation(obj, path)
	uniqObj := fmt.Sprint(obj, v.id)
	var header []string
	focusNodeisValueNode := false

	if obj == "?sub" {
		focusNodeisValueNode = true
		header = []string{obj}
	} else {
		header = []string{"?sub", uniqObj}
	}

	checkQuery := SparqlQuery{
		head:   header,
		target: targetLine,
		body:   []string{body},
		group:  []string{},
		graph:  ep.GetGraph(),
	}

	table := ep.Query(checkQuery)

	iterChan := table.IterRows()

	for row := range iterChan {
		var report ValidationResult
		// row := table.content[i]

		report.focusNode = row[0]
		report.pathName = path
		report.sourceShape = shapeNames
		// fmt.Println("SparqlCHeck VT: ", shapeNames)

		switch v.vt {
		case class:
			report.sourceConstraintComponent = res(_sh + "ClassConstraintComponent")
		case nodeKind:
			report.sourceConstraintComponent = res(_sh + "NodeKindConstraintComponent")
		case datatype:
			report.sourceConstraintComponent = res(_sh + "DatatypeConstraintComponent")
		}

		if focusNodeisValueNode {
			report.value = report.focusNode
		} else {
			report.value = row[1]
		}

		reports = append(reports, report)
		result = false
		// if focusNodeisValueNode {
		// 	break // stop after the first hit in this case
		// }
	}

	return result, reports
}

func (v ValueTypeConstraint) String() string {
	switch v.vt {
	case class:
		return _sh + "class " + v.term.String()
	case nodeKind:
		return _sh + "nodeKind " + v.term.String()
	}
	return _sh + "datatype " + v.term.String()
}

func (v ValueTypeConstraint) SparqlBody(obj string, path PropertyPath) (out string) {
	// uniqObj := obj + strconv.Itoa(int(v.vt)) + v.term.RawValue()
	uniqObj := fmt.Sprint(obj, v.id)
	switch v.vt {
	case class: // UNIVERSAL PROPERTY

		if path != nil { // PROPERTY SHAPE
			out = fmt.Sprint("FILTER NOT EXISTS { ?sub ", path.PropertyString(), " ", uniqObj,
				" . FILTER NOT EXISTS {", uniqObj, " rdf:type/rdfs:subClassOf* ",
				v.term.String(), "} . }.")
		} else { // NODE SHAPE
			out = obj + " rdf:type/rdfs:subClassOf* " + v.term.String() + "."
		}

	case nodeKind: // UNIVERSAL PROPERTY
		if path != nil { // PROPERTY SHAPE

			inner := ""
			switch v.term.RawValue() {
			case _sh + "IRI":
				inner = "FILTER ( !isIRI(" + uniqObj + ") ) ."
			case _sh + "BlankNodeOrIRI":
				inner = "FILTER ( !isIRI(" + uniqObj + ") && !isBlank(" + uniqObj + " ) ) ."
			case _sh + "IRIOrLiteral":
				inner = "FILTER ( !isIRI(" + uniqObj + ") && !isLiteral(" + uniqObj + " ) ) ."
			case _sh + "Literal":
				inner = "FILTER ( !isLiteral(" + uniqObj + ") ) ."
			case _sh + "BlankNode":
				inner = "FILTER ( !isBlank(" + uniqObj + ") ) ."
			case _sh + "BlankNodeOrLiteral":
				inner = "FILTER ( !isBlank(" + uniqObj + ") && !isLiteral(" + uniqObj + ") ) ."
			}

			out = fmt.Sprint("FILTER NOT EXISTS { ?sub ", path.PropertyString(), " ", uniqObj, " . ", inner, "}")

		} else { // NODE SHAPE
			switch v.term.RawValue() {
			case _sh + "IRI":
				out = "FILTER ( isIRI(" + obj + ") ) ."
			case _sh + "BlankNodeOrIRI":
				out = "FILTER ( isIRI(" + obj + ") || isBlank(" + obj + " ) ) ."
			case _sh + "IRIOrLiteral":
				out = "FILTER ( isIRI(" + obj + ") || isLiteral(" + obj + " ) ) ."
			case _sh + "Literal":
				out = "FILTER ( isLiteral(" + obj + ") ) ."
			case _sh + "BlankNode":
				out = "FILTER ( isBlank(" + obj + ") ) ."
			case _sh + "BlankNodeOrLiteral":
				out = "FILTER ( isBlank(" + obj + ") || isLiteral(" + obj + ") ) ."
			}
		}

	case datatype: // UNIVERSAL PROPERTY

		if RecognisedDatatype(v.term) { // recognised data type
			if path != nil {
				b4 := fmt.Sprint("( (datatype(", uniqObj, ") = xsd:string ) || (datatype(", uniqObj, ") != ", v.term.String(), " )) ||")
				if v.term.RawValue() == _xsd+"string" {
					b4 = ""
				}
				// inner := "FILTER ( datatype( " + uniqObj + ") != " + v.term.RawValue() + " ) ."
				inner := fmt.Sprint("FILTER ( ", b4, " ", v.term.String(), "(str(", uniqObj, ")) != ", uniqObj, " ) .")

				out = fmt.Sprint("FILTER NOT EXISTS { ?sub ", path.PropertyString(), " ", uniqObj, " . ", inner, "}")
			} else {
				b4 := fmt.Sprint("( (datatype(", obj, ") = xsd:string ) || (datatype(", obj, ") = ", v.term.String(), " )) &&")
				if v.term.RawValue() == _xsd+"string" {
					b4 = ""
				}
				// out = "FILTER (     datatype( " + obj + ") = " + v.term.RawValue() + " ) ."
				out = fmt.Sprint("FILTER ( ", b4, " ", v.term.String(), "(str(", obj, ")) = ", obj, " ) .")
			}
		} else {
			if path != nil {
				inner := "FILTER ( datatype( " + uniqObj + ") != " + v.term.String() + " ) ."
				// inner := fmt.Sprint("FILTER ( ", v.term.String(), "(str(", uniqObj, ")) != ", obj, " ) .")

				out = fmt.Sprint("FILTER NOT EXISTS { ?sub ", path.PropertyString(), " ", uniqObj, " . ", inner, "}")
			} else {
				out = "FILTER (     datatype( " + obj + ") = " + v.term.String() + " ) ."
				// out = fmt.Sprint("FILTER ( ", v.term.String(), "(str(", obj, ")) = ", obj, " ) .")
			}
		}

	}

	return out
}

func (v ValueTypeConstraint) SparqlBodyValidation(obj string, path PropertyPath) (out string) {
	// uniqObj := obj + strconv.Itoa(int(v.vt)) + v.term.RawValue()
	uniqObj := fmt.Sprint(obj, v.id)
	switch v.vt {
	case class: // UNIVERSAL PROPERTY

		if path != nil { // PROPERTY SHAPE
			out = fmt.Sprint("?sub ", path.PropertyString(), " ", uniqObj,
				" . FILTER NOT EXISTS {", uniqObj, " rdf:type/rdfs:subClassOf* ",
				v.term.String(), "} . ")
		} else { // NODE SHAPE
			out = "FILTER NOT EXISTS {" + obj + " rdf:type/rdfs:subClassOf* " + v.term.String() + ". }"
		}

	case nodeKind: // UNIVERSAL PROPERTY
		if path != nil { // PROPERTY SHAPE

			inner := ""
			switch v.term.RawValue() {
			case _sh + "IRI":
				inner = "FILTER ( !isIRI(" + uniqObj + ") ) ."
			case _sh + "BlankNodeOrIRI":
				inner = "FILTER ( !isIRI(" + uniqObj + ") && !isBlank(" + uniqObj + " ) ) ."
			case _sh + "IRIOrLiteral":
				inner = "FILTER ( !isIRI(" + uniqObj + ") && !isLiteral(" + uniqObj + " ) ) ."
			case _sh + "Literal":
				inner = "FILTER ( !isLiteral(" + uniqObj + ") ) ."
			case _sh + "BlankNode":
				inner = "FILTER ( !isBlank(" + uniqObj + ") ) ."
			case _sh + "BlankNodeOrLiteral":
				inner = "FILTER ( !isBlank(" + uniqObj + ") && !isLiteral(" + uniqObj + ")) ."
			}

			out = fmt.Sprint("?sub ", path.PropertyString(), " ", uniqObj, " . ", inner)

		} else { // NODE SHAPE
			switch v.term.RawValue() {
			case _sh + "IRI":
				out = "FILTER ( !isIRI(" + obj + ") ) ."
			case _sh + "BlankNodeOrIRI":
				out = "FILTER ( !isIRI(" + obj + ") && !isBlank(" + obj + " ) ) ."
			case _sh + "IRIOrLiteral":
				out = "FILTER ( !isIRI(" + obj + ") && !isLiteral(" + obj + " ) ) ."
			case _sh + "Literal":
				out = "FILTER ( !isLiteral(" + obj + ") ) ."
			case _sh + "BlankNode":
				out = "FILTER ( !isBlank(" + obj + ")  ) ."
			case _sh + "BlankNodeOrLiteral":
				out = "FILTER ( !isBlank(" + obj + ") && !isLiteral(" + obj + ") ) ."
			}
		}

	case datatype: // UNIVERSAL PROPERTY

		if RecognisedDatatype(v.term) { //  recognised data types

			if path != nil {
				var inner string
				if v.term.RawValue() == _xsd+"string" {
					inner = "FILTER ( datatype( " + uniqObj + ") != " + v.term.String() + " ) ."
				} else {
					b4b4 := fmt.Sprint("( (datatype(", uniqObj, ") != xsd:string ) && (datatype(", uniqObj, ") != ", v.term.String(), " )) ||")
					b4 := fmt.Sprint("BIND (", v.term.String(), "(str(", uniqObj, ")) AS ?OfType", v.id, " ).\n")

					// inner := "FILTER ( datatype( " + uniqObj + ") != " + v.term.RawValue() + " ) ."
					inner = b4 + fmt.Sprint("FILTER ( ", b4b4, " !BOUND(?OfType", v.id, ")).")
				}

				out = fmt.Sprint(" ?sub ", path.PropertyString(), " ", uniqObj, " . ", inner)
			} else {
				if v.term.RawValue() == _xsd+"string" {
					out = "FILTER ( !isLiteral(" + obj + ") ||  datatype( " + obj + ") != " + v.term.String() + " ) ."
				} else {
					b4b4 := fmt.Sprint("( (datatype(", obj, ") != xsd:string ) && (datatype(", obj, ") != ", v.term.String(), " )) ||")
					b4 := fmt.Sprint("BIND (", v.term.String(), "(str(", obj, ")) AS ?OfType", v.id, " ).\n")
					out = b4 + fmt.Sprint("FILTER ( ", b4b4, " !BOUND(?OfType", v.id, ")).")
				}
			}
		} else {
			if path != nil {
				// b4 := fmt.Sprint("BIND (", v.term.String(), "(str(", uniqObj, ")) AS ?OfType", v.id, " ).\n")

				inner := "FILTER ( !isLiteral(" + uniqObj + ") || datatype( " + uniqObj + ") != " + v.term.String() + " ) ."
				// inner := fmt.Sprint("FILTER ( !BOUND(?OfType", v.id, ")).")

				out = fmt.Sprint(" ?sub ", path.PropertyString(), " ", uniqObj, " . ", inner)
			} else {
				// b4 := fmt.Sprint("BIND (", v.term.String(), "(str(", obj, ")) AS ?OfType", v.id, " ).\n")
				out = "FILTER ( !isLiteral(" + obj + ") ||  datatype( " + obj + ") != " + v.term.String() + " ) ."
				// out = b4 + fmt.Sprint("FILTER ( !BOUND(?OfType", v.id, ")).")
			}
		}

	}

	return out
}

// ExtractValueTypeConstraint gets the input rdf2go graph and a goal term and tries to
// extract a ValueTypeConstraint (sh:class, sh:dataType or sh:dataType) from it
func ExtractValueTypeConstraint(graph *rdf2go.Graph, triple *rdf2go.Triple) (out ValueTypeConstraint, err error) {
	id := getCount()
	switch triple.Predicate.RawValue() {
	case _sh + "class":
		out = ValueTypeConstraint{class, triple.Object, id}
	case _sh + "datatype":
		out = ValueTypeConstraint{datatype, triple.Object, id}
	case _sh + "nodeKind":
		switch triple.Object.RawValue() {
		case _sh + "NodeKind", _sh + "BlankNode", _sh + "IRI",
			_sh + "Literal", _sh + "BlankNodeOrIRI", _sh + "BlankNodeOrLiteral",
			_sh + "IRIOrLiteral": // do nothing since object is of correct type
		default:
			// log.Panicln("Object val of dataType breaks standard ", triple)
			return out, errors.New(fmt.Sprint("Object val of dataType breaks standard ", triple))
		}

		out = ValueTypeConstraint{nodeKind, triple.Object, id}
	default:
		// log.Panicln("Triple is not proper value type constr. ", triple)
		return out, errors.New(fmt.Sprint("Triple is not proper value type constr. ", triple))
	}
	return out, nil
}

type ValueRange int64

const (
	minExcl ValueRange = iota
	maxExcl
	minIncl
	maxInclu
)

type ValueRangeConstraint struct {
	vr    ValueRange  // denotes what kind of value range constraint we have
	value rdf2go.Term // the associated the integer value of the constraint
	id    int64       // used to create unique references in Sparql translation
}

func (v ValueRangeConstraint) String() string {
	switch v.vr {
	case minExcl:
		return fmt.Sprint(_sh, "minExclusive ", v.value)
	case maxExcl:
		return fmt.Sprint(_sh, "maxExclusive ", v.value)
	case minIncl:
		return fmt.Sprint(_sh, "minInclusive ", v.value)
	}
	return fmt.Sprint(_sh, "maxInclusive ", v.value)
}

func (v ValueRangeConstraint) GetSubConstraints() []Constraint {
	return []Constraint{}
}

func (v ValueRangeConstraint) SparqlCheck(ep endpoint, obj string, path PropertyPath, shapeNames rdf2go.Term, target SparqlQueryFlat) (result bool, reports []ValidationResult) {
	// focusNode = obj
	// path = path
	// value .. must be extracted from query
	// sourceShape ... Unkown
	// sourceConstraintComponent .. known

	targetLine := fmt.Sprint("{\n\t", target.StringPrefix(false), "\n\t}")
	result = true
	body := v.SparqlBodyValidation(obj, path)
	uniqObj := fmt.Sprint(obj, v.id)
	var header []string
	focusNodeisValueNode := false

	if obj == "?sub" {
		focusNodeisValueNode = true
		header = []string{obj}
	} else {
		header = []string{"?sub", uniqObj}
	}

	checkQuery := SparqlQuery{
		head:   header,
		target: targetLine,
		body:   []string{body},
		group:  []string{},
		graph:  ep.GetGraph(),
	}

	table := ep.Query(checkQuery)

	iterChan := table.IterRows()

	for row := range iterChan {
		var report ValidationResult
		// row := table.content[i]

		report.focusNode = row[0]
		report.pathName = path
		report.sourceShape = shapeNames

		switch v.vr {
		case minExcl:
			report.sourceConstraintComponent = res(_sh + "MinExclusiveConstraintComponent")
		case maxExcl:
			report.sourceConstraintComponent = res(_sh + "MaxExclusiveConstraintComponent")
		case minIncl:
			report.sourceConstraintComponent = res(_sh + "MinInclusiveConstraintComponent")
		case maxInclu:
			report.sourceConstraintComponent = res(_sh + "MaxInclusiveConstraintComponent")
		}

		if focusNodeisValueNode {
			report.value = report.focusNode
		} else {
			report.value = row[1]
		}

		reports = append(reports, report)
		result = false
		// if focusNodeisValueNode {
		// 	break // stop after the first hit in this case
		// }
	}

	return result, reports
}

func (v ValueRangeConstraint) SparqlBody(obj string, path PropertyPath) (out string) {
	// uniqObj := obj + strconv.Itoa(int(v.vr)) + strconv.Itoa(v.value)
	uniqObj := fmt.Sprint(obj, v.id)

	switch v.vr {
	case minExcl: // UNIVERSAL PROPERTY
		if path != nil {
			inner := fmt.Sprint("BIND( ", v.value, " < ", uniqObj, "  AS ?result", v.id, " ) . FILTER ( !bound(?result", v.id, ") || !(?result", v.id, " )) .")
			out = fmt.Sprint("FILTER NOT EXISTS { ?sub ", path.PropertyString(), " ", uniqObj, " . ", inner, "}")
		} else {
			out = fmt.Sprint("FILTER ( ", v.value, " < ", obj, ") .")
		}
	case maxExcl: // UNIVERSAL PROPERTY
		if path != nil {
			inner := fmt.Sprint("BIND( ", v.value, " > ", uniqObj, "  AS ?result", v.id, " ) . FILTER ( !bound(?result", v.id, ") || !(?result", v.id, " )) .")
			out = fmt.Sprint("FILTER NOT EXISTS { ?sub ", path.PropertyString(), " ", uniqObj, " . ", inner, "}")
		} else {
			out = fmt.Sprint("FILTER ( ", v.value, " > ", obj, ") .")
		}
	case minIncl: // UNIVERSAL PROPERTY
		if path != nil {
			inner := fmt.Sprint("BIND( ", v.value, " <= ", uniqObj, "  AS ?result", v.id, " ) . FILTER ( !bound(?result", v.id, ") || !(?result", v.id, " )) .")
			out = fmt.Sprint("FILTER NOT EXISTS { ?sub ", path.PropertyString(), " ", uniqObj, " . ", inner, "}")
		} else {
			out = fmt.Sprint("FILTER ( ", v.value, " <= ", obj, ") .")
		}

	case maxInclu: // UNIVERSAL PROPERTY

		if path != nil {
			inner := fmt.Sprint("BIND( ", v.value, " >= ", uniqObj, "  AS ?result", v.id, " ) . FILTER ( !bound(?result", v.id, ") || !(?result", v.id, " )) .")
			out = fmt.Sprint("FILTER NOT EXISTS { ?sub ", path.PropertyString(), " ", uniqObj, " . ", inner, "}")
		} else {
			out = fmt.Sprint("FILTER ( ", v.value, " >= ", obj, ") .")
		}
	}

	return out
}

func (v ValueRangeConstraint) SparqlBodyValidation(obj string, path PropertyPath) (out string) {
	// uniqObj := obj + strconv.Itoa(int(v.vt)) + v.term.RawValue()
	uniqObj := fmt.Sprint(obj, v.id)

	var b4 string

	if path != nil {
		b4 = fmt.Sprint("BIND ((", uniqObj, ") > (", v.value, ") AS ?IsNum", v.id, " ).\n")
	} else {
		b4 = fmt.Sprint("BIND ((", obj, ") > (", v.value, ") AS ?IsNum", v.id, " ).\n")
	}

	switch v.vr {
	case minExcl: // UNIVERSAL PROPERTY
		if path != nil {
			inner := b4 + fmt.Sprint("FILTER ( !BOUND(?IsNum", v.id, ") || ", v.value, " >= ", uniqObj, ") .")
			out = fmt.Sprint("?sub ", path.PropertyString(), " ", uniqObj, " . ", inner)
		} else {
			out = b4 + fmt.Sprint("FILTER ( !BOUND(?IsNum", v.id, ") || ", v.value, " >= ", obj, ") .")
		}
	case maxExcl: // UNIVERSAL PROPERTY
		if path != nil {
			inner := b4 + fmt.Sprint("FILTER ( !BOUND(?IsNum", v.id, ") ||  ", v.value, " <= ", uniqObj, ") .")
			out = fmt.Sprint("?sub ", path.PropertyString(), " ", uniqObj, " . ", inner)
		} else {
			out = b4 + fmt.Sprint("FILTER ( !BOUND(?IsNum", v.id, ") ||  ", v.value, " <= ", obj, ") .")
		}
	case minIncl: // UNIVERSAL PROPERTY
		if path != nil {
			inner := b4 + fmt.Sprint("FILTER ( !BOUND(?IsNum", v.id, ") ||  ", v.value, " > ", uniqObj, ") .")
			out = fmt.Sprint("?sub ", path.PropertyString(), " ", uniqObj, " . ", inner)
		} else {
			out = b4 + fmt.Sprint("FILTER ( !BOUND(?IsNum", v.id, ") ||   ", v.value, " > ", obj, ") .")
		}

	case maxInclu: // UNIVERSAL PROPERTY

		if path != nil {
			inner := b4 + fmt.Sprint("FILTER ( !BOUND(?IsNum", v.id, ") ||  ", v.value, " < ", uniqObj, ") .")
			out = fmt.Sprint("?sub ", path.PropertyString(), " ", uniqObj, " . ", inner)
		} else {
			out = b4 + fmt.Sprint("FILTER ( !BOUND(?IsNum", v.id, ") ||  ", v.value, " < ", obj, ") .")
		}
	}

	return out
}

func ExtractValueRangeConstraint(graph *rdf2go.Graph, triple *rdf2go.Triple) (out ValueRangeConstraint, err error) {
	id := getCount()
	switch triple.Predicate.RawValue() {
	case _sh + "minExclusive":
		out = ValueRangeConstraint{minExcl, triple.Object, id}
	case _sh + "maxExclusive":
		out = ValueRangeConstraint{maxExcl, triple.Object, id}
	case _sh + "minInclusive":
		out = ValueRangeConstraint{minIncl, triple.Object, id}
	case _sh + "maxInclusive":
		out = ValueRangeConstraint{maxInclu, triple.Object, id}
	default:
		// log.Panicln("Triple is not proper value range constr. ", triple)
		return out, errors.New(fmt.Sprint("Triple is not proper value range constr. ", triple))

	}

	return out, nil
}

type StringBased int64

const (
	minLen StringBased = iota
	maxLen
	pattern
	langIn
	uniqLang
)

type StringBasedConstraint struct {
	sb         StringBased
	length     int
	pattern    string
	flags      string
	langs      []string
	uniqueLang bool  // property shapes ony
	id         int64 // used to create unique references in Sparql translation
}

func (v StringBasedConstraint) GetSubConstraints() []Constraint {
	return []Constraint{}
}

func (v StringBasedConstraint) SparqlCheck(ep endpoint, obj string, path PropertyPath, shapeNames rdf2go.Term, target SparqlQueryFlat) (result bool, reports []ValidationResult) {
	// focusNode = obj
	// path = path
	// value .. must be extracted from query
	// sourceShape ... Unkown
	// sourceConstraintComponent .. known

	uniqLangCase := false
	switch v.sb {
	case uniqLang:
		uniqLangCase = true
	}

	targetLine := fmt.Sprint("{\n\t", target.StringPrefix(false), "\n\t}")
	result = true
	body := v.SparqlBodyValidation(obj, path)
	uniqObj := fmt.Sprint(obj, v.id)
	var header []string
	focusNodeisValueNode := false

	if obj == "?sub" {
		focusNodeisValueNode = true
		header = []string{obj}
	} else if uniqLangCase {
		header = []string{"?sub", "( lang(" + uniqObj + ") AS ?lang) "}
	} else {
		header = []string{"?sub", uniqObj}
	}

	checkQuery := SparqlQuery{
		head:   header,
		target: targetLine,
		body:   []string{body},
		group:  []string{},
		graph:  ep.GetGraph(),
	}

	table := ep.Query(checkQuery)
	iterChan := table.IterRows()

	for row := range iterChan {
		var report ValidationResult
		// row := table.content[i]

		report.focusNode = row[0]
		report.pathName = path
		report.sourceShape = shapeNames

		switch v.sb {
		case minLen:
			report.sourceConstraintComponent = res(_sh + "MinLengthConstraintComponent")
		case maxLen:
			report.sourceConstraintComponent = res(_sh + "MaxLengthConstraintComponent")
		case pattern:
			report.sourceConstraintComponent = res(_sh + "PatternConstraintComponent")
		case langIn:
			report.sourceConstraintComponent = res(_sh + "LanguageInConstraintComponent")
		case uniqLang:
			report.sourceConstraintComponent = res(_sh + "UniqueLangConstraintComponent")
		}

		if focusNodeisValueNode {
			report.value = report.focusNode
		} else if uniqLangCase {
			report.otherValue = row[1]
		} else {
			report.value = row[1]
		}

		reports = append(reports, report)
		result = false
		// if focusNodeisValueNode {
		// 	break // stop after the first hit in this case
		// }
	}

	return result, reports
}

func (v StringBasedConstraint) String() string {
	switch v.sb {
	case minLen:
		return fmt.Sprint(_sh, "minLength ", v.length)
	case maxLen:
		return fmt.Sprint(_sh, "maxLength ", v.length)
	case pattern:
		return fmt.Sprint(_sh, "pattern ", v.pattern)
	case langIn:
		return fmt.Sprint(_sh, "languageIn (", strings.Join(v.langs, " "), ")")
	}
	return fmt.Sprint(_sh, "uniqueLang ", v.uniqueLang)
}

func (v StringBasedConstraint) SparqlBody(obj string, path PropertyPath) (out string) {
	// uniqObj := obj + strconv.Itoa(int(v.sb)) + strconv.Itoa(v.length) + v.pattern + v.flags
	uniqObj := fmt.Sprint(obj, v.id)

	switch v.sb {
	case minLen: // UNIVERSAL PROPERTY
		if path != nil { // PROPERTY SHAPE
			inner := fmt.Sprint("FILTER (STRLEN(str(", uniqObj, ")) < ", v.length, ") .")
			out = fmt.Sprint("FILTER NOT EXISTS { ?sub ", path.PropertyString(), " ", uniqObj, " . ", inner, "}")
		} else { // NODE SHAPE
			out = fmt.Sprint("FILTER (STRLEN(str(", obj, ")) >= ", v.length, ") .")
		}
	case maxLen: // UNIVERSAL PROPERTY

		if path != nil { // PROPERTY SHAPE
			inner := fmt.Sprint("FILTER (STRLEN(str(", uniqObj, ")) > ", v.length, ") .")
			out = fmt.Sprint("FILTER NOT EXISTS { ?sub ", path.PropertyString(), " ", uniqObj, " . ", inner, "}")
		} else { // NODE SHAPE
			out = fmt.Sprint("FILTER (STRLEN(str(", obj, ")) <= ", v.length, ") .")
		}

	case pattern: // UNIVERSAL PROPERTY
		// v.pattern = strings.ReplaceAll(v.pattern, "\\", "\\\\")
		if path != nil {
			inner := ""
			if len(v.flags) != 0 {
				inner = fmt.Sprint("FILTER (isBlank(" + uniqObj + ") || !regex(str(" + uniqObj + "), " + v.pattern + ", " + v.flags + ") )")
			} else {
				inner = fmt.Sprint("FILTER (isBlank(" + uniqObj + ") || !regex(str(" + uniqObj + "), " + v.pattern + ") )")
			}

			out = fmt.Sprint("FILTER NOT EXISTS { ?sub ", path.PropertyString(), " ", uniqObj, " . ", inner, "}")
		} else {
			if len(v.flags) != 0 {
				out = fmt.Sprint("FILTER (!isBlank(" + obj + ") && regex(str(" + obj + "), " + v.pattern + ", " + v.flags + ") )")
			} else {
				out = fmt.Sprint("FILTER (!isBlank(" + obj + ") && regex(str(" + obj + "), " + v.pattern + ") )")
			}
		}
	case langIn: // Universal Property

		if path != nil { // Property Shape

			var langChecks []string

			for i := range v.langs {
				langChecks = append(langChecks, fmt.Sprint("langMatches(lang(", uniqObj, "),", v.langs[i], ")"))
			}
			inner := fmt.Sprint("FILTER (  ", strings.Join(langChecks, " || "), " ) .")
			out = fmt.Sprint("FILTER NOT EXISTS { ?sub ", path.PropertyString(), " ", uniqObj, " . ", inner, "}")
		} else { // Node Shape

			var langChecks []string

			for i := range v.langs {
				langChecks = append(langChecks, fmt.Sprint("langMatches(lang(", obj, "),", v.langs[i], ")"))
			}

			out = fmt.Sprint("FILTER (  ", strings.Join(langChecks, " || "), "   ) .")
		}
	case uniqLang: // Universal Property

		if path != nil { // Property Shape

			innerInner := fmt.Sprint(
				"BIND(lang(", uniqObj, ") AS ?lang1", v.id, "). ",
				"BIND(lang(", uniqObj, "B) AS ?lang2", v.id, ").",
				"FILTER ( ", uniqObj, " != ", uniqObj, "B && ?lang2", v.id, " = ?lang1", v.id, " && ?lang1", v.id, " != \"\").")

			inner := fmt.Sprint(" ?sub ", path.PropertyString(), " ", uniqObj, "B .", innerInner)

			out = fmt.Sprint("FILTER NOT EXISTS { ?sub ", path.PropertyString(), " ", uniqObj, " . ", inner, "}")
		} else {
			out = "" // nothing to do for NodeShape, since it cannot violate this constraint
		}

	}

	return out
}

func (v StringBasedConstraint) SparqlBodyValidation(obj string, path PropertyPath) (out string) {
	// uniqObj := obj + strconv.Itoa(int(v.sb)) + strconv.Itoa(v.length) + v.pattern + v.flags
	uniqObj := fmt.Sprint(obj, v.id)

	switch v.sb {
	case minLen: // UNIVERSAL PROPERTY
		if path != nil { // PROPERTY SHAPE
			inner := fmt.Sprint("FILTER ( isBlank(", uniqObj, ") || STRLEN(str(", uniqObj, ")) < ", v.length, ") .")
			out = fmt.Sprint("?sub ", path.PropertyString(), " ", uniqObj, " . ", inner)
		} else { // NODE SHAPE
			out = fmt.Sprint("FILTER ( isBlank(", obj, ")  || STRLEN(str(", obj, ")) < ", v.length, ") .")
		}
	case maxLen: // UNIVERSAL PROPERTY

		if path != nil { // PROPERTY SHAPE
			inner := fmt.Sprint("FILTER ( isBlank(", uniqObj, ") || STRLEN(str(", uniqObj, ")) > ", v.length, ") .")
			out = fmt.Sprint("?sub ", path.PropertyString(), " ", uniqObj, " . ", inner)
		} else { // NODE SHAPE
			out = fmt.Sprint("FILTER ( isBlank(", obj, ") || STRLEN(str(", obj, ")) > ", v.length, ") .")
		}

	case pattern: // UNIVERSAL PROPERTY
		// v.pattern = strings.ReplaceAll(v.pattern, "\\", "\\\\")
		if path != nil {
			inner := ""
			if len(v.flags) != 0 {
				inner = fmt.Sprint("FILTER (isBlank(" + uniqObj + ") || !regex(str(" + uniqObj + "), " + v.pattern + ", " + v.flags + ") )")
			} else {
				inner = fmt.Sprint("FILTER (isBlank(" + uniqObj + ") || !regex(str(" + uniqObj + "), " + v.pattern + ") )")
			}

			out = fmt.Sprint("?sub ", path.PropertyString(), " ", uniqObj, " . ", inner)
		} else {
			if len(v.flags) != 0 {
				out = fmt.Sprint("FILTER (isBlank(" + obj + ") || !regex(str(" + obj + "), " + v.pattern + ", " + v.flags + ") )")
			} else {
				out = fmt.Sprint("FILTER (isBlank(" + obj + ") || !regex(str(" + obj + "), " + v.pattern + ") )")
			}
		}
	case langIn: // Universal Propety

		if path != nil { // Property Shape

			var langChecks []string

			for i := range v.langs {
				langChecks = append(langChecks, fmt.Sprint("!langMatches(lang(", uniqObj, "),", v.langs[i], ")"))
			}

			b4 := fmt.Sprint("BIND (lang(", uniqObj, ") AS ?lang", v.id, ").\n")
			inner := b4 + fmt.Sprint("FILTER ( !bound(?lang", v.id, ") || ", strings.Join(langChecks, " && "), "  ) .")
			out = fmt.Sprint("?sub ", path.PropertyString(), " ", uniqObj, " . ", inner)
		} else { // Node Shape

			var langChecks []string

			for i := range v.langs {
				langChecks = append(langChecks, fmt.Sprint("!langMatches(lang(", obj, "),", v.langs[i], ")"))
			}

			b4 := fmt.Sprint("BIND (lang(", obj, ") AS ?lang", v.id, ").\n")
			out = b4 + fmt.Sprint("FILTER ( !bound(?lang", v.id, ") || ", strings.Join(langChecks, " &&"), "  ) .")
		}
	case uniqLang:
		if path != nil { // Property Shape
			innerInner := fmt.Sprint(
				"BIND(lang(", uniqObj, ") AS ?lang1", v.id, "). ",
				"BIND(lang(", uniqObj, "B) AS ?lang2", v.id, ").",
				"FILTER ( ", uniqObj, " != ", uniqObj, "B && ?lang2", v.id, " = ?lang1", v.id, " && ?lang1", v.id, " != \"\").")

			inner := fmt.Sprint(" ?sub ", path.PropertyString(), " ", uniqObj, "B .", innerInner)

			out = fmt.Sprint("?sub ", path.PropertyString(), " ", uniqObj, " . ", inner)
		}
	}

	return out
}

func ExtractStringBasedConstraint(graph *rdf2go.Graph, triple *rdf2go.Triple) (out StringBasedConstraint, err error) {
	id := getCount()
	switch triple.Predicate.RawValue() {
	case _sh + "minLength":
		val, err := strconv.Atoi(triple.Object.RawValue())
		check(err)
		out = StringBasedConstraint{sb: minLen, length: val, id: id}
	case _sh + "maxLength":
		val, err := strconv.Atoi(triple.Object.RawValue())
		check(err)
		out = StringBasedConstraint{sb: maxLen, length: val, id: id}
	case _sh + "pattern":
		// check if "sh:flags" defined:
		flags := graph.One(triple.Subject, res(_sh+"flags"), nil)
		if flags != nil {
			out = StringBasedConstraint{
				sb:      pattern,
				pattern: triple.Object.String(),
				flags:   flags.Object.String(),
				id:      id,
			}
		} else {
			out = StringBasedConstraint{
				sb:      pattern,
				pattern: triple.Object.String(),
				id:      id,
			}
		}

	case _sh + "uniqueLang":
		var val bool
		tmp := triple.Object.RawValue()
		switch tmp {
		case "true":
			val = true
		case "false":
			val = false
		default:
			// log.Panicln("StringBasedConstraint not using proper value: ", triple)
			return out, errors.New(fmt.Sprint("StringBasedConstraint not using proper value: ", triple))
		}

		out = StringBasedConstraint{
			sb:         uniqLang,
			uniqueLang: val,
			id:         id,
		}
	case _sh + "languageIn":

		listTriples := graph.All(triple.Object, nil, nil)

		foundFirst := false
		foundRest := false
		foundNil := false

		for i := 0; i < len(listTriples); i++ {
			switch listTriples[i].Predicate.RawValue() {
			case _rdf + "nil":
				foundNil = true
			case _rdf + "first":
				foundFirst = true

				out.langs = append(out.langs, listTriples[i].Object.String())
			case _rdf + "rest":
				foundRest = true
				newTriples := graph.All(listTriples[i].Object, nil, nil)
				listTriples = append(listTriples, newTriples...) // wonder if this works
			}
		}

		if !foundFirst && !foundRest && !foundNil {
			// log.Panicln("Invalid languageIn Constraint structure in graph")
			return out, errors.New("invalid languageIn Constraint structure in graph")
		}

		out.id = id
		out.sb = langIn
	default:
		// log.Panicln()
		return out, errors.New(fmt.Sprint("triple is not proper value range constr. ", triple))
	}

	return out, nil
}

type PropertyPair int64

const (
	equals PropertyPair = iota
	disjoint
	lessThan
	lessThanOrEquals
)

type PropertyPairConstraint struct {
	pp   PropertyPair
	term rdf2go.Term
	id   int64 // used to create unique references in Sparql translation
}

func (v PropertyPairConstraint) GetSubConstraints() []Constraint {
	return []Constraint{}
}

func (v PropertyPairConstraint) SparqlCheck(ep endpoint, obj string, path PropertyPath, shapeNames rdf2go.Term, target SparqlQueryFlat) (result bool, reports []ValidationResult) {
	// focusNode = obj
	// path = path
	// value .. must be extracted from query
	// sourceShape ... Unkown
	// sourceConstraintComponent .. known

	inEqualsCase := false
	lessThanCase := false
	switch v.pp {
	case equals:
		inEqualsCase = true
	case lessThan, lessThanOrEquals:
		lessThanCase = true
	}

	targetLine := fmt.Sprint("{\n\t", target.StringPrefix(false), "\n\t}")
	result = true
	body := v.SparqlBodyValidation(obj, path)
	uniqObj := fmt.Sprint(obj, v.id)
	var header []string

	if path == nil {
		header = []string{"?sub", uniqObj} // only consider equals and disjoint
	} else {
		if inEqualsCase {
			header = []string{"?sub", uniqObj + "A", uniqObj + "B"}
		} else if lessThanCase {
			header = []string{"?sub", uniqObj, uniqObj + "B"}
		} else {
			header = []string{"?sub", uniqObj}
		}
	}

	checkQuery := SparqlQuery{
		head:   header,
		target: targetLine,
		body:   []string{body},
		group:  []string{},
		graph:  ep.GetGraph(),
	}

	table := ep.Query(checkQuery)
	iterChan := table.IterRows()

	for row := range iterChan {
		var report ValidationResult
		// row := table.content[i]

		report.focusNode = row[0]
		report.pathName = path
		report.sourceShape = shapeNames

		switch v.pp {
		case equals:
			report.sourceConstraintComponent = res(_sh + "EqualsConstraintComponent")
		case disjoint:
			report.sourceConstraintComponent = res(_sh + "DisjointConstraintComponent")
		case lessThan:
			report.sourceConstraintComponent = res(_sh + "LessThanConstraintComponent")
		case lessThanOrEquals:
			report.sourceConstraintComponent = res(_sh + "LessThanOrEqualsConstraintComponent")
		}

		if inEqualsCase && path != nil {

			var haveValueA bool
			var haveValueB bool

			// check if current value node already Reported
			var nodeToCheckA rdf2go.Term
			var nodeToCheckB rdf2go.Term

			_, ok := row[1].(rdf2go.BlankNode)
			if !ok {
				haveValueA = true
				nodeToCheckA = row[1]
			}

			_, ok = row[2].(rdf2go.BlankNode)
			if !ok {
				haveValueB = true
				nodeToCheckB = row[2]
			}

			if haveValueA {
				reportA := report
				reportA.value = nodeToCheckA
				reports = append(reports, reportA)
			}

			if haveValueB {
				reportB := report
				reportB.value = nodeToCheckB
				reports = append(reports, reportB)
			}

			result = !haveValueA && !haveValueB

		} else if inEqualsCase && path == nil {

			var nodeToCheck rdf2go.Term

			_, ok := row[1].(rdf2go.BlankNode)
			if ok {
				nodeToCheck = report.focusNode
			} else {
				nodeToCheck = row[1]
			}

			report.value = nodeToCheck
			reports = append(reports, report)
			result = false
		} else {
			report.value = row[1]

			if lessThanCase {
				report.otherValue = row[2]
			}

			reports = append(reports, report)
			result = false
		}

	}

	return result, reports
}

func (v PropertyPairConstraint) String() string {
	switch v.pp {
	case equals:
		return fmt.Sprint(_sh, "equals ", v.term)
	case disjoint:
		return fmt.Sprint(_sh, "disjoint ", v.term)
	case lessThan:
		return fmt.Sprint(_sh, "lessThan ", v.term)
	}
	return fmt.Sprint(_sh, "lessThanOrEquals ", v.term)
}

// SparqlBody produces the statements to be added to the body of a Sparql query
// to capture the meaning of the corresponding SHACL constraint. obj provides the object to be
// constrained, this will differ between node and property shapes, and path  is non-empty if
// called by a property shape.
func (v PropertyPairConstraint) SparqlBody(obj string, path PropertyPath) (out string) {
	// uniqObj := obj + strconv.Itoa(int(v.pp)) + v.term.RawValue()
	uniqObj := fmt.Sprint(obj, v.id)

	switch v.pp {
	case equals: // Universal Property: set equality between value nodes and objects reachable via equals
		other := v.term.String()
		if path != nil {

			// implemented via two not exists: one testing that A ⊆ B and another testing B ⊆ A
			out1 := fmt.Sprint("FILTER NOT EXISTS { ?sub ", other, " ", uniqObj, "A . FILTER NOT EXISTS { ?sub ", path.PropertyString(), " ", uniqObj, "A .} . } .\n")
			out2 := fmt.Sprint("FILTER NOT EXISTS { ?sub ", path.PropertyString(), " ", uniqObj, "B . FILTER NOT EXISTS { ?sub ", other, " ", uniqObj, "B .} . } .")
			out = out1 + out2
		} else {
			b4 := fmt.Sprint(obj, " ", other, " ", obj, ". ")
			out = fmt.Sprint(b4, " FILTER NOT EXISTS { ", obj, " ", other, " ", uniqObj, " . FILTER ( ", obj, " != ", uniqObj, " ) . } .")
		}

	case disjoint: // Universal Property: set of value nodes and those reachable by disjoint must be distinct
		other := v.term.String()
		if path != nil {
			// implemented via one exists: one testing that A∩B = ∅
			out = fmt.Sprint("FILTER NOT EXISTS { ?sub ", path.PropertyString(), " ", uniqObj, " . ?sub ", other, " ", uniqObj, " . } .")
		} else { // NON-STANDARD: implementing this since the Test Suite supports it (for some reason)
			out = fmt.Sprint("FILTER NOT EXISTS { ", obj, " ", other, " ", uniqObj, " . FILTER ( ", obj, " = ", uniqObj, ") .  } .")
		}

	case lessThan: // Universal: there is no value node with value higher or equal than those reachable by lessThan
		// if path == nil {
		// 	log.Panicln("Standard Violating and unsupported use of sh:lessThan inside  NodeShapde.")
		// }

		other := v.term.String()

		// implemented via one exists: one testing that A∩B = ∅
		out = fmt.Sprint("FILTER NOT EXISTS { ?sub ", path.PropertyString(), " ", uniqObj, " . ?sub ", other, " ", uniqObj, "B . BIND ( ", uniqObj, " < ", uniqObj, "B AS ?result", v.id, ") .  FILTER (!bound(?result", v.id, ") || !(?result", v.id, ")) .  } .")
	case lessThanOrEquals: // Universal: there is no value node with value higher than those reachable by lessThan
		// if path == nil {
		// 	log.Panicln("Standard Violating and unsupported use of sh:lessThanOrEquals inside  NodeShapde.")
		// }
		other := v.term.String()

		// implemented via one exists: one testing that A∩B = ∅
		out = fmt.Sprint("FILTER NOT EXISTS { ?sub ", path.PropertyString(), " ", uniqObj, " . ?sub ", other, " ", uniqObj, "B . BIND ( ", uniqObj, " <= ", uniqObj, "B AS ?result", v.id, ") .  FILTER (!bound(?result", v.id, ") || !(?result", v.id, ")) .  } .")
	}

	return out
}

func (v PropertyPairConstraint) SparqlBodyValidation(obj string, path PropertyPath) (out string) {
	// uniqObj := obj + strconv.Itoa(int(v.pp)) + v.term.RawValue()
	uniqObj := fmt.Sprint(obj, v.id)

	switch v.pp {
	case equals: // Universal Property: set equality between value nodes and objects reachable via equals
		other := v.term.String()
		if path != nil {

			// implemented via two not exists: one testing that A ⊆ B and another testing B ⊆ A
			out1 := fmt.Sprint("?sub ", other, " ", uniqObj, "A . FILTER NOT EXISTS { ?sub ", path.PropertyString(), " ", uniqObj, "A .} . ")
			out2 := fmt.Sprint("?sub ", path.PropertyString(), " ", uniqObj, "B . FILTER NOT EXISTS { ?sub ", other, " ", uniqObj, "B .} . ")

			out = fmt.Sprint("OPTIONAL { ", out1, "} OPTIONAL {", out2, " } FILTER ( BOUND (", uniqObj, "A) || BOUND(", uniqObj, "B) ) ")
		} else { // NON-STANDARD: implementing this since the Test Suite supports it (for some reason)

			inner := fmt.Sprint("FILTER ( !BOUND(", uniqObj, ") || ", uniqObj, " != ", obj, "  ).")
			out1 := fmt.Sprint(obj, " ", other, " ", uniqObj, " . ")

			out = fmt.Sprint("OPTIONAL {", out1, "} ", inner)
		}

	case disjoint: // Universal Property: set of value nodes and those reachable by disjoint must be distinct
		other := v.term.String()
		if path != nil {
			// implemented via one exists: one testing that A∩B = ∅
			out = fmt.Sprint("?sub ", path.PropertyString(), " ", uniqObj, " . ?sub ", other, " ", uniqObj, " .")
		} else { // NON-STANDARD: implementing this since the Test Suite supports it (for some reason)
			inner := fmt.Sprint("FILTER ( ", uniqObj, " = ", obj, "  ).")
			out = fmt.Sprint(obj, " ", other, " ", uniqObj, ". ", inner)
		}

	case lessThan: // Universal: there is no value node with value higher or equal than those reachable by lessThan
		// if path == nil {
		// 	log.Panicln("Standard Violating and unsupported use of sh:lessThan inside  NodeShapde.")
		// }
		other := v.term.String()

		// implemented via one exists: one testing that A∩B = ∅
		// out = fmt.Sprint("?sub ", other, " ", uniqObj, " . FILTER( ", other, " <= ", obj, " ) .")

		out = fmt.Sprint("?sub ", path.PropertyString(), " ", uniqObj, " . ?sub ", other, " ", uniqObj, "B . BIND ( ", uniqObj, " < ", uniqObj, "B AS ?result", v.id, ") .  FILTER (!bound(?result", v.id, ") || !(?result", v.id, ")) .")
	case lessThanOrEquals: // Universal: there is no value node with value higher than those reachable by lessThan
		// if path == nil {
		// 	log.Panicln("Standard Violating and unsupported use of sh:lessThanOrEquals inside  NodeShapde.")
		// }
		other := v.term.String()

		// implemented via one exists: one testing that A∩B = ∅
		// out = fmt.Sprint("?sub ", other, " ", uniqObj, " . FILTER( ", other, " < ", obj, " )  .")

		out = fmt.Sprint("?sub ", path.PropertyString(), " ", uniqObj, " . ?sub ", other, " ", uniqObj, "B . BIND ( ", uniqObj, " <= ", uniqObj, "B AS ?result", v.id, ") .  FILTER (!bound(?result", v.id, ") || !(?result", v.id, ")) .")
	}

	return out
}

func ExtractPropertyPairConstraint(graph *rdf2go.Graph, triple *rdf2go.Triple) (out PropertyPairConstraint, err error) {
	id := getCount()
	switch triple.Predicate.RawValue() {
	case _sh + "equals":
		out.pp = equals
	case _sh + "disjoint":
		out.pp = disjoint
	case _sh + "lessThan":
		out.pp = lessThan
	case _sh + "lessThanOrEquals":
		out.pp = lessThanOrEquals
	default:
		// log.Panicln("Triple is not proper property pair constr. ", triple)
		return out, errors.New(fmt.Sprint("Triple is not proper property pair constr. ", triple))
	}
	out.term = triple.Object
	out.id = id
	return out, nil
}

type Other int64

const (
	closed Other = iota
	hasValue
	in
)

type OtherConstraint struct {
	oc           Other
	graph        *rdf2go.Graph // needed for path extraction for the closedness constraint
	closed       bool
	allowedPaths *[]string
	terms        []rdf2go.Term // overloaded, for in/hasValue this collects the terms to match, for closed
	// it matches the ignoredProperties
	id int64 // used to create unique references in Sparql translation
}

func (v OtherConstraint) GetSubConstraints() []Constraint {
	return []Constraint{}
}

func (v OtherConstraint) SparqlCheck(ep endpoint, obj string, path PropertyPath, shapeNames rdf2go.Term, target SparqlQueryFlat) (result bool, reports []ValidationResult) {
	// focusNode = obj
	// path = path
	// value .. must be extracted from query
	// sourceShape ... Unkown
	// sourceConstraintComponent .. known

	targetLine := fmt.Sprint("{\n\t", target.StringPrefix(false), "\n\t}")
	result = true
	body := v.SparqlBodyValidation(obj, path)
	uniqObj := fmt.Sprint(obj, v.id)
	var header []string
	focusNodeisValueNode := false

	if v.oc == closed {
		header = []string{"?sub", "?path", "?ClosedObjTest"}
	} else {
		if obj == "?sub" {
			focusNodeisValueNode = true
			header = []string{obj}
		} else {
			header = []string{"?sub", uniqObj}
		}
	}

	checkQuery := SparqlQuery{
		head:   header,
		target: targetLine,
		body:   []string{body},
		group:  []string{},
		graph:  ep.GetGraph(),
	}

	table := ep.Query(checkQuery)
	iterChan := table.IterRows()

	for row := range iterChan {
		var report ValidationResult
		// row := table.content[i]

		report.focusNode = row[0]
		if v.oc != closed {
			report.pathName = path
		} else {
			report.pathName = SimplePath{path: row[1]} // Sparql cannot return complex paths here
		}

		report.sourceShape = shapeNames

		switch v.oc {
		case in:
			report.sourceConstraintComponent = res(_sh + "InConstraintComponent")
		case hasValue:
			report.sourceConstraintComponent = res(_sh + "HasValueConstraintComponent")
		case closed:
			report.sourceConstraintComponent = res(_sh + "ClosedConstraintComponent")
		}

		if focusNodeisValueNode && v.oc != hasValue {
			report.value = report.focusNode
		} else if focusNodeisValueNode && v.oc == hasValue {
			report.value = nil
		}
		if v.oc != hasValue && len(header) == 2 {
			// fmt.Println("~~~~~~~~~~~~~~~~~~~~~")
			// fmt.Println("ROW", row)
			// fmt.Println("VC", v.oc)
			// fmt.Println("~~~~~~~~~~~~~~~~~~~~~")
			report.value = row[1]
		} else if v.oc != hasValue && len(header) == 3 {
			report.value = row[2]
		}

		reports = append(reports, report)
		result = false
		// if focusNodeisValueNode {
		// 	break // stop after the first hit in this case
		// }
	}

	// fmt.Println("OTHER: returning this many reports:", len(reports))

	return result, reports
}

func (v OtherConstraint) String() string {
	switch v.oc {
	case closed:
		return fmt.Sprint(_sh, "closed true")
		// var ignoredStrings []string
		// for i := range n.terms {
		// 	ignoredStrings = append(ignoredStrings, n.terms[i].String())
		// }

		// sb.WriteString(fmt.Sprint(_sh, "ignoredProperties (", strings.Join(ignoredStrings, " "), ")"))

	case hasValue:
		return fmt.Sprint(_sh, "hasValue ", v.terms[0])
	}

	var sb strings.Builder
	sb.WriteString("( ")
	for i := range v.terms {
		sb.WriteString(v.terms[i].String())
		if i != len(v.terms) {
			sb.WriteString(", ")
		}
	}
	sb.WriteString(" )")

	return fmt.Sprint(_sh, "in ", sb.String())
}

func (v OtherConstraint) SparqlBody(obj string, path PropertyPath) (out string) {
	uniqObj := fmt.Sprint(obj, v.id)

	switch v.oc {
	case in: // Univereal Property: every value node must be \in terms
		var inList []string

		for i := range v.terms {
			inList = append(inList, v.terms[i].String())
		}
		if path != nil { // Property Shape

			inner := fmt.Sprint("FILTER ( ", uniqObj, " NOT IN (", strings.Join(inList, ", "), ") ) .")
			out = fmt.Sprint("FILTER NOT EXISTS { ?sub ", path.PropertyString(), " ", uniqObj, " . ", inner, "}")
		} else { // Node Shape
			out = fmt.Sprint("FILTER ( ", obj, "  IN (", strings.Join(inList, ", "), ") ) .")
		}
	case hasValue: // Existential Property: there _must_ exist a value that
		if path != nil { // Property Shape
			inner := fmt.Sprint("FILTER ( ", uniqObj, " IN (", v.terms[0].String(), ") ) .")
			out = fmt.Sprint("FILTER EXISTS { ?sub ", path.PropertyString(), " ", uniqObj, " . ", inner, "}")
		} else { // Node Shape
			out = fmt.Sprint("FILTER ( ", obj, " IN (", v.terms[0].String(), ") ) .")
		}
	case closed: // Universal  Property: every path reachable from focusNode must be in allowed

		var finalAllow []string

		printf := "FILTER NOT EXISTS {\n\t\t %s \n\t }"

		for _, s := range *(v.allowedPaths) {
			finalAllow = append(finalAllow, fmt.Sprintf(printf, "?sub "+s+" ?ClosedObjTest ."))
		}
		for i := range v.terms {
			finalAllow = append(finalAllow, fmt.Sprintf(printf, "?sub "+v.terms[i].String()+" ?ClosedObjTest ."))
		}

		inner := strings.Join(finalAllow, "\n\t")
		out = fmt.Sprint("FILTER NOT EXISTS { \n\t ?sub ?path ?ClosedObjTest . \n\t", inner, "\n\t}")
	}

	return out
}

func (v OtherConstraint) SparqlBodyValidation(obj string, path PropertyPath) (out string) {
	uniqObj := fmt.Sprint(obj, v.id)
	switch v.oc {
	case in: // Univereal Property: every value node must be \in terms
		var inList []string

		for i := range v.terms {
			inList = append(inList, v.terms[i].String())
		}
		if path != nil { // Property Shape

			inner := fmt.Sprint("FILTER ( ", uniqObj, " NOT IN (", strings.Join(inList, ", "), ") ) .")
			out = fmt.Sprint("?sub ", path.PropertyString(), " ", uniqObj, " . ", inner)
		} else { // Node Shape
			out = fmt.Sprint("FILTER ( ", obj, "  NOT IN (", strings.Join(inList, ", "), ") ) .")
		}
	case hasValue: // Existential Property: there _must_ exist a value that
		if path != nil { // Property Shape
			inner := fmt.Sprint("FILTER ( ", uniqObj, " IN (", v.terms[0].String(), ") ) .")
			out = fmt.Sprint("FILTER NOT EXISTS { ?sub ", path.PropertyString(), " ", uniqObj, " . ", inner, "}")
		} else { // Node Shape
			out = fmt.Sprint("FILTER ( ", obj, " NOT IN (", v.terms[0].String(), ") ) .")
		}

	case closed: // Universal  Property: every path reachable from focusNode must be in allowed

		var finalAllow []string

		printf := "FILTER NOT EXISTS {\n\t\t %s \n\t }"

		for _, s := range *(v.allowedPaths) {
			finalAllow = append(finalAllow, fmt.Sprintf(printf, "?sub "+s+" ?ClosedObjTest ."))
		}
		for i := range v.terms {
			finalAllow = append(finalAllow, fmt.Sprintf(printf, "?sub "+v.terms[i].String()+" ?ClosedObjTest ."))
		}

		inner := strings.Join(finalAllow, "\n\t")
		out = fmt.Sprint("?sub ?path ?ClosedObjTest . \n\t", inner)
	}

	return out
}

func ExtractOtherConstraint(graph *rdf2go.Graph, triple *rdf2go.Triple) (out OtherConstraint, err error) {
	switch triple.Predicate.RawValue() {
	case _sh + "in":
		out.oc = in

		listTriples := graph.All(triple.Object, nil, nil)

		foundFirst := false
		foundRest := false
		foundNil := false

		for i := 0; i < len(listTriples); i++ {
			switch listTriples[i].Predicate.RawValue() {
			case _rdf + "nil":
				foundNil = true
			case _rdf + "first":
				foundFirst = true

				out.terms = append(out.terms, listTriples[i].Object)
			case _rdf + "rest":
				foundRest = true
				newTriples := graph.All(listTriples[i].Object, nil, nil)
				listTriples = append(listTriples, newTriples...) // wonder if this works
			}
		}

		if !foundFirst && !foundRest && !foundNil {
			// log.Panicln("Invalid In Constraint structure in graph")
			return out, errors.New("invalid In Constraint structure in graph")
		}

	case _sh + "closed":
		out.oc = closed

		tmp := triple.Object.RawValue()
		switch tmp {
		case "true":
			out.closed = true
		case "false":
			out.closed = false
		default:
			// log.Panicln("closedConstraint not using proper value: ", triple)
			return out, errors.New(fmt.Sprint("closedConstraint not using proper value: ", triple))
		}

		// check if any ignoredProperties
		ignoredProp := graph.All(triple.Subject, res(_sh+"ignoredProperties"), nil)

		if len(ignoredProp) > 1 {
			// log.Panicln("Defined sh:ignoredProperties more than once for a node shape.")
			return out, errors.New("defined sh:ignoredProperties more than once for a node shape")
		}

		if len(ignoredProp) == 1 {
			listTriples := graph.All(ignoredProp[0].Object, nil, nil)

			foundFirst := false
			foundRest := false
			foundNil := false

			for i := 0; i < len(listTriples); i++ {
				switch listTriples[i].Predicate.RawValue() {
				case _rdf + "nil":
					foundNil = true
				case _rdf + "first":
					foundFirst = true

					out.terms = append(out.terms, listTriples[i].Object)
				case _rdf + "rest":
					foundRest = true
					newTriples := graph.All(listTriples[i].Object, nil, nil)
					listTriples = append(listTriples, newTriples...) // wonder if this works
				}
			}

			if !foundFirst && !foundRest && !foundNil {
				// log.Panicln("Invalid ignoredProperties structure in shape definition")
				return out, errors.New("invalid ignoredProperties structure in shape definition")
			}
		}

	case _sh + "hasValue":
		out.oc = hasValue
		out.terms = append(out.terms, triple.Object)

	default:
		// log.Panicln("Triple is not other constr. ", triple)
		return out, errors.New(fmt.Sprint("Triple is not other constr. ", triple))
	}

	out.id = getCount()
	return out, nil
}

/// LOGICAL CONSTRAINTS

// TODO: make sure the same targeLine is never cached twice

var targetCache map[string]Table[rdf2go.Term] = make(map[string]Table[rdf2go.Term])

func GetTableForLogicalConstraints(ep endpoint, path PropertyPath, propertyName string, targets []SparqlQueryFlat) (out Table[rdf2go.Term]) {
	if len(targets) == 0 {
		return &GroupedTable[rdf2go.Term]{}
	}
	// out = &TableSimple[rdf2go.Term]{}
	if path != nil {
		for i := range targets {
			pathBody := "?sub " + path.PropertyString() + " ?obj ."

			groupConcat := fmt.Sprint("( ?obj AS ?", propertyName, " )")

			targetLine := fmt.Sprint("{\n\t", targets[i].StringPrefix(false), "\n\t}")

			checkQuery := SparqlQuery{
				head:   []string{"?sub", groupConcat},
				target: targetLine,
				body:   []string{pathBody},
				graph:  ep.GetGraph(),
			}

			var tmp Table[rdf2go.Term]

			if cache, ok := targetCache[checkQuery.String()]; ok {
				tmp = cache
			} else {
				tmp = ep.Query(checkQuery)
				targetCache[checkQuery.String()] = tmp
			}

			// fmt.Println("Table before merge ", tmp)
			if out == nil {
				out = tmp
			} else {
				err := out.Merge(tmp) // assume this is what as intended here
				check(err)
			}

			// fmt.Println("Table after merge ", out)
		}
	} else {
		for i := range targets {

			targetLine := fmt.Sprint("{\n\t", targets[i].StringPrefix(false), "\n\t}")

			checkQuery := SparqlQuery{
				head:   []string{"?sub"},
				target: targetLine,
				// body:   []string{targetLine},
				graph: ep.GetGraph(),
			}

			var tmp Table[rdf2go.Term]

			if cache, ok := targetCache[checkQuery.String()]; ok {
				tmp = cache
			} else {
				tmp = ep.Query(checkQuery)
				targetCache[checkQuery.String()] = tmp
			}
			if out == nil {
				out = tmp
			} else {
				err := out.Merge(tmp) // assume this is what as intended here
				check(err)
			}
		}
	}

	return GetGroupedTable(out)
}

type AndListConstraint struct {
	shapes []ShapeRef
	id     int64 // used to create unique references in Sparql translation
}

func (a AndListConstraint) String() string {
	var c *color.Color

	red := color.New(color.FgRed).Add(color.Underline)
	green := color.New(color.FgGreen).Add(color.Underline)

	var shapeStrings []string

	for i := range a.shapes {
		if a.shapes[i].negative {
			c = red
		} else {
			c = green
		}

		shapeStrings = append(shapeStrings, c.Sprint(a.shapes[i].name))
	}

	return fmt.Sprint(_sh, "and (", strings.Join(shapeStrings, " "), ")")
}

// IsPropertyShape checks for the necessary "path" property, to decide what kind of shape
// a term can be
func IsPropertyShape(graph *rdf2go.Graph, term rdf2go.Term) bool {
	res := graph.One(term, res(_sh+"path"), nil)

	return res != nil
}

func (s *ShaclDocument) ExtractAndListConstraint(graph *rdf2go.Graph, triple *rdf2go.Triple) (out AndListConstraint, err error) {
	if triple.Predicate.RawValue() != _sh+"and" {
		// log.Panicln("Called ExtractAndListConstraint function at wrong triple", triple)
		return out, errors.New(fmt.Sprint("Called ExtractAndListConstraint function at wrong triple", triple))
	}

	listTriples := graph.All(triple.Object, nil, nil)

	var shapeRefs []ShapeRef

	foundFirst := false
	foundRest := false
	foundNil := false

	for i := 0; i < len(listTriples); i++ {
		switch listTriples[i].Predicate.RawValue() {
		case _rdf + "nil":
			foundNil = true
		case _rdf + "first":
			foundFirst = true

			var sr ShapeRef
			sr.doc = s

			// check if shape already extracted, if not, do it now
			_, ok := s.shapeNames[listTriples[i].Object.RawValue()]

			if !ok {
				out2, err2 := s.GetShape(graph, listTriples[i].Object)
				if err2 != nil {
					return out, err2
				}

				sr.name, sr.ref = listTriples[i].Object.RawValue(), out2
			} else {
				sr.name = listTriples[i].Object.RawValue()
				sr.ref = s.shapeNames[listTriples[i].Object.RawValue()]
			}

			shapeRefs = append(shapeRefs, sr)
		case _rdf + "rest":
			foundRest = true
			newTriples := graph.All(listTriples[i].Object, nil, nil)
			listTriples = append(listTriples, newTriples...) // wonder if this works
		}
	}

	if !foundFirst && !foundRest && !foundNil {
		// log.Panicln("Invalid AndList structure in graph")
		return out, errors.New("invalid AndList structure in graph")
	}

	out.shapes = shapeRefs
	out.id = getCount()
	return out, nil
}

type NotShapeConstraint struct {
	shape ShapeRef
	id    int64 // used to create unique references in Sparql translation
}

func (n NotShapeConstraint) String() string {
	var c *color.Color

	red := color.New(color.FgRed).Add(color.Underline)
	green := color.New(color.FgGreen).Add(color.Underline)

	if n.shape.negative {
		c = red
	} else {
		c = green
	}

	shapeString := c.Sprint(n.shape.name)

	return fmt.Sprint(_sh, "not ", shapeString)
}

func (s *ShaclDocument) ExtractNotShapeConstraint(graph *rdf2go.Graph, triple *rdf2go.Triple) (out NotShapeConstraint, err error) {
	if triple.Predicate.RawValue() != _sh+"not" {
		// log.Panicln("Called ExtractNotShapeConstraint function at wrong triple", triple)
		return out, errors.New(fmt.Sprint("Called ExtractNotShapeConstraint function at wrong triple", triple))
	}

	var sr ShapeRef
	sr.negative = true
	sr.doc = s

	// check if shape already extracted, if not, do it now
	_, ok := s.shapeNames[triple.Object.RawValue()]

	if !ok {
		out2, err2 := s.GetShape(graph, triple.Object)
		if err2 != nil {
			return out, err2
		}
		sr.name, sr.ref = triple.Object.RawValue(), out2
	} else {
		sr.name = triple.Object.RawValue()
		sr.ref = s.shapeNames[triple.Object.RawValue()]
	}

	out.shape = sr
	out.id = getCount()
	return out, nil
}

type OrShapeConstraint struct {
	shapes []ShapeRef
	id     int64 // used to create unique references in Sparql translation
}

func (o OrShapeConstraint) String() string {
	var c *color.Color

	red := color.New(color.FgRed).Add(color.Underline)
	green := color.New(color.FgGreen).Add(color.Underline)

	var shapeStrings []string

	for i := range o.shapes {
		if o.shapes[i].negative {
			c = red
		} else {
			c = green
		}

		shapeStrings = append(shapeStrings, c.Sprint(o.shapes[i].name))
	}

	return fmt.Sprint(_sh, "or (", strings.Join(shapeStrings, " "), ")")
}

func (s *ShaclDocument) ExtractOrShapeConstraint(graph *rdf2go.Graph, triple *rdf2go.Triple) (out OrShapeConstraint, err error) {
	if triple.Predicate.RawValue() != _sh+"or" {
		// log.Panicln("Called ExtractAndListConstraint function at wrong triple", triple)
		return out, errors.New(fmt.Sprint("Called ExtractAndListConstraint function at wrong triple", triple))
	}

	listTriples := graph.All(triple.Object, nil, nil)

	var shapeRefs []ShapeRef

	foundFirst := false
	foundRest := false
	foundNil := false

	for i := 0; i < len(listTriples); i++ {
		switch listTriples[i].Predicate.RawValue() {
		case _rdf + "nil":
			foundNil = true
		case _rdf + "first":
			foundFirst = true

			var sr ShapeRef
			sr.doc = s

			// check if shape already extracted, if not, do it now
			_, ok := s.shapeNames[listTriples[i].Object.RawValue()]

			if !ok {
				out2, err2 := s.GetShape(graph, listTriples[i].Object)
				if err2 != nil {
					return out, err2
				}

				sr.name, sr.ref = listTriples[i].Object.RawValue(), out2
			} else {
				sr.name = listTriples[i].Object.RawValue()
				sr.ref = s.shapeNames[listTriples[i].Object.RawValue()]
			}

			shapeRefs = append(shapeRefs, sr)
		case _rdf + "rest":
			foundRest = true
			newTriples := graph.All(listTriples[i].Object, nil, nil)
			listTriples = append(listTriples, newTriples...) // wonder if this works
		}
	}

	if !foundFirst && !foundRest && !foundNil {
		// log.Panicln("Invalid Or structure in graph")
		return out, errors.New("invalid Or structure in graph")
	}

	out.shapes = shapeRefs
	out.id = getCount()
	return out, nil
}

type XoneShapeConstraint struct {
	shapes []ShapeRef
	id     int64 // used to create unique references in Sparql translation
}

func (x XoneShapeConstraint) String() string {
	var c *color.Color

	red := color.New(color.FgRed).Add(color.Underline)
	green := color.New(color.FgGreen).Add(color.Underline)

	var shapeStrings []string

	for i := range x.shapes {
		if x.shapes[i].negative {
			c = red
		} else {
			c = green
		}

		shapeStrings = append(shapeStrings, c.Sprint(x.shapes[i].name))
	}

	return fmt.Sprint(_sh, "xone (", strings.Join(shapeStrings, " "), ")")
}

func (s *ShaclDocument) ExtractXoneShapeConstraint(graph *rdf2go.Graph, triple *rdf2go.Triple) (out XoneShapeConstraint, err error) {
	if triple.Predicate.RawValue() != _sh+"xone" {
		// log.Panicln("Called ExtractXoneShapeConstraint function at wrong triple", triple)
		return out, errors.New(fmt.Sprint("Called ExtractXoneShapeConstraint function at wrong triple", triple))
	}

	listTriples := graph.All(triple.Object, nil, nil)

	var shapeRefs []ShapeRef

	foundFirst := false
	foundRest := false
	foundNil := false

	for i := 0; i < len(listTriples); i++ {
		switch listTriples[i].Predicate.RawValue() {
		case _rdf + "nil":
			foundNil = true
		case _rdf + "first":
			foundFirst = true

			var sr ShapeRef
			sr.doc = s

			// check if shape already extracted, if not, do it now
			_, ok := s.shapeNames[listTriples[i].Object.RawValue()]

			if !ok {
				out2, err2 := s.GetShape(graph, listTriples[i].Object)
				if err2 != nil {
					return out, err2
				}

				sr.name, sr.ref = listTriples[i].Object.RawValue(), out2
			} else {
				sr.name = listTriples[i].Object.RawValue()
				sr.ref = s.shapeNames[listTriples[i].Object.RawValue()]
			}

			shapeRefs = append(shapeRefs, sr)
		case _rdf + "rest":
			foundRest = true
			newTriples := graph.All(listTriples[i].Object, nil, nil)
			listTriples = append(listTriples, newTriples...) // wonder if this works
		}
	}

	if !foundFirst && !foundRest && !foundNil {
		// log.Panicln("Invalid Xone structure in graph")
		return out, errors.New("invalid Xone structure in graph")
	}

	out.shapes = shapeRefs
	out.id = getCount()
	return out, nil
}

type QSConstraint struct {
	shape    ShapeRef // the shape to check for in existential, numerically qualified manner
	disjoint bool     // defines disjoinedness over 'sibling' qualified shapes
	min      int      // if 0, then undefined
	max      int      // if 0, then undefined
	id       int64    // used to create unique references in Sparql translation
}

func (q QSConstraint) String() string {
	var c *color.Color

	red := color.New(color.FgRed).Add(color.Underline)
	green := color.New(color.FgGreen).Add(color.Underline)

	if q.shape.negative {
		c = red
	} else {
		c = green
	}

	shapeString := c.Sprint(q.shape.name)

	add := ""
	if q.disjoint {
		add = " disjoint "
	}

	return fmt.Sprint(_sh, "qualifiedValueShape ", shapeString, "[ ", q.min, ",", q.max, " ]", add)
}

// TODO: test with topbraid what happens when a property has two QSConstraints, that
// 'share' the same mins and maxs

// ExtractQSConstraint extract the needed information for a given triple with sh:qualifiedValueShape
// as its property, it fails if called with any other kind of triple as argument
func (s *ShaclDocument) ExtractQSConstraint(graph *rdf2go.Graph, triple *rdf2go.Triple) (out QSConstraint, err error) {
	out.max = -1 // using -1 as the default value for max constraints

	if triple.Predicate.RawValue() != _sh+"qualifiedValueShape" {
		// log.Panicln("Called ExtractQSConstraint function at wrong triple", triple)
		return out, errors.New(fmt.Sprint("Called ExtractQSConstraint function at wrong triple", triple))
	}

	var err2 error
	// find max and min
	minTriple := graph.One(triple.Subject, res(_sh+"qualifiedMinCount"), nil)
	disjoint := graph.One(triple.Subject, res(_sh+"qualifiedValueShapesDisjoint"), nil)
	maxTriple := graph.One(triple.Subject, res(_sh+"qualifiedMaxCount"), nil)
	if minTriple != nil {
		out.min, err2 = strconv.Atoi(minTriple.Object.RawValue())
		if err2 != nil {
			return out, errors.New(fmt.Sprint("Invalid MinValue for qualifiedMinCount", triple))
		}
	}
	if maxTriple != nil {
		out.max, err2 = strconv.Atoi(maxTriple.Object.RawValue())
		if err2 != nil {
			return out, errors.New(fmt.Sprint("Invalid MinValue for qualifiedMaxCount", triple))
		}
	}
	if disjoint != nil {
		// log.Panicln("qualifiedValueShapesDisjoint option is not supported at this moment.")
		tmp := disjoint.Object.RawValue()
		switch tmp {
		case "true":
			out.disjoint = true
		case "false":
			out.disjoint = false
		default:
			// log.Panicln("qualifiedValueShapesDisjoint not using proper value: ", disjoint)
			return out, errors.New(fmt.Sprint("qualifiedValueShapesDisjoint not using proper value: ", disjoint))
		}
	}

	if (minTriple == nil) && (maxTriple == nil) {
		// log.Panicln("No proper min and max counts defined for shape: ", triple.Subject)
		return out, errors.New(fmt.Sprint("No proper min and max counts defined for shape: ", triple.Subject))
	}

	var sr ShapeRef
	sr.doc = s

	// check if shape already extracted, if not, do it now
	_, ok := s.shapeNames[triple.Object.RawValue()]

	if !ok {
		out2, err2 := s.GetShape(graph, triple.Object)
		if err2 != nil {
			return out, err2
		}
		sr.name, sr.ref = triple.Object.RawValue(), out2
	} else {
		sr.name = triple.Object.RawValue()
		sr.ref = s.shapeNames[triple.Object.RawValue()]
	}

	out.shape = sr
	out.id = getCount()
	return out, nil
}

// CardinalityConstraints

type CardinalityConstraints struct {
	min bool // Min if true, Max if false
	num int  // the number on which it is consrained
}

func (v CardinalityConstraints) SparqlCheck(ep endpoint, obj string, path PropertyPath, shapeNames rdf2go.Term, target SparqlQueryFlat) (result bool, reports []ValidationResult) {
	targetLine := fmt.Sprint("{\n\t", target.StringPrefix(false), "\n\t}")
	result = true
	body := fmt.Sprint("?sub ", path.PropertyString(), " ", obj, ".")

	if v.min {
		body = "OPTIONAL {\n\t" + body + "\n\t}"
	}

	var countConst CountingSubQuery

	if v.min {
		countConst.numMax = v.num - 1
		countConst.max = true
	} else {
		countConst.numMin = v.num + 1
		countConst.min = true
	}

	countConst.id = 42
	countConst.path = path
	countConst.graph = ep.GetGraph()
	countConst.target = targetLine

	// tmp := HavingClause{
	// 	min:      !v.min, // flip the comparison for validation step
	// 	numeral:  actualNum,
	// 	variable: obj,
	// 	path:     path,
	// }

	checkQuery := SparqlQuery{
		head:       []string{"?sub"},
		target:     targetLine,
		body:       []string{body},
		subqueries: []CountingSubQuery{countConst},
		graph:      ep.GetGraph(),
		group:      []string{"?sub"},
	}

	table := ep.Query(checkQuery)
	iterChan := table.IterRows()

	for row := range iterChan {
		var report ValidationResult
		// row := table.content[i]

		report.focusNode = row[0]
		report.pathName = path
		report.sourceShape = shapeNames

		if v.min {
			report.sourceConstraintComponent = res(_sh + "MinCountConstraintComponent")
		} else {
			report.sourceConstraintComponent = res(_sh + "MaxCountConstraintComponent")
		}

		reports = append(reports, report)
		result = false
	}

	return result, reports
}

type PropertyPath interface {
	PropertyString() string
	PropertyRDF() string
}

type SimplePath struct {
	path rdf2go.Term
}

func (s SimplePath) PropertyString() string {
	return s.path.String()
}

func (s SimplePath) PropertyRDF() string {
	return s.path.String()
}

type InversePath struct {
	path PropertyPath
}

func (i InversePath) PropertyString() string {
	return "^" + i.path.PropertyString()
}

func (i InversePath) PropertyRDF() string {
	return fmt.Sprint("[ <", _sh, "inversePath> ", i.path.PropertyRDF(), " ]")
}

type SequencePath struct {
	paths []PropertyPath
}

func (s SequencePath) PropertyString() string {
	var out []string
	for i := range s.paths {
		out = append(out, s.paths[i].PropertyString())
	}
	return strings.Join(out, "/")
}

func (s SequencePath) PropertyRDF() string {
	var out []string
	for i := range s.paths {
		out = append(out, s.paths[i].PropertyRDF())
	}
	return "( " + strings.Join(out, " ") + " )"
}

type AlternativePath struct {
	paths []PropertyPath
}

func (a AlternativePath) PropertyString() string {
	var out []string
	for i := range a.paths {
		out = append(out, a.paths[i].PropertyString())
	}
	return strings.Join(out, "|")
}

func (a AlternativePath) PropertyRDF() string {
	var out []string
	for i := range a.paths {
		out = append(out, a.paths[i].PropertyRDF())
	}
	return fmt.Sprint("[ <", _sh, "alternativePath> ( ", strings.Join(out, " "), " ) ]")
}

type ZerOrMorePath struct {
	path PropertyPath
}

func (z ZerOrMorePath) PropertyRDF() string {
	return fmt.Sprint("[ <", _sh, "zeroOrMorePath> ", z.path.PropertyRDF(), " ]")
}

func (z ZerOrMorePath) PropertyString() string {
	return z.path.PropertyRDF() + "*"
}

type OneOrMorePath struct {
	path PropertyPath
}

func (o OneOrMorePath) PropertyString() string {
	return o.path.PropertyString() + "+"
}

func (o OneOrMorePath) PropertyRDF() string {
	return fmt.Sprint("[ <", _sh, "oneoOrMorePath> ", o.path.PropertyRDF(), " ]")
}

type ZerOrOnePath struct {
	path PropertyPath
}

func (o ZerOrOnePath) PropertyString() string {
	return o.path.PropertyString() + "?"
}

func (o ZerOrOnePath) PropertyRDF() string {
	return fmt.Sprint("[ <", _sh, "zeroOrOnePath> ", o.path.PropertyRDF(), " ]")
}

// ExtractPropertyPath takes the input graph, and one value term from an sh:path constraint,
// and extracts the `full` property path
func ExtractPropertyPath(graph *rdf2go.Graph, initTerm rdf2go.Term) (out PropertyPath, err error) {
	// fmt.Println("Term: ", initTerm)

	// check if term is a blank
	switch initTerm.(type) {
	case *rdf2go.BlankNode:
		// fmt.Println("Got a blank node! ", initTerm)
		// decide which complex case we are in
		triple := graph.One(initTerm, nil, nil)
		// fmt.Println("Gotten triple: ", triple)
		switch triple.Predicate.RawValue() {
		case _sh + "inversePath":
			further := triple.Object

			pathRec, err2 := ExtractPropertyPath(graph, further)
			if err2 != nil {
				return out, err2
			}
			out = InversePath{path: pathRec}
		case _sh + "alternativePath":
			further := triple.Object
			pathRec, err2 := ExtractPropertyPath(graph, further)
			if err2 != nil {
				return out, err2
			}
			sequence := pathRec.(SequencePath)
			out = AlternativePath(sequence)
		case _sh + "zeroOrMorePath":
			further := triple.Object
			pathRec, err2 := ExtractPropertyPath(graph, further)
			if err2 != nil {
				return out, err2
			}
			out = ZerOrMorePath{path: pathRec}
		case _sh + "oneOrMorePath":
			further := triple.Object
			pathRec, err2 := ExtractPropertyPath(graph, further)
			if err2 != nil {
				return out, err2
			}
			out = OneOrMorePath{path: pathRec}
		case _sh + "zeroOrOnePath":
			further := triple.Object
			pathRec, err2 := ExtractPropertyPath(graph, further)
			if err2 != nil {
				return out, err2
			}
			out = ZerOrOnePath{path: pathRec}
		case _rdf + "first", _rdf + "rest":
			allTriples := graph.All(initTerm, nil, nil) // get both triples
			var paths []PropertyPath

			foundFirst := false
			foundRest := false
			foundNil := false

			for i := 0; i < len(allTriples); i++ {
				// fmt.Println("Current triple: ", allTriples[i])
				switch allTriples[i].Predicate.RawValue() {
				case _rdf + "nil": // to cover the edge case that we get a top level nil somehow
					// log.Panicln("Invalid SHACL List, cannot have rdf:nil in predicate position")
					return out, errors.New("invalid SHACL List, cannot have rdf:nil in predicate position")
					// foundNil = true
				case _rdf + "first":
					foundFirst = true

					pathNext, err2 := ExtractPropertyPath(graph, allTriples[i].Object)
					if err2 != nil {
						return out, err2
					}

					curr := pathNext

					paths = append(paths, curr)
					// fmt.Println("Gotten path , ", curr)
				case _rdf + "rest":
					foundRest = true
					newTriples := graph.All(allTriples[i].Object, nil, nil)
					allTriples = append(allTriples, newTriples...) // wonder if this works
					// fmt.Println("Adding ", len(newTriples), " new triples based on term", allTriples[i].Object)
				}
			}

			if !foundFirst && !foundRest && !foundNil {
				// log.Panicln("Invalid Sequence structure in graph")
				return out, errors.New("invalid Sequence structure in graph")
			}

			out = SequencePath{paths: paths}

		}
	default: // we are in the simple path case
		// fmt.Printf("I don't know about type %T!\n", v)
		// fmt.Print("Simple Path ", initTerm)
		out = SimplePath{path: initTerm}
	}
	// fmt.Println("Found pp: ", out.PropertyString())
	return out, nil
}

func (s *ShaclDocument) GetPropertyShape(graph *rdf2go.Graph, term rdf2go.Term) (*PropertyShape, error) {
	node, ok := s.shapeNames[term.RawValue()]

	if ok {
		out, ok := (node).(*PropertyShape)
		if !ok {
			// log.Panicln("Shape term ", term.String(), " parsed before as NodeShape")
			return out, errors.New(fmt.Sprint("Shape term ", term.String(), " parsed before as NodeShape"))
		}
		if out.shape.insideProp == nil {
			return out, errors.New("prased propShape inproperly before")
		}

		return out, nil
	}

	var out PropertyShape
	out.maxCount = -1 // using this as the default

	triples := graph.All(term, nil, nil)
	foundPath := false

	for i := range triples {
		switch triples[i].Predicate.RawValue() {
		case _sh + "hasValue":
			out.universalOnly = false
		case _sh + "path":
			path, err2 := ExtractPropertyPath(graph, triples[i].Object)
			if err2 != nil {
				return &out, err2
			}
			out.path = path
			foundPath = true
		case _sh + "name":
			out.name = triples[i].Object.RawValue()
		case _sh + "minCount":
			val, err := strconv.Atoi(triples[i].Object.RawValue())
			check(err)
			if val > 0 {
				out.universalOnly = false
			}
			out.minCount = val
		case _sh + "maxCount":
			val, err := strconv.Atoi(triples[i].Object.RawValue())

			check(err)
			out.maxCount = val
		}
	}
	var err2 error
	out.shape, err2 = s.GetNodeShape(graph, term, &out)
	if err2 != nil {
		return nil, err2
	}
	out.id = out.shape.id

	out.universalOnly = true // set to true by default

	// for i := range out.shape.deps { // all shape dependencies of property shapes are, by def., external
	// 	out.shape.deps[i].external = true
	// 	out.shape.deps[i].origin = out.GetQualName()
	// }

	for i := range out.shape.qualifiedShapes {
		if out.shape.qualifiedShapes[i].min != 0 {
			out.universalOnly = false
		}
	}

	if !foundPath {
		log.Panicln("Defined PropertyShape without path: ", term)
	}
	if out.name == "" {
		// out.name = fmt.Sprint("Property", id)
		out.name = term.String()
		// fmt.Println("Name of property", out.name)
	}

	// No need for a separate dependency check, since GetNodeShape above already took care of it

	s.shapeNames[term.RawValue()] = &out

	return &out, nil
}

type TargetExpression interface {
	String() string
	Target()
}

type TargetIndirect struct {
	indirection *PropertyPath
	actual      TargetExpression
	level       int // levlels of indirection
}

func (t TargetIndirect) Target() {}

func (t TargetIndirect) String() string {
	var out string
	switch t.actual.(type) {
	case TargetSubjectOf:
		out = "(TargetSubjectOf) "
	case TargetObjectsOf:
		out = "(TargetObjectOf) "
	case TargetClass:
		out = "(TargetClass) "
	case TargetNode:
		out = "(TargetNode) "
	}

	return out + " <<" + (*t.indirection).PropertyString() + ">> " + t.actual.String()
}

type TargetClass struct {
	class rdf2go.Term // the class that is being targeted
}

func (t TargetClass) Target() {}

func (t TargetClass) String() string {
	return t.class.RawValue()
}

type TargetObjectsOf struct {
	path rdf2go.Term // the property the target is the object of
}

func (t TargetObjectsOf) Target() {}

func (t TargetObjectsOf) String() string {
	return t.path.RawValue()
}

type TargetSubjectOf struct {
	path rdf2go.Term // the property the target is the subject of
}

func (t TargetSubjectOf) Target() {}

func (t TargetSubjectOf) String() string {
	return t.path.RawValue()
}

type TargetNode struct {
	node rdf2go.Term // the node that is selected
}

func (t TargetNode) Target() {}

func (t TargetNode) String() string {
	return t.node.RawValue()
}

func ExtractTargetExpression(graph *rdf2go.Graph, triple *rdf2go.Triple) (out TargetExpression, err error) {
	switch triple.Predicate.RawValue() {
	case _sh + "targetNode":
		out = TargetNode{triple.Object}
	case _sh + "targetClass":
		out = TargetClass{triple.Object}
	case _sh + "targetObjectsOf":
		out = TargetObjectsOf{triple.Object}
	case _sh + "targetSubjectsOf":
		out = TargetSubjectOf{triple.Object}
	default:
		// log.Panicln("Triple is not proper value type const. ", triple)
		return out, errors.New(fmt.Sprint("Triple is not proper value type const. ", triple))
	}

	return out, nil
}

func GetTargetTerm(t TargetExpression) string {
	var queryBody string
	switch t := t.(type) {
	case TargetIndirect:
		var after string
		if t.indirection != nil {
			after = fmt.Sprint("\n?indirect", t.level, " ", (*t.indirection).PropertyString(), " ?sub .")
			return (strings.ReplaceAll(GetTargetTerm(t.actual), "?sub", fmt.Sprint("?indirect", t.level))) + after
		} else {
			return GetTargetTerm(t.actual)
		}
	case TargetClass:
		queryBody = "?sub <http://www.w3.org/1999/02/22-rdf-syntax-ns#type>/<http://www.w3.org/2000/01/rdf-schema#subClassOf>* NODE ."
		queryBody = strings.ReplaceAll(queryBody, "NODE", t.class.String())

	case TargetNode:
		queryBody = " BIND (NODE AS ?sub)"
		queryBody = strings.ReplaceAll(queryBody, "NODE", t.node.String())
	case TargetSubjectOf:
		queryBody = "  ?sub NODE ?obj ."
		queryBody = strings.ReplaceAll(queryBody, "NODE", t.path.String())

	case TargetObjectsOf:
		queryBody = " ?obj NODE ?sub ."
		queryBody = strings.ReplaceAll(queryBody, "NODE", t.path.String())
	}

	return queryBody
}

// GetNodeShape takes as input an rdf2go graph and a term signifying a NodeShape
// and then iteratively queries the rdf2go graph to extract all its details
func (s *ShaclDocument) GetNodeShape(graph *rdf2go.Graph, term rdf2go.Term, insideProp *PropertyShape) (*NodeShape, error) {
	nodeShape, ok := s.shapeNames[term.RawValue()]

	if ok {
		out, ok := (nodeShape).(*NodeShape)
		if !ok {
			// log.Panicln("Shape term ", term.String(), " parsed before as PropertyShape")
			return out, errors.New(fmt.Sprint("Shape term ", term.String(), " parsed before as PropertyShape"))
		}
		return out, nil
	}

	var viaPath *PropertyPath
	var isExternal bool
	var qualName string

	var out NodeShape
	out.IRI = term
	out.id = getCount()
	triples := graph.All(term, nil, nil) // this back-conversion here is needed (for some reason)
	var deps []dependency

	var allowedPaths []string

	for i := range triples {
		switch triples[i].Predicate.RawValue() {
		// target expressions
		case _sh + "targetClass", _sh + "targetNode", _sh + "targetObjectsOf", _sh + "targetSubjectsOf":
			te, err2 := ExtractTargetExpression(graph, triples[i])
			if err2 != nil {
				log.Println(err2)
				continue
			}
			out.target = append(out.target, te)
		// ValueTypes constraints
		case _sh + "class", _sh + "datatype", _sh + "nodeKind":
			vt, err2 := ExtractValueTypeConstraint(graph, triples[i])
			if err2 != nil {
				log.Println(err2)
				continue
			}
			out.valuetypes = append(out.valuetypes, vt)
		// ValueRanges constraints
		case _sh + "minExclusive", _sh + "maxExclusive", _sh + "minInclusive", _sh + "maxInclusive":
			vr, err2 := ExtractValueRangeConstraint(graph, triples[i])
			if err2 != nil {
				log.Println(err2)
				continue
			}
			out.valueranges = append(out.valueranges, vr)
		// string based Constraints
		case _sh + "minLength", _sh + "maxLength", _sh + "pattern", _sh + "languageIn", _sh +
			"uniqueLang":
			sr, err2 := ExtractStringBasedConstraint(graph, triples[i])
			if err2 != nil {
				log.Println(err2)
				continue
			}
			out.stringconts = append(out.stringconts, sr)
		// property pair constraints
		case _sh + "equals", _sh + "disjoint", _sh + "lessThan", _sh + "lessThanOrEquals":
			pp, err2 := ExtractPropertyPairConstraint(graph, triples[i])
			if err2 != nil {
				log.Println(err2)
				continue
			}
			out.propairconts = append(out.propairconts, pp)
		// Combine with PropertyShape constraint
		case _sh + "property":
			var pshape *PropertyShape
			pshape, err2 := s.GetPropertyShape(graph, triples[i].Object)

			if err2 != nil {
				log.Println(err2)
				continue
			}

			if !pshape.Nested() && insideProp == nil {
				// pDeps := markPos(pshape.shape.deps, len(out.properties))
				deps = append(deps, pshape.shape.deps...) // should be ok
			}

			out.properties = append(out.properties, pshape)

			allowedPaths = append(allowedPaths, pshape.path.PropertyString())
		// logic-based constraints
		case _sh + "and":
			ac, err2 := s.ExtractAndListConstraint(graph, triples[i])
			if err2 != nil {
				log.Println(err2)
				continue
			}
			out.ands.shapes = append(out.ands.shapes, ac.shapes...) // simply add them to the pile
		case _sh + "or":
			oc, err2 := s.ExtractOrShapeConstraint(graph, triples[i])
			if err2 != nil {
				log.Println(err2)
				continue
			}
			out.ors = append(out.ors, oc)
		case _sh + "not":
			ns, err2 := s.ExtractNotShapeConstraint(graph, triples[i])
			if err2 != nil {
				log.Println(err2)
				continue
			}
			out.nots = append(out.nots, ns)
		case _sh + "xone":
			xs, err2 := s.ExtractXoneShapeConstraint(graph, triples[i])
			if err2 != nil {
				log.Println(err2)
				continue
			}
			out.xones = append(out.xones, xs)
		// Combine with other NodeShape constraint
		case _sh + "node":
			var sr ShapeRef
			sr.doc = s

			// check if blank (indicating an inlined shape def)
			_, ok := triples[i].Object.(*rdf2go.BlankNode)
			if ok {
				out2, err2 := s.GetShape(graph, triples[i].Object)
				if err2 != nil {
					log.Println(err2)
					continue
				}
				// if !ok {
				// 	log.Panicln("Invalid inline shape def. in Xone list")
				// }

				sr.name, sr.ref = triples[i].Object.RawValue(), out2
			} else {
				sr.name = triples[i].Object.RawValue()
			}

			out.nodes = append(out.nodes, sr)

			// qualified shape constraint
		case _sh + "qualifiedValueShape":
			qs, err2 := s.ExtractQSConstraint(graph, triples[i])
			if err2 != nil {
				log.Println(err2)
				continue
			}
			out.qualifiedShapes = append(out.qualifiedShapes, qs)
		// closedness condition , with manually specifiable exceptions
		case _sh + "closed", _sh + "hasValue", _sh + "in":
			oc, err2 := ExtractOtherConstraint(graph, triples[i])
			if err2 != nil {
				log.Println(err2)
				continue
			}

			if oc.oc != closed || oc.closed {

				if triples[i].Predicate.RawValue() == _sh+"closed" {
					oc.allowedPaths = &allowedPaths
				}

				out.others = append(out.others, oc)
			}
		case _sh + "severity":
			out.severity = triples[i].Object
		case _sh + "message":
			// fmt.Println("Extracing sh:message: ", triples[i].Object.String())
			message := make(map[string]rdf2go.Term)
			switch messageType := triples[i].Object.(type) {
			case *rdf2go.Literal:
				if messageType.Datatype != nil && messageType.Datatype.RawValue() == _xsd+"string" {
					message["en"] = messageType
					out.message = message
				} else if messageType.Language != "" {
					// fmt.Println("Adding message")
					message[messageType.Language] = messageType
					out.message = message
				}
				// anything not matching these two cases is invalid, thus being ignored
			default:
				// invalid type of message, thus being ignored
			}
		// allows NodeShape to be manually 'turned off' (i.e. not be considered in validation)
		case _sh + "deactivated":
			tmp := triples[i].Object.RawValue()
			switch tmp {
			case "true":
				out.deactivated = true
			case "false":
				out.deactivated = false
			default:
				log.Println("deactivated not using proper value: ", triples[i])
			}
		}
	}

	qualName = out.GetQualName()
	if insideProp != nil {
		viaPath = &insideProp.path
		isExternal = true
		qualName = fmt.Sprint("Property", out.id)
		out.insideProp = insideProp
	}

	// Dependency Check
	if len(out.ands.shapes) > 0 {
		dep := dependency{
			name:     out.ands.shapes,
			origin:   qualName,
			external: isExternal,
			mode:     and,
			path:     viaPath,
			max:      -1,
		}
		deps = append(deps, dep)
	}

	for i := range out.ors {
		dep := dependency{
			name:     out.ors[i].shapes,
			origin:   qualName,
			external: isExternal,
			mode:     or,
			path:     viaPath,
			max:      -1,
		}
		deps = append(deps, dep)
	}

	for i := range out.xones {
		dep := dependency{
			name:     out.xones[i].shapes,
			origin:   qualName,
			external: isExternal,
			mode:     xone,
			max:      -1,
			path:     viaPath,
		}
		deps = append(deps, dep)
	}
	for i := range out.nots {
		dep := dependency{
			name:     []ShapeRef{out.nots[i].shape},
			origin:   qualName,
			external: isExternal,
			mode:     not,
			path:     viaPath,
			max:      -1,
		}
		deps = append(deps, dep)
	}
	for i := range out.nodes {
		dep := dependency{
			name:     []ShapeRef{out.nodes[i]},
			origin:   qualName,
			external: isExternal,
			mode:     node,
			max:      -1,
			path:     viaPath,
		}
		deps = append(deps, dep)
	}

	for i := range out.qualifiedShapes {
		dep := dependency{
			name:     []ShapeRef{out.qualifiedShapes[i].shape},
			origin:   qualName,
			external: isExternal,
			mode:     qualified,
			min:      out.qualifiedShapes[i].min,
			max:      out.qualifiedShapes[i].max,
			disjoint: out.qualifiedShapes[i].disjoint,
			path:     viaPath,
		}
		deps = append(deps, dep)
	}

	// nested Properties

	for i := range out.properties {
		if insideProp == nil && !out.properties[i].Nested() {
			continue
		}

		dep := dependency{
			name: []ShapeRef{{
				name: out.properties[i].shape.GetIRI(),
				ref:  out.properties[i],
				doc:  s,
			}},
			origin:   qualName,
			external: false,
			mode:     property,
			max:      -1,
			path:     viaPath,
		}
		deps = append(deps, dep)
	}

	out.deps = deps
	if insideProp == nil {
		s.shapeNames[term.RawValue()] = &out
	}

	return &out, nil
}

// DefineSiblingValues computes the relevant sibling values over an RDF graph and a term
// and saves them inside the relevant QualiviedValueShape constraint dependency of the shape
func (s *ShaclDocument) DefineSiblingValues(shape string, qualShape string) (*[]Shape, error) {
	// fmt.Println("\nGetting siblings for shape ", shape, " except for shape ", qualShape)

	shapeVal, ok := s.shapeNames[shape]

	if !ok {
		return nil, errors.New("shape " + shape + " is not defined")
	}

	switch shapeTyp := shapeVal.(type) {

	case *NodeShape:

		// check if there is a qualifiedValueShape with disjointedness present:
		needsSiblings := false
		var siblingsShapes []string

		for _, p := range shapeTyp.properties {
		inner:
			for _, qs := range p.shape.qualifiedShapes {
				if qs.disjoint {
					needsSiblings = true
				}
				if qs.shape.name == qualShape {
					continue inner
				}
				siblingsShapes = append(siblingsShapes, qs.shape.name)
			}
		}

		siblingsShapes = removeDuplicate(siblingsShapes)

		// fmt.Println("SIblings: ", strings.Join(siblingsShapes, ", "))

		out := []Shape{}
		if needsSiblings {
			for i := range siblingsShapes {
				out = append(out, s.shapeNames[siblingsShapes[i]])
			}

			return &out, nil
		} else {
			return nil, nil
		}

	case *PropertyShape:
		// check if there is a qualifiedValueShape with disjointedness present:
		needsSiblings := false
		var siblingsShapes []string

		for _, p := range shapeTyp.shape.properties {
			for _, qs := range p.shape.qualifiedShapes {
				if qs.disjoint {
					needsSiblings = true
				}
				if qs.shape.name == qualShape {
					continue
				}
				siblingsShapes = append(siblingsShapes, qs.shape.name)
			}
		}

		siblingsShapes = removeDuplicate(siblingsShapes)

		out := []Shape{}
		if needsSiblings {
			for i := range siblingsShapes {
				out = append(out, s.shapeNames[siblingsShapes[i]])
			}

			return &out, nil
		} else {
			return nil, nil
		}

	}

	return nil, nil
}
