package main

import (
	"fmt"
	"log"
	"strconv"
	"strings"

	"github.com/deiu/rdf2go"
	"github.com/fatih/color"
)

// GetShape determins which kind of shape (if at all) the given term is,
// and returns the extracted Shape
func (s *ShaclDocument) GetShape(graph *rdf2go.Graph, term rdf2go.Term) (shape Shape) {
	// check if shape is already known
	if v, ok := s.shapeNames[term.RawValue()]; ok {
		return *v
	}

	if IsPropertyShape(graph, term) {
		shape = s.GetPropertyShape(graph, term)
	} else {
		shape = s.GetNodeShape(graph, term)
	}

	return shape
}

// A ShapeRef is used to capture the abilty of Shacl Documents to point to shapes
// even before they are defined. Via lazy dereferencing, we can easily parse these
// and get the pointer to an actual shape at time of translation to Sparql
type ShapeRef struct {
	name     string //
	ref      *Shape
	negative bool // if true, then the reference is on the negation of this shape
}

func (s ShapeRef) IsBlank() bool {
	if s.ref == nil {
		return false
	}

	return (*s.ref).IsBlank()
}

type ValueType int64

const (
	class ValueType = iota
	nodeKind
	dataType
)

type ValueTypeConstraint struct {
	vt   ValueType   // denotes what kind of value type we are dealing with
	term rdf2go.Term // the associated term
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

func (v ValueTypeConstraint) SparqlBody(obj, path string) (out string) {
	uniqObj := obj + strconv.Itoa(int(v.vt)) + v.term.RawValue()
	switch v.vt {
	case class: // UNIVERSAL PROPERTY

		if path != "" { // PROPERTY SHAPE
			out = fmt.Sprint("FILTER NOT EXISTS { ?sub ", path, " ", uniqObj,
				" . FILTER NOT EXISTS {", uniqObj, "rdf2go:type/rdf2gos:subClassOf* ",
				v.term.String(), "} . }.")
		} else { // NODE SHAPE
			out = obj + " rdf2go:type/rdf2gos:subClassOf* " + v.term.String() + "."
		}

	case nodeKind: // UNIVERSAL PROPERTY
		if path != "" { // PROPERTY SHAPE

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
			default:
				log.Panicln("Invalid term used in def. of NodeKindConstraint: ", v.term)
			}

			out = fmt.Sprint("FILTER NOT EXISTS { ?sub ", path, " ", uniqObj, " . ", inner, "}")

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
			default:
				log.Panicln("Invalid term used in def. of NodeKindConstraint: ", v.term)
			}
		}

	case dataType: // UNIVERSAL PROPERTY
		if path != "" {
			inner := "FILTER ( datatype( " + uniqObj + ") != " + v.term.RawValue() + " ) ."

			out = fmt.Sprint("FILTER NOT EXISTS { ?sub ", path, " ", uniqObj, " . ", inner, "}")
		} else {
			out = "FILTER ( datatype( " + obj + ") == " + v.term.RawValue() + " ) ."
		}

	}

	return out
}

// ExtractValueTypeConstraint gets the input rdf2go graph and a goal term and tries to
// extract a ValueTypeConstraint (sh:class, sh:dataType or sh:dataType) from it
func (s *ShaclDocument) ExtractValueTypeConstraint(graph *rdf2go.Graph, triple *rdf2go.Triple) (out ValueTypeConstraint) {
	switch triple.Predicate.RawValue() {
	case _sh + "class":
		out = ValueTypeConstraint{class, triple.Object}
	case _sh + "nodeKind":
		out = ValueTypeConstraint{nodeKind, triple.Object}
	case _sh + "dataType":
		switch triple.Object.RawValue() {
		case _sh + "NodeKind", _sh + "BlankNode", _sh + "IRI",
			_sh + "Literal", _sh + "BlankNodeOrIRI", _sh + "BlankNodeOrLiteral",
			_sh + "IRIOrLiteral": // do nothing since object is of correct type
		default:
			log.Panicln("Object val of dataType breaks standard ", triple)
		}

		out = ValueTypeConstraint{dataType, triple.Object}
	default:
		log.Panicln("Triple is not proper value type constr. ", triple)
	}
	return out
}

type ValueRange int64

const (
	minExcl ValueRange = iota
	maxExcl
	minIncl
	maxInclu
)

type ValueRangeConstraint struct {
	vr    ValueRange // denotes what kind of value range constraint we have
	value int        // the associated the integer value of the constraint
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

func (v ValueRangeConstraint) SparqlBody(obj, path string) (out string) {
	uniqObj := obj + strconv.Itoa(int(v.vr)) + strconv.Itoa(v.value)

	switch v.vr {
	case minExcl: // UNIVERSAL PROPERTY
		if path != "" {
			inner := fmt.Sprint("FILTER ( ", v.value, " >= ", uniqObj, ") .")
			out = fmt.Sprint("FILTER NOT EXISTS { ?sub ", path, " ", uniqObj, " . ", inner, "}")
		} else {
			out = fmt.Sprint("FILTER ( ", v.value, " < ", obj, ") .")
		}
	case maxExcl: // UNIVERSAL PROPERTY
		if path != "" {
			inner := fmt.Sprint("FILTER ( ", v.value, " <= ", uniqObj, ") .")
			out = fmt.Sprint("FILTER NOT EXISTS { ?sub ", path, " ", uniqObj, " . ", inner, "}")
		} else {
			out = fmt.Sprint("FILTER ( ", v.value, " > ", obj, ") .")
		}
	case minIncl: // UNIVERSAL PROPERTY
		if path != "" {
			inner := fmt.Sprint("FILTER ( ", v.value, " > ", uniqObj, ") .")
			out = fmt.Sprint("FILTER NOT EXISTS { ?sub ", path, " ", uniqObj, " . ", inner, "}")
		} else {
			out = fmt.Sprint("FILTER ( ", v.value, " <= ", obj, ") .")
		}

	case maxInclu: // UNIVERSAL PROPERTY

		if path != "" {
			inner := fmt.Sprint("FILTER ( ", v.value, " < ", uniqObj, ") .")
			out = fmt.Sprint("FILTER NOT EXISTS { ?sub ", path, " ", uniqObj, " . ", inner, "}")
		} else {
			out = fmt.Sprint("FILTER ( ", v.value, " >= ", obj, ") .")
		}
	}

	return out
}

func (s *ShaclDocument) ExtractValueRangeConstraint(graph *rdf2go.Graph, triple *rdf2go.Triple) (out ValueRangeConstraint) {
	val, err := strconv.Atoi(triple.Object.RawValue())
	check(err)

	switch triple.Predicate.RawValue() {
	case _sh + "minExclusive":
		out = ValueRangeConstraint{minExcl, val}
	case _sh + "maxExclusive":
		out = ValueRangeConstraint{maxExcl, val}
	case _sh + "ValueRangeConstraint":
		out = ValueRangeConstraint{minIncl, val}
	case _sh + "maxInclusive":
		out = ValueRangeConstraint{maxInclu, val}
	default:
		log.Panicln("Triple is not proper value range constr. ", triple)
	}

	return out
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
	uniqueLang bool // property shapes ony
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

func (v StringBasedConstraint) SparqlBody(obj, path string) (out string) {
	uniqObj := obj + strconv.Itoa(int(v.sb)) + strconv.Itoa(v.length) + v.pattern + v.flags

	switch v.sb {
	case minLen: // UNIVERSAL PROPERTY
		if path != "" { // PROPERTY SHAPE
			inner := fmt.Sprint("FILTER (STRLEN(str(", uniqObj, ")) < ", v.length, ") .")
			out = fmt.Sprint("FILTER NOT EXISTS { ?sub ", path, " ", uniqObj, " . ", inner, "}")
		} else { // NODE SHAPE
			out = fmt.Sprint("FILTER (STRLEN(str(", obj, ")) >= ", v.length, ") .")
		}
	case maxLen: // UNIVERSAL PROPERTY

		if path != "" { // PROPERTY SHAPE
			inner := fmt.Sprint("FILTER (STRLEN(str(", uniqObj, ")) > ", v.length, ") .")
			out = fmt.Sprint("FILTER NOT EXISTS { ?sub ", path, " ", uniqObj, " . ", inner, "}")
		} else { // NODE SHAPE
			out = fmt.Sprint("FILTER (STRLEN(str(", obj, ")) <= ", v.length, ") .")
		}

	case pattern: // UNIVERSAL PROPERTY
		if path != "" {
			inner := ""
			if len(v.flags) == 0 {
				inner = fmt.Sprint("FILTER (isBlank(" + uniqObj + ") || !regex(str(" + uniqObj + "), " + v.pattern + ", " + v.flags + ") )")
			} else {
				inner = fmt.Sprint("FILTER (isBlank(" + uniqObj + ") || !regex(str(" + uniqObj + "), " + v.pattern + ") )")
			}

			out = fmt.Sprint("FILTER NOT EXISTS { ?sub ", path, " ", uniqObj, " . ", inner, "}")
		} else {
			if len(v.flags) == 0 {
				out = fmt.Sprint("FILTER (!isBlank(" + obj + ") && regex(str(" + obj + "), " + v.pattern + ", " + v.flags + ") )")
			} else {
				out = fmt.Sprint("FILTER (!isBlank(" + obj + ") && regex(str(" + obj + "), " + v.pattern + ") )")
			}
		}
	case langIn:
		// TODO
	case uniqLang:
		// TODO
	}

	return out
}

func (s *ShaclDocument) ExtractStringBasedConstraint(graph *rdf2go.Graph, triple *rdf2go.Triple) (out StringBasedConstraint) {
	switch triple.Predicate.RawValue() {
	case _sh + "minLength":
		val, err := strconv.Atoi(triple.Object.RawValue())
		check(err)
		out = StringBasedConstraint{sb: minLen, length: val}
	case _sh + "maxLength":
		val, err := strconv.Atoi(triple.Object.RawValue())
		check(err)
		out = StringBasedConstraint{sb: maxLen, length: val}
	case _sh + "pattern":
		// check if "sh:flags" defined:
		flags := graph.One(triple.Subject, res(_sh+"flags"), nil)
		if flags != nil {
			out = StringBasedConstraint{sb: pattern, pattern: triple.Object.RawValue(), flags: flags.Object.RawValue()}
		} else {
			out = StringBasedConstraint{sb: pattern, pattern: triple.Object.RawValue()}
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
			log.Panicln("StringBasedConstraint not using proper value: ", triple)
		}

		out = StringBasedConstraint{sb: uniqLang, uniqueLang: val}
	default:
		log.Panicln("Triple is not proper value range constr. ", triple)
	}

	return out
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
func (v PropertyPairConstraint) SparqlBody(obj, path string) (out string) {
	uniqObj := obj + strconv.Itoa(int(v.pp)) + v.term.RawValue()

	switch v.pp {
	case equals: // Universal Property: set equality between value nodes and objects reachable via equals
		other := v.term.RawValue()

		// implemented via two not exists: one testing that A ⊆ B and another testing B ⊆ A
		out1 := fmt.Sprint("FILTER NOT EXISTS { ?sub ", other, " ", uniqObj, " . FILTER NOT EXISTS { ?sub ", path, " ", uniqObj, " .} . } .\n")
		out2 := fmt.Sprint("FILTER NOT EXISTS { ?sub ", path, " ", uniqObj, " . FILTER NOT EXISTS { ?sub ", other, " ", uniqObj, " .} . } .")

		out = out1 + out2
	case disjoint: // Universal Property: set of value nodes and those reachable by disjoint must be distinct
		other := v.term.RawValue()

		// implemented via one exists: one testing that A∩B = ∅
		out = fmt.Sprint("FILTER NOT EXISTS { ?sub ", path, " ", uniqObj, " . ?sub ", other, " ", uniqObj, " . } .")
	case lessThan: // Universal: there is no value node with value higher or equal than those reachable by lessThan
		other := v.term.RawValue()

		// implemented via one exists: one testing that A∩B = ∅
		out = fmt.Sprint("FILTER NOT EXISTS { ?sub ", other, " ", uniqObj, " . FILTER( ", other, " <= ", obj, " )  . } .")
	case lessThanOrEquals: // Universal: there is no value node with value higher than those reachable by lessThan
		other := v.term.RawValue()

		// implemented via one exists: one testing that A∩B = ∅
		out = fmt.Sprint("FILTER NOT EXISTS { ?sub ", other, " ", uniqObj, " . FILTER( ", other, " < ", obj, " )  . } .")
	}

	return out
}

func (s *ShaclDocument) ExtractPropertyPairConstraint(graph *rdf2go.Graph, triple *rdf2go.Triple) (out PropertyPairConstraint) {
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
		log.Panicln("Triple is not proper property pair constr. ", triple)
	}
	out.term = triple.Object
	return out
}

type AndListConstraint struct {
	shapes []ShapeRef
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

func (s *ShaclDocument) ExtractAndListConstraint(graph *rdf2go.Graph, triple *rdf2go.Triple) (out AndListConstraint) {
	if triple.Predicate.RawValue() != _sh+"and" {
		log.Panicln("Called ExtractAndListConstraint function at wrong triple", triple)
	}

	listTriples := graph.All(triple.Object, nil, nil)

	var shapeRefs []ShapeRef

	foundFirst := false
	foundRest := false
	foundNil := false

	for i := range listTriples {
		switch listTriples[i].Predicate.RawValue() {
		case _rdf + "nil":
			foundNil = true
		case _rdf + "first":
			foundFirst = true

			var sr ShapeRef

			// check if blank (indicating an inlined shape def)
			_, ok := listTriples[i].Object.(*rdf2go.BlankNode)
			if ok {
				out2 := s.GetShape(graph, listTriples[i].Object)
				// if !ok {
				// 	log.Panicln("Invalid inline shape def. in And list")
				// }
				s.nodeShapes = append(s.nodeShapes, out2)
				s.shapeNames[listTriples[i].Object.RawValue()] = &out2
				sr.name, sr.ref = listTriples[i].Object.RawValue(), &out2
			} else {
				sr.name = listTriples[i].Object.RawValue()
			}

			shapeRefs = append(shapeRefs, sr)
		case _rdf + "rest":
			foundRest = true
			newTriples := graph.All(listTriples[i].Object, nil, nil)
			listTriples = append(listTriples, newTriples...) // wonder if this works
		}
	}

	if !foundFirst && !foundRest && !foundNil {
		log.Panicln("Invalid AndList structure in graph")
	}

	out.shapes = shapeRefs
	return out
}

func (s *ShaclDocument) ExtractInConstraint(graph *rdf2go.Graph, triple *rdf2go.Triple) (out []rdf2go.Term) {
	if triple.Predicate.RawValue() != _sh+"in" {
		log.Panicln("Called ExtractInConstraint function at wrong triple", triple)
	}

	listTriples := graph.All(triple.Object, nil, nil)

	foundFirst := false
	foundRest := false
	foundNil := false

	for i := range listTriples {
		switch listTriples[i].Predicate.RawValue() {
		case _rdf + "nil":
			foundNil = true
		case _rdf + "first":
			foundFirst = true

			out = append(out, listTriples[i].Object)
		case _rdf + "rest":
			foundRest = true
			newTriples := graph.All(listTriples[i].Object, nil, nil)
			listTriples = append(listTriples, newTriples...) // wonder if this works
		}
	}

	if !foundFirst && !foundRest && !foundNil {
		log.Panicln("Invalid In Constraint structure in graph")
	}

	return out
}

type NotShapeConstraint struct {
	shape ShapeRef
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

	var shapeString string = c.Sprint(n.shape.name)

	return fmt.Sprint(_sh, "not ", shapeString)
}

func (s *ShaclDocument) ExtractNotShapeConstraint(graph *rdf2go.Graph, triple *rdf2go.Triple) (out NotShapeConstraint) {
	if triple.Predicate.RawValue() != _sh+"not" {
		log.Panicln("Called ExtractNotShapeConstraint function at wrong triple", triple)
	}

	var sr ShapeRef
	sr.negative = true

	_, ok := triple.Object.(*rdf2go.BlankNode)

	if ok {
		out2 := s.GetShape(graph, triple.Object)
		// if !ok {
		// 	log.Panicln("Invalid inline shape def. in Not Shape")
		// }
		s.nodeShapes = append(s.nodeShapes, out2)
		s.shapeNames[triple.Object.RawValue()] = &out2
		sr.name, sr.ref = triple.Object.RawValue(), &out2
	} else {
		sr.name = triple.Object.RawValue()
	}

	out.shape = sr
	return out
}

type OrShapeConstraint struct {
	shapes []ShapeRef
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

func (s *ShaclDocument) ExtractOrShapeConstraint(graph *rdf2go.Graph, triple *rdf2go.Triple) (out OrShapeConstraint) {
	if triple.Predicate.RawValue() != _sh+"or" {
		log.Panicln("Called ExtractAndListConstraint function at wrong triple", triple)
	}

	listTriples := graph.All(triple.Object, nil, nil)

	var shapeRefs []ShapeRef

	foundFirst := false
	foundRest := false
	foundNil := false

	for i := range listTriples {
		switch listTriples[i].Predicate.RawValue() {
		case _rdf + "nil":
			foundNil = true
		case _rdf + "first":
			foundFirst = true

			var sr ShapeRef

			// check if blank (indicating an inlined shape def)
			_, ok := listTriples[i].Object.(*rdf2go.BlankNode)
			if ok {
				out2 := s.GetShape(graph, listTriples[i].Object)
				// if !ok {
				// 	log.Panicln("Invalid inline shape def. in Or list")
				// }
				s.nodeShapes = append(s.nodeShapes, out2)
				s.shapeNames[listTriples[i].Object.RawValue()] = &out2
				sr.name, sr.ref = listTriples[i].Object.RawValue(), &out2
			} else {
				sr.name = listTriples[i].Object.RawValue()
			}

			shapeRefs = append(shapeRefs, sr)
		case _rdf + "rest":
			foundRest = true
			newTriples := graph.All(listTriples[i].Object, nil, nil)
			listTriples = append(listTriples, newTriples...) // wonder if this works
		}
	}

	if !foundFirst && !foundRest && !foundNil {
		log.Panicln("Invalid Or structure in graph")
	}

	out.shapes = shapeRefs
	return out
}

type XoneShapeConstraint struct {
	shapes []ShapeRef
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

func (s *ShaclDocument) ExtractXoneShapeConstraint(graph *rdf2go.Graph, triple *rdf2go.Triple) (out XoneShapeConstraint) {
	if triple.Predicate.RawValue() != _sh+"xone" {
		log.Panicln("Called ExtractXoneShapeConstraint function at wrong triple", triple)
	}

	listTriples := graph.All(triple.Object, nil, nil)

	var shapeRefs []ShapeRef

	foundFirst := false
	foundRest := false
	foundNil := false

	for i := range listTriples {
		switch listTriples[i].Predicate.RawValue() {
		case _rdf + "nil":
			foundNil = true
		case _rdf + "first":
			foundFirst = true

			var sr ShapeRef

			// check if blank (indicating an inlined shape def)
			_, ok := listTriples[i].Object.(*rdf2go.BlankNode)
			if ok {
				out2 := s.GetShape(graph, listTriples[i].Object)
				// if !ok {
				// 	log.Panicln("Invalid inline shape def. in Xone list")
				// }
				s.nodeShapes = append(s.nodeShapes, out2)
				s.shapeNames[listTriples[i].Object.RawValue()] = &out2
				sr.name, sr.ref = listTriples[i].Object.RawValue(), &out2
			} else {
				sr.name = listTriples[i].Object.RawValue()
			}

			shapeRefs = append(shapeRefs, sr)
		case _rdf + "rest":
			foundRest = true
			newTriples := graph.All(listTriples[i].Object, nil, nil)
			listTriples = append(listTriples, newTriples...) // wonder if this works
		}
	}

	if !foundFirst && !foundRest && !foundNil {
		log.Panicln("Invalid Xone structure in graph")
	}

	out.shapes = shapeRefs
	return out
}

type QSConstraint struct {
	shape    ShapeRef // the shape to check for in existential, numerically qualified manner
	disjoint bool     // defines disjoinedness over 'sibling' qualified shapes
	min      int      // if 0, then undefined
	max      int      // if 0, then undefined
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
func (s *ShaclDocument) ExtractQSConstraint(graph *rdf2go.Graph, triple *rdf2go.Triple) (out QSConstraint) {
	if triple.Predicate.RawValue() != _sh+"qualifiedValueShape" {
		log.Panicln("Called ExtractQSConstraint function at wrong triple", triple)
	}

	var err error
	// find max and min
	minTriple := graph.One(triple.Subject, res(_sh+"qualifiedMinCount"), nil)
	disjoint := graph.One(triple.Subject, res(_sh+"qualifiedValueShapesDisjoint"), nil)
	maxTriple := graph.One(triple.Subject, res(_sh+"qualifiedMaxCount"), nil)
	if minTriple != nil {
		out.min, err = strconv.Atoi(minTriple.Object.RawValue())
		check(err)
	}
	if maxTriple != nil {
		out.max, err = strconv.Atoi(maxTriple.Object.RawValue())
		check(err)
	}
	if disjoint != nil {
		log.Panicln("qualifiedValueShapesDisjoint option is not supported at this moment.")
		// tmp := disjoint.Object.RawValue()
		// switch tmp {
		// case "true":
		// 	out.disjoint = true
		// case "false":
		// 	out.disjoint = false
		// default:
		// 	log.Panicln("qualifiedValueShapesDisjoint not using proper value: ", disjoint)
		// }
	}

	if (minTriple == nil) && (maxTriple == nil) {
		log.Panicln("No proper min and max counts defined for shape: ", triple.Subject)
	}

	var sr ShapeRef

	// check if blank (indicating an inlined shape def)
	_, ok := triple.Object.(*rdf2go.BlankNode)
	if ok {
		out2 := s.GetShape(graph, triple.Object)
		// if !ok {
		// 	log.Panicln("Invalid inline shape def. in QualifiedShape")
		// }
		s.nodeShapes = append(s.nodeShapes, out2)
		s.shapeNames[triple.Object.RawValue()] = &out2
		sr.name, sr.ref = triple.Object.RawValue(), &out2
	} else {
		sr.name = triple.Object.RawValue()
	}

	out.shape = sr

	return out
}

type PropertyPath interface {
	PropertyString() string
}

type SimplePath struct {
	path rdf2go.Term
}

func (s SimplePath) PropertyString() string {
	return s.path.String()
}

type InversePath struct {
	path PropertyPath
}

func (i InversePath) PropertyString() string {
	return "^" + i.path.PropertyString()
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

type ZerOrMorePath struct {
	path PropertyPath
}

func (z ZerOrMorePath) PropertyString() string {
	return z.path.PropertyString() + "*"
}

type OneOrMorePath struct {
	path PropertyPath
}

func (o OneOrMorePath) PropertyString() string {
	return o.path.PropertyString() + "+"
}

type ZerOrOnePath struct {
	path PropertyPath
}

func (o ZerOrOnePath) PropertyString() string {
	return o.path.PropertyString() + "?"
}

// func TestPropertyPath(graph rdf2go.Graph, triple rdf2go.Triple) (PropertyPath, bool) {
// 	if triple.Predicate.RawValue() != _sh+"property" {
// 		return SimplePath{}, false
// 	}
// 	return ExtractPropertyPath(graph, triple.ObjeGct), true
// }

// ExtractPropertyPath takes the input graph, and one value term from an sh:path constraint,
// and extracts the `full` property path
func (s *ShaclDocument) ExtractPropertyPath(graph *rdf2go.Graph, initTerm rdf2go.Term) (out PropertyPath) {
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
			out = InversePath{path: s.ExtractPropertyPath(graph, further)}
		case _sh + "alternativePath":
			further := triple.Object
			sequence := s.ExtractPropertyPath(graph, further).(SequencePath)
			out = AlternativePath{paths: sequence.paths}
		case _sh + "zeroOrMorePath":
			further := triple.Object
			out = ZerOrMorePath{path: s.ExtractPropertyPath(graph, further)}
		case _sh + "oneOrMorePath":
			further := triple.Object
			out = OneOrMorePath{path: s.ExtractPropertyPath(graph, further)}
		case _sh + "zeroOrOnePath":
			further := triple.Object
			out = ZerOrOnePath{path: s.ExtractPropertyPath(graph, further)}
		case _rdf + "first", _rdf + "rest":
			allTriples := graph.All(initTerm, nil, nil) // get both triples
			var first PropertyPath
			var rest *PropertyPath

			foundFirst := false
			foundRest := false
			foundNil := false
			for i := range allTriples {
				switch allTriples[i].Predicate.RawValue() {
				case _rdf + "nil": // to cover the edge case that we get a top level nil somehow
					foundNil = true
				case _rdf + "first":
					first = s.ExtractPropertyPath(graph, allTriples[i].Object)
					foundFirst = true
				case _rdf + "rest":
					foundRest = true
					if allTriples[i].Object.RawValue() == _rdf+"nil" {
						rest = nil
					} else {
						restRef := s.ExtractPropertyPath(graph, allTriples[i].Object)
						rest = &restRef
					}
				}
			}

			if !foundFirst && !foundRest && !foundNil {
				log.Panicln("Invalid Sequence structure in graph")
			}

			if foundNil {
				out = SequencePath{} // return the empty sequence path
			} else {
				var restSequence SequencePath = (*rest).(SequencePath)

				var paths []PropertyPath
				paths = append(paths, first)
				paths = append(paths, restSequence.paths...)

				out = SequencePath{paths}
			}

		}
	default: // we are in the simple path case
		// fmt.Printf("I don't know about type %T!\n", v)
		// fmt.Print("Simple Path ", initTerm)
		out = SimplePath{path: initTerm}
	}
	// fmt.Println("Found pp: ", out.PropertyString())
	return out
}

func (s *ShaclDocument) GetPropertyShape(graph *rdf2go.Graph, term rdf2go.Term) (out PropertyShape) {
	out.shape = s.GetNodeShape(graph, term)

	for i := range out.shape.deps { // all shape dependencies of property shapes are, by def., external
		out.shape.deps[i].external = true
	}

	triples := graph.All(term, nil, nil)
	foundPath := false

	for i := range triples {
		switch triples[i].Predicate.RawValue() {
		case _sh + "path":
			path := s.ExtractPropertyPath(graph, triples[i].Object)
			out.path = path
			foundPath = true
		case _sh + "name":
			out.name = triples[i].Object.RawValue()
		case _sh + "minCount":
			val, err := strconv.Atoi(triples[i].Object.RawValue())
			check(err)
			out.minCount = val
		case _sh + "maxCount":
			val, err := strconv.Atoi(triples[i].Object.RawValue())
			check(err)
			out.maxCount = val
		}
	}

	if !foundPath {
		log.Panicln("Defined PropertyShape without path: ", term)
	}

	// No need for a separate dependency check, since GetNodeShape above already took care of it

	return out
}

// TODO: if there are valid SHACL docs with collections of targets, then extend this to support it

type TargetExpression interface {
	String() string
}

type TargetIndirect struct {
	terms []string // the list of terms
}

func (t TargetIndirect) String() string {
	return fmt.Sprint(t.terms)
}

type TargetClass struct {
	class rdf2go.Term // the class that is being targeted
}

func (t TargetClass) String() string {
	return t.class.RawValue()
}

type TargetObjectsOf struct {
	path rdf2go.Term // the property the target is the object of
}

func (t TargetObjectsOf) String() string {
	return t.path.RawValue()
}

type TargetSubjectOf struct {
	path rdf2go.Term // the property the target is the subject of
}

func (t TargetSubjectOf) String() string {
	return t.path.RawValue()
}

type TargetNode struct {
	node rdf2go.Term // the node that is selected
}

func (t TargetNode) String() string {
	return t.node.RawValue()
}

func (s *ShaclDocument) ExtractTargetExpression(graph *rdf2go.Graph, triple *rdf2go.Triple) (out TargetExpression) {
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
		log.Panicln("Triple is not proper value type const. ", triple)
	}

	return out
}

// GetNodeShape takes as input and rdf2go graph and a term signifying a NodeShape
// and then iteratively queries the rdf2go graph to extract all its details
func (s *ShaclDocument) GetNodeShape(graph *rdf2go.Graph, term rdf2go.Term) (out NodeShape) {
	out.IRI = term
	triples := graph.All(term, nil, nil)
	var deps []dependency
	// fmt.Println("Found triples", triples)

	// isNodeShape := false // determine if its a proper NodeShape at all
	// var target TargetExpression
	// target = nil
	// var closed bool
	// var properties []PropertyShape
	// var positives []string
	// var negatives []string

	for i := range triples {
		switch triples[i].Predicate.RawValue() {
		// target expressions
		case _sh + "targetClass", _sh + "targetNode", _sh + "targetObjectsOf", _sh + "targetSubjectsOf":
			te := s.ExtractTargetExpression(graph, triples[i])
			out.target = append(out.target, te)
		// ValueTypes constraints
		case _sh + "class", _sh + "dataType", _sh + "nodeKind":
			vt := s.ExtractValueTypeConstraint(graph, triples[i])
			out.valuetypes = append(out.valuetypes, vt)
		// ValueRanges constraints
		case _sh + "minExclusive", _sh + "maxExclusive", _sh + "minInclusive", _sh + "maxInclusive":
			vr := s.ExtractValueRangeConstraint(graph, triples[i])
			out.valueranges = append(out.valueranges, vr)
		// string based Constraints
		case _sh + "minLength", _sh + "maxLength", _sh + "pattern", _sh + "languageIn":
			sr := s.ExtractStringBasedConstraint(graph, triples[i])
			out.stringconts = append(out.stringconts, sr)
		// property pair constraints
		case _sh + "equals", _sh + "disjoint", _sh + "lessThan", _sh + "lessThanOrEquals":
			pp := s.ExtractPropertyPairConstraint(graph, triples[i])
			out.propairconts = append(out.propairconts, pp)
		// Combine with PropertyShape constraint
		case _sh + "property":
			pshape := s.GetPropertyShape(graph, triples[i].Object)

			// pDeps := markPos(pshape.shape.deps, len(out.properties))
			deps = append(deps, pshape.shape.deps...) // should be ok
			out.properties = append(out.properties, pshape)
		// logic-based constraints
		case _sh + "and":
			ac := s.ExtractAndListConstraint(graph, triples[i])
			out.ands.shapes = append(out.ands.shapes, ac.shapes...) // simply add them to the pile
		case _sh + "or":
			oc := s.ExtractOrShapeConstraint(graph, triples[i])
			out.ors = append(out.ors, oc)
		case _sh + "not":
			ns := s.ExtractNotShapeConstraint(graph, triples[i])
			out.nots = append(out.nots, ns)
		case _sh + "xone":
			xs := s.ExtractXoneShapeConstraint(graph, triples[i])
			out.xones = append(out.xones, xs)
		// Combine with other NodeShape constraint
		case _sh + "node":
			var sr ShapeRef

			// check if blank (indicating an inlined shape def)
			_, ok := triples[i].Object.(*rdf2go.BlankNode)
			if ok {
				out2 := s.GetShape(graph, triples[i].Object)
				// if !ok {
				// 	log.Panicln("Invalid inline shape def. in Xone list")
				// }
				s.nodeShapes = append(s.nodeShapes, out2)
				s.shapeNames[triples[i].Object.RawValue()] = &out2
				sr.name, sr.ref = triples[i].Object.RawValue(), &out2
			} else {
				sr.name = triples[i].Object.RawValue()
			}

			out.nodes = append(out.nodes, sr)

			// qualified shape constraint
		case _sh + "qualifiedValueShape":
			qs := s.ExtractQSConstraint(graph, triples[i])
			out.qualifiedShapes = append(out.qualifiedShapes, qs)
		// closedness condition , with manually specifiable exceptions
		case _sh + "closed":
			tmp := triples[i].Object.RawValue()
			switch tmp {
			case "true":
				out.closed = true
			case "false":
				out.closed = false
			default:
				log.Panicln("closedConstraint not using proper value: ", triples[i])
			}
		case _sh + "ignoredProperties":
			// validation report related options
			// TODO
		case _sh + "hasValue":
			out.hasValue = &triples[i].Object
		case _sh + "in":
			out.in = append(out.in, s.ExtractInConstraint(graph, triples[i])...)
		case _sh + "severity":
			out.severity = &triples[i].Object
		case _sh + "message":
			out.message = &triples[i].Object
		// allows NodeShape to be manually turned off (i.e. not be considered in validation)
		case _sh + "deactivated":
			tmp := triples[i].Object.RawValue()
			switch tmp {
			case "true":
				out.deactivated = true
			case "false":
				out.deactivated = false
			default:
				log.Panicln("qualifiedValueShapesDisjoint not using proper value: ", triples[i])
			}
		}
	}

	// Dependency Check

	if len(out.ands.shapes) > 0 {
		dep := dependency{
			name:     out.ands.shapes,
			origin:   term.RawValue(),
			external: false, // and ref inside node shape is internal
			mode:     and,
		}
		deps = append(deps, dep)
	}

	for i := range out.ors {
		dep := dependency{
			name:     out.ors[i].shapes,
			origin:   term.RawValue(),
			external: false, // or ref inside node shape is internal
			mode:     or,
		}
		deps = append(deps, dep)
	}

	for i := range out.xones {
		dep := dependency{
			name:     out.xones[i].shapes,
			origin:   term.RawValue(),
			external: false, // or ref inside node shape is internal
			mode:     xone,
		}
		deps = append(deps, dep)
	}
	for i := range out.nots {
		dep := dependency{
			name:     []ShapeRef{out.nots[i].shape},
			origin:   term.RawValue(),
			external: false, // not ref inside node shape is internal
			mode:     not,
		}
		deps = append(deps, dep)
	}
	for i := range out.nodes {
		dep := dependency{
			name:     []ShapeRef{out.nodes[i]},
			origin:   term.RawValue(),
			external: false, // not ref inside node shape is internal
			mode:     and,   // collection of sh:node refs acts equivalent to one sh:and ref
		}
		deps = append(deps, dep)
	}

	for i := range out.qualifiedShapes {
		dep := dependency{
			name:     []ShapeRef{out.qualifiedShapes[i].shape},
			origin:   term.RawValue(),
			external: false, // not ref inside node shape is internal
			mode:     qualified,
			min:      out.qualifiedShapes[i].min,
			max:      out.qualifiedShapes[i].max,
		}
		deps = append(deps, dep)
	}

	out.deps = deps

	return out
}
