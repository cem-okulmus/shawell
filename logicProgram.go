package main

import (
	"errors"
	"fmt"
	"log"
	"os"
	"os/exec"
	"runtime"
	"sort"
	"strings"

	rdf "github.com/cem-okulmus/rdf2go-1"

	"github.com/alecthomas/participle"
	"github.com/alecthomas/participle/lexer"
	"github.com/alecthomas/participle/lexer/ebnf"
)

// the hardcoded address to DLV
var dlv = func() string {
	if runtime.GOOS == "windows" {
		return "bin/dlv.exe"
	}
	return "bin/dlv"
}()
var demoLP bool

var (
	renameMap  map[rdf.Term]string
	reverseMap map[string]rdf.Term
)

// rewrite generates a unique term identifier for an RDF term that hasn't been encoded yet.
// Maintains bidirectional mappings between original terms and their encoded identifiers.
func rewrite(term rdf.Term) string {
	if demoLP {
		return term.RawValue()
	}

	// check if already encoded
	if encoding, ok := renameMap[term]; ok {
		return encoding
	}

	var prefix string
	switch v := term.(type) {
	case rdf.Resource:
		prefix = "iri" // these must be lower-case, since they are constants (in DLV syntax)!
	case rdf.BlankNode:
		prefix = "blank"
	case rdf.Literal:
		prefix = "literal"
	default:
		fmt.Println("Type of term is: ", v)
		log.Panicln("Unknown type of rdf.Term.")
		// 	prefix = "Xerm"
	}

	newTerm := fmt.Sprint(prefix, theCount)
	theCount++

	reverseMap[newTerm] = term
	renameMap[term] = newTerm

	return newTerm
}

// // decode reconstructs an rdf.Term from an encoded string produced by rewrite.
// // It uses the prefix ("iri", "blank", "literal") to determine the concrete type
// // and looks up the original raw value in renameMap.
// func decode(encoded string) (rdf.Term, bool) {
// 	raw, present := renameMap[encoded]

// 	if present == false {
// 		return nil, present
// 	}
// 	switch {
// 	case strings.HasPrefix(encoded, "iri"):
// 		return rdf.NewResource(raw), present
// 	case strings.HasPrefix(encoded, "blank"):
// 		return rdf.NewBlankNode(raw), present
// 	case strings.HasPrefix(encoded, "literal"):
// 		return rdf.NewLiteral(raw), present
// 	case strings.HasPrefix(encoded, "term"):
// 		log.Panicln("Old term encoding still used somewhere.")
// 		return nil, present
// 	default: // in this case, res is being used to create a new IRI from a rawValue string
// 		log.Panicln("Illformated string present in renameMap: ", encoded)
// 		return nil, present
// 	}
// }

// serialisedRule represents the serialised logic program
type serialisedRule struct {
	head string
	body []string
}

// rewrite updates all occurrences of a substring in both the head and body of a rule.
func (r serialisedRule) rewrite(replace, with string) serialisedRule {
	head := strings.ReplaceAll(r.head, replace, with)
	body := make([]string, len(r.body))
	copy(body, r.body)

	for i := range r.body {
		body[i] = strings.ReplaceAll(body[i], replace, with)
	}

	return serialisedRule{head: head, body: body}
}

type serialisedProgram struct {
	rules []serialisedRule
}

// IsEmpty returns true if the logic program contains no rules.
func (p serialisedProgram) IsEmpty() bool {
	return len(p.rules) == 0
}

const (
	MaxUint = ^uint(0)
	MaxInt  = int(MaxUint >> 1)
)

type DLVAnswer struct {
	Negation  string   `parser:" @\"-\"? "`
	Predicate string   `parser:" @(Number|Ident|String) "`
	Constant  []string `parser:"\"(\" [ @(Number|Ident|String) { \",\" @(Number|Ident|String) } ] \")\""`
}

type DLVOutput struct {
	Answers          []DLVAnswer `parser:" \"True:\" \"{\" ( @@ \",\"?)* \"}\" "`
	UndefinedAnswers []DLVAnswer `parser:" \"Undefined:\" \"{\" ( @@ \",\"?)* \"}\" "`
}

// ToTables converts a DLV output into a slice of result tables, one per arity level.
// Each row contains [decoded_predicate, decoded_arg0, ...]; predicate is column 0.
func (d DLVOutput) ToTables() (out []Table[rdf.Term]) {
	arityMap := make(map[int][][]string)

	for i := range d.Answers {

		if d.Answers[i].Negation != "" {
			continue // skip negated results
		}

		p, v := d.Answers[i].Predicate, d.Answers[i].Constant

		arity := len(v) + 1
		tuple := []string{p}
		tuple = append(tuple, v...)

		prev, ok := arityMap[arity]
		if !ok {
			arityMap[arity] = [][]string{tuple}
		} else {
			arityMap[arity] = append(prev, tuple)
		}
	}

	for k, v := range arityMap {
		var tmp TableSimple[rdf.Term]

		header := []string{"predicate"}

		for i := range k - 1 {
			header = append(header, fmt.Sprint("argument ", i))
		}

		tmp.header = append(tmp.header, header...)

		// fmt.Println("Map content")
		// for k, v := range renameMap {
		// 	fmt.Println("Key ", k, " Value ", v)
		// }

		for i := range v {
			var actualTuple []rdf.Term

			for num, c := range v[i] {

				// column 0 used for the predicate -> never encoded hence nothing to decode
				if num == 0 {
					actualTuple = append(actualTuple, rdf.NewResource(c))
				} else {
					decoded, present := reverseMap[c]

					if !present {
						actualTuple = append(actualTuple, rdf.NewResource(c))
					} else {
						actualTuple = append(actualTuple, decoded)
					}

				}

			}

			tmp.content = append(tmp.content, actualTuple)
		}

		out = append(out, &tmp)
	}

	return out
}

// UndefinedToTables converts the Undefined set of a DLV output into tables, one per arity level.
func (d DLVOutput) UndefinedToTables() (out []Table[rdf.Term]) {
	arityMap := make(map[int][][]string)

	for i := range d.UndefinedAnswers {
		if d.UndefinedAnswers[i].Negation != "" {
			continue
		}
		p, v := d.UndefinedAnswers[i].Predicate, d.UndefinedAnswers[i].Constant
		arity := len(v) + 1
		tuple := []string{p}
		tuple = append(tuple, v...)
		prev, ok := arityMap[arity]
		if !ok {
			arityMap[arity] = [][]string{tuple}
		} else {
			arityMap[arity] = append(prev, tuple)
		}
	}

	for k, v := range arityMap {
		var tmp TableSimple[rdf.Term]
		header := []string{"predicate"}
		for i := range k - 1 {
			header = append(header, fmt.Sprint("argument ", i))
		}
		tmp.header = append(tmp.header, header...)
		for i := range v {
			var actualTuple []rdf.Term
			for num, c := range v[i] {
				// column 0 used for the predicate -> never encoded hence nothing to decode
				if num == 0 {
					actualTuple = append(actualTuple, rdf.NewResource(c))
				} else {
					decoded, present := reverseMap[c]

					if !present {
						actualTuple = append(actualTuple, rdf.NewResource(c))
					} else {
						actualTuple = append(actualTuple, decoded)
					}

				}
			}
			tmp.content = append(tmp.content, actualTuple)
		}
		out = append(out, &tmp)
	}
	return out
}

// runDLV invokes DLV under well-founded semantics and returns the parsed output.
// When debug is true the raw DLV output is printed, passed through DecodedString.
func (p serialisedProgram) runDLV(debug bool, nofacts bool) (DLVOutput, bool) {
	if p.IsEmpty() {
		return DLVOutput{}, false
	}

	graphLexer := lexer.Must(ebnf.New(`
    Comment = ("%" | "//") { "\u0000"…"\uffff"-"\n" } .
    Ident = (digit| alpha | "_") { Punct |  "_" | alpha | digit } .
    String = "\"" { "\u0000"…"\uffff"-"\""-"\\" | "\\" any } "\"" .
    Number = [ "-" | "+" ] ("." | digit) { "." | digit } .
    Punct = "." | ";"  | "_" | ":" | "!" | "?" | "\\" | "/" | "=" | "[" | "]" | "'" | "$" | "<" | ">" | "-" | "+" | "~" | "@" | "*" | "\""  .
    Parenthesis = "(" | ")"  | "," | "{" | "}".
    Whitespace = " " | "\t" | "\n" | "\r" .
    alpha = "a"…"z" | "A"…"Z" .
    digit = "0"…"9" .
    any = "\u0000"…"\uffff" .
    `))

	args := []string{"--wellfounded"}
	if nofacts {
		args = []string{"--wellfounded", "--no-facts"}
	}

	cmd := exec.Command(dlv, args...)
	outLP := p.String()
	cmd.Stdin = strings.NewReader(outLP)

	out, err := cmd.CombinedOutput()
	outString := string(out)

	if strings.Contains(outString, "INCOHERENT") {
		fmt.Fprintln(os.Stderr, "DLV semantic error: the logic program is incoherent (no model exists).")
		fmt.Fprintln(os.Stderr, "DLV output:\n", outString)
		os.Exit(1)
	}
	if strings.Contains(outString, "Safety Error") {
		fmt.Fprintln(os.Stderr, "DLV semantic error: safety violation detected (a variable appears only under negation without a positive occurrence).")
		fmt.Fprintln(os.Stderr, "DLV output:\n", outString)
		os.Exit(1)
	}

	check(err)

	if debug {
		fmt.Println("----\n\n", DecodedString(outString), "\n\n-------")
	}

	parser := participle.MustBuild(&DLVOutput{}, participle.UseLookahead(1), participle.Lexer(graphLexer),
		participle.Elide("Comment", "Whitespace"))

	// set max size for matchings in participle
	participle.MaxIterations = MaxInt

	var parsedDLVOutput DLVOutput
	err = parser.ParseString(outString, &parsedDLVOutput)
	if err != nil {
		fmt.Println("----\n\n", outLP, "\n\n-------")
		log.Panicln("input for parser: ", outString, "\n \n", err)
	}

	return parsedDLVOutput, true
}

// Answer sends the logic program to DLV configured for well-founded semantics and returns the computed interpretation.
// Returns (true tables, undefined tables), each grouped by predicate arity.
func (p serialisedProgram) Answer(debug bool, nofacts bool) ([]Table[rdf.Term], []Table[rdf.Term]) {
	out, ok := p.runDLV(debug, nofacts)
	if !ok {
		return []Table[rdf.Term]{}, []Table[rdf.Term]{}
	}
	return out.ToTables(), out.UndefinedToTables()
}

// String returns a string representation of the logic program with all rules.
func (p serialisedProgram) String() string {
	var sb strings.Builder

	for _, r := range p.rules {
		if len(r.body) > 0 { // rule
			sb.WriteString(fmt.Sprint(r.head, " :- ", strings.Join(r.body, ", "), ".\n"))
		} else { // fact
			sb.WriteString(fmt.Sprint(r.head, ". \n"))
		}
	}

	return sb.String()
}

// DecodedString returns a human-readable string representation of the logic program
// where each encoded term (e.g. iri0, literal3) is replaced by its original RDF value.
// Keys are applied longest-first to prevent partial-match corruption (e.g. iri10 vs iri1).
// Note: intended for debug use only; may mis-decode if original values contain encoded-looking substrings (e.g. "http://ex.org/iri1" ).
func DecodedString(encoded string) string {

	// collect keys sorted by descending length
	keys := make([]string, 0, len(reverseMap))
	for k := range reverseMap {
		keys = append(keys, k)
	}

	sort.Slice(keys, func(i, j int) bool { return len(keys[i]) > len(keys[j]) })

	for _, k := range keys {
		encoded = strings.ReplaceAll(encoded, k, reverseMap[k].RawValue())
	}

	return abbr(encoded)
}

var (
	qual    = 1
	xoneVar = 1
	orVar   = 1
)

// TODO expandRules needs to be heavily rewritten.
// It creates a set of rules that together ensure
// that a given shape name can be derived. The current
// code is super convoluted and prone to failure (and kind of impressive it even works)
// What is needed: a way to systemically modify and "split" rules

// expandRules generates logic program rules for handling SHACL constraints.
// It creates rules that encode cardinality constraints, disjointness, and other logical conditions.
func expandRules(valuesSlice []rdf.Term, indices []int, deps []dependency, header, element string) (out []serialisedRule) {
	// valuesSlice := strings.Split(strings.ToLower(values.RawValue()), " ")

	// for i := range valuesSlice {
	// 	valuesSlice[i] = "\"" + valuesSlice[i] + "\""
	// }

	head := fmt.Sprint(header, "(", element, ")")

	var externalRules []serialisedRule // these are needed in qualifiedShape and XONE, and don't directly
	// concern the general rule for this shape and element

	for _, i := range indices {
		switch deps[i].mode {
		case and, node: // should be ok?
			var body []string

			for _, ref := range deps[i].name {
				for _, v := range valuesSlice {
					body = append(body, fmt.Sprint(ref.GetLogName(), "(", rewrite(v), ")"))
				}
			}

			if len(out) == 0 {
				out = append(out, serialisedRule{head: head, body: body})
			} else {
				for j := range out {
					if len(out[j].body) == 0 {
						continue // don't attach stuff to facts
					}
					out[j].body = append(out[j].body, body...) // attach the ands to all prior rules
				}
			}
		case or:
			var bodyOr []string

			var orRules []serialisedRule

			// var bodyOne []string
			for _, v := range valuesSlice {
				bodyOr = append(bodyOr, fmt.Sprint("OrShape", orVar, "(", rewrite(v), ")"))

				for _, ref := range deps[i].name {
					orRules = append(orRules, serialisedRule{
						head: fmt.Sprint("OrShape", orVar, "(", rewrite(v), ")"),
						body: []string{fmt.Sprint(ref.ref.GetLogName(), "(", rewrite(v), ")")},
					})
				}
			}

			if len(out) == 0 {
				out = append(out, serialisedRule{head: head, body: bodyOr})
			} else {
			here:
				for j := range out {
					if len(out[j].body) == 0 {
						continue here // don't attach stuff to facts
					}
					out[j].body = append(out[j].body, bodyOr...) // attach the orRules to all prior rules
				}
			}

			// adding the value-specific or rules
			externalRules = append(externalRules, orRules...)

		case not:
			ref := deps[i].name[0].GetLogName() // not has only singular reference (in current design)

			var body []string
			for _, v := range valuesSlice {
				body = append(body, fmt.Sprint("not ", ref, "(", rewrite(v), ")"))
			}

			if len(out) == 0 {
				out = append(out, serialisedRule{head: head, body: body})
			} else {
				for j := range out {
					if len(out[j].body) == 0 {
						continue // don't attach stuff to facts
					}
					out[j].body = append(out[j].body, body...) // attach negated values to prior rules
				}
			}

		case xone: // will require some simple combinatorics

			var refs []string

			for k := range deps[i].name {
				refs = append(refs, deps[i].name[k].GetLogName())
			}

			var genericXONErules []serialisedRule

			headXONEgeneric := fmt.Sprint("XONE_TERM_", xoneVar, "( VAR )")

			for k := range refs {
				var body []string

				for j := range refs {
					var presPos string

					if j == k {
						presPos = " not "
					}
					body = append(body, fmt.Sprint(presPos, refs[j], "( VAR )"))
				}
				genericXONErules = append(genericXONErules, serialisedRule{head: headXONEgeneric, body: body})
			}

			// produce bound rules
			var boundRules []serialisedRule

			for v := range valuesSlice {
				for r := range genericXONErules {
					boundRules = append(boundRules, genericXONErules[r].rewrite("VAR", rewrite(valuesSlice[v]))) // #nosec G602 -- v ranges over valuesSlice
				}
			}

			var specificXONErule serialisedRule

			specificXONErule.head = fmt.Sprint("XONE_", xoneVar, "( ", element, " )")

			for v := range valuesSlice {
				specificXONErule.body = append(specificXONErule.body, fmt.Sprint("XONE_TERM_", xoneVar, "( ", rewrite(valuesSlice[v]), " )"))
			}

			// attach the XONE shape predicate to all prior rules
			if len(out) == 0 {
				out = append(out, serialisedRule{head: head, body: []string{specificXONErule.head}})
			} else {
				for j := range out {
					if len(out[j].body) == 0 {
						continue // don't attach stuff to facts
					}
					out[j].body = append(out[j].body, specificXONErule.head) // attach xone shape to all  prior rules
				}
			}

			// add XONE rules to the pile of external rules
			externalRules = append(externalRules, boundRules...)
			externalRules = append(externalRules, specificXONErule)

			xoneVar++
		case qualified: // will require crazy combinatorics
			ref := deps[i].name[0].GetLogName() // like not, qualified can only have single reference

			// When disjoint, any node matching a sibling qualified shape is excluded from counting.
			// Siblings are all other qualified deps not belonging to the current column (indices).
			var siblingRefs []string
			if deps[i].disjoint {
				inCurrent := make(map[int]bool)
				for _, idx := range indices {
					inCurrent[idx] = true
				}
				for si, d := range deps {
					if d.mode == qualified && !inCurrent[si] {
						siblingRefs = append(siblingRefs, d.name[0].GetLogName())
					}
				}
			}

			mark := fmt.Sprint("Qual", qual)
			atLeast := fmt.Sprint("AtLeast", qual)
			qual++

			qualHead := fmt.Sprint(mark, "Head(", element, ")")
			if len(out) == 0 {
				out = append(out, serialisedRule{head: head, body: []string{qualHead}})
			} else {
				for j := range out {
					if len(out[j].body) == 0 {
						continue // don't attach stuff to facts
					}

					out[j].body = append(out[j].body, qualHead) // attach qualfified to rule
				}
			}

			// var tmp string
			// if deps[i].max != -1 {
			// 	tmp = fmt.Sprint("count", mark, "Max(K), K >=", deps[i].min, ", K <= ", deps[i].max)
			// } else {
			// 	tmp = fmt.Sprint("count", mark, "Max(K), K >=", deps[i].min)
			// }

			// var tmp string
			// if deps[i].max != -1 {
			// 	tmp = fmt.Sprint("#count{ A  : ", mark, "(A), ", ref, "(A)  } = X, X >= ", deps[i].min, ", X <= ", deps[i].max)
			// } else {
			// 	tmp = fmt.Sprint("#count{ A  : ", mark, "(A), ", ref, "(A)  } >= ", deps[i].min)
			// }

			var tmp string

			minVal := deps[i].min
			maxVal := deps[i].max

			if deps[i].min != 0 {
				if deps[i].max != -1 {
					tmp = fmt.Sprint(atLeast, "Un(", minVal, "), not ", atLeast, "Un(", maxVal+1, ")")
				} else {
					tmp = fmt.Sprint(atLeast, "Un(", minVal, ")")
				}
			} else {
				if deps[i].max != -1 {
					tmp = fmt.Sprint("not ", atLeast, "Un(", maxVal+1, ")")
				} else {
					tmp = "" // empty since trivially satisfied
				}
			}

			qualifiedRule := serialisedRule{
				head: qualHead,
				body: strings.Split(tmp, ", "),
			}

			if tmp == "" { // make rule body empty when the tmp body is just ""
				qualifiedRule.body = nil
			}

			// tmp = fmt.Sprint("count", mark, "(X,K), not -count", mark, "Max(K)")
			// countMax1 := rule{
			// 	head: fmt.Sprint("count", mark, "Max(K)"),
			// 	body: strings.Split(tmp, ", "),
			// }

			// tmp = fmt.Sprint("count", mark, "(X,K), count", mark, "(Y,K+1)")
			// countMax2 := rule{
			// 	head: fmt.Sprint("-count", mark, "Max(K)"),
			// 	body: strings.Split(tmp, ", "),
			// }

			// tmp = fmt.Sprint("count", mark, "(Y,K-1), ", mark, "(X), ", ref,
			// 	"(X), Y < X, not -count", mark, "(X,K)")
			// countStep1 := rule{
			// 	head: fmt.Sprint("count", mark, "(X,K)"),
			// 	body: strings.Split(tmp, ", "),
			// }

			// tmp = fmt.Sprint("count", mark, "(Y,K-1), ", mark, "(X), ", ref,
			// 	"(X), Y < X, ", mark, "(Z), ", ref, "(Z), Y < Z, Z < X")
			// countStep2 := rule{
			// 	head: fmt.Sprint("-count", mark, "(X,K)"),
			// 	body: strings.Split(tmp, ", "),
			// }

			// tmp = fmt.Sprint(mark, "(X), ", ref, "(X), not -count", mark, "(X,1)")
			// countBase1 := rule{
			// 	head: fmt.Sprint("count", mark, "(X,1)"),
			// 	body: strings.Split(tmp, ", "),
			// }
			// tmp = fmt.Sprint(mark, "(X), ", ref, "(X), ", mark, "(Y), ", ref, "(Y), X > Y")
			// countBase2 := rule{
			// 	head: fmt.Sprint("-count", mark, "(X,1)"),
			// 	body: strings.Split(tmp, ", "),
			// }

			// rules := []rule{countBase1, countBase2, countStep1, countStep2, countMax1, countMax2, qualifiedRule}

			externalRules = append(externalRules, qualifiedRule)
			// attach facts to values to mark for counting
			for i, v := range valuesSlice {
				v1 := rewrite(v)
				if i == 0 {
					externalRules = append(externalRules,
						serialisedRule{head: fmt.Sprint(mark, "(", 0, ", ", v1, ")")})
					if i != len(valuesSlice)-1 {
						// #nosec G602 -- guarded by i != len-1
						v2 := rewrite(valuesSlice[i+1])
						externalRules = append(externalRules, serialisedRule{
							head: fmt.Sprint(mark, "(", v1, ", ", v2, ")"),
						})
					}

				} else if i == len(valuesSlice)-1 {
					externalRules = append(externalRules, serialisedRule{
						head: fmt.Sprint(mark, "(", v1, ", ", 1, ")"),
					})
				} else {
					v2 := rewrite(valuesSlice[i+1]) //gosec:disable G602 -- else-branch: i < len-1
					externalRules = append(externalRules, serialisedRule{
						head: fmt.Sprint(mark, "(", v1, ", ", v2, ")"),
					})
				}
			}

			// AtLeastRules
			externalRules = append(externalRules, serialisedRule{
				head: fmt.Sprint(atLeast, "(X,0)"),
				body: []string{fmt.Sprint(mark, "(0,X)")},
			})
			bodyBase1 := []string{
				fmt.Sprint(mark, "(0,X) "),
				fmt.Sprint(ref, "(X)"),
			}
			for _, sib := range siblingRefs {
				bodyBase1 = append(bodyBase1, fmt.Sprint("not ", sib, "(X)"))
			}
			externalRules = append(externalRules, serialisedRule{
				head: fmt.Sprint(atLeast, "(X,1)"),
				body: bodyBase1,
			})
			externalRules = append(externalRules, serialisedRule{
				head: fmt.Sprint(atLeast, "(Y,Z)"),
				body: []string{
					fmt.Sprint(mark, "(X,Y) "),
					fmt.Sprint(atLeast, "(X,Z)"),
				},
			})
			bodyStep := []string{
				fmt.Sprint(mark, "(X,Y) "),
				fmt.Sprint(atLeast, "(X,Z)"),
				fmt.Sprint(ref, "(Y)"),
			}
			for _, sib := range siblingRefs {
				bodyStep = append(bodyStep, fmt.Sprint("not ", sib, "(Y)"))
			}
			externalRules = append(externalRules, serialisedRule{
				head: fmt.Sprint(atLeast, "(Y,Z+1)"),
				body: bodyStep,
			})

			externalRules = append(externalRules, serialisedRule{
				head: fmt.Sprint(atLeast, "Un(Y)"),
				body: []string{
					fmt.Sprint(atLeast, "(X,Y)"),
				},
			})

		}
	}

	// only now add the external rules
	out = append(out, externalRules...)

	return out
}

// GetLogNameFromQualName is meant to transform a LogName into a QualName. Edge case: sometimes the attribute
// check is already in QualName, so in that case we just return it again.
func (s ShaclDocument) GetLogNameFromQualName(name string) (string, error) {

	for _, v := range s.shapeNames {
		switch vType := v.(type) {
		case *PropertyShape:
			if v.GetQualName() == name || v.GetLogName() == name {
				return v.GetLogName(), nil
			}
			test := NodeShape{}
			test.id = vType.id
			if test.GetQualName() == name || test.GetLogName() == name {
				return v.GetLogName(), nil
			}
		case *NodeShape:
			if v.GetQualName() == name || v.GetLogName() == name {
				return v.GetLogName(), nil
			}
		}
	}

	return "", errors.New("no shape with this qualname found: " + name)
}

// TableToLP converts a table representation of conditional answers into logic program rules.
// Each row in the table becomes facts or rules in the generated program.
func (s ShaclDocument) TableToLP(tablePreCast Table[rdf.Term], deps []dependency, internalDeps bool) (out serialisedProgram) {
	table, ok := tablePreCast.(*GroupedTable[rdf.Term])
	if !ok {
		log.Panicln("Passed a non-group Tabled")
	}

	// fmt.Println("Transforming table: ", table.GetHeader())

	header := table.GetHeader()
	table.Regroup()

	if len(table.group) < 1 && !internalDeps {
		log.Panicln("Not provided a conditional table")
	}

	// if internalDeps {
	// }

	// need to this nonsense, since the head variable needs more complex logic to handle (sadly)
	headerName, err := s.GetLogNameFromQualName(header[0])
	check(err)

	head := headerName + " (  VAR )"
	var body []string

	depMap := make(map[int]int)
	attrMap := make(map[int][]int)

	numMatched := 0

	if internalDeps {
		body = append(body, headerName+"INTERN(  VAR )")

		for i := range deps {
			if !deps[i].external {
				depMap[i] = 0
				attrMap[0] = append(attrMap[0], i)
				numMatched++
			}
		}

	}

	for j, attr := range header {
		// attrProper := strings.ReplaceAll(attr, "group", "") // remove the "group"
		if j == 0 {
			continue // skip this for the main elemnet
		}

		// need to this nonsense, since the head variable needs more complex logic to handle (sadly)
		attrName, err := s.GetLogNameFromQualName(attr)
		check(err)

		body = append(body, attrName+"( VAR )")

		matchingDepFound := false
		for i := range deps {
			// if dep[i]

			if deps[i].origin == attr {
				_, ok := depMap[i]
				if ok {
					log.Panicln("multiple appearances of attr ", attr, " in header")
				}
				matchingDepFound = true
				depMap[i] = j
				attrMap[j] = append(attrMap[j], i)
				numMatched++
			}
		}

		if !matchingDepFound {

			s.debug = true
			fmt.Println(s)

			fmt.Println("Header: ", header)
			fmt.Println("Dep origins: len(", len(deps), ") ")
			for i := range deps {
				fmt.Print(deps[i].origin, " ", "external: ", deps[i].external)
				fmt.Println("Comp res", deps[i].origin == attr)
			}
			log.Panicln("\nfor attribute ", attr, " there is no matching dependency")
		}
	}

	if numMatched != len(deps) {
		log.Panicln("Couldn't find a matching attribute for every dep")
	}

	generalRule := serialisedRule{head: head, body: body}

	// fmt.Println("Gotten general rule", generalRule)

	if len(table.group) < 1 {

		iterChan := table.IterTargets()

		for element := range iterChan {
			generalRuleNew := generalRule.rewrite("VAR", rewrite(element))
			out.rules = append(out.rules, generalRuleNew)

			// var tempRules []serialisedRule // collection of all rules generated so far
			// expandRules for target if InternDep
			tempRules := expandRules([]rdf.Term{element}, attrMap[0], deps, headerName+"INTERN", rewrite(element))

			out.rules = append(out.rules, tempRules...)
		}
	} else {
		for element, groupMap := range table.group {
			// element := row[0].RawValue()

			generalRuleNew := generalRule.rewrite("VAR", rewrite(element))
			out.rules = append(out.rules, generalRuleNew)

			var tempRules []serialisedRule // collection of all rules generated so far

			// expandRules for target if InternDep
			if internalDeps {
				tempRules = expandRules([]rdf.Term{element}, attrMap[0], deps, headerName+"INTERN", rewrite(element))
			}

			// for _, groupMap := range  {
			for index, values := range groupMap {
				headerIndexName, err := s.GetLogNameFromQualName(header[index])
				check(err)

				tempRules = append(tempRules, expandRules(values, attrMap[index], deps, headerIndexName, rewrite(element))...)
			}
			// }

			out.rules = append(out.rules, tempRules...)
		}
	}

	return out
}

// FactsToLP converts a unary table (single column) of facts into logic program facts.
// Panics if the input table has more than one column.
func (s ShaclDocument) FactsToLP(table Table[rdf.Term]) (out serialisedProgram) {
	header := table.GetHeader()
	if len(header) != 1 {
		log.Panic("FactsToLP requires unary table as input.")
	}

	// shape := header[0]

	// need to this nonsense, since the head variable needs more complex logic to handle (sadly)
	headerName, err := s.GetLogNameFromQualName(header[0])
	check(err)

	for row := range table.IterRows() {
		out.rules = append(out.rules, serialisedRule{head: fmt.Sprint(headerName, "(", rewrite(row[0]), ")")})
	}

	return out
}

// GetOneLP generates a logic program encoding all constraints for a single named shape.
// Returns the combined program with facts and rules for the shape and its dependencies.
func (s ShaclDocument) GetOneLP(name string) (out serialisedProgram) {
	if !s.answered {
		log.Panicln("Cannot produce logic programs, before conditional answers have been computed.")
	}

	shape, ok := s.shapeNames[name]

	if !ok {
		log.Panicln("Provided shape name does not exist in document.")
	}

	condTable, ok := s.condAnswers[name]

	// fmt.Println("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")
	// fmt.Println("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")
	// fmt.Println("Cond Table used in LP transformation; shape ", name)
	// fmt.Println("Table: \n ", condTable)
	// fmt.Println("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")
	// fmt.Println("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")

	if !ok { // no cond Table means there is nothing to do
		return out
	}

	deps := shape.GetDeps()

	areInternalDeps := false

	for i := range deps {
		if !deps[i].external {
			areInternalDeps = true
		}
	}
	if condTable.Len() == 0 {
		return out // empty program, since nothing in Table
	}

	// check if it is indeed a conditional table
	if len(condTable.GetHeader()) == 1 && !areInternalDeps {
		// fmt.Println("Shape: ", name, " had already uncond Table.")
		return s.FactsToLP(condTable)
	}

	// fmt.Println("For shape ", name, " computing LP with deps ", deps)
	return s.TableToLP(condTable, deps, areInternalDeps)
}

// GetAllLPs generates a logic program encoding all constraints for all shapes in the document.
// Returns a unified program that can be sent to the DLV solver.
func (s ShaclDocument) GetAllLPs() (out serialisedProgram) {
	for name, value := range s.shapeNames {

		// fmt.Println("Producing LP for shape ", value.GetQualName())

		if !value.IsActive() {
			continue
		}

		outTmp := s.GetOneLP(name)

		// fmt.Println("For shape ", value.GetQualName(), " I got the program ", outTmp, "  with ", len(outTmp.rules))

		out.rules = append(out.rules, outTmp.rules...)
	}

	return out
}
