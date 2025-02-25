package main

import (
	"errors"
	"fmt"
	"log"
	"os/exec"
	"strings"

	rdf "github.com/cem-okulmus/rdf2go-1"

	"github.com/alecthomas/participle"
	"github.com/alecthomas/participle/lexer"
	"github.com/alecthomas/participle/lexer/ebnf"
)

// the hardcoded address to DLV
var dlv string = "bin/dlv"
var demoLP bool

var (
	renameMap  map[string]string
	reverseMap map[string]string
)

func rewrite(term rdf.Term) string {
	if demoLP {
		return term.RawValue()
	}

	// check if already encoded
	if _, ok := reverseMap[term.RawValue()]; ok {
		return reverseMap[term.RawValue()]
	}

	newTerm := fmt.Sprint("term", theCount)
	theCount++

	reverseMap[term.RawValue()] = newTerm
	renameMap[newTerm] = term.RawValue()

	// testString := removeAbbr(strings.ToLower(term.RawValue()))
	// rewriteSuccess := false

	// for !rewriteSuccess {
	// 	if oldTerm, ok := renameMap[testString]; ok {
	// 		if oldTerm == term.RawValue() { // trying to encode the same string again
	// 			// fmt.Println("found exsisting term", term.RawValue())
	// 			return testString
	// 		} else { // CONFLICT!
	// 			// fmt.Println("Conflict: ", oldTerm, " ", term)
	// 			testString = testString + "conflict"
	// 			continue
	// 		}
	// 	}
	// 	renameMap[testString] = term.RawValue()
	// 	rewriteSuccess = true
	// }
	return newTerm
}

type rule struct {
	head string
	body []string
}

func (r rule) rewrite(replace, with string) rule {
	head := strings.ReplaceAll(r.head, replace, with)
	body := make([]string, len(r.body))
	copy(body, r.body)

	for i := range r.body {
		body[i] = strings.ReplaceAll(body[i], replace, with)
	}

	return rule{head: head, body: body}
}

type program struct {
	rules []rule
}

func (p program) IsEmpty() bool {
	return len(p.rules) == 0
}

const (
	MaxUint = ^uint(0)
	MinUint = 0
	MaxInt  = int(MaxUint >> 1)
	MinInt  = -MaxInt - 1
)

type DLVAnswer struct {
	Negation  string   ` @"-"? `
	Predicate string   ` @(Number|Ident|String) `
	Constant  []string `"("  @ (( Number|Ident|String) ","?)*  ")" `
}

type DLVOutput struct {
	Answers []DLVAnswer ` "True:" "{" ( @@ ","?)* "}" (String|Ident|Number|Punct) "{" (Number|Ident|String|Punct|"("|")"|","|" ")*  "}" `
}

func (d DLVOutput) ToTables() (out []Table[rdf.Term]) {
	answerMap := make(map[string][]string)

	for i := range d.Answers {

		if d.Answers[i].Negation != "" {
			continue // skip negated results
		}

		p, v := d.Answers[i].Predicate, d.Answers[i].Constant

		prev, ok := answerMap[p]
		if !ok {
			answerMap[p] = []string{v[0]}
		} else {
			answerMap[p] = append(prev, v[0])
		}
	}

	for k, v := range answerMap {
		var tmp TableSimple[rdf.Term]

		tmp.header = append(tmp.header, k)

		// fmt.Println("Map content")
		// for k, v := range renameMap {
		// 	fmt.Println("Key ", k, " Value ", v)
		// }

		for i := range v {
			actualValue := renameMap[v[i]]
			// fmt.Println("Actual Value ", actualValue, " of term ", v[i])
			tmp.content = append(tmp.content, []rdf.Term{res(actualValue)})
		}

		out = append(out, &tmp)
	}

	return out
}

// Answer sends the logic program to DLV, set to use well-founded semantics, and returns the output
func (p program) Answer(debug bool) []Table[rdf.Term] {
	if p.IsEmpty() {
		return []Table[rdf.Term]{}
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

	cmd := exec.Command(dlv, "--wellfounded")

	outLP := p.String()

	cmd.Stdin = strings.NewReader(outLP)

	out, err := cmd.Output()
	check(err)

	outString := string(out)

	if debug {
		fmt.Println("----\n\n", outString, "\n\n-------")
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

	return parsedDLVOutput.ToTables()
}

func (p program) String() string {
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

var (
	qual    int = 1
	xoneVar int = 1
	orVar   int = 1
)

func expandRules(valuesSlice []rdf.Term, indices []int, deps []dependency, header, element string) (out []rule) {
	// valuesSlice := strings.Split(strings.ToLower(values.RawValue()), " ")

	// for i := range valuesSlice {
	// 	valuesSlice[i] = "\"" + valuesSlice[i] + "\""
	// }

	head := fmt.Sprint(header, "(", element, ")")

	var externalRules []rule // these are needed in qualifiedShape and XONE, and don't directly
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
				out = append(out, rule{head: head, body: body})
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

			var orRules []rule

			// var bodyOne []string
			for _, v := range valuesSlice {
				bodyOr = append(bodyOr, fmt.Sprint("OrShape", orVar, "(", rewrite(v), ")"))

				for _, ref := range deps[i].name {
					orRules = append(orRules, rule{
						head: fmt.Sprint("OrShape", orVar, "(", rewrite(v), ")"),
						body: []string{fmt.Sprint(ref.ref.GetLogName(), "(", rewrite(v), ")")},
					})
				}
			}

			if len(out) == 0 {
				out = append(out, rule{head: head, body: bodyOr})
			} else {
				var newOut []rule
			here:
				for j := range out {
					if len(out[j].body) == 0 {
						continue here // don't attach stuff to facts
					}
					out[j].body = append(out[j].body, bodyOr...) // attach the orRules to all prior rules
				}
				out = newOut
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
				out = append(out, rule{head: head, body: body})
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

			var genericXONErules []rule

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
				genericXONErules = append(genericXONErules, rule{head: headXONEgeneric, body: body})
			}

			// produce bound rules
			var boundRules []rule

			for v := range valuesSlice {
				for r := range genericXONErules {
					boundRules = append(boundRules, genericXONErules[r].rewrite("VAR", rewrite(valuesSlice[v])))
				}
			}

			var specificXONErule rule

			specificXONErule.head = fmt.Sprint("XONE_", xoneVar, "( ", element, " )")

			for v := range valuesSlice {
				specificXONErule.body = append(specificXONErule.body, fmt.Sprint("XONE_TERM_", xoneVar, "( ", rewrite(valuesSlice[v]), " )"))
			}

			// attach the XONE shape predicate to all prior rules
			if len(out) == 0 {
				out = append(out, rule{head: head, body: []string{specificXONErule.head}})
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

			mark := fmt.Sprint("Qual", qual)
			atLeast := fmt.Sprint("AtLeast", qual)
			qual++

			if len(out) == 0 {
				// out = append(out, rule{head: head, body: []string{head}})
			} else {
				for j := range out {
					if len(out[j].body) == 0 {
						continue // don't attach stuff to facts
					}

					out[j].body = append(out[j].body, head) // attach qualfified to rule
				}
			}
			// qualHead := fmt.Sprint(mark, "Head(", element, ")")

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

			min := deps[i].min
			max := deps[i].max

			if deps[i].min != 0 {
				if deps[i].max != -1 {
					tmp = fmt.Sprint(atLeast, "Un(", min, "), not ", atLeast, "Un(", max+1, ")")
				} else {
					tmp = fmt.Sprint(atLeast, "Un(", min, ")")
				}
			} else {
				if deps[i].max != -1 {
					tmp = fmt.Sprint("not ", atLeast, "Un(", max+1, ")")
				} else {
					tmp = "" // empty since trivially satisfied
				}
			}

			qualifiedRule := rule{
				head: head,
				body: strings.Split(tmp, ", "),
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
				v_i := rewrite(v)
				if i == 0 {
					externalRules = append(externalRules,
						rule{head: fmt.Sprint(mark, "(", 0, ", ", v_i, ")")})
					if i != len(valuesSlice)-1 {
						v_ii := rewrite(valuesSlice[i+1])
						externalRules = append(externalRules, rule{
							head: fmt.Sprint(mark, "(", v_i, ", ", v_ii, ")"),
						})
					}

				} else if i == len(valuesSlice)-1 {
					externalRules = append(externalRules, rule{
						head: fmt.Sprint(mark, "(", v_i, ", ", 1, ")"),
					})
				} else {
					v_ii := rewrite(valuesSlice[i+1])
					externalRules = append(externalRules, rule{
						head: fmt.Sprint(mark, "(", v_i, ", ", v_ii, ")"),
					})
				}
			}

			// AtLeastRules
			externalRules = append(externalRules, rule{
				head: fmt.Sprint(atLeast, "(X,0)"),
				body: []string{fmt.Sprint(mark, "(0,X)")},
			})
			externalRules = append(externalRules, rule{
				head: fmt.Sprint(atLeast, "(X,1)"),
				body: []string{
					fmt.Sprint(mark, "(0,X) "),
					fmt.Sprint(ref, "(X)"),
				},
			})
			externalRules = append(externalRules, rule{
				head: fmt.Sprint(atLeast, "(Y,Z)"),
				body: []string{
					fmt.Sprint(mark, "(X,Y) "),
					fmt.Sprint(atLeast, "(X,Z)"),
				},
			})
			externalRules = append(externalRules, rule{
				head: fmt.Sprint(atLeast, "(Y,Z+1)"),
				body: []string{
					fmt.Sprint(mark, "(X,Y) "),
					fmt.Sprint(atLeast, "(X,Z)"),
					fmt.Sprint(ref, "(Y)"),
				},
			})

			externalRules = append(externalRules, rule{
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
			if v.GetQualName() == name || v.GetLogName() == name  {
				return v.GetLogName(), nil
			}
			test := NodeShape{}
			test.id = vType.id
			if test.GetQualName() == name || test.GetLogName() == name  {
				return v.GetLogName(), nil
			}
		case *NodeShape:
			if v.GetQualName() == name || v.GetLogName() == name  {
				return v.GetLogName(), nil
			}
		}
	}

	return "", errors.New("no shape with this qualname found: " + name)
}

func (s ShaclDocument) TableToLP(tablePreCast Table[rdf.Term], deps []dependency, internalDeps bool) (out program) {
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

	generalRule := rule{head: head, body: body}

	// fmt.Println("Gotten general rule", generalRule)

	if len(table.group) < 1 {

		iterChan := table.IterTargets()

		for element := range iterChan {
			generalRuleNew := generalRule.rewrite("VAR", rewrite(element))
			out.rules = append(out.rules, generalRuleNew)

			var tempRules []rule // collection of all rules generated so far
			// expandRules for target if InternDep
			tempRules = expandRules([]rdf.Term{element}, attrMap[0], deps, headerName+"INTERN", rewrite(element))

			out.rules = append(out.rules, tempRules...)
		}
	} else {
		for element, groupMap := range table.group {
			// element := row[0].RawValue()

			generalRuleNew := generalRule.rewrite("VAR", rewrite(element))
			out.rules = append(out.rules, generalRuleNew)

			var tempRules []rule // collection of all rules generated so far

			// expandRules for target if InternDep
			if internalDeps {
				tempRules = expandRules([]rdf.Term{element}, attrMap[0], deps, headerName+"INTERN", rewrite(element))
			}

			// for _, groupMap := range  {
			for index, values := range groupMap {
				headerIndexName, err := s.GetLogNameFromQualName(header[index])
				check(err)

				tempRules = expandRules(values, attrMap[index], deps, headerIndexName, rewrite(element))
			}
			// }

			out.rules = append(out.rules, tempRules...)
		}
	}

	return out
}

// FactsToLP assumes that the input is a unary table, ie. with only one column, will panic otherwise
func (s ShaclDocument) FactsToLP(table Table[rdf.Term]) (out program) {
	header := table.GetHeader()
	if len(header) != 1 {
		log.Panic("FactsToLP requires unary table as input.")
	}

	// shape := header[0]

	// need to this nonsense, since the head variable needs more complex logic to handle (sadly)
	headerName, err := s.GetLogNameFromQualName(header[0])
	check(err)

	for row := range table.IterRows() {
		out.rules = append(out.rules, rule{head: fmt.Sprint(headerName, "(", rewrite(row[0]), ")")})
	}

	return out
}

func (s ShaclDocument) GetOneLP(name string) (out program) {
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

func (s ShaclDocument) GetAllLPs() (out program) {
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
