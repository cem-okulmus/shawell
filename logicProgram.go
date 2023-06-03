package main

import (
	"fmt"
	"log"
	"os/exec"
	"strings"

	rdf "github.com/deiu/rdf2go"

	"github.com/alecthomas/participle"
	"github.com/alecthomas/participle/lexer"
	"github.com/alecthomas/participle/lexer/ebnf"
)

// the hardcoded address to DLV
var dlv string = "bin/dlv"

type rule struct {
	head string
	body []string
}

func (r rule) rewrite(replace, with string) rule {
	head := strings.ReplaceAll(r.head, replace, with)
	var body []string = make([]string, len(r.body))
	copy(body, r.body)

	for i := range r.body {
		body[i] = strings.ReplaceAll(body[i], replace, with)
	}

	return rule{head: head, body: body}
}

type program struct {
	rules []rule
}

// TODO: no nice parsing back into the unconditional tables yet.

type DLVAnswer struct {
	Predicate string ` @(Number|Ident|String) `
	Constant  string `"(" ( @(Number|Ident|String) ) ")" `
}

type DLVOutput struct {
	Answers []DLVAnswer ` (String|Ident|Number|Punct) "{" ( @@ ","?)* "}" (String|Ident|Number|Punct) "{" (Number|Ident|String|Punct|"("|")"|","|" ")*  "}" `
}

func (d DLVOutput) ToTables() (out []Table) {
	answerMap := make(map[string][]string)

	for i := range d.Answers {

		p, v := d.Answers[i].Predicate, d.Answers[i].Constant

		prev, ok := answerMap[p]
		if !ok {
			answerMap[p] = []string{v}
		} else {
			answerMap[p] = append(prev, v)
		}
	}

	for k, v := range answerMap {
		var tmp Table

		tmp.header = append(tmp.header, k)

		for i := range v {
			tmp.content = append(tmp.content, []rdf.Term{res(v[i])})
		}

		out = append(out, tmp)
	}

	return out
}

// Answer sends the logic program to DLV, set to use well-founded semantics, and returns the output
func (p program) Answer() []Table {
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

	// fmt.Println("----\n\n,", outLP, "\n\n-------")

	out, _ := cmd.Output()
	// check(err)

	outString := fmt.Sprintf("%s", out)

	parser := participle.MustBuild(&DLVOutput{}, participle.UseLookahead(1), participle.Lexer(graphLexer),
		participle.Elide("Comment", "Whitespace"))

	var parsedDLVOutput DLVOutput
	err := parser.ParseString(outString, &parsedDLVOutput)
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

	return removeAbbr(sb.String())
}

var qual int = 1

func expandRules(values rdf.Term, indices []int, deps []dependency, header, element string) (out []rule) {
	valuesSlice := strings.Split(strings.ToLower(values.RawValue()), " ")

	for i := range valuesSlice {
		valuesSlice[i] = "\"" + valuesSlice[i] + "\""
	}

	head := fmt.Sprint(header, "(\"", strings.ToLower(element), "\")")

	for _, i := range indices {
		switch deps[i].mode {
		case and:
			var body []string

			for _, ref := range deps[i].name {
				for _, v := range valuesSlice {
					body = append(body, fmt.Sprint(ref.name, "(", v, ")"))
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
			var bodyAll [][]string

			for _, ref := range deps[i].name {
				var bodyOne []string
				for _, v := range valuesSlice {
					bodyOne = append(bodyOne, fmt.Sprint(ref.name, "(", v, ")"))
				}
				bodyAll = append(bodyAll, bodyOne)
			}

			if len(out) == 0 {
				for _, b := range bodyAll {
					for _, bs := range b {
						out = append(out, rule{head: head, body: []string{bs}})
					}
				}
			} else {
				var newOut []rule
			here:
				for j := range out {
					if len(out[j].body) == 0 {
						continue here // don't attach stuff to facts
					}
					old := out[j]

					for _, b := range bodyAll {
						for _, bs := range b {
							old.body = append(old.body, bs)
							newOut = append(newOut, old)
						}
					}
				}
			}
		case not:
			ref := deps[i].name[0].name // not has only singular reference (in current design)

			var body []string
			for _, v := range valuesSlice {
				body = append(body, fmt.Sprint("not ", ref, "(", v, ")"))
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
			log.Panicln("XONE not supported yet")
		case qualified: // will require crazy combinatorics
			ref := deps[i].name[0].name // like not, qualified can only have single reference

			mark := fmt.Sprint("Qual", qual)
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

			var tmp string
			if deps[i].max != 0 {
				tmp = fmt.Sprint("count", mark, "Max(K), K >=", deps[i].min, ", K <= ", deps[i].max)
			} else {
				tmp = fmt.Sprint("count", mark, "Max(K), K >=", deps[i].min)
			}

			qualifiedRule := rule{
				head: head,
				body: strings.Split(tmp, ", "),
			}

			tmp = fmt.Sprint("count", mark, "(X,K), not -count", mark, "Max(K)")
			countMax1 := rule{
				head: fmt.Sprint("count", mark, "Max(K)"),
				body: strings.Split(tmp, ", "),
			}

			tmp = fmt.Sprint("count", mark, "(X,K), count", mark, "(Y,K+1)")
			countMax2 := rule{
				head: fmt.Sprint("-count", mark, "Max(K)"),
				body: strings.Split(tmp, ", "),
			}

			tmp = fmt.Sprint("count", mark, "(Y,K-1), ", mark, "(X), ", ref,
				"(X), Y < X, not -count", mark, "(X,K)")
			countStep1 := rule{
				head: fmt.Sprint("count", mark, "(X,K)"),
				body: strings.Split(tmp, ", "),
			}

			tmp = fmt.Sprint("count", mark, "(Y,K-1), ", mark, "(X), ", ref,
				"(X), Y < X, ", mark, "(Z), ", ref, "(Z), Y < Z, Z < X")
			countStep2 := rule{
				head: fmt.Sprint("-count", mark, "(X,K)"),
				body: strings.Split(tmp, ", "),
			}

			tmp = fmt.Sprint(mark, "(X), ", ref, "(X), not -count", mark, "(X,1)")
			countBase1 := rule{
				head: fmt.Sprint("count", mark, "(X,1)"),
				body: strings.Split(tmp, ", "),
			}
			tmp = fmt.Sprint(mark, "(X), ", ref, "(X), ", mark, "(Y), ", ref, "(Y), X > Y")
			countBase2 := rule{
				head: fmt.Sprint("-count", mark, "(X,1)"),
				body: strings.Split(tmp, ", "),
			}

			rules := []rule{countBase1, countBase2, countStep1, countStep2, countMax1, countMax2, qualifiedRule}

			out = append(out, rules...)
			// attach facts to values to mark for counting
			for _, v := range valuesSlice {
				out = append(out, rule{head: fmt.Sprint(mark, "(", v, ")")})
			}

		}
	}

	return out
}

func (s ShaclDocument) TableToLP(table Table, deps []dependency, internalDeps bool) (out program) {
	if len(table.header) <= 1 && !internalDeps {
		log.Panicln("Not provided a conditional table")
	}

	if internalDeps {
	}

	head := table.header[0] + " (  VAR )"
	var body []string

	var depMap map[int]int = make(map[int]int)
	var attrMap map[int][]int = make(map[int][]int)

	numMatched := 0

	if internalDeps {
		body = append(body, table.header[0]+"INTERN(  VAR )")

		for i := range deps {
			if !deps[i].external {
				depMap[i] = 0
				attrMap[0] = append(attrMap[0], i)
				numMatched++
			}
		}

	}

	for j, attr := range table.header {
		if j == 0 {
			continue // skip this for the main elemnet
		}
		body = append(body, attr+"( VAR )")

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
			log.Panicln("for attribute ", attr, " there is matching dependency")
		}
	}

	if numMatched != len(deps) {
		log.Panicln("Couldn't find a matching attribute for every dep")
	}

	generalRule := rule{head: head, body: body}

	for _, row := range table.content {
		element := row[0].RawValue()

		generalRuleNew := generalRule.rewrite("VAR", "\""+strings.ToLower(element)+"\"")
		out.rules = append(out.rules, generalRuleNew)

		var tempRules []rule // collection of all rules generated so far

		for i, values := range row {
			if i == 0 {
				if internalDeps {
					tempRules = expandRules(values, attrMap[i], deps, table.header[i]+"INTERN", element)
				}
				continue
			}

			tempRules = expandRules(values, attrMap[i], deps, table.header[i], element)
		}

		out.rules = append(out.rules, tempRules...)

	}
	return out
}

// FactsToLP assumes that the input is a unary table, ie. with only one column, will panic otherwise
func (s ShaclDocument) FactsToLP(table Table) (out program) {
	if len(table.header) != 1 {
		log.Panic("FactsToLP requires unary table as input.")
	}

	shape := table.header[0]

	for _, row := range table.content {
		out.rules = append(out.rules, rule{head: fmt.Sprint(shape, "(", row[0].RawValue(), ")")})
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

	if !ok {
		log.Panic("conditional Answer for shape has not been produced yet", name)
	}

	deps := (*shape).GetDeps()

	areInternalDeps := false

	for i := range deps {
		if !deps[i].external {
			areInternalDeps = true
		}
	}
	if len(condTable.content) == 0 {
		return out // empty program, since nothing in Table
	}

	// check if it is indeed a conditional table
	if len(condTable.content[0]) == 1 && !areInternalDeps {
		// fmt.Println("Shape: ", name, " had already uncond Table.")
		return s.FactsToLP(condTable)
	}

	// fmt.Println("For shape ", name, " computing LP with deps ", deps)
	return s.TableToLP(condTable, deps, areInternalDeps)
}

func (s ShaclDocument) GetAllLPs() (out program) {
	for name, value := range s.shapeNames {

		if !(*value).IsActive() {
			continue
		}

		outTmp := s.GetOneLP(name)

		out.rules = append(out.rules, outTmp.rules...)
	}

	return out
}
