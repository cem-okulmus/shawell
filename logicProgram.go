package main

import (
	"fmt"
	"log"
	"strings"

	rdf "github.com/deiu/rdf2go"
)

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

func (p program) String() string {
	var sb strings.Builder

	for _, r := range p.rules {
		if len(r.body) > 0 { // rule
			sb.WriteString(fmt.Sprint(r.head, " :- ", strings.Join(r.body, ", "), ".\n"))
		} else { // fact
			sb.WriteString(fmt.Sprint(r.head, ". \n"))
		}
	}

	return abbr(sb.String())
}

func expandRules(values rdf.Term, indices []int, deps []dependency, head string) (out []rule) {
	valuesSlice := strings.Split(values.RawValue(), " ")

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
				for j := range out {
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
			ref := deps[i].name[0] // not has only singular reference (in current design)

			var body []string
			for _, v := range valuesSlice {
				body = append(body, fmt.Sprint("~", ref.name, "(", v, ")"))
			}

			if len(out) == 0 {
				out = append(out, rule{head: head, body: body})
			} else {
				for j := range out {
					out[j].body = append(out[j].body, body...) // attach negated values to prior rules
				}
			}

		case xone: // will require some simple combinatorics
		case qualified: // will require crazy combinatorics
			log.Panicln("Qualified Shape Value not supported yet")
		}
	}

	return out
}

func (s ShaclDocument) TableToLP(table Table, deps []dependency) (out program) {
	if len(table.header) <= 1 {
		log.Panicln("Not provided a conditional table")
	}

	head := table.header[0] + " (  VAR )"
	var body []string

	var depMap map[int]int = make(map[int]int)
	var attrMap map[int][]int = make(map[int][]int)

	numMatched := 0

	for j, attr := range table.header {
		if j == 0 {
			continue // skip this for the main elemnet
		}
		body = append(body, attr+"( VAR )")

		matchingDepFound := false
		for i := range deps {
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

		generalRuleNew := generalRule.rewrite("VAR", element)
		out.rules = append(out.rules, generalRuleNew)

		var tempRules []rule // collection of all rules generated so far

		for i, values := range row {
			if i == 0 {
				continue // skip this for the main elemnet
			}

			tempRules = expandRules(values, attrMap[i], deps, table.header[i]+"( "+element+" )")
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

func (s ShaclDocument) ToLP(name string) (out program) {
	if !s.answered {
		log.Panicln("Cannot produce logic programs, before conditional answers have been computed.")
	}

	shape, ok := s.shapeNames[name]
	if !ok {
		log.Panicln("Provided shape name does not exist in document.")
	}

	condTable, ok := s.condAnswers[name]
	if !ok {
		log.Panic("conditional Answer for shape has not been produced yet", name)
	}

	// check if it is indeed a conditional table
	if len(condTable.content[0]) == 1 {
		return s.FactsToLP(condTable)
	}

	return s.TableToLP(condTable, (*shape).GetDeps())
}
