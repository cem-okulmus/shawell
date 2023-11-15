package main

import (
	"errors"
	"fmt"
	"log"
	"sort"
	"strings"
	"text/tabwriter"

	rdfA "github.com/knakk/rdf"

	rdf "github.com/cem-okulmus/rdf2go-1"
	"github.com/cem-okulmus/sparql"
)

// GetTable returns from a query result a table, and a header of shape names

type stringer interface {
	comparable
	String() string
}

type Table[T stringer] interface {
	GetColumn(column int) ([]T, error)    // Get a column based on index, if a valid index
	GetAttribute(att string) ([]T, error) // Get a column via its attribute name, if exists
	IterRows() chan []T                   // iterate over rows the table (in ordered fashion)
	GetHeader() []string                  // header required to be strings
	AddRow([]T)                           // add a Row to the Table
	Merge(Table[T]) error                 // merging two tables together, if they share headers
	Len() int
	String() string
	Limit(int) string
}

type TableSimple[T stringer] struct {
	header  []string
	content [][]T
}

func (t *TableSimple[T]) String() string {
	return t.Limit(len(t.content))
}

func (t *TableSimple[T]) Len() int { return len(t.content) }

func (t *TableSimple[T]) GetColumn(column int) ([]T, error) {
	var out []T

	if column >= len(t.header) || column < 0 {
		return []T{}, errors.New("Out of bounds error.")
	}

	for i := range t.content {
		out = append(out, t.content[i][column])
	}

	return out, nil
}

func (t *TableSimple[T]) GetAttribute(att string) ([]T, error) {
	var column int = -1

	// find attribute
	for i := range t.header {
		if t.header[i] == att {
			column = i
		}
	}
	if column == -1 {
		return []T{}, errors.New("Attribute not found error.")
	}

	return t.GetColumn(column)
}

func (t *TableSimple[T]) IterRows() chan []T {
	out := make(chan []T)

	go func() {
		for i := range t.content {
			out <- t.content[i]
		}
		close(out) // hope it's ok to close this at this point
	}()

	return out
}

func (t *TableSimple[T]) GetHeader() []string { return t.header }

func (t *TableSimple[T]) AddRow(row []T) { t.content = append(t.content, row) }

func (t TableSimple[T]) Limit(n int) string {
	if n > len(t.content) {
		n = len(t.content)
	}
	var sb strings.Builder
	const padding = 4
	w := tabwriter.NewWriter(&sb, 0, 0, padding, ' ', tabwriter.TabIndent)

	fmt.Fprint(w, "\n", strings.Join(t.header, "\t"), "\t\n")

	for i := range t.content[:n] {

		for j := range t.content[i] {
			fmt.Fprint(w, t.content[i][j].String())
			fmt.Fprint(w, "\t ")
		}
		fmt.Fprint(w, "\n")
	}

	if n < len(t.content) {
		fmt.Fprint(w, "\n\n\t\t⋮ (showing first ",
			n, " lines from ", len(t.content), " total) \n")
	} else {
		fmt.Fprint(w, "\n\t\t ( Total: ", len(t.content), " lines) \n")
	}

	err := w.Flush()
	check(err)
	return abbr(sb.String())
}

func (t *TableSimple[T]) Merge(other Table[T]) error {
	// check if the two tables share the same header

	otherCast, ok := other.(*TableSimple[T])
	if !ok {
		return errors.New("Cannot merge a SimpleTable with different kind")
	}
	if len(t.header) != len(otherCast.header) {
		return errors.New("Incompatible tables to merge")
	}
	for i := range t.header {
		if t.header[i] != otherCast.header[i] {
			return errors.New("Incompatible tables to merge")
		}
	}

	t.content = append(t.content, otherCast.content...)

	return nil
}

func GetTable(r *sparql.Results) *TableSimple[rdf.Term] {
	// for i := range r.Results.Bindings {
	// 	for k, v := range r.Results.Bindings[i] {
	// 		fmt.Println("Key ", k)

	// 		fmt.Println("Type: ", v.Type)
	// 		fmt.Println("Value: ", v.Value)
	// 		fmt.Println("Lang: ", v.Lang)
	// 		fmt.Println("DataType: ", v.DataType)
	// 	}
	// }

	var resultTable [][]rdf.Term

	var ordering map[string]int = make(map[string]int)

	for i, s := range r.Head.Vars {
		ordering[s] = i
	}

	for _, t := range r.Solutions() {
		// var tupleOrdered []rdf.Term = make([]rdf.Term, len(t))

		var tupleOrdered []rdf.Term = make([]rdf.Term, len(r.Head.Vars))

		for _, s := range r.Head.Vars {

			v := t[s]
			var err error
			if v == nil {
				v, err = rdfA.NewBlank(fmt.Sprint("blank", getCount()))
				check(err)
			}

			// if v.String() == "" {
			// 	continue
			// }

			var newTerm rdf.Term

			switch vt := v.(type) {
			case rdfA.Blank:
				newTerm = rdf.BlankNode{ID: vt.String()} // cuts off the first two char, keeping for compat
			case rdfA.IRI:
				newTerm = rdf.Resource{URI: vt.String()}
			case rdfA.Literal:
				data := rdf.Resource{URI: vt.DataType.String()}
				newTerm = rdf.Literal{Value: vt.String(), Datatype: data, Language: vt.Lang()}
			}

			// tupleOrdered[ordering[k]] = res(v.String()) // needed since range over map unsorted
			tupleOrdered[ordering[s]] = newTerm // needed since range over map unsorted
		}

		if len(tupleOrdered) == 0 {
			continue
		}

		resultTable = append(resultTable, tupleOrdered)
	}

	return &TableSimple[rdf.Term]{header: r.Head.Vars, content: resultTable}
}

// GroupedTable is a virtually grouped Table, that uses the same structure as simple tables,
// (and offers all the same methods) but in addition also provides access to the grouped values
// of a  value of the key attribute (fixed to be the first column)

type GroupedTable[T stringer] struct {
	header  []string
	content [][]T
	group   map[T](map[int][]T) // the grouping map
	key     map[T]int           // the grouping map
}

func (t *GroupedTable[T]) String() string {
	return t.Limit(len(t.content))
}

func (t *GroupedTable[T]) Len() int { return len(t.content) }

func (t *GroupedTable[T]) GetColumn(column int) ([]T, error) {
	var out []T

	if column >= len(t.header) || column < 0 {
		return []T{}, errors.New("Out of bounds error.")
	}

	for i := range t.content {
		out = append(out, t.content[i][column])
	}

	return out, nil
}

func (t *GroupedTable[T]) GetAttribute(att string) ([]T, error) {
	var column int = -1

	// find attribute
	for i := range t.header {
		if t.header[i] == att {
			column = i
		}
	}
	if column == -1 {
		return []T{}, errors.New("Attribute not found error.")
	}

	return t.GetColumn(column)
}

func (t *GroupedTable[T]) IterTargets() chan T {
	out := make(chan T)

	go func() {
		for k := range t.group {
			out <- k
		}
		close(out) // hope it's ok to close this at this point
	}()

	return out
}

func (t *GroupedTable[T]) IterRows() chan []T {
	out := make(chan []T)

	go func() {
		for i := range t.content {
			out <- t.content[i]
		}
		close(out) // hope it's ok to close this at this point
	}()

	return out
}

func (t *GroupedTable[T]) GetHeader() []string { return t.header }

func (t *GroupedTable[T]) AddRow(row []T) { t.content = append(t.content, row) }

func (t GroupedTable[T]) Limit(n int) string {
	if n > len(t.content) {
		n = len(t.content)
	}
	var sb strings.Builder
	const padding = 4
	w := tabwriter.NewWriter(&sb, 0, 0, padding, ' ', tabwriter.TabIndent)

	fmt.Fprint(w, "\n", strings.Join(t.header, "\t"), "\t\n")

	for i := range t.content[:n] {

		for j := range t.content[i] {
			fmt.Fprint(w, t.content[i][j].String())
			fmt.Fprint(w, "\t ")
		}
		fmt.Fprint(w, "\n")
	}

	if n < len(t.content) {
		fmt.Fprint(w, "\n\n\t\t⋮ (showing first ",
			n, " lines from ", len(t.content), " total) \n")
	} else {
		fmt.Fprint(w, "\n\t\t ( Total: ", len(t.content), " lines) \n")
	}

	err := w.Flush()
	check(err)
	return abbr(sb.String())
}

func (t *GroupedTable[T]) Merge(other Table[T]) error {
	// check if the two tables share the same header

	otherCast, ok := other.(*GroupedTable[T])
	if !ok {
		return errors.New("Cannot merge a GroupedTable with different kind")
	}

	if len(t.header) != len(otherCast.header) {
		return errors.New("Incompatible tables to merge")
	}
	for i := range t.header {
		if t.header[i] != otherCast.header[i] {
			return errors.New("Incompatible tables to merge")
		}
	}

	t.content = append(t.content, otherCast.content...)

	return nil
}

func (t *GroupedTable[T]) GetIndex(key T) (int, error) {
	val, ok := t.key[key]
	if !ok {
		return -1, errors.New("key not present in GroupedTable")
	}
	if val > len(t.content) {
		log.Panicln("Key Map is wrong")
	}

	return val, nil
}

func (t *GroupedTable[T]) AddIndex(key T, other *GroupedTable[T]) error {
	if len(t.header) != len(other.header) {
		return errors.New("Incompatible tables to AddIndex")
	}
	for i := range t.header {
		if t.header[i] != other.header[i] {
			return errors.New("Incompatible tables to AddIndex")
		}
	}

	for row := range other.IterRows() {
		if row[0] == key {
			t.content = append(t.content, row)
		}
	}

	return nil
}

func (t *GroupedTable[T]) RemoveIndex(key T) error {
	var badIndices []int

	for i := range t.content {
		if t.content[i][0] == key {
			badIndices = append(badIndices, i)
		}
	}

	sort.Sort(sort.Reverse(sort.IntSlice(badIndices)))

	for i := range badIndices {
		t.content = remove(t.content, i)
	}

	return nil
}

func (t *GroupedTable[T]) GetGroupOfTarget(key T, attribute int) []T {
	if attribute == 0 {
		return []T{key}
	}
	return t.group[key][attribute]
}

func (t *GroupedTable[T]) GetGroup(index int, attribute int) []T {
	if attribute == 0 {
		return []T{t.content[index][0]}
	}
	return t.group[t.content[index][0]][attribute]
}

func (t *GroupedTable[T]) Regroup() {
	// fmt.Println("Started regroup")

	t.group = make(map[T](map[int][]T))
	t.key = make(map[T]int)

	var attributesToGroup []int

	// fmt.Println("Header: ", t.header)
	for i := range t.header {
		if strings.HasSuffix(t.header[i], "group") {
			// fmt.Println("Adding index ", i, " s ince header ", t.header[i], " ends on group")
			attributesToGroup = append(attributesToGroup, i)
		}
	}

	for i := range t.content {
		row := t.content[i]
		key := row[0]
		if _, ok := t.key[key]; !ok {
			t.key[key] = i
		}
		for _, a := range attributesToGroup {

			_, ok := t.group[key]
			if !ok {
				t.group[key] = make(map[int][]T)
			}
			t.group[key][a] = append(t.group[key][a], row[a])

		}
	}

	// remove duplicates
	for k, v := range t.group {
		for _, a := range attributesToGroup {
			tmp := removeDuplicate[T](v[a])
			// fmt.Println("For key ", k, " at attribute ", a, " having group ", tmp)
			t.group[k][a] = tmp
		}
	}
}

func GetGroupedTable[T stringer](inputToCheck Table[T]) *GroupedTable[T] {
	// fmt.Println("Calling Group on Table", inputToCheck)
	input, ok := inputToCheck.(*TableSimple[T])
	if !ok {
		// fmt.Println("Do nothing in group")
		outTable := inputToCheck.(*GroupedTable[T])
		return outTable // do nothing if given a GroupedTable as input
	}

	var out GroupedTable[T]

	out.header = make([]string, len(input.header))
	out.content = make([][]T, len(input.content))
	copy(out.header, input.header)
	copy(out.content, input.content)

	out.Regroup()

	return &out
}
