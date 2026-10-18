package main

import (
	"errors"
	"fmt"
	"log"
	"sort"
	"strings"
	"text/tabwriter"

	"github.com/fatih/color"

	rdf "github.com/cem-okulmus/rdf2go-1"
	"github.com/knakk/sparql"
)

type Unbound struct{}

func (u Unbound) String() string {
	return "unbound"
}

func (u Unbound) RawValue() string {
	return ""
}

func (u Unbound) Equal(_ rdf.Term) bool {
	return false
}

type stringer interface {
	comparable
	String() string
}

type Table[T stringer] interface {
	GetColumn(column int) ([]T, error)    // Get a column based on index, if a valid index
	GetAttribute(att string) ([]T, error) // Get a column via its attribute name, if exists
	IterRows() chan []T                   // iterate over rows the table (in ordered fashion)
	GetHeader() []string                  // header required to be strings
	SetHeader([]string)                   // change the header
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
		return []T{}, errors.New("out of bounds error")
	}

	for i := range t.content {
		out = append(out, t.content[i][column])
	}

	return out, nil
}

func (t *TableSimple[T]) GetAttribute(att string) ([]T, error) {
	column := -1

	// find attribute
	for i := range t.header {
		if t.header[i] == att {
			column = i
		}
	}
	if column == -1 {
		return []T{}, errors.New("attribute not found error")
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

func (t *TableSimple[T]) GetHeader() []string      { return t.header }
func (t *TableSimple[T]) SetHeader(input []string) { t.header = input }

func (t *TableSimple[T]) AddRow(row []T) { t.content = append(t.content, row) }

func (t TableSimple[T]) Limit(n int) string {
	if n > len(t.content) {
		n = len(t.content)
	}
	var sb strings.Builder
	bold := color.New(color.Bold)

	const padding = 4
	w := tabwriter.NewWriter(&sb, 0, 0, padding, ' ', tabwriter.TabIndent)

	fmt.Fprint(w, "\n", bold.Sprint(strings.Join(t.header, "\t")), "\t\n")

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
		return errors.New("cannot merge a SimpleTable with different kind")
	}
	if len(t.header) != len(otherCast.header) {
		return errors.New("incompatible tables to merge")
	}
	for i := range t.header {
		if t.header[i] != otherCast.header[i] {
			return errors.New("incompatible tables to merge")
		}
	}

	t.content = append(t.content, otherCast.content...)

	return nil
}

func termFromBinding(kind, value, lang, datatype string) (rdf.Term, error) {
	switch kind {
	case "bnode":
		return rdf.BlankNode{ID: value}, nil
	case "uri":
		return rdf.Resource{URI: value}, nil
	case "literal", "typed-literal":
		// Untyped literals are typed as xsd:string
		if lang != "" {
			return rdf.Literal{Value: value, Language: lang}, nil // the datatype is implied by the language
		}
		if datatype == "" {
			datatype = _xsd + "string" // plain literals are xsd:string
		}
		return rdf.Literal{Value: value, Datatype: rdf.Resource{URI: datatype}}, nil
	default:
		return nil, fmt.Errorf("unknown binding type %q for value %q", kind, value)
	}

}

func solutions(r *sparql.Results) (out []map[string]rdf.Term) {

	out = make([]map[string]rdf.Term, 0)

	for _, s := range r.Results.Bindings {
		solution := make(map[string]rdf.Term)
		for k, v := range s {
			term, err := termFromBinding(v.Type, v.Value, v.Lang, v.DataType)
			if err != nil {
				log.Panicln(err) // a bound value must not silently become unbound
			}
			solution[k] = term
		}
		out = append(out, solution)
	}

	return out
}

// GetTable converts a SPARQL query result into a TableSimple data structure.
// Each column in the SPARQL result becomes a column in the table.
func GetTable(r *sparql.Results) *TableSimple[rdf.Term] {

	var resultTable [][]rdf.Term

	ordering := make(map[string]int)

	for i, s := range r.Head.Vars {
		ordering[s] = i
	}

	for _, t := range solutions(r) {

		tupleOrdered := make([]rdf.Term, len(r.Head.Vars))

		for _, s := range r.Head.Vars {
			v := t[s]

			if v == nil {
				v = Unbound{} // set unbound variables to unbound type
			}

			tupleOrdered[ordering[s]] = v // needed since range over map unsorted
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
// of a value of the key attribute (fixed to be the first column)
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
		return []T{}, errors.New("out of bounds error")
	}

	for i := range t.content {
		out = append(out, t.content[i][column])
	}

	return out, nil
}

func (t *GroupedTable[T]) GetAttribute(att string) ([]T, error) {
	column := -1

	// find attribute
	for i := range t.header {
		if t.header[i] == att {
			column = i
		}
	}
	if column == -1 {
		return []T{}, errors.New("attribute not found error")
	}

	return t.GetColumn(column)
}

func (t *GroupedTable[T]) IterTargets() chan T {
	out := make(chan T)

	// if len(t.group) != 0 {
	go func() {
		for k := range t.key {
			out <- k
		}

		close(out) // hope it's ok to close this at this point
	}()
	// } else {
	// 	go func() {
	// 		for i := range t.content {
	// 			out <- t.content[i][0]
	// 		}
	// 		close(out) // hope it's ok to close this at this point
	// 	}()
	// }

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

func (t *GroupedTable[T]) SetHeader(input []string) { t.header = input }

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
		return errors.New("cannot merge a GroupedTable with different kind")
	}

	if len(t.header) != len(otherCast.header) {
		return errors.New("incompatible tables to merge")
	}
	for i := range t.header {
		if t.header[i] != otherCast.header[i] {
			return errors.New("incompatible tables to merge")
		}
	}

	t.content = append(t.content, otherCast.content...)
	t.Regroup()

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

// Join
func (t *GroupedTable[T]) AddIndex(key T, other *GroupedTable[T]) error {
	if len(t.header) != len(other.header) {
		return errors.New("incompatible tables to AddIndex")
	}
	for i := range t.header {
		if t.header[i] != other.header[i] {
			return errors.New("incompatible tables to AddIndex")
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
		t.content = remove(t.content, badIndices[i])
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
		// if strings.HasSuffix(t.header[i], "group") {
		if i > 0 {
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
			if _, ok := t.group[key][a]; !ok {
				t.group[key][a] = []T{} // keep the column present, even if it stays empty
			}
			if _, unbound := any(row[a]).(Unbound); unbound {
				continue
			}
			t.group[key][a] = append(t.group[key][a], row[a])

		}
	}

	// remove duplicates
	for k, v := range t.group {
		for _, a := range attributesToGroup {
			tmp := removeDuplicate(v[a])
			// fmt.Println("For key ", k, " at attribute ", a, " having group ", tmp)
			t.group[k][a] = tmp
		}
	}
}

// GetGroupedTable converts a simple table into a grouped table where the first column becomes a grouping key.
// This enables efficient lookup of all values associated with a particular subject.
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
