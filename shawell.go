// shawell - SHAcl (with) WELLfounded (semantics)
// A research prototype for validating SHACL documents under well-founded
// semantics.

package main

import (
	"bufio"
	"errors"
	"fmt"
	"io"
	"log"
	"net/url"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"runtime"
	"strings"
	"text/tabwriter"
	"time"

	"github.com/fatih/color"
	flags "github.com/jessevdk/go-flags"

	rdf "github.com/cem-okulmus/rdf2go-1"
)

var theCount int64 // lord of all things counting

// getCount increments and returns a global counter.
// Used to generate unique identifiers throughout the validation process.
func getCount() int64 {
	theCount++
	return theCount
}

// check is a helper function that panics if the given error is not nil.
func check(e error) {
	if e != nil {
		var exitErr *exec.ExitError
		if errors.As(e, &exitErr) {
			stderr := strings.TrimSpace(string(exitErr.Stderr))
			if stderr != "" {
				panic(fmt.Sprintf("%v\nstderr:\n%s", e, stderr))
			}
		}

		panic(e)
	}
}

// func res(s string) rdf.Term {
// 	return rdf.NewResource(s)
// }

var prefixes = make(map[string]string)

// making it easier to define proper terms
var (
	_shawell = "https://github.com/cem-okulmus/shawell#"
	_sh      = "http://www.w3.org/ns/shacl#"
	_rdf     = "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
	_rdfs    = "http://www.w3.org/2000/01/rdf-schema#"
	_xsd     = "http://www.w3.org/2001/XMLSchema#"
)

// GetNameSpace parses namespace prefixes from a Turtle file and populates the global prefixes map.
// It extracts @prefix declarations and stores the mapping between abbreviations and full URIs.
// Standard RDF namespaces (sh, rdf, rdfs) are set by default.
func GetNameSpace(file *os.File) {
	// TODO: make this less crazy and ugly

	// fix standard prefixes
	prefixes["sh:"] = _sh
	prefixes["rdf:"] = _rdf
	prefixes["rdfs:"] = _rdfs

	// call the Seek method first
	_, err := file.Seek(0, io.SeekStart)
	check(err)

	scanner := bufio.NewScanner(file)
	check(scanner.Err())
	validID := regexp.MustCompile(`<.*?>`)

	// iterate over each line in the file
	for scanner.Scan() {
		line := scanner.Text()
		ps := "@prefix "
		if strings.HasPrefix(line, ps) {
			abbr, _ := strings.CutPrefix(line, ps)
			getStart := 0
			abbrOut := ""
			for i, c := range abbr {
				if c == ':' {
					getStart = i
					break
				}
			}
			abbrOut = abbr[:getStart+1]
			fullPath := validID.FindString(line)
			_, ok := prefixes[abbrOut]
			if !ok {
				prefixes[abbrOut] = fullPath[1 : len(fullPath)-1]
			}
		}
	}
}

var activeDoc *ShaclDocument

// abbr abbreviates a string by replacing full namespace URIs with their registered prefixes.
// It also replaces qualified names of shapes with their abbreviated forms when available.
func abbr(in string) string {

	pairs1 := []string{
		// Angle-bracket stripping: preserve operators by listing them first (longer wins).
		" <> ", "\x01",
		">=", "\x02",
		"<=", "\x03",
		" > ", "\x04",
		" < ", "\x05",
		">", "",
		"<", "",
	}
	pairs2 := []string{
		"\x01", " <> ",
		"\x02", ">=",
		"\x03", "<=",
		"\x04", " > ",
		"\x05", " < ",
	}
	in = strings.NewReplacer(pairs2...).Replace(strings.NewReplacer(pairs1...).Replace(in))

	for k, v := range prefixes {
		in = strings.ReplaceAll(in, v, k)
	}

	if activeDoc != nil {
		for name, shape := range activeDoc.shapeNames {
			in = strings.ReplaceAll(in, shape.GetQualName(), name)
		}
	}

	return in
}

type timeComposer struct {
	times []labelTime
}

func (t timeComposer) String() string {
	var sb strings.Builder
	const padding = 4
	w := tabwriter.NewWriter(&sb, 0, 0, padding, ' ', tabwriter.TabIndent)
	var total float64
	for _, time := range t.times {
		fmt.Fprint(w, time.String(), "\n")
		total += time.time
	}
	fmt.Fprintf(w, "Total \t: %.5f ms\n", total)
	err := w.Flush()
	check(err)
	// Bold the Total line after flushing so tabwriter width calculations are unaffected.
	it := color.New(color.Bold)
	lines := strings.Split(sb.String(), "\n")
	for i := len(lines) - 1; i >= 0; i-- {
		if strings.TrimSpace(lines[i]) != "" {
			lines[i] = it.Sprint(lines[i])
			break
		}
	}
	return strings.Join(lines, "\n")
}

type labelTime struct {
	time  float64
	label string
}

func (l labelTime) String() string {
	return fmt.Sprintf("%s \t: %.5f ms", l.label, l.time)
}

var QueryStore []string

// answerShacl performs SHACL validation on a parsed SHACL document against a SPARQL endpoint
// using well-founded semantics. It handles both acyclic and recursive constraint patterns.
// Parameters:
//   - ep: SPARQL endpoint to query the data graph
//   - parsedDoc: the parsed and initialized SHACL document containing shapes and constraints
//   - config: configuration options for the validation process
//
// Returns a ValidationReport indicating whether the data conforms to the shape constraints.
func answerShacl(ep *SparqlEndpoint, parsedDoc ShaclDocument, config config) *ValidationReport {

	debug := config.debug
	omitVR := config.omitVR
	vrOutFile := config.vrOutFile
	silent := config.silent
	forceLP := config.forceLP
	onlyLP := config.onlyLP
	onlyQueries := config.onlyQueries

	var status ValidationStatus

	// if onlyLP || onlyQueries {
	// 	silent = true
	// }
	if !debug {
		log.SetOutput(io.Discard)
	} else {
		log.SetOutput(os.Stderr)
	}

	// for k, v := range parsedDoc.condAnswers {
	// 	fmt.Println("TABLE: ", k)
	// 	fmt.Println(v.Limit(5))
	// }

	if onlyQueries {
		fmt.Println("The produced SPAQRL queries: ")

		for _, query := range QueryStore {
			fmt.Println(abbr(query))
		}

		return nil

	}

	var c timeComposer
	var start time.Time
	var d time.Duration
	var msec float64

	renameMap = make(map[rdf.Term]string)
	reverseMap = make(map[string]rdf.Term)

	if !silent {
		fmt.Println("Checking conditional answers ... ")
	}

	start = time.Now()
	parsedDoc.AllCondAnswers(ep)
	d = time.Since(start)
	msec = d.Seconds() * float64(time.Second/time.Millisecond)
	c.times = append(c.times, labelTime{time: msec, label: "Conditional Table computation"})
	if !silent {
		fmt.Println("All conditinal answers found.")
	}

	var res bool
	var invalidTargets map[string]Table[rdf.Term]
	var lp serialisedProgram
	var lpTables []Table[rdf.Term]

	if parsedDoc.IsRecursive() || forceLP {
		if !silent {
			fmt.Println("Recursive document parsed, transforming to LP and sending off to solver.")
		}

		var lpUndefinedTables []Table[rdf.Term]

		start := time.Now()
		lp = parsedDoc.GetAllLPs()
		d := time.Since(start)
		msec := d.Seconds() * float64(time.Second/time.Millisecond)
		c.times = append(c.times, labelTime{time: msec, label: "Logic Program generation"})

		if debug || onlyLP {
			fmt.Print("The produced Logic Program:  \n\n")
			fmt.Println(abbr(lp.String()))
			if onlyLP {
				return nil
			}
		}

		switch config.semantics {
		case "well-founded":
			{

				start = time.Now()
				// fmt.Println("Unified LP: ", lp)
				lpTables, lpUndefinedTables, _ = lp.Answer(debug, false, "well-founded")
				d = time.Since(start)
				msec = d.Seconds() * float64(time.Second/time.Millisecond)
				c.times = append(c.times, labelTime{time: msec, label: "DLV solving"})

				err := parsedDoc.AdoptLPAnswers(lpTables)
				check(err)
				parsedDoc.AdoptLPUndefinedAnswers(lpUndefinedTables)

				if debug {
					fmt.Println("Answer from DLV: ")
					for i := range lpTables {
						fmt.Println(lpTables[i].Limit(5))
					}
				}

				start = time.Now()
				res, invalidTargets = parsedDoc.ValidateLP(ep)
				d = time.Since(start)
				msec = d.Seconds() * float64(time.Second/time.Millisecond)
				c.times = append(c.times, labelTime{time: msec, label: "Extracing answers from the LP"})

				// for now, we do the same as in non-recursive, will change as phase progresses
				if res {
					status = Valid
				} else {
					status = Invalid
				}

			}
		case "stable-brave":
			{
				// first call the LP with targets

				var solveStatus solveStatus

				targetLP := parsedDoc.GetTargetConstraintsLP(ep)

				mergedLP := lp.Merge(targetLP)

				start = time.Now()
				// fmt.Println("Unified LP: ", lp)
				lpTables, _, solveStatus = mergedLP.Answer(debug, false, "stable-brave")
				d = time.Since(start)
				msec = d.Seconds() * float64(time.Second/time.Millisecond)
				c.times = append(c.times, labelTime{time: msec, label: "clingo solving - brave call 1"})

				if solveStatus != unsatisfiable {

					if solveStatus == unknown {
						status = Unknown

					} else {

						err := parsedDoc.AdoptLPAnswers(lpTables)
						check(err)

						if debug {
							fmt.Println("Answer from Clingo: ")
							for i := range lpTables {
								fmt.Println(lpTables[i].Limit(5))
							}
						}

						start = time.Now()
						res, invalidTargets = parsedDoc.ValidateLP(ep)
						d = time.Since(start)
						msec = d.Seconds() * float64(time.Second/time.Millisecond)
						c.times = append(c.times, labelTime{time: msec, label: "Extracing answers from the LP"})

						if !res {
							log.Panicln("Found brave model that matches targets, but coudn't validate LP!")
						}

						status = Valid
					}

				} else { // next, if first call was unsatisfiable, run program without targets to see if there is any stable model at all
					start = time.Now()
					// fmt.Println("Unified LP: ", lp)
					lpTables, _, solveStatus = lp.Answer(debug, false, "stable-brave")
					d = time.Since(start)
					msec = d.Seconds() * float64(time.Second/time.Millisecond)
					c.times = append(c.times, labelTime{time: msec, label: "clingo solving - brave call 2"})

					// no need to run AdoptLPAnswers and ValidateLP if no model was found
					if solveStatus == satisfiable {
						err := parsedDoc.AdoptLPAnswers(lpTables)
						check(err)

						if debug {
							fmt.Println("Answer from Clingo: ")
							for i := range lpTables {
								fmt.Println(lpTables[i].Limit(5))
							}
						}

						start = time.Now()
						res, invalidTargets = parsedDoc.ValidateLP(ep)
						d = time.Since(start)
						msec = d.Seconds() * float64(time.Second/time.Millisecond)
						c.times = append(c.times, labelTime{time: msec, label: "Extracing answers from the LP"})

						if res {
							log.Panicln("Found brave model without target constraint, but it validated the targets !?")
						}
					}

					switch solveStatus {
					case unsatisfiable:
						status = NoModel
					case satisfiable:
						status = Invalid
					default:
						status = Unknown
					}

				}

			}
		case "stable-cautious":
			{
				var solveStatus solveStatus

				targetLP := parsedDoc.GetTargetConstraintsLPCautious(ep)

				if !targetLP.IsEmpty() {

					mergedLP := lp.Merge(targetLP)

					start = time.Now()
					// fmt.Println("Unified LP: ", lp)
					lpTables, lpUndefinedTables, solveStatus = mergedLP.Answer(debug, false, "stable-brave")
					d = time.Since(start)
					msec = d.Seconds() * float64(time.Second/time.Millisecond)
					c.times = append(c.times, labelTime{time: msec, label: "clingo solving - cautious call 1"})
				} else {
					solveStatus = unsatisfiable
				}

				// Run second Call to Determine if there is a model or not
				switch solveStatus {
				case unsatisfiable:
					start = time.Now()
					// fmt.Println("Unified LP: ", lp)
					lpTables, _, solveStatus = lp.Answer(debug, false, "stable-brave")
					d = time.Since(start)
					msec = d.Seconds() * float64(time.Second/time.Millisecond)
					c.times = append(c.times, labelTime{time: msec, label: "clingo solving - cautious call 2"})

					// no need to run AdoptLPAnswers and ValidateLP if no model was found
					if solveStatus == satisfiable {
						err := parsedDoc.AdoptLPAnswers(lpTables)
						check(err)

						if debug {
							fmt.Println("Answer from clingo: ")
							for i := range lpTables {
								fmt.Println(lpTables[i].Limit(5))
							}
						}

						start = time.Now()
						res, invalidTargets = parsedDoc.ValidateLP(ep)
						d = time.Since(start)
						msec = d.Seconds() * float64(time.Second/time.Millisecond)
						c.times = append(c.times, labelTime{time: msec, label: "Extracing answers from the LP"})

						if !res {
							log.Panicln("First cautious call showed invalidation is unsatisfiable, but now there are invalid targets !?")
						}
					}

					switch solveStatus {
					case unsatisfiable:
						status = NoModel
					case satisfiable:
						status = Valid
					default:
						status = Unknown
					}

				case satisfiable:
					err := parsedDoc.AdoptLPAnswers(lpTables)
					check(err)

					if debug {
						fmt.Println("Answer from clingo: ")
						for i := range lpTables {
							fmt.Println(lpTables[i].Limit(5))
						}
					}

					start = time.Now()
					res, invalidTargets = parsedDoc.ValidateLP(ep)
					d = time.Since(start)
					msec = d.Seconds() * float64(time.Second/time.Millisecond)
					c.times = append(c.times, labelTime{time: msec, label: "Extracing answers from the LP"})

					if res {
						log.Panicln("Found a cautious counter-model, but it validated all targets !?")
					}

					status = Invalid
				case unknown:
					status = Unknown
				}

			}
		default:
			log.Panicln("Unknown/Unimplemented semantics: ", config.semantics)
		}

	} else {
		start := time.Now()
		res, invalidTargets = parsedDoc.Validate(ep)
		d := time.Since(start)
		msec := d.Seconds() * float64(time.Second/time.Millisecond)
		c.times = append(c.times, labelTime{time: msec, label: "Unwinding acyclic cond. tables"})

		// in non-recursive case, we can set the status directly based on the validation result
		if res {
			status = Valid
		} else {
			status = Invalid
		}
	}

	if !silent {
		for _, v := range invalidTargets {
			if v.Len() > 0 {
				fmt.Println("Found a shape with invalid targets: \n", v.Limit(20))
			}
		}
	}

	green := color.New(color.FgGreen)
	red := color.New(color.FgRed)
	magenta := color.New(color.FgMagenta)
	yellow := color.New(color.BgYellow)

	if !silent {
		fmt.Println("----------------------------------")
		fmt.Println("RESULT: --------------------------")

		switch status {
		case Valid:
			fmt.Println("Shacl Document valid: ", green.Sprint(res))
		case Invalid:
			fmt.Println("Shacl Document valid: ", red.Sprint(res))
		case NoModel:
			fmt.Println("Shacl Document valid: ", magenta.Sprint("No model found"))
		case Unknown:
			fmt.Println("Shacl Document valid: ", yellow.Sprint("Unknown"))
		}

		fmt.Println("----------------------------------")
	}
	// Producing a Validation Repot in case of failure

	// fmt.Println("ValidationResult in XML form: ")

	actual := &ValidationReport{conforms: status == Valid}
	actual.status = status
	var reports []ValidationResult

	allValid := true

	if !omitVR {
		actual = &ValidationReport{}
		actual.status = status

		start = time.Now()

		if status == NoModel || status == Unknown {

			if !silent && status == NoModel {
				fmt.Fprintln(os.Stderr, "Warning: no stable model exists; the report lists every target as violated.")
			} else if !silent {
				fmt.Fprintln(os.Stderr, "Warning: the solver was interrupted; the report lists every target, without a verdict for any of them.")
			}

			reports = append(reports, parsedDoc.GetNoModelReport(status == Unknown)...)

			allValid = len(reports) == 0
		} else {
			for _, v := range parsedDoc.shapeNames {
				// var reportsFromShape []ValidationResult

				switch t := v.(type) {
				case *NodeShape:
					if t.deactivated {
						continue
					}
					// fmt.Println("Computing VRs for shape ", t.GetIRI())
					valid, reportsOfShape := parsedDoc.GetValidationReport(t, ep)
					if !valid {
						allValid = false
					}
					if !valid && len(reportsOfShape) == 0 {
						log.Panic("Reporting not valid for NodeSHape ", t.IRI,
							" but no reports returned!")
					}

					reports = append(reports, reportsOfShape...)
				case *PropertyShape:
					if t.shape.deactivated {
						continue
					}
					// fmt.Println("Computing VRs for shape ", t.GetIRI())
					valid, repsOfShape := parsedDoc.GetVRProperty(t, ep, nil, "")
					if !valid {
						allValid = false
					}

					if !valid && len(repsOfShape) == 0 {
						log.Panic("Reporting not valid for PropertyShape ", t.name,
							" but no reports returned!")
					}

					reports = append(reports, repsOfShape...)
				}
			}

			if !silent && config.semantics == "stable-cautious" && status == Invalid {
				fmt.Fprintln(os.Stderr, "Note: the report shows one counter-model; other targets may also fail in other stable models.")
			}
		}

		// reports = removeDuplicateVR(reports)
		d = time.Since(start)
		msec = d.Seconds() * float64(time.Second/time.Millisecond)
		c.times = append(c.times, labelTime{time: msec, label: "Validation Report creation"})

		actual.results = reports
		actual.conforms = res
	}

	if !omitVR && allValid != res && status != NoModel && status != Unknown {

		if parsedDoc.IsRecursive() || forceLP {
			fmt.Println("\nGenerated LP: ", lp)

			fmt.Println("LP Tables: ")
			for i := range lpTables {
				fmt.Println(lpTables[i].Limit(10))
			}

			fmt.Println("log names of shapes")
			for name, shape := range parsedDoc.shapeNames {
				fmt.Println(shape.GetLogName())
				fmt.Println(parsedDoc.uncondAnswers[name])
				fmt.Println("Invalid Targets: ", invalidTargets[name])
			}
		}

		fmt.Println("Number of reports: ", len(reports))

		fmt.Println("VALIDATION REPORT: \n", actual)
		log.Panicln("Mismatch between ValidationResult & ValidationReports result! ", allValid, res)
	}

	if !silent && !omitVR && vrOutFile == nil {
		fmt.Println("VALIDATION REPORT: \n", abbr(actual.String()))
	} else if vrOutFile != nil {
		_, err := vrOutFile.WriteString(actual.String())
		check(err)
	}

	if config.timer {
		fmt.Println("\n\nTime Composition:")
		fmt.Println(c)
	}
	return actual
}

// used to collect the needed options for SHACL answer function, to avoid too many parameters
type config struct {
	debug       bool
	omitVR      bool
	vrOutFile   *os.File
	silent      bool
	forceLP     bool
	onlyLP      bool
	onlyQueries bool
	timer       bool
	semantics   string
}

// binaryExists reports whether the binary at path is reachable — stat for paths
// containing a separator, LookPath for bare names.
func binaryExists(path string) bool {
	if strings.ContainsRune(path, '/') || strings.ContainsRune(path, os.PathSeparator) {
		_, err := os.Stat(path)
		return err == nil
	}
	_, err := exec.LookPath(path)
	return err == nil
}

// findDepScript searches for the appropriate dependency-download script next to
// the running executable, then in the current working directory.
// On Windows it looks for download_deps.ps1; on all other platforms download_deps.sh.
// Returns the script path and the interpreter command to run it with.
func findDepScript() (script, interpreter string, err error) {
	var name string
	if runtime.GOOS == "windows" {
		name = "download_deps.ps1"
		interpreter = "powershell"
	} else {
		name = "download_deps.sh"
		interpreter = "bash"
	}

	if exe, exeErr := os.Executable(); exeErr == nil {
		candidate := filepath.Join(filepath.Dir(exe), name)
		if _, statErr := os.Stat(candidate); statErr == nil {
			return candidate, interpreter, nil
		}
	}
	if _, statErr := os.Stat(name); statErr == nil {
		return name, interpreter, nil
	}
	return "", "", fmt.Errorf("%s not found next to executable or in working directory", name)
}

func findClingo(clingoArgument string) ([]string, error) {

	if clingoArgument != "" {
		if _, err := exec.LookPath(clingoArgument); err == nil {
			return []string{clingoArgument}, nil
		} else {
			log.Panicf("User-defined clingo binary not found: %v", err)
		}
	}

	if path, err := exec.LookPath("clingo"); err == nil {
		return []string{path}, nil
	}
	// fist check for local binary in bin/ folder
	local := "bin/clingo"
	if runtime.GOOS == "windows" {
		local = "bin/clingo.exe"
	}

	localVenvPath := "bin/clingo-venv/bin/python"
	if runtime.GOOS == "windows" {
		localVenvPath = "bin/clingo-venv/Scripts/python.exe"
	}

	if _, err := os.Stat(localVenvPath); err == nil {
		// venv exists, return command prefix
		return []string{localVenvPath, "-m", "clingo"}, nil
	}
	if _, err := os.Stat(local); err == nil {
		return []string{local}, nil
	}
	return []string{}, fmt.Errorf("clingo binary not found in PATH or %s or %s; "+
		"needs to be downloaded from https://potassco.org/clingo/, "+
		"the included download_deps.sh can set it up easily", local, localVenvPath)
}

// ensureDependencies checks whether the required binaries are present and, if
// any are missing, locates and runs the platform-appropriate download script.
func ensureDependencies(needOxigraph bool, needClingo bool) {
	dlvMissing := !binaryExists(dlv)
	oxiMissing := needOxigraph && func() bool {
		_, err := findOxigraph()
		return err != nil
	}()
	clingoMissing := needClingo && func() bool {
		_, err := findClingo("")
		return err != nil
	}()

	if !dlvMissing && !oxiMissing && !clingoMissing {
		return
	}

	script, interpreter, err := findDepScript()
	if err != nil {
		return // let execution continue; the real error will surface later
	}

	interpPath, err := exec.LookPath(interpreter)
	if err != nil {
		// Try the alternative PowerShell executable name on Windows
		if runtime.GOOS == "windows" {
			interpPath, err = exec.LookPath("pwsh")
		}
		if err != nil {
			fmt.Fprintf(os.Stderr, "Dependencies missing. Run %s manually to set them up.\n", script)
			return
		}
	}

	var args []string
	if runtime.GOOS == "windows" {
		// -ExecutionPolicy Bypass allows running unsigned local scripts
		args = []string{"-ExecutionPolicy", "Bypass", "-File", script}
		if clingoMissing {
			args = append(args, "--clingo")
		}
	} else {
		args = []string{script}
		if clingoMissing {
			args = append(args, "--clingo")
		}

	}
	cmd := exec.Command(interpPath, args...)

	fmt.Println("Missing dependencies detected — running", script)
	cmd.Stdout = os.Stdout
	cmd.Stderr = os.Stderr
	if err := cmd.Run(); err != nil {
		fmt.Fprintf(os.Stderr, "Warning: %s failed: %v\n", script, err)
	}
}

// cliOptions holds all command-line flags parsed by go-flags.
// Fields of type flags.Filename receive automatic shell completion for file paths.
type cliOptions struct {
	Endpoint          string         `short:"e" long:"endpoint"           description:"The URL to a SPARQL endpoint."`
	EndpointUpdate    string         `short:"E" long:"endpointUpdate"     description:"The URL to a SPARQL endpoint used for updating the data."`
	Local             bool           `short:"l" long:"local"              description:"Start a local in-memory Oxigraph SPARQL server. Requires --dataIncluded."`
	ShaclDoc          flags.Filename `short:"s" long:"shaclDoc"           description:"The file path to a SHACL document."`
	Dlv               flags.Filename `short:"d" long:"dlv"                description:"The location of the DLV binary used to evaluate recursive SHACL."`
	DataIncluded      bool           `short:"i" long:"dataIncluded"       description:"Set this to true if the SHACL document also contains the data to be checked."`
	ReuseData         bool           `            long:"reuseData"        description:"Use together with --dataIncluded and --endpoint when the target named graph was already populated separately (e.g. via a bulk import into GraphDB). Skips clearing the graph before inserting the SHACL doc's own triples and skips clearing it afterwards, so large pre-loaded datasets aren't re-parsed and re-inserted through this tool on every invocation."`
	User              string         `short:"u" long:"user"               description:"The username needed to access endpoint."`
	Password          string         `short:"p" long:"password"           description:"The password needed to access endpoint."`
	Debug             bool           `short:"D" long:"debug"              description:"Activating debugging features."`
	Silent            bool           `short:"S" long:"silent"             description:"Completely suppressing any stdio output."`
	PoseTestQuery     flags.Filename `short:"q" long:"poseTestQuery"      description:"A query to run and return the results. Used for testing/debug purposes."`
	OmitVR            bool           `short:"o" long:"omitVR"             description:"Omits outputting the Validation Report."`
	OutputVR          flags.Filename `short:"O" long:"outputVR"           description:"A filepath used to export the Validation Report in turtle notation."`
	ForceLP           bool           `short:"f" long:"forceLP"            description:"Force the translation into logic programs."`
	RuleSet           flags.Filename `short:"r" long:"ruleSet"            description:"The file path to a set of SHACL rules."`
	Stratified        bool           `short:"T" long:"stratified"         description:"Use stratified evaluation: each rule and shape must carry a [N]/sw:stratum annotation; strata are evaluated in order 1..N instead of iterating to fixpoint."`
	DemoOutputLP      bool           `short:"L" long:"demoOutputLP"       description:"Outputs only the produced LPs."`
	DemoOutputQueries bool           `short:"Q" long:"demoOutputQueries"  description:"Outputs only the produced SPARQL queries."`
	Timer             bool           `            long:"timer"             description:"Print time composition after validation."`
	Completion        string         `short:"c" long:"completion"         description:"Output a shell completion setup script and exit." choice:"bash" choice:"zsh" choice:"fish"`
	Clingo            string         `long:"clingo"             description:"The location of the clingo binary used to evaluate recursive SHACL."`
	Semantics         string         `short:"m" long:"semantics" description:"The semantics to use for recursive SHACL evaluation." choice:"well-founded" choice:"stable-brave" choice:"stable-cautious" default:"well-founded"`
}

// printCompletion outputs the one-liner shell setup that hooks shawell into the shell's
// completion system. go-flags handles the actual completion at runtime via COMP_LINE/COMP_POINT.
func printCompletion(shell string) {
	self, err := os.Executable()
	if err != nil {
		self = "shawellRules"
	}

	switch shell {
	case "bash":
		fmt.Printf(`_%[1]s_completion() {
    local args
    args=("${COMP_WORDS[@]:1}")
    COMPREPLY=( $(GO_FLAGS_COMPLETION=1 %[2]s "${args[@]}" 2>/dev/null) )
    return 0
}
complete -F _%[1]s_completion shawell
`, "shawell", self)
	case "zsh":
		fmt.Printf(`autoload -U +X bashcompinit && bashcompinit
_%[1]s_completion() {
    local args
    args=("${COMP_WORDS[@]:1}")
    COMPREPLY=( $(GO_FLAGS_COMPLETION=1 %[2]s "${args[@]}" 2>/dev/null) )
    return 0
}
complete -F _%[1]s_completion shawell
`, "shawell", self)
	case "fish":
		fmt.Printf(`function _shawell_complete
    set -lx GO_FLAGS_COMPLETION 1
    set args (commandline -opc)
    set -e args[1]
    %s $args 2>/dev/null
end
complete -c shawell -a '(_shawell_complete)' -f
`, self)
	}
}

func SHACLPredicate(predicate rdf.Term) bool {

	// sh:  type predicate
	if strings.HasPrefix(predicate.RawValue(), _sh) {
		return true
	}
	if predicate.RawValue() == _rdf+"first" || predicate.RawValue() == _rdf+"rest" {
		return true
	}

	return false
}

func main() {
	// ==============================================
	// Command-Line Argument Parsing

	exitCode := 0
	defer func() {
		if r := recover(); r != nil {
			fmt.Fprintln(os.Stderr, r)
			os.Exit(1)
		}
		os.Exit(exitCode)
	}()

	var opts cliOptions
	opts.Dlv = flags.Filename("bin/dlv")
	if runtime.GOOS == "windows" {
		opts.Dlv = flags.Filename("bin/dlv.exe")
	}

	parser := flags.NewParser(&opts, flags.Default)
	if _, err := parser.Parse(); err != nil {
		if e, ok := err.(*flags.Error); ok && e.Type == flags.ErrHelp {
			return
		}
		exitCode = 2
		return
	}

	if opts.Completion != "" {
		printCompletion(opts.Completion)
		return
	}

	// If only --shaclDoc is given with no endpoint or --local flag, assume --local --dataIncluded.
	if opts.ShaclDoc != "" && opts.Endpoint == "" && !opts.Local {
		opts.Local = true
		opts.DataIncluded = true
	}

	if (opts.Endpoint == "" && !opts.Local) || opts.ShaclDoc == "" {
		parser.WriteHelp(os.Stderr)
		exitCode = 2
		return
	}

	if opts.Local && !opts.DataIncluded {
		fmt.Fprintln(os.Stderr, "Error: --local requires --dataIncluded (the data must be in the SHACL document)")
		exitCode = 2
		return
	}

	usingUpdateEndpoint := opts.EndpointUpdate != ""

	// END Command-Line Argument Parsing
	// ==============================================

	// set DLV
	dlv = string(opts.Dlv)

	// For clingo: only needed if semantics is not well-founded and clingo path is not provided explicitly by user.
	// FindClingo will then be used to deliver the command.
	needClingo := opts.Semantics != "well-founded"
	ensureDependencies(opts.Local, needClingo && opts.Clingo == "")

	var err error
	if needClingo {
		clingoCmd, err = findClingo(opts.Clingo)
		check(err)
	}

	shaclDoc, err := os.Open(string(opts.ShaclDoc))
	check(err)
	defer shaclDoc.Close()

	var vrOutFile *os.File
	if !opts.OmitVR && opts.OutputVR != "" {
		vrOutFile, err = os.OpenFile(string(opts.OutputVR), os.O_CREATE|os.O_WRONLY, 0o644)
		check(err)
		defer vrOutFile.Close()
	}

	g2 := rdf.NewGraph(_sh)

	err = g2.Parse(shaclDoc, "text/turtle")
	check(err)

	// fmt.Println("Parsed Graph: ", g2)

	var endpoint *SparqlEndpoint
	if opts.Local {
		var oxiCleanup func()
		endpoint, oxiCleanup, err = StartOxigraph(opts.Debug)
		check(err)
		defer oxiCleanup()
	} else {
		endpoint = GetSparqlEndpoint(
			opts.Endpoint,
			opts.EndpointUpdate,
			opts.User,
			opts.Password,
			opts.Debug,
			usingUpdateEndpoint,
			"",
		)
	}

	// Test Query routine
	if opts.PoseTestQuery != "" {
		queryFile, err := os.ReadFile(string(opts.PoseTestQuery))
		check(err)

		endpoint.QueryString(string(queryFile))

		form := url.Values{}
		form.Set("query", string(queryFile))
		arg := form.Encode()

		fmt.Println("Argument: ", arg)

		exitCode = 0
		return
	}

	GetNameSpace(shaclDoc)

	// var VR *ValidationReport

	var graphName string

	// check if data needs to be inserted into Endpoint
	if opts.DataIncluded {
		basename := filepath.Base(string(opts.ShaclDoc))
		fileName := strings.TrimSuffix(basename, filepath.Ext(basename))

		insertGraph := g2
		// under stable-semantics, do not insert shapes tripes into endpoint
		if opts.Semantics == "stable-brave" || opts.Semantics == "stable-cautious" {
			var selectedTriples []*rdf.Triple
			queue := GetNodeTerms(g2)
			queue = append(queue, GetSubjectFromTriples(g2.All(nil, rdf.NewResource(_sh+"path"), nil))...) // property shapes

			excluded := make(map[string]bool)

			for len(queue) > 0 {
				t := queue[len(queue)-1]
				queue = queue[:len(queue)-1]
				if excluded[t.String()] {
					continue
				}
				excluded[t.String()] = true
				for _, tr := range g2.All(t, nil, nil) {
					if _, ok := tr.Object.(*rdf.BlankNode); ok { // nested shapes, list cells, complex paths
						queue = append(queue, tr.Object)
					}
				}
			}

			for r := range g2.IterTriples() {
				if excluded[r.Subject.String()] && SHACLPredicate(r.Predicate) { // skip triples whose subject is a term from shape graph and who use a "SHACL" vocabulary predicate
					continue
				}
				if excluded[r.Subject.String()] && r.Predicate.RawValue() == _rdf+"type" && r.Object.RawValue() == _sh+"NodeShape" { // skip triples that define a SHACL shape
					continue
				}
				if excluded[r.Subject.String()] && r.Predicate.RawValue() == _rdf+"type" && r.Object.RawValue() == _sh+"PropertyShape" { // skip triples that define a SHACL shape
					continue
				}

				selectedTriples = append(selectedTriples, r)
			}

			g2ModuloShapes := rdf.NewGraph(_sh)

			for _, t := range selectedTriples {
				g2ModuloShapes.Add(t)
			}

			insertGraph = g2ModuloShapes

		}
		err := endpoint.Insert(insertGraph, "<"+_sh+fileName+">", opts.ReuseData)
		check(err)

		graphName = "<" + _sh + fileName + ">"
	}

	parsedDoc := GetShaclDocument(g2, graphName, opts.Debug, opts.Semantics)

	if opts.DemoOutputLP {
		demoLP = true
	}

	parsedDoc.debug = opts.Debug
	var addedText string
	if !opts.Debug {
		it := color.New(color.Italic)
		addedText = it.Sprint("(use --debug to also show blank Shapes)")
	}
	if !opts.Silent {
		fmt.Println("The parsed SHACL Document:", addedText, parsedDoc.String())
	}

	// set active
	activeDoc = &parsedDoc

	// set up needed config for answerShacl
	config := config{
		debug:       opts.Debug,
		omitVR:      opts.OmitVR,
		vrOutFile:   vrOutFile,
		silent:      opts.Silent,
		forceLP:     opts.ForceLP,
		onlyLP:      opts.DemoOutputLP,
		onlyQueries: opts.DemoOutputQueries,
		timer:       opts.Timer,
		semantics:   opts.Semantics,
	}

	// Main Routine
	vr := answerShacl(endpoint, parsedDoc, config)

	if vr == nil {
		return // in demo mode
	}

	if !vr.conforms {
		switch vr.status {
		case Valid:
			log.Panicln("Produced non-conforming VR with Valid ValidationStatus!")
		case Invalid:
			exitCode = 3
		case NoModel:
			exitCode = 4
		case Unknown:
			exitCode = 5
		}
	}

	// If needed, clean up the named graph afterwards
	if opts.DataIncluded && !opts.ReuseData {
		err = endpoint.ClearGraph(parsedDoc.fromGraph)
		check(err)
	}
}
