# shaWell

[![](https://img.shields.io/github/v/tag/cem-okulmus/shawell?sort=semver)](https://github.com/cem-okulmus/shawell/releases/latest)
[![Go Reference](https://pkg.go.dev/badge/github.com/cem-okulmus/shawell.svg)](https://pkg.go.dev/github.com/cem-okulmus/shawell)


A validator for SHACL using Well-founded semantics.

## Contents

- [Usage](#usage)
- [Flags](#flags)
- [How to Build](#how-to-build)
- [Support for recursive SHACL](#support-for-recursive-shacl)
- [Using Oxigraph as a SPARQL endpoint](#using-oxigraph-as-a-sparql-endpoint)
## Usage
When running against a given RDF dataset with constraints:

```
./shawell --shaclDoc <location to a SHACL document, in Turtle format> 
```


When running against a given SPARQL endpoint, with an external SHACL document:

```
./shawell --endpoint <URL to a Sparql endpoint> --shaclDoc <location to a SHACL document, in Turtle format> 
```

## Flags

| Flag | Short | Description |
|------|-------|-------------|
| `--endpoint` | `-e` | The URL to a SPARQL endpoint. |
| `--endpointUpdate` | `-E` | The URL to a SPARQL endpoint used for updating the data. |
| `--local` | `-l` | Start a local in-memory Oxigraph SPARQL server. Requires `--dataIncluded`. |
| `--shaclDoc` | `-s` | The file path to a SHACL document. |
| `--dlv` | `-d` | The location of the DLV binary used to evaluate recursive SHACL. |
| `--dataIncluded` | `-i` | Set this if the SHACL document also contains the data to be checked. |
| `--user` | `-u` | The username needed to access the endpoint. |
| `--password` | `-p` | The password needed to access the endpoint. |
| `--debug` | `-D` | Activate debugging features. |
| `--silent` | `-S` | Completely suppress any stdio output. |
| `--poseTestQuery` | `-q` | A query to run and return the results. Used for testing/debug purposes. |
| `--omitVR` | `-o` | Omit outputting the Validation Report. |
| `--outputVR` | `-O` | A filepath used to export the Validation Report in Turtle notation. |
| `--forceLP` | `-f` | Force the translation into logic programs. |
| `--stratified` | `-T` | Use stratified evaluation: each rule and shape must carry a `[N]/sw:stratum` annotation; strata are evaluated in order 1..N instead of iterating to fixpoint. |
| `--demoOutputLP` | `-L` | Output only the produced logic programs. |
| `--demoOutputQueries` | `-Q` | Output only the produced SPARQL queries. |

## How to Build
Install Go on your system. Installation files for Linux, macOS and Windows can be found [here](https://go.dev/dl/). Then simply run:
 
```
go build
```  

There is an included script to automatically download the needed binaries. If the user wishes to download the needed binaries themselves, for example to use a different version, it's explained below how to do so.

## Support for recursive SHACL
Currently, shaWell uses the solver DLV to compute well-founded models in the presence of recursion. The most recent versions of DLV can be found [here](https://dlv.demacs.unical.it/home). The tool expects by default that the binary to dlv is present in a local "bin/" subfolder and simply named "dlv". This can be overridden via the optional "-dlv" flag, which expects the location to a DLV binary.

## Using Oxigraph as a SPARQL endpoint

[Oxigraph](https://github.com/oxigraph/oxigraph) is a lightweight, self-contained SPARQL 1.1 triple store that can be used in place of a SPARQL endpoint (this tool has been tested against such as GraphDB, but in theory works on any SPARQL endpoint).

### Manually Downloading Oxigraph

Pre-built binaries are available on the [Oxigraph releases page](https://github.com/oxigraph/oxigraph/releases). Download the binary that matches your platform (e.g. `oxigraph_linux_x86_64` on 64-bit Linux) and place it under `bin/oxigraph`:

```bash
# Example for Linux x86-64 — adjust the version and filename for your platform
VERSION=0.5.7
curl -L "https://github.com/oxigraph/oxigraph/releases/download/v${VERSION}/oxigraph_linux_x86_64" \
     -o bin/oxigraph
chmod +x bin/oxigraph
```

The tool also accepts an `oxigraph` binary anywhere on your `PATH`, so a system-wide install works equally well. Manually downloading is optional, since the tool, as with dlv, can detect when the oxigraph binary is missing (or not in the right directory and name), and initiate the script to download all missing binaries automatically.

#### Manual mode: external Oxigraph server

If you want to keep the store running between invocations, start Oxigraph manually first:

```bash
bin/oxigraph serve --location /tmp/oxigraph-data --bind 127.0.0.1:7878
```

Then point shaWell at its endpoints:

```bash
./shawell \
  --endpoint http://127.0.0.1:7878/query \
  --endpointUpdate http://127.0.0.1:7878/update \
  --shaclDoc <path/to/document.ttl>
```

