# shaWell

[![](https://img.shields.io/github/v/tag/cem-okulmus/shawell?sort=semver)](https://github.com/cem-okulmus/shawell/releases/latest)
[![Go Reference](https://pkg.go.dev/badge/github.com/cem-okulmus/shawell.svg)](https://pkg.go.dev/github.com/cem-okulmus/shawell)
[![Go Report Card](https://goreportcard.com/badge/github.com/cem-okulmus/shawell)](https://goreportcard.com/report/github.com/cem-okulmus/shawell)

A validator for SHACL using Well-founded semantics.

## Usage
```
./shawell -endpoint <URL to a Sparql endpoint> -shaclDoc <location to a SHACL document, in Turtle format>
```

## How to Build
Install Go on your system. Installation files for Linux, macOS and Windows can be found [here](https://go.dev/dl/). Then simply run:
 
```
go build
```  


## Support for recursive SHACL
Currently, shaWell uses the solver DLV to compute well-founded models in the presence of recursion. The most recent versions of DLV can be found [here](https://dlv.demacs.unical.it/home). The tool expects by default that the binary to dlv is present in a local "bin/" subfolder and simply named "dlv". This can be overridden via the optional "-dlv" flag, which expects the location to a DLV binary.
