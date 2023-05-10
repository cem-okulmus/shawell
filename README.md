# shaWell
A validator for SHACL using Well-founded semantics.

## Usage
`./shawell -endpoint <URL to a Sparql endpoint> -shaclDoc <location to a SHACL document, in Turtle format>`

## Support for recursive SHACL
Currently, shaWell uses the solver DLV to compute well-founded models in the presence of recursion. The most recent versions of DLV can be found [here](https://dlv.demacs.unical.it/home). The tool expects by default that the binary to dlv is present in a local "bin/" subfolder and simply named "dlv". This can be overridden via the optional "-dlv" flag, which expects the location to a DLV binary.
