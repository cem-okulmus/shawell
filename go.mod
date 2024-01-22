module github.com/cem-okulmus/shawell

go 1.20

require (
	github.com/cem-okulmus/rdf2go-1 v0.1.6
	github.com/fatih/color v1.15.0
	github.com/knakk/rdf v0.0.0-20190304171630-8521bf4c5042
	golang.org/x/exp v0.0.0-20230510235704-dd950f8aeaea
)

require (
	github.com/cem-okulmus/gon3-1 v0.2.3 // indirect
	github.com/knakk/digest v0.0.0-20160404164910-fd45becddc49 // indirect
	github.com/mattn/go-colorable v0.1.13 // indirect
	github.com/mattn/go-isatty v0.0.17 // indirect
	golang.org/x/sys v0.6.0 // indirect
)

require (
	github.com/alecthomas/participle v0.7.1
	github.com/knakk/sparql v0.0.0-20240119140508-255b851aa040
	github.com/linkeddata/gojsonld v0.0.0-20170418210642-4f5db6791326 // indirect
	github.com/rychipman/easylex v0.0.0-20160129204217-49ee7767142f // indirect
)

replace (
	github.com/cem-okulmus/MyRDF2Go v0.1.3 => ../rdf2go-1
	github.com/cem-okulmus/gon3-1 v0.2.2 => ../gon3-1
)
