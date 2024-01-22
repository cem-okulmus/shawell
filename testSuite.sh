#/usr/bin/bash


SPARQL_ENDPOINT=http://localhost:7200/repositories/graphdb
UPDATE_ENDPOINT=http://localhost:7200/repositories/graphdb/statements
# SPARQL_ENDPOINT=http://localhost:8890/sparql-auth/
# UPDATE_ENDPOINT=http://localhost:8890/sparql-auth/


time ./shawell   -endpointUpdate $UPDATE_ENDPOINT  -endpoint $SPARQL_ENDPOINT  -shaclDoc resources/W3_SHACL_Test_Suite_Core/$1 -dataIncluded $2
