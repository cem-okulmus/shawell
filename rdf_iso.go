package main

import (
	"crypto/sha256"
	"encoding/hex"
	"sort"
	"strings"

	rdf2go "github.com/cem-okulmus/rdf2go-1"
)

// rdfTurtleIsomorphic parses two Turtle documents and tests them for RDF isomorphism.
//
// Two RDF graphs are isomorphic iff there exists a bijection on blank node identifiers
// that maps the triple set of the first graph onto the triple set of the second.
// Ground triples (no blank nodes) must be strictly equal as a set; blank-node triples
// are matched via iterative Weisfeiler-Lehman signature hashing followed by an
// exhaustive search over any remaining ambiguous groups.
//
// Returns false if either document fails to parse.
func rdfTurtleIsomorphic(turtle1, turtle2 string) bool {
	g1 := rdf2go.NewGraph("")
	g2 := rdf2go.NewGraph("")
	if err := g1.Parse(strings.NewReader(turtle1), "text/turtle"); err != nil {
		return false
	}
	if err := g2.Parse(strings.NewReader(turtle2), "text/turtle"); err != nil {
		return false
	}
	return triplesIsomorphic(collectTriples(g1), collectTriples(g2))
}

// collectTriples drains IterTriples into a slice. rdf2go's All(nil,nil,nil) has a
// missing branch and returns nothing when all three pattern terms are nil, so we use
// IterTriples directly.
func collectTriples(g *rdf2go.Graph) []*rdf2go.Triple {
	var out []*rdf2go.Triple
	for t := range g.IterTriples() {
		out = append(out, t)
	}
	return out
}

// isBlankT reports whether term is a blank node.
func isBlankT(t rdf2go.Term) bool {
	switch t.(type) {
	case *rdf2go.BlankNode, rdf2go.BlankNode:
		return true
	}
	return false
}

// tripleKey returns a canonical string key for a triple whose terms are already in
// their final form (no pending bijection substitution needed).
func tripleKey(t *rdf2go.Triple) string {
	return t.Subject.String() + "\x00" + t.Predicate.String() + "\x00" + t.Object.String()
}

// triplesIsomorphic is the entry point for comparing two sets of triples.
func triplesIsomorphic(t1, t2 []*rdf2go.Triple) bool {
	if len(t1) != len(t2) {
		return false
	}

	// Partition into ground triples (no blank nodes) and those containing blank nodes.
	var ground1, bn1 []*rdf2go.Triple
	var ground2, bn2 []*rdf2go.Triple
	for _, t := range t1 {
		if isBlankT(t.Subject) || isBlankT(t.Object) {
			bn1 = append(bn1, t)
		} else {
			ground1 = append(ground1, t)
		}
	}
	for _, t := range t2 {
		if isBlankT(t.Subject) || isBlankT(t.Object) {
			bn2 = append(bn2, t)
		} else {
			ground2 = append(ground2, t)
		}
	}

	// Ground triples carry no blank nodes, so isomorphism reduces to set equality.
	if !sameTripleSet(ground1, ground2) {
		return false
	}
	if len(bn1) != len(bn2) {
		return false
	}
	if len(bn1) == 0 {
		return true
	}

	// Compute stable WL signatures for every blank node in each graph.
	sigs1 := stableSignatures(bn1)
	sigs2 := stableSignatures(bn2)
	bySig1 := groupBySig(sigs1)
	bySig2 := groupBySig(sigs2)

	// Quick structural check: same signature multiset.
	if len(bySig1) != len(bySig2) {
		return false
	}
	for sig, nodes := range bySig1 {
		if len(bySig2[sig]) != len(nodes) {
			return false
		}
	}

	// Search for a valid bijection, trying permutations within each ambiguous group
	// (groups where multiple blank nodes share the same signature).
	return searchBijection(bn1, bn2, bySig1, bySig2, make(map[string]string))
}

// sameTripleSet reports whether a and b contain the same multiset of triples.
func sameTripleSet(a, b []*rdf2go.Triple) bool {
	if len(a) != len(b) {
		return false
	}
	counts := make(map[string]int, len(a))
	for _, t := range a {
		counts[tripleKey(t)]++
	}
	for _, t := range b {
		if counts[tripleKey(t)]--; counts[tripleKey(t)] < 0 {
			return false
		}
	}
	return true
}

// stableSignatures computes a WL-style signature for every blank node in triples,
// iterating oneRound until the partition of blank nodes by signature no longer changes.
//
// Note: exact hash-value equality between consecutive rounds is NOT the right
// termination condition. For a chain b1→b2, each round produces new hash values
// (because they incorporate the previous round's hashes) even though the partition
// {b1},{b2} is already stable after round 1. We stop when the equivalence relation
// "same signature" is unchanged between two consecutive rounds.
func stableSignatures(triples []*rdf2go.Triple) map[string]string {
	sigs := make(map[string]string)
	for _, t := range triples {
		if isBlankT(t.Subject) {
			sigs[t.Subject.RawValue()] = ""
		}
		if isBlankT(t.Object) {
			sigs[t.Object.RawValue()] = ""
		}
	}
	for {
		next := oneRound(triples, sigs)
		if samePartition(sigs, next) {
			return next
		}
		sigs = next
	}
}

// samePartition returns true when a and b induce the same equivalence relation on
// blank node IDs: for any two nodes i and j, a[i]==a[j] iff b[i]==b[j]. This is
// equivalent to asking whether there is a bijection on signature values mapping a to b.
func samePartition(a, b map[string]string) bool {
	if len(a) != len(b) {
		return false
	}
	aToB := make(map[string]string, len(a))
	bToA := make(map[string]string, len(b))
	for id := range a {
		aSig, bSig := a[id], b[id]
		if prev, ok := aToB[aSig]; ok && prev != bSig {
			return false
		}
		if prev, ok := bToA[bSig]; ok && prev != aSig {
			return false
		}
		aToB[aSig] = bSig
		bToA[bSig] = aSig
	}
	return true
}

// oneRound computes a new signature map by hashing each blank node's neighborhood.
// For each triple a blank node participates in, it records the predicate and a
// reference to the other side — either the ground term's string or the previous
// round's signature for a blank node neighbor. The sorted list of these descriptors
// is SHA-256 hashed to produce the new signature.
func oneRound(triples []*rdf2go.Triple, prev map[string]string) map[string]string {
	parts := make(map[string][]string, len(prev))
	for id := range prev {
		parts[id] = nil
	}

	for _, t := range triples {
		pred := t.Predicate.String()
		subBlank := isBlankT(t.Subject)
		objBlank := isBlankT(t.Object)

		if subBlank {
			id := t.Subject.RawValue()
			var objRef string
			if objBlank {
				objRef = "B" + prev[t.Object.RawValue()]
			} else {
				objRef = "G" + t.Object.String()
			}
			parts[id] = append(parts[id], "S\x00"+pred+"\x00"+objRef)
		}
		if objBlank {
			id := t.Object.RawValue()
			var subRef string
			if subBlank {
				subRef = "B" + prev[t.Subject.RawValue()]
			} else {
				subRef = "G" + t.Subject.String()
			}
			parts[id] = append(parts[id], "O\x00"+subRef+"\x00"+pred)
		}
	}

	next := make(map[string]string, len(prev))
	for id, ps := range parts {
		sort.Strings(ps)
		h := sha256.Sum256([]byte(strings.Join(ps, "\x01")))
		next[id] = hex.EncodeToString(h[:16]) // 128 bits is more than enough
	}
	return next
}

func groupBySig(sigs map[string]string) map[string][]string {
	out := make(map[string][]string, len(sigs))
	for id, sig := range sigs {
		out[sig] = append(out[sig], id)
	}
	return out
}

// nextUnassigned returns a blank node in bySig1 not yet present in bij, along with
// the pool of candidate target nodes from bySig2 that share its signature.
// Returns empty strings if all nodes are assigned.
func nextUnassigned(bySig1, bySig2 map[string][]string, bij map[string]string) (pick string, pool []string) {
	for sig, nodes := range bySig1 {
		for _, n := range nodes {
			if _, ok := bij[n]; !ok {
				return n, bySig2[sig]
			}
		}
	}
	return "", nil
}

// searchBijection recursively extends a partial bijection (G1 blank node IDs →
// G2 blank node IDs). When every blank node in G1 is assigned, it validates the
// complete bijection against the actual triple sets. Within each signature group,
// all permutations are tried if necessary (required only when multiple blank nodes
// share an identical WL signature, which does not occur for SHACL validation reports).
func searchBijection(t1, t2 []*rdf2go.Triple, bySig1, bySig2 map[string][]string, bij map[string]string) bool {
	pick, pool := nextUnassigned(bySig1, bySig2, bij)
	if pick == "" {
		return bijectionValid(t1, t2, bij)
	}

	used := make(map[string]bool, len(bij))
	for _, v := range bij {
		used[v] = true
	}
	for _, candidate := range pool {
		if used[candidate] {
			continue
		}
		bij[pick] = candidate
		if searchBijection(t1, t2, bySig1, bySig2, bij) {
			return true
		}
		delete(bij, pick)
	}
	return false
}

// bijectionValid applies bij to every triple in t1 (substituting each blank node ID
// with its mapped counterpart) and checks that the resulting multiset of triples
// equals t2.
func bijectionValid(t1, t2 []*rdf2go.Triple, bij map[string]string) bool {
	applyBij := func(term rdf2go.Term) string {
		if isBlankT(term) {
			if mapped, ok := bij[term.RawValue()]; ok {
				return "_:" + mapped
			}
		}
		return term.String()
	}
	counts := make(map[string]int, len(t2))
	for _, t := range t2 {
		counts[tripleKey(t)]++
	}
	for _, t := range t1 {
		key := applyBij(t.Subject) + "\x00" + t.Predicate.String() + "\x00" + applyBij(t.Object)
		if counts[key]--; counts[key] < 0 {
			return false
		}
	}
	return true
}
