// Package lean provides Go values intended to map to Lean's Array, ByteArray,
// Option, List, BitVec w, Std.TreeMap, and Std.TreeSet. A translator can identify
// the curated operations by their Go package and type identities.
//
// Updates return new values. Generic elements, keys, and values are copied
// according to Go assignment semantics, so persistence is shallow.
package lean
