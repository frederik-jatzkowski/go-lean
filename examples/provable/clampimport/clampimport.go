package clampimport

import "github.com/frederik-jatzkowski/go-lean/examples/provable/clampimport/limits"

//golean:verify clampBounds : ∀ value low high : Int64, low ≤ high →
//golean:verify+ low ≤ Clamp value low high ∧ Clamp value low high ≤ high
//golean:verify clampIdempotent : ∀ value low high : Int64, low ≤ high →
//golean:verify+ Clamp (Clamp value low high) low high = Clamp value low high
//golean:abstract limits.Min
//golean:abstract limits.Max
func Clamp(value, low, high int64) int64 {
	return limits.Min(limits.Max(value, low), high)
}
