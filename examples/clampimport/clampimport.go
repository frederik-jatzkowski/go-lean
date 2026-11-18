package clampimport

import "github.com/frederik-jatzkowski/go-lean/examples/clampimport/limits"

//golean:verify
func Clamp(value, low, high int64) int64 {
	return limits.Min(limits.Max(value, low), high)
}
