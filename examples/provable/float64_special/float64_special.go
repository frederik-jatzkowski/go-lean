//go:build golean_planned

package float64_special

//golean:verify
func IsNaN(x float64) bool { return x != x }

//golean:verify
func Less(x, y float64) bool { return x < y }
