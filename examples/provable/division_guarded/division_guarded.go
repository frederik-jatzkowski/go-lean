//go:build golean_planned

package division_guarded

//golean:verify
func DivideOr(x, divisor, fallback int64) int64 {
	if divisor == 0 {
		return fallback
	}
	return x / divisor
}
