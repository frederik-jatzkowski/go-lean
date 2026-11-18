//go:build golean_planned

package boolean_implication

//golean:verify
func Implies(p, q bool) bool {
	return !p || q
}
