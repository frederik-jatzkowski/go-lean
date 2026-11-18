package boolean_implication

//golean:verify
func Implies(p, q bool) bool {
	return !p || q
}

func positiveQuotient(x, divisor int64) bool {
	return x/divisor > 0
}

//golean:verify
func AndCheck(p bool, x, divisor int64) bool {
	return p && positiveQuotient(x, divisor)
}
