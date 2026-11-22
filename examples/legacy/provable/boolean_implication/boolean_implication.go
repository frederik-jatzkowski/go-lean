package boolean_implication

//golean:verify impliesFalse : ∀ (q : Bool),
//golean:verify+   Implies false q = true
//golean:verify impliesTrue : ∀ (q : Bool),
//golean:verify+   Implies true q = q
func Implies(p, q bool) bool {
	return !p || q
}

func positiveQuotient(x, divisor int64) bool {
	return x/divisor > 0
}

//golean:verify falseSkipsDivision : ∀ (x : Int64),
//golean:verify+   AndCheck false x 0 = some false
//golean:verify trueEvaluatesDivision : ∀ (x : Int64),
//golean:verify+   AndCheck true x 0 = none
func AndCheck(p bool, x, divisor int64) bool {
	return p && positiveQuotient(x, divisor)
}
