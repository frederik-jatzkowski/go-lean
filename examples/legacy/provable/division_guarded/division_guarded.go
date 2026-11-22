package division_guarded

//golean:verify divideOrZero : ∀ (x fallback : Int64),
//golean:verify+   DivideOr x 0 fallback = some fallback
//golean:verify divideOrNonzero : ∀ (x divisor fallback : Int64) (h : divisor ≠ 0),
//golean:verify+   DivideOr x divisor fallback = some (Int64.ofInt (x.toInt.tdiv divisor.toInt))
//golean:verify divideOrPanicFree : ∀ (x divisor fallback : Int64),
//golean:verify+   ∃ result, DivideOr x divisor fallback = some result
func DivideOr(x, divisor, fallback int64) int64 {
	if divisor == 0 {
		return fallback
	}
	return x / divisor
}
