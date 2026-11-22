package division_propagation

func quotient(x, divisor int64) int64 { return x / divisor }

//golean:verify propagatesDivisionPanic : ∀ (x : Int64),
//golean:verify+   DivideThenIncrement x 0 = none
//golean:verify incrementsSuccessfulQuotient : ∀ (x divisor : Int64) (h : divisor ≠ 0),
//golean:verify+   DivideThenIncrement x divisor = some (Int64.ofInt (x.toInt.tdiv divisor.toInt) + 1)
func DivideThenIncrement(x, divisor int64) int64 {
	return quotient(x, divisor) + 1
}
