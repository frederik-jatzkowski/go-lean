package division_precondition

//golean:verify dividePanicFree : ∀ (x divisor : Int64) (h : divisor ≠ 0),
//golean:verify+   Divide x divisor = some (Int64.ofInt (x.toInt.tdiv divisor.toInt))
//golean:verify divideByZeroPanics : ∀ (x : Int64),
//golean:verify+   Divide x 0 = none
//golean:verify negativeDividendTruncates : Divide (-7) 3 = some (-2)
//golean:verify negativeDivisorTruncates : Divide 7 (-3) = some (-2)
//golean:verify minDividedByNegativeOne : Divide Int64.minValue (-1) = some Int64.minValue
func Divide(x, divisor int64) int64 { return x / divisor }
