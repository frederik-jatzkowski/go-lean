package division_propagation

func quotient(x, divisor int64) int64 { return x / divisor }

//golean:verify
func DivideThenIncrement(x, divisor int64) int64 {
	return quotient(x, divisor) + 1
}
