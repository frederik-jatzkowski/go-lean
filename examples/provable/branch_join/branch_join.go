package branch_join

//golean:verify
func PickThenIncrement(first, second int64) int64 {
	result := second
	if first < second {
		result = first
	}
	return result + 1
}

//golean:verify
func IncrementWithOptionalQuotient(useQuotient bool, value, divisor int64) int64 {
	result := value
	if useQuotient {
		result = value / divisor
	}
	return result + 1
}
