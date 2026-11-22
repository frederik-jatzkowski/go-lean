package branch_join

//golean:verify branchAssignmentReachesJoin : ∀ (first second : Int64),
//golean:verify+   PickThenIncrement first second = (if first < second then first else second) + 1
func PickThenIncrement(first, second int64) int64 {
	result := second
	if first < second {
		result = first
	}
	return result + 1
}

//golean:verify skippedDivisionReachesJoin : ∀ (value : Int64),
//golean:verify+   IncrementWithOptionalQuotient false value 0 = some (value + 1)
//golean:verify divisionPanicSkipsJoin : ∀ (value : Int64),
//golean:verify+   IncrementWithOptionalQuotient true value 0 = none
func IncrementWithOptionalQuotient(useQuotient bool, value, divisor int64) int64 {
	result := value
	if useQuotient {
		result = value / divisor
	}
	return result + 1
}
