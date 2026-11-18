package integerremainder

const daysPerMonth = 30

// DayOfMonth converts elapsed campaign days into a 1-based calendar day.
//
//golean:verify
func DayOfMonth(elapsed uint64) uint64 {
	return elapsed%daysPerMonth + 1
}

// OffsetInPeriod keeps the sign of a backward offset.
//
//golean:verify
func OffsetInPeriod(offset, period int64) int64 {
	return offset % period
}

// OffsetOrZero treats a zero period as a disabled cycle.
//
//golean:verify
func OffsetOrZero(offset, period int64) int64 {
	if period == 0 {
		return 0
	}
	return OffsetInPeriod(offset, period)
}
