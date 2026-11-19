package integerremainder

const daysPerMonth = 30

// DayOfMonth converts elapsed campaign days into a 1-based calendar day.
//
//golean:verify dayBounds : ∀ (elapsed : UInt64),
//golean:verify+   ∃ day, DayOfMonth elapsed = some day ∧ 1 ≤ day ∧ day ≤ 30
//golean:verify monthRollover : DayOfMonth 29 = some 30 ∧ DayOfMonth 30 = some 1
func DayOfMonth(elapsed uint64) uint64 {
	return elapsed%daysPerMonth + 1
}

// OffsetInPeriod keeps the sign of a backward offset.
//
//golean:verify signedRemainder : OffsetInPeriod (-7) 3 = some (-1) ∧ OffsetInPeriod 7 (-3) = some 1
//golean:verify minimumByNegativeOne : OffsetInPeriod (-9223372036854775808) (-1) = some 0
//golean:verify zeroPeriodPanics : ∀ (offset : Int64),
//golean:verify+   OffsetInPeriod offset 0 = none
func OffsetInPeriod(offset, period int64) int64 {
	return offset % period
}

// OffsetOrZero treats a zero period as a disabled cycle.
//
//golean:verify zeroPeriodFallback : ∀ (offset : Int64),
//golean:verify+   OffsetOrZero offset 0 = some 0
//golean:verify nonzeroPeriod : ∀ (offset period : Int64) (h : period ≠ 0),
//golean:verify+   OffsetOrZero offset period = some (offset % period)
func OffsetOrZero(offset, period int64) int64 {
	if period == 0 {
		return 0
	}
	return OffsetInPeriod(offset, period)
}
