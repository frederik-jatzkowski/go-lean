package array_bounds

//golean:verify guardedIndexInBounds : ∀ (xs : Vector Int64 4) (i : GoTypes.Int) (fallback : Int64) (low : 0 ≤ i.toInt) (high : i.toInt < 4),
//golean:verify+   AtOr xs i fallback = xs.toArray[i.toInt.toNat]?
//golean:verify guardedIndexFallback : ∀ (xs : Vector Int64 4) (i : GoTypes.Int) (fallback : Int64) (outside : i.toInt < 0 ∨ 4 ≤ i.toInt),
//golean:verify+   AtOr xs i fallback = some fallback
//golean:verify guardedIndexPanicFree : ∀ (xs : Vector Int64 4) (i : GoTypes.Int) (fallback : Int64),
//golean:verify+   ∃ result, AtOr xs i fallback = some result
func AtOr(values [4]int64, index int, fallback int64) int64 {
	if index < 0 || index >= len(values) {
		return fallback
	}
	return values[index]
}
