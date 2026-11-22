package map_build

//golean:verify lastWriteWins : ∀ (key first last : Int64),
//golean:verify+   Overwrite key first last = some ([(key, last)] : List (Int64 × Int64))
func Overwrite(key, first, last int64) map[int64]int64 {
	values := make(map[int64]int64, 2)
	values[key] = first
	values[key] = last
	return values
}

//golean:verify distinctKeysRetainBothValues : ∀ (firstKey lastKey first last : Int64) (different : firstKey ≠ lastKey),
//golean:verify+   (WriteTwoKeys firstKey lastKey first last).bind (List.lookup firstKey) = some first ∧
//golean:verify+   (WriteTwoKeys firstKey lastKey first last).bind (List.lookup lastKey) = some last
func WriteTwoKeys(firstKey, lastKey, first, last int64) map[int64]int64 {
	values := make(map[int64]int64, 2)
	values[firstKey] = first
	values[lastKey] = last
	return values
}
