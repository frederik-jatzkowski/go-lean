package map_lookup

//golean:verify missingKeyUsesFallback : ∀ (key fallback : Int64),
//golean:verify+   ReadOr ([] : List (Int64 × Int64)) key fallback = fallback
//golean:verify presentZeroIsAValue : ∀ (key : Int64),
//golean:verify+   ReadOr [(key, 0)] key 9 = 0
//golean:verify missingKeyInNonemptyMap : ∀ (entry key value fallback : Int64) (different : key ≠ entry),
//golean:verify+   ReadOr [(entry, value)] key fallback = fallback
func ReadOr(values map[int64]int64, key, fallback int64) int64 {
	if value, ok := values[key]; ok {
		return value
	}
	return fallback
}
