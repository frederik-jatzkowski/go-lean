package filter_and_count

//golean:verify filtersAndCounts : ∀ (input : Option (List ByteArray × Nat)),
//golean:verify+   let keys := (input.getD ([], 0)).1
//golean:verify+   let keep := keys.filter (fun key => !(key == ByteArray.mk #[]))
//golean:verify+   let result := FilterAndCount input
//golean:verify+   result.1 = some (keep, keys.length) ∧
//golean:verify+   ∀ key : ByteArray, List.lookup key result.2 =
//golean:verify+     if keep.count key = 0 then none else some ((OfNat.ofNat (keep.count key) : GoTypes.Int))
func FilterAndCount(keys []string) ([]string, map[string]int) {
	filtered := make([]string, 0, len(keys))
	counts := make(map[string]int)
	for _, key := range keys {
		if key == "" {
			continue
		}
		filtered = append(filtered, key)
		counts[key]++
	}
	return filtered, counts
}
