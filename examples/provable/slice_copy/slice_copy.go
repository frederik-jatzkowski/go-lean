package slice_copy

//golean:verify clonePreservesContents : ∀ (xs : List Int64),
//golean:verify+   Clone xs = some xs
func Clone(values []int64) []int64 {
	result := make([]int64, len(values))
	copy(result, values)
	return result
}
