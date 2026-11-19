package slice_copy

//golean:verify
func Clone(values []int64) []int64 {
	result := make([]int64, len(values))
	copy(result, values)
	return result
}
