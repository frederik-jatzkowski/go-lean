package slice_copy

//golean:verify
func Clone(values []int64) []int64 {
	result := make([]int64, len(values))
	for i, value := range values {
		result[i] = value
	}
	return result
}
