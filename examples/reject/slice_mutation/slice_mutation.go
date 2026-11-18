//go:build golean_reject

package slice_mutation

//golean:verify
func ReplaceFirst(values []int64, value int64) int64 {
	if len(values) == 0 {
		return 0
	}
	old := values[0]
	values[0] = value
	return old
}
