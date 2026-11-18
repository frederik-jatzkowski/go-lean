//go:build golean_reject

package map_mutation

//golean:verify
func Set(values map[int64]int64, key, value int64) int64 {
	if values == nil {
		return 0
	}
	old := values[key]
	values[key] = value
	return old
}
