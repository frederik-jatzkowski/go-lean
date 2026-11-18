//go:build golean_planned

package range_fold

//golean:verify
func Sum(values []int64) int64 {
	var result int64
	for _, value := range values {
		result += value
	}
	return result
}
