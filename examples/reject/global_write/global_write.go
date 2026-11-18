//go:build golean_reject

package global_write

var total int64

//golean:verify
func Accumulate(value int64) int64 {
	total += value
	return total
}
