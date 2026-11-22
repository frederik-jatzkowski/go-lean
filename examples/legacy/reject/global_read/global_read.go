//go:build golean_reject

package global_read

var offset int64 = 7

//golean:export
func Adjust(value int64) int64 { return value + offset }
