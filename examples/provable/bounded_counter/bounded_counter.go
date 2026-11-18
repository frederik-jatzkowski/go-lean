//go:build golean_planned

package bounded_counter

//golean:verify
func RepeatAdd(value int64, count uint8) int64 {
	var result int64
	for i := uint8(0); i < count; i++ {
		result += value
	}
	return result
}
