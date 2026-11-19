package bounded_counter

//golean:verify
func RepeatAdd(value int64, count int) int64 {
	var result int64
	for i := 0; i < count; i++ {
		result += value
	}
	return result
}
