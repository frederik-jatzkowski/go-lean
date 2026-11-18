package arithmetic

//golean:verify
func CancelAdd(x, y int64) int64 {
	sum := x + y
	return sum - y
}

//golean:verify
func MultiplyByOne(x int64) int64 {
	var one int64 = 1
	return x * one
}

//golean:verify
func Increment(x int64) int64 {
	return x + 1
}
