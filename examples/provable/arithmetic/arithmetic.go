package arithmetic

//golean:verify cancelAdd : ∀ (x y : Int64),
//golean:verify+   CancelAdd x y = x
func CancelAdd(x, y int64) int64 {
	sum := x + y
	return sum - y
}

//golean:verify multiplyByOne : ∀ (x : Int64),
//golean:verify+   MultiplyByOne x = x
func MultiplyByOne(x int64) int64 {
	var one int64 = 1
	return x * one
}

//golean:verify incrementWraps : Increment Int64.maxValue = Int64.minValue
func Increment(x int64) int64 {
	return x + 1
}
