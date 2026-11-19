package bounded_counter

//golean:verify repeatedAdditionIsMultiplication : ∀ (value : Int64) (count : GoTypes.Int),
//golean:verify+   RepeatAdd value count = value * Int64.ofNat count.toInt.toNat
func RepeatAdd(value int64, count int) int64 {
	var result int64
	for i := 0; i < count; i++ {
		result += value
	}
	return result
}
