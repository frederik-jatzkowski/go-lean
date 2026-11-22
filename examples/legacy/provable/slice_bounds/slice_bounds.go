package slice_bounds

//golean:verify validIndexReadsElement : ∀ (xs : List Int64) (i : GoTypes.Int) (low : 0 ≤ i.toInt),
//golean:verify+   At xs i = xs[i.toInt.toNat]?
//golean:verify validIndexPanicFree : ∀ (xs : List Int64) (i : GoTypes.Int) (low : 0 ≤ i.toInt) (high : i.toInt < Int.ofNat xs.length),
//golean:verify+   ∃ result, At xs i = some result
//golean:verify invalidIndexPanics : ∀ (xs : List Int64) (i : GoTypes.Int) (outside : i.toInt < 0 ∨ Int.ofNat xs.length ≤ i.toInt),
//golean:verify+   At xs i = none
func At(values []int64, index int) int64 { return values[index] }

//golean:verify maxUnsignedIndexIsOutOfRange : AtUnsigned [42] 0xffffffffffffffff = none
func AtUnsigned(values []int64, index uint64) int64 { return values[index] }

//golean:verify discardedAddressStillPanics : Touch [] 0 = none
func Touch(values []int64, index int) int64 {
	_ = &values[index]
	return 7
}
