package slice_bounds

//golean:verify
func At(values []int64, index int) int64 { return values[index] }

//golean:verify
func AtUnsigned(values []int64, index uint64) int64 { return values[index] }

//golean:verify
func Touch(values []int64, index int) int64 {
	_ = &values[index]
	return 7
}
