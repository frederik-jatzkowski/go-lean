package immutable_closure

//golean:verify capturedOffsetIsAdded : ∀ (value offset : Int64),
//golean:verify+   AddOffset value offset = value + offset
func AddOffset(value, offset int64) int64 {
	add := func(x int64) int64 { return x + offset }
	return add(value)
}
