package constant_conversions

type Count int64

const offset = 7

//golean:verify
func Adjusted(x Count) int64 { return int64(x) + offset }
