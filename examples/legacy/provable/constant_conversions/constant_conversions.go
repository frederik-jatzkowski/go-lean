package constant_conversions

type Count int64

const offset = 7

//golean:verify addsPackageConstant : ∀ (x : Int64),
//golean:verify+   Adjusted x = x + 7
//golean:verify namedInputWraps : Adjusted Int64.maxValue = Int64.minValue + 6
func Adjusted(x Count) int64 { return int64(x) + offset }
