package switch_tagless

//golean:verify negativeMatchesFirst : ∀ (x : Int64) (negative : x < 0),
//golean:verify+   Bucket x = -1
//golean:verify smallNonnegativeMatchesSecond : ∀ (x : Int64) (low : 0 ≤ x) (high : x < 10),
//golean:verify+   Bucket x = 0
//golean:verify largeMatchesDefault : ∀ (x : Int64) (high : 10 ≤ x),
//golean:verify+   Bucket x = 1
func Bucket(x int64) int64 {
	switch {
	case x < 0:
		return -1
	case x < 10:
		return 0
	default:
		return 1
	}
}
