package range_fold

//golean:verify rangeSumIsFold : ∀ (xs : List Int64),
//golean:verify+   Sum xs = xs.foldl (· + ·) 0
func Sum(values []int64) int64 {
	var result int64
	for _, value := range values {
		result += value
	}
	return result
}
