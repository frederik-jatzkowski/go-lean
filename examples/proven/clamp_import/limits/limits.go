package limits

//golean:export
//golean:verify atMostRight : ∀ x y : Int64, Min x y ≤ y
//golean:verify leftIdentity : ∀ x y : Int64, x ≤ y → Min x y = x
//golean:verify rightIdentity : ∀ x y : Int64, y ≤ x → Min x y = y
func Min(x, y int64) int64 {
	if x < y {
		return x
	}
	return y
}

//golean:export
//golean:verify atLeastRight : ∀ x y : Int64, y ≤ Max x y
//golean:verify leftIdentityMax : ∀ x y : Int64, y ≤ x → Max x y = x
func Max(x, y int64) int64 {
	if x > y {
		return x
	}
	return y
}
