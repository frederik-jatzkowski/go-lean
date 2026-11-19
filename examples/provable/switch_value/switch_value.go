package switch_value

//golean:verify firstTwoTiers : ∀ (tier : Int64) (h : tier = 1 ∨ tier = 2),
//golean:verify+   Rate tier = 5
//golean:verify thirdTier : Rate 3 = 8
//golean:verify unmatchedTier : ∀ (tier : Int64) (h₁ : tier ≠ 1) (h₂ : tier ≠ 2) (h₃ : tier ≠ 3),
//golean:verify+   Rate tier = 0
func Rate(tier int64) int64 {
	switch tier {
	case 1, 2:
		return 5
	case 3:
		return 8
	default:
		return 0
	}
}
