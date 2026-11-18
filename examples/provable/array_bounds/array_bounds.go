package array_bounds

//golean:verify
func AtOr(values [4]int64, index int, fallback int64) int64 {
	if index < 0 || index >= len(values) {
		return fallback
	}
	return values[index]
}
