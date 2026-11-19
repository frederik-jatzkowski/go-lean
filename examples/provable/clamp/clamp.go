package clamp

//golean:verify clampBounds : ∀ value low high : Int64, low ≤ high →
//golean:verify+ low ≤ Clamp value low high ∧ Clamp value low high ≤ high
//golean:verify clampIdempotent : ∀ value low high : Int64, low ≤ high →
//golean:verify+ Clamp (Clamp value low high) low high = Clamp value low high
func Clamp(value, low, high int64) int64 {
	if value < low {
		return low
	}
	if value > high {
		return high
	}
	return value
}
