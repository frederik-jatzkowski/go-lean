package integer_clamp

//golean:verify clampsToByte : ∀ x : Int32,
//golean:verify+   (ClampToByte x).toNat = (max 0 (min 255 x.toInt)).toNat
func ClampToByte(x int32) uint8 {
	return uint8(min(max(int64(x), 0), 255))
}
