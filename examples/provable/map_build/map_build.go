package map_build

//golean:verify
func Overwrite(key, first, last int64) map[int64]int64 {
	values := make(map[int64]int64)
	values[key] = first
	values[key] = last
	return values
}

//golean:verify
func WriteTwoKeys(firstKey, lastKey, first, last int64) map[int64]int64 {
	values := make(map[int64]int64)
	values[firstKey] = first
	values[lastKey] = last
	return values
}
