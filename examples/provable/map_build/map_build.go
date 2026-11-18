//go:build golean_planned

package map_build

//golean:verify
func Overwrite(key, first, last int64) map[int64]int64 {
	values := make(map[int64]int64)
	values[key] = first
	values[key] = last
	return values
}
