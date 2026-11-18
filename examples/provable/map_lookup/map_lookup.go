//go:build golean_planned

package map_lookup

//golean:verify
func ReadOr(values map[int64]int64, key, fallback int64) int64 {
	if value, ok := values[key]; ok {
		return value
	}
	return fallback
}
