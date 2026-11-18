//go:build golean_planned

package switch_value

//golean:verify
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
