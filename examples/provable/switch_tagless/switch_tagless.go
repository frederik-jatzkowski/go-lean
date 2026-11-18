//go:build golean_planned

package switch_tagless

//golean:verify
func Bucket(x int64) int64 {
	switch {
	case x < 0:
		return -1
	case x < 10:
		return 0
	default:
		return 1
	}
}
