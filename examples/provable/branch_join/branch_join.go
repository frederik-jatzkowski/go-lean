//go:build golean_planned

package branch_join

//golean:verify
func PickThenIncrement(first, second int64) int64 {
	result := second
	if first < second {
		result = first
	}
	return result + 1
}
