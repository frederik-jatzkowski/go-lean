//go:build golean_reject

package type_assertion

//golean:verify
func Unbox(value any) int64 {
	if integer, ok := value.(int64); ok {
		return integer
	}
	return 0
}
