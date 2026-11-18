//go:build golean_reject

package deferred_effect

var calls int64

//golean:verify
func CountAfterReturn(value int64) int64 {
	defer func() { calls++ }()
	return value
}
