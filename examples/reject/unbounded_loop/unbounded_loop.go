//go:build golean_reject

package unbounded_loop

//golean:verify
func WaitForZero(value int64) int64 {
	// Adding two preserves parity, so odd inputs never reach zero.
	for value != 0 {
		value += 2
	}
	return value
}
