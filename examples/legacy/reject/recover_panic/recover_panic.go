//go:build golean_reject

package recover_panic

//golean:export
func RecoverDivision(value, divisor int64) (result int64) {
	defer func() {
		if recover() != nil {
			result = 0
		}
	}()
	return value / divisor
}
