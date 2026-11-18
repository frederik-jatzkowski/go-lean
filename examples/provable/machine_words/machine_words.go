//go:build golean_planned

package machine_words

//golean:verify
func ToUnsigned(x int) uint { return uint(x) }

//golean:verify
func RoundTrip(x int) int { return int(ToUnsigned(x)) }
