//go:build golean_planned

package string_bytes

//golean:verify
func Join(a, b string) string { return a + b }

//golean:verify
func ByteLen(s string) int { return len(s) }
