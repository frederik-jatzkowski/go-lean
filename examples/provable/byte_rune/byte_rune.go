//go:build golean_planned

package byte_rune

//golean:verify
func LowerASCII(b byte) byte {
	if 'A' <= b && b <= 'Z' {
		return b + ('a' - 'A')
	}
	return b
}

//golean:verify
func DigitValue(r rune) int32 {
	if '0' <= r && r <= '9' {
		return r - '0'
	}
	return -1
}
