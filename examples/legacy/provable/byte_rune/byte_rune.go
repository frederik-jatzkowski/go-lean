package byte_rune

//golean:verify lowerASCIIIdempotent : ∀ (b : UInt8),
//golean:verify+   LowerASCII (LowerASCII b) = LowerASCII b
func LowerASCII(b byte) byte {
	if 'A' <= b && b <= 'Z' {
		return b + ('a' - 'A')
	}
	return b
}

//golean:verify asciiDigit : DigitValue 0x39 = 9
//golean:verify nonASCIIDigit : DigitValue 0x660 = -1
func DigitValue(r rune) int32 {
	if '0' <= r && r <= '9' {
		return r - '0'
	}
	return -1
}
