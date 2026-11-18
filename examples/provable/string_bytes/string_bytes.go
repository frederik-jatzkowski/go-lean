package string_bytes

//golean:verify
func Join(a, b string) string { return a + b }

//golean:verify
func ByteLen(s string) int { return len(s) }

//golean:verify
func AddRawPrefix(s string) string { return "\xff\x00" + s }
