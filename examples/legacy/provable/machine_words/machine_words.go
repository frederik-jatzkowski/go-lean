package machine_words

//golean:verify negativeOneUsesAllBits : ToUnsigned (-1) = (0 : GoTypes.UInt) - 1
func ToUnsigned(x int) uint { return uint(x) }

//golean:verify roundTrip : ∀ (x : GoTypes.Int),
//golean:verify+   RoundTrip x = x
func RoundTrip(x int) int { return int(ToUnsigned(x)) }
