package unsigned_wrap

//golean:verify increment8Wraps : Increment8 0xff = 0
func Increment8(x uint8) uint8 { return x + 1 }

//golean:verify increment16Wraps : Increment16 0xffff = 0
func Increment16(x uint16) uint16 { return x + 1 }

//golean:verify increment32Wraps : Increment32 0xffffffff = 0
func Increment32(x uint32) uint32 { return x + 1 }

//golean:verify increment64Wraps : Increment64 0xffffffffffffffff = 0
func Increment64(x uint64) uint64 { return x + 1 }

//golean:verify zeroDivisorPanics : ∀ (value : UInt64),
//golean:verify+   Quotient64 value 0 = none
//golean:verify quotientUsesUnsignedMagnitude : Quotient64 0xffffffffffffffff 2 = some 0x7fffffffffffffff
func Quotient64(value, divisor uint64) uint64 { return value / divisor }
