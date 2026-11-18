//go:build golean_planned

package unsigned_wrap

//golean:verify
func Increment8(x uint8) uint8 { return x + 1 }

//golean:verify
func Increment16(x uint16) uint16 { return x + 1 }

//golean:verify
func Increment32(x uint32) uint32 { return x + 1 }

//golean:verify
func Increment64(x uint64) uint64 { return x + 1 }
