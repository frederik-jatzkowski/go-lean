//go:build golean_planned

package narrow_signed

//golean:verify
func Increment8(x int8) int8 { return x + 1 }

//golean:verify
func Increment16(x int16) int16 { return x + 1 }

//golean:verify
func Increment32(x int32) int32 { return x + 1 }
