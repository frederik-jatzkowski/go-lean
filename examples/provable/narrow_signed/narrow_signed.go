package narrow_signed

//golean:verify increment8Wraps : Increment8 Int8.maxValue = Int8.minValue
func Increment8(x int8) int8 { return x + 1 }

//golean:verify increment16Wraps : Increment16 Int16.maxValue = Int16.minValue
func Increment16(x int16) int16 { return x + 1 }

//golean:verify increment32Wraps : Increment32 Int32.maxValue = Int32.minValue
func Increment32(x int32) int32 { return x + 1 }
