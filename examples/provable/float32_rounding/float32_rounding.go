package float32_rounding

//golean:verify
func AddUnit(x float32) float32 { return x + 1 }

// RoundedConstant is just above the midpoint between 1 and its next float32.
//
//golean:verify
func RoundedConstant() float32 { return 1.0000000596046448 }
