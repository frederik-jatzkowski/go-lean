package float32_rounding

//golean:verify addUnitAtPrecisionBoundary : (AddUnit 16777216 == (16777216 : Float32)) = true
//golean:verify addUnitBelowPrecisionBoundary : (AddUnit 16777215 == (16777216 : Float32)) = true
func AddUnit(x float32) float32 { return x + 1 }

// RoundedConstant is just above the midpoint between 1 and its next float32.
//
//golean:verify constantRoundsOnce : RoundedConstant.toBits = 0x3f800001
func RoundedConstant() float32 { return 1.0000000596046448 }
