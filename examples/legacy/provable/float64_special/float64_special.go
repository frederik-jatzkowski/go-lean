package float64_special

//golean:verify detectsNaN : ∀ (x : Float),
//golean:verify+   IsNaN x = x.isNaN
func IsNaN(x float64) bool { return x != x }

//golean:verify nanIsUnordered : ∀ (x y : Float) (h : x.isNaN = true ∨ y.isNaN = true),
//golean:verify+   Less x y = false
func Less(x, y float64) bool { return x < y }

//golean:verify signedZeroEqualsZero : IsZero (Float.ofBits 0x8000000000000000) = true
//golean:verify nanDoesNotEqualZero : IsZero (Float.ofBits 0x7ff8000000000000) = false
func IsZero(x float64) bool { return x == 0.0 }

//golean:verify preservesSubnormalConstant : SmallestPositive.toBits = 1
func SmallestPositive() float64 { return 0x1p-1074 }
