package float64_special

//golean:verify
func IsNaN(x float64) bool { return x != x }

//golean:verify
func Less(x, y float64) bool { return x < y }

//golean:verify
func IsZero(x float64) bool { return x == 0.0 }

//golean:verify
func SmallestPositive() float64 { return 0x1p-1074 }
