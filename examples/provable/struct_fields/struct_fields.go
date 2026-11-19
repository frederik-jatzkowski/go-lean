package struct_fields

type Point struct {
	X int64
	Y int64
}

//golean:verify swapInvolutive : ∀ (point : Point),
//golean:verify+   Swap (Swap point) = point
func Swap(point Point) Point { return Point{X: point.Y, Y: point.X} }
