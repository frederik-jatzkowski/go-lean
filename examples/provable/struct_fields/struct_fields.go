//go:build golean_planned

package struct_fields

type Point struct {
	X int64
	Y int64
}

//golean:verify
func Swap(point Point) Point { return Point{X: point.Y, Y: point.X} }
