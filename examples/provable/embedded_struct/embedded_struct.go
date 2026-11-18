package embedded_struct

type Point struct {
	X int64
}

type Sample struct {
	Point
	Scale int64
}

//golean:verify
func PromotedX(sample Sample) int64 { return sample.X }

//golean:verify
func ExplicitX(sample Sample) int64 { return sample.Point.X }
