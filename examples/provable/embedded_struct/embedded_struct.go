package embedded_struct

type Point struct {
	X int64
}

type Sample struct {
	Point
	Scale int64
}

//golean:verify promotionReadsEmbeddedField : ∀ (sample : Sample),
//golean:verify+   PromotedX sample = ExplicitX sample
func PromotedX(sample Sample) int64 { return sample.X }

//golean:export
func ExplicitX(sample Sample) int64 { return sample.Point.X }
