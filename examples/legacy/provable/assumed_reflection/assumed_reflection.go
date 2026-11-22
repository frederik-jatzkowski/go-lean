package assumed_reflection

import "reflect"

type Reading int64

//golean:assume returnsReading : ∀ r : Int64, Value r = r
func (r Reading) Value() int64 {
	return reflect.ValueOf(r).Int()
}

//golean:abstract Reading.Value
//golean:verify agreesWithSign : ∀ r : Int64, Nonnegative r = decide (0 ≤ r)
func Nonnegative(r Reading) bool {
	return r.Value() >= 0
}
