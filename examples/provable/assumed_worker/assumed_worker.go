package assumed_worker

import "github.com/frederik-jatzkowski/go-lean/examples/provable/assumed_worker/worker"

//golean:abstract worker.Mirror
//golean:verify matchesInput : ∀ x : Int64, MatchesInput dependency0 x = true
func MatchesInput(x int64) bool {
	return worker.Mirror(x) == x
}
