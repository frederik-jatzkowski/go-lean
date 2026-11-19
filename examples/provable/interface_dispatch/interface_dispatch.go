package interface_dispatch

// Evaluator models an evaluation boundary.
//
//golean:law evaluate_identity : ∀ s x, Evaluate s x = x
type Evaluator interface {
	Evaluate(int64) int64
}

//golean:verify
func Apply(evaluator Evaluator, value int64) int64 { return evaluator.Evaluate(value) }
