package interface_dispatch

// Evaluator models an evaluation boundary.
//
//golean:assume evaluate_identity : ∀ s x, Evaluate s x = x
type Evaluator interface {
	Evaluate(int64) int64
}

//golean:verify apply_identity : ∀ {Handle : Type} (contract : InterfaceContracts.EvaluatorContract Handle) (evaluator : Handle)
//golean:verify+   (value : Int64),
//golean:verify+   Apply contract evaluator value = value
func Apply(evaluator Evaluator, value int64) int64 { return evaluator.Evaluate(value) }
