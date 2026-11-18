//go:build golean_reject

package interface_dispatch

type Evaluator interface {
	Evaluate(int64) int64
}

//golean:verify
func Apply(evaluator Evaluator, value int64) int64 { return evaluator.Evaluate(value) }
