# Assumed worker

Call `MatchesInput(42)`. The runtime worker sends 42 through a channel and returns the received value. The caller compares that result with 42.

```go
//golean:abstract worker.Mirror
//golean:verify matchesInput : ∀ x : Int64, MatchesInput dependency0 x = true
func MatchesInput(x int64) bool {
	return worker.Mirror(x) == x
}
```

## go-lean features

`//golean:abstract worker.Mirror` replaces the modeled direct call with the operation from a contract. The worker's `//golean:assume` directives supply `preservesInput` and `preservesZero` as contract fields. The law names the first generated contract parameter `dependency0`. [Caller](assumed_worker.go) and [worker](worker/worker.go)

## Proof challenge

After introducing the contract and input, the proof reduces the goal to `decide (worker.operation x = x) = true`. The field `worker.preservesInput x` provides exactly the equality needed by `simp`. The proof uses the general input law without using the zero-specific field.

The checked theorem quantifies over a worker satisfying the contract. For the Go implementation, the argument for that contract comes from inspecting the channel exchange. The only sent value is the input, and the return reads that value. The verified caller law concerns the comparison after a normal return. [Lean proof](assumed_worker_proofs.lean)

```sh
go run ./cmd/go-lean verify ./examples/proven/assumed_worker
```
