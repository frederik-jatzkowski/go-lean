# Clamp with an imported package

Evaluate `Clamp(12, 2, 8)`. The inner `Max` keeps 12 because it is above 2. The outer `Min` returns 8. A second clamp on 8 leaves the result unchanged.

```go
func Clamp(value, low, high int64) int64 {
	return limits.Min(limits.Max(value, low), high)
}
```

## go-lean features

The `limits` package exports `Min` and `Max` and declares laws about their bounds and identity cases. The generated caller imports the concrete model of that package. The handwritten clamp proof imports `clamp_import.limits.limits_verify` to use its `Checked` theorems. [Caller](clamp_import.go) and [dependency](limits/limits.go)

## Proof challenge

`clampBounds` claims `low ≤ Clamp value low high ∧ Clamp value low high ≤ high` given `low ≤ high`. The upper bound follows directly from `atMostRight`. For the lower bound, split on the order of `Max value low` and `high`. The minimum is either the intermediate value, which is at least `low` by `atLeastRight`, or `high`, which is at least `low` by the premise.

`clampIdempotent` applies `clampBounds` to the first result. The lower bound makes `Max` an identity on the second call, and the upper bound makes `Min` an identity. Read the two theorems together to see how a verified fact becomes a premise for the next proof. [Lean proofs](clamp_import_proofs.lean)

```sh
go run ./cmd/go-lean verify ./examples/proven/clamp_import
```
