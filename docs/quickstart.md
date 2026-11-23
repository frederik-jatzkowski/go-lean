# Verify your first Go package

This example proves that clamping an integer produces a value between two ordered bounds. The [imported clamp walkthrough](../examples/proven/clamp_import/README.md) extends it by proving idempotence and reusing theorems from a separate Go package.

## Set up the project

Use Go 1.26 or later and install Elan so that `lean` and `lake` are on PATH. In a new directory, run:

```sh
go mod init example.com/firstproof
go get -tool github.com/frederik-jatzkowski/go-lean/cmd/go-lean@latest
go tool go-lean setup
go tool go-lean doctor
```

Use the existing module path if your project already has a `go.mod`, and substitute it in the proof namespace below. Setup pins Lean 4.36.0 when it creates `lean-toolchain` and preserves an existing pin. Commit the Go and Lean toolchain configuration to share it with contributors and CI.

## Declare a law

Create `clamp.go` in the module root:

```go
package clamp

//golean:verify bounds : ∀ x low high : Int64, low ≤ high →
//golean:verify+   low ≤ Clamp x low high ∧ Clamp x low high ≤ high
func Clamp(x, low, high int64) int64 {
	if x < low {
		return low
	}
	if x > high {
		return high
	}
	return x
}
```

The directive selects the whole package for translation and declares a proposition about `Clamp`. The premise `low ≤ high` limits the inputs covered by the theorem.

## Generate the model and prove the law

```sh
go tool go-lean transpile .
```

Read `clamp.lean` to see the translated function and `Laws.bounds`. Replace the scaffold in `clamp_proofs.lean` with:

```lean
import clamp

namespace GoLean.«example.com/firstproof».Proofs

theorem bounds : Laws.bounds := by
  intro x low high ordered
  by_cases below : x < low
  · simp [Clamp, below, ordered]
  · by_cases above : high < x
    · simp [Clamp, below, above, ordered]
    · simpa [Clamp, below, above] using
        And.intro (Int64.not_lt.mp below) (Int64.not_lt.mp above)

end GoLean.«example.com/firstproof».Proofs
```

The two case splits mirror the Go comparisons. When the result is an endpoint, the ordered-bounds premise supplies the other inequality. When the result is the input, the two failed comparisons give both inequalities.

```sh
go tool go-lean verify .
```

The generated verification module checks the proof and exposes the theorem as `GoLean.«example.com/firstproof».Checked.bounds`. Edit the Go declaration to change the law, and edit the proof companion to change its proof. Generation preserves an existing proof companion.

From a checkout of go-lean, use `go run ./cmd/go-lean` in place of `go tool go-lean`. For example, run `go run ./cmd/go-lean verify ./examples/proven/clamp_import` from the repository root.
