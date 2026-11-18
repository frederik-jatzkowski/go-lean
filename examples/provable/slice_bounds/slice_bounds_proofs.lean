-- Pending proof draft. The imported definitions will be generated when this feature is supported.
import slice_bounds.slice_bounds_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/slice_bounds».slice_bounds

theorem validIndexPanicFree (xs : List Int64) (i : ISize)
    (low : 0 ≤ i.toInt) (high : i.toInt < Int.ofNat xs.length) :
    ∃ result, At xs i = some result := by
  sorry

theorem validIndexReadsElement (xs : List Int64) (i : ISize) (low : 0 ≤ i.toInt) :
    At xs i = xs[i.toInt.toNat]? := by
  sorry

theorem invalidIndexPanics (xs : List Int64) (i : ISize)
    (outside : i.toInt < 0 ∨ Int.ofNat xs.length ≤ i.toInt) :
    At xs i = none := by
  sorry
