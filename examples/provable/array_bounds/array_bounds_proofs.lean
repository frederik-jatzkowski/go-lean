-- Pending proof draft. The imported definitions will be generated when this feature is supported.
import array_bounds.array_bounds_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/array_bounds».array_bounds

theorem guardedIndexPanicFree (xs : Vector Int64 4) (i : ISize) (fallback : Int64) :
    ∃ result, AtOr xs i fallback = some result := by
  sorry

theorem guardedIndexInBounds (xs : Vector Int64 4) (i : ISize) (fallback : Int64)
    (low : 0 ≤ i.toInt) (high : i.toInt < 4) :
    AtOr xs i fallback = xs.toArray[i.toInt.toNat]? := by
  sorry

theorem guardedIndexFallback (xs : Vector Int64 4) (i : ISize) (fallback : Int64)
    (outside : i.toInt < 0 ∨ 4 ≤ i.toInt) :
    AtOr xs i fallback = some fallback := by
  sorry
