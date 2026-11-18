-- Pending proof draft. The imported definitions will be generated when this feature is supported.
import range_fold.range_fold_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/range_fold».range_fold

theorem rangeSumIsFold (xs : List Int64) : Sum xs = xs.foldl (· + ·) 0 := by
  sorry
