import clamp.clamp_gen
import Std.Tactic.BVDecide

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/clamp».clamp

theorem clampBounds (value low high : Int64) (ordered : low ≤ high) :
    low ≤ Clamp value low high ∧ Clamp value low high ≤ high := by
  unfold Clamp
  bv_decide

theorem clampIdempotent (value low high : Int64) (ordered : low ≤ high) :
    Clamp (Clamp value low high) low high = Clamp value low high := by
  unfold Clamp
  bv_decide
