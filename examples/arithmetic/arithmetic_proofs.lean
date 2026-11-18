import arithmetic.arithmetic_gen
import Std.Tactic.BVDecide

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/arithmetic».arithmetic

theorem cancelAdd (x y : Int64) : CancelAdd x y = x := by
  unfold CancelAdd
  bv_decide

theorem multiplyByOne (x : Int64) : MultiplyByOne x = x := by
  unfold MultiplyByOne
  bv_decide

theorem incrementWraps : Increment Int64.maxValue = Int64.minValue := by
  decide
