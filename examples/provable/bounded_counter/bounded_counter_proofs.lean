import bounded_counter.bounded_counter_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/bounded_counter».bounded_counter

private theorem loopAdds (value : Int64) (fuel : Nat) (acc : Int64) :
    «RepeatAdd$loop» value fuel acc = acc + value * Int64.ofNat fuel := by
  induction fuel generalizing acc with
  | zero => simp [«RepeatAdd$loop»]
  | succ fuel ih =>
    change «RepeatAdd$loop» value fuel (acc + value) =
      acc + value * Int64.ofNat (fuel + 1)
    have step : Int64.ofNat (fuel + 1) = Int64.ofNat fuel + 1 :=
      Int64.ofNat_add fuel 1
    rw [ih, step, Int64.mul_succ]
    ac_rfl

theorem repeatedAdditionIsMultiplication (value : Int64) (count : UInt8) :
    RepeatAdd value count = value * Int64.ofNat count.toNat := by
  simp [RepeatAdd, loopAdds]
