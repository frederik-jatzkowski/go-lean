-- Pending proof draft. The imported definitions will be generated when this feature is supported.
import bounded_counter.bounded_counter_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/bounded_counter».bounded_counter

-- The loop uses count - i as a termination measure over natural numbers.
theorem repeatedAdditionIsMultiplication (value : Int64) (count : UInt8) :
    RepeatAdd value count = value * Int64.ofNat count.toNat := by
  sorry
