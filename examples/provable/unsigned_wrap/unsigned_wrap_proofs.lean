-- Pending proof draft. The imported definitions will be generated when this feature is supported.
import unsigned_wrap.unsigned_wrap_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/unsigned_wrap».unsigned_wrap

theorem increment8Wraps : Increment8 0xff = 0 := by
  sorry

theorem increment16Wraps : Increment16 0xffff = 0 := by
  sorry

theorem increment32Wraps : Increment32 0xffffffff = 0 := by
  sorry

theorem increment64Wraps : Increment64 0xffffffffffffffff = 0 := by
  sorry
