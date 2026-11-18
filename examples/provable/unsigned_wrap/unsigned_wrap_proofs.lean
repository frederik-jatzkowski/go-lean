import unsigned_wrap.unsigned_wrap_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/unsigned_wrap».unsigned_wrap

theorem increment8Wraps : Increment8 0xff = 0 := by
  decide

theorem increment16Wraps : Increment16 0xffff = 0 := by
  decide

theorem increment32Wraps : Increment32 0xffffffff = 0 := by
  decide

theorem increment64Wraps : Increment64 0xffffffffffffffff = 0 := by
  decide

theorem zeroDivisorPanics (value : UInt64) : Quotient64 value 0 = none := by
  simp [Quotient64]

theorem quotientUsesUnsignedMagnitude :
    Quotient64 0xffffffffffffffff 2 = some 0x7fffffffffffffff := by
  decide
