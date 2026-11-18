import constant_conversions.constant_conversions_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/constant_conversions».constant_conversions

-- Count is represented by its underlying signed integer type.
theorem addsPackageConstant (x : Int64) : Adjusted x = x + 7 := by
  rfl

theorem namedInputWraps : Adjusted Int64.maxValue = Int64.minValue + 6 := by
  decide
