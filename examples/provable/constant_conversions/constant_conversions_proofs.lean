import constant_conversions.constant_conversions_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/constant_conversions».constant_conversions.Proofs

-- Count is represented by its underlying signed integer type.
theorem addsPackageConstant : Laws.addsPackageConstant := by
  intro x
  rfl

theorem namedInputWraps : Laws.namedInputWraps := by
  unfold Laws.namedInputWraps
  decide

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/constant_conversions».constant_conversions.Proofs
