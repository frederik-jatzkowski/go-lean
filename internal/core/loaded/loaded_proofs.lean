import «loaded».«loaded»

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/internal/core/loaded».Proofs

theorem «missingIDs» : Laws.«missingIDs» := by
  intro p
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem «objectLookup» : Laws.«objectLookup» := by
  intro p id nonzero
  simp [«Program$LookupObject», nonzero]

theorem «identityConversionRequiresSameScalar» : Laws.«identityConversionRequiresSameScalar» := by
  intro target source accepted
  by_cases same : target.«field:Basic» = source.«field:Basic»
  · exact same
  · simp [«Type$AllowsIdentityConversion», same] at accepted

end GoLean.«github.com/frederik-jatzkowski/go-lean/internal/core/loaded».Proofs
