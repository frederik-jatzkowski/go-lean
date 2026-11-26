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

theorem packageVariablesRejected : Laws.packageVariablesRejected := by
  intro p declaration object isVariable
  simp [«Program$CheckDeclaration», isVariable, Variable, UnsupportedPackageVariable]

theorem rawLoopsRejected : Laws.rawLoopsRejected := by
  intro pos loop
  rfl

theorem genericSignaturesRejected : Laws.genericSignaturesRejected := by
  intro f signature result generic
  cases variadic : signature.«field:Variadic» <;>
    simp [«Function$ValidateSignature», generic, variadic, InvalidFunctionSignature]

theorem signatureRequiresUnnamedResultAndValueReceiver :
    Laws.signatureRequiresUnnamedResultAndValueReceiver := by
  intro f signature result accepted
  unfold «Function$ValidateSignature» at accepted
  split at accepted
  · simp [Valid] at accepted
  · by_cases receiver : signature.«field:Receiver» = 0 <;>
      cases value : signature.«field:ValueReceiver» <;>
      by_cases name : result.«field:Name» = [] <;>
      simp_all [Valid, validDiagnostic] <;>
      split at accepted <;> simp at accepted

theorem methodDispatchRequiresDirectValueReceiver :
    Laws.methodDispatchRequiresDirectValueReceiver := by
  intro call signature pos selected
  unfold NoSelection at selected
  cases value : signature.«field:ValueReceiver» <;>
    cases direct : call.«field:Selection».«field:Direct» <;>
    simp [«CallExpr$ValidateReceiver», selected, value, direct, Valid, validDiagnostic]

theorem nonEnumSwitchesRejected : Laws.nonEnumSwitchesRejected := by
  intro s method pos missing
  rcases missing with missing | missing
  · simp [«SwitchStmt$ValidateCaseMethod», missing, InvalidEnumSwitch]
  · by_cases selected : s.«field:CaseMethod» = 0 <;>
      simp [«SwitchStmt$ValidateCaseMethod», selected, missing, InvalidEnumSwitch]

end GoLean.«github.com/frederik-jatzkowski/go-lean/internal/core/loaded».Proofs
