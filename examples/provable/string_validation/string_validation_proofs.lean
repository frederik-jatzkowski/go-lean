import string_validation.string_validation_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/string_validation».string_validation.Proofs

theorem validatesPrefix : Laws.validatesPrefix := by
  intro input ⟨word, representable⟩
  have size : (OfNat.ofNat input.size : GoTypes.Int).toInt = input.size := by
    first
    | exact Int64.toInt_ofNat_of_lt (have := Int64.toInt_lt word; by omega)
    | exact Int32.toInt_ofNat_of_lt (have := Int32.toInt_lt word; by omega)
  have two : (2 : GoTypes.Int).toInt = 2 := by decide
  have ltWord (x y : GoTypes.Int) : x < y ↔ x.toInt < y.toInt := by
    first | exact Int64.lt_iff_toInt_lt | exact Int32.lt_iff_toInt_lt
  first
  | change (Int64.ofNat input.size).toInt = _ at size
    change (Int64.ofInt 2).toInt = 2 at two
  | change (Int32.ofNat input.size).toInt = _ at size
    change (Int32.ofInt 2).toInt = 2 at two
  simp only [ValidateKey, ltWord, size, two, decide_eq_true_eq]
  by_cases short : input.size < 2
  · have h : ¬ 2 ≤ input.size := by omega
    rw [ite_eq_left (show (input.size : Int) < 2 from Int.ofNat_lt.mpr short)]
    simp [h]
  · have long : 2 ≤ input.size := by omega
    have longInt : (2 : Int) ≤ (input.size : Int) := Int.ofNat_le.mpr long
    rw [ite_eq_right (Int.not_lt.mpr longInt)]
    simp [long, longInt]

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/string_validation».string_validation.Proofs
