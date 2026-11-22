import integer_clamp.integer_clamp_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/integer_clamp».integer_clamp.Proofs

theorem clampsToByte : Laws.clampsToByte := by
  intro x
  have lower := x.le_toInt
  have upper := x.toInt_lt
  have widening : (Int64.ofInt x.toInt).toInt = x.toInt :=
    Int64.toInt_ofInt_of_le (by omega) (by omega)
  have byteCast (n : Int) (lo : 0 ≤ n) (hi : n < 256) :
      (Int8.ofInt n).toUInt8.toNat = n.toNat := by
    change (BitVec.ofInt 8 n).toNat = n.toNat
    rw [BitVec.toNat_ofInt]
    change (n % 256).toNat = n.toNat
    rw [Int.emod_eq_of_lt lo hi]
  have zero : (Int64.ofInt 0).toInt = 0 := by decide
  have top : (Int64.ofInt 255).toInt = 255 := by decide
  unfold ClampToByte
  simp only [Int64.lt_iff_toInt_lt, widening, zero, top]
  by_cases below : x.toInt < 0
  · rw [ite_eq_left below, zero, ite_eq_right (show ¬ (255 : Int) < 0 by decide), zero]
    rw [byteCast _ (by decide) (by decide), Int.min_eq_right (by omega), Int.max_eq_left (by omega)]
  · rw [ite_eq_right below, widening]
    by_cases above : 255 < x.toInt
    · rw [ite_eq_left above, top, byteCast _ (by decide) (by decide),
        Int.min_eq_left (by omega), Int.max_eq_right (by decide)]
    · rw [ite_eq_right above, widening, byteCast _ (by omega) (by omega),
        Int.min_eq_right (by omega), Int.max_eq_right (by omega)]

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/integer_clamp».integer_clamp.Proofs
