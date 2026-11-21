import bytecode_vm.compiler.emit_proof

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/bytecode_vm/compiler».compiler.TypeProof

open PassModel EmitProof

set_option linter.unusedSimpArgs false

private theorem signatureAgrees (kind : UInt8) : operatorTypes kind = signature kind := by
  by_cases a : kind = 3 <;> by_cases b : kind = 4 <;> by_cases c : kind = 5 <;>
    by_cases d : kind = 6 <;> simp [operatorTypes, signature, a, b, c, d]

private theorem less {a b : Nat} (ha : a ≤ 256) (hb : b ≤ 256) :
    native a < native b ↔ a < b := by
  first | rw [Int64.lt_iff_toInt_lt] | rw [Int32.lt_iff_toInt_lt]
  rw [counterValue ha, counterValue hb]
  omega

private theorem ge {a b : Nat} (ha : a ≤ 256) (hb : b ≤ 256) :
    native a ≥ native b ↔ a ≥ b := by
  change native b ≤ native a ↔ b ≤ a
  first | rw [Int64.le_iff_toInt_le] | rw [Int32.le_iff_toInt_le]
  rw [counterValue ha, counterValue hb]
  omega

private theorem inferAgrees (kind left right : UInt8) (index : Nat) (h : index < 32)
    (known : Vector UInt8 32) :
    infer kind (native left.toNat) (native right.toNat) (native index) known =
      some (nodeType kind left.toNat right.toNat index known) := by
  have leftFits : left.toNat ≤ 256 := by have := left.toNat_lt; omega
  have rightFits : right.toNat ≤ 256 := by have := right.toNat_lt; omega
  have atL := counterValue leftFits
  have atR := counterValue rightFits
  have geL := ge (a := left.toNat) (b := index) leftFits (by omega)
  have geR := ge (a := right.toNat) (b := index) rightFits (by omega)
  by_cases int : kind = 1
  · simp [infer, nodeType, int]
  by_cases bool : kind = 2
  · simp [infer, nodeType, int, bool]
  by_cases l : left.toNat < index
  · have lread := read known (show left.toNat < 32 by omega)
    by_cases lmatch : known.getD left.toNat 0 = (signature kind).1
    · by_cases unary : kind = 8
      · simp [infer, nodeType, arity, signatureAgrees, int, bool, unary, geL,
          Nat.not_le.mpr l, l, atL, lread, lmatch]
      · by_cases r : right.toNat < index
        · have rread := read known (show right.toNat < 32 by omega)
          by_cases rmatch : known.getD right.toNat 0 = (signature kind).1 <;>
            simp [infer, nodeType, arity, signatureAgrees, int, bool, unary, geL, geR,
              Nat.not_le.mpr l, Nat.not_le.mpr r, l, r, atL, atR, lread, rread, lmatch, rmatch]
        · simp [infer, nodeType, arity, signatureAgrees, int, bool, unary, geL, geR,
            Nat.not_le.mpr l, Nat.le_of_not_gt r, l, r, atL, lread, lmatch]
    · simp [infer, nodeType, signatureAgrees, int, bool, geL, Nat.not_le.mpr l, l, atL, lread, lmatch]
  · simp [infer, nodeType, int, bool, geL, Nat.le_of_not_gt l, l]

private theorem subOne (n : Nat) (pos : 0 < n) :
    native n - signed 1 = native (n-1) := by
  change signed (n : Int) - signed 1 = signed ((n-1 : Nat) : Int)
  first | rw [← Int64.ofInt_sub] | rw [← Int32.ofInt_sub]
  rw [show (n : Int) - 1 = ((n-1 : Nat) : Int) by omega]

private theorem checkLoop (input : tree) (pos : 0 < input.«field:Count».toNat)
    (count : input.«field:Count».toNat ≤ 32) (n fuel : Nat)
    (remaining : n+fuel = input.«field:Count».toNat) (known : Vector UInt8 32) :
    checkTypes.«v15_loop» input (native input.«field:Count».toNat) fuel (native n, known) =
      some (inferTypes input fuel n known) := by
  induction fuel generalizing n known with
  | zero =>
    have atLast := counterValue (show input.«field:Count».toNat-1 ≤ 256 by omega)
    simp only [checkTypes.«v15_loop», inferTypes, subOne _ pos, atLast,
      Int.not_lt.mpr (Int.natCast_nonneg _), ite_false, Int.toNat_natCast]
    rw [read known (show input.«field:Count».toNat-1 < 32 by omega)]
    rfl
  | succ fuel ih =>
    have range : n < 32 := by omega
    have atN := counterValue (show n ≤ 256 by omega)
    have inferred := inferAgrees (input.«field:Kind».getD n 0)
      (input.«field:Left».getD n 0) (input.«field:Right».getD n 0) n range known
    let typ := nodeType (input.«field:Kind».getD n 0)
      (input.«field:Left».getD n 0).toNat (input.«field:Right».getD n 0).toNat n known
    simp only [checkTypes.«v15_loop», atN, Int.not_lt.mpr (Int.natCast_nonneg _),
      ite_false, Int.toNat_natCast, show (∀ x : Nat, signed (Int.ofNat x) = native x) from fun _ => rfl,
      show signed 1 = native 1 by rfl, counterAdd]
    rw [read input.«field:Kind» range, read input.«field:Left» range, read input.«field:Right» range]
    simp only [bind, Option.bind, show UInt8.ofNat 0 = (0 : UInt8) by rfl, inferred, inferTypes]
    by_cases valid : typ = 0
    · have failCond : nodeType (input.«field:Kind».getD n 0)
          (input.«field:Left».getD n 0).toNat (input.«field:Right».getD n 0).toNat n known = 0 := valid
      simp only [failCond, decide_true, ↓reduceIte]
      rw [read input.«field:Start» range]
      rfl
    · have next := ih (n+1) (by omega) (known.setIfInBounds n typ)
      have goodCond : nodeType (input.«field:Kind».getD n 0)
          (input.«field:Left».getD n 0).toNat (input.«field:Right».getD n 0).toNat n known ≠ 0 := valid
      simp only [goodCond, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [read known range]
      exact next

theorem checkTypesAgrees : TypeContract := by
  intro input
  have fits : input.«field:Count».toNat ≤ 256 := by have := input.«field:Count».toNat_lt; omega
  have atCount := counterValue fits
  have nativeZero : native input.«field:Count».toNat = signed 0 ↔ input.«field:Count».toNat = 0 := by
    have zero : signed 0 = native 0 := rfl
    rw [zero]
    constructor
    · intro h
      have eq := congrArg (fun i : GoTypes.Int => i.toInt) h
      rw [atCount, counterValue (show 0 ≤ 256 by decide)] at eq
      omega
    · intro h
      rw [h]
  have tooMany : native input.«field:Count».toNat > signed 32 ↔ 32 < input.«field:Count».toNat := by
    change signed 32 < native input.«field:Count».toNat ↔ _
    exact less (show 32 ≤ 256 by decide) fits
  simp only [checkTypes, typeResult, show ∀ x : Nat, signed (Int.ofNat x) = native x from fun _ => rfl,
    decide_eq_true_eq, nativeZero, tooMany]
  by_cases empty : input.«field:Count».toNat = 0
  · simp [empty, emptyTypes]
  by_cases large : 32 < input.«field:Count».toNat
  · simp [empty, large, emptyTypes]
  · have run := checkLoop input (by omega) (by omega) 0 input.«field:Count».toNat (by simp)
      (Vector.replicate 32 0)
    simp only [empty, large, false_or, decide_false, Bool.false_eq_true, ↓reduceIte,
      show signed 0 = native 0 by rfl, show UInt8.ofNat 0 = (0 : UInt8) by rfl,
      atCount, counterValue (show 0 ≤ 256 by decide), Int.ofNat_zero,
      Int.sub_zero, Int.toNat_natCast]
    exact run

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/bytecode_vm/compiler».compiler.TypeProof
