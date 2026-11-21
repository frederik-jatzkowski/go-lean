import bytecode_vm.compiler.pass_model

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/bytecode_vm/compiler».compiler.EmitProof

open PassModel

set_option linter.unusedSimpArgs false

abbrev native (n : Nat) : GoTypes.Int := .ofNat n
abbrev signed (i : Int) : GoTypes.Int := .ofInt i

theorem counterValue {n : Nat} (h : n ≤ 256) :
    (native n).toInt = n := by
  change (signed (n : Int)).toInt = n
  first
  | exact Int64.toInt_ofInt_of_le (by omega) (by omega)
  | exact Int32.toInt_ofInt_of_le (by omega) (by omega)

theorem counterAdd (n m : Nat) :
    (native n) + (native m) = .ofNat (n + m) := by
  change signed (n : Int) + signed (m : Int) = signed ((n+m : Nat) : Int)
  first | rw [← Int64.ofInt_add] | rw [← Int32.ofInt_add]
  rfl

private theorem counterMul (n m : Nat) :
    (native n) * (native m) = .ofNat (n * m) := by
  change signed (n : Int) * signed (m : Int) = signed ((n*m : Nat) : Int)
  first | rw [← Int64.ofInt_mul] | rw [← Int32.ofInt_mul]
  rfl

theorem read {α : Type} [OfNat α 0] {size : Nat} (data : Vector α size)
    {index : Nat} (h : index < size) :
    data.toArray[index]? = some (data.getD index 0) := by
  rw [Array.getElem?_eq_getElem (by simpa using h)]
  simp [Vector.getD, h]

private theorem encodedWord (kind value : UInt8) : encode kind value = word kind value := by
  by_cases first : kind = 1 <;> by_cases second : kind = 2 <;> simp [encode, word, first, second]

private def Prefix (input : tree) (n : Nat) (buffer : Code) : Prop :=
  ∀ j : Fin 66, buffer[j] = if j.val / 2 < n then byteAt input j.val else 0

private theorem prefixPush (input : tree) (n : Nat) (buffer : Code)
    (within : n < input.«field:Count».toNat)
    (written : Prefix input n buffer) :
    let pair := word (input.«field:Kind».getD n 0) (input.«field:Value».getD n 0)
    Prefix input (n+1) ((buffer.setIfInBounds (2*n) pair.1).setIfInBounds (2*n+1) pair.2) := by
  intro pair j
  change ((buffer.setIfInBounds (2*n) pair.1).setIfInBounds (2*n+1) pair.2)[j.val] = _
  rw [Vector.getElem_setIfInBounds j.isLt, Vector.getElem_setIfInBounds j.isLt]
  by_cases odd : j.val = 2*n+1
  · simp [odd, byteAt, within, pair, show (2*n+1)/2 = n by omega,
      show (2*n+1)%2 ≠ 0 by omega]
  by_cases even : j.val = 2*n
  · simp [even, odd, byteAt, within, pair, show (2*n)/2 = n by omega]
  have same : j.val / 2 < n + 1 ↔ j.val / 2 < n := by omega
  simpa [odd, even, Ne.symm odd, Ne.symm even, same] using written j

private theorem emitLoop (input : tree) (count : input.«field:Count».toNat ≤ 32)
    (n fuel : Nat) (remaining : n + fuel = input.«field:Count».toNat)
    (buffer : Code) (written : Prefix input n buffer) :
    emit.«v9_loop» input (native input.«field:Count».toNat) fuel (native n, buffer) =
      some (code input, codeLength input) := by
  induction fuel generalizing n buffer with
  | zero =>
    have same : buffer = code input := by
      ext j hj
      have done : n = input.«field:Count».toNat := by omega
      have atIndex := written ⟨j, hj⟩
      by_cases h : j / 2 < n
      · simpa [code, h] using atIndex
      · have outside : ¬ j / 2 < input.«field:Count».toNat := by omega
        simpa [code, byteAt, h, outside] using atIndex
    rw [same]
    have length := counterValue (show 2 * (input.«field:Count».toNat + 1) ≤ 256 by omega)
    simp only [emit.«v9_loop», codeLength, show signed 1 = native 1 by rfl,
      show signed 2 = native 2 by rfl, counterAdd, counterMul, length,
      show ∀ k : Nat, (Int8.ofInt (k : Int)).toUInt8 = UInt8.ofNat k from fun _ => rfl,
      pure]
  | succ fuel ih =>
    have next : n < input.«field:Count».toNat := by omega
    have readIndex : n < 32 := by omega
    have doubleIndex : 2*n < 66 := by omega
    have oddIndex : 2*n+1 < 66 := by omega
    let pair := word (input.«field:Kind».getD n 0) (input.«field:Value».getD n 0)
    let updated := (buffer.setIfInBounds (2*n) pair.1).setIfInBounds (2*n+1) pair.2
    have nextWritten : Prefix input (n+1) updated := prefixPush input n buffer next written
    have atN := counterValue (show n ≤ 256 by omega)
    have atDouble := counterValue (show 2*n ≤ 256 by omega)
    have atOdd := counterValue (show 2*n+1 ≤ 256 by omega)
    simp only [emit.«v9_loop», show signed 1 = native 1 by rfl,
      show signed 2 = native 2 by rfl, counterAdd, counterMul, atN, atDouble, atOdd,
      Int.not_lt.mpr (Int.natCast_nonneg _), ite_false, Int.toNat_natCast,
      encodedWord]
    rw [read input.«field:Kind» readIndex, read input.«field:Value» readIndex,
      read buffer doubleIndex, read _ oddIndex]
    exact ih (n+1) (by omega) updated nextWritten

theorem emitAgrees : EmitContract := by
  intro input count
  have atCount := counterValue (show input.«field:Count».toNat ≤ 256 by omega)
  have guard : ¬ native input.«field:Count».toNat > signed 32 := by
    change ¬ signed 32 < native input.«field:Count».toNat
    first | rw [Int64.lt_iff_toInt_lt] | rw [Int32.lt_iff_toInt_lt]
    change ¬ (native 32).toInt < (native input.«field:Count».toNat).toInt
    rw [counterValue (by decide : 32 ≤ 256), atCount]
    omega
  have run := emitLoop input count 0 input.«field:Count».toNat (by omega)
    (Vector.replicate 66 0) (by intro j; simp)
  simpa only [emit, show ∀ x : Nat, signed (Int.ofNat x) = native x from fun _ => rfl,
    guard, decide_false, Bool.false_eq_true, ↓reduceIte,
    show signed 0 = native 0 by rfl,
    show UInt8.ofNat 0 = (0 : UInt8) by rfl,
    atCount, counterValue (show 0 ≤ 256 by decide), Int.ofNat_zero,
    Int.sub_zero, Int.toNat_natCast] using run

theorem emitTotalAgrees (input : tree) :
    emit input = some (if input.«field:Count».toNat ≤ 32 then (code input, codeLength input)
      else (Vector.replicate 66 0, 0)) := by
  by_cases bound : input.«field:Count».toNat ≤ 32
  · simpa only [ite_eq_left bound] using emitAgrees input bound
  · have fits : input.«field:Count».toNat ≤ 256 := by have := input.«field:Count».toNat_lt; omega
    have guard : signed (Int.ofNat input.«field:Count».toNat) > signed 32 := by
      change signed 32 < native input.«field:Count».toNat
      first | rw [Int64.lt_iff_toInt_lt] | rw [Int32.lt_iff_toInt_lt]
      change (native 32).toInt < (native input.«field:Count».toNat).toInt
      rw [counterValue (by decide : 32 ≤ 256), counterValue fits]
      omega
    simp only [emit, guard, decide_true, ↓reduceIte, bound]
    rfl

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/bytecode_vm/compiler».compiler.EmitProof
