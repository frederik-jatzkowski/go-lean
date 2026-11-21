import bytecode_vm.compiler.compiler_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/bytecode_vm/compiler».compiler.Parser

structure Arena where
  kinds : Vector UInt8 32 := Vector.replicate 32 0
  values : Vector UInt8 32 := Vector.replicate 32 0
  offsets : Vector UInt16 32 := Vector.replicate 32 0
  left : Vector UInt8 32 := Vector.replicate 32 0
  right : Vector UInt8 32 := Vector.replicate 32 0
  roots : Vector UInt8 32 := Vector.replicate 32 0

def operandCount (kind : UInt8) : Nat :=
  if kind = 1 ∨ kind = 2 then 0 else if kind = 8 then 1 else 2

def syntaxError (input : tokens) : tree × Diagnostic :=
  (⟨Vector.replicate 32 0, Vector.replicate 32 0, Vector.replicate 32 0,
    Vector.replicate 32 0, Vector.replicate 32 0, 0⟩, ⟨4, input.«field:End»⟩)

def insert (input : tokens) (index reversed depth operands : Nat) (arena : Arena) : Arena where
  kinds := arena.kinds.setIfInBounds index (input.«field:Kind».getD reversed 0)
  values := arena.values.setIfInBounds index (input.«field:Value».getD reversed 0)
  offsets := arena.offsets.setIfInBounds index (input.«field:Start».getD reversed 0)
  left := if operands = 0 then arena.left
    else arena.left.setIfInBounds index (arena.roots.getD (depth - 1) 0)
  right := if operands = 2 then arena.right.setIfInBounds index (arena.roots.getD (depth - 2) 0)
    else arena.right
  roots := arena.roots.setIfInBounds (depth - operands) (UInt8.ofNat index)

def parseRemaining (input : tokens) : Nat → Nat → Nat → Arena → tree × Diagnostic
  | 0, _, depth, arena =>
    if depth = 1 then
      (⟨arena.kinds, arena.values, arena.offsets, arena.left, arena.right, input.«field:Count»⟩, ⟨0, 0⟩)
    else syntaxError input
  | remaining + 1, index, depth, arena =>
    let operands := operandCount (input.«field:Kind».getD remaining 0)
    if depth < operands then syntaxError input
    else parseRemaining input remaining (index + 1) (depth - operands + 1)
      (insert input index remaining depth operands arena)

def reference (input : tokens) : tree × Diagnostic :=
  if input.«field:Count».toNat > 32 then syntaxError input
  else parseRemaining input input.«field:Count».toNat 0 0 {}

def Contract : Prop := ∀ input, parse input = some (reference input)

private abbrev native (n : Nat) : GoTypes.Int := .ofInt (Int.ofNat n)

private theorem counterValue {n : Nat} (h : n ≤ 256) : (native n).toInt = n := by
  change ((.ofInt (n : Int)) : GoTypes.Int).toInt = n
  first
  | exact Int64.toInt_ofInt_of_le (by omega) (by omega)
  | exact Int32.toInt_ofInt_of_le (by omega) (by omega)

private theorem counterAdd (n m : Nat) :
    native n + native m = native (n + m) := by
  unfold native
  first | rw [← Int64.ofInt_add] | rw [← Int32.ofInt_add]
  rfl

private theorem counterSub (n m : Nat) (h : m ≤ n) :
    native n - native m = native (n - m) := by
  unfold native
  first | rw [← Int64.ofInt_sub] | rw [← Int32.ofInt_sub]
  exact congrArg (fun x : Int => (.ofInt x : GoTypes.Int)) (Int.ofNat_sub h).symm

private theorem counterLt (n m : Nat) (hn : n ≤ 256) (hm : m ≤ 256) :
    native n < native m ↔ n < m := by
  first | rw [Int64.lt_iff_toInt_lt] | rw [Int32.lt_iff_toInt_lt]
  rw [counterValue hn, counterValue hm]
  omega

private theorem counterEq (n m : Nat) (hn : n ≤ 256) (hm : m ≤ 256) :
    native n = native m ↔ n = m := by
  constructor
  · intro same
    have values := congrArg (fun x : GoTypes.Int => x.toInt) same
    rw [counterValue hn, counterValue hm] at values
    omega
  · exact congrArg native

private theorem read [OfNat α 0] {size : Nat} (data : Vector α size) {index : Nat}
    (h : index < size) : data.toArray[index]? = some (data.getD index 0) := by
  rw [Array.getElem?_eq_getElem (by simpa using h)]
  simp [Vector.getD, h]

private theorem arityMatches (kind : UInt8) : arity kind = native (operandCount kind) := by
  by_cases first : kind = 1 <;> by_cases second : kind = 2 <;> by_cases last : kind = 8 <;>
    simp [arity, operandCount, first, second, last] <;> rfl

private theorem atIndex {n : Nat} (bound : n ≤ 256) : (native n).toInt.toNat = n := by
  rw [counterValue bound, Int.toNat_natCast]

private theorem notNegative {n : Nat} (bound : n ≤ 256) : ¬ (native n).toInt < 0 := by
  rw [counterValue bound]
  exact Int.not_lt.mpr (Int.natCast_nonneg n)

private theorem castIndex {n : Nat} (bound : n ≤ 256) :
    (Int8.ofInt (native n).toInt).toUInt8 = UInt8.ofNat n := by
  rw [counterValue bound]
  exact Int8.toUInt8_ofNat'

set_option maxHeartbeats 600000 in
private theorem mainLoop (input : tokens) (count : input.«field:Count».toNat ≤ 32)
    (fuel i depth : Nat) (progress : i + fuel = input.«field:Count».toNat) (room : depth ≤ i)
    (arena : Arena) :
    parse.«v15_loop» input (native input.«field:Count».toNat) fuel
        (native depth, native i, arena.kinds, arena.values, arena.offsets, arena.left, arena.right, arena.roots) =
      some (parseRemaining input fuel i depth arena) := by
  induction fuel generalizing i depth arena with
  | zero =>
    have one := counterEq depth 1 (by omega) (by decide)
    change native depth = (.ofInt 1 : GoTypes.Int) ↔ depth = 1 at one
    simp only [parse.«v15_loop», parseRemaining, syntaxError,
      ne_eq, one]
    by_cases done : depth = 1 <;> simp [done]
  | succ fuel ih =>
    have inside : i < 32 := by omega
    have reverseInside : fuel < 32 := by omega
    have reverse : input.«field:Count».toNat - 1 - i = fuel := by omega
    have countPositive : 1 ≤ input.«field:Count».toNat := by omega
    let kind := input.«field:Kind».getD fuel 0
    let operands := operandCount kind
    have small : operands ≤ 2 := by
      by_cases leaf : kind = 1 ∨ kind = 2 <;> by_cases unary : kind = 8 <;>
        simp [operands, operandCount, leaf, unary]
    have carried (safe : operands ≤ depth) :
        parse.«v15_loop» input (native input.«field:Count».toNat) fuel
          (native (depth - operands + 1), native (i + 1),
            (insert input i fuel depth operands arena).kinds, (insert input i fuel depth operands arena).values,
            (insert input i fuel depth operands arena).offsets, (insert input i fuel depth operands arena).left,
            (insert input i fuel depth operands arena).right, (insert input i fuel depth operands arena).roots) =
          some (parseRemaining input fuel (i+1) (depth-operands+1) (insert input i fuel depth operands arena)) :=
      ih (i+1) (depth-operands+1) (by omega) (by omega) _
    have reverseNative : (native input.«field:Count».toNat - .ofInt 1) - native i = native fuel := by
      change (native input.«field:Count».toNat - native 1) - native i = native fuel
      rw [counterSub _ _ countPositive, counterSub _ _ (by omega), reverse]
    have condition : (native depth < native (operandCount (input.«field:Kind».getD fuel 0))) ↔
        depth < operands := counterLt depth operands (by omega) (by omega)
    simp only [parse.«v15_loop», parseRemaining, reverseNative,
      notNegative (show fuel ≤ 256 by omega), atIndex (show fuel ≤ 256 by omega), ↓reduceIte,
      show UInt8.ofNat 0 = (0 : UInt8) by rfl, show UInt16.ofNat 0 = (0 : UInt16) by rfl,
      read input.«field:Kind» reverseInside, bind, Option.bind, arityMatches, decide_eq_true_eq, condition]
    by_cases underflow : depth < operands
    · have specUnderflow : depth < operandCount (input.«field:Kind».getD fuel 0) := underflow
      simp only [underflow, specUnderflow, ↓reduceIte, syntaxError, Option.pure_def]
      rfl
    have safe : operands ≤ depth := by omega
    have options : operands = 0 ∨ operands = 1 ∨ operands = 2 := by omega
    have found := carried safe
    rcases options with none | one | two
    · have ar : operandCount (input.«field:Kind».getD fuel 0) = 0 := none
      simp only [underflow, ar, ↓reduceIte, Nat.not_lt_zero, show ¬ (native 0 ≥ (.ofInt 1 : GoTypes.Int)) by decide]
      simpa only [none, Nat.sub_zero, insert, ↓reduceIte, show ¬ (0 : Nat) = 2 by decide,
        show ¬ native 0 = (.ofInt 2 : GoTypes.Int) by decide,
        notNegative (show i ≤ 256 by omega), notNegative (show depth ≤ 256 by omega),
        atIndex (show i ≤ 256 by omega), atIndex (show depth ≤ 256 by omega),
        read arena.kinds inside, read arena.values inside, read arena.offsets inside,
        read input.«field:Value» reverseInside, read input.«field:Start» reverseInside,
        read arena.roots (show depth < 32 by omega), castIndex (show i ≤ 256 by omega),
        show (.ofInt 1 : GoTypes.Int) = native 1 by rfl, counterAdd] using found
    · have ar : operandCount (input.«field:Kind».getD fuel 0) = 1 := one
      have noUnderflow : ¬ depth < 1 := by omega
      simp only [underflow, ar, noUnderflow, ↓reduceIte,
        show native 1 ≥ (.ofInt 1 : GoTypes.Int) by decide,
        show ¬ native 1 = (.ofInt 2 : GoTypes.Int) by decide]
      simpa only [one, insert, ↓reduceIte, show ¬ (1 : Nat) = 0 by decide,
        show ¬ (1 : Nat) = 2 by decide, show (.ofInt 1 : GoTypes.Int) = native 1 by rfl,
        counterSub depth 1 (by omega), notNegative (show i ≤ 256 by omega),
        notNegative (show depth - 1 ≤ 256 by omega), atIndex (show i ≤ 256 by omega),
        atIndex (show depth - 1 ≤ 256 by omega), read arena.left inside, read arena.kinds inside,
        read arena.values inside, read arena.offsets inside,
        read input.«field:Value» reverseInside, read input.«field:Start» reverseInside,
        read arena.roots (show depth - 1 < 32 by omega),
        castIndex (show i ≤ 256 by omega), counterAdd] using found
    · have ar : operandCount (input.«field:Kind».getD fuel 0) = 2 := two
      have noUnderflow : ¬ depth < 2 := by omega
      simp only [underflow, ar, noUnderflow, ↓reduceIte,
        show native 2 = (.ofInt 2 : GoTypes.Int) by rfl]
      have sub2 : native (depth - 1) - native 1 = native (depth - 2) := by
        rw [counterSub _ _ (by omega), show depth - 1 - 1 = depth - 2 by omega]
      simpa only [two, insert, ↓reduceIte, show ¬ (2 : Nat) = 0 by decide,
        show (.ofInt 2 : GoTypes.Int) ≥ native 1 by decide,
        show (.ofInt 1 : GoTypes.Int) = native 1 by rfl,
        counterSub depth 1 (by omega), sub2, notNegative (show i ≤ 256 by omega),
        notNegative (show depth - 1 ≤ 256 by omega), notNegative (show depth - 2 ≤ 256 by omega),
        atIndex (show i ≤ 256 by omega), atIndex (show depth - 1 ≤ 256 by omega),
        atIndex (show depth - 2 ≤ 256 by omega), read arena.left inside, read arena.right inside,
        read arena.kinds inside, read arena.values inside, read arena.offsets inside,
        read input.«field:Value» reverseInside, read input.«field:Start» reverseInside,
        read arena.roots (show depth - 1 < 32 by omega), read arena.roots (show depth - 2 < 32 by omega),
        castIndex (show i ≤ 256 by omega), counterAdd] using found

theorem agrees : Contract := by
  intro input
  have byteBound := input.«field:Count».toNat_lt
  have guard := counterLt 32 input.«field:Count».toNat (by decide) (by omega)
  change (.ofInt 32 : GoTypes.Int) < (.ofInt (Int.ofNat input.«field:Count».toNat)) ↔ _ at guard
  by_cases over : 32 < input.«field:Count».toNat
  · simp only [parse, reference, GT.gt, guard, over, decide_true, ↓reduceIte, syntaxError]
    rfl
  · have count : input.«field:Count».toNat ≤ 32 := by omega
    have loop := mainLoop input count input.«field:Count».toNat 0 0 (by omega) (by omega) {}
    simp only [parse, reference, GT.gt, guard, over, decide_false, Bool.false_eq_true, ↓reduceIte,
      show (.ofInt (Int.ofNat input.«field:Count».toNat) : GoTypes.Int) = native input.«field:Count».toNat by rfl,
      counterValue (show input.«field:Count».toNat ≤ 256 by omega), show ((.ofInt 0 : GoTypes.Int)).toInt = 0 by decide,
      Int.sub_zero, Int.toNat_natCast]
    exact loop

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/bytecode_vm/compiler».compiler.Parser
