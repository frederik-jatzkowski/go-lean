import bytecode_vm.compiler.compiler_gen
import bytecode_vm.compiler.compiler_spec

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/bytecode_vm/compiler».compiler.PassModel

abbrev Code := Vector UInt8 66

def word (kind value : UInt8) : UInt8 × UInt8 :=
  if kind = 1 ∨ kind = 2 then (1, value) else (kind - 3 + 2, 0)

def byteAt (input : tree) (index : Nat) : UInt8 :=
  if index / 2 < input.«field:Count».toNat then
    let pair := word (input.«field:Kind».getD (index / 2) 0)
      (input.«field:Value».getD (index / 2) 0)
    if index % 2 = 0 then pair.1 else pair.2
  else 0

def code (input : tree) : Code :=
  Vector.ofFn (fun index => byteAt input index.val)

def codeLength (input : tree) : UInt8 :=
  UInt8.ofNat (2 * (input.«field:Count».toNat + 1))

def EmitContract : Prop :=
  ∀ input : tree, input.«field:Count».toNat ≤ 32 →
    emit input = some (code input, codeLength input)

def signature (kind : UInt8) : UInt8 × UInt8 :=
  if kind = 3 ∨ kind = 4 then (1, 1)
  else if kind = 5 ∨ kind = 6 then (1, 2)
  else (2, 2)

def nodeType (kind : UInt8) (left right index : Nat)
    (known : Vector UInt8 32) : UInt8 :=
  if kind = 1 then 1
  else if kind = 2 then 2
  else
    let (operand, result) := signature kind
    if left < index ∧ known.getD left 0 = operand ∧
        (kind = 8 ∨ (right < index ∧ known.getD right 0 = operand)) then result else 0

def emptyTypes : types := ⟨Vector.replicate 32 0, 0⟩

def inferTypes (input : tree) : Nat → Nat → Vector UInt8 32 → types × Diagnostic
  | 0, _, known => (⟨known, known.getD (input.«field:Count».toNat-1) 0⟩, ⟨0, 0⟩)
  | fuel+1, index, known =>
    let kind := input.«field:Kind».getD index 0
    let left := input.«field:Left».getD index 0
    let right := input.«field:Right».getD index 0
    let inferred := nodeType kind left.toNat right.toNat index known
    if inferred = 0 then (emptyTypes, ⟨5, input.«field:Start».getD index 0⟩)
    else inferTypes input fuel (index+1) (known.setIfInBounds index inferred)

def typeResult (input : tree) : types × Diagnostic :=
  let count := input.«field:Count».toNat
  if count = 0 ∨ 32 < count then (emptyTypes, ⟨5, 0⟩)
  else inferTypes input count 0 (Vector.replicate 32 0)

def TypeContract : Prop :=
  ∀ input : tree, checkTypes input = some (typeResult input)

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/bytecode_vm/compiler».compiler.PassModel
