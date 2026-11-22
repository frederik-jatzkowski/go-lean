import bytecode_vm.compiler.compiler_model

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/bytecode_vm/compiler».vm.VMModel

/-- Boolean observations have canonical byte encodings. -/
def boolByte (value : Bool) : UInt8 := if value then 1 else 0

/-- A binary instruction consumes the top byte as its left operand. -/
def binary (opcode left right : UInt8) : UInt8 :=
  if opcode = 2 then left + right
  else if opcode = 3 then left - right
  else if opcode = 4 then boolByte (decide (left = right))
  else if opcode = 5 then boolByte (decide (left < right))
  else boolByte (decide (left ≠ 0 ∧ right ≠ 0))

/-- The raw result includes the unused stack cells, which a step preserves except at its
    designated write index. Immediate bytes affect only push instructions. -/
def step (code : Vector UInt8 66) (state : State) : State × UInt8 :=
  let pc := state.«field:PC»
  let depth := state.«field:Depth»
  let stack := state.«field:Stack»
  let opcode := code.getD pc.toNat 0
  let advance (index : Nat) (value nextDepth : UInt8) :=
    (State.mk (pc + 2) (stack.setIfInBounds index value) nextDepth, (0 : UInt8))
  if pc ≥ 66 ∨ pc % 2 ≠ 0 then (state, 2)
  else if depth > 32 then (state, 3)
  else if opcode > 7 then (state, 4)
  else if opcode = 0 then (state, 1)
  else if pc = 64 then (state, 2)
  else if opcode = 1 then
    if depth = 32 then (state, 3)
    else advance depth.toNat (code.getD (pc.toNat + 1) 0) (depth + 1)
  else if opcode = 7 then
    if depth = 0 then (state, 3)
    else
      let top := depth.toNat - 1
      advance top (boolByte (decide (stack.getD top 0 = 0))) depth
  else
    if depth < 2 then (state, 3)
    else
      let top := depth.toNat - 1
      let below := depth.toNat - 2
      advance below (binary opcode (stack.getD top 0) (stack.getD below 0)) (depth - 1)

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/bytecode_vm/compiler».vm.VMModel
