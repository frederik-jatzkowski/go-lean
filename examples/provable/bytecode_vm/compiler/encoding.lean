import bytecode_vm.compiler.layout
import bytecode_vm.compiler.pass_model

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/bytecode_vm/compiler».compiler.Encoding

open Spec

private theorem nodeWordSize (node : Node) : node.word.length = 2 := by
  unfold Node.word
  split <;> rfl

private theorem nodeByteLength (nodes : List Node) :
    (nodes.flatMap Node.word).length = 2 * nodes.length := by
  induction nodes with
  | nil => rfl
  | cons node tail ih => simp [nodeWordSize, ih]; omega

private theorem flatByte (nodes : List Node) (i : Nat) :
    (nodes.flatMap Node.word)[i]?.getD 0 =
      ((nodes[i / 2]?).map (fun node => node.word[i % 2]?.getD 0)).getD 0 := by
  induction nodes generalizing i with
  | nil => simp
  | cons node tail ih =>
    simp only [List.flatMap_cons]
    by_cases first : i < 2
    · have quotient : i / 2 = 0 := by omega
      rw [List.getElem?_append_left (by rw [nodeWordSize]; exact first), quotient,
        Nat.mod_eq_of_lt first]
      rfl
    · have rest : 2 ≤ i := by omega
      have quotient : i / 2 = (i - 2) / 2 + 1 := by omega
      have remainder : (i - 2) % 2 = i % 2 := by omega
      rw [List.getElem?_append_right (by rw [nodeWordSize]; exact rest),
        nodeWordSize, ih, quotient, remainder, List.getElem?_cons_succ]

/-- The bytecode buffer pads a sequence of instructions with zero bytes. -/
def packed (instructions : List Instruction) : Vector UInt8 66 :=
  Vector.ofFn (fun i : Fin 66 => (instructions.flatMap Instruction.encode)[i.val]?.getD 0)

theorem bytesMatch (arena : tree) (expr : Expr) (layout : Layout arena expr) :
    PassModel.code arena = packed (expr.code ++ [.halt]) := by
  apply Vector.ext
  intro i hi
  simp only [PassModel.code, packed, Vector.getElem_ofFn]
  have flatten := expr.words 0
  simp only [List.flatMap_append, ← flatten, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, Instruction.encode]
  let nodes := expr.nodesFrom 0
  have count : arena.«field:Count».toNat = nodes.length := layout.1
  by_cases onNode : i / 2 < nodes.length
  · have inBytes : i < (nodes.flatMap Node.word).length := by rw [nodeByteLength]; omega
    rw [List.getElem?_append_left inBytes, flatByte,
      List.getElem?_eq_getElem onNode]
    have fields := layout.2 (i / 2) onNode
    have within : i / 2 < arena.«field:Count».toNat := count.symm ▸ onNode
    simp only [Option.map_some, Option.getD_some, PassModel.byteAt, within, ite_true,
      fields.1, fields.2.1]
    have modulo : i % 2 = 0 ∨ i % 2 = 1 := by omega
    rcases modulo with zero | one
    · simp [zero, Node.word, PassModel.word]
      split <;> rfl
    · simp [one, Node.word, PassModel.word]
      split <;> rfl
  · have outOfBytes : (nodes.flatMap Node.word).length ≤ i := by rw [nodeByteLength]; omega
    rw [List.getElem?_append_right outOfBytes]
    have outside : ¬ i / 2 < arena.«field:Count».toNat := by omega
    simp only [PassModel.byteAt, outside, ite_false]
    generalize i - (nodes.flatMap Node.word).length = byte
    rcases byte with _ | ⟨_ | _⟩ <;> rfl

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/bytecode_vm/compiler».compiler.Encoding
