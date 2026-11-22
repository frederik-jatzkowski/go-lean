import bytecode_vm.compiler.compiler_gen
import bytecode_vm.compiler.compiler_spec

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/bytecode_vm/compiler».compiler

namespace Spec

structure Node where
  kind : UInt8
  value : UInt8
  start : Nat
  left : Nat
  right : Nat
  deriving DecidableEq

def BinaryOp.kind : BinaryOp → UInt8
  | .add => 3
  | .sub => 4
  | .eq => 5
  | .lt => 6
  | .and => 7

def Expr.nodesFrom : Expr → Nat → List Node
  | .number value start, _ => [⟨1, value, start, 0, 0⟩]
  | .boolean value start, _ => [⟨2, (Value.boolean value).encode, start, 0, 0⟩]
  | .unary start child, first =>
    child.nodesFrom first ++ [⟨8, 0, start, first + child.nodeCount - 1, 0⟩]
  | .binary op start left right, first =>
    let second := first + right.nodeCount
    right.nodesFrom first ++ left.nodesFrom second ++
      [⟨op.kind, 0, start, second + left.nodeCount - 1, second - 1⟩]

@[simp] theorem Expr.nodesLength (expr : Expr) (first : Nat) :
    (expr.nodesFrom first).length = expr.nodeCount := by
  induction expr generalizing first <;> simp [Expr.nodesFrom, Expr.nodeCount, Nat.add_assoc, *]

theorem Expr.positive (expr : Expr) : 0 < expr.nodeCount := by
  cases expr <;> simp [Expr.nodeCount]

theorem Expr.childBounds (expr : Expr) (first : Nat) (node : Node)
    (belongs : node ∈ expr.nodesFrom first) :
    node.left < first + expr.nodeCount ∧ node.right < first + expr.nodeCount := by
  induction expr generalizing first with
  | number | boolean =>
    simp [Expr.nodesFrom] at belongs
    subst node
    simp [Expr.nodeCount]
  | unary position child ih =>
    simp only [Expr.nodesFrom, List.mem_append, List.mem_singleton] at belongs
    rcases belongs with lower | root
    · have := ih first lower
      simp [Expr.nodeCount]
      omega
    · subst node
      simp [Expr.nodeCount]
      omega
  | binary op position left right ihLeft ihRight =>
    simp only [Expr.nodesFrom, List.mem_append, List.mem_singleton] at belongs
    rcases belongs with (r | l) | root
    · have := ihRight first r
      simp [Expr.nodeCount]
      omega
    · have := ihLeft (first + right.nodeCount) l
      simp [Expr.nodeCount]
      omega
    · subst node
      simp [Expr.nodeCount]
      omega

def Node.word (node : Node) : List UInt8 :=
  if node.kind = 1 ∨ node.kind = 2 then [1, node.value] else [node.kind - 3 + 2, 0]

theorem Expr.words (expr : Expr) (first : Nat) :
    (expr.nodesFrom first).flatMap Node.word = expr.code.flatMap Instruction.encode := by
  induction expr generalizing first with
  | number | boolean => simp [Expr.nodesFrom, Expr.code, Node.word, Instruction.encode]
  | unary start child ih =>
    simp [Expr.nodesFrom, Expr.code, Node.word, Instruction.encode, ih]
  | binary op start left right ihLeft ihRight =>
    simp [Expr.nodesFrom, Expr.code, ihLeft, ihRight]
    cases op <;> simp [Node.word, BinaryOp.kind, BinaryOp.instruction, Instruction.encode]

end Spec

def HasNodes (arena : tree) (nodes : List Spec.Node) : Prop :=
  arena.«field:Count».toNat = nodes.length ∧
    ∀ i (valid : i < nodes.length),
      let node := nodes[i]
      arena.«field:Kind».getD i 0 = node.kind ∧
      arena.«field:Value».getD i 0 = node.value ∧
      arena.«field:Start».getD i 0 = UInt16.ofNat node.start ∧
      (arena.«field:Left».getD i 0).toNat = node.left ∧
      (arena.«field:Right».getD i 0).toNat = node.right

def Layout (arena : tree) (expr : Spec.Expr) : Prop :=
  HasNodes arena (expr.nodesFrom 0)

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/bytecode_vm/compiler».compiler
