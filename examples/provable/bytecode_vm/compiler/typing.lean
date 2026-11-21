import bytecode_vm.compiler.layout
import bytecode_vm.compiler.pass_model

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/bytecode_vm/compiler».compiler.Typing

open Spec

set_option linter.unusedSimpArgs false

def lookup (known : List UInt8) (index : Nat) : UInt8 :=
  known[index]?.getD 0

def nodeType (node : Node) (known : List UInt8) : UInt8 :=
  if node.kind = 1 then 1
  else if node.kind = 2 then 2
  else
    let (operand, result) := PassModel.signature node.kind
    if node.left < known.length ∧ lookup known node.left = operand ∧
        (node.kind = 8 ∨ (node.right < known.length ∧ lookup known node.right = operand))
    then result else 0

def checkNodes : List Node → List UInt8 → Except Nat (List UInt8)
  | [], known => .ok known
  | node :: rest, known =>
    let ty := nodeType node known
    if ty = 0 then .error node.start else checkNodes rest (known ++ [ty])

private theorem checkAppend (left right : List Node) (known : List UInt8) :
    checkNodes (left ++ right) known = (checkNodes left known).bind (checkNodes right) := by
  induction left generalizing known with
  | nil => rfl
  | cons node rest ih =>
    simp only [List.cons_append, checkNodes]
    split <;> simp [Except.bind, ih]

private theorem typeAtRoot (expr : Expr) (known entries : List UInt8) (checked : expr.typeCheck = .ok (entries, ty)) :
    lookup (known ++ entries) (known.length + expr.nodeCount - 1) = ty := by
  have len := (expr.typeTableShape checked).1
  have last := (expr.typeTableShape checked).2
  have positive := expr.positive
  unfold lookup
  rw [List.getElem?_append_right (by omega)]
  have offset : known.length + expr.nodeCount - 1 - known.length = entries.length-1 := by omega
  simp [offset, last]

private theorem rootBeforeEnd (expr : Expr) (known entries : List UInt8)
    (checked : expr.typeCheck = .ok (entries, ty)) :
    known.length + expr.nodeCount - 1 < (known ++ entries).length := by
  rw [List.length_append, (expr.typeTableShape checked).1]
  have := expr.positive
  omega

theorem nodesAgree (expr : Expr) (known : List UInt8) :
    checkNodes (expr.nodesFrom known.length) known =
      expr.typeCheck.map (fun result => known ++ result.1) := by
  induction expr generalizing known with
  | number | boolean => rfl
  | unary start child ih =>
    simp only [Expr.nodesFrom, checkAppend, ih]
    cases verdict : child.typeCheck with
    | error e => simp [Expr.typeCheck, verdict, bind, Except.bind, Except.map]
    | ok result =>
      rcases result with ⟨entries, ty⟩
      have lookup := typeAtRoot child known entries verdict
      have within := rootBeforeEnd child known entries verdict
      simp only [List.length_append] at within
      by_cases valid : ty = 2 <;>
        simp [Expr.typeCheck, verdict, bind, Except.bind, pure, Except.pure, Except.map,
          checkNodes, nodeType, PassModel.signature, lookup, within, valid, List.append_assoc]
  | binary op start left right ihLeft ihRight =>
    simp only [Expr.nodesFrom, checkAppend, ihRight]
    cases r : right.typeCheck with
    | error e => simp [Expr.typeCheck, r, bind, Except.bind, Except.map]
    | ok rightResult =>
      rcases rightResult with ⟨rtypes, rty⟩
      have rshape := (right.typeTableShape r).1
      have that : (known ++ rtypes).length = known.length + right.nodeCount := by simp [rshape]
      simp only [r, Except.map, Except.bind, ← that, ihLeft]
      cases l : left.typeCheck with
      | error e => simp [Expr.typeCheck, r, l, bind, Except.bind, Except.map]
      | ok leftResult =>
        rcases leftResult with ⟨ltypes, lty⟩
        have lshape := (left.typeTableShape l).1
        have readL := typeAtRoot left (known ++ rtypes) ltypes l
        have withinL := rootBeforeEnd left (known ++ rtypes) ltypes l
        have withinR := rootBeforeEnd right known rtypes r
        have readR : lookup ((known ++ rtypes) ++ ltypes) ((known ++ rtypes).length - 1) = rty := by
          unfold lookup
          rw [List.getElem?_append_left (by have := right.positive; omega)]
          exact that ▸ typeAtRoot right known rtypes r
        have beforeEnd : (known ++ rtypes).length - 1 < ((known ++ rtypes) ++ ltypes).length := by
          simp only [List.length_append] at *
          omega
        simp only [List.append_assoc, List.length_append] at readL readR withinL beforeEnd
        by_cases lValid : lty = op.signature.1 <;>
          by_cases rValid : rty = op.signature.1 <;>
          cases op <;>
          simp only [BinaryOp.signature, Prod.fst] at lValid rValid <;>
          simp [Expr.typeCheck, r, l, bind, Except.bind, pure, Except.pure, Except.map,
            BinaryOp.kind, BinaryOp.signature, checkNodes, nodeType, PassModel.signature,
            readL, withinL, readR, beforeEnd, List.append_assoc, lValid, rValid]

def table (known : List UInt8) : Vector UInt8 32 :=
  Vector.ofFn (fun index => lookup known index.val)

private theorem tableRead (known : List UInt8) (index : Nat) (within : index < 32) :
    (table known).getD index 0 = lookup known index := by
  simp [table, Vector.getD, within]

private theorem tableExtend (known : List UInt8) (value : UInt8) :
    (table known).setIfInBounds known.length value = table (known ++ [value]) := by
  ext i bound
  rw [Vector.getElem_setIfInBounds bound]
  simp only [table, Vector.getElem_ofFn]
  by_cases same : i = known.length
  · simp [same, lookup]
  by_cases earlier : i < known.length
  · simp [same, Ne.symm same, lookup, List.getElem?_append_left earlier]
  · have absent : known.length < i := by omega
    have oldMissing : known[i]? = none := List.getElem?_eq_none (by omega)
    have newMissing : (known ++ [value])[i]? = none := List.getElem?_eq_none (by simp; omega)
    simp [same, Ne.symm same, lookup, oldMissing, newMissing]

private theorem nodeMatches (node : Node) (known : List UInt8) (room : known.length < 32) :
    PassModel.nodeType node.kind node.left node.right known.length (table known) = nodeType node known := by
  by_cases l : node.left < known.length <;> by_cases r : node.right < known.length
  · simp [PassModel.nodeType, nodeType, l, r, tableRead _ _ (show node.left < 32 by omega),
      tableRead _ _ (show node.right < 32 by omega)]
  · simp [PassModel.nodeType, nodeType, l, r, tableRead _ _ (show node.left < 32 by omega)]
  · simp [PassModel.nodeType, nodeType, l]
  · simp [PassModel.nodeType, nodeType, l]

def finish (count : Nat) : Except Nat (List UInt8) → types × Diagnostic
  | .ok entries => (⟨table entries, lookup entries (count-1)⟩, ⟨0, 0⟩)
  | .error offset => (PassModel.emptyTypes, ⟨5, UInt16.ofNat offset⟩)

private theorem inferMatches (input : tree) (nodes : List Node) (layout : HasNodes input nodes)
    (fits : nodes.length ≤ 32) (pos : 0 < nodes.length) (fuel : Nat) (known : List UInt8)
    (remaining : known.length + fuel = nodes.length) :
    PassModel.inferTypes input fuel known.length (table known) =
      finish nodes.length (checkNodes (nodes.drop known.length) known) := by
  induction fuel generalizing known with
  | zero =>
    have dropped : nodes.drop known.length = [] := List.drop_eq_nil_of_le (by omega)
    simp [PassModel.inferTypes, finish, checkNodes, dropped, layout.1,
      tableRead _ _ (show nodes.length-1 < 32 by omega)]
  | succ fuel ih =>
    have next : known.length < nodes.length := by omega
    have room : known.length < 32 := by omega
    let node := nodes[known.length]
    obtain ⟨kind, _value, offset, left, right⟩ := layout.2 known.length next
    rw [List.drop_eq_getElem_cons next]
    change _ = finish nodes.length (checkNodes (node :: nodes.drop (known.length+1)) known)
    have same := nodeMatches nodes[known.length] known room
    simp only [PassModel.inferTypes, kind, left, right, same, checkNodes, offset]
    by_cases rejected : nodeType node known = 0
    · simp [node] at rejected
      simp [rejected, finish, node]
    · let ty := nodeType node known
      have length : (known ++ [ty]).length = known.length+1 := by simp
      have run := ih (known ++ [ty]) (by simp; omega)
      rw [length, ← tableExtend] at run
      simp [node] at rejected
      simpa [rejected, ty, node] using run

theorem typeResultAgrees (input : tree) (expr : Expr) (layout : Layout input expr)
    (fits : expr.nodeCount ≤ 32) :
    PassModel.typeResult input =
      match expr.typeCheck with
      | .ok (entries, ty) => (⟨table entries, ty⟩, ⟨0, 0⟩)
      | .error offset => (PassModel.emptyTypes, ⟨5, UInt16.ofNat offset⟩) := by
  have count : input.«field:Count».toNat = expr.nodeCount := by simpa using layout.1
  have pos := expr.positive
  have len := expr.nodesLength 0
  have initial : table [] = Vector.replicate 32 0 := by
    ext i bound
    simp [table, lookup]
  have run := inferMatches input (expr.nodesFrom 0) layout (by omega) (by omega) expr.nodeCount []
    (by simp [len])
  have spec := nodesAgree expr []
  change checkNodes (expr.nodesFrom 0) [] = _ at spec
  simp only [List.length_nil, List.drop_zero, initial, len, spec] at run
  have nonempty : expr.nodeCount ≠ 0 := by omega
  have enough : ¬ 32 < expr.nodeCount := by omega
  simp only [PassModel.typeResult, count, nonempty, enough, or_self, ↓reduceIte]
  rw [run]
  cases checked : expr.typeCheck with
  | error offset => rfl
  | ok result =>
    rcases result with ⟨entries, ty⟩
    obtain ⟨len, atLast⟩ := expr.typeTableShape checked
    simp [finish, Except.map, lookup, ← len, atLast]

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/bytecode_vm/compiler».compiler.Typing
