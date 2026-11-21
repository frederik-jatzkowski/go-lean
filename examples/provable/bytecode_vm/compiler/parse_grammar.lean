import bytecode_vm.compiler.compiler_spec
import bytecode_vm.compiler.lexer_spec

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/bytecode_vm/compiler».compiler.Grammar

open Spec
open LexerSpec (Token)

inductive Form where
  | integer (value : UInt8)
  | boolean (value : Bool)
  | unary
  | binary (op : BinaryOp)
  deriving DecidableEq

def binaryKind : BinaryOp → UInt8
  | .add => 3
  | .sub => 4
  | .eq => 5
  | .lt => 6
  | .and => 7

def token (position : Nat) : Form → Token
  | .integer value => ⟨1, value, position⟩
  | .boolean value => ⟨2, (Value.boolean value).encode, position⟩
  | .unary => ⟨8, 0, position⟩
  | .binary op => ⟨binaryKind op, 0, position⟩

def form (t : Token) : Option Form :=
  if t.kind = 1 then some (.integer t.value)
  else if t.kind = 2 then
    if t.value = 0 then some (.boolean false)
    else if t.value = 1 then some (.boolean true) else none
  else if t.value ≠ 0 then none
  else if t.kind = 8 then some .unary
  else if t.kind = 3 then some (.binary .add)
  else if t.kind = 4 then some (.binary .sub)
  else if t.kind = 5 then some (.binary .eq)
  else if t.kind = 6 then some (.binary .lt)
  else if t.kind = 7 then some (.binary .and)
  else none

@[simp] theorem form_token (position : Nat) (f : Form) :
    form (token position f) = some f := by
  cases f with
  | integer => rfl
  | boolean value => cases value <;> rfl
  | unary => rfl
  | binary op => cases op <;> rfl

@[simp] theorem token_start (position : Nat) (f : Form) : (token position f).start = position := by
  cases f <;> rfl

theorem token_of_form {t : Token} {f : Form} (h : form t = some f) :
    token t.start f = t := by
  rcases t with ⟨kind, value, position⟩
  simp only [form] at h
  repeat' split at h
  all_goals first | contradiction | (cases h; simp_all [token, binaryKind, Value.encode])

/-- The prefix grammar as its token encoding, with original positions at every node. -/
def prefixTokens : Expr → List Token
  | .number value position => [token position (.integer value)]
  | .boolean value position => [token position (.boolean value)]
  | .unary position expr => token position .unary :: prefixTokens expr
  | .binary op position left right =>
    token position (.binary op) :: (prefixTokens left ++ prefixTokens right)

def pushTree (t : Token) (trees : List Expr) : Option (List Expr) :=
  match form t, trees with
  | some (.integer value), _ => some (.number value t.start :: trees)
  | some (.boolean value), _ => some (.boolean value t.start :: trees)
  | some .unary, expr :: rest => some (.unary t.start expr :: rest)
  | some (.binary op), left :: right :: rest => some (.binary op t.start left right :: rest)
  | _, _ => none

theorem pushesTokens (t : Token) (before after : List Expr)
    (step : pushTree t before = some after) :
    after.flatMap prefixTokens = t :: before.flatMap prefixTokens := by
  cases h : form t with
  | none => simp [pushTree, h] at step
  | some f =>
    have canonical := token_of_form h
    cases f with
    | integer value =>
      simp only [pushTree, h, Option.some.injEq] at step
      subst after
      simp [prefixTokens, canonical]
    | boolean value =>
      simp only [pushTree, h, Option.some.injEq] at step
      subst after
      simp [prefixTokens, canonical]
    | unary =>
      cases before with
      | nil => simp [pushTree, h] at step
      | cons expr rest =>
        simp only [pushTree, h, Option.some.injEq] at step
        subst after
        simp [prefixTokens, canonical]
    | binary op =>
      rcases before with _ | ⟨left, _ | ⟨right, rest⟩⟩
      · simp [pushTree, h] at step
      · simp [pushTree, h] at step
      · simp only [pushTree, h, Option.some.injEq] at step
        subst after
        simp [prefixTokens, canonical, List.append_assoc]

/-- Scan from right to left, reducing each token and its operands to one tree. -/
def parseForest : List Token → Option (List Expr)
  | [] => some []
  | head :: tail => (parseForest tail).bind (pushTree head)

def parse (tokens : List Token) : Option Expr :=
  match parseForest tokens with
  | some [expr] => some expr
  | _ => none

theorem forestSound {tokens : List Token} {forest : List Expr}
    (parsed : parseForest tokens = some forest) :
    forest.flatMap prefixTokens = tokens := by
  induction tokens generalizing forest with
  | nil => simp [parseForest] at parsed; subst forest; rfl
  | cons head tail ih =>
    cases tailResult : parseForest tail with
    | none => simp [parseForest, tailResult] at parsed
    | some trees =>
      have step : pushTree head trees = some forest := by
        simpa [parseForest, tailResult] using parsed
      rw [pushesTokens _ _ _ step, ih tailResult]

theorem parsePrefix (expr : Expr) (tail : List Token) :
    parseForest (prefixTokens expr ++ tail) =
      (parseForest tail).map (expr :: ·) := by
  induction expr generalizing tail with
  | number value position =>
    cases h : parseForest tail <;> simp [prefixTokens, parseForest, h, pushTree]
  | boolean value position =>
    cases h : parseForest tail <;> simp [prefixTokens, parseForest, h, pushTree]
  | unary position expr ih =>
    rw [prefixTokens, List.cons_append, parseForest, ih]
    cases parseForest tail <;> simp [pushTree]
  | binary op position left right leftIH rightIH =>
    rw [prefixTokens, List.cons_append, parseForest, List.append_assoc, leftIH, rightIH]
    cases parseForest tail <;> simp [pushTree]

theorem parsesExactly (tokens : List Token) (expr : Expr) :
    parse tokens = some expr ↔ prefixTokens expr = tokens := by
  constructor
  · intro parsed
    unfold parse at parsed
    split at parsed
    · rename_i found h
      cases parsed
      simpa using forestSound h
    · contradiction
  · intro encoded
    rw [← encoded]
    have word := parsePrefix expr []
    simp only [List.append_nil, parseForest, Option.map_some] at word
    simp [parse, word]

def instructionOf (t : Token) : Instruction :=
  match form t with
  | some (.integer value) => .push value
  | some (.boolean value) => .push (Value.boolean value).encode
  | some .unary => .not
  | some (.binary op) => op.instruction
  | none => .halt

theorem codeFromPrefix (expr : Expr) :
    (prefixTokens expr).reverse.map instructionOf = expr.code := by
  induction expr <;> simp [prefixTokens, Expr.code, instructionOf, List.reverse_append, List.append_assoc, *]

def Canonical (sourceLength : Nat) (out : List Token) : Prop :=
  ∀ t ∈ out, form t ≠ none ∧ t.start ≤ sourceLength

private theorem wordForm (bytes : List UInt8) (position : Nat)
    (valid : (LexerSpec.word bytes).1 ≠ 0) :
    form ⟨(LexerSpec.word bytes).1, (LexerSpec.word bytes).2, position⟩ ≠ none := by
  rcases bytes with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, rest⟩⟩⟩⟩⟩⟩
  all_goals simp only [LexerSpec.word] at valid ⊢
  all_goals repeat' first | contradiction | split at valid
  all_goals repeat' first | contradiction | split
  all_goals simp_all [form]

private theorem finishCanonical (source : List UInt8) (start width : Nat) (prior out : List Token)
    (before : Canonical source.length prior) (position : start ≤ source.length)
    (result : LexerSpec.finish source start width prior = .ok out) :
    Canonical source.length out := by
  unfold LexerSpec.finish at result
  split at result
  · cases result
    exact before
  · dsimp at result
    split at result
    · contradiction
    · rename_i valid
      split at result
      · contradiction
      · cases result
        intro t member
        rcases List.mem_append.mp member with earlier | current
        · exact before t earlier
        · simp only [List.mem_singleton] at current
          subst t
          exact ⟨wordForm _ _ valid, position⟩

private theorem scanCanonical (source remaining : List UInt8) (i start width : Nat)
    (prior out : List Token) (before : Canonical source.length prior)
    (position : start ≤ i) (fits : i + remaining.length ≤ source.length)
    (result : LexerSpec.scan source remaining i start width prior = .ok out) :
    Canonical source.length out := by
  induction remaining generalizing i start width prior with
  | nil =>
    exact finishCanonical source start width prior out before (by simp at fits; omega) result
  | cons b rest ih =>
    simp only [LexerSpec.scan] at result
    split at result
    · cases finalized : LexerSpec.finish source start width prior with
      | error err => simp [finalized, Except.bind] at result
      | ok next =>
        have valid := finishCanonical source start width prior next before (by omega) finalized
        simp only [finalized, Except.bind] at result
        exact ih (i+1) start 0 next valid (by omega) (by simp at fits; omega) result
    · have nextStart : (if width = 0 then i else start) ≤ i + 1 := by split <;> omega
      exact ih (i+1) _ (width+1) prior before nextStart (by simp at fits; omega) result

theorem lexCanonical (source : List UInt8) (out : List Token)
    (result : LexerSpec.lex source = .ok out) :
    source.length ≤ 256 ∧ Canonical source.length out := by
  unfold LexerSpec.lex at result
  split at result
  · contradiction
  · exact ⟨by omega, scanCanonical source source 0 0 0 [] out (by simp [Canonical])
      (by decide) (by simp) result⟩

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/bytecode_vm/compiler».compiler.Grammar
