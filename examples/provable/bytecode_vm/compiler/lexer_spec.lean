import bytecode_vm.compiler.compiler_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/bytecode_vm/compiler».compiler

namespace LexerSpec

structure Token where
  kind : UInt8
  value : UInt8
  start : Nat
  deriving DecidableEq

abbrev Result := Except (UInt8 × Nat) (List Token)

def space (b : UInt8) : Prop :=
  b = 32 ∨ b = 9 ∨ b = 13 ∨ b = 10

instance (b : UInt8) : Decidable (space b) := inferInstanceAs
  (Decidable (b = 32 ∨ b = 9 ∨ b = 13 ∨ b = 10))

def digit (b : UInt8) : Prop := 48 ≤ b ∧ b ≤ 57

instance (b : UInt8) : Decidable (digit b) := inferInstanceAs (Decidable (48 ≤ b ∧ b ≤ 57))

def digitValue (b : UInt8) : UInt16 := (b - 48).toUInt16

def word : List UInt8 → UInt8 × UInt8
  | [a] =>
    if digit a then (1, a - 48) else (0, 0)
  | [a, b] =>
    if (a, b) = (101, 113) then (5, 0)
    else if (a, b) = (108, 116) then (6, 0)
    else if a ≠ 48 ∧ digit a ∧ digit b then
      (1, 10 * (a - 48) + (b - 48))
    else (0, 0)
  | [a, b, c] =>
    if (a, b, c) = (97, 100, 100) then (3, 0)
    else if (a, b, c) = (115, 117, 98) then (4, 0)
    else if (a, b, c) = (97, 110, 100) then (7, 0)
    else if (a, b, c) = (110, 111, 116) then (8, 0)
    else if a ≠ 48 ∧ digit a ∧ digit b ∧ digit c then
      let n := 100 * digitValue a + 10 * digitValue b + digitValue c
      if n ≤ 255 then (1, UInt8.ofNat n.toNat) else (0, 0)
    else (0, 0)
  | [a, b, c, d] => if (a, b, c, d) = (116, 114, 117, 101) then (2, 1) else (0, 0)
  | [a, b, c, d, e] =>
    if (a, b, c, d, e) = (102, 97, 108, 115, 101) then (2, 0) else (0, 0)
  | _ => (0, 0)

def finish (source : List UInt8) (start width : Nat) (out : List Token) : Result :=
  if width = 0 then .ok out
  else
    let (kind, value) := word ((source.drop start).take width)
    if kind = 0 then .error (2, start)
    else if out.length = 32 then .error (3, start)
    else .ok (out ++ [{ kind, value, start }])

/-- A pending lexeme is the half-open span ending at the next input index.
    At each separator, validate the complete span before checking token capacity. -/
def scan (source : List UInt8) : List UInt8 → Nat → Nat → Nat → List Token → Result
  | [], _, start, width, out => finish source start width out
  | b :: rest, i, start, width, out =>
    if space b then
      (finish source start width out).bind fun next => scan source rest (i + 1) start 0 next
    else scan source rest (i + 1) (if width = 0 then i else start) (width + 1) out

def lex (source : List UInt8) : Result :=
  if source.length > 256 then .error (1, 256) else scan source source 0 0 0 []

private theorem finish_length {source : List UInt8} {start width : Nat} {out xs : List Token}
    (bound : out.length ≤ 32) (ok : finish source start width out = .ok xs) : xs.length ≤ 32 := by
  unfold finish at ok
  split at ok
  · cases ok
    exact bound
  · dsimp at ok
    split at ok
    · contradiction
    · split at ok
      · contradiction
      · cases ok
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega

theorem scan_length {source remaining : List UInt8} {i start width : Nat} {out xs : List Token}
    (bound : out.length ≤ 32) (ok : scan source remaining i start width out = .ok xs) :
    xs.length ≤ 32 := by
  induction remaining generalizing i start width out with
  | nil => exact finish_length bound ok
  | cons b rest ih =>
    simp only [scan] at ok
    split at ok
    · cases verdict : finish source start width out with
      | error error => simp [verdict, Except.bind] at ok
      | ok next =>
        exact ih (finish_length bound verdict) (by simpa [verdict, Except.bind] using ok)
    · exact ih bound ok

theorem lex_length {source : List UInt8} {xs : List Token} (ok : lex source = .ok xs) :
    xs.length ≤ 32 := by
  unfold lex at ok
  split at ok
  · contradiction
  · exact scan_length (by decide : ([] : List Token).length ≤ 32) ok

private theorem finish_error_ne_zero {source : List UInt8} {start width offset : Nat}
    {out : List Token} {kind : UInt8} (error : finish source start width out = .error (kind, offset)) :
    kind ≠ 0 := by
  unfold finish at error
  split at error
  · contradiction
  · dsimp at error
    split at error
    · cases error
      decide
    · split at error
      · cases error
        decide
      · contradiction

private theorem scan_error_ne_zero {source remaining : List UInt8} {i start width offset : Nat}
    {out : List Token} {kind : UInt8} (error : scan source remaining i start width out = .error (kind, offset)) :
    kind ≠ 0 := by
  induction remaining generalizing i start width out with
  | nil => exact finish_error_ne_zero error
  | cons b rest ih =>
    simp only [scan] at error
    split at error
    · cases verdict : finish source start width out with
      | error found =>
        have same := Except.error.inj (by simpa only [verdict, Except.bind] using error)
        rw [same] at verdict
        exact finish_error_ne_zero verdict
      | ok next =>
        exact ih (by simpa only [verdict, Except.bind] using error)
    · exact ih error

theorem lex_error_ne_zero {source : List UInt8} {kind : UInt8} {offset : Nat}
    (error : lex source = .error (kind, offset)) : kind ≠ 0 := by
  unfold lex at error
  split at error
  · cases error
    decide
  · exact scan_error_ne_zero error

end LexerSpec

namespace LexerModel

def field (project : LexerSpec.Token → α) (zero : α) (out : List LexerSpec.Token) :
    Vector α 32 :=
  Vector.ofFn fun i => (out[i.val]?.map project).getD zero

def encode (endPos : Nat) (out : List LexerSpec.Token) : tokens :=
  ⟨field LexerSpec.Token.kind 0 out, field LexerSpec.Token.value 0 out,
    field (UInt16.ofNat ∘ LexerSpec.Token.start) 0 out, UInt8.ofNat out.length, UInt16.ofNat endPos⟩

def result (endPos : Nat) : LexerSpec.Result → tokens × Diagnostic
  | .ok out => (encode endPos out, ⟨0, 0⟩)
  | .error (kind, offset) => (encode 0 [], ⟨kind, UInt16.ofNat offset⟩)

def Agrees : Prop :=
  ∀ (source : List UInt8), (source.length : Int) < 2 ^ (GoTypes.WordBits - 1) →
    tokenize source = some (result source.length (LexerSpec.lex source))

end LexerModel
end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/bytecode_vm/compiler».compiler
