import bytecode_vm.compiler.compiler_contract
import bytecode_vm.compiler.parse_grammar
import bytecode_vm.compiler.typing
import bytecode_vm.compiler.encoding
import bytecode_vm.compiler.sequencing
import bytecode_vm.compiler.parse_refinement
import bytecode_vm.compiler.lexer_proof
import Lean.Util.CollectAxioms

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/bytecode_vm/compiler»

namespace Source

open compiler compiler.Spec

set_option linter.unusedSimpArgs false

def reference (source : List UInt8) : Except (UInt8 × Nat) (Expr × UInt8) :=
  match LexerSpec.lex source with
  | .error diagnostic => .error diagnostic
  | .ok words =>
    match Grammar.parse words with
    | none => .error (4, source.length)
    | some expr =>
      match expr.typeCheck with
      | .error offset => .error (5, offset)
      | .ok (_, ty) => .ok (expr, ty)

def artifact (expr : Expr) (ty : UInt8) : Compiled :=
  ⟨Encoding.packed (expr.code ++ [.halt]), UInt8.ofNat (2 * (expr.nodeCount + 1)), ty⟩

def result : Except (UInt8 × Nat) (Expr × UInt8) → Compiled × Diagnostic
  | .error (kind, offset) => (Pipeline.emptyCompiled, ⟨kind, UInt16.ofNat offset⟩)
  | .ok (expr, ty) => (artifact expr ty, ⟨0, 0⟩)

def ParserAgrees : Prop :=
  ∀ source words, LexerSpec.lex source = .ok words →
    let input := LexerModel.encode source.length words
    match Grammar.parse words with
    | none => Parser.reference input = Parser.syntaxError input
    | some expr =>
      (Parser.reference input).2 = ⟨0, 0⟩ ∧
        Layout (Parser.reference input).1 expr ∧ expr.nodeCount ≤ 32

private theorem expressionFits {source : List UInt8} {words : List LexerSpec.Token}
    (lexed : LexerSpec.lex source = .ok words) (parsed : Grammar.parse words = some expr) :
    expr.nodeCount ≤ 32 := by
  have encoded := (Grammar.parsesExactly words expr).mp parsed
  have count := congrArg List.length (Grammar.codeFromPrefix expr)
  simp [encoded, expr.codeLength] at count
  rw [← count]
  exact LexerSpec.lex_length lexed

theorem parserAgrees : ParserAgrees := by
  intro source words lexed
  obtain ⟨size, canonical⟩ := Grammar.lexCanonical source words lexed
  have contract := Parser.referenceMatchesGrammar source.length words size (LexerSpec.lex_length lexed)
    canonical
  cases parsed : Grammar.parse words with
  | none => simpa [parsed] using contract
  | some expr =>
    have fits := expressionFits lexed parsed
    rw [parsed] at contract
    obtain ⟨arena, run, layout⟩ := contract
    simp [run, layout, fits]

theorem compilerMatchesSource (lexer : LexerModel.Agrees) (parser : ParserAgrees)
    (source : List UInt8) (fits : (source.length : Int) < 2 ^ (GoTypes.WordBits - 1)) :
    Compile source = some (result (reference source)) := by
  rw [Pipeline.agreesWhenTokenizerAgrees lexer source fits]
  unfold reference Pipeline.reference
  cases lexed : LexerSpec.lex source with
  | error diagnostic =>
    rcases diagnostic with ⟨kind, offset⟩
    have nonzero : kind ≠ 0 := LexerSpec.lex_error_ne_zero lexed
    simp [LexerModel.result, result, nonzero]
  | ok words =>
    have h := parser source words lexed
    cases parsed : Grammar.parse words with
    | none =>
      simp only [parsed] at h
      simp only [LexerModel.result, result, parsed, h, Prod.snd, Prod.fst]
      simp [Parser.syntaxError, LexerModel.encode]
    | some expr =>
      rw [parsed] at h
      obtain ⟨syntaxOK, layout, room⟩ := h
      let input := LexerModel.encode source.length words
      let arena := (Parser.reference input).1
      have checked := Typing.typeResultAgrees arena expr layout room
      have count : arena.«field:Count».toNat = expr.nodeCount := by simpa using layout.1
      have enough : arena.«field:Count».toNat ≤ 32 := by omega
      have encoded := Encoding.bytesMatch arena expr layout
      cases typing : expr.typeCheck with
      | error offset =>
        have rejected := checked
        simp only [typing] at rejected
        simp [LexerModel.result, result, parsed, syntaxOK, rejected, input, arena, typing]
      | ok typeResult =>
        rcases typeResult with ⟨entries, ty⟩
        have accepted := checked
        simp only [typing] at accepted
        simp [LexerModel.result, result, parsed, syntaxOK, accepted, enough, encoded,
          PassModel.codeLength, artifact, count, input, arena, typing, room]

def initial : vm.State := ⟨0, Vector.replicate 32 0, 0⟩

private theorem sourceTyped {source : List UInt8} {expr : Expr} {ty : UInt8}
    (accepted : reference source = .ok (expr, ty)) :
    expr.nodeCount ≤ 32 ∧ ∃ entries, expr.typeCheck = .ok (entries, ty) := by
  unfold reference at accepted
  cases lexed : LexerSpec.lex source with
  | error d => simp [lexed] at accepted
  | ok words =>
    cases parsed : Grammar.parse words with
    | none => simp [lexed, parsed] at accepted
    | some tree =>
      cases typed : tree.typeCheck with
      | error offset => simp [lexed, parsed, typed] at accepted
      | ok output =>
        rcases output with ⟨entries, inferred⟩
        simp [lexed, parsed, typed] at accepted
        obtain ⟨rfl, rfl⟩ := accepted
        exact ⟨expressionFits lexed parsed, entries, typed⟩

private theorem sourceErrorKind {source : List UInt8} {kind : UInt8} {offset : Nat}
    (rejected : reference source = .error (kind, offset)) : kind ≠ 0 := by
  unfold reference at rejected
  cases lexed : LexerSpec.lex source with
  | error d =>
    simp [lexed] at rejected
    subst d
    exact LexerSpec.lex_error_ne_zero lexed
  | ok words =>
    cases parsed : Grammar.parse words with
    | none =>
      simp [lexed, parsed] at rejected
      obtain ⟨rfl, rfl⟩ := rejected
      decide
    | some expr =>
      cases typed : expr.typeCheck with
      | ok output =>
        rcases output with ⟨entries, ty⟩
        simp [lexed, parsed, typed] at rejected
      | error why =>
        simp [lexed, parsed, typed] at rejected
        obtain ⟨rfl, rfl⟩ := rejected
        decide

theorem compileMatchesReference
    (source : List UInt8) (fits : (source.length : Int) < 2 ^ (GoTypes.WordBits - 1)) :
    Compile source = some (result (reference source)) :=
  compilerMatchesSource LexerProofs.tokenizeAgrees parserAgrees source fits

theorem compiledSourceHalts
    (source : List UInt8) (fits : (source.length : Int) < 2 ^ (GoTypes.WordBits - 1))
    (compiled : Compiled) (success : Compile source = some (compiled, ⟨0, 0⟩)) :
    ∃ expr value final,
      reference source = .ok (expr, value.type) ∧ expr.eval = some value ∧
      compiled = artifact expr value.type ∧
      Execution.Continues compiled.«field:Code» initial expr.nodeCount final ∧
      final.«field:PC».toNat = 2 * expr.nodeCount ∧
      vm.Step compiled.«field:Code» final = some (final, 1) ∧
      Execution.Live final [value.encode] := by
  rw [compileMatchesReference source fits] at success
  cases accepted : reference source with
  | error diagnostic =>
    rcases diagnostic with ⟨kind, offset⟩
    have nonzero := sourceErrorKind accepted
    rw [accepted] at success
    change some (Pipeline.emptyCompiled, (⟨kind, UInt16.ofNat offset⟩ : Diagnostic)) =
      some (compiled, ⟨0, 0⟩) at success
    have impossible := congrArg (fun pair : Compiled × Diagnostic => pair.2.«field:Kind»)
      (Option.some.inj success)
    exact False.elim (nonzero impossible)
  | ok output =>
    rcases output with ⟨expr, ty⟩
    obtain ⟨room, entries, typed⟩ := sourceTyped accepted
    rw [accepted] at success
    change some (artifact expr ty, (⟨0, 0⟩ : Diagnostic)) = some (compiled, ⟨0, 0⟩) at success
    have pairEq : (artifact expr ty, (⟨0, 0⟩ : Diagnostic)) = (compiled, ⟨0, 0⟩) :=
      Option.some.inj success
    have artifactEq := congrArg (fun pair : Compiled × Diagnostic => pair.1) pairEq
    change artifact expr ty = compiled at artifactEq
    rw [← artifactEq]
    have evaluation := expr.evalType
    rw [typed] at evaluation
    cases evaluated : expr.eval with
    | none => simp [evaluated] at evaluation
    | some value =>
      simp only [evaluated, Option.map_some, Option.some.injEq] at evaluation
      have valueType : value.type = ty := evaluation
      subst ty
      have cover := Execution.coversPacked (expr.code ++ [.halt]) (by simp [expr.codeLength]; omega)
      obtain ⟨final, run, pc, stop, live⟩ :=
        Execution.compiledHalts (artifact expr value.type).«field:Code» initial expr value evaluated
          cover room (by decide) (by simp [Execution.Live, initial])
      exact ⟨expr, value, final, rfl, evaluated, rfl, run, pc, stop, live⟩

run_cmd
  for theoremName in [``compileMatchesReference, ``compiledSourceHalts] do
    for axiomName in ← Lean.collectAxioms theoremName do
      unless [`propext, `Quot.sound, `Classical.choice].contains axiomName do
        throwError "Source execution proof {theoremName} depends on unapproved axiom {axiomName}"

end Source
end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/bytecode_vm/compiler»
