import bytecode_vm.compiler.lexer_spec
import bytecode_vm.compiler.parse_proof
import bytecode_vm.compiler.pass_model
import bytecode_vm.compiler.type_proof

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/bytecode_vm/compiler».compiler.Pipeline

def emptyCompiled : Compiled := ⟨Vector.replicate 66 0, 0, 0⟩

def reference (source : List UInt8) : Compiled × Diagnostic :=
  let (tokens, lexical) := LexerModel.result source.length (LexerSpec.lex source)
  if lexical.«field:Kind» ≠ 0 then (emptyCompiled, lexical)
  else
    let (tree, parsing) := Parser.reference tokens
    if parsing.«field:Kind» ≠ 0 then (emptyCompiled, parsing)
    else
      let (inferred, typing) := PassModel.typeResult tree
      if typing.«field:Kind» ≠ 0 then (emptyCompiled, typing)
      else
        let (code, length) := if tree.«field:Count».toNat ≤ 32 then
          (PassModel.code tree, PassModel.codeLength tree)
          else (Vector.replicate 66 0, 0)
        (⟨code, length, inferred.«field:Root»⟩, ⟨0, 0⟩)

def Contract : Prop :=
  ∀ source : List UInt8, (source.length : Int) < 2 ^ (GoTypes.WordBits - 1) →
    Compile source = some (reference source)

theorem agreesWhenTokenizerAgrees (tokenizer : LexerModel.Agrees) : Contract := by
  intro source fits
  have parsing (input : tokens) : parse input = some (Parser.reference input) := Parser.agrees input
  have checking (input : tree) : checkTypes input = some (PassModel.typeResult input) :=
    TypeProof.checkTypesAgrees input
  simp only [Compile, reference, tokenizer source fits, parsing, checking,
    EmitProof.emitTotalAgrees, bind, Option.bind, pure, emptyCompiled, decide_eq_true_eq,
    show UInt8.ofNat 0 = (0 : UInt8) by rfl]
  split
  · rfl
  · split
    · rfl
    · split <;> rfl

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/bytecode_vm/compiler».compiler.Pipeline
