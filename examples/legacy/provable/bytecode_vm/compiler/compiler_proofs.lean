import bytecode_vm.compiler.compiler_laws
import bytecode_vm.compiler.emit_proof
import bytecode_vm.compiler.type_proof
import bytecode_vm.compiler.lexer_proof
import bytecode_vm.compiler.source_execution

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/bytecode_vm/compiler».compiler.Proofs

theorem tokenizerAgreement : Laws.tokenizerAgreement := LexerProofs.tokenizeAgrees
theorem parserAgreement : Laws.parserAgreement := Parser.agrees
theorem typeCheckerAgreement : Laws.typeCheckerAgreement := TypeProof.checkTypesAgrees
theorem emitterAgreement : Laws.emitterAgreement := EmitProof.emitAgrees

theorem compilerAgreement : Laws.compilerAgreement :=
  Pipeline.agreesWhenTokenizerAgrees LexerProofs.tokenizeAgrees

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/bytecode_vm/compiler».compiler.Proofs
