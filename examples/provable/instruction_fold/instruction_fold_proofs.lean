import instruction_fold.instruction_fold_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/instruction_fold».instruction_fold.Proofs

private theorem foldOperands (instructions : List Instruction) (sum : Int64) :
    instructions.foldl (fun acc ins => (ins.«field:Operands».getD []).foldl (· + ·) acc) sum =
      (instructions.flatMap (fun ins => ins.«field:Operands».getD [])).foldl (· + ·) sum := by
  induction instructions generalizing sum with
  | nil => rfl
  | cons ins rest ih => simp [List.flatMap_cons, List.foldl_append, ih]

theorem byOperandsMatchesFlattenedFold : Laws.byOperandsMatchesFlattenedFold := by
  intro code
  exact foldOperands (code.getD []) 0

theorem byInstructionMatchesFlattenedFold : Laws.byInstructionMatchesFlattenedFold := by
  intro code
  exact foldOperands (code.getD []) 0

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/instruction_fold».instruction_fold.Proofs
