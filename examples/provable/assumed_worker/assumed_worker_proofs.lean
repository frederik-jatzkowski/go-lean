import assumed_worker.assumed_worker

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/assumed_worker».Proofs

theorem matchesInput : Laws.matchesInput := by
  intro worker
  intro x
  change decide (worker.operation x = x) = true
  have identity : worker.operation x = x := worker.preservesInput x
  simp [identity]

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/assumed_worker».Proofs
