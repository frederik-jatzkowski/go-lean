import interface_dispatch.interface_dispatch_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/interface_dispatch».interface_dispatch.Proofs

theorem apply_identity : Laws.apply_identity := by
  intro Handle contract evaluator value
  exact contract.evaluate_identity evaluator value

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/interface_dispatch».interface_dispatch.Proofs
