import interface_dispatch.interface_dispatch_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/interface_dispatch».interface_dispatch

theorem apply_identity {Handle : Type} (contract : InterfaceContracts.EvaluatorContract Handle)
    (evaluator : Handle) (value : Int64) :
    Apply contract evaluator value = value :=
  contract.evaluate_identity evaluator value
