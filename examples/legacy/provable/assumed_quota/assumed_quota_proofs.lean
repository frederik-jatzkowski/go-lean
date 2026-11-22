import assumed_quota.assumed_quota_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/assumed_quota».assumed_quota.Proofs

theorem deniesEleven : Laws.deniesEleven := by
  intro quota
  change decide ((11 : Int64) ≤ quota.operation) = false
  have bounded : quota.operation ≤ 10 := quota.quotaBound
  have denied : ¬ (11 : Int64) ≤ quota.operation := fun h => by
    have impossible : ¬ (11 : Int64) ≤ 10 := by decide
    exact impossible (Int64.le_trans h bounded)
  simp [denied]

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/assumed_quota».assumed_quota.Proofs
