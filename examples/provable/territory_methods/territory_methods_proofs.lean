import territory_methods.territory_methods_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/territory_methods».territory_methods.Proofs

theorem configuredCaps : Laws.configuredCaps := by
  unfold Laws.configuredCaps
  decide

theorem villageCanClaimItsLastTile : Laws.villageCanClaimItsLastTile := by
  unfold Laws.villageCanClaimItsLastTile
  decide

theorem fullTerritoryCannotClaim : Laws.fullTerritoryCannotClaim := by
  intro tier
  simp [«Territory$CanClaim»]

theorem nilTerritoryPanics : Laws.nilTerritoryPanics := by
  rfl

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/territory_methods».territory_methods.Proofs
