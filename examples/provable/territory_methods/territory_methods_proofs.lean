import territory_methods.territory_methods_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/territory_methods».territory_methods

theorem configuredCaps : «Tier$TileLimit» 1 = 25 ∧ «Tier$TileLimit» 2 = 35 := by
  decide

theorem villageCanClaimItsLastTile : «Territory$CanClaim» (some ⟨2, 34⟩) = some true := by
  decide

theorem fullTerritoryCannotClaim (tier : UInt8) :
    «Territory$CanClaim» (some ⟨tier, «Tier$TileLimit» tier⟩) = some false := by
  simp [«Territory$CanClaim»]

theorem nilTerritoryPanics : «Territory$CanClaim» none = none := by
  rfl
