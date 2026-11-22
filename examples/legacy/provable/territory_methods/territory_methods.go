package territorymethods

type Tier uint8

const (
	ClaimedLands Tier = 1
	Village      Tier = 2
)

//golean:verify configuredCaps : «Tier$TileLimit» 1 = 25 ∧ «Tier$TileLimit» 2 = 35
func (tier Tier) TileLimit() uint8 {
	switch tier {
	case ClaimedLands:
		return 25
	case Village:
		return 35
	default:
		return 0
	}
}

type Territory struct {
	Tier       Tier
	Controlled uint8
}

// CanClaim reports whether there is room for one additional tile.
//
//golean:verify villageCanClaimItsLastTile : «Territory$CanClaim» (some ⟨2, 34⟩) = some true
//golean:verify fullTerritoryCannotClaim : ∀ (tier : UInt8),
//golean:verify+   «Territory$CanClaim» (some ⟨tier, «Tier$TileLimit» tier⟩) = some false
//golean:verify nilTerritoryPanics : «Territory$CanClaim» none = none
func (territory *Territory) CanClaim() bool {
	return territory.Controlled < territory.Tier.TileLimit()
}
