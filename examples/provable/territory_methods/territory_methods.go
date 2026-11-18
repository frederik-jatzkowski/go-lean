package territorymethods

type Tier uint8

const (
	ClaimedLands Tier = 1
	Village      Tier = 2
)

//golean:verify
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
//golean:verify
func (territory *Territory) CanClaim() bool {
	return territory.Controlled < territory.Tier.TileLimit()
}
