// Package bowling scores a single game of American ten-pin bowling.
// Starting from Start, every sequence of attempted rolls follows the ten-pin
// rules for acceptance and final scoring.
//
//golean:verify:import bowling.bowling_rules
//golean:verify fromStartMatchesRules : ∀ attempts,
//golean:verify+   let reference := Bowling.Rules.play Bowling.Rules.initial (attempts.map Int64.toInt)
//golean:verify+   let actual := run Start attempts
//golean:verify+   actual.1 = reference.1 ∧ «Game$Score» actual.2 = answer (Bowling.Rules.score reference.2.2)
package bowling

const (
	firstBall = iota
	secondBall
	afterTenthStrike
	fillBall
)

// Game tracks a player's rolls and score. The zero value is ready to bowl.
// Once Score reports completion, Roll rejects every delivery and the score
// stays fixed.
//
//golean:verify completedGameIsStable : ∀ game score pins,
//golean:verify+   «Game$Score» game = (score, true) →
//golean:verify+   «Game$Roll» game pins = (game, false) ∧
//golean:verify+     «Game$Score» («Game$Roll» game pins).1 = (score, true)
type Game struct {
	frame       int // zero-based; 10 means the game is complete
	stage       int
	standing    int // used when the rack is not necessarily fresh
	total       int
	bonusNext   int
	bonusSecond int
}

// Start returns a new game.
//
//golean:verify startEmpty : Start = ⟨0, 0, 0, 0, 0, 0⟩
func Start() Game { return Game{} }

// Roll returns the next game, or the original game if the delivery is illegal.
//
//golean:verify rejectionUnchanged : ∀ s pins, («Game$Roll» s pins).2 = false → («Game$Roll» s pins).1 = s
func (game Game) Roll(pins int) (Game, bool) {
	if game.frame == 10 || pins < 0 || pins > game.rack() {
		return game, false
	}

	switch game.stage {
	case firstBall:
		if pins < 10 {
			game.stage = secondBall
			game.standing = 10 - pins
			return game.record(pins, 0), true
		}
		if game.frame == 9 {
			game.stage = afterTenthStrike
			return game.record(pins, 0), true
		}
		return game.finishFrame().record(pins, 2), true
	case secondBall:
		if pins == game.standing {
			if game.frame == 9 {
				game.stage = fillBall
				game.standing = 10
				return game.record(pins, 0), true
			}
			return game.finishFrame().record(pins, 1), true
		}
	case afterTenthStrike:
		game.stage = fillBall
		game.standing = 10
		if pins < 10 {
			game.standing = 10 - pins
		}
		return game.record(pins, 0), true
	}
	return game.finishFrame().record(pins, 0), true
}

func (game Game) rack() int {
	if game.stage == firstBall || game.stage == afterTenthStrike {
		return 10
	}
	return game.standing
}

func (game Game) record(pins, bonus int) Game {
	game.total += pins * (1 + game.bonusNext)
	game.bonusNext = game.bonusSecond
	game.bonusSecond = 0
	if bonus > 0 {
		game.bonusNext++
	}
	if bonus == 2 {
		game.bonusSecond = 1
	}
	return game
}

func (game Game) finishFrame() Game {
	game.frame++
	game.stage = firstBall
	game.standing = 0
	return game
}

// Score returns the final score once all required deliveries have been made.
//
//golean:verify finalScore : ∀ s, «Game$Score» s = if s.«field:frame» = 10 then (s.«field:total», true) else (0, false)
func (game Game) Score() (int, bool) {
	if game.frame == 10 {
		return game.total, true
	}
	return 0, false
}
