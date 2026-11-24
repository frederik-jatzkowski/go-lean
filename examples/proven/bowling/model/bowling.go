// Package bowling scores one game of American ten-pin bowling.
//
//golean:verify:import bowling.bowling_rules
//golean:verify fromStartMatchesRules : ∀ attempts,
//golean:verify+ let reference := Bowling.Rules.play Bowling.Rules.initial (attempts.map Int64.toInt)
//golean:verify+ let actual := Replay attempts
//golean:verify+ let result := «Game$Score» actual.«field:Game»
//golean:verify+ actual.«field:Decisions» = reference.1 ∧
//golean:verify+   (result.«field:Total», result.«field:Complete») =
//golean:verify+     Bowling.Rules.answer (Bowling.Rules.score reference.2.2)
package bowling

import "github.com/frederik-jatzkowski/go-lean/pkg/lean"

const (
	firstBall = iota
	secondBall
	afterTenthStrike
	fillBall
)

// Game tracks a player's rolls and score. Its zero value is ready to bowl.
type Game struct {
	frame       int64 // zero-based; 10 means complete
	stage       int64
	standing    int64
	total       int64
	bonusNext   int64 // at most two earlier frames can claim the next ball
	bonusSecond int64 // at most one can also claim the ball after that
}

// Start returns a new game.
//
//golean:verify startEmpty : Start = ⟨0, 0, 0, 0, 0, 0⟩
func Start() Game {
	return Game{frame: 0, stage: firstBall, standing: 0, total: 0, bonusNext: 0, bonusSecond: 0}
}

type RollResult struct {
	Game     Game
	Accepted bool
}

type ScoreResult struct {
	Total    int64
	Complete bool
}

// Roll returns the next game and whether the delivery was accepted.
//
//golean:verify rejectionUnchanged : ∀ s pins,
//golean:verify+   («Game$Roll» s pins).«field:Accepted» = false → («Game$Roll» s pins).«field:Game» = s
func (game Game) Roll(pins int64) RollResult {
	if game.frame == 10 || pins < 0 || pins > game.rack() {
		return RollResult{Game: game, Accepted: false}
	}
	if game.stage == firstBall {
		if pins < 10 {
			return game.record(pins, game.frame, secondBall, 10-pins, 0)
		}
		if game.frame == 9 {
			return game.record(pins, game.frame, afterTenthStrike, 0, 0)
		}
		return game.record(pins, game.frame+1, firstBall, 0, 2)
	}
	if game.stage == secondBall && pins == game.standing {
		if game.frame == 9 {
			return game.record(pins, game.frame, fillBall, 10, 0)
		}
		return game.record(pins, game.frame+1, firstBall, 0, 1)
	}
	if game.stage == afterTenthStrike {
		if pins == 10 {
			return game.record(pins, game.frame, fillBall, 10, 0)
		}
		return game.record(pins, game.frame, fillBall, 10-pins, 0)
	}
	return game.record(pins, game.frame+1, firstBall, 0, 0)
}

func (game Game) rack() int64 {
	if game.stage == firstBall || game.stage == afterTenthStrike {
		return 10
	}
	return game.standing
}

func creditedPins(pins, claims int64) int64 {
	if claims == 2 {
		return pins + pins + pins
	}
	if claims == 1 {
		return pins + pins
	}
	return pins
}

func nextBonus(second, balls int64) int64 {
	if balls > 0 {
		return second + 1
	}
	return second
}

func secondBonus(balls int64) int64 {
	if balls == 2 {
		return 1
	}
	return 0
}

func (game Game) record(pins, frame, stage, standing, balls int64) RollResult {
	return RollResult{
		Game: Game{
			frame:       frame,
			stage:       stage,
			standing:    standing,
			total:       game.total + creditedPins(pins, game.bonusNext),
			bonusNext:   nextBonus(game.bonusSecond, balls),
			bonusSecond: secondBonus(balls),
		},
		Accepted: true,
	}
}

//golean:verify finalScore : ∀ s,
//golean:verify+   «Game$Score» s = if s.«field:frame» = 10 then ⟨s.«field:total», true⟩ else ⟨0, false⟩
//golean:verify completedGameIsStable : ∀ game total pins,
//golean:verify+   «Game$Score» game = ⟨total, true⟩ →
//golean:verify+   «Game$Roll» game pins = ⟨game, false⟩ ∧
//golean:verify+   «Game$Score» («Game$Roll» game pins).«field:Game» = ⟨total, true⟩
func (game Game) Score() ScoreResult {
	if game.frame == 10 {
		return ScoreResult{Total: game.total, Complete: true}
	}
	return ScoreResult{Total: 0, Complete: false}
}

// ReplayResult records the final game and acceptance decisions in attempt order.
type ReplayResult struct {
	Game      Game
	Decisions lean.List[bool]
}

func replayAttempt(pins int64, state ReplayResult) ReplayResult {
	result := state.Game.Roll(pins)
	return ReplayResult{Game: result.Game, Decisions: lean.Cons(result.Accepted, state.Decisions)}
}

func prependDecision(accepted bool, decisions lean.List[bool]) lean.List[bool] {
	return lean.Cons(accepted, decisions)
}

// Replay starts a new game and applies each attempt in order.
//
//golean:export
func Replay(attempts lean.List[int64]) ReplayResult {
	initial := ReplayResult{Game: Start(), Decisions: lean.Nil[bool]()}
	result := lean.FoldList(attempts, initial, replayAttempt)
	ordered := lean.FoldList(result.Decisions, lean.Nil[bool](), prependDecision)
	return ReplayResult{Game: result.Game, Decisions: ordered}
}
