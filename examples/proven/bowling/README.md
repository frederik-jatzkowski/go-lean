# Ten-pin bowling

Roll 10, then 3, then 4. The first delivery closes the opening frame as a strike, and the next two accepted deliveries make that frame worth 17. The scorer accumulates those bonuses while it records later frames.

## go-lean features

The public `Roll` wrapper calls a modeled value method and unpacks its result:

```go
func (game Game) Roll(pins int) (Game, bool) {
	result := game.roll(int64(pins))
	return result.game, result.accepted
}
```

The translator models `roll` as `«Game$roll»` with the receiver first. `Replay` folds over `lean.List[int64]` using a named step, then reverses the accumulated acceptance decisions with a second fold. The package imports a handwritten rules module and declares `fromStartMatchesRules`, equating the decision list and the final score observation with the independent rules for every list of attempts. [Modeled Go](bowling.go) and [rules](bowling_rules.lean)

## Proof challenge

The rules award a strike its next two accepted deliveries and a spare its next one. The Go state stores pending claims in `bonusNext` and `bonusSecond`. Those counters can overlap when consecutive strikes make two frames claim one roll. The proof relates the counters, running total, frame, and stage to the rule state. It also accounts for fill balls in the tenth frame.

Read `rollMatchesRules` for the one-delivery argument. A rejected delivery keeps the game unchanged and still contributes a false decision. Then read `fromStartMatchesRules` for the lift to histories from `Start`. This is where the proof must match both the ordered acceptance trace and the final score and completion flag. [Lean proofs](bowling_proofs.lean)

```sh
go test ./examples/proven/bowling
go run ./cmd/go-lean verify ./examples/proven/bowling
```
