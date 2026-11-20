# Ten-pin bowling

`Start` returns an empty game. `Game.Roll(pins)` returns a new game and an acceptance flag. A rejected roll returns the original game, so callers can continue from the returned value after any attempt. `Game.Score()` returns `(0, false)` while play is ongoing and the final score with `true` when play is complete. [Go implementation](../examples/provable/bowling/bowling.go)

## Follow a delivery

`Roll` checks that the game is ongoing and the number of pins is between zero and the pins standing on the current rack. In the first nine frames, a strike ends the frame and schedules bonuses for the next two legal deliveries. A spare ends the frame and schedules a bonus for the next legal delivery. The next frame starts with a full rack.

For example, a strike followed by rolls of 7 and 2 earns 19 points for the strike frame and 9 points for the second frame. The implementation counts these bonuses as deliveries arrive. `record` multiplies the new pin count by one plus the number of bonuses due for that delivery, then advances the pending bonus counters. The public `Score` still reports the game as ongoing at that point.

A tenth-frame spare earns one fill ball with a fresh rack. A tenth-frame strike earns two fill balls. If the first fill knocks down 7, the second can knock down at most 3. An attempt of 4 leaves the game unchanged, so a subsequent roll of 3 can still finish it.

## Read the laws by scope

| Scope | Law | Checked behavior |
| --- | --- | --- |
| Function | `startEmpty` | `Start` returns the empty game representation. |
| Method | `rejectionUnchanged` | Every rejected roll preserves the entire game value. |
| Method | `finalScore` | Completion and the returned score agree with the internal frame and total. |
| Type | `completedGameIsStable` | A completed game rejects further rolls and retains its score. |
| Package | `fromStartMatchesRules` | From `Start`, every finite sequence of attempts yields the reference acceptance flags and score result. |

The package law includes attempts after completion and compares both components of the final `Score` pair. [Generated laws](../examples/provable/bowling/bowling_laws.lean)

## Follow the history proof

[bowling_rules.lean](../examples/provable/bowling/bowling_rules.lean) defines legal deliveries using an explicit `Phase`. Its scorer computes strike and spare bonuses by looking ahead in the list of accepted deliveries. `play` records acceptance for every attempt and passes only accepted deliveries to scoring.

In [bowling_proofs.lean](../examples/provable/bowling/bowling_proofs.lean), start with `encode`. It relates the rules phase, running total, and pending bonuses to the generated fields of `Game`. Then follow these lemmas:

1. `rollMatchesRules` proves that one attempt on an encoded state agrees with the rules. On success, it relates the next game to the next phase and updated scoring fields. On rejection, the game remains unchanged.
2. `runAgrees` uses induction over attempted deliveries. The accepted branch advances the phase and relates pending bonuses to the reference scorer's lookahead. The rejected branch keeps the game and the phase and records a false flag.
3. `fromStartMatchesRules` applies that result to the empty game. The file also derives `goScoreBounds`, which bounds any completed score reached from `Start` between 0 and 300.

[Run the bowling checks from a checkout](../CONTRIBUTING.md#check-the-bowling-example).
