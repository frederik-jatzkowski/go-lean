# Ten-pin bowling

`Start()` returns a game ready for its first delivery, as does the zero value of
`Game`. Call `game.Roll(pins)` with the number of pins knocked down and keep the
returned game. A rejected delivery returns the original game and `false`.
`game.Score()` returns `(0, false)` until the game ends, then returns the final
score as an `int` and `true`.

The game has ten frames. In frames 1–9, a strike ends the frame and adds the
next two deliveries to its score. A spare adds the next delivery. In the tenth,
an open frame ends after two deliveries, and a strike or spare earns a third.
After a tenth-frame strike, the second delivery uses a fresh rack. If that
delivery knocks down seven pins, the third can knock down at most three. If it
strikes, the third uses a fresh rack. Fill balls count toward the tenth and can
settle bonuses from earlier frames.
[USBC scoring guide](https://bowl.com/keeping-score)

## Checked behavior

| Scope | Proposition | Where it is declared |
| --- | --- | --- |
| Method | `rejectionUnchanged` states that a rejected `Roll` preserves its receiver. | `Roll`'s Go doc comment |
| Type | `completedGameIsStable` relates `Score` and `Roll`. Once the game reports a final score, every further roll is rejected and the same score is reported. | `Game`'s Go doc comment |
| Package | `fromStartMatchesRules` relates `Start`, `Roll`, and `Score` over every finite history. | Package doc comment |

The package comment uses `//golean:verify:import bowling.bowling_rules`. Generation
puts the propositions in `bowling_laws.lean`, which the proof companion imports.

The Go scorer accumulates points as deliveries arrive and tracks bonuses owed
on the next two deliveries. The handwritten Lean rules define legal deliveries
by frame and compute the score by looking ahead at the deliveries that follow
each strike or spare.

`rollMatchesRules` relates each modeled Go transition to the Lean rules,
including the full next state. `rollAcceptedIffCompletable` shows that a roll
is accepted exactly when it can begin a legal completion of the current game.
`fromStartMatchesRules` proves that for every finite sequence of attempted
deliveries, the model and rules agree on all acceptance decisions and on
whether a final score exists and what it is. `goScoreBounds` proves that every
final score returned by the model is in the range 0–300.

Run `lake build bowling.bowling_verify` to check the proofs and audit their axiom
dependencies. The example covers scoring and validation of recorded pinfall for
one player. Applying the result to Go execution assumes that go-lean preserves
Go semantics.
