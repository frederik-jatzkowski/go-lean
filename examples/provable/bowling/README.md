# Ten-pin bowling

`Start()` and the zero value of `Game` both start a new game. Call
`game.Roll(pins)` and keep the returned game. An illegal delivery returns the
original game and `false`. `game.Score()` returns `(0, false)` until the game
ends, then returns the final score and `true`.

The game has ten frames. In frames 1–9, a strike earns the next two deliveries
as bonuses and a spare earns the next one. In the tenth frame, a strike or
spare earns a third delivery. After a tenth-frame strike, the second delivery
uses a fresh rack. The third uses a fresh rack only if the second was also a
strike. Fill balls can settle bonuses owed to earlier frames.

## Go model

The strict model advances one delivery at a time. It stores the frame, stage,
standing pins, running total, and credits due on the next two deliveries in a
value struct. Each accepted delivery constructs a new state and shifts the
credits forward. At most two earlier frames can claim the next delivery, so
the scoring step uses repeated addition for the three possible credit counts.

The modeled methods return a single named struct each. The public methods
unpack those structs into the legacy result pairs. The model uses `int64`
internally so the generated Lean integer width is stable across Go targets.
The public API still takes an `int`, and every reachable final score fits
within 0–300.

## Lean verification

The Go directives check the initial state, rejection without a state change,
the final-score projection, and stability after completion. The independent
Lean rules score by looking ahead from strikes and spares. The Go package
declares `fromStartMatchesRules`, which states that over every finite history
from `Start()`, the two scorers agree on acceptance, completion, and the final
score. The generated model includes that law and the verifier checks its
proof. The proof companion also proves and audits the score bounds and shows
that a legal delivery can always lead to a completed game.

```sh
go test ./examples/provable/bowling
go run ./cmd/go-lean verify ./examples/provable/bowling
```
