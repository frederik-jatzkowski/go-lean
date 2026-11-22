# Nine Men's Morris

Run `go run ./examples/provable/nine_mens_morris/cmd/morris` from the repo root.
The terminal shows the 24 numbered points. White moves first. Enter one point to
place or capture, two points to move, or `q` to quit.

## Rules

Each player starts with nine reserve stones. Players alternate placing one stone
on a vacant point until both reserves are empty. From then on, a player with
more than three stones slides from one point to an adjacent vacant point. A
player with exactly three stones may fly directly to any vacant point. Flying
has no path and leaves opposing stones in place. A mill formed by flying
grants the same separate capture action as a mill formed by sliding or placing.

Completing a mill at the destination grants one required capture, including
when the action completes two mills. A stone in an opposing mill is protected
unless all opposing stones are in mills. The same player acts until the capture
is complete. If the opponent has no stones to capture, the turn passes
immediately.

After placement, the player to move loses if they have fewer than three stones
or have no legal move. This example uses a draw after 50 consecutive movement
turns without a capture. A capture resets the count, and an eligible win takes
precedence over a draw. The example uses this counter instead of repetition
history. See Ralph Gasser's [rules and variant discussion](https://library.slmath.org/books/Book29/files/gasser.pdf).

## Checked behavior

`Game` owns the rules and a board backed by a 24-element array. Its public `Place`, `Move`, and `Capture`
methods return a complete next game value on acceptance and the original value
on rejection. The CLI keeps the returned game. Callers can also retain earlier
values or persist the returned state separately.

`IsValid` checks that the current player is White or Black. Start a new game
with `Start()`. A zero-value `Game` fails the check and rejects all actions.
The validity check certifies initialization. Reachability from the opening
position is a property of the game history.

Regenerate with `go tool task generate`. Run
`lake build nine_mens_morris.morris_verify` to check the companion proofs.

The Go-declared laws cover the initial state, the board edges and mills, the
effect of editing a board point, placement and movement eligibility, mill
protection, capture eligibility, turn completion, and the complete result of
each individual action. The outcome laws specify blocking, loss on material,
the draw threshold, and the order in which those outcomes are considered.
Board layout cases are finite. The action laws quantify over state and point
arguments rather than sampling complete games.

The action, legality, and outcome laws are attached to the public game methods.
The public `Move` laws also prove that an accepted move preserves every opposing
stone and leaves a capture pending exactly when it closes a mill and the
opponent has a stone to take.
`morris_rules.lean` defines the rules using the game state fields, board
geometry, and the variant described above. `morrisCorrect` proves that for
every game that passes `IsValid`, the translated Go methods agree with those
rules on legality, the entire next state, and the outcome. All three actions
preserve `IsValid`, including on rejection.

`fromStartMatchesRules` proves by induction that the initial state and outcome
agree and that every finite sequence of attempted actions produces the same
acceptance decisions, states, and outcomes. `reachableIsValid` proves that
every state reached by legal play passes `IsValid`.

The package doc comment declares `fromStartMatchesRules` and imports the
reference rules with `//golean:verify:import nine_mens_morris.morris_rules`. The
rules module imports the generated model for its state types. The generated
`morris_laws.lean` imports both, and the proof companion imports that law module.

Applying these theorems to Go assumes that go-lean preserves Go semantics.
Persistence, terminal input, and rendering are outside the Lean laws.
