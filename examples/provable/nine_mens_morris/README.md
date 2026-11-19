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

`Game` owns the board and the rules. Its public `Place`, `Move`, and `Capture`
methods return a complete next game value on acceptance and the original value
on rejection. The CLI keeps the returned game. Callers can also retain earlier
values or persist the returned state separately.

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
The model assumes normal go-lean translation correctness. Go tests exercise the
public API, including double-mill capture, flying, a blocked loss, and a draw.
Whole-game reachability, persistence, terminal input, and rendering are outside
the Lean laws.
