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
history.

## Go model

The board holds 24 cells in a `lean.Array[Player]`. Reads use
`Get(...).UnwrapOr(Empty)` and writes use `Set`, so a caller can retain any
previous game as a snapshot. The array makes `Board` and `Game` non-comparable
with Go's `==` operator.

The model uses value methods on `Game` and `Board`. go-lean lowers each
method to a Lean function with the receiver as its first argument. Private
modeled methods use `uint` indices for the curated array API. Public methods
convert the legacy `Point` type at the boundary. A modeled action returns one
record containing the next game and acceptance flag, which the public action
method unpacks into two results. The terminal driver handles input, rendering
and repetition in ordinary Go.

Board geometry and scans are finite. Geometry is written as point-specific
conditions, and the scans explicitly visit the 24 fixed points. Each accepted
transition builds a fresh keyed state value, and each rejected transition
returns the input state. `IsValid` checks the active player. `Start` initializes
both the active player and the board.

## Verification

Run `go run ./cmd/go-lean verify ./examples/provable/nine_mens_morris` from
the repository root with Elan on PATH. The checked-in model was generated for
a 64-bit Go target.

The Go-declared laws cover board geometry, legality, outcomes and complete
single-action transitions. The Lean proof companion also compares the generated
functions with independent rules and proves agreement on acceptance, state and
outcome for every finite history from the opening position. The terminal driver
runs in ordinary Go.
