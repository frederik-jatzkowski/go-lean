# Nine Men’s Morris

Form a mill by completing three stones in a line. From the opening position, enter `0`, `3`, `1`, `4`, and `2` to alternate placements. White's last placement completes the line at 0, 1, and 2. White acts again and can enter `3` to capture that black stone. The same pending-capture rule applies when a slide or flight completes a mill.

```sh
go run ./examples/proven/nine_mens_morris/cmd/morris
```

Each player starts with nine reserve stones. After placement, players slide to adjacent vacant points, or fly to any vacant point when they have exactly three stones. An opposing stone in a mill is protected unless all opposing stones are in mills. A player loses after placement if they have fewer than three stones or no legal move. The example also uses a draw after 50 consecutive movement turns without a capture, with a win taking precedence.

## go-lean features

The private `gameState` and `boardState` use concrete value methods. Lean calls the generated move as `«gameState$move» s f t`, with the game first. The board stores stones in a `lean.Array[playerColor]`. Updating the source and destination creates a new board value. Public transition methods return a private result with `Next()` and `Accepted()` accessors. The terminal handles input and display in ordinary Go.

The move-availability scan carries the board and player as immutable state:

```go
return lean.FoldNUntil(24, boardScan{board: board, player: player}, findSlide).Stop
```

`FoldN` counts stones, while `FoldNUntil` can stop on the first available slide or unprotected stone. [Modeled Go](morris.go)

## Proof challenge

The implementation encodes adjacency and mills with point-specific conditions. The proof connects those conditions to the rule relations on board points. It also shows that the fixed scans implement counting and existence. In particular, `scanMatchesAny` connects the early-stop flag to a satisfied predicate in the visited range.

For an accepted move, `movePreservesOpposingStones` proves the opposing stones stay put, and `moveGrantsCaptureExactlyOnMill` characterizes when the resulting game has a pending capture. The proof then combines legality and transitions in `stepMatchesRules`. Its history theorem extends that agreement to every finite sequence of actions from the opening position, including rejected actions. [Rules](morris_rules.lean) and [Lean proofs](morris_proofs.lean)

```sh
go test ./examples/proven/nine_mens_morris/...
go run ./cmd/go-lean verify ./examples/proven/nine_mens_morris
```
