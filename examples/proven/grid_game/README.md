# Grid game

Start at `(1, 1)` on an eight-by-eight board. In wrapping mode, moving left from the start would enter the wall at `(0, 1)`, so the position stays put. A left move from `(0, 3)` wraps to `(7, 3)` in that mode and stays at `(0, 3)` in bounded mode.

```sh
go run ./examples/proven/grid_game/cmd/grid-game -wrap
```

## go-lean features

The `layout` function stores the board as an array of eight row arrays. Rows
run from top to bottom, and cells within each row run from left to right, both
starting at zero. To edit `(x, y)`, find row `y` and change its cell at column
`x` to `Open`, `Wall`, or `WrapWall`. A `WrapWall` blocks movement only in
wrapping mode. Both movement and rendering read the layout through `IsWall`.

The interactive driver calls the modeled `Step` with explicit position, direction, and mode. `Replay` uses `lean.FoldList` with a named step and an immutable state record to apply the same transition to a list of directions. The Go law can therefore quantify over Lean lists:

```go
//golean:verify youCantWin : ∀ (wrap : Bool) (moves : List UInt8),
//golean:verify+   Won (Replay moves wrap) = false
```

The concrete step laws cover bounded edges, wrapping, ordinary and seam walls, and unknown direction codes. [Modeled Go](model/grid_game.go)

## Walkthrough challenges

Proving that the current cell differs from the goal gives too little information about the next move. The proof defines `safe` to require an in-bounds cell outside the goal room and walls. `boardCases` checks all board coordinates, four cardinal directions, and both modes using Lean's `decide`. `stepSafe` uses those finite cases for cardinal moves and unfolds `Step` for unknown codes, which leave the position unchanged.

`replayAgrees` relates the generated fold to a Lean replay. `replaySafe` inducts over the move list, applying `stepSafe` at each move. Since the start satisfies `safe`, the invariant gives the claimed result for histories of any finite length. [Lean proofs](model/grid_game_proofs.lean)

```sh
go run ./cmd/go-lean verify ./examples/proven/grid_game/model
```

Try each edit independently. Restore the original cell after each challenge
and run verification again on the restored board.

1. **Add a wall at `(2, 1)`.** Change the third cell in the second row from
   `Open` to `Wall`. Predict where the first right move will leave you, then
   try it in the game and rerun verification. The player stays at `(1, 1)`
   and `youCantWin` still verifies.
2. **Open the wall at `(5, 1)`.** Change the sixth cell in the second row
   from `Wall` to `Open`. Find a winning move history in bounded mode, then
   rerun verification. Six right moves from `(1, 1)` reach the goal at
   `(7, 1)`, giving a counterexample to `youCantWin`. The
   `stepOrdinaryWall` check also fails because it expects that cell to block
   movement. Run the game without `-wrap` to try the winning history.
