# Ten-pin bowling

Roll 10, then 3, then 4. The first delivery closes the opening frame as a strike, and the next two accepted deliveries make that frame worth 17. The scorer accumulates those bonuses while it records later frames.

## Play from bytes

```go
result := bowling.Play(lean.ByteArrayFromBytes([]byte("10, 3, 4")))
if result.IsSome() {
    played := result.UnwrapOr(bowling.Replay(lean.Nil[int64]()))
    score := played.Game().Score()
    fmt.Println(score.Total(), score.Complete())
}
```

`result.IsSome()` reports whether the whole input matched this grammar.

```ebnf
input = ws, [ count, { ws, ",", ws, count } ], ws, EOF ;
count = "0" | "1" | "2" | "3" | "4" | "5"
      | "6" | "7" | "8" | "9" | "10" ;
ws    = { " " | "\t" | "\r" | "\n" } ;
```

Empty input and whitespace alone represent zero attempts. Malformed input returns
an empty option. For valid input, `played.Decisions()` records the legality of every
delivery, including any rejected deliveries. `played.Game().Score()` reports a
score when the game is complete.

The lexer scans for counts and commas and discards ASCII whitespace. The parser
walks the lexer's reversed token list and prepends the counts to recover delivery
order. It hands the complete attempt list to `Replay`.

The Go package declares `playInputMatchesSpec`. For every modeled byte array
whose length fits the counted fold's index type, it checks that syntax failure
is equivalent to the absence of a parse under the standalone grammar. For every
valid parse it checks the ordered acceptance decisions, final score, and
completion flag against the bowling rules. The caller converts raw bytes before passing them to the modeled package.
[Go declaration](bowling.go) and [Lean grammar](bowling_grammar.lean)

## go-lean features

`Roll` returns a private result record with public `Game()` and `Accepted()` methods.

The translator models `roll` as `«gameState$roll»` with the receiver first. `Replay` folds over `lean.List[int64]` using a named step, then reverses the accumulated acceptance decisions with a second fold. The package imports a handwritten rules module and declares `fromStartMatchesRules`, equating the decision list and the final score observation with the independent rules for every list of attempts. [Modeled Go](bowling.go) and [rules](bowling_rules.lean)

## Proof challenge

The rules award a strike its next two accepted deliveries and a spare its next one. The Go state stores pending claims in `bonusNext` and `bonusSecond`. Those counters can overlap when consecutive strikes make two frames claim one roll. The proof relates the counters, running total, frame, and stage to the rule state. It also accounts for fill balls in the tenth frame.

Read `rollMatchesRules` for the one-delivery argument. A rejected delivery keeps the game unchanged and still contributes a false decision. Then read `fromStartMatchesRules` for the lift to histories from `Start`. This is where the proof must match both the ordered acceptance trace and the final score and completion flag. [Lean proofs](bowling_proofs.lean)

```sh
go test ./examples/proven/bowling
go run ./cmd/go-lean verify ./examples/proven/bowling
```
