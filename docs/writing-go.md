# Writing modeled Go

Choose a small operation whose inputs and outputs express a property you want to prove. Let ordinary Go gather input, perform I/O, and display results. Put the decision in a function that takes values and returns one unnamed result. A record can carry the next state and observations together.

## Put the model in its own package

Move pure functions and records into a model package. Keep runtime code in a separate Go package that calls the model with supported values. Call pure operations directly from the model. Bowling’s `Roll` returns a record containing the next game and an acceptance flag. The compiler facade copies source bytes into a `lean.ByteArray` before calling its model. [Bowling](../examples/proven/bowling/README.md) and [compiler](../examples/proven/stack_machine_compiler/README.md)

Use concrete value receivers, explicit immutable local initializers, keyed record literals, `if`, and early returns. Return a new value when a field changes. A translated value method takes its receiver first in Lean, so `game.Roll(pins)` becomes an application of `«Game$Roll»` to `game` and `pins`.

## Move traversal state into a record

The grid game replays moves with a named step that receives a direction and the current replay state. The state carries the position and wrapping mode. It returns the next position with the same mode:

```go
return lean.FoldList(moves, replayState{Position: Start(), Wrap: wrap}, replayMove).Position
```

Use `FoldN` to visit a known number of indices, `FoldList` to visit list items, and the `Until` variants to stop early. Put extra inputs in the state record. For arrays and byte arrays, iterate over `Size()` and use `Get(index)`. Named steps follow the same subset rules as other modeled functions. [Grid game walkthrough](../examples/proven/grid_game/README.md)

## Give recursive records a decreasing measure

The compiler represents child expressions with direct `lean.Box[expression]` fields. Use `lean.NewBox(value)` for a child and an empty box for absence. Check `IsSome()` before recursively processing `Get()`. The compiler marks its directly recursive passes with `//golean:termination:by sizeOf expr`. Lean checks that the measure decreases at each recursive call and exposes an unfolding equation ending in `.eq_def`. [Compiler walkthrough](../examples/proven/stack_machine_compiler/README.md)

See [Supported Go](supported-go.md) for representations and restrictions.
