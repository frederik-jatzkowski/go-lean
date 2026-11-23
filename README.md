# go-lean

![A Go gopher sends a Go method through go-lean to produce a Lean theorem.](docs/images/go-lean-hero.png)

**Write the logic in Go. Prove its properties in Lean.**

go-lean brings Go decision logic into Lean, where you can prove critical parts of your system.
A core written in the supported subset gives go-lean the code it needs to generate a Lean model.
You state the laws alongside the Go code and write proofs that Lean checks against that model.

[Supported Go](docs/supported-go.md)

## Verify your first package

With Go 1.26 or later and Elan on PATH, run these commands from your Go module root:

```sh
go get -tool github.com/frederik-jatzkowski/go-lean/cmd/go-lean@latest
go tool go-lean setup
go tool go-lean doctor
```

Follow the [quickstart](docs/quickstart.md) to declare a law, generate Lean, write a proof, and verify it.

## Fully verified examples

| Example | Techniques |
| --- | --- |
| [Recursive expressions](examples/proven/recursive_expr/README.md) | Private enums, generated constructors, exhaustive matching, and structural recursion |
| [Stack-machine compiler](examples/proven/stack_machine_compiler/README.md) | Early-stopping folds, boxed recursion, and compiler correctness |
| [Ten-pin bowling](examples/proven/bowling/README.md) | Value-state transitions, list folds, and refinement against scoring rules |
| [Grid game](examples/proven/grid_game/README.md) | Finite step checks and induction over arbitrary move histories |
| [Nine Men’s Morris](examples/proven/nine_mens_morris/README.md) | Value methods, board scans, and agreement with game rules |
| [Clamp with an imported package](examples/proven/clamp_import/README.md) | Concrete cross-package translation and theorem reuse |
| [Assumed worker](examples/proven/assumed_worker/README.md) | Abstract calls and proofs conditional on a dependency contract |

## Documentation

- [Writing modeled Go](docs/writing-go.md)
- [Writing and checking proofs](docs/verification.md)
- [Supported Go and Lean representations](docs/supported-go.md)
- [CLI and directive reference](docs/reference.md)
- [Contributing](CONTRIBUTING.md) and [roadmap](docs/roadmap.md)

## License

Copyright © 2026 Frederik Jatzkowski. Licensed under the [GNU General Public License, version 3](LICENSE).
