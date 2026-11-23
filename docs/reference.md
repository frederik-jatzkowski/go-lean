# CLI and directive reference

Run from the Go module root. In a checkout of go-lean, replace `go tool go-lean` with `go run ./cmd/go-lean`.

| Command | Result |
| --- | --- |
| `go tool go-lean setup` | Initialize the Lean workspace, preserving existing configuration. |
| `go tool go-lean doctor` | Check workspace and toolchain prerequisites. |
| `go tool go-lean transpile ./pkg` | Generate the selected package's Lean files and enum Go artifacts, including modeled dependencies. |
| `go tool go-lean transpile ./...` | Generate across the module and reconcile managed artifacts. |
| `go tool go-lean verify ./pkg` | Generate and check the selected package. |
| `go tool go-lean verify` | Generate and check the workspace. |

Package selectors include `.`, `./pkg`, `./pkg/...`, and `./...`. See [Writing and checking proofs](verification.md) for Lake configuration and troubleshooting.

## Go directives

Use the exact `//golean:` prefix in Go doc comments.

| Directive | Purpose |
| --- | --- |
| `//golean:export` | Select the package and allow concrete calls to the marked operation. Private functions in enum packages receive a checked public Go entry point. |
| `//golean:verify name : proposition` | Select the package and declare a package-unique law. |
| `//golean:verify+ continuation` | Continue a law on consecutive lines. |
| `//golean:verify:import Lean.Module` | Import one Lean module from a package doc comment. |
| `//golean:generate:enum expr { constant, add }` | Select the package and generate an enum from private, package-local variant structs. |
| `//golean:generate:enum+ continuation` | Continue an enum directive on consecutive lines. |
| `//golean:assume name : proposition` | Declare a law about a scalar dependency function. Use its unqualified Go name in the law. |
| `//golean:assume+ continuation` | Continue a dependency law on consecutive lines. |
| `//golean:abstract alias.Function` | Replace an explicitly named direct call from a verified root with a contract parameter. A local function can use an unqualified name. |
| `//golean:termination:by measure` | Supply a Lean `Nat` measure over a recursive function's entry parameters. |

## Generated files and proofs

| File | Contents |
| --- | --- |
| `lean.gen.go` | Generated Go constructors, matchers, and checked entry points for packages that declare enums. |
| `<stem>.lean` | Generated model and `Laws` propositions. |
| `<stem>_proofs.lean` | Handwritten proofs, initially scaffolded by generation. |
| `<stem>_verify.lean` | Generated theorem checks and `Checked` exports. |
