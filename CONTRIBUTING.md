# Contributing

## How you can contribute

go-lean is an early prototype and does not currently accept pull requests. Please open a [GitHub issue](https://github.com/frederik-jatzkowski/go-lean/issues) to report a potential soundness issue or translation bug, or to share feedback on the developer experience.

## Build and check the repository

Run the commands on this page from the repository root. The `go` directive in [go.mod](go.mod) sets the minimum Go version. [lean-toolchain](lean-toolchain) selects the default Lean version. With Elan on your PATH, run `lake --version` to confirm the selected version.

The repository pins Go Task as a Go tool.

```sh
go tool task build
go tool task generate
go tool task check
```

`build` builds the CLI. `generate` regenerates Lean modules from marked Go sources. `check` runs Go tests, vet, and the default Lake build. See [Taskfile.yml](Taskfile.yml) for individual tasks.

To generate and check directly:

```sh
go run ./cmd/go-lean transpile ./...
go test ./...
go vet ./...
lake build
```

## Preview the documentation site

With Python 3.12 available, install the docs dependency and run MkDocs from the repository root. These commands work in a virtual environment.

```sh
python -m pip install -r requirements-docs.txt
python -m mkdocs serve --watch README.md --watch CONTRIBUTING.md --watch LICENSE
```

MkDocs prints the local preview URL. It builds the homepage from the root README and picks up Markdown pages under `docs/` automatically. Run `python -m mkdocs build --strict` to check the production build.

### Enable GitHub Pages deployment

Set the Pages source to **GitHub Actions** in the repository settings. For a private repository, confirm **Private** site visibility is available before enabling Pages and select it before enabling deployment. Once publishing is authorized, set the repository Actions variable `DEPLOY_DOCS_PAGES` to `true`. The next push to `main` deploys the site after a strict build.

## Reproduce the toolchain checks

Run these commands with Go 1.26.0 and again with Go 1.27.1. Use a separate clean checkout for each run, put the selected Go binary first on PATH, and use the same target architecture for both runs.

```sh
export GOTOOLCHAIN=local
go version
go tool task build
go tool task generate
go test ./...
go vet ./...
git diff --exit-code -- '*.lean' lakefile.toml
```

Run the proof build and integration tests in a separate clean checkout for each Lean version. Set `ELAN_TOOLCHAIN` for the entire shell session because the integration tests invoke Lake themselves. Repeat the commands with `leanprover/lean4:v4.35.0` after checking 4.36.0.

```sh
export ELAN_TOOLCHAIN=leanprover/lean4:v4.36.0
lake --version
lake build
go test -count=1 -v ./cmd/go-lean ./internal/transpile
```

In PowerShell, replace the two `export` commands with `$env:GOTOOLCHAIN = 'local'` and `$env:ELAN_TOOLCHAIN = 'leanprover/lean4:v4.36.0'`.

## Check the clamp proof

```sh
go run ./cmd/go-lean transpile ./examples/provable/clamp
lake build clamp.clamp_verify
```

`clampBounds` states that the result lies between ordered bounds. Follow the declaration and matching theorem in the [verification guide](docs/verification.md#select-a-proof-target).

## Check the expression parser

```sh
go test ./examples/provable/expression_parser
go run ./cmd/go-lean transpile ./examples/provable/expression_parser
lake build expression_parser.expression_parser_verify
```

## Run and check the order service

```sh
go run ./examples/provable/order_service/cmd/orders
go test ./examples/provable/order_service
go run ./cmd/go-lean transpile ./examples/provable/order_service
lake build order_service.orders_verify
```

## Check the bowling example

```sh
go test ./examples/provable/bowling
go run ./cmd/go-lean transpile ./examples/provable/bowling
lake build bowling.bowling_verify
```

## Run the playable examples

```sh
go run ./examples/provable/grid_game/cmd/grid-game
go run ./examples/provable/grid_game/cmd/grid-game -wrap
go run ./examples/provable/nine_mens_morris/cmd/morris
```
