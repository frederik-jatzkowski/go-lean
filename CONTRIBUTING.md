# Working in the go-lean checkout

Run the commands on this page from the repository root. Use the Go version in [go.mod](go.mod) and the Lean version in [lean-toolchain](lean-toolchain). With Elan on your PATH, run `lake --version` to check that it can load the selected toolchain.

## Build and check the repository

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
