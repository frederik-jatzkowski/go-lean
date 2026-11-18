.DEFAULT_GOAL := build

GO ?= go
LAKE ?= lake

ifeq ($(OS),Windows_NT)
CLI := go-lean.exe
else
CLI := go-lean
endif

.PHONY: build generate test vet fmt prove check clean

build:
	$(GO) build -o $(CLI) ./cmd/go-lean

generate:
	$(GO) run ./cmd/go-lean transpile ./...

test:
	$(GO) test ./...

vet:
	$(GO) vet ./...

fmt:
	$(GO) fmt ./...

prove:
	$(LAKE) build

check: test vet prove

clean:
	$(LAKE) clean
ifeq ($(OS),Windows_NT)
	powershell -NoProfile -Command "if (Test-Path -LiteralPath '$(CLI)' -PathType Leaf) { Remove-Item -LiteralPath '$(CLI)' -ErrorAction Stop }"
else
	$(RM) $(CLI)
endif
