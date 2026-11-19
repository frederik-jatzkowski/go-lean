// Package golean bundles the files installed by the go-lean CLI.
package golean

import _ "embed"

//go:embed lean-toolchain
var LeanToolchain string

//go:embed .agents/skills/go-lean/SKILL.md
var Skill string
