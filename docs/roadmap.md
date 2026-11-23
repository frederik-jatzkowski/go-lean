# Roadmap

go-lean currently checks laws over generated Lean models. A long-term goal is a semantics-preservation theorem relating supported Go executions to those models, including target integer widths and explicit assumptions about inputs and dependencies.

Broader coverage would require models and validation for additional Go operations. Each extension should cover a reusable class of programs and specify what a Lean theorem says about their Go executions. For an overview of the current scope, see [Supported Go](supported-go.md).

External APIs are another area for exploration. Today a project can use a checked concrete dependency or declare a contract on a scalar call it controls. A mechanism for external library models would need a way to state and justify the connection to the actual API. [Dependency contracts](verification.md#use-dependencies-in-a-proof)
