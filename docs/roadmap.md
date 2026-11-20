# Roadmap

The long-term goal is to establish that translation preserves Go's returned values and modeled panic outcomes for supported programs under explicit input and dependency assumptions. Today, Lean checks laws against the generated model. Applying those laws to Go execution still relies on the correctness of the translation.

## Translation and proof coverage

- **Semantics preservation.** Specify the Go behavior covered by the translator and relate it to the generated Lean definitions. Include target-dependent integer widths, value and aliasing assumptions, and the points at which modeled panics propagate.
- **Termination and panic reasoning.** Generalize beyond recognized bounded loops and structural recursion patterns by supporting additional decreasing measures. Use facts from guards and preconditions to discharge more obligations for division, indexing, and dereference. The current subset already models those panic outcomes and handles some guarded operations as total. [Current result and panic model](supported-go.md#data-types-and-results)

## Go and library boundaries

- **Sentinel error identity.** Extend the current support for nil and boxed zero-field error types to cover returning, forwarding, and comparing selected package-level sentinel values.
- **User-supplied library models.** Allow users to attach Lean models and explicit contracts to external APIs they cannot modify. Concrete call abstraction and named-interface contracts already let users verify callers against declared laws. A library model mechanism would extend that approach to APIs that lack project-owned declarations or wrappers. The actual library would still need to satisfy the model. [Current dependency contracts](verification.md#model-a-dependency)

## Longer-term concurrency research

Investigate whether restricted classes such as deterministic fan-out and fan-in can use a sequential model once race freedom, determinism, and equivalence have been established. General channel communication would need a model of scheduling and communication. State scheduler assumptions for any deadlock-freedom or liveness claims. The current effect traces record classified calls in sequential order.
