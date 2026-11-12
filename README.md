# Galois

Galois is a Rocq library for verified program analyses. The library is being rebuilt around
module signatures, implementations and explicit time contracts.

The [design documents](docs/design/) describe the components, their interfaces and their
costs. [Agent instructions](AGENTS.md) state the design invariants and development commands.
The [guarantees](docs/guarantees.md) record the proof and trust policy.

Enter `nix develop` at the repository root and use `just` for builds and checks. The
[workflow](docs/workflow.md) points to the commands and session rules.
