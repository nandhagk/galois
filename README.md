# Galois

Galois is a standalone Rocq library for verified program analysis. It provides common data
structures, constraint solvers, semantic views and reusable analyses without assuming a particular
compiler, graph representation, control structure or word size. It is MIT licensed.

A client supplies a graph and a sound transfer for each edge. For example, on the true edge of
`x < 10`, an interval analysis can refine an unsigned `x` to `[0, 9]`; an impossible edge produces
bottom. The library's intended solver returns a post-solution, and the view's soundness theorem
connects that result to the client's semantics. The While reference client exercises several dense
analyses; the interval example describes the intended general client API.

## Packages

The following table describes the target packages. Their interfaces are still being rebuilt.

| Package | Purpose |
| --- | --- |
| `Cost` | Cost monad, loops and bounds. |
| `Base` | Keys, collections and shared utilities. |
| `Lattice` | Orders, lattices and domain combinators. |
| `Bits` | Fixed-width words and expressions. |
| `Graph` | Graph algorithms and certificates. |
| `Fixpoint` | Constraint systems and solvers. |
| `Domains` | Value and state abstractions. |
| `Program` | Program presentations and semantic links. |
| `Datalog` | Stratified rules and evaluation. |
| `Egraph` | Equality saturation and extraction. |
| `Framework` | Reusable analysis frameworks. |
| `Analyses` | Concrete analyses and specialised algorithms. |
| `Float` | Optional floating-point domains using Flocq. |

## Build

Enter `nix develop` at the repository root and run `just build`, `just test` and `just check`.
See the [workflow](docs/workflow.md) for commands and conventions.

## Documentation

- The [architecture](docs/architecture.md) describes the target design.
- The [guarantees](docs/guarantees.md) state the proof and trust policy.
- The [workflow](docs/workflow.md) covers development and checks.
- The [decisions](docs/decisions/) record design rulings.
- The [research notes](docs/research/) record historical investigations.
- The [package guides](docs/guide/) describe landed packages.
- The [performance guide](docs/performance.md) covers measurements.
- `just doc` generates the API reference under `_build/`.
- The [references](docs/references.md) list sources.

## Status

The rebuild is in progress. A package has landed when its guide exists in `docs/guide/`.
