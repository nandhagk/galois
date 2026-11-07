# Architecture

This document describes the target redesign. [README](../README.md) states what has landed.

## Design principles

A program presentation describes client code. A domain describes knowledge about values or
states. A framework turns a presentation and a domain into equations. A solver produces a
solution, and a certificate lets a checker validate an untrusted answer.

Computational records contain data and functions. Separate `Prop` records carry semantic links
and laws, so running an analysis requires neither semantics nor a termination proof. Dictionaries
are explicit and parametric in their types. Modules are namespaces.

Preparation interns client keys into dense `positive` IDs. Core algorithms use `Cost.t` and
provide cost theorems. Their plain functions project the costed result. Engines report explicit
outcomes such as `Solved`, `OutOfFuel` and `Rejected`.

Packages publish types, signatures and specification lemmas. Consumers use those public names
without unfolding another package's definitions. Each public theorem has a comment, and tests
cover positive, negative and boundary cases.

## Packages

Each target package is a `Galois.<Package>` Rocq theory. Arrows point to dependencies.

```text
Analyses/{Dataflow,Values,Ssa,Equality,Loops,Calls,Memory}    Float
        |                                                      |
     Framework ------------------------------------------------+
     /       \
 Program    Datalog   Egraph
    |    \     |        |
 Domains  Fixpoint -----+
    |    /    |
  Bits  Lattice   Graph
     \     |      /
        Base
         |
        Cost
```

| Package | Contents |
| --- | --- |
| `Cost` | Cost monad, loops, bounds and tactics. |
| `Base` | Keys, interning, tries, maps, sets, heaps, union-find and shared utilities. |
| `Lattice` | Orders, lattices, widening, narrowing and domain combinators. |
| `Bits` | Width-indexed words, operators and expressions. |
| `Graph` | Search, SCCs, dominance, frontiers, paths and colouring. |
| `Fixpoint` | Query trees, systems, certificates and solvers. |
| `Domains` | Value and state abstractions, transfers and memory domains. |
| `Program` | CFG, SSA, structured, call and memory presentations and semantic links. |
| `Datalog` | Stratified rules, joins and evaluation. |
| `Egraph` | Sorted rewriting, matching, bounded saturation and extraction. |
| `Framework` | Dense and sparse analyses, summaries and IFDS/IDE. |
| `Analyses/*` | Concrete analyses and specialised algorithms. |
| `Float` | Optional Flocq-based domains. |

`Analyses` contains `Dataflow`, `Values`, `Ssa`, `Equality`, `Loops`, `Calls` and `Memory`
families. `examples/` holds client programs, `tools/` holds checks and benchmarks, and
`extraction/` contains extraction clients. Tests mirror the theories under `tests/`.
Differential tests against the previous library live under `tests/legacy/`.

## Core interfaces

These interfaces are sketches of the target design. Package guides and source define landed
interfaces.

```coq
Record Cost.t (A : Type) := mk { value : A; ticks : N }.
Record lattice (A : Type) := {
  leb_c : A -> A -> Cost.t bool;
  join_c : A -> A -> Cost.t A;
  widen_c : A -> A -> Cost.t A;
  narrow_c : A -> A -> Cost.t A;
  bot : A
}.
```

Presentations carry their encodings, and separate semantic links connect program steps to
presentations. An `Analysis.t` combines a system, lattice and policy. `analyze` produces an
explicit outcome, and `certify` checks an untrusted candidate.

## Shared abstractions

The target shares a fuel driver and potential lemmas in `Cost`. `Base` supplies interning,
indexes, memo tables, interval sets, relations and certificate helpers. `Graph` shares search,
SCC hierarchy and dominance infrastructure. `Fixpoint` shares its evaluator and update rule.
`Lattice` shares combinator laws, `Bits` shares an operator table, and `Domains` shares transfer
dispatch. `Program` shares semantic completion lemmas, and `Framework` shares gen/kill and
tabulation machinery.

## Shared tactics

The target tactics have documented contracts and representative tests. Cost tactics simplify
cost projections and bounds. Map and set tactics normalise lookups and membership. Other tactics
handle key equality, option and bind cases, loop invariants, lattice order, domain soundness,
operator cases and encoding round trips.

## Migration

The previous library is tagged `pre-redesign` and is removed when the rebuilt packages replace it.

## Beyond the redesign

Possible extensions include relational numeric domains, alarms, widening control, a driver and
front end. Other possible work includes richer context policies, incremental analysis, shape
analysis and resource analysis. SSA construction and destruction require a separate scope
decision as described in [deferred scope](decisions/0011-deferred-scope.md).
