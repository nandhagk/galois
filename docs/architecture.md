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
families. `examples/` holds client programs, and
`extraction/` contains extraction clients. Tests mirror the theories under `tests/`.

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

Presentations carry the encodings needed by their algorithms. The separate `Link.t` relates
concrete states and steps to a presentation. Its laws belong in a separate `Prop` record.

```coq
Record Cfg.t N E := {
  graph : Graph.t N E; node_enc : encoding N; edge_enc : encoding E
}.
Record Ssa.t N E V K G := {
  cfg : Cfg.t N E; val_enc : encoding V; values : list V;
  def : V -> definition N V K; home : V -> N; params : N -> list V;
  args : E -> list V; guards : E -> list (G * list V)
}.
Record Link.t S O N E := {
  point : S -> N; taken : S -> list O -> S -> E -> Prop;
  stays : S -> list O -> S -> Prop
}.
```

The value abstraction accepts any operator language `K` and guard language `G`. `Bits` supplies
one instance. `ValueAbs.t` contains the computational operations, and `ValueSem.t` describes
their concrete interpretation. Separate laws connect the two.

```coq
Record ValueAbs.t A K G := {
  lat : lattice A; top : A; op : K -> list A -> A;
  back : K -> A -> list A -> list A; guard : G -> list A -> list A
}.
Record ValueSem.t C K G := {
  eval : K -> list C -> option C; holds : G -> list C -> Prop
}.
```

An `Analysis.t` combines a system, lattice and policy. Running it needs no semantic proof.
`analyze` reports whether a post-solution was obtained, fuel ran out or a candidate was rejected.
`certify` connects a check to its soundness proof at the acceptance boundary.

```coq
Record Policy.t X := {
  order : X -> positive; widen_at : X -> bool; delay : nat; narrowing : nat
}.
Record Analysis.t X C A := {
  key_enc : encoding X; row_enc : encoding C; lat : lattice A;
  system : System.t X C A; static : System.static system; policy : Policy.t X
}.
Parameter analyze : forall {X C A} (a : Analysis.t X C A), positive ->
  Outcome.t X A {s : X -> A | post_solution (lat a) (system a) s}.
Parameter certify : forall {W} (P : W -> Prop) (check : W -> bool),
  (forall w, check w = true -> P w) -> W -> option {w | P w}.
```

Frameworks construct an `Analysis.t`. The memory framework accepts a client-supplied alias
oracle, whose semantic laws are separate from its operations.

```coq
Record Alias.t R := {
  disjoint : R -> R -> bool; covers : R -> R -> bool; all : R
}.
```

## Shared abstractions

The target shares recurring implementations and their proofs through these package interfaces.

| Home | Shared abstraction and responsibility |
| --- | --- |
| `Cost` | `iterate` and `fix_wf` provide loop drivers, invariants and potential lemmas. |
| `Base` | `Index.group_by` and `Map.find_or` share indexing and default lookup. |
| `Base` | `Memo` supplies tables, validity invariants and agreement with a reference function. |
| `Base` | `Intern` prepares dense IDs, inverse tables and interned collections with agreement to client keys. |
| `Base` | `IntervalSet` shares interval operations; `Rel` shares paths and relational closures. |
| `Base` | `certify` and `certify_or` share checked acceptance and fallback. Derived encodings prove injectivity by round trip. |
| `Graph` | `Search` shares traversal with visitors. The SCC hierarchy supports WTO and loop projections. Dominance backends share preparation. |
| `Fixpoint` | A constraint evaluator, update rule and checker serve the solver engines. `Analysis.t`, `Policy.t` and `analyze` separate systems from scheduling. |
| `Lattice` | The combinator kit derives operations and laws. `height_on` expresses finiteness relative to an invariant. |
| `Bits` | One operator table supplies evaluation, arity, result width and codes. |
| `Domains` | A transfer harness shares arity dispatch, singleton handling, backward defaults and soundness. |
| `Program` | Presentations bundle encodings. Step-local laws and structured-language completion lemmas share semantic reasoning. |
| `Framework` | Gen/kill problems and stack-alphabet tabulation share dataflow and matched-call machinery. |

## Shared tactics

The target tactics have documented contracts, named hint databases and representative tests.

- `cost_simpl` and `bigO_solver` simplify cost projections and combine bounds.
- `simpl_map` and `simpl_set` normalise map lookups and set membership after updates and set operations.
- `set_solver` reflects membership goals to propositions and uses `intuition`.
- `inv_option` and `inv_bind` destruct option matches and costed bind chains.
- `case_key` derives equalities and disequalities from encoded-key and `eqb` tests.
- `fold_invariant` and `iterate_invariant` apply invariant lemmas and leave the step obligation.
- `order_solver` uses lattice laws and the `galois_order` database at a fixed depth.
- `gamma_solver` applies registered domain transfer-soundness lemmas.
- `op_cases` splits on the `Bits` operator table.
- `solve_roundtrip` proves decoder round trips for derived encodings.

## Migration

The previous library is tagged `pre-redesign` and is removed when the rebuilt packages replace it.

## Beyond the redesign

Possible extensions include relational numeric domains, alarms, widening control, a driver and
front end. Other possible work includes richer context policies, incremental analysis, shape
analysis and resource analysis. SSA construction and destruction require a separate scope
decision as described in [deferred scope](decisions/0011-deferred-scope.md).
