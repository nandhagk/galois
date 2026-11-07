# E-graphs

`Galois.Egraph` represents sorted finite terms in equivalence classes. A class can
contain several nodes and can refer to itself. Its meaning comes from finite
derivations of `EggSpec.represents`. A class containing `a` and `f(a)` can represent
`a`, `f(a)` and `f(f(a))`.

## Languages and rules

A client builds an `EggAlg.t K Sort V` from operator, sort and variable types. The
record carries an injective encoding for each type, a costed variable declaration
lookup and a costed operator-shape check. `EggAlg.of_pure` lifts primitive callbacks.
Callbacks that traverse client data must charge that work in their costed fields.
`EggSpec.encoding_laws` holds the injectivity proofs separately from the executable
record.

`EggTerm.Var s v` and `EggTerm.App s op args` carry result-sort annotations.
`EggTerm.typed` checks the annotations against the algebra. Patterns add
`EggPattern.Hole s h`. An `EggSubst.t` is a costed partial hole lookup.
`EggSubst.instantiate` returns `None` when a required hole is absent.
`EggSubst.instantiate_typed` proves that a typed substitution instantiates a typed
pattern to a typed term of the annotated sort.

A client gives partial interpretations through `EggSem.t`. Variable lookup and
operator evaluation return `option C`. Evaluation is strict and proceeds from left
to right. `EggSem.equiv` compares the complete result in every admissible
interpretation, including `None`.

`EggFact.t` gives facts a meaning over `option C` and supplies a costed ground
checker. The separate `EggFact.laws` record requires a successful check to imply
validity in every admissible interpretation. A fact can require definedness by
rejecting `None` in its `holds` predicate.

An `EggRule.t` carries a hole encoding and declares holes, their sorts, two patterns
and a costed guard. `EggRule.encoding_laws` supplies the separate hole-encoding
injectivity condition needed by class-substitution maps.
The runtime guard has type `(H -> Cost.t F) -> Cost.t bool`, so each actual fact
read can retain a map or substitution lookup's cost. The pure guard has type
`(H -> F) -> bool` and supplies `Cost.ret`-valued lookups.
The separate `EggRule.guard_laws` record requires runtime values to agree with the
pure guard on returned facts. `EggRule.guard_agrees` supplies that bridge to runner
and explanation proofs. Semantic rule soundness continues to use the pure guard.
`EggRule.wf` requires typed sides of the same sort.
`EggRule.sound` requires valid facts and a true guard to justify an instantiated
equality. `EggEqual.rel` closes those instances under reflexivity, symmetry,
transitivity and application congruence. `EggEqual.sound` proves partial semantic
equivalence from sound rules. `EggEqual.typed` proves sort and typing preservation
from well-formed rules.

## Graph operations

`Egraph.empty` allocates no identifiers. `Egraph.add_node` checks a local node,
canonicalizes its children and looks up its encoded signature in the memo table.
A miss allocates the next positive identifier. `Egraph.add_term` inserts a finite
term bottom-up. Both operations return `None` when a declaration, child lookup or
shape check fails.

`Egraph.find` returns a class representative. Base's unknown-key convention makes
an unknown identifier its own representative. `Egraph.sort_of` returns `None` for
an unallocated identifier. The bound in `EggSpec.find_wf` therefore requires a
successful sort lookup.

`Egraph.union` rejects unknown identifiers and different sorts. A successful union
keeps the memo table, so historical keys can become stale.
`Egraph.rebuild` rescans canonical signatures and merges congruent classes.
The reference implementation charges full scans. It makes no deferred-kernel
complexity claim. Each operation has a `_c` form whose `Cost.value` is the plain
operation. List traversals, encoding callbacks and Base operations retain their
charges.

Clients use graph operations and `EggSpec` laws. They do not inspect state fields.
`EggSpec.wf` includes Base forest and map invariants, local typing and finite-term
witnesses for allocated classes. A dirty memo entry denotes a class through a
stored-node witness. The representative's own node can have different syntax.
`EggSpec.clean` additionally requires congruence closure and a current complete
memo index.

`EggSpec.sound` requires every pair of terms represented in one class to be
related by `EggEqual.rel`. A client must justify a union by a genuine relation
between its old classes and must establish old soundness. The structural union
operation itself needs no semantics or proof argument.

`EggInsertSpec.add_node_sound` and `EggInsertSpec.add_term_sound` prove that
successful insertion preserves soundness from old WF, old soundness and encoding
laws. The allocation proof retracts output representations at old identifiers to
their old finite terms. Terms at the fresh class come from its new node and old
child classes. The insertion laws require no post-state soundness premise.

## Scope

The reference package supplies syntax, guarded equality and graph operations.
Matching, saturation limits, class analyses, extraction and explanation certificates
belong to later cards. Tree extraction and shared-DAG extraction have different
objectives. An optimal finite tree does not imply an optimal shared DAG.
