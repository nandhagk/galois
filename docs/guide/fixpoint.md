# Constraint systems and certified analysis

A query returns a value, reads unknowns and emits side contributions.
[`Query.t`](../../theories/Fixpoint/FixpointQuery.v#L14) exposes these operations as
`Ret`, `Ask` and `Side`.
For example, `Ask x` can read a value and contribute it to another unknown through `Side`.
An `Ask` continuation returns `Cost.t`, so constructing the selected query retains transfer costs.
`Query.run_c` charges each node, each lookup invocation and each continuation invocation.
Its trace keeps the order and repetitions of reads and sides.
`query_determined` proves that agreement on the actual reads determines all observations.

A [`System.t`](../../theories/Fixpoint/FixpointSystem.v#L16) lists constraints and supplies
costed target and right-hand-side callbacks.
`System.static` supplies costed lists of possible reads and side targets.
`System.static_laws` separately proves that those lists cover every dynamic trace.
Computing an analysis requires neither these laws nor a termination proof.
`lookup_c` interprets absent map entries as lattice bottom.
Map well-formedness and encoding injectivity are explicit proof premises.

[`Eval.outputs_c`](../../theories/Fixpoint/FixpointEval.v#L17) evaluates a constraint once.
It places the primary output before the ordered side contributions and also returns the reads.
Every engine uses this evaluator.
[`Update.rule_c`](../../theories/Fixpoint/FixpointEval.v#L67) compares an output with the current
value, skips a bounded output and otherwise calls its costed operator and writes the map.
`Update.apply_c` applies this rule in trace order.
Repeated side targets therefore see earlier updates from the same evaluation.
Prepared indexes deduplicate each constraint's declared keys.
Repeated constraint occurrences stay in their buckets.
Partial checking deduplicates row visits through the row encoding.

The certificates have different scopes.

- `check_post_c` checks every listed constraint and every output.
  `check_post_iff` reflects the full post-solution property without lattice or summary laws.
- `check_partial_c` checks indexed contributors of an explored set.
  It requires every dynamic read to lie in that set and checks outputs whose destinations lie
  in the set.
  `check_partial_correct` assumes lawful encodings, a lawful index and a well-formed explored set.
- `expand_c` starts from the stored cut values and reconstructs planned unknowns.
  It rejects repeated or overlapping plan keys, uncovered outputs and reads ordered after their
  consumers.
  An input with no contributors is ready at bottom.
  Expansion independently runs the full checker after reconstruction.
  `expand_sound` proves a full post-solution and exact preservation of stored cut values.
  Entries stored outside the cuts are ignored.

The full-check cost bound sums evaluator work and lookup and lattice-comparison work for each
output, including invocation overhead.
Partial-check costs add distinct-row preparation and one check per visited row.
Cut expansion adds plan validation, cut seeding and reconstruction to full-check costs.
These are bounds for the charged definitions.
They do not assert native running times or trie bounds for the reference list maps.

[`Outcome.t`](../../theories/Fixpoint/FixpointSolver.v#L29) makes failure observable.
`Solved` contains a result.
`OutOfFuel` contains an unchecked reached assignment.
`Rejected` contains a `Reason.t`, including `Check_failed`.
`Solver.t` contains the computational runner alone.
Its separate `Solver.laws` establishes soundness of solved candidates and reachability of joining
candidates from bottom.
`analyze_with` accepts any computational solver and independently certifies its candidate.
A producer needs no solver-law proof to run, so a wrong candidate can be tested and rejected.

[`analyze_ref`](../../theories/Fixpoint/FixpointAnalyze.v#L16) runs the reference round-robin
joining engine and certifies its answer.
`analyze` currently uses the same engine.
Fuel counts complete constraint-list rounds through the binary `iterate` driver.
The engine stops after a round whose update flags are all false.
This reference engine always joins and ignores scheduling, widening and narrowing requests.
Later engines consume those policy fields.

`Terminates.t` supplies an invariant, an invariant-relative bounded height, bottom and join
closure, and preservation of the invariant by query outputs.
`kleene_fuel_adequate` proves that fuel exceeding total declared output rank capacity suffices.
The support counts declared output occurrences, so duplicates give a conservative bound.
`reference_fuel` adds a final probe to that capacity.
`solve` computes this fuel and returns a certified result.
Its proof inputs are separate from the computational `analyze` interface.
`analyze_least` and `solve_least` additionally require least joins and monotone queries.
Least solutions agree up to preorder equivalence.

Widening engines need their own termination arguments.
A widening rank alone does not bound propagation around a cycle.
The widening worklist bound also depends on paths avoiding widening points and can be exponential.
The worklist guide extension will supply that bound and its scheduling premises.

The checked fixtures in
[`tests/Fixpoint`](../../tests/Fixpoint/FixpointAnalyzeTest.v#L27) cover the cycle, repeated
side targets, empty systems, exhausted fuel, total solving and rejection of a bad solver.
The differential tests compare the reference results with the legacy total solver on the
empty and joining-cycle fixtures.
The unbounded numeric fixture also checks the strategy difference.
The joining reference run exhausts its fuel, while the legacy widening total solver finishes.
