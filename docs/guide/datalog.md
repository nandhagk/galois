# Datalog

`Galois.Datalog` evaluates finite stratified rules through compiled `Fixpoint` systems.
A client supplies predicate keys, arities, rules, ground facts and positive fuel.
For example, a path rule can extend a reachable pair through an edge.
`tests/Datalog/DatalogSolveTest.v` contains executable clients.

## Syntax and levels

`DatalogSyntax` defines constants as `positive` and tuples as lists of constants.
Terms are variables or constants.
Rules contain a head and an ordered list of positive or negative atoms.
`program` carries `penc`, `arity_c` and `rules`.
`arity` observes the value returned by `arity_c`.
`safe_rule` requires every head variable and negative variable to occur in a positive atom.
`program_wf` adds the declared arities of all source atoms and facts.

`DatalogStratify.stratify` raises predicate levels along literal dependencies.
Positive dependencies allow equal levels.
Negative dependencies require a strictly lower body level.
The reference loop uses a natural budget of `n * n + 1`, where `n` counts predicate occurrences.
`stratify_sound` requires no encoding law.
`stratify_complete` takes `encoding_laws (penc prog)` separately.

## Relations and compiled systems

`DatalogRelation.relation` is the public valid finite-set carrier `set_t tuple_encoding`.
Its representation certificate concerns set validity.
Program semantics and predicate-key injectivity stay outside the runtime data.
The relation lattice uses inclusion and union.
`relation_height_on U` uses cardinality rank, universe-list length as its bound and
`within_set tuple_encoding U` as its invariant.
The proof-only `universe prog facts` contains tuples over source constants at source head or
fact lengths.
The executable solver never enumerates this universe.

`DatalogFire.fire_rule_c` uses nested loops over positive atoms in source order.
Bindings check tuple length, repeated variables and constants.
Negative literals test the supplied immutable lower relations after positive matching.
`fire_rule_sound` needs no safety premise.
`fire_rule_exact` requires `safe_rule`.
Standalone firing accepts arbitrary environment constants.
`fire_rule_support` proves source-universe support when the input relations have that support.
This replaces the legacy firing function's unconditional head-universe filter.

`DatalogCompile.stratum_system` creates rule-position constraints and fact-predicate constraints.
`Constraint.FromRule` retains the head predicate so an invalid position still has a total target.
Queries use costed `ask_all` continuations for same-level positives.
Lower positives and negatives read the fixed completed database.
`stratum_static` has computational callbacks and separate `stratum_static_laws`.
`stratum_analysis_laws` supplies key, row, lattice and summary laws.
`DatalogExact.stratum_least_is_derives` connects least solutions to source derivations.

## Models, outcomes and fuel

`DatalogModel.derives` inductively closes one stratum over completed lower levels.
`model_below` combines completed strata and `perfect_model` completes the stratification.
`least_model` selects the empty predicate when stratification fails.
This convention does not assert that the empty predicate satisfies an unstratifiable program.

`DatalogSolve.solve_program` takes program data, facts and positive fuel.
Each stratum uses `Policy.flat` and certified `analyze_ref`.
This reference entry point stays fixed when generic `analyze` selects a later engine.
The current reference solver uses binary fuel to count joining rounds.
A final stationary round is required.
The outcomes have distinct meanings.

- `Solved db` carries the database.
- `OutOfFuel have` carries the unchecked assignment of the interrupted stratum.
  Completed lower strata are absent from this local assignment.
- `Rejected Bad_stratification` reports failed stratification.
  Other rejection reasons propagate from analysis.

`DatalogSolveProof.solve_program_exact` takes separate predicate-encoding laws and `program_wf`.
A solved database then represents `least_model` at every predicate and tuple.
`solve_program_adequate` takes these premises and a source stratification.
It proves that every fuel above a finite threshold returns `Solved`.
`program_capacity` bounds the number of constraints times the universe height.
Runtime evaluation requires none of these proof inputs.

The predicate-encoding premise matters even for empty rule lists.
The aliasing test gives both boolean predicates the same code and supplies a nullary fact for
`false`.
The keyed database then also reports the fact at `true`.
The source model distinguishes the predicates.
The lawful boolean encoding provides the discriminating control.

## Reference costs and compatibility

The `analyze_ref` result exposes a pure lookup function.
The reference Datalog solver repeats the public reference run after successful certification to
recover a map whose lookups retain their costs during database storage.
`solved_stratum_least` derives leastness from public reference reachability and soundness.
`DatalogPipelineCost` retains the charges of both runs.
The second callback adds an invocation tick after successful certification.
Exhaustion and rejection skip that invocation and its work.
A public map-valued certified reference entry point would remove this repeated work.
The public `analyze_ref_accepts` theorem connects a sound raw reference result to certification.

The source-order fixtures observe repeated same-level query reads around fixed lower literals.
They also compare raw binding lists from two independent multirow atoms.
Reversing those atoms changes binding enumeration order while final relation sets agree.

`DatalogCost` bounds nested-loop firing using local callback budgets and candidate counts.
The bounds retain full environment, enumeration, negative-test, instantiation and set-construction
costs.
They make no optimal-join claim.
The optimized join and semi-naive engine belong to `DLOG-ENGINE`.

The legacy comparison tests compute whole relations with the bounded legacy solver.
`bounded_legacy_is_reference` connects successful bounded runs to the total legacy reference
under legacy well-formedness and stratification.
The recursive fixture instantiates that connection.
A direct VM reduction of the legacy total solver exceeded the worker's command deadline.
