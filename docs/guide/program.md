# Program presentations

A presentation contains the syntax readers and encodings that an analysis needs.
For example, a variable presentation says which variables an edge reads and writes.
An analysis can use that presentation before its client supplies a concrete semantics.

A link maps concrete states and transitions into a presentation.
Its law record connects those observations to reachable runs.
The computational presentation contains neither the link nor its laws.
Every dictionary callback used by an algorithm has a costed `_c` field and a pure accessor.
The `of_pure` adapters treat client callbacks as primitives and charge one tick per call.
Clients with recursive readers should supply the costed fields directly.

Consumers use public operations and theorem interfaces.
They do not unfold another package's implementation.
The [Base guide](base.md#encodings-and-codecs) describes the separate encoding laws.

## Semantics and behaviours

[`semantics`](../../theories/Program/ProgramSemantics.v#L11) supplies `initial` and `step`.
Each transition emits a list of events.
`exec` concatenates those lists along a finite run.
`reachable_state` starts a finite run at an initial state.
`exec_in` additionally requires a predicate at every state, including the endpoint.
`diverges` describes an infinite sequence of transitions.

[`endings`](../../theories/Program/ProgramSemantics.v#L20) distinguishes final, trapped and
stopped states.
A stuck state has neither a transition nor a declared ending.
`endings_wf` requires declared endings to halt and be disjoint.
`same_behaviour` preserves ending tags, finite trace prefixes and diverging prefixes.
It retains the distinction between a resource stop and a stuck state.

`bisimulation` matches individual transitions and endings in both directions.
`stuttering` also permits unmatched silent transitions with decreasing natural measures.
The proved `stuttering_same_behaviour` and `bisimilar_same_behaviour` transport behaviours.
`same_behaviour_refl`, `same_behaviour_sym` and `same_behaviour_trans` give equality laws.
These theorems require the stated relations at the states being compared.
They do not require those states to be initial.

## Step-local laws

[`on_steps`](../../theories/Program/ProgramSteps.v#L11) states the common transition premises.
For a semantics `m` and predicate `P`, it means that `P s l s'` holds whenever `s` is reachable
and `step m s l s'`.
`on_steps_mono` transports pointwise implications.
`on_steps_and` conjoins laws about the same step.
`on_steps_forall` commutes an external universal quantifier with the step premises.
`reachable_step` closes reachability under a transition.
`reachable_ind` proves an invariant from initial establishment and reachable-step preservation.

`intro_step` introduces fresh names `s`, `l`, `s'`, `Hs` and `Hstep`.
It leaves the instantiated predicate to prove.
It performs no simplification or search.
The [counter fixtures](../../tests/Program/ProgramStepsTest.v#L16) use the tactic and prove the
requested reachable invariant.
They also check conjunction, monotonicity and universal quantification.

Use `on_steps` for transition clauses.
Keep state-only and unrestricted clauses on their original domains.
For example, `var_laws.no_stays` forbids stationary classifications on all transitions.
`var_laws.exits_determine` compares reachable states without requiring either state to step.
Restricting either clause to `on_steps` would lose part of the legacy contract.

## CFGs and variables

[`Cfg.t`](../../theories/Program/ProgramCfg.v#L16) packages `Graph.t`, `node_enc` and `edge_enc`.
`Cfg.edges` enumerates outgoing edges in node order and outgoing-list order.
It retains parallel edges and repeated occurrences.
`Cfg.edges_spec` characterizes membership by a listed source node and its outgoing list.
The operation is a plain preparation-time enumeration.
Frameworks should retain the enumeration when they need it repeatedly.

[`Vars.t`](../../theories/Program/ProgramCfg.v#L45) adds `var_enc`, `uses_c`, `defs_c` and
`exits_c`.
Uses are observed before the edge's definitions.
Exit uses describe observations without taking an edge.
`Vars.universe` deduplicates every edge use, definition and listed-node exit use in canonical
encoded-key order.
`Vars.universe_spec` needs `encoding_laws` for the variable dictionary.
Compute the universe once per analysis.

[`Link.t`](../../theories/Program/ProgramLink.v#L14) supplies `point`, `taken` and `stays`.
`link_laws` requires a well-formed graph, initial entry points, transition coverage, valid taken
edges and point preservation for stationary steps.
`var_laws` adds unwritten-value preservation, input-determined steps and exit-determined endings.
The comparison state in `uses_determine` must itself be reachable.
The matching transition preserves the same event list and taken edge.

## SSA and instruction points

[`Ssa.t`](../../theories/Program/ProgramSsa.v#L25) carries a CFG, a value encoding and inventory,
definitions, homes, block parameters, incoming edge arguments and client guards.
The readers have `_c` fields and pure observations `def`, `home`, `params`, `args` and `guards`.
A definition is `Op`, `Param` or `Arbitrary`.
A guard pairs a client value of type `G` with an operand list.
Program does not choose an operator or guard language.

[`SsaLink.t`](../../theories/Program/ProgramSsa.v#L62) adds a partial concrete valuation.
`ssa_laws` takes the operator evaluator and guard meaning as ordinary arguments.
It requires parameter-definition agreement, defined and satisfied guard operands, source-state
consistency of operations used by guards, constructive origins of changed bindings and coverage
by the value inventory.
`value_origin` permits a preserved binding, a computed operation, a taken-edge argument for a
parameter, or an arbitrary definition.
The operator-guard clause applies to every operand of a client guard.
It specializes to the legacy singleton-subject clause.

[`SsaPoints.t`](../../theories/Program/ProgramSsaPoints.v#L90) relates an ordered point-level
variable presentation to a block CFG.
Its costed readers supply point chains, instruction and parameter edges, owners, edge
projections, block parameters, incoming arguments and definition homes.
`SsaPoints.of_ssa` reuses the block SSA presentation's CFG and its charged parameter and argument
readers.
`ssa_point_laws` covers every block, including unreachable components.
It retains distinct incoming edges and each edge's phi operands.

`reachable_point_ssa` requires strict dominance and definition homes on reachable points.
It does not require unreachable components to satisfy those reachable-use conditions.
`syntactic_live` is the finite use-before-kill relation over `Vars.t`.
`syntactic_live_path_iff` characterizes it by a kill-free prefix ending at an exit or edge use.
The terminal use edge is outside the prefix and may define the same value.

## Structured skeletons

[`Skeleton.stmt`](../../theories/Program/ProgramSkeleton.v#L15) has atoms, sequences,
conditionals, blocks, loops, jumps, conditional jumps and jump tables.
Positions are root-outward lists of directions.
`sub` rejects missing children.
`positions_exact` proves that preorder enumeration has no duplicates and contains every valid
position.
`labels_ok` checks every relative label against its enclosing block and loop depth.
Repeated jump-table labels remain distinct alternatives.
Missing labels produce no taken graph edge.

[`skeleton_client`](../../theories/Program/ProgramSkeletonMachine.v#L12) supplies atom events,
traps, stops, partial guard results and jump store effects.
The continuation machine retains explicit sequence, join, block and loop frames.
`skeleton_client_laws` requires atom progress, disjoint halting trap and stop outcomes, and total
jump effects.
`skeleton_endings_wf` requires those client laws.
`skeleton_not_stuck` additionally requires successful root label validation and reachability.
It makes no progress claim for arbitrary malformed machine states.
`skeleton_machine C prog` is the client-first constructor.
The legacy-order `skeleton_semantics prog C` remains available.

[`skeleton_cfg`](../../theories/Program/ProgramSkeletonCfg.v#L648) provides entry and exit
points and source/slot edge keys.
`skel_action` records atom, boolean guard, exact index, default index and jump observations.
`acts_hold` composes their semantic effects.
`skel_acts` observes the actions at a slot.
An absent slot targets its source and has no actions.
An absent point has no outgoing keys.

`skeleton_index` prepares syntax rows once.
Each row retains its position, subtree, canonical stack and entry/exit ranks.
The traversal returns its next rank, so a second child starts after the first child's span.
It never recomputes subtree measures inside a graph callback.
`syntax_rows_context` proves retained subtrees and stacks agree with their source positions.
`syntax_rows_span` proves the counter consumes the statement's specified span.
`prepared_rows_agree` connects all outgoing rows to the reference `skel_out` selector.
`indexed_positions_exact` proves that cached positions equal the complete syntax enumeration.
`prepared_skeleton_wf` establishes all map invariants internally.

Graph callbacks close over the prepared outgoing and payload maps.
The index also stores an optional point-rank lookup and the total span.
Unrecognized rank keys return `None`.
Direction, position, point and edge encodings use Base's charged derivation and pullback
operations.
Their injectivity proofs live in separate theorems.

Preparation charges syntax visits, path copying, label-stack traversal, table alternatives,
list construction and map operations.
The current maps are reference implementations.
No asymptotic preparation bound or extraction timing claim is made here.
Forward analysis, structured simulation and cycle-cut theorems belong to the later Program
theory card.

## Calls and interprocedural graphs

[`Calls.t`](../../theories/Program/ProgramCalls.v#L39) contains functions, roots, costed site,
caller and resolver readers, and function and site encodings.
`Calls.graph` preserves function-site and resolver-list order.
Its edge encoding retains both site and target identity.
`call_graph_wf` takes explicit inventory closure and distinct-node premises.
It does not infer resolver completeness from a concrete execution.

`CallsLink.t` exposes the current function and suspended callers in innermost-first order.
`Calls.active` lists the current function followed by the suspended callers.
`calls_laws` requires initial roots, listed active functions and stay, push or pop step shapes.
`reachable_frames_linked` proves that resolver links persist in reachable stacks.
`active_reachable_in_call_graph` proves that every active reachable function is graph-reachable.

[`Icfg.t`](../../theories/Program/ProgramIcfg.v#L25) adds a site encoding and charged kind reader
to a CFG.
`Icfg.kind` is the type with `Internal`, `Call` and `Return` constructors.
The pure kind accessor is `Icfg.edge_kind` because a namespace cannot give the type and
accessor the same name.
`IcfgLink.t` supplies the concrete call-site stack.
`icfg_laws` requires initial empty stacks, kind-directed changes on taken edges and unchanged
stacks on stationary transitions.
Returns require the matching site at the stack top.

## Effects and memory

[`Effects.t`](../../theories/Program/ProgramEffects.v#L14) carries charged flags for reads,
writes, traps, divergence, stops, allocation, freeing, calls and observations.
`EffectsLink.t` supplies the concrete instruction, heap image, heap agreement relation and depth.
`effects_laws` retains the legacy transition, ending and comparison-state domains.
`silent_exec_in` proves that a restricted run through non-observing instructions emits no events.

[`Alias.t`](../../theories/Program/ProgramMemory.v#L16) supplies charged disjointness and
coverage queries and an all-memory region.
`alias_laws` states soundness of true answers and fullness of the all-memory region.
It makes no completeness or symmetry demand on the oracle.
`Memory.t` adds a region encoding and an ordered effect list per edge.
Effects distinguish `Read`, `Write`, `ReadWrite`, `Call` and `Barrier`.
Read and write projections return region lists so absence needs no empty-region oracle.
`Memory.barrier_read_write` proves that a barrier has the same projections as an all-memory
read/write effect and counts as a definition.
It makes no sequential decomposition claim about an arbitrary client's effect-step relation.

`MemoryLink.t` supplies snapshots, stable historical addresses, cell observations, region
membership, individual effect steps and actual reads.
`memory_laws` requires one shared snapshot trace for all reads of a taken edge.
It preserves historical addresses and covers changes to existing addresses by that trace's writes.
The changed-cell theorems take an explicit decision procedure for cell equality.
They do not use classical logic.
An instance can choose cells to be bytes and stable addresses to be allocation-site/offset pairs.
The byte and pointer models belong to Domains.

## Validation

The [CFG fixtures](../../tests/Program/ProgramCfgTest.v#L15) cover a three-node graph, a
self-loop, an empty graph, variable deduplication, open SSA guards, point adapters, resolver
edges, interprocedural kinds, effect flags and memory projections.
They also observe primitive callback charges.
The [skeleton fixtures](../../tests/Program/ProgramSkeletonTest.v#L15) cover all statement
constructors, good and bad labels, invalid points and slots, cached positions and ranks, and
machine resume and ending observations.
The [differential suite](../../tests/legacy/Program/ProgramSkeletonLegacyTest.v#L61) compares
ordered endpoints, edge counts and label checks with the legacy implementation.
These computed examples complement the generic theorems.
They do not establish the later forward or cut theory.
