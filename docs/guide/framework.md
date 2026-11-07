# Framework generators

Framework turns computational program presentations and domain dictionaries into
`Analysis.t` values. `analyze` takes one of these values and positive fuel. It returns a
certified `Solved` result, an unchecked `OutOfFuel` map or an explicit `Rejected` reason.
No generator takes a semantics, semantic link, value-law record or termination proof.

The interfaces and fixture computations are available in this stage. Later framework cards
own the connections from post-solutions to concrete program runs. A successful fixture
does not establish those later soundness theorems.

## Dense forward and backward problems

[`Dense.t`](../../theories/Framework/FrameworkDense.v#L47) contains a CFG, direction, lattice,
optional boundary reader and edge transfer. The readers are `boundary_c` and `transfer_c`.
The pure `boundary` and `transfer` accessors observe their values. `Dense.of_pure` adapts
primitive client callbacks.

`Dense.system` emits seeds before flows. Forward seeds follow `Graph.entries`. Backward
seeds follow **every listed node**, including unreachable and nonterminal nodes. This
retains the legacy observation boundary. An instance that wants terminal-only seeds returns
`None` at other nodes. Flow rows follow node order and each outgoing edge's occurrence order.
Parallel edges and duplicates survive preparation.

`Dense.post_solution_iff` takes weak lattice laws. It characterizes the optional boundary
inequalities on `Dense.seeds` and the transfer inequalities on listed edges. A `None` seed
contributes bottom. Boundaries at unlisted seed nodes impose no inequality. An unrestricted
boundary theorem would be false on a singleton CFG whose boundary mentions another node.

`Dense.analysis D policy` accepts a computational policy. `Dense.static_laws` proves exact
read coverage and absence of sides. `Dense.analysis_laws` combines that fact with node/edge
encoding laws and weak lattice laws. Forward and backward diamond, loop, singleton, absent
boundary and exhausted-fuel observations are in
[`FrameworkDenseTest.v`](../../tests/Framework/FrameworkDenseTest.v#L1).

## Prepared may and must gen/kill

[`Bitvector.t`](../../theories/Framework/FrameworkBitvector.v#L20) supplies fact encoding,
universe support, direction and costed gen, kill and boundary lists. `prepare_c` enumerates
edges once, groups edge/fact occurrences through `Index.group_by_c` and builds valid sets.
Its pure accessor is `prepare`. Prepared boundaries are node-keyed maps.

A transfer reads two prepared maps and computes `(input \ kill) union gen`. It never
rescans the universe, rebuilds gen/kill lists or re-encodes composite syntax. Missing edge
buckets are empty. `prepare_sets_equation` and `prepare_sets_lookup` connect the maps to
stable grouped source occurrences. `prepare_gen_mem` and `prepare_kill_mem` prove source
membership agreement on listed edges under edge-encoding laws.
`may_transfer_raw` exposes the difference/union equation.

`may_analysis` uses `set_t (fact_enc P)` and the library may lattice.
`must_analysis` uses `must_t (fact_enc P)` and the library must lattice. Must `All` is fresh
unreachable bottom. A transfer preserves `All`. Reached `Only` sets use the same gen/kill
expression, and the must join intersects them. Universe lists are support and height data.
They do not enumerate either runtime carrier and do not become lattice-law inputs.

`may_post_iff` and `must_post_iff` need fact-encoding injectivity and state the prepared
boundary and gen/kill inequalities. They reuse the collection laws. This package proves
no second set-lattice law.

The guide's liveness constructor is compiled in
[`FrameworkBitvectorTest.v`](../../tests/Framework/FrameworkBitvectorTest.v#L34).

```coq
Definition liveness {N E X} (P : Vars.t N E X) :=
  Bitvector.may_analysis
    (Bitvector.Make (Vars.cfg P) (Vars.var_enc P) (Vars.universe P) Backward
      (Vars.uses_c P) (Vars.defs_c P)
      (fun n => Cost.map Some (Vars.exits_c P n))).
```

This prepares variable support once and preserves exit observations at every node.
The fixtures run loop liveness, reaching definitions and diamond availability. Legacy
comparisons include the unreachable component and nonterminal exit observations of the
legacy diamond. May comparisons observe membership at each coordinate. Must comparisons
observe membership inside the declared universe, interpreting fresh `All` universally.
They do not assert representation equality between the new and legacy must carriers.

## State-domain action lists

[`Env.t`](../../theories/Framework/FrameworkEnv.v#L30) contains a CFG, variable encoding and
costed action lists. `Env.action` has `Assign`, `Havoc` and `Assume`. Terms and guards belong
to the client. The generator imports no Bits vocabulary.

`Env.apply_actions_c D actions state` folds a `StateAbs.t` dictionary from left to right.
Every action observes the state returned by its predecessor. The
`apply_actions_left_fold` theorem states that order through the pure StateAbs operations.
The state dictionary owns term evaluation and assumption refinement.

`env_analysis P D entry` uses code scheduling. `Env.analysis P D entry policy` accepts a
custom policy. Both prepare each edge's action list once and seed the supplied state at
forward entries. The interval counter fixture uses assignment, infeasible assumptions,
havoc and an empty action list. Reversing assignment and assumption changes its result.

The fixture requests a loop widening point and one narrowing round. The landed reference
solver always joins and ignores scheduling, widening and narrowing requests. The bounded
counter fixture reaches its interval hull through joining. It does not test an implemented
narrowing pass. The later solver cards own that behavior.

## Sparse SSA values and client guards

[`Sparse.t`](../../theories/Framework/FrameworkSparse.v#L92) contains an SSA presentation,
`ValueAbs.t` and charged entry-argument facts. `sparse_analysis P entry` shares `option A`
across `UVal`, `UEdge` and `UBlock`. Fresh `None` is unreachable. Reached block and edge
facts use the domain's plain top value.

Preparation retains the seven legacy row kinds. All graph-entry block rows precede value
rows in `Ssa.values` order. Each edge then emits `CEdge`, `CBlock` and increasing `CArg`
slots. Invalid parameter slots contribute `None` at the edge unknown. The `entry` argument
supplies a total fallback target for unlisted row lookup. It does not replace the graph's
entry inventory. Valid generated rows are independent of this fallback.

Preparation reads definitions, parameters, arguments, endpoints and guard syntax once.
Each guard plan retains its operands and their immediate operation definitions. Fixed-read
row plans retain the query keys. Runtime rows collect their selected facts, apply each
client guard to the **stored operand facts**, and run `ValueAbs.back_c` one operation level
backward. Ordered guards thread a changing map. Repeated operand updates retain the first
refined occurrence. Static summaries contain all prepared reads and no sides.

`Sparse.static_laws` needs no value-law input. The numeric fixture pins the full tiny row
list in `sparse_rows_exact`, computes one-plus-one, rejects the equal-zero edge and checks a
hand-written candidate. Stored-subject truth, unknown width, comparison and truncation
regressions are in
[`FrameworkSparseTest.v`](../../tests/Framework/FrameworkSparseTest.v#L56).
Later sparse cards own semantic preservation and dominating-guard theorems.

## Region folds and position tables

[`Region.algebra`](../../theories/Framework/FrameworkRegion.v#L17) supplies one charged
operation per skeleton constructor. `Region.fold_c` performs the bottom-up fold.
`fold_equation` states its constructor equations.

`Region.visit_c` traverses the syntax once and returns the root result and preorder subtree
rows. It prefixes retained relative positions and charges those list traversals.
`Region.table_c` builds a position-keyed map from those retained rows.
`Region.table_get_spec` proves that `sub s p = Some s'` implies a lookup of
`Some (Region.fold alg s')`. It needs no semantic algebra laws.

The table algorithm does not recompute the fold at each position. Position copying and
reference map construction can still have superlinear aggregate cost. No linear native
time claim is made. The fixtures cover all constructors, a missing position, a root-only
leaf and a leaf visit charge. A loop algebra supplies its own loop summary computation.
The region fold itself has no solver.

## Function summaries and context policies

[`Summary.spec`](../../theories/Framework/FrameworkSummary.v#L78) supplies a lattice,
`local_c` and `via_call_c`. `summary_analysis` has one unknown per function. Its local rows
precede call rows in function, site and resolver-target order. Preparation retains caller
lookups and compiled row plans. Hot rows do not invoke the resolver.

`Ctx.t` supplies an encoding, finite context inventory, initial context and optional
call-entry callback. `Ctx.insensitive` has the single unit context.
`Ctx.call_string k calls` prepares site strings of length at most `k` and truncates pushes
to the innermost `k` sites. `ctx_summary_analysis` emits context-major rows.
Local summaries are available in every listed context. A rejected `enter` contributes
bottom and reads no callee. Coverage and closure of a client's context inventory are
separate obligations for later soundness.

`summary_policy_scc` prepares a reflexive Floyd call-graph closure. Priority is the
reachable-set cardinality plus one. For a closed call inventory, a callee in another SCC
has a smaller priority than its caller.
The first member in canonical set-code order of each component is its widening head.
Unlisted functions use their code priority and are not widening points. The policy does
not certify a solver result or select a fallback solver.

The fixtures run a recursive pair, a two-site call string, a zero context bound, rejected
entry and an empty function inventory. They pin row order and both SCC-head observations.
Later summary cards own the call-coverage and scheduling theorems.

## Matched stacks and IFDS dictionaries

[`Stack.step`](../../theories/Framework/FrameworkStack.v#L19) requires a listed edge and an
actual exploded-flow alternative. Internal edges preserve the stack. A call pushes its
site, and a return pops that same top site. `Stack.path` retains the intermediate
configurations. `path_trans` composes paths at the same configuration.

`Stack.balanced` begins and ends at the empty stack. `Stack.truncate` keeps the innermost
sites, and `truncate_length` gives its exact minimum-length equation.

[`Ifds.t`](../../theories/Framework/FrameworkIfds.v#L61) supplies an ICFG, fact encoding,
finite fact support and `flow_c`. `None` is the zero fact. The fact list permits finite
exploded-row preparation. It is not a value-carrier enumeration. `Ifds.as_ide` supplies
unit values, Boolean symbolic jump weights and constant true arc weights.
Reachability and taint are observed in its Boolean jump map. Unit value results carry
no additional reachability information.

The declarations share a file. `IfdsData` stores the underlying IFDS record so that
`Ide.t` can refer to it and the final `Ifds` namespace can own `as_ide` without namespace
reopening or `Include` aggregation. `Ifds.t`, constructor and projections expose that
same record through direct aliases.

## IDE symbolic jumps and values

[`Micro.t`](../../theories/Framework/FrameworkMicro.v#L15) supplies `id`, charged composition,
charged application and a function lattice. Composition applies the right argument first.
`micro_laws` separately states weak and least-join laws, application equations,
monotonicity and join upper bounds. `micro_boolean_laws` proves the Boolean instance.
Neither the data record nor its laws contain lists of values or functions.

[`Ide.t`](../../theories/Framework/FrameworkIfds.v#L41) adds the value lattice and charged
edge weights. Jump keys are pairs of entry/destination vertices, and each vertex contains
a point and optional fact. `Jump.rows_c` prepares start identities, call-entry identities,
internal path extension and matched call/return summaries. A return composes its weight
after the callee jump, call weight and caller prefix. Unmatched returns create no row.

`jump_post` states the algebraic inequalities of these rows. `check_jumps_c` checks a
positive-keyed map and uses function-lattice bottom for absent keys.
`check_jumps_iff` proves reflection, and `check_jumps_sound` gives acceptance soundness.
Neither theorem needs micro laws or trusts a producer. The jump phase has no `Analysis.t`.
The later tabulation card supplies its producer and balanced-path theorems.

`value_analysis I jump_c start a0` accepts a charged jump lookup, prepares its weights once
and returns an ordinary analysis. Rows seed the start value, apply balanced jumps and
propagate values into callees. `vrow` distinguishes these three kinds. The jump callback
is costed to retain map-lookup and any client computation charges.

The IDE fixture checks taint through one matched call and runs the unit value phase. Its
second instance represents integer translations `x+b` over flat integer facts. It checks
a translation jump and computes the final integer value. `no_carrier_enumeration` proves
that no finite list enumerates the shared value/function carrier. These fixtures do not
implement tabulation or establish the later path-soundness theorem.

## Charges and verification boundary

Public callbacks retain their returned charges and separate invocation overhead.
Recursive list work uses Cost traversals. Shared prepared rows use the fixed read list
and charge their evaluator. Bitvector and syntax caches are built outside transfer closures.

The preparation tick fixture doubles repeated same-edge occurrences while holding the
key/fact support fixed. Its exact observations concern the reference backend. They do not
establish a general linear bound for list-backed maps or grouping. Framework tabulation
cost theorems belong to its later implementation card.

The card's checks are `just build-new`, `just test-new` and the exact staged forbidden-proof
grep under the owner's command policy. The full stage-one claims, formatting and extraction
audits remain the master's gate.
