# Dominator conversion manifest

The dominator component keeps one immediate-dominator producer, an independent checker,
and forest numbering. The producer is the simple Lengauer–Tarjan pipeline. Its result
becomes trusted through `check_sound`. Producer soundness proofs and backend selection
leave the rebuilt library under rule R9.

The source revision is `87192fee4d4e605ae21d917b730b30188c6b677c`. All old paths below are
relative to that revision. The design inputs are `run/design/core-design.md`, dominators
in §3.4, the Graph conversion table in §4, and risk 5 in §9. The run rules override the old
record dictionaries, cost monad and proof policy in `AGENTS.md` and `docs/workflow.md`.
This manifest is a conversion plan. It does not claim that the target cost contracts have
been proved or that the proposed signatures have been compiled.

## File decisions

Every source matching `theories/Graph/GraphDom*.v` or
`theories/Graph/GraphCheckDom*.v` has a row in the table. A conversion retains the named
parts and deletes the rest of that old file. New destinations are relative to
`theories/Graph/`. Deleted cost files supply proof ideas for `DomSig.v` where stated.

| Old file | Decision | Reason |
| --- | --- | --- |
| `GraphCheckDom.v` | Convert to `Spec.v`, `DomSig.v`, `Dom.v` | Retain exactness and checker reasoning, replace radix numbering and slow checking as needed. |
| `GraphCheckDomCost.v` | Delete | Monadic instrumentation gives raw-chain budgets, not the target checker bound. |
| `GraphDomAncestorIndex.v` | Delete | Materializing every ancestor chain needs quadratic space and work. |
| `GraphDomBackend.v` | Convert to `Dom.v` | Keep the LT parent pipeline and accepted-candidate renumbering pattern, remove backend records and fallback certification. |
| `GraphDomBucketCost.v` | Convert ideas to `DomSig.v` | Distinct queried buckets partition inserted occurrences. |
| `GraphDomCheckBound.v` | Delete | Raw storage polynomial is evidence about the old checker. |
| `GraphDomCheckedCost.v` | Delete | Checked fallback wrapper and its branch budgets leave the API. |
| `GraphDomCost.v` | Delete | Compatibility cost facade duplicates the checker and backend entry points. |
| `GraphDomCostBasis.v` | Delete | Argent and public trie contracts replace the monadic primitive estimates. |
| `GraphDomCut.v` | Delete | Closed semidominator cuts support producer soundness. |
| `GraphDomCutPath.v` | Delete | Avoiding-path equivalence supports producer soundness. |
| `GraphDomCutTransport.v` | Delete | Virtual ranked-cut transport supports producer soundness. |
| `GraphDomDfs.v` | Convert selected inventory lemmas to `Dom.v` and `DomSig.v` | Rank decrease and settlement order support producer termination and cost. |
| `GraphDomDfsPath.v` | Delete | White-path closure supports semidominator correctness. |
| `GraphDomErase.v` | Convert selected code to `Dom.v` | Endpoint conversion supplies the chosen pipeline's output map. |
| `GraphDomFastCheck.v` | Convert rejection and agreement reasoning to `Dom.v` | Retain domain checks and reference agreement arguments, delete the cached pair-loop implementation. |
| `GraphDomFastCheckCost.v` | Delete | Proves a graph product bound, which cannot discharge linear checking. |
| `GraphDomFiniteClosure.v` | Delete | New first-order prepared adjacency removes the raw interpreted-graph transport. |
| `GraphDomFiniteCost.v` | Delete | Raw normalization and callback prices disappear with closure records. |
| `GraphDomFiniteQueryCost.v` | Delete | Repeated normalized reachability is outside the target linear checker. |
| `GraphDomFiniteReach.v` | Convert selected reachability materialization to `Dom.v` | Supplies the reference deletion checker without retaining `GraphReach`. |
| `GraphDomFiniteSearch.v` | Delete | The new search directly consumes first-order prepared data. |
| `GraphDomFiniteTransport.v` | Delete | Raw finite-view ID transport has no new representation counterpart. |
| `GraphDomFiniteView.v` | Delete | Preparing one first-order graph replaces the normalization layer. |
| `GraphDomGlobalCost.v` | Delete | Its proved LT bound is a vertex-edge product. |
| `GraphDomInputCost.v` | Delete | Original callback duties and virtual augmentation leave the new single-root API. |
| `GraphDomLayoutCost.v` | Convert inventory ideas to `DomSig.v` | Retain widths and charge predecessor occurrences in aggregate. |
| `GraphDomLink.v` | Convert code to `Dom.v` | Link, compression and minimum-label evaluation serve simple LT. |
| `GraphDomLinkCost.v` | Convert support invariants to `DomSig.v` | Rank-linear query bounds need a new aggregate logarithmic proof. |
| `GraphDomLinkProof.v` | Convert `minimum_member` to `Dom.v` | Numeric support needs the selected input, delete segment-minimum correctness. |
| `GraphDomLt.v` | Convert code to `Dom.v` | Select bucket settlement and forward correction as the single finisher. |
| `GraphDomLtChoice.v` | Delete | Exact provisional parent choices are producer soundness. |
| `GraphDomLtCost.v` | Convert phase inventory ideas to `DomSig.v` | Keep bucket and correction work accounting, replace per-query rank bounds. |
| `GraphDomLtProof.v` | Delete | LT exactness and backend agreement are producer soundness. |
| `GraphDomLtReverse.v` | Convert `bucket_index_spec` to `Dom.v` | Numeric bucket support needs input membership, delete provisional exactness. |
| `GraphDomNca.v` | Delete | The second finisher is outside the chosen producer. |
| `GraphDomNcaCost.v` | Delete | Prices the removed threshold-walk finisher. |
| `GraphDomNcaProof.v` | Delete | Proves the removed finisher's exactness. |
| `GraphDomNumber.v` | Convert to `Dom.v` | Group inverse parent bindings and number the resulting forest by one DFS. |
| `GraphDomNumberCost.v` | Convert inventory ideas to `DomSig.v` | The old quadratic estimate needs an exact forest-edge inventory. |
| `GraphDomOutput.v` | Convert `renumber_exact` reasoning to `Dom.v` | Checked parent maps retain exactness after DFS numbering. |
| `GraphDomOutputCost.v` | Convert selected inventory ideas to `DomSig.v` | Price erasure and output enumeration once, omit producer exactness dependencies. |
| `GraphDomParents.v` | Convert selected semantic lemmas to `Dom.v` | Immediate-parent uniqueness can support checker exactness without a producer. |
| `GraphDomPath.v` | Delete | Label-preserving ranked paths support producer correctness. |
| `GraphDomPipelineCost.v` | Delete | Old whole-tree composition includes removed virtual and numbering phases. |
| `GraphDomPost.v` | Delete | Reverse-view post-dominator wrappers are outside `DOM_OPS`. |
| `GraphDomPredSize.v` | Convert inventory reasoning to `DomSig.v` | Distinct target rows partition predecessor occurrences. |
| `GraphDomPrologueCost.v` | Convert phase decomposition ideas to `DomSig.v` | Separate DFS, layout and settlement charges, replace product estimates. |
| `GraphDomRank.v` | Delete | Use Argent's timed positive comparison and `N` loop counters. |
| `GraphDomRankMap.v` | Delete | Generic partial-rank transport proofs belong to the removed soundness pipeline. |
| `GraphDomReachCost.v` | Delete | Prices removed compatibility closure iteration. |
| `GraphDomSemi.v` | Convert selected code to `Dom.v` | Keep rank layout and reverse semidominator settlement for LT. |
| `GraphDomSemiCost.v` | Convert numeric support and occurrence invariants to `DomSig.v` | The retained settlement needs an aggregate link/eval bound. |
| `GraphDomSemiEval.v` | Delete | Cut-forest minima establish producer correctness. |
| `GraphDomSemiExact.v` | Delete | High-path minima establish producer correctness. |
| `GraphDomSize.v` | Convert selected inventory lemmas to `DomSig.v` | DFS node and edge counts support finite costs and loop fuel. |
| `GraphDomSpec.v` | Convert to `Spec.v` and `DomSig.v` | Keep semantic dominance and exact parents, separate numbering from map exactness. |
| `GraphDomTransport.v` | Delete | Direct positive vertices remove virtual-name inverse transport. |
| `GraphDomVirtual.v` | Delete | The public operation supplies one root directly. |
| `GraphDomVirtualCost.v` | Delete | Prices the removed multi-entry virtual-root constructor. |

The tests below supply semantic fixtures for `tests/Graph/DomTest.v`. Ported executable
tests retain their old expected values. Multi-entry tests require an explicitly constructed
synthetic root fixture because the new public call supplies a single root. Producer
soundness clients, backend comparisons and literal tick assertions are deleted.
Internal rank expectations that include the old virtual root also require that explicit
synthetic-root fixture. Direct-root tests retain their public parent and query expectations.

| Old test under `tests/Graph/` | Decision | Reason |
| --- | --- | --- |
| `GraphCheckDomTest.v` | Convert to `DomTest.v` | Keep accepted fixtures, wrong parents, cycles, missing bindings and absent interval queries. |
| `GraphCheckDomCostTest.v` | Convert value cases to `DomTest.v` | Keep candidate rejection and chain boundary cases where helpers survive. |
| `GraphDomBackendTest.v` | Convert public value cases to `DomTest.v` | Keep LT parent outputs and numbering queries, remove certification and backend clients. |
| `GraphDomCallbackCostTest.v` | Delete | First-order graph data has no stored graph callbacks to reprice. |
| `GraphDomCheckedCostTest.v` | Delete | The checked fallback wrapper is removed. |
| `GraphDomCostTest.v` | Convert checker value cases to `DomTest.v` | Keep bad-domain and cyclic-parent rejection, remove raw storage and tick contracts. |
| `GraphDomFastCheckCostTest.v` | Delete | Old indexed checker cost controls do not test the new contract. |
| `GraphDomGlobalCostTest.v` | Delete | Old virtual-pipeline product bounds do not test the new contract. |
| `GraphDomLinkCostTest.v` | Convert value cases to `DomTest.v` | Keep compression representative and shortcut updates, delete monadic prices. |
| `GraphDomPostTest.v` | Delete | Post-dominator wrappers are outside the new API. |
| `GraphDomSemiTest.v` | Convert code cases to `DomTest.v` | Keep line and diamond semidominators, numeric order and unreachable-source filtering. |
| `GraphDomSpecTest.v` | Convert relevant cases to `DomTest.v` | Keep reflexivity and strict/immediate dominance fixtures under a specified root. |
| `GraphDomVirtualTest.v` | Delete | Tests the removed virtual-root and name-erasure interface. |

## Producer

`build g r` runs DFS from `r`, constructs discovery-rank parent and predecessor tables,
settles semidominators in reverse discovery order, builds buckets, processes those buckets
in reverse order, and corrects provisional parents in forward order. The retained code
comes from `DomSemi`, `DomLink`, `DomLt` and the LT branch of `DomBackend.parents_c`.
Output conversion maps discovered ranks back to original positive vertex IDs. The root
has no strict parent. Unreachable vertices have no output bindings.

Simple LT matches the producer assumed by core §3.4 and avoids keeping both LT and
Semi-NCA. The landed Semi-NCA walk has a rank-linear bound per query in
`DomNcaCost.walk_cost`. Its finisher has a quadratic bound in
`DomNcaCost.actual_finish_numeric_cost`. Selecting that finisher would not establish the
published LT target.

The retained link/eval code uses `fix_wf` on unary rank measures. Conversion replaces that
recursion with explicit `loopN` states and unwind stacks. Each walk receives sufficient
binary fuel derived from the discovered node count. State data and stacks are first order.
The time derivation must charge descending walks, saved stack cells and unwinding writes.
Choosing `loopN` alone proves termination of the bounded code. It does not establish the
logarithmic aggregate work bound.

The cost arguments also need two functional helper lemmas from files whose semantic
proofs are deleted. `DomLinkProof.minimum_member` bounds selected labels without proving
semidominator correctness. `DomLtReverse.bucket_index_spec` bounds bucket members by the
input order without proving provisional-parent correctness. Both proofs move alongside
the retained code, so the timed producer has no dependency on deleted soundness files.
Other retained inventory arguments must likewise be restated over numeric discovery and
operation support, rather than importing deleted ranked-path or producer-exactness proofs.

## Checker specification

Let `R` be the vertices reachable from `r` in `base g`. Let `parent_m v` be the lookup of
`v` in the candidate map `m`. Strict dominance means dominance between distinct vertices.
An immediate dominator strictly dominates its child and is dominated by every strict
dominator of that child. Candidate exactness has the following obligations.

- Every present binding has both endpoints in `R` and gives an immediate dominator.
- A reachable vertex has no parent if and only if it has no strict dominator.
- The parent relation is well founded.

These obligations define `exact g r m` in `DOM_SPEC`. Canonical `PTrie` storage removes
the old `Map.wf` field. The definition concerns the supplied map. Tree numbering and
children ordering receive separate specifications because `check` accepts a parent map.
No result from `build` occurs in `exact` or in the checker laws.

The independent reference checker computes `R`, validates binding endpoints and terminating
parent chains, and compares parent ancestry with absence from reachability after deleting
each reachable potential dominator. `DomCheck.check_sound` is the semantic proof source.
Its actual premises are `Prepared.ready p`, `Map.wf positive_encoding m`, and acceptance.
Its conclusion is `Dom.exact p (DomCheck.of_parents p m)`, which also certifies the old
radix numbering. It is not already the new map-only theorem.

The conversion proves the map-only fields first, then derives the numbered-tree result.
The following landed lemmas identify the available proof steps.

| New obligation | Landed source | Conversion duty |
| --- | --- | --- |
| Candidate domain | `DomCheck.checked_domain` | Replace name/ID transport by direct positive endpoints. |
| Parent termination | `DomCheck.checked_ends`, `checked_forest`, `ends_acc` | Use canonical storage and a finite reachable domain. |
| Parent ancestry | `DomCheck.ancestor_b_spec` | Retain the termination premise for bounded parent walks. |
| Semantic ancestry | `DomCheck.checked_dominance` | Replace `Reach.avoiding` by a search-based deletion reachability lemma. |
| Immediate parents | `DomCheck.checked_strict`, `checked_immediate` | Carry reachable endpoints and exclude cycles. |
| Missing parents | `DomCheck.checked_absent` | Prove the equivalence for every reachable child. |
| Semantic reachability of dominators | `DomCheck.dominator_reachable` | Specialize every-entry paths to root `r`. |
| Parent ancestry from exactness | `DomCheck.ancestry_spec` | Rebuild against map-only `exact`. |
| Interval queries | `DomCheck.dominates_b_spec` | Use DFS numbering, handle unreachable query dominators explicitly. |
| DFS forest intervals | `DomNumber.named_ancestry`, `of_parents_covers`, `of_parents_numbering` | Remove re-interning and keep original positive keys. |
| Renumbering exact maps | `DomOutput.renumber_exact` | Its proof uses checker exactness and forest numbering independently of producer correctness. |
| Inverse children | `DomNumber.forest_out`, `forest_edge`, `forest_out_nodup` | Retain grouped binding membership and prove the specified list order. |

Several checker helpers in this table are `Local Lemma`s in `GraphCheckDom.v`. Their
proofs must move into `Dom.v` before the old files are deleted. Their old module paths
are not an importable public interface.

`dominates_b_spec` in the design assumes reachability of the queried target `v`. The landed
lemma also assumes reachability of the queried dominator `u` and supplies prepared-name
bindings for both endpoints. Conversion discharges the extra reachability case without
adding a public hypothesis. If `u` is unreachable and `v` is reachable, semantic dominance
is false by `dominator_reachable`. Tree lookup must return no interval for `u`, so the
Boolean is false. The reachable case uses `ancestry_spec` and `of_parents_numbering`.
Conversion also proves absence of intervals outside `R`. Coverage of `R` alone does not
prove that absence property.

`kids_spec` is planned as exact inverse membership, absence of duplicates, and ascending
tree preorder within each parent's child list. `DomNumber.forest_out` gives the inverse
membership list in filtered map-enumeration order. `forest_edge` and `forest_out_nodup`
give membership and uniqueness. No landed lemma orders these lists by the new tree
preorder. The numbering traversal must visit children in the order stored by `kids`.
Its traversal-order lemma then proves the ordering clause without sorting afterward.

The new graph has no interpreted graph or naming dictionary. A proof that the prepared
predecessor cache agrees with `base g` is still necessary wherever the checker uses
`preds`. A checker that uses only `base g` avoids that cache premise. The public acceptance
law must not silently import old `Prepared.ready`. Malformed graph data and an absent
root require explicit behavior in the signatures and executable checks before freezing.

## Cost gaps

Let `n` and `e` count graph vertices and edge occurrences. Let `w` bound the bit width of
queried vertex IDs and generated counters. The retained public targets are those of core
§3.4. Checking and tree construction cost at most `c * (n + e + 1) * (w + 1)`.
An interval query costs at most `c * (w + 1)`. Building parents costs at most
`c * (n + e + 1) * (Nat.log2 n + 1) * (w + 1)`.
<!-- src: run/design/core-design.md, dominators in §3.4, supplied run kit. -->

The following landed results do not prove these targets.

- `DomCheckCost.ancestor_cost` prices construction and scanning of one parent chain.
  `DomCheckCost.check_c` repeats that work inside the live-node pair loop.
- `DomFastCheckCost.check_table_cost` proves a bound proportional to
  `(1 + n) * (1 + n + e) * (1 + w)` on its stated finite-input domain. Caching ancestor
  sets removes repeated chain reconstruction but retains every live-node pair and one
  blocked search per potential dominator.
- `DomCheck.of_parents` encodes complete parent paths as radix intervals. Label widths
  grow with parent depth, so constant-width interval lookup cannot be inferred from it.
- `DomNumberCost.number_cost` composes forest construction, re-preparation, search and
  annotation. `number_shape` proves a quadratic upper bound. Its `edge_inventory` uses
  `c * c` despite the forest's unique parent keys.
- `DomLinkCost.eval_identity_cost` bounds one evaluator query by the numeric rank limit.
  `DomLtCost.actual_finish_cost` and `DomGlobalCost.lt_cost` compose that estimate into
  a vertex-edge product. They contain no aggregate logarithmic link/eval theorem.

The linear checker needs a new implementation and a proof of acceptance implying the
same `exact`. A proof of agreement with the deletion checker would reuse the old
soundness argument. The reading pass does not select a proved linear checker algorithm.
Changing a constant or a `TimeFun` annotation cannot remove the pair loop. A candidate
algorithm must be reviewed before `DOM_PLAN` claims a linear work inventory.

Candidate storage also needs an explicit accounting decision. A parent map can contain
more bindings or wider keys than the graph. Scanning every supplied binding cannot have
a graph-only bound on arbitrary raw candidates. Early rejection must bound the amount
of storage inspected using graph-derived budgets, including trie depth. Alternatively,
the specification must define how candidate input size enters the existing measures.
The public target is left unchanged pending review of this boundary.

## Draft functional chain

The following names are planned obligations for `DOM_PLAN`. The names record dependencies
for task 6.5. They are not new checked Rocq declarations.

| Planned lemma | Statement and dependency |
| --- | --- |
| `F1_reach` | A root search lists each reachable vertex once and lists no other vertex. Uses the new `Search` laws. |
| `F2_parent_domain` | Acceptance gives reachable endpoints for each candidate binding. Ports `checked_domain`. |
| `F3_parent_forest` | Acceptance gives a well-founded parent relation and terminating bounded walks. Ports `checked_ends` and `checked_forest`. |
| `F4_checked_ancestry` | Accepted candidate ancestry equals semantic dominance on reachable endpoints. Ports `checked_dominance` for the reference checker. |
| `F5_exact` | `F2` through `F4` give immediate-parent soundness, parent absence equivalence and map-only exactness. Ports `checked_immediate` and `checked_absent`. |
| `F6_tree_edges` | Inverse grouping has exactly the candidate edges and no duplicate child. Ports `forest_edge` and `forest_out_nodup`. |
| `F7_tree_numbering` | A single DFS of the checked parent forest covers exactly reachable vertices and gives nested intervals exactly for ancestry. Ports `named_ancestry` and `of_parents_numbering`. |
| `F8_kids_order` | Each stored child list is visited in its stored order, so its preorder numbers are strictly increasing. New traversal-order proof. |
| `F9_dominates_b` | `F4` and `F7` prove the reachable query case. Interval absence and `dominator_reachable` prove the unreachable-dominator case. |
| `F10_check_sound` | The selected efficient checker implies `F2` through `F5`, either directly or through agreement with the reference checker. New efficient-checker proof. |

`F10` must be proved independently of the selected producer. A checker that recomputes LT
and compares results would require a producer soundness theorem and would inherit its
build time. Such a construction does not meet the design's checker role or linear target.

## Draft time chain

The plan exposes a traversal work inventory and named coefficients before stating the
contracts. `TimeFun` derives the time functions of every retained helper. Old tick
functions and old numerical coefficients are deleted. Groundwork uses the run's `STUB`
form for the unproved time obligations after review.

| Planned lemma | Work inventory and dependency |
| --- | --- |
| `T1_trie` | Public trie lookup, insertion and bounded traversal costs include the actual queried key widths. |
| `T2_reach` | `F1` and search cost charge each reached vertex and outgoing edge occurrence once. |
| `T3_tree_group` | Group candidate bindings once into inverse child lists. Charge every inspected trie node and emitted binding. |
| `T4_tree_edges` | The exact number of forest edges is the number of present candidate keys. Reachable-domain exactness bounds it by `n`. Repair the old quadratic `edge_inventory`. |
| `T5_tree_search` | Traverse those child lists directly through first-order prepared data. `T3`, `T4` and search cost give linear grouping and numbering work. |
| `T6_tree` | Add reachable enumeration, inverse grouping, numbering and annotation. Derive the target `T_tree_le` from `T2` through `T5`. |
| `T7_query` | Bound four interval lookups and two binary comparisons. `F7` bounds counter widths. Derive `T_dominates_b_le`. |
| `T8_check_inventory` | Prove the reviewed efficient checker inspects a linear number of graph and candidate items, including failed candidates. New implementation-specific obligation. |
| `T9_check` | Combine `T1`, `T2` and `T8` to derive the unchanged `T_check_le`. Reference deletion-checker bounds cannot prove this lemma. |
| `T10_build_inventory` | DFS ranks are distinct, each reachable incoming occurrence is scanned once, and total bucket membership is linear. Reuse `DomPredSize.actual_incoming_mass` and `DomBucketCost.index_cost` reasoning. |
| `T11_link_eval` | Prove aggregate LT link/eval work is bounded by a named constant times `(n + e + 1) * (Nat.log2 n + 1)`. New amortized proof over the actual retained evaluator. |
| `T12_build` | Compose DFS, rank layout, settlement, bucket settlement, forward correction and rank-to-ID output. `T10` and `T11` imply the unchanged `T_build_le`. |
| `T13_bigO` | Derive the published corollaries from the corresponding contracts on their specified input domains. |

`T11` needs a manifest potential or charging invariant for shortcuts, labels and the
unwind stack. The landed rank-descent proof supplies termination and finite support.
It supplies no logarithmic potential. The plan must not assert that each individual
query costs logarithmic time. The intended target is an aggregate bound over the actual
LT operation sequence. A failure to prove that bound for this evaluator requires review
of the evaluator implementation.

Numbering can avoid the old cost gap by grouping inverse parents once and running DFS
directly over that forest. The grouping proof must use the sum of row lengths, because
charging the longest child row once per vertex recreates the old quadratic estimate.
Binary DFS clocks and all explicit loop fuels need width lemmas and the additive fuel-bit
cost required by rule R10. An empty traversal needs its driver overhead too.

The unresolved obligations for review are the efficient checker algorithm and its proof,
candidate-storage accounting, the graph validity boundary, and the aggregate LT evaluator
bound. Task 6.5 turns the reviewed chain into statements. Task 6.6 ports the retained code
and functional lemmas after the reviewer resolves those obligations.
