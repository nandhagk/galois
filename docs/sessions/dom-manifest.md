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
| `GraphCheckDom.v` | Convert to `Spec.v`, `DomSig.v`, `Dom.v` | Retain semantic definitions and replace checking by the reviewed low-high certificate. |
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
| `GraphDomFiniteReach.v` | Delete | The reviewed certificate checker replaces deletion reachability. |
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

`build g r` returns a parent map and a list in low-high order. The reviewed producer runs
simple Lengauer and Tarjan, then constructs the order from divergent spanning trees.
The producer remains untrusted under R9. Acceptance by `check g r m o` certifies its result.
The producer bodies in `Dom.v` are marked `STUB-CODE` until the following phases are ported.

The Lengauer and Tarjan phase numbers reached vertices by binary counters. It records
DFS parents, semidominators, relative dominators and the predecessor whose evaluation
minimizes each semidominator. Reverse settlement and forward correction produce the
candidate immediate parents. Link-and-evaluate operates on binary DFS numbers and records
its actual sequence in `lt_ops g r`.

The order phase follows the reviewed construction below.

1. Colour vertices in increasing DFS order using semidominators and relative dominators.
   Choose each divergent-tree parent from its DFS parent and minimizing predecessor.
2. Replace both divergent-tree parents by the immediate parent when its direct edge exists.
   Otherwise find each derived source in the appropriate immediate-parent child subtree.
3. Maintain child counters and a queue of removable vertices in the derived trees. Remove
   a qualifying vertex and record its anchor and witness. Redirect its remaining child.
4. Reinsert vertices in reverse removal order beside their anchors. Compare each witness
   with its anchor to choose the side.
5. Use the offline anchor tree and subtree sizes to assign binary intervals during insertion.
   A missing anchor or an empty candidate queue takes the specified total fallback.
6. Walk the immediate-parent tree in the resulting child order to emit the certificate.

The construction and its source algorithms are specified in F1-50 §4.4 of
`run/review/F1-findings-2.md`. That ruling cites Georgiadis and Tarjan,
[Dominator tree certification and divergent spanning trees](https://arxiv.org/abs/1210.8303),
Algorithms 3, 5, 7 and 8. Producer correctness proofs are outside the R9 conversion scope.
Its aggregate time contract still requires the actual phase and operation inventories.

## Checker specification

`dom_exact g r m` concerns the candidate map independently of production. Every binding
has reachable endpoints and gives an immediate dominator. Every reachable vertex lacks a
parent precisely when it lacks a strict dominator. The parent relation is well founded.
The order argument supplies an independently checked certificate for those properties.

`dom_cert (base g) r m o` has the following clauses.

- `cert_preorder` makes `o` a duplicate-free rooted tree preorder and rejects extra bindings.
- `cert_parent` closes the order under graph edges and makes every target parent an ancestor
  of its edge source.
- `cert_low_high` gives each child a parent edge or predecessors on both sides in preorder.
  The high predecessor lies outside the child's subtree.

The checker reads the base graph and ignores all prepared caches. Its bounded passes follow
F1-50 §4.2.

1. Scan listed vertices and their successor rows to compute graph measures and membership.
2. Read the order up to the graph vertex budget. Reject a wrong root, repeated key, unlisted
   key or key whose width exceeds the graph width. Build the position trie.
3. Read each ordered vertex's parent. Require no root parent and an earlier ordered parent
   for every other vertex. Reconstruct the candidate bindings.
4. Compare the reconstructed canonical trie structurally with the supplied map. Recursion
   follows the reconstructed trie, so extra raw candidate storage is rejected within budget.
5. Accumulate subtree sizes backwards through the order and validate parent containment.
6. Scan each ordered source row. Reject an absent target and test the parent property through
   intervals. Record direct-parent flags and minimum and maximum predecessor positions.
7. Test each child's direct-parent flag or low-high predecessor bounds.

`tree g r m o` numbers the accepted order and groups inverse parents in that order. Its
preorder and postorder fields are binary intervals. `dominates_b` tests interval containment.
`DOM_LAWS` requires acceptance before exposing exactness, inverse-child laws and semantic
query reflection. A query target must also be reachable for `dominates_b_spec`.

## Functional plan

The functional plan follows the reviewed chain in F1-50 §4.3. Every declaration is in
`DOM_PLAN` in `DomSig.v`. The following proof obligations remain admitted in groundwork.

| Lemma | Claim |
| --- | --- |
| `F0_path_last` | A nonsingleton path has a last edge. |
| `F1_dominates_trans` | Dominance composes through a dominated vertex. |
| `F2_check_cert` | Acceptance establishes the certificate clauses. |
| `F3_anc_before` | A proper ancestor precedes its descendant. |
| `F4_root_anc` | The root is an ancestor of every listed vertex. |
| `F5_reach_listed` | Every reachable vertex occurs in the order. |
| `F6_listed_reach` | Every ordered vertex is reachable. |
| `F7_anc_dominates` | Candidate ancestry implies dominance. |
| `F8_anc_dec` | Candidate ancestry is decidable on the ordered domain. |
| `F9a_low_path` | A listed vertex has a path through vertices at or before it. |
| `F9b_high_path` | A child has a parent path whose internal vertices follow it. |
| `F9c_avoid` | A nonancestor is avoided by some root path. |
| `F9_dominates_anc` | Dominance implies candidate ancestry. |
| `F10_cert_exact` | A certificate makes the parent map exact. |
| `F11_intervals` | Positions and subtree sizes decide ancestry. |
| `F12_tree_exact` | Numbering an accepted certificate gives an exact tree. |
| `F13_ops_length` | The actual producer sequence has linear operation count. |

`check_sound` follows from `F2_check_cert` and `F10_cert_exact`. The tree laws use
`F12_tree_exact`. This chain replaces all-pairs deletion checking and requires no soundness
claim about the producer.

## Time plan

Let `n`, `e` and `w` be `graph_n (base g)`, `graph_e (base g)` and
`graph_width (base g)`. The checker and accepted tree target is
`c_dom * N.of_nat ((n + e + 1) * (w + 1))`. Query cost charges actual key and interval widths.
The producer target adds `Nat.log2 n + 1` and assumes `prepared_ok g`.
<!-- src: run/review/F1-findings-2.md, F1-50 §4.1 and RULES §8. -->

The time chain follows F1-50 §4.5.

| Lemma | Work inventory |
| --- | --- |
| `T1_scan` | Listed vertices, their rows and their membership trie. |
| `T2_read` | Budgeted certificate reading with bounded key inspection. |
| `T3_map` | Parent reconstruction and bounded structural comparison. |
| `T4_sizes` | Subtree sizes and the per-vertex low-high tests. |
| `T5_edges` | Parent-property and predecessor accumulator updates. |
| `T6_tree` | Accepted numbering and inverse-parent grouping. |
| `T7_dfs` | Producer numbering by binary counters. |
| `T8_link_eval` | Aggregate compression work over `lt_ops g r`. |
| `T9_semi` | Semidominators, buckets and forward correction. |
| `T10_order` | Divergent trees, derived sources and offline insertion. |

The aggregate forest potential sums logarithms of subtree sizes and charges each link by a
logarithmic increment. It does not promise a logarithmic cost for each evaluation.
All time values, coefficients and potentials use `N` under RULES §8. The checker and tree
proofs, producer implementation and aggregate evaluator proof remain conversion obligations.

`T4_sizes` requires duplicate-free listed entries, a graph-sized order and parents within
that order. `T5_edges` also requires parents of ordered entries to belong to the order.
The bounded read and parent-validation phases establish these premises before either pass
runs. The master approved these internal premise repairs for the raw-input gap in F1-50.
The public time targets are unchanged. Read and parent-validation helpers take the initial
scan result, so their per-vertex bounds exclude repeated graph scans.
