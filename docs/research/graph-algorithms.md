Copied from the pre-redesign research notes on 2026-11-07. Card and ruling IDs refer to the retired run.

# Graph algorithms: evidence and implementation plan

Research snapshot, 2026-10-28. This is a proposed plan, not a contract or a claim of
implemented, benchmarked, or kernel-checked Gaulois behavior. `historical API contracts` is binding;
the owner must rule on changes of meaning, names, statements, or prescribed algorithms. Minimal
contract repairs follow C14 and must be reported for the next documentation checkpoint. The
ledger lists all GRA cards as queued; `theories/Graph` contains only its dune skeleton.

## Recent research and implementation check

Focused search through 2026-10-28 covered 2023–2026 dominator construction and certification,
frontier/IDF placement, loop/WTO/WPO construction and verification, SSA chordal colouring, and
official current implementation source. This is a targeted search, not an exhaustive survey
or a claim that no newer result exists. Relevant findings:

* [La Spina, Demange and Blazy 2025](https://doi.org/10.1007/978-3-031-91121-7_4) formalize
  WTO and two solver strategies; their producer is validated afterward. Their paper's WTO
  need not match loop nesting, and its evidence does not prove Gaulois's producer directly.
  It supports studying shared ordering/solver invariants, not replacing the direct proof goal.
* [Yang et al. 2025][inter-wto] develop interprocedural WTO for recursion. The paper's actual
  definitions concern a different interprocedural problem; it is not a drop-in faster proof of
  the contracted intraprocedural ordering. Read the paper, not merely the abstract.
* [Léchenet 2026][dom-2026]
  reports a Rocq-verified dominator certificate validator, not a direct LT producer proof. The
  official conference abstract was readable, but the linked full preprint was access-denied;
  treat its detailed proof and assumptions as unverified here. It strengthens the case for an
  optional external-result validator, without changing the direct-backend priority.
* The examined current official LLVM 24.0.0git [dominator source][llvm-dom] implements
  Semi-NCA; its [IDF source][llvm-idf] uses a Sreedhar–Gao-derived on-demand algorithm with
  optional live-in pruning and a priority queue. These are implementation facts and stated
  engineering bounds, not timing results for Gaulois or evidence for a persistent-trie bound.
* The focused recent searches found no directly applicable newer replacement that clearly
  dominates the selected static dominator, frontier or SSA-colouring approaches under this
  contract. Keep the classic approaches on their proved properties and explicit assumptions;
  this search cannot rule out work not retrieved.

## Cost model and common infrastructure

Let N be listed nodes, R reachable nodes, M listed edges, P maximum encoded key bit length,
L = ceil(log2(N+1)), and H the nesting depth. The API's `O(log)` map qualification is only
valid with a bound on encoding length; arbitrary injective positive encodings can have P much
larger than log N. Canonical binary trie lookup/update costs O(P), plus encoding and allocation;
binary counters/comparisons cost O(L) bit operations, not constant. `nat` colours and lengths
also require accounting for their actual representation. Paper bounds below count constant-time
array operations and word arithmetic. A prepared dense numbering plus a verified indexed store
would permit a word-RAM-like account only with stated machine bounds and an extraction argument;
never silently identify it with the current functional positive trie. Charge list traversal,
sorting, deduplication, output size, equality/weight operations, copying and peak allocation.

`prepare` builds both adjacency indexes once; retain ordered parallel edges and the `ready`
premises. `pred_nodup` relies on edge identity and no duplicate outgoing edge, not on distinct
endpoints. A virtual *fresh* root connected to each entry handles multi-entry dominance without
requiring a distinguished V value; prove a path bijection and erase its parent bindings. Avoid
materializing root edges in E: use a tagged internal vertex/edge representation. Empty entries,
duplicate entries, unreachable nodes, self loops and parallel edges need explicit examples.
Share an iterative DFS machine, dense numbering, reverse index and reachability once across
algorithms; memoize computed values in the caller, not hidden mutable global state. Each walk
must prove a potential bound including roots and initialization; `fuel p` is per traversal, not
automatically enough for repeated rounds or nested searches.

## Reachability, DFS, RPO and paths (GRA-1a/1b)

Current: explicit stack with remaining successors, binary fuel, pre/post numbers, parent edges,
blocked set, order-preserving roots, interval ancestry; `check_path` scans the current adjacency
for each edge and takes edge equality. Tarjan's original DFS and SCC paper gives O(N+M) with
constant-time indexed state ([Tarjan 1972](https://doi.org/10.1137/0201010)). This matches the
input-reading lower bound, not a claim that its persistent-trie implementation is linear in bit
operations. `check_path` costs sum of scanned out-degrees plus equality and lookup, potentially
much larger than path length. `tree_path` costs its parent-chain length times lookup and output;
detect malformed parent chains or constrain its theorem to a genuine DFS result.

Recommendation: implement the contracted machine directly. Prove stack frames are a simple open
DFS path, each frame's consumed/remaining edge partition, discovery once, finished closure, and
reachability witnesses; show each transition consumes an edge, discovers a node or finishes one.
Prove interval nesting/disjointness and edge classification as consequences. For all roots,
prove the aggregate fuel bound, including skipped roots, rather than reusing a bound intended
for one run without a proof. Prove `check_path` sound/complete given equality correctness;
an optional edge-indexed membership structure needs an edge encoding API and a separately
accounted build. Counterexample tests should include a blocked entry, roots reachable from an
earlier root, high-degree paths, self loops, and long chains.

## Dominators, postdominators and edge dominance (GRA-2a/2b)

Current: CHK candidate in RPO, at most `fuel p` rounds; `check_idom` performs one blocked DFS
for each reachable candidate dominator and verifies a forest, O(R(R+M)) graph operations plus
trie and numbering costs. `dominator_tree` checks and falls back to a flat sound forest; exactness
and downstream precision are conditional. This checker can dominate every faster producer and
`dominator_tree`'s textual definition recomputes the candidate unless extraction or refactoring
shares it. Cache the candidate and DFS results explicitly without changing the result.

Evidence, all under a single reachable root unless a super-root reduction is proved:

* [Cooper, Harvey and Kennedy 2001](https://hipersoft.cs.rice.edu/grads/publications/dom14.pdf)
  report an O(N²) formulation and favorable measurements on their compiler graphs. The API
  quotes O(NM); do not assume either bound for a particular implementation without proving it.
* [Lengauer and Tarjan 1979](https://doi.org/10.1145/357062.357071) give simple O(M log N)
  and sophisticated O(M alpha(M,N)) implementations, with indexed storage and path evaluation.
  Include N+M when disconnected input and preparation are counted.
* [Georgiadis, Tarjan and Werneck 2006](https://doi.org/10.7155/jgaa.00119) found simple LT
  and a hybrid consistently fast in their study, increasingly so on large/complex graphs. This
  contrasts with CHK's earlier corpus; neither establishes a universal winner today.
* [LLVM's implementation][llvm-dom]
  uses Semi-NCA, documents O(N²) worst case from nearest-common-ancestor walks and reports it
  usually slightly faster than simple LT. This is an engineering assertion, not a Gaulois
  benchmark. [Georgiadis 2005](https://www.cs.princeton.edu/research/techreps/432) develops
  Semi-NCA and linear-time variants. [Fraczak et al. 2013](https://arxiv.org/abs/1310.2118)
  give static-tree union variants that are near-linear or linear with the required union structure.
* Direct mechanized proof is realistic: [Zhao and Zdancewic 2012][verified-dom]
  formalize a certified dominator analysis in Coq; [Jiang 2021][verified-chk]
  proves a CHK-style list/semilattice algorithm sound and complete in Isabelle. These are proof
  references, not proof that Gaulois's particular parent-chain CHK is already verified, nor
  permission to import axioms or source.

Recommended portfolio: directly proved simple LT and Semi-NCA as consumer-selectable exact
backends, sharing DFS, semidominators and path evaluation. Default to simple LT for its stronger
worst-case bound; offer Semi-NCA for consumers favoring the practical tradeoff described by LLVM,
without requiring a benchmark before either is available. Do not first implement or prove CHK
as a comparison baseline. Simple LT has a simpler path-evaluation structure than the sophisticated
inverse-Ackermann variant. Prove the shared DFS numbering and semidominator path characterization,
and `link/eval` minimum-label path invariant under compression. For LT prove bucket settlement
and the semidominator-to-idom correction. For Semi-NCA prove that the nearest common ancestor of
the semidominator and DFS parent in the already constructed dominator forest is the immediate
dominator, including the parent-chain walk's termination. Each backend then proves correspondence
of its parent chains to every-entry-path dominance. Prove termination from reverse DFS order and
decreasing parent ranks; explain operation and bit/allocation counts in the implementation report.
Static-tree DSU is future work if a suitable verified data structure already exists and linearity
matters; it is not a prerequisite.

Propose a new explicit backend selector, for example `dom_algorithm := SimpleLT | SemiNCA`, and
`dominator_tree_with` parameterized by it. Both implementations must establish the same exact
forest and interval-query contract under `ready`; equality of parent maps follows from uniqueness
of immediate dominators, independent of internal numbering. A default wrapper selects SimpleLT.
Keep any legacy sound-but-imprecise fallback under a separately specified sound interface, not
under an unconditional exactness promise. Exact constructor naming and legacy compatibility need
owner review. Changing `chk_idom`, removing the mandatory checker from `dominator_tree`, changing
fuel, or strengthening unconditional exactness requires an owner ruling and card/API revisions. A cheap
debug or ingestion checker remains useful, especially for externally supplied trees. A verified
low-high certificate checker is a concrete near-linear alternative to the current quadratic
re-search: [Georgiadis and Tarjan 2015](https://doi.org/10.1145/2764913) prove linear-time
certification with suitable witnesses; prove the witness checks and tree theorem first, count
certificate construction, and do not pretend that it is a direct proof of the producer. Keep
the current expensive independent checker for small differential tests if retained at all.

Postdominance: reverse once by swapped indexes and prove path reversal; preserve explicit exits
and vacuity for nodes with no exit path. Infinite executions are not modeled by the current
finite-path definition; adding synthetic exits changes meaning and needs an owner decision.
Validate exit membership for `ready` and test multi-exit, no-exit, nonterminating SCCs. Edge
dominance: prove the unique reachable incoming edge from outside the dominated region criterion,
including parallel distinct edges, entry targets and self loops; build once and walk ancestors in
output-sensitive time. On an imprecise fallback tree show only soundness, not completeness.

## SCC, condensation, DAG and forwarding (GRA-3a/3b)

Current: iterative Tarjan within a region, reverse-topological component emission, condensation;
toposort uses DFS RPO and rejects retreating edges; max paths does reachable-DAG dynamic
programming; forwarding resolves a functional edge relation with memoization. Tarjan 1972's
O(N+M) unit-cost method is asymptotically optimal for input traversal. Preserve region membership
sets and original edge order; ensure each region root and each edge is processed once per call.
Prove pending-stack/frames partition, lowlink's restricted-path meaning, SCC root pop maximality,
and emission order; `2N+M+2` must include the actual machine's component pops and skipped roots.
Use SCC IDs directly for condensation and prove acyclicity from emission order. Preserve multiple
cross edges as the contract requires; if deduplicating, change the contract explicitly.

Topo proof: every non-self retreat edge gives a tree path back to its source, and every directed
cycle includes a retreating edge; output lists all nodes once. DAG maximum-path proof: process
reachable RPO and maintain the optimum over processed paths, including zero-weight entry paths,
negative edge weights, multiple entries, unreachable cycles, and `via` reconstruction. Cost
includes arbitrary Z arithmetic and path materialization. Forwarding proof: active/finished colors
and memo table distinguish terminal chains, cycles and tails entering cycles; each node becomes
finished once. Keep semantic behavior for starting nodes outside `Graph.nodes` separate from the
all-nodes theorem. In each case cost is O(N+M) graph operations plus trie/key/weight costs, not
automatic O(N+M) bit time.

## Loops, reducibility and WTO (GRA-4a/4b/4c)

Current: reducibility tests whether every reachable DFS retreat edge is dominance-backed;
natural-loop membership uses one reverse search stopped at the header. Recursive SCC
decomposition chooses the RPO-first header and emits nested forest sets; WTO uses the same
kind of recursion and a separate interval checker, with all-heads fallback. Current complexity is
O(H(N+M)) graph operations, and explicit `loop_nodes` alone can have Theta(NH) membership output;
no linear total construction is possible while materializing such output on deep nesting.
For one natural loop charge reverse incoming edges visited; for all back edges count repeated
work and output separately.

Proof: retreating edge plus DFS tree path is a cycle; conversely every reachable cycle contains
a retreating edge. Prove the dominance characterization and qualify `reducible_b` completeness
by tree exactness. For natural loops prove reversal and blocked-path equivalence with the header
added, including a self loop. For nested SCCs, induct on strict region size, prove each SCC is
maximal in the parent region, parent/child containment, header order, and coverage of irreducible
cycles. For WTO, prove SCC topological concatenation and recursive head removal establish every
backward edge's enclosing head; then producer validity directly, rather than relying solely on
acceptance. Token balance and interval-checker equivalence yield a useful linear-operation guard.

[Bourdoncle 1993](https://doi.org/10.1007/BFb0039704) motivates WTO widening schedules;
[Kim et al. 2019](https://arxiv.org/abs/1909.05951) study deterministic parallel fixpoints via
weak partial orders. A WPO is an optional new scheduling interface, not an interchangeable WTO
or a proof of identical results for all widening policies. [Ramalingam 1999][loops-1999]
shows the original Havlak variant can be quadratic and modifies algorithms to almost-linear time;
different loop forests are not automatically equivalent. Investigate a directly verified faster
forest only after proving it yields the contract's exact SCC/header decomposition; otherwise add
a separately named API and specify its relationship. Account for nesting depth and materialized
output separately. Changing header choice, output representation, or WTO order needs owner ruling.

## Frontiers, IDF and control dependence (GRA-5)

Current: per-edge runner to the immediate dominator, materialized set frontiers, then worklist
closure; control dependence uses a reverse-graph runner and retains edge identity. Prove the
shared chain lemma, self-frontiers and multiple entry roots, and postdom reversal under
`exits_reachable`. Output-sensitive costs must count *runner visits*, not merely distinct output
pairs: duplicate/parallel predecessor edges can revisit the same pair. Deduplicate per target
or stop at an already recorded pair only after proving the remaining chain is already covered;
otherwise state O(N + M + visits), with up to O(MN) visits, plus set operations and output.
IDF closure additionally pays the adjacency sizes actually traversed. Control-dependence edge
output may itself be Theta(MN).

[Cytron et al. 1991](https://doi.org/10.1145/115372.115320) gives dominance frontiers and SSA;
CHK gives the runner method. For per-variable SSA, use direct on-demand IDF with a dominator-tree
priority worklist and optional live-in pruning, while retaining the materialized contract for
clients that need all frontiers. [Sreedhar and Gao 1995](https://doi.org/10.1145/199448.199464)
give a linear-time phi-placement algorithm under their graph/data-structure assumptions; this
is not a linear bound on materializing all variables' full frontiers. Prove worklist discovery
soundness, least-closure completeness, once-only visitation and live-pruning semantics separately;
pruning changes the output from unpruned IDF and requires a new API. Preserve edge-sensitive
control dependence and explicit nontermination semantics; do not silently replace it with a
node-pair relation or a synthetic-exit convention.

## Interference and colouring (GRA-6a/6b)

Current: `add_point` adds each def/live pair except self and move source; greedy selects a
move-preferred free colour or spills; Briggs simplifies low-degree vertices, optimistically
chooses a candidate and selects in reverse; the checker verifies properness. Direct proofs are
already contracted for both producers. Maintain symmetry and set membership by induction on
pair insertion. Cost of interference construction is proportional to the sum of def/live pair
attempts (including duplicates), not just distinct edges. Build a move-partner index once;
scanning all moves per vertex violates the no-list-scan policy. Bucket updates and forbidden
colour construction cost adjacency visits and trie operations; the specified lowest free colour
scan adds up to O(Nk), with unary `nat` and representation costs counted. Prove properness via
the coloured-subgraph invariant and no spill via fewer than k colored neighbours. For Briggs,
prove residual degree and bucket consistency, each removal exactly once, and the degeneracy
elimination property; precoloured vertices remain fixed and can invalidate an unqualified
degeneracy guarantee. A checker remains valuable at external boundaries; direct proof makes
the wrapper unnecessary for internally constructed outputs only after an API ruling.

SSA offers a stronger specialized route. [Hack and Goos 2006][ssa-colouring]
prove chordality and polynomial optimal colouring for their strict SSA/liveness model and uniform
registers; [Hack, Grund and Goos 2006](https://pp.ipd.kit.edu/publication.php?id=hack06cc&lang=en)
separate colouring, spilling and coalescing. Prove live ranges are connected subtrees of the
dominator tree, their intersection graph is chordal, obtain a perfect elimination order, then
greedily colour in reverse order and prove colours equal maximum clique size. A linear graph
recognition/ordering routine is O(vertices + interference edges) under indexed adjacency, but
forming that graph may be quadratic; count that cost and prove the order actually is perfect.
Do not claim optimal machine allocation: move exclusions, precolours, register classes, aliases,
calling conventions, coalescing, spills and phi-edge liveness may violate the theorem's model.
In particular Gaulois's move-source exclusion may remove edges from a chordal graph, so the
current `add_point` output is not automatically chordal. A specialized SSA interference API
must state exact phi-edge uses, instruction points, liveness, move policy and strict dominance.
Integrate with the SSA research before proposing cross-package dependencies; retain general
Briggs for non-SSA and constrained allocation.

## Migration, verification and experiments

1. Amend GRA-1 prerequisites to expose verified dense indexing/cost model and common DFS invariants;
   prove reverse/index agreement and multi-entry virtual-root lemmas once. No code or public
   contract changes are authorized by this report.
2. Split GRA-2 into semantic dominance and virtual-root reduction; shared DFS/semidominator and
   path-evaluation infrastructure; separate direct simple-LT and Semi-NCA correctness cards;
   common exact selector/interface; then post/edge dominance. A certificate is optional for
   external trees, not a dependency of either directly verified producer. Allocate proof budgets
   to the shared foundation and each distinct correction theorem, not duplicate DFS proofs.
   Remove checker-dependent exactness only after owner approval and a closed proof. Reassess
   GRA-4a and GRA-5 dependencies and exactness premises at that checkpoint.
3. Keep GRA-3 SCC proof independent; share region decomposition with GRA-4. Split output-heavy
   loop/WTO proofs from optional near-linear representations. Prove WTO producer validity, but
   retain the externally useful cheap checker and fallback if contract requires them.
4. Split GRA-5 materialized frontier and direct IDF; coordinate strict SSA and colouring with
   Views/SSA. Separate generic graph colouring from a theorem with explicit SSA hypotheses.
5. Test long chains, wide diamonds, high-degree joins, parallel edges, nested and irreducible
   cycles, multiple entries/exits, disconnected graphs, cyclic forwarding, negative DAG weights,
   huge encodings and SSA move edges. Use the existing harness for a small targeted measurement
   only when an actual extraction or workload choice remains unresolved; neither exact backend
   depends on a benchmark gate.

All proposed theorems must be closed under Gaulois's no-axiom policy and checked by the claims
audit; published proofs and experiments are supporting evidence, not evidence about Gaulois.

[llvm-dom]: https://www.llvm.org/docs/doxygen/GenericDomTreeConstruction_8h_source.html
[verified-dom]: https://www.cis.upenn.edu/~stevez/papers/ZZ12.pdf
[verified-chk]: https://isa-afp.org/entries/Dominance_CHK.html
[loops-1999]: https://research.ibm.com/publications/identifying-loops-in-almost-linear-time
[ssa-colouring]: https://doi.org/10.1016/j.ipl.2006.01.008
[inter-wto]: https://drops.dagstuhl.de/storage/00lipics/lipics-vol333-ecoop2025/LIPIcs.ECOOP.2025.34/LIPIcs.ECOOP.2025.34.pdf
[llvm-idf]: https://llvm.org/doxygen/GenericIteratedDominanceFrontier_8h_source.html
[dom-2026]: https://popl26.sigplan.org/details/CPP-2026-papers/24/Mechanized-Dominator-Tree-Certification
