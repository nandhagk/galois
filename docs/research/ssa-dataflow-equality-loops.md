Copied from the pre-redesign research notes on 2026-11-07. Card and ruling IDs refer to the retired run.

# SSA, dataflow, equality and loops: research and migration plan

Scope: recommendations for future owner review, not a change to the binding API or cards. As of
this research the README describes a skeleton, not implemented analyses. `historical API contracts` are
contracts, and their statements have not all been compiled. No timings or kernel-checked results
are claimed here. The `historical ledger` progress and current C rulings govern landing, not this plan.
All replacement or additional public statements need an owner ruling and a docs checkpoint; C14
only covers narrow type/name/premise repairs, not a change of meaning. This research does not edit
contracts or cards. Directly verified algorithms are the primary route below; independent checkers
are useful secondary fallbacks where explicitly identified as such.

## Cost model and shared premises

Let N, E be reachable CFG nodes and edges, V SSA values, U operand occurrences including edge
arguments, P the number of phi/edge arguments, X the fact universe, W machine bits per packed
word, and Q the number of queries. Let H be the number of strict increases per abstract cell,
including widening steps when bounded, and R the number of dependency edges in a sparse system.
Account separately for graph preparation, CFG versus sparse index storage, fact copying, result
materialization and invalidation. A dense bitset consumes Theta(N ceil(X/W)) words just to retain
all point facts; a bitmap worklist propagation costs O(sum of visits times fact operations), not
simply O(N+E). Canonical positive tries are the current required representation; their actual
lookup/update cost depends on positive-code bit length and sharing, and a union is not a unit-cost
operation. Canonical tries are the default. Outputting all live (point,value) pairs alone costs
Omega(output).

Build successors, predecessors, ordered instruction positions, value definitions, operand users,
edge argument indexes, entry/exit seeds, dominance and loop information once with coverage and
agreement lemmas. Do not silently assume numbers are compact or hash operations are worst-case O(1).
Strict SSA means a unique static definition that dominates uses, with intra-block order and phi
operands used on their incoming edge. Separate reachable nodes and unreachable components; model
parallel edges individually. A dynamic loop execution may revisit the same static definition;
there is no single execution-wide immutable cell unless the theorem explicitly justifies it.
Include exceptional and trap edges and exits if the client's graph represents them; soundness
otherwise requires the view's coverage laws. Irreducible control flow is valid input unless a
particular algorithm explicitly proves or checks a reducibility premise. For mixed unreachable,
non-strict or unsupported graphs retain the general system, not an invented answer.

Where credible methods have genuinely different cost or precision profiles, expose them as
consumer-selectable backends with shared semantic interfaces and proof lemmas. Do not require a
benchmark before offering either; distinguish equal-result implementations from different
abstract semantics. Replace an approach only where a competing approach dominates it for the
same capability and assumptions. The selections below identify the primary route, not a ban on
other non-dominated backends.

## Liveness and reaching definitions

Current ANA-1 has a dense backward liveness constraint system and a proved post-solution interface;
ANA-11 explicitly contracts least-model equivalence, and EX-5a provides SSA adapters. ANA-2 adds a
structured loop-head certificate and replay. Thus semantic liveness safety, least syntactic
liveness, and equality to reachable semantic liveness are three different claims: infeasible CFG
paths make the last equivalence generally false. Reaching definitions tracks historical pairs for
mutable source variables; SSA's unique value definition is not the same result.

**First investment: exact SSA query.** Boissinot et al.'s 2008 method prepares graph-only
reachability information and answers whether an SSA value is live at a point by combining its
uses, dominance, DFS and reduced reachability. Its cost is preprocessing plus a query-dependent
scan of uses and auxiliary reachability sets; it is not automatically constant time. The 2020
verified study gives a mechanically proved version and carefully states live-in conventions:
[Boissinot et al. 2008](https://publikationen.bibliothek.kit.edu/1000120906),
[verified liveness 2020](https://pmc.ncbi.nlm.nih.gov/articles/PMC7324086/). For few queries or
repeated instruction-only edits with an unchanged CFG, use this query engine;
for many queries or huge use lists, precomputation and repeated scans can dominate. Cache only
against an explicit CFG version; a use or def edit still changes the query's value-specific data.

Proof roadmap: construct and verify DFS/reduced-reachability indexes on the reachable graph;
prove their relation to paths including backedges, irreducible cycles and self loops. Define
liveness by a finite CFG path from the queried point to a use with no intervening definition,
accounting for edge uses and point-before/after conventions. Prove dominance filters and path
characterization both ways, then equality with the least ANA-1 liveness solution under strict SSA,
correct use/def adapters and graph well-formedness. Derive the existing backward agreement theorem
from this exact result; do not require an untrusted producer. Test bounded small graphs against
the existing ANA-11 least model when available, plus hand tests for phi on one edge, parallel edges,
use before def, loop-carried phi, irreducible SCC, unreachable blocks and exceptional exits.

For clients needing all facts, use the loop-structure SSA live-set construction in
[Boissinot's thesis](https://bernsteinbear.com/assets/img/boissinot-thesis.pdf), which describes an
edge visit and second node visit at the control-graph level. Set unions and output size still cost
extra, and this claim requires the algorithm's assumptions, not a blanket linear-time assertion.
The dense system remains for non-SSA clients and for clients requiring all facts. SSA query
liveness and the all-facts engine can share the same exact syntactic relation: one avoids
materializing the whole output, the other amortizes repeated point queries. For one named
SSA value, reaching definition at a valid use is its unique static
definition; dominance checks and correct phi-edge use establish it. Do not substitute this for
ANA-1's reaching historical `(variable, definition edge)` relation or its ANA-11 least model.
For original variables maintain SSA renaming/provenance and a mapping theorem, or retain dense
reaching defs; include definitions not reaching any use and initial values.

SSA live ranges are connected subtrees of the dominance tree under the specific interference and
point model. [Hack and Goos 2006][hack]
prove chordality and polynomial optimal coloring for a uniform register set; this does not make
spilling, coalescing, register classes or actual machine allocation polynomial. Any chordality API
needs a separate model proof including phi edge semantics and simultaneous definitions, and an
explicit interference-graph-size cost. Coordinate its graph lemmas with GRA/VIEW-5, avoiding a
second dominator implementation. Do not assume this theorem for approximate liveness sets.

## Availability, anticipation and code motion

ANA-1 supplies generic finite-universe gen/kill available and very-busy systems plus `lcm_check`,
`lcm_insert_safe`, and `lcm_delete_current`. Their history and backward-path statements are sound;
the checker does not itself promise optimal placement or a transformed-program equivalence.
Boundary seeds, exits and infinite paths matter. Generic expressions involving mutable memory,
trapping operations or changed operands need kills and effect laws, not just matching syntax.

[Sparse evaluation graphs, Choi, Cytron and Ferrante 1991][seg]
connect generators, consumers and merge points for forward or backward monotone problems and map
results back to dense edges. Build only for per-variable separable problems; do not assume every
relational domain admits the same projection. Construct the sparse graph with a representation
mapping, prove that each dense equation is simulated and that sparse least solutions reconstruct
the dense least solution under the relevant distributivity/monotonicity hypotheses. Select SEG
for separable non-SSA sparse analyses; charge construction and projection, since a fact queried
at nearly every point or expressions killed everywhere can erase the savings. On-demand placement in
[Cytron and Ferrante 1993](https://repository.library.washu.edu/cse_research/312/) is an
almost-linear construction for the stated phi-node set; charge dominance and output costs.

For SSA-specific PRE, [Kennedy et al. 1999][ssapre]
provide SSAPRE and its factored redundancy graph, with computational and temporary-lifetime
optimality under its model. It avoids a bitvector formulation but expression-phi construction,
renaming, edge insertion and output SSA repair cost space and time; worst-case expression graph
size can be large. Pursue a direct verified sparse placement engine only after a typed expression
universe, operand congruence, exception/effect and phi translation semantics exist. Prove sparse
availability/anticipation equivalence to chosen dense spec, placement legality, SSA repair and
semantic preservation; prove any optimality theorem separately with exactly the paper's model.
Offer SSAPRE for SSA PRE and generic LCM for general clients. They have different interfaces
and guarantees; equate placements only if a separate proof establishes the same specification.
Exceptional exits, trapping computations and
infinite loops must be in the theorem or explicitly excluded; do not infer safe speculation from
availability alone.

## Equality, zero, value numbering and e-graphs

ANA-1 equality is a must-equality partition for mutable variables and zero-since-entry means no
write since entry, not an abstract interpreter for every zero value. ANA-5 contracts dominator
scoped numbering, optimistic GVN and loop invariance; ANA-6 currently makes saturation an untrusted
producer with a verified explanation checker. They solve different problems and should coexist.

For zero, a def-use constant/known-bits SSA evaluation (ANA-3) can establish more zeros, but cannot
replace the historical no-write property. A copy-class union-find gives local equalities efficiently
only under its update model: kills, branches and intersections require persistence/refinement,
not a global monotone union that conflates mutually exclusive paths. ANA-1's sound transfer remains
the oracle. For scoped numbering traverse the dominator tree once, using scoped expression tables
with rollback or persistent maps; an expression key includes operator, type/width, semantic flags,
operand numbers and relevant memory/effect version. Match only pure expressions and prove both
operands exist and leader dominates each substitution. Count key comparison, trie depth and rollback
cost; bound table sizes by active dominator path plus saved state.

[Briggs, Cooper and Simpson 1997][vn]
compare hash and partition approaches. For cyclic phis, optimistic partition refinement or SCC
processing can find equivalences missed by simple dominator hashing. Their result is a congruence
under a chosen abstract expression language, not equality of all semantically equivalent machine
programs. Direct proof: finite partition refinement terminates by strictly splitting classes;
show each stable class satisfies corresponding operation and aligned incoming-edge equations,
then use induction/coinduction justified over finite execution prefixes to prove same values at
reachable joint points. Handle partial operators, poison/traps, type widths and phi predecessor
alignment explicitly. The cost is the total number of signature evaluations, partition updates and
use re-enqueues; do not promise near-linearity without a proved implementation bound. Choose
optimistic GVN for global congruence, and scoped numbering for a cheaper dominance-local answer.
These have different completeness and should be consumer-selectable, not equated by interface.
Test cyclic phis, branch scopes and successive splits.

For stronger algebraic rewrites [egg 2021][egg]
uses batched rebuilding and e-class analysis; saturation can grow without bound, so bound nodes,
iterations and time and report quality versus budget. A verified native congruence closure with
finite fuel, sound rewrites and proof-carrying guards is a useful direct-engine research track;
its invariant relates each class to word-expression denotations and every merge to a proved
rewrite, then extracted representatives preserve semantics. Memory, exceptions, control predicates
and dominance still need separate side conditions. ANA-6's existing checked explanations remain
remains the contracted route until a direct engine is approved; neither proves saturation complete.
Choose bounded direct equality saturation for algebraic rewrite search after its verified engine
is available. GVN remains the default for global congruence without algebraic search.

## Sparse constants, numeric refinements and demand

VIEW-4 already gives `UVal`, `UEdge`, `UBlock`, static constraints and sparse soundness; VIEW-5
adds guard facts at dominated uses; ANA-3 composes SCCP, known bits and intervals. Wegman and
Zadeck's [1991 paper](https://rsim.cs.illinois.edu/arch/qual_papers/compilers/wegman91.pdf)
shows sparse conditional constant propagation tracks executable edges together with values. Its
classic linear SSA-graph bound applies to its finite-height constant lattice and accounting model,
not arbitrary intervals, SMT queries, widening or repeated large phi scans. Implement indexed
edge-to-phi-argument updates and def-to-user worklists so each edge activation and each actual
value change schedules only affected rows; maintain an incremental join where justified by the
lattice, rather than rescan all predecessors after every activation. Charge join cost and H:
a simple bound is O(preparation + H*R*transfer_cost), subject to fair de-duplicated scheduling;
individual row fan-in and representation costs must be included. Large finite height, widening,
non-monotone transfers, or widening schedule dependence invalidate the simple exactness claim.

Prove directly that each worklist update preserves bounds, terminates with finite ascending chains,
and processes every affected dependency; establish least solution when joins are least, transfers
monotone and iteration is fair with no widening/fuel fallback. VIEW-4 then gives semantic soundness.
Choose directly verified sparse conditional propagation as the SSA default. A sound
overapproximation is not proof of equivalence to
path-sensitive collecting semantics.

SSI introduces split definitions at conditional edges and is useful for predicated and backward
sparse analyses: [Ananian 1999][ssi],
[parameterized sparse representations 2014](https://arxiv.org/abs/1403.5952). Choose VIEW-5's
on-demand dominated guard chain for query workloads; offer explicit SSI for consumers needing
repeated sparse predicate propagation or a split representation. They need separate construction
and equivalence proofs when intended to compute identical abstract facts. A dominating edge must hold on
all executions reaching that use, including self-loops and alternate edges; a block dominance
fact alone is insufficient. SSI may cost additional sigma nodes, arguments and SSA repair; lazy
queries may repeat guard traversals. Prove inserted sigma values denote their original value on
the correct edge, constraints reconstruct the original analysis, and each client guard has a
sound transfer. Invalidate the guard index after relevant CFG edits.

ANA-4's `needed_values` contracts the least closed Boolean demand; demanded/observable bits use
agreement, and erasure has distinct trap policies. Sparse backward traversal from observable
roots over indexed SSA users/operands can compute Boolean neededness in O(V+U+effects) graph
operations when each item is queued once, plus index and trie costs. Bit masks may change up to
width-dependent H times; transfers for carries, shifts, compares, poison and guards must be sound,
not simple bitwise reachability. LLVM documents a practical demanded-bits example at
[DemandedBits.h](https://llvm.org/doxygen/DemandedBits_8h_source.html). Prove per-operator masked
agreement, least closure under fair worklist, then derive the existing two-program simulation.
ADCE also needs control dependence, retained observable effects and a sound treatment of
potential divergence; phi edge demand is conditional on relevant predecessor control. Choose
sparse Boolean marking for neededness and masks when bit-level demand is requested; test narrow
truncations, carries and dead cycles. A dead
value alone does not authorize dropping a trap, event, memory write or divergent loop.

## Structured regions and loops

VIEW-2's binary sequence tree and frame machine, VIEW-3 region algebra, ANA-2 loop-head cut
certificates and replay already support compact structured analyses. An exact region summary for
an acyclic, distributive gen/kill region may compose transfer functions once; nested jumps,
backedges, divergence and multiple exits require multi-exit summaries and a proved simulation of
the frame machine. Arbitrary relational domains cannot assume a compact exact summary. For a
fixed finite universe, size is potentially proportional to input/output boundary facts; charge
summary construction, composition, invalidation, and replay, not only final query time. Test
nested loops, branch labels, relative jumps, empty sequences and multiple exits against dense
skeleton constraints. A census of uses/definitions/effects, built bottom-up with mergeable trie
summaries, can speed repeated queries; it is not a dataflow solution and must prove coverage.

ANA-5 loop invariance says the value changes at most once during an execution of the loop under
`loop_info_wf`, while ANA-7 contracts affine recurrences, checked no-wrap evidence and counted
loops. Distinguish stable value from permission to hoist: an operation may trap, have effects or
fail to execute on some paths. Prove invariant seeds outside the loop, recursively closed pure
operands, edge/phi initialization and no unsupported loop-carried definitions; use indexed
worklist cost proportional to visited dependencies plus trie costs. For loads require ANA-10's
invariant address and write-footprint disjointness as well as memory-view coverage.

Extend SCEV incrementally: direct proofs for affine add recurrences over modular words first;
prove no-wrap under explicit signed/unsigned range obligations before lifting to integers. Define
exit count per exiting edge and distinguish zero iterations, header entries and backedges; multiple
exits, exceptional exits and divergence need separate evidence. The
[LLVM ScalarEvolution documentation](https://llvm.org/doxygen/classllvm_1_1ScalarEvolution.html)
explicitly distinguishes exact, maximum and symbolic counts and assumes no abnormal exits for
its backedge count. Do not import this API's sentinel conventions as a theorem. Build canonical
DAGs and memoized recurrence queries with cycle guards; charge normalization and integer arithmetic
bit complexity. Test wrap boundaries, negative strides, multiple exits, early exception and nested
loops. Trip count, bound and unknown must be distinct result constructors. Prove each result from
`loop_view_laws`, prefix induction and the no-wrap evidence; do not claim termination merely from
an upper bound unless exit/progress conditions establish it. Fill/copy idioms need per-iteration
memory footprints, alias and effect proof, and are beyond the currently counted-loop idiom; retain
ANA-7's stated scope until a new owner ruling.

## Migration sequence and card map

1. Preserve current card contracts. Land core graph, VIEW-1/4/5 and EX-5a/5c; prove their
   reachability, phi and strictness premises. Establish ANA-1/11 leastness where contracted;
   do not implement an additional baseline solely to compare engines. The graph track owns DFS,
   dominance and SCC infrastructure; this track owns
   SSA use-to-path refinements. Request an owner ruling before adding new public query APIs.
2. Add verified SSA liveness query and its equality to the dense least model; keep existing API
   and let clients opt in. Prove exact agreement to the specified syntactic live relation and
   establish invalidation conditions. Test representative and bounded small cases.
3. Make the sparse SCCP worklist directly verified and match its results to the static constraint
   system; verify per-value neededness, demanded-bit transfer and guard indexes. Keep widening
   and disjunction alternatives as explicitly less precise or differently scheduled analyses.
   PRE/SEG equivalence is a distinct follow-on, not a prerequisite for liveness.
4. Establish ANA-5 producer acceptance and semantic theorems as specified. Direct equality
   saturation is the selected future rewrite-search engine. General PRE, SSI and e-graphs require
   their own public contracts and cannot silently alter ANA-1's existing claims.
5. Extend ANA-7 only after bit-vector recurrence and loop-view results are in place. Add proofs
   for any new exact/upper-bound exit count or memory idiom before claiming those capabilities.

Targeted measurement is optional only for an unresolved question: for example, whether cached
guard chains outperform traversal for repeated queries in the extracted trie representation.
Use the existing TOOL-2 harness when available; include index construction and report query count,
encoding lengths and allocation. It is not an adoption gate and requires no duplicate proof or
implementation. Prove required semantic and exactness results and test the semantic corner cases
regardless of measurement; verify proof closure and extracted behavior separately.

Crosswalk: ANA-1/11 and EX-5a are dense liveness/reaching; VIEW-4/5 and ANA-3 cover sparse values
and path/guard refinement; ANA-4 covers Boolean demand, bit demand and ADCE; ANA-5 and VIEW-5
cover DVN, GVN and invariance; ANA-6 covers e-graphs; ANA-7 covers recurrences, trip count and
counted idioms; VIEW-2/3 and ANA-2 cover region and structured code; ANA-10 supplies loop-load
memory premises. Add optional SSA query, sparse PRE/SEG, SSI, direct e-graph and expanded SCEV
only via new approved declarations/cards. ANA-5 already requires proofs that both its numbering
producers pass `numbering_check`; this is stronger than acceptance of an arbitrary candidate but
is not a stated theorem that every semantic equality is discovered.

| Card | Existing obligation and proposed action | Dependencies and optional split |
| --- | --- | --- |
| ANA-1 | Keep dense systems, history and LCM safety contracts for general clients. | VIEW-1, DOM-7, FIX; add SSA query and SSAPRE in separate approved cards. |
| ANA-2 | Keep structured liveness, cut certificates and replay. | VIEW-2/3 and FIX; bottom-up census is a separate optional API. |
| ANA-3 | Directly solve sparse numeric constraints with value and executable-edge indexes. | VIEW-4/5, DOM numeric laws, FIX and EX-5a; leastness only for appropriate join iteration. |
| ANA-4 | Directly compute Boolean closure and bit demand; preserve erasure policies. | VIEW-1/6, Bits and EX-5a; ADCE needs control and divergence premises. |
| ANA-5 | Prove both contracted numbering producers accepted and their soundness. | VIEW-5 strict SSA and dominance; optimistic GVN is global default. |
| ANA-6 | Keep contracted explanation checking until a direct bounded engine is approved. | Bits and rewrite laws; a direct saturation engine is a distinct future card. |
| ANA-7 | Prove affine recurrence and counted-loop statements with no-wrap evidence. | VIEW-4/5 and Bits; multiple-exit and memory idioms require new contracts. |
| ANA-11 | Prove contracted least-model correspondence for rule analyses. | RUL, ANA-1/4; it serves rules clients, not a comparison-only baseline. |
| VIEW-4 | Keep sparse values, blocks, edges and `sparse_sound`. | Graph coverage and phi-edge indexing; new SSI representation needs a separate contract. |
| VIEW-5 | Keep strict SSA and on-demand dominated guard refinement. | GRA dominance and EX-5c; share graph indexes with liveness query. |
| EX-5a | Supply SSA adapter laws and factorial examples. | EX-2, VIEW-4, ANA-1/4; include edge uses and instruction order in added query tests. |

Backend selection is a public client choice, not a benchmark-selected implementation detail.
New owner-approved cards should expose a common liveness query relation with both prepared SSA
query and materialized set implementations; exactness proves equal answers where premises overlap.
Likewise expose the existing generic forward/backward systems and the sparse specialization, with
equivalence only for shared distributive, correctly seeded problems. Provide distinct result or
precision metadata for scoped numbering and optimistic GVN, and for generic LCM and SSAPRE: common
soundness does not imply identical detected equalities or placements. Guard-chain queries and an
explicit SSI representation should both be implemented when their respective client interfaces
are approved; give each semantic preservation and its own invalidation conditions. New public
declarations and split cards need owner ruling; no benchmark gates these proof obligations.

## Recent literature and implementation audit

Search cutoff 2026-10-28. Searched 2023–2026 primary SSA liveness, sparse/conditional dataflow,
PRE, GVN, guards and loop-analysis work, plus official LLVM and GCC implementation references;
the egg and egglog specialist covers that separate track. This is a bounded search, not a claim
that no other paper exists or that any algorithm is universally fastest. Read the actual accessible
papers or primary author material below; moving official documentation describes its current tree,
not a pinned release or a proof of correctness.

- [Lemerre, POPL 2023][lemerre] treats SSA construction itself as abstract interpretation and
  combines SSA, optimistic GVN, SCCP and loop-invariant motion in a small pass. Its unified
  abstraction is a credible future composite backend for clients wanting joint precision; it
  requires its own semantic domain and proofs, rather than being equated to the existing separate
  VIEW-4 and ANA-3/5 systems. Preserve modular engines for clients wanting individual facts.
- [Aigner et al., MPLR 2024][lazy] give lazy SCCP for Graal's sea-of-nodes graph. The paper's
  section 3 distinguishes loop and non-loop phi handling, with unknown reachability requiring
  care; it is not simply the existing CFG worklist with skipped nodes. Offer this as a separate
  backend for a future sea-of-nodes view, with exactness to its specified solution and a proof of
  the scheduling/reachability treatment. Standard CFG SCCP remains appropriate for current views.
- [Brito 2024][brito] examines optimistic SSA GVN with undefined behavior, SSI and MemorySSA,
  and the [LLVM 2024 NewGVN report][newgvn] describes work to improve its implementation. This
  supports retaining optimistic and scoped consumers, but LLVM's poison and memory semantics do
  not transfer to Gaulois without explicit view laws. ANA-5's producer acceptance is not a proof
  of the thesis implementation or an all-semantic-equalities completeness claim.
- [Nougrahiya and Nandivada 2025][inc] prove incremental iterative dataflow under monotone
  unidirectional transfer functions and finite-height lattices. A versioned incremental backend
  is a credible separate workload choice after the solver track provides an update interface;
  directly prove equivalence to fresh solving for those premises and handle removals. This does
  not establish exact incremental widening or arbitrary dynamic side-effecting systems.
- The current official [LLVM SCCP source][llvm-sccp] uses value-lattice and constant-range
  machinery, while [ScalarEvolution documentation][scev] separates exit-count kinds and cache
  invalidation. They corroborate representation and API concerns, not Rocq proofs. The recent
  search located no directly applicable proved replacement for SSA liveness or general SSAPRE;
  the 2008/2020 liveness and 1999 PRE sources remain the concrete proof roadmaps here. This is a
  search finding, not an exhaustive novelty or superiority claim.

[lemerre]: https://binsec.github.io/assets/publications/papers/2023-popl-full-with-appendices.pdf
[lazy]: https://ckirsch.github.io/publications/proceedings/MPLR24.pdf
[brito]: https://web.ist.utl.pt/nuno.lopes/students/Manuel_Brito_MSc.pdf
[newgvn]: https://blog.llvm.org/posts/2024-09-01-reviving-newgvn/
[inc]: https://www.cse.iitm.ac.in/~krishna/preprints/oopsla25/oopsla25.pdf
[llvm-sccp]: https://github.com/llvm/llvm-project/blob/main/llvm/lib/Transforms/Utils/SCCPSolver.cpp
[scev]: https://llvm.org/doxygen/classllvm_1_1ScalarEvolution.html

[hack]: https://www.cs.ucla.edu/~palsberg/course/cs232/papers/HackGoos-ipl06.pdf
[seg]: https://research.ibm.com/publications/automatic-construction-of-sparse-data-flow-evaluation-graphs
[ssapre]: https://web.eecs.umich.edu/~mahlke/courses/583f23/lectures/Dec1/group19_paper.pdf
[vn]: https://www.cs.tufts.edu/~nr/cs257/archive/keith-cooper/value-numbering.pdf
[egg]: https://popl21.sigplan.org/details/POPL-2021-research-papers/23/egg-Fast-and-Extensible-Equality-Saturation
[ssi]: https://dspace.mit.edu/entities/publication/90fce509-5200-494b-9292-d34ffade899f
