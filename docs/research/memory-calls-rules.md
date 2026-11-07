Copied from the pre-redesign research notes on 2026-11-07. Card and ruling IDs refer to the retired run.

# Calls, memory and rules: algorithm and proof roadmap

Status: research proposal, 2026-10-28. The API is a planned contract, not evidence of an
implementation. The ledger has ANA-8 through ANA-11, VIEW-6/7, RUL-1a/b and EX-6 queued. This
report covers inventory IDs VIEW-CALL, VIEW-MEM, ANA-TARGET through ANA-CONTEXT,
ANA-ANDERSEN through ANA-INVLOAD, RUL-*, and B-NORETURN, B-MODREF and B-STORELOAD. Names
below for new interfaces and cards are proposals, not changes to `historical API contracts`. C12 requires an
owner ruling for changed contracts; C14 covers only the documented minimal fixes. No claim here
is a kernel-checked Gaulois result or a measurement of Gaulois.

## Recommendation and limits

Retain each current theorem and its meaning. Build specialized, directly proved algorithms as
additional implementations whose output refines the existing system, instead of making a
producer/checker the primary strategy. Prefer exact equivalence to the least solution when that
is the existing precision; a sound post-solution alone permits top and is insufficient to prove
an optimization preserves precision. `solve_fuel` may return top: compare with the exact
mathematical solution separately from the existing fuel result. Keep the current independent
checker as fallback and cross-check, especially because C7 expressly specifies an untrusted
MemorySSA producer. Changing that contract or replacing it with a complete MemorySSA is an owner
decision, not a C14 correction. After approval, make the directly proved memory graph and walker
the primary implementation. Reuse them for a compatibility projection of `def_of_load` and
the existing byte theorem only where their stronger reverse-walk premises are proved; a general
memory phi or conservative clobber answer does not automatically meet those premises. Preserve
the checker for optional external or cached candidates, not as a mandatory validation pass after
every proved internal construction. Do not build a second legacy constructor solely to maintain
the old representation.

Strict SSA exposes explicit scalar def-use and phi-edge uses, so argument/return flows and many
query dependencies can be indexed once. SSA alone does not resolve memory aliases, identify
individual dynamic allocations, make calls pure, or justify a strong update. Memory needs a
sound may-points-to preanalysis and a memory-version graph; summary edges must include indirect
calls and unknown effects. Representation preparation is an up-front cost, often worthwhile for
many queries but potentially slower for one query or tiny functions. Cost all construction,
proof-erased extracted execution, query and invalidation separately.

There are explicit semantic gaps. The example activation semantics is one function with loads,
allocations and call results arbitrary, and `activation_lifting` gives frame reachability and trace
subsequence; it does not lift activation behavioural equivalence to full executions. EX-6's
full memory view does not itself prove this stronger simulation. Bulk copy/move/set, externally
modified state, volatility, atomics, exceptions, concurrency and allocation failure require
explicit client operations and laws; do not infer their semantics from ordinary stores. Site
abstraction represents many dynamic objects, so a site singleton is not a concrete singleton.

## Calls and summaries

* **Target resolution and reachability.** ANA-8 `resolver` chooses a direct target, a fact-derived
  list, or all functions; `resolver_sound` depends on its client coverage laws. Index sites by
  caller and targets by site once, deduplicate edges, and build reverse callers once. Traverse
  entry reachability with a visited set in O(V+E) graph operations after indexing; Tarjan-style
  SCCs and condensation compute recursion and cycle reachability in O(V+E), counting trie key
  operations separately. A recursive function is in a nontrivial SCC or has a self-loop; a
  function that merely reaches such an SCC is not itself recursive. Directly prove the graph
  representation agrees with `call_graph`, search closure and least reachable set, and SCC
  equivalence to paths; derive the existing reachable/recursive soundness. Resolver fallback to
  all is essential for unknown targets and may create quadratic edges; report output size.
  Call-graph refinement and pointer constraints are mutually recursive: either freeze a sound
  conservative graph first or prove a combined monotone fixed point, including newly discovered
  parameter/return edges. No unverified pruning.
* **Summary, purity, stack and leaf.** The VIEW-6 summary system joins local facts with callee
  contributions; purity=false guarantees no emitted event and unchanged heap under its cover
  laws, not termination or no trap. Evaluate SCCs bottom-up, propagate deltas on reverse call
  edges, and solve recursion inside each SCC. For booleans, each component changes at most once;
  generic summary domains need their own height/rank and monotonicity. Prove indexed equations,
  SCC schedule preserves all inequalities and leastness when joins are least and transfers
  monotone. Stack demand is None if a reachable call cycle exists, including self-loops, else
  DAG maximum of nonnegative frame weights; None is conservative even for infeasible cycles.
  Prove DP against all graph paths then apply the frame-chain law. `callee_leaf` means no listed
  call site, not a no-return or externally effect-free function. External sites and callbacks
  must be represented in the view.
* **Arguments and constants.** `arg_fact` joins actual facts from `callers_index`; zero callers
  yields bottom, and missing actuals are omitted, so the soundness premises must cover arity,
  entry/external callers, and argument binding. Index `(callee, argument position)` once;
  couple actual value changes to formal facts by sparse SSA def-use worklists. Recursive calls
  require a joint fixed point, not a single pass. State exact equivalence to the existing fold
  for identical facts; interprocedural SCCP with executable edges is a new precision contract.
* **Call strings and richer interprocedural flow.** Current contexts are the last k sites and
  can require O(F * P^k) contexts plus edges. Construct only reachable contexts with a worklist,
  prove projection agrees with the full finite system on reachable contexts, and account for
  overflow/unknown contexts conservatively. k=0 must agree with context-insensitive summary.
  For a different client with finite facts and distributive transfer, IFDS computes meet over
  realizable call/return paths; the original bound is O(E D^3), not a bound for arbitrary
  summary lattices or nonlinear constant propagation. IDE adds edge functions for suitable
  value environments; general constants and heap interactions need separate hypotheses. These
  are new APIs and precision choices, not replacements for bounded strings. See the original
  [IFDS paper](https://pages.cs.wisc.edu/~fischer/cs701.f14/popl95.pdf) and the authors'
  [interprocedural research overview](https://pages.cs.wisc.edu/~reps/past-research.html).
* **No-return and mod/ref are catalogue compositions, not dedicated guarantees.** Add optional
  summaries only with owner approval: may-return initialized conservatively for unknown code,
  plus a proof that false excludes every normal return (divergence, trap and exceptional exit
  remain distinct); may-read and may-write footprints with calls, allocation, free, callbacks
  and bulk operations covered. SCC propagation is suitable for finite facts. No-return derived
  by assuming recursive cycles never return is unsound: a recursive branch may have a base
  case. Mod/ref summaries must include unknown/external effects, distinguish reads from writes,
  and treat allocation identity/lifetime and observable ordering separately from byte writes.

## Points-to, escape and fresh allocations

ANA-9 specifies flow-insensitive site-based inclusion constraints: allocation seeds, copy edges,
loads from abstract heap nodes and stores with dynamic side effects. `andersen_static` safely
lists every heap site as a possible dependency/side target, but this can cause many irrelevant
re-evaluations. Implement a second direct solver with indexed constraints, adjacency sets and
per-node delta points-to sets. When a newly discovered pointee t of p activates `x=*p`, add
heap(t) -> x; `*p=y` adds y -> heap(t). On insertion of a copy edge, propagate the source's
*already known* set as well as future deltas. Deduplicate edges and facts. The central invariant
is that all discovered facts and edges have inclusion derivations, every processed delta has
been sent along all applicable edges, and every unresolved obligation is queued. Termination
follows from a finite bounded set of node/site pairs and possible copy edges, with binary or
well-founded fuel. At quiescence all original constraints hold; induction over derivations gives
leastness. Prove equality with the least solution of `andersen_system` (when leastness premises
hold), then inherit `andersen_sound`. Charge each edge creation and each propagated fact; N
nodes and T sites allow O(NT) output facts, up to O(N²) generated copy edges and O(N²T)
edge/fact propagation in a simple bound. Trie operations, key length and dynamic-index costs
are additional. Sparse input does not promise sparse closure.

Collapse SCCs of **actual inclusion edges**: mutual inclusion entails equality of their sets.
Merging components must preserve incoming/outgoing edges, pending deltas and load/store
subscriptions; new dynamic edges can create new SCCs. An offline substitution is valid only
with a proved bidirectional semantic equivalence for its selected graph, not merely because
nodes look syntactically similar. Difference/wave propagation and selective cycle detection
are worthwhile when their proved equivalence applies, not unconditional speedups. The work on
[exploiting pointer/location equivalence](https://www.cs.utexas.edu/~lin/papers/hardekopf.pdf)
discusses these optimizations and their assumptions. Use delta propagation as the default,
with SCC/substitution passes only under their proved preconditions.

`steensgaard` unifies pointer classes rather than computing Andersen inclusion. It is a separate,
coarser result; prove preservation of unification constraints, semantic coverage, and the
contracted `steensgaard_coarser` relationship, never substitute it under an exact Andersen API.
The original [Steensgaard algorithm](https://www.microsoft.com/en-us/research/publication/points-to-analysis-in-almost-linear-time/)
claims almost-linear time and linear space for its particular representation and source model;
that bound does not automatically transfer to persistent Rocq tries, enumeration of expanded
alias pairs, or field sensitivity. Union-find cost must include encoding and persistence.

`escaped_sites` is reachability from PEscape pointees over heap points-to edges; build adjacency
once and visit each reachable site/edge once, with proof of closure and leastness. A PEscape
must cover return-to-unknown, global publication, captured closures, thread handoff and external
calls as relevant to the client. Escape of an allocation site is not necessarily escape of every
object at it, and nonescape needs a complete client view.

`PAlloc` identifies an allocation site; it does not by itself establish a globally unique result
or that a callee's returned pointer is fresh. A proposed allocation-result summary must track
normal returns, failure/null, uniqueness relative to reachable caller heap, aliasing among
returns and fresh lifetime per invocation. Prove it against a full call/heap semantics, not
activation arbitrary results. Current `zero_written_system` is a forward may-union of writes;
`z_fresh`, `z_kept` and initial laws establish zero outside accumulated covered ranges. Its
site-wide history is safe but can lose precision after an earlier object at the same site was
written. Epoch or concrete allocation identity can recover precision only with explicit
freshness, reuse and free laws, and unknown writes must invalidate it. A zero claim is conditional
on a readable byte and the client's zero-fill law; no generic allocator guarantees it.

## Accesses, dead stores, forwarding and MemorySSA

* **Validation.** `validated_system` is a forward must range analysis: successful accesses add
  validation and barriers clear it, with fuel/top fallback. `accessible_bytes` explicitly needs a
  single allocation witness for the whole positive-width range; per-byte witnesses from multiple
  site instances do not suffice. An epoch-keyed extension may invalidate just affected objects
  when precise free/resize/call summaries permit, but prove same-allocation identity and epoch
  stability through every transition. Otherwise keep the global barrier. Canonical interval sets
  and indexed site/range overlap checks avoid full list scans; prove add/remove/intersection
  preserve coverage, including empty and adjacent ranges.
* **Dead stores and forwarding.** The current backward must system removes possibly read or
  escaping bytes and adds certainly overwritten bytes. Derive the transformation only with the
  `sagree`, step, endings and effect/trap policy laws: whole-range coverage is required, partial
  overlap alone is insufficient; paths that exit, read, trap or expose bytes defeat deletion.
  Store-to-load availability is a client composition of ANA-1 `available_system`, not an
  existing dedicated theorem. Propose an explicit range/value view with endian, width, alignment,
  lifetime, read validity, overlapping writes, calls, and value reconstruction; a forwarding
  theorem proves the returned byte sequence and preserved observable behaviour, including traps.
  MemorySSA can accelerate candidates but no-clobber alone is not a value equality proof.
* **Current MemorySSA.** ANA-10's `memory_ssa` only maps each load to an optional `MDef` or
  `MLive`; the checker reverse-searches for clobbering walks and proves byte preservation under
  `bytes_laws`. It does not require the proposed def to dominate the load, completeness, phi
  nodes, or a conventional SSA graph. Its accepted no-clobber condition must be read exactly
  with its theorem premises; do not treat acceptance as a general def-use certificate.
* **Directly proved extension.** Build per-function memory versions using CFG predecessor indexes,
  dominance and iterated dominance-frontier placement, then rename along the dominator tree with
  an explicit stack. Include live-on-entry, MemoryDef, MemoryUse and predecessor-indexed
  MemoryPhi, and cover all effects and ordering operations. Prove every access has one version,
  def dominates use (phi arguments on incoming edges), renaming agrees with each concrete CFG
  path, and phi merges all incoming may-reaching versions. Then prove an alias-aware walker
  sound: every skipped def has disjoint read/write footprints; all phi branches are accounted
  for; cycles terminate with a visited/memo state; returned def/phi/live entry conservatively
  covers every feasible clobber. Give a bridge to the existing checker when its stronger
  no-clobber condition holds. The classical construction bound depends on dominance frontier
  and phi output; do not claim linear time independent of output. A single whole-memory version
  is cheaper to construct but less discriminating than partitioned versions; coarse partitions
  still need sound overlap. [LLVM's documentation](https://www.llvm.org/docs/MemorySSA.html)
  explicitly distinguishes may-reaching memory phis, lazy alias-aware walking, intraprocedural
  scope, and the possible quadratic cost of optimizing all defs. Cache entries must be keyed by
  location, graph, alias facts and effect summaries, or invalidated when any changes.
* **Immutable and invariant loads.** `immutable_sound` uses byte-frame and absence of covered
  writes; `invariant_load_sound` combines stable SSA address and disjoint loop writes, including
  callees. Index loop write footprints once, cache site/range summaries, and query overlap by
  range. Full soundness additionally depends on object existence, stable identity, readability,
  no relevant volatile/atomic semantics and the theorem's hypotheses. Results within one loop
  execution do not imply cross-activation equivalence.

## Sparse value-flow and demand

An optional staged engine can use Andersen's conservative solution to construct a sound sparse
value-flow graph (SVFG), including memory versions, call/return edges and unknown effects. Every
concrete value flow must be represented; an SSA def-use edge alone misses heap aliasing and
calls. Only then answer a demand query by backward traversal and refine flows. Strong updates
require a concrete singleton and a definitely targeted whole location; allocation-site or
bounded-context singleton is insufficient if a loop, recursion or multiple live objects can
instantiate it. If budget runs out, return the conservative preanalysis result, not partial
under-approximation. Prove graph coverage, query simulation and fallback inclusion independently.
SUPA reports 97.4% of a particular whole-program flow-sensitive baseline, 0.18 seconds and 65 KB
per query on average for 18 C programs and its stated 10,000-edge budget; those are historical
experiment results, excluding any assumption that they transfer to Gaulois or cover all costs.
See [SUPA](https://arxiv.org/abs/1701.05650) and the [SVF paper](https://yuleisui.github.io/publications/cc16.pdf).
SVF uses preanalysis, interprocedural memory SSA and configurable partitions; its precision and
setup cost differ from LLVM's single intraprocedural memory version. Demand is compelling for
few queries; repeated demands may revisit graph and exceed whole-program work. A cache requires
explicit invalidation or a proof of monotone incremental maintenance.

## Rules

RUL-1a/b contract safe finite rules, stratified negation, indexed nested-loop firing, a static
constraint system and exact stratum-wise least model; ANA-11 relates liveness, neededness and
reaching definitions to lattice solutions. The Herbrand universe is proof-only: enumerating the
full Cartesian universe in the executable algorithm would destroy scalability. Build per-relation
indexes once, choose bound-variable join order, and probe keyed tries; anti-joins for negative
literals may inspect only completed lower strata. Prove each index lookup agrees with relation
membership and each join enumerates exactly the satisfying valuations, including repeated
variables and constants. Cost join intermediate cardinalities, not merely result size.

Add a directly proved semi-naive engine: keep old and delta relations, evaluate each recursive
rule variant with at least one current delta, deduplicate against accumulated tuples, then advance
until deltas empty. With multiple recursive body literals use an ordered partition of variants
or permit duplicate candidates and deduplicate; prove all newly derivable tuples appear and no
invalid ones do. Each tuple enters the accumulated set once, but a tuple can participate in many
joins: semi-naive is not a general linear-time guarantee. Process predicate SCCs/strata in
order; do not interpret negation against an unfinished relation. Prove induction by derivation
height and quiescent closure, then equality with `least_model` and the existing `solve_program`
for well-formed stratifiable input. Preserve None on stratification failure. An incremental
extension for insertions uses deltas; deletions or a changed negative dependency require
rederivation/support tracking or rebuilding affected strata, not mere tuple subtraction.

Automatic selection among useful index orders is a separate optimization and proof obligation;
[Souffle's index-selection paper](https://souffle-lang.github.io/vldb19.html) reports up to 2x
speed and up to 6x less memory against other automated choices on its own workloads, not an
expected Gaulois result. Materializing multiple indexes consumes memory and update time. Direct
finite-set dataflow and rule evaluation serve different clients and share their established
result correspondence under ANA-11's leastness conditions.

## Proposed selection interfaces and work packages

Offer credible non-dominating choices without requiring a benchmark contest. A selector is an
explicit parameter, never a global instance. Names below are illustrative owner-review proposals:

* `points_to_backend = InclusionDelta | Unification` selects Andersen or Steensgaard. Both
  implement a semantic may-points-to soundness interface; only inclusion promises the Andersen
  least solution. A consumer requesting exact inclusion must not receive unification instead.
* `memory_ssa_backend = FrontierRename | SealedBlocks` selects two direct constructors behind a
  shared memory-version well-formedness and path-coverage interface. FrontierRename is the
  default for a complete static CFG; SealedBlocks serves incrementally assembled CFGs or sparse
  construction. Outputs need not have identical phi IDs or placement: prove observational
  equivalence of the represented may-flows where each promises it, rather than literal equality.
  Retain the existing checker as an optional boundary for externally supplied or cached legacy
  candidates; this does not claim their output has the new structure or require another builder.
* A `rule_backend` may select the current total joining solver or semi-naive evaluation: both
  promise the same perfect model on well-formed stratifiable inputs. Semi-naive is the default
  for recursive rule evaluation; the existing solver remains the contracted baseline and a
  useful general integration path, with the same exactness interface.
* Bounded call strings and IFDS/IDE are different analysis contracts, not interchangeable solver
  implementations. A proposed `interproc_mode` exposes its context and domain prerequisites:
  bounded call strings remain the default existing API; IFDS is for finite distributive fact
  problems with realizable paths; IDE is for its suitable value-function class. They share
  client semantic soundness infrastructure, not a blanket equal-precision theorem.

Each selector documents unknown-call handling, result precision, finite universes, preconditions,
failure and conservative fallback. Exact-equivalent backends share an exactness theorem; choices
with different abstractions share only the soundness theorem and any separately proved ordering.
The selector may be implemented internally without modifying the binding API; any public
extension needs the owner's ruling.

These are new cards/dependencies for owner review, not edits to existing cards or contracts:

1. **CALL-FAST** after GRA SCC/reachability, VIEW-6 and ANA-8: proved indexed call graph,
   SCC summary engine, stack DAG, caller/argument indexes and bounded-context reachable solver.
   Deliver graph agreement, least-solution equivalence and existing semantic corollaries.
2. **PTS-DELTA** after ANA-9, collections and FIX: indexed inclusion solver, dynamic-edge and
   delta invariants, exact leastness, termination; add applicable proved SCC/substitution passes.
   Keep Steensgaard as a separate coarser API. Escape reachability uses the same indexing.
3. **MEM-VERSION** after VIEW-7, ANA-9/10 and dominators: explicit memory-SSA graph and direct
   constructor, SSA/path coverage proofs and alias-aware walker. Keep current checked producer
   and establish a bridge only where its contract applies. **MEM-SEM** adds allocation epochs,
   bulk operations, mod/ref and complete interprocedural semantic laws before consumers rely on
   them. **MEM-CLIENT** adds verified forwarding/no-return as independent opt-in contracts.
4. **RULE-DELTA** after RUL-1b and ANA-11: semi-naive, indexes, exact least-model refinement and
   regression against the original engine. **IP-FLOW** adds IFDS/IDE only with its
   finite/distributive hypotheses and precise call-return semantics.

Correctness tests cover self/mutual recursion, dynamic inclusion cycles, repeated allocation
sites, partial overwrites, barriers, unknown calls, cyclic memory phis, stratified negation and
insertions/deletions. Verify proofs closed under the trust policy and compare extracted runs with
kernel-computed small fixtures. Targeted measurements in the existing harness are optional for
unresolved questions such as persistent-trie cost or memory-phi/cache behavior in a concrete
client; measure construction, query, peak memory and precision for that question, under the pinned
toolchain and caps. Measurements are not a prerequisite to offering independently justified
backends. Never claim an asymptotic bound without an explicit operation accounting model,
including trie key-bit costs and materialized output; no general complexity theorem is required.

## MemorySSA: construction choices and proof milestones

This is a retained ANA-10 deliverable, not a dropped analysis. Its planned constructor is
executable, but no constructor correctness theorem is contracted; `no_clobber_check` checks the
specific proposed `def_of_load` relation, and `no_clobber_unchanged` supplies the relevant byte
preservation theorem with its stated hypotheses. A full conventional memory-version IR below is
an additional design, and claiming it as an existing structure would overstate the contract.

Offer these non-dominating construction choices on the same effect view:

1. **Iterated dominance frontiers and rename.** For each whole-memory or sound partition, collect
   may-def blocks, compute iterated dominance frontiers, insert needed phi nodes and rename on a
   dominator tree. [Cytron et al. (1991)](https://doi.org/10.1145/115372.115320) establish
   scalar SSA construction via dominance frontiers. Using it for memory requires additional laws
   that every clobber, allocation, free, call and ordering event is represented; scalar SSA
   correctness does not itself prove memory correctness. Phi pruning requires a proved memory
   liveness criterion; removing a phi with identical operands requires equality of versions and
   semantics for cycles, not merely equal current IDs. Count frontier work and produced phis.
2. **On-demand sealed-block construction.** [Braun et al. (2013)](https://cdl.uni-saarland.de/projects/ssaconstr/)
   construct scalar SSA via backward reads and incomplete phis until predecessors are known.
   Explore it for an evolving CFG or sparse memory queries: memoize per block/partition, complete
   phis when sealed, eliminate trivial phis with a proved substitution and retain live-on-entry.
   The paper's scalar minimal/pruned claims and experiment are not already a theorem for
   may-alias memory, exceptional edges or unsealed loops. A fixed preindexed CFG plus IDF is the
   default for complete static CFGs. Offer both behind the shared semantic obligations above.
3. **Compatibility boundary.** After the owner-approved architecture change, the directly proved
   graph and walker replace the legacy constructor; project a legacy load/def pair only when its
   stronger reverse-walk property is proved. Retain the existing checker as an independently
   useful optional boundary for externally supplied or cached candidates. It need not run on
   every internal construction, and acceptance is not automatic for every valid memory graph.

Prove in layers: (a) finite graph, edge-index and instruction/effect coverage; (b) version
well-formedness, predecessor-complete phis and dominance; (c) every execution path selects a
version reflecting all preceding possible writes and order events; (d) location-specific walker
returns a conservative clobber, using only sound no-alias or disjoint-range proofs to skip defs;
(e) consumers derive byte equality, accessibility, or behaviour only from their additional
premises. May-alias says a write might clobber: retaining it is conservative. A flow-sensitive
clobber query may skip it only after a proved path/location-specific noninterference result.
MemoryPhi merges alternatives rather than asserting one definite concrete write; calls and bulk
memory effects use complete summaries, with unknown effects as barriers. Cache phi traversals
and query results by version, location, alias/effect state and CFG revision; cap walkers by
returning a conservative ancestor/phi, never by silently declaring no clobber.

Incremental edits require versioned dependencies on CFG, dominance, instructions, ranges,
points-to and callee summaries. The simplest correct initial policy is rebuild on any dependency
change; then add a directly proved updater that reestablishes the same representation and
semantic invariant. [LLVM's updater implementation](https://www.llvm.org/doxygen/MemorySSAUpdater_8cpp_source.html)
illustrates the engineering surface, not a proof or a Gaulois complexity guarantee. Test phi
insertion/removal and cyclic phis, moves across blocks, changed call targets, bulk writes,
unknown aliases and invalidated caches against a clean rebuild. For a concrete workload where
extraction or cache behavior is uncertain, optional targeted measurements can include output size
and per-query worst cases; they do not gate either directly proved construction.

## Recent research and implementation audit

Search cutoff: 2026-10-28. Queried 2023–2026 primary papers for sparse, incremental and
path-sensitive pointer/value-flow analysis, indirect calls and rule engines, and inspected the
actual paper PDFs below plus official LLVM MemorySSA, SVF and Souffle project documentation.
This is a scoped search, not a claim to have exhausted the literature or identified a universal
fastest algorithm. Findings refine the portfolio without making recent publication a proof of
superiority for Gaulois:

* [SkipFlow (2025)](https://arxiv.org/pdf/2501.19150) tracks primitive as well as object values
  and predicate edges in GraalVM Native Image's closed-world Java analysis. Its published
  experiments report 9% fewer reachable methods on average on its workloads without significant
  analysis-time increase. This is a different reachability/precision contract than ANA-9's
  flow-insensitive site inclusion system. Plan predicate-conditioned value-flow as a separate
  consumer-selectable precision extension after SSA guards, value domains and call-edge coverage
  are proved; do not relabel it as an exact Andersen optimization or assume closed world for a
  generic client. A client must conservatively model reflection, unknown code and dynamic calls.
* [Octopus (2024)](https://chengpeng-wang.github.io/publications/TOSEM23.pdf) constructs a
  guarded value-flow graph and parallelizes collection of realizable path conditions by composing
  intraprocedural segments. The paper defines its graph as acyclic, assumes field-sensitive pointer
  information and guarded edges, and then uses satisfiability reasoning; it does not remove the
  complexity of call-return realizability or SMT. Its 15-program experiment and 40-thread LLVM
  result describe that tool and workload. This motivates a separate guarded, demand-oriented
  interprocedural client, not a drop-in solver for arbitrary cyclic Gaulois systems. Prove graph
  coverage, realizability and formula soundness under explicit assumptions first; no solver axiom
  or undocumented feasibility oracle may enter core proofs.
* [IncSFS (2026 preprint)](https://arxiv.org/pdf/2608.24391) incrementally propagates both
  additions and deletions on a graph derived from full-sparse flow-sensitive C/C++ analysis.
  Its stated termination and least-fixed-point result requires the points-to relation to remain
  object-acyclic throughout analysis; the reported 9.60x/5.84x averages cover six projects and
  particular full and reset-recompute baselines. This condition excludes ordinary cyclic object
  graphs unless separately justified. Treat it as a conditional future incremental backend, with a
  proved dynamic precondition and safe rebuild/fallback on failure, not a replacement for ANA-9's
  all-input finite inclusion solver. A paper proof is not a Rocq proof.
* [CG-FSPTA (2025 preprint, revised 2026)](https://arxiv.org/pdf/2508.01974) uses a
  flow-sensitive constraint graph and Andersen-style graph optimizations. It offers a distinct
  precision/workload choice, not the same least solution as the contracted flow-insensitive
  constraints. Consider alongside sparse value-flow only after defining the flow-sensitive client
  semantics, strong updates and direct refinement proof; don't silently substitute it for ANA-9.
  [TIPS (2024)](https://yuleisui.github.io/publications/fse24b.pdf) highlights that C++ member
  function pointers mix integer and pointer flows: generic `resolver_sound` still needs client
  coverage of such representations or the all-functions fallback.

The current official [LLVM MemorySSA](https://llvm.org/docs/MemorySSA.html) remains a useful
intraprocedural single-memory-version design with lazy alias-aware walking, not a complete
interprocedural flow-sensitive pointer analysis. The current [SVF project](https://github.com/SVF-tools/SVF)
provides a practical interprocedural value-flow implementation; it does not supply Gaulois proof
obligations. [Souffle](https://souffle-lang.github.io/) demonstrates engineered relation indexing
and Datalog execution, but Gaulois still needs its own constructive exactness proof and explicit
stratified-negation contract. Classic IDF, sealed-block SSA, inclusion constraints and semi-naive
rules remain chosen because they directly address those contracts with understood proof
interfaces; the newer techniques answer additional precision, parallel or incremental questions.
No production card or public API changes follow from this audit without owner approval.
