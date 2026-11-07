Copied from the pre-redesign research notes on 2026-11-07. Card and ruling IDs refer to the retired run.

# Domains, support structures and fixpoint engines: research and proof roadmap

Research snapshot, 2026-10-28. This is a proposal, not an implementation or a claim that any
new theorem has been kernel checked. The baseline is the binding `historical API contracts` contract, not a
measurement. C18 replaces the trie traversal bound. C2–C8, C12–C14 remain binding; meaning changes
below need an owner ruling and a docs checkpoint. No source from the references should be copied.
Status moves during the run: consult the ledger; at the snapshot COL-1a, ORD-1 and BIT-1 had
landed, COL-1b was accepted and BIT-2 and DOM-1a were active. Do not disrupt those cards.

## Decision and cost model

Prioritize directly proved executable algorithms, preserving current public contracts. Offer a
consumer-selectable portfolio where credible approaches have distinct, non-dominating use cases;
document a default and its workload assumptions. Retain an optimal existing approach and replace
a clearly dominated one where the contract permits. Do not require a benchmark winner before
offering alternatives, or serially prove old and new implementations solely for comparison.
Propose additions rather than silently changing a specified algorithm, traversal order, result,
or deterministic schedule. Verification by a checker remains valuable for the existing local
solver and narrowed candidates, but is not a substitute for a direct proof of a new engine when
that proof is practical. Distinguish soundness, termination, leastness, precision and cost:
none follows automatically from another. Numeric transfers currently have soundness laws but no
monotonicity theorem. Weak joins, including wrapped intervals, do not imply least solutions.

Let `n` be live bindings, `b(k)` encoded key length, `N` visited trie nodes, `L` the sum of
emitted code lengths, `H` heap entries including stale entries, `q` live entries, `w` bit width,
`M(w)` multiplication cost, and `B` machine-word bits. Arithmetic and positive comparison are not
unit cost for arbitrary widths. Account for encoding, allocation, traversal, bigint, callback,
query, index construction and proof-erased extracted execution separately. Optional targeted
measurements can resolve specific extraction or workload uncertainty; they are not prerequisites
for offering credible alternatives. None of the references establishes a universal winner on
Gaulois workloads.

### Backend selection and shared proof interfaces

For sets and maps, default to canonical tries for arbitrary encodable keys; offer dense bitsets
for a stable, bounded, sufficiently dense universe and sparse block hybrids for mixed density.
Each exact backend implements a parametric dictionary with separate laws, refining membership,
updates and set operations to the same mathematical finite set; enumeration order is shared only
when its contract specifies it. C4 keeps public `FinSet` trie-backed until an owner ruling permits
otherwise. For flat list tables, use the contracted representation by default; offer a prefix
table for repeated long common prefixes with exact lookup/update refinement and a separate
enumeration interface if order differs. For the queue, retain the contracted persistent queue as
default, and offer dense-rank buckets where static compact priorities make them appropriate;
both must preserve the specified minimum, decrease-key and tie behavior.

For numeric facts, default to the contracted domain selected by the client: constants and signs
for inexpensive coarse reasoning, intervals for ordinary bounds, wrapped intervals for modular
arithmetic, known bits for masks, congruences for strides, and reduced products when correlation
matters. These are consumer choices under shared `word_domain` soundness laws, not interchangeable
exact-result implementations. A bounded disjunction is a separate precision/cost choice.
For engines, default to the existing priority worklist, with RPO for general forward flow;
offer SCC, WTO priority, directly proved nested WTO, and eventually WPO where their graph and
concurrency assumptions apply. They share post-solution and applicable termination interfaces,
not equality of widened answers. Pure alternatives share index and query proofs; adding a
parallel extracted runtime needs a separate trust and refinement decision.

## Collections and representation (COL-ENC/TRIE/MAP/QUEUE/UF/TABLE)

* **Encoding and tries.** Current pair/list encoding doubles bits and terminates each field;
  construction and lookup are O(total encoded bits), potentially much larger than the number of
  keys. Uncompressed LSB-first canonical tries have lookup/update O(b(k)) and share unchanged
  paths; combine visits two input node structures, and `union_with` shares one-sided subtrees.
  C18 makes fold/elements O(N + L) plus callbacks. Sparse long codes and nested products make
  depth and L expensive. Canonical shapes enable propositional extensional equality; a balanced
  tree or compressed radix trie needs a fresh canonicity proof, not just extensional lookup.
  [Appel and Leroy 2023](https://www.cs.princeton.edu/~appel/papers/ptree.pdf) proved and
  benchmarked extensional binary tries in Coq and extracted OCaml; results support this baseline,
  not an imported implementation. [Appel 2011][redblack] gives a verified balanced-tree alternative
  and adaptive set operations, but a generic ordered
  dictionary changes the C4 representation and equality interface.
* **Dense numbering and bitsets.** Build an injective finite `K <-> [0,n)` index once and prove
  inverse, coverage and membership. Packed words use O(n/B) storage and union/intersection scan
  O(n/B) words; sparse tries use space proportional to occupied paths and can win at low density.
  Sparse/dense hybrid block containers improve mixed workloads but introduce conversion and
  normalization costs. [Roaring 2016](https://arxiv.org/abs/1603.06549) evaluates bitmaps on
  database datasets, including cases favoring runs; it does not measure persistent Gallina sets.
  Add a separate finite-universe carrier and prove `mem`, set algebra and height by refinement to
  `FinSet`; C4 means this cannot silently replace public `FinSet` storage. Dense IDs need stable
  versions and an explicit mapping when edited graphs or serialized caches change.
* **Queue.** The contract permits a leftist heap plus live trie map with lazy deletion: a push
  adds at most one physical entry and a pop may discard arbitrarily many stale entries. A single
  pop is not O(log q); work depends on `H`, stale count, priority/code bit comparisons and trie
  lookups. Prove heap order, live-entry coverage, size and lexicographic minimum and amortize stale
  removals over insertions on a linear execution. Persistence and branching require a separate
  cost argument. Evaluate a verified periodic rebuild or an indexed heap/priority buckets for
  static dense ranks, retaining exact decrease-key semantics and tie order. Rebuild from live map
  costs enumeration O(N+L) and needs a measured threshold; buckets can cost O(number of ranks)
  when searching empties. API `members` order and persistent behaviour must remain intact.
* **Union-find.** Current rank-strict parent links justify `S max_rank` fuel and path compression;
  each traversed link involves encoded-map lookup/update, so charge their bit lengths. Show
  compression preserves representatives and the entire partition, rank strictly increases on
  edges, and linking preserves disjoint classes; `max_rank` bounds recursion. Do not claim the
  imperative inverse-Ackermann bound for arbitrary persistent branches or trie costs. The
  [Conchon–Filliâtre 2007](https://usr.lmf.cnrs.fr/~jcf/ftp/publis/puf-wml07.pdf) approach uses
  hidden mutation and a separately verified model; [Charguéraud–Pottier 2017][uf] proves an
  imperative complexity bound using separation logic. Neither implies a bound here.
  A dense pure vector/persistent-array variant needs a new refinement proof, version ownership and
  extraction trust decision. Equality partitions also require `forget`, which union-find alone
  cannot implement by merely deleting one parent link.
* **Tables.** Current flat list encoding repeats doubled field bits for every lookup and does not
  share list prefixes; hash-consing incurs encode plus O(sum field bit lengths). A nested trie
  keyed per operand could share prefixes; prove lookup, overwrite, remove, empty-list and
  enumeration order equivalence, or introduce a separate table if order differs. Constant/hash
  caching is correct only with proof of equality and collision resolution. No unverified hash or
  pointer identity may serve as equality evidence.

## Lattices, words and domain representation (ORD/BIT/DOM)

* **Combinators and finite carriers.** Weak-law explicit dictionaries, erased `Prop` laws and
  separate `lub_laws` preserve typed extraction. Current products are componentwise; reduced
  comparison reduces the left side and join reduces the result, while widening deliberately
  avoids reduction. Prove reduction reductive, concretization preserving and bottom-compatible,
  then prove rank decreases even across joins. Do not infer widening termination merely from
  reduction soundness. Bounded disjunction uses O(k²) element comparisons, compact and a cap;
  retaining antichains or merging closest disjuncts can improve precision at extra comparisons
  and sorting. A different selection/tie policy changes answers. Prove coverage of every input,
  cap and rank, plus leastness only under explicit hypotheses. Finite-universe ranks are ghost
  proofs; they do not justify repeated runtime universe scans.
* **Bits evaluation.** `BIT-1/2` uses Z and total SMT-style division, including zero divisor and
  oversized shifts; rotations, signed division, minimum signed value and width-zero cases need
  exact contract semantics. Each operation uses a constant number of bigint operations, not O(1)
  bit time; multiplication/division depend on operand lengths, and current popcount scans w bits.
  Prove a divide-and-conquer popcount against `Z.testbit`, with termination and operation-count
  bounds, and preserve zero/count behaviour. Measure selected widths only if extracted performance
  remains uncertain. Expression evaluation is O(tree size) plus operator and bigint costs;
  DAG hash-consing shares repeated syntax only if evaluation preserves every operand order,
  width, and `None` case. Directly prove evaluator refinement before specializing extraction;
  native machine integers require a separately proved range/overflow correspondence or trusted
  extraction mapping, especially for arbitrary width. See the official
  [SMT-LIB fixed-size bitvector theory](https://smt-lib.org/theories-FixedSizeBitVectors.shtml)
  for semantics; pinned contract takes precedence over evolving online text.
* **Constants/signs/integer intervals.** Constant and three-bit sign transfers are cheap but
  lose nonconstant numeric correlations; unsigned intervals hull values and fall back to full
  range on possible overflow. Wider thresholds improve some invariants but may increase iterations.
  Pre-sort/deduplicate thresholds once; a balanced search preserves *nearest threshold* semantics,
  with O(log t) comparisons after O(t log t) preparation, each comparison charged by integer size.
  Distinguish that from [Kim et al. 2016](https://prl.korea.ac.kr/papers/spe15-kimhoy.pdf), whose
  binary-search widening changes the sequence of thresholds and precision: their reported 81.5%
  efficiency improvement and 20.9% precision compromise are experiment-specific. Prove ordered
  search returns the same threshold and preserve rank; changed widening requires a new contract.
* **Known bits.** Current zero/one masks admit contradictory bits as bottom; exact bitwise and
  constant-shift transfers and carry-based add/sub precede a coarse multiply (only low zero bits
  except constants). Prove carry reachability by bit induction, then refine the stronger tnum
  multiply directly against modular multiplication, including normalization and bottom. The
  [tnum paper (2022)](https://arxiv.org/abs/2105.05398) proves optimal add/sub for its model and
  reports 33% average speedup for its multiplication versus the then Linux implementation in a
  per-input cycle microbenchmark (393 vs 262 cycles), not total analyzer speed. Translate its
  value/mask convention carefully to zero/one masks. Optimality does not
  transfer automatically to Gaulois's noncanonical contradictory masks. Variable shifts by
  enumerating feasible amounts can grow exponentially if implemented by enumerating values; scan
  only distinct relevant amounts, treating amounts >= width according to each operation, and
  prove equivalence of the join. A better formula must prove inclusion and any precision claim.
* **Wrapped intervals and congruence.** Wrapped arcs retain useful overflow facts, unlike ordinary
  intervals; their cover is not generally a least upper bound and meet can only guarantee the
  specified left lower bound. Prove circular offset membership, covering and normalization,
  partition at signed/unsigned poles, and `log2` rank under the specified widening. A bounded
  union of arcs captures disconnected intersections at O(k²) comparisons but changes carrier,
  widening and results. [Gange et al. 2014][wrapped] analyzes wrapped machine arithmetic and
  reports experimental tradeoffs, not a universal bound.
  Congruences retain stride/alignment; prove gcd join, Chinese-remainder meet, finite-width
  normalization and gcd with 2^w on wrap, including modulus zero and negative residues. Charge
  Euclidean gcd/division by bigint size. Interval–congruence endpoint rounding and bit–arc
  reduction need inclusion in both directions for every concrete word, bottom detection and rank
  preservation; two rounds are sound only after each individual reduction is proved. Iterate to
  a fixed point only with a new termination measure and evidence of useful precision gains.
  [Verasco 2015](https://xavierleroy.org/publi/verasco-popl2015.pdf) demonstrates a directly
  proved modular combination including intervals, congruences, floats and points-to; it is a
  feasibility precedent, not a source-code dependency.
* **Demanded bits.** Existing mask agreement is relational: prove each backward rule from two
  concrete evaluations, with constants holding for both states, widths and result defined.
  Carries justify fill-down for add/sub/mul; shifts must treat large amounts and sign extension;
  `ite` must preserve condition and selected branch, and traps are handled by client view laws.
  Forward known bits can refine variable shifts and masks, but requires an extended premise and
  monotonicity in demand, not just tests. Prove the refined mask sound and its claimed inclusion;
  changing named `demand` results needs the relevant contract review.
* **Addresses, ranges and equality.** Current points-to finite sets support precise finite targets
  but unions cost visited trie nodes; top trades precision for a bound. Sorted disjoint byte ranges
  admit O(r+s) merge, with full-range or unknown-object representations for conservative overlap.
  A tree improves isolated updates to O(log r) plus output but adds normalization; bitsets fit
  compact bounded byte regions and waste space on sparse offsets. Must-ranges use reverse
  inclusion and must not inherit may-union semantics. Equality partition join groups pairs of
  representatives, charging all find and pair-code costs; union-find is efficient for merge but
  forgetting and joins need rebuilding or persistent membership indexes. Prove all concretizations,
  overlap containment, sorted-disjoint normalization, partition equivalence and hash-cons
  injectivity, including deletion and object provenance.
* **Floating point and NaN.** FLT-1 directs outward rounded Flocq bounds with explicit NaN,
  signed-zero and subnormal flags; per-operation constant *count* of Flocq calls does not mean
  constant bit complexity for arbitrary `prec`/`emax`. Directed rounding, infinities, zero division,
  underflow and NaN propagation require separate soundness lemmas; preserve payload/sign only as
  demanded and account for client traps and non-float observations. Naive host floats change the
  rounding/trust model. Split finite signed ranges or affine/error domains may improve precision
  but increase transfer cost and need new γ, joins and termination proofs. [Flocq 2011][flocq]
  supplies the formal arithmetic foundation; C13 allows only the enumerated Flocq real axioms in
  Float. Verify assumptions for every claim rather than extending that allowance to core.

## Solvers, schedules and precision (FIX)

* **Direct worklist proof.** Ret/Ask/Side records both actual reads and contributions. Preserve
  the invariant: every unqueued constraint is satisfied at its last evaluation unless an observed
  read has changed, in which case it is queued; all side outputs are processed in their stated
  order. Declared readers overapproximate all possible reads and side targets; Recorded readers
  accumulate actual reads and require initial scheduling of every constraint. Queue emptiness
  yields the full post-solution. Prove each update is extensive, all requeues occur, and top
  fallback is sound. `solve_total` additionally needs a finite unknown/support bound and a
  well-founded measure across queue activity and finite-height or widening-rank updates; cycle
  cuts alone do not show the individual rank exists. The binary fuel loop has logarithmic stack
  depth, but n steps still cost n evaluations and fuel exhaustion returns top.
* **Schedules.** Current RPO, SCC and WTO strategies assign *static priorities* to the same
  global queue and select widening points; current WTO is not Bourdoncle's nested stabilization.
  RPO is cheap and good for forward acyclic flow, SCC confines cyclic work, and WTO can reduce
  widening locations, but with nonassociative weak joins or widening their outputs can differ.
  [Bourdoncle 1993][wto]
  gives nested iteration and admissible widening points. Add a separate directly verified nested
  iterator: component frames, dirty dependencies, exit only after all internal constraints are
  stable, side outputs awaken the correct enclosing frame, and valid heads cut cycles. Prove
  post-solution and termination; compare exact outputs only under stated stronger conditions.
  Account for preprocessing and fallback (all heads may reduce precision) in selection guidance.
* **Parallelism.** [Kim, Venet and Thakur 2020][wpo]
  construct weak partial orders and a deterministic parallel strategy; on 1,017 C programs they
  report arithmetic mean 2.06x on four cores and maximum 10.97x on 16, relative to IKOS. Their
  1,017 programs exclude cases where IKOS took under five seconds.
  It is not evidence for this implementation. WPO regions need dependency and nesting checks;
  deterministic publication of contributions, barriers and handling of side effects require a
  proof of equivalence to a specified sequential trace or a direct post-solution proof. Mutable
  OCaml parallel queues, memory ordering and primitive extraction expand trust unless independently
  verified; start with a pure sequential model and explicit refinement before considering them.
* **Widening, narrowing and local work.** Threshold widening can improve loop bounds but alter
  cost; delaying widening needs finite delay in the termination measure. Narrowing currently
  computes simultaneous rounds and keeps the candidate only if full checking passes. Directly
  prove a specialized narrowing preserves post-solution when possible; retain checked fallback
  for arbitrary user passes, and count one RHS evaluation per constraint per round plus checking.
  The existing local solver explores the *static dependency closure*, potentially the entire
  graph, and its checker establishes only a closed partial solution. Dynamic demand-driven
  solving can avoid untouched branches, but side effects can create new contributors: prove
  coverage/closure and detect dependency changes, or return only the existing checked guarantee.
  [Apinis et al. 2012](https://ut.ee/~vesal/papers/Apinis_2012_SCS.pdf) describes side-effecting
  local systems; [Apinis et al. 2018](https://kodu.ut.ee/~vesal/papers/Apinis_2018_MAP.pdf)
  addresses map-based demand solving. Incremental caches must track reverse dependencies,
  versions, deleted contributions and graph/transfer changes; a prior post-solution can remain
  sound but unnecessarily imprecise after deletion. Recompute affected SCCs from bottom when
  leastness/precision matters; prove invalidation completeness and compare with a fresh run.
  [Demanded abstract interpretation 2021](https://arxiv.org/abs/2104.01270) reports 95% of its
  interactive queries within 1.2s for its prototype, not Gaulois.

## Recent evidence and its scope

Search cutoff is 2026-10-28. Searches covered 2023–2026 bitvector domains, abstract
transformers, verified and parallel fixpoint engines, memory-efficient iteration, and current
Linux tnum implementation; this is a targeted search, not an exhaustive literature survey.
Primary papers and official artifacts were preferred. The 2022 tnum and 2020 WPO PDFs were
inspected for the numerical results above; their results are historical, workload-specific
experiments. The current [Linux tnum source][linux-tnum] is a moving implementation, so pin a
commit before a reproducibility comparison; it does not
prove Gaulois's implementation or semantics.

* [Fan et al. 2025](https://doi.org/10.1145/3728905) propose a signedness-aware reduced
  combination of generalized bit and bound information, with Crab and PREVAIL implementations.
  Plan a selectable word-domain product using shared reduction soundness infrastructure. It has
  a distinct precision/cost profile; its transformers and reductions need direct proofs for
  Gaulois widths and total operations. Publisher full text was inaccessible in this search, so
  this assessment is limited to the primary abstract; no unverified quantitative claim is used.
* [Kim 2025](https://escholarship.org/uc/item/7vv0w22q) and the related
  [memory-efficient fixpoint paper](https://link.springer.com/article/10.1007/s10703-025-00471-8)
  describe retaining only facts needed by a fixed recursive WTO strategy, with the same result
  and a memory-optimality claim for that model. The paper reports mean peak-memory reductions of
  24.57x for assertion verification and 2.29x for buffer analysis against IKOS, on its own
  datasets. Add `FIX-MEM` after `FIX-NEST`: prove liveness of cached facts, safe eviction and
  replay, and exact equality with that fixed sequential iterator including side contributions.
  Static dependencies and the chosen scheduling model are required; no claim extends directly to
  Gaulois's dynamic systems or WPO. This is a selectable memory-conscious mode sharing solver
  interfaces, with proof and extraction trust as above.
* [Spear 2026](https://arxiv.org/abs/2606.16229) uses parallel bitvector optimization to
  synthesize best transformers. It is useful for generating candidate formulas offline, not as
  evidence that a generated Gaulois transformer is sound or optimal. Independently prove any
  chosen formula in Rocq; no external solver becomes a core dependency.

The classic trie, tnum, interval and WTO sources remain useful because they describe the actual
contracted models and supply proof strategies. Recent work broadens the portfolio; it does not
establish a single fastest backend across workloads or override the contracts.

## Concrete proposals, dependencies and targeted checks

1. **Within current cards:** prove COL-1b/1c, COL-2, BIT-2, ORD-2, DOM-1 through DOM-7, FIX-1
   through FIX-4 and FLT-1 against their actual contracts. Record C14 corrections exactly; do not
   change semantics. Correctness tests and the contracted proof claims remain mandatory.
2. **New COL-DENSE and ORD-DENSE:** after COL-1c and ORD-2, propose a separate finite-universe
   numbering record (encode/decode and coverage laws), packed-set carrier and direct refinement
   of every operation to FinSet. Decide extraction representation and cross-version identity at
   the docs checkpoint; do not change C4 implicitly. Offer dense and sparse use cases without a
   benchmarking prerequisite.
3. **New BIT-FAST / DOM-TNUM:** after BIT-2 and DOM-2, add proved popcount and stronger
   multiplication with explicit soundness and precision inclusion. Do not prove and maintain an
   old implementation solely as a comparison oracle. If replacing specified transfers, request
   an owner ruling and update `bits.md`,
   `domains.md` and the card; prove two-state demand compatibility separately.
4. **New FIX-NEST / FIX-INCR / FIX-WPO:** after FIX-1–3 and Graph WTO, define distinct nested,
   incremental and WPO interfaces with exact side/read semantics. Prove post-solution and
   termination first; add leastness only with `lub_laws`, monotonicity and fair scheduling.
   Include direct refinement to the contracted engine where equality is valid; it need not be
   valid for widened outputs. Parallel implementation follows the pure model and a trust ruling.
5. **New DOM-REDUCE / FLT-EXT:** after DOM-4/FLT-1, prove reduction preservation and extra
   operations individually; define rank for any new iteration. A stronger abstract transformer
   is admissible only under the actual API's stated latitude, otherwise obtain a ruling.

Use existing harnesses for optional targeted measurements when a specific uncertainty remains,
such as extracted wide-word popcount, heap stale-entry buildup, or dense-set crossover for a
known client workload. Include preparation costs and relevant allocation and query counts in
that measurement. Do not build a custom benchmark project or require measurements before
offering the portfolio. Correctness examples should cover wrap, zero division, oversized shifts,
NaNs, subnormals, side contributions and irreducible cycles. Tiny exhaustive checks are
diagnostic only, not proofs; audit claims and extraction assumptions separately.

Coverage map: COL-ENC/TRIE/MAP/QUEUE/UF/TABLE; ORD-CORE/COMB/SETS; BIT-WORD/OPS/EXPR;
FIX-QUERY/FULL/CUT/REPLAY/FUEL/TOTAL/SCHED/NARROW/LOCAL; DOM numeric, demand, memory and equality;
FLT intervals, NaN and SSA bridge. Cut checking and replay remain the existing direct proof
obligations: expansion respects each side contributor and topological dependency; replay is a
fold over the same point/fact observations. Rules and client-specific analyses are covered by
the separate inventory and analysis tracks.

[uf]: https://gallium.inria.fr/~fpottier/dev/uf/
[redblack]: https://www.cs.princeton.edu/~appel/papers/redblack.pdf
[wrapped]: https://jorgenavas.github.io/papers/ACM-TOPLAS-wrapped.pdf
[flocq]: https://guillaume.melquiond.fr/doc/11-arith20-article.pdf
[wto]: https://citeseerx.ist.psu.edu/document?doi=169dc1991ada9a611045d8938639f56d60d6095a
[wpo]: https://thakur.cs.ucdavis.edu/assets/pubs/POPL2020.pdf
[linux-tnum]: https://github.com/torvalds/linux/blob/master/kernel/bpf/tnum.c
