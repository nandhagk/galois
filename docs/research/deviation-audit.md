Copied from the pre-redesign research notes on 2026-11-07. Card and ruling IDs refer to the retired run.

# Investigation of potentially adverse algorithm choices

Snapshot: `1dbd346be0a3702e4010da8b51dcee44cc749c2c`; live ledger consulted during this
investigation. This is source inspection and mathematical analysis, not a build, proof replay,
benchmark or native runtime comparison. It uses reviewed prior investigations as explicitly cited
below; it does not independently recheck every proof or every operation in the library. Source
costs are charged separately from extracted behavior. Priority reflects possible consequence and
evidence, not measured prevalence. The owner approved classic graph backends and the C19 deferred
Rewrite scope; these are not implementation failures.

## Executive matrix

1. IDE: `k^k` function materialization; finite-carrier scope.
2. Rewrite: quartic pair-comparison family; source cost.
3. SCEV: exponential wrapped first-failure search, despite the landed cache.
4. DOM-9 widening: exponential strict-improvement chain.
5. DOM-8 multiplication: counterexamples in both component-precision directions.
6. MemorySSA: conservative cuts, whole-memory precision and retained phi costs.
7. Graph and collections: encoded-key and persistent-operation cost risks.
8. Float: documented zero-sign and division-hull precision loss.
9. SSA and PRE: query costs, restricted clients and unproved optimality.
10. Solvers, Rules and products: preparation and bounded-reduction risks.

The detailed sections distinguish semantic results, costs, soundness and proof guarantees.
The first engineering candidates are narrow: SCEV's unsigned unit-step fast path, reusable
MemorySSA preparation and acyclic memoization, and Rewrite's set-backed pair queue. IDE can
begin with a finite, client-supplied transformer registry. These require interface and soundness
proofs, but do not first require general infinite-carrier IDE, modular first-hit arithmetic,
partitioned memory or a new Rewrite objective. A benchmark is not needed to establish the
analytical families and counterexamples; measurements answer practical workload questions.

## Multiplier comparison

[CGO 2022 §III, Listings 3–4, pp. 259–261](https://people.cs.rutgers.edu/~sn349/papers/cgo-2022.pdf)
uses separate value and uncertainty accumulators; Listing 4 initializes the former with the
concrete product and adds the latter at the end. `DomainsKnownBitsFast.v:18–34` instead executes
exactly `w` stages over the second operand, adds the shifted first operand for a known one, and
joins the old and added result for an unknown bit. It is not Listing 4's `our_mul`. DOM-2's
`DomainsKnownBits.v:751–757` uses constants or a low-zero approximation. C37 and
`DomainsSignedBoundsDomain.v:840–856` select DOM-8 by default and retain DOM-2 as classic.
The older DOM-9 audit’s default-multiplier comparison predates C37.

An independently written finite value/mask model uses the current `tnum_adc` equations at
`DomainsKnownBits.v:545–553,611–624`, bit-copy scalar shift at lines 904–906 and 1252–1253,
and the actual iteration order. For the paper, P is the second operand and Q the first.
The five-bit results below are hand-checkable model observations, not Rocq theorems:

| First operand | Second operand | DOM-8 `(value, mask)` | Paper `(value, mask)` | Inclusion |
| --- | --- | --- | --- | --- |
| `3` | `{1,3}` | `(1,10)` | `(1,14)` | DOM-8 is strictly tighter. |
| `3` | `{6,7}` | `(0,31)` | `(16,7)` | Paper is strictly tighter; products are `{18,21}`. |

For the second row, the unknown low bit joins 0 and 3, obtaining `(0,3)`; adding 6 gives
`(0,15)` and adding 12 gives top. The paper's value accumulator is 18, its uncertainty mask is
3, and the final addition gives `(16,7)`. For the first row, after adding 3, joining with its
addition to 6 gives `(1,10)`; paper adds value 3 to uncertainty `(0,6)`, yielding `(1,14)`.
The result encodings denote all words agreeing on fixed bits, not just the concrete products.
These examples show neither algorithm dominates the other at the component level. They do not
establish a whole-DOM-9 comparison, where bounds and reduction also matter. For the second
example, bounds `[18,21]` remove the difference. The diagnostic `multiplier.js` records the
independent finite model and witness checks.
It and `witness-bigint.js` ran with the pinned Node binary under a 4 GiB scope and 20 second
timeout; the latter checks all concrete products for both witnesses. Neither is a kernel-checked
example. The exact commands, exit statuses and file hashes are in `MANIFEST.md` in this directory.

DOM-8 does at most `w` abstract additions, up to `w` joins and `w` scalar shifts, and always
visits all `w` bit positions. Listing 4 stops when the multiplier value and mask become zero.
It has one concrete multiplication, at most one abstract addition per active bit, and a final
addition.
That is a source-operation comparison: DOM-8's shifts apply the word operation to the min and max
masks, and `Z` arithmetic, masking, shifting and width construction have nonconstant bit costs.
`N.iter` and extracted bigints also need actual backend inspection before runtime conclusions.
An independently authored Listing 4 alternative can use the existing word-domain dictionary;
prove soundness, bottom and width handling, and dictionary laws. Optionally expose a new word
domain that meets both sound
results, proving intersection preserves every concrete product. It can coexist with the present
domains. Making it the default or changing an existing public meaning requires an owner ruling;
retain the original choices.

## DOM-9 and the 2025 bit/bounds paper

[Fan et al., §§4–6 and Figs. 4, 5 and 7](https://doi.org/10.1145/3728905) describe sign-split
bit and interval operations and a per-hemisphere doubling widening. The independently reviewed
`historical research note paper-3728905-audit.md` examines the supplied complete main paper and the source
artifact at [Zenodo](https://zenodo.org/records/14024794); the paper refers to supplements whose
full transfer specifications were not separately identified. The artifact is implementation
evidence, not an invented specification for missing paper text.

Exact component-hull reduction is stronger than the printed three exchanges for 4-bit zero-sign
`T={0,4}`, interval `[1,6]`: their joint set is `{4}`, but the printed steps leave `T={0,4}`
and `[1,4]`. `DomainsSignedBounds.v:343–354` implements per-half reduction and
`DomainsSignedBoundsDomain.v:90–105` joins via reduction. This is a component distinction:
reduction preserves joint concretization, so the result does not establish a smaller represented
set or a generally better whole analysis. Its implementation and the prior audit's mathematical
argument were not recompiled here.

Operation comparison, with paper sections and missing details as described above:

- Add, subtract and negate: current carry and wrapped transfers have no established ordering.
- Multiply: default DOM-8 and classic DOM-2 both use DOM-3 bounds; component witnesses do not
  establish whole-product dominance. The older DOM-2 witness applies only to classic.
- Unsigned divide: compare the leading-zero transfer, Fig. 4 and zero-divisor conventions.
- Signed divide and remainders: coarse component transfers create a structural precision risk;
  missing supplement details prevent a full relative comparison.
- AND, OR, XOR and NOT: bit and bounds information is complementary; no blanket ordering.
- Variable shifts: an earlier reviewed artifact-specific witness uses `64 >> {0,4}` at width 8.
  DOM-2 excludes 32; the inspected artifact joins intermediate counts and retains 32.
- Truncation, extensions, comparisons: printed rules are partial; parity remains unknown.
- Counts, extracts, concatenation, rotations, `ite` and malformed shapes: the printed paper does
  not supply a comparable complete operation suite. Current shape fallbacks remain sound.
- Join and widening: current join permits the following long chain; the paper uses doubling.

For `w >= 2`, take the exact half abstraction of `[0,k]`, for successive `k` from zero through
`2^(w-1)-1`, with the other half empty. Joining the next singleton yields the exact hull of the
expanded interval, so every step changes the represented set. This admits exponentially many
strict improvements in `w`; realizing the sequence in a particular solver depends on its transfer
and schedule. `DomainsSignedBoundsDomain.v:193–200,252–269,304–310` uses span plus known-bit
rank; its bound is `2 * (1 + 2w + 2^w)`. The paper's doubling does not imply a direct bound on
Gaulois as implemented. As a first stage, implement a separate widening dictionary for endpoint
thresholds or doubling.
Prove enclosure of both inputs, sign-range handling, gamma preservation of reduction and a
decreasing finite rank even after reduction. Keep the existing dictionary selectable.
It can overshoot compared with join, so the choice changes answers and requires a new ruling.

## Rewrite: demonstrated source-level cost family

`RewriteRebuild.v:116–135` groups application partners by operator, then generates all ordered
pairs in each bucket. For `m` distinct same-operator application nodes with unique IDs and unique
bucket entries, this produces exactly `m²` distinct pairs. `rw_rebuild` at lines 892–900 invokes
Stdlib list `nodup` on this universe. For a unique list of length `n`, the usual Stdlib `nodup`
uses a linear membership search over the remaining list for each element, giving `n(n-1)/2` pair
equality calls: Θ(m⁴), plus encoded positive comparison cost. This is an analytical source-work
family. The pinned Stdlib 9.2.0 `Lists/List.v:2647–2650` confirms that `nodup` tests membership
in the tail, and `nix develop` identifies that package in `ROCQPATH`. No benchmark or machine-time
bound follows. `rw_enqueue` at lines 240–243 also deduplicates newly generated pairs plus pending
work. `RewriteRun.v:235–250` calls rebuild after a successful accepted union, including on the
prepared run path; rejected attempts do not necessarily rebuild. REW-2's ledger already records
pair-cost concerns.

[egg §3](https://arxiv.org/abs/2004.03082) describes rebuilding around canonical signatures and
batched restoration. It does not establish its native runtime on this library or provide a proof
for a new implementation. A small optional replacement should maintain canonical-node signature
and parent incidence tables and process dirty parents after each merge, preserving lookup,
congruence closure, sort and soundness invariants. Directly prove a clean sound extension, finite
witness preservation and any observable matching/extraction agreement; a different merge order
can affect scheduled finite runs, so do not silently promise identical bounded outcomes. A trie
set for pending pairs alone can reduce repeated list membership costs while preserving the pair
universe, but needs a deterministic order or an explicit result-order contract.

The extractor's optimum is for finite materialized additive tree cost
(`RewriteExtract.v:331` and `historical design and trust documents`); shared DAG/program cost is a different objective.
No fairness or full saturation guarantee follows from bounded attempts. A timeout in another
engine also limits completeness, so boundedness alone is not a comparative defect. The facade can
return `None` when explanation construction fails. C19 explicitly approves deferred global DAG,
binder and context extensions; these are scope choices, not regressions.

## IDE and IFDS

`AnalysesInterprocedural.v:842–862` requires `ide_values` to contain every value of the entire
carrier and requires distributivity; lines 896, 1044, 1149–1182 enumerate all output vectors
and combine each with each fact. For `k` distinct carrier values the function list has exactly
`k^k` length, and the lifted fact universe includes one such table for each distinct optional
fact. Encoding, list generation, index construction, and storing tables cost more than merely
counting functions. `IdeTab.contributions` at line 1465 scans the product of vertices and all
function keys; `ide_solve` at line 1545 exposes that path. This family holds even for a problem
with one actual identity edge function.
It is a source-level combinatorial cost, not evidence of a measured runtime or proof that the
original IDE implementation always performs less work on every problem. Original IDE supports
suitable distributive edge functions without requiring the whole lattice carrier to be explicitly
enumerated; see [Sagiv, Reps and Horwitz’s TAPSOFT 1995 IDE paper][ide]. The API also cites
the POPL 1996 version. The POPL 1995 IFDS paper is a distinct work.
Infinite fact sets are outside IFDS itself; do not call that a departure. Gaulois preserves
matched call/return paths for its supplied finite problem, not bounded-callstring approximations.
Other call-summary algorithms and call strings in `AnalysesCallScc.v:771,1226–1252` are distinct
client choices, not the IFDS path semantics.

The first stage is a separate on-demand registry for a client-supplied finite closed set of
canonical transformers. Prove identity membership, closure under composition and pointwise join,
decidable extensional equality and table evaluation agreement. Then prove that indexed reachability
and all path joins agree with the existing finite IDE semantics, including reachable bottom.
It can avoid `k^k` when the registered closure is small but
may still reach it. Supporting nonenumerable lattices needs a different algebraic interface,
termination argument and public contract, not merely this optimization. Neither change weakens
the existing exact matched-path guarantee.

## MemorySSA

At snapshot, ANA-10a through ANA-10e are landed; ANA-10f is **in review**, and EX-7 is **active**
in the fresh ledger. These are moving run statuses, not negative findings about the review branch.
The frontier/rename constructor is in `AnalysesMemoryFrontier.v:689–699`; the sealed-block
constructor is in `AnalysesMemorySealed.v:381–430,1522–1533`. Both exist. The latter installs
whole-memory `MemoryPhi` entries when recording predecessor edges and retains a graph satisfying
its current graph laws; it does not visibly perform a separate trivial-phi elimination. That can
leave more graph nodes and walker steps than a pruned representation; the precise amount depends
on the CFG and constructor, and no timing is established.

`AnalysesMemoryWalk.v:16–20,39–51` skips a definition only when effects prove the write scope
disjoint from the query and follows phi operands. Unknown calls and other unknown scopes are
conservative clobbers. Lines 74–86 and 169–175 retain cuts for revisits and fuel, while lines
733–785 report roots and an explicit completeness bit. Any repeated version, including
convergent acyclic or parallel paths, can produce an incomplete
result; more fuel alone cannot necessarily remove a revisit cut. A duplicate terminal may only
change the completeness flag and need not change the roots. `AnalysesMemoryLegacy.v:519` uses
the roots, so a false completeness flag alone does not prove a lost legacy forwarding result.

A concrete source-derived DAG witness shows more than a false completeness flag. Let a reachable
edge contain two ordered writes: P writes the queried region and D writes a disjoint region.
Its target has two distinct empty parallel edges into a non-entry phi node; both phi operands
are D. A load after that phi queries P's region. The graph's incoming edges are distinct and
`GraphCore.v:41–46` does not prohibit parallel endpoints. The memory flow and operand requirements
at `AnalysesMemoryGraph.v:81–109` admit this shape: P precedes D, each empty edge carries D, and
the phi has one operand per edge. With sufficient fuel, the walk expands phi, D and then P;
on encountering D a second time it retains D as a revisit cut. The deduplicated roots are
`{D,P}`, so `legacy_clobber_proposal` returns `None` for the two roots. A completed acyclic
memoized walk can reuse D's already determined terminal P and propose P. Legacy's subsequent
`legacy_pair_check` still decides acceptance; this witness establishes the missed proposal, not
an independently proved final forwarding result. This is a hand-derived source-graph example,
not a constructed or kernel-checked Rocq instance. A cycle-safe memoized walk needs proofs of
terminal coverage and unchanged conservative behavior for in-progress cyclic visits.

Partitioned memory and richer byte/site/call summaries can
reduce false clobbers, but only if their client-provided alias and effect facts are sound.
Each `memory_clobbers` call builds `memory_walk_index` at lines 585–591,733–741: it prepares
the CFG, effect table and adjacency for all listed memory versions, even for a local query.
For Q queries this repeats that preparation Q times; charge graph, effects and version visits
plus key and footprint costs. Sharing the query-independent base and computing scope-specific
adjacency lazily, or memoizing by graph version, scope and completeness policy, may amortize it.
Each variant needs a coverage proof for actual dynamic histories;
proof of non-clobber needs the exact queried bytes, not a merely disjoint unrelated footprint.

A safe incremental route is a postpass that eliminates a phi only when all incoming versions
resolve to the same representative, with a cycle-safe handling of self references. Prove graph
well-formedness, path provenance and the legacy projection before exposing it as an alternative.
Its output graph can change, so exact graph equality is not the specification. Precise effects
and partitioning need additional alias laws; no claim is made that the current whole-memory
representation is unsound. ANA-10f's still-unlanded sparse flow and forwarding must not be
reported as absent once it lands.

## Graph and collections

`GraphDominators.v:30–32,118–122,699` selects simple LT by default, offers Semi-NCA and proves
same result on ready inputs. `GraphSemiDominators.v:300–322` threads persistent shortcut and
label maps; `GraphSemiNca.v:19–33,64–80` follows rank-decreasing dominator parents and explicitly
charges each walk, noting potentially quadratic total visits. Both use the same semidominator
phase. The classic LT paper's simple and balanced link/eval variants have different operation
bounds; see [Lengauer and Tarjan, §4][lt].
That URL returned 403 in this session; the independent earlier graph inventory records the
primary comparison. No claim of paper-exact complexity follows from naming the algorithm, and
the owner approves classic LT; balanced LT is absent and outside the current required backend
choice. A fresh faithful-algorithm and worst-case proof,
including each persistent map lookup and compression update, remains open. Dominance boundary
checkers are available for external or cached candidates; the directly proved producer does not
require running one on every call (`GraphDominators.v:122`).

Collections use uncompressed positive tries: lookup/update traverses the encoded key bits, not
constant-time array indices. `CollectionsEncoding.v:154–184` serializes each component of pair
and list keys into an injective bit stream, so composite key length and materialized emitted bits
must be charged. `CollectionsUnionFind.v:59–85` threads a new map through path compression and
rank-based linking; that supports persistent use but is not an imperative array cost model.
Separate branches cannot automatically share the amortized credit of one linear execution.
See [Appel and Leroy's canonical trie paper](https://www.cs.princeton.edu/~appel/papers/ptree.pdf)
and [Conchon and Filliâtre’s persistent union-find][puf].
A compact-ID dense backend or compressed trie can reduce some paths but needs encoding, lookup,
update and enumeration agreement, plus canonicity where propositional equality is required.
Setup and memory can dominate sparse small cases; no practical winner is established.

SCC, WTO, loops and IDF deserve analogous complete cost accounting, including preparation,
output and edge multiplicity. Their existence does not prove source-paper operation bounds, and
this investigation does not identify a concrete dominating alternative for each. See the current
source and `historical research note graph-algorithms.md`; absent a specific comparison they remain structural
risks, not proved regressions.

## SCEV: exponential exact wrapped search

`AnalysesScev.v:252–261,496,546–550,593–599` visits indices in increasing order. Binary
recursion reduces stack depth but does not skip predicate evaluations. For width `w >= 2`, unsigned
start 0, step 1, and continuation `x < 2^w - 1`, the first failure is at `2^w - 1`; all preceding
indices pass, so the implementation evaluates the predicate `2^w` times. For start 0, step 2
and the same bound, every observed word is even and hence below the odd bound; no exit exists,
but the implementation still checks all `2^w` indices. These are mathematical source-operation
families, not timing measurements. C68 shares expression processing; it does not alter this
first-failure search.

A first-stage optional fast path recognizes unsigned increasing unit-step cases with a
provable first failure before wrap, computes that count directly, and calls the existing exact
search for every other case. Prove pointwise equality with `affine_first_failure`, including
`Some` and `None`, and preserve the current `trip_count` interface and its theorems. Extending
this to general modular steps and no-exit cases needs gcd/period and
first-hit arithmetic; no unproved shortcut should replace the universal wrapped fallback.

## SSA, PRE and recurrences

The SEG implementation is a per-expression finite gen/kill specialization and proves its
materialized least facts under the stated laws, rather than a general guarantee for arbitrary
sparse analyses. Construction and dense result materialization can outweigh sparse savings.
For liveness, `AnalysesSsaLiveQuery.v:102–146` prepares graph and value indexes, then scans the
back-closure and indexed uses with dominance and trie membership. The query's work is proportional
to the actual candidates and emitted bits; preprocessing is not free. Compare with the actual
query phase, input representation and preparation in [Léchenet, Blazy and Pichardie 2020][live],
which formalizes and evaluates the earlier Boissinot et al. approach. A one-shot versus
prepared-query portfolio needs exact
liveness agreement and preparation coverage, not just a faster inner loop.

`AnalysesSsaPre.v:402` and `AnalysesSsaPreSemantics.v:73` implement and prove the stated
pure, total client realizer and semantic premises. [SSAPRE](https://doi.org/10.1145/319301.319348)
addresses a broader optimization setting; unique-entry, totality and semantic laws narrow client
coverage. The lack of a PRE optimality theorem in `historical design and trust documents` is a weaker guarantee, not a
counterexample to optimal placement. Proving or refuting optimality needs a defined cost objective,
legal competitor transformations and a concrete witness; changing these is a contract decision.

`AnalysesScev.v:938–948,1963,2313,2518,2940` handles ranked dependencies and prepared cached
expressions. C68's integrated sharing landed, so the old repeated-expansion issue is not an open
finding. The supported recognition domain rejects unsupported nonlinear and mutual feedback;
that is a concrete coverage restriction, not a demonstration that every unsupported expression
has an available closed form. [Bachmann, Wang and Zima 1994, §§2–4][cr]
studies recurrence algebra for evaluating closed forms, a different task from discovering and
proving arbitrary program loops. More recognizers should preserve wrap, signed observation,
first-failure and context-validated cache laws; LLVM-style assumptions about overflow and
poison cannot be imported without matching client semantics.

## Floating point and other choices

`FloatOps.v:1055–1057` retains both zero signs whenever the finite bounds contain zero; lines
1083–1127 return the full ordered hull for division through zero when there are nonzero divisor
values. These explicit conservative choices can hide sign information and finite bounds even when
a more refined IEEE treatment could preserve them. A split negative/positive nonzero divisor
transfer with separately handled signed zeros, NaNs and infinities could be more precise, but
must prove outward rounding and the exact current observable semantics; traps and NaN payload
observability must not be silently strengthened. This is not a least-hull implementation claim.
C13/C56 permit exactly the four named Float axioms listed in `historical design and trust documents`; no exception is
extended to core. Flocq is a semantic and proof dependency, not a competitor analysis.

For a concrete source-derived binary32 example, take numerator `[1,1]` and a denominator
enclosing the nonnegative finite values from +0 to 2, with only positive zero enabled and no NaN.
The finite denominator envelope touches zero and is not zero-only, so `fl_finite_bin` returns
the full ordered hull. `fl_bin` joins that hull with the exceptional table, so it retains -1.
Every actual quotient of +1 by an admitted nonnegative divisor is nonnegative or +infinity;
thus -1 is a spurious result. A sign-aware sound enclosure can exclude it. This is a hand-derived
precision counterexample against that enclosure, not a comparison with a particular Float paper
and not a kernel-checked instance. `FloatInterval.v:46–52` defines the relevant membership.

`FixpointNested.v:28–102,690` already provides a nested solver; the older research inventory's
absence claim is stale. `FixpointLocal.v:66–78` and global worklists have different preparation,
dependency and checking costs, and widenings can produce different results. Static scheduling is
not automatically nested iteration, but the nested alternative exists. `RulesDelta.v:40–88,
172–229,414–440,765–797` prepares and incrementally updates join plans; claiming all indexes are
rebuilt every round would be false. Its materialization and index-maintenance overhead, and
multiway versus nested join behavior, depend on actual relations and reuse. Full checking or a
finite-universe materialization can dominate a small workload, but neither is a universal
slowdown. Domain product refinement at `DomainsProduct.v:36` has bounded rounds, which can
leave further reductions available; a fixed-point version needs a terminating measure and
concretization preservation and may alter answers. Wrapped intervals and variable shifts have
sound overapproximations and finite-width edge cases; no additional specific relative precision
counterexample is established here. Interning, sort and cache strategies likewise need an actual
client and controlled native measurement before asserting a regression.

## Decisions, proof obligations and evidence limits

Same-result changes can first be proposed as optional refinements: trie-backed pending pair sets,
prepared query reuse, exact indexed algorithms and phi simplification with proved observational
agreement. Structural graph outputs or bounded rewrite schedules can differ even when soundness
and cleanliness hold, so their public observable contracts require review. A changed widening,
multiplier default, precision order, IDE client domain, PRE optimization objective, floating-point
observations or source theorem statement changes meaning and needs an owner ruling and the next
docs checkpoint. No C14 contract repair is proposed in this investigation.

Adding an independently proved optional implementation within the fixed interface is engineering
work; preserving existing public equations and theorem statements is its compatibility obligation.
An unproved stronger statement, such as PRE optimality or universal multiplier dominance, is a
missing proof promise, not evidence that an implementation violates its current contract.

No broad claim establishes that the library is uniformly slower, less precise or less correct
than any cited analyzer. No native timing, global complexity proof, full paper transfer parity,
whole-product multiplier ordering, PRE optimality, soundness failure, or all-library proof replay
is established. The complete Fan transfer supplement and primary graph PDFs blocked by browser
access remain missing from this independent inspection. Historical inventories are leads; current
source and current cards take precedence. The analysis does not exhaustively inspect every public
operation, generated/native realization, proof statement or current run branch. Focused follow-up
is needed before describing this as an exhaustive comparison of every library choice.



[ide]: https://research.cs.wisc.edu/wpis/abstracts/tapsoft95.abs.html
[lt]: https://www.cs.princeton.edu/courses/archive/spring03/cs423/download/dominators.pdf
[puf]: https://usr.lmf.cnrs.fr/~jcf/ftp/publis/puf-wml07.pdf
[live]: https://pmc.ncbi.nlm.nih.gov/articles/PMC7324086/
[cr]: https://bohr.wlu.ca/ezima/papers/ISSAC94_p242-bachmann.pdf


Rocq skill completion: types/data and algorithms reviewed unchanged for the identified source
paths; structure/naming, values/text, resource handling, interfaces and verification reviewed
for evidence boundaries; proof editing, syntax, build recovery and source changes not applicable.
No build, tests, assumptions audit or performance measurement was run. The bounded independent
JavaScript checks are not Rocq proofs. The paper PDF access and full transfer supplement limits
are stated above; the recorded Float assumptions are inherited policy, not independently audited.
