Copied from the pre-redesign research notes on 2026-11-07. Card and ruling IDs refer to the retired run.

# SSA book crosscheck against the Gaulois inventory

The inspected [book-full.pdf](https://pfalcon.github.io/ssabook/latest/book-full.pdf) has 412
physical PDF pages and a title page dated 8 June 2018; its printed chapter pagination begins at
page 1 and, for numbered pages, physical PDF page = printed page + 16. Chapter authors are named
in the contents below. The [pfalcon repository](https://github.com/pfalcon/ssabook) describes
itself as a mirror of the collaborative InriaForge book, not a sole-author work. Its `latest`
directory lists this file dated 2018-06-08. This particular full draft has placeholder front matter,
TODOs, unresolved `??` cross-references and uneven chapter maturity; it is not an authoritative
new version of a verified algorithm. The later published book need not have identical pagination.
References below use printed pages and sections of this specific draft. We inspected contents and
relevant chapter text, including pseudocode and example discussions. No source code is copied.

IDs below refer to `capability-inventory.md`; they map closest capabilities, not a claim that an
entire chapter is contracted. New interfaces require owner rulings and new cards. Existing APIs
and strict direct proof requirements remain binding. Construction, destruction and register
allocation are optional client adapter/consumer extensions, not prerequisites for the current
analysis library. There is no benchmark gate for a non-dominated backend.

## Chapter-by-chapter inventory crosswalk

| Chapter, printed pages | Relevance, existing inventory IDs and proposed action |
| --- | --- |
| 1 Singer, pp. 5–14 | SSA model and phi semantics: VIEW-SSA, EX-SSA, ANA-REACH. Clarify phi use on predecessor edges, distinguish static SSA definitions from source-variable reaching histories. |
| 2 Brisk/Rastello, pp. 15–26 | Strictness, pruned/minimal and conventional/transformed forms: VIEW-SSA/GUARD, ANA-LIVE, GRA-DOM/COLOR. Separate defined-on-all-paths strictness from noninterfering phi-web conventionality; do not derive either solely from unique names. Stronger interference is value-sensitive and differs from plain live-range intersection. |
| 3 Singer/Rastello, pp. 27–44 | IDF insertion, renaming, conventional destruction: GRA-FRONT, GRA-DOM, VIEW-SSA, EX-SSA. Optional construction/destruction adapter must preserve executions and SSA laws; general analysis does not require it. |
| 4 Das/Ramakrishna/Sreedhar, pp. 45–58 | DJ-graph and loop-nesting IDF: GRA-FRONT, GRA-LOOP, GRA-DOM. Add direct verified single-set IDF backend with adjacency/ordered-bucket premises; retain general all-frontier interface when requested. |
| 5 Hack, pp. 59–66 | SSA reconstruction after edits: VIEW-SSA/GUARD, GRA-DOM/FRONT. Optional incremental repair adapter needs coverage, invalidation and semantic preservation; do not retain stale dominance or def-use indexes. |
| 6 Beringer, pp. 67–94 | SSA/functional correspondence, liveness construction and nesting: VIEW-STRUCT, VIEW-SSA, ANA-LIVE. Optional functional-client adapter with operational correspondence; no assumption that pruned means minimal. |
| 7 Schordan/Rastello, pp. 95–98 | Analysis overview: VIEW-SSA, VIEW-DENSE, FIX-QUERY, ANA-SCCP/LIVE. Points to workload-dependent sparse/dense formulations rather than a universal replacement. |
| 8 Brandner/Novillo, pp. 99–112 | Sparse propagation, copy example and limitations: VIEW-SSA, ANA-SCCP/VALUE/PATH/MUSTEQ, FIX-TOTAL. Reuse def-use indexes and prove semantic/lattice assumptions per analysis; unsupported memory effects require separate modeling. |
| 9 Boissinot/Rastello, pp. 113–128 | Full live sets for reducible and irreducible graphs, outermost-excluding-loop, reachability queries and path exploration: ANA-LIVE, GRA-DFS/DOM/LOOP, VIEW-SSA. Expose exact query and materialized backends with one liveness relation and edge-use semantics. |
| 10 Pop/Cohen, pp. 129–138 | Loop trees, induction and recurrence/trip-count: GRA-NATLOOP/LOOP, ANA-INVAR/SCEV/TRIP/IDIOM. Preserve per-exit and wrap assumptions; graph extraction without CFG is a separate adapter. |
| 11 Chow, pp. 139–160 | SSAPRE, speculative PRE, load/store placement and value-based elimination: ANA-AVAIL/BUSY/LCM/DVN/GVN, ANA-INVLOAD/MEMSSA. Add direct SSAPRE as an SSA client option with safety and separate optimality theorem; speculation and promotion need extra trap, memory and effect laws. |
| 12 Sarkar/Rastello, pp. 161–168 | Overview SSI, control, gated, predicated and memory variants: VIEW-SSA/GUARD/MEM, GRA-POST/FRONT, ANA-PATH/ADCE/MEMSSA. Separate representations from semantic analysis capabilities. |
| 13 Pereira/Rastello, pp. 169–188 | SSI splits and partitioned per-variable lattice: VIEW-SSA/GUARD, ANA-SCCP/VALUE/PATH/NEEDED. An SSI backend requires splitting/renaming semantics and separability; shared soundness is insufficient for identical-fact equivalence without a representation theorem. |
| 14 Stanier, pp. 189–204 | Dataflow, dependence and gated graphs: GRA-FRONT/POST, ANA-ADCE/PATH/INVAR. PDG/GSA/VSDG would be optional representation and analysis extensions, not promises of existing control dependence. |
| 15 de Ferrière, pp. 205–218 | Psi-SSA for predicated execution: VIEW-SSA/GUARD, ANA-PATH; separate optional predicated client with execution, guard ordering and psi normalization proofs. |
| 16 Mantione/Chow, pp. 219–232 | HSSA, memory alias mu/chi and virtual variables: VIEW-MEM, ANA-ANDERSEN/STEENS/MEMSSA/GVN. HSSA is a possible client memory representation, not interchangeable with the current no-clobber checker. |
| 17 Sarkar/Knobe/Fink, pp. 233–252 | Array SSA and sparse array constants: DOM-ADDR/RANGE, VIEW-MEM, ANA-SCCP/MEMSSA/INVLOAD. Array-element partitions require index alias/disjointness proofs; optional precision extension. |
| 18 Dupont de Dinechin, pp. 253–266 | Machine SSA engineering and lowering constraints: EX-SSA, VIEW-SSA, GRA-COLOR. Target constraints and instruction scheduling are client scope, not existing generic analyses. |
| 19 Ebner/Krall/Scholz, pp. 267–280 | Tree/DAG instruction selection and PBQP: no corresponding inventory analysis; external target backend scope. |
| 20 Bruel, pp. 281–296 | If-conversion and predication: VIEW-GUARD/SEM, ANA-PATH. Optional transformation client requires full branch/effect/trap correspondence; not required for dataflow. |
| 21 Rastello, pp. 297–314 | Out-of-SSA correctness, copies and quality: VIEW-SSA, ANA-LIVE, GRA-COLOR. Optional adapter needs critical-edge and parallel-copy semantics and a separate simulation. |
| 22 Bouchez/Hack/Rastello, pp. 315–340 | SSA pressure, spilling, coloring, coalescing: ANA-LIVE, GRA-DOM/COLOR/CB. Optional dominance-tree coloring is a distinct consumer; uniform-register exact coloring does not solve constrained allocation, spilling or coalescing. |
| 23 Diniz/Brisk, pp. 341–358 | Hardware mapping, phi multiplexers: no matching named analysis; hardware client scope. |
| 24 Biggar/Gregg, pp. 359–371 | PHP whole-program analysis, dynamic aliasing, HSSA: VIEW-CALL/MEM, ANA-ANDERSEN/IPC/CONTEXT/MEMSSA. Client semantics and dynamic features require coverage laws; no generic performance result follows. |

## Decisions, proof obligations and pitfalls uncovered

**Liveness.** Chapter 9 §§9.2–9.4 treats reducible and irreducible sets separately and uses the
outermost excluding loop and modified forward reachability. Do not apply its reducible traversal
unchanged to arbitrary graphs. Preserve both materialized live sets and on-demand query interfaces;
prove both exact for the same syntactic CFG path relation under their respective graph premises.
SSA phi operands are predecessor-edge uses; self-loops, irreducibility, unreachable blocks and
instruction ordering need explicit tests. Directly verified query proof route:
[Boissinot et al. 2008](https://publikationen.bibliothek.kit.edu/1000120906) and
[verified implementation 2020](https://pmc.ncbi.nlm.nih.gov/articles/PMC7324086/). Both differ
from semantic feasibility and from the backwards agreement post-solution. Full-set storage and
preparation costs remain separate from per-query work; index invalidation depends on graph/uses.

**Placement and construction.** Chapter 4's DJ graph can compute one iterated frontier without
materializing every individual frontier. [Sreedhar and Gao 1995](https://www.chapmanhall.com/jp/jp030401.abs.html)
state a linear single-SEG placement algorithm with a given DJ representation; count dominance,
index construction and emitted output separately. Compare only identical IDF specifications,
not all-frontier output versus one queried set. For optional SSA clients provide IDF/rename and
sealed-block construction as different integration choices, using shared semantic correctness.
[Braun et al. 2013](https://c9x.me/compile/bib/braun13cc.pdf) §3.2 explicitly shows that base
sealed construction may create redundant phi SCCs for irreducible control flow; the additional
SCC removal step is necessary for its stronger minimality result. Pruned, strict, minimal and
conventional are independent stated properties, not interchangeable tags. The precise semantics
of undefined entry definitions must come from the client; a synthetic definition cannot silently
repair uninitialized behavior.

**Destruction and phi copy hazards.** Chapter 2 §2.5 and chapter 21 show that SSA optimizations
can break conventional phi-web noninterference even while preserving unique definitions; naive
renaming then changes behavior. Critical edges, mutually dependent parallel copies and lost-copy
hazards require explicit handling. Optional adapter roadmap: give parallel edge-copy semantics;
prove critical-edge splitting preserves traces and guards; prove cycle-breaking sequential moves
simulate simultaneous assignment using fresh temporary; prove coalescing only under a sound
interference condition; connect to SSA semantics. See
[Boissinot et al. 2009](https://inria.hal.science/inria-00349925v1), especially its lost-copy and
swap cases. Include loop phi swaps, multiple phis, critical and exceptional edges in tests.
These are extensions to clients and do not block direct proofs of existing analyses.

**Interference and allocation.** Chapters 2 §2.6 and 22 separate plain live-range overlap from
more refined value-aware interference. Chordality and exact tree-scan coloring are for the
strict SSA live-range model and uniform registers, not arbitrary coalesced graphs, target
constraints, minimum spill cost or optimal move elimination. Implementing the tree-scan consumer
would require a shared live-range/dominator-tree theorem and a proper-coloring proof; GRA-COLOR/CB
already serves general graphs, so both cover different consumers. If allocation is outside scope,
retain this as an explicit optional extension, not a newly implied contracted analysis.

**Book-specific quality.** Draft references include unresolved `Chapter ??` markers (e.g. p. 320)
while initial pages contain placeholder text; printed examples and pseudo-code are explanatory,
not machine-checked specifications. We have not established a particular algorithmic book bug
beyond these observable draft defects. In particular, the abstract of Braun et al. must be read
with its §3.2 rather than treating base sealed SSA as minimal on every irreducible input. For
algorithm claims rely on the cited original papers and state their precise premises, then build
independent Rocq proofs rather than trusting a book transcription.
