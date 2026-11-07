Copied from the pre-redesign research notes on 2026-11-07. Card and ruling IDs refer to the retired run.

# Gaulois capability inventory

Snapshot: 2026-10-28. This is a research checklist, not an implementation-status claim. The
catalogue describes a planned library; the live `historical ledger` controls implementation status.
At this snapshot COL-1a, ORD-1 and BIT-1 had landed; consult the ledger for later changes.

IDs identify research targets, not public API names. A row can encompass several contracted
operations; aliases are explicitly paired in the row. `C` means named API definitions and
claims, `B` means a broader catalogue composition with no dedicated named analysis contract.
`P` means the relevant contracted claims are to be proved directly; `V` means an untrusted
producer's result matters only after a proved checker accepts. `P/V` includes both. These are
intended proof obligations, not assertions that proofs currently exist. Soundness is always
conditional on the exact API hypotheses and client view laws. API names and theorem statements
remain binding; changing their meaning needs an owner ruling. C14 governs minimal contract fixes.
Complexity descriptions are contract notes, not kernel-checked complexity theorems.

## Collections, order and words

| ID | Class | Capability / baseline algorithm | Contract and card | Evidence |
|---|---|---|---|---|
| COL-ENC | C | Injective positive encodings; self-delimiting pair/list codes | collections; COL-1a | P |
| COL-TRIE | C | Canonical little-endian binary tries, merge/share, folds and extensionality | collections; COL-1b | P |
| COL-MAP | C | Maps and finite sets over encoded keys, indexed lookup and set algebra | collections; COL-1c | P |
| COL-QUEUE | C | Persistent leftist priority heap, live map and lazy stale-entry deletion | collections; COL-2 | P |
| COL-UF | C | Persistent union by rank and path compression; `S max_rank` fuel | collections; COL-2 | P |
| COL-TABLE | C | Flat encoded-list map for tables and hash-consing | collections; COL-2 | P |
| ORD-CORE | C | Explicit weak lattice, laws, order, meanings and monotone maps | order; ORD-1 | P |
| ORD-COMB | C | Flat, lift, product, pullback, reduced product, dual and agreements | order; ORD-1 | P |
| ORD-SETS | C | May/must powersets, finite and pointwise maps, bounded disjunction | order; ORD-2 | P |
| BIT-WORD | C | Width-tagged words over Z, signed/unsigned views and bit operations | bits; BIT-1, BIT-2 | P |
| BIT-OPS | C | QF_BV arithmetic, division, shifts, rotations, comparisons, extensions | bits; BIT-1, BIT-2 | P |
| BIT-EXPR | C | Word expression evaluation and client operator bridge | bits; BIT-1, BIT-2 | P |

C18 supersedes the trie traversal note: fold/elements cost O(N + L) plus callback work,
including emitted key-bit construction. Prepared-index agreement is a proof obligation.

## Graph algorithms and checkers

| ID | Class | Capability / baseline algorithm | Contract and card | Evidence |
|---|---|---|---|---|
| GRA-PREP | C | Graph well-formedness, one-pass adjacency/predecessor indexes, reverse and binary fuel | graph; GRA-1a | P |
| GRA-DFS | C | Explicit-stack DFS, reachability, paths, preorder/postorder, RPO and ancestors | graph; GRA-1b | P |
| GRA-DOM | C | Cooper–Harvey–Kennedy dominators; blocked-search exactness checker; flat fallback | graph; GRA-2a | P/V |
| GRA-POST | C | Dominating edges and reverse-graph post-dominators | graph; GRA-2b | P/V |
| GRA-SCC | C | Iterative Tarjan lowlinks, SCC membership, condensation and restricted SCC | graph; GRA-3a | P |
| GRA-DAG | C | Topological sort and maximum-weight paths by DAG dynamic programming | graph; GRA-3b | P |
| GRA-FORWARD | C | Forwarding-chain resolution by memoised walking | graph; GRA-3b | P |
| GRA-NATLOOP | C | Reducibility and natural loops from dominance and backwards search | graph; GRA-4a | P |
| GRA-LOOP | C | Loop nesting forest including irreducible graphs, recursive SCC decomposition | graph; GRA-4b | P |
| GRA-WTO | C | Bourdoncle weak topological order, checker and all-heads fallback | graph; GRA-4c | P/V |
| GRA-FRONT | C | Dominance frontiers, iterated frontiers and control dependence; runner walks | graph; GRA-5 | P; exact-tree premise |
| GRA-COLOR | C | Interference graph, greedy colouring and proper-colouring checker | graph; GRA-6a | P |
| GRA-CB | C | Chaitin–Briggs optimistic colouring, move bias, degree buckets and spills | graph; GRA-6b | P |

Dominator exactness is conditional on acceptance; fallback still gives sound dominance answers.
Post-dominance inherits that distinction. WTO fallback is valid. The contract does not prove
that either proposed producer always succeeds; frontier/control results require an exact tree.

## Constraint and rule engines

| ID | Class | Capability / baseline algorithm | Contract and card | Evidence |
|---|---|---|---|---|
| FIX-QUERY | C | Ret/Ask/Side queries, static and dynamic systems, post- and least solutions | fixpoint; FIX-1 | P |
| FIX-FULL | C | Full post-solution checker, one execution per constraint | fixpoint; FIX-1 | P |
| FIX-CUT | C | Static cut-point certificate expansion and checking, one-pass recomputation | fixpoint; FIX-1 | P |
| FIX-REPLAY | C | Observer replay over facts without retaining extra results | fixpoint; FIX-1 | P |
| FIX-FUEL | C | Priority worklist, indexed readers, binary fuel, top fallback | fixpoint; FIX-2a | P |
| FIX-TOTAL | C | Accessibility-recursive total solver; finite height or widening-rank termination | fixpoint; FIX-2b | P |
| FIX-SCHED | C | RPO, WTO nesting and SCC bottom-up schedulers; cycle-cut widening points | fixpoint; FIX-3 | P |
| FIX-NARROW | C | Narrowing/precision pass kept only when full checking accepts | fixpoint; FIX-3 | P/V |
| FIX-LOCAL | C | Demand-driven local solver and indexed closed partial-solution checker | fixpoint; FIX-4 | V |
| RUL-SYNTAX | C | Safe rule syntax, stratified negation, derivability and stratification | rules; RUL-1a | P |
| RUL-COMPILE | C | Compile each stratum to static side-effecting constraint system | rules; RUL-1a | P |
| RUL-SOLVE | C | Naive bottom-up strata, indexed nested-loop joins and least perfect model | rules; RUL-1b | P |
| RUL-ANALYSES | C | Rule liveness, neededness and reaching definitions equal lattice versions | analyses; ANA-11 | P |

The Rules baseline rebuilds a bound-position index per firing; it is naive, not semi-naive.
Local checking only covers the explored closed partial solution; it is not a global result.

## Abstract domains

| ID | Class | Capability / baseline algorithm | Contract and card | Evidence |
|---|---|---|---|---|
| DOM-NUM | C | Numeric interface, abstract expression evaluation, width tags and capped domains | domains; DOM-1a | P |
| DOM-CONST | C | Constant propagation flat domain and sign domain | domains; DOM-1a | P |
| DOM-INT | C | Integer intervals, threshold widening and narrowing | domains; DOM-1b | P |
| DOM-BITS | C | Tristate known bits with forward transfers and assumptions | domains; DOM-2 | P |
| DOM-WRAP | C | Circular wrapping intervals, minimal-cover join and doubling widening | domains; DOM-3 | P |
| DOM-CONG | C | Arithmetic congruences | domains; DOM-4 | P |
| DOM-PROD | C | Reduced products: bits × wrapping intervals, intervals × congruences, constants | domains; DOM-4 | P |
| DOM-DEMAND | C | Demanded bit masks, relational agreement and backward transfers | domains; DOM-5 | P |
| DOM-ADDR | C | Site/offset addresses, overlap, points-to sets, footprints and byte ranges | domains; DOM-6 | P |
| DOM-RANGE | C | Canonical sorted byte ranges and must-range lattice | domains; DOM-6 | P |
| DOM-EQ | C | Equality partitions, forget and intersection join; symbolic hash-consed keys | domains; DOM-7 | P |

## Semantic adapters and reusable generators

| ID | Class | Capability / baseline algorithm | Contract and card | Evidence |
|---|---|---|---|---|
| VIEW-SEM | C | Semantics, observations, events, traps, divergence and resource stops | views; VIEW-1 | P |
| VIEW-DENSE | C | Graph views, forward/backward constraint generators, invariants and agreement | views; VIEW-1 | P |
| VIEW-STRUCT | C | Structured binary sequence tree, relative jumps, frame machine and loop-head cuts | views; VIEW-2 | P |
| VIEW-REGION | C | Region summaries including normal completion, labels, nesting and height | views; VIEW-3 | P |
| VIEW-SSA | C | SSA view, sparse conditional system, equation and activation soundness | views; VIEW-4 | P |
| VIEW-GUARD | C | Strict SSA dominated-use refinement, edge-dominance index and contexts | views; VIEW-5 | P |
| VIEW-CALL | C | Effects, call graph, frame summaries and bottom-up summary engine | views; VIEW-6 | P |
| VIEW-MEM | C | Allocation and byte memory adapter, points-to soundness template | views; VIEW-7 | P |

## Named analysis compositions

| ID | Class | Capability / baseline algorithm | Contract and card | Evidence |
|---|---|---|---|---|
| ANA-LIVE | C | Dense backward may-liveness, gen/kill and total fixed point | analyses; ANA-1 | P |
| ANA-REACH | C | Forward may-reaching definitions over variable/edge pairs | analyses; ANA-1 | P |
| ANA-ZERO | C | Zero since entry via forward must intersection | analyses; ANA-1 | P |
| ANA-MUSTEQ | C | Dense must-equality via partition merge and forget | analyses; ANA-1 | P |
| ANA-AVAIL | C | Forward must available expressions, gen/kill | analyses; ANA-1 | P |
| ANA-BUSY | C | Backward very busy/anticipated expressions, gen/kill | analyses; ANA-1 | P |
| ANA-LCM | C | Lazy code motion: checked insert/delete candidate with availability and busy facts | analyses; ANA-1 | V |
| ANA-STRUCT | C | Structured liveness, loop-head certificates, expansion and replay | analyses; ANA-2 | P/V |
| ANA-CENSUS | C | Region summary table, including normal/label/nesting/height summaries | analyses; ANA-2 | P |
| ANA-SCCP | C | Sparse conditional constant propagation over SSA | analyses; ANA-3 | P |
| ANA-VALUE | C | Sparse known bits, intervals and reduced products; checked narrowing | analyses; ANA-3 | P/V |
| ANA-PATH | C | Edge predicates, bounded path facts and dominated guard chains | analyses; ANA-3 | P |
| ANA-NEEDED | C | Backward closed neededness; dead values and effect-aware erasure | analyses; ANA-4 | P |
| ANA-DEMANDBIT | C | Demanded and observable bits using forward facts and backward agreement | analyses; ANA-4 | P |
| ANA-ADCE | C | Aggressive dead code: effect roots, data/control-dependence closure | analyses; ANA-4 | P |
| ANA-DVN | C | Dominator-scoped value numbering with strict SSA and scoped leaders | analyses; ANA-5 | P |
| ANA-GVN | C | Optimistic GVN: coarsest congruence by partition refinement and checker | analyses; ANA-5 | P |
| ANA-INVAR | C | Loop invariance closure over pure operations and invariant operands | analyses; ANA-5 | P |
| ANA-EGRAPH | C | E-graph saturation/extraction and replayed rewrite explanations | analyses; ANA-6 | V |
| ANA-SCEV | C | Chains of recurrences recognition and algebra | analyses; ANA-7 | P |
| ANA-TRIP | C | Affine trip counts and separate interval-based no-wrap check | analyses; ANA-7 | P/V |
| ANA-IDIOM | C | Counted-loop idiom via recurrences and trip counts; no fill/copy claim | analyses; ANA-7 | P |
| ANA-TARGET | C | Direct/indirect call target resolution, fallback to all functions | analyses; ANA-8 | P |
| ANA-RECUR | C | Recursion and call-graph reachability via graph components | analyses; ANA-8 | P |
| ANA-IPC | C | Interprocedural constants by joining indexed callers' actual arguments | analyses; ANA-8 | P |
| ANA-PURITY | C | Purity summary propagated bottom-up across calls | analyses; ANA-8 | P |
| ANA-STACK | C | Stack demand: DAG max-weight paths; None if reachable recursion | analyses; ANA-8 | P |
| ANA-LEAF | C | Callee shape/leaf test from call sites | analyses; ANA-8 | P |
| ANA-CONTEXT | C | Bounded call-string contexts as summary-system unknowns | analyses; ANA-8 | P |
| ANA-ANDERSEN | C | Inclusion-based points-to, static query system with load/store side effects | analyses; ANA-9 | P |
| ANA-STEENS | C | Unification-based points-to, persistent union-find pointee classes | analyses; ANA-9 | P |
| ANA-ESCAPE | C | Escape closure from escape roots through heap points-to | analyses; ANA-9 | P |
| ANA-ALLOC | C | Allocation-site identity and fresh-zero facts, may-written footprints | analyses; ANA-9 | P |
| ANA-EPOCH | C | Access epochs/validated accessible byte ranges, forward must system | analyses; ANA-10 | P |
| ANA-DEADSTORE | C | Dead-store byte coverage, backward must overwrites and reads | analyses; ANA-10 | P |
| ANA-MEMSSA | C | MemorySSA construction and no-clobber walk checker | analyses; ANA-10 | V |
| ANA-IMMUT | C | Immutable data from byte-write facts | analyses; ANA-10 | P |
| ANA-INVLOAD | C | Invariant loads via loop writes, callee mod facts and disjoint footprints | analyses; ANA-10 | P |
| FLT-INTERVAL | C | Finite-float intervals, NaN/signed-zero flags and directed rounding | float; FLT-1 | P, C13 assumptions |
| FLT-NAN | C | NaN observability demand and agreement | float; FLT-1 | P, C13 assumptions |
| FLT-OPS | C | Flocq operations, NaN choice, bit conversion and SSA float operators | float; FLT-1 | P, C13 assumptions |

LCM and MemorySSA construction have no producer correctness theorem. E-graph explanations
validate individual rewrites. The no-wrap check supplies a distinct premise; a trip count is not
itself a no-wrap guarantee. KeepTraps erasure has the stated behaviour equality, while
DropUnreadTraps has only the contract's conditional refinement.

## Broader compositions, examples and operational support

| ID | Class | Capability / baseline algorithm | Source and card | Evidence |
|---|---|---|---|---|
| B-OCCUR | B | Occurrence census composed by a client; distinct from contracted region table | catalogue | No dedicated theorem |
| B-NORETURN | B | No-return summaries composed by a client | catalogue | No dedicated theorem |
| B-MODREF | B | Mod/ref summaries composed by a client | catalogue | No dedicated theorem |
| B-STORELOAD | B | Store-to-load availability composed by a client | catalogue | No dedicated theorem |
| EX-WHILE | C | While semantics, 32-bit bridge, graph/structured views and analysis adapters | examples; EX-1, EX-4 | P |
| EX-SSA | C | Typed SSA semantics, calls, frames, byte memory, bridges and view proofs | examples; EX-2, EX-5a/b/c, EX-6 | P |
| TOOL-CHECK | C | Hygiene, layout and theorem-assumption checker | TASKS; TOOL-1 | Tool checks; theorem audit |
| TOOL-BENCH | C | Typed extraction and performance benchmarks | TASKS; TOOL-2 | Experiments, not proofs |

Coverage crosswalk: catalogue graph → GRA-*; dense → ANA-LIVE through ANA-LCM;
structured → VIEW-STRUCT/REGION, ANA-STRUCT/CENSUS; values → DOM-*, VIEW-SSA/GUARD,
ANA-SCCP/VALUE/PATH; neededness → DOM-DEMAND and ANA-NEEDED/DEMANDBIT/ADCE; equality →
DOM-EQ and ANA-MUSTEQ/DVN/GVN/INVAR/EGRAPH; loops → GRA-NATLOOP/LOOP/WTO and
ANA-SCEV/TRIP/IDIOM; calls → VIEW-CALL and ANA-TARGET through CONTEXT; memory → DOM-ADDR/RANGE,
VIEW-MEM and ANA-ANDERSEN through INVLOAD; float → FLT-*; rules → RUL-*; broader compositions →
B-*. Examples and support engines are independent performance targets, not additional analyses.
