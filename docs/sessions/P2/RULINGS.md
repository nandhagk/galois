# P2 decisions

The owner decided these on 2026-11-17, after planners A (ruling P2-ANALYSES below) and B
(ruling P2-STRUCTURES below) drafted the batch.

- The benchmark harness uses Jane Street Core. Core (with `ppx_jane` and the OCaml tools the
  harness needs) joins the chat-session toolchain in the release that the readability change
  rebuilds anyway.
- Run first: BENCH1, BENCH2, LIVE1, LIVE2, LIVE3 and INC. The speculative cards wait for the
  benchmark's profiles: PEDGE (narrower point-edge keys, ~1.4x on `live_in`), CAPJOIN and
  CAPRUN (capped join, only for explosive rules), RANGE and RANGEX (batched Karr ranges, which
  no client calls yet; plumbing `eval_many` would cost ~1.5 more sessions), and the worklist
  record per key (below 1.2x, gate in BENCH2). The Tarjan trie merge and the echelon cache stay
  dropped.
- PLAN2's cap rises from 8 to 32 function atoms in P1 stage 2, which keeps `T_plan_le` cubic
  with the same constant (G2X arithmetic, checked by planner B). Delta-first planning without a
  cap stays dropped.
- Accepted: IN-3's widened width measure in four frozen incremental time fields and two
  complexity fields (`demand_complexity` and `edit_complexity`), and block liveness with its
  runtime `cover_ok` fallback to the old search.
- The Opus review of the P2 rulings and cards runs after the readability change lands, so it
  checks them under the new names, and before any P2 card is dispatched.
- The benchmark times its workloads with `ppx_bench` and core_bench (owner, 2026-11-17): inline
  `let%bench` benchmarks, run by a `core_bench` runner executable per library,
  indexed over input sizes so the growth can be compared with the proved class, with OLS estimates and allocation counts. A thin layer keeps the reference checks, the
  derived-clock column, peak memory in a child process, and commit comparison. The session
  toolchain has `core_bench` and `ppx_bench` with Core.
- The benchmark's correctness checks are inline expect tests with `ppx_expect` (owner,
  2026-11-17), as the repository's rule for OCaml tests says: each workload prints a
  deterministic summary of its result, pinned beside the code and run before any benchmark.
  Timings stay in `ppx_bench`. The toolchain has `ppx_expect`.
- The expect tests and the runner's `report` and `compare` print `Ascii_table` tables (owner,
  2026-11-17), so a regression shows as a changed cell. Each workload's tests sit in one
  `let%test_module "Name" = (module struct ... end)` with small named fixtures and one property per
  test (the pinned `ppx_inline_test` v0.17.1 rejects `module%test`). The table library is
  `textutils.ascii_table` (opam package `textutils` v0.17.0, module `Ascii_table`). The toolchain
  has it beside `core_bench`, `ppx_bench`, `ppx_expect` and Core, all required.

## Notes after the Opus review (2026-11-18)

- The review, kept with the batch drafts, fixed 5 high, 8 medium and 19 low defects in place.
- The default `devShell` has the benchmark libraries too (owner, 2026-11-18). Commit `60fda13b`
  of `p1r/base` gives both shells one list of OCaml libraries, so a local run of the harness uses
  plain `nix develop`. The session shell, and with it the release toolchain, is unchanged.
- By the owner's card-size rule, the three cards that needed about 7 hours were split, and their
  items moved unchanged. The cards to run first are now BENCH1, BENCH1B, BENCH2, LIVE1, LIVE1B,
  LIVE2, LIVE3 and INC, in that order within each chain. CAPJOIN, CAPJOINB and CAPRUN wait for
  the benchmark's profiles as before, and start after readability step R8.

## Dispatch without kits (owner, 2026-11-18)

- The P2 groundwork (the rulings applied to the signatures, with STUB proofs) merges into
  `main` once its gates pass, and `main` is pushed before dispatch. There is no `p2/base` branch,
  no bundle and no kit.
- The cards clone `main` and switch to `{P2_BASE}`, the base commit. They download
  `{P2_RELEASE}`, the session toolchain release (`toolchain-e5f6fee` today).
- The rulings that the cards cite go into the repository as `docs/sessions/P2/RULINGS.md`, with
  the groundwork. `OWNERSHIP.md` goes beside them.
- `~/Projects/galois-archive/fill-cards.sh P2 cards OUT BASE RELEASE` fills the cards, and
  `~/Projects/galois-archive/test-bootstrap.sh OUT` checks the release and the base.

## The groundwork on `main` (reviewer, 2026-11-18)

The groundwork applies the signature changes that the owner accepted, with STUB proofs, and adds
this file and `OWNERSHIP.md`.

- Ruling F8 (section 1.5 of ruling P2-ANALYSES). `LIVE_TIME` in `Ssa/LiveSig.v` gains the
  definitions `straight_in` and `is_head`, the spec parameter `live_head_region` with
  `live_head_region_nodup` and `live_head_region_spec`, the definition `live_head_size` and
  `live_head_size_le`, all after `live_in_ids`. It gains `T_live_in_head_le` and
  `live_in_head_complexity` after `live_in_complexity`. The module `Live` in `Ssa/Live.v` defines
  `straight_in` and `is_head` with the same bodies, at its end. `LiveT` ends with the placeholder
  `live_head_region` (STUB-CODE, the empty list), the definition `live_head_size` and five STUB
  lemmas. The headers of both files list `live_in_head_complexity`.
- Ruling IN-3 (section 4.2 of ruling P2-ANALYSES). `LOCAL_TIME` in `Fixpoint/SystemSig.v` gains
  `rcw`, `row_code_bits_le` and `rows_of_nodup`. `width` adds `S.rcw p` in `IncrementalSig.v` and
  in its copy in `IncrementalT`. `IndexedT` defines `rcw` as the ruling gives it and holds the two
  laws as STUB lemmas. `Incremental.v` builds with no change of proof.
- `just/frozen.sha256` has new hashes for `Ssa/LiveSig.v`, `Fixpoint/SystemSig.v` and
  `Incremental/IncrementalSig.v`, the three frozen files that these two decisions change.
- The signature text of ruling P2-STRUCTURES (sections 1.6 and 3.4) is not on the groundwork.
  Its cards start after P1 stage 2 and wait for gates of the owner, so the reviewer lands and
  compiles that text on their base, with the card appendices as the list. P1-EGG2 owns `Join.v`
  from `09655375`, and step R8 of the readability plan rewrites `JoinSig.v` and `Join.v` after the
  stage-2 lanes end. No client calls `range_many`, so its STUB lemmas would stay on `main` with no
  card to close them until the owner accepts the profiles.
- `cover_ok_wf` is a lemma of P2-LIVE3 (section 1.5 of ruling P2-ANALYSES). It names `cover_ok`,
  which P2-LIVE1 writes, so the groundwork does not hold it.

Corrections at landing, made in the rulings below and in the cards.

- Section 1.8 missed a consumer. `BuildT` in `Ssa/Build.v` applies `LiveT` as the module
  `UniverseClock`, and the lemma `budget_universe_clock` uses six helpers of `LiveT` that no
  signature states. Section 1.8 names them, and the four liveness cards keep their text.
- Section 4.2 named two proofs of `IncrementalT` that unfold `width`. Four do, namely
  `T_row_keys_le`, `T_discovery_row_le`, `T_discovery_step_le` and `discovery_row_bits_le`. Each
  ends in `lia` or `nia`, and each builds with the new summand.
- Section 5.3. Since the EG batch, the client tower of `tests/Clients/SolveTest.v` has a runner,
  `SolveRunner`, an application of `RunnerCode` of `Front/Runner.v`, which `AndersenCode` takes.
- Section 5.4. `p1r/base` is merged into `main`, so both shells of `nix/default.nix` on `main`
  carry the benchmark libraries.
- Sections 1.5 and 1.8 cited line numbers of `8228e48a` in `Live.v`, `LiveTest.v` and `Build.v`.
  They name the lemmas, definitions and test groups now.
- The cards cite this file for the rulings and the decisions. `RULING-P2-ANALYSES.md`,
  `RULING-P2-STRUCTURES.md` and `DECISIONS.md` were the names of the drafts.
- The cards. P2-LIVE1 names `live_driver_atom` as the clock lemma that unfolds `T_live_in`,
  because `T_live_in_le` and `T_live_in_split` reach the body through it. P2-LIVE3 states
  `cover_ok_wf` itself. P2-BENCH1B owns the `gb_egglog` stanza of
  `bench/egglog/dune`, which gains `gb_egglog_extracted`. P2-BENCH2 names `ShortStages`, the
  configuration that `KnownBitsCode` takes in `KnownBitsMulTest.v`. Each chained card says that
  its `{P2_BASE}` is the commit of `main` that integrates the card before it, and each card ends
  with the STUB items of its base.

# Ruling P2-ANALYSES

Group ANALYSES of batch P2. It rules on five items that batch P1 dropped or deferred. Names are
those of `main` = `d90c6b3d`, after the readability rename. Line numbers still refer to
`8228e48a`, so find each place by name. The reader is the reviewer, who lands the signature text
on the batch base with `STUB` proofs. The owner decided the points of section 7 on 2026-11-17
(the P2 decisions).

## 0. Verdicts

| Item | Verdict | Gain (derived) | Proof size | Cards |
| --- | --- | --- | --- | --- |
| F8 block-level liveness | accept, with a design that needs no `SP.wf` | 3x to 8x on `live_in` | ~1,800 lines | P2-LIVE1, P2-LIVE1B, P2-LIVE2, P2-LIVE3 |
| F9 narrow point-edge keys | accept, after LIVE3 and the benchmark's profile | 4x to 5x on edge keys, 1.3x to 1.5x on `prepare` | ~600 lines | P2-PEDGE |
| C8 one record per key | drop, with a measured gate | 1.2x to 1.3x on a row visit | ~8,000 lines | none |
| IN-3 each row once | accept, with a ruling on `LOCAL_TIME` | up to 1 + (writes per row) on demands | ~400 lines | P2-INC |
| Benchmark | accept, three cards | not applicable | ~1,500 lines OCaml and Rocq | P2-BENCH1, P2-BENCH1B, P2-BENCH2 |

The order of the cards is P2-BENCH1, P2-BENCH1B, P2-BENCH2, then P2-LIVE1, P2-LIVE1B, P2-LIVE2
and P2-LIVE3, with P2-INC free to run beside any of them. The benchmark comes first because
every other gain of the batch is a derived clock until a wall-clock baseline exists. P2-PEDGE is
speculative. It runs after P2-LIVE3 and only when the benchmark's profile shows the share of edge-keyed work
(the P2 decisions).

## 1. F8 Block-level liveness

### 1.1 What P1 found and why it does not bind

`Live.live_in` runs one search per variable over instruction points and keeps only the block
entries. P1 (ruling F8) dropped the block-level search because its soundness proof for
`live_in_size` must hold for every function `p`, while the laws that order the points of a block
(`points_ordered`, `points_owner`, `blocks_nonempty` of `SSA_POINTS_LAWS`) hold only under `SP.wf`,
which `LANG_PRESENT_BUDGET.points_wf` gives for SSA programs only.

The obstacle disappears if the search does not use blocks at all. A block is a maximal run of
points joined by straight edges, and the point graph `C` shows the run by itself. Two facts make
this work.

- `LANG_PRESENT_BUDGET.prepared_wf` gives `C.wf (R.prepare p)` for every `p`, without `ssa_wf`.
  So `C.out_spec` and `C.inc_spec` hold for every prepared program. They are the only laws that
  the soundness proof needs besides `C.edges_nodes`.
- `point_live` is defined over `C.out`, `C.dst`, `U.uses`, `U.defs` and `U.exits` and over nothing
  else. A chain of straight edges has a closed form in these terms (section 1.3).

The design therefore contracts straight chains of the point graph, which are the instruction
sequences of the blocks in an SSA program, and it proves soundness and completeness from
`point_live` and `C.wf`. It does not touch `SsaSig.v`'s point laws. P1's draft restatement of
`points_ordered` without `wf` is not needed.

### 1.2 Definitions of the spec layer

These definitions go into `LIVE_TIME` of `Ssa/LiveSig.v` as ordinary `Definition`s, after
`live_in_ids` and before the head region of section 1.5. They use
no new operation. The reviewer lands the same two bodies in the module `Live` of `Live.v`, which
`LiveT` includes, so that the chain lemmas of `Live` can name them and `LiveT` matches the
signature. `CFG_LAWS` states `C.inc` and `C.out` by membership, so a list may repeat an edge.
Both definitions therefore read membership, and the second disjunct of `is_head` is exactly the
test of `entry_block`, so the heads of the code and of the specification agree on every node.

```coq
(** A point is straight when one edge enters it and that edge is the only edge that leaves its
    source. A list may repeat the edge. *)
Definition straight_in (q : Q.t) (m : N.t) : Prop :=
  exists e, In e (C.inc q m) /\ (forall e', In e' (C.inc q m) -> e' = e) /\
    (forall e', In e' (C.out q (C.src q e)) -> e' = e).

(** Heads start the chains. Every point of the entry table is a head, so every output row sits
    at a head. *)
Definition is_head (q : Q.t) (m : N.t) : Prop :=
  ~ straight_in q m \/
  (In m (C.nodes q) /\ In (SP.block_of_point q m) (BC.nodes q) /\
    m = C.src q (SP.parameter_edge q (SP.block_of_point q m))).
```

A chain is a head `h`, then the straight successors `n1, n2, ...` of `h` up to the first point
whose outgoing list does not hold exactly one edge, up to repetition, into a non-head. That last
point is the tail. The edges between consecutive chain points are the links. Interior points have
one outgoing edge, so the chain is a simple path. A chain cannot revisit a point, because each
point after the head has exactly one incoming edge. A link into a head cannot occur, because a
head is never `straight_in` by the first disjunct of `is_head`, or it is a point of the entry
table that the scan stops at.

For a chain `c` with points `n0 .. nk` (`n0` the head, `nk` the tail), links `e0 .. e(k-1)` and
the outgoing edges `outs` of the tail, define two sets of variables.

- `chain_kill c`, the variables defined by some link edge, which is the union of `U.defs q ej`
  over `j < k`.
- `chain_up c`, the upward exposed variables. A variable `x` is in it when for some `j <= k`, `x`
  is in `U.exits q nj` or in `U.uses q ej` (`j < k`) or in `U.uses q e` for some `e` in `outs`
  (`j = k`), and `x` is not in `U.defs q ei` for any `i < j`.

### 1.3 The two facts that carry the proofs

Both are lemmas of `Live.v`, with the hypothesis `C.wf q` and nothing else.

```coq
(** A variable is live at a head when it is upward exposed in the head's chain. *)
Lemma chain_up_live : forall q c x, C.wf q -> is_chain q c ->
  In x (chain_up q c) ->
  point_live (C.nodes q) (C.out q) (C.dst q) (U.uses q) (U.defs q) (U.exits q) x (chain_head c).

(** A variable is live at a head exactly when it is upward exposed, or it passes the links and a
    tail edge into a live head. *)
Lemma chain_head_live_iff : forall q c x, C.wf q -> is_chain q c ->
  (point_live (C.nodes q) (C.out q) (C.dst q) (U.uses q) (U.defs q) (U.exits q) x (chain_head c) <->
   In x (chain_up q c) \/
   (~ In x (chain_kill q c) /\ exists e, In e (C.out q (chain_tail c)) /\
      ~ In x (U.defs q e) /\ In (C.dst q e) (C.nodes q) /\
      point_live (C.nodes q) (C.out q) (C.dst q) (U.uses q) (U.defs q) (U.exits q) x (C.dst q e))).
```

Here `is_chain q c` says that `c` is a list of points that starts at a head, that each point but
the last has one outgoing edge `e` (it is in `C.out q n`, and every edge of `C.out q n` is `e`)
with `C.dst q e` the next point and not a head, and that the last point is a tail by the
definition above. The proof of the first lemma is an induction on the
length of the chain along `Point_live_next`. The proof of the second is an induction on the
`point_live` derivation for the direction from left to right, and the same induction as the first
lemma for the other direction. Each is about 150 lines. The statement `is_chain` is an inductive
predicate of about 15 lines.

### 1.4 The code

The executable change is in `LiveCode` and adds these definitions. All bodies get a `TimeFun`
line.

1. `chain_heads q`, a trie of the head points of `C.nodes q` keyed by `N.encode`. The code reads
   the graph through two tables built in one pass over the deduplicated edge inventory
   `incoming_edges q`, the existing incoming table and an outgoing table of the same shape. It
   never calls `C.inc` or `C.out`. Their contracts (`T_inc_le`, `T_out_le`) charge the whole list,
   `CFG_LAWS` lets a list repeat an edge, and the head test runs for every node, live or not, so
   a call per node is a cost that no measure pays. A point is a head when its incoming row does
   not hold exactly one edge `e`, or when the outgoing row of `C.src q e` does not hold exactly
   one edge, or when its code is in `entry_table q (BC.nodes q)`. The entry table already exists
   (`entry_table`).
2. `chain_scan`, which for each head follows the outgoing row of `n` while it holds exactly one
   edge `e` whose destination is not a head. The scan keeps two persistent tries, the defined set
   `D` (a `ptrie unit` of variable codes) and the upward exposed set. At step `n` it adds each `x`
   of `U.exits q n` and of `U.uses q e` that is not in `D` to the exposed set, then adds each `x`
   of `U.defs q e` to `D`. At a tail it adds the uses of every edge of its outgoing row in the
   same way and records the pair `(head, D)` in a trie `tails` keyed by the code of the tail. The
   persistent tries share structure, so a chain of `k` links with `d` defined variables allocates
   `O(d)` nodes of width `w`, which the existing seed and kill tables already pay.
3. `chain_seeds`, the index from a variable code to the list of heads where it is upward exposed.
   It replaces `seed_index`.
4. `chain_incoming`, the incoming table of the heads only. A head's row lists, for each edge `e`
   of its incoming row (one record per distinct edge, so parallel edges keep their records), the
   record `(tail code, head of the tail, kill of e, kill of the chain)`, where
   the kill of `e` is `live_intersection (U.defs q e) None` as in `incoming_edge` and the kill of
   the chain is the trie `D` of the tail. Two membership tests then decide whether `x` passes
   the edge. This avoids the union `defs e` with `D`, which would cost `|D|` per incoming edge.
5. `blocks_search`, the per-variable search. It starts from the heads of `chain_seeds` and, for
   each live head `h` and each record of its row, discovers the head of the tail when `x` is in
   neither kill set. It is `cached_fuel` with the new row type, so the termination fuel is
   `length (C.nodes q)` as today.
6. `cover_ok q`, `forallb` over `C.nodes q` of "the code of the node is in the table of covered
   points". The scan marks each point that it passes. Isolated cycles of straight edges that
   contain no block entry are the only points that no chain reaches. A cycle of that kind cannot
   occur in a prepared SSA program, because every cycle crosses a block entry. The generic
   statements about `C` cannot exclude it, so the runtime check does.
7. `live_in_blocks p` is `if cover_ok q then (rows grouped from blocks_search) else
   live_in_cached p`. The old body keeps its name `live_in_cached`, so the proofs of the old
   body stay valid. `live_in` becomes `live_in_blocks` only in P2-LIVE3.

The output grouping is `group_entry` over the visited heads, as today, so each row lists a
variable at most once and the order of the variables in a row follows the universe. Row order does
not depend on the order of the search, which is the reason that exact equality with `live_in_spec`
is a sensible law (section 1.5).

### 1.5 Laws and fields

No existing field changes its statement. The following are added. The reviewer lands them with
`STUB` proofs on the batch base. The region fields of the first block hold for every `p`. The two
time fields of the second block hold only when `live_in` is `live_in_blocks` and the fast branch
runs.

In `LIVE_TIME`, add `live_head_region` to the `(* spec: live_region *)` comment, and insert after
`live_in_ids`:

```coq
  (** The head region lists the live pairs at chain heads. *)
  Parameter live_head_region : P.t -> list (N.t * positive).
  (** The head region lists each pair once. *)
  Parameter live_head_region_nodup : forall p, NoDup (live_head_region p).
  (** The head region holds exactly the live pairs whose point is a head. *)
  Parameter live_head_region_spec : forall p n x,
    In (n, x) (live_head_region p) <->
    In (n, x) (live_region p) /\ is_head (R.prepare p) n.
  Definition live_head_size p := fold_right (fun pair n =>
    1 + length (C.inc (R.prepare p) (fst pair)) + n) 0 (live_head_region p).
  (** Head pairs are among the charged live pairs, so the head measure is no larger. *)
  Parameter live_head_size_le : forall p, live_head_size p <= live_size p.
```

Insert after `live_in_complexity`, where `T_live_in` and `c_live` are declared:

```coq
  (** On an SSA program the producer pays for the head region only. *)
  Parameter T_live_in_head_le : forall p, SP.wf (R.prepare p) ->
    (T_live_in p <= c_live * N.of_nat (function_size p + live_head_size p + 1) *
      N.of_nat (function_width p + 1))%N.
  (** On an SSA program the producer is linear in the syntax and the head region. *)
  Parameter live_in_head_complexity :
    T_live_in p ∈ 𝑂(N.of_nat ((function_size p + live_head_size p + 1) *
      (function_width p + 1))) for p | SP.wf (R.prepare p).
```

The reviewer adds `live_in_head_complexity` to the `Main results` list of the headers of
`LiveSig.v` and `Live.v`, as `rules.md` section 7 requires. `LiveT` defines `live_head_size` with
the body above, as it does `live_size`.

`live_head_size_le` follows from `live_head_region_nodup`, `live_head_region_spec` and
`live_weighted_incl` (`Live.v`, top level), which bounds the weighted sum over a duplicate-free
list by the sum over any list that includes it. The existing proof of `live_in_size` has the same
shape.

In the non-time part of `Live` (an ordinary lemma, not a signature field), with the hypothesis
that `C.wf (R.prepare p)`:

```coq
  Lemma live_in_blocks_agrees : forall p, C.wf (R.prepare p) ->
    live_in_blocks p = live_in_spec p.
```

This lemma is the exactness law that no signature states today. The present `live_in` has only
Examples that compare it with `live_in_spec` (the group `CachedSearchTests` of
`tests/Ssa/LiveTest.v`). `live_in_entries_agrees` (module `Live` of `Live.v`) already ties
`live_in_spec` to the entry-table
form, and `search_spec` makes the per-variable point search complete and sound. The new proof
shows that for each variable the set of entry points that the head search finds is the set
that `search` finds, and then uses the argument that row order does not depend on the order of
visits. Completeness is the part that needs `chain_head_live_iff`.

For the existing fields:

- `live_in_ids` follows from `group_entry` as today. The fallback branch uses the old proof.
- `live_in_size` follows from the head pairs being a duplicate-free subset of `live_region`
  (`blocks_search_live`, `blocks_search_nodup`) and the weight of each pair being at least 1. The
  proof copies the structure of the present proof of `live_in_size` in `LiveT`, with
  `cached_region` replaced by the head region.
- `T_live_in_le` and `T_live_in_split` hold for the fast branch because `live_head_size_le` gives
  `head <= live_size`, and for the fallback branch by the old proofs. Both branches also pay the
  deduplicated tables, the head test, the scan and the cover check, which run before the branch is
  known. They cost a constant times `(function_size p + 1) * (function_width p + 1)` by
  `points_le`, `point_bits_le` and `occurrence_width_le`, so `c_live` and `k_rows` grow by a
  closed expression. `T_live_in_split` keeps its statement, in which the plan clocks
  `T_use_index`, `T_kill_index` and `T_explore` stay on the right side as nonnegative terms.

The head fields in `LIVE_TIME` use the premise `SP.wf (R.prepare p)` for one reason only. Under
it the cover check passes, so the fast branch runs and the clock is the head clock. The lemma
is `cover_ok_wf`, and its proof needs `points_ordered`, `instruction_edges_complete` and
`point_edge_projection` of `SSA_POINTS_LAWS`. Take a point `n = (b, j)`. Either `n` is not
`straight_in`, so it is a head and is covered, or its unique incoming edge is an instruction edge
from `(b, j-1)`. Induction on `j` covers it. About 150 lines.

### 1.6 Truth conditions and revert behaviour

The fields `T_live_in_head_le` and `live_in_head_complexity` are true only when `live_in` is
`live_in_blocks`. P2-LIVE3 makes that switch. If the clock proofs of P2-LIVE3 cannot be finished,
the card reverts the switch (`live_in := live_in_cached`), and the two fields are then false. The
reviewer removes them from `LiveSig.v` in that case, which is a signature edit and so is not left
to the session. The rest of the fields are true in both states.

### 1.7 Gain

The cost of the search is `Σ (1 + |inc n|)` over the visited pairs. Let `B` be the number of
points of an average block (instructions plus the entry), so an interior point has one incoming
edge and a block entry has `d` of them, with `d` about 1.5 on average. The old search visits each
live point of a block, so it pays about `2B` per live block and variable. The new search pays
about `1 + d = 2.5` for the head. The ratio on the search term is about `0.8 B`, which is 4x at
`B = 5` and 24x at `B = 30`.

The clock of `live_in` is `s + L`, with `s` the syntax term (preparation, tables, scans) and `L` the
search term. Let `r = L / s` for the old code. Then the ratio is `(1 + r) / (1 + r / (0.8 B))`.

| `B` | `r` | ratio |
| --- | --- | --- |
| 10 | 3 | 2.9x |
| 10 | 10 | 4.9x |
| 30 | 10 | 7.7x |

The value of `r` depends on the live-range length of the input. It is the average number of
variables live across a point divided by the operands per instruction, so `r` between 3 and 10
is typical for compiler IR. These are derived from the clock formula and not measured. P2-BENCH1B
measures them. The chain tables add one pass over the points with the same per-point cost as the
seed and kill tables that they replace, so `s` does not grow by more than about 20%.

Memory. The head trie `D` per tail is a persistent set that shares structure with the set of the
preceding point, so the tables stay linear in the syntax size.

### 1.8 Consumers outside the cards

`Ssa/Build.v` reads `L.live_in p` in `placement` and `produce`, through `live_sets` and
`val_index`. It reads the rows only and the output is equal (`live_in_blocks_agrees`), so no proof
changes. `BuildT` also applies `LiveT` itself, as the module `UniverseClock`, and its lemma
`budget_universe_clock` uses six helpers of `LiveT`, which are no signature fields. They are the
definitions `live_clock_scale`, `live_clock_width`, `live_clock_atom` and `live_graph_load` and the
lemmas `live_graph_load_bound` and `live_universe_atom`. The cards keep these definitions and the
statements of the two lemmas, so `Build.v` compiles unchanged. The tests
`tests/Ssa/BuildTest.v` and `tests/Ssa/LiveTest.v` use `LiveCode` directly. The Examples that
compare `live_in` with `live_in_spec` stay and now check the head search.

### 1.9 Checked against the P1 review patterns

- Wide names. Chain tables are keyed by `N.encode` of a point, whose width is bounded by
  `point_bits_le`, and by variable codes of at most `function_width` bits. No new key kind enters.
- Repeated entries. The incoming row of a head keeps one record per distinct edge into `h`,
  including parallel edges, and the head measure charges `|inc h|` for each head pair, which is at
  least the number of distinct edges, so every record is charged. A list of `C.inc` or `C.out` may
  repeat an edge, and no law bounds the sum of their lengths over all nodes, so the code never
  calls them. It reads the tables of the deduplicated edge inventory, as the present
  `incoming_table` does. The order of `C.nodes` has no duplicates under `C.wf`.
- Unbounded numbers. No slot or counter appears.
- A field true only after a revertible change. Section 1.6 states it and names who removes the
  fields.
- Bodies that break proofs in files that the card does not own. `live_in_cached` keeps the old
  body and name. `Build.v` sees `live_in` only through its output, and the six helpers of `LiveT`
  that its `UniverseClock` uses keep their text (section 1.8).

## 2. F9 Narrow point-edge keys

### 2.1 The present key and its widths

`PointEdge.encode` is `PointEdgeTupleKey.encode (src, (dst, be))`. The pair code is
`glue (fa a) (fb b)`, and `glue a b` doubles every bit of `a` and adds one marker bit, so its
width is about `2 |a| + |b|`. Let `β` be the width of a block identifier and `ι` the width of a
point index (`N.succ_pos i`, about 4 bits). A point key `(b, i)` is `glue b i`, so it has about
`2β + ι` bits. A point edge then has these widths.

- An internal edge. `2 |src| + 2 |dst| + |None|` is about `8β + 4ι + 1`.
- An exit edge. The same plus the block edge key `glue source (glue arm target)`, about
  `3β + 4` bits, so about `11β + 4ι + 5`.

With `β = 14` and `ι = 4` that is about 129 bits for an internal edge and 175 for an exit edge.

### 2.2 The change

`PointEdge.encode_inj` forces the destination into the key because `point_edge` has an
independent destination field. The destination is a function of the source. An internal edge
ends at `(b, i + 1)`, and an exit edge ends at `(target, 0)`, where the target is a field of its
block edge (`lang_point_edge_block_sides`, line 1119, proves `edge_source be = fst (point_src e)`
and `edge_target be = fst (point_dst e)`, and `summarize`, line 358, builds every edge in
exactly these two forms). The type becomes an inductive type with one constructor per kind.

```coq
Inductive point_edge :=
  | InstrEdge (src : PointKey.t)
  | ExitEdge (be : block_edge) (last : N).

Definition point_src (e : point_edge) : PointKey.t :=
  match e with InstrEdge s => s | ExitEdge be i => (edge_source be, i) end.
Definition point_dst (e : point_edge) : PointKey.t :=
  match e with
  | InstrEdge (b, i) => (b, N.succ i)
  | ExitEdge be _ => (edge_target be, 0%N)
  end.
Definition point_block_edge (e : point_edge) : option block_edge :=
  match e with InstrEdge _ => None | ExitEdge be _ => Some be end.

(** The old three-argument form, for the construction sites. The destination is determined. *)
Definition PointEdge (s _ : PointKey.t) (be : option block_edge) : point_edge :=
  match be with None => InstrEdge s | Some be => ExitEdge be (snd s) end.
```

The key packs the small component first, because `glue` doubles its first argument.

```coq
Definition point_edge_code (e : point_edge) : positive :=
  match e with
  | InstrEdge s => xO (PointKey.encode s)
  | ExitEdge be i => xI (glue (N.succ_pos i) (BlockEdge.encode be))
  end.
```

Widths are then `2β + ι + 1` bits for an internal edge and `3β + 2ι + 5` for an exit edge, which is
about 33 and 55 bits at `β = 14` and `ι = 4`. The ratio to the old widths is 3.9x and 3.2x. With
one exit per nine internal edges the average narrows by about 3.8x. Swapping the pair order of
`PointKey` as well (item PE-3, section 2.4) gives `β + 2ι` bits for the point, so about 23 bits for
an internal edge. The exit key holds no point key and stays at about 55 bits. The ratios are then
5.6x and 3.2x, and about 5x on average.

`encode_inj` for the new type follows from `PointKey.encode_inj`, `BlockEdge.encode_inj` and
`glue_inj` (the existing lemma behind `pair_code`), by case analysis on the two constructors that
the tag bit separates. About 40 lines.

### 2.3 Sites

`Ssa/Present.v` mentions `PointEdge` at 111 places and `point_dst`, `point_src` and
`point_block_edge` at 97. The shim `PointEdge` keeps every construction site (the consistent
destinations at lines 225, 368, 372, 440, 458, 843, 844, 848 and the ones in `lang_prepare`)
unchanged. Proofs that use the projections reduce by `cbn [point_dst]` once the argument is a
constructor application, so most of them stay. Three kinds of site change.

- Statements that fix a destination, such as `PointEdge s t be` with a `t` that differs from the
  determined one. None exists in the tests. `SharedKeyTests` of `tests/Ssa/PresentTest.v` uses
  `PointEdge (1, 0) (2, 0) (Some edge)` with `edge = BlockEdge 1 True_arm 2`, whose source block
  is 1 and whose destination is `(2, 0)`, so its Examples keep their statements and run through
  the shim.
- `point_src (PointEdge last t (Some be)) = last`. It needs `fst last = edge_source be`, which
  `summarize` guarantees, because `listed_edge_args kept b` builds every `be` from the block
  `b` of the summary. A lemma `exit_edges_source` states this and `lang_point_edge_block_sides`
  becomes its corollary.
- The key module and its time proofs (`PointEdgeTupleKey`, `point_edge_tuple`, `PointEdge.T_encode_le`,
  `T_eqb_le`, `c_key`). They are rewritten for the new code, about 100 lines.

`tests/Ssa/BuildTest.v` and `tests/Ssa/LiveTest.v` pass `PointEdge` as the key module of an edge
(`BuildTest.v` lines 38, 112, 204, `LiveTest.v` lines 26, 164, 174). That is the module `PointEdge`
and it keeps its name. The `DuplicateEdges` fixture of `LiveTest.v` lists `View.C.edges` twice and
builds no edge by hand, so neither file changes. No SSA file iterates a trie keyed by points or
edges (no `PTrieCode.elements` or fold over one), so the new encodings change no computed order.

### 2.4 Gain, and whether it is worth it

The edge key enters every trie that is keyed by an edge. `prepare` builds the `uses` and `defs`
tables with `first_table PointEdge.encode` (lines 817, 818 and 848), and `live_in` reads them per
edge, builds `incoming_edges` by `E.encode` and uses `E.encode` in `live_pair_member`. Each of
these operations costs about the key width. The derived gain is about 3.7x on each edge-keyed
operation, and P1 estimated 1.3x on `prepare` and 1.2x on `live_in` from the share of edge-keyed
operations. After P2-LIVE3 the search term shrinks and the setup term, where the edge keys sit,
becomes a larger share of `live_in`, so the gain on `live_in` rises to about 1.4x at `r = 10`
(derived from the formula in section 1.7 with the setup at 50% of the old total). The
benchmark measures it, and the card requires the measurement before and after.

The card costs about 6.5 hours. The gain is moderate, so it runs last in the group, and only when
the benchmark's profile shows the edge-keyed share (the P2 decisions).

Item PE-3 swaps the pair order of `PointKey` so that the block identifier, the larger component,
is not doubled. The value type `positive * N` stays. Only `PointKey.encode` changes, so the node
keys of every point-keyed trie get 2x narrower. The proof of `encode_inj` and the two time lemmas
are rewritten, about 80 lines, and `point_bits_le` and `edge_bits_le` of `LANG_PRESENT_BUDGET`
(narrower keys satisfy the same bounds) are checked again.

## 3. C8 One record per key in the worklist

### 3.1 Count

`update_one` (`Fixpoint/Worklist.v` line 387) does these trie operations for a strict update. A
store read for `old`, a counter read, an `ws_armed` read, a store write, a counter write, and, when
the key was not armed, the readers read of `enqueue` and the `ws_armed` write of `arm`. That is 5
operations on the same key code plus 2 more when the key arms. A record `{value; count; readers;
armed}` per code makes it 1 read and 1 write, so 7 operations become 2 (5 become 2 when armed).
The check agrees with the brief.

### 3.2 Why the record is not worth its price now

- The solver reads the store through `eval_row p r (ws_store s)`, where `S.resume` receives
  `look_or S.key_code L.bot m`. A state of records would pass a different lookup function, which
  the code allows, because `eval_query` takes a callback and not a `kmap`.
- The result of `run` is `Solved (ws_store s)` of type `kmap S.key L.t` in `SolverSig.v`, which
  `Check`, `Certified`, `Narrow`, `Incremental` and `Framework` consume. The records need one
  final pass `filter_map` over all keys, so `T_run` gains an additive `O(keys * w)` term. The
  fields `T_run_le` of `WorklistSig.v` would have to be restated.
- `WorklistSig.v` names `ws_store`, `ws_counters`, `ws_readers` and `ws_armed` at 41 places, and
  `Worklist.v` at 186 places across 8,238 lines.
- No signature statement shows a constant factor. The contracts say `c_wl * (work p pol + ...)`
  with an abstract constant. So the change adds no proved fact. It changes the constant
  that no contract fixes.

### 3.3 Gain per row visit

A row visit pays a priority-queue pop (`Q.pop`), a rows read, a live-set removal, `d` store
reads for `d` dependencies, `d` armed removals, and for each of its `t` written keys one `update_one`.
Take `d = 2`, `t = 1`, an update that is strict with probability `f`, and `m` readers enqueued
per strict update (each costing a ranks read, a live read and write and a queue push). Then the
trie operations per visit are about `3 + 2 + 2 + 1 + f (6 + 3m)` plus `f m` queue pushes. At
`f = 0.5` and `m = 2` that is 14 trie operations, of which the record saves `f * 5 = 2.5`. So the
saving is 18% of the trie operations, and a row visit gains about 1.2x if trie operations were all
of its cost. The lattice operations `leb`, `join`, `widen` and the evaluation of the row cost more
than trie operations for any domain with a map state. So the gain on a solve is below 1.2x for
dense analyses. The brief's 2x to 3x describes the update alone (7 to 2 operations), and the
update is a minor part of a row visit.

### 3.4 Decision

Drop, as P1 did, and keep one gate. P2-BENCH2 profiles the interval analysis, one of the three
`ai-*` workloads that run the `Fixpoint` worklist, with `perf`. If the inclusive time of the four
tries of `update_one` (the five operations of section 3.1) is at least 25% of the solve, the item
returns as a card in the next batch with this design. The design is the record

```coq
Record key_cell (K A : Type) := KeyCell {
  kc_stored : option (K * A);
  kc_count : N;
  kc_readers : list positive;
  kc_armed : bool
}.
```

in a `ptrie (key_cell K A)` field `ws_keys`, with `look`, `counter`, `heads_unchanged` and the
other readers redefined through it, and `Solved (store_of_cells ...)` at the end. The proof
strategy is a view lemma `wl_view` equality with the old state, which keeps the invariants of
`Worklist.v` stated over the view. That keeps the 8,000 lines and changes the definitions near
`ws_*` only. It is still a large card (two sessions), which is why the gate applies.

## 4. IN-3 Discover each row once

### 4.1 The problem and the repair

`discovery_step` (`Incremental/Incremental.v` line 270) pops a key `x` and calls `discovery_row`
for each row of `S.rows_of p x`. A row with `k` discovered writes appears `k` times in `rows_of`
lists, so it appears `k` times in `discovery_rows`, in `region`, in the `selected` rows of `R.mk`
and in `record_rows`. The solver then evaluates each copy. A seen set keyed by `S.row_code r`
removes the copies. P1 dropped it because no law bounds the width of a row code, so the frozen
`T_discovery_le` and `T_demand_le` do not pay for the set (`REVIEW-P1-R4` item 1).

The statements need two new facts, and the second one was missed by P1.

- A bound on row codes, so the seen set is paid by `width`.
- A statement that `rows_of p x` has no repeated row. Without it a row can occur many times in one
  list, the deduplicated region then has fewer entries than the number of lookups, and the cost of
  the lookups is not covered by the region measure. The old code charged each occurrence, because
  `region` kept them.

### 4.2 Signature text

In `Fixpoint/SystemSig.v`, module type `LOCAL_TIME` (after `T_rows_of_le`), with the pragma that
`rules.md` section 8 asks for a new spec parameter:

```coq
  (* spec: rcw *)
  Parameter rcw : prog -> nat.
  (** Row codes of listed rows fit the row-code width. *)
  Parameter row_code_bits_le : forall p r, wf p -> In r (rows p) ->
    Pos.size_nat (row_code r) <= rcw p.
  (** The index lists a row once for each key. *)
  Parameter rows_of_nodup : forall p x, wf p -> NoDup (rows_of p x).
```

In `Incremental/IncrementalSig.v`, module type `INCREMENTAL_TIME`, the definition of `width`
(line 159) becomes

```coq
  Definition width (p : S.prog) (_ : state) : nat :=
    S.kw p + N.to_nat (S.row_work p 0) + S.rcw p.
```

No statement is edited by hand. `T_demand_le` and `T_edit_le` of `INCREMENTAL_TIME`,
`T_discovery_le` and `T_invalidate_le` of `INCREMENTAL_PLAN`, and the two complexity fields
`demand_complexity` and `edit_complexity` use `width`, so they weaken together. Each weakening is
by the added summand `rcw p`, and a proof of the old statement gives the new one by `lia`, because
the new width is at least the old width.

`IncrementalT` (`Incremental.v`) repeats the definition of `width`, as a module must for a
definition of its signature, so the reviewer changes that copy in the same commit. Its four proofs
that unfold `width`, `T_row_keys_le`, `T_discovery_row_le`, `T_discovery_step_le` and
`discovery_row_bits_le`, end in `lia` or `nia` and absorb the new summand, and every other proof
reads `width p st` as a whole. The file therefore builds on the base with no new admission, which
the build of the groundwork confirmed.

The laws go into `LOCAL_TIME`, not `LOCAL_LAWS`, so that the test systems
`OneRow <: LOCAL_SYSTEM WitnessBool` (`IncrementalTest.v` line 110) and the others, which are not
timed, need no new proof. The only timed implementation is `IndexedT` (`Fixpoint/Indexed.v`, which
includes `LOCAL_TIME` at line 71 of `IndexedSig.v`). The reviewer lands its definition
`rcw p := Pos.size_nat (Pos.of_succ_nat (length (S.rows (program p))))` on the base, so that only
the two laws are `STUB` lemmas and no placeholder makes `row_code_bits_le` false. Row codes are
the numbers `1 .. n` of `number_from`, and `Pos.size_nat` is monotone, so `row_code_bits_le`
follows from the bound `id <= n`. `rows_of_nodup` follows from `index_row`: each row is inserted
once per distinct key code (`PTrieCode.elements keys` has distinct codes), and numbered rows are
distinct. About 60 lines in `Indexed.v`.

### 4.3 The code

`incremental_discovery` gets a field `discovery_row_seen : ptrie unit`. `discovery_row` becomes

```coq
  Definition discovery_row (p : S.prog) (st : state)
      (acc : incremental_discovery S.key S.row L.t) (r : S.row)
      : incremental_discovery S.key S.row L.t :=
    let code := S.row_code r in
    match PTrieCode.get code (discovery_row_seen acc) with
    | Some _ => acc
    | None =>
      let next := fold_left (fun current x => discovery_visit st x current) (row_keys p r)
        {| ... discovery_row_seen := PTrieCode.set code tt (discovery_row_seen acc); ... |} in
      {| ... discovery_rows := r :: discovery_rows next; ... |}
    end.
```

Each occurrence pays `S.T_row_code r` and a `get`, each first occurrence a `set`, all at width at most
`rcw p` (`T_row_code_le`, `row_code_bits_le` and the trie bound). By `rows_of_nodup` and
`discover_nodup`, the number of occurrences is at most `Σ_{r in region} |writes r|`, because the
pair `(x, r)` occurs once and `x` is a write of `r` (`rows_of_spec`). Each region row is charged
`(deps + sides + 1)` times `(width + 1)` by the contract, and `|writes r| = 1 + |sides r|`, so
the lookups fit in the same charge with a larger constant.

`region` is now duplicate free. `discovery_views` needs no change, because it states `rs = region`.
A repeated occurrence of a row visits only keys that the first occurrence marked seen, so every
other field of the discovery state is the one that the old pass computes. The new pass therefore
equals the old one except that `discovery_rows` is `dedup_rows` of the old list, the first
occurrence of each row code in the order of the old list (a lemma `discovery_rows_dedup`). The
specification layer (`discovery_region`, `region_for`, `frozen_pairs`) filters `S.rows p` in
program order and stays unchanged. The executable region is in discovery order, so no list
equality ties the two. The lemmas that connect them read the region by membership (for example
`region_rows`, `region_new` and `regional_run_below_result`), and `dedup_rows` keeps membership.

### 4.4 Gain

A region row that has `s` sides is listed in `rows_of` for each of its discovered writes, at most
`1 + s` times. Discovery and the restricted solver pay for each copy. So the gain on a demand is
the average multiplicity of the region rows, up to `1 + s`, and it is 1x for rows without sides.
Rows of an Andersen-like system have no sides, so the gain there is nil. A system that writes
side keys (memory writes with alarms, for example) gains 2x to 5x at `s` from 1 to 4. The
solver runs on `R.mk p fz rg`, so duplicated rows also stop being evaluated twice in every round.

The ruling is safe to land alone. With the old code every weakened field is still true, because
the new `width` is at least the old one. If P2-INC reverts the code, nothing else changes.

### 4.5 Checked against the P1 review patterns

- Wide names. Row codes are now charged through `rcw`. The code reads them in `discovery_row` and its clock
  lemmas only. `rows_of_nodup` closes the
  repeated-entry hole.
- The width of the key trie bound uses `Pos.size_nat (row_code r)` (the trie contract), and not
  `S.kw p`.
- The signature change adds parameters to `LOCAL_TIME` only, and its only implementation outside
  tests is `IndexedT`, which the card owns for these proofs.

## 5. Benchmark

### 5.1 What exists

- `main` has no OCaml source, no extraction command and no benchmark. `rg Extraction theories`
  finds none. `examples/` holds `Toy.v`, a Rocq example run by `vm_compute`, and nothing is run
  natively.
- Derived clocks (`T_*` by `TimeFun`) measure call-by-value work on fixtures such as the 200-row
  database. They are accounting and not time. Memory is estimated by hand (the P1-DBW card counts
  list cells).
- An older tree (the Gaulois design, bundle `galois-archive/2026-11-07/galois-all-refs.bundle`,
  commit `86ce112`, card TOOL-2) had an `extraction/` directory and a Core timing loop
  `tools/bench.ml` at sizes 8 to 512. Its shape is reused. The stanza was

  ```
  (rocq.extraction (prelude ExtractGaulois) (extracted_files algorithms.ml algorithms.mli ...)
   (theories ...))
  ```

  with `copy_files` into a library that relaxes warnings 4, 39 and 41, and `Extraction Language
  OCaml` with `Stdlib.extraction` `ExtrOcamlBasic` and `ExtrOcamlNatInt`. That experiment "does not
  establish scaling".

### 5.2 Layout

A new directory `bench/` at the root, outside `theories`, so `just build`, `just test` and
`just session-check` do not build it. Its parts are separate directories so that two cards own
disjoint files.

| Path | Content | Card |
| --- | --- | --- |
| `bench/dune`, `bench/README.md` | alias `bench`, directory notes | P2-BENCH1 |
| `bench/runner/` | library `gb_runner`, the shared layer: `workload.ml`, `summary.ml`, `peak.ml`, `clock.ml`, `growth.ml`, `compare.ml`, `sizes.ml`, each with its `.mli` | P2-BENCH1 |
| `bench/runner/bin/` | executable `main.exe`: `main.ml` and `registry.ml` (with `.mli`), linking `gb_runner` and every workload library | P2-BENCH1 |
| `bench/egglog/` | `ExtractEgglog.v`, the extracted library `gb_egglog_extracted`, and the workload library `gb_egglog` (`gen_egglog.ml`, `workload_egglog.ml`, expect tests and `let%bench_fun` at the bottom) with its `run_bench` | P2-BENCH1 (extraction), P2-BENCH1B (workload) |
| `bench/ssa/` | `ExtractSsa.v`, `dune`, library `gb_ssa`: `gen_ssa.ml`, `workload_ssa.ml` (expect tests and benchmarks), its `run_bench` | P2-BENCH1B |
| `bench/ai/` | `ExtractAi.v`, `dune`, library `gb_ai`: `gen_ai.ml`, `workload_ai.ml` (expect tests and benchmarks), its `run_bench` | P2-BENCH2 |

Every workload library depends on `gb_runner`, for `Workload` and `Summary`, and only the
executable depends on the workload libraries. A registry inside `gb_runner` would make `gb_runner`
and `gb_ssa` depend on each other, which dune rejects as a cycle. P2-BENCH1 creates `bench/egglog/`,
`bench/ssa/` and `bench/ai/` workload libraries with one placeholder workload each, so the dune
graph is complete, and P2-BENCH1B and P2-BENCH2 replace whole files. `justfile` recipes are owned
by P2-BENCH1.

### 5.3 Extraction

Each directory has a prelude `.v` that instantiates the functor tower for concrete modules
(as `tests/Clients/SolveTest.v` does for Andersen: `SolveValue`, `SolveIndex`, `SolveJoin`,
`SolveDatabase`, `SolveRun`, `SolveRunner`, `SolveAndersen`) and then runs one
`Extraction "name.ml" roots`. A single
file per prelude avoids the module list of `Separate Extraction`. No test or example applies
`SaturateCode` (`tests/Egraph/SaturateTest.v` checks front-end inputs only), so the egglog prelude
builds the saturation tower from the modules of `SolveTest.v` and `CompileCode`. `just lint` runs
`r13.awk` over every tracked `.v` file, so each prelude names the root of every `Require`.
Settings are `ExtrOcamlBasic` (bool, option, list, pair) and `ExtrOcamlNatInt` for `nat` only. `positive`, `N` and `Z` stay
inductive, which keeps the cost shape of the tries. The native-int realizations of `ExtrOcamlZInt`
cannot be used, because composite keys such as `PointEdge` have 100 or more bits and would
overflow. A dedicated library per directory compiles the extracted file with `-w -4-39-41-32-33-26-27`,
as in the older design, so the root flags (`-w +a ... -warn-error +a`) do not apply to generated code.

The checks that the first session runs, in order, because each can block the whole plan.

1. `Extraction` of `SolveAndersen.solve` for the fixture of `SolveTest.v` prints OCaml with no
   `Obj.magic` and no opaque-access warning. If an `Acc`-based `loopN` or a `Qed` helper in code
   blocks extraction, record the term and the roots and stop (the rocq skill's rule is to look at
   the unavailable computational content first and not to make proofs transparent as a
   workaround).
2. The compiled result equals the `vm_compute` result of the same Example (`Saturated`, points
   `[true; true; true; false]`).
3. `ocamlfind ocamlopt` compiles it under the dune flags.

### 5.4 The harness

Timing is `ppx_bench`. Each workload is a `let%bench_fun` (setup outside the timed closure) with
`[@indexed n = [...]]` over the input sizes, written at the bottom of the workload's own `.ml`,
as the repository keeps inline expect tests. Jane Street's `core_bench` runs them through
a runner executable per library. Dune's inline-test runner has no `-benchmarks-runner` option, so the
executable (`(libraries <lib> core_bench.inline_benchmarks)`, `(link_flags (-linkall))`, body
`Inline_benchmarks_public.Runner.main ~libname:"<lib>"`, with `(modules ...)` fields so that the
library and the runner do not clash) runs them when the environment variable
`BENCHMARKS_RUNNER=TRUE` is set, together with `X_LIBRARY_INLINING=true` or the flag
`-run-without-cross-library-inlining`. Its options include `-quota <INT>x|<SPAN>` (for example
`-quota 2s`), `-save`, `-load FILE`, `-ascii`, `-csv`, `-sexp`, `-fork`, `-stabilize-gc`,
`-no-compactions`, `-width`, `-regression`, the column names `time`, `alloc`, `gc`, `percentage`,
`speedup` and `samples`, and `-matching` (in the source, not in `-help`). It gives OLS estimates with confidence intervals,
and allocation and GC counts per run. Growth with size is measured at the indexed sizes and compared with the proved big-O class.
The correctness layer is inline expect tests with `ppx_expect`, in the same modules, grouped per
workload in a test module (`let%test_module "Name" = (module struct ... end)`, because the pinned
`ppx_inline_test` v0.17.1 rejects `module%test`) and printed as `Ascii_table` tables. Core, `ppx_jane`,
`ppx_bench`, `ppx_expect` and `textutils.ascii_table` (opam package `textutils`, module
`Ascii_table`; there is no standalone `ascii_table`) are in the toolchain, at Core v0.17.2,
`core_unix` v0.17.1, `ppx_jane` v0.17.0, `ppx_expect` v0.17.3, `ppx_inline_test` v0.17.1,
`ppx_bench` v0.17.1, `core_bench` v0.17.0 and `textutils` v0.17.0. Both shells of
`nix/default.nix` on `main` have them, since `60fda13b` of `p1r/base`, which `main` merged. The
release environment `galois-env.sh` captures the
session shell (`nix print-dev-env .#session`), and a local build of `bench/` runs in
`nix develop`.

The dune text of each library with benchmarks has `(preprocess (pps ppx_jane ppx_bench))`,
`(inline_tests)` and a `modules` field, next to its `run_bench` executable, and the alias `bench` of `bench/dune` builds the runners.

Thin layer, in `bench/runner/`, for what `ppx_bench` does not cover.

- Expect tests. For every workload, `let%expect_test`s print a deterministic summary of its
  result as an `Ascii_table`, with a fixed column order and alignment and ASCII bars
  (`Ascii_table.to_string_noattr` with an explicit width, as the repository's OCaml skill asks),
  on a small seeded input. Each test shows one property beside the workload and size columns (the
  number of points-to facts, a few samples, the saturation status, the e-class count, whether the
  SSA output validates, the analysis results at a few program points), pinned inline. They run with the inline tests before any benchmark (`just bench-check`).
  Timings never appear in expect output. Where an independent check exists in the extracted code
  (`Validate`, the fixpoint `Check`), the summary prints its verdict, and the octagon test
  compares with a plain Floyd-Warshall closure. A hand-written reference implementation per
  workload is not written.
- `peak`. Peak memory per workload size, measured in a child process (`main.exe peak`) that builds
  the input, runs the operation once and prints `VmHWM` from `/proc/self/status` on Linux and
  `top_heap_words`. A crash or a wall-time overrun is recorded as a failure.
- `report`. One `Ascii_table` with the benchmark, the size, the `core_bench` estimate and its
  confidence interval, the derived-clock column (section 5.6), the log-log slope and the proved
  class, joined to the saved results and the peaks.
- `compare OLD NEW`. Reads two result files that the runner saved with `-save`, through its
  `-load FILE` (repeatable, it analyses saved data without running) with `-sexp`. Per benchmark and size it prints
  the estimates, their intervals and the ratio, and marks a regression when the ratio exceeds
  `1 + max(0.05, relative half-width of the wider interval)` and the intervals do not overlap. It
  prints an `Ascii_table` and ends with the geometric mean.

Inputs are produced in OCaml from a seed (`Random.State.make [| seed |]`) with fixed default seeds
in `bench/README.md`. Generators build the extracted data types directly (`Addr`, `Copy`, lists,
`positive` through a small `Rocq_data` helper). The sizes start at the values below and the
session rescales them so that the largest takes 1 to 5 seconds per run on the owner's machine.
They are recorded in `bench/runner/sizes.ml`.
### 5.5 Workloads and inputs

| Workload | Rocq root | Input | Indexed sizes |
| --- | --- | --- | --- |
| `andersen` | `SolveAndersen.solve` | `V` variables, `V/4` `Addr`, `3V/2` `Copy`, `V/4` `Load`, `V/4` `Store`, plus one `Copy` chain of length `V/10` so that propagation is deep | `V` = 200, 2,000, 20,000 |
| `saturate` | `Saturate.saturate` | a random expression of `n` binary nodes over 8 variables, rules for commutativity, associativity and one distribution, limits of 8 iterations | `n` = 30, 150, 600 |
| `ssa-build` | the public `build` of `BuildSig` | a random structured function (nested `if` and `while`) of `n` blocks, mean block length `B = 8`, variables used up to 4 blocks after their definition, non-SSA form so that `build` places the phis | `n` = 200, 2,000, 20,000 |
| `liveness` | `live_in` of `LiveSig` | the same generator in SSA form, `B` of 5, 10 and 30 at `n` = 2,000, and a variant with live ranges that span the whole function | `n` = 200, 2,000, 20,000 |
| `ai-interval`, `ai-congruence`, `ai-knownbits` | `Interp` with the domain over `Env` | a CFG of `n` nodes, `k = 16` variables, assignments `x := y + c` and `x := y * c` and guards `x < c`, with loops from back edges to a random dominator | `n` = 100, 1,000, 10,000 |
| `ai-octagon` | `Octagon` state operations | `m` variables, a random closed octagon, operations `close`, `join`, `widen`, `leb` and `assign`, in a loop of 100 | `m` = 8, 24, 64 |

The sizes are starting points. Congruence and known bits run over the word language
(`WordLanguageCode`, as `tests/Domains/CongruenceTest.v` and `KnownBitsMulTest.v` instantiate), and
interval over `ZLangCode` (as `examples/Toy.v`). The `ai-*` workloads share a generator that builds
the instruction type of the chosen language. P2-BENCH2 reads the three tests for the instance
names.

The liveness variants isolate the two factors of section 1.7. `B` varies the block length at a
fixed live range, and the span variant raises `r`.

### 5.6 Calibration against the derived clocks

For `andersen` and `liveness` the layer also prints the derived clock of the operation
(`AndersenT.T_solve`, `LiveT.T_live_in`) on the same input, computed by extracting the clock
functions in the same file, beside the OLS estimate of the same size. The ratio of time to clock
units should stay within a small factor across the sizes. A drift flags a cost-model problem (a
hidden quadratic, or a constant that the model charges at the wrong place). This is the first
empirical check of the `TimeFun` translation, which `argent-correctness-pinned` leaves open. If the
`T` tower does not instantiate for a fixture, the card records it and prints the column as `-`.

### 5.7 Running under `just`

Recipes in `justfile` (the `just` skill applies). All run through `capped`, so they share the
10 GB `galois.slice`.

- `just bench-build` builds `bench/` (the alias `bench` of `bench/dune`).
- `just bench-check` builds the inline tests and runs them with dune's inline-test runner, which
  runs no benchmark, so every expect test passes before a benchmark runs. `just bench-promote` promotes changed expect output
  after the diff has been read.
- `just bench NAME` runs `bench-check`, then the `run_bench.exe` of the library of NAME with
  `BENCHMARKS_RUNNER=TRUE`, `X_LIBRARY_INLINING=true`, `-matching NAME`, a time quota (`-quota 2s`
  by default, a recipe parameter) and `-save`, and moves the saved file to
  `bench/results/NAME-<short sha>.txt`.
  It then runs `peak` and `report`. `bench/results/` is in `.gitignore`.
- `just bench-compare OLD NEW NAME` creates a detached `git worktree` for each ref in a temporary
  directory outside the repository, copies the current `bench/` over it, runs `just bench NAME` in
  each (the dune cache is shared, so a ref whose theories are cached builds fast), runs the two refs
  one after the other twice (A, B, A, B) and compares the second pair, and calls `main.exe compare`.
  It requires that both refs define the extraction roots, so it covers the refs after the readability
  rename.
- `just bench-profile NAME` runs `perf record -g` on one child when `perf` exists. It is
  the tool for the gate of section 3.4.

Reproducibility notes for the README. Pin to one core (`taskset -c 2`), a performance governor
if available, and a quiet machine. Report the toolchain (`ocamlfind ocamlopt -version`), the
commit, the cap and the jobs, as the rocq skill requires for performance claims.

## 6. Proof sizes and hours

| Card | Hours | Content |
| --- | --- | --- |
| P2-BENCH1 | 5.5 | extraction, `ppx_bench` setup, thin layer, placeholder workloads, `just` recipes |
| P2-BENCH1B | 4 | Andersen and saturation, SSA and liveness, expect tests |
| P2-BENCH2 | 4 | four abstract domains, expect tests, the C8 gate profile, baselines |
| P2-LIVE1 | 6 | deduplicated in and out tables, chain tables, head search, chain invariants, soundness, ids, size |
| P2-LIVE1B | 4 | tests of the head search, completeness, agreement with `live_in_spec` |
| P2-LIVE2 | 4 | unconditional clocks, the head region, tests of the head region |
| P2-LIVE3 | 5.5 | cover under `SP.wf`, head fields, the switch, tests and numbers |
| P2-PEDGE | 6.5 | inductive edge, narrow key, point key swap |
| P2-INC | 5.5 | `LOCAL_TIME` proofs in `Indexed.v`, row dedup, regional lemmas |

## 7. Decisions of the owner

The owner decided these points on 2026-11-17 (the P2 decisions).

1. The benchmark uses Jane Street Core with `ppx_bench` and `core_bench`, a runner executable per
   library, inline expect tests with `ppx_expect` in `let%test_module` blocks, and
   `textutils.ascii_table` tables. Both shells of `main` and the release environment carry
   these libraries (section 5.4).
2. F9 waits for the benchmark's profile. It runs after P2-LIVE3 if the edge-keyed share justifies
   about 1.4x on `live_in` and 1.3x on `prepare` for 6.5 hours.
3. C8 stays dropped. The gate of section 3.4, run in P2-BENCH2, decides from a profile.
4. IN-3 is accepted. Its widened `width` weakens four frozen time fields and two complexity fields
   by `rcw p`. The gain is nil for systems without side writes.
5. Block liveness with the runtime `cover_ok` fallback is accepted. The fallback costs one
   `forallb` per call and keeps `live_in` total for every prepared program.

# Ruling P2-STRUCTURES: states, Tarjan, the capped join and the planner cap

This ruling answers four items that batch P1 deferred. Two items are accepted with a signature
ruling and a card each, and two are dropped with the numbers below. The reader is the reviewer,
who lands the signature text on the batch base with `Proof. Admitted. (* STUB *)` lemmas, and
the owner, who decided what runs on 2026-11-17 (the P2 decisions). Facts come from reading
`main` = `8228e48a`, the P1 rulings D, E and G2X, the P2 decisions and the P1 reviews. Nothing was
built. Every Rocq text below is uncompiled, so the reviewer compiles it once before a session
starts. The groundwork of the first wave does not hold it. The reviewer lands it on the base of the
cards of this ruling when the owner accepts their gates (the P2 decisions, the groundwork).
Names are those of `main` = `d90c6b3d`, after the readability rename. Line numbers still refer to
`8228e48a`, so find each place by name.

Every statement about cost is derived from the code and marked as derived. No number below is a
measurement.

| Item | Decision | Derived gain | Cost | Card |
| --- | --- | --- | --- | --- |
| 1. Karr and Poly re-elimination | Batch `range_many` accepted for the generic numeric signature and gated on the benchmark's profiles, echelon cache rejected | Karr range cost divides by about the number of queries on one state | 2 cards, 6 h and 3 h | `CARD-P2-RANGE`, `CARD-P2-RANGEX` |
| 2. Tarjan state | Dropped | 30% of `Scc.run`, 10% to 15% of `Wto.build` | 12 h and a frozen signature | none |
| 3. Capped join | Accepted, gated on the benchmark | 2x to 30x on a strike round's join | 3 cards, 3.5 h, 3.5 h and 6 h | `CARD-P2-CAPJOIN`, `CARD-P2-CAPJOINB`, `CARD-P2-CAPRUN` |
| 4. Delta-first beyond 8 atoms | Dropped. The owner raised the cap to 32 atoms in P1 stage 2 | none for any program in the repository | 6 h and extra slots | none |

## 1. Karr and Poly re-elimination

### 1.1 What re-eliminates today

`Karr.leb` already shares one basis between the contradiction test and every target row (P1 item
K1). What remains is that every operation starts from the raw row list. `Karr.range_linear`
(`Karr.v:6361`) builds the basis `equality_basis xs prepared` and walks one target through it.
Each call to `range` therefore pays one elimination, `elimination_work` in the class
`(n + t + 1)^3 * (ellB (n + t + 1) bits + 1)^2` of `range_work_def` (`KarrSig.v:238`), where `n` is
`length rows + length vars` and `t` the size of the queried term.

`Poly.range_linear` (`Poly.v:2691`) runs Fourier-Motzkin elimination of every original variable
with a fresh variable for the queried form. `Poly.leb` is `forallb (keep_row P) Q`, and every
`keep_row` runs `entail_cert`, which normalizes `P` and eliminates again, unless the syntactic scan
`poly_fast` finds the row.

### 1.2 Option A, an echelon basis in the state

The state `reach (list (lcons X.t))` and every field of `KarrSig.v` that speaks of
`Reached P` change. D9 counted about 25 fields. Three more costs come from reading the code.

- A cached basis is a field of a record, and records hold no closures, so it must be built
  eagerly. `assume` (`Karr.v:6270`) is now a list append and `T_assume_le` charges the
  elimination of the new rows only through `assume_work`. With a cache, every `assume`, `assign`,
  `join` and `widen` result pays a basis update, and a state that is never queried pays it for
  nothing. A fixpoint loop builds many such states and queries few.
- `NumStateSig.v` fixes `t` by `LATTICE` laws that every consumer (`RelEnv`, the product
  domain) already instantiates. A new carrier type touches the four `Include ... with Definition t`
  constraints.
- Polyhedra do not profit. Fourier-Motzkin elimination is not an echelon form. A cached system
  holds one projection order, and a query for another variable restarts. So option A helps Karr
  only.

The gain would be the cubic elimination of one `range` and a constant 2 to 3 on `leb`, because
`leb` already shares one basis.

### 1.3 Option B, a batch query

A batch `range_many es s` runs one elimination for the state and one target walk per expression.
It is an additive change with no new carrier, and a state that is never queried pays nothing.

Derived gain for Karr. One query costs `E(n + t)` where `E(d) = d^3 * (ellB d bits + 1)^2`. A
batch of `m` expressions of size `t_i` costs `E(n + sum t_i)` plus `m` walks, and every walk is at
most `E(n')/n'` for `n' = n + sum t_i`, so the walks fit inside the elimination because `m <=
sum t_i <= n'`. The table gives the ratio of `m` single queries to one batch at bit width fixed.

| `n` | `m` | `t_i` | `m * E(n + 3)` | `E(n + 3m)` | ratio |
| --- | --- | --- | --- | --- | --- |
| 100 | 2 | 3 | 2 * 103^3 = 2.2M | 106^3 = 1.2M | 1.8 |
| 100 | 8 | 3 | 8 * 103^3 = 8.7M | 124^3 = 1.9M | 4.6 |
| 20 | 8 | 3 | 8 * 23^3 = 97k | 44^3 = 85k | 1.1 |

The ratio tends to `m` when the state is much larger than the queried terms, and it is near 1
when the queries are as large as the state. So "a factor of about n" in the P1 note holds only
for `m` near `n` queries with small terms.

Derived gain for Poly, Zone and Octagon. None. Poly eliminates toward a fresh variable per
expression, so no intermediate system is shared between two expressions. Zone and Octagon read
closed matrices, and one `range` is already cheap. They implement `range_many` as a map, so the
signature stays generic.

### 1.4 Who calls it

The decision of the owner decides whether the gain is ever collected, and the owner should see
this before accepting.

- `RelEnv.eval` (`RelEnv.v:36`) calls `R.range e (fst s)` once. No analysis in the library
  instantiates `RelEnv` outside `tests/Relational/`.
- `Alarms.alarm` (`Alarms.v:22`) evaluates `map (fun e => S.eval e s) (args k)` on one state, so
  it asks `m` = the arity of one check, 1 to 3. It sees a `STATE_DOMAIN`, which has `eval` and no
  batch, so it cannot reach `range_many`.

So option B as drafted here gives a batch operation that no in-tree client calls. Collecting the
gain needs `eval_many` in `STATE_DOMAIN_OPS` (`StateSig.v:12`), with an implementation in `Env`,
`Disjunction`, `Partition` and `RelEnv`, and a change of `Alarms.alarm` or a new grouped alarm
over all checks of one site (the grouped form reaches `m` above 3). That plumbing is a second
ruling and about 1.5 sessions, and it is not drafted. It is decision O1 below.

### 1.5 Recommendation

Accept option B for `NUM_STATE` and Karr. Reject option A. Do not draft a Poly gain.
The batch is cheap (one card for Karr, one small card for the three instances) and it is the
step that every later plumbing needs. If the owner never wants the plumbing, drop both cards,
because a batch without a caller has no value of its own. The owner decided that both cards wait
for the benchmark's profiles, and that the plumbing through `eval_many` is not drafted
(the P2 decisions).

### 1.6 Signature text, `NumStateSig.v` (frozen, the reviewer updates its hash)

In `NUM_STATE_OPS`, after `range`.

```coq
  Parameter range_many : list (term L.op X.t) -> t -> list (bnd * bnd).
```

In `NUM_STATE_LAWS`, after `range_sound`.

```coq
  (** A batch query returns one range for each expression. *)
  Parameter range_many_length : forall es s, length (range_many es s) = length es.
  (** Each batch range covers the successful concrete result of its expression. *)
  Parameter range_many_sound : forall es s st cs,
    ngamma s (fun y => N.num (st y)) ->
    Forall2 (fun e c => eval_term L.eval st e = Some c) es cs ->
    Forall2 (fun b c => in_bnd (fst b) (snd b) (N.num c)) (range_many es s) cs.
```

No equality `range_many es s = map (fun e => range e s) es` is stated, because it is not
provable for Karr without a completeness argument. The batch basis has another column order
than the basis of each single query, so the two results agree only through the semantic
characterization (the target is in the span of the rows if and only if the form is determined),
which is the `leb_complete_rational` family and about 300 lines for each direction. A test example checks the agreement on the
fixtures instead. The statement `range_many_sound` is enough for every consumer that refines a
value.

In `NUM_STATE_TIME`, add `range_many_work` to the `(* spec: ... *)` comment and insert after
`range_complexity`.

```coq
  Parameter range_many_work : list (term L.op X.t) -> t -> nat.
  Parameter T_range_many : list (term L.op X.t) -> t -> N.
  (** Batch queries charge their stated numeric work. *)
  Parameter T_range_many_le : forall es s,
    (T_range_many es s <= c_num * N.of_nat (range_many_work es s + 1))%N.
  (** A batch query is linear in its stated numeric work. *)
  Parameter range_many_complexity :
    T_range_many es s ∈ 𝑂(N.of_nat (range_many_work es s)) for (es, s).
```

The reviewer adds `range_many_sound` and `range_many_complexity` to the `Main results` list of the
header of `NumStateSig.v`, and the implemented fields to the headers of `Karr.v`, `Poly.v`,
`Zone.v` and `Octagon.v`, as `rules.md` section 7 requires.

In `KARR_PLAN` (`KarrSig.v`), after `range_work_def`.

```coq
  Definition tsizes (es : list (term L.op X.t)) : nat := fold_right Nat.add 0 (map tsize es).
  Definition bitss (es : list (term L.op X.t)) : nat := fold_right Nat.add 0 (map F.bits_e es).
  (** Batch range work charges one elimination over the rows and every queried expression,
      plus the linearization of each. *)
  Parameter range_many_work_def : forall es s,
    (N.of_nat (range_many_work es s) =
      N.of_nat (terms s * (nell s + 1) + (n s + tsizes es + 1)^3 *
        (ellB (n s + tsizes es + 1) (nell s + bitss es) + 1)^2) +
      fold_right N.add 0%N (map F.T_lin_of es))%N.
  (** A batch of one expression charges what a single query charges. *)
  Parameter range_many_work_singleton : forall e s,
    range_many_work (e :: nil) s = range_work e s.
```

The names follow `rules.md` section 7. An unfolding equation is `<subject>_def`, as for
`range_work_def`, and a plan fact has no `F_` number. `KarrSig.v` imports no list notation, so the
singleton is written `e :: nil`, as `elimination_work (Reached (r :: nil))` already is.

`range_many_work_singleton` is true for the code because both measures are the same polynomial
after `tsizes (e :: nil) = tsize e` and `bitss (e :: nil) = F.bits_e e` (`lia`, since
`x + 0 = x`), with `fold_right N.add 0 (x :: nil) = x + 0`. It states that a batch never costs
more than one query for a batch of one. The reviewer adds `tsizes` and `bitss` as definitions in
the signature, and `tsize e >= 1` is a lemma of `Karr.v` (a term has a node, `LangSig.v`), needed
for `m <= tsizes es`.

### 1.7 Why the fields are true for the planned code

Code, in `KarrCode`, with the old `range_linear` kept as the specification.

```coq
  Definition range_in (xs : list X.t) (basis : list karr_row) (prepared : list (lcons X.t))
      (f : lin X.t) : bnd * bnd :=
    (* the body of range_linear after the consistency test, with xs and basis as arguments *)
  Definition range_many_linear (P : list (lcons X.t))
      (fs : list (option (lin X.t * wrapping))) : list (bnd * bnd) :=
    (* one prepare, one variables, one equality_basis, one consistency test, then range_in
       for each form that linearizes without wrapping, and top for every other form *)
  Definition range_many (es : list (term L.op X.t)) (s : t) : list (bnd * bnd) :=
    match s with
    | Unreached => map (fun _ => (NegInf, PosInf)) es
    | Reached P => range_many_linear P (map F.lin_of es)
    end.
```

The basis and the consistency test are computed under a lazy `if` that tests whether any form
linearizes, so a batch of unlinearizable terms pays no elimination.

- Length. `map` keeps the length.
- Soundness. `range_linear_sound` (`Karr.v:11509`) proves its statement from
  `C.check_entails_sound` alone, for the variable list and the basis that its body names, and it
  never uses the order or the content of `xs`. The new lemma `range_in_sound` takes `xs` and
  `basis := equality_basis xs prepared` as arguments, and the old proof applies line by line.
  The wrapped and unlinearizable cases return `(NegInf, PosInf)`, which contains everything.
  The consistency test is shared, and when it fails every result is top.
- `range_many_work_def` and `T_range_many_le`. The clock splits into the shared prepare, variables,
  basis and consistency stages and one `range_in` clock per form. The stages are bounded by the
  lemmas `T_karr_range_linear_components` (`Karr.v:24337`) and `T_karr_range_linear_bounded`
  (`24450`), which fix the variable list to `variables (c :: prepared)`. They must be restated
  for an arbitrary `xs` with `length xs <= n s + tsizes es` and for the bit measure
  `nell s + bitss es`. The names the card must handle are wide. Every queried expression adds its
  variables to `xs`, even a variable that no row mentions, so `length xs` is `n s + tsizes es` and
  not `n s`. Repeated expressions add their size once for each repeat, which the measure
  `tsizes` already counts. The walk and the certificate check of one form cost at most
  `E(n')/n'` for `n' = n s + tsizes es + 1` (the walk is `rows * width * bits^2`, the check
  is bounded by `csize`, which is `n'^2 * bits^2` at the Hadamard width), and `length es <=
  tsizes es` gives `sum` of the walks `<= E(n')`.
- Risk. The per-form bound `E(n')/n'` for one walk and one check is the part not yet proved for a
  shared `xs`. The existing lemmas bound a single query's walk (`T_karr_range_target_bounded`) and
  certificate (`T_karr_range_entail_bounded`) by a cubic `d^3 * v^2`, and `entail_cert_size` bounds
  a certificate by one elimination, so the batch needs a new quadratic bound. If it fails, a walk
  and a check are known to cost one elimination each, and the honest measure gains the term
  `length es * (n s + tsizes es + 1)^3 * (ellB (n s + tsizes es + 1) (nell s + bitss es) + 1)^2`,
  with which a batch costs as much as its single queries. A quadratic term would not cover that
  case. `range_many_work_def` then changes through a `SIG-QUESTION` report, and the batch has no
  stated gain, so the gate decides again. The reviewer lands the text above, since a false field
  must not stay.
- `range_many_complexity` is `T_range_many_le` with `bigO_intro c_num`, five lines.

No revert rule for the Karr fields. If the batch code were reverted to `map range`, the field
`range_many_work_def` would be false (`m` eliminations against one), so the card keeps the code
and leaves an unfinished lemma `OPEN`, as P1-KARR did for K1.

Poly, Zone and Octagon. `range_many es s := map (fun e => range e s) es` and
`range_many_work es s := fold_right Nat.add 0 (map (fun e => range_work e s + 1) es) + 1`.
Length is `length_map`. Soundness is an induction on `es` and `cs` with `range_sound`.
`T_range_many_le` follows from `T_range_le` summed by an induction on `es` over the derived clock
`ListDef.T_map` of Argent's `Std` (its lemma `ListDef.T_map_le` needs one bound for every element,
which a sum of different `range_work`s is not). The per-element overhead of the derived clock of
`map` is a constant `k` per element, so `T_range_many <= (c_num + k) * (work + 1)`. The constant
`c_num` is a `Definition` in each module (`Poly.v:22301`, `Zone.v:2652`, `Octagon.v:2256`,
`Karr.v:24563`) that no law fixes, so each card raises it by a closed expression and records the
old and the new value. Everything that uses `c_num` in the same file is proved again, which is why the three
instances sit in a card of their own.

### 1.8 Consumers outside the cards

`tests/Relational/RelEnvTest.v` (module `Numeric`, line 39 at `main`) defines `NUM_STATE_OPS` by
hand, as the argument `R` of `RelEnvCode`, and gains one line,
`Definition range_many es s := map (fun e => range e s) es.` The reviewer lands it with the
signature. The module `Numeric` of `tests/Relational/Review16Test.v` is a `NUM_VIEW`
(`Definition num (z : Z) := z.`), and that file gets `range_many` from the functors `Karr`, `Poly`,
`Zone` and `Octagon`, so it stays unchanged. No other module implements `NUM_STATE_OPS` by hand.
`RelEnvSig.v`, `RelEnv.v`, `Alarms` and `Interp` stay unchanged.

## 2. Tarjan state (dropped)

### 2.1 What merging saves

Callback trie operations, counted in `Scc.v` (`TarjanVisitor`, lines 115 to 176). Write `n` for
vertices and `e` for non-tree edges.

| Event | Now | Merged `disc`, `low`, `active` |
| --- | --- | --- |
| enter | 3 sets | 1 set |
| leave | 2 gets | 1 get |
| pop, per vertex | `remove low`, `remove active`, `set owners` | 1 update of the merged entry, `set owners` |
| lower the parent, non-root leave | 1 get, 1 set | 1 get, 1 set |
| edge to an inactive vertex | 1 get | 1 get |
| edge to an active vertex | 3 gets, 1 set | 1 get, 1 get, 1 set |

For an acyclic graph with `e = n` (all vertices are roots, no active edges) the callbacks go
from `8n + e = 9n` to `4n + e = 5n`, a saving of 44%. For a graph with every non-tree edge active
and no roots except the first, from `10n + 4e = 14n` to `6n + 3e = 9n`, a saving of 36%. These
are derived counts of trie operations at equal width. Add the search itself, which I did not
count in detail and take as about `2n + e` operations, and the saving on `Scc.run` is about 30%.

### 2.2 What it costs

- `tarjan_active` and `tarjan_disc` and `tarjan_low` are fields of `tarjan_state` in `SccSig.v`,
  which is frozen. `inventory` (`SccSig.v:121`), `width_domain` (`113`), `pop_spec`, `T_tarjan_pop_amort`,
  `tarjan_pop` and `T_tarjan_pop` all name them, so the signature text changes in 11 places.
- `Scc.v` mentions the three fields 393 times, and `Wto.v` reads `tarjan_owners`,
  `tarjan_emitted` and `tarjan_initial` directly in `wto_components`, `wto_components_spec` and
  `wto_components_ready` (74 lemmas of `Wto.v` name `wto_components`). A new record changes the
  proof text of about 800 lines of `Scc.v` and some lines of `Wto.v`. The `Wto.v` change needs a
  card on a file that P1-GRAPH has just closed.
- I estimate two sessions, 12 hours.

### 2.3 Why it does not pay

The only consumer of `Scc.run` and of the Tarjan search is `Wto.v`, and the search runs once for
each nesting level of the weak topological order. The Tarjan callbacks are the larger part of
that run. I take them as about 40% of `Wto.build` (derived from a flat count of search, scoped
materialization and callbacks, not measured), so the saving is about 12% to 15% of `Wto.build`
and smaller for the SSA pipeline, because I found no call of the Tarjan search outside `Scc.v` and
`Wto.v` (`DomProducer.v` imports `Scc` for `scc_graph` only). `Wto.build` is one preprocessing pass over a control flow graph and
is not in a loop. Twelve hours for a constant factor of 1.15 on one preprocessing pass fails the
test that every other P2 item has to meet.

The smaller change, dropping only `active`, saves 2 operations per vertex (about 10% of
`Scc.run`), because `active` and the domain of `low` carry the same set (the two `inventory`
clauses are equivalent). It still changes the frozen `inventory`. Dropped with the rest.

What would change the verdict. A measurement showing that `Wto.build` dominates a pipeline that
the owner cares about. The benchmark of the other P2 planners will show it.

## 3. Capped join (accepted, gated on the benchmark)

### 3.1 What it does

`round_with` (ruling G2X, section 2.1) computes every job of every selected plan, counts the
jobs of each rule, and drops all jobs of a rule that exceeds `match_limit * 2^strikes`. A
strike round pays the whole join, then throws it away. `J.run_upto` stops the join after the
limit.

### 3.2 Gain, derived

Let `M_s` be the match count of a rule at its strike round `s`, `L2^s` the limit of that round
and `c_m` the cost of one match. The uncapped strike round pays `M_s * c_m` and the capped one
pays about `(L2^s + 1) * c_m` plus the dead ends before the last match. The saving is
`1 - L2^s / M_s`. If the table of the rule's relations grows by a factor `g` each round, the
count at the first strike is at most `g` times the limit, and after a ban of `5 * 2^s` rounds
(the default) it is at most `g^(5 * 2^s)` times. For `g = 2` the ratio `M_s / L2^s` is between
2 and 32 at the first strike, so the capped round is 2x to 30x cheaper than the uncapped one.
A rule pays its join at its strike rounds only, about `log2(M / L)` times, so the effect on a run
is the share of strike rounds in the run, which I cannot derive. The first-level scan stays: the
join reads the children of its first pivot, so a capped round still costs the first-level
degree.

### 3.3 Design

Two points decide the design.

- `keep` filters jobs after the join, and the rule's count `n_i` is over kept jobs. A cap on raw
  bindings counts the wrong thing when a plan has a post filter. `plan_post c = []` implies
  `keep p c t = true` (`keep_post` returns `true` on `[]`, `Run.v:230`), which holds for every
  rule without a primitive guard or a repeated variable in one atom. So the capped join serves
  plans with `plan_post c = []` only, and other plans run the full join. The decision of the
  rule is the same as before. Each capped plan is capped at `limit_i + 1`. If one plan is cut,
  `n_i >= limit_i + 1` and the rule exceeds, as before. If no plan is cut, every list is the full
  list (`run_upto_spec` with `length (run ..) <= n`), so a rule that does not exceed keeps exactly
  its old jobs. A cut plan belongs to a rule whose jobs are dropped. So `round_with` returns the
  same result, and every law of `run_with` follows from an agreement lemma, as in the standing
  pattern of the P1 cards.
- A strict language has no lazy list. The code threads a budget `b : N` through the recursion
  and returns as soon as it reaches zero. The loop over the children of a node ends at that
  point, and the children list itself has been built, which `work_at_step` already charges.

### 3.4 Signature text, `JoinSig.v` (frozen, the reviewer updates the hash)

In `JOIN_OPS`.

```coq
  Parameter run_upto : N -> jplan -> list I.t -> list (list (cell V.t)).
```

In `JOIN_LAWS`.

```coq
  (** A capped run keeps the answers that [run] finds first, in the order of [run]. *)
  Parameter run_upto_spec : forall n p ixs, wf_plan p ixs ->
    run_upto n p ixs = skipn (length (run p ixs) - N.to_nat n) (run p ixs).
```

Why this is exact. `enumerate` prepends each answer to `acc`, so `run` lists the answers in
reverse discovery order. The first `n` answers found are the last `n` entries of that list,
which is `skipn (length - n)`. The law gives length `min n (length (run ..))`, soundness
(`In b (run_upto ..) -> In b (run ..)`), duplicate-freeness (`skipn` of a `NoDup` list) and the
equality `run_upto n = run` when `length (run ..) <= n`, which the consumer needs. They are
lemmas of the consumer and need no field.

In `JOIN_TIME`, add `work_upto` to the `(* spec: ... *)` comment and insert after `T_run_le`.

```coq
  Parameter work_upto : N -> jplan -> list I.t -> nat.
  Parameter T_run_upto : N -> jplan -> list I.t -> N.
  (** A capped run pays the work of the explored prefix and, once, the counter of its cap. *)
  Parameter T_run_upto_le : forall n p ixs, wf_plan p ixs ->
    (T_run_upto n p ixs <= c_join * N.of_nat (work_upto n p ixs + length ixs + 2) *
      N.of_nat (wmax p ixs + 1) * N.of_nat ((nvars p + 1) * (nvars p + 1)) +
      c_join * N.of_nat (N.size_nat n + 1))%N.
  (** A capped run is linear in the work of its explored prefix and the bits of its cap. *)
  Parameter run_upto_complexity :
    T_run_upto n p ixs ∈ 𝑂(N.of_nat ((work_upto n p ixs + length ixs + 2) * (wmax p ixs + 1) *
      ((nvars p + 1) * (nvars p + 1)) + N.size_nat n)) for (n, p, ixs) | wf_plan p ixs.
```

The term `c_join * N.of_nat (N.size_nat n + 1)` pays the budget, and it is added once. Each child
pays one test `N.eqb b 0`, which is one match against `0` and fits the per-child term of the work.
Each emitted answer pays one `N.pred b`, whose derived clock walks the trailing zeros of `b`
(`Z.T_pred_double_zeros`, Argent `Std.v`). Take the number of zero bits of the budget as the
potential. Trailing zeros alone would not do, since decrementing an odd number can create many.
One decrement then costs a constant amortized, as `Z.T_pos_sub_zeros` shows for subtraction, so
the decrements of a run cost a constant per answer, which the work pays, plus the zero bits of
`n`, at most `N.size_nat n`. A factor `N.size_nat n + 1` on the whole work would be true as
well. The consumer could not pay it, since `T_run_with_le` charges the bits of a cap in
`sched_work`, once per plan and round and beside the work. It absorbs an added counter term and
no product of the work and the counter (section 3.6). The complexity field is the contract with
`bigO_intro c_join`, since `c_join * a + c_join * (s + 1) = c_join * (a + s + 1)`.

In `JOIN_PLAN`, after `T_run_go`. The spec function mirrors `work_at_step` along the capped
enumeration and returns the unspent budget with the work.

```coq
  (* spec: work_upto_at *)
  Parameter work_upto_at : nat -> jplan -> list I.t -> nat -> list positive -> N -> N * nat.
  (** The children of a pivot node pay their subtrees in order, until the budget is spent. *)
  Fixpoint children_work (p : jplan) (ixs : list I.t) (l : nat) (ns : list positive) (b : N)
      (cs : list (cell V.t)) {struct cs} : N * nat :=
    match cs with
    | [] => (b, 0)
    | c :: rest =>
      if N.eqb b 0 then (b, 0) else
      match advance p ixs l ns c with
      | None => children_work p ixs l ns b rest
      | Some ns' =>
        let '(b', w) := work_upto_at (nvars p - S l) p ixs (S l) ns' b in
        let '(b'', w') := children_work p ixs l ns b' rest in
        (b'', w + w')
      end
    end.
  (** Public capped work starts at the root nodes with the whole cap. *)
  Parameter work_upto_root : forall n p ixs,
    work_upto n p ixs = snd (work_upto_at (nvars p) p ixs 0 (map I.root ixs) n).
  (** The prefix work is at most the full work. *)
  Parameter work_upto_le : forall n p ixs, wf_plan p ixs -> work_upto n p ixs <= work p ixs.
  (** A cap above the answer count explores everything. *)
  Parameter work_upto_full : forall n p ixs, wf_plan p ixs ->
    length (run p ixs) < N.to_nat n -> work_upto n p ixs = work p ixs.
  (** A level with budget left pays the pivot, the probes and the surviving subtrees, in order,
      until the budget is spent. *)
  Parameter work_upto_step : forall p ixs l pre ns j n, nodes_ok p ixs l pre ns ->
    l < nvars p -> choose p ixs l ns = Some j -> (0 < n)%N ->
    snd (work_upto_at (nvars p - l) p ixs l ns n) =
      1 + length (cols p) + length (cols p) *
        (1 + N.to_nat (I.degree (nth j ixs I.empty) (nth j ns 1%positive))) +
      snd (children_work p ixs l ns n
        (I.children (nth j ixs I.empty) (nth j ns 1%positive))).
```

`children_work` is a definition of the signature, so `JoinT` repeats its body. `work_upto_at` is
the implementation's `Fixpoint` on the fuel with an inner `fix` on the children list, the shape of
the code below. A leaf returns `(N.pred b, 1 + nvars p)` and a level without a pivot returns the
work of `recursive_work`, so that the capped work equals the full work when the budget lasts.
`work_upto_step` is an unfolding of `work_upto_at`, after `nvars p - l = S (nvars p - S l)`, and
an induction on the children list that matches the inner `fix` with `children_work`.

`work_upto_full` needs the strict `<`. With `length (run p ixs) = N.to_nat n` the budget reaches
zero at the last answer, and every later child of every open level is skipped, so the work of a
later subtree without answers is missing. For example, a plan with two variables whose first
pivot node has two children, the first leading to the only answer and the second to a level whose
probe fails, has `work_upto 1 < work`. With `length (run p ixs) < N.to_nat n` the budget stays
above zero throughout, and the capped enumeration is the full one. `run_upto_spec` keeps `<=`,
because the list is the whole of `run` either way, and that is all that the consumer needs.

The code, in `JoinCode`, has the shape below. It keeps `enumerate` as the specification.

```coq
  Fixpoint enumerate_upto (fuel : nat) (p : jplan) (ixs : list I.t) (ns : list positive)
      (pre : list (cell V.t)) (b : N) (acc : list (list (cell V.t))) {struct fuel}
      : N * list (list (cell V.t)) :=
    match fuel with
    | 0 => (N.pred b, rev pre :: acc)
    | S rest =>
      match choose_index p ixs (length pre) ns with
      | None => (b, acc)
      | Some j =>
        (fix loop (cs : list (cell V.t)) (b : N) (out : list (list (cell V.t))) {struct cs}
            : N * list (list (cell V.t)) :=
          match cs with
          | [] => (b, out)
          | c :: cs' =>
            if N.eqb b 0 then (b, out) else
            match advance_nodes p ixs (length pre) ns c with
            | None => loop cs' b out
            | Some nodes =>
              let '(b', out') := enumerate_upto rest p ixs nodes (c :: pre) b out in
              loop cs' b' out'
            end
          end) (I.children (nth j ixs I.empty) (nth j ns 1%positive)) b acc
      end
    end.

  Definition run_upto (n : N) (p : jplan) (ixs : list I.t) : list (list (cell V.t)) :=
    if N.eqb n 0 then [] else
    snd (enumerate_upto (level_count p) p ixs (map I.root ixs) [] n []).
```

The entry guard keeps `b > 0` whenever `enumerate_upto` runs, so `N.pred b` at a leaf is a real
decrement.

### 3.5 Proof route and size

- `enumerate_upto_spec`. For all `b > 0`, `enumerate_upto b .. acc = (b - min b |G|, skipn
  (|G| - b) G ++ acc)` with `G = enumerate .. []`. It is an induction on the fuel with an inner
  induction on the children list, and it mirrors `go_sound` and `go_complete` (`Join.v:1690`).
  About 300 lines.
- `run_upto_spec` follows from it and from `run_go`.
- `work_upto_le` and `work_upto_full` are inductions over the same shape as the clock lemma
  `T_go_le` (`Join.v:1752`), about 150 lines.
- `T_run_upto_le` is `T_go_le` for the capped loop, with the budget operations added. The lemma
  about the capped loop states its clock plus `k` times the zero bits of the final budget, at most
  the capped work plus `k` times the zero bits of the initial budget, for a constant `k` that
  `Z.T_pred_double_zeros` gives. The root call then pays at most `N.size_nat n` for the
  counter. About 300 lines.
- Join.v has 101 lemmas, and about 40 of them speak of `go`, `advance` and `choose`. The capped
  loop reuses `advance`, `choose` and their lemmas (`step_ok`, `advance_none`, `choose_min`)
  unchanged, so the new work is the three families above and no existing lemma changes. That is
  the difference from the estimate "about 40 lemmas change" of ruling G2X, which assumed a new
  `go`. Here `go` and `enumerate` stay.

### 3.6 Consumers outside the join card

`Run.v` changes in card `CARD-P2-CAPRUN`. `RunSig.v` does not change. The functor parameter `J :
JOIN` of `Run`, `Saturate` and the clients gains the new fields, and every module that implements
`JOIN` is `Join`, so nothing else must provide them. `tests/Egglog/JoinTest.v` gains examples.

The capped round pays, for each capped plan, the old bound of its join with `work_upto` in place of
`work`, plus `c_join * N.of_nat (N.size_nat cap + 1)`. A cap `N.succ (L * 2^s)` has at most
`N.size_nat L + s + 1` bits, and `sched_work` charges `N.size_nat L` and `N.to_nat s` for each
plan and rule in the round, so the added terms fit `round_work_with` with a larger `c_run`. A
factor `N.size_nat cap + 1` on the join work would not fit, because `sched_work` adds the bits of
the cap to the work and does not multiply them.

### 3.7 Gate

Start the two cards only if the benchmark of the other P2 planners shows, for an explosive
program under `default_sched`, that the joins of strike rounds are at least 20% of the run. Below
that the saving of at most a few percent does not pay 12.5 hours and two frozen-signature
changes. Without a benchmark, the decision stays with the owner (O2).

## 4. Delta-first planning beyond 8 atoms (dropped)

### 4.1 What lifting needs

The cube of `T_plan_le` fails because `sort_pairs` costs about `a^3/6` for an atom of arity `a`
and the planner makes `n + 1` passes (section 4.3 of ruling G2X). A counting placement, each
position in a list of the join width, costs `a * jw` per atom, so a pass costs at most `Q^2` for
query size `Q`, and `n + 1 <= Q + 1` passes fit the cube. The placement would replace
`sort_pairs` for every plan, so an agreement lemma "the placement equals the stable insertion
sort" (about 200 lines) keeps all plans and tests. I estimate one session, 6 hours.

### 4.2 Why it is dropped

- Reach. Andersen and Steensgaard have four rules each with at most two atoms
  (`Clients/Andersen.v`, `Clients/Steensgaard.v`), and no test program has a rule with more than
  three function atoms. The cap of 8 covers every rule in the repository, and so does the cap of
  32 that P1-PLAN2 sets.
- Cost per `put`. P2 adds a slot for each distinct permutation of a pivot atom, and each `put`
  into a relation pays one index update per slot (ruling G2X, decision 1). A rule with 20 atoms
  adds up to 19 slots, spread over the relations it reads. Lifting the cap can make `put` slower
  for programs whose long rules use few atoms of each relation, a regression that the cap
  avoids.
- Risk. The invariants `planner_used` and its family (`Run.v` 3551 to 3960) decide the proof
  size, and the cap-free statement needs a new bound on slots, `2 * (n + 1) * (size + 1)`, which
  is quadratic.

### 4.3 The cheap alternative

The cube argument bounds the passes by `c_run / 65536 = 2^22 / 2^16 = 64` (ruling G2X, section
4.3), so a cap of 16 or 32 in `Nat.leb (length atoms) 8` keeps the statement of `T_plan_le` and the value
of `c_run`, and needs only the numerals of two or three clock lemmas to change. About one hour. I
do not draft it as a card, because the gain is the same unreached territory. The owner decided
O3 on 2026-11-17. The cap rises from 8 to 32 function atoms in card P1-PLAN2 of P1 stage 2,
with at most 33 passes below `c_run >= 2^22` (the P2 decisions), so no P2 card carries it.

## 5. Cards, order and the P1 review patterns

| Card | Owns | Hours | Starts after |
| --- | --- | --- | --- |
| `CARD-P2-RANGE` | `Relational/Karr.v`, `tests/Relational/KarrTest.v` | 6 | signature landed, P1 stage 2 integrated, the benchmark's profile accepted |
| `CARD-P2-RANGEX` | `Relational/Poly.v`, `Zone.v`, `Octagon.v` and their three test files | 3 | same, parallel to RANGE |
| `CARD-P2-CAPJOIN` | `Egglog/Join.v`, `tests/Egglog/JoinTest.v` | 3.5 | P1-EGG2 and step R8 of the readability plan on `Join.v` integrated, the gate of section 3.7 accepted |
| `CARD-P2-CAPJOINB` | `Egglog/Join.v` | 3.5 | CAPJOIN integrated |
| `CARD-P2-CAPRUN` | `Egglog/Run.v`, `tests/Egglog/RunTest.v` | 6 | CAPJOINB, the whole `Run.v` chain of stage 2 (PLAN, PLAN2, BACKOFF, BACKOFF3, BACKOFF2, FUSE) and step R8 on `Run.v` integrated |

`Join.v` and `Run.v` are edited by P1 stage 2 now (P1-EGG2, P1-FUSE and the backoff cards), and
step R8 of the readability plan rewrites their notation, headers and tests after their lanes end.
The three Egglog cards start from the base after both, and each card says so. CAPJOINB needs
CAPJOIN because it proves the work and clock of `J.run_upto`, and CAPRUN needs CAPJOINB because it
calls `J.run_upto` and pays its clock. CAPJOIN writes the code, the law and the tests (CJ-1, CJ-2
and CJ-4), and CAPJOINB writes the plan and time fields (CJ-3). No other P2 card edits `Run.v`
or `Join.v`, which the reviewer checked against the cards of planner A.

Decisions of the owner (2026-11-17, the P2 decisions).

- O1. `range_many` is not plumbed to clients now. `CARD-P2-RANGE` and `RANGEX` wait for the
  benchmark's profiles, and the plumbing through `eval_many` would cost about 1.5 more sessions.
- O2. The capped join waits for the benchmark's profiles and the gate of section 3.7.
- O3. The planner cap rises from 8 to 32 function atoms in P1 stage 2 (section 4.3).
- O4. Tarjan (section 2) and the echelon cache (section 1.2) stay dropped.

Checks against the P1 review patterns.

- Bounds that missed a cost. The batch measure counts the variables of every queried expression
  and their bits, so wide names are in it. A repeated expression adds its size once per repeat.
  The cap counter pays `N.size_nat n` once per capped run, as an added term that the consumer's
  `sched_work` covers. The first-level scan of a capped join is stated as a cost that stays.
- Fields true only after a change that a card could revert. The Karr batch fields hold only for
  the batch code, so the card has no revert rule. The capped join fields hold for the new code
  only, and CAPJOIN has no revert rule for its fields either. Both are listed under each card's
  rules. In `CAPRUN` the reverting of the consumer is harmless, because the agreement lemma keeps
  `round_with` equal and the bounds are the old ones.
- Body changes that break proofs in files a card does not own. `range_many` adds a field to
  `NUM_STATE`, so `Poly.v`, `Zone.v`, `Octagon.v` and the fixture `Numeric` of `RelEnvTest.v`
  must compile, and the reviewer lands stubs for them. `Run.v` uses only the public statements of
  `JoinSig.v`.
- Unbounded slot numbers. CAPRUN adds no slot.
