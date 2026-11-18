# P1 decisions

The owner decided the four questions marked "owner" on 2026-11-16. The reviewer decided the
rest. The rulings files in `rulings/` hold the exact text of each accepted item.

## Landed on `p1/base` first, fully proved

- A1 and A7. `trie_get` stops at the first absent child, `TrieSig.T_get_hit_ge` holds for stored
  keys, and `Graph/Dom.v` gets the version-neutral pre-edit.
- A5. `Word.wrap` is a mask, with the listed pre-edits outside `Bits/`.
- `UnionFindCode.root_of` with its lemmas (P1-TRIE item T5), which P1-DB uses.

## Signature rulings applied on `p1/base` with STUB proofs

- A2. The 25 big-O fields of Base, with the `min` form for set union, intersection and
  difference.
- G1-A and G1-B. The 17 big-O fields of `IndexSig.v` and `DatabaseSig.v`, raw and amortized.
- G2. R1 (the round advances before it applies: `driver_def`, `round_eq_jobs`,
  `round_changed_adds_row`, `T_round_split`), R2, J1 (delete `JoinSig.T_run_ge`), J2, X1, C1, S1,
  and the client fields A1 and T1 of that file.
- D. The 29 big-O fields, the 4 conditional `RelEnvSig.v` fields (P1-STATE has no generic
  lattice fields), and the Zone and Octagon `assign_fast_complexity` fields of D7, because the
  owner accepted Z1 and O1. The optional Poly `leb_present_complexity` stays optional in the card
  as an ordinary theorem.
- B. Tier 1 only (40 fields). Tier 2 restates existing `T_*_le` contracts and is dropped.
  The optional tightening B8 (`T_tnum_normalise_le` linear) is accepted.
- C. The 34 big-O fields on concrete signatures. No field goes into generic lattice or state
  signatures.
- E. `heads_complexity`, `ranks_complexity`, `reducible_b_linear_complexity`, and the replaced `tree_complexity`.
  The exploratory `build_rank_bigO` is dropped.
- F. F1 and the 40 big-O fields (43 STUBs). F2 is dropped, because its field depends on the
  riskiest SSA item.

Policy. An operation gets a big-O field only where no explicit contract already has that
shape, or where the code is in a tighter class than its contract. Pure restatements are
dropped.

## Dropped

A3 (`union_with` and `inter_with`), A4, A6, the Base heap compaction, G2 D1 (copy levels),
C5 to C10, D's echelon basis and batched range queries, dropping `check_entails` in Poly,
B9 and B10 (reducer early stop and skip-top), E's three signature-level drops (Tarjan trie
merge, executed log, `scc_graph` skip), the fused `check_tree`, skipping the dominator check
in SSA (the producer has no correctness proof), F6 to F10, and the per-function arity law in
`DATABASE_LAWS`.

## Owner decisions

- G1-C accepted. The width histories go, in card P1-DBW, after P1-DB, on `p1b/base`.
- Z1 and O1 accepted. Fast zone and octagon assignment, same result on closed matrices.
- Both Egglog extras added. The per-rule match limit with backoff and the literal-first and
  pivot-first planner, in cards after P1-RUN, on `p1b/base` (area G2X).
- All cards run, in waves ordered by dependency and gain.

## Guidelines for every card

- Where an `orb` or `andb` joins two costly operands on an executable path, prefer a lazy
  `if`, with an agreement lemma where a frozen law names the old shape (from area C).
- Line numbers in the cards refer to `07f190c6`. The base adds lemmas, so search by name.

## Egglog extras (ruling G2X, after P1-RUN, on `p1b/base`)

- Cards in order: P1-PLAN before P1-PLAN2, and P1-BACKOFF before P1-BACKOFF2. All four edit
  `Run.v`, so they run one at a time, each after the previous one is integrated. P1-DBW can
  run beside them.
- The signature changes of G2X are additive (`sched`, `run_with` and its laws, plan and time
  fields). `run_with_off` makes `run_with` with no limit equal to `run`.
- Reviewer choices on the questions of G2X: the planner's extra slot indexes are accepted;
  `RunSig.v` gains a `default_sched` with egg's values (match limit 1000, ban length 5);
  limits count the delta matches of semi-naive rounds; `saturate_with` is exposed now (B6);
  the capped join `J.run_upto` is deferred.

## Release

On 2026-11-16 the owner had the last GitHub release, `b2-base`, deleted. Its tag stays, and its
four assets are kept in `~/Projects/galois-assets/b2-base/` (checked against the release's
`SHA256SUMS` before the deletion). The P1 cards therefore bootstrap from a new release `p1-base`,
built with `just assets` from `p1/base` once it is final. It carries a build cache that matches
the base, so sessions skip the cold build. Every card's bootstrap section changes from `b2-base`
to `p1-base` at finalization.

## After review R1 (Opus)

- P1-TRIE item T2 (set operations through `merge_with`) is mandatory and first, because the
  `min`-sized set fields of A2 are false for the present code. If `T_merge_with_min` does not
  close, the three set fields stay `OPEN` with T2's code in place.
- The restatement policy has one exception. The foundations, namely the tries, maps, sets,
  heaps, interning and union-find of `Base` and the Egglog index and database (A2, G1-A, G1-B),
  keep their big-O fields even where a contract already has the shape. They publish the
  complexity that every other component builds on. Elsewhere pure restatements stay dropped.
- Phase 2 on `p1/base` states `T_root_of_le` with `c_uf` and `wf u`, and adds
  `Definition amortized` to `DatabaseT` with the G1-B fields.
- The defects that R1 fixed are in `reviews/REVIEW-P1-R1.md`.

## After review R2 (Opus), and the restatement policy

- The policy that dropped pure restatements is withdrawn. The owner asked for big-O theorems
  for almost every main operation, and reviews R1 and R2 showed the policy was applied
  unevenly. Every accepted field stays, and ruling B's tier 2 fields are accepted again, except
  a tier 2 field on a generic signature that would force more than three trivial STUB lemmas
  (reviewer R3 lists each such drop).
- PLAN2's delta-first planning applies only to rules with at most 8 function atoms, so the
  cube of `T_plan_le` holds. A faster ordering of positions is deferred.
- P1-RUN item 1 (the reorder of ruling R1) is mandatory, because a revert would leave four
  `RunSig.v` statements false. A lemma that does not close stays `OPEN`.
- Phase 2 on `p1/base` deletes the test module `InitialFlagTerminationCounterexample` from
  `tests/Egglog/RunTest.v` together with ruling R1, since it refutes the old budget through the
  old step equations. P1-RUN adds `raised_flag_two_rounds` in its place.
- `saturate_with` gets only its equality law with `saturate` for the unlimited scheduler. A
  public law for limited runs is deferred.
- P1-BACKOFF2 edits `Egraph/Saturate.v` after P1-EGRAPH is integrated, as `OWNERSHIP.md` must
  record.
- The defects that R2 fixed are in `reviews/REVIEW-P1-R2.md`.

## A1 helper restatements (owner approval, 2026-11-16)

The early-exit `trie_get` makes some exact or lower clock facts false, because a miss now
costs less than every key bit. The owner approved restating these helper lemmas, none of which
is a signature field or frozen: `dom_lt_identity_clock_table` and its chain
(`Graph/DomOrder.v`), `dom_time_size_get` (`Graph/Dom.v`), `loop_children_clock_lower`
(`Graph/Loops.v`), and `keep_width_clock_lower` and `keep_width_unbounded` (`Egglog/Run.v`,
now with the binding `[Id 1]`). The permission system had denied the agent's `Run.v` edit, and
the owner approved it directly.

## After review R4 (Opus)

- Accepted: C11 (20 fields) and F11 (26 fields), the restatements that cover the main
  operations left without a field. Ruling F's counts become 39 fields with 42 STUBs, plus F11.
- Dropped: P1-INC item IN-3 (the seen set keyed by row codes is not paid by the frozen
  `T_discovery_le` and `T_demand_le`) and P1-GRAPH item F2 (it breaks the frozen
  `T_df_split` after A1). IN-3 needs a ruling that adds row-code widths to the width measure
  of `INCREMENTAL_TIME`, and is deferred to a later batch.
- Accepted as an optional item of P1-STATE: one generic functor of ordinary theorems in a new
  `Lattice` file that derives `leb`, `join` and `widen` big-O theorems for every `LATTICE_T`
  implementation from its contracts, so no implementation gains a STUB.
- The defects that R4 fixed are in `reviews/REVIEW-P1-R4.md`.

## After review R3 (Opus)

- P1-DBM is split. P1-DBM keeps `Zone.v`, and the new card P1-OCT owns `Octagon.v`. Z1 and O1
  are mandatory, with half-bounded forms, crossed bounds returning `Unreached`, and O1 keeping
  the strengthened entries so closed octagons lose no precision.
- Eight speed items are mandatory because their big-O fields are false for the present code,
  each with a checked counterexample: INTERVAL C1 to C3, KBITS K5a, KARR K3 and K1, and Z1 and
  O1. A lemma that does not close stays `OPEN`, as for P1-RUN.
- Ruling B's tier 2 is back: nineteen fields on signatures with one implementation. Seven B1
  fields on generic signatures (`pleb`, `pjoin`, `pwiden`, `pmeet`, `pnarrow`, `wfwd`, `wbwd`)
  stay dropped, since each would force six or seven STUBs.
- D6's six lattice fields use the new measure `entries`, because `MapSig` never bounds codes by
  nodes.
- A5 must also repair `Domains/Const.v`, `Domains/Reducers.v` and `Domains/IntervalBack.v`.
- INTERVAL keeps the bodies of `pjoin` and `pmeet`, which `States/EnvBudget.v` unfolds.
- The defects that R3 fixed are in `reviews/REVIEW-P1-R3.md`. All four reviews are complete.

## Release and kits (2026-11-17)

- `p1/base` = `b9889589` (`main` plus `root_of`, A1, A5 and three signature passes; 311 STUB
  lemmas; gates passed).
- Release `p1-base` on GitHub, tag at `main` = `07f190c6`: the toolchain and environment of
  `b2-base` (the flake is unchanged) and a new build cache from `b9889589` (cold build with two
  jobs, 23 minutes, 102 MB). Local copy in `~/Projects/galois-assets/p1-base/`.
- Kit `out/P1-kit.tar.gz`, SHA-256 `f19f64588b62399d33fbd2aaca108a0e89074cd5f0202ad9e8da50822d58a208`,
  shared by all 23 stage-1 cards in `out/cards/`. Built by `mkkit-p1.sh`, tested by
  `test-bootstrap-p1.sh` from a fresh GitHub clone.

## No optional items (owner, 2026-11-17)

Stage-1 sessions finished everything above their cut lines and almost nothing below them. From
now on a card has no optional, stretch or below-the-cut items: every item is required, and a
card is sized to fit a session. A cut line only says where to stop if time runs out, and what
follows it goes to the next card. The skipped stage-1 items are folded into later cards
(`LEFTOVERS.md`): `Database.v` items into P1-DBW, the `Run.v` per-plan fusion into a new card
P1-FUSE after P1-BACKOFF2, and the `Join.v` and `Index.v` items into a new card P1-EGG2. Items
worth a few percent, test-only fixtures, and INTERVAL's measured-regressive multiplication are
dropped.
- Stage 2 after the fold (`LEFTOVERS.md`, `OWNERSHIP.md`): on `Database.v` P1-DBW, P1-DBW2 (with
  DB-6) and P1-DBW3 (DB-5) in order; on `Run.v` P1-PLAN, P1-PLAN2, P1-BACKOFF, P1-BACKOFF3,
  P1-BACKOFF2 and P1-FUSE in order; P1-EGG2 (JOIN item 3 and IX-4 on `Join.v` and `Index.v`)
  beside both. Dropped: DB-4, the post-atom half of the fusion, INC's bucket fusion, STATE's
  clock fixtures, INTERVAL's multiplication, PROG PG-5 (only tests use `Cfg.prepare`) and the
  TRIE constant tightening.
- `p1b/base` = `e7657091` (G1-C and G2X applied, 19 STUB lemmas and 4 STUB-CODE placeholders).
  For P1-BACKOFF: `RunSig.v` gives no `TimeFun` for `fresh_mode` or the new record projections,
  so derived clocks need match readers (as `limits_iter` does for `limits`) and the body of
  `fresh_mode` written inline. The placeholders make `run_with_unfolds_loop`, `trace_with_spec`,
  `T_run_with_le` and `saturate_with_run` false until the backoff cards write the code.

## After review R5 (Opus, stage 2)

- R5 fixed 2 high, 8 medium and 9 low defects in the ten stage-2 cards (`reviews/REVIEW-P1-R5.md`),
  among them the `OLat` kind test that DB-5 needs, DB-6's clock bound in `unit db`, strict
  `andb` in DB-6, revert fallbacks for DB-6 and FUSE-1, and ban tests on `chain_seed`.
- IX-4 is dropped after all: with R5's correct design it saves about 1% of an insertion. P1-EGG2
  keeps only JOIN item 3 and owns `Join.v` alone.
- FUSE stays for its memory gain, although its time gain may be a few percent without the
  post-atom half.
- P1-PLAN (~7 h), P1-BACKOFF2 and P1-DBW (~6.5 h) keep their items under the stop rule.
- R5's suggestion to point `T_locate_le` and `T_repair_entry_le` at the new `entry_cells_fit` is
  not taken. On `p1b/base` they cite the helper `entry_cells_written`, which keeps its proof,
  where the new field is a STUB until P1-DBW2.

## Readability joins stage 2 (owner, 2026-11-17)

The owner wants the readability work (`galois-archive/2026-11-17/readability/`) to be part of
stage 2, done on the base by agents: a Haiku swarm for the mechanical parts (scripted renames,
notation rewrites that keep proofs, file headers listing the main results, card updates) and
Sonnet or Opus agents for anything that needs a proof (the Argent complexity layer and
notation, the pin bump, breakage after renames). The stage-2 base, release, kit and cards are
then rebuilt with the new names. A session that started on the old base is integrated by
replaying its patches there and re-running the rename script before the merge.
- PLAN2's cap rises from 8 to 32 function atoms (owner, 2026-11-17). With at most 33 passes the
  planner clock grows by at most 33 times `2^16`, which stays below `c_run >= 2^22`, and the
  slots grow to at most `66 * (size + 1)`. `CARD-P1-PLAN2.md` and ruling G2X section 4.3 are
  updated.


# Rulings for area G1 (P1-DB and P1-INDEX)

Cards P1-DB and P1-INDEX need three rulings. The reviewer applies each accepted ruling to the
signature and puts a `Proof. Admitted. (* STUB *)` lemma for each new field into the owning
implementation (`Egglog/IndexSig.v` into `Egglog/Index.v`, `Egglog/DatabaseSig.v` into
`Egglog/Database.v`), on branch `p1/base`, before the sessions start.

| Ruling | Signature | What it adds | Needed by | Decision |
| --- | --- | --- | --- | --- |
| G1-A | `IndexSig.v`, `INDEX_TIME` | 5 big-O fields | P1-INDEX | accept, additive |
| G1-B | `DatabaseSig.v`, `DATABASE_TIME` | 1 definition and 12 big-O fields | P1-DB | accept, additive |
| G1-C | `DatabaseSig.v`, `DATABASE_PLAN` | replaces the two history lists by the watermark | follow-up card P1-DBW | accepted by the owner, card P1-DBW on `p1b/base` |

G1-A and G1-B change no existing statement. G1-C changes four statements of the plan layer and
one comment, and removes two parameters. No other area uses them (checked with `grep` over
`theories` and `tests` at `07f190c6`). Only `Database.v` and `tests/Egglog/DatabaseTest.v` mention the history lists.
The public time fields `wmark_cells`, `wmark_names` and `wmark_index` stay as they are, so
`Run.v`, `Extract.v` and `Clients/Steensgaard.v` compile unchanged.

## Why the amortized fields have this form

The database contracts are amortized with a potential. The potential is the deferred rebuild
work, `potential B db`. A statement `T_put f k o db <= g` is not provable for the whole
interface with a small `g`, because one `union` queues work that a later `rebuild` pays. The
contracts `T_put_amort`, `T_make_amort`, `T_union_amort` and `T_rebuild_amort` charge each
operation its own clock plus the potential it leaves, against the potential it found.

G1-B states two kinds of big-O fields.

- Raw fields bound the operation's own clock, with no potential. They hold for `find`, `lookup`,
  `init`, `put`, `make`, `union`, `index` and `advance`. The clock of `rebuild` has no raw field
  because it depends on the queued work and is bounded only against the potential.
- Amortized fields bound `amortized T u after before`, which is the clock plus `u` times the
  potential left, less `u` times the potential found. Here `u` is the spending unit of the result.
  They hold for `put`, `make`, `union` and `rebuild`. No field bounds a whole sequence. A
  sequence bound needs one unit `U` that covers every unit of the run, as the plan lemmas
  `T_rstep_go_credit` to `T_rebuild_loop_amort` use it, and the potential starts at zero
  (`potential_init`). The per-operation fields are what clients compose.

The size measure of both kinds is built from `unit db`, which is `(log2 ids + 1) * (size wmark +
1)`. It is the number of bit steps of one identifier or cell operation, so a big-O in `unit` is
a big-O in the bit widths of the largest identifier and the widest cell ever stored.

The raw `put` field is linear in the arity. The existing amortized contract is quadratic,
`(|k| + 2)^2`, and the quadratic part is the rebuild credit, not the direct work. Each of the up
to `|k| + 1` identifier occurrences of a row registers a use entry that is weighted by the whole
row (`entry_weight`), and each entry can be repaired `log2 B` times. The notes called this a
loose contract. It is tight for the present amortization, so the amortized field keeps the
quadratic shape. The raw field is the tighter class that the brief asks for, and its proof
exists already as `T_put_recorded_unit` in `Database.v` (line 30715) and
`T_make_recorded_execution` (line 30749).

## G1-A. `IndexSig.v`, module type `INDEX_TIME`

Add `BigO` to the import line `From Argent Require Import Time Std.`, which becomes
`From Argent Require Import Time Std BigO.`

Insert these five fields after `T_degree_le`, before `End INDEX_TIME.`

```coq
  (** Insertion is linear in the tuple length and the stored bit width. *)
  Parameter insert_complexity : bigO
    (fun x : nat * list (cell V.t) * t => wf (fst (fst x)) (snd x))
    (fun x => N.of_nat ((length (snd (fst x)) + 1) *
      (width (snd x) (snd (fst x)) + 1)))
    (fun x => T_insert (snd (fst x)) (snd x)).
  (** Removal is linear in the tuple length and the stored bit width. *)
  Parameter remove_complexity : bigO
    (fun x : nat * list (cell V.t) * t => wf (fst (fst x)) (snd x))
    (fun x => N.of_nat ((length (snd (fst x)) + 1) *
      (width (snd x) (snd (fst x)) + 1)))
    (fun x => T_remove (snd (fst x)) (snd x)).
  (** Child lookup is linear in the bit width of one edge. *)
  Parameter child_complexity : bigO (fun _ => True)
    (fun x : t * positive * cell V.t =>
      N.of_nat (width (fst (fst x)) [snd x] + 1))
    (fun x => T_child (fst (fst x)) (snd (fst x)) (snd x)).
  (** Child enumeration is linear in the degree and the bit width of a node. *)
  Parameter children_complexity : bigO
    (fun x : nat * t * positive => wf (fst (fst x)) (snd (fst x)))
    (fun x => N.of_nat ((N.to_nat (degree (snd (fst x)) (snd x)) + 1) *
      (width (snd (fst x)) [] + 1)))
    (fun x => T_children (snd (fst x)) (snd x)).
  (** Degree lookup is linear in the bit width of a node. *)
  Parameter degree_complexity : bigO (fun _ => True)
    (fun x : t * positive => N.of_nat (width (fst x) [] + 1))
    (fun x => T_degree (fst x) (snd x)).
```

Why they are true. `T_insert_le`, `T_remove_le`, `T_child_le`, `T_children_le` and
`T_degree_le` already have this shape with the constant `c_ix`. Each field is
`bigO_intro` with `c := c_ix` and a rewrite by `Nat2N.inj_mul` and `Nat2N.inj_add`. The proof
is `exists c_ix` followed by `intros x Hx` and `nia` over the instance of the contract, about 8
lines per field.

The contracts keep their shape after the speed changes of P1-INDEX, because the new `insert`
tests membership with `contains` and then walks only an absent tuple, and `remove` walks only a
present one. Both cost at most the old clock, so `T_insert_le` and `T_remove_le` are proved again
for the new body with the same constants. The fields therefore hold unchanged.

Proof size is about 60 lines in total. The mutual dependence is none.

## G1-B. `DatabaseSig.v`, module type `DATABASE_TIME`

Change the import line to `From Argent Require Import Time Std Loop BigO.`

Insert the definition after `slots_of`, before `Parameter potential`.

```coq
  (** The clock of an operation plus the potential it leaves, less the potential it found,
      with potentials priced at the spending unit [u] of the result. *)
  Definition amortized (T : N) (u : nat) (after before : N) : N :=
    (T + N.of_nat u * after - N.of_nat u * before)%N.
```

`DatabaseT` (`Database.v:24630`) repeats this definition with the same body, as it repeats
`unit` and `slots_of`, because a module type's `Definition` must reappear in the module that
implements it.

Insert these twelve fields after `T_ids_le`, before `End DATABASE_TIME.`

```coq
  (** Find is linear in the bit steps of one identifier operation. *)
  Parameter find_complexity : bigO
    (fun x : positive * t => wf (snd x) /\ allocated (snd x) (fst x))
    (fun x => N.of_nat (unit (snd x)))
    (fun x => T_find (fst x) (snd x)).
  (** Lookup is linear in the key length and the key's encoded cells. *)
  Parameter lookup_complexity : bigO
    (fun x : positive * list (cell V.t) * t => wf (snd x))
    (fun x => N.of_nat ((length (snd (fst x)) + 1) * unit (snd x) +
      fold_right (fun c n => cell_bits V.encode c + n) 0 (snd (fst x))))
    (fun x => T_lookup (fst (fst x)) (snd (fst x)) (snd x)).
  (** Initialization is linear in the declarations and the permutation sizes, with the
      layout work of insertion sorting. *)
  Parameter init_complexity : bigO (fun _ => True)
    (fun x : list decl * list (positive * list nat) =>
      N.of_nat ((length (fst x) + length (snd x) + layout_work (snd x) + 1) *
        (fold_right (fun s n => length (snd s) + n) 0 (snd x) + 1) +
        (fold_right (fun d n => Pos.size_nat (name d) + n) 0 (fst x) +
         fold_right (fun s n => Pos.size_nat (fst s) + n) 0 (snd x))))
    (fun x => T_init (fst x) (snd x)).
  (** Insertion, without its share of the deferred rebuild, is linear in the arity and the
      number of slots of its function. *)
  Parameter put_complexity : bigO
    (fun x : positive * list (cell V.t) * option (cell V.t) * t =>
      let '(f, k, o, db) := x in wf db /\ slots_fit db f (length (k ++ option_list o)))
    (fun x => let '(f, k, o, db) := x in
      N.of_nat ((length k + 1) * (slots_of db f + 1) * unit (put f k o db)))
    (fun x => let '(f, k, o, db) := x in T_put f k o db).
  (** Constructor allocation, without its share of the deferred rebuild, has the same class. *)
  Parameter make_complexity : bigO
    (fun x : positive * list (cell V.t) * t =>
      let '(f, k, db) := x in wf db /\ slots_fit db f (S (length k)))
    (fun x => let '(f, k, db) := x in
      N.of_nat ((length k + 1) * (slots_of db f + 1) * unit (snd (make f k db))))
    (fun x => let '(f, k, db) := x in T_make f k db).
  (** Union, without queued work, is linear in the bit steps of one identifier operation. *)
  Parameter union_complexity : bigO
    (fun x : positive * positive * t =>
      let '(i, j, db) := x in wf db /\ allocated db i /\ allocated db j)
    (fun x => let '(i, j, db) := x in N.of_nat (unit db))
    (fun x => let '(i, j, db) := x in T_union i j db).
  (** Insertion pays its own clock and the rebuild credit of its new use entries. *)
  Parameter put_amort_complexity : bigO
    (fun x : N * positive * list (cell V.t) * option (cell V.t) * t =>
      let '(B, f, k, o, db) := x in
      wf db /\ slots_fit db f (length (k ++ option_list o)) /\ (ids (put f k o db) <= B)%N)
    (fun x => let '(B, f, k, o, db) := x in
      N.of_nat (unit (put f k o db) * ((length k + 1) * (length k + 1)) *
        (slots_of db f + 1) * (N.to_nat (N.log2 B) + 1)))
    (fun x => let '(B, f, k, o, db) := x in
      amortized (T_put f k o db) (unit (put f k o db))
        (potential B (put f k o db)) (potential B db)).
  (** Constructor allocation has the same amortized class as insertion. *)
  Parameter make_amort_complexity : bigO
    (fun x : N * positive * list (cell V.t) * t =>
      let '(B, f, k, db) := x in
      wf db /\ slots_fit db f (S (length k)) /\ (ids (snd (make f k db)) <= B)%N)
    (fun x => let '(B, f, k, db) := x in
      N.of_nat (unit (snd (make f k db)) * ((length k + 1) * (length k + 1)) *
        (slots_of db f + 1) * (N.to_nat (N.log2 B) + 1)))
    (fun x => let '(B, f, k, db) := x in
      amortized (T_make f k db) (unit (snd (make f k db)))
        (potential B (snd (make f k db))) (potential B db)).
  (** Union is constant at the spending unit, because it only queues rebuild work. *)
  Parameter union_amort_complexity : bigO
    (fun x : N * positive * positive * t =>
      let '(B, i, j, db) := x in
      wf db /\ allocated db i /\ allocated db j /\ (ids db <= B)%N)
    (fun x => let '(B, i, j, db) := x in N.of_nat (unit (union i j db)))
    (fun x => let '(B, i, j, db) := x in
      amortized (T_union i j db) (unit (union i j db))
        (potential B (union i j db)) (potential B db)).
  (** Rebuilding is linear in the pending equalities at the spending unit. *)
  Parameter rebuild_amort_complexity : bigO
    (fun x : N * t => let '(B, db) := x in wf db /\ (ids (rebuild db) <= B)%N)
    (fun x => let '(B, db) := x in
      N.of_nat (unit (rebuild db) * (pending db + 1)))
    (fun x => let '(B, db) := x in
      amortized (T_rebuild db) (unit (rebuild db))
        (potential B (rebuild db)) (potential B db)).
  (** Slot lookup is logarithmic in the slot number. *)
  Parameter index_complexity : bigO (fun _ => True)
    (fun x : N * bool * t => N.of_nat (N.to_nat (N.log2 (fst (fst x))) + 1))
    (fun x => T_index (fst (fst x)) (snd (fst x)) (snd x)).
  (** Advancing is constant, because it empties the new-row indexes with one store. *)
  Parameter advance_complexity : bigO (fun _ => True) (fun _ : t => 0%N) T_advance.
```

Why they are true.

- `find_complexity`, `lookup_complexity`, `init_complexity`, `index_complexity` are `bigO_intro` with `c := c_db`. They follow
  from `T_find_le`, `T_lookup_le`, `T_init_le` and `T_index_le`. The measure of `lookup_complexity` is the
  right-hand side of `T_lookup_le` with `c_db` factored out, so the bound is the contract itself.
  About 10 lines each.
- `put_complexity` is `bigO_intro` with `c := 131072 * (I.c_ix + PTrieT.c_trie + UnionFindT.c_uf + V.c_key
  + V.c_val + DatabaseUseMap.c_map + 1)`. `T_put_recorded_unit` gives `T_put <= 65536 * C *
  (slots_of + 1) * (|k| + 2) * unit (put ..)`, and `|k| + 2 <= 2 * (|k| + 1)`. About 15 lines,
  the nonlinear step is one small lemma.
- `make_complexity` follows the same way from `T_make_recorded_execution`.
- `union_complexity` follows from `T_union_unit_bound` (`T_union <= c_db * unit db`) with `inv db` from
  `wf_inv`.
- `put_amort_complexity`, `make_amort_complexity`, `union_amort_complexity` and `rebuild_amort_complexity` follow from
  `T_put_amort`, `T_make_amort`, `T_union_amort` and `T_rebuild_amort`. From
  `T + u * p' <= u * (budget + p)`, `lia` over `N` gives `T + u * p' - u * p <= u * budget`, because
  truncated subtraction only loses when the left side is smaller. Then `(|k| + 2)^2 <= 4 * (|k| +
  1)^2` (one `nia` lemma) gives `c := 4 * c_db`. For `union_amort_complexity` and `rebuild_amort_complexity`
  the constant is `c_db`. About 25 lines each.
- `advance_complexity` needs a new constant bound. The existing proof of `T_advance_le` unfolds
  the clocks of three record updates and ends in `nia` against `c_db * (num_slots + 1)`. The same
  proof without the `num_slots` factor gives `T_advance db <= c_db`, because `PTrieCode.empty` and
  the record stores have constant clocks. The contract `T_advance_le` was loose.

After the speed changes of P1-DB the fields stay true. Item DB-2 replaces `find` by a walk in
`normal_cell`, which lowers `T_put` and keeps the premises of `T_put_recorded_unit` unchanged.
Item DB-3 skips row identity for rows without identifier cells and lowers `T_put` again.

Proof size is about 300 lines. The mutual dependence is none.

## G1-C. `DatabaseSig.v`, module type `DATABASE_PLAN`: the width histories

The owner accepted this ruling. It trades four plan statements for a memory bound.

The problem. `db_written_cells` (list of cells) and `db_index_counters` (list of positives)
are fields of the database state. `database_record_cache` (`Database.v:2159`) and
`database_record_inputs` (`Database.v:2184`) prepend to them on every `put`, `make` and slot
update, and `ensure_row_identity` (`Database.v:2692`) prepends the row counter. Nothing removes
an entry. A `put` with arity 3 and 4 slots prepends about 31 list cells, 9 cells and 22
counters, so ~0.7 KB on a 64-bit machine (derived from the code, not measured). One million
puts keep ~0.7 GB alive, and the lists are never read by any executable operation. They exist
only so that `wmark` can be defined as a maximum over them and `index_history` can bound the width
of cached indexes. `wmark` is used in `unit`, so it appears in every time contract.

The change. Replace the two lists by two counters in the state, and define `wmark` from them.
The implementation, which belongs to the follow-up card P1-DBW, has three parts.

- `db_wmark : N` already exists in the state and holds a constant set at `init`. It becomes the
  running maximum of the function names and cell codes passed to `put` and `make`.
  Updating costs one `N.max` per cell, which is `O(bits)` and falls inside the existing
  `(|k| + 2) * unit` factor.
- A new `db_ticks : N` counts the cells and calls recorded. It grows by `|u| + 1` in each
  `slots_update` and by 1 in `ensure_row_identity`.
- `wmark db := N.max (N.max (db_nuses db) (ids db)) (N.max (db_wmark db) (N.succ (db_ticks db)))`.

The facts that the lists gave are recovered from public laws. The next counter of an index
satisfies `next (insert r ix) <= next ix + length r` (`next_insert` in `INDEX_LAWS`), so every
cached index has `I.next ix <= 1 + db_ticks`. The index width satisfies `max_cell_bits (insert r
ix) <= Nat.max (max_cell_bits ix) (cells of r)` (`max_cell_bits_insert`), so every cached
index has `I.max_cell_bits ix <= N.size_nat (db_wmark db)`. These two invariants replace
`database_index_history` (31 uses in `Database.v`) and clause 4 of `metadata_ok`.

The lists carry eight more facts. Each reaches `wmark` through `recorded_counters_wmark`
(`Database.v:25367`, 10 uses) or `recorded_cells_wmark` (`25384`), and each has a counter form
that `init` sets and every operation keeps.

| Fact read from the lists today | Where it is used | Replacement |
| --- | --- | --- |
| `1` is a recorded counter | `metadata_ok` clause 1, `wmark_pos` | `1 <= N.succ (db_ticks db)` |
| `N.succ_pos (length (slots db))` is recorded | `metadata_ok` clause 2, `metadata_slot_strict` for `slot_place_spec` | `N.succ (N.of_nat (length (slots db))) <= db_wmark db`, set by `init` |
| the cache counter is recorded | `metadata_ok` clause 3, `metadata_updates_wmark` | `db_cache_updates db <= db_ticks db` |
| the rank `length u + 1` of a slot update is recorded | `slots_update_rank_wmark`, `repair_temporary_wmark` | `N.of_nat (length u + 1) <= N.succ (db_ticks (slots_update b f u db))` |
| the row counter is recorded | `database_row_store_ok` (`3301`), `row_counter_lt` | `Npos (row_fresh (db_row_store db)) <= N.succ (db_ticks db)` |
| the name passed to `put` or `make` is recorded | `record_inputs_function_wmark` | `Npos f <= db_wmark` of the result |
| the key cells of use entries are written cells | `database_row_store_ok`, `entry_cells_fit` | each cell code `<= db_wmark db` |
| the cells of stored rows are written cells | `wmark_cells` | each cell code `<= db_wmark db` |

The declared names, which the old `wmark` read from `decl_names`, need
`Npos f <= db_wmark db` for each declared `f`, which `init` sets through `database_max_name`.
The ticks pay for the slot-update rank and the cache counter because each slot update adds
`length u + 1` to `db_ticks`. The row counter grows only in `ensure_row_identity`, which adds 1.

Exact signature change in `DATABASE_PLAN`.

1. In the comment `(* spec: rows uses_entries queue next_id forest_ok class_size uf_state
   index_counters written_cells located decl_names *)`, remove `index_counters written_cells`.
2. Delete `Parameter index_counters : t -> list positive.` and
   `Parameter written_cells : t -> list (cell V.t).`
3. Replace `row_counter_lt` by

```coq
  (** Row identifiers stay below a counter that the watermark covers. *)
  Parameter row_counter_lt : forall db work f k r, inv_on db work -> row_id db f k = Some r ->
    (r < next_row db)%positive /\ (row_parent db r < next_row db)%positive /\
    (Npos (next_row db) <= wmark db)%N.
```

4. Replace `entry_cells_fit` by

```coq
  (** The keys of use entries fit the watermark. *)
  Parameter entry_cells_fit : forall db work x f k c, inv_on db work -> uses db x (f, k) ->
    In c k -> cell_bits V.encode c <= N.size_nat (wmark db).
```

5. Replace `wmark_pos` by

```coq
  (** The watermark covers the counter of the empty index. *)
  Parameter wmark_pos : forall db, inv db -> (1 <= wmark db)%N.
```

6. Replace `wmark_covers` by

```coq
  (** The watermark covers the allocation counter, the use counter and every declared name. *)
  Parameter wmark_covers : forall db, inv db ->
    (N.max (nuses db) (ids db) <= wmark db)%N /\
    (forall f, kind (view db) f <> None -> (Npos f <= wmark db)%N).
```

`wmark_covers_index`, `wmark_cells`, `wmark_names`, `wmark_index`, `decl_names_spec` and `decl_names`
stay as they are. The old `wmark_covers` was an equation. The new one is an inequality, so the
watermark may be larger than the old maximum. It is the maximum over all values ever written
(`db_wmark` never decreases), which is what the old definition was. The loss is the exact
equation. Consumers use only upper bounds, so no consumer changes. A big-O stated in `unit`
stays a big-O in the bit widths of the largest value ever stored.

Gain. Memory per operation drops from ~31 list cells to zero. Time drops by the append and
the second `slot_updated_counters` traversal (about `2S` small trie reads per slot update, with
`S` the number of slots), about 5 to 10% of a `put`. The cost of the running maximum is `O(|u|)`
`N.max` calls per update. Net time gain is small and the memory gain is the point.

Proof size. About 250 sites in `Database.v` mention the histories (`db_written_cells` 62,
`db_index_counters` 64, `written_cells` 77, `index_counters` 106, `database_index_history` 31).
Most are `incl` monotonicity lemmas that become `<=` monotonicity lemmas, and the
`database_index_history_*` family (about 100 lines) disappears. Estimate 4 to 6 hours, one
session, so it is a separate card (P1-DBW) that follows P1-DB on the same file. The tests that
read the histories (`tests/Egglog/DatabaseTest.v` lines 78, 164, 172, 255, 267, 396, 648) change
with it.

Drop option. If the owner rejects G1-C, nothing else in the cards depends on it. The memory
growth stays and is documented in `docs/performance.md` as a known limit.

## Items that need no ruling

These speed items change bodies only inside `Database.v` and `Index.v` and keep every signature
statement. They are listed here so that the reviewer can confirm the claim.

- DB-2 (root-only find at three sites). It uses `UnionFindCode.root_of`, which item T5 of `CARD-P1-TRIE.md` adds with public
  lemmas. The reviewer lands T5 in `p1/base` first (see the dependency in `CARD-P1-DB.md`).
- DB-3 (rows without identifier cells skip row identity). `row_locate`, `row_absent`,
  `forest_located` and `inv_on` constrain `row_id` only for keys that have an entry, and a
  row without an identifier cell has none. The row count of `row_counter_lt` is conditional on
  `row_id db f k = Some r`.
- DB-4 (row code computed once). Pure refactor, same values.
- IX-1 to IX-3 in `CARD-P1-INDEX.md` (membership first, fresh path built directly, empty nodes
  dropped). `insert_def` and `remove_def` are equations between the new bodies and the
  stepwise specification, proved by an agreement lemma. `next_remove`, `mem_*` and `node_*`
  stay true, because the reads go through `read_node`, which answers an absent node with the
  empty node. IX-2 drops a node only when it equals `empty_node` (no edges, degree 0, not
  terminal), so every read agrees with the old table on every index, valid or not.

## Items rejected

- Skipping the projection count table for slots whose permutation covers the whole tuple. A
  function name has no declared arity in `Database.v`. `slots_fit db f n` is checked per call, so
  one function can hold rows of arities 2 and 3. Take the slot permutation `[0; 1]`, the row
  `k = [a], o = Some b` (arity 2, injective projection `[a; b]`) and the row `k = [a; b], o = Some
  d` (arity 3, projection `[a; b]`). Both project to `[a; b]`, the true count is 2, and a table
  that skips the first row stores 1, so removing the second row would delete `[a; b]` from the index
  while the first row stays. The skip is sound only under a per-function arity invariant, which
  would be a signature change in `DATABASE_LAWS`. Not proposed.
- Counting projections inside the index terminal marker. It needs a counting insert in
  `INDEX_OPS`. Large, unmeasured gain. Not proposed.
- Choosing the union winner by bucket length. It changes `UnionFind.union` (area A) and the
  doubling law `class_size_doubles`. Not proposed.
- Per-row repair entries. It changes `entry_weight` and the credit laws. Not proposed.


# Ruling P1-G2X: backoff scheduler and literal-first, pivot-first planning

Base is `07f190c6` plus the reorder of ruling P1-G2, section R1, as integrated by card P1-RUN.
The target branch is `p1b/base`. Nothing here is built, and every Rocq text must be compiled once
by the reviewer before the sessions start. The text extends ruling P1-G2, items D2 and D3 of its
section 9, which the owner has now accepted.

## 0. Summary

| ID | File | Change | Kind | Needs the reorder R1 |
| --- | --- | --- | --- | --- |
| B1 | `RunSig.v` | Three records, three definitions and `unclean_rounds` | behaviour, additive | no |
| B2 | `RunSig.v` | Operation `run_with` in `RUN_OPS` | behaviour, additive | no |
| B3 | `RunSig.v` | Eight laws of `run_with` in `RUN_LAWS` | behaviour, additive | yes |
| B4 | `RunSig.v` | Driver, loop law, trace law and termination bound in `RUN_PLAN` | behaviour, additive | yes |
| B5 | `RunSig.v` | `trace_with`, clock `T_run_with`, its contract and one big-O field in `RUN_TIME` | time, additive | yes |
| B6 | `SaturateSig.v` | `saturate_with` and two laws | client hook, accepted | yes |
| P1 | `Run.v` | Literal-first variable order | speed, no signature change | no |
| P2 | `Run.v` | Pivot-first variable order per semi-naive plan | speed, no signature change | yes |

No existing statement changes. `Egglog/Syntax.v` stays as it is, `limits` keeps its two fields,
and `Clients/Andersen.v`, `Clients/Steensgaard.v` and every test compile unchanged. B6 is the
only edit outside `RunSig.v`. The reviewer accepted it on 2026-11-16 (`DECISIONS.md`), so
`SaturateSig.v` gains its text and `Egraph/Saturate.v` gains `saturate_with`, first as a
placeholder on `p1b/base` and then in card P1-BACKOFF2.

## 1. Choices

### 1.1 A new record `sched`, and a second entry point `run_with`

The owner's rule is to change `limits` only if nothing else works. Two alternatives exist.

- Add the two fields to `limits`. Every `Limits a b` expression changes. They occur in
  `Clients/Andersen.v` (line 1335), in `tests/Egglog/RunTest.v` (about 10 places) and in every
  client that builds limits. `Syntax.v` is frozen, so this needs a ruling for a file that
  every other card depends on.
- Add a `sched` argument to `run`. Every law of `RUN_LAWS` that mentions `run`, `Saturate.v`, `Andersen.v`,
  `Steensgaard.v` and their three signatures change.

The choice is a new record `sched` and a new operation `run_with p cp lim sc db`. The old `run`
keeps its text and its proofs. The law `run_with_off` says that `run_with` with a scheduler that
has no limit is `run`, so the default behaviour is the old one and the backoff changes a result
only when a limit fires, which is the owner's condition. The cost is that the laws of `run` that
a client wants under backoff exist a second time (B3). The proofs are shared, because they
speak of arbitrary subsets of the jobs of a round.

### 1.2 Scheduler state in a record `mode`, not in `D.t`

A ban needs a table that survives from round to round. `DatabaseSig.v` has no place for it, and a
table inside the database would change a signature that three cards use. The driver state of
`run_with` is therefore `mode * D.t`, where the old driver has `bool * D.t`. The old `driver`,
`trace`, `run_unfolds_loop` and their clock statements stay as they are.

### 1.3 What a ban skips, and why a catch-up round is needed

R1 makes the rows of a round the delta of the next. A rule that skips a round loses the matches
that use that round's delta, and a semi-naive plan never finds them again, because the delta is
consumed. The scheduler therefore marks a banned rule `stale`. When its ban ends, the rule runs
its naive plan in the next round, whatever the mode of the driver, and the mark clears if the
rule does not exceed its limit again. This matches egg, which searches every match when a rule
resumes, and it keeps the lost derivations from waiting for a quiet round. The soundness of
`Saturated` does not depend on the mark, because the final round is a clean naive round and
covers every match. The mark costs one flag per rule and one more case in the plan selection.

### 1.4 The join is not capped

egg stops a search after `limit` matches. `JoinSig.v` has no bounded run, and adding one is a
frozen-file change with about 40 lemmas in `Join.v`. So the strike round pays the full join and
the apply is dropped. Banned rounds pay neither. A rule pays the join about once per strike, and
strikes are logarithmic in its match count, because the limit doubles. A capped `J.run_upto` is
listed as a later item in section 9.

## 2. The scheduler

### 2.1 Definition of the round

Let `md` be the mode and `now = now md`. For a rule `i`, `banned md i` means
`now < until (stat md i)`. The round `round_with p cp sc md db` is as follows.

1. Select plans. If `naive_next md` then the naive plan of every unbanned rule. Otherwise the
   naive plan of every unbanned stale rule, and the semi-naive plans of every unbanned rule that
   is not stale.
2. Compute the jobs of the selected plans from `db`, with the same `keep` filter and the same
   plan order as `jobs`.
3. For each selected rule `i`, let `n_i` be the number of its jobs. The rule exceeds its limit
   when `match_limit sc = Some L` and `L * 2^(strikes i) < n_i`.
4. Drop the jobs of every rule that exceeds. Such a rule gets `strikes + 1`,
   `until := now + ban_length sc * 2^strikes` (with the old strike count) and `stale := true`.
   Every other selected rule that ran its naive plan gets `stale := false`. A rule that ran only
   semi-naive plans keeps its mark, which is `false`.
5. Apply the kept jobs in order to `D.advance db`, then rebuild, as R1 does.
6. Return `now + 1`, the new table, and `clean = true` exactly when no rule was banned at `now`
   and no rule exceeded.

The driver `driver_with` calls it and then does the following. It returns `IdLimit` as the old
driver does. It returns `Saturated` exactly when `naive_next md`, the flag `D.changed next` is
down and `clean` holds. Otherwise it continues with `naive_next := negb (D.changed next)`. After a
quiet naive round that is not clean, it first moves `now` to the least `until` above `now`, as
egg's `can_stop` does, so that a run with only banned rules left does not spend rounds waiting.

Every naive round starts from a state with a down flag. The first round is semi-naive. A naive
round follows a quiet round only, and a quiet round returns a state whose flag is down by the
step equation of R1. This is the premise of `naive_quiet_closed`.

### 2.2 Why `run_with_off` holds

With `match_limit sc = None` no rule exceeds, so no table entry changes except the counter. No
rule is ever stale, and the selection is the naive list or the semi list, so every round is the
round of R1. The states differ in type, and the proof is a simulation of the two loops by
induction on the fuel, with the relation `naive_next md = nv` and an invariant on the mode.
Every entry of `stats md` has `until <= now md` and `stale = false`. The fresh mode has it, and a
round without a limit keeps it, because no entry is banned or marked and `now` only grows. The
simulation is false for a mode without the invariant, because an entry with `until > now` bans
its rule and makes the round unclean. The selection filters the naive and semi lists in their
order, and an index past the end of the table reads the default entry `RStat 0 0 false`. So
`run_with_off` holds for every program and plan, without `plans_ok`.

## 3. Signature text for B1 to B5

All text goes into `RunSig.v`. No new import is needed.

### 3.1 B1, after `program_terms` and before `RUN_OPS`

```coq
(** A backoff scheduler bans a rule whose matches in one round exceed its limit, as egg does. A
    rule with [strikes] earlier bans may match [match_limit * 2^strikes] times in a round, and its
    next ban lasts [ban_length * 2^strikes] rounds. [None] never bans. *)
Record sched : Type := Sched { match_limit : option N; ban_length : N }.

Definition no_backoff : sched := Sched None 0%N.

(** egg's scheduler. A rule may match 1000 times in a round before its first ban, and that ban
    lasts 5 rounds. *)
Definition default_sched : sched := Sched (Some 1000%N) 5%N.

(** What the scheduler remembers of one rule. A stale rule lost matches to a ban and runs its
    naive plan before it returns to semi-naive rounds. *)
Record rstat : Type := RStat { strikes : N; until : N; stale : bool }.

(** The state of a driver call. The table is indexed by rule number. The flag [clean] says that
    the round that produced the state found no rule banned and banned none. *)
Record mode : Type := Mode { naive_next : bool; now : N; stats : list rstat; clean : bool }.

Definition fresh_mode {V} (p : program V) : mode :=
  Mode false 0%N (repeat (RStat 0%N 0%N false) (length (rules V p))) true.

(** The rounds of a trace that met a ban. *)
Definition unclean_rounds {T : Type} (tr : list (mode * T)) : nat :=
  length (filter (fun st => negb (clean (fst st))) tr).
```

The table is a list so that the specification stays simple. The code reads entry `i` with a
binary countdown, as `rule_at` does. The countdown pays about one step per entry that it passes
plus the bits of `i`, by the credit lemma `loopN_pred_credit` of `Base/Loop.v`. The pessimistic
clock `|rules| * bits i` of `run_split_rule_clock` is too large, because `sched_work` of B5 has
no factor `bits i`. A checked plan's rule index is below `length (rules V.t p)`, which equals
`length (stats md)` along a trace, so `sched_work` pays one lookup per plan.

### 3.2 B2, in `RUN_OPS`, after `run`

```coq
  Parameter run_with : program V.t -> compiled V.t -> limits -> sched -> D.t -> stop * D.t.
```

### 3.3 B3, in `RUN_LAWS`, after `run_limits`

Each law is the law of `run` with `run_with p cp lim sc` in place of `run p cp lim`, and with the
premises of the old law. The closure law needs nothing more than a saturated result, because the
driver returns `Saturated` only after a clean naive round.

```coq
  (** A scheduler without a limit changes nothing. *)
  Parameter run_with_off : forall p cp lim sc db, match_limit sc = None ->
    run_with p cp lim sc db = run p cp lim db.
  Parameter run_with_wf : forall p cp lim sc db, plans_ok p cp -> D.wf db -> loaded p cp db ->
    D.wf (snd (run_with p cp lim sc db)) /\ D.canonical (snd (run_with p cp lim sc db)) /\
    loaded p cp (snd (run_with p cp lim sc db)).
  Parameter run_with_grows : forall p cp lim sc db, plans_ok p cp -> D.wf db -> loaded p cp db ->
    grows db (snd (run_with p cp lim sc db)).
  Parameter run_with_sat : forall p cp lim sc db (M : model (V := V.t)) nu,
    plans_ok p cp -> D.wf db -> loaded p cp db -> valid_sorted V.prim V.merge M p ->
    sat V.merge M nu (D.view db) -> exists nu',
      (forall i, D.allocated db i -> nu' i = nu i) /\
      sat V.merge M nu' (D.view (snd (run_with p cp lim sc db))).
  (** Saturation under backoff still establishes every rule's closure obligation. *)
  Parameter run_with_closed : forall p cp lim sc db db', plans_ok p cp -> D.wf db ->
    loaded p cp db -> run_with p cp lim sc db = (Saturated, db') ->
    closed V.prim V.merge p (D.view db').
  Parameter run_with_derives : forall p cp lim sc db f k o, plans_ok p cp -> D.wf db ->
    loaded p cp db -> relational_fragment p = true -> no_ids db ->
    row (D.view (snd (run_with p cp lim sc db))) f k o -> derives V.prim p (D.view db) f k.
  Parameter run_with_least : forall p cp lim sc db db', plans_ok p cp -> D.wf db ->
    loaded p cp db -> relational_fragment p = true -> no_ids db ->
    run_with p cp lim sc db = (Saturated, db') ->
    forall w, closed V.prim V.merge p w -> includes (D.view db) w ->
      (forall f, kind w f = program_kind p f) -> view_sorted (program_sorts p) w ->
      includes (D.view db') w.
  Parameter run_with_limits : forall p cp lim sc db, plans_ok p cp -> D.wf db ->
    loaded p cp db -> fst (run_with p cp lim sc db) = IdLimit ->
    (D.ids (snd (run_with p cp lim sc db)) > max_ids lim)%N.
```

Proofs. `run_with_off` is the simulation of section 2.2. The other seven are the proofs of
`run_wf`, `run_grows`, `run_sat`, `run_closed`, `run_derives`, `run_least` and `run_limits`, with
two changes. The helpers behind the round lemmas (`run_apply_jobs_state`,
`run_apply_jobs_grows`, `run_apply_jobs_sat`, `run_apply_jobs_progress`,
`run_apply_jobs_derives`, `run_apply_jobs_quiet`) already take any job list whose jobs satisfy
`run_job_facts` for the matched database. The kept jobs of `round_with` are such a list, because
each is a job of `jobs p cp true db` or of `jobs p cp false db` (`run_jobs_facts`).
`run_with_closed` uses the one fact that sets the scheduler apart. A clean naive round is the
plain naive round, so `naive_quiet_closed` applies to it.

### 3.4 B4, in `RUN_PLAN`, after `run_unfolds_loop`

`RUN_PLAN` takes `RUN_T` as a parameter, so `herbrand`, `run_with` and `trace_with` (B5, in
`RUN_TIME`) are in scope. The driver sits in `RUN_PLAN`, as `driver` does.

```coq
  Parameter driver_with : program V.t -> compiled V.t -> limits -> sched ->
    (mode * D.t) -> (mode * D.t) + (stop * D.t).
  (** The binary loop of the backoff driver, and the final rebuild. *)
  Parameter run_with_unfolds_loop : forall p cp lim sc db, plans_ok p cp -> D.wf db ->
    loaded p cp db ->
    match loopN (driver_with p cp lim sc) (max_iter lim) (fresh_mode p, db) with
    | inl (_, db') => run_with p cp lim sc db = (IterLimit, D.rebuild db')
    | inr (st, db') => run_with p cp lim sc db = (st, D.rebuild db')
    end.
  Parameter trace_with_spec : forall p cp lim sc db,
    trace_with p cp lim sc db =
      driver_trace (driver_with p cp lim sc) (N.to_nat (max_iter lim)) (fresh_mode p, db).
  (** A relational run that ends on its fuel had fuel for at most the Herbrand budget and the
      rounds that met a ban. Without a ban the bound is [2 * herbrand + 2], so the budget
      [2 * herbrand + 3] of [run_terminates] suffices. *)
  Parameter run_with_iterlimit_bound : forall p cp lim sc db, plans_ok p cp -> D.wf db ->
    loaded p cp db -> relational_fragment p = true -> prim_free p = true -> no_ids db ->
    fst (run_with p cp lim sc db) = IterLimit ->
    N.to_nat (max_iter lim) <=
      2 * herbrand p db + 2 * unclean_rounds (trace_with p cp lim sc db) + 2.
```

The bound is true for the following reason. Let `F` be the fuel, so the run made `F` driver
calls. A changed round adds a row of the finite universe (`F9`, `F14`), so at most `H` rounds
changed. A quiet round that is not clean counts in `unclean_rounds`. A quiet clean round is
semi-naive, because a quiet clean naive round would have returned `Saturated`. It is followed by
a naive round, which is changed (at most `H`), or quiet and unclean (counted), or the last round.
So `F <= H + u + (H + u + 1) = 2H + 2u + 1`. The proof is the proof of `run_terminates` with the
unclean rounds counted separately, about 150 lines.

The old law `run_terminates` stays as it is and is the case `unclean_rounds = 0`. A direct bound
on the number of bans would need a bound on the number of matches of a rule by a function of
`herbrand`, which needs a counting lemma over `J.run` that no signature states. The bound above
asks the caller for nothing and reads the cost of backoff from the trace.

### 3.5 B5, in `RUN_TIME`, after `run_complexity` of ruling P1-G2 (R2)

The trace, the clock, the measures, the contract and the big-O field of `run_with` sit where
`trace`, `T_run`, `run_cost`, `T_run_le` and `run_complexity` sit. A time contract of a public
operation belongs to the time module type (`AGENTS.md`), and a client that sees `RUN_T` sees
them. For example, `SaturateT`, whose `E` is a `RUN_T`, can derive a clock for a caller of
`E.run_with` only if `E.T_run_with` is a field of `RUN_TIME`. `trace_with` is a parameter here,
as `trace` is, and `trace_with_spec` in `RUN_PLAN` fixes it.

```coq
  Parameter trace_with : program V.t -> compiled V.t -> limits -> sched -> D.t ->
    list (mode * D.t).
  (** The bookkeeping of one round. Each plan reads its rule's table entry, and each entry is
      read and written with binary counters. *)
  Definition sched_work (p : program V.t) (cp : compiled V.t) (sc : sched) (md : mode) : nat :=
    (length (naive V.t cp) + length (seminaive V.t cp) + 1) *
    (fold_right (fun s n => N.size_nat (now md) + N.size_nat (ban_length sc) +
        N.to_nat (strikes s) + N.size_nat (strikes s) + N.size_nat (until s) + 1 + n) 0
      (stats md) +
     match match_limit sc with Some l => N.size_nat l | None => 0 end + 1).
  (** The round work of a backoff round is the work of its mode, plus the naive plans of the
      stale rules when the mode is semi-naive, plus the bookkeeping. *)
  Definition round_work_with (p : program V.t) (cp : compiled V.t) (sc : sched) (md : mode)
      (db : D.t) : nat :=
    round_work p cp (naive_next md) db +
    (if naive_next md || negb (existsb stale (stats md)) then 0 else round_work p cp true db) +
    sched_work p cp sc md.
  Definition run_work_with (p : program V.t) (cp : compiled V.t) (lim : limits) (sc : sched)
      (db : D.t) : nat :=
    fold_right Nat.add 0 (map (fun st => round_work_with p cp sc (fst st) (snd st) + 1)
      (trace_with p cp lim sc db)) + D.pending db + 1.
  Definition run_cost_with (B : N) (U : nat) (p : program V.t) (cp : compiled V.t)
      (lim : limits) (sc : sched) (db : D.t) : N :=
    (N.of_nat U * N.of_nat ((N.to_nat (N.log2 B) + 1) * (wbits p + 1)) *
        N.of_nat (run_work_with p cp lim sc db) +
      N.of_nat (N.size_nat (max_iter lim) + 1) + N.of_nat U * D.potential B db)%N.
  Parameter T_run_with : program V.t -> compiled V.t -> limits -> sched -> D.t -> N.
  (** A backoff run pays its trace work at the identifier width, its fuel counter and its
      scaled initial credit. *)
  Parameter T_run_with_le : forall B U p cp lim sc db, plans_ok p cp -> D.wf db ->
    loaded p cp db -> (D.ids (snd (run_with p cp lim sc db)) <= B)%N ->
    D.unit (snd (run_with p cp lim sc db)) <= U ->
    (T_run_with p cp lim sc db <=
      c_run * N.of_nat U * N.of_nat ((N.to_nat (N.log2 B) + 1) * (wbits p + 1)) *
        (fold_right N.add 0 (map (fun st =>
          N.of_nat (round_work_with p cp sc (fst st) (snd st) + 1))
          (trace_with p cp lim sc db)) + N.of_nat (D.pending db + 1)) +
      c_run * N.of_nat (N.size_nat (max_iter lim) + 1) +
      N.of_nat U * D.potential B db)%N.
  Parameter run_with_complexity : bigO
    (fun x : N * nat * program V.t * compiled V.t * limits * sched * D.t =>
      let '(B, U, p, cp, lim, sc, db) := x in
      plans_ok p cp /\ D.wf db /\ loaded p cp db /\
      (D.ids (snd (run_with p cp lim sc db)) <= B)%N /\
      D.unit (snd (run_with p cp lim sc db)) <= U)
    (fun x => let '(B, U, p, cp, lim, sc, db) := x in run_cost_with B U p cp lim sc db)
    (fun x => let '(_, _, p, cp, lim, sc, db) := x in T_run_with p cp lim sc db).
```

The sheet adds `BigO` to the Argent import line if ruling G2 has not done so.

Why `T_run_with_le` is true. The selected plans are a sublist of the naive list and the semi
list. The first summand of `round_work_with` pays the plans of the mode, the second pays the
catch-up naive plans, and `round_work_def` sums non-negative terms per plan, so a sublist costs
at most the sum. The kept jobs are a sublist of the jobs, so the amortised per-job argument of
`T_round_amort` (which sums `T_apply_amort` over the jobs, and needs only that each job is a
valid job of a loaded database) applies to the kept list.

The bookkeeping is the new work, and it splits into three parts.

- Per plan, the selection reads one table entry by a binary countdown. By `loopN_pred_credit`
  the countdown costs the entries that it passes plus the bits of the index. A checked plan's
  index is below `length (rules V.t p)` (`job_rule_spec`), which equals `length (stats md)` along
  a trace, because `fresh_mode` has that length and `next_stats` keeps it. So one lookup costs
  about `length (stats md)` steps, and `sched_work` charges that per plan.
- Per job, the code looks up its rule's entry twice, once to count the job and once to drop it
  when its rule exceeds. The counts are `nat`, so a count step costs a constant. The two lookups
  cost at most a constant times the `rule_work p c` that `round_work_def` charges per binding, by
  the same length equation. So `round_work` pays the per-job work. `sched_work` cannot pay it,
  because it has no database.
- Per entry, the counters `now`, `until` and `strikes` have at most
  `size now + size ban + strikes` bits, and the shift by `strikes` costs `N.to_nat strikes`.
  The test `L * 2^strikes < n` steps the count `n` and the cap down together, which costs `n`
  plus the bits of the cap, and the count is paid per job. `strikes` counts strike rounds, so it
  is at most the number of rounds so far, and `sched_work` charges it in full. Argent derives a
  clock for `N.shiftl` and proves no bound for it, so the session proves one first.

If the constant `c_run` does not fit, the session raises its value, as the rules of the cards
allow, and records the old and the new value.

Proof size of B5. About 250 lines, with `T_round_amort` as the model. The risk is the sublist form
of the job induction. `T_run_with_le` is the card BACKOFF2 and not BACKOFF.

### 3.6 B6, accepted, `SaturateSig.v`

The reviewer accepted B6 on 2026-11-16 (`DECISIONS.md`). It needs the card P1-EGRAPH
integrated, because `Saturate.v` is its file. In `SATURATE_OPS`, after `saturate` (`E` is a
`RUN_OPS`, so `E.run_with` is in scope).

```coq
  Parameter saturate_with : list decl -> list (rewrite V.t) -> list (rule V.t) -> limits ->
    sched -> list (fexpr V.t) -> reject + (stop * D.t * list positive).
```

In `SATURATE_LAWS`, after `saturate_limits`. A law belongs to the laws module type, and
`SATURATE_SPEC` holds definitions only.

```coq
  (** Without a limit the call is [saturate]. *)
  Parameter saturate_with_off : forall ds rws ans lim sc es, match_limit sc = None ->
    saturate_with ds rws ans lim sc es = saturate ds rws ans lim es.
```

In `SATURATE_PLAN`, after `saturate_run`. The field names `add_inputs`, which is a parameter
of `SATURATE_PLAN`, so it cannot sit in `SATURATE_SPEC` or `SATURATE_LAWS`.

```coq
  (** An accepted call runs the backoff engine with the planned program on the loaded inputs. *)
  Parameter saturate_with_run : forall ds rws ans lim sc es out,
    saturate_with ds rws ans lim sc es = inr out ->
    let p := C.compile ds rws ans in
    let cp := E.plan p in
    exists initial, front_ok ds rws ans es /\ E.plans_ok p cp /\ D.wf initial /\
      E.loaded p cp initial /\ add_inputs es (E.load p cp) = (snd out, initial) /\
      E.run_with p cp lim sc initial = fst out.
```

The code is `saturate` with `E.run_with p cp lim sc` in place of `E.run p cp lim`. The proofs
are `saturate_run` and a rewrite by `E.run_with_off`. No field names a clock of
`saturate_with`, so `SaturateT` needs no `TimeFun` for it. A client that sees `SATURATE_ALL` can
derive the closure theorems of a limited call from `saturate_with_run` and
`E.run_with_closed`. A client that sees only `SATURATE` learns nothing about a limited call
beyond `saturate_with_off` (section 9, item 4). `SaturateSig.v` joins the list of hashes to
update in `just/frozen.sha256`.

## 4. Planner changes P1 and P2

No signature statement changes. The checker `check_cplan` reads each plan on its own. It asks
for copies first, then any order of the other variables, for literals at fresh names, and for
slots that the table holds. So any variable order that the planner emits is accepted, and the
contracts `plan_checked`, `plan_passes_shape`, `T_check_plan_le` and `size_compiled_spec` keep
their text. Semi-naive plans need only be sound (`plan_match_sound`), because the naive round
confirms completeness (`naive_plans_complete`), so a different order per plan is safe.

### 4.1 P1, literals first

The layout numbers copies `0 .. C-1`, then literals, then real variables. Today literals and
variables share one counter in order of first position. `place_terms` gets a second counter, the
layout gets two fields (`nl`, `ln`) for the literal count and the literal names, and the real
variables start at `base + L` where `L` is the number of literal positions of the query
(`query_lits`, like `query_copies`). The plan's names list is
`rev_append cn (rev_append ln (rev_append mn []))`. An atom whose literal is not at its first
position gets a new slot whose permutation puts the literal position first, for example
`Add(a, 0)` gets the slot `(Add, [1; 0; 2])` besides `(Add, [0; 1; 2])`.

### 4.2 P2, the delta atom first

The naive plan and every semi-naive plan share one layout today (`semi_plans`). After P2 the
semi-naive plan for the atom `k` has its own layout. It numbers the real variables of atom `k`
first, in position order, then the other variables in order of first occurrence. The code is a
function `number_terms` that registers the real variables of a term list in a layout before
`plan_atoms` runs, so `place_terms` finds them by its existing `Some j` branch. Copies keep
their query order, which the checker needs, and literals stay first by P1. For `k = 0` the layout
is the default one, so the first atom needs no extra slot. For `k >= 1` an atom whose variables
sit in another order needs a slot with the permutation that matches. Slots are shared through the
table of `add_slot`, so two plans that need the same permutation share it.

P2 applies to a rule with at most 32 function atoms. A rule with more keeps the shared layout of
`semi_plans` for all its semi-naive plans, and `semi_plans` stays in the code. Section 4.3
explains why the cap is needed for the cube.

### 4.3 Contracts that stay true

- `T_plan_le` (cube). One pass of the planner over a rule costs at most
  `16384 * rule_bits r * (cap + 1)^2` (`run_plan_rule_clock`), and the cubic part is real. A
  function atom of arity `a` with distinct variables numbered in position order costs about
  `a³/6` steps in `sort_pairs`, because each insertion walks the whole sorted list with `Nat.leb`
  on unary join indices. Without a cap, P2 makes `n + 1` passes for a rule of `n` function
  atoms. The rule `W(x1, ..., xa), U(x1), ..., U(x1)` with `n = a` unary atoms keeps the default
  numbering in every pass, so planning it costs about `a⁴/6` steps, while its text has about
  `a log a` bits. The ratio to the cube grows like `a / log³ a`, so `T_plan_le` would be false.
  The inequality `n * a <= Q` fails for this rule, because only the sum of the arities is below
  `Q`. With the cap of 32 function atoms a rule makes at most 33 passes, so its clock grows by at
  most a factor of 33 plus the linear cost of `number_terms`. `run_plan_program_clock` has the
  constant 65536 = 2^16, and `c_run` is at least 2^22, so `T_plan_le` keeps its text and
  `c_run` its value. A cap-free P2 needs an ordering of an atom's positions that costs at most
  the query size per position, so that a pass costs at most `Q^2`. That is a decision for the
  owner (section 9).
- `plan_slots_le`. Each pass adds at most one slot per atom, so the slots grow from
  `2 * (size + 1)` to at most `66 * (size + 1)`, below the cube for `c_run >= 66`.
- Clients. `Andersen.v` and `Steensgaard.v` bound the slots by `R.plan_slots_le` and the plan
  clock by `R.T_plan_le` through `k_rules = c_run * 512^3 + 1`. Their proofs use no fact about
  the layout beyond `check_plan_slots`, so they compile unchanged. The Andersen program
  (`Copy(x,y), Pts(y,z)` and the Load and Store rules) goes from 5 slots to 9 by hand count. The
  four new slots are `(2, [1; 0])`, `(3, [1; 0])`, `(5, [1; 0])` and `(4, [1; 0])`, from the
  pivot plans of the Copy rule, of the Load rule (twice) and of the Store rule. The card
  re-counts and reports. `Saturate.v` uses `plan_full_slots`, and the full slots stay first.

### 4.4 Dependence on R1

P1 does not depend on R1. P2 does. Before R1 a semi-naive round reads empty `New` indexes, so
its pivot order cannot matter. After R1 the `New` index holds the delta of the previous round,
and the pivot-first order lets that delta drive the join. B3 to B5 depend on R1 because
`round_with` applies its jobs to `D.advance db`, as `round` does after R1. The proof of
`run_with_closed` reads `round_eq_jobs` of R1 through `round_with_clean_naive`, and the down flag
of a naive state comes from the step of `driver_with`, as it comes from `driver_def` for
`driver`. The bound of B4 uses the progress argument of `round_changed_adds_row` without its flag
premise, which holds for `round_with` for the same reason. `round_with` does not call `round`.
It uses `jobs`, `keep`, `bind_trie` and `apply_all`, which P1-RUN keeps as the specification
even if its optional fused loop lands.

## 5. Consumers outside `Run.v`

| File | Change |
| --- | --- |
| `Clients/Andersen.v`, `Clients/Steensgaard.v` | none |
| `Egraph/Saturate.v`, `SaturateSig.v` | B6. A placeholder on `p1b/base`, the code and the proofs in card P1-BACKOFF2 |
| `tests/Egraph/SaturateTest.v` | one example of `saturate_with`, card P1-BACKOFF2 |
| `AndersenSig.v`, `SteensgaardSig.v` | none |
| `tests/Egglog/RunTest.v` | owned by the cards. P1 changes the expected plan of `filter_plan_layout` (line 226), and P2 that of `closure_plan` (lines 125 to 139). The alias examples of lines 300 to 420 build their plans by hand and keep their results. B adds examples. |
| `tests/Egglog/JoinTest.v` | none |
| `docs/design/engines.md` | the reviewer may add the scheduler to section 1.10 |

## 6. Gains, derived

- P1. A plan with a literal in a later position scans the first level of its atom, which has as
  many keys as the atom has distinct values at that level, say `r`. Then it probes the literal
  for each. After P1 it probes the literal once and enumerates the `m` matching rows. The join
  work for that atom falls from `Theta(r)` to `Theta(1 + m)` per round. The slot costs one more
  index to maintain per `put` into that relation.
- P2. A semi-naive plan for atom `k >= 1` scans the first level of atom 0 every round, which
  costs `Theta(|roots of atom 0|)` whatever the delta. After P2 it scans the roots of the delta
  of atom `k`. Over a run each row is a delta row once, so the sum of first-level work falls from
  `rounds * |atom 0|` to about `|relation of atom k|`. For Andersen `Copy(x,y), Pts(y,z)` with
  `Pts` as the delta this is `rounds * |Copy|` against `|Pts|`.
- B. A rule that explodes (associativity with commutativity) is evaluated at its strike rounds
  only, about `log(M / L)` times for a final match count `M`, and each strike round drops its
  apply and its rebuild work. A banned round pays nothing for that rule. The effect on a
  terminating program that never exceeds its limit is the bookkeeping of `sched_work` and nothing
  else.

## 7. What the reviewer lands on `p1b/base` before these cards run

1. Integrate P1-RUN. Its item 1 (the reorder) is required, because both B3 and P2 depend on it.
   Its item 2 (big-O fields) is expected. Its item 3 (the fused loop) may or may not land, and the
   cards work either way.
2. Integrate P1-EGRAPH, which B6 needs because `Saturate.v` is its file. Integrate P1-JOIN, P1-DB
   and P1-INDEX if they are ready. They are not required, because the cards need `JoinSig.v` as it
   is on `p1/base`.
3. Apply ruling G2X, sections 3.1 to 3.5, to `RunSig.v` and section 3.6 to `SaturateSig.v`. Add
   `saturate_with` to `SaturateCode` with a placeholder body marked `STUB-CODE`, and
   `Proof. Admitted. (* STUB *)` lemmas for `saturate_with_run` and `saturate_with_off` to
   `Saturate.v`. Add one `Proof. Admitted. (* STUB *)` lemma to `Run.v` for each new field. The list
   is `run_with`, `driver_with`, `trace_with` (definitions with a placeholder body marked
   `STUB-CODE`) and the lemmas `run_with_off`, `run_with_wf`, `run_with_grows`, `run_with_sat`,
   `run_with_closed`, `run_with_derives`, `run_with_least`, `run_with_limits`,
   `run_with_unfolds_loop`, `trace_with_spec`, `run_with_iterlimit_bound`, `T_run_with` (a clock
   derived by `TimeFun` once the body exists), `T_run_with_le` and `run_with_complexity`. The definitions
   of section 3 go in `RunSig.v` as written.
4. Compile `RunSig.v`, `Run.v`, `SaturateSig.v` and `Saturate.v`, update `just/frozen.sha256` for
   the changed signatures, and run `just session-check`.
5. Build the kit `galois-p1b.bundle` with the branch `p1b/base` and the file `RULINGS-P1B.md`
   (this ruling and the integrated parts of ruling G2). Fill `{P1B_BASE}` and `{KIT_SHA}`.
6. Run the planner cards first or the backoff cards first, as the owner prefers. They edit
   disjoint regions of `Run.v` (planner at lines 330 to 600, 2100 to 4600, 13500 and 14893 on
   the base, backoff at the round, the driver and lines 10400 to 13200 and 17700 to 20800), so
   textual conflicts are unlikely, but each card needs the previous one integrated, because the
   statements of `Run.v` must compile on the base the session starts from.
7. Record in `docs/sessions` that `run` is the unbanned engine and that `run_with` is the
   scheduled one.

## 8. Cards and order

| Order | Card | Content | Hours |
| --- | --- | --- | --- |
| 1 | `CARD-P1-PLAN.md` | P1, literals first | 6 |
| 2 | `CARD-P1-PLAN2.md` | P2, delta atom first | 6 |
| 3 | `CARD-P1-BACKOFF.md` | B2 and B3, B4 | 6 |
| 4 | `CARD-P1-BACKOFF2.md` | B5 and B6 | 5 to 6 |

Cards 1 to 4 each end with every proof closed or a field left `OPEN` under the rules of the
brief. Card 4 may precede card 2 or card 1, since each changes disjoint code, but not card 3.

## 9. Decisions

The reviewer decided items 1 to 5 on 2026-11-16 (`DECISIONS.md`). Items 6 and 7 are open.

1. Extra indexes. Accepted. P1 and P2 add slots, and each `put` into a relation pays one index
   update per slot of that relation. The cards report slot counts and `put` clocks before and
   after.
2. The default scheduler. `RunSig.v` gains `default_sched` with egg's values, a match limit of
   1000 and a ban length of 5 (B1). The cards test with small values and once with
   `default_sched`.
3. A match counts for the limit in the round that finds it, so a semi-naive round counts delta
   matches only, where egg counts all matches of an iteration. Accepted. The alternative was to
   count only in naive rounds, which makes the scheduler act late.
4. B6. Accepted, `saturate_with` is exposed now.
5. A capped join `J.run_upto`, so that a strike round stops its search at the limit. It changes
   `JoinSig.v` and about 40 lemmas of `Join.v`. Deferred.
6. The cap of P2 (section 4.3). P2 applies to rules with at most 32 function atoms, which keeps
   `T_plan_le` cubic. Lifting the cap needs a way to order the positions of an atom that costs at
   most the query size per position, for example placing each position at its join index in a
   list of the join width. That changes `plan_atoms` and its lemmas, about one more session.
7. A public law for a limited `saturate_with`. B6 gives a client of `SATURATE` only
   `saturate_with_off`. A law such as `saturated_closed` for `saturate_with` needs one more field
   in `SATURATE_LAWS`, proved like `saturated_closed` from `E.run_with_closed`.

## 10. Note on the base of each card

Each card starts from `p1b/base` as the reviewer rebuilds it after the previous card is
integrated. P1-PLAN2 needs P1-PLAN, and P1-BACKOFF2 needs P1-BACKOFF. Before each card the
reviewer applies nothing new to the signatures, because the sections of this ruling were applied
once. P1-PLAN and P1-PLAN2 have no `STUB` lemmas, so their kits carry no new signature text. Their
base still holds the `STUB` lemmas and `STUB-CODE` placeholders of sections 3.1 to 3.6, which
belong to the backoff cards, and their cards say to leave them alone. P1-BACKOFF2 starts only
after P1-EGRAPH is integrated, because it edits `Saturate.v`. If P1-BACKOFF leaves a law open,
the reviewer names it in the kit of P1-BACKOFF2, which takes it after its cut line.


# Ruling P1-G2: signature changes for the Egglog engine, e-graph and client cards

Base is `07f190c6`. This file covers the cards P1-RUN, P1-JOIN and P1-EGRAPH. The reviewer
applies each ruling below to the signature and adds a `Proof. Admitted. (* STUB *)` lemma to the
owning implementation on `p1/base`. Nothing here is built. Every Rocq text was written against
the signatures at the base and must be compiled once before the sessions start.

All new fields use `bigO` from Argent. Each signature that gains a field adds `BigO` to its
`From Argent Require Import` line. `CompileSig.v` has no Argent import yet, so it gains
`From Argent Require Import BigO.`

## 0. Summary

| ID | File | Change | Kind | Verdict |
| --- | --- | --- | --- | --- |
| R1 | `RunSig.v` | Four statements change so that the round advances before it applies | speed | accept, the main gain of the batch |
| R2 | `RunSig.v` | Measures `load_cost`, `run_work`, `run_cost`, `round_cost` and five big-O fields | big-O | accept |
| J1 | `JoinSig.v` | Delete `T_run_ge` so that probes can stop at the first miss | speed | accept |
| J2 | `JoinSig.v` | One big-O field | big-O | accept |
| X1 | `ExtractSig.v` | Four big-O fields | big-O | accept |
| C1 | `CompileSig.v` | Two big-O fields | big-O | accept |
| S1 | `SaturateSig.v` | One measure and three big-O fields | big-O | accept |
| A1 | `AndersenSig.v` | Four big-O fields | big-O | accept |
| T1 | `SteensgaardSig.v` | Four big-O fields | big-O | accept |
| D1 | `JoinSig.v` and `Run.v` | Copy levels as equality levels | speed | dropped, reasons in section 9 |
| D2 | `Run.v` | Literal-first and pivot-first variable order | speed | accepted by the owner, text in ruling P1-G2X |
| D3 | `Saturate.v` | Per-rule match limit | behaviour | accepted by the owner, text in ruling P1-G2X |

The total is 23 big-O fields, 4 changed statements and 1 deleted field.

## 1. R1, the round advances before it applies (`RunSig.v`, module type `RUN_PLAN`)

### Why a ruling is needed

The driver calls `D.advance` on the result of a round. `advance` empties the new-row indexes, so
the next round reads empty `New` sources. Every semi-naive round after the first therefore finds
no binding, its changed flag stays down, the driver switches to a naive round, and every
productive iteration is a full naive round. The remedy is to read the jobs from the database
that carries the delta, to advance that database, and to apply the actions and the rebuild on the
advanced copy. The rows that the round writes then form the delta of the next round.

The new round is

```coq
round p cp nv db = D.rebuild (apply_all p (jobs p cp nv db) (D.advance db))
```

The jobs are computed from `db`, so the `New` sources still see the previous delta. The
database is persistent, so advancing it afterwards cannot disturb the jobs.

### The new driver order

1. Compute the jobs of the round from `db`. Plans read `All` and `New` indexes of `db`.
2. Advance `db`. The new indexes and the change flag are cleared.
3. Apply the actions of the jobs to the advanced database.
4. Rebuild. Rows that the rebuild repairs enter the new indexes as well.
5. Return the rebuilt database. The driver no longer advances.

The loop keeps its present shape. A quiet semi-naive round (`nv = false`) is followed by a naive
round. A quiet naive round returns `Saturated`. A productive naive round is followed by a
semi-naive round, which now reads the rows of the naive round. So a run costs the semi-naive
joins over the deltas plus one confirming naive round at the end.

### The four statements

Replace `driver_def`.

```coq
  (** The round advances the database before it applies, so its result carries the rows that
      the round changed as new rows. The driver passes that result on without advancing. *)
  Parameter driver_def : forall p cp lim nv db,
    driver p cp lim (nv, db) =
      let next := round p cp nv db in
      if N.ltb (max_ids lim) (D.ids next) then inr (IdLimit, next)
      else if andb nv (negb (D.changed next)) then inr (Saturated, next)
      else inl (negb (D.changed next), next).
```

Replace `round_eq_jobs`.

```coq
  (** A round reads its jobs from the starting database, applies them to its advanced copy
      in order and rebuilds once. *)
  Parameter round_eq_jobs : forall p cp nv db,
    round p cp nv db = D.rebuild (apply_jobs p (jobs p cp nv db) (D.advance db)).
```

Replace `round_changed_adds_row`. The premise `D.changed db = false` goes, because the new driver
passes on states whose flag is raised.

```coq
  (** A changed relational round adds a row absent from its starting view. *)
  Parameter round_changed_adds_row : forall p cp nv db, plans_ok p cp -> D.wf db -> loaded p cp db ->
    relational_fragment p = true -> no_ids db ->
    D.changed (round p cp nv db) = true ->
    exists f k, row (D.view (round p cp nv db)) f k None /\ ~ row (D.view db) f k None.
```

Replace the conclusion of `T_round_split` by this one. It names the advanced copy, and it adds
the clock of `D.advance`.

```coq
  Parameter T_round_split : forall p cp nv db, plans_ok p cp -> D.wf db ->
    loaded p cp db ->
    (T_round p cp nv db <=
      fold_right N.add 0 (map (fun c =>
        J.T_run (join V.t c) (map (source_index db) (sources V.t c)))
        (if nv then naive V.t cp else seminaive V.t cp)) +
      fold_right N.add 0 (map (fun c =>
        fold_right N.add 0 (map (fun b => T_bind_trie c b + T_keep p c (bind_trie c b))
          (bindings cp c db)))
        (if nv then naive V.t cp else seminaive V.t cp)) +
      T_apply_jobs p (jobs p cp nv db) (D.advance db) +
      D.T_rebuild (apply_jobs p (jobs p cp nv db) (D.advance db)) +
      D.T_advance db +
      k_driver * N.of_nat (round_work p cp nv db + 1) * N.of_nat (wbits p + 1))%N.
```

### Fields that stay as they are

- `naive_quiet_closed` keeps its premise `D.changed db = false`. A naive round runs only after
  a quiet semi-naive round. By `driver_def` that round returned a state with
  `negb (D.changed next) = true`, so the flag of the state is down. The proof of `run_closed`
  reads this from the step equation.
- `run_unfolds_loop`, `trace_spec`, `trace_is_chain` and `T_driver_loop_split` speak of `driver` only.
- `herbrand_round_le`, `new_rows_in_universe`, `round_monotone` and `round_leaves_idle` speak of
  `round` as a black box. The proofs go through `round_eq_jobs`.
- `T_driver_split` keeps its text. The driver no longer pays for `D.advance`, so the stated bound
  has slack of `k_driver * length slots`. The session may prove it with that slack.
- `T_round_amort` keeps its text. The new term `D.T_advance db` is at most
  `D.c_db * (num_slots + 1)` by `T_advance_le`. The term `length (slots cp)` of `round_work_def`
  and the constant `k_driver` (which contains `D.c_db`) cover it.
- `run_terminates` keeps `2 * herbrand p db + 3`. The new loop needs at most `2 * herbrand + 2`
  rounds, because the first round advances and clears the seed flag, so the old bound stays true.
  Its comment gives the raised seed flag as the reason for the extra round, which is false after
  R1. The reviewer replaces the comment, and only the comment, by this one.

```coq
  (** A relational run reaches saturation within its finite Herbrand budget. The budget has
      one round of slack, because each round advances its database before it applies. *)
```

- The four changed statements hold only for the new `round` and `driver`. The code change of
  card P1-RUN is therefore mandatory, and the card has no revert rule for it. A lemma that the
  session cannot close stays `OPEN` with the new code in place.

### Why the new text is true for the planned code

- `F21`. The new `driver` returns `next` instead of `D.advance next`. The check `D.ids next` is
  unchanged.
- `F32`. By definition of the new `round`.
- `F9`. By `D.wf_advance`, the advanced copy has the same view as `db`, is well formed, and has
  `changed = false`. The existing progress lemma for `apply_jobs` started from a database with a
  down flag, so it applies to the advanced copy. A raised final flag then gives a row of the
  applied database that the advanced copy lacks, and the views of `db` and its advanced copy are
  equal.
- `T1a`. The derived clock of the new `round` is the clock of the old one plus the clock of
  `D.advance db`, because `advance` is one more call. The other summands are those of the old
  proof with `db` replaced by `D.advance db` where they mention the applied database.

### Which proofs the session redoes

Most round lemmas already take two databases, one for the matches and one for the evolving
application (for example `run_apply_jobs_state p cp db js db'`). The change instantiates the
second one with `D.advance db` and transfers facts with `run_advance_state`,
`run_advance_canonical`, `run_advance_grows` and `run_no_ids_advance`, which exist. The list
that follows comes from a search at `07f190c6` for the lemmas of `Run.v` that name `D.advance`,
`driver_def` or `round_eq_jobs`, or unfold `driver`, `round` or `T_round`.
`advance_preserves_sorted` also names `D.advance` and keeps its proof.

| Lemma | Line at `07f190c6` | Work |
| --- | --- | --- |
| `driver_def`, `round_eq_jobs`, `jobs_def` | 10410, 10446, 10428 | restate, close by `reflexivity` or one rewrite |
| `run_round_state`, `run_round_canonical`, `run_round_grows_from`, `run_round_grows`, `run_round_sat` | 10995 to 11160 | instantiate with the advanced copy |
| `run_driver_database_invariant`, `run_driver_state_continue` | 11169, 11215 | the advance hypothesis goes |
| `run_loop_database_invariant`, `run_loop_state`, `run_domain_advance`, `run_trace_database_invariant` | 11237, 11259, 12651, 12882 | the advance hypothesis goes |
| `run_quiet_round_closed`, `round_monotone` | 12094, 15105 | apply on the advanced copy |
| `round_changed_adds_row`, `run_progress_initial` | 11675 | drop the premise, use `wf_advance` |
| `naive_quiet_closed`, `run_driver_closed_stop`, `run_closed` | 10914, 12116, 12135 | the quiet round is applied to the advanced copy |
| `run_sat`, `run_grows`, `run_wf`, `run_derives_state`, `run_round_derives`, `run_round_no_ids`, `run_round_domain`, `new_rows_in_universe` | 11778 to 12960 | trace states now carry the flag of the round that made them |
| `run_terminates` | 13136 | recount the rounds with the new step equation |
| `T_round_split`, `run_split_*` clock lemmas | 17722 to 18052 | one more summand |
| `T_driver_split`, `T_run_split`, `T_driver_loop_split` | 18094 to 18183 | drop the advance summand |
| `T_round_amort`, `run_round_*_cost` | 20164 to 20455 | add the `D.T_advance` term |
| `run_timing_loop_mono`, `run_timing_fuel_bounds`, `run_timing_driver_continue`, `run_timing_fuel_cost`, `run_run_from_round` | 20536 to 20775 | a continuing state is the round itself, not its advanced copy |

### Consumers outside `Run.v`

The four statements have one consumer outside `Run.v`. The module
`InitialFlagTerminationCounterexample` of `tests/Egglog/RunTest.v` (lines 526 to 692) refutes the
old budget `2 * herbrand + 2` for the old driver. Its lemmas `empty_round`, `first_driver_step`
and `second_driver_step` rewrite with `round_eq_jobs` and `driver_def`, so they stop
compiling as soon as the new text is applied. For example, `empty_round` is left with
`D.rebuild (D.advance db) = D.rebuild db`. Its `two_rounds_exhaust` becomes false once the
code changes, because the first round now clears the raised seed flag and `Limits 2 0`
saturates. The reviewer deletes the module, with its section comment at line 526, on
`p1/base`. Card P1-RUN adds the example of the new behaviour. No theory file and no other test
uses the four statements.

The estimate is 2 to 3 hours of proof work in one session, if the fused loop of work item 3 of the
card is done afterwards on the same lemmas. It does not fit beside the Join work, so the reorder
sits in P1-RUN and the Join work sits in P1-JOIN.

### Gain

A productive iteration pays the delta joins and one first-level scan per semi-naive plan, instead
of a full naive round and a wasted quiet semi-naive round. The ratio is between 3x and 100x on
propagation chains, as the notes estimate, but it has a floor. A semi-naive plan whose `New`
atom is not the first atom still scans the root level of the first atom (see D2). The Andersen
rule `Copy(x,y), Pts(y,z)` pays one scan over all `x` of `Copy` per round when `Pts` is the delta.
So the gain is large for rules that join several big relations (Load and Store of Andersen),
and small for two-atom rules over small deltas.

## 2. R2, big-O fields of `RunSig.v`

Add `BigO` to the Argent import line.

### Module type `RUN_TIME`, after `T_check_plan_le`

```coq
  (** Loading costs the initialisation of its declarations and slots. The measure is the right
      side of [D.T_init_le] without its constant. *)
  Definition load_cost (p : program V.t) (cp : compiled V.t) : N :=
    N.of_nat ((length (decls V.t p) + length (Syntax.slots V.t cp) +
        layout_work (Syntax.slots V.t cp) + 1) *
      (fold_right (fun s n => length (snd s) + n) 0 (Syntax.slots V.t cp) + 1) +
      (fold_right (fun d n => Pos.size_nat (name d) + n) 0 (decls V.t p) +
       fold_right (fun s n => Pos.size_nat (fst s) + n) 0 (Syntax.slots V.t cp)) + 1).
  (** The work of a run is the sum of the round work of its trace and the pending repairs. *)
  Definition run_work (p : program V.t) (cp : compiled V.t) (lim : limits) (db : D.t) : nat :=
    fold_right Nat.add 0 (map (fun st => round_work p cp (fst st) (snd st) + 1)
      (trace p cp lim db)) + D.pending db + 1.
  (** The cost of a run at identifier bound [B] and unit bound [U]. *)
  Definition run_cost (B : N) (U : nat) (p : program V.t) (cp : compiled V.t) (lim : limits)
      (db : D.t) : N :=
    (N.of_nat U * N.of_nat ((N.to_nat (N.log2 B) + 1) * (wbits p + 1)) *
        N.of_nat (run_work p cp lim db) +
      N.of_nat (N.size_nat (max_iter lim) + 1) + N.of_nat U * D.potential B db)%N.
  (** Planning is cubic in the program text, because sorting the positions of an atom
      compares unary join indices. *)
  Parameter plan_complexity : bigO (fun _ => True)
    (fun p => N.of_nat ((size_program p + 1) * (size_program p + 1) * (size_program p + 1)))
    T_plan.
  Parameter load_complexity : bigO (fun _ => True)
    (fun x : program V.t * compiled V.t => load_cost (fst x) (snd x))
    (fun x => T_load (fst x) (snd x)).
  Parameter check_plan_complexity : bigO (fun _ => True)
    (fun x : program V.t * compiled V.t =>
      N.of_nat ((size_program (fst x) + size_compiled (snd x) + 1) * (wbits (fst x) + 1)))
    (fun x => T_check_plan (fst x) (snd x)).
  (** A run costs its trace work at the identifier width, its fuel counter and its scaled
      initial credit. *)
  Parameter run_complexity : bigO
    (fun x : N * nat * program V.t * compiled V.t * limits * D.t =>
      let '(B, U, p, cp, lim, db) := x in
      plans_ok p cp /\ D.wf db /\ loaded p cp db /\
      (D.ids (snd (run p cp lim db)) <= B)%N /\ D.unit (snd (run p cp lim db)) <= U)
    (fun x => let '(B, U, p, cp, lim, db) := x in run_cost B U p cp lim db)
    (fun x => let '(_, _, p, cp, lim, db) := x in T_run p cp lim db).
```

### Module type `RUN_PLAN`, after `T_round_amort`

```coq
  (** The cost of one round at identifier bound [B] and unit bound [U]. *)
  Definition round_cost (B : N) (U : nat) (p : program V.t) (cp : compiled V.t) (nv : bool)
      (db : D.t) : N :=
    (N.of_nat U * N.of_nat ((N.to_nat (N.log2 B) + 1) * (wbits p + 1)) *
        N.of_nat (round_work p cp nv db + D.pending db + 1) +
      N.of_nat U * D.potential B db)%N.
  Parameter round_complexity : bigO
    (fun x : N * nat * program V.t * compiled V.t * bool * D.t =>
      let '(B, U, p, cp, nv, db) := x in
      plans_ok p cp /\ D.wf db /\ loaded p cp db /\
      (D.ids (round p cp nv db) <= B)%N /\ D.unit (round p cp nv db) <= U)
    (fun x => let '(B, U, p, cp, nv, db) := x in round_cost B U p cp nv db)
    (fun x => let '(_, _, p, cp, nv, db) := x in T_round p cp nv db).
```

The field sits in `RUN_PLAN` because `T_round_amort` is a `RUN_PLAN` field and the proof needs it.

### Why each is true and how it is proved

- `plan_complexity`. A corollary of `T_plan_le` with `c := c_run`. Use `bigO_intro`, `Nat2N.inj_mul`
  and one `nia` step. `sort_pairs` inserts into a sorted list with `Nat.leb` on unary join
  indices, which costs about a³/6 steps for one atom of arity a with distinct variables. Such an
  atom needs about a log a bits of text, so the cube is within a factor log³ of the worst case
  and is not tight. A lower class would need a binary comparison in the planner. The planner
  runs once per program, so the cube stays.
- `load_complexity`. From `T_load_le` and `D.T_init_le`. The constant is `c_run + D.c_db`. The measure
  `load_cost` is the sum of the two terms of `T_init_le` plus one, so
  `c_db * A * B + c_db * C <= c_db * (A * B + C + 1)`.
- `check_plan_complexity`. A corollary of `T_check_plan_le` with `c := c_run`.
- `run_complexity`. A corollary of `T_run_le` with `c := c_run + 1`. The sum
  `fold_right N.add 0 (map (fun start => N.of_nat (round_work ... + 1)) trace)` equals
  `N.of_nat` of the natural sum, by induction on the trace. `run_work` adds
  `pending + 1`, as the contract does. The bound is the engine's own accounting. It is not a
  closed form in the program and the database, because `JoinSig.v` has no bound of `J.work` by
  index sizes. After R1, `round_work` of a semi-naive round counts joins over the delta, so this
  measure is the delta-sized one.
- `round_complexity`. A corollary of `T_round_amort`. Drop the nonnegative potential term on the left,
  then use `c := c_run + 1`.

The session may leave `plan_complexity`, `check_plan_complexity` and `load_complexity` for last, because each is a
few lines.

## 3. J1, probes stop at the first miss (`JoinSig.v`, module type `JOIN_TIME`)

Delete this field.

```coq
  (** Recursive probe work is a lower bound on running time. *)
  Parameter T_run_ge : forall p ixs, wf_plan p ixs ->
    (N.of_nat (work p ixs) <= T_run p ixs)%N.
```

The lemma `T_run_ge` has no use outside `Join.v`. The note in `docs/sessions/B1-5.md` records
that this field forces `advance` to pass over every column. The code of `advance_columns` says
"both computations precede the result match" for the same reason. Removing the field lets
`advance_columns` return `None` at the first failing probe. A failing child then costs the probes
up to the first miss instead of all `length cols` probes. With two columns per level the saving
is up to half of the probe work of failing children. `work_at_step` keeps counting all probes, so
`work` stays an upper bound, and `T_go_le` and `T_run_le` keep their text. Only the lower bound
is lost, and nothing uses it for performance. The lines of `docs/design/engines.md` that list
`T_run_ge` become stale, and the reviewer may leave them as design history.

Proof size. The pure functions are unchanged as functions, so `advance_columns_preserves`,
`advance_columns_complete` and `advance_columns_probe` need one more case split each. The clock
lemmas `T_advance_columns_ge`, `T_advance_nodes_ge` and the `_ge` family for `go` go. The upper
bounds `T_advance_columns_budget` and `T_advance_columns_le` need the early exit in the
induction. About 150 lines.

## 4. J2, big-O of the join (`JoinSig.v`, module type `JOIN_TIME`, after `T_run_le`)

```coq
  (** A join costs its recursive probe work at the maximum index width. The factor of the
      variable count comes from unary level tests inside each probe. *)
  Parameter run_complexity : bigO (fun x : jplan * list I.t => wf_plan (fst x) (snd x))
    (fun x => N.of_nat ((work (fst x) (snd x) + length (snd x) + 2) *
      (wmax (fst x) (snd x) + 1) * ((nvars (fst x) + 1) * (nvars (fst x) + 1))))
    (fun x => T_run (fst x) (snd x)).
```

A corollary of `T_run_le` with `c := c_join`. Use `bigO_intro`, `Nat2N.inj_mul` and `nia`.

The factor `(nvars + 1)^2` is real. Each probe tests `existsb (Nat.eqb lvl) lv` on unary levels,
which costs `|lv| * lvl` and both are at most `nvars`. Hoisting that test out of the child loop
(work item 3 of P1-JOIN) lowers the constant and not the class, because the test still runs once
per node. So the field keeps the contract's shape on purpose.

## 5. X1, big-O of extraction (`ExtractSig.v`, module type `EXTRACT_TIME`, after `T_extract_le`)

```coq
  Parameter inventory_complexity : bigO (fun _ => True)
    (fun x : list decl * list (positive * list nat) =>
      N.of_nat ((layout_bits (fst x) (snd x) + 1) * (Nat.log2 (length (snd x)) + 1)))
    (fun x => T_inventory (fst x) (snd x)).
  (** Best rows cost the inventory, the incidences and the heap, at the database unit. *)
  Parameter best_complexity : bigO
    (fun x : list (positive * (N * nat)) * D.t =>
      D.wf (snd x) /\ D.canonical (snd x) /\ ctor_inventory (fst x) (snd x))
    (fun x => N.of_nat ((inventory_bits (fst x) + (R (snd x) + 1) * (a (snd x) + 1) +
      (R (snd x) + 1) * (Nat.log2 (R (snd x)) + 1)) * (D.unit (snd x) + 1) *
      (cost_width (snd x) + 1)))
    (fun x => T_best (fst x) (snd x)).
  Parameter check_dag_complexity : bigO
    (fun x : D.t * positive * extraction_dag V.t => D.wf (fst (fst x)))
    (fun x => let '(db, c, g) := x in
      N.of_nat ((cert_size V.encode g + Pos.size_nat c + 1) * (D.unit db + 1) *
        (match check_dag db c g with Some n => N.size_nat n | None => 0 end + 1)))
    (fun x => let '(db, c, g) := x in T_check_dag db c g).
  Parameter extract_complexity : bigO
    (fun x : list (positive * (N * nat)) * D.t * positive =>
      let '(cs, db, _) := x in D.wf db /\ D.canonical db /\ ctor_inventory cs db)
    (fun x => let '(cs, db, _) := x in
      N.of_nat ((inventory_bits cs + 2 * ((R db + 1) * (a db + 1)) +
        (R db + 1) * (Nat.log2 (R db) + 1)) * (D.unit db + 1) * (cost_width db + 1)))
    (fun x => let '(cs, db, c) := x in T_extract cs db c).
```

All four are corollaries of the contract of the same name, with `c := c_ex`. For
`extract_complexity` add `T_best_le` and `T_extract_le`, then bound the sum by the doubled
`(R + 1) * (a + 1)` term. The contracts are already near linear in the rows (`R log R` for the
heap and `R * a` for the incidences), so no tighter class exists.

## 6. C1, big-O of compilation (`CompileSig.v`)

In `COMPILE_TIME`, after `compile_rule_bits`.

```coq
  Parameter compile_complexity : bigO (fun _ => True)
    (fun x : list decl * list (rewrite V.t) * list (rule V.t) =>
      let '(_, rws, ans) := x in
      N.of_nat (fold_right (fun rw n => (rewrite_size rw + n)%nat) 0 rws + length ans + 1))
    (fun x => let '(ds, rws, ans) := x in T_compile ds rws ans).
```

In `COMPILE_PLAN`, after `T_compile_rule_le`.

```coq
  Parameter compile_rule_complexity : bigO (fun _ => True)
    (fun rw => N.of_nat (rewrite_size rw + 1)) T_compile_rule.
```

Corollaries of `T_compile_le` with `c := c_compile` and of `T_compile_rule_le` with
`c := k_compile`. Compilation is linear in the rewrites, as the contract says.

## 7. S1, big-O of saturation (`SaturateSig.v`, module type `SATURATE_TIME`, after `T_saturate_le`)

```coq
  (** The cost of saturation on accepted input, at identifier bound [B] and unit bound [U]. *)
  Definition saturate_cost (B : N) (U : nat) (ds : list decl) (rws : list (rewrite V.t))
      (ans : list (rule V.t)) (lim : limits) (es : list (fexpr V.t)) : N :=
    let p := C.compile ds rws ans in
    let cp := E.plan p in
    let db0 := E.load p cp in
    (N.of_nat (front_size ds rws ans es + 1) +
      N.of_nat ((E.size_program p + 1) * (E.size_program p + 1) * (E.size_program p + 1)) +
      E.load_cost p cp +
      N.of_nat U * N.of_nat (N.to_nat (N.log2 B) + 1) * N.of_nat (D.num_slots db0 + 1) *
        N.of_nat (fold_right (fun e n => (expr_work e + 1 + n)%nat) 1%nat es) +
      E.run_cost B U p cp lim (inputs_db es db0))%N.
  Parameter check_front_complexity : bigO (fun _ => True)
    (fun x : list decl * list (rewrite V.t) * list (rule V.t) * list (fexpr V.t) =>
      let '(ds, rws, ans, es) := x in N.of_nat (front_size ds rws ans es + 1))
    (fun x => let '(ds, rws, ans, es) := x in T_check_front ds rws ans es).
  (** Adding an input costs its nodes at the identifier width, and its scaled credit. *)
  Parameter add_expr_complexity : bigO
    (fun x : N * nat * list decl * fexpr V.t * D.t =>
      let '(B, U, ds, e, db) := x in
      D.wf db /\ expr_ok ds db e /\ (D.ids (snd (add_expr e db)) <= B)%N /\
      D.unit (snd (add_expr e db)) <= U)
    (fun x => let '(B, U, _, e, db) := x in
      (N.of_nat U * N.of_nat (N.to_nat (N.log2 B) + 1) * N.of_nat (D.num_slots db + 1) *
        N.of_nat (expr_work e) + N.of_nat U * D.potential B db)%N)
    (fun x => let '(_, _, _, e, db) := x in T_add_expr e db).
  Parameter saturate_complexity : bigO
    (fun x : N * nat * list decl * list (rewrite V.t) * list (rule V.t) * limits *
        list (fexpr V.t) =>
      let '(B, U, ds, rws, ans, lim, es) := x in
      let p := C.compile ds rws ans in
      let cp := E.plan p in
      let db0 := E.load p cp in
      front_ok ds rws ans es /\
      (D.ids (inputs_db es db0) <= B)%N /\ D.unit (inputs_db es db0) <= U /\
      (D.ids (snd (E.run p cp lim (inputs_db es db0))) <= B)%N /\
      D.unit (snd (E.run p cp lim (inputs_db es db0))) <= U)
    (fun x => let '(B, U, ds, rws, ans, lim, es) := x in saturate_cost B U ds rws ans lim es)
    (fun x => let '(_, _, ds, rws, ans, lim, es) := x in T_saturate ds rws ans lim es).
```

Notes on the proofs.

- `check_front_complexity` is `T_check_front_le` with `c := c_sat`.
- `add_expr_complexity` is `T_add_expr_amort` with `c := c_sat + 1`. Drop the nonnegative left potential
  term, and keep the right potential term, as in `run_complexity`.
- `saturate_complexity` composes `T_saturate_le` with these facts. `front_ok` gives
  `check_front = None` by `check_front_spec`, so the second branch of `T_saturate_le` applies.
  `T_compile_le` gives `c_compile * (sum of rewrite sizes + length ans + 1)`, and that is at most
  `front_size + 1` times a constant, because each rule has at least one bit. `T_plan_le` gives the
  cube. `load_complexity` gives `load_cost`. `T_inputs_le` gives the inputs term, and it also bounds
  `U * D.potential B (inputs_db es db0)`. `T_run_le` through `run_complexity` needs `plans_ok`, which
  comes from `compile_sorted` (via `front_ok`) and `plan_checked`, and it needs `wf` and `loaded`
  of `inputs_db es db0`, which `inputs_loaded` gives. The constant is
  `c_sat * (c_sat + c_run + c_compile + D.c_db + 1)`.
- The session closes `check_front_complexity` and `add_expr_complexity` first. `saturate_complexity` is the longest
  and may be the last lemma of the card.

## 8. A1 and T1, big-O of the clients (`AndersenSig.v`, `SteensgaardSig.v`)

In `ANDERSEN_TIME`, after `T_solve_le`. Add `BigO` to the import line. The Steensgaard text is the
same with `c_steensgaard`, `steensgaard_program`, and `8 * D.unit db` in place of `3 * D.unit db`
in `points_complexity`.

```coq
  Parameter seed_complexity : bigO (fun _ => True)
    (fun q => N.of_nat ((length (constraints q) + length (initial_pointers q) + 1) *
      D.unit (seed q) * (N.to_nat (N.log2 (D.ids (seed q))) + 1)))
    T_seed.
  (** Compilation emits a fixed program, so its cost is a constant. *)
  Parameter compile_complexity : bigO (fun _ => True) (fun _ => 0%N) T_compile.
  Parameter points_complexity : bigO (fun z : D.t * positive * positive => D.wf (fst (fst z)))
    (fun z => let '(db, x, a) := z in
      N.of_nat (3 * D.unit db + cell_bits V.encode (Val x) + cell_bits V.encode (Val a) + 1))
    (fun z => let '(db, x, a) := z in T_points db x a).
  (** A solve costs its seed, the cube of the fixed program for planning, and the run. *)
  Parameter solve_complexity : bigO
    (fun x : N * nat * pointer_input * limits =>
      let '(B, U, q, lim) := x in
      (D.ids (snd (solve q lim)) <= B)%N /\ D.unit (snd (solve q lim)) <= U)
    (fun x => let '(B, U, q, lim) := x in
      (N.of_nat ((length (constraints q) + length (initial_pointers q) + 1) *
        D.unit (seed q) * (N.to_nat (N.log2 (D.ids (seed q))) + 1)) +
      N.of_nat ((R.size_program (compile q) + 1) * (R.size_program (compile q) + 1) *
        (R.size_program (compile q) + 1)) +
      R.run_cost B U (compile q) (R.plan (compile q)) lim (seed q))%N)
    (fun x => let '(_, _, q, lim) := x in T_solve q lim).
```

Proofs. `seed_complexity`, `compile_complexity` and `points_complexity` are corollaries of `T_seed_le`,
`T_compile_le` and `T_points_le` with the constant of the client. `solve_complexity` combines
`T_solve_le` with `T_seed_le`, `T_plan_le`, and `R.run_complexity` at `p := compile q`. The premises of
`run_complexity` come from `solve_run` (the run is on `seed q`), `seed_wf`, `seed_loaded` and
`program_sorted` followed by `R.plan_checked`. The cost of the run is the engine's trace work.
A closed form such as cubic in the variable count needs a bound of `J.work` by index sizes, which
no signature states. That is left for a later batch and is not a card item.

## 9. Dropped and deferred items

### D1, copy levels as equality levels. Dropped.

The note says the planner puts copy levels after their variables. The code puts them first. The
layout in `var_layout` numbers copies from 0, and `layout_fresh` requires them first. So only
literal levels come late. A copy level still enumerates every value of the later position
before the variable it must equal is bound, and the equality is tested in the post filter.
`R(x, x)` therefore scans all rows of `R`. A join with equality levels needs
`wf_plan` to allow repeated variables in one column (it demands `StronglySorted lt`), a second
probe of the same index at one level in `advance_columns`, a change of `nodes_ok` (it filters
the column by level), and a new planner and checker. That touches `JoinSig.v`, `Join.v`,
and about 40 lemmas of the planner and checker. The gain applies only to atoms that repeat a
variable, and neither client has one. Drop it.

### D2, literal-first and pivot-first variable order. Accepted, see ruling P1-G2X.

The owner accepted D2 and D3 on 2026-11-16. Ruling P1-G2X holds their exact text and supersedes
the two sketches below, which stay as the record of the first estimate.

Both are planner changes in `Run.v` (`place_terms`, `plan_atoms`, `plan_rule`).

- Literal-first. `place_terms` gives a literal `j := base + nm` in position order. `Add(a, 0)`
  opens at `a` and scans every `a` of `Add` before the literal probe. Opening at the literal
  turns the scan into one probe. The checker already accepts it, because `layout_literals` takes
  literal columns at any fresh index. The change is `place_terms` (a literal counter and a
  variable counter offset by the literal total of the query) and the planner lemmas that mention
  `j` and the order of `vars`.
- Pivot-first. A semi-naive plan with the new atom at position k should open with the variables
  of that atom, so that the delta, and not the first atom, drives the join. It needs one layout
  per semi-naive plan, so the slots multiply (up to one extra slot per atom), and each extra
  slot is one more index to maintain on every `put`. That trade must be measured.

The planner has 124 lemmas over a shared layout (`planner_place_*`, `planner_layout_*`,
`run_place_terms_*` and the clock family from line 13508). I estimate two full sessions for the
pair, with the risk concentrated in the clock lemmas. The gain is the largest one left after R1
for rules with literals and for rules whose first atom is large. The reviewer should decide
whether to open a P2 card for it. The statements of `RunSig.v` do not fix the order, so no
ruling is needed.

### D3, per-rule match limit (backoff scheduler). Accepted, see ruling P1-G2X.

This changes behaviour, so it is listed and not scheduled. It would take the following.

- `limits` gains a per-rule match limit and a ban length, in `Egglog/Syntax.v`, which is frozen.
- `round` gains a ban state, and `driver` threads it. A rule whose matches exceed its limit is
  skipped for some rounds and its limit doubles, as in egg.
- `Saturated` may be reported only after a round with no banned rule, so `F8` needs the premise
  that no rule is banned, and `run_terminates` needs a bound that includes the ban rounds.
- `naive_plans_complete` stays true, because a naive round that bans nothing is still complete.
  `F9`, `F12` and `F14` stay true. `run_closed`, `run_least` and `saturate_closed` keep their
  conclusions but need the unbanned final round in their proofs.
- Size. About 600 lines of change in `Run.v`, one change to a frozen file, and statement changes
  in `RunSig.v` and `SaturateSig.v`. One session after R1 is merged, since both rewrite the driver.
- Effect. Runs of explosive rules such as associativity and commutativity stop earlier with
  `IterLimit`. Results that the present code reaches with `Saturated` are unchanged when no limit
  fires. The owner decides whether the library wants that policy.

### Other items checked and dropped

- Item 11, the two-list table with `nth_error` (`Saturate.v`, `table_get`). Child indices are
  unary `nat` in the frozen `Egraph/Syntax.v`, and `enode_work` and `expr_work` already charge
  `j + 1` per child. The cost is linear in that measure. The table is optimal for recent
  references and costs the distance for far ones. A binary index needs a change in the frozen
  syntax. Dropped, with no speed card item.
- Extraction recomputes `best` on every `extract` call, and the certificate it returns holds the
  whole table. No code outside `tests/Egglog/ExtractTest.v` calls `extract`, so there is no
  caller to speed up. An `extract_with` that shares `best` would change `ExtractSig.v`. Dropped.
- `Join.v` per-level participation tables. They lower the constant by the length of a column and
  not the class. This is work item 3 of P1-JOIN, behind the cut line, and needs no ruling.
