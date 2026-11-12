# Galois abstract domains: design document

This document covers value domains, states, relational domains, widening control, alarms, Float and the work split. I read the Argent design (sections 0, 2, 4, 5 and 7), `theories/Domains` (64 files) and `theories/Lattice` in `galois-integrate`, the earlier designs, and the legacy `Float`. I checked the snippets marked "checked" in the REPL. Nothing else was compiled.

## 0. Findings that change the brief

1. **The Flocq dependency conflicts with "No axioms" (checked).** In the Rocq 9.3 environment, `Print Assumptions` on Flocq's `Bplus` (the function itself, not only `Bplus_correct`) lists four axioms:
   - `ClassicalDedekindReals.sig_not_dec`
   - `ClassicalDedekindReals.sig_forall_dec`
   - `functional_extensionality_dep`
   - `Classical_Prop.classic`

   Anything in `Float` that mentions a Flocq operation therefore depends on these axioms.

   By contrast, Stdlib's `SpecFloat.SFadd` is "Closed under the global context", and so is `QArith`'s `Qred_correct`.

   The owner must choose:
   - (a) an axiom exception scoped to the `Float` package, which is what the earlier design did; or
   - (b) postpone Float. See section 6.
2. **Today's harness and `Env` store closures, which `TimeFun` rejects.**
   - The harness table `Transfer.table` (`DomainsTransfer.v:17`) stores closures in its fields (`fwd : K -> nat -> option (R -> list A -> B)`).
   - `DomainsEnv.refine_c` returns `X -> Cost.t A`.

   Both are rewritten below as first-order functor parameters and data. The harness is checked in the REPL in section 1.3.
3. **Signed bounds should go.** `DomainsSignedBounds*`, `DomainsSignedOrder` and `DomainsSignedWiden` are 13 files and about 4.9k lines. Their role is already covered by two published results:
   - Wrapped intervals are signedness-agnostic (Navas et al. 2012; Gange et al. 2015).
   - The eBPF-style "bounds plus tnum" pairing is a reduced product (Vishwanathan et al. 2022, 2023).

   I replace the files with `Reduced(Wrapped, KnownBits)` and a reducer of about 300 lines.
4. **Requests to Argent and core:**
   - **Z cost model.** Every bound depends on how the core prices `Z` primitives. I assume two `CostStd` contracts, with ℓ the bit length (`Z.size`):
     - `add`, `sub`, `compare`, `min`, `max`, `land`, `lor`, `lxor` and shifts by a small amount cost c·(ℓ+1);
     - `mul`, `div`, `modulo` and `gcd` cost c·(ℓ+1)².

     If the core prices Z operations as O(1), replace every (ℓ+1) and (ℓ+1)² factor below by 1.
   - **Recursion support.** `term` is nested through `list`, so its evaluators need `TimeFun` support for a local `fix` or for a mutual `fix`. Both are "specified" in Argent §2 but rejected by the prototype. This is a blocking risk; the fallback is a postfix encoding of terms (§2.1).

## 1. Value-domain library

### 1.0 Citations

| Topic | References |
|---|---|
| Framework, intervals, widening and narrowing | Cousot & Cousot, POPL 1977; Cousot & Cousot, "Comparing the Galois connection and widening/narrowing approaches", PLILP 1992; Miné, "Tutorial on static inference of numeric invariants by abstract interpretation", FnT PL 4(3–4), 2017 (reference text for the whole package) |
| Products | Cousot & Cousot, POPL 1979 (reduced product); Granger, "Improving the results of static analyses…", PLILP 1992 (local iterations); Cousot, Cousot & Mauborgne, FoSSaCS 2011 (reduce iteratively, never after widening) |
| Constants | Kildall, POPL 1973; Wegman & Zadeck, TOPLAS 1991 |
| Congruences | Granger, "Static analysis of arithmetical congruences", IJCM 1989; Granger, TAPSOFT 1991 |
| Known bits (tnums) | Vishwanathan, Shachnai, Narayana & Nagarakatte, "Sound, precise, and fast abstract interpretation with tristate numbers", CGO 2022 (add, sub and `tnum_mul`); Regehr & Duongsaa, LCTES 2006; Miné, WING 2012 (bit-level domains) |
| Wrapped intervals | Navas, Schachte, Søndergaard & Stuckey, APLAS 2012; Gange, Navas, Schachte, Søndergaard & Stuckey, TOPLAS 37(1), 2015 |
| eBPF bounds and tnum reduction | Vishwanathan, Shachnai, Narayana & Nagarakatte, "Verifying the verifier: eBPF range analysis verification", CAV 2023 |
| Threshold widening | Blanchet et al., PLDI 2003 (Astrée); Halbwachs, Proy & Roumanoff, FMSD 1997 ("widening up to", delayed widening); Lakhdar-Chaouch, Jeannet & Girault, ATVA 2011 |
| Backward refinement | Benhamou, Goualard, Granvilliers & Puget, "Revising hull and box consistency", ICLP 1999 (HC4-revise); Miné 2017, §4.5 |

### 1.1 Layout and the fate of the landed files

Package `theories/Domains/`.

| New file | Contents | Comes from |
|---|---|---|
| `LangSig.v` | `term` (top level), `eval_term`, `LANG`, `LANG_TIME` | `DomainsTerm.v` (definitions), `DomainsValue.v` (`ValueSem`) — **merge** |
| `ValueSig.v` | `VALUE_DOMAIN`, `VALUE_DOMAIN_TIME`, `RANGE_QUERY`, `RANGE_REFINE` | `DomainsValue.v` `value_laws`, `DomainsNumeric.v` `numeric_laws` — **merge** (or core-owned, see §1.2) |
| `HarnessSig.v`, `Harness.v` | `HARNESS_BASE`, `TABLE`, functor `Harness` | `DomainsTransfer.v`, `DomainsPoint.v` — **merge** |
| `WordSig.v`, `Tagged.v` | `WORD_PAYLOAD`, `WORD_TABLE`, functors `Tagged` and `TaggedTable` | `DomainsNumeric.v` (`word_domain`), `DomainsTagged.v`, word part of `DomainsTransfer.v` — **merge** |
| `BitsLang.v` | `BitsLang <: LANG` over `BitsOp` | `DomainsBitsValue.v` — **merge**; the `op_bridge` records become the `Translate` functor |
| `ZLang.v` | integer language for tests and relational domains | new |
| `Const.v` | flat constants, generic over `LANG` | `DomainsConst.v` — **convert** |
| `Sign.v` | sign flags, word payload | `DomainsSign.v` — **convert** |
| `Congruence.v` | congruences, word payload | `DomainsCongruence.v` — **convert** |
| `Thresholds.v` | balanced threshold tree | `DomainsThreshold.v` — **convert** |
| `Interval.v`, `IntervalOps.v`, `IntervalBack.v` | Z intervals; Z and word transfers | `DomainsBound`, `DomainsInterval`, `…IntervalArith`, `…Bitwise`, `…Compare`, `…Shift`, `…Signed`, `…Transfer`, `…Refine`, `…Back`, `…Rank` (11 files, ~3.1k lines) — **merge** |
| `KnownBits.v`, `KnownBitsOps.v`, `KnownBitsBack.v` | tnums | `DomainsTnum*` (9 files) and `DomainsKnownBits*` (3 files), ~3.9k lines — **merge**; `DomainsTnumCost.v` **goes** |
| `Wrapped.v`, `WrappedOps.v` | wrapped intervals | `DomainsWrapped*` (7 files, ~2.2k lines) — **merge** |
| `ProductSig.v`, `Product.v`, `Reduced.v` | `Product`, `REDUCER`, `Reduced` | `DomainsValueCombine.v` (product part), `LatticeReduced.v`, `LatticeProduct.v` — **merge** |
| `Reducers.v` | `WrappedBits`, `IntervalCongr` and `IntervalBits` reducers | the reduction ideas of `DomainsSignedBounds*`, rewritten |
| `Translate.v` | reuse a domain under a language morphism | `ValueAbs.rename`, `DomainsBitsValue.v` |
| — | **goes** | `DomainsSignedBounds*` (11 files), `DomainsSignedOrder.v`, `DomainsSignedWiden.v`; the value-level `ValueAbs.disjunctive` (replaced by the state-level `Disj`); `DomainsTactics.v` (replaced by a 30-line `gamma_auto` in `ValueSig.v`); `DomainsState.v` and `DomainsRelational.v` (replaced by core `STATE_DOMAIN` and `NUM_STATE`, §3) |
| `Memory/Footprint.v` | must-written byte ranges | `Memory/DomainsFootprint.v` — **convert after the batches**; nothing in this design needs it |

What carries over from `theories/Lattice/`:
- `LatticeEnv.v` (1.2k lines): its pointwise lemmas port into `States/Env.v`.
- `LatticeDisjunction.v` (632 lines): the coverage order, with Hoare order and cap, ports into `States/Disjunction.v`.
- `LatticeReduced.v`: the "descending reducer, unreduced widening" rule moves into `Reduced.v`.
- `LatticeFlat.v` goes into `Const.v`.
- `LatticeHeight.v`: its rank conventions become the `wrank` law (§4).
- `LatticePartition*` (equality partitions) is not in my area.

The proofs in the converted files are kept. The conversion removes `_c`, `Cost.value` and `autorewrite with galois_cost`, turns records into modules, and drops the `*_cost` theorems, which `TimeFun` contracts replace.

### 1.2 Signatures

Core owns `VALUE_DOMAIN`. Below are the exact fields I need; anything core omits must be added. The snippets use `From Stdlib Require Import ZArith List`.

```coq
(* LangSig.v -- definitions at top level *)
Inductive term (K X : Type) : Type :=
| Leaf (x : X)
| Node (k : K) (ts : list (term K X)).
Arguments Leaf {K X} x.  Arguments Node {K X} k ts.

Fixpoint sequence {C} (xs : list (option C)) : option (list C) := (* as today *).
Fixpoint eval_term {K X C} (ev : K -> list C -> option C) (st : X -> C) (t : term K X)
  : option C := (* as DomainsTerm.v:42 *).
Definition eval_terms {K X C} ev st (ts : list (term K X)) := sequence (map (eval_term ev st) ts).
Fixpoint tsize {K X} (t : term K X) : nat :=
  match t with Leaf _ => 1 | Node _ ts => S (list_sum (map tsize ts)) end.
Definition upd {X C} (eqb : X -> X -> bool) (st : X -> C) (x : X) (c : C) : X -> C :=
  fun y => if eqb y x then c else st y.             (* spec-only *)

Module Type LANG.
  Parameter op guard val : Type.
  Parameter eval : op -> list val -> option val.
  Parameter holds : guard -> list val -> Prop.
  Parameter literal : op -> option Z.               (* program constants, for threshold mining *)
End LANG.

Module Type LANG_TIME (Import L : LANG).
  (* spec: work *)
  Parameter work : op -> list val -> nat.
  Parameter T_eval : op -> list val -> nat.
  Parameter T_literal : op -> nat.
  Parameter c_lang : nat.
  Parameter T_eval_le : forall o vs, T_eval o vs <= c_lang * (work o vs + 1).
  Parameter T_literal_le : forall o, T_literal o <= c_lang.
End LANG_TIME.
```

```coq
(* ValueSig.v *)
Module Type VALUE_DOMAIN (L : LANG).
  Parameter t : Type.
  Parameter leb : t -> t -> bool.
  Parameter join meet : t -> t -> t.
  Parameter bot top : t.
  Parameter is_bot : t -> bool.
  Parameter gamma : t -> L.val -> Prop.             (* GAMMA *)
  Parameter forward  : L.op -> list t -> t.
  Parameter backward : L.op -> t -> list t -> list t.
  Parameter guard    : L.guard -> list t -> list t.
  (* LATTICE weak laws *)
  Parameter leb_refl  : forall a, leb a a = true.
  Parameter leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Parameter join_ub_l : forall a b, leb a (join a b) = true.
  Parameter join_ub_r : forall a b, leb b (join a b) = true.
  Parameter meet_lb_l : forall a b, leb (meet a b) a = true.
  (* GAMMA laws *)
  Parameter gamma_mono : forall a b c, leb a b = true -> gamma a c -> gamma b c.
  Parameter gamma_bot  : forall c, ~ gamma bot c.
  Parameter gamma_top  : forall c, gamma top c.
  Parameter gamma_meet : forall a b c, gamma a c -> gamma b c -> gamma (meet a b) c.
  Parameter is_bot_sound : forall a c, is_bot a = true -> ~ gamma a c.
  (* transfer laws *)
  Parameter forward_sound : forall o xs cs c,
    Forall2 gamma xs cs -> L.eval o cs = Some c -> gamma (forward o xs) c.
  Parameter backward_sound : forall o r xs cs c,
    Forall2 gamma xs cs -> L.eval o cs = Some c -> gamma r c ->
    Forall2 gamma (backward o r xs) cs.
  Parameter backward_refines : forall o r xs,
    Forall2 (fun y x => leb y x = true) (backward o r xs) xs.
  Parameter guard_sound : forall g xs cs,
    Forall2 gamma xs cs -> L.holds g cs -> Forall2 gamma (guard g xs) cs.
  Parameter guard_refines : forall g xs,
    Forall2 (fun y x => leb y x = true) (guard g xs) xs.
End VALUE_DOMAIN.

(* Core's widening extension, with the fields I need. [wparam] carries program data such as thresholds. *)
Module Type WIDENING (Import D : LATTICE).
  Parameter wparam : Type.
  Parameter widen : wparam -> t -> t -> t.
  Parameter narrow : t -> t -> t.
  Parameter widen_ub_l : forall p a b, leb a (widen p a b) = true.
  Parameter widen_ub_r : forall p a b, leb b (widen p a b) = true.
  Parameter widen_stable : forall p a b, leb b a = true -> widen p a b = a.
  (* spec: wrank *)
  Parameter wrank : wparam -> t -> nat.
  Parameter wrank_widen : forall p a b, is_bot a = false -> leb b a = false ->
    wrank p (widen p a b) < wrank p a.
  Parameter narrow_between : forall a b, leb b a = true ->
    leb b (narrow a b) = true /\ leb (narrow a b) a = true.
End WIDENING.

Module Type VALUE_DOMAIN_TIME (L : LANG) (Import D : VALUE_DOMAIN L).
  (* spec: size work gwork *)
  Parameter size : t -> nat.
  Parameter work : L.op -> list t -> nat.
  Parameter gwork : L.guard -> list t -> nat.
  Parameter T_leb T_join T_meet : t -> t -> nat.
  Parameter T_is_bot : t -> nat.
  Parameter T_forward : L.op -> list t -> nat.
  Parameter T_backward : L.op -> t -> list t -> nat.
  Parameter T_guard : L.guard -> list t -> nat.
  Parameter c_val : nat.
  Parameter T_leb_le  : forall a b, T_leb a b  <= c_val * (size a + size b + 1).
  Parameter T_join_le : forall a b, T_join a b <= c_val * (size a + size b + 1).
  Parameter T_meet_le : forall a b, T_meet a b <= c_val * (size a + size b + 1).
  Parameter T_is_bot_le : forall a, T_is_bot a <= c_val * (size a + 1).
  Parameter T_forward_le  : forall o xs,   T_forward o xs    <= c_val * (work o xs + 1).
  Parameter T_backward_le : forall o r xs, T_backward o r xs <= c_val * (work o xs + size r + 1).
  Parameter T_guard_le    : forall g xs,   T_guard g xs      <= c_val * (gwork g xs + 1).
End VALUE_DOMAIN_TIME.
(* Widening time, in each domain's own *_TIME:
   T_widen p a b <= c * (size a + size b + wsize p + 1), where [wsize] is a spec. *)

(* Queries used by alarms (§5) and by relational reduction (§3). N is a numeric view. *)
Module Type NUM_VIEW (L : LANG).  Parameter num : L.val -> Z.  End NUM_VIEW.
Inductive bnd := NegInf | Fin (z : Z) | PosInf.          (* top level; shared with Interval *)
Definition in_bnd (lo hi : bnd) (z : Z) : Prop := (* lo <= z <= hi *).
Module Type RANGE_QUERY (L : LANG) (N : NUM_VIEW L) (Import D : VALUE_DOMAIN L).
  Parameter range : t -> bnd * bnd.
  Parameter range_sound : forall a c, gamma a c -> in_bnd (fst (range a)) (snd (range a)) (N.num c).
End RANGE_QUERY.
Module Type RANGE_REFINE (L : LANG) (N : NUM_VIEW L) (Import D : VALUE_DOMAIN L).
  Parameter refine_range : bnd -> bnd -> t -> t.
  Parameter refine_range_sound : forall lo hi a c,
    gamma a c -> in_bnd lo hi (N.num c) -> gamma (refine_range lo hi a) c.
  Parameter refine_range_lower : forall lo hi a, leb (refine_range lo hi a) a = true.
End RANGE_REFINE.
```

Each component also has `*_PLAN` module types (decision 3). For converted domains the plan is the list of carried theorem names (§1.5). For new code the plans are written out below.

### 1.3 The transfer harness

Tables are functor parameters with first-order entries. "Not modelled" is `None`, not a stored closure. I checked this shape in the REPL: `Harness (L : LANG) (B : HBASE L) (T : TABLE L B)` with `points` and `forward` compiles.

```coq
(* HarnessSig.v *)
Module Type HARNESS_BASE (L : LANG).
  (* the lattice and GAMMA part of VALUE_DOMAIN: t leb join meet bot top is_bot gamma
     and their laws, as above *)
  Parameter point : t -> option L.val.          (* Some v when gamma a = {v} *)
  Parameter abst  : L.val -> t.                 (* best abstraction of one value *)
  Parameter point_sound : forall a v c, point a = Some v -> gamma a c -> c = v.
  Parameter abst_sound : forall v, gamma (abst v) v.
End HARNESS_BASE.

Module Type TABLE (L : LANG) (B : HARNESS_BASE L).
  Parameter fwd : L.op -> list B.t -> option B.t.
  Parameter bwd : L.op -> B.t -> list B.t -> option (list B.t).
  Parameter grd : L.guard -> list B.t -> option (list B.t).
  Parameter fwd_sound : forall o xs cs c r, fwd o xs = Some r ->
    Forall2 B.gamma xs cs -> L.eval o cs = Some c -> B.gamma r c.
  Parameter bwd_sound : forall o r xs ys cs c, bwd o r xs = Some ys ->
    Forall2 B.gamma xs cs -> L.eval o cs = Some c -> B.gamma r c -> Forall2 B.gamma ys cs.
  Parameter grd_sound : forall g xs ys cs, grd g xs = Some ys ->
    Forall2 B.gamma xs cs -> L.holds g cs -> Forall2 B.gamma ys cs.
End TABLE.
Module Type TABLE_TIME (L : LANG) (B : HARNESS_BASE L) (T : TABLE L B).
  (* spec: twork tgwork bsize *)
  Parameter bsize : B.t -> nat.
  Parameter twork : L.op -> list B.t -> nat.
  Parameter tgwork : L.guard -> list B.t -> nat.
  Parameter T_fwd : L.op -> list B.t -> nat.  Parameter T_bwd : L.op -> B.t -> list B.t -> nat.
  Parameter T_grd : L.guard -> list B.t -> nat.  Parameter T_point T_is_bot : B.t -> nat.
  Parameter T_abst : L.val -> nat.  Parameter T_meet : B.t -> B.t -> nat.
  Parameter c_tab : nat.
  Parameter T_fwd_le : forall o xs, T_fwd o xs <= c_tab * (twork o xs + 1).
  Parameter T_bwd_le : forall o r xs, T_bwd o r xs <= c_tab * (twork o xs + bsize r + 1).
  Parameter T_grd_le : forall g xs, T_grd g xs <= c_tab * (tgwork g xs + 1).
  Parameter T_point_le : forall a, T_point a <= c_tab * (bsize a + 1).
  Parameter T_is_bot_le : forall a, T_is_bot a <= c_tab * (bsize a + 1).
  Parameter T_meet_le : forall a b, T_meet a b <= c_tab * (bsize a + bsize b + 1).
  Parameter T_abst_le : forall v xs o cs, L.eval o cs = Some v -> Forall2 (fun x c => B.point x = Some c) xs cs ->
    T_abst v <= c_tab * (twork o xs + 1).
End TABLE_TIME.
```

```coq
(* Harness.v *)
Module Harness (L : LANG) (LT : LANG_TIME L) (B : HARNESS_BASE L) (T : TABLE L B)
  <: VALUE_DOMAIN L.
  Include B.   (* lattice part *)
  Fixpoint points (xs : list B.t) : option (list L.val) := (* checked *).
  Definition forward o xs :=
    if existsb B.is_bot xs then B.bot else
    match points xs with
    | Some cs => match L.eval o cs with Some c => B.abst c | None => B.bot end
    | None => match T.fwd o xs with Some r => r | None => B.top end
    end.
  Fixpoint meet_all (xs ys : list B.t) : list B.t :=
    match xs, ys with x :: xs, y :: ys => B.meet x y :: meet_all xs ys | _, _ => xs end.
  Definition backward o r xs :=
    match T.bwd o r xs with
    | Some ys => if Nat.eqb (length ys) (length xs) then meet_all xs ys else xs
    | None => xs end.
  Definition guard g xs := (* as backward, with T.grd *).
  TimeFun points. TimeFun forward. TimeFun meet_all. TimeFun backward. TimeFun guard.
End Harness.
```

The harness meets with the input itself. Tables therefore never prove refinement, which removes `table_refines` and `passume_refines`.

Plan (`HARNESS_PLAN`):

```coq
Parameter points_sound : forall xs cs vs, Forall2 B.gamma xs cs -> points xs = Some vs -> vs = cs.
Parameter no_bot : forall xs cs, Forall2 B.gamma xs cs -> existsb B.is_bot xs = false.
Parameter meet_all_sound : forall xs ys cs, length ys = length xs ->
  Forall2 B.gamma xs cs -> Forall2 B.gamma ys cs -> Forall2 B.gamma (meet_all xs ys) cs.
Parameter meet_all_refines : forall xs ys, Forall2 (fun y x => B.leb y x = true) (meet_all xs ys) xs.
(* forward_sound, backward_sound, backward_refines, guard_* then follow by case analysis. *)
Parameter T_points_le : forall xs, T_points xs <= c * (list_sum (map bsize xs) + length xs + 1).
Parameter T_forward_le' : forall o xs, T_forward o xs <=
  c * (list_sum (map bsize xs) + length xs + LT.work o (opt_vals xs) + twork o xs + 1).
```

The `VALUE_DOMAIN_TIME` instance takes `work o xs := Σ bsize + |xs| + LT.work o (opt_vals xs) + twork o xs`. Here `opt_vals` is a spec function giving the points, or `[]`.

- **Bound:** linear in the operands plus one concrete evaluation plus one table entry. It is tight, because a lower-bound witness exists in both branches.
- **Estimate:** 450 lines, 0.6 h.
- **Risk:** low.

### 1.4 Word lifting and the bit-vector language

```coq
(* BitsLang.v *)
Inductive bop := BConst (w : width) (z : Z) | BOp (o : BitsOp.op).
Inductive bguard := BTruth (b : bool).
Module BitsLang <: LANG.
  Definition op := bop.  Definition guard := bguard.  Definition val := word.
  Definition eval (o : op) (vs : list val) : option val :=
    match o, vs with BConst w z, [] => Some (w, wrap w z) | BOp o, _ => eval_op o vs | _, _ => None end.
  Definition holds (g : guard) (vs : list val) : Prop :=
    match g, vs with BTruth b, [v] => v = (1%positive, if b then 1 else 0) | _, _ => False end.
  Definition literal o := match o with BConst _ z => Some z | _ => None end.
End BitsLang.
Module BitsLangTime <: LANG_TIME BitsLang.
  Definition work (o : bop) (vs : list word) := (list_sum (map (fun v => Pos.to_nat (fst v)) vs) + 1) ^ 2.
  (* T_eval_le: case split over the 33 descriptors. Each runs O(1) Z operations on w-bit
     numbers, and clz/ctz/popcnt are O(w) loops of O(w) work. Tight at bvmul. *)
End BitsLangTime.

(* WordSig.v *)
Inductive tagged (P : Type) := TBot | TVal (w : width) (p : P) | TAny.   (* top level *)
Module Type WORD_PAYLOAD.
  Parameter p : Type.
  Parameter pleb : width -> p -> p -> bool.  Parameter pjoin pmeet : width -> p -> p -> p.
  Parameter pbot ptop : width -> p.          Parameter pis_bot : width -> p -> bool.
  Parameter pgamma : width -> p -> Z -> Prop.
  Parameter pconst : width -> Z -> p.        Parameter ppoint : width -> p -> option Z.
  (* laws, as word_laws (DomainsNumeric.v:94) restricted to the lattice: *)
  Parameter pgamma_mono : forall w a b z, pleb w a b = true -> pgamma w a z -> pgamma w b z.
  Parameter ptop_full : forall w z, is_word w z -> pgamma w (ptop w) z.
  Parameter pconst_sound : forall w z, pgamma w (pconst w z) (wrap w z).
  Parameter ppoint_sound : forall w a z v, ppoint w a = Some v -> pgamma w a z -> z = v.
  (* plus refl, trans, ub, lb, bot, meet and is_bot laws per width *)
End WORD_PAYLOAD.
Module Type WORD_TABLE (W : WORD_PAYLOAD).
  Parameter wfwd : BitsOp.op -> width -> list (width * W.p) -> option W.p.
  Parameter wbwd : BitsOp.op -> width -> W.p -> list (width * W.p) -> option (list W.p).
  Parameter wfwd_sound : forall o rw wps cs z r, wfwd o rw wps = Some r ->
    Forall2 (fun wp c => fst wp = fst c /\ W.pgamma (fst wp) (snd wp) (snd c)) wps cs ->
    eval_op o cs = Some (rw, z) -> W.pgamma rw r z.
  Parameter wbwd_sound : (* analogous to word_laws.passume_sound *).
End WORD_TABLE.

(* Tagged.v *)
Module Tagged (W : WORD_PAYLOAD) <: HARNESS_BASE BitsLang.
  Definition t := tagged W.p.
  Definition gamma (a : t) (c : word) : Prop :=
    match a with TBot => False | TAny => True
    | TVal w p => fst c = w /\ is_word w (snd c) /\ W.pgamma w p (snd c) end.
  (* joining different widths gives TAny, as DomainsTagged.v does today *)
End Tagged.
Module TaggedTable (W : WORD_PAYLOAD) (WT : WORD_TABLE W) <: TABLE BitsLang (Tagged W).
  (* untag every operand, compute rw := result_width o (map fst ws), call WT.wfwd or WT.wbwd,
     retag; any TAny operand or ill-typed width gives None *)
End TaggedTable.
Module WordDomain (W : WORD_PAYLOAD) (WT : WORD_TABLE W) :=
  Harness BitsLang BitsLangTime (Tagged W) (TaggedTable W WT).
```

- **Plan:** `untag_sound`, `retag_sound`, then `TaggedTable.fwd_sound` from `WT.wfwd_sound` and `eval_op_is_word` (this is `DomainsTransfer.v:358` `combine_backward`, moved here).
- **Estimates:** `Tagged`/`TaggedTable` 600 lines; `BitsLang` 350 lines; 1.2 h together.

### 1.5 The domains

`size (TVal w _) := Pos.to_nat w` for every word payload. The bounds use w = Pos.to_nat (result or operand width).

| Domain | Representation (top level) | Height or widening | Tight forward bound | Plan: carried lemmas, then new ones |
|---|---|---|---|---|
| `Const (L) (E : VAL_EQ L)` | `Inductive flat (A) := FBot \| FVal (a : A) \| FTop` | height 2, `widen := join`, `wrank := 2 - level` | `LT.work` (eval on points) | `DomainsConst.v`: annihilator entries and inverse backward entries for add/sub/xor/not/neg/eq (stay in the word table `ConstWordTable`); new: `T_*_le` |
| `Sign` | `Record sgn := Sgn { neg : bool; zero : bool; pos : bool }` (signed view) | height 3 | O(w²) (point path); O(1) table | `DomainsSign.v` theorems; new: time |
| `Congruence` (Granger 1989) | `Inductive congr := CBot \| C (m r : Z)`, normalised `0 ≤ r < m` or `m = 0`, `m \| 2^w` | height ≤ w+2, `widen := join`, `wrank := w + 2 - log2 m` | O(w²) (gcd, CRT meet) | `DomainsCongruence.v` (919 lines): `crt_meet_sound`, `congr_add_sound`, … |
| `Interval` (Z core) | `Inductive itv := IBot \| I (lo hi : bnd)` | thresholds (below) | O((ℓ+1)²) for Z; O(w²) for words | see `INTERVAL_PLAN` below |
| `KnownBits` (CGO 2022) | `Record tnum := Tnum { tv : Z; tm : Z }`, `land tv tm = 0` | height w+1, `widen := join`, `wrank := w - popcount tm` | add/sub/and/or/xor O(w); `tnum_mul` O(w²) (w rounds of an O(w) add, CGO'22 Listing 4); shifts by an unknown amount O(w²) (`DomainsTnumExpand`) | `DomainsTnum*`, `DomainsKnownBits*`; the `MulStages`, `MulAcc` and `MulBoth` choices stay as a value of type `mulchoice` in `wparam`… **no**: it becomes a module parameter `TNUM_CONFIG`, because it is configuration, not program data |
| `Wrapped` (Navas 2012) | `Inductive warc := WBot \| WArc (lo hi : Z) \| WTop`, an arc read clockwise | widening doubles the arc (Navas §4), `wrank := w + 1 - log2 (card)` (`DomainsWrappedRank.v`) | O(w²) (mul splits at both poles: ≤ 4×4 pieces) | `DomainsWrapped*` theorems; `DomainsWrappedRank` gives `wrank_widen` |

**Interval in detail.** This is the one fully written instance; the others follow its pattern.

```coq
(* Thresholds.v *)
Inductive ttree := TLeaf | TNode (l : ttree) (z : Z) (r : ttree).
Module Thresholds.
  Fixpoint msort ... (* top-down merge sort written for TimeFun: split by halves, structural on fuel = length *)
  Definition dedup_sorted : list Z -> list Z.
  Fixpoint build (fuel : nat) (xs : list Z) : ttree.    (* median split; fuel := length xs, as today *)
  Definition make (zs : list Z) : ttree := build (length zs) (dedup_sorted (msort zs)).
  Fixpoint above (t : ttree) (z : Z) : option Z.        (* least u in t with z <= u *)
  Fixpoint below (t : ttree) (z : Z) : option Z.
End Thresholds.
Module Type THRESHOLDS_PLAN.
  Parameter vals : ttree -> list Z.   Parameter depth : ttree -> nat.
  Parameter make_vals : forall zs x, In x (vals (make zs)) <-> In x zs.
  Parameter make_ordered : forall zs, ordered (make zs).
  Parameter make_depth : forall zs, depth (make zs) <= Nat.log2 (length zs) + 1.
  Parameter above_spec : forall t z, ordered t -> match above t z with
    | Some u => In u (vals t) /\ z <= u /\ forall v, In v (vals t) -> z <= v -> u <= v
    | None => forall v, In v (vals t) -> v < z end.
  Parameter below_spec : (* symmetric *).
  (* time: zb t = max bit size of the values in t *)
  Parameter T_msort_le : forall zs, T_msort zs <= c * (length zs * (Nat.log2 (length zs) + 1) + 1) * (zb zs + 1).
  Parameter T_make_le : forall zs, T_make zs <= c * (length zs * (Nat.log2 (length zs) + 1) + 1) * (zb zs + 1).
  Parameter T_above_le : forall t z, T_above t z <= c * (depth t + 1) * (zb t + Z.size z + 1).
End THRESHOLDS_PLAN.
```

The time bounds are tight:
- `make` is Θ(n log n) comparisons, by the comparison-sort lower bound.
- `above` is Θ(depth): a search whose answer is a leaf of a balanced tree visits `depth` nodes.

The proofs carry over from `DomainsThreshold.v:234–441`.

```coq
(* Interval.v -- Z core, then a word payload *)
Module ZInterval.   (* HARNESS_BASE ZLang and WIDENING with wparam := ttree *)
  Definition t := itv.
  Definition widen (T : ttree) (a b : itv) : itv :=
    match a, b with IBot, _ => b | _, IBot => a
    | I l1 h1, I l2 h2 =>
      I (if bnd_ltb l2 l1 then match l2 with Fin z => opt_lo (Thresholds.below T z) | _ => NegInf end else l1)
        (if bnd_ltb h1 h2 then match h2 with Fin z => opt_hi (Thresholds.above T z) | _ => PosInf end else h1)
    end.
  (* spec *) Definition wrank (T : ttree) (a : itv) : nat :=
    match a with IBot => 0 | I l h =>
      (match h with Fin z => 1 + count_gt T z | _ => 0 end) + (match l with Fin z => 1 + count_lt T z | _ => 0 end) end.
End ZInterval.
Module IntervalPayload <: WORD_PAYLOAD.   (* pgamma w i z := in_itv i z /\ is_word w z *) End IntervalPayload.
Module IntervalWordTable <: WORD_TABLE IntervalPayload.   (* from IntervalOps.v *) End IntervalWordTable.
```

`INTERVAL_PLAN` (carried names in parentheses):
- `widen_ub_l` and `widen_ub_r` (`widen_lower_old`/`_next`, `widen_upper_old`/`_next`);
- `widen_stable`;
- `wrank_widen`: the jumped side's count drops by at least 1 by `above_spec`, and the other side is unchanged;
- `wrank_le : wrank T a <= 2 * (length (vals T) + 1)`;
- forward entries: `add_sound`, `sub_sound`, `mul_sound`, `udiv_sound`, `urem_sound`, `and_sound`, `or_sound`, `shl_sound`, `cmp_sound`, `signed_split_sound` (`DomainsIntervalArith`, `…Bitwise`, `…Shift`, `…Compare`, `…Signed`);
- backward entries: HC4 inverse rules `add_back_sound` … `ult_back_sound` (`DomainsIntervalBack`, `DomainsIntervalRefine`);
- `T_widen_le : T_widen T a b <= c * (depth T + 1) * (zb T + size a + size b + 1)`.

Corollary: under one threshold set, a head can be widened strictly at most `2 (|T| + 1)` times. Plain intervals (`T = TLeaf`) are the special case.

**Products.**

```coq
(* ProductSig.v *)
Module Type REDUCER (L : LANG) (A B : VALUE_DOMAIN L).
  Parameter reduce : A.t * B.t -> A.t * B.t.
  Parameter reduce_sound : forall a b c, A.gamma a c -> B.gamma b c ->
    A.gamma (fst (reduce (a, b))) c /\ B.gamma (snd (reduce (a, b))) c.
  Parameter reduce_lower : forall a b,
    A.leb (fst (reduce (a, b))) a = true /\ B.leb (snd (reduce (a, b))) b = true.
End REDUCER.
Module Type ROUNDS.  Parameter rounds : nat.  End ROUNDS.     (* configuration, not program data *)
Module Product (L : LANG) (A B : VALUE_DOMAIN L) <: VALUE_DOMAIN L.
  Definition t := (A.t * B.t)%type.
  Definition gamma (x : t) c := A.gamma (fst x) c /\ B.gamma (snd x) c.
  (* leb, join, meet, forward and backward componentwise; is_bot := A.is_bot || B.is_bot *)
End Product.
Module Reduced (L : LANG) (A B : VALUE_DOMAIN L) (R : REDUCER L A B) (K : ROUNDS) <: VALUE_DOMAIN L.
  Include Product L A B.
  Definition red (x : t) : t := Nat.iter K.rounds R.reduce x.
  (* forward, backward, guard and meet are followed by red; join and leb are not; widen is
     componentwise and never reduced (Cousot, Cousot & Mauborgne 2011, §6). The wrank of the
     product is the sum of the components' wranks. *)
End Reduced.
```

Plan:
- `red_sound : gamma x c -> gamma (red x) c` (by induction on `rounds`);
- `red_lower`;
- the `VALUE_DOMAIN` laws, which then follow componentwise;
- `T_red_le : T_red x <= K.rounds * c_R * (sizeA + sizeB + 1)`.

The reducers live in `Reducers.v`; each instantiates `REDUCER BitsLang`.
- `WrappedBits`: the CAV 2023 `reg_bounds_sync` steps (tnum → arc [tv, tv lor tm] when the arc does not cross the pole; arc → tnum by the common prefix of lo and hi).
- `IntervalCongr` (Granger 1989): round the bounds inward to the residue class; a singleton interval gives a congruence with m = 0.
- `IntervalBits`.

Each reducer is about 300 lines. Its plan is `reduce_sound` split per step.

Finally, `Translate (L1 L2) (F : LANG_MORPHISM L1 L2) (D : VALUE_DOMAIN L2) <: VALUE_DOMAIN L1` replaces `ValueAbs.rename` and `op_bridge`. Its law is `F.eval_agrees : L1.eval o cs = Some c -> L2.eval (F.op o) (map F.val cs) = Some (F.val c)`.

**Estimates and risks.**

Lines after conversion: Const 500, Sign 650, Congruence 850, Thresholds 550, Interval (all three files) 2,600, KnownBits 3,000, Wrapped 1,800, Product/Reduced 500, Reducers 900, Translate 200.

New proof work is mostly the time layers (about 120 to 400 lines per domain) and the reducers.

Risks:
- `TimeFun` on `BitsFun` loops (clz, ctz, popcnt) and on `tnum_mul` needs `CostStd` entries for `Z.testbit` and `Z.shiftl`.
- The quadratic `work` assumes the core's Z model (§0.4).

## 2. States

### 2.1 Non-relational environment

Core owns `STATE_DOMAIN`. These are the fields I need:

```coq
Module Type STATE_DOMAIN (X : KEY) (L : LANG).
  Declare Module V : VALUE_DOMAIN L.
  (* LATTICE + TOP + WIDENING fields: t leb join bot top is_bot widen wparam wrank narrow *)
  Parameter gamma : t -> (X.t -> L.val) -> Prop.
  Parameter assign : X.t -> term L.op X.t -> t -> t.
  Parameter havoc  : X.t -> t -> t.
  Parameter assume : L.guard -> list (term L.op X.t) -> t -> t.
  Parameter eval   : term L.op X.t -> t -> V.t.               (* project x = eval (Leaf x) *)
  Parameter gamma_mono : forall a b st, leb a b = true -> gamma a st -> gamma b st.
  Parameter gamma_bot : forall st, ~ gamma bot st.   Parameter gamma_top : forall st, gamma top st.
  Parameter assign_sound : forall x e s st c, gamma s st -> eval_term L.eval st e = Some c ->
    gamma (assign x e s) (upd X.eqb st x c).
  Parameter havoc_sound : forall x s st c, gamma s st -> gamma (havoc x s) (upd X.eqb st x c).
  Parameter assume_sound : forall g es s st cs, gamma s st -> eval_terms L.eval st es = Some cs ->
    L.holds g cs -> gamma (assume g es s) st.
  Parameter eval_sound : forall e s st c, gamma s st -> eval_term L.eval st e = Some c ->
    V.gamma (eval e s) c.
End STATE_DOMAIN.
```

`gamma` reads `st` only pointwise, so no functional extensionality is needed.

Fields I need from core's `MAP` (over `KEY` `X`), each with a time contract:
- `empty`, `get`, `set`, `remove`;
- `merge (f : option A -> option B -> option C) m1 m2`, with `T_merge f T_f m1 m2 <= c_map * (k + 1) * (nodes m1 + nodes m2 + 1)` under `forall a b, T_f a b <= k`; this is not listed in the core brief and must be added;
- `forall2b`, with the same shape of contract;
- `fold` and `elements` (in increasing `encode` order);
- `nodes : t A -> nat` (spec);
- `get_merge`, `get_set_same`, `get_set_other`, `elements_spec`.

From `KEY` I need `eqb`, `eqb_spec` and `encode_inj`. I also need key functors on `KEY`: `OptKey (X)` (None ↦ 1, Some x ↦ (encode x)~0) and `LitKey (X)` ((x,b) ↦ (encode x)~1 or (encode x)~0). I write them in `Relational/Keys.v`.

```coq
Inductive reach (A : Type) := Unreached | Reached (a : A).                    (* top level *)
Inductive ann (K X A : Type) := ALeaf (x : X) (a : A) | ANode (k : K) (a : A) (kids : list (ann K X A)).
Module Env (X : KEY) (M : MAP with Module K := X) (L : LANG) (LT : LANG_TIME L)
           (V0 : VALUE_DOMAIN L) (VT : VALUE_DOMAIN_TIME L V0) (VW : WIDENING V0)
  <: STATE_DOMAIN X L with Module V := V0.
  Module V := V0.
  Definition t := reach (M.t V.t).                 (* an absent key reads as V.top *)
  Definition read (m : M.t V.t) x := match M.get x m with Some a => a | None => V.top end.
  Fixpoint annotate (m : M.t V.t) (e : term L.op X.t) : ann L.op X.t V.t.   (* forward HC4 pass *)
  Definition root : ann L.op X.t V.t -> V.t.
  Fixpoint refine (q : V.t) (n : ann L.op X.t V.t) (m : M.t V.t) : M.t V.t.
    (* ALeaf x a  => M.set x (V.meet (read m x) q) m
       ANode k a ks => fold the kids with V.backward k (V.meet a q) (map root ks) *)
  Definition assume g es s := match s with Unreached => Unreached | Reached m =>
    let ns := map (annotate m) es in let qs := V.guard g (map root ns) in
    let m' := fold_left2 refine qs ns m in
    if M.existsb V.is_bot m' then Unreached else Reached m' end.
  Definition assign x e s := (* Reached (M.set x (root (annotate m e)) m) or Unreached when is_bot *).
  Definition havoc x s := (* M.remove x *).
  Definition eval e s := match s with Unreached => V.bot | Reached m => root (annotate m e) end.
  (* join: M.merge keeps keys present on both sides; leb: M.forall2b with read defaults;
     widen p: pointwise VW.widen p; wrank p s := sum of VW.wrank p over the bindings *)
  TimeFun read. TimeFun annotate. TimeFun refine. TimeFun assume. (* ... *)
End Env.
```

`annotate` and `refine` recurse through `list` and need `TimeFun` support for a nested `fix` (§0.4). The fallback is mutual `term`/`terms` types, which needs Argent's mutual support.

Plan (`ENV_PLAN`). The lemmas port from `DomainsEnv.v:174–748` and `LatticeEnv.v`. `models m st` is `forall x, V.gamma (read m x) (st x)`.

```coq
Parameter annotate_sound : forall m st e c, models m st -> eval_term L.eval st e = Some c ->
  ann_models st (annotate m e) e /\ V.gamma (root (annotate m e)) c.
  (* ann_models: every node's value describes that node's concrete value *)
Parameter refine_sound : forall m st e n q c, models m st -> ann_models st n e ->
  eval_term L.eval st e = Some c -> V.gamma q c -> models (refine q n m) st.
Parameter refine_lower : forall q n m x, V.leb (read (refine q n m) x) (read m x) = true.
Parameter assume_sound', assign_sound', havoc_sound', eval_sound'.   (* the STATE_DOMAIN laws *)
Parameter join_models : forall a b st, models a st \/ models b st -> models (join_map a b) st.
Parameter wrank_widen_env : (* sum of component wranks over the domain of the left argument *).
(* time; tcost m e is a spec equal to the sum over nodes of (VT.work k args + 1) plus key bits at leaves *)
Parameter T_annotate_le : forall m e, T_annotate m e <= c * tcost m e.
Parameter T_assume_le : forall g es s, T_assume g es s <=
  c * (list_sum (map (tcost_s s) es) + VT.gwork g (roots s es) + 1).
Parameter T_join_le : forall a b, T_join a b <= c * (esize a + esize b + 1).
  (* esize m = sum over bindings (k, v) of (bits k + VT.size v + 1) *)
```

- **Bound:** Θ(Σ over term nodes of (transfer work + key bits)). It is tight, because every node is visited once in each pass.
- **Estimate:** 1,300 lines, 1.5 h.
- **Risk:** the `TimeFun` treatment of nested recursion.

### 2.2 Partitioning (Mauborgne & Rival, ESOP 2005)

```coq
Module Partition (X : KEY) (L : LANG) (Tk : KEY) (MT : MAP with Module K := Tk) (S : STATE_DOMAIN X L)
  <: STATE_DOMAIN X L with Module V := S.V.
  Definition t := MT.t S.t.                            (* an absent token reads as S.bot *)
  Definition gamma (p : t) st := exists k s, MT.get k p = Some s /\ S.gamma s st.
  Definition inject (k : Tk.t) (s : S.t) : t := MT.set k s MT.empty.
  Definition merge (k : Tk.t) (p : t) : t := inject k (MT.fold (fun _ s acc => S.join s acc) p S.bot).
  Definition retag (k : Tk.t) (p : t) : t := merge k p.
  (* assign, havoc, assume and widen apply pointwise; eval joins the parts' results; tokens are
     program data supplied by the analysis, e.g. the encoded last branch outcomes *)
End Partition.
```

Plan:
- `gamma_inject`;
- `merge_sound : gamma p st -> gamma (merge k p) st`;
- the pointwise transfer laws;
- `wrank` is the sum over parts.

Bound: `T_op ≤ c · Σ_parts (T_S.op + bits tok + 1)`. Estimate 500 lines, 0.6 h.

### 2.3 Bounded disjunction (Bagnara, Hill & Zaffanella, STTT 8(4), 2006; Sankaranarayanan et al., SAS 2006)

```coq
Module Type CAP.  Parameter k : nat.  Parameter k_pos : 0 < k.  End CAP.
Module Disj (X : KEY) (L : LANG) (S : STATE_DOMAIN X L) (C : CAP) <: STATE_DOMAIN X L with Module V := S.V.
  Definition t := list S.t.          (* invariant: no S.is_bot element and length <= C.k *)
  Definition gamma (d : t) st := Exists (fun s => S.gamma s st) d.
  Definition leb (a b : t) := forallb (fun x => existsb (S.leb x) b) a.        (* Hoare order *)
  Fixpoint compact (n : nat) (d : t) : t.   (* join the two last elements until length <= n *)
  Definition join a b := compact C.k (a ++ b).
  Definition widen p (a b : t) :=
    if leb b a then a else
    let b' := compact (length a) (join a b) in
    if Nat.eqb (length b') (length a) then map2 (S.widen p) a b' else [S.widen p (collapse a) (collapse b)].
  (* spec *) Definition wrank p d := list_sum (map (S.wrank p) d) + (if length d =? 1 then 0 else C.k).
End Disj.
```

Plan:
- `compact_covers : forall x, In x d -> exists y, In y (compact n d) /\ S.leb x y = true`;
- `compact_len : length (compact n d) <= max n 1`;
- `leb_trans` (from `S.leb_trans`);
- `widen_ub_l` and `widen_ub_r` (via `compact_covers` and `S.widen_ub_*`);
- `wrank_widen`: either the lengths are equal and some component strictly decreases while the others do not increase, or the result collapses and the `C.k` term drops.

This needs one more law in core's `WIDENING`: `wrank_widen_le : is_bot a = false -> wrank p (widen p a b) <= wrank p a`.

Bound: join is O(k²·T_S.join), leb is O(k²·T_S.leb). Estimate 800 lines, 1 h. The proofs port from `LatticeDisjunction.v`.

## 3. Relational domains

### 3.0 Shared structure

Citations:
- Miné, "A new numerical abstract domain based on difference-bound matrices", PADO 2001.
- Miné, "The octagon abstract domain", HOSC 19(1), 2006.
- Bagnara, Hill & Zaffanella, "An improved tight closure algorithm for integer octagonal constraints", VMCAI 2008.
- Bagnara, Hill & Zaffanella, "Weakly-relational shapes for numeric abstractions", FMSD 2009 (one strengthening pass after Floyd–Warshall suffices).
- Chawdhary, Robbins & King, "Simple and efficient algorithms for octagons", APLAS 2014 (incremental closure in O(n²)).
- Gange, Navas, Schachte, Søndergaard & Stuckey, "Exploiting sparsity in difference-bound matrices", SAS 2016.
- Hougardy, "The Floyd–Warshall algorithm on graphs with negative cycles", IPL 2010 (exit at the first negative diagonal).
- Karr, Acta Informatica 6, 1976; Müller-Olm & Seidl, "A note on Karr's algorithm", ICALP 2004.
- Fouilhé, Monniaux & Périn, SAS 2013 (Farkas certificates); Fouilhé & Boulmé, VSTTE 2014; Boulmé, Maréchal, Monniaux, Périn & Yu, "The Verified Polyhedron Library: an overview", SYNASC 2018.
- Besson, Jensen, Pichardie & Turpin, TGC 2010 (certified polyhedral result checking).
- Cousot & Halbwachs, POPL 1978; Bagnara, Hill, Ricci & Zaffanella, SCP 58, 2005 (widenings).
- Benoy, King & Mesnard, TPLP 5, 2005 (convex hull by projection).
- Schrijver, *Theory of Linear and Integer Programming*, 1986, §12.2 (Fourier–Motzkin and Farkas).
- Chvátal 1973 (integer cuts).
- Simon & King, "Taming the wrapping of integer arithmetic", SAS 2007 (machine words).

Relational domains are over `Z`. A `NUM_STATE` is reduced with `Env` to give a `STATE_DOMAIN` (the Astrée practice).

```coq
(* Relational/LinForm.v -- data at top level *)
Record lin (X : Type) := Lin { coef : list (X * Z); cst : Z }.    (* sorted by encode, no zero coefficients *)
Inductive rel := REq | RLe.
Record lcons (X : Type) := LCons { lhs : list (X * Z); lrel : rel; rhs : Z }.   (* sum a_x * v x  rel  rhs *)
Inductive wrapr := NoWrap | WrapTo (lo hi : Z).
Inductive cmp := CLe | CLt | CEq.
Record atom (X : Type) := Atom { al : lin X; alw : wrapr; acmp : cmp; ar : lin X; arw : wrapr }.
Definition wrap_into (r : wrapr) (z : Z) : Z :=
  match r with NoWrap => z | WrapTo lo hi => lo + (z - lo) mod (hi - lo + 1) end.

Module Type LINEARIZE (X : KEY) (L : LANG) (N : NUM_VIEW L).
  Parameter lin_of : term L.op X.t -> option (lin X.t * wrapr).
  Parameter atoms_of : L.guard -> list (term L.op X.t) -> list (atom X.t).
  Parameter lin_sound : forall st e c f r, eval_term L.eval st e = Some c -> lin_of e = Some (f, r) ->
    N.num c = wrap_into r (eval_lin (fun x => N.num (st x)) f).
  Parameter atoms_sound : forall g es st cs, eval_terms L.eval st es = Some cs -> L.holds g cs ->
    Forall (atom_holds (fun x => N.num (st x))) (atoms_of g es).
  (* time: T_lin_of e <= c * (tsize e) * (bits_e + 1) *)
End LINEARIZE.
```

Instances:
- `ZLinearize`: `NoWrap` everywhere.
- `BitsLinearizeU` and `BitsLinearizeS`, the unsigned and signed views:
  - `bvadd` gives `WrapTo 0 (2^w-1)` (or the signed range);
  - multiplication by a constant is linear;
  - `bvult`/`bvslt` under `BTruth` become `CLt` atoms in the matching view;
  - every other operator gives `None`.

  Key lemma: `wrap_into_id : lo <= z <= hi -> wrap_into (WrapTo lo hi) z = z`. A domain uses a wrapped form exactly only after proving from its own bounds that the value is in range; otherwise it havocs and then asserts the range (Simon & King 2007).

```coq
Module Type NUM_STATE (X : KEY) (L : LANG) (N : NUM_VIEW L) (Lz : LINEARIZE X L N).
  (* LATTICE + TOP + WIDENING fields *)
  Parameter ngamma : t -> (X.t -> Z) -> Prop.
  Parameter assign : X.t -> term L.op X.t -> t -> t.
  Parameter havoc : X.t -> t -> t.
  Parameter assume : L.guard -> list (term L.op X.t) -> t -> t.
  Parameter range : term L.op X.t -> t -> bnd * bnd.
  Parameter assign_sound : forall x e s st c, ngamma s (fun y => N.num (st y)) ->
    eval_term L.eval st e = Some c -> ngamma (assign x e s) (fun y => N.num (upd X.eqb st x c y)).
  Parameter havoc_sound, assume_sound (* as in STATE_DOMAIN, through N.num *).
  Parameter range_sound : forall e s st c, ngamma s (fun y => N.num (st y)) ->
    eval_term L.eval st e = Some c -> in_bnd (fst (range e s)) (snd (range e s)) (N.num c).
End NUM_STATE.
(* States/RelEnv.v *)
Module RelEnv (X L N Lz) (R : NUM_STATE X L N Lz) (E : STATE_DOMAIN X L) (RR : RANGE_REFINE L N E.V)
  <: STATE_DOMAIN X L with Module V := E.V.
  Definition t := (R.t * E.t)%type.
  Definition eval e (s : t) := RR.refine_range (fst (R.range e (fst s))) (snd (R.range e (fst s))) (E.eval e (snd s)).
End RelEnv.
```

Matrix entries are `Z` (finite); an absent entry is +∞.

Cost notation:
- n is the number of variables in the support;
- b is the maximum key bits;
- ℓ is the maximum bit size of an entry.

### 3.1 Zones

```coq
Module Zone (X : KEY) (M : MAP with Module K := OptKey X) (L N Lz) <: NUM_STATE X L N Lz.
  Definition dbm := M.t (M.t Z).         (* m[i][j] bounds v j - v i; None is the constant 0 *)
  Definition t := reach dbm.
  Definition ngamma (s : t) (v : X.t -> Z) := match s with Unreached => False
    | Reached m => forall i j d, entry m i j = Some d -> vz v j - vz v i <= d end.
  Definition fw_round (k : option X.t) (m : dbm) : dbm.      (* m[i][j] := min (m[i][j], m[i][k] + m[k][j]) *)
  Definition close (m : dbm) : t :=                          (* fold over support; Unreached at the first m[k][k] < 0 *)
  Definition add_cons (i j : option X.t) (d : Z) (m : dbm) : dbm.
  Definition incr_close (i j : option X.t) (d : Z) (m : dbm) : t.   (* O(n^2) after one new edge *)
  (* leb: entrywise, left NOT closed (transitive by construction); join: close both, then the max
     on common keys; widen: keep m[i][j] when b[i][j] <= a[i][j], else drop it, with no closure
     (Miné 2006 §4.6); wparam := ttree for the threshold version; wrank := finite-entry count.
     assign x := y + c and x := c exact; other affine forms havoc x and then add the range of e
     computed by [range]; assume: CLe/CLt atoms of shape x - y <= c become add_cons + incr_close,
     other atoms are skipped. *)
End Zone.
```

Plan (`ZONE_PLAN`):

```coq
Parameter fw_round_implied : forall k m v, models m v -> models (fw_round k m) v.
Parameter close_sound : forall m v, models m v -> ngamma (close m) v.
Parameter close_bot : forall m, close m = Unreached -> forall v, ~ models m v.
Parameter incr_close_sound : forall i j d m v, models m v -> vz v j - vz v i <= d -> ngamma (incr_close i j d m) v.
Parameter leb_sound : forall a b v, leb a b = true -> ngamma a v -> ngamma b v.
Parameter join_sound_l, join_sound_r, widen_ub_l, widen_ub_r, wrank_widen.
Parameter assign_sound', havoc_sound', assume_sound', range_sound'.
(* precision, not needed for soundness *)
Parameter close_shortest : forall m m', close m = Reached m' -> forall i j,
  entry m' i j = min_path_weight m i j.                     (* Floyd–Warshall invariant over rounds *)
Parameter incr_close_eq : forall m i j d, closed m -> incr_close i j d m = close (add_cons i j d m).
(* time *)
Parameter bits_close_le : forall m m', close m = Reached m' -> ell m' <= ell m + Nat.log2 (supp m) + 1.
Parameter T_close_le : forall m, T_close m <= c * (supp m)^3 * (b m + ell m + Nat.log2 (supp m) + 1).
Parameter T_incr_close_le : forall i j d m, T_incr_close i j d m <= c * (supp m)^2 * (b m + ell m + Z.size d + 1).
Parameter T_join_le, T_leb_le, T_widen_le : (* c * (supp a + supp b)^2 * (b + ell + 1) *).
```

The soundness lemmas are easy: each update is an implied constraint. `close_shortest` and `bits_close_le` are the hard ones.

- **Bounds:** close is Θ(n³) entry updates (Floyd–Warshall is cubic on dense inputs); `incr_close` is Θ(n²).
- **Checked:** nothing. A closure certificate costs as much to check as to compute, and soundness is already cheap.
- **Estimate:** 1,800 lines for soundness and time, plus 600 for `close_shortest`; 2.6 h.
- **Risk:** `bits_close_le` with early exit. If it is not proved, the bound falls back to ℓ + n.

### 3.2 Octagons

The representation is the zone's, keyed by `LitKey X`: a literal is (x, true) for +x and (x, false) for −x. A unary bound is m[x̄][x] = 2c.

```coq
Definition strengthen (m) := (* m[i][j] := min (m[i][j], (m[i][ī] + m[j̄][j]) / 2), Z floor division *).
Definition tighten (m) := (* m[i][ī] := 2 * (m[i][ī] / 2) *).          (* integers, BHZ 2008 *)
Definition close m := strengthen (fw m)                   (* BHZ 2009: one strengthening pass suffices *)
Definition tclose m := let m1 := fw m in let m2 := tighten m1 in
   if exists i, m2[i][ī] + m2[ī][i] < 0 then Unreached else Reached (strengthen m2).
Definition incr_close (lit_i lit_j d) m.                  (* Chawdhary et al. 2014, Fig. 3; O(n^2) *)
```

Plan (`OCTAGON_PLAN`):
- `strengthen_implied`: (a + b)/2 is implied by v_i − v_ī ≤ a and v_j̄ − v_j ≤ b, using floor division over Z;
- `tighten_implied`: 2·x ≤ a implies 2·x ≤ 2⌊a/2⌋ over Z;
- `tclose_sound`, `tclose_bot`, `incr_close_sound`, and the rest as for zones;
- precision: `close_strong`, so `close` gives a strongly closed matrix over Q (Miné 2006 Thm 4.3.2 with the BHZ 2009 correction);
- precision: `tclose_tight`, a tightly closed matrix over Z (BHZ 2008 Thm 3);
- precision: `incr_close_eq`;
- time: `T_tclose_le : T_tclose m <= c * (supp m)^3 * (b + ell + log n + 1)`, `T_incr_close_le` in n²;
- `wrank` as for zones; coherence (m[i][j] = m[j̄][ī]) is kept as an invariant for precision only.

- **Bounds:** Θ(n³) closure and Θ(n²) incremental closure. Both are tight for the algorithms as written.
- **Estimate:** 2,000 lines for soundness and time, plus 1,300 for the three precision theorems; 3.3 h.
- **Risk:** the tight-closure proof (BHZ 2008 is 10 pages of case analysis). The precision theorems can slip without affecting soundness.

### 3.3 The linear-certificate checker, shared by Karr and polyhedra

```coq
(* Relational/LinCert.v *)
Record cert := Cert { mults : list Z; scale : Z; cut : bool }.   (* dense, aligned with the system *)
Module LinCert (X : KEY).
  Definition combine (P : list (lcons X.t)) (ms : list Z) : option (lcons X.t).
    (* fails on a length mismatch or a negative multiplier on an RLe row;
       the result is REq iff every used row is REq *)
  Definition check_entails (P : list (lcons X.t)) (c : lcons X.t) (k : cert) : bool :=
    (0 <? scale k) &&
    match combine P (mults k) with
    | Some s => lin_eqb (lhs s) (scale_lin (scale k) (lhs c)) &&
       match lrel c, lrel s with
       | REq, REq => Z.eqb (rhs s) (scale k * rhs c)
       | RLe, _   => if cut k then Z.leb (rhs s / scale k) (rhs c)       (* Chvátal–Gomory cut, Z only *)
                     else Z.leb (rhs s) (scale k * rhs c)
       | REq, RLe => false end
    | None => false end.
  Definition check_empty (P : list (lcons X.t)) (ms : list Z) : bool :=
    match combine P ms with Some s => is_zero (lhs s) && (match lrel s with RLe => rhs s <? 0 | REq => negb (rhs s =? 0) end)
    | None => false end.
End LinCert.
```

The soundness lemmas are the trust base of §3.4 and §3.5. A cut requires the scaled left-hand side to be integral; the checker checks that the coefficients are divisible by `scale`.

```coq
Theorem check_entails_sound : forall P c k, check_entails P c k = true ->
  forall v : X.t -> Z, Forall (sat v) P -> sat v c.
Theorem check_entails_sound_Q : forall P c k, check_entails P c k = true -> cut k = false ->
  forall v : X.t -> Q, Forall (satQ v) P -> satQ v c.
Theorem check_empty_sound : forall P ms, check_empty P ms = true -> forall v, ~ Forall (sat v) P.
Theorem T_check_entails_le : forall P c k,
  T_check_entails P c k <= c_lc * (csize P (mults k) + lsize c + 1).
  (* csize = sum over rows of (row length * (b + (Z.size m_i + 1) * (ell_row + 1))) *)
```

- **Bound:** linear in the certificate-weighted input size. It is tight.
- **Estimate:** 800 lines, 1 h.

### 3.4 Linear equalities (Karr 1976)

The representation is `reach (list (lcons X.t))` with every row `REq`, in echelon form: each row has a pivot variable that appears in no other row. Rows are kept fraction-free, each divided by the gcd of its coefficients.

| Operation | Producer (untrusted) | Checker | Fallback when the check fails |
|---|---|---|---|
| `join a b` | Karr's affine hull: stack the generator forms and run fraction-free Gaussian elimination (Bareiss 1968) | each output row is `check_entails a row` and `check_entails b row`, with `REq` combinations | `top` (sound) |
| `leb a b` | reduce each row of b by a's pivots | `check_entails a row` for every row of b | `false` |
| `havoc x` | eliminate x by pivoting | each output row has `check_entails a row` and does not mention x | drop every row mentioning x (sound without a check) |
| `assign x := f` (affine, `NoWrap` or in range) | invertible: substitute; otherwise havoc, then add x = f[x0] | each output row r satisfies `check_entails a (subst x f r)` | havoc x |
| `assume` (`CEq` atom) | append and re-echelonise | none needed for soundness: appending is exact | — |
| bottom detection | elimination finds 0 = c with c ≠ 0 | `check_empty` | stay reached |

Widening is `join`, because the height is at most n+1 (Karr). Then `wrank a := n_max + 1 - rank a`, with `wparam := nat`, the number of program variables.

Plan:
- `subst_sat : sat v (subst x f r) <-> sat (upd v x (eval_lin v f)) r`;
- `join_sound_l`, `join_sound_r`, `havoc_sound`, `assign_sound`, `assume_sound` (each from `check_entails_sound`);
- `leb_complete_Q : (forall v : X.t -> Q, Forall (satQ v) a -> Forall (satQ v) b) -> leb a b = true` (for echelon a; needed for `leb_trans`: the proof builds a rational point from the free variables);
- `leb_trans` from `leb_complete_Q` and `check_entails_sound_Q`;
- `wrank_widen`: a strict join raises the dimension, so the row count drops;
- time: `T_join_le : T_join a b <= c * n^3 * (ellB n ell + 1)^2`, where `ellB n ell := n * (ell + Nat.log2 n + 1)` is the Hadamard bound on Bareiss entries;
- `bareiss_minor`: every intermediate entry is a minor of the input (Bareiss 1968; Edmonds 1967), which is used only for the time bound.

- **Bound:** O(n³) arithmetic operations per join (Müller-Olm & Seidl 2004), on O(n(ℓ + log n))-bit numbers.
- **Estimate:** 1,800 lines, plus 900 for `bareiss_minor`; 2.7 h.
- **Risk:** `bareiss_minor` (Sylvester's identity). Until it is proved, the time contract stays `Admitted` and is listed as remaining.

### 3.5 Convex polyhedra, constraint form (VPL architecture)

The representation is `reach (list (lcons X.t))` with rows `REq` or `RLe`.

The producer is Fourier–Motzkin (FM) with multiplier tracking. Each derived row carries its dense multiplier vector over the original rows, so a contradiction found by FM is a Farkas certificate directly. `entail_cert P c` runs FM to elimination on P ∧ (−lhs c ≤ −rhs c − 1) (integers) or with strictness (rationals) and reads off the certificate. Simplex replaces FM after the batches (§7).

| Operation | Producer | Checker | Fallback |
|---|---|---|---|
| `leb a b` | `entail_cert a r` for each row r of b; syntactic fast path when r ∈ a (needed for `leb_refl`) | `check_entails` | `false` |
| `join a b` | **weak join**: the rows of a entailed by b, plus the rows of b entailed by a (Sankaranarayanan et al. 2006); the exact hull of Benoy, King & Mesnard 2005 is a post-batch upgrade | each output row has `check_entails` from a and from b | `top` |
| `havoc x` | one FM elimination of x | each output row has `check_entails a row` and does not mention x | drop the rows mentioning x |
| `assign x := f` | invertible: substitute x := (x − f')/a; otherwise FM through a temporary variable `PTmp` (internal key type `TmpKey X`, producer only) | `check_entails a (subst x f r)` for each output row | havoc x |
| `assume` (`CLe`, `CLt`, `CEq` atoms in range) | append; `CLt` over Z becomes ≤ −1 | none needed for soundness (exact) | — |
| bottom | FM derives 0 ≤ negative | `check_empty` (with an optional cut) | stay reached |
| `widen a b` | standard widening (Cousot & Halbwachs 1978): the rows of a entailed by b; with thresholds, also the threshold constraints entailed by both ("widening up to", Halbwachs et al. 1997) | `check_entails b row` for each kept row (a ⊑ result holds syntactically: kept rows ⊆ a) | drop the row |

`wrank a := length (rows a)`. `wrank_widen` holds because the result's rows are a sublist of a's, and a strict step drops at least one: if no row is dropped, every row of a is certified entailed by b, so `leb b a = true`.

Plan (`POLY_PLAN`):

```coq
Parameter fm_step_mults : forall P x r, In r (fm_elim x P) ->
  combine P (mults_of r) = Some (row_of r).                     (* the tracked multipliers are exact *)
Parameter entail_cert_checks : forall P c k, entail_cert P c = Some k -> check_entails P c k = true.
  (* optional: soundness never relies on it *)
Parameter join_sound_l, join_sound_r, havoc_sound, assign_sound, assume_sound, widen_ub_l, widen_ub_r, wrank_widen.
Parameter fm_complete_Q : forall P c, entail_cert P c = None ->
  exists v : X.t -> Q, Forall (satQ v) P /\ ~ satQ v c.       (* Fourier 1827, Motzkin 1936; Schrijver §12.2 *)
Parameter leb_trans : (* from fm_complete_Q and check_entails_sound_Q *).
(* time, with m rows, n variables and lsz the row size *)
Parameter fm_rows_le : forall x P, length (fm_elim x P) <= (length P)^2 / 4 + length P.
Parameter T_fm_elim_le : forall x P, T_fm_elim x P <= c * (length P)^2 * (n + length P) * (ell P + 1)^2.
Parameter ell_fm_le : forall x P, ell (fm_elim x P) <= 2 * ell P + 1.
Parameter T_entail_cert_le : forall P c, T_entail_cert P c <=
  c * fmcost (n P) (length P + 1) (ell P + ell1 c).
  (* fmcost 0 m l = 1;  fmcost (S k) m l = m^2 (n + m) (l+1)^2 + fmcost k (m^2/4 + m) (2l + 1) *)
```

- **Bounds:**
  - **Checker:** linear in the certificate size (§3.3). It is the only trusted computation.
  - **Producer:** T_entail_cert is bounded by `fmcost`, which is doubly exponential in n. This is tight for FM as written, which keeps every combination: the row count reaches m²/4 when signs split evenly.
- **Estimate:** 2,500 lines, plus 1,200 for `fm_complete_Q`; 3.7 h.
- **Risks:**
  - `fm_complete_Q` is a real proof. Without it, `leb_trans` stays `Admitted` and the polyhedra do not satisfy the core weak laws.
  - FM's blow-up limits the producer to small dimensions. VPL uses simplex and parametric LP for this reason; that is §7, "after".

## 4. Widening control

Package `theories/Widening/`. Citations:
- Bourdoncle, "Efficient chaotic iteration strategies with widenings", FMPA 1993 (weak topological order, WTO);
- Halbwachs, Proy & Roumanoff 1997 (delay; widening up to);
- Blanchet et al. 2003 and Lakhdar-Chaouch et al. 2011 (thresholds);
- Cousot & Cousot 1977, 1992 (narrowing);
- Halbwachs & Henry, SAS 2012 (descending sequences);
- Amato, Scozzari, Seidl, Apinis & Vojdani, SCP 120, 2016 (intertwining widening and narrowing).

```coq
(* Widening/Mining.v *)
Module Mining (X : KEY) (L : LANG).
  Fixpoint lits (e : term L.op X.t) : list Z.               (* L.literal at each node *)
  Definition mine (es : list (term L.op X.t)) (extra : list Z) : ttree :=
    Thresholds.make (flat_map (fun z => [z - 1; z; z + 1]) (flat_map lits es ++ extra)).
    (* extra: the word boundaries 0, 2^(w-1)-1, 2^(w-1), 2^w-1 for each program width *)
End Mining.
(* Widening/Policy.v -- policies are data *)
Record head_cfg := HeadCfg { delay : nat; narrow_passes : nat }.          (* top level *)
Module Policy (X : KEY) (MX : MAP with Module K := X) (D : LATTICE) (W : WIDENING D).
  Record policy := Pol { heads : MX.t head_cfg; wp : W.wparam }.
  Definition update (p : policy) (x : X.t) (cnt : nat) (old new : D.t) : D.t * nat :=
    if D.leb new old then (old, cnt) else
    match MX.get x (heads p) with
    | None => (D.join old new, cnt)                                          (* not a head *)
    | Some h => if Nat.ltb cnt (delay h) then (D.join old new, S cnt) else (W.widen (wp p) old new, S cnt)
    end.
  Definition of_wto (w : Wto.t) (cfg : head_cfg) (wp : W.wparam) : policy.   (* heads := Wto.heads w *)
End Policy.
```

The theorems keep the engines engine-agnostic.

1. **Soundness is free.** Every result is certified by the engines' checker. `Solver.solved_sound` (engines) is the statement, and a policy changes only the candidate. The policy module therefore proves only the facts engines use for termination and cost:

```coq
Theorem update_ub : forall p x cnt old new,
  D.leb old (fst (update p x cnt old new)) = true /\ D.leb new (fst (update p x cnt old new)) = true.
Theorem update_stable : forall p x cnt old new, D.leb new old = true -> update p x cnt old new = (old, cnt).
(* For a head: the number of strict updates is bounded by a potential. *)
Definition head_pot (h : head_cfg) wp (cnt : nat) (a : D.t) : nat :=
  (delay h - cnt) + (if D.is_bot a then 1 else 0) + (if Nat.ltb cnt (delay h) then 0 else W.wrank wp a).
Theorem head_strict_steps : forall p x h cnt a new, MX.get x (heads p) = Some h ->
  D.leb new a = false -> Nat.leb (delay h) cnt = true ->
  let '(a', cnt') := update p x cnt a new in head_pot h (wp p) cnt' a' < head_pot h (wp p) cnt a.
Theorem head_updates_le : forall p x h (news : list D.t) a0, MX.get x (heads p) = Some h ->
  strict_count (run_updates p x 0 a0 news) <= delay h + 1 + W.wrank (wp p) (value_after_delay ...).
```

2. **Every cycle is cut.** `of_wto_cuts : WtoCheck.check g roots w = true -> forall cycle in g, exists y in cycle, MX.get y (heads (of_wto w cfg wp)) <> None`. This comes from Graph's `WtoCheck.check_correct` (`GraphCheckWto.v:180`). I need the engines or Graph architect to export `Wto.heads` and a "cycle contains a head" corollary.

3. **Narrowing passes.** Functor `Narrow (Sys : SYSTEM) (Chk : the core checker)`. Each pass computes x'ᵢ = narrow xᵢ (Fᵢ x) over the WTO order. The result is passed to the checker and replaced by the input when the check fails.

```coq
Theorem narrow_pass_post : forall s, Sys.post_solution s -> Sys.post_solution (narrow_pass s).  (* by the check fallback *)
Theorem narrow_pass_below : forall s x, D.leb (narrow_pass s x) (s x) = true.
Theorem narrow_pass_exact_mono : Sys.monotone -> forall s, Sys.post_solution s ->
  check (narrow_candidate s) = true.        (* Cousot 1977: under monotonicity the check always passes *)
Theorem T_narrow_passes_le : forall k s, T_narrow_passes k s <= k * (T_eval_all s + T_check s + 1).
```

From core and engines I need: `SYSTEM.post_solution`, `check : assignment -> bool`, `check_sound`, and `T_check_le`.

Estimate: Mining 300 lines, Policy 600, Narrow 400; 1.4 h. Risk: low. The only cross-team dependency is the names above.

## 5. Alarms

Package `theories/Alarms/`. Citations: Cousot et al., "The ASTRÉE analyzer", ESOP 2005; Jourdan et al., "A formally-verified C static analyzer", POPL 2015 (the "no alarm implies safe" form).

```coq
(* Alarms/ChecksSig.v *)
Inductive kind := DivZero | Overflow (o : BitsOp.op) (signed : bool) | Bounds | NullDeref.  (* bits instance *)
Record check (N K X Kd : Type) := Check { site : N; ckind : Kd; args : list (term K X) }.  (* top level *)
Module Type CHECKS (L : LANG) (V : VALUE_DOMAIN L).
  Parameter kd : Type.
  Parameter safe : kd -> list L.val -> Prop.
  Parameter may_fail : kd -> list V.t -> bool.
  Parameter may_fail_sound : forall k xs cs, may_fail k xs = false -> Forall2 V.gamma xs cs -> safe k cs.
  Parameter may_fail_top : forall k n, (exists cs, length cs = n /\ ~ safe k cs) -> may_fail k (repeat V.top n) = true.
End CHECKS.
Module Type CHECKS_POINT (L : LANG) (B : HARNESS_BASE L) (C : CHECKS L ...).
  Parameter may_fail_point : forall k xs cs, Forall2 (fun x c => B.point x = Some c) xs cs ->
    ~ C.safe k cs -> C.may_fail k xs = true.
End CHECKS_POINT.
```

`BitsChecks (V) (Q : RANGE_QUERY BitsLang NumU V) (QS : RANGE_QUERY BitsLang NumS V)` defines the four kinds:
- `DivZero [d]`: `snd d <> 0`. It may fail iff 0 is in `range d`.
- `Overflow o s [a; b]`: the mathematical result of o in view s lies in that view's range. It may fail iff the interval arithmetic on the ranges leaves the range.
- `Bounds [i; len]`: `0 <= snd i < snd len`. It may fail iff `hi i >= lo len` or `lo i < 0`.
- `NullDeref [p]`: `snd p <> 0`.

```coq
Module Alarms (N X : KEY) (MN : MAP with Module K := N) (L : LANG) (S : STATE_DOMAIN X L) (C : CHECKS L S.V).
  Definition inv_at (inv : MN.t S.t) n := match MN.get n inv with Some s => s | None => S.bot end.
  Definition alarm (inv : MN.t S.t) (k : check N.t L.op X.t C.kd) : bool :=
    C.may_fail (ckind k) (map (fun e => S.eval e (inv_at inv (site k))) (args k)).
  Definition alarms inv ks := filter (alarm inv) ks.
  TimeFun alarm. TimeFun alarms.

  Theorem no_alarm_safe : forall (reach : N.t -> (X.t -> L.val) -> Prop) inv,
    (forall n st, reach n st -> S.gamma (inv_at inv n) st) ->
    forall k, alarm inv k = false ->
    forall st cs, reach (site k) st -> eval_terms L.eval st (args k) = Some cs -> C.safe (ckind k) cs.
  (* Proof: S.eval_sound on each argument gives Forall2 S.V.gamma, then C.may_fail_sound. *)

  (* Non-vacuity, two forms *)
  Theorem alarm_at_top : forall inv k, inv_at inv (site k) = S.top ->
    (forall e, In e (args k) -> S.eval e S.top = S.V.top) ->           (* a top state gives top values *)
    (exists cs, length cs = length (args k) /\ ~ C.safe (ckind k) cs) -> alarm inv k = true.
  Theorem alarm_on_exact_error : (* with CHECKS_POINT: if every argument evaluates to a point and
    the points violate safe, then alarm inv k = true *).
  Theorem T_alarms_le : forall inv ks, T_alarms inv ks <=
    c * list_sum (map (fun k => list_sum (map (fun e => S_eval_cost e (inv_at inv (site k))) (args k))
                               + C_cost k + bits (site k) + 1) ks).
End Alarms.
```

The end-to-end corollary is `analysis_no_alarm_safe`. It instantiates `reach` with the program semantics and the covering hypothesis with the framework's soundness theorem for certified post-solutions, which the engines architect must name. The tests check precision only (a guarded division raises no alarm), because no theorem states it.

Estimate: `Alarms` 700 lines, `BitsChecks` 500 lines; 1.2 h. Risk: the overflow precision rules for signed `bvmul`.

## 6. Float

**What to keep.** From the legacy package (`galois-archive/.../legacy/theories/Float`, about 3.8k lines, fully proved) I would keep three parts:
- `FloatInterval.v` (739 lines): non-NaN bounds plus flags for NaN, +0 and −0. The two signed zeros stay distinguishable.
- The transfer core of `FloatOps.v`, about lines 190–1381:
  - outward rounding of bounds for neg, abs, add, sub, mul and div;
  - backward `assume_lt`;
  - an explicit NaN policy. The NaN policy becomes a module parameter `NAN_MODEL`, and the format (prec, emax) becomes a module parameter `FORMAT`, replacing the literals 24/128 and 53/1024.

These become `FloatLang <: LANG`, with `val := binary_float prec emax` and the operator table as data, and `FloatInterval <: HARNESS_BASE FloatLang` with a `TABLE` instance, so floats use the same harness as everything else. `FloatSsa.v` and the NaN-demand domain in `FloatNan.v` go: they are client-specific and belong with the analyses or examples, if anywhere. Cost: Flocq's `Bplus` and the rest are closed constants outside Galois, so they need mirrored `T_` constants in a `FloatStd` file (Argent §2, naming rule). For a fixed format every operation is O(prec) on mantissas, which is constant per format.

**The blocking issue.** I checked in the REPL that `Bplus` itself, not only its correctness lemma, depends on `ClassicalDedekindReals.sig_not_dec`, `sig_forall_dec`, `functional_extensionality_dep` and `classic`. Under decision 7 ("no axioms") a Flocq-based Float package cannot exist. I recommend that the owner grant an exception scoped by import to `theories/Float/`, exactly as the earlier `float.md` did, and that no other package may import `Galois.Float`. The axiom-free alternative is Stdlib's `SpecFloat` (`SFadd` is closed). It would need every monotonicity-of-rounding fact re-proved over `Z` without `R`, which I estimate at 4–6k lines of new mathematics with no published Coq development to follow. I therefore schedule no Float session: Float is listed under "after".

## 7. Work packages

### 7.1 Groundwork before the sessions (our own agents)

1. **Signature and data files, compiling.** Every implementation file listed below gets a stub with `Admitted` proofs and `TimeFun` lines.
   - `Domains`: `LangSig.v`, `ValueSig.v` (or core's, with my fields), `HarnessSig.v`, `WordSig.v`, `ProductSig.v`, and one `*Sig.v` per domain containing `FOO`, `FOO_TIME` and `FOO_PLAN`.
   - `States`: `EnvSig.v`, `PartitionSig.v`, `DisjunctionSig.v`, `RelEnvSig.v`.
   - `Relational`: `Keys.v` (`OptKey`, `LitKey`, `TmpKey`, fully written; about 150 lines), `LinForm.v` (data and spec evaluation, written in full), `LinearizeSig.v`, `NumStateSig.v`, `LinCertSig.v`, `ZoneSig.v`, `OctagonSig.v`, `KarrSig.v`, `PolySig.v`.
   - `Widening`: `MiningSig.v`, `PolicySig.v`, `NarrowSig.v`.
   - `Alarms`: `ChecksSig.v`, `AlarmsSig.v`.

   About 3.5k lines of statements.
2. **Mechanical conversion of the value domains.** For each file in the table of §1.1:
   - remove the monad: `f_c` becomes `f`, and `Cost.value (f_c x)` becomes `f x`;
   - delete the `*_cost` and `_equation` theorems;
   - merge the files as in §1.1;
   - ascribe the result to the new `*Sig.v` types.

   A proof that does not survive in 15 minutes becomes `Admitted` with a `(* CONVERT: <old theorem name> *)` tag, so the session knows which proof to port. This is about 16k lines in, about 13k out. `KnownBits` and `Wrapped` may run until batch 2 starts, because only S4 needs them proved.
3. **Delete** `DomainsSignedBounds*`, `DomainsSignedOrder.v`, `DomainsSignedWiden.v`, `DomainsTnumCost.v`, `DomainsState.v`, `DomainsRelational.v` and `DomainsTactics.v`, and their tests.
4. **Exact replacements.** Port the `tests/Domains/*` examples whose expected values still hold, under the new names.

### 7.2 Sessions

Each session owns the listed paths and the matching `tests/<Package>/<Name>Test.v`. No session edits a `*Sig.v` file.

| Id | Batch | Owned paths | Closes | Estimate |
|---|---|---|---|---|
| **S1 Value core** | 1 | `Domains/{Harness,Tagged,BitsLang,ZLang,Const,Sign,Congruence,Product,Reduced,Translate}.v` | `HARNESS_PLAN`; `TaggedTable` soundness; the `BitsLangTime` contracts (33 cases); every `CONVERT` admit and time layer of Const, Sign and Congruence; the Product and Reduced laws and `T_red_le` | 3.9k lines, 5 h |
| **S2 Intervals and widening** | 1 | `Domains/{Thresholds,Interval,IntervalOps,IntervalBack}.v`, `Widening/{Mining,Policy,Narrow}.v` | `THRESHOLDS_PLAN`; `INTERVAL_PLAN` (threshold `wrank` and the word table); `head_strict_steps`, `head_updates_le`, `of_wto_cuts`; `narrow_pass_*` | 3.9k lines, 5 h |
| **S3 States and alarms** | 1 | `States/{Env,Partition,Disjunction,RelEnv}.v`, `Alarms/{Alarms,BitsChecks}.v` | `ENV_PLAN`; the Partition and Disjunction plans (`compact_covers`, Disj `wrank_widen`); `RelEnv` laws; `no_alarm_safe`, `alarm_at_top`, `alarm_on_exact_error`; `BitsChecks` (it uses `RANGE_QUERY` only through its signature) | 3.8k lines, 5 h |
| **S4 Bit-level domains** | 2 | `Domains/{KnownBits,KnownBitsOps,KnownBitsBack,Wrapped,WrappedOps,Reducers}.v` | the `CONVERT` admits left over from groundwork; the time layers (`tnum_mul` O(w²), the shift stages); Wrapped `wrank_widen` (from `DomainsWrappedRank`); the three reducers' `reduce_sound`; the `RANGE_QUERY` instances for Interval, Wrapped and KnownBits | 4.0k lines, 5 h |
| **S5 DBM domains** | 2 | `Relational/{Linearize,Zone,Octagon}.v` | `ZLinearize`, `BitsLinearizeU`, `BitsLinearizeS` (`wrap_into_id`, `lin_sound`, `atoms_sound`); `ZONE_PLAN` including `close_shortest` and `bits_close_le`; `OCTAGON_PLAN` soundness and time, then `close_strong`, `incr_close_eq`, `tclose_tight` in that order | 5.0k lines, 6 h |
| **S6 Linear-algebra domains** | 2 | `Relational/{LinCert,Karr,Poly}.v` | `check_entails_sound`, `check_entails_sound_Q`, `check_empty_sound`; the `KARR_PLAN` soundness lemmas plus `leb_complete_Q` and `leb_trans`; the `POLY_PLAN` soundness lemmas, `fm_step_mults`, the FM time lemmas, then `fm_complete_Q` | 5.0k lines, 6 h |

Ordering:
- Batches 1 and 2 meet only through `*Sig.v` statements. A batch-2 session may use a batch-1 lemma before it is proved, because it is a `Parameter` in a `PLAN`.
- S4 is in batch 2 because its proofs are the longest groundwork conversion.
- S5 and S6 are in batch 2 because they are the largest new mathematics and benefit from the proved `Env` and `LinForm` for their tests.

If the master allots fewer than six sessions to this area, cut in this order:
1. S6's polyhedra; Karr stays.
2. S5's tight closure and incremental-closure precision.
3. S4's reducers.
4. S3's Partition and Disjunction.

### 7.3 What remains after both batches

- **Float:** needs the owner's axiom decision (§6). Then a port of about 2.5k lines.
- **Precision and cost lemmas that may slip:** each has a soundness-free fallback already in place.
  - `bareiss_minor` (Karr time bound);
  - `fm_complete_Q` (polyhedra `leb_trans`);
  - `tclose_tight`;
  - `bits_close_le`.
- **Polyhedra producers:** the exact hull by Benoy, King & Mesnard, and a simplex-based `entail_cert`. Simplex is Bland's rule under `loop_fuel` with fuel `binom (m+n) n`, which is the tight pivot bound for that rule (Avis & Chvátal 1978), with an arithmetic bound from the Hadamard lemma. Both are checked by the same `LinCert`, so soundness is unchanged.
- **Octagon variable packing** (Astrée) and decomposition (Singh, Püschel & Vechev, PLDI 2015).
- **`Memory/Footprint.v` conversion.**
- **Modular-arithmetic Karr** (Müller-Olm & Seidl, TOPLAS 2007), as an alternative to the wrap fallback.

## 8. Risks

1. **`TimeFun` on nested `term` recursion.** It blocks the `Env` time layer. The fallback is mutual `term`/`terms`.
2. **The Z cost model is undecided.** Every bound above carries (ℓ+1) factors that change form if the core prices Z operations as O(1).
3. **Float versus "no axioms".** Section 6 needs an owner decision.
4. **`leb_trans` for Karr and polyhedra needs a completeness proof** (`leb_complete_Q`, `fm_complete_Q`). These are standard textbook proofs but the largest single lemmas in this area.
5. **The FM producer blows up.** It is tight but doubly exponential, so polyhedra are practical only in small dimension until the simplex producer lands. Soundness is unaffected.
6. **Groundwork conversion volume.** About 16k lines are mechanically converted. Unconverted proofs land as tagged `Admitted` and are routed to S1, S2 and S4.
7. **Cross-team names.** My lemmas depend on these being fixed by the core and engines architects:
   - core `MAP.merge`/`forall2b` with higher-order time contracts;
   - core `WIDENING` (`wparam`, `wrank`, `wrank_widen`, `wrank_widen_le`, `widen_stable`);
   - `Wto.heads` and its cycle-cut corollary;
   - `SYSTEM.post_solution`, `check`, `check_sound`;
   - the framework theorem that a certified post-solution covers the reachable states.

### Critical files for implementation
- /home/nandhagk/Projects/galois-integrate/theories/Domains/DomainsTransfer.v (the harness being replaced; its `combine_backward` and `forward_sound` proofs carry over)
- /home/nandhagk/Projects/galois-integrate/theories/Domains/DomainsEnv.v and /home/nandhagk/Projects/galois-integrate/theories/Lattice/LatticeEnv.v (the source of `States/Env.v`)
- /home/nandhagk/Projects/galois-integrate/theories/Domains/DomainsThreshold.v and /home/nandhagk/Projects/galois-integrate/theories/Domains/DomainsInterval.v (thresholds and the widening rank)
- /home/nandhagk/Projects/galois-integrate/theories/Bits/BitsOp.v (the `BitsLang` instance)
- /home/nandhagk/Projects/galois-integrate/theories/Graph/GraphCheckWto.v (`of_wto_cuts`)
- /home/nandhagk/Projects/argent/docs/design.md (sections 2, 4 and 5: `TimeFun` rules, loops, the time-layer convention)
- /home/nandhagk/Projects/galois-archive/2026-11-11/legacy/theories/Float/FloatInterval.v and FloatOps.v (what Float keeps)
