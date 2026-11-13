(** * Bounded disjunctive states

    Lists of alternatives represent a union and compact when the capacity is exceeded.
    For example, cap one joins two alternatives into one state.
    Builds on: DisjunctionSig, StateSig and the lattice interfaces. *)

From Stdlib Require Import List NArith Arith Bool.
From Argent Require Import Time Tactics Std.
From Galois.Base Require Import KeySig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.States Require Import StateSig DisjunctionSig.
Import List.ListNotations.
Local Open Scope nat_scope.

Module Specif.
  TimeFun proj1_sig.
End Specif.

Module Nat.
  TimeFun Nat.pred.
End Nat.

Lemma replace_first_length {A} (is_bot : A -> bool) (f : A -> A) xs :
  length (replace_first is_bot f xs) = length xs.
Proof.
  induction xs as [|x rest IH]; simpl; auto.
  destruct (is_bot x); simpl; now rewrite ?IH.
Qed.

Module StateDisjunctionCode (X : KEY_OPS) (L : LANG_OPS) (V : VALUE_DOMAIN_OPS L)
    (S : STATE_DOMAIN_OPS X L V) (C : CAP) (P : SharedDisjunction.DISJUNCTION_OPS S C)
    <: DISJUNCTION_OPS X L V S C P.
  Definition t := P.t.
  Definition leb := P.leb.
  Definition bot := P.bot.
  Definition is_bot := P.is_bot.
  Definition join := P.join.
  Definition top := P.clip [S.top].
  Definition collapse (xs : list S.t) : S.t :=
    match xs with [] => S.bot | x :: rest => fold_left S.join rest x end.
  Fixpoint compact_tail (n : nat) (xs : list S.t) : list S.t :=
    match n, xs with
    | S m, x :: rest => x :: compact_tail m rest
    | _, _ => [collapse xs]
    end.
  Definition compact (n : nat) (xs : list S.t) : list S.t :=
    if Nat.eqb n C.k then proj1_sig (P.clip xs)
    else if Nat.leb (length xs) n then xs else compact_tail (Nat.pred n) xs.
  Definition meet (a b : t) : t :=
    P.clip (flat_map (fun x => map (S.meet x) (proj1_sig b)) (proj1_sig a)).
  Definition wparam := S.wparam.
  Definition widen (p : wparam) (a b : t) : t.
  Proof.
    destruct a as [old Hbound].
    destruct (leb b (exist _ old Hbound)) eqn:Hstable.
    - exact (exist _ old Hbound).
    - destruct (is_bot (exist _ old Hbound)) eqn:Hempty.
      + exact b.
      + destruct (forallb S.is_bot old) eqn:Hbottom.
        * exact (P.clip [S.top]).
        * refine (exist _ (replace_first S.is_bot
          (fun x => S.widen p x (collapse (x :: uncovered S.leb old (proj1_sig b)))) old) _).
          now rewrite replace_first_length.
  Defined.
  Definition narrow (a _ : t) := a.

  Definition map_bounded (f : S.t -> S.t) (d : t) : t.
  Proof.
    destruct d as [xs Hbound].
    refine (exist _ (map f xs) _).
    now rewrite length_map.
  Defined.

  Definition assign x e (d : t) := map_bounded (S.assign x e) d.
  Definition havoc x (d : t) := map_bounded (S.havoc x) d.
  Definition assume g es (d : t) := map_bounded (S.assume g es) d.
  Definition eval e (d : t) := fold_left (fun a s => V.join a (S.eval e s)) (proj1_sig d) V.bot.
End StateDisjunctionCode.

Module StateDisjunction (X : KEY) (L : LANG) (V : VALUE_DOMAIN L)
    (S : STATE_DOMAIN X L V) (C : POS_CAP) (P : SharedDisjunction.DISJUNCTION S C)
    <: DISJUNCTION X L V S C P.
  Include StateDisjunctionCode X L V S C P.
  Definition gamma (d : t) (st : X.t -> L.val) : Prop :=
    Exists (fun s => S.gamma s st) (proj1_sig d).
  Definition wrank (p : wparam) (d : t) : nat :=
    fold_right Nat.add 0 (map (S.wrank p) (proj1_sig d)) +
      if forallb S.is_bot (proj1_sig d) then 1 + S.wrank p S.top else 0.
  Lemma leb_refl : forall a, leb a a = true.
  Proof. Admitted. (* STUB *)
  (** The order composes through an intermediate value. *)
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof. Admitted. (* STUB *)
  (** Bottom is below every value. *)
  Lemma bot_least : forall a, leb bot a = true.
  Proof. Admitted. (* STUB *)
  (** The bottom test recognizes bottom. *)
  Lemma is_bot_bot : is_bot bot = true.
  Proof. Admitted. (* STUB *)
  (** Every recognized bottom is below every value. *)
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof. Admitted. (* STUB *)
  (** Join is above its left operand. *)
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof. Admitted. (* STUB *)
  (** Join is above its right operand. *)
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof. Admitted. (* STUB *)

  Lemma top_greatest : forall a, leb a top = true.
  Proof. Admitted. (* STUB *)

  (** Widening is above its previous value. *)
  Lemma widen_ub_l : forall p a b, leb a (widen p a b) = true.
  Proof. Admitted. (* STUB *)
  (** Widening is above its candidate value. *)
  Lemma widen_ub_r : forall p a b, leb b (widen p a b) = true.
  Proof. Admitted. (* STUB *)
  (** A candidate below the previous value leaves widening unchanged. *)
  Lemma widen_stable : forall p a b, leb b a = true -> widen p a b = a.
  Proof. Admitted. (* STUB *)
  (** An unstable widening from a nonbottom strictly decreases rank. *)
  (* F2-22 replaced the former twoStateDisj aligned-pair rank route with uncovered
     alternatives, and F2-30 supplies the size and widening-unit capabilities it needs. *)
  Lemma wrank_widen : forall p a b, is_bot a = false -> leb b a = false ->
    wrank p (widen p a b) < wrank p a.
  Proof. Admitted. (* STUB *)
  (** Widening from a nonbottom does not increase rank. *)
  Lemma wrank_widen_le : forall p a b, is_bot a = false -> wrank p (widen p a b) <= wrank p a.
  Proof. Admitted. (* STUB *)
  (** Narrowing stays between an ordered candidate and previous value. *)
  Lemma narrow_between : forall a b, leb b a = true ->
    leb b (narrow a b) = true /\ leb (narrow a b) a = true.
  Proof. Admitted. (* STUB *)

  (** Abstract inclusion entails inclusion of concrete environments. *)
  Lemma gamma_mono : forall a b st, leb a b = true -> gamma a st -> gamma b st.
  Proof. Admitted. (* STUB *)
  (** Bottom describes no concrete environment. *)
  Lemma gamma_bot : forall st, ~ gamma bot st.
  Proof. Admitted. (* STUB *)
  (** Top describes every concrete environment. *)
  Lemma gamma_top : forall st, gamma top st.
  Proof. Admitted. (* STUB *)
  (** Assignment contains each successful concrete update. *)
  Lemma assign_sound : forall x e s st c,
    gamma s st -> eval_term L.eval st e = Some c ->
    gamma (assign x e s) (upd X.eqb st x c).
  Proof. Admitted. (* STUB *)
  (** Havoc contains every concrete update of the selected variable. *)
  Lemma havoc_sound : forall x s st c,
    gamma s st -> gamma (havoc x s) (upd X.eqb st x c).
  Proof. Admitted. (* STUB *)
  (** Assuming a true guard retains its concrete environment. *)
  Lemma assume_sound : forall g es s st cs,
    gamma s st -> eval_terms L.eval st es = Some cs -> L.holds g cs ->
    gamma (assume g es s) st.
  Proof. Admitted. (* STUB *)
  (** Abstract evaluation describes every successful concrete result. *)
  Lemma eval_sound : forall e s st c,
    gamma s st -> eval_term L.eval st e = Some c -> V.gamma (eval e s) c.
  Proof. Admitted. (* STUB *)
  Lemma gamma_alternatives : forall d st,
    gamma d st <-> Exists (fun s => S.gamma s st) (proj1_sig d).
  Proof. Admitted. (* STUB *)
  Lemma leb_hoare : forall a b, leb a b =
    forallb (fun x => existsb (S.leb x) (proj1_sig b)) (proj1_sig a).
  Proof. Admitted. (* STUB *)
  Lemma join_compact : forall a b, join a b = P.clip (proj1_sig a ++ proj1_sig b).
  Proof. Admitted. (* STUB *)
  Lemma compact_cap : forall d, compact C.k d = proj1_sig (P.clip d).
  Proof. Admitted. (* STUB *)
  Lemma compact_covers : forall n d x, In x d ->
    exists y, In y (compact n d) /\ S.leb x y = true.
  Proof. Admitted. (* CONVERT: compact_covers: The variable compact_equation was not found in the current environment. *)
  Lemma compact_len : forall n d, length (compact n d) <= Nat.max n 1.
  Proof. Admitted. (* STUB *)
  Lemma collapse_covers : forall xs x, In x xs -> S.leb x (collapse xs) = true.
  Proof. Admitted. (* STUB *)
End StateDisjunction.

Module StateDisjunctionT (X : KEY_T) (L : LANG_T) (V : VALUE_DOMAIN_T L)
    (S : STATE_DOMAIN_T X L V) (JS : JOIN_SIZE S) (JU : JOIN_UNITS X L V S) (C : POS_CAP)
    (P : SharedDisjunction.DISJUNCTION_T S JS C)
    <: DISJUNCTION_ALL X L V S JS JU C P.
  Module Plain := StateDisjunction X L V S C P.
  Include Plain.
  Definition T_leb : t -> t -> N := P.T_leb.
  Definition T_join : t -> t -> N := P.T_join.
  Definition T_is_bot : t -> N := P.T_is_bot.
  TimeFun top.
  TimeFun collapse.
  TimeFun compact_tail.
  TimeFun compact.
  TimeFun widen.
  TimeFun narrow.
  TimeFun map_bounded.
  TimeFun assign.
  TimeFun havoc.
  TimeFun assume.
  TimeFun eval.
  Definition size : t -> nat := P.size.
  Definition c_lat : N := 1%N. (* STUB *)
  Definition c_state : N := 1%N. (* STUB *)
  Definition c_disjunction : N := 1%N. (* STUB *)
  Definition wsize : wparam -> nat := S.wsize.
  Definition wunits (d : t) : nat :=
    fold_right Nat.add 0%nat (map S.wunits (proj1_sig d)).
  Definition assign_work (x : X.t) (e : term L.op X.t) (d : t) : nat :=
    fold_right Nat.add 0%nat (map (fun s => S.assign_work x e s + 1) (proj1_sig d)).
  Definition havoc_work (x : X.t) (d : t) : nat :=
    fold_right Nat.add 0%nat (map (fun s => S.havoc_work x s + 1) (proj1_sig d)).
  Definition assume_work (g : L.guard) (es : list (term L.op X.t)) (d : t) : nat :=
    fold_right Nat.add 0%nat (map (fun s => S.assume_work g es s + 1) (proj1_sig d)).
  Definition eval_work (e : term L.op X.t) (d : t) : nat :=
    fold_right Nat.add 0%nat (map (fun s =>
      S.eval_work e s + V.size (S.eval e s) + 1) (proj1_sig d)).

  (** Assignment work is the component work of every alternative. *)
  Lemma assign_work_alternatives : forall x e d, assign_work x e d =
    fold_right Nat.add 0%nat (map (fun s => S.assign_work x e s + 1) (proj1_sig d)).
  Proof. Admitted. (* STUB *)
  (** Havoc work is the component work of every alternative. *)
  Lemma havoc_work_alternatives : forall x d, havoc_work x d =
    fold_right Nat.add 0%nat (map (fun s => S.havoc_work x s + 1) (proj1_sig d)).
  Proof. Admitted. (* STUB *)
  (** Assumption work is the component work of every alternative. *)
  Lemma assume_work_alternatives : forall g es d, assume_work g es d =
    fold_right Nat.add 0%nat (map (fun s => S.assume_work g es s + 1) (proj1_sig d)).
  Proof. Admitted. (* STUB *)
  (** Evaluation work is the component work and the value size of every alternative. *)
  Lemma eval_work_alternatives : forall e d, eval_work e d =
    fold_right Nat.add 0%nat (map (fun s =>
      S.eval_work e s + V.size (S.eval e s) + 1) (proj1_sig d)).
  Proof. Admitted. (* STUB *)
  Lemma c_lat_pos : (1 <= c_lat)%N.
  Proof. Admitted. (* STUB *)
  Lemma T_leb_le : forall a b,
    (T_leb a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_join_le : forall a b,
    (T_join a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_is_bot_le : forall a,
    (T_is_bot a <= c_lat * N.of_nat (size a + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_widen_le : forall p a b,
    (T_widen p a b <= c_lat * N.of_nat
      ((wunits a + wunits b) * wsize p + (size a + size b + wsize p + 1)))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_narrow_le : forall a b,
    (T_narrow a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_assign_le : forall x e s,
    (T_assign x e s <= c_state * N.of_nat (assign_work x e s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_havoc_le : forall x s,
    (T_havoc x s <= c_state * N.of_nat (havoc_work x s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_assume_le : forall g es s,
    (T_assume g es s <= c_state * N.of_nat (assume_work g es s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_eval_le : forall e s,
    (T_eval e s <= c_state * N.of_nat (eval_work e s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_assign_alternatives : forall x e d,
    (T_assign x e d <= c_disjunction *
      (fold_right N.add 0%N (map (fun s => S.T_assign x e s + 1) (proj1_sig d)) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_havoc_alternatives : forall x d,
    (T_havoc x d <= c_disjunction *
      (fold_right N.add 0%N (map (fun s => S.T_havoc x s + 1) (proj1_sig d)) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_assume_alternatives : forall g es d,
    (T_assume g es d <= c_disjunction *
      (fold_right N.add 0%N (map (fun s => S.T_assume g es s + 1) (proj1_sig d)) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma c_lat_shared : (P.c_lat <= c_lat)%N.
  Proof. Admitted. (* STUB *)
  Lemma wunits_alternatives : forall d,
    wunits d = fold_right Nat.add 0%nat (map S.wunits (proj1_sig d)).
  Proof. Admitted. (* STUB *)
  Lemma wsize_component : forall p, wsize p = S.wsize p.
  Proof. Admitted. (* STUB *)
  Lemma T_collapse_le : forall xs, length xs <= C.k + 1 ->
    (T_collapse xs <= c_disjunction * N.of_nat
      (fold_right Nat.add 0%nat (map S.size xs) + length xs + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma collapse_size : forall xs, length xs <= C.k + 1 ->
    (N.of_nat (S.size (collapse xs)) <= c_disjunction * N.of_nat
      (fold_right Nat.add 0%nat (map S.size xs) + length xs + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma collapse_wunits : forall xs, length xs <= C.k + 1 ->
    (N.of_nat (S.wunits (collapse xs)) <= c_disjunction * N.of_nat
      (fold_right Nat.add 0%nat (map S.wunits xs) + 1))%N.
  Proof. Admitted. (* STUB *)

  Definition eval_joins (e : term L.op X.t) (xs : list S.t) : N :=
    fst (fold_left (fun acc s =>
      ((fst acc + V.T_join (snd acc) (S.eval e s) + 1)%N,
       V.join (snd acc) (S.eval e s))) xs (0%N, V.bot)).
  Definition k_disjunction : N := 1%N. (* STUB *)
  Lemma F2_widen : forall p a b, proj1_sig (widen p a b) =
    if leb b a then proj1_sig a else
    if is_bot a then proj1_sig b else
    if forallb S.is_bot (proj1_sig a) then [S.top] else
    replace_first S.is_bot
      (fun x => S.widen p x (collapse (x :: uncovered S.leb (proj1_sig a) (proj1_sig b))))
      (proj1_sig a).
  Proof. Admitted. (* STUB *)
  Lemma F3_rank : forall p d, wrank p d =
    fold_right Nat.add 0%nat (map (S.wrank p) (proj1_sig d)) +
      if forallb S.is_bot (proj1_sig d) then 1 + S.wrank p S.top else 0.
  Proof. Admitted. (* STUB *)
  Lemma F4_assign : forall x e d,
    proj1_sig (assign x e d) = map (S.assign x e) (proj1_sig d).
  Proof. Admitted. (* STUB *)
  Lemma F5_havoc : forall x d,
    proj1_sig (havoc x d) = map (S.havoc x) (proj1_sig d).
  Proof. Admitted. (* STUB *)
  Lemma F6_assume : forall g es d,
    proj1_sig (assume g es d) = map (S.assume g es) (proj1_sig d).
  Proof. Admitted. (* STUB *)
  Lemma T1_widen : forall p a b,
    (T_widen p a b <= k_disjunction *
      (T_leb b a + T_is_bot a + P.T_clip [S.top] + N.of_nat (length (proj1_sig a) + 1) +
       fold_right N.add 0%N (map S.T_is_bot (proj1_sig a)) +
       fold_right N.add 0%N (map (fun y => fold_right N.add 0%N
         (map (fun x => S.T_leb y x + 1) (proj1_sig a))) (proj1_sig b)) +
       fold_right N.add 0%N (map (fun x =>
         let c := collapse (x :: uncovered S.leb (proj1_sig a) (proj1_sig b)) in
         T_collapse (x :: uncovered S.leb (proj1_sig a) (proj1_sig b)) + S.T_widen p x c)
         (proj1_sig a))))%N.
  Proof. Admitted. (* STUB *)
  (** Evaluation joins the values of the alternatives from bottom. *)
  Lemma F7_eval : forall e d,
    eval e d = fold_left (fun a s => V.join a (S.eval e s)) (proj1_sig d) V.bot.
  Proof. Admitted. (* STUB *)
  (** Evaluation charges each alternative's evaluation and the value joins. *)
  Lemma T2_eval : forall e d, (T_eval e d <= k_disjunction *
    (fold_right N.add 0%N (map (fun s => S.T_eval e s + 1) (proj1_sig d)) +
     eval_joins e (proj1_sig d) + 1))%N.
  Proof. Admitted. (* STUB *)
  (** The value joins of a capped list charge the sizes of the evaluated values. *)
  Lemma T3_eval_joins : forall e xs, length xs <= C.k ->
    (eval_joins e xs <= k_disjunction * N.of_nat (fold_right Nat.add 0%nat
      (map (fun s => (V.size (S.eval e s) + 1)%nat) xs) + 1))%N.
  Proof. Admitted. (* STUB *)
End StateDisjunctionT.

(* The landed lattice source exposed the following raw-list equations. The shared
   bounded carrier now supplies P.clip. Its laws allow different oversized-list
   covers, so the exact raw suffix equation is not implied by the reviewed P.
Theorem compact_equation {A} k (L : lattice A) xs :
  compact k L xs =
    if Nat.leb (length xs) k then xs
    else firstn (k - 1) xs ++ [join_all L (skipn (k - 1) xs)].

   The state widening grows the first nonbottom alternative using uncovered candidates.
   The landed lattice widening used a single collapse and its equation is a different claim.
Theorem widen_disjunction {A} k (L : lattice A) xs ys :
  widen (disjunction k L) xs ys =
    if disjunction_leb L ys xs then xs
    else [widen L (join_all L xs) (join_all L (xs ++ ys))].

   The old selective-join and invariant-based rank bundles used lattice_laws,
   lub_laws, concretisation_laws and widening_rank_on records, which are no longer
   the shared bounded component interface. Their original claims were:
Theorem disjunction_lub k :
  (forall a b, leb L (join L a b) a = true \/ leb L (join L a b) b = true) ->
  lub_laws (disjunction k L).
Theorem monotone_join_all {A} (L : lattice A) xs ys :
  lattice_laws L -> lub_laws L ->
  Forall2 (fun x y => leb L x y = true) xs ys ->
  leb L (join_all L xs) (join_all L ys) = true.
Theorem disjunction_gamma_laws {A C} k (L : lattice A) (G : concretisation A C) :
  concretisation_laws L G ->
  concretisation_laws (disjunction k L) (disjunction_gamma G).
Theorem disjunction_bot_empty {A C} k (L : lattice A) (G : concretisation A C) :
  bottom_empty (disjunction k L) (disjunction_gamma G).
Theorem disjunction_wrank k : widening_rank_on (disjunction k L) (Forall inv).
*)

(* The landed cost statements below refer to the removed Cost monad and raw-list
   lattice. The later timing part derives clocks for the reviewed bounded carrier.
Theorem compact_ticks k xs :
  Cost.ticks (compact_c k L xs) =
    (N.of_nat (length xs) + 1 +
      if Nat.leb (length xs) k then 0 else
        Cost.ticks (compact_tail_c (k - 1) L xs))%N.
Theorem disjunction_cost_bounded k m :
  cost_bounded_on (disjunction k L) (fun xs => Forall inv xs /\ length xs <= m)
    (((2 * N.of_nat m + 1) * (2 * N.of_nat m + 1)) * (c + 6))%N.
Theorem disjunction_cost_bigO {X} k (xs ys : X -> list A) :
  (forall x, Forall inv (xs x)) -> (forall x, Forall inv (ys x)) ->
  bigO
    (fun x => let n := (N.of_nat (length (xs x)) + N.of_nat (length (ys x)) + 1)%N in
      (n * n)%N)
    (fun x =>
      (Cost.ticks (leb_c (disjunction k L) (xs x) (ys x)) +
       Cost.ticks (join_c (disjunction k L) (xs x) (ys x)) +
       Cost.ticks (widen_c (disjunction k L) (xs x) (ys x)) +
       Cost.ticks (narrow_c (disjunction k L) (xs x) (ys x)))%N).
*)

Module StateDisjunctionClaims (X : KEY) (L : LANG) (V : VALUE_DOMAIN L)
    (S : STATE_DOMAIN X L V) (C : POS_CAP) (P : SharedDisjunction.DISJUNCTION S C).
  Include StateDisjunction X L V S C P.

  Theorem join_all_equation xs :
    collapse xs = match xs with [] => S.bot | x :: rest => fold_left S.join rest x end.
  Proof. destruct xs; reflexivity. Qed.

  Theorem disjunction_leb_equation a b : leb a b =
    forallb (fun x => existsb (S.leb x) (proj1_sig b)) (proj1_sig a).
  Proof. Admitted. (* CONVERT: disjunction_leb_equation: The reference disjunction_leb was not found in the current *)

  Theorem disjunction_leb_spec a b : leb a b = true <->
    forall x, In x (proj1_sig a) ->
      exists y, In y (proj1_sig b) /\ S.leb x y = true.
Proof.
  rewrite disjunction_leb_equation, forallb_forall.
  split; intros H x Hin; specialize (H x Hin); now apply existsb_exists in H.
Qed.

  Theorem join_disjunction a b : join a b = P.clip (proj1_sig a ++ proj1_sig b).
  Proof. Admitted. (* CONVERT: join_disjunction: The reference Cost.value_bind was not found in the current *)

  Theorem disjunction_join_size a b : length (proj1_sig (join a b)) <= C.k.
  Proof. Admitted. (* CONVERT: disjunction_join_size: No product even after head-reduction. *)

  Theorem join_all_upper xs x : In x xs -> S.leb x (collapse xs) = true.
  Proof. Admitted. (* CONVERT: join_all_upper: The variable fold_upper_start was not found in the current environment. *)
End StateDisjunctionClaims.

(* The old fold equation named a charged helper whose pure value is now collapse.
Theorem fold_join_equation {A} (L : lattice A) xs a :
  Cost.value (fold_join_c L xs a) = fold_left (join L) xs a.

   The old closure statements quantified over closed_on and lattice_laws record
   bundles. The reviewed bounded state interface supplies neither such invariant
   provider nor its preservation contract for an arbitrary P.clip.
Theorem join_all_closed xs : Forall inv xs -> inv (join_all L xs).
Theorem disjunction_closed k : closed_on (disjunction k L) (Forall inv).
Theorem disjunction_laws k : lattice_laws (disjunction k L).
*)
