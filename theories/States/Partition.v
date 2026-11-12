(** * Token-partitioned states

    A capped list of labelled states represents their union.
    For example, a join combines states carrying the same token.
    Builds on: PartitionSig, StateSig and LatticeSig. *)

From Stdlib Require Import List NArith Arith Bool Lia.
From Argent Require Import Time Tactics Std.
From Galois.Base Require Import KeySig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.States Require Import StateSig DisjunctionSig PartitionSig.
Import List.ListNotations.
Local Open Scope nat_scope.

(** The tail fitting operation adds at most one part to its prefix. *)
Lemma fit_tail_length {K A} (bot : A) (join : A -> A -> A) n
    (xs : list (option K * A)) : length (fit_tail bot join n xs) <= S n.
Proof.
  revert xs.
  induction n as [|n IH]; intros [|x xs]; simpl; try lia.
  specialize (IH xs); lia.
Qed.

(** Fitting parts produces a list inside the requested cap. *)
Lemma fit_parts_inside {K A} (bot : A) (join : A -> A -> A) n
    (xs : list (option K * A)) : Nat.leb (length (fit_parts bot join n xs)) n = true.
Proof.
  destruct n as [|n]; simpl; auto.
  destruct (Nat.leb (length xs) (S n)) eqn:Hfit; auto.
  apply Nat.leb_le, fit_tail_length.
Qed.

(** Absorption keeps the number of parts. *)
Lemma absorb_length {K A} (eqb : K -> K -> bool) (leb : A -> A -> bool)
    (bot : A) (join widen : A -> A -> A) strays fresh old :
    length (absorb eqb leb bot join widen strays fresh old) = length old.
Proof.
  revert strays.
  induction old as [|q rest IH]; simpl; auto.
  intros strays.
  destruct (leb (snd q) bot); simpl; now rewrite IH.
Qed.

Module PartitionCode (X Tk : KEY_OPS) (L : LANG_OPS) (V : VALUE_DOMAIN_OPS L)
    (S : STATE_DOMAIN_OPS X L V) (C : CAP) <: PARTITION_OPS X Tk L V S C.
  Definition t := capped (option Tk.t * S.t) C.k.
  Definition fit (ps : list (option Tk.t * S.t)) : t :=
    exist _ (fit_parts S.bot S.join C.k ps) (fit_parts_inside S.bot S.join C.k ps).
  Definition leb (a b : t) : bool := forallb (fun q => S.leb (snd q) S.bot ||
    existsb (fun r => S.leb (snd q) (snd r)) (proj1_sig b)) (proj1_sig a).
  Definition bot : t := exist _ [] eq_refl.
  Definition is_bot (a : t) : bool := forallb (fun q => S.leb (snd q) S.bot) (proj1_sig a).
  Definition join (a b : t) : t := fit (merge_parts Tk.eqb S.join (proj1_sig a) (proj1_sig b)).
  Definition top : t := fit [(None, S.top)].
  Definition meet (a b : t) : t := fit (flat_map (fun q =>
    map (fun r => (fst q, S.meet (snd q) (snd r))) (proj1_sig b)) (proj1_sig a)).
  Definition wparam := S.wparam.
  Definition widen (p : wparam) (a b : t) : t.
  Proof.
    destruct a as [old Hbound].
    destruct (leb b (exist _ old Hbound)).
    - exact (exist _ old Hbound).
    - destruct (is_bot (exist _ old Hbound)).
      + exact b.
      + pose (fresh := fresh_parts S.leb S.bot old (proj1_sig b)).
        refine (exist _ (absorb Tk.eqb S.leb S.bot S.join (S.widen p)
          (stray_parts Tk.eqb S.leb S.bot old fresh) fresh old) _).
        now rewrite absorb_length.
  Defined.
  Definition narrow (a _ : t) : t := a.
  Definition inject (k : Tk.t) (s : S.t) : t := fit [(Some k, s)].
  Definition merge (k : Tk.t) (a : t) : t :=
    inject k (collapse_with S.bot S.join (map snd (proj1_sig a))).
  Definition retag := merge.
  Definition map_bounded (f : S.t -> S.t) (a : t) : t.
  Proof.
    destruct a as [xs Hbound].
    refine (exist _ (map (fun q => (fst q, f (snd q))) xs) _).
    now rewrite length_map.
  Defined.
  Definition assign x e (a : t) := map_bounded (S.assign x e) a.
  Definition havoc x (a : t) := map_bounded (S.havoc x) a.
  Definition assume g es (a : t) := map_bounded (S.assume g es) a.
  Definition eval e (a : t) :=
    fold_left (fun v q => V.join v (S.eval e (snd q))) (proj1_sig a) V.bot.
End PartitionCode.

Module Specif.
  TimeFun proj1_sig.
End Specif.

Module Partition (X Tk : KEY) (L : LANG) (V : VALUE_DOMAIN L)
    (S : STATE_DOMAIN X L V) (C : POS_CAP) <: PARTITION X Tk L V S C.
  Include PartitionCode X Tk L V S C.
  Definition gamma (d : t) (st : X.t -> L.val) : Prop :=
    Exists (fun q => S.gamma (snd q) st) (proj1_sig d).
  Definition wrank (p : wparam) (d : t) : nat :=
    fold_right Nat.add 0 (map (fun q =>
      if S.leb (snd q) S.bot then 0 else S.wrank p (snd q)) (proj1_sig d)).
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
  Lemma gamma_parts : forall a st,
    gamma a st <-> Exists (fun q => S.gamma (snd q) st) (proj1_sig a).
  Proof. Admitted. (* STUB *)
  Lemma leb_cover : forall a b, leb a b = forallb (fun q => S.leb (snd q) S.bot ||
    existsb (fun r => S.leb (snd q) (snd r)) (proj1_sig b)) (proj1_sig a).
  Proof. Admitted. (* STUB *)
  Lemma is_bot_parts : forall a,
    is_bot a = forallb (fun q => S.leb (snd q) S.bot) (proj1_sig a).
  Proof. Admitted. (* STUB *)
  Lemma bot_raw : proj1_sig bot = [].
  Proof. Admitted. (* STUB *)
  Lemma top_raw : proj1_sig top = [(None, S.top)].
  Proof. Admitted. (* STUB *)
  Lemma join_parts : forall a b, proj1_sig (join a b) =
    fit_parts S.bot S.join C.k (merge_parts Tk.eqb S.join (proj1_sig a) (proj1_sig b)).
  Proof. Admitted. (* STUB *)
  Lemma wrank_parts : forall p a, wrank p a = fold_right Nat.add 0 (map (fun q =>
    if S.leb (snd q) S.bot then 0 else S.wrank p (snd q)) (proj1_sig a)).
  Proof. Admitted. (* STUB *)
  Lemma inject_raw : forall k s, proj1_sig (inject k s) = [(Some k, s)].
  Proof. Admitted. (* STUB *)
  Lemma merge_eq : forall k a,
    merge k a = inject k (collapse_with S.bot S.join (map snd (proj1_sig a))).
  Proof. Admitted. (* STUB *)
  Lemma retag_eq : forall k a, retag k a = merge k a.
  Proof. Admitted. (* STUB *)
  Lemma gamma_inject : forall k s st, S.gamma s st -> gamma (inject k s) st.
  Proof. Admitted. (* STUB *)
  Lemma merge_sound : forall k a st, gamma a st -> gamma (merge k a) st.
  Proof. Admitted. (* STUB *)
End Partition.

Module PartitionT (X Tk : KEY_T) (L : LANG_T) (V : VALUE_DOMAIN_T L)
    (S : STATE_DOMAIN_T X L V) (JS : JOIN_SIZE S) (JU : JOIN_UNITS X L V S)
    (C : POS_CAP) <: PARTITION_ALL X Tk L V S JS JU C.
  Module Plain := Partition X Tk L V S C.
  Include Plain.
  TimeFun fit.
  TimeFun leb.
  TimeFun is_bot.
  TimeFun join.
  TimeFun top.
  TimeFun widen.
  TimeFun narrow.
  TimeFun inject.
  TimeFun merge.
  TimeFun retag.
  TimeFun map_bounded.
  TimeFun assign.
  TimeFun havoc.
  TimeFun assume.
  TimeFun eval.

  Definition size (a : t) : nat := parts_size Tk.bits S.size (proj1_sig a).
  Definition wunits (a : t) : nat := parts_units S.wunits (proj1_sig a).
  Definition wsize : wparam -> nat := S.wsize.
  Definition assign_work (x : X.t) (e : term L.op X.t) (a : t) : nat :=
    fold_right Nat.add 0%nat (map (fun q => S.assign_work x e (snd q) + 1) (proj1_sig a)).
  Definition havoc_work (x : X.t) (a : t) : nat :=
    fold_right Nat.add 0%nat (map (fun q => S.havoc_work x (snd q) + 1) (proj1_sig a)).
  Definition assume_work (g : L.guard) (es : list (term L.op X.t)) (a : t) : nat :=
    fold_right Nat.add 0%nat
      (map (fun q => S.assume_work g es (snd q) + 1) (proj1_sig a)).
  Definition eval_work (e : term L.op X.t) (a : t) : nat :=
    fold_right Nat.add 0%nat (map (fun q =>
      S.eval_work e (snd q) + V.size (S.eval e (snd q)) + 1) (proj1_sig a)).
  Definition c_lat : N := 1%N. (* STUB *)
  Definition c_state : N := 1%N. (* STUB *)
  Definition c_partition : N := 1%N. (* STUB *)

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
  Lemma T_assign_le : forall x e a,
    (T_assign x e a <= c_state * N.of_nat (assign_work x e a + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_havoc_le : forall x a,
    (T_havoc x a <= c_state * N.of_nat (havoc_work x a + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_assume_le : forall g es a,
    (T_assume g es a <= c_state * N.of_nat (assume_work g es a + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_eval_le : forall e a,
    (T_eval e a <= c_state * N.of_nat (eval_work e a + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma size_parts : forall a, size a = parts_size Tk.bits S.size (proj1_sig a).
  Proof. Admitted. (* STUB *)
  Lemma wunits_parts : forall a, wunits a = parts_units S.wunits (proj1_sig a).
  Proof. Admitted. (* STUB *)
  Lemma wsize_component : forall p, wsize p = S.wsize p.
  Proof. Admitted. (* STUB *)
  Lemma assign_work_parts : forall x e a, assign_work x e a =
    fold_right Nat.add 0%nat (map (fun q => S.assign_work x e (snd q) + 1) (proj1_sig a)).
  Proof. Admitted. (* STUB *)
  Lemma havoc_work_parts : forall x a, havoc_work x a =
    fold_right Nat.add 0%nat (map (fun q => S.havoc_work x (snd q) + 1) (proj1_sig a)).
  Proof. Admitted. (* STUB *)
  Lemma assume_work_parts : forall g es a, assume_work g es a =
    fold_right Nat.add 0%nat
      (map (fun q => S.assume_work g es (snd q) + 1) (proj1_sig a)).
  Proof. Admitted. (* STUB *)
  Lemma eval_work_parts : forall e a, eval_work e a = fold_right Nat.add 0%nat (map (fun q =>
    S.eval_work e (snd q) + V.size (S.eval e (snd q)) + 1) (proj1_sig a)).
  Proof. Admitted. (* STUB *)
  Lemma T_inject_le : forall k s,
    (T_inject k s <= c_partition * N.of_nat (Tk.bits k + S.size s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_merge_le : forall k a,
    (T_merge k a <= c_partition * N.of_nat (Tk.bits k + size a + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_retag_le : forall k a,
    (T_retag k a <= c_partition * N.of_nat (Tk.bits k + size a + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma join_size : forall a b,
    (N.of_nat (size (join a b)) <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma join_wunits : forall a b,
    (N.of_nat (wunits (join a b)) <= c_lat * N.of_nat (wunits a + wunits b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma merge_size : forall k a,
    (N.of_nat (size (merge k a)) <= c_partition * N.of_nat (Tk.bits k + size a + 1))%N.
  Proof. Admitted. (* STUB *)

  Definition k_partition : N := 1%N. (* STUB *)
  Definition route_time (p : S.wparam) (old new : list (option Tk.t * S.t)) : N :=
    let fresh := fresh_parts S.leb S.bot old new in
    (T_fresh_parts S.leb S.T_leb S.bot old new +
     T_stray_parts Tk.eqb Tk.T_eqb S.leb S.T_leb S.bot old fresh +
     T_absorb Tk.eqb Tk.T_eqb S.leb S.T_leb S.bot S.join S.T_join
       (S.widen p) (S.T_widen p) (stray_parts Tk.eqb S.leb S.bot old fresh) fresh old)%N.
  Definition eval_joins (e : term L.op X.t) (ps : list (option Tk.t * S.t)) : N :=
    fst (fold_left (fun acc q =>
      ((fst acc + V.T_join (snd acc) (S.eval e (snd q)) + 1)%N,
       V.join (snd acc) (S.eval e (snd q)))) ps (0%N, V.bot)).

  Lemma F1_assign : forall x e a, proj1_sig (assign x e a) =
    map (fun q => (fst q, S.assign x e (snd q))) (proj1_sig a).
  Proof. Admitted. (* STUB *)
  Lemma F2_havoc : forall x a, proj1_sig (havoc x a) =
    map (fun q => (fst q, S.havoc x (snd q))) (proj1_sig a).
  Proof. Admitted. (* STUB *)
  Lemma F3_assume : forall g es a, proj1_sig (assume g es a) =
    map (fun q => (fst q, S.assume g es (snd q))) (proj1_sig a).
  Proof. Admitted. (* STUB *)
  Lemma F4_eval : forall e a,
    eval e a = fold_left (fun v q => V.join v (S.eval e (snd q))) (proj1_sig a) V.bot.
  Proof. Admitted. (* STUB *)
  Lemma F5_widen : forall p a b, proj1_sig (widen p a b) =
    if leb b a then proj1_sig a else
    if is_bot a then proj1_sig b else
    let old := proj1_sig a in
    let fresh := fresh_parts S.leb S.bot old (proj1_sig b) in
    absorb Tk.eqb S.leb S.bot S.join (S.widen p)
      (stray_parts Tk.eqb S.leb S.bot old fresh) fresh old.
  Proof. Admitted. (* STUB *)
  Lemma F6_narrow : forall a b, narrow a b = a.
  Proof. Admitted. (* STUB *)
  Lemma F7_merge_parts_length : forall ps qs,
    length (merge_parts Tk.eqb S.join ps qs) <= length ps + length qs.
  Proof. Admitted. (* STUB *)
  Lemma F8_collapse_size : forall xs, length xs <= 2 * C.k + 1 ->
    (N.of_nat (S.size (collapse_with S.bot S.join xs)) <= k_partition * N.of_nat
      (fold_right Nat.add 0%nat (map S.size xs) + length xs + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma F9_collapse_units : forall xs, length xs <= 2 * C.k + 1 ->
    (N.of_nat (S.wunits (collapse_with S.bot S.join xs)) <= k_partition * N.of_nat
      (fold_right Nat.add 0%nat (map S.wunits xs) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma F10_merge_parts_size : forall ps qs,
    length ps <= C.k -> length qs <= C.k ->
    (N.of_nat (parts_size Tk.bits S.size
      (merge_parts Tk.eqb S.join ps qs)) <= k_partition * N.of_nat
        (parts_size Tk.bits S.size ps + parts_size Tk.bits S.size qs + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma F11_merge_parts_units : forall ps qs,
    length ps <= C.k -> length qs <= C.k ->
    (N.of_nat (parts_units S.wunits
      (merge_parts Tk.eqb S.join ps qs)) <= k_partition * N.of_nat
        (parts_units S.wunits ps + parts_units S.wunits qs + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma F12_fit_size : forall ps, length ps <= 2 * C.k ->
    (N.of_nat (parts_size Tk.bits S.size
      (fit_parts S.bot S.join C.k ps)) <= k_partition * N.of_nat
        (parts_size Tk.bits S.size ps + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma F13_fit_units : forall (ps : list (option Tk.t * S.t)), length ps <= 2 * C.k ->
    (N.of_nat (parts_units S.wunits
      (fit_parts S.bot S.join C.k ps)) <= k_partition * N.of_nat
        (parts_units S.wunits ps + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T1_leb : forall a b,
    (T_leb a b <= k_partition *
      (fold_right N.add 0%N (map (fun q => S.T_leb (snd q) S.bot +
        fold_right N.add 0%N (map (fun r => S.T_leb (snd q) (snd r) + 1) (proj1_sig b)) + 1)
        (proj1_sig a)) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T2_is_bot : forall a,
    (T_is_bot a <= k_partition *
      (fold_right N.add 0%N (map (fun q => S.T_leb (snd q) S.bot + 1) (proj1_sig a)) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T3_join : forall a b,
    (T_join a b <= k_partition *
      (T_merge_parts Tk.eqb Tk.T_eqb S.join S.T_join (proj1_sig a) (proj1_sig b) +
       T_fit_parts S.bot S.join S.T_join C.k
         (merge_parts Tk.eqb S.join (proj1_sig a) (proj1_sig b)) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T4_merge_parts : forall ps qs, length ps <= C.k -> length qs <= C.k ->
    (T_merge_parts Tk.eqb Tk.T_eqb S.join S.T_join ps qs <= k_partition *
      N.of_nat (parts_size Tk.bits S.size ps + parts_size Tk.bits S.size qs + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T5_fit_parts : forall ps, length ps <= 2 * C.k ->
    (T_fit_parts S.bot S.join S.T_join C.k ps <= k_partition *
      N.of_nat (parts_size Tk.bits S.size ps + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T6_widen : forall p a b,
    (T_widen p a b <= k_partition *
      (T_leb b a + T_is_bot a + route_time p (proj1_sig a) (proj1_sig b) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T7_route : forall p old new,
    length old <= C.k -> length new <= C.k ->
    (route_time p old new <= k_partition * N.of_nat
      ((parts_units S.wunits old + parts_units S.wunits new + 1) * S.wsize p +
       (parts_size Tk.bits S.size old + parts_size Tk.bits S.size new + S.wsize p + 1)))%N.
  Proof. Admitted. (* STUB *)
  Lemma T8_collapse : forall xs, length xs <= 2 * C.k + 1 ->
    (T_collapse_with S.bot S.join S.T_join xs <= k_partition * N.of_nat
      (fold_right Nat.add 0%nat (map S.size xs) + length xs + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T9_merge : forall k a,
    (T_merge k a <= k_partition *
      (T_collapse_with S.bot S.join S.T_join (map snd (proj1_sig a)) +
       T_inject k (collapse_with S.bot S.join (map snd (proj1_sig a))) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T10_retag : forall k a,
    (T_retag k a <= k_partition * (T_merge k a + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T11_inject : forall k s, (T_inject k s <= k_partition)%N.
  Proof. Admitted. (* STUB *)
  Lemma T12_eval : forall e a,
    (T_eval e a <= k_partition *
      (fold_right N.add 0%N (map (fun q => S.T_eval e (snd q) + 1) (proj1_sig a)) +
       eval_joins e (proj1_sig a) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T13_eval_joins : forall e ps, length ps <= C.k ->
    (eval_joins e ps <= k_partition * N.of_nat (fold_right Nat.add 0%nat
      (map (fun q => (V.size (S.eval e (snd q)) + 1)%nat) ps) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T14_assign : forall x e a,
    (T_assign x e a <= k_partition *
      (fold_right N.add 0%N
        (map (fun q => S.T_assign x e (snd q) + 1) (proj1_sig a)) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T15_havoc : forall x a,
    (T_havoc x a <= k_partition *
      (fold_right N.add 0%N (map (fun q => S.T_havoc x (snd q) + 1) (proj1_sig a)) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T16_assume : forall g es a,
    (T_assume g es a <= k_partition *
      (fold_right N.add 0%N
        (map (fun q => S.T_assume g es (snd q) + 1) (proj1_sig a)) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T17_narrow : forall a b, (T_narrow a b <= k_partition)%N.
  Proof. Admitted. (* STUB *)
End PartitionT.
