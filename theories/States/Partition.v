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

Module PartitionClock (X Tk : KEY_T) (L : LANG_T) (V : VALUE_DOMAIN_T L)
    (S : STATE_DOMAIN_T X L V) (C : CAP).
  Include PartitionCode X Tk L V S C.
  TimeFun fit.
  TimeFun leb.
  TimeFun is_bot.
  TimeFun join.
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
End PartitionClock.

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
