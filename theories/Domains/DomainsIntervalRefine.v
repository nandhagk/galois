(** * Interval operand refinements

    Backward arithmetic intersects operands with the inverse endpoint constraints.
    For example, assuming x < 10 tightens the upper endpoint of x to nine.
    Builds on: DomainsInterval and the public Bits wrapping laws. *)

From Stdlib Require Import ZArith List Bool Lia.
From Galois.Lattice Require Import LatticeCore.
From Galois.Bits Require Import BitsWord.
From Galois.Domains Require Import DomainsBound DomainsThreshold DomainsInterval.

Local Open Scope Z_scope.

Definition interval_swap (p : interval * interval) : interval * interval := (snd p, fst p).

Definition interval_assume_equal (a b : interval) : interval * interval :=
  (interval_meet a b, interval_meet b a).

(** Equality retains a common concrete word in both operands. *)
Theorem interval_assume_equal_sound w a b z :
  interval_pgamma w a z -> interval_pgamma w b z ->
  interval_pgamma w (fst (interval_assume_equal a b)) z /\
  interval_pgamma w (snd (interval_assume_equal a b)) z.
Proof.
  intros Ha Hb. split; apply interval_meet_sound; assumption.
Qed.

Definition interval_assume_ult (a b : interval) : interval * interval :=
  match interval_finite a, interval_finite b with
  | Some (la, _), Some (_, hb) =>
    (interval_meet a (Itv NegInf (Fin (hb - 1))),
     interval_meet b (Itv (Fin (la + 1)) PosInf))
  | _, _ => (a, b)
  end.

(** Strict unsigned refinement retains every pair satisfying the comparison. *)
Theorem interval_assume_ult_sound wa wb a b x y :
  interval_pgamma wa a x -> interval_pgamma wb b y -> x < y ->
  interval_pgamma wa (fst (interval_assume_ult a b)) x /\
  interval_pgamma wb (snd (interval_assume_ult a b)) y.
Proof.
  intros Ha Hb Hlt. unfold interval_assume_ult.
  destruct (interval_finite a) as [[la ha]|] eqn:Hfa;
    destruct (interval_finite b) as [[lb hb]|] eqn:Hfb; cbn; try tauto.
  pose proof (interval_finite_sound wa a la ha x Ha Hfa) as Hax.
  pose proof (interval_finite_sound wb b lb hb y Hb Hfb) as Hby.
  split; apply interval_meet_sound; try assumption.
  - split; [exact (proj1 Ha)|]. cbn. split; [reflexivity|apply Z.leb_le; lia].
  - split; [exact (proj1 Hb)|]. cbn. split; [apply Z.leb_le; lia|reflexivity].
Qed.

Definition interval_assume_ule (a b : interval) : interval * interval :=
  match interval_finite a, interval_finite b with
  | Some (la, _), Some (_, hb) =>
    (interval_meet a (Itv NegInf (Fin hb)), interval_meet b (Itv (Fin la) PosInf))
  | _, _ => (a, b)
  end.

(** Non-strict unsigned refinement retains every pair satisfying the comparison. *)
Theorem interval_assume_ule_sound wa wb a b x y :
  interval_pgamma wa a x -> interval_pgamma wb b y -> x <= y ->
  interval_pgamma wa (fst (interval_assume_ule a b)) x /\
  interval_pgamma wb (snd (interval_assume_ule a b)) y.
Proof.
  intros Ha Hb Hle. unfold interval_assume_ule.
  destruct (interval_finite a) as [[la ha]|] eqn:Hfa;
    destruct (interval_finite b) as [[lb hb]|] eqn:Hfb; cbn; try tauto.
  pose proof (interval_finite_sound wa a la ha x Ha Hfa) as Hax.
  pose proof (interval_finite_sound wb b lb hb y Hb Hfb) as Hby.
  split; apply interval_meet_sound; try assumption.
  - split; [exact (proj1 Ha)|]. cbn. split; [reflexivity|apply Z.leb_le; lia].
  - split; [exact (proj1 Hb)|]. cbn. split; [apply Z.leb_le; lia|reflexivity].
Qed.

(** Equality refinement lies below each original operand. *)
Theorem interval_assume_equal_lower ts a b :
  leb (interval_lattice ts) (fst (interval_assume_equal a b)) a = true /\
  leb (interval_lattice ts) (snd (interval_assume_equal a b)) b = true.
Proof.
  split; apply interval_meet_lower_left.
Qed.

(** Strict comparison refinement lies below each original operand. *)
Theorem interval_assume_ult_lower ts a b :
  leb (interval_lattice ts) (fst (interval_assume_ult a b)) a = true /\
  leb (interval_lattice ts) (snd (interval_assume_ult a b)) b = true.
Proof.
  unfold interval_assume_ult.
  destruct (interval_finite a) as [[la ha]|]; destruct (interval_finite b) as [[lb hb]|];
    split; try apply interval_meet_lower_left; apply (leb_refl (interval_laws ts)).
Qed.

(** Non-strict comparison refinement lies below each original operand. *)
Theorem interval_assume_ule_lower ts a b :
  leb (interval_lattice ts) (fst (interval_assume_ule a b)) a = true /\
  leb (interval_lattice ts) (snd (interval_assume_ule a b)) b = true.
Proof.
  unfold interval_assume_ule.
  destruct (interval_finite a) as [[la ha]|]; destruct (interval_finite b) as [[lb hb]|];
    split; try apply interval_meet_lower_left; apply (leb_refl (interval_laws ts)).
Qed.

Definition interval_assume_add (w : width) (a b q : interval) : interval * interval :=
  match interval_finite a, interval_finite b, interval_finite q with
  | Some (la, ha), Some (lb, hb), Some (lq, hq) =>
    if Z.ltb (ha + hb) (modulus w) then
      (interval_meet a (Itv (Fin (lq - hb)) (Fin (hq - lb))),
       interval_meet b (Itv (Fin (lq - ha)) (Fin (hq - la))))
    else (a, b)
  | _, _, _ => (a, b)
  end.

(** Nonwrapping addition refinement retains operands whose sum satisfies the result fact. *)
Theorem interval_assume_add_sound w a b q x y :
  interval_pgamma w a x -> interval_pgamma w b y ->
  interval_pgamma w q (wrap w (x + y)) ->
  interval_pgamma w (fst (interval_assume_add w a b q)) x /\
  interval_pgamma w (snd (interval_assume_add w a b q)) y.
Proof.
  intros Ha Hb Hq. unfold interval_assume_add.
  destruct (interval_finite a) as [[la ha]|] eqn:Hfa;
    destruct (interval_finite b) as [[lb hb]|] eqn:Hfb;
    destruct (interval_finite q) as [[lq hq]|] eqn:Hfq; cbn [fst snd]; try tauto.
  destruct (Z.ltb (ha + hb) (modulus w)) eqn:Hfit; cbn [fst snd]; [|tauto].
  apply Z.ltb_lt in Hfit.
  pose proof (interval_finite_sound w a la ha x Ha Hfa).
  pose proof (interval_finite_sound w b lb hb y Hb Hfb).
  pose proof (interval_finite_sound w q lq hq (wrap w (x + y)) Hq Hfq) as Hresult.
  assert (Hword : is_word w (x + y)) by
    (split; pose proof (proj1 (proj1 Ha)); pose proof (proj1 (proj1 Hb)); lia).
  rewrite (wrap_id w _ Hword) in Hresult.
  split; apply interval_meet_sound; try assumption.
  - split; [exact (proj1 Ha)|]. cbn. split; apply Z.leb_le; lia.
  - split; [exact (proj1 Hb)|]. cbn. split; apply Z.leb_le; lia.
Qed.

Definition interval_assume_sub (a b q : interval) : interval * interval :=
  match interval_finite a, interval_finite b, interval_finite q with
  | Some (la, ha), Some (lb, hb), Some (lq, hq) =>
    if Z.leb hb la then
      (interval_meet a (Itv (Fin (lq + lb)) (Fin (hq + hb))),
       interval_meet b (Itv (Fin (la - hq)) (Fin (ha - lq))))
    else (a, b)
  | _, _, _ => (a, b)
  end.

(** Nonwrapping subtraction refinement retains operands satisfying the result fact. *)
Theorem interval_assume_sub_sound w a b q x y :
  interval_pgamma w a x -> interval_pgamma w b y ->
  interval_pgamma w q (wrap w (x - y)) ->
  interval_pgamma w (fst (interval_assume_sub a b q)) x /\
  interval_pgamma w (snd (interval_assume_sub a b q)) y.
Proof.
  intros Ha Hb Hq. unfold interval_assume_sub.
  destruct (interval_finite a) as [[la ha]|] eqn:Hfa;
    destruct (interval_finite b) as [[lb hb]|] eqn:Hfb;
    destruct (interval_finite q) as [[lq hq]|] eqn:Hfq; cbn [fst snd]; try tauto.
  destruct (Z.leb hb la) eqn:Hfit; cbn [fst snd]; [|tauto].
  apply Z.leb_le in Hfit.
  pose proof (interval_finite_sound w a la ha x Ha Hfa).
  pose proof (interval_finite_sound w b lb hb y Hb Hfb).
  pose proof (interval_finite_sound w q lq hq (wrap w (x - y)) Hq Hfq) as Hresult.
  assert (Hword : is_word w (x - y)) by
    (destruct (proj1 Ha) as [Hxl Hxh]; destruct (proj1 Hb) as [Hyl Hyh]; split; lia).
  rewrite (wrap_id w _ Hword) in Hresult.
  split; apply interval_meet_sound; try assumption.
  - split; [exact (proj1 Ha)|]. cbn. split; apply Z.leb_le; lia.
  - split; [exact (proj1 Hb)|]. cbn. split; apply Z.leb_le; lia.
Qed.

(** Addition refinement lies below each original operand independently of any concrete witness. *)
Theorem interval_assume_add_lower ts w a b q :
  leb (interval_lattice ts) (fst (interval_assume_add w a b q)) a = true /\
  leb (interval_lattice ts) (snd (interval_assume_add w a b q)) b = true.
Proof.
  unfold interval_assume_add.
  destruct (interval_finite a) as [[la ha]|]; destruct (interval_finite b) as [[lb hb]|];
    destruct (interval_finite q) as [[lq hq]|];
    try (split; apply (leb_refl (interval_laws ts))).
  destruct (Z.ltb (ha + hb) (modulus w)); split;
    try apply interval_meet_lower_left; apply (leb_refl (interval_laws ts)).
Qed.

(** Subtraction refinement lies below each original operand independently of any witness. *)
Theorem interval_assume_sub_lower ts a b q :
  leb (interval_lattice ts) (fst (interval_assume_sub a b q)) a = true /\
  leb (interval_lattice ts) (snd (interval_assume_sub a b q)) b = true.
Proof.
  unfold interval_assume_sub.
  destruct (interval_finite a) as [[la ha]|]; destruct (interval_finite b) as [[lb hb]|];
    destruct (interval_finite q) as [[lq hq]|];
    try (split; apply (leb_refl (interval_laws ts))).
  destruct (Z.leb hb la); split;
    try apply interval_meet_lower_left; apply (leb_refl (interval_laws ts)).
Qed.

Definition interval_assume_rewrap (rw : width) (a q : interval) : interval :=
  match interval_finite a with
  | Some (lo, hi) =>
    if (Z.leb 0 lo && Z.ltb hi (modulus rw))%bool then interval_meet a q else a
  | None => a
  end.

(** Resize refinement uses the result interval only when the operand range already fits. *)
Theorem interval_assume_rewrap_sound rw w a q x :
  interval_pgamma w a x -> interval_pgamma rw q (wrap rw x) ->
  interval_pgamma w (interval_assume_rewrap rw a q) x.
Proof.
  intros Ha Hq. unfold interval_assume_rewrap.
  destruct (interval_finite a) as [[lo hi]|] eqn:Hfinite; [|exact Ha].
  destruct (Z.leb 0 lo && Z.ltb hi (modulus rw))%bool eqn:Hfit; [|exact Ha].
  apply andb_true_iff in Hfit as [Hlo Hhi].
  apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi.
  pose proof (interval_finite_sound w a lo hi x Ha Hfinite).
  assert (Hword : is_word rw x) by (split; lia).
  rewrite (wrap_id rw x Hword) in Hq.
  apply interval_meet_sound; [exact Ha|]. split; [exact (proj1 Ha)|exact (proj2 Hq)].
Qed.

(** Resize refinement is below the original operand even when the result width differs. *)
Theorem interval_assume_rewrap_lower ts rw a q :
  leb (interval_lattice ts) (interval_assume_rewrap rw a q) a = true.
Proof.
  unfold interval_assume_rewrap.
  destruct (interval_finite a) as [[lo hi]|]; [|apply (leb_refl (interval_laws ts))].
  destruct (Z.leb 0 lo && Z.ltb hi (modulus rw))%bool;
    [apply interval_meet_lower_left|apply (leb_refl (interval_laws ts))].
Qed.

Definition interval_exclude (a : interval) (c : Z) : interval :=
  match interval_finite a with
  | Some (lo, hi) =>
    if Z.eqb lo c then interval_meet a (Itv (Fin (c + 1)) PosInf)
    else if Z.eqb hi c then interval_meet a (Itv NegInf (Fin (c - 1)))
    else a
  | None => a
  end.

(** Endpoint exclusion retains every represented value different from the excluded integer. *)
Theorem interval_exclude_sound w a x c :
  interval_pgamma w a x -> x <> c -> interval_pgamma w (interval_exclude a c) x.
Proof.
  intros Ha Hneq. unfold interval_exclude.
  destruct (interval_finite a) as [[lo hi]|] eqn:Hfinite; [|exact Ha].
  pose proof (interval_finite_sound w a lo hi x Ha Hfinite) as Hbounds.
  destruct (Z.eqb lo c) eqn:Hlo.
  - apply Z.eqb_eq in Hlo. apply interval_meet_sound; [exact Ha|].
    split; [exact (proj1 Ha)|]. cbn. split; [apply Z.leb_le; lia|reflexivity].
  - destruct (Z.eqb hi c) eqn:Hhi; [|exact Ha].
    apply Z.eqb_eq in Hhi. apply interval_meet_sound; [exact Ha|].
    split; [exact (proj1 Ha)|]. cbn. split; [reflexivity|apply Z.leb_le; lia].
Qed.

(** Endpoint exclusion is below the original interval. *)
Theorem interval_exclude_lower ts a c :
  leb (interval_lattice ts) (interval_exclude a c) a = true.
Proof.
  unfold interval_exclude. destruct (interval_finite a) as [[lo hi]|];
    [|apply (leb_refl (interval_laws ts))].
  destruct (Z.eqb lo c); [apply interval_meet_lower_left|].
  destruct (Z.eqb hi c); [apply interval_meet_lower_left|apply (leb_refl (interval_laws ts))].
Qed.

Definition interval_assume_neq (a b : interval) : interval * interval :=
  (match interval_singleton b with Some c => interval_exclude a c | None => a end,
   match interval_singleton a with Some c => interval_exclude b c | None => b end).

(** Disequality excludes each known singleton from the opposite operand. *)
Theorem interval_assume_neq_sound w a b x y :
  interval_pgamma w a x -> interval_pgamma w b y -> x <> y ->
  interval_pgamma w (fst (interval_assume_neq a b)) x /\
  interval_pgamma w (snd (interval_assume_neq a b)) y.
Proof.
  intros Ha Hb Hneq. unfold interval_assume_neq. split; cbn [fst snd].
  - destruct (interval_singleton b) as [c|] eqn:Hsingle; [|exact Ha].
    apply interval_exclude_sound; [exact Ha|].
    pose proof (interval_singleton_sound w b y c Hb Hsingle). congruence.
  - destruct (interval_singleton a) as [c|] eqn:Hsingle; [|exact Hb].
    apply interval_exclude_sound; [exact Hb|].
    pose proof (interval_singleton_sound w a x c Ha Hsingle). congruence.
Qed.

(** Disequality refinement is below each original operand. *)
Theorem interval_assume_neq_lower ts a b :
  leb (interval_lattice ts) (fst (interval_assume_neq a b)) a = true /\
  leb (interval_lattice ts) (snd (interval_assume_neq a b)) b = true.
Proof.
  unfold interval_assume_neq. split.
  - destruct (interval_singleton b);
      [apply interval_exclude_lower|apply (leb_refl (interval_laws ts))].
  - destruct (interval_singleton a);
      [apply interval_exclude_lower|apply (leb_refl (interval_laws ts))].
Qed.
