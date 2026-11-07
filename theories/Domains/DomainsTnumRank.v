(** * Known-bit progress credits

    The rank counts forgotten bit facts through an explicitly charged width traversal.
    For example, forgetting one known-zero fact increases the rank by one.
    Builds on: DomainsTnum, CostMonad and LatticeHeight. *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Lattice Require Import LatticeCore LatticeHeight.
From Galois.Bits Require Import BitsWord.
From Galois.Domains Require Import DomainsTnum.
Import Cost.Notations.

Local Open Scope nat_scope.

Fixpoint tnum_unknown_from_c (n i : nat) (m : Z) : Cost.t nat :=
  match n with
  | O => Cost.ret O
  | S n =>
    Cost.step ;;
    let* rest := tnum_unknown_from_c n (S i) m in
    Cost.ret (if Z.testbit m (Z.of_nat i) then rest else S rest)
  end.

Definition tnum_unknown (w : width) (m : Z) : nat :=
  Cost.value (tnum_unknown_from_c (Pos.to_nat w) O m).

(** The charged counter counts unset bits over its exact contiguous index range. *)
Theorem tnum_unknown_from_equation : forall n i m,
  Cost.value (tnum_unknown_from_c n i m) =
  length (filter (fun j => negb (Z.testbit m (Z.of_nat j))) (seq i n)).
Proof.
  intro n. induction n as [|n IH]; intros i m; cbn [tnum_unknown_from_c seq filter length];
    autorewrite with galois_cost; [reflexivity|].
  rewrite IH. destruct (Z.testbit m (Z.of_nat i)); reflexivity.
Qed.

(** Every counted bit incurs one visit and no recursive work is hidden in a pure lift. *)
Theorem tnum_unknown_from_cost : forall n i m,
  Cost.ticks (tnum_unknown_from_c n i m) = N.of_nat n.
Proof.
  intro n. induction n as [|n IH]; intros i m; cbn [tnum_unknown_from_c];
    autorewrite with galois_cost; [reflexivity|].
  rewrite IH, Nat2N.inj_succ. lia.
Qed.

Definition tnum_rank_c (w : width) (a : tnum) : Cost.t nat :=
  let* zero := tnum_unknown_from_c (Pos.to_nat w) O (zeros a) in
  let* one := tnum_unknown_from_c (Pos.to_nat w) O (ones a) in
  Cost.ret (zero + one).

Definition tnum_rank (w : width) (a : tnum) : nat := Cost.value (tnum_rank_c w a).

(** The bit rank counts forgotten facts in both masks independently. *)
Theorem tnum_rank_equation : forall w a,
  tnum_rank w a = tnum_unknown w (zeros a) + tnum_unknown w (ones a).
Proof.
  intros w a. unfold tnum_rank, tnum_rank_c. autorewrite with galois_cost. reflexivity.
Qed.

Lemma tnum_filter_count_monotone : forall (A : Type) (f g : A -> bool) xs,
  (forall x, In x xs -> f x = true -> g x = true) ->
  length (filter f xs) <= length (filter g xs).
Proof.
  intros A f g xs. induction xs as [|x xs IH]; intro Hsub; [reflexivity|].
  assert (Htail : length (filter f xs) <= length (filter g xs)).
  { apply IH. intros y Hy. apply Hsub. now right. }
  specialize (Hsub x (or_introl eq_refl)). cbn [filter].
  destruct (f x), (g x); cbn in *; try discriminate; lia.
Qed.

Lemma tnum_filter_count_equal : forall (A : Type) (f g : A -> bool) xs,
  (forall x, In x xs -> f x = true -> g x = true) ->
  length (filter f xs) = length (filter g xs) ->
  forall x, In x xs -> f x = g x.
Proof.
  intros A f g xs. induction xs as [|y xs IH]; intros Hsub Hcount x Hin.
  - contradiction.
  - assert (Htailsub : forall a, In a xs -> f a = true -> g a = true).
    { intros a Ha. apply Hsub. now right. }
    pose proof (tnum_filter_count_monotone A f g xs Htailsub) as Htail.
    pose proof (Hsub y (or_introl eq_refl)) as Hhead.
    cbn [filter] in Hcount.
    destruct (f y) eqn:Hf, (g y) eqn:Hg; cbn in Hcount; try discriminate; try lia.
    + destruct Hin as [->|Hin]; [now rewrite Hf, Hg|].
      apply IH; [exact Htailsub|lia|exact Hin].
    + destruct Hin as [->|Hin]; [now rewrite Hf, Hg|].
      apply IH; [exact Htailsub|exact Hcount|exact Hin].
Qed.

Lemma tnum_unknown_monotone : forall w a b,
  tnum_subset w b a = true -> tnum_unknown w a <= tnum_unknown w b.
Proof.
  intros w a b Hsub. rewrite tnum_subset_bits in Hsub.
  unfold tnum_unknown. rewrite !tnum_unknown_from_equation.
  apply tnum_filter_count_monotone. intros i Hi Hbit. apply in_seq in Hi.
  apply negb_true_iff in Hbit. apply negb_true_iff.
  destruct (Z.testbit b (Z.of_nat i)) eqn:Hb; [|reflexivity].
  specialize (Hsub (Z.of_nat i) ltac:(rewrite <- positive_nat_Z; lia) Hb). congruence.
Qed.

Lemma tnum_unknown_equal : forall w a b,
  tnum_subset w b a = true -> tnum_unknown w a = tnum_unknown w b ->
  tnum_subset w a b = true.
Proof.
  intros w a b Hsub Hcount. apply tnum_subset_bits. intros i Hi Hbit.
  assert (Himp : forall j, In j (seq 0 (Pos.to_nat w)) ->
    negb (Z.testbit a (Z.of_nat j)) = true ->
    negb (Z.testbit b (Z.of_nat j)) = true).
  { intros j Hj Hzero. apply in_seq in Hj. apply negb_true_iff in Hzero.
    apply negb_true_iff. rewrite tnum_subset_bits in Hsub.
    destruct (Z.testbit b (Z.of_nat j)) eqn:Hb; [|reflexivity].
    specialize (Hsub (Z.of_nat j) ltac:(rewrite <- positive_nat_Z; lia) Hb). congruence. }
  unfold tnum_unknown in Hcount. rewrite !tnum_unknown_from_equation in Hcount.
  pose proof (tnum_filter_count_equal nat _ _ _ Himp Hcount (Z.to_nat i)
    ltac:(apply in_seq; cbn [Nat.add]; split; [lia|]; apply Nat2Z.inj_lt;
      rewrite Z2Nat.id, positive_nat_Z by lia; lia)) as Heq.
  cbn beta in Heq. rewrite Z2Nat.id in Heq by lia. rewrite Hbit in Heq.
  destruct (Z.testbit b i); cbn in Heq; congruence.
Qed.

(** Forgetting known bits never decreases the bit rank, including raw garbage masks. *)
Theorem tnum_rank_monotone : forall w a b,
  leb (tnum_lattice w) a b = true -> tnum_rank w a <= tnum_rank w b.
Proof.
  intros w a b Hle.
  change (tnum_subset w (zeros b) (zeros a) &&
    tnum_subset w (ones b) (ones a) = true) in Hle.
  apply andb_true_iff in Hle as [Hz Ho].
  apply tnum_unknown_monotone in Hz, Ho. rewrite !tnum_rank_equation. lia.
Qed.

(** Equal ranks under mask inclusion imply reverse inclusion, without asserting raw equality. *)
Theorem tnum_rank_equal : forall w a b,
  leb (tnum_lattice w) a b = true -> tnum_rank w a = tnum_rank w b ->
  leb (tnum_lattice w) b a = true.
Proof.
  intros w a b Hle Heq.
  change (tnum_subset w (zeros b) (zeros a) &&
    tnum_subset w (ones b) (ones a) = true) in Hle.
  apply andb_true_iff in Hle as [Hz Ho].
  pose proof (tnum_unknown_monotone w _ _ Hz) as Hzero.
  pose proof (tnum_unknown_monotone w _ _ Ho) as Hone.
  rewrite !tnum_rank_equation in Heq.
  change (tnum_subset w (zeros a) (zeros b) &&
    tnum_subset w (ones a) (ones b) = true).
  apply andb_true_iff. split; apply tnum_unknown_equal; try assumption; lia.
Qed.

(** At most two facts per word bit can be forgotten. *)
Theorem tnum_rank_bounded : forall w a, tnum_rank w a <= 2 * Pos.to_nat w.
Proof.
  intros w a. rewrite tnum_rank_equation. unfold tnum_unknown.
  rewrite !tnum_unknown_from_equation.
  pose proof (filter_length_le (fun i => negb (Z.testbit (zeros a) (Z.of_nat i)))
    (seq 0 (Pos.to_nat w))) as Hz.
  pose proof (filter_length_le (fun i => negb (Z.testbit (ones a) (Z.of_nat i)))
    (seq 0 (Pos.to_nat w))) as Ho.
  rewrite length_seq in Hz, Ho. lia.
Qed.

(** The raw mask preorder has bounded height even though it is not antisymmetric on records. *)
Definition tnum_height_on (w : width) : height_on (tnum_lattice w) (fun _ => True).
Proof.
  refine {| rank := tnum_rank w; bound := 2 * Pos.to_nat w |}.
  - intros a _. apply tnum_rank_bounded.
  - intros a b _ _. apply tnum_rank_monotone.
  - intros a b _ _ Hstrict.
    pose proof (join_upper_l (tnum_laws w) a b) as Hle.
    pose proof (tnum_rank_monotone w _ _ Hle) as Hrank.
    destruct (Nat.eq_dec (tnum_rank w a) (tnum_rank w (join (tnum_lattice w) a b)))
      as [Heq|Hneq]; [|lia].
    pose proof (tnum_rank_equal w _ _ Hle Heq). congruence.
Defined.
