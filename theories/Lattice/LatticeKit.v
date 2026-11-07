(** * Two-slot combinator kit

    Projection equations let a combinator reuse its components' laws and measures.
    For example, pair height is the sum of the two component heights.
    Builds on: LatticeCore, LatticeHeight and LatticeConcrete. *)

From Stdlib Require Import Bool Arith Lia List.
From Galois.Lattice Require Import LatticeCore LatticeHeight LatticeConcrete.

(** Slots reflect order and commute with operations, including exact component bottoms. *)
Record slots2 {B A1 A2} (L : lattice B) (L1 : lattice A1) (L2 : lattice A2)
    (p1 : B -> A1) (p2 : B -> A2) : Prop := {
  slots_leb : forall x y, leb L x y = true <->
    leb L1 (p1 x) (p1 y) = true /\ leb L2 (p2 x) (p2 y) = true;
  slots_bot : p1 (bot L) = bot L1 /\ p2 (bot L) = bot L2;
  slots_join : forall x y, p1 (join L x y) = join L1 (p1 x) (p1 y) /\
    p2 (join L x y) = join L2 (p2 x) (p2 y);
  slots_widen : forall x y, p1 (widen L x y) = widen L1 (p1 x) (p1 y) /\
    p2 (widen L x y) = widen L2 (p2 x) (p2 y);
  slots_narrow : forall x y, p1 (narrow L x y) = narrow L1 (p1 x) (p1 y) /\
    p2 (narrow L x y) = narrow L2 (p2 x) (p2 y)
}.

Arguments slots_leb {B A1 A2 L L1 L2 p1 p2}.
Arguments slots_bot {B A1 A2 L L1 L2 p1 p2}.
Arguments slots_join {B A1 A2 L L1 L2 p1 p2}.
Arguments slots_widen {B A1 A2 L L1 L2 p1 p2}.
Arguments slots_narrow {B A1 A2 L L1 L2 p1 p2}.

(** Slot meanings intersect the component meanings of the same concrete value. *)
Definition slots2_gamma {B A1 A2 C} (G1 : concretisation A1 C) (G2 : concretisation A2 C)
    (p1 : B -> A1) (p2 : B -> A2) : concretisation B C :=
  {| gamma := fun x c => gamma G1 (p1 x) c /\ gamma G2 (p2 x) c |}.

(** Slot agreement requires both component agreements. *)
Definition slots2_agree {B A1 A2 C} (R1 : agreement A1 C) (R2 : agreement A2 C)
    (p1 : B -> A1) (p2 : B -> A2) : agreement B C :=
  {| agree := fun a x y => agree R1 (p1 a) x y /\ agree R2 (p2 a) x y |}.

(** This local normalization uses only the supplied slot equations. *)
Local Ltac slots_reduce S :=
  repeat first
    [ rewrite (proj1 (slots_bot S))
    | rewrite (proj2 (slots_bot S))
    | rewrite (proj1 (slots_join S _ _))
    | rewrite (proj2 (slots_join S _ _))
    | rewrite (proj1 (slots_widen S _ _))
    | rewrite (proj2 (slots_widen S _ _))
    | rewrite (proj1 (slots_narrow S _ _))
    | rewrite (proj2 (slots_narrow S _ _)) ].

Section Slots.
Context {B A1 A2 : Type} {L : lattice B} {L1 : lattice A1} {L2 : lattice A2}
  {p1 : B -> A1} {p2 : B -> A2} (S : slots2 L L1 L2 p1 p2).

(** Component weak laws imply the observed lattice's weak laws. *)
Theorem slots2_laws : lattice_laws L1 -> lattice_laws L2 -> lattice_laws L.
Proof.
  intros H1 H2; constructor.
  - intro x; apply (slots_leb S); split; apply leb_refl; assumption.
  - intros x y z Hxy Hyz; apply (slots_leb S) in Hxy; apply (slots_leb S) in Hyz.
    apply (slots_leb S); destruct Hxy, Hyz; split; eapply leb_trans; eassumption.
  - intro x; apply (slots_leb S); slots_reduce S; split; apply bot_least; assumption.
  - intros x y; apply (slots_leb S); slots_reduce S; split; apply join_upper_l; assumption.
  - intros x y; apply (slots_leb S); slots_reduce S; split; apply join_upper_r; assumption.
  - intros x y; apply (slots_leb S); slots_reduce S; split; apply widen_upper_l; assumption.
  - intros x y; apply (slots_leb S); slots_reduce S; split; apply widen_upper_r; assumption.
  - intros x y Hyx; apply (slots_leb S) in Hyx; destruct Hyx as [Hle1 Hle2].
    apply (slots_leb S); slots_reduce S; split; eapply narrow_lower; eassumption.
  - intros x y Hyx; apply (slots_leb S) in Hyx; destruct Hyx as [Hle1 Hle2].
    apply (slots_leb S); slots_reduce S; split; eapply narrow_upper; eassumption.
Qed.

(** Component least joins imply least joins in the observed lattice. *)
Theorem slots2_lub : lub_laws L1 -> lub_laws L2 -> lub_laws L.
Proof.
  intros H1 H2; constructor; intros x y z Hxz Hyz.
  apply (slots_leb S) in Hxz; apply (slots_leb S) in Hyz; destruct Hxz, Hyz.
  apply (slots_leb S); slots_reduce S; split; eapply join_least; eassumption.
Qed.

(** A value projecting to component tops bounds every observed value. *)
Definition slots2_top (T1 : top L1) (T2 : top L2) (t : B)
    (Ht1 : p1 t = top_value T1) (Ht2 : p2 t = top_value T2) : top L.
Proof.
  refine {| top_value := t |}; intro x; apply (slots_leb S).
  rewrite Ht1, Ht2; split; apply top_greatest.
Defined.

(** Component closure lifts to the conjunction of projected invariants. *)
Theorem slots2_closed {inv1 inv2} :
  closed_on L1 inv1 -> closed_on L2 inv2 ->
  closed_on L (fun x => inv1 (p1 x) /\ inv2 (p2 x)).
Proof.
  intros C1 C2; constructor.
  - slots_reduce S; split; apply bot_inv; assumption.
  - intros x y [Hx1 Hx2] [Hy1 Hy2]; slots_reduce S.
    split; eapply join_inv; eassumption.
  - intros x y [Hx1 Hx2] [Hy1 Hy2]; slots_reduce S.
    split; eapply widen_inv; eassumption.
  - intros x y [Hx1 Hx2] [Hy1 Hy2] Hyx.
    apply (slots_leb S) in Hyx; destruct Hyx as [Hle1 Hle2]; slots_reduce S.
    split; eapply narrow_inv; eassumption.
Qed.

(** Summed component heights grow whenever a join grows in some slot. *)
Definition slots2_height {inv1 inv2} (H1 : lattice_laws L1) (H2 : lattice_laws L2)
    (C1 : closed_on L1 inv1) (C2 : closed_on L2 inv2)
    (R1 : height_on L1 inv1) (R2 : height_on L2 inv2) :
    height_on L (fun x => inv1 (p1 x) /\ inv2 (p2 x)).
Proof.
  refine {| rank := fun x => rank R1 (p1 x) + rank R2 (p2 x);
            bound := bound R1 + bound R2 |}.
  - intros x [Hx1 Hx2].
    pose proof (rank_bounded R1 _ Hx1); pose proof (rank_bounded R2 _ Hx2); lia.
  - intros x y [Hx1 Hx2] [Hy1 Hy2] Hxy; apply (slots_leb S) in Hxy.
    destruct Hxy as [Hle1 Hle2].
    pose proof (rank_monotone R1 _ _ Hx1 Hy1 Hle1).
    pose proof (rank_monotone R2 _ _ Hx2 Hy2 Hle2); lia.
  - intros x y [Hx1 Hx2] [Hy1 Hy2] Hstrict; slots_reduce S.
    pose proof (rank_monotone R1 _ _ Hx1 (join_inv C1 _ _ Hx1 Hy1)
      (join_upper_l H1 _ _)) as Hg1.
    pose proof (rank_monotone R2 _ _ Hx2 (join_inv C2 _ _ Hx2 Hy2)
      (join_upper_l H2 _ _)) as Hg2.
    destruct (leb L1 (join L1 (p1 x) (p1 y)) (p1 x)) eqn:Hle1.
    + assert (Hle2 : leb L2 (join L2 (p2 x) (p2 y)) (p2 x) = false).
      { destruct (leb L2 (join L2 (p2 x) (p2 y)) (p2 x)) eqn:Hle2; [| reflexivity].
        assert (Hback : leb L (join L x y) x = true).
        { apply (slots_leb S); slots_reduce S; auto. }
        congruence. }
      pose proof (join_rank_grows R2 _ _ Hx2 Hy2 Hle2); lia.
    + pose proof (join_rank_grows R1 _ _ Hx1 Hy1 Hle1); lia.
Defined.

(** Summed component widening credits decrease in every escaping slot. *)
Definition slots2_wrank {inv1 inv2}
    (W1 : widening_rank_on L1 inv1) (W2 : widening_rank_on L2 inv2) :
    widening_rank_on L (fun x => inv1 (p1 x) /\ inv2 (p2 x)).
Proof.
  refine {| wrank := fun x => wrank W1 (p1 x) + wrank W2 (p2 x);
            wbound := wbound W1 + wbound W2 |}.
  - intros x [Hx1 Hx2].
    pose proof (wrank_bounded W1 _ Hx1); pose proof (wrank_bounded W2 _ Hx2); lia.
  - intros x y [Hx1 Hx2] [Hy1 Hy2] _; slots_reduce S.
    pose proof (widening_rank_nonincreasing W1 _ _ Hx1 Hy1).
    pose proof (widening_rank_nonincreasing W2 _ _ Hx2 Hy2); lia.
  - intros x y [Hx1 Hx2] [Hy1 Hy2] Hstrict; slots_reduce S.
    pose proof (widening_rank_nonincreasing W1 _ _ Hx1 Hy1).
    pose proof (widening_rank_nonincreasing W2 _ _ Hx2 Hy2).
    destruct (leb L1 (p1 y) (p1 x)) eqn:Hle1.
    + assert (Hle2 : leb L2 (p2 y) (p2 x) = false).
      { destruct (leb L2 (p2 y) (p2 x)) eqn:Hle2; [| reflexivity].
        assert (Hback : leb L y x = true) by (apply (slots_leb S); auto).
        congruence. }
      pose proof (widen_rank_progress W2 _ _ Hx2 Hy2 Hle2); lia.
    + pose proof (widen_rank_progress W1 _ _ Hx1 Hy1 Hle1); lia.
Defined.

Context {C : Type} (G1 : concretisation A1 C) (G2 : concretisation A2 C)
  (R1 : agreement A1 C) (R2 : agreement A2 C).

(** Intersecting monotone slot meanings preserves monotonicity. *)
Theorem slots2_gamma_laws : concretisation_laws L1 G1 -> concretisation_laws L2 G2 ->
  concretisation_laws L (slots2_gamma G1 G2 p1 p2).
Proof.
  intros HG1 HG2; constructor; intros x y c Hle [Hx1 Hx2].
  apply (slots_leb S) in Hle; destruct Hle as [Hle1 Hle2].
  split; eapply gamma_monotone; eassumption.
Qed.

(** Empty bottom in either slot makes the combined bottom empty. *)
Theorem slots2_bot_empty : bottom_empty L1 G1 \/ bottom_empty L2 G2 ->
  bottom_empty L (slots2_gamma G1 G2 p1 p2).
Proof.
  intros Hbot; constructor; intros c [Hc1 Hc2]; slots_reduce S.
  destruct Hbot as [H1 | H2].
  - rewrite (proj1 (slots_bot S)) in Hc1; exact (gamma_bot_empty H1 c Hc1).
  - rewrite (proj2 (slots_bot S)) in Hc2; exact (gamma_bot_empty H2 c Hc2).
Qed.

(** A value projecting to full component tops has full combined meaning. *)
Theorem slots2_top_full (T1 : top L1) (T2 : top L2) t Ht1 Ht2 :
  top_full T1 G1 -> top_full T2 G2 ->
  top_full (slots2_top T1 T2 t Ht1 Ht2) (slots2_gamma G1 G2 p1 p2).
Proof.
  intros HG1 HG2; constructor; intro c; cbn; rewrite Ht1, Ht2.
  split; apply gamma_top_full; assumption.
Qed.

(** Intersecting slot agreements preserves reflexivity and antitonicity. *)
Theorem slots2_agree_laws : agreement_laws L1 R1 -> agreement_laws L2 R2 ->
  agreement_laws L (slots2_agree R1 R2 p1 p2).
Proof.
  intros HR1 HR2; constructor.
  - intros x c; split; [apply (agree_refl HR1) | apply (agree_refl HR2)].
  - intros x y c d Hle [Hc1 Hc2]; apply (slots_leb S) in Hle.
    destruct Hle as [Hle1 Hle2]; split; eapply agree_antitone; eassumption.
Qed.

(** Slot join equations transport the component join-agreement laws. *)
Theorem slots2_agree_join : agreement_join_law L1 R1 -> agreement_join_law L2 R2 ->
  agreement_join_law L (slots2_agree R1 R2 p1 p2).
Proof.
  intros HR1 HR2; constructor; intros x y c d [Hx1 Hx2] [Hy1 Hy2].
  cbn; slots_reduce S; split; eapply agree_join; eassumption.
Qed.
End Slots.

(** Summing a measure over a list counts each occurrence, including duplicates. *)
Definition msum {I} (U : list I) (m : I -> nat) :=
  fold_right (fun i n => m i + n) 0 U.

(** A constant measure sums to the list length times that constant. *)
Theorem msum_constant {I} (U : list I) b : msum U (fun _ => b) = length U * b.
Proof.
  unfold msum; induction U as [| i U IH]; cbn; [reflexivity | rewrite IH; reflexivity].
Qed.

(** Pointwise bounds imply a bound on the list sum. *)
Theorem msum_bounded {I} (U : list I) (m b : I -> nat) :
  (forall i, In i U -> m i <= b i) -> msum U m <= msum U b.
Proof.
  unfold msum; induction U as [| i U IH]; cbn; intro H; [lia |].
  specialize (IH (fun j Hj => H j (or_intror Hj))).
  specialize (H i (or_introl eq_refl)); lia.
Qed.

(** One strict summand and weak growth elsewhere force strict sum growth. *)
Theorem msum_grows {I} (U : list I) (m n : I -> nat) :
  (forall i, In i U -> m i <= n i) ->
  (exists i, In i U /\ m i < n i) -> msum U m < msum U n.
Proof.
  unfold msum; induction U as [| i U IH]; cbn; intros Hmono [j [Hj Hstrict]].
  - contradiction.
  - pose proof (Hmono i (or_introl eq_refl)) as Hi.
    assert (Hrest : forall k, In k U -> m k <= n k).
    { intros k Hk; apply Hmono; right; exact Hk. }
    destruct Hj as [Heq | Hj].
    + subst j; pose proof (msum_bounded U m n Hrest) as Hsum; unfold msum in Hsum; lia.
    + specialize (IH Hrest (ex_intro _ j (conj Hj Hstrict))); lia.
Qed.
