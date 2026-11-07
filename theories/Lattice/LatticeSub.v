(** * Invariant subtypes

    Subtype operations retain the underlying values and attach closure evidence.
    For example, an invariant-relative height becomes a total height on its subtype.
    Builds on: CostMonad, LatticeCore, LatticeHeight and LatticeConcrete. *)

From Stdlib Require Import Bool NArith Lia.
From Galois.Cost Require Import CostMonad CostTactics.
From Galois.Lattice Require Import LatticeCore LatticeHeight LatticeConcrete.
Import Cost.Notations.

(** Ordered narrowing is refined and unordered narrowing keeps the invariant left value. *)
Local Definition sub_narrow_result_c {A} (L : lattice A) (inv : A -> Prop) (C : closed_on L inv)
    (a b : {a | inv a}) (q : bool) (Hq : leb L (proj1_sig b) (proj1_sig a) = q) :
    Cost.t {a | inv a} :=
  match q as q' return leb L (proj1_sig b) (proj1_sig a) = q' -> Cost.t {a | inv a} with
  | true => fun Hle => Cost.step ;;
      Cost.refine (narrow_c L (proj1_sig a) (proj1_sig b))
        (narrow_inv C _ _ (proj2_sig a) (proj2_sig b) Hle)
  | false => fun _ => Cost.ret a
  end Hq.

(** Subtype callbacks charge their underlying callback and retain closure evidence by refinement. *)
Definition sub_lattice {A} (L : lattice A) (inv : A -> Prop) (C : closed_on L inv) :
    lattice {a | inv a} :=
  {| leb_c := fun a b => Cost.step ;; leb_c L (proj1_sig a) (proj1_sig b);
     join_c := fun a b => Cost.step ;;
       Cost.refine (join_c L (proj1_sig a) (proj1_sig b))
         (join_inv C _ _ (proj2_sig a) (proj2_sig b));
     widen_c := fun a b => Cost.step ;;
       Cost.refine (widen_c L (proj1_sig a) (proj1_sig b))
         (widen_inv C _ _ (proj2_sig a) (proj2_sig b));
     narrow_c := fun a b => Cost.step ;;
       let* q := Cost.refine (P := fun q => leb L (proj1_sig b) (proj1_sig a) = q)
         (leb_c L (proj1_sig b) (proj1_sig a)) eq_refl in
       sub_narrow_result_c L inv C a b (proj1_sig q) (proj2_sig q);
     bot := exist inv (bot L) (bot_inv C) |}.

Section Sub.
Context {A : Type} (L : lattice A) (inv : A -> Prop) (C : closed_on L inv).

Local Lemma sub_narrow_result_value a b q Hq :
  q = true ->
  proj1_sig (Cost.value (sub_narrow_result_c L inv C a b q Hq)) =
    narrow L (proj1_sig a) (proj1_sig b).
Proof.
  destruct q; [reflexivity | discriminate].
Qed.

Local Lemma sub_narrow_result_unordered a b q Hq :
  q = false ->
  proj1_sig (Cost.value (sub_narrow_result_c L inv C a b q Hq)) = proj1_sig a.
Proof.
  destruct q; [discriminate | reflexivity].
Qed.

Local Lemma sub_narrow_result_cost k :
  cost_bounded_on L inv k ->
  forall a b q Hq,
    (Cost.ticks (sub_narrow_result_c L inv C a b q Hq) <= 1 + k)%N.
Proof.
  intros H a b [] Hq; cbn [sub_narrow_result_c]; cost_simpl.
  - destruct (H _ _ (proj2_sig a) (proj2_sig b)) as [Hle [Hjoin [Hwiden Hnarrow]]]; lia.
  - lia.
Qed.

(** Subtype callbacks cost at most two component calls and two wrapper ticks. *)
Theorem sub_cost k : cost_bounded_on L inv k ->
  cost_bounded_on (sub_lattice L inv C) (fun _ => True) (2 * k + 2)%N.
Proof.
  intros H a b _ _; cbn [sub_lattice leb_c join_c widen_c narrow_c]; cost_simpl.
  cbn [proj1_sig proj2_sig].
  pose proof (sub_narrow_result_cost k H a b
    (Cost.value (leb_c L (proj1_sig b) (proj1_sig a))) eq_refl) as Hn.
  destruct (H _ _ (proj2_sig a) (proj2_sig b)) as [Hle [Hjoin [Hwiden Hnarrow]]].
  destruct (H _ _ (proj2_sig b) (proj2_sig a)) as [Hle_rev Hrest].
  repeat split; lia.
Qed.

(** Subtype order is exactly underlying order. *)
Theorem leb_sub a b :
  leb (sub_lattice L inv C) a b = leb L (proj1_sig a) (proj1_sig b).
Proof.
  reflexivity.
Qed.

(** Subtype join projects to the underlying join. *)
Theorem join_sub a b :
  proj1_sig (join (sub_lattice L inv C) a b) = join L (proj1_sig a) (proj1_sig b).
Proof.
  reflexivity.
Qed.

(** Subtype widening projects to the underlying widening. *)
Theorem widen_sub a b :
  proj1_sig (widen (sub_lattice L inv C) a b) = widen L (proj1_sig a) (proj1_sig b).
Proof.
  reflexivity.
Qed.

(** Ordered subtype narrowing projects to the underlying narrowing. *)
Theorem narrow_sub a b :
  leb L (proj1_sig b) (proj1_sig a) = true ->
  proj1_sig (narrow (sub_lattice L inv C) a b) = narrow L (proj1_sig a) (proj1_sig b).
Proof.
  intro Hle; unfold narrow; cbn [sub_lattice narrow_c]; cost_simpl.
  apply sub_narrow_result_value; exact Hle.
Qed.

(** Unordered subtype narrowing returns its left underlying value without calling narrowing. *)
Theorem narrow_sub_unordered a b :
  leb L (proj1_sig b) (proj1_sig a) = false ->
  proj1_sig (narrow (sub_lattice L inv C) a b) = proj1_sig a.
Proof.
  intro Hle; unfold narrow; cbn [sub_lattice narrow_c]; cost_simpl.
  apply sub_narrow_result_unordered; exact Hle.
Qed.

(** Subtype weak laws follow from underlying weak laws on ordered narrowing inputs. *)
Theorem sub_laws : lattice_laws L -> lattice_laws (sub_lattice L inv C).
Proof.
  intro H; constructor.
  - intro a; rewrite leb_sub; apply (leb_refl H).
  - intros a b c Hab Hbc; rewrite leb_sub in *; eapply (leb_trans H); eassumption.
  - intro a; rewrite leb_sub; apply (bot_least H).
  - intros a b; rewrite leb_sub, join_sub; apply (join_upper_l H).
  - intros a b; rewrite leb_sub, join_sub; apply (join_upper_r H).
  - intros a b; rewrite leb_sub, widen_sub; apply (widen_upper_l H).
  - intros a b; rewrite leb_sub, widen_sub; apply (widen_upper_r H).
  - intros a b Hba; rewrite leb_sub in *; rewrite narrow_sub by exact Hba.
    apply (narrow_lower H), Hba.
  - intros a b Hba; rewrite leb_sub in *; rewrite narrow_sub by exact Hba.
    apply (narrow_upper H), Hba.
Qed.

(** Underlying least joins give subtype least joins. *)
Theorem sub_lub : lub_laws L -> lub_laws (sub_lattice L inv C).
Proof.
  intro H; constructor; intros a b c Ha Hb; rewrite leb_sub in *.
  rewrite join_sub; apply (join_least H); assumption.
Qed.

(** An invariant top gives a subtype top. *)
Definition sub_top (T : top L) (HT : inv (top_value T)) : top (sub_lattice L inv C).
Proof.
  refine {| top_value := exist inv (top_value T) HT |}.
  intro a; rewrite leb_sub; apply (top_greatest T).
Defined.

(** Subtype meaning forgets the invariant evidence. *)
Definition sub_gamma {D} (G : concretisation A D) :
  concretisation {a | inv a} D := comap_gamma (@proj1_sig A inv) G.

(** Subtype projection pulls back monotone concretisation. *)
Theorem sub_gamma_laws {D} (G : concretisation A D) :
  concretisation_laws L G -> concretisation_laws (sub_lattice L inv C) (sub_gamma G).
Proof.
  apply (comap_gamma_laws L (sub_lattice L inv C) G (@proj1_sig A inv)).
  intros a b; apply leb_sub.
Qed.

(** Invariant-relative height becomes total subtype height. *)
Theorem sub_height (H : height_on L inv) : height (sub_lattice L inv C).
Proof.
  refine {| rank := fun a => rank H (proj1_sig a);
            bound := bound H |}.
  - intros a _; apply (rank_bounded H), (proj2_sig a).
  - intros a b _ _ Hle; rewrite leb_sub in Hle.
    apply (rank_monotone H); [apply (proj2_sig a) | apply (proj2_sig b) | exact Hle].
  - intros a b _ _ Hstrict; rewrite leb_sub, join_sub in Hstrict; rewrite join_sub.
    apply (join_rank_grows H); [apply (proj2_sig a) | apply (proj2_sig b) | exact Hstrict].
Defined.

(** Invariant-relative widening credits become total subtype widening credits. *)
Theorem sub_wrank (W : widening_rank_on L inv) : widening_rank (sub_lattice L inv C).
Proof.
  refine {| wrank := fun a => wrank W (proj1_sig a);
            wbound := wbound W |}.
  - intros a _; apply (wrank_bounded W), (proj2_sig a).
  - intros a b _ _ Hle; rewrite leb_sub in Hle; rewrite widen_sub.
    apply (widen_rank_stable W); [apply (proj2_sig a) | apply (proj2_sig b) | exact Hle].
  - intros a b _ _ Hle; rewrite leb_sub in Hle; rewrite widen_sub.
    apply (widen_rank_progress W); [apply (proj2_sig a) | apply (proj2_sig b) | exact Hle].
Defined.
End Sub.
