(** * Symbolic weights and their algebraic boundary

    Path weights compose a finite list of exploded arcs without listing either carrier.
    For example, the weight of a call, body and return applies the call first.
    Builds on: FrameworkMicro, FrameworkIde and CostList. *)

From Stdlib Require Import List Bool NArith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Lattice Require Import LatticeCore LatticeSimple.
From Galois.Framework Require Import FrameworkMicro FrameworkIfds FrameworkIde.
Import List.ListNotations Cost.Notations.

Module TabWeight.

(** Symbolic unit and associativity concern F order, independently of application to A. *)
Record laws {A F} (M : Micro.t A F) : Prop := Laws {
  unit_left : forall f,
    equivalent (Micro.lat M) (Micro.compose M (Micro.id M) f) f;
  unit_right : forall f,
    equivalent (Micro.lat M) (Micro.compose M f (Micro.id M)) f;
  associative : forall f g h,
    equivalent (Micro.lat M) (Micro.compose M (Micro.compose M f g) h)
      (Micro.compose M f (Micro.compose M g h))
}.
Arguments unit_left {A F M}.
Arguments unit_right {A F M}.
Arguments associative {A F M}.

Definition fold_c {N E P D A F} (M : Micro.t A F)
    (as_ : list (Jump.arc N E P D F)) f :=
  fold_left_c (fun before a =>
    Cost.step ;; Micro.compose_c M (Jump.weight a) before) as_ f.

Definition fold {N E P D A F} (M : Micro.t A F)
    (as_ : list (Jump.arc N E P D F)) f := Cost.value (fold_c M as_ f).

(** A path weight includes identity even for the empty path. *)
Definition weight_c {N E P D A F} (I : Ide.t N E P D A F)
    (as_ : list (Jump.arc N E P D F)) :=
  fold_c (Ide.micro I) as_ (Micro.id (Ide.micro I)).

Definition weight {N E P D A F} (I : Ide.t N E P D A F) as_ :=
  Cost.value (weight_c I as_).

(** The weight observation is accumulation from the symbolic identity. *)
Theorem weight_fold {N E P D A F} (I : Ide.t N E P D A F) as_ :
  weight I as_ = fold (Ide.micro I) as_ (Micro.id (Ide.micro I)).
Proof.
  reflexivity.
Qed.

(** Weight accumulation exposes its left-to-right composition order. *)
Theorem fold_equation {N E P D A F} (M : Micro.t A F)
    (as_ : list (Jump.arc N E P D F)) f :
  fold M as_ f =
    match as_ with
    | [] => f
    | a :: rest => fold M rest (Micro.compose M (Jump.weight a) f)
    end.
Proof.
  destruct as_; unfold fold, fold_c; rewrite !value_fold_left_c; reflexivity.
Qed.

(** The empty path has the symbolic identity weight. *)
Theorem weight_nil {N E P D A F} (I : Ide.t N E P D A F) :
  weight I ([] : list (Jump.arc N E P D F)) = Micro.id (Ide.micro I).
Proof.
  reflexivity.
Qed.

(** Concatenation first accumulates the prefix and then the suffix. *)
Theorem fold_app {N E P D A F} (M : Micro.t A F)
    (xs ys : list (Jump.arc N E P D F)) f :
  fold M (xs ++ ys) f = fold M ys (fold M xs f).
Proof.
  revert f; induction xs as [|a xs IH]; intro f.
  - reflexivity.
  - cbn [app]; rewrite (fold_equation M (a :: (xs ++ ys)) f).
    rewrite (fold_equation M (a :: xs) f), IH; reflexivity.
Qed.

(** Each accumulated arc costs its traversal, callback invocation and composition body. *)
Theorem fold_cost_equation {N E P D A F} (M : Micro.t A F)
    (as_ : list (Jump.arc N E P D F)) f :
  Cost.ticks (fold_c M as_ f) =
    match as_ with
    | [] => 0%N
    | a :: rest =>
      (2 + Cost.ticks (Micro.compose_c M (Jump.weight a) f) +
        Cost.ticks (fold_c M rest (Micro.compose M (Jump.weight a) f)))%N
    end.
Proof.
  destruct as_ as [|a rest]; [reflexivity|].
  unfold fold_c; rewrite ticks_fold_left_c_cons; autorewrite with galois_cost.
  fold (Micro.compose M (Jump.weight a) f); lia.
Qed.

(** A primitive composition budget gives a total bound for every finite trace. *)
Theorem weight_cost {N E P D A F} (I : Ide.t N E P D A F)
    (as_ : list (Jump.arc N E P D F)) Km :
  (forall f g, (Cost.ticks (Micro.compose_c (Ide.micro I) f g) <= Km)%N) ->
  (Cost.ticks (weight_c I as_) <= N.of_nat (length as_) * (2 + Km))%N.
Proof.
  intro Hcompose; unfold weight_c.
  assert (Hfold : forall (xs : list (Jump.arc N E P D F)) f,
    (Cost.ticks (fold_c (Ide.micro I) xs f) <= N.of_nat (length xs) * (2 + Km))%N).
  { intro xs; induction xs as [|a xs IH]; intro f; rewrite fold_cost_equation.
    - cbn [length]; nia.
    - specialize (IH (Micro.compose (Ide.micro I) (Jump.weight a) f)).
      specialize (Hcompose (Jump.weight a) f).
      cbn [length]; rewrite Nat2N.inj_succ; nia. }
  apply Hfold.
Qed.

(** Boolean conjunction has the symbolic unit and associativity duties. *)
Theorem boolean_laws : laws Micro.boolean.
Proof.
  constructor.
  - intros []; split; reflexivity.
  - intros []; split; reflexivity.
  - intros [] [] []; split; reflexivity.
Qed.

(** Accumulation is monotone in its incoming symbolic function. *)
Theorem fold_mono {N E P D A F} (LA : lattice A) (M : Micro.t A F)
    (HM : micro_laws LA M) (xs : list (Jump.arc N E P D F)) f g :
  leb (Micro.lat M) f g = true ->
  leb (Micro.lat M) (fold M xs f) (fold M xs g) = true.
Proof.
  revert f g; induction xs as [|a xs IH]; intros f g Hfg.
  - exact Hfg.
  - rewrite (fold_equation M (a :: xs) f), (fold_equation M (a :: xs) g).
    apply IH, (compose_mono _ _ HM); [apply leb_refl; exact (lat_ok _ _ HM)|exact Hfg].
Qed.

(** Symbolic associativity moves an incoming composition through accumulation. *)
Theorem fold_compose {N E P D A F} (LA : lattice A) (M : Micro.t A F)
    (HM : micro_laws LA M) (HW : laws M) (xs : list (Jump.arc N E P D F)) f g :
  equivalent (Micro.lat M) (fold M xs (Micro.compose M f g))
    (Micro.compose M (fold M xs f) g).
Proof.
  revert f g; induction xs as [|a xs IH]; intros f g.
  - split; apply leb_refl; exact (lat_ok _ _ HM).
  - rewrite (fold_equation M (a :: xs) (Micro.compose M f g)).
    rewrite (fold_equation M (a :: xs) f).
    destruct (IH (Micro.compose M (Jump.weight a) f) g) as [Hforward Hback].
    destruct (associative HW (Jump.weight a) f g) as [Hassoc Hreverse].
    split.
    + eapply leb_trans; [exact (lat_ok _ _ HM)| |exact Hforward].
      apply (fold_mono LA M HM); exact Hreverse.
    + eapply leb_trans; [exact (lat_ok _ _ HM)|exact Hback|].
      apply (fold_mono LA M HM); exact Hassoc.
Qed.

(** Concatenated trace weights compose in chronological order modulo symbolic equivalence. *)
Theorem weight_app {N E P D A F} (I : Ide.t N E P D A F)
    (HM : micro_laws (Ide.values I) (Ide.micro I))
    (HW : laws (Ide.micro I)) (xs ys : list (Jump.arc N E P D F)) :
  equivalent (Micro.lat (Ide.micro I)) (weight I (xs ++ ys))
    (Micro.compose (Ide.micro I) (weight I ys) (weight I xs)).
Proof.
  unfold weight, weight_c; fold (fold (Ide.micro I) (xs ++ ys) (Micro.id (Ide.micro I))).
  rewrite fold_app.
  destruct (fold_compose (Ide.values I) (Ide.micro I) HM HW ys
    (Micro.id (Ide.micro I)) (fold (Ide.micro I) xs (Micro.id (Ide.micro I))))
    as [Hforward Hback].
  destruct (unit_left HW (fold (Ide.micro I) xs (Micro.id (Ide.micro I))))
    as [Hunit Hreverse].
  split.
  - eapply leb_trans; [exact (lat_ok _ _ HM)| |exact Hforward].
    apply (fold_mono (Ide.values I) (Ide.micro I) HM); exact Hreverse.
  - eapply leb_trans; [exact (lat_ok _ _ HM)|exact Hback|].
    apply (fold_mono (Ide.values I) (Ide.micro I) HM); exact Hunit.
Qed.

End TabWeight.
