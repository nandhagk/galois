(** * Extended integer bounds

    Bounds include finite integers and both infinities.
    For example, the minimum of minus infinity and a finite bound is minus infinity.
    Builds on: Stdlib integer arithmetic. *)

From Stdlib Require Import ZArith Lia.

(** Bounds order the integers between two infinite endpoints. *)
Inductive bound : Type :=
  | NegInf
  | Fin (z : Z)
  | PosInf.

Definition bound_leb (a b : bound) : bool :=
  match a, b with
  | NegInf, _ => true
  | _, PosInf => true
  | Fin x, Fin y => Z.leb x y
  | _, _ => false
  end.

Definition bound_min (a b : bound) : bound :=
  if bound_leb a b then a else b.

Definition bound_max (a b : bound) : bound :=
  if bound_leb a b then b else a.

(** Every bound is below itself. *)
Theorem bound_leb_refl : forall a, bound_leb a a = true.
Proof.
  intros [|z|]; cbn; try reflexivity.
  apply Z.leb_refl.
Qed.

(** Bound comparison is transitive. *)
Theorem bound_leb_trans : forall a b c,
  bound_leb a b = true -> bound_leb b c = true -> bound_leb a c = true.
Proof.
  intros [|x|] [|y|] [|z|]; cbn; try discriminate; try reflexivity.
  intros Hxy Hyz. apply Z.leb_le in Hxy. apply Z.leb_le in Hyz.
  apply Z.leb_le. lia.
Qed.

(** Any two bounds are comparable. *)
Theorem bound_leb_total : forall a b, bound_leb a b = true \/ bound_leb b a = true.
Proof.
  intros [|x|] [|y|]; cbn; try (now left); try (now right).
  destruct (Z.leb x y) eqn:Hxy; [now left|right].
  apply Z.leb_gt in Hxy. apply Z.leb_le. lia.
Qed.

(** The minimum is below its left input. *)
Theorem bound_min_lower_l : forall a b, bound_leb (bound_min a b) a = true.
Proof.
  intros a b. unfold bound_min. destruct (bound_leb a b) eqn:Hab.
  - apply bound_leb_refl.
  - destruct (bound_leb_total a b) as [H|H]; congruence.
Qed.

(** The minimum is below its right input. *)
Theorem bound_min_lower_r : forall a b, bound_leb (bound_min a b) b = true.
Proof.
  intros a b. unfold bound_min. destruct (bound_leb a b) eqn:Hab.
  - exact Hab.
  - apply bound_leb_refl.
Qed.

(** A common lower bound is below the minimum. *)
Theorem bound_min_greatest : forall a b c,
  bound_leb c a = true -> bound_leb c b = true -> bound_leb c (bound_min a b) = true.
Proof.
  intros a b c Ha Hb. unfold bound_min. destruct (bound_leb a b); assumption.
Qed.

(** The maximum is above its left input. *)
Theorem bound_max_upper_l : forall a b, bound_leb a (bound_max a b) = true.
Proof.
  intros a b. unfold bound_max. destruct (bound_leb a b) eqn:Hab.
  - exact Hab.
  - apply bound_leb_refl.
Qed.

(** The maximum is above its right input. *)
Theorem bound_max_upper_r : forall a b, bound_leb b (bound_max a b) = true.
Proof.
  intros a b. unfold bound_max. destruct (bound_leb a b) eqn:Hab.
  - apply bound_leb_refl.
  - destruct (bound_leb_total a b) as [H|H]; congruence.
Qed.

(** The maximum is below every common upper bound. *)
Theorem bound_max_least : forall a b c,
  bound_leb a c = true -> bound_leb b c = true -> bound_leb (bound_max a b) c = true.
Proof.
  intros a b c Ha Hb. unfold bound_max. destruct (bound_leb a b); assumption.
Qed.
