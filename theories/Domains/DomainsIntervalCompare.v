(** * Boolean interval comparisons

    Separated endpoints decide comparisons and overlapping ranges retain both Boolean values.
    For example, every element of [0,3] is below every element of [5,10].
    Builds on: DomainsInterval. *)

From Stdlib Require Import ZArith List Bool Lia.
From Galois.Bits Require Import BitsWord.
From Galois.Domains Require Import DomainsBound DomainsInterval.

Local Open Scope Z_scope.

Definition interval_truth (decision : option bool) : interval :=
  match decision with
  | Some true => Itv (Fin 1) (Fin 1)
  | Some false => Itv (Fin 0) (Fin 0)
  | None => Itv (Fin 0) (Fin 1)
  end.

(** A decision contains its Boolean result whenever each decided case is justified. *)
Theorem interval_truth_sound : forall w decision value,
  (decision = Some true -> value = true) -> (decision = Some false -> value = false) ->
  interval_pgamma w (interval_truth decision) (if value then 1 else 0).
Proof.
  intros w [[|]|] value Htrue Hfalse; destruct value; cbn in *;
    try (exfalso; specialize (Htrue eq_refl); discriminate);
    try (exfalso; specialize (Hfalse eq_refl); discriminate);
    split; try apply one_is_word; try apply zero_is_word; split; reflexivity.
Qed.

Definition interval_bool_not (a : interval) : interval :=
  match interval_finite a with
  | Some (lo, hi) =>
    if Z.eqb lo 0 && Z.eqb hi 0 then interval_truth (Some true)
    else if Z.eqb lo 1 && Z.eqb hi 1 then interval_truth (Some false)
    else interval_truth None
  | None => interval_truth None
  end.

(** Boolean complement retains every complemented Boolean input. *)
Theorem interval_bool_not_sound : forall w a (b : bool),
  interval_pgamma w a (if b then 1 else 0) ->
  interval_pgamma w (interval_bool_not a) (if negb b then 1 else 0).
Proof.
  intros w a b Ha. unfold interval_bool_not.
  destruct (interval_finite a) as [[lo hi]|] eqn:Hfinite;
    [|apply interval_truth_sound; discriminate].
  pose proof (interval_finite_sound w a lo hi (if b then 1 else 0) Ha Hfinite) as Hbounds.
  destruct (Z.eqb lo 0 && Z.eqb hi 0)%bool eqn:Hzero.
  - apply andb_true_iff in Hzero as [Hlo Hhi]. apply Z.eqb_eq in Hlo. apply Z.eqb_eq in Hhi.
    destruct b; cbn in Hbounds; [lia|].
    apply interval_truth_sound; [reflexivity|discriminate].
  - destruct (Z.eqb lo 1 && Z.eqb hi 1)%bool eqn:Hone.
    + apply andb_true_iff in Hone as [Hlo Hhi]. apply Z.eqb_eq in Hlo. apply Z.eqb_eq in Hhi.
      destruct b; cbn in Hbounds; [|lia].
      apply interval_truth_sound; [discriminate|reflexivity].
    + apply interval_truth_sound; discriminate.
Qed.

Definition interval_ult (a b : interval) : interval :=
  match interval_finite a, interval_finite b with
  | Some (la, ha), Some (lb, hb) =>
    interval_truth (if Z.ltb ha lb then Some true
                    else if Z.leb hb la then Some false else None)
  | _, _ => interval_truth None
  end.

(** Strict comparison contains every comparison of represented unsigned integers. *)
Theorem interval_ult_sound : forall wa wb a b x y w,
  interval_pgamma wa a x -> interval_pgamma wb b y ->
  interval_pgamma w (interval_ult a b) (if Z.ltb x y then 1 else 0).
Proof.
  intros wa wb a b x y w Ha Hb. unfold interval_ult.
  destruct (interval_finite a) as [[la ha]|] eqn:Hfa;
    destruct (interval_finite b) as [[lb hb]|] eqn:Hfb;
    try (apply interval_truth_sound; discriminate).
  pose proof (interval_finite_sound wa a la ha x Ha Hfa) as Hax.
  pose proof (interval_finite_sound wb b lb hb y Hb Hfb) as Hby.
  destruct (Z.ltb ha lb) eqn:Htrue.
  - apply Z.ltb_lt in Htrue. apply interval_truth_sound; [|discriminate].
    intros _. apply Z.ltb_lt. lia.
  - destruct (Z.leb hb la) eqn:Hfalse.
    + apply Z.leb_le in Hfalse. apply interval_truth_sound; [discriminate|].
      intros _. apply Z.ltb_ge. lia.
    + apply interval_truth_sound; discriminate.
Qed.

Definition interval_ule (a b : interval) : interval :=
  match interval_finite a, interval_finite b with
  | Some (la, ha), Some (lb, hb) =>
    interval_truth (if Z.leb ha lb then Some true
                    else if Z.ltb hb la then Some false else None)
  | _, _ => interval_truth None
  end.

(** Non-strict comparison contains every comparison of represented unsigned integers. *)
Theorem interval_ule_sound : forall wa wb a b x y w,
  interval_pgamma wa a x -> interval_pgamma wb b y ->
  interval_pgamma w (interval_ule a b) (if Z.leb x y then 1 else 0).
Proof.
  intros wa wb a b x y w Ha Hb. unfold interval_ule.
  destruct (interval_finite a) as [[la ha]|] eqn:Hfa;
    destruct (interval_finite b) as [[lb hb]|] eqn:Hfb;
    try (apply interval_truth_sound; discriminate).
  pose proof (interval_finite_sound wa a la ha x Ha Hfa) as Hax.
  pose proof (interval_finite_sound wb b lb hb y Hb Hfb) as Hby.
  destruct (Z.leb ha lb) eqn:Htrue.
  - apply Z.leb_le in Htrue. apply interval_truth_sound; [|discriminate].
    intros _. apply Z.leb_le. lia.
  - destruct (Z.ltb hb la) eqn:Hfalse.
    + apply Z.ltb_lt in Hfalse. apply interval_truth_sound; [discriminate|].
      intros _. apply Z.leb_gt. lia.
    + apply interval_truth_sound; discriminate.
Qed.

Definition interval_eq (a b : interval) : interval :=
  match interval_finite a, interval_finite b with
  | Some (la, ha), Some (lb, hb) =>
    interval_truth (if (Z.ltb ha lb || Z.ltb hb la)%bool then Some false
      else if (Z.eqb la ha && Z.eqb lb hb && Z.eqb la lb)%bool then Some true else None)
  | _, _ => interval_truth None
  end.

(** Equality contains every equality test of represented integers. *)
Theorem interval_eq_sound : forall wa wb a b x y w,
  interval_pgamma wa a x -> interval_pgamma wb b y ->
  interval_pgamma w (interval_eq a b) (if Z.eqb x y then 1 else 0).
Proof.
  intros wa wb a b x y w Ha Hb. unfold interval_eq.
  destruct (interval_finite a) as [[la ha]|] eqn:Hfa;
    destruct (interval_finite b) as [[lb hb]|] eqn:Hfb;
    try (apply interval_truth_sound; discriminate).
  pose proof (interval_finite_sound wa a la ha x Ha Hfa) as Hax.
  pose proof (interval_finite_sound wb b lb hb y Hb Hfb) as Hby.
  destruct (Z.ltb ha lb || Z.ltb hb la)%bool eqn:Hdisjoint.
  - assert (Hneq : x <> y).
    { apply orb_true_iff in Hdisjoint as [Hdisjoint|Hdisjoint];
        apply Z.ltb_lt in Hdisjoint; lia. }
    apply interval_truth_sound; [discriminate|]. intros _. now apply Z.eqb_neq.
  - destruct (Z.eqb la ha && Z.eqb lb hb && Z.eqb la lb)%bool eqn:Hpoint.
    + repeat rewrite andb_true_iff in Hpoint. destruct Hpoint as [[Ha' Hb'] Hab].
      apply Z.eqb_eq in Ha'. apply Z.eqb_eq in Hb'. apply Z.eqb_eq in Hab.
      apply interval_truth_sound; [intros _; apply Z.eqb_eq; lia|discriminate].
    + apply interval_truth_sound; discriminate.
Qed.
