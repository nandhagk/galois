(** * Tactics on encoded values and primitives

    The lemmas that the command [Egglog] of [Derive.v] generates relate values to their
    encodings, and calls of primitive functions to their results. These tactics decode an
    encoding back to its value, evaluate a call of a primitive function on encoded arguments,
    and read a hypothesis on such a call as decoded arguments and an encoded result. The
    tactics of the glue lemmas call them by name.

    For example, [egglog_inj] turns a hypothesis [encode x = encode y] of a registered encoder
    into [x = y].

    Builds on: the definitions that derived programs call. *)

From Stdlib Require Import List PArith.
From Galois.Front Require Import DeriveHelpers.

Import List.ListNotations.

(** * Decoding values *)

(** A value whose encoding is a known positive: decoding the equation [encode x = k] gives the
    value [x]. *)
Ltac egglog_decode_literal Hinj e x :=
  let E := fresh "E" in
  eassert (_ (e x) = Some x) as E by (eauto with egglog_decode);
  rewrite Hinj in E; cbv in E;
  injection E as E; clear Hinj; subst.

(** Equal encodings come from equal values: the injectivity lemma of each registered encoder
    turns a hypothesis [encode x = encode y] into [x = y], and the decoder turns [encode x = k]
    for a literal [k] into the value of [k]. *)
Ltac egglog_inj :=
  repeat match goal with
  | Hinj : ?e ?x = ?e ?y |- _ =>
      let E := fresh "E" in
      assert (x = y) as E by (eauto with egglog_inj);
      clear Hinj; try subst
  | Hinj : ?e ?x = _ |- _ => is_var x; egglog_decode_literal Hinj e x
  | Hinj : _ = ?e ?x |- _ => is_var x; symmetry in Hinj; egglog_decode_literal Hinj e x
  end.

(** A hypothesis [d (e x) = Some y] that decodes an encoding gives [x = y]. *)
Ltac egglog_decoded H :=
  cbv [id_decode id_encode] in H;
  try match type of H with
  | ?d (?e ?x) = Some _ =>
      let E := fresh "E" in
      assert (d (e x) = Some x) as E by (eauto with egglog_decode);
      rewrite E in H; clear E
  end;
  injection H; clear H; intros; try subst.

(** * Calls of primitive functions *)

(** Unfold the primitive function of a set in the goal, down to the call of its function. *)
Ltac egglog_unfold_prims :=
  repeat match goal with
  | |- context [?p ?q ?vs] =>
      lazymatch type of p with
      | positive -> list positive -> option positive => is_const p; unfold p
      end
  end;
  cbv [prim_case Pos.eqb].

(** Replace each call of a primitive function on encodings by the encoding of its result. *)
Ltac egglog_eval_prims :=
  repeat match goal with
  | |- context [@prim1d _ _ ?da ?er ?f [?a]] =>
      let E := fresh "E" in
      eassert (prim1d da er f [a] = Some _) as E
        by (eapply prim1d_some; eauto with egglog_decode);
      rewrite E; clear E
  | |- context [@prim2d _ _ _ ?da ?db ?er ?f [?a; ?b]] =>
      let E := fresh "E" in
      eassert (prim2d da db er f [a; b] = Some _) as E
        by (eapply prim2d_some; eauto with egglog_decode);
      rewrite E; clear E
  | |- context [@prim3d _ _ _ _ ?da ?db ?dc ?er ?f [?a; ?b; ?c]] =>
      let E := fresh "E" in
      eassert (prim3d da db dc er f [a; b; c] = Some _) as E
        by (eapply prim3d_some; eauto with egglog_decode);
      rewrite E; clear E
  end.

(** An equation between the values of patterns, which holds by evaluation of the primitives. *)
Ltac egglog_values :=
  simpl; egglog_unfold_prims; egglog_eval_prims; simpl; reflexivity.

(** A call of a primitive function on encoded arguments has the encoded result, which an
    equation premise [f x1 .. xn = w] names. *)
Ltac egglog_prim_goal :=
  lazymatch goal with
  | |- ?p _ _ = _ =>
      unfold p; cbv [prim_case Pos.eqb];
      first [eapply prim1d_some | eapply prim2d_some | eapply prim3d_some];
      eauto with egglog_decode
  end.

(** The goal [prim q vs = Some w] from a premise [f x1 .. xn = w] among the hypotheses. *)
Ltac egglog_prim_leaf :=
  match goal with
  | H : _ = _ |- _ = Some _ =>
      try rewrite <- H; first [reflexivity | egglog_prim_goal]
  end.

(** A hypothesis [p q vs = Some w] on the call of a primitive function: the arguments decode to
    values, and [w] is the encoding of the result. *)
Ltac egglog_prim_in H :=
  try (lazymatch type of H with
       | ?p _ _ = _ => is_const p; unfold p in H
       end);
  cbv [prim_case Pos.eqb] in H;
  first
    [ apply prim1d_inv in H; destruct H as [? [Ha Hw]]; egglog_decoded Ha
    | apply prim2d_inv in H; destruct H as [? [? [Ha [Hb Hw]]]];
      egglog_decoded Ha; egglog_decoded Hb
    | apply prim3d_inv in H; destruct H as [? [? [? [Ha [Hb [Hc Hw]]]]]];
      egglog_decoded Ha; egglog_decoded Hb; egglog_decoded Hc ];
  subst.
