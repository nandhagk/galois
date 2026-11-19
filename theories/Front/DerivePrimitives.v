(** * Tactics on encoded values and primitives

    The lemmas that the command [Egglog] of [Derive.v] generates relate values to their
    encodings, and calls of primitive functions to their results. These tactics decode an
    encoding back to its value, evaluate a call of a primitive function on encoded arguments,
    and read a hypothesis on such a call as decoded arguments and an encoded result. A call
    takes one step for each argument, so the tactics repeat a step until the call ends, and they
    handle primitives of every arity. The tactics of the glue lemmas call them by name.

    For example, [egglog_inj] turns a hypothesis [encode x = encode y] of a registered encoder,
    or of the encoder of pairs, options or lists of such values, into [x = y].

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

(** Equal encodings come from equal values: the injectivity lemma of each registered encoder,
    or else the decoder of the encoding, turns a hypothesis [encode x = encode y] into [x = y].
    The decoder turns [encode x = k] for a literal [k] into the value of [k]. *)
Ltac egglog_inj :=
  repeat match goal with
  | Hinj : ?e ?x = ?e ?y |- _ =>
      let E := fresh "E" in
      assert (x = y) as E
        by (first
              [ solve [eauto with egglog_inj]
              | eapply (encode_inj_of e); [intros; eauto with egglog_decode | exact Hinj] ]);
      clear Hinj; try subst
  | Hinj : ?e ?x = _ |- _ => is_var x; egglog_decode_literal Hinj e x
  | Hinj : _ = ?e ?x |- _ => is_var x; symmetry in Hinj; egglog_decode_literal Hinj e x
  end.

(** A hypothesis [d (e x) = Some y] that decodes an encoding gives [x = y]. *)
Ltac egglog_decoded H :=
  try match type of H with
  | ?d (?e ?x) = Some _ =>
      let E := fresh "E" in
      assert (d (e x) = Some x) as E by (eauto with egglog_decode);
      rewrite E in H; clear E
  end;
  cbv [id_decode id_encode] in H;
  injection H; clear H; intros; try subst.

(** * Calls of primitive functions

    The primitive function of a set tests the code of a call against the code of each of its
    functions. A code is a constant, so these tactics select the call with [prim_case_hit] and
    [prim_case_miss], whose conditions [reflexivity] computes, and they never reduce the call of
    another function. *)

(** Prove the goal [d a = Some x] of a step of a call, whose argument [a] is an encoding or a
    positive without variables that [d] decodes by computation. *)
Ltac egglog_decode_arg :=
  first [solve [eauto with egglog_decode] | reflexivity].

(** Select the call of each primitive function in the goal by its code. *)
Ltac egglog_dispatch :=
  repeat first
    [ rewrite prim_case_hit by reflexivity
    | rewrite prim_case_miss by reflexivity ].

(** Select the call of the primitive function in the hypothesis [H] by its code. *)
Ltac egglog_dispatch_in H :=
  repeat first
    [ rewrite prim_case_hit in H by reflexivity
    | rewrite prim_case_miss in H by reflexivity ].

(** Unfold the primitive function of a set in the goal, down to the call of its function. *)
Ltac egglog_unfold_prims :=
  repeat match goal with
  | |- context [?p ?q ?vs] =>
      lazymatch type of p with
      | positive -> list positive -> option positive => is_const p; unfold p
      end
  end;
  cbv beta; egglog_dispatch.

(** Replace each call of a primitive function on encodings by the encoding of its result, one
    step at a time. *)
Ltac egglog_eval_prims :=
  repeat match goal with
  | |- context [@prim_arg ?A ?F ?da ?k ?f (?a :: ?vs)] =>
      let E := fresh "E" in
      eassert (@prim_arg A F da k f (a :: vs) = k (f _) vs) as E
        by (eapply prim_arg_cons; egglog_decode_arg);
      rewrite E; clear E
  | |- context [@prim_ret ?R ?er ?r []] => rewrite (prim_ret_nil er r)
  end.

(** An equation between the values of patterns, which holds by evaluation of the primitives. *)
Ltac egglog_values :=
  simpl; egglog_unfold_prims; egglog_eval_prims; simpl; reflexivity.

(** A call of a primitive function on encoded arguments has the encoded result, which an
    equation premise [f x1 .. xn = w] names. *)
Ltac egglog_prim_goal :=
  lazymatch goal with
  | |- ?p _ _ = _ =>
      unfold p; cbv beta; egglog_dispatch;
      repeat (erewrite prim_arg_cons by egglog_decode_arg);
      apply prim_ret_nil
  end.

(** The goal [prim q vs = Some w] from a premise [f x1 .. xn = w] among the hypotheses. *)
Ltac egglog_prim_leaf :=
  match goal with
  | H : _ = _ |- _ = Some _ =>
      try rewrite <- H; first [reflexivity | egglog_prim_goal]
  end.

(** A hypothesis [p q vs = Some w] on the call of a primitive function: the arguments decode to
    values, and [w] is the encoding of the result. *)
Ltac egglog_prim_call_in H :=
  try (lazymatch type of H with
       | ?p _ _ = _ => is_const p; unfold p in H
       end);
  cbv beta in H; egglog_dispatch_in H;
  repeat (apply prim_arg_inv in H;
          let Ha := fresh "Ha" in
          destruct H as [? [Ha H]]; egglog_decoded Ha);
  apply prim_ret_inv in H; subst.

(** A hypothesis [H] on the values of patterns that call primitive functions on encodings, such
    as the values of a conclusion [R (f x)]. Each call becomes the encoding of its result, and
    [H] becomes the equation of the values that are left. A call on encodings of [positive]
    reduces by computation. A call on the encoding of a registered type needs the decoder
    lemmas. *)
Ltac egglog_prim_values_in H :=
  progress (
    repeat match type of H with
    | context [?p ?q ?vs] =>
        lazymatch type of p with
        | positive -> list positive -> option positive => is_const p; unfold p in H
        end
    end;
    cbv beta in H; egglog_dispatch_in H;
    repeat match type of H with
    | context [@prim_arg ?A ?F ?da ?k ?f (?a :: ?vs)] =>
        let E := fresh "E" in
        eassert (@prim_arg A F da k f (a :: vs) = k (f _) vs) as E
          by (eapply prim_arg_cons; egglog_decode_arg);
        rewrite E in H; clear E
    | context [@prim_ret ?R ?er ?r []] => rewrite (prim_ret_nil er r) in H
    end);
  simpl in H;
  try (injection H; clear H; intros; try subst).

(** A hypothesis [H] on a call of a primitive function, or on values of patterns with such
    calls. *)
Ltac egglog_prim_in H :=
  first [egglog_prim_call_in H | egglog_prim_values_in H].
