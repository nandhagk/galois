(** * Client bridges and width-changing expressions

    A successful client operation can be represented by a generic word expression.
    For example, an addition bridge applies the target operator to variables zero and one.
    Builds on: BitsWord, BitsFun, BitsArith, BitsOp and BitsExpr. *)

From Stdlib Require Import ZArith List Bool Lia Ring.
From Galois.Bits Require Import BitsWord BitsFun BitsArith BitsOp BitsExpr.
Import List.ListNotations Expr.

Open Scope Z_scope.

(** An operator bridge preserves every successful client result. *)
Definition bridge_op {O O' V} (client_eval : O -> list V -> option V)
  (to_bits : V -> word) (ev : O' -> list word -> option word) (bridge : O -> O') : Prop :=
  forall o xs r, client_eval o xs = Some r ->
    ev (bridge o) (map to_bits xs) = Some (to_bits r).

(** An expression bridge uses normalized arguments and a one-bit zero default environment. *)
Definition bridge_expr {O O' V} (client_eval : O -> list V -> option V)
  (to_bits : V -> word) (ev : O' -> list word -> option word)
  (bridge : O -> Expr.t O') : Prop :=
  forall o xs r, client_eval o xs = Some r ->
    eval ev (env_of (1%positive, 0) (map to_bits xs)) (bridge o) = Some (to_bits r).

(** Evaluating consecutive variables normalizes consecutive environment entries. *)
Theorem eval_variable_sequence : forall {O} (ev : O -> list word -> option word) env n start,
  eval_args ev env (map Var (seq start n)) =
    Some (map (fun i => normalize_word (env i)) (seq start n)).
Proof.
  intros O ev env n. induction n as [|n IH]; intro start.
  - reflexivity.
  - cbn [seq map]. rewrite eval_args_cons, eval_var, IH. reflexivity.
Qed.

Local Lemma nth_sequence : forall (A : Type) (d : A) xs,
  map (fun i => nth i xs d) (seq 0 (length xs)) = xs.
Proof.
  intros A d xs. induction xs as [|x xs IH]; [reflexivity|].
  cbn [length seq map nth]. rewrite <- seq_shift, map_map. cbn. now rewrite IH.
Qed.

(** Enumerating exactly the normalized input words recovers the input list for any default. *)
Theorem eval_vars_words : forall {O} (ev : O -> list word -> option word) d xs,
  (forall x, In x xs -> is_word (fst x) (snd x)) ->
  eval_args ev (env_of d xs) (vars (length xs)) = Some xs.
Proof.
  intros O ev d xs Hwords. unfold vars. rewrite eval_variable_sequence.
  unfold env_of. rewrite <- map_map, nth_sequence.
  f_equal. transitivity (map (fun x : word => x) xs); [|apply map_id].
  apply map_ext_in. intros [w x] Hin. unfold normalize_word. cbn.
  rewrite wrap_id; [reflexivity|exact (Hwords (w, x) Hin)].
Qed.

(** Every arity-correct operator bridge induces a bridge through consecutive variables. *)
Theorem bridge_op_expr : forall {O O' V : Type}
  (client_eval : O -> list V -> option V) (to_bits : V -> word)
  (ev : O' -> list word -> option word) (arity : O' -> nat) (bridge : O -> O'),
  (forall o xs r, ev o xs = Some r -> length xs = arity o) ->
  (forall v, is_word (fst (to_bits v)) (snd (to_bits v))) ->
  bridge_op client_eval to_bits ev bridge ->
  bridge_expr client_eval to_bits ev (fun o => App (bridge o) (vars (arity (bridge o)))).
Proof.
  intros O O' V client_eval to_bits ev arity bridge Harity Hwords Hbridge o xs r Hclient.
  specialize (Hbridge o xs r Hclient).
  pose proof (Harity _ _ _ Hbridge) as Hlength.
  rewrite eval_app, <- Hlength, eval_vars_words.
  - exact Hbridge.
  - intros x Hin. apply in_map_iff in Hin as [v [<- _]]. apply Hwords.
Qed.

(** The Bits evaluator supplies the arity premise of the generic bridge theorem. *)
Theorem bridge_op_expr_bits : forall {O V : Type}
  (client_eval : O -> list V -> option V) (to_bits : V -> word) (bridge : O -> op),
  (forall v, is_word (fst (to_bits v)) (snd (to_bits v))) ->
  bridge_op client_eval to_bits eval_op bridge ->
  bridge_expr client_eval to_bits eval_op (fun o => App (bridge o) (vars (arity (bridge o)))).
Proof.
  intros O V client_eval to_bits bridge Hwords Hbridge.
  apply bridge_op_expr; [apply eval_op_arity|exact Hwords|exact Hbridge].
Qed.

(** * Width-changing expression laws *)

(** Zero extension preserves the normalized unsigned value. *)
Theorem zext_value : forall env w n x, env 0%nat = (w, x) ->
  eval eval_op env (App (bvzext n) [Var 0]) = Some ((w + n)%positive, wrap w x).
Proof.
  intros env w n x Henv.
  rewrite eval_app, eval_args_cons, eval_var, Henv, eval_args_nil.
  change (eval_op (bvzext n) [(w, wrap w x)] = Some ((w + n)%positive, wrap w x)).
  rewrite eval_zext_value, wrap_wrap. reflexivity.
Qed.

(** Sign extension wraps the original signed interpretation at the larger width. *)
Theorem sext_value : forall env w n x, env 0%nat = (w, x) ->
  eval eval_op env (App (bvsext n) [Var 0]) =
    Some ((w + n)%positive, wrap (w + n)%positive (signed w x)).
Proof.
  intros env w n x Henv.
  rewrite eval_app, eval_args_cons, eval_var, Henv, eval_args_nil.
  change (eval_op (bvsext n) [(w, wrap w x)] =
    Some ((w + n)%positive, wrap (w + n)%positive (signed w x))).
  rewrite eval_sext_value, signed_wrap. reflexivity.
Qed.

(** Sign extension preserves the signed value. *)
Theorem sext_signed : forall env w n x, env 0%nat = (w, x) -> exists z,
  eval eval_op env (App (bvsext n) [Var 0]) = Some ((w + n)%positive, z) /\
  signed (w + n)%positive z = signed w x.
Proof.
  intros env w n x Henv. exists (wrap (w + n)%positive (signed w x)).
  split; [now apply sext_value|]. rewrite signed_wrap. apply signed_id.
  pose proof (signed_range w x).
  pose proof (half_monotone w (w + n)%positive (width_add_le w n)). lia.
Qed.

(** A successful expression can be truncated to any no-wider target width. *)
Theorem eval_trunc_value : forall env e w t x, eval eval_op env e = Some (w, x) ->
  (t <= w)%positive -> eval eval_op env (App (bvtrunc t) [e]) = Some (t, wrap t x).
Proof.
  intros env e w t x Heval Hle.
  rewrite eval_app, eval_args_cons, Heval, eval_args_nil.
  now apply BitsOp.eval_trunc_value.
Qed.

(** Truncating a zero extension recovers the original word. *)
Theorem trunc_zext : forall env w n x, env 0%nat = (w, x) ->
  eval eval_op env (App (bvtrunc w) [App (bvzext n) [Var 0]]) = Some (w, wrap w x).
Proof.
  intros env w n x Henv. rewrite <- (wrap_wrap w x).
  eapply eval_trunc_value; [now apply zext_value|apply width_add_le].
Qed.

(** Truncating a sign extension recovers the original word. *)
Theorem trunc_sext : forall env w n x, env 0%nat = (w, x) ->
  eval eval_op env (App (bvtrunc w) [App (bvsext n) [Var 0]]) = Some (w, wrap w x).
Proof.
  intros env w n x Henv.
  pose proof (eval_trunc_value env (App (bvsext n) [Var 0])
    (w + n)%positive w _ (sext_value env w n x Henv) (width_add_le w n)) as Htrunc.
  rewrite wrap_narrow, wrap_signed in Htrunc by apply width_add_le. exact Htrunc.
Qed.

(** Truncation commutes with word addition. *)
Theorem trunc_wadd : forall env w t x y,
  env 0%nat = (w, x) -> env 1%nat = (w, y) -> (t <= w)%positive ->
  eval eval_op env (App (bvtrunc t) [App bvadd [Var 0; Var 1]]) = Some (t, wadd t x y).
Proof.
  intros env w t x y Hx Hy Hle.
  assert (Hadd : eval eval_op env (App bvadd [Var 0; Var 1]) = Some (w, wadd w x y)).
  { rewrite eval_app, !eval_args_cons, !eval_var, eval_args_nil, Hx, Hy.
    change (eval_op bvadd [(w, wrap w x); (w, wrap w y)] = Some (w, wadd w x y)).
    rewrite (eval_op_fun2 bvadd w _ _ wadd eq_refl).
    unfold wadd. now rewrite <- wrap_add. }
  pose proof (eval_trunc_value env _ w t _ Hadd Hle) as Htrunc.
  unfold wadd in *. rewrite wrap_narrow in Htrunc by exact Hle. exact Htrunc.
Qed.

(** Concatenation expressions place their first operand above their second. *)
Theorem eval_concat_value : forall env w w2 x y,
  env 0%nat = (w, x) -> env 1%nat = (w2, y) ->
  eval eval_op env (App bvconcat [Var 0; Var 1]) =
    Some ((w + w2)%positive, wrap w x * modulus w2 + wrap w2 y).
Proof.
  intros env w w2 x y Hx Hy.
  rewrite eval_app, !eval_args_cons, !eval_var, eval_args_nil, Hx, Hy.
  change (eval_op bvconcat [(w, wrap w x); (w2, wrap w2 y)] =
    Some ((w + w2)%positive, wrap w x * modulus w2 + wrap w2 y)).
  rewrite BitsOp.eval_concat_value, !wrap_wrap. reflexivity.
Qed.

(** Truncation of a concatenation recovers its low operand. *)
Theorem trunc_concat_lo : forall env w w2 x y,
  env 0%nat = (w, x) -> env 1%nat = (w2, y) ->
  eval eval_op env (App (bvtrunc w2) [App bvconcat [Var 0; Var 1]]) = Some (w2, wrap w2 y).
Proof.
  intros env w w2 x y Hx Hy.
  assert (Hle : (w2 <= w + w2)%positive).
  { rewrite Pos.add_comm. apply width_add_le. }
  pose proof (eval_trunc_value env _ _ w2 _ (eval_concat_value env w w2 x y Hx Hy) Hle)
    as Htrunc.
  replace (wrap w x * modulus w2 + wrap w2 y) with
    (wrap w2 y + wrap w x * modulus w2) in Htrunc by ring.
  rewrite wrap_add_modulus, wrap_wrap in Htrunc. exact Htrunc.
Qed.

(** Extracting the high positions of a concatenation recovers its first operand. *)
Theorem extract_concat_hi : forall env w w2 x y,
  env 0%nat = (w, x) -> env 1%nat = (w2, y) ->
  eval eval_op env (App
    (bvextract (Pos.to_nat (w + w2)%positive - 1)%nat (Pos.to_nat w2))
    [App bvconcat [Var 0; Var 1]]) = Some (w, wrap w x).
Proof.
  intros env w w2 x y Hx Hy. rewrite eval_app, eval_args_cons,
    (eval_concat_value env w w2 x y Hx Hy), eval_args_nil.
  assert (Hw : (0 < Pos.to_nat w)%nat) by apply Pos2Nat.is_pos.
  assert (Hw2 : (0 < Pos.to_nat w2)%nat) by apply Pos2Nat.is_pos.
  assert (Hwidth : result_width
    (bvextract (Pos.to_nat (w + w2)%positive - 1) (Pos.to_nat w2))
    [(w + w2)%positive] = Some w).
  { change ((if (Nat.leb (Pos.to_nat w2) (Pos.to_nat (w + w2)%positive - 1) &&
      Nat.ltb (Pos.to_nat (w + w2)%positive - 1) (Pos.to_nat (w + w2)%positive))%bool
      then Some (Pos.of_nat (S (Pos.to_nat (w + w2)%positive - 1 - Pos.to_nat w2)))
      else None) = Some w).
    rewrite Pos2Nat.inj_add.
    rewrite (proj2 (Nat.leb_le (Pos.to_nat w2)
      (Pos.to_nat w + Pos.to_nat w2 - 1)) ltac:(lia)),
      (proj2 (Nat.ltb_lt (Pos.to_nat w + Pos.to_nat w2 - 1)
        (Pos.to_nat w + Pos.to_nat w2)) ltac:(lia)). cbn [andb].
    replace (S (Pos.to_nat w + Pos.to_nat w2 - 1 - Pos.to_nat w2))%nat
      with (Pos.to_nat w) by lia.
    now rewrite Pos2Nat.id. }
  change ((match result_width
    (bvextract (Pos.to_nat (w + w2)%positive - 1) (Pos.to_nat w2)) [(w + w2)%positive]
    with
    | Some rw => Some (rw, wrap rw
        (wrap (w + w2)%positive (wrap w x * modulus w2 + wrap w2 y) /
          2 ^ Z.of_nat (Pos.to_nat w2)))
    | None => None
    end) = Some (w, wrap w x)).
  rewrite Hwidth.
  rewrite (wrap_id (w + w2)%positive _ (concat_is_word w w2 x y)).
  rewrite positive_nat_Z. fold (modulus w2).
  replace (wrap w x * modulus w2 + wrap w2 y) with
    (wrap w2 y + wrap w x * modulus w2) by ring.
  rewrite Z.div_add by apply modulus_nonzero.
  rewrite Z.div_small by apply wrap_is_word.
  rewrite Z.add_0_l, wrap_wrap. reflexivity.
Qed.
