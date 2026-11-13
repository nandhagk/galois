(** * Placeholder Steensgaard driver

    This driver provides the pointer analysis interface.
    For example, its placeholder query returns false.
    Builds on: SteensgaardSig. *)

From Stdlib Require Import List PArith NArith Bool.
From Argent Require Import Time Tactics Std.
From Galois.Base Require Import Trie.
From Galois.Egglog Require Import Syntax Model ValueSig IndexSig JoinSig DatabaseSig RunSig.
From Galois.Clients Require Import AndersenSig SteensgaardSig.
Import List.ListNotations.

Module SteensgaardCode (V : VALUE_OPS with Definition t := positive)
    (I : INDEX_OPS V) (J : JOIN_OPS V I) (D : DATABASE_OPS V I)
    (R : RUN_OPS V I J D) <: STEENSGAARD_OPS V I J D R.
  (* STUB-CODE *)
  Definition compile (_ : pointer_input) : program V.t := steensgaard_program.
  (* STUB-CODE *)
  Definition seed (_ : pointer_input) : D.t := D.init [] [].
  (* STUB-CODE *)
  Definition solve (q : pointer_input) (_ : limits) : stop * D.t := (IterLimit, seed q).
  (* STUB-CODE *)
  Definition points (_ : D.t) (_ _ : positive) : bool := false.
End SteensgaardCode.

Module Steensgaard (V : VALUE with Definition t := positive)
    (I : INDEX V) (J : JOIN V I) (D : DATABASE V I) (R : RUN V I J D) <: STEENSGAARD V I J D R.
  Include SteensgaardCode V I J D R.
  Lemma compile_rules : forall q, compile q = steensgaard_program.
  Proof. Admitted. (* STUB *)

  Lemma seed_rows : forall q f k o,
    row (D.view (seed q)) f k o <-> steensgaard_seed_row q f k o.
  Proof. Admitted. (* STUB *)

  Lemma seed_loaded : forall q, R.loaded (compile q) (R.plan (compile q)) (seed q).
  Proof. Admitted. (* STUB *)

  Lemma seed_wf : forall q, D.wf (seed q) /\ D.canonical (seed q).
  Proof. Admitted. (* STUB *)

  Lemma solve_run : forall q lim,
    solve q lim = R.run (compile q) (R.plan (compile q)) lim (seed q).
  Proof. Admitted. (* STUB *)

  Lemma points_spec : forall db x a, D.wf db -> D.canonical db ->
    reflect (exists i j, represents (D.view db) (Id i) (pointer_expression (Deref (Cell x))) /\
      represents (D.view db) (Id j) (pointer_expression (Cell a)) /\ same (D.view db) i j)
      (points db x a).
  Proof. Admitted. (* STUB *)

  Lemma solve_wf : forall q lim, D.wf (snd (solve q lim)) /\ D.canonical (snd (solve q lim)).
  Proof. Admitted. (* STUB *)

  Lemma solve_covers : forall q lim db, solve q lim = (Saturated, db) ->
    forall x a, pointer_congruence q (Deref (Cell x)) (Cell a) -> points db x a = true.
  Proof. Admitted. (* STUB *)

End Steensgaard.

Module SteensgaardT (V : VALUE_T with Definition t := positive)
    (I : INDEX_T V) (J : JOIN_T V I) (D : DATABASE_T V I) (R : RUN_T V I J D) <: STEENSGAARD_ALL V I J D R.
  Include Steensgaard V I J D R.
  TimeFun compile.
  TimeFun seed.
  TimeFun solve.
  TimeFun points.
  Definition c_steensgaard : N := 1. (* STUB *)
  Definition k_rules : N := 1. (* STUB *)
  Definition k_seed : N := 1. (* STUB *)
  Definition k_wrap : N := 1. (* STUB *)
  Lemma T_seed_le : forall q,
    (T_seed q <= c_steensgaard *
      N.of_nat (length (constraints q) + length (initial_pointers q) + 1) *
      N.of_nat (D.unit (seed q)) * N.of_nat (N.to_nat (N.log2 (D.ids (seed q))) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T_compile_le : forall q, (T_compile q <= c_steensgaard)%N.
  Proof. Admitted. (* STUB *)

  Lemma T_points_le : forall db x a, D.wf db ->
    (T_points db x a <= c_steensgaard * (N.of_nat (8 * D.unit db) +
      N.of_nat (cell_bits V.encode (Val x) + cell_bits V.encode (Val a)) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T_solve_le : forall q lim, let p := compile q in let cp := R.plan p in
    (T_solve q lim <= T_compile q + T_seed q + R.T_plan p +
      R.T_run p cp lim (seed q) + c_steensgaard)%N.
  Proof. Admitted. (* STUB *)

  Lemma F1_source_closed : forall q,
    pointer_closed q (fun x a => pointer_congruence q (Deref (Cell x)) (Cell a)).
  Proof. Admitted. (* STUB *)

  Lemma F2_inclusion_unifies : forall q x a, may_points q x a ->
    pointer_congruence q (Deref (Cell x)) (Cell a).
  Proof. Admitted. (* STUB *)

  Lemma F3_saturated_equations : forall q lim db, solve q lim = (Saturated, db) ->
    forall t u, pointer_congruence q t u ->
    forall i j, represents (D.view db) (Id i) (pointer_expression t) ->
      represents (D.view db) (Id j) (pointer_expression u) -> same (D.view db) i j.
  Proof. Admitted. (* STUB *)

  Lemma F4_endpoints_represented : forall q lim db x a,
    solve q lim = (Saturated, db) -> pointer_congruence q (Deref (Cell x)) (Cell a) ->
    (exists i, represents (D.view db) (Id i) (pointer_expression (Deref (Cell x)))) /\
    (exists j, represents (D.view db) (Id j) (pointer_expression (Cell a))).
  Proof. Admitted. (* STUB *)

  Lemma F6_step_covered : forall q instruction before after,
    In instruction (constraints q) ->
    memory_covered (fun x a => pointer_congruence q (Deref (Cell x)) (Cell a)) before ->
    pointer_exec instruction before = Some after ->
    memory_covered (fun x a => pointer_congruence q (Deref (Cell x)) (Cell a)) after.
  Proof. Admitted. (* STUB *)

  Lemma T1_wrapper : forall q lim, let p := compile q in let cp := R.plan p in
    (T_solve q lim <= T_compile q + T_seed q + R.T_plan p +
      R.T_run p cp lim (seed q) + k_wrap)%N.
  Proof. Admitted. (* STUB *)

End SteensgaardT.

Module SteensgaardSound (V : VALUE with Definition t := positive)
    (I : INDEX V) (J : JOIN V I) (D : DATABASE V I) (R : RUN V I J D)
    (A : STEENSGAARD V I J D R) (L : POINTER_LINK) <: STEENSGAARD_SOUND V I J D R A L.
  Lemma F1_source_closed : forall q,
    pointer_closed q (fun x a => pointer_congruence q (Deref (Cell x)) (Cell a)).
  Proof. Admitted. (* STUB *)

  Lemma F2_inclusion_unifies : forall q x a, may_points q x a ->
    pointer_congruence q (Deref (Cell x)) (Cell a).
  Proof. Admitted. (* STUB *)

  Lemma F6_step_covered : forall q instruction before after,
    In instruction (constraints q) ->
    memory_covered (fun x a => pointer_congruence q (Deref (Cell x)) (Cell a)) before ->
    pointer_exec instruction before = Some after ->
    memory_covered (fun x a => pointer_congruence q (Deref (Cell x)) (Cell a)) after.
  Proof. Admitted. (* STUB *)

  Lemma concrete_sound : forall q lim db s, A.solve q lim = (Saturated, db) ->
    pointer_reachable (L.initial q) (L.step q) s -> forall x a,
      trie_get x (L.memory s) = Some a -> A.points db x a = true.
  Proof. Admitted. (* STUB *)
End SteensgaardSound.

Module SteensgaardExact (V : VALUE with Definition t := positive)
    (I : INDEX V) (J : JOIN V I) (D : DATABASE V I) (R : RUN V I J D)
    (A : STEENSGAARD V I J D R) (Q : POINTER_QUOTIENT)
    <: STEENSGAARD_EXACT V I J D R A Q.
  Definition source_relation q f x y :=
    (f = 1%positive /\ (In (Addr x y) (constraints q) \/ In (x, y) (initial_pointers q))) \/
    (f = 2%positive /\ In (Copy x y) (constraints q)) \/
    (f = 3%positive /\ In (Load x y) (constraints q)) \/
    (f = 4%positive /\ In (Store x y) (constraints q)).
  Definition concrete_model q : model (V := V.t) :=
    Model (Q.carrier q)
      (fun f args => exists x y, args = [inr x; inr y] /\ source_relation q f x y)
      (fun f args =>
        match f, args with
        | 6%positive, [inr x] => Q.cell q x
        | 7%positive, [inl address] => Q.deref q address
        | _, _ => Q.cell q 1%positive
        end)
      (fun _ _ _ => False).
  (** Address constraints equate the pointer's dereference with the addressed cell. *)
  Lemma addr_equation : forall q x a,
    In (Addr x a) (constraints q) \/ In (x, a) (initial_pointers q) ->
    Q.deref q (Q.cell q x) = Q.cell q a.
  Proof. Admitted. (* STUB *)
  (** Copy constraints equate their two dereference terms. *)
  Lemma copy_equation : forall q x y, In (Copy x y) (constraints q) ->
    Q.deref q (Q.cell q x) = Q.deref q (Q.cell q y).
  Proof. Admitted. (* STUB *)
  (** Load constraints equate a result's dereference with the operand's second dereference. *)
  Lemma load_equation : forall q x y, In (Load x y) (constraints q) ->
    Q.deref q (Q.cell q x) = Q.deref q (Q.deref q (Q.cell q y)).
  Proof. Admitted. (* STUB *)
  (** Store constraints equate the destination's second dereference with the stored pointer. *)
  Lemma store_equation : forall q x y, In (Store x y) (constraints q) ->
    Q.deref q (Q.deref q (Q.cell q x)) = Q.deref q (Q.cell q y).
  Proof. Admitted. (* STUB *)
  (** Source equations establish validity of all generated union rules. *)
  Lemma rules_valid : forall q, valid V.prim V.merge (concrete_model q) (A.compile q).
  Proof. Admitted. (* STUB *)

  (** Saturated query answers are exactly the source congruence approximation. *)
  Lemma solve_exact : forall q lim db, A.solve q lim = (Saturated, db) ->
    forall x a, A.points db x a = true <-> pointer_congruence q (Deref (Cell x)) (Cell a).
  Proof. Admitted. (* STUB *)
End SteensgaardExact.
