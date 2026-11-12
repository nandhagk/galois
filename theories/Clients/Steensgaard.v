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
  Lemma seed_kinds : forall q f, kind (D.view (seed q)) f = program_kind (compile q) f.
  Proof. Admitted. (* STUB *)
  Lemma seed_wf : forall q, D.wf (seed q) /\ D.canonical (seed q).
  Proof. Admitted. (* STUB *)
  Lemma solve_checked : forall q lim, let cp := R.plan (compile q) in
    solve q lim = if R.check_plan (compile q) cp then R.run (compile q) cp lim (seed q)
      else (IterLimit, seed q).
  Proof. Admitted. (* STUB *)
  Lemma points_spec : forall db x a, D.wf db -> D.canonical db ->
    reflect (exists i j, represents (D.view db) (Id i) (pointer_expression (Deref (Cell x))) /\
      represents (D.view db) (Id j) (pointer_expression (Cell a)) /\ same (D.view db) i j)
      (points db x a).
  Proof. Admitted. (* STUB *)
  Lemma solve_wf : forall q lim, D.wf (snd (solve q lim)) /\ D.canonical (snd (solve q lim)).
  Proof. Admitted. (* STUB *)
  Lemma solve_unifies : forall q lim db, solve q lim = (Saturated, db) ->
    forall x a, points db x a = true <-> pointer_congruence q (Deref (Cell x)) (Cell a).
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
  Lemma T_solve_le : forall q lim, let p := compile q in let cp := R.plan p in
    (T_solve q lim <= T_compile q + T_seed q + R.T_plan p + R.T_check_plan p cp +
      R.T_run p cp lim (seed q) + c_steensgaard)%N.
  Proof. Admitted. (* STUB *)
  Definition k_rules : N := 1. (* STUB *)
  Definition k_seed : N := 1. (* STUB *)
  Definition k_wrap : N := 1. (* STUB *)
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
  Lemma F5_equalities_source : forall q lim db t u i j,
    solve q lim = (Saturated, db) -> represents (D.view db) (Id i) (pointer_expression t) ->
    represents (D.view db) (Id j) (pointer_expression u) -> same (D.view db) i j ->
    pointer_congruence q t u.
  Proof. Admitted. (* STUB *)
  Lemma F6_step_covered : forall q instruction before after,
    In instruction (constraints q) ->
    memory_covered (fun x a => pointer_congruence q (Deref (Cell x)) (Cell a)) before ->
    pointer_exec instruction before = Some after ->
    memory_covered (fun x a => pointer_congruence q (Deref (Cell x)) (Cell a)) after.
  Proof. Admitted. (* STUB *)
  Lemma T1_wrapper : forall q lim, let p := compile q in let cp := R.plan p in
    (T_solve q lim <= T_compile q + T_seed q + R.T_plan p + R.T_check_plan p cp +
      R.T_run p cp lim (seed q) + k_wrap)%N.
  Proof. Admitted. (* STUB *)
End SteensgaardT.
