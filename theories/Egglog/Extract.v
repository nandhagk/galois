(** * Placeholder expression extraction

    These operations provide the interfaces for extraction and certificate checking.
    For example, the placeholder extractor returns no certificate.
    Builds on: ExtractSig. *)

From Stdlib Require Import List PArith NArith Relations.Relation_Operators.
From Argent Require Import Time Tactics Std Loop.
From Galois.Egglog Require Import ValueSig IndexSig DatabaseSig Syntax Model ExtractSig.

Import List.ListNotations.

Module ExtractCode (V : VALUE_OPS) (I : INDEX_OPS V) (D : DATABASE_OPS V I)
    (C : COST_OPS V) <: EXTRACT_OPS V I D C.
  (* STUB-CODE *)
  Definition best (_ : D.t) : extraction_best V.t := [].
  (* STUB-CODE *)
  Definition extract (_ : D.t) (_ : positive) : option (extraction_dag V.t) := None.
  (* STUB-CODE *)
  Definition check_dag (_ : D.t) (_ : positive) (_ : extraction_dag V.t) : option N := None.
End ExtractCode.

Module Extract (V : VALUE) (I : INDEX V) (D : DATABASE V I) (C : COST V)
    <: EXTRACT V I D C.
  Include ExtractCode V I D C.
  Include EXTRACT_SPEC V I D C.
  Definition dag_cost (_ : extraction_dag V.t) : N := 0%N.
  Definition unfold (_ : extraction_dag V.t) (_ : positive) : option (@Model.expr V.t) := None.
  Lemma unfold_spec : forall g c e, NoDup (map fst g) ->
    (unfold g c = Some e <-> dag_represents g c e).
  Proof. Admitted. (* STUB *)
  Lemma best_row : forall db c n f k, D.wf db -> D.canonical db ->
    In (c, (n, (f, k))) (best db) ->
    row (D.view db) f k (Some (Id c)) /\
      n = C.fn_cost f (map (cost_of (best db)) k).
  Proof. Admitted. (* STUB *)
  Lemma best_optimal : forall db c e, D.wf db -> D.canonical db ->
    represents (D.view db) (Id c) e ->
    exists n ch, In (c, (n, ch)) (best db) /\ (n <= tree_cost e)%N.
  Proof. Admitted. (* STUB *)
  Lemma best_attained : forall db c n ch, D.wf db -> D.canonical db ->
    In (c, (n, ch)) (best db) ->
    exists e, represents (D.view db) (Id c) e /\ tree_cost e = n.
  Proof. Admitted. (* STUB *)
  Lemma check_dag_sound : forall db c g n, D.wf db -> check_dag db c g = Some n ->
    dag_valid (D.view db) c g /\ n = dag_cost g /\
    exists e, represents (D.view db) (Id c) e /\ unfold g c = Some e.
  Proof. Admitted. (* STUB *)
  Lemma extract_checked : forall db c g, D.wf db -> D.canonical db ->
    extract db c = Some g -> exists n m ch,
      check_dag db c g = Some n /\ In (c, (m, ch)) (best db) /\ (n <= m)%N.
  Proof. Admitted. (* STUB *)
End Extract.

Module ExtractT (V : VALUE_T) (I : INDEX_T V) (D : DATABASE_T V I) (C : COST_T V)
    <: EXTRACT_ALL V I D C.
  Include Extract V I D C.
  TimeFun best.
  TimeFun extract.
  TimeFun check_dag.
  Definition R (_ : D.t) : nat := 0.
  Definition a (_ : D.t) : nat := 0.
  Definition c_ex : N := 1. (* STUB *)
  Lemma T_best_le : forall db, D.wf db ->
    (T_best db <= c_ex *
      N.of_nat (R db * (a db + 1) + R db * (Nat.log2 (R db) + 1)) *
      N.of_nat (D.unit db + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_check_dag_le : forall db c g,
    (T_check_dag db c g <= c_ex * N.of_nat (length g + 1) *
      N.of_nat (a db + 1) * N.of_nat (D.unit db + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_extract_le : forall db c,
    (T_extract db c <= T_best db + c_ex * N.of_nat (R db + 1) *
      N.of_nat (a db + 1) * N.of_nat (D.unit db + 1))%N.
  Proof. Admitted. (* STUB *)
  Definition state := unit.
  (* STUB-CODE *)
  Definition initial (_ : D.t) : state := tt.
  (* STUB-CODE *)
  Definition step (_ : D.t) (_ : state) : state + extraction_best V.t := inr [].
  (* STUB-CODE *)
  Definition finalised (_ : state) : extraction_best V.t := [].
  (* STUB-CODE *)
  Definition counter (_ : state) (_ : positive) : nat := 0.
  (* STUB-CODE *)
  Definition children (_ : D.t) (_ : positive) : list positive := [].
  (* STUB-CODE *)
  Definition ready (_ : state) : list (positive * N) := [].
  (* STUB-CODE *)
  Definition heap_potential (_ : state) : N := 0%N.
  TimeFun initial.
  TimeFun step.
  TimeFun finalised.
  TimeFun counter.
  TimeFun children.
  TimeFun ready.
  TimeFun heap_potential.
  Definition k_step : N := 1. (* STUB *)
  Definition reachable (db : D.t) (s : state) : Prop :=
    clos_refl_trans state (fun a b => step db a = inl b) (initial db) s.
  Definition knuth_inv (db : D.t) (s : state) : Prop :=
    forall c n ch, In (c, (n, ch)) (finalised s) ->
      forall e, represents (D.view db) (Id c) e -> (n <= tree_cost e)%N.
  Lemma F1_initial : forall db, D.wf db -> D.canonical db ->
    finalised (initial db) = [] /\ knuth_inv db (initial db).
  Proof. Admitted. (* STUB *)
  Lemma F2_counter_spec : forall db s c, reachable db s ->
    counter s c = length (filter
      (fun i => negb (existsb (fun entry => Pos.eqb i (fst entry)) (finalised s)))
      (children db c)).
  Proof. Admitted. (* STUB *)
  Lemma F3_ready : forall db s c n, reachable db s ->
    In (c, n) (ready s) -> counter s c = 0.
  Proof. Admitted. (* STUB *)
  Lemma F4_pop_final : forall db s s', D.wf db -> D.canonical db ->
    reachable db s -> knuth_inv db s -> step db s = inl s' -> knuth_inv db s'.
  Proof. Admitted. (* STUB *)
  Lemma F5_finalised_attained : forall db s c n ch, D.wf db ->
    reachable db s -> In (c, (n, ch)) (finalised s) ->
    exists e, represents (D.view db) (Id c) e /\ tree_cost e = n.
  Proof. Admitted. (* STUB *)
  Lemma F6_best_loop : forall db, D.wf db -> D.canonical db ->
    loop_fuel (step db) (R db + 1) (initial db) = inr (best db).
  Proof. Admitted. (* STUB *)
  Lemma T1_step_amort : forall db s s', D.wf db -> reachable db s -> knuth_inv db s ->
    step db s = inl s' ->
    (T_step db s + heap_potential s' <= heap_potential s + k_step *
      N.of_nat (a db + Nat.log2 (R db) + 2) * N.of_nat (D.unit db + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T2_best_loop : forall db, D.wf db ->
    (T_best db <= c_ex *
      N.of_nat (R db * (a db + 1) + R db * (Nat.log2 (R db) + 1)) *
      N.of_nat (D.unit db + 1))%N.
  Proof. Admitted. (* STUB *)
End ExtractT.
