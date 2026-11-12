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
  Definition best (_ : list (positive * list nat)) (_ : D.t) : extraction_best V.t := [].
  (* STUB-CODE *)
  Definition extract (_ : list (positive * list nat)) (_ : D.t) (_ : positive)
      : option (extraction_dag V.t) := None.
  (* STUB-CODE *)
  Definition check_dag (_ : D.t) (_ : positive) (_ : extraction_dag V.t) : option N := None.
End ExtractCode.

Module Extract (V : VALUE) (I : INDEX V) (D : DATABASE V I) (C : COST V)
    <: EXTRACT V I D C.
  Include ExtractCode V I D C.
  Include EXTRACT_SPEC V I D C.
  (* STUB-CODE *)
  Definition unfold (_ : extraction_dag V.t) (_ : positive) : option (@Model.expr V.t) := None.
  Lemma unfold_spec : forall g c e, NoDup (map fst g) ->
    (unfold g c = Some e <-> dag_represents g c e).
  Proof. Admitted. (* STUB *)
  Lemma best_row : forall sl db c n f k, D.wf db -> D.canonical db -> full_slots sl db ->
    In (c, (n, (f, k))) (best sl db) ->
    row (D.view db) f k (Some (Id c)) /\
      n = C.fn_cost f (map (cost_of (best sl db)) k).
  Proof. Admitted. (* STUB *)
  Lemma best_optimal : forall sl db c e, D.wf db -> D.canonical db -> full_slots sl db ->
    represents (D.view db) (Id c) e ->
    exists n ch, In (D.repr db c, (n, ch)) (best sl db) /\ (n <= tree_cost e)%N.
  Proof. Admitted. (* STUB *)
  Lemma best_attained : forall sl db c n ch, D.wf db -> D.canonical db -> full_slots sl db ->
    In (c, (n, ch)) (best sl db) ->
    exists e, represents (D.view db) (Id c) e /\ tree_cost e = n.
  Proof. Admitted. (* STUB *)
  Lemma check_dag_sound : forall db c g n, D.wf db -> check_dag db c g = Some n ->
    dag_valid (D.view db) c g /\
    exists e, represents (D.view db) (Id c) e /\ unfold g c = Some e /\ n = tree_cost e.
  Proof. Admitted. (* STUB *)
  Lemma extract_checked : forall sl db c g, D.wf db -> D.canonical db -> full_slots sl db ->
    extract sl db c = Some g -> exists n m ch,
      check_dag db c g = Some n /\ In (D.repr db c, (m, ch)) (best sl db) /\ (n <= m)%N.
  Proof. Admitted. (* STUB *)
End Extract.

Module ExtractT (V : VALUE_T) (I : INDEX_T V) (D : DATABASE_T V I) (C : COST_T V)
    <: EXTRACT_ALL V I D C.
  Include Extract V I D C.
  TimeFun best.
  TimeFun extract.
  TimeFun check_dag.
  TimeFun unfold.
  (* STUB-CODE *)
  Definition R (_ : D.t) : nat := 0.
  (* STUB-CODE *)
  Definition a (_ : D.t) : nat := 0.
  (* STUB-CODE *)
  Definition cost_width (_ : D.t) : nat := 0.
  Definition c_ex : N := 1. (* STUB *)
  Lemma R_spec : forall db, D.wf db -> exists rs, NoDup rs /\ length rs = R db /\
    forall f k i, In (f, k, i) rs <-> row (D.view db) f k (Some (Id i)).
  Proof. Admitted. (* STUB *)
  Lemma a_spec : forall db, D.wf db ->
    (forall f k i, row (D.view db) f k (Some (Id i)) -> length k <= a db) /\
    (a db = 0 \/ exists f k i, row (D.view db) f k (Some (Id i)) /\ length k = a db).
  Proof. Admitted. (* STUB *)
  Lemma cost_width_spec : forall sl db, D.wf db -> D.canonical db -> full_slots sl db ->
    (forall f k i, row (D.view db) f k (Some (Id i)) ->
      N.size_nat (C.fn_cost f (map (cost_of (best sl db)) k)) <= cost_width db) /\
    (forall f k i v, row (D.view db) f k (Some (Id i)) -> In (Val v) k ->
      N.size_nat (C.val_cost v) <= cost_width db) /\
    (cost_width db = 0 \/
      (exists f k i, row (D.view db) f k (Some (Id i)) /\
        N.size_nat (C.fn_cost f (map (cost_of (best sl db)) k)) = cost_width db) \/
      (exists f k i v, row (D.view db) f k (Some (Id i)) /\ In (Val v) k /\
        N.size_nat (C.val_cost v) = cost_width db)).
  Proof. Admitted. (* STUB *)
  Lemma T_best_le : forall sl db, D.wf db -> D.canonical db -> full_slots sl db ->
    (T_best sl db <= c_ex *
      N.of_nat ((R db + 1) * (a db + 1) + (R db + 1) * (Nat.log2 (R db) + 1)) *
      N.of_nat (D.unit db + 1) * N.of_nat (cost_width db + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_check_dag_le : forall db c g, D.wf db ->
    (T_check_dag db c g <= c_ex * N.of_nat (cert_size V.encode g + Pos.size_nat c + 1) *
      N.of_nat (D.unit db + 1) *
      N.of_nat (match check_dag db c g with
        | Some n => N.size_nat n
        | None => 0
        end + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_extract_le : forall sl db c, D.wf db -> D.canonical db -> full_slots sl db ->
    (T_extract sl db c <= T_best sl db + c_ex * N.of_nat (R db + 1) *
      N.of_nat (a db + 1) * N.of_nat (D.unit db + 1) * N.of_nat (cost_width db + 1))%N.
  Proof. Admitted. (* STUB *)
  Definition state := unit.
  (* STUB-CODE *)
  Definition initial (_ : list (positive * list nat)) (_ : D.t) : state := tt.
  (* STUB-CODE *)
  Definition step (_ : list (positive * list nat)) (_ : D.t) (_ : state)
      : state + extraction_best V.t := inr [].
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
  Definition reachable (sl : list (positive * list nat)) (db : D.t) (s : state) : Prop :=
    clos_refl_trans state (fun a b => step sl db a = inl b) (initial sl db) s.
  Definition knuth_inv (db : D.t) (s : state) : Prop :=
    forall c n ch, In (c, (n, ch)) (finalised s) ->
      forall e, represents (D.view db) (Id c) e -> (n <= tree_cost e)%N.
  Lemma F1_initial : forall sl db, D.wf db -> D.canonical db -> full_slots sl db ->
    finalised (initial sl db) = [] /\ knuth_inv db (initial sl db).
  Proof. Admitted. (* STUB *)
  Lemma F2_counter_spec : forall sl db s c, reachable sl db s ->
    counter s c = length (filter
      (fun i => negb (existsb (fun entry => Pos.eqb i (fst entry)) (finalised s)))
      (children db c)).
  Proof. Admitted. (* STUB *)
  Lemma F3_ready : forall sl db s c n, reachable sl db s ->
    In (c, n) (ready s) -> counter s c = 0.
  Proof. Admitted. (* STUB *)
  Lemma F4_pop_final : forall sl db s s', D.wf db -> D.canonical db -> full_slots sl db ->
    reachable sl db s -> knuth_inv db s -> step sl db s = inl s' -> knuth_inv db s'.
  Proof. Admitted. (* STUB *)
  Lemma F5_finalised_attained : forall sl db s c n ch, D.wf db ->
    reachable sl db s -> In (c, (n, ch)) (finalised s) ->
    exists e, represents (D.view db) (Id c) e /\ tree_cost e = n.
  Proof. Admitted. (* STUB *)
  Lemma F6_best_loop : forall sl db, D.wf db -> D.canonical db -> full_slots sl db ->
    loop_fuel (step sl db) (R db + 1) (initial sl db) = inr (best sl db).
  Proof. Admitted. (* STUB *)
  Lemma T1_step_amort : forall sl db s s', D.wf db -> D.canonical db -> full_slots sl db ->
    reachable sl db s -> knuth_inv db s ->
    step sl db s = inl s' ->
    (T_step sl db s + heap_potential s' <= heap_potential s + k_step *
      N.of_nat (a db + Nat.log2 (R db) + 2) * N.of_nat (D.unit db + 1) *
      N.of_nat (cost_width db + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T2_best_loop : forall sl db, D.wf db -> D.canonical db -> full_slots sl db ->
    (T_best sl db <= c_ex *
      N.of_nat ((R db + 1) * (a db + 1) + (R db + 1) * (Nat.log2 (R db) + 1)) *
      N.of_nat (D.unit db + 1) * N.of_nat (cost_width db + 1))%N.
  Proof. Admitted. (* STUB *)
End ExtractT.
