(** * Indexed reverse postorder scheduler examples

    These checks follow the actual counted index, graph and scheduler preparation.
    For example, a reader of zero supplies the outgoing edge from zero to one.
    Builds on: FixpointAuditScheduleWrapperAdequacy and the indexed sample client. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet
  CollectionsAuditEncoding
  CollectionsAuditEncodingAdequacy.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointWorklist FixpointSchedule
  FixpointAuditIndex
  FixpointAuditSchedule FixpointAuditScheduleWrapper FixpointAuditScheduleWrapperAdequacy.
From Galois.Tests.Fixpoint Require Import FixpointFIX1 FixpointAuditModelsExamples
  FixpointAuditIndexExamples.
Import List.ListNotations.

(** * Dependency and scheduler observations *)

(** A present reader bucket and a missing bucket produce different outgoing edges. *)
Example fx_schedule_reader_branches :
  let ix := fst (fx_index_nested_counted sample_system fx_models_callbacks) in
  (fst (fx_dep_out fx_models_callbacks ix 0), fst (fx_dep_out fx_models_callbacks ix 7)) =
    ([(0, 1)], []).
Proof.
  vm_compute; reflexivity.
Qed.

(** Nonempty preparation retains its exact DFS postorder and its fast reverse. *)
Example fx_schedule_reverse_execution :
  let result := fx_rpo_scheduler_counted nat_encoding sample_system sample_static
    fx_models_callbacks in
  fx_rpo_reverse_input result <> [] /\
  fx_rpo_reverse_output result = rev (fx_rpo_reverse_input result) /\
  fx_rpo_reverse_work result = 1 + 2 * length (fx_rpo_reverse_input result).
Proof.
  vm_compute; repeat split; discriminate || reflexivity.
Qed.

(** The sample's counted positions and heads produce the same scheduler observations. *)
Example fx_schedule_sample_erases :
  let result := fx_rpo_scheduler_counted nat_encoding sample_system sample_static
    fx_models_callbacks in
  forall x,
    fst (audit_rpo_schedule_priority (fx_dep_encoder fx_models_callbacks)
      (fx_rpo_positions result) x) = priority (rpo_scheduler nat_encoding sample_system
        sample_static) x /\
    fst (audit_rpo_schedule_widening (fx_dep_encoder fx_models_callbacks)
      (fx_rpo_heads result) x) = widening_point (rpo_scheduler nat_encoding sample_system
        sample_static) x.
Proof.
  exact (fx_rpo_scheduler_erasure_correct nat bool bool _ nat_encoding sample_system sample_static
    fx_models_callbacks fx_index_fixture_erases).
Qed.

(** The loop client records natural encoding frames and its own static callbacks. *)
Definition fx_schedule_loop_callbacks :
    fx_index_external_model nat bool (audit_nat_encoding_event + unit) :=
  FxIndexExternalModel nat bool (audit_nat_encoding_event + unit)
    (fxi_encode fx_models_callbacks)
    (fun c => (System.target loop_system c, [inr tt]))
    (fun c => (side_targets loop_static c, [inr tt]))
    (fun c => (deps loop_static c, [inr tt])).

(** A cycle has a recorded retreat target and at least one widening point. *)
Example fx_schedule_cycle_retreat :
  let result := fx_rpo_scheduler_counted nat_encoding loop_system loop_static
    fx_schedule_loop_callbacks in
  existsb (fun x => FinSet.mem nat_encoding x (fx_rpo_heads result)) [0; 1] = true /\
  existsb (fun event =>
    match event with
    | RpoGraphOut _ _ body => negb (Nat.eqb (length body) 0)
    | _ => false
    end) (fx_rpo_retreat_events result) = true.
Proof.
  vm_compute; split; reflexivity.
Qed.

(** The sample encoder receipt carries an actual natural-number source derivation. *)
Definition fx_schedule_sample_source :
    fx_index_external_source nat bool (audit_nat_encoding_event + unit) :=
  FxIndexExternalSource nat bool (audit_nat_encoding_event + unit)
    (fun x code body => exists events work,
      audit_nat_encode_run x code events work /\ body = map inl events)
    (fun c output body => output = System.target sample_system c /\ body = [inr tt])
    (fun c output body => output = side_targets sample_static c /\ body = [inr tt])
    (fun c output body => output = deps sample_static c /\ body = [inr tt]).

Lemma fx_schedule_sample_source_laws : fx_dep_source_laws fx_models_callbacks
    fx_schedule_sample_source.
Proof.
  unfold fx_dep_source_laws; split.
  - intro x; destruct (audit_nat_encode_run_total x) as [code [events [work Hrun]]].
    pose proof (audit_nat_encode_run_correct x code events work Hrun) as [_ [Htrace _]].
    unfold fx_models_callbacks; cbn [fxi_encode].
    rewrite <- Htrace; cbn; exists events, work; split; [exact Hrun | reflexivity].
  - split.
    + intro c; split; reflexivity.
    + split; intro c; split; reflexivity.
Qed.

(** The sample's recorded preparation, DFS and scheduler events retain those source bodies. *)
Example fx_schedule_sample_source_receipts :
  let result := fx_rpo_scheduler_counted nat_encoding sample_system sample_static
    fx_models_callbacks in
  fx_dep_body_source fx_schedule_sample_source (fx_rpo_build_events result) /\
  Forall (fx_dep_prepare_source fx_schedule_sample_source) (fx_rpo_prepare_events result) /\
  Forall (fx_dep_dfs_source fx_schedule_sample_source) (fx_rpo_dfs_events result) /\
  Forall (fx_dep_positions_source fx_schedule_sample_source) (fx_rpo_position_events result) /\
  Forall (fx_dep_retreat_source fx_schedule_sample_source) (fx_rpo_retreat_events result).
Proof.
  exact (fx_rpo_scheduler_source_correct nat bool bool _ nat_encoding sample_system sample_static
    fx_models_callbacks fx_schedule_sample_source fx_schedule_sample_source_laws).
Qed.

(** An outgoing receipt retains the reader lookup and the actual encoder trace for zero. *)
Example fx_schedule_out_reader_receipt :
  let result := fx_rpo_scheduler_counted nat_encoding sample_system sample_static
    fx_models_callbacks in
  existsb (fun event =>
    match event with
    | RpoGraphOut 0 [(0, 1)] body =>
      existsb (fun item =>
        match item with
        | FxDepIndexEvent (FxiRead 0 1%positive _ (Some [true])
            [inl (AuditNatFrame 0)] _) => true
        | _ => false
        end) body
    | _ => false
    end) (fx_rpo_retreat_events result) = true.
Proof.
  vm_compute; reflexivity.
Qed.

(** Ancestor checks distinguish a visited vertex from an absent vertex. *)
Example fx_schedule_ancestor_branches :
  let g := dependency_graph nat_encoding sample_system sample_static in
  let search := dfs (prepare nat_encoding g) FinSet.empty (Graph.entries g) in
  (fst (audit_rpo_graph_ancestor (fx_dep_encoder fx_models_callbacks) search 0 0),
   fst (audit_rpo_graph_ancestor (fx_dep_encoder fx_models_callbacks) search 99 0)) = (true, false).
Proof.
  vm_compute; reflexivity.
Qed.

(** The finite sample instantiates the whole input bound without evaluating its large budget. *)
Example fx_schedule_sample_input_bound :
  fx_rpo_scheduler_work fx_models_budget
    (fx_rpo_scheduler_counted nat_encoding sample_system sample_static fx_models_callbacks) <=
  fx_rpo_scheduler_budget nat_encoding sample_system sample_static fx_models_budget.
Proof.
  exact (fx_rpo_scheduler_input_bound_correct nat bool bool _ nat_encoding sample_system
    sample_static fx_models_callbacks fx_models_budget fx_index_fixture_erases
    fx_index_fixture_bounded).
Qed.
