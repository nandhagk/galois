(** * SEG solver source composition

    The solver composition shares the builder, scheduler and total-solver receipts.
    For example, a flow continuation reads the summary of its captured sparse edge.
    Builds on: SEG builder, reconstruction and fixpoint source models. *)
From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Order Require Import OrderLattice.
From Galois.Graph Require Import GraphCore GraphAuditBase.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointWorklist
  FixpointSchedule FixpointTotal
  FixpointAuditIndex FixpointAuditWorklist FixpointAuditWorklistBudget
  FixpointAuditWorklistCallbacks FixpointAuditScheduleWrapper FixpointAuditTotal.
From Galois.Views Require Import ViewsGraph.
From Galois.Analyses Require Import AnalysesAvailable AnalysesSeg AnalysesAuditSsaQueryBase
  AnalysesAuditSegBuilder AnalysesAuditSegFixpoint AnalysesAuditSegSystem
  AnalysesAuditSegReconstruct.

(** * Total solver contract *)

(** The two-point must lattice has a finite rank. *)
Definition audit_seg_solver_height : height seg_must_lattice.
Proof.
  refine (@Height bool seg_must_lattice (fun b => if b then 0 else 1) 1 _ _).
  - abstract (intros []; cbn; lia).
  - abstract (intros [] []; cbn; intro Hstrict; try discriminate; lia).
Defined.

(** Under callback laws, either direction has a matching join-solver run and bounded work. *)
Definition audit_seg_solver_adapted_statement : Prop :=
  forall S O N E U C B (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (gk : genkill_view S O N E U C) (cb : audit_seg_build_callbacks N E U B) u direction
    (weight : B -> nat)
    node_source edge_source target_source source_source node_budget edge_budget target_budget
    source_budget,
    audit_seg_full_callbacks_erase EN EE EU gk cb ->
    audit_graph_external_callback_adapter (seg_build_node_encode cb) weight node_source
      node_budget ->
    audit_graph_external_callback_adapter (seg_build_edge_encode cb) weight edge_source
      edge_budget ->
    audit_graph_external_callback_adapter (seg_build_target cb) weight target_source
      target_budget ->
    audit_graph_external_callback_adapter (seg_build_source cb) weight source_source
      source_budget ->
    let receipt := audit_seg_full_source_counted EN EE (cfg (gkview gk)) cb u in
    let idx := audit_seg_full_result receipt in
    let p := audit_seg_full_index receipt in let work := audit_seg_full_work_state receipt in
    let system := audit_seg_fx_system EE EU gk u idx direction in
    let static := audit_seg_fx_static EE EU gk u idx direction in
    let index_cb := audit_seg_fx_index_model direction (seg_build_node_encode cb)
      (seg_build_edge_encode cb)
      (seg_build_target cb) (seg_build_source cb) work in
    let index_source := audit_seg_fx_index_source direction (seg_build_node_encode cb)
      (seg_build_edge_encode cb)
      (seg_build_target cb) (seg_build_source cb) work in
    let index_budget := audit_seg_fx_index_budget EN EE weight node_budget edge_budget
      target_budget source_budget in
    let schedule := fx_rpo_scheduler_counted EN system static index_cb in
    let source := audit_seg_fx_declared_source EN EE EU gk u p direction (seg_build_node_encode cb)
      (seg_build_edge_encode cb) (seg_build_target cb) (seg_build_source cb) work idx schedule in
    let budget := audit_seg_fx_declared_budget EN EE weight node_budget edge_budget
      target_budget source_budget (System.constraints system) in
    exists result index_events init_events engine_events init_bodies engine_bodies,
      fx_total_callbacks_run EN (dense_constraint_encoding EN EE) seg_must_lattice
        (rpo_scheduler EN system static) Joining system index_cb result index_events init_events
        engine_events /\
      fx_index_external_trace_adequacy index_source index_events /\
      fx_declared_trace_source source init_events init_bodies /\
      fx_declared_trace_source source engine_events engine_bodies /\
      result = proj1_sig (total_solver_map EN (dense_constraint_encoding EN EE)
        seg_must_lattice seg_must_laws (rpo_scheduler EN system static) Joining system static
        (inhabits audit_seg_solver_height)) /\
      fx_dep_body_source index_source (fx_rpo_build_events schedule) /\
      Forall (fx_dep_prepare_source index_source) (fx_rpo_prepare_events schedule) /\
      Forall (fx_dep_dfs_source index_source) (fx_rpo_dfs_events schedule) /\
      Forall (fx_dep_positions_source index_source) (fx_rpo_position_events schedule) /\
      Forall (fx_dep_retreat_source index_source) (fx_rpo_retreat_events schedule) /\
      fx_rpo_scheduler_work index_budget schedule <= fx_rpo_scheduler_budget EN system static
        index_budget /\
      let ix := index_system EN system static in
      let fuel := Pos.of_succ_nat (fx_total_join_step_bound seg_must_lattice
        audit_seg_solver_height static) in
      fx_index_adapter_work index_budget index_events + fx_declared_model_work
        (dense_constraint_encoding EN EE) init_events +
        fx_declared_model_work (dense_constraint_encoding EN EE) engine_events +
        fx_declared_body_work (fx_body_weight budget) init_bodies + fx_declared_body_work
        (fx_body_weight budget) engine_bodies <=
      fx_index_nested_input_budget EN system static index_budget +
        fx_declared_run_input_budget EN (dense_constraint_encoding EN EE) seg_must_lattice
          (rpo_scheduler EN system static) Joining system static ix fuel +
        fx_declared_external_trace_budget budget init_events + fx_declared_external_trace_budget
          budget engine_events.

(** The solver contract combines constraint, callback, solve and reconstruction obligations. *)
Definition audit_seg_solver_contract_statement : Prop :=
  audit_seg_system_adapted_statement /\ audit_seg_fx_instantiation_statement /\
  audit_seg_solver_adapted_statement /\ audit_seg_reconstruct_adapted_statement.
