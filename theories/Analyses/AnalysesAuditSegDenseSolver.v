(** * Dense SEG total-solver source

    One captured dense initialization and RPO-indexed total solve feed the result probes.
    For example, a batch reuses the same assignment rather than running one solve per expression.
    Builds on: dense system callbacks, initialization, probes and FixpointAuditTotal. *)
From Stdlib Require Import List PArith Arith.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet.
From Galois.Order Require Import OrderLattice OrderPowerset.
From Galois.Graph Require Import GraphCore GraphAuditBase.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointWorklist FixpointSchedule
  FixpointTotal FixpointAuditIndex FixpointAuditWorklist FixpointAuditWorklistBudget
  FixpointAuditWorklistCallbacks FixpointAuditScheduleWrapper FixpointAuditTotal.
From Galois.Views Require Import ViewsGraph.
From Galois.Analyses Require Import AnalysesAvailable AnalysesAuditSsaQueryBase
  AnalysesAuditSegBuilder
  AnalysesAuditSegUniverse AnalysesAuditSegDenseSystem AnalysesAuditSegDenseCallbacks
  AnalysesAuditSegDenseBudget AnalysesAuditSegDenseInit AnalysesAuditSegDenseQuery
  AnalysesAuditSegDenseAnnotated.
Import List.ListNotations.

(** * Dense SEG total-solver source *)

(** The selected existing dense solution preserves the original analysis direction. *)
Definition audit_dense_solution {S O N E U C} (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (gk : genkill_view S O N E U C) (direction : audit_seg_direction) : N -> avail_set EU gk :=
  match direction with
  | AuditAvailable => audit_dense_available EN EE EU gk
  | AuditBusy => audit_dense_busy EN EE EU gk
  end.

(** The solver bound uses original inputs, finite height and the actual generated index. *)
Definition audit_dense_solve_budget {S O N E U C B} (EN : encoding N) (EE : encoding E)
    (EU : encoding U) (gk : genkill_view S O N E U C) (cb : audit_seg_build_callbacks N E U B)
    (direction : audit_seg_direction) (weight : B -> nat)
    (costs : audit_dense_client_budget N E U) : nat :=
  let sys := audit_dense_fx_system EU gk direction in
  let static := audit_dense_fx_static EU gk direction in
  let lattice := avail_lattice EU gk in
  let height := base_height (finite_must_height EU (expr_universe EU gk)
    (audit_universe_nodup EU gk)) in
  let index_budget := audit_dense_fx_index_budget (U := U) EN EE weight (dense_node_budget costs)
    (dense_edge_budget costs) (dense_target_budget costs) (dense_source_budget costs) in
  let ix := index_system EN sys static in
  let fuel := Pos.of_succ_nat (fx_total_join_step_bound lattice height static) in
  audit_dense_initial_budget EU gk costs + audit_dense_constraints_budget (cfg (gkview gk)) +
    fx_rpo_scheduler_budget EN sys static index_budget + fx_index_nested_input_budget EN sys
    static index_budget +
    fx_declared_run_input_budget EN (dense_constraint_encoding EN EE) lattice
      (rpo_scheduler EN sys static) Joining sys static ix fuel.

(** Under callback laws, one solver run matches the dense solution and satisfies its work bound. *)
Definition audit_dense_solver_source_statement : Prop :=
  forall (S O N E U C B : Type) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (gk : genkill_view S O N E U C) (cb : audit_seg_build_callbacks N E U B)
    (direction : audit_seg_direction) (weight : B -> nat) (costs : audit_dense_client_budget N E U)
    node_source edge_source expr_source out_source target_source source_source gen_source
    kill_source,
    audit_seg_full_callbacks_erase EN EE EU gk cb ->
    audit_graph_external_callback_adapter (seg_build_node_encode cb) weight node_source
      (dense_node_budget costs) ->
    audit_graph_external_callback_adapter (seg_build_edge_encode cb) weight edge_source
      (dense_edge_budget costs) ->
    audit_graph_external_callback_adapter (seg_build_expr_encode cb) weight expr_source
      (dense_expr_budget costs) ->
    audit_graph_external_callback_adapter (seg_build_out cb) weight out_source
      (dense_out_budget costs) ->
    audit_graph_external_callback_adapter (seg_build_target cb) weight target_source
      (dense_target_budget costs) ->
    audit_graph_external_callback_adapter (seg_build_source cb) weight source_source
      (dense_source_budget costs) ->
    audit_graph_external_callback_adapter (seg_build_gen cb) weight gen_source
      (dense_gen_budget costs) ->
    audit_graph_external_callback_adapter (seg_build_kill cb) weight kill_source
      (dense_kill_budget costs) ->
    let sys := audit_dense_fx_system EU gk direction in
    let static := audit_dense_fx_static EU gk direction in
    let lattice := avail_lattice EU gk in
    let height := base_height (finite_must_height EU (expr_universe EU gk)
      (audit_universe_nodup EU gk)) in
    let index_cb := audit_dense_index_model cb direction in
    let index_source := audit_dense_index_source cb direction in
    let index_budget := audit_dense_fx_index_budget (U := U) EN EE weight (dense_node_budget costs)
      (dense_edge_budget costs) (dense_target_budget costs) (dense_source_budget costs) in
    let schedule := fx_rpo_scheduler_counted EN sys static index_cb in
    let source := audit_dense_declared_source EN EE EU gk cb direction schedule in
    let budget := audit_dense_declared_budget EN EE EU gk costs weight direction in
    let '(constraints, constraint_events) := audit_dense_constraints (cfg (gkview gk)) cb
      direction in
    let '(bottom, bottom_events) := audit_dense_initial (cfg (gkview gk)) cb in
    exists result index_events init_events engine_events init_bodies engine_bodies,
      constraints = System.constraints sys /\ bottom = proj1_sig (bot lattice) /\
      audit_dense_annotated_total EN (dense_constraint_encoding EN EE) lattice
        (rpo_scheduler EN sys static) Joining sys index_cb index_source source
        result index_events init_events engine_events init_bodies engine_bodies /\
      fx_total_callbacks_run EN (dense_constraint_encoding EN EE) lattice
        (rpo_scheduler EN sys static) Joining sys index_cb result index_events init_events
        engine_events /\
      fx_index_external_trace_adequacy index_source index_events /\
      fx_declared_trace_source source init_events init_bodies /\
      fx_declared_trace_source source engine_events engine_bodies /\
      Forall (fx_dep_prepare_source index_source) (fx_rpo_prepare_events schedule) /\
      Forall (fx_dep_dfs_source index_source) (fx_rpo_dfs_events schedule) /\
      Forall (fx_dep_positions_source index_source) (fx_rpo_position_events schedule) /\
      Forall (fx_dep_retreat_source index_source) (fx_rpo_retreat_events schedule) /\
      fx_dep_body_source index_source (fx_rpo_build_events schedule) /\
      (forall n, audit_dense_solution EN EE EU gk direction n = lookup EN lattice result n) /\
      let ix := index_system EN sys static in
      let fuel := Pos.of_succ_nat (fx_total_join_step_bound lattice height static) in
      audit_dense_initial_work weight bottom_events + audit_seg_universe_work weight
        constraint_events +
        fx_rpo_scheduler_work index_budget schedule + fx_index_adapter_work index_budget
        index_events +
        fx_declared_model_work (dense_constraint_encoding EN EE) init_events +
        fx_declared_model_work (dense_constraint_encoding EN EE) engine_events +
        fx_declared_body_work (fx_body_weight budget) init_bodies +
        fx_declared_body_work (fx_body_weight budget) engine_bodies <=
      audit_dense_solve_budget EN EE EU gk cb direction weight costs +
        fold_right (fun e n => audit_seg_universe_event_budget (dense_out_budget costs)
          (dense_gen_budget costs) (dense_expr_budget costs) e + n) 0 constraint_events +
        fx_declared_external_trace_budget budget init_events +
        fx_declared_external_trace_budget budget engine_events.
