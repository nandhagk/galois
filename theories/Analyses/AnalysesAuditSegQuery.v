(** * Expression-specific SEG query source

    The query retains the universe test, one builder and scheduler receipt, and one solver run.
    For example, an absent expression returns false before constructing a sparse graph.
    Builds on: SEG universe, builder, fixpoint, system and reconstruction source models. *)
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Graph Require Import GraphCore GraphAuditBase.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointWorklist FixpointSchedule
  FixpointAuditIndex FixpointAuditWorklist FixpointAuditWorklistBudget
  FixpointAuditWorklistCallbacks
  FixpointAuditScheduleWrapper FixpointAuditTotal.
From Galois.Views Require Import ViewsGraph.
From Galois.Analyses Require Import AnalysesAvailable AnalysesSeg AnalysesAuditSsaQueryBase
  AnalysesAuditSegBuilder AnalysesAuditSegFixpoint AnalysesAuditSegSystem
  AnalysesAuditSegReconstruct
  AnalysesAuditSegSolver AnalysesAuditSegUniverse.
Import List.ListNotations.

(** * Expression-specific SEG query source *)

(** The requested direction selects the corresponding public sparse query. *)
Definition audit_seg_query_expected {S O N E U C} (EN : encoding N) (EE : encoding E)
    (EU : encoding U)
    (gk : genkill_view S O N E U C) (direction : audit_seg_direction) (u : U) (n : N) : bool :=
  match direction with
  | AuditAvailable => seg_available EN EE EU gk u n
  | AuditBusy => seg_busy EN EE EU gk u n
  end.

(** The producer budget observes only original inputs and declared callback budgets. *)
Definition audit_seg_query_producer_budget {S O N E U C B} (EN : encoding N) (EE : encoding E)
    (EU : encoding U) (gk : genkill_view S O N E U C) direction u (weight : B -> nat)
    (node_budget : N -> nat) (edge_budget target_budget source_budget : E -> nat) : nat :=
  let idx := build_expression_seg EN EE EU gk u in
  let system := audit_seg_fx_system EE EU gk u idx direction in
  let static := audit_seg_fx_static EE EU gk u idx direction in
  let index_budget := audit_seg_fx_index_budget EN EE weight node_budget edge_budget
    target_budget source_budget in
  let ix := index_system EN system static in
  let fuel := Pos.of_succ_nat
    (fx_total_join_step_bound seg_must_lattice audit_seg_solver_height static) in
  audit_seg_full_input_budget EN EE EU gk u + audit_seg_system_input_budget EN idx +
    fx_rpo_scheduler_budget EN system static index_budget +
    fx_index_nested_input_budget EN system static index_budget +
    fx_declared_run_input_budget EN (dense_constraint_encoding EN EE) seg_must_lattice
      (rpo_scheduler EN system static) Joining system static ix fuel.

(** A one-shot query adds its own reconstruction operand budget. *)
Definition audit_seg_query_input_budget {S O N E U C B} (EN : encoding N) (EE : encoding E)
    (EU : encoding U) (gk : genkill_view S O N E U C) direction u n (weight : B -> nat)
    (node_budget : N -> nat) (edge_budget target_budget source_budget : E -> nat) : nat :=
  audit_seg_query_producer_budget EN EE EU gk direction u weight node_budget edge_budget
    target_budget source_budget +
    audit_seg_reconstruct_input_budget EN EE EU gk (build_expression_seg EN EE EU gk u) u n.

(** Under callback laws, a present expression shares one solve and probe; an absent one is false. *)
Definition audit_seg_query_adapted_statement : Prop :=
  forall S O N E U C B (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (gk : genkill_view S O N E U C) (cb : audit_seg_build_callbacks N E U B)
    direction u n (weight : B -> nat)
    node_source edge_source expr_source out_source target_source source_source gen_source
    kill_source
    node_budget edge_budget expr_budget out_budget target_budget source_budget gen_budget
    kill_budget,
    audit_seg_full_callbacks_erase EN EE EU gk cb ->
    audit_graph_external_callback_adapter (seg_build_node_encode cb) weight node_source
      node_budget ->
    audit_graph_external_callback_adapter (seg_build_edge_encode cb) weight edge_source
      edge_budget ->
    audit_graph_external_callback_adapter (seg_build_expr_encode cb) weight expr_source
      expr_budget ->
    audit_graph_external_callback_adapter (seg_build_out cb) weight out_source out_budget ->
    audit_graph_external_callback_adapter (seg_build_target cb) weight target_source
      target_budget ->
    audit_graph_external_callback_adapter (seg_build_source cb) weight source_source
      source_budget ->
    audit_graph_external_callback_adapter (seg_build_gen cb) weight gen_source gen_budget ->
    audit_graph_external_callback_adapter (seg_build_kill cb) weight kill_source kill_budget ->
    let '(present, universe_events) := audit_seg_universe_counted (cfg (gkview gk)) cb u in
    let universe_external := fold_right (fun event total =>
      audit_seg_universe_event_budget out_budget gen_budget expr_budget event + total) 0
      universe_events in
    audit_seg_universe_work weight universe_events <= audit_seg_universe_input_budget EU gk u +
      universe_external /\
    if present then
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
      let source := audit_seg_fx_declared_source EN EE EU gk u p direction
        (seg_build_node_encode cb)
        (seg_build_edge_encode cb) (seg_build_target cb) (seg_build_source cb) work idx schedule in
      let budget := audit_seg_fx_declared_budget EN EE weight node_budget edge_budget
        target_budget source_budget (System.constraints system) in
      let '(constraints, system_events) := audit_seg_system_constraints p
        (seg_build_node_encode cb) work idx direction in
      exists result index_events init_events engine_events init_bodies engine_bodies,
        constraints = System.constraints system /\
        fx_total_callbacks_run EN (dense_constraint_encoding EN EE) seg_must_lattice
          (rpo_scheduler EN system static) Joining system index_cb result index_events
          init_events engine_events /\
        fx_index_external_trace_adequacy index_source index_events /\
        fx_declared_trace_source source init_events init_bodies /\
        fx_declared_trace_source source engine_events engine_bodies /\
        fx_dep_body_source index_source (fx_rpo_build_events schedule) /\
        Forall (fx_dep_prepare_source index_source) (fx_rpo_prepare_events schedule) /\
        Forall (fx_dep_dfs_source index_source) (fx_rpo_dfs_events schedule) /\
        Forall (fx_dep_positions_source index_source) (fx_rpo_position_events schedule) /\
        Forall (fx_dep_retreat_source index_source) (fx_rpo_retreat_events schedule) /\
        let '(cuts, setup_events) := audit_seg_reconstruct_setup cb idx in
        let '(answer, query_events) := audit_seg_reconstruct_probe cb work idx result direction
          u n cuts in
        let builder_external := fold_right (fun event total =>
          audit_seg_full_event_budget node_budget out_budget edge_budget target_budget source_budget
            gen_budget expr_budget kill_budget event + total) 0 (audit_seg_full_events receipt) in
        let system_external := fold_right (fun event total =>
          audit_seg_system_event_budget node_budget event + total) 0 system_events in
        let query_external := fold_right (fun event total =>
          audit_seg_reconstruct_event_budget node_budget edge_budget target_budget source_budget
            gen_budget expr_budget kill_budget event + total) 0 (setup_events ++ query_events) in
        answer = audit_seg_query_expected EN EE EU gk direction u n /\
        audit_seg_full_source_work weight (audit_seg_full_events receipt) +
          audit_seg_system_work weight system_events + fx_rpo_scheduler_work index_budget schedule +
          fx_index_adapter_work index_budget index_events +
          fx_declared_model_work (dense_constraint_encoding EN EE) init_events +
          fx_declared_model_work (dense_constraint_encoding EN EE) engine_events +
          fx_declared_body_work (fx_body_weight budget) init_bodies +
          fx_declared_body_work (fx_body_weight budget) engine_bodies +
          audit_seg_reconstruct_work weight (setup_events ++ query_events) <=
        audit_seg_query_input_budget EN EE EU gk direction u n weight node_budget edge_budget
          target_budget source_budget +
          fx_declared_external_trace_budget budget init_events +
          fx_declared_external_trace_budget budget engine_events +
          builder_external + system_external + query_external
    else audit_seg_query_expected EN EE EU gk direction u n = false.

(** The query contract combines universe, builder, solver and one-shot source obligations. *)
Definition audit_seg_query_contract_statement : Prop :=
  audit_seg_universe_adapted_statement /\ audit_seg_builder_contract_statement /\
  audit_seg_solver_contract_statement /\ audit_seg_query_adapted_statement.
