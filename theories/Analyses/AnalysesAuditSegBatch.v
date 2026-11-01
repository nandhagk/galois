(** * Shared sparse expression queries

    One sparse builder and one solver result serve a list of node probes.
    For example, when the expression is present, an empty batch still constructs one query setup.
    Builds on: SEG query source and captured reconstruction setup. *)
From Stdlib Require Import List PArith NArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphAuditBase.
From Galois.Fixpoint Require Import FixpointSystem FixpointWorklist FixpointSchedule
  FixpointAuditIndex FixpointAuditWorklist FixpointAuditWorklistCallbacks
  FixpointAuditScheduleWrapper
  FixpointAuditTotal.
From Galois.Views Require Import ViewsGraph.
From Galois.Analyses Require Import AnalysesAvailable AnalysesSeg AnalysesAuditSsaQueryBase
  AnalysesAuditSegBuilder AnalysesAuditSegFixpoint AnalysesAuditSegSystem
  AnalysesAuditSegReconstruct
  AnalysesAuditSegUniverse AnalysesAuditSegQuery.
Import List.ListNotations.

(** * Shared sparse expression queries *)

(** Each probe reuses the same cut set, graph work state and solver assignment. *)
Fixpoint audit_seg_sparse_batch_probes {N E U B} (cb : audit_seg_build_callbacks N E U B)
    (work : seg_work N E) (idx : seg_index N E) (solution : Map.t N bool)
    (direction : audit_seg_direction) (u : U) (cuts : FinSet.t N) (nodes : list N)
    : list bool * list (list (audit_seg_reconstruct_event N E U B)) :=
  match nodes with
  | [] => ([], [])
  | n :: rest =>
    let '(answer, calls) := audit_seg_reconstruct_probe cb work idx solution direction u n cuts in
    let '(answers, traces) := audit_seg_sparse_batch_probes cb work idx solution direction u cuts
      rest in
    (answer :: answers, calls :: traces)
  end.

(** Setup is bounded by the captured graph's node count and actual encoded widths. *)
Definition audit_seg_sparse_setup_budget {N E} (EN : encoding N) (idx : seg_index N E) : nat :=
  let nodes := Graph.nodes (seg_graph idx) in
  let width := fold_right (fun n total => Pos.size_nat (encode EN n) + total) 0 nodes in
  (N.to_nat 65536%N) * Nat.pow (S (length nodes + width)) 8.

(** The batch derives its native producer and every probe allowance from original inputs. *)
Definition audit_seg_sparse_batch_input_budget {S O N E U C B} (EN : encoding N) (EE : encoding E)
    (EU : encoding U) (gk : genkill_view S O N E U C) direction u (nodes : list N)
    (weight : B -> nat) (node_budget : N -> nat)
    (edge_budget target_budget source_budget : E -> nat) : nat :=
  let idx := build_expression_seg EN EE EU gk u in
  audit_seg_query_producer_budget EN EE EU gk direction u weight node_budget edge_budget
    target_budget source_budget +
    audit_seg_sparse_setup_budget EN idx + Nat.succ (length nodes) +
    fold_right (fun n total => audit_seg_reconstruct_input_budget EN EE EU gk idx u n + total) 0
      nodes.

(** A present expression shares one solver receipt and setup; an absent one gives false answers. *)
Definition audit_seg_sparse_batch_adapted_statement : Prop :=
  forall S O N E U C B (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (gk : genkill_view S O N E U C) (cb : audit_seg_build_callbacks N E U B)
    direction u nodes (weight : B -> nat)
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
      let '(constraints, system_events) := audit_seg_system_constraints p (seg_build_node_encode cb)
        work idx direction in
      exists result index_events init_events engine_events init_bodies engine_bodies,
        constraints = System.constraints system /\
        fx_total_callbacks_run EN (dense_constraint_encoding EN EE) seg_must_lattice
          (rpo_scheduler EN system static) Joining system index_cb result index_events init_events
          engine_events /\
        fx_index_external_trace_adequacy index_source index_events /\
        fx_declared_trace_source source init_events init_bodies /\
        fx_declared_trace_source source engine_events engine_bodies /\
        fx_dep_body_source index_source (fx_rpo_build_events schedule) /\
        Forall (fx_dep_prepare_source index_source) (fx_rpo_prepare_events schedule) /\
        Forall (fx_dep_dfs_source index_source) (fx_rpo_dfs_events schedule) /\
        Forall (fx_dep_positions_source index_source) (fx_rpo_position_events schedule) /\
        Forall (fx_dep_retreat_source index_source) (fx_rpo_retreat_events schedule) /\
        let '(cuts, setup_events) := audit_seg_reconstruct_setup cb idx in
        let '(answers, traces) := audit_seg_sparse_batch_probes cb work idx result direction u cuts
          nodes in
        let builder_external := fold_right (fun event total =>
          audit_seg_full_event_budget node_budget out_budget edge_budget target_budget source_budget
            gen_budget expr_budget kill_budget event + total) 0 (audit_seg_full_events receipt) in
        let system_external := fold_right (fun event total =>
          audit_seg_system_event_budget node_budget event + total) 0 system_events in
        let recon_external := fold_right (fun event total =>
          audit_seg_reconstruct_event_budget node_budget edge_budget target_budget source_budget
            gen_budget expr_budget kill_budget event + total) 0 (setup_events ++ concat traces) in
        answers = map (audit_seg_query_expected EN EE EU gk direction u) nodes /\
        length traces = length nodes /\
        audit_seg_full_source_work weight (audit_seg_full_events receipt) +
          audit_seg_system_work weight system_events + fx_rpo_scheduler_work index_budget schedule +
          fx_index_adapter_work index_budget index_events +
          fx_declared_model_work (dense_constraint_encoding EN EE) init_events +
          fx_declared_model_work (dense_constraint_encoding EN EE) engine_events +
          fx_declared_body_work (fx_body_weight budget) init_bodies +
          fx_declared_body_work (fx_body_weight budget) engine_bodies +
          audit_seg_reconstruct_work weight setup_events +
          fold_right (fun events total => audit_seg_reconstruct_work weight events + total) 0
            traces +
          Nat.succ (length nodes) <=
        audit_seg_sparse_batch_input_budget EN EE EU gk direction u nodes weight node_budget
          edge_budget target_budget source_budget + fx_declared_external_trace_budget budget
            init_events +
          fx_declared_external_trace_budget budget engine_events + builder_external +
          system_external + recon_external
    else map (audit_seg_query_expected EN EE EU gk direction u) nodes = map (fun _ => false) nodes.
