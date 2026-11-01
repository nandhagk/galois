(** * Dense SEG batch source composition

    A single total-solver witness supplies every requested node-expression result.
    For example, two expressions at one node reuse the same solved assignment.
    Builds on: AnalysesAuditSegDenseSolver and AnalysesAuditSegDenseQuery. *)
From Stdlib Require Import List PArith Arith.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet CollectionsAuditMap
  CollectionsAuditFinSet.
From Galois.Order Require Import OrderLattice.
From Galois.Graph Require Import GraphCore GraphAuditBase.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointWorklist FixpointSchedule
  FixpointAuditIndex FixpointAuditWorklist FixpointAuditWorklistBudget
  FixpointAuditWorklistCallbacks
  FixpointAuditScheduleWrapper FixpointAuditTotal.
From Galois.Views Require Import ViewsGraph.
From Galois.Analyses Require Import AnalysesAvailable AnalysesAuditSsaQueryBase
  AnalysesAuditSegBuilder
  AnalysesAuditSegUniverse AnalysesAuditSegDenseSystem AnalysesAuditSegDenseCallbacks
  AnalysesAuditSegDenseBudget AnalysesAuditSegDenseInit AnalysesAuditSegDenseQuery
  AnalysesAuditSegDenseSolver AnalysesAuditSegDenseClient AnalysesAuditSegDenseAnnotated.
Import List.ListNotations.

(** * Dense SEG batch source composition *)

(** Probe receipts expose actual node and expression encoder client bodies. *)
Definition audit_dense_probe_client_source {N E U A B} (weight : B -> nat)
    (source : audit_dense_client_source N E U B) (event : audit_dense_probe_event N U A B) : Prop :=
  match event with
  | DenseProbeMap (AuditMapGet n code _ _ body _) | DenseProbeMap (AuditMapSet n _ code _ _
    body _) |
    DenseProbeMap (AuditMapRemove n code _ _ body _) =>
    dense_node_source source n code body (audit_dense_client_body_work weight body)
  | DenseProbeSet event => audit_dense_expr_set_source weight source event
  | DenseProbeCase => True
  end.

(** The batch bound pays for one actual solve and the original query operands. *)
Definition audit_dense_batch_budget {S O N E U C B} (EN : encoding N) (EE : encoding E)
    (EU : encoding U) (gk : genkill_view S O N E U C) (cb : audit_seg_build_callbacks N E U B)
    (direction : audit_seg_direction) (weight : B -> nat) (costs : audit_dense_client_budget N E U)
    (queries : list (N * U)) : nat :=
  audit_dense_solve_budget EN EE EU gk cb direction weight costs +
    audit_dense_probe_batch_budget EN EU queries.

(** Under client laws, one solve supplies the ordered batch answers and bounded same-run work. *)
Definition audit_dense_batch_source_statement : Prop :=
  forall (S O N E U C B : Type) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (gk : genkill_view S O N E U C) (cb : audit_seg_build_callbacks N E U B)
    (direction : audit_seg_direction) (weight : B -> nat) (costs : audit_dense_client_budget N E U)
    (source : audit_dense_client_source N E U B) (queries : list (N * U)),
    audit_dense_client_laws EN EE EU gk cb weight costs source ->
    let sys := audit_dense_fx_system EU gk direction in
    let static := audit_dense_fx_static EU gk direction in
    let lattice := avail_lattice EU gk in
    let index_cb := audit_dense_index_model cb direction in
    let index_source := audit_dense_index_source cb direction in
    let index_budget := audit_dense_fx_index_budget (U := U) EN EE weight (dense_node_budget costs)
      (dense_edge_budget costs) (dense_target_budget costs) (dense_source_budget costs) in
    let schedule := fx_rpo_scheduler_counted EN sys static index_cb in
    let declared_source := audit_dense_declared_source EN EE EU gk cb direction schedule in
    let declared_budget := audit_dense_declared_budget EN EE EU gk costs weight direction in
    let '(constraints, constraint_events) := audit_dense_constraints (cfg (gkview gk)) cb
      direction in
    let '(bottom, bottom_events) := audit_dense_initial (cfg (gkview gk)) cb in
    exists result index_events init_events engine_events init_bodies engine_bodies,
      constraints = System.constraints sys /\ bottom = proj1_sig (bot lattice) /\
      Forall (audit_dense_universe_client_source weight source) constraint_events /\
      Forall (audit_dense_fx_client_source weight source) bottom_events /\
      audit_dense_annotated_total EN (dense_constraint_encoding EN EE) lattice
        (rpo_scheduler EN sys static) Joining sys index_cb index_source declared_source
        result index_events init_events engine_events init_bodies engine_bodies /\
      fx_total_callbacks_run EN (dense_constraint_encoding EN EE) lattice
        (rpo_scheduler EN sys static) Joining sys index_cb result index_events init_events
        engine_events /\
      fx_index_external_trace_adequacy index_source index_events /\
      Forall (audit_dense_index_client_source weight source) index_events /\
      fx_declared_trace_source declared_source init_events init_bodies /\
      fx_declared_trace_source declared_source engine_events engine_bodies /\
      Forall (Forall (Forall (audit_dense_fx_client_source weight source))) init_bodies /\
      Forall (Forall (Forall (audit_dense_fx_client_source weight source))) engine_bodies /\
      fx_dep_body_source index_source (fx_rpo_build_events schedule) /\
      Forall (fx_dep_prepare_source index_source) (fx_rpo_prepare_events schedule) /\
      Forall (fx_dep_dfs_source index_source) (fx_rpo_dfs_events schedule) /\
      Forall (fx_dep_positions_source index_source) (fx_rpo_position_events schedule) /\
      Forall (fx_dep_retreat_source index_source) (fx_rpo_retreat_events schedule) /\
      let '(answers, query_events) := audit_dense_probe_batch EU (expr_universe EU gk) cb (bot
        lattice)
        result queries in
      Forall (audit_dense_probe_client_source weight source) query_events /\
      answers = map (fun q => audit_seg_dense_query EN EE EU gk direction (fst q) (snd q))
        queries /\
      audit_dense_initial_work weight bottom_events + audit_seg_universe_work weight
        constraint_events +
        fx_rpo_scheduler_work index_budget schedule + fx_index_adapter_work index_budget
        index_events +
        fx_declared_model_work (dense_constraint_encoding EN EE) init_events +
        fx_declared_model_work (dense_constraint_encoding EN EE) engine_events +
        fx_declared_body_work (fx_body_weight declared_budget) init_bodies +
        fx_declared_body_work (fx_body_weight declared_budget) engine_bodies +
        audit_dense_probe_work weight query_events <=
      audit_dense_batch_budget EN EE EU gk cb direction weight costs queries +
        fold_right (fun e n => audit_seg_universe_event_budget (dense_out_budget costs)
          (dense_gen_budget costs) (dense_expr_budget costs) e + n) 0 constraint_events +
        fx_declared_external_trace_budget declared_budget init_events +
        fx_declared_external_trace_budget declared_budget engine_events +
        fold_right (fun e n => audit_dense_probe_event_budget (dense_node_budget costs)
          (dense_expr_budget costs) e + n) 0 query_events.
