(** * AnalysesAuditRewriteFacadeOptimizer

    This module relates facade extraction, explanation checking, and optimization to their work.
    For example, a missing selected explanation yields a reconstruction result of None.
    Builds on: AnalysesAuditRewriteFacadeRun and
    AnalysesAuditRewriteFacadeCheckedMaterialize. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Analyses Require Import AnalysesEgraph.
From Galois.Analyses Require Import AnalysesAuditRewriteFacadeCheckedMaterialize
  AnalysesAuditRewriteFacadeDimensions AnalysesAuditRewriteFacadeMaterialize
  AnalysesAuditRewriteFacadePrepare AnalysesAuditRewriteFacadeReference
  AnalysesAuditRewriteFacadeRun AnalysesAuditRewriteFacadeSourceWork.
From Galois.Rewrite Require Import RewriteAuditIndexDimensions RewriteAuditIndexRebuild
  RewriteAuditProofRun RewriteAuditProofSelected RewriteAuditProofTick
  RewriteAuditQueueReference RewriteAuditSharedExtract RewriteAuditSharedReference.
Import List.ListNotations.

Definition rw_facade_legacy_dimension {K} (legacy : rw_legacy_tracked_state K) : nat :=
  S (Pos.size_nat (rw_legacy_root K legacy) + rw_facade_tracked_dimension (rw_tracked_final
    (rw_legacy_core K legacy)) + rw_facade_leaves_dimension (rw_legacy_leaves K legacy)).

Definition rw_facade_dag_dimension {K} (dag : rw_shared_tree K unit nat) : nat :=
  S (Pos.size_nat (rw_shared_root K unit nat dag) +
    rw_whole_map_dimension Pos.size_nat (fun node =>
      match node with
      | RWSharedVar _ _ _ _ index => S index
      | RWSharedApp _ _ _ _ _ children => S (rw_whole_ids_dimension children)
      end) (rw_shared_nodes K unit nat dag)).

Definition rw_facade_steps_dimension {K} (steps : list (rewrite_step K)) : nat :=
  fold_right (fun step total => S (rw_facade_step_dimension step + total)) 1 steps.

(** Explanation reconstruction relates the selected core tree to checked replay steps
    or failure, with source work and operand dimension. *)
Inductive rw_facade_explain_core_run {K} (op : rw_queue_encoder_adapter K)
    (guard : rw_facade_guard_adapter K) (rules : list (rewrite_rule K)) (seed : term K)
    (source : rw_term K unit nat) (legacy : rw_legacy_tracked_state K)
    (tree : rw_term K unit nat) : option (list (rewrite_step K)) -> nat -> nat -> Prop :=
  | RPFExplainMissing : forall selected_work,
      rw_rp_selected_atomic op rw_facade_unit_adapter rw_facade_nat_adapter
        (rw_tracked_final (rw_legacy_core K legacy)) (rw_legacy_root K legacy) source tree =
        (None, selected_work) ->
      rw_facade_explain_core_run op guard rules seed source legacy tree None (64 + selected_work)
        (S (rw_facade_legacy_dimension legacy + rw_facade_core_dimension source +
          rw_facade_core_dimension tree))
  | RPFExplainMalformed : forall proof id selected_work materialization_work,
      rw_rp_selected_atomic op rw_facade_unit_adapter rw_facade_nat_adapter
        (rw_tracked_final (rw_legacy_core K legacy)) (rw_legacy_root K legacy) source tree =
        (Some (proof, id), selected_work) ->
      rw_facade_checked_materialize_run proof id None materialization_work ->
      rw_facade_explain_core_run op guard rules seed source legacy tree None
        (64 + selected_work + materialization_work)
        (S (rw_facade_legacy_dimension legacy + rw_facade_core_dimension source +
          rw_facade_core_dimension tree + rw_facade_proof_dimension proof + Pos.size_nat id))
  | RPFExplainChecked : forall proof id selected_work steps materialization_work output
      projection_work accepted checker_trace,
      rw_rp_selected_atomic op rw_facade_unit_adapter rw_facade_nat_adapter
        (rw_tracked_final (rw_legacy_core K legacy)) (rw_legacy_root K legacy) source tree =
        (Some (proof, id), selected_work) ->
      rw_facade_checked_materialize_run proof id (Some steps) materialization_work ->
      rw_facade_materialize_project_atomic tree = (output, projection_work) ->
      rw_facade_checker_atomic (rw_external_encoding_events op) guard rules seed output steps =
        (accepted, checker_trace) ->
      rw_facade_explain_core_run op guard rules seed source legacy tree
        (if accepted then Some steps else None)
        (64 + selected_work + materialization_work + projection_work +
          rw_facade_checker_source_work checker_trace)
        (S (rw_facade_legacy_dimension legacy + rw_facade_core_dimension source +
          rw_facade_core_dimension tree + rw_facade_proof_dimension proof + Pos.size_nat id +
          rw_facade_steps_dimension steps + rw_facade_term_dimension output +
          rw_facade_term_dimension seed)).

(** A selected explanation run embeds its endpoints and records reconstruction result,
    work, and dimension. *)
Inductive rw_facade_selected_run {K} (op : rw_queue_encoder_adapter K)
    (guard : rw_facade_guard_adapter K) (rules : list (rewrite_rule K)) (seed : term K)
    (legacy : rw_legacy_tracked_state K) (output : term K) :
    option (list (rewrite_step K)) -> nat -> nat -> Prop :=
  | RPFSelectedRun : forall source source_trace tree tree_trace result work dimension,
      rw_facade_embed_atomic seed = (source, source_trace) ->
      rw_facade_embed_atomic output = (tree, tree_trace) ->
      rw_facade_explain_core_run op guard rules seed source legacy tree result work dimension ->
      rw_facade_selected_run op guard rules seed legacy output result
        (64 + 64 * audit_work source_trace + 64 * audit_work tree_trace + work)
        (S (rw_facade_term_dimension seed + rw_facade_term_dimension output + dimension)).

(** Facade extraction relates the tracked result to an extracted shared tree and its
    unfolding, or failure, with work and dimension. *)
Inductive rw_facade_extract_run {K} (op : rw_queue_encoder_adapter K)
    (cost : K -> nat * nat) (legacy : rw_legacy_tracked_state K) :
    option (rw_shared_tree K unit nat * rw_term K unit nat) -> nat -> nat -> Prop :=
  | RPFExtractMissing : forall graph graph_work extraction_work,
      rw_ri_graph_atomic (rw_tracked_machine (rw_tracked_final (rw_legacy_core K legacy))) =
        (graph, graph_work) ->
      rw_shared_extract_run op rw_facade_unit_adapter rw_facade_nat_adapter
        (fun _ => (0, 64)) cost graph (rw_legacy_root K legacy) None extraction_work ->
      rw_facade_extract_run op cost legacy None (64 + graph_work + extraction_work)
        (S (rw_facade_legacy_dimension legacy + rw_facade_graph_dimension graph))
  | RPFExtractMalformed : forall graph graph_work dag extraction_work unfolding_trace,
      rw_ri_graph_atomic (rw_tracked_machine (rw_tracked_final (rw_legacy_core K legacy))) =
        (graph, graph_work) ->
      rw_shared_extract_run op rw_facade_unit_adapter rw_facade_nat_adapter
        (fun _ => (0, 64)) cost graph (rw_legacy_root K legacy) (Some dag) extraction_work ->
      rw_shared_unfold_atomic dag = (None, unfolding_trace) ->
      rw_facade_extract_run op cost legacy None
        (64 + graph_work + extraction_work + rw_shared_unfold_trace_cost unfolding_trace)
        (S (rw_facade_legacy_dimension legacy + rw_facade_graph_dimension graph +
          rw_facade_dag_dimension dag))
  | RPFExtractFound : forall graph graph_work dag extraction_work tree unfolding_trace,
      rw_ri_graph_atomic (rw_tracked_machine (rw_tracked_final (rw_legacy_core K legacy))) =
        (graph, graph_work) ->
      rw_shared_extract_run op rw_facade_unit_adapter rw_facade_nat_adapter
        (fun _ => (0, 64)) cost graph (rw_legacy_root K legacy) (Some dag) extraction_work ->
      rw_shared_unfold_atomic dag = (Some tree, unfolding_trace) ->
      rw_facade_extract_run op cost legacy (Some (dag, tree))
        (64 + graph_work + extraction_work + rw_shared_unfold_trace_cost unfolding_trace)
        (S (rw_facade_legacy_dimension legacy + rw_facade_graph_dimension graph +
          rw_facade_dag_dimension dag + rw_facade_core_dimension tree)).

(** An optimizer run combines tracked execution, extraction, and selected explanation
    into an optional result, work, and dimension. *)
Inductive rw_facade_optimizer_run {K} (EK : encoding K) (op : rw_queue_encoder_adapter K)
    (guard : rw_facade_guard_adapter K) (cost : K -> nat * nat)
    (rules : list (rewrite_rule K)) (fuel : positive) (seed : term K) :
    option (rw_shared_tree K unit nat * list (rewrite_step K)) -> nat -> nat -> Prop :=
  | RPFOptimizerNoTree : forall legacy run_work run_dimension extraction_work extraction_dimension,
      rw_facade_tracked_run EK op guard rules fuel seed legacy run_work run_dimension ->
      rw_facade_extract_run op cost legacy None extraction_work extraction_dimension ->
      rw_facade_optimizer_run EK op guard cost rules fuel seed None
        (64 + run_work + extraction_work) (Nat.max run_dimension extraction_dimension)
  | RPFOptimizerSelected : forall legacy run_work run_dimension dag tree extraction_work
      extraction_dimension source source_trace result selection_work selection_dimension,
      rw_facade_tracked_run EK op guard rules fuel seed legacy run_work run_dimension ->
      rw_facade_extract_run op cost legacy (Some (dag, tree)) extraction_work
        extraction_dimension ->
      rw_facade_embed_atomic seed = (source, source_trace) ->
      rw_facade_explain_core_run op guard rules seed source legacy tree
        result selection_work selection_dimension ->
      rw_facade_optimizer_run EK op guard cost rules fuel seed
        (option_map (fun steps => (dag, steps)) result)
        (64 + run_work + extraction_work + 64 * audit_work source_trace + selection_work)
        (Nat.max run_dimension (Nat.max extraction_dimension selection_dimension)).
