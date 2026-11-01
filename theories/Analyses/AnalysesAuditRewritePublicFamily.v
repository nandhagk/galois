(** * Fixed public Rewrite source family

    This module combines the fixed facade source-work contracts with the public source family.
    For example, the tracked cost type uses 1 as the ceiling's fuel argument when fuel is 1.
    Builds on: fixed plain builders, exact public contracts and full source cost models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Analyses Require Import AnalysesEgraph.
From Galois.Analyses Require Import AnalysesAuditRewriteFacadeCheckerContracts
  AnalysesAuditRewriteFacadeDimensions AnalysesAuditRewriteFacadeOptimizer
  AnalysesAuditRewriteFacadePlainContracts AnalysesAuditRewriteFacadePlainExplain
  AnalysesAuditRewriteFacadePlainMaterializer AnalysesAuditRewriteFacadePlainRun
  AnalysesAuditRewriteFacadePrepare AnalysesAuditRewriteFacadeRun
  AnalysesAuditRewriteFacadeWholeContracts.
From Galois.Rewrite Require Import RewriteAuditIndexPlainContracts RewriteAuditIndexPublicSource
  RewriteAuditIndexWholeContracts RewriteAuditProofFactWholeContracts
  RewriteAuditProofPlainContracts RewriteAuditProofPublicSource
  RewriteAuditProofSelectedContracts RewriteAuditProofWholeContracts RewriteAuditQueueContracts
  RewriteAuditQueueReference RewriteAuditSharedBoundsContracts RewriteAuditSharedFixedContracts
  RewriteAuditSharedPlain RewriteAuditSharedPlainContracts.
Import List.ListNotations.
Local Coercion encode : encoding >-> Funclass.

(** With agreeing operator encoding and guard laws, the tracked builder has a source run;
    its work meets the ceiling when the foreign envelope holds. *)
Definition rw_facade_public_tracked_source_cost_type (Hwf : rw_rd_plain_compare_well_founded_type) :
    Prop :=
  forall K (EK : encoding K) (op : rw_queue_encoder_adapter K) guard rules fuel seed width body,
    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    rw_facade_guard_program_laws guard ->
    exists work dimension,
      rw_facade_tracked_run EK op guard rules fuel seed
        (rw_legacy_tracked_builder Hwf K EK rules fuel seed) work dimension /\
      (rw_facade_foreign_envelope op guard (fun _ => (0, 0)) rules
        (rw_facade_input_ops rules [seed]) dimension width body 0 ->
        (N.of_nat work <= rw_facade_whole_ceiling (Npos fuel) dimension width body 0)%N).

(** With agreeing operator encoding and guard laws, the selected builder has a source run;
    its work meets the ceiling when the foreign envelope holds. *)
Definition rw_facade_public_selected_source_cost_type (Hmat :
    rw_facade_plain_materialize_well_founded_type) : Prop :=
  forall K (EK : encoding K) (op : rw_queue_encoder_adapter K) guard rules seed
    (legacy : rw_legacy_tracked_state K) output width body,
    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    rw_facade_guard_program_laws guard ->
    exists work dimension,
      rw_facade_selected_run op guard rules seed legacy output
        (rw_legacy_selected_explanation_builder Hmat K EK rules seed legacy output)
        work dimension /\
      (let complete_dimension := S (dimension +
          fold_right (fun rule total => S (rw_facade_rule_dimension rule + total)) 1 rules) in
        rw_facade_foreign_envelope op guard (fun _ => (0, 0)) rules
          (rw_facade_selected_ops rules seed output legacy) complete_dimension width body 0 ->
        (N.of_nat work <= rw_facade_whole_ceiling 0%N complete_dimension width body 0)%N).

(** With agreeing operator encoding and guard laws, the optimizer builder has a source run;
    its work meets the ceiling when the foreign envelope holds. *)
Definition rw_facade_public_optimizer_source_cost_type (Hwf : rw_rd_plain_compare_well_founded_type)
    (Hmat : rw_facade_plain_materialize_well_founded_type) : Prop :=
  forall K (EK : encoding K) (op : rw_queue_encoder_adapter K) guard
    (cost : K -> nat * nat) rules fuel seed width body weight,
    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    rw_facade_guard_program_laws guard ->
    exists work dimension,
      rw_facade_optimizer_run EK op guard cost rules fuel seed
        (rw_tracked_optimise_builder Hwf Hmat K EK rules (fun k => fst (cost k)) fuel seed)
        work dimension /\
      (rw_facade_foreign_envelope op guard cost rules (rw_facade_input_ops rules [seed])
          dimension width body weight ->
        (N.of_nat work <= rw_facade_whole_ceiling (Npos fuel) dimension width body weight)%N).

(** The family combines the two well-foundedness propositions with the fixed producer,
    semantic, and source-work contracts under those well-foundedness witnesses. *)
Definition rw_fixed_public_source_family_statement : Prop :=
  rw_rd_plain_compare_well_founded_type /\
  rw_facade_plain_materialize_well_founded_type /\
  forall (Hwf : rw_rd_plain_compare_well_founded_type)
    (Hmat : rw_facade_plain_materialize_well_founded_type),
    rw_rq_rebuild_source_complete_contract_statement /\
    rw_rq_rebuild_input_bound_statement /\
    rw_rd_extract_bound_statement /\
    rw_rd_scalar_bound_statement /\
    rw_rd_unary_cost_bound_statement /\
    rw_ri_whole_bound_statement /\
    rw_rp_whole_bound_statement /\
    rw_rp_selected_bound_statement /\
    rw_rp_fact_whole_bound_statement /\
    rw_facade_optimizer_whole_bound_statement /\
    rw_facade_selected_whole_bound_statement /\
    rw_facade_checker_whole_bound_statement /\
    rw_ri_public_source_cost_statement /\
    rw_rp_public_source_cost_statement /\
    rw_rp_public_selected_source_cost_statement /\
    rw_rp_public_fact_source_cost_statement /\
    rw_facade_tracked_realizes_fixed_type Hwf /\
    rw_legacy_run_link_fixed_type Hwf /\
    rw_facade_selected_realizes_fixed_type Hmat /\
    rw_selected_explanation_accepts_fixed_type Hwf Hmat /\
    rw_facade_optimizer_realizes_fixed_type Hwf Hmat /\
    rw_tracked_optimise_selected_fixed_type Hwf Hmat /\
    rw_ri_rule_step_realizes_fixed_type /\
    rw_ri_apply_realizes_fixed_type /\
    rw_ri_run_realizes_fixed_type /\
    rw_index_run_clean_trace_fixed_type /\
    rw_index_run_zero_fixed_type /\
    rw_index_run_correct_fixed_type /\
    rw_index_run_callback_bound_fixed_type /\
    rw_index_rule_step_supported_fixed_type /\
    rw_rp_run_realizes_fixed_type /\
    rw_rp_selected_realizes_fixed_type /\
    rw_repr_find_spec_fixed_type /\
    rw_tracked_extractable_fixed_type /\
    rw_tracked_selected_fixed_type /\
    rw_tracked_run_invariants_fixed_type /\
    rw_tracked_tick_projection_fixed_type /\
    rw_tracked_tick_congruence_fixed_type /\
    rw_tracked_rebuild_trace_correct_fixed_type /\
    rw_tracked_apply_projects_fixed_type /\
    rw_tracked_factful_apply_reject_fixed_type /\
    rw_tracked_factful_apply_accept_fixed_type /\
    rw_factful_run_zero_fixed_type /\
    rw_factful_run_valid_fixed_type /\
    rw_factful_run_callback_bound_fixed_type /\
    rw_rp_repr_realizes_fixed_type /\
    rw_rp_connect_realizes_fixed_type /\
    rw_rp_tick_realizes_fixed_type /\
    rw_rp_rebuild_realizes_fixed_type /\
    rw_rp_rule_step_realizes_fixed_type /\
    rw_rp_apply_realizes_fixed_type /\
    rw_rp_factful_apply_realizes_fixed_type /\
    rw_rp_fact_run_realizes_fixed_type /\
    rw_rd_compare_realizes_fixed_type Hwf /\
    rw_rd_extract_realizes_fixed_type Hwf /\
    rw_rd_scalar_realizes_fixed_type /\
    rw_shared_compare_agrees_fixed_type Hwf /\
    rw_shared_compare_reject_fixed_type Hwf /\
    rw_shared_extract_unfold_fixed_type Hwf /\
    rw_shared_tree_cost_agrees_fixed_type /\
    rw_shared_tree_cost_binary_agrees_fixed_type /\
    rw_shared_tree_size_binary_agrees_fixed_type /\
    rw_shared_observers_reject_fixed_type /\
    rw_rd_plain_compare_realizes_type Hwf /\
    rw_rd_plain_extract_realizes_type Hwf /\
    rw_rd_plain_scalar_realizes_type /\
    rw_rd_plain_compare_agrees_type Hwf /\
    rw_rd_plain_compare_reject_type Hwf /\
    rw_rd_plain_extract_unfold_type Hwf /\
    rw_rd_plain_tree_cost_agrees_type /\
    rw_rd_plain_tree_cost_binary_agrees_type /\
    rw_rd_plain_tree_size_binary_agrees_type /\
    rw_rd_plain_observers_reject_type /\
    rw_rd_plain_compare_source_erases_type Hwf /\
    rw_rd_plain_extract_source_erases_type Hwf /\
    rw_rd_plain_production_source_erases_type /\
    rw_facade_plain_materialize_source_erases_type Hmat /\
    rw_facade_plain_materialize_realizes_type Hmat /\
    rw_facade_plain_materialize_shape_erases_type /\
    rw_facade_plain_materialize_source_bound_type Hmat /\
    rw_facade_public_tracked_source_cost_type Hwf /\
    rw_facade_public_selected_source_cost_type Hmat /\
    rw_facade_public_optimizer_source_cost_type Hwf Hmat.
