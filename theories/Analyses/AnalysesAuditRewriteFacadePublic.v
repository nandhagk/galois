(** * AnalysesAuditRewriteFacadePublic

    This module states totality, uniqueness, agreement, and checking contracts for the facade.
    For example, given a well-formed provenance map with a rule-0 node, its capture claim
    requires a corresponding step at the same identifier.
    Builds on: AnalysesAuditRewriteFacadeOffers and
    AnalysesAuditRewriteFacadeOptimizer. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Analyses Require Import AnalysesEgraph.
From Galois.Analyses Require Import AnalysesAuditRewriteFacadeMaterialize
  AnalysesAuditRewriteFacadeOffers AnalysesAuditRewriteFacadeOptimizer
  AnalysesAuditRewriteFacadePrepare AnalysesAuditRewriteFacadeReference2
  AnalysesAuditRewriteFacadeRun.
From Galois.Rewrite Require Import RewriteAuditIndexReference RewriteAuditProofCarrier
  RewriteAuditProofRun RewriteAuditProofTick RewriteAuditQueueReference.
Import List.ListNotations.

(** The facade strategy has an offer, work, and dimension observation for every state. *)
Definition rw_facade_strategy_total_statement : Prop :=
  forall K (op : rw_queue_encoder_adapter K) guard (prepared : rw_facade_prepared K) state, exists
    offer work dimension, rw_facade_strategy_run op guard prepared state offer work dimension.

(** Two strategy runs on the same inputs have equal offers, work, and dimensions. *)
Definition rw_facade_strategy_unique_statement : Prop :=
  forall K (op : rw_queue_encoder_adapter K) guard (prepared : rw_facade_prepared K) state first fw
    fd second sw sd, rw_facade_strategy_run op guard prepared state first fw fd ->
    rw_facade_strategy_run op guard prepared state second sw sd ->
    first = second /\
    fw = sw /\
    fd = sd.

(** When the operator adapter agrees, guard laws hold, and the index is valid, a
    prepared facade strategy run chooses the legacy strategy offer. *)
Definition rw_facade_strategy_agrees_statement : Prop :=
  forall K (EK : encoding K) (op : rw_queue_encoder_adapter K) guard rules state offer work
    dimension, (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    rw_facade_guard_program_laws guard ->
    rw_index_valid EK unit_encoding nat_encoding legacy_signature state ->
    rw_facade_strategy_run op guard (fst (rw_facade_prepare_atomic rules 0)) state offer work
      dimension ->
    offer = rw_legacy_strategy EK rules (legacy_list_table rules 0) (rw_index_view EK unit_encoding
      nat_encoding state).

(** For a well-formed provenance map containing the specified rule node, capture
    stores its rule index and erased bindings under the same identifier. *)
Definition rw_facade_capture_exact_statement : Prop :=
  forall K (output : rw_tracked_output K unit nat nat) id index bindings,
    let proof := rw_tracked_provenance (rw_tracked_final output) in
    (exists node, Map.get positive_encoding id (rw_provenance_nodes proof) = Some node /\
      rw_evidence_reason_of node = RWEvidenceRule index bindings) ->
    Map.wf positive_encoding (rw_provenance_nodes proof) ->
    Map.get positive_encoding id (fst (rw_facade_capture_atomic output)) =
      Some (RewriteStep nil index true (fst (rw_facade_bindings_atomic bindings))).

(** When the operator adapter agrees and guard laws hold, a selected facade run
    returning steps produces an explanation accepted by the checker. *)
Definition rw_facade_selected_checked_statement : Prop :=
  forall K (EK : encoding K) (op : rw_queue_encoder_adapter K) guard rules seed legacy output steps
    work dimension, (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    rw_facade_guard_program_laws guard ->
    rw_facade_selected_run op guard rules seed legacy output (Some steps) work dimension ->
    check_explanation EK rules seed output steps = true.

(** The facade optimizer has a result, work, and dimension observation for every input. *)
Definition rw_facade_optimizer_total_statement : Prop :=
  forall K (EK : encoding K) (op : rw_queue_encoder_adapter K) guard cost rules fuel seed, exists
    result work dimension, rw_facade_optimizer_run EK op guard cost rules fuel seed result work
    dimension.

(** Two optimizer runs on the same inputs have equal results, work, and dimensions. *)
Definition rw_facade_optimizer_unique_statement : Prop :=
  forall K (EK : encoding K) (op : rw_queue_encoder_adapter K) guard cost rules fuel seed first fw
    fd second sw sd, rw_facade_optimizer_run EK op guard cost rules fuel seed first fw fd ->
    rw_facade_optimizer_run EK op guard cost rules fuel seed second sw sd ->
    first = second /\
    fw = sw /\
    fd = sd.
