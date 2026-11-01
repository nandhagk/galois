(** * Adapted family source bounds

    These obligations bind every genuine foreign callback to its actual input, result and body.
    For example, internally prepared predecessor lookups never receive a foreign source-price law.
    Builds on: the family's complete source model and the shared actual-call adapter. *)

From Stdlib Require Import List PArith NArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare GraphAuditBase.
From Galois.Domains Require Import DomainsFootprint.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryWalk.
From Galois.Collections Require Import CollectionsAuditCallback CollectionsAuditMap
  CollectionsAuditElements.
From Galois.Analyses Require Import AnalysesAuditMemoryEncoding AnalysesAuditMemoryInputBudget
  AnalysesAuditMemoryRawNext AnalysesAuditMemoryWalkIndex AnalysesAuditMemoryTable
  AnalysesAuditMemorySharedBudget AnalysesAuditMemoryClobbersSource AnalysesAuditMemorySearch
  AnalysesAuditMemorySearchInputBudget.
Import List.ListNotations.

(** Matching node, outgoing and target callbacks and adapter laws bound adjacency construction,
    search and root materialization. *)
Definition audit_memory_clobbers_whole_input_bound_adapted_statement : Prop :=
  forall N E T CN CE SE OE TE FE PE BE (EN : encoding N)
      (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
      (site_enc : T -> positive * list SE) (out : N -> list E * list OE)
      (target : E -> N * list TE) (effects : E -> list (memory_effect T) * list FE)
      (operand : N -> option E -> option (memory_version N E) * list PE)
      (before : E -> nat -> option (memory_version N E) * list BE)
      node_work edge_work site_work out_work target_work effect_work operand_work before_work
      node_budget edge_budget site_budget out_budget target_budget effect_budget
      operand_budget before_budget (g : Graph.t N E) (mg : memory_graph N E) scope start fuel
        node_enc_source edge_enc_source site_enc_source out_source target_source effects_source
        operand_source before_source,
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall n, fst (out n) = Graph.out g n) ->
    (forall e, fst (target e) = Graph.target g e) ->
    audit_external_callback_adapter node_enc node_work node_enc_source node_budget ->
    audit_external_callback_adapter edge_enc edge_work edge_enc_source edge_budget ->
    audit_external_callback_adapter site_enc site_work site_enc_source site_budget ->
    audit_external_callback_adapter out out_work out_source out_budget ->
    audit_external_callback_adapter target target_work target_source target_budget ->
    audit_external_callback_adapter effects effect_work effects_source effect_budget ->
    audit_external_callback_adapter
      (fun args => operand (fst args) (snd args)) operand_work operand_source
      (fun args => operand_budget (fst args) (snd args)) ->
    audit_external_callback_adapter
      (fun args => before (fst args) (snd args)) before_work before_source
      (fun args => before_budget (fst args) (snd args)) ->
    audit_memory_clobbers_full_source_work node_work edge_work site_work out_work target_work
      effect_work operand_work before_work (audit_memory_clobbers_source_counted EN node_enc
        edge_enc
        site_enc out target effects operand before g mg scope start fuel) <=
    audit_memory_clobbers_whole_input_budget EN node_enc edge_enc site_enc out target effects
      operand
      before node_budget out_budget edge_budget effect_budget target_budget site_budget
      operand_budget before_budget g mg scope start fuel.
