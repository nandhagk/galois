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
From Galois.Collections Require Import CollectionsAuditCallback.
From Galois.Analyses Require Import AnalysesAuditMemoryPhiState.
From Galois.Collections Require Import CollectionsAuditMap.
From Galois.Analyses Require Import AnalysesAuditMemoryEncoding AnalysesAuditMemoryInputBudget
  AnalysesAuditMemoryPhiProducer AnalysesAuditMemoryPhiInputBudget AnalysesAuditMemoryPhiConsumer
  AnalysesAuditMemoryPhiSetup.
Import List.ListNotations.

(** Matching node, outgoing and target callbacks and adapter laws bound phi pruning from graph
    preparation through the produced graph. *)
Definition audit_memory_phi_prune_whole_input_bound_adapted_statement : Prop :=
  forall N E T CN CE OE TE PE (EN : encoding N) (EE : encoding E)
      (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
      (out : N -> list E * list OE) (target : E -> N * list TE)
      (operand : N -> option E -> option (memory_version N E) * list PE)
      node_work edge_work out_work target_work operand_work
      node_budget edge_budget out_budget target_budget operand_budget
      (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E)
        node_enc_source edge_enc_source out_source target_source operand_source,
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall n, fst (out n) = Graph.out g n) ->
    (forall e, fst (target e) = Graph.target g e) ->
    audit_external_callback_adapter node_enc node_work node_enc_source node_budget ->
    audit_external_callback_adapter edge_enc edge_work edge_enc_source edge_budget ->
    audit_external_callback_adapter out out_work out_source out_budget ->
    audit_external_callback_adapter target target_work target_source target_budget ->
    audit_external_callback_adapter
      (fun args => operand (fst args) (snd args)) operand_work operand_source
      (fun args => operand_budget (fst args) (snd args)) ->
    let '(base, preparation, run) := audit_memory_phi_prune_counted EN EE node_enc edge_enc
      out target operand g effects mg in
    audit_prepare_source_work (audit_phi_input_graph_body_work node_work out_work target_work)
      preparation +
    audit_phi_producer_work node_work edge_work (audit_map_source_work node_work) operand_work
      (audit_memory_version_work node_work edge_work) EN run <=
    audit_prepare_source_budget EN g + audit_graph_prepare_full_event_bound g *
      audit_phi_input_graph_envelope out target node_budget out_budget target_budget
        (Graph.nodes g) +
    audit_phi_producer_input_budget EN EE node_enc edge_enc
      (audit_phi_predecessors_counted EN node_enc g base) operand node_budget edge_budget
      (audit_phi_get_input_budget node_enc node_budget) operand_budget g effects mg.

(** Under the three callback adapter laws, the optional callback has its recorded source witness
    and the closure work is bounded by the input budget. *)
Definition audit_phi_optional_closure_source_bound_statement : Prop :=
  forall I N E CN CE B (node_enc : N -> positive * list CN)
      (edge_enc : E -> positive * list CE)
      (base : I -> option (memory_version N E) * list B)
      node_work edge_work base_work node_budget edge_budget base_budget
      node_source edge_source base_source representatives input,
    audit_external_callback_adapter node_enc node_work node_source node_budget ->
    audit_external_callback_adapter edge_enc edge_work edge_source edge_budget ->
    audit_external_callback_adapter base base_work base_source base_budget ->
    base_source input (fst (base input)) (snd (base input)) (base_work (snd (base input))) /\
    audit_phi_closure_source_work (audit_memory_version_work node_work edge_work) base_work
      (snd (audit_phi_output_optional_call (audit_memory_version_encode node_enc edge_enc)
        base representatives input)) <=
    audit_phi_closure_input_budget (audit_memory_version_encode node_enc edge_enc) base
      (audit_memory_version_input_budget node_enc edge_enc node_budget edge_budget) base_budget
        input.

(** Under the three callback adapter laws, the total callback has its recorded source witness
    and the closure work is bounded by the optional-wrapper input budget. *)
Definition audit_phi_total_closure_source_bound_statement : Prop :=
  forall I N E CN CE B (node_enc : N -> positive * list CN)
      (edge_enc : E -> positive * list CE) (base : I -> memory_version N E * list B)
      node_work edge_work base_work node_budget edge_budget base_budget
      node_source edge_source base_source representatives input,
    audit_external_callback_adapter node_enc node_work node_source node_budget ->
    audit_external_callback_adapter edge_enc edge_work edge_source edge_budget ->
    audit_external_callback_adapter base base_work base_source base_budget ->
    base_source input (fst (base input)) (snd (base input)) (base_work (snd (base input))) /\
    audit_phi_closure_source_work (audit_memory_version_work node_work edge_work) base_work
      (snd (audit_phi_output_total_call (audit_memory_version_encode node_enc edge_enc)
        base representatives input)) <=
    audit_phi_closure_input_budget (audit_memory_version_encode node_enc edge_enc)
      (fun argument => let '(version, body) := base argument in (Some version, body))
      (audit_memory_version_input_budget node_enc edge_enc node_budget edge_budget) base_budget
        input.
