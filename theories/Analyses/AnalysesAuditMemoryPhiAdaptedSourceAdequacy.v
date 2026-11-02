(** * Foreign callback bounds for phi closures

    Actual foreign callback witnesses compose with the library's concrete version encoder bound.
    For example, a total callback retains its original result before the optional wrapper is used.
    Builds on: AnalysesAuditMemoryPhiAdaptedSource and closure and encoder adequacy. *)

From Stdlib Require Import List.
From Galois.Collections Require Import CollectionsAuditCallback CollectionsAuditCallbackAdequacy.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesAuditMemoryEncoding
  AnalysesAuditMemoryInputBudget AnalysesAuditMemoryInputBudgetAdequacy
  AnalysesAuditMemoryPhiConsumer AnalysesAuditMemoryPhiConsumerAdequacy
  AnalysesAuditMemoryPhiAdaptedSource AnalysesAuditMemoryPhiSetupAdequacy.

Lemma audit_phi_adapter_budget A R B (call : A -> R * list B) work source budget :
  audit_external_callback_adapter call work source budget ->
  forall input, work (snd (call input)) <= budget input.
Proof.
  intros Hadapter input.
  exact (proj2 (audit_external_callback_observed A R B call work source budget Hadapter input)).
Qed.

(** Actual foreign witnesses supply each callback budget; predecessor reads stay internal. *)
Theorem audit_memory_phi_prune_whole_input_bound_adapted :
  audit_memory_phi_prune_whole_input_bound_adapted_statement.
Proof.
  intros N E T CN CE OE TE PE EN EE node_enc edge_enc out target operand
    node_work edge_work out_work target_work operand_work
    node_budget edge_budget out_budget target_budget operand_budget g effects mg
    node_source edge_source out_source target_source operand_source
    Hencode Hout Htarget Hnode Hedge Hout_adapter Htarget_adapter Hoperand.
  apply audit_memory_phi_prune_whole_input_bound; try assumption.
  - apply (audit_phi_adapter_budget _ _ _ node_enc node_work node_source node_budget Hnode).
  - apply (audit_phi_adapter_budget _ _ _ edge_enc edge_work edge_source edge_budget Hedge).
  - apply (audit_phi_adapter_budget _ _ _ out out_work out_source out_budget Hout_adapter).
  - apply (audit_phi_adapter_budget _ _ _ target target_work target_source target_budget
      Htarget_adapter).
  - intros n key.
    exact (audit_phi_adapter_budget _ _ _ (fun args => operand (fst args) (snd args))
      operand_work operand_source (fun args => operand_budget (fst args) (snd args))
      Hoperand (n, key)).
Qed.

(** Optional closure work retains its actual source witness and concrete input-derived bound. *)
Theorem audit_phi_optional_closure_source_bound : audit_phi_optional_closure_source_bound_statement.
Proof.
  intros I N E CN CE B node_enc edge_enc base node_work edge_work base_work
    node_budget edge_budget base_budget node_source edge_source base_source representatives
    input Hnode Hedge Hbase.
  split.
  - exact (proj1 (audit_external_callback_observed I _ B base base_work base_source base_budget
      Hbase input)).
  - apply audit_phi_closure_whole_input_bound.
    + intro v; apply audit_memory_version_input_bound.
      * apply (audit_phi_adapter_budget _ _ _ node_enc node_work node_source node_budget Hnode).
      * apply (audit_phi_adapter_budget _ _ _ edge_enc edge_work edge_source edge_budget Hedge).
    + apply (audit_phi_adapter_budget _ _ _ base base_work base_source base_budget Hbase).
Qed.

(** The library's optional wrapper preserves a total callback's witness and body budget. *)
Theorem audit_phi_total_closure_source_bound : audit_phi_total_closure_source_bound_statement.
Proof.
  intros I N E CN CE B node_enc edge_enc base node_work edge_work base_work
    node_budget edge_budget base_budget node_source edge_source base_source representatives
    input Hnode Hedge Hbase.
  split.
  - exact (proj1 (audit_external_callback_observed I _ B base base_work base_source base_budget
      Hbase input)).
  - unfold audit_phi_output_total_call.
    apply audit_phi_closure_whole_input_bound.
    + intro v; apply audit_memory_version_input_bound.
      * apply (audit_phi_adapter_budget _ _ _ node_enc node_work node_source node_budget Hnode).
      * apply (audit_phi_adapter_budget _ _ _ edge_enc edge_work edge_source edge_budget Hedge).
    + intro arg.
      pose proof (audit_phi_adapter_budget _ _ _ base base_work base_source base_budget Hbase arg)
        as Hbound.
      destruct (base arg); exact Hbound.
Qed.
