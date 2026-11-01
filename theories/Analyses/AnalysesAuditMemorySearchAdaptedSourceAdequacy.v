(** * Adapted clobber-search source bound

    Foreign callback adapters supply budgets for the bodies returned by the same calls.
    For example, an operand adapter receives the actual node and incoming key together.
    Builds on: callback adequacy and complete clobber source adequacy. *)

From Galois.Collections Require Import CollectionsAuditCallbackAdequacy.
From Galois.Analyses Require Import AnalysesAuditMemorySearchAdaptedSource
  AnalysesAuditMemoryClobbersSourceAdequacy.

(** * Foreign callback budgets *)

(** Each foreign adapter supplies the per-input bound used by the complete search. *)
Theorem audit_memory_clobbers_whole_input_bound_adapted :
  audit_memory_clobbers_whole_input_bound_adapted_statement.
Proof.
  intros N E T CN CE SE OE TE FE PE BE EN node_enc edge_enc site_enc out target effects operand
    before node_work edge_work site_work out_work target_work effect_work operand_work before_work
    node_budget edge_budget site_budget out_budget target_budget effect_budget operand_budget
    before_budget g mg scope start fuel node_source edge_source site_source out_source target_source
    effects_source operand_source before_source Hnode Hout Htarget Hnode_adapter Hedge_adapter
    Hsite_adapter Hout_adapter Htarget_adapter Heffects_adapter Hoperand_adapter Hbefore_adapter.
  apply audit_memory_clobbers_whole_input_bound; try assumption.
  - intro n; exact (proj2 (audit_external_callback_observed N _ CN node_enc node_work node_source
      node_budget Hnode_adapter n)).
  - intro e; exact (proj2 (audit_external_callback_observed E _ CE edge_enc edge_work edge_source
      edge_budget Hedge_adapter e)).
  - intro t; exact (proj2 (audit_external_callback_observed T _ SE site_enc site_work site_source
      site_budget Hsite_adapter t)).
  - intro n; exact (proj2 (audit_external_callback_observed N _ OE out out_work out_source
      out_budget Hout_adapter n)).
  - intro e; exact (proj2 (audit_external_callback_observed E _ TE target target_work target_source
      target_budget Htarget_adapter e)).
  - intro e; exact (proj2 (audit_external_callback_observed E _ FE effects effect_work
      effects_source effect_budget Heffects_adapter e)).
  - intros n key; exact (proj2 (audit_external_callback_observed (N * option E)%type _ PE
      (fun args => operand (fst args) (snd args)) operand_work operand_source
      (fun args => operand_budget (fst args) (snd args)) Hoperand_adapter (n, key))).
  - intros e index; exact (proj2 (audit_external_callback_observed (E * nat)%type _ BE
      (fun args => before (fst args) (snd args)) before_work before_source
      (fun args => before_budget (fst args) (snd args)) Hbefore_adapter (e, index))).
Qed.
