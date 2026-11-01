(** * Foreign callback composition for memo source bounds

    Actual callback adapters bound the very bodies retained by the public memo and snapshot calls.
    For example, an operand adapter receives its node and incoming key together.
    Builds on: callback observations and concrete public memo and refresh source bounds. *)

From Stdlib Require Import List.
From Galois.Collections Require Import CollectionsAuditCallback CollectionsAuditCallbackAdequacy.
From Galois.Analyses Require Import AnalysesAuditMemoryMemoAdaptedSource
  AnalysesAuditMemoryMemoPublicSourceAdequacy AnalysesAuditMemoryMemoSnapshotSourceAdequacy.

(** * Actual callback budgets *)

(** A genuine callback's adapter supplies the bound at the same actual input and returned body. *)
Local Ltac audit_memo_foreign_budget :=
  match goal with
  | H : audit_external_callback_adapter ?call ?work ?source ?budget |-
      ?work (snd (?call ?argument)) <= ?budget ?argument =>
    exact (proj2 (audit_external_callback_observed _ _ _ call work source budget H argument))
  end.

(** Public memo bounds compose only genuine foreign encoder and memory callback adapters. *)
Theorem audit_memory_memo_public_whole_input_bound_adapted :
  audit_memory_memo_public_whole_input_bound_adapted_statement.
Proof.
  intros N E T CN CE SE OE BE EN node_enc edge_enc site_enc g effects mg state operand before
    node_work edge_work site_work operand_work before_work
    node_budget edge_budget site_budget operand_budget before_budget scope start fuel
    node_source edge_source site_source operand_source before_source
    Hnode Hedge Hsite Hoperand Hbefore.
  apply audit_memory_memo_public_whole_input_bound.
  - intro node; audit_memo_foreign_budget.
  - intro edge; audit_memo_foreign_budget.
  - intro site; audit_memo_foreign_budget.
  - intros node key; exact (proj2 (audit_external_callback_observed (N * option E)%type _ OE
      (fun args => operand (fst args) (snd args)) operand_work operand_source
      (fun args => operand_budget (fst args) (snd args)) Hoperand (node, key))).
  - intros edge index; exact (proj2 (audit_external_callback_observed (E * nat)%type _ BE
      (fun args => before (fst args) (snd args)) before_work before_source
      (fun args => before_budget (fst args) (snd args)) Hbefore (edge, index))).
Qed.

(** Initial preparation adapters cover every actual graph and effect callback body. *)
Theorem audit_memory_memo_initial_whole_input_bound_adapted :
  audit_memory_memo_initial_whole_input_bound_adapted_statement.
Proof.
  intros N E T CN CE OE TE FE EN node_enc edge_enc out target effects
    node_work edge_work out_work target_work effect_work
    node_budget edge_budget out_budget target_budget effect_budget g mg
    node_source edge_source out_source target_source effects_source
    Hnode Hout Htarget Hnode_adapter Hedge_adapter Hout_adapter Htarget_adapter Heffects_adapter.
  apply audit_memory_memo_initial_whole_input_bound; try assumption;
    intro argument; audit_memo_foreign_budget.
Qed.

(** Saved-query adapters refer to the stored callback inputs and preserve its concrete recurrence.
    *)
Theorem audit_snapshot_query_whole_input_bound_adapted :
  audit_snapshot_query_whole_input_bound_adapted_statement.
Proof.
  intros N E T Epoch CN CE SE OE BE EN node_enc edge_enc site_enc cache operand before
    node_work edge_work site_work operand_work before_work
    node_budget edge_budget site_budget operand_budget before_budget scope start fuel
    node_source edge_source site_source operand_source before_source
    Hnode Hedge Hsite Hoperand Hbefore.
  apply audit_snapshot_query_whole_input_bound.
  - intro node; audit_memo_foreign_budget.
  - intro edge; audit_memo_foreign_budget.
  - intro site; audit_memo_foreign_budget.
  - intros node key; exact (proj2 (audit_external_callback_observed (N * option E)%type _ OE
      (fun args => operand (fst args) (snd args)) operand_work operand_source
      (fun args => operand_budget (fst args) (snd args)) Hoperand (node, key))).
  - intros edge index; exact (proj2 (audit_external_callback_observed (E * nat)%type _ BE
      (fun args => before (fst args) (snd args)) before_work before_source
      (fun args => before_budget (fst args) (snd args)) Hbefore (edge, index))).
Qed.

(** Refresh adapters cover epoch comparison and the complete current-snapshot rebuild. *)
Theorem audit_snapshot_refresh_whole_input_bound_adapted :
  audit_snapshot_refresh_whole_input_bound_adapted_statement.
Proof.
  intros N E T Epoch CE CN OE FE TE EN epoch_enc node_enc edge_enc out target effects
    epoch_work node_work edge_work out_work effect_work target_work
    epoch_budget node_budget edge_budget out_budget effect_budget target_budget old current
    epoch_source node_source edge_source out_source effects_source target_source
    Hnode Hout Htarget Hepoch_adapter Hnode_adapter Hedge_adapter Hout_adapter Heffects_adapter
    Htarget_adapter.
  apply audit_snapshot_refresh_whole_input_bound; try assumption;
    intro argument; audit_memo_foreign_budget.
Qed.
