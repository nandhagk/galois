(** * Phi preparation phase adequacy

    Dependency preparation retains the original index and its five ordered phase receipts.
    For example, the SCC phase receives the graph produced by the same input rows.
    Builds on: AnalysesAuditMemoryPhiPrepare and AnalysesAuditMemoryPhiState. *)

From Galois.Analyses Require Import AnalysesAuditMemoryPhiPrepare AnalysesAuditMemoryPhiState.

(** The counted preparation returns the exact plain dependency index. *)
Theorem audit_phi_prepare_dependencies_erases : audit_phi_prepare_dependencies_erases_statement.
Proof.
  intros N E T EN EE g effects mg.
  reflexivity.
Qed.

(** Dependency preparation records exactly the five fixed phases. *)
Theorem audit_phi_prepare_phase_count : audit_phi_prepare_phase_count_statement.
Proof.
  intros N E T EN EE g effects mg.
  reflexivity.
Qed.
