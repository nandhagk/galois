(** * Proof-carrying memory phi pruning

    The public operations package the fixed pruning graph with its library well-formedness proof.
    For example, the graph-only operation projects the same representative-bearing result.
    Builds on: AnalysesAuditMemoryPhiState, AnalysesAuditMemoryPhiPublic and its adequacy proof. *)

From Galois.Analyses Require Import AnalysesAuditMemoryPhiState AnalysesAuditMemoryPhiPublic
  AnalysesAuditMemoryPhiPublicAdequacy.

Definition memory_prune_with_map : memory_prune_with_map_type :=
  audit_memory_phi_prune_pack audit_memory_phi_prune_wf.

Definition memory_prune : memory_prune_type :=
  audit_memory_phi_graph_pack audit_memory_phi_prune_wf.
