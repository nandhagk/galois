(** * Historical byte preservation for the legacy projection

    The fixed producer establishes checker acceptance before applying the historical byte law.
    For example, a live-on-entry candidate preserves the byte of the same allocation identity.
    Builds on: AnalysesAuditMemoryLegacyBytes and AnalysesMemoryLegacy. *)

From Galois.Analyses Require Import AnalysesAuditMemoryLegacyBytes AnalysesMemoryLegacy.

(** Retained definitions preserve covered bytes under the exact original historical premises. *)
Theorem audit_legacy_projection_historical_bytes :
  audit_legacy_projection_historical_bytes_statement.
Proof.
  intros S O N E T F L m bv EN EE EF ET function effects reads mg loads fuel Hbytes Hgraph.
  apply (no_clobber_unchanged m bv EN EF ET function); [exact Hbytes|].
  apply project_memory_legacy_correct; exact Hgraph.
Qed.
