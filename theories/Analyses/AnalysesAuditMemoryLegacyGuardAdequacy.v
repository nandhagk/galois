(** * Adequacy of the legacy guard observer

    The recorded guard preserves the original decisions and charges every outer frame.
    For example, a failed equality still records both set probes.
    Builds on: AnalysesAuditMemoryLegacyGuard and collection adequacy. *)

From Stdlib Require Import List Lia.
From Galois.Collections Require Import CollectionsAuditFinSet CollectionsAuditPrimitive
  CollectionsAuditFinSetAdequacy
  CollectionsAuditPrimitiveAdequacy.
From Galois.Analyses Require Import AnalysesAuditMemoryLegacyGuard.

(** * Guard erasure and work *)

(** Matching callbacks recover the source guard's Boolean result. *)
Theorem audit_legacy_guard_erases : audit_legacy_guard_erases_statement.
Proof.
  intros N E CN CE SE EN EE g node_enc edge_enc source reached listed edge node
    Hnode Hedge Hsource.
  unfold audit_legacy_guard.
  pose proof (audit_finset_mem_erases N CN node_enc EN (fst (source edge)) reached
    (Hnode (fst (source edge)))) as Hreached.
  pose proof (audit_finset_mem_erases E CE edge_enc EE edge listed (Hedge edge)) as Hlisted.
  pose proof (audit_positive_eqb_erases (fst (node_enc (fst (source edge))))
    (fst (node_enc node))) as Hequal.
  destruct (source edge) as [src se] eqn:Hsrc; cbn in *.
  destruct (node_enc src) as [src_code src_body] eqn:Hsrc_code; cbn in *.
  destruct (node_enc node) as [node_code node_body] eqn:Hnode_code; cbn in *.
  destruct (audit_positive_eqb src_code node_code) as [same eq_body]; cbn in *.
  destruct (audit_finset_mem node_enc src reached) as [seen seen_body]; cbn in *.
  destruct (audit_finset_mem edge_enc edge listed) as [present present_body]; cbn in *.
  specialize (Hnode src) as Hsrc_match.
  specialize (Hnode node) as Hnode_match.
  rewrite Hsrc_code in Hsrc_match; rewrite Hnode_code in Hnode_match.
  cbn in Hsrc_match, Hnode_match.
  specialize (Hsource edge); rewrite Hsrc in Hsource; cbn in Hsource.
  rewrite Hequal, Hreached, Hlisted, Hsrc_match, Hnode_match, Hsource.
  reflexivity.
Qed.

(** Every guard evaluation emits seven outer frames. *)
Theorem audit_legacy_guard_count : audit_legacy_guard_count_statement.
Proof.
  intros N E CN CE SE node_enc edge_enc source reached listed edge node.
  unfold audit_legacy_guard.
  destruct (source edge) as [src se].
  destruct (node_enc src) as [src_code src_body].
  destruct (node_enc node) as [node_code node_body].
  destruct (audit_positive_eqb src_code node_code) as [same eq_body].
  destruct (audit_finset_mem node_enc src reached) as [seen seen_body].
  destruct (audit_finset_mem edge_enc edge listed) as [present present_body].
  reflexivity.
Qed.

(** The fixed outer charge is fourteen in addition to the captured primitive work. *)
Theorem audit_legacy_guard_source_bound : audit_legacy_guard_source_bound_statement.
Proof.
  intros N E CN CE SE node_enc edge_enc source reached listed edge node
    node_work edge_work source_work.
  unfold audit_legacy_guard_source_work.
  rewrite (audit_legacy_guard_count N E CN CE SE node_enc edge_enc source reached listed edge node).
  lia.
Qed.
