(** * Composed memo source adequacy

    Scope encoding composes with the tree's occurrence-sensitive source bound.
    For example, the all-memory scope pays its own encoding before a completed memo hit.
    Builds on: scope encoder adequacy and memo tree source adequacy. *)

From Stdlib Require Import Lia.
From Galois.Analyses Require Import AnalysesAuditMemoryEncoding
  AnalysesAuditMemoryEncodingAdequacy AnalysesAuditMemoryMemo AnalysesAuditMemoryMemoAdequacy
  AnalysesAuditMemoryMemoComposition AnalysesAuditMemoryRawNext.

(** The scope and memo bounds concern the same actual encoders and captured successor calls. *)
Theorem audit_memory_memo_composed_bound : audit_memory_memo_composed_bound_statement.
Proof.
  intros N E T CN CE SE IE OE BE node_enc edge_enc site_enc table incoming operand before
    q active memo v fuel result final remaining events node_work edge_work site_work
    incoming_work operand_work before_work.
  cbn zeta; intro Htree.
  pose proof (audit_memory_scope_work_bound T SE site_enc site_work q) as Hscope.
  pose proof (audit_memo_tree_source_bound N E _ _ _
    (audit_memory_version_encode node_enc edge_enc)
    (audit_memory_memo_key_encode node_enc edge_enc)
    (fst (audit_memory_scope_encode site_enc q))
    (audit_memory_raw_next edge_enc site_enc table incoming
      operand before q) active memo v fuel result final remaining events
    (audit_memory_version_work node_work edge_work) (audit_memory_memo_key_work node_work edge_work)
    (audit_raw_next_source_work edge_work site_work incoming_work
      operand_work before_work) Htree) as Hmemo.
  lia.
Qed.
