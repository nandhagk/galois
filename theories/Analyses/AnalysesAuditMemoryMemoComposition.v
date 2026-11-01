(** * Composed memo-walk source cost

    This candidate binds the actual scope, version and raw-successor observers to one memo run.
    For example, a definition version includes its real unary index and scope comparison trace.
    Builds on: the audit memory encoding, raw-next and memo models. *)

From Stdlib Require Import List NArith PArith.
From Galois.Collections Require Import CollectionsMap CollectionsFinSet.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryWalk
  AnalysesAuditMemoryState AnalysesAuditMemoryEncoding AnalysesAuditMemoryRawNext
  AnalysesAuditMemoryMemo.
Import List.ListNotations.

(** For a memo-tree derivation, scope encoding and tree work are bounded by fuel, successor
    occurrences and captured primitive work. *)
Definition audit_memory_memo_composed_bound_statement : Prop :=
  forall N E T CN CE SE IE OE BE
      (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
      (site_enc : T -> positive * list SE) (table : Map.t E (Map.t nat (memory_effect T)))
      (incoming : N -> list E * list IE)
      (operand : N -> option E -> option (memory_version N E) * list OE)
      (before : E -> nat -> option (memory_version N E) * list BE)
      (q : memory_scope T) (active : FinSet.t (memory_version N E))
      (memo : Map.t (positive * memory_version N E) (memo_entry N E)) v fuel result final remaining
      events (node_work : list CN -> nat) (edge_work : list CE -> nat)
      (site_work : list SE -> nat) (incoming_work : list IE -> nat)
      (operand_work : list OE -> nat) (before_work : list BE -> nat),
    let scope := audit_memory_scope_encode site_enc q in
    let version_enc := audit_memory_version_encode node_enc edge_enc in
    let key_enc := audit_memory_memo_key_encode node_enc edge_enc in
    let next := audit_memory_raw_next edge_enc site_enc table incoming operand before q in
    let version_work := audit_memory_version_work node_work edge_work in
    let key_work := audit_memory_memo_key_work node_work edge_work in
    let next_work := audit_raw_next_source_work edge_work site_work incoming_work operand_work
      before_work in
    audit_memo_tree version_enc key_enc (fst scope) next active memo v fuel result final remaining
      events ->
    audit_memory_scope_work site_work (snd scope) +
      audit_memo_source_work version_work key_work next_work events <=
    audit_memory_scope_budget site_enc site_work q + 8 + 8 * BinNat.N.to_nat fuel +
      6 * audit_memo_successor_occurrences events +
      audit_memo_primitive_work version_work key_work next_work events.
