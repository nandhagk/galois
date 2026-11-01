(** * Persistent union-find contract bundle

    Historical observations and concrete source-frame bounds hold together for the fixed bodies.
    For example, union erasure and independently started history bounds are both available.
    Builds on: CollectionsAuditContracts and historical and counted forest adequacy. *)

From Galois.Collections Require Import CollectionsAuditContracts
  CollectionsAuditHistoricalUFAdequacy CollectionsAuditUnionFindAdequacy.

(** * Combined forest contract *)

(** The bundle combines historical result/counter equalities, erasure conditional on encoder
    agreement, and event-count and source-work upper bounds retaining primitive terms where
    specified. *)
Theorem union_find_cost_contract_holds : union_find_cost_contract.
Proof.
  unfold union_find_cost_contract.
  split; [exact trace_find_result |].
  split; [exact trace_union_result |].
  split; [exact trace_actions_result |].
  split; [exact trace_branch_sum |].
  split; [exact union_source_work |].
  split; [exact audit_uf_find_fuel_erases |].
  split; [exact audit_uf_find_erases |].
  split; [exact audit_uf_union_erases |].
  split; [exact audit_uf_equivb_erases |].
  split; [exact audit_uf_keys_erases |].
  split; [exact audit_uf_history_erases |].
  split; [exact audit_uf_of_unions_erases |].
  split; [exact audit_uf_find_fuel_count |].
  split; [exact audit_uf_union_count |].
  split; [exact audit_uf_equivb_count |].
  split; [exact audit_uf_find_fuel_work_bound |].
  split; [exact audit_uf_union_work_bound |].
  split; [exact audit_uf_equivb_work_bound |].
  split; [exact audit_uf_keys_input_bound |].
  split; [exact audit_uf_history_bound |].
  split; [exact audit_uf_branches_bound | exact audit_uf_of_unions_source_bound].
Qed.
