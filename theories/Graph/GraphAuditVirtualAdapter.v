(** * Virtual graph source adapters

    The virtual search prices each captured original callback at its actual input.
    For example, a virtual entry charges the encoder of the original entry vertex.
    Builds on: the virtual graph, preparation and DFS source models. *)

From Stdlib Require Import List.
From Galois.Collections Require Import CollectionsEncoding CollectionsAuditFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDominance GraphSemiDominators
  GraphAuditBase GraphAuditDfs GraphAuditVirtual.

(** Each virtual wrapper resolves to the supplied original callback it executes. *)
Definition audit_virtual_adapter_call_budget {V E B} (encode_budget out_budget : V -> nat)
    (target_budget : E -> nat) (event : audit_virtual_full_call V E B) : nat :=
  match event with
  | VirtualFullOut v _ _ => out_budget v
  | VirtualFullTarget e _ _ => target_budget e
  | VirtualFullEncode v _ _ => encode_budget v
  | VirtualFullEntry (VirtualEntriesSet (AuditSetAdd v _ _ _ _ _))
  | VirtualFullEntry (VirtualEntriesSet (AuditSetMem v _ _ _ _ _))
  | VirtualFullEntry (VirtualEntriesSet (AuditSetRemove v _ _ _ _ _)) => encode_budget v
  | _ => 0
  end.

(** One captured virtual search has the full original-input and per-call source bound. *)
Definition audit_virtual_source_search_adapted_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (cb : audit_virtual_base_callbacks V E B) (weight : B -> nat)
    encode_source out_source target_source encode_budget out_budget target_budget,
    audit_virtual_base_callbacks_erase EV g cb ->
    audit_graph_external_callback_adapter (audit_virtual_base_encode cb) weight encode_source
      encode_budget ->
    audit_graph_external_callback_adapter (audit_virtual_base_out cb) weight out_source out_budget
      ->
    audit_graph_external_callback_adapter (audit_virtual_base_target cb) weight target_source
      target_budget ->
    let '(vp, (result, (prepare_events, dfs_events))) := audit_virtual_source_search EV g cb in
    let budget := audit_virtual_adapter_call_budget encode_budget out_budget target_budget in
    vp = virtual_prepared p /\ result = virtual_dfs p /\
    audit_prepare_source_work
      (fun item => audit_virtual_full_internal_event_work item +
        audit_virtual_full_body_event_work weight item)
      prepare_events +
    audit_dfs_source_work
      (fun item => audit_virtual_full_internal_event_work item +
        audit_virtual_full_body_event_work weight item)
      dfs_events <= audit_virtual_source_search_budget EV g +
    audit_prepare_source_body_work budget prepare_events + audit_dfs_source_body_work budget
      dfs_events.
