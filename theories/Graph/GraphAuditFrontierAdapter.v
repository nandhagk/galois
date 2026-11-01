(** * Dominance-frontier source adapters

    Frontier work uses source, target and encoder budgets at each actual invocation.
    For example, a missing rank map entry still retains the encoder call that found it.
    Builds on: graph DFS and frontier source models. *)

From Stdlib Require Import List.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditMap CollectionsAuditFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDominators GraphFrontier
  GraphAuditBase GraphAuditDfs GraphAuditFrontier.

(** Each frontier event chooses the budget for its recorded client callback input. *)
Definition audit_frontier_adapter_event_budget {V E B} (encode_budget : V -> nat)
    (target_budget source_budget : E -> nat) (event : audit_frontier_source_event V E B) : nat :=
  match event with
  | FrontierSourceDfs (_, calls) => fold_right (fun call n =>
      match call with
      | AuditGraphEncodeCapture _ _ _ v _ _ => encode_budget v + n
      | AuditGraphTargetCapture _ _ _ e _ _ => target_budget e + n
      end) 0 calls
  | FrontierSourceSource e _ _ => source_budget e
  | FrontierSourceTarget e _ _ => target_budget e
  | FrontierSourceParent (AuditMapGet v _ _ _ _ _)
  | FrontierSourceParent (AuditMapSet v _ _ _ _ _
    _) |
    FrontierSourceParent (AuditMapRemove v _ _ _ _ _) | FrontierSourceRank (AuditMapGet v _ _ _ _
      _) |
    FrontierSourceRank (AuditMapSet v _ _ _ _ _ _) | FrontierSourceRank (AuditMapRemove v _ _ _ _
      _) |
    FrontierSourcePred (AuditMapGet v _ _ _ _ _) | FrontierSourcePred (AuditMapSet v _ _ _ _ _ _) |
    FrontierSourcePred (AuditMapRemove v _ _ _ _ _) | FrontierSourceRows (AuditMapGet v _ _ _ _ _) |
    FrontierSourceRows (AuditMapSet v _ _ _ _ _ _) | FrontierSourceRows (AuditMapRemove v _ _ _ _
      _) |
    FrontierSourceSet (AuditSetAdd v _ _ _ _ _) | FrontierSourceSet (AuditSetMem v _ _ _ _ _) |
    FrontierSourceSet (AuditSetRemove v _ _ _ _ _) => encode_budget v
  | _ => 0
  end.

(** The complete frontier producer applies each source law at the captured call. *)
Definition audit_frontier_source_adapted_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) (t : dom_tree V)
    (cb : audit_frontier_source_callbacks V E B) (weight : B -> nat)
    encode_source target_source source_source encode_budget target_budget source_budget,
    audit_frontier_source_callbacks_erase EV g cb ->
    audit_graph_external_callback_adapter (audit_frontier_source_encode cb) weight encode_source
      encode_budget ->
    audit_graph_external_callback_adapter (audit_frontier_source_target cb) weight target_source
      target_budget ->
    audit_graph_external_callback_adapter (audit_frontier_source_source cb) weight source_source
      source_budget ->
    let '(result, events) := audit_frontier_source_counted cb p t in
    result = dominance_frontier p t /\
    audit_frontier_source_work weight events <= audit_frontier_source_input_budget EV g p t +
      fold_right (fun event n => audit_frontier_adapter_event_budget encode_budget target_budget
        source_budget event + n)
        0 events.
