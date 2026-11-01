(** * Default dominator source adapters

    The default LT path charges the callbacks in one virtual-search receipt.
    For example, the forest search reuses the parent map produced by that same run.
    Builds on: virtual, LT and dominator source models. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsAuditMap
  CollectionsAuditFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphDominance
  GraphSemiDominators GraphDominators GraphAuditBase GraphAuditDfs GraphAuditVirtual
    GraphAuditSemiDominators GraphAuditLengauerTarjan GraphAuditDominators.
Import List.ListNotations.

(** Virtual events identify the actual supplied operation and argument. *)
Definition audit_default_virtual_event_budget {V E B} (encode_budget out_budget : V -> nat)
    (target_budget source_budget : E -> nat) (event : audit_virtual_full_call V E B) : nat :=
  match event with
  | VirtualFullOut v _ _ => out_budget v
  | VirtualFullTarget e _ _ => target_budget e
  | VirtualFullSource e _ _ => source_budget e
  | VirtualFullEncode v _ _ => encode_budget v
  | VirtualFullEntry (VirtualEntriesSet (AuditSetAdd v _ _ _ _ _))
  | VirtualFullEntry (VirtualEntriesSet (AuditSetMem v _ _ _ _ _))
  | VirtualFullEntry (VirtualEntriesSet (AuditSetRemove v _ _ _ _ _)) => encode_budget v
  | _ => 0
  end.

Definition audit_default_erase_event_budget {V B} (encode_budget : V -> nat)
    (event : audit_erase_nested_event V B) : nat :=
  match event with
  | EraseNestedSet (AuditMapGet v _ _ _ _ _)
  | EraseNestedSet (AuditMapSet v _ _ _ _ _ _)
  | EraseNestedSet (AuditMapRemove v _ _ _ _ _) => encode_budget v
  | _ => 0
  end.

Definition audit_default_forest_body_budget {V B} (encode_budget : V -> nat)
    (event : audit_dom_source_body V B) : nat :=
  match event with
  | DomSourceBodyMap (AuditMapGet v _ _ _ _ _)
  | DomSourceBodyMap (AuditMapSet v _ _ _ _ _ _)
  | DomSourceBodyMap (AuditMapRemove v _ _ _ _ _)
  | DomSourceBodyEncode v _ _ => encode_budget v
  | DomSourceBodyTarget _ => 0
  end.

Definition audit_default_dom_event_budget {V E B} (encode_budget : V -> nat) (target_budget : E ->
  nat)
    (event : audit_dom_source_event V E B) : nat :=
  match event with
  | DomSourceInitialDfs (_, calls) => fold_right (fun call n =>
      match call with
      | AuditGraphEncodeCapture _ _ _ v _ _ => encode_budget v + n
      | AuditGraphTargetCapture _ _ _ e _ _ => target_budget e + n
      end) 0 calls
  | DomSourceChild (AuditMapGet v _ _ _ _ _)
  | DomSourceChild (AuditMapSet v _ _ _ _ _ _)
  | DomSourceChild (AuditMapRemove v _ _ _ _ _)
  | DomSourceParent (AuditMapGet v _ _ _ _ _)
  | DomSourceParent (AuditMapSet v _ _ _ _ _ _)
  | DomSourceParent (AuditMapRemove v _ _ _ _ _) =>
      encode_budget v
  | DomSourcePrepare call => audit_prepare_source_body_work (audit_default_forest_body_budget
    encode_budget) [call]
  | DomSourceDfs call => audit_dfs_source_body_work (audit_default_forest_body_budget
    encode_budget) [call]
  | _ => 0
  end.

(** The original-input budget covers virtual LT and the finite forest producer. *)
Definition audit_default_dom_input_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) : nat :=
  let edges := flat_map (Graph.out g) (Graph.nodes g) in
  let vertices := Graph.nodes g ++ Graph.entries g ++ map (Graph.source g) edges ++ map
    (Graph.target g) edges in
  let width := fold_right Nat.max 0 (map (fun v => Pos.size_nat (encode EV v)) vertices) in
  let scale := S (4 + length vertices + length edges + width + Pos.to_nat (fuel p) +
    audit_dfs_full_input_width EV g p (Graph.entries g) + audit_dfs_source_budget EV g p
      (Graph.entries g)) in
  (1024 * 1024)%nat * Nat.pow scale 64.

(** The default producer binds one virtual receipt and budgets each actual callback. *)
Definition audit_default_dom_single_adapted_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (cb : audit_virtual_base_callbacks V E B) (source : E -> V * list B) (weight : B -> nat)
    encode_source out_source target_source source_source encode_budget out_budget target_budget
      source_budget,
    audit_virtual_base_callbacks_erase EV g cb -> (forall edge, fst (source edge) = Graph.source g
      edge) ->
    audit_graph_external_callback_adapter (audit_virtual_base_encode cb) weight encode_source
      encode_budget ->
    audit_graph_external_callback_adapter (audit_virtual_base_out cb) weight out_source out_budget
      ->
    audit_graph_external_callback_adapter (audit_virtual_base_target cb) weight target_source
      target_budget ->
    audit_graph_external_callback_adapter source weight source_source source_budget ->
    exists vp search prepare_events dfs_events semi_state semi_events virtual_parents lt_events
      parents erase_events receipt result,
      audit_virtual_source_search EV g cb = (vp, (search, (prepare_events, dfs_events))) /\
      audit_semi_producer_nested_run (audit_virtual_full_encode cb) (audit_virtual_full_source
        source)
        vp search semi_state semi_events /\
      audit_lt_nested_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
        search (SemiState.result semi_state) virtual_parents lt_events /\
      audit_erase_virtual_nested (audit_virtual_base_encode cb) virtual_parents = (parents,
        erase_events) /\
      receipt = audit_dom_search_source_counted p parents
        (AuditDfsCallbackModel V E B (audit_virtual_base_target cb) (audit_virtual_base_encode
          cb)) /\
      result = DomTree parents (pre_num (audit_dom_source_result receipt))
        (post_num (audit_dom_source_result receipt)) /\ result = dominator_tree p /\
      let work := audit_prepare_source_work
        (fun event => audit_virtual_full_internal_event_work event +
          audit_virtual_full_body_event_work weight event)
        prepare_events + audit_dfs_source_work
        (fun event => audit_virtual_full_internal_event_work event +
          audit_virtual_full_body_event_work weight event)
        dfs_events + audit_virtual_semi_stage_work weight semi_events +
          audit_virtual_lt_stage_work weight lt_events +
        audit_erase_nested_work weight erase_events + audit_dom_source_work weight
          (audit_dom_source_events receipt) in
      let virtual_budget := audit_default_virtual_event_budget encode_budget out_budget
        target_budget source_budget in
      let external := audit_prepare_source_body_work virtual_budget prepare_events +
        audit_dfs_source_body_work virtual_budget dfs_events +
        audit_semi_producer_nested_body_work virtual_budget semi_events +
          audit_lt_nested_body_work virtual_budget lt_events +
        fold_right (fun e n => audit_default_erase_event_budget encode_budget e + n) 0
          erase_events +
        fold_right (fun e n => audit_default_dom_event_budget encode_budget target_budget e + n) 0
          (audit_dom_source_events receipt) in
      work <= audit_default_dom_input_budget EV g p + external /\
      work <= audit_virtual_lt_input_budget EV g + audit_dom_search_source_budget EV g p parents
        receipt + external.
