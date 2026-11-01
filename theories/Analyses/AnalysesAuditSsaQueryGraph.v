(** * Full SSA graph source contract

    Compose original preparation, reduced and T indexes, default dominance and T closures.
    For example, each closure search uses the T index prepared by the same run.
    Builds on: graph audit components and SSA query source components. *)
From Stdlib Require Import List Bool PArith NArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditMap CollectionsAuditFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphDominators GraphSemiDominators
  GraphAuditBase GraphAuditDfs GraphAuditVirtual GraphAuditSemiDominators GraphAuditLengauerTarjan
  GraphAuditDominators GraphAuditFrontier.
From Galois.Analyses Require Import AnalysesSsaLiveQuery AnalysesAuditSsaQuerySource.
Import List.ListNotations.

(** * Full SSA graph source contract *)

(** Original graph callbacks expose only the supplied outgoing, target and encoder operations. *)
Definition audit_sq_graph_prepare_callbacks {N E B} (cb : audit_virtual_base_callbacks N E B)
    : audit_prepare_callback_model N E B :=
  AuditPrepareCallbackModel _ _ _ (audit_virtual_base_out cb) (audit_virtual_base_target cb)
    (audit_virtual_base_encode cb).

(** Original graph DFS calls the same supplied target and encoder operations. *)
Definition audit_sq_graph_dfs_callbacks {N E B} (cb : audit_virtual_base_callbacks N E B)
    : audit_dfs_callback_model N E B :=
  AuditDfsCallbackModel _ _ _ (audit_virtual_base_target cb) (audit_virtual_base_encode cb).

(** Input support includes every original node, entry and listed edge endpoint. *)
Definition audit_sq_graph_input_scale {N E} (EN : encoding N) (g : Graph.t N E) : nat :=
  let edges := flat_map (Graph.out g) (Graph.nodes g) in
  let nodes := Graph.nodes g ++ Graph.entries g ++ map (Graph.target g) edges ++
    map (Graph.source g) edges in
  let width := fold_right Nat.max 0 (map (fun n => Pos.size_nat (encode EN n)) nodes) in
  S (length nodes + length edges + width + audit_prepare_source_budget EN g +
    audit_dfs_source_budget EN g (prepare EN g) (Graph.entries g)).

(** The graph-preparation bound is determined before any callback execution. *)
Definition audit_sq_graph_input_budget {N E} (EN : encoding N) (g : Graph.t N E) : nat :=
  (N.to_nat 1048576%N) * Nat.pow (audit_sq_graph_input_scale EN g) 256.

(** Virtual callbacks expose only actual original graph callback inputs. *)
Definition audit_sq_graph_virtual_call_budget {N E B} (encode_budget out_budget : N -> nat)
    (target_budget source_budget : E -> nat) (event : audit_virtual_full_call N E B) : nat :=
  match event with
  | VirtualFullOut n _ _ => out_budget n
  | VirtualFullTarget e _ _ => target_budget e
  | VirtualFullSource e _ _ => source_budget e
  | VirtualFullEncode n _ _ => encode_budget n
  | VirtualFullEntry (VirtualEntriesSet (AuditSetAdd n _ _ _ _ _)) |
    VirtualFullEntry (VirtualEntriesSet (AuditSetMem n _ _ _ _ _)) |
    VirtualFullEntry (VirtualEntriesSet (AuditSetRemove n _ _ _ _ _)) => encode_budget n
  | _ => 0
  end.

(** Erasure prices only the actual client-vertex encoder input. *)
Definition audit_sq_graph_erase_budget {N B} (encode_budget : N -> nat)
    (event : audit_erase_nested_event N B) : nat :=
  match event with
  | EraseNestedSet (AuditMapGet n _ _ _ _ _) | EraseNestedSet (AuditMapSet n _ _ _ _ _ _) |
    EraseNestedSet (AuditMapRemove n _ _ _ _ _) => encode_budget n
  | _ => 0
  end.

(** Forest callback bodies price their captured original node encoder input. *)
Definition audit_sq_graph_dom_body_budget {N B} (encode_budget : N -> nat)
    (event : audit_dom_source_body N B) : nat :=
  match event with
  | DomSourceBodyMap (AuditMapGet n _ _ _ _ _) | DomSourceBodyMap (AuditMapSet n _ _ _ _ _ _) |
    DomSourceBodyMap (AuditMapRemove n _ _ _ _ _) | DomSourceBodyEncode n _ _ => encode_budget n
  | DomSourceBodyTarget _ => 0
  end.

(** Forest-search events retain actual client callback inputs. *)
Definition audit_sq_graph_dom_budget {N E B} (encode_budget : N -> nat) (target_budget : E -> nat)
    (event : audit_dom_source_event N E B) : nat :=
  match event with
  | DomSourceInitialDfs (_, calls) =>
    fold_right (fun call total => match call with
      | AuditGraphEncodeCapture _ _ _ n _ _ => encode_budget n + total
      | AuditGraphTargetCapture _ _ _ e _ _ => target_budget e + total
      end) 0 calls
  | DomSourceChild (AuditMapGet n _ _ _ _ _) | DomSourceChild (AuditMapSet n _ _ _ _ _ _) |
    DomSourceChild (AuditMapRemove n _ _ _ _ _) | DomSourceParent (AuditMapGet n _ _ _ _ _) |
    DomSourceParent (AuditMapSet n _ _ _ _ _ _) | DomSourceParent (AuditMapRemove n _ _ _ _ _) =>
    encode_budget n
  | DomSourcePrepare call =>
    audit_prepare_source_body_work (audit_sq_graph_dom_body_budget encode_budget) [call]
  | DomSourceDfs call =>
    audit_dfs_source_body_work (audit_sq_graph_dom_body_budget encode_budget) [call]
  | _ => 0
  end.

(** Under callback laws, one graph pipeline returns the prepared index within both work bounds. *)
Definition audit_sq_graph_full_source_statement : Prop :=
  forall N E B (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (cb : audit_virtual_base_callbacks N E B) (source : E -> N * list B) (weight : B -> nat)
    encode_source out_source target_source source_source encode_budget out_budget target_budget
    source_budget,
    audit_virtual_base_callbacks_erase EN g cb ->
    (forall edge, fst (source edge) = Graph.source g edge) ->
    audit_graph_external_callback_adapter (audit_virtual_base_encode cb) weight encode_source
      encode_budget ->
    audit_graph_external_callback_adapter (audit_virtual_base_out cb) weight out_source
      out_budget ->
    audit_graph_external_callback_adapter (audit_virtual_base_target cb) weight target_source
      target_budget ->
    audit_graph_external_callback_adapter source weight source_source source_budget ->
    let '(p, prep_events) := audit_prepare_source_counted EN g
      (audit_sq_graph_prepare_callbacks cb) in
    let '(search, dfs_events) := audit_dfs_source_counted p (audit_sq_graph_dfs_callbacks cb)
      FinSet.empty (Graph.entries g) in
    let '(rm, reduced_events) := audit_sq_reduced_source_rows p (audit_virtual_base_encode cb)
      (audit_virtual_base_target cb) source search (rev_append (postorder search) []) in
    let '(tg, (rows, t_events)) := audit_sq_t_source_counted p (audit_virtual_base_encode cb)
      (audit_virtual_base_target cb) source search rm (preorder search) in
    let '(tp, tp_events) := audit_prepare_source_counted EN tg
      (audit_sq_t_internal_prepare_callbacks (audit_virtual_base_encode cb) rows) in
    exists vp virtual_search virtual_prep_events virtual_dfs_events semi_state semi_events
      virtual_parents lt_events parents erase_events dom_receipt tree,
      audit_virtual_source_search EN g cb = (vp, (virtual_search, (virtual_prep_events,
        virtual_dfs_events))) /\
      audit_semi_producer_nested_run (audit_virtual_full_encode cb)
        (audit_virtual_full_source source) vp virtual_search semi_state semi_events /\
      audit_lt_nested_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
        virtual_search (SemiState.result semi_state) virtual_parents lt_events /\
      audit_erase_virtual_nested (audit_virtual_base_encode cb) virtual_parents = (parents,
        erase_events) /\
      dom_receipt = audit_dom_search_source_counted p parents (audit_sq_graph_dfs_callbacks cb) /\
      tree = DomTree parents (pre_num (audit_dom_source_result dom_receipt))
        (post_num (audit_dom_source_result dom_receipt)) /\
      let '(closure, closure_events) := audit_sq_closure_source_rows tp
        (audit_virtual_base_encode cb) (preorder search) in
      SsaQueryGraph g search tree rm closure = prepare_ssa_query_graph EN EE g /\
      let work := 64 + audit_graph_reverse_fast_work (length (postorder search)) +
        audit_prepare_source_work weight prep_events + audit_dfs_source_work weight dfs_events +
        audit_sq_reduced_source_work weight reduced_events + audit_sq_t_source_work weight
          t_events +
        audit_prepare_source_work (audit_sq_t_internal_work weight) tp_events +
        audit_prepare_source_work
          (fun event => audit_virtual_full_internal_event_work event +
            audit_virtual_full_body_event_work weight event)
          virtual_prep_events +
        audit_dfs_source_work
          (fun event => audit_virtual_full_internal_event_work event +
            audit_virtual_full_body_event_work weight event)
          virtual_dfs_events + audit_virtual_semi_stage_work weight semi_events +
        audit_virtual_lt_stage_work weight lt_events + audit_erase_nested_work weight erase_events +
        audit_dom_source_work weight (audit_dom_source_events dom_receipt) +
        audit_sq_closure_source_work weight closure_events in
      let external := audit_prepare_source_body_work weight prep_events +
        audit_dfs_source_body_work weight dfs_events +
        audit_sq_reduced_source_external weight reduced_events +
        audit_sq_t_source_external weight t_events +
        audit_prepare_source_body_work (audit_sq_t_internal_external weight) tp_events +
        audit_prepare_source_body_work (audit_virtual_full_body_event_work weight)
          virtual_prep_events +
        audit_dfs_source_body_work (audit_virtual_full_body_event_work weight) virtual_dfs_events +
        audit_virtual_semi_external_work weight semi_events +
        audit_virtual_lt_external_work weight lt_events +
        audit_erase_nested_body_work weight erase_events +
        audit_dom_source_external_work weight (audit_dom_source_events dom_receipt) +
        audit_sq_closure_source_external weight closure_events in
      let virtual_budget := audit_sq_graph_virtual_call_budget encode_budget out_budget
        target_budget source_budget in
      let adapted :=
        fold_right (fun event n => audit_prepare_source_event_budget encode_budget out_budget
          target_budget event + n) 0 prep_events +
        fold_right (fun item n => fold_right (fun call k =>
          match call with
          | AuditGraphEncodeCapture _ _ _ v _ _ => encode_budget v + k
          | AuditGraphTargetCapture _ _ _ e _ _ => target_budget e + k
          end) 0 (snd item) + n) 0
          dfs_events +
        fold_right (fun event n => audit_sq_reduced_source_event_budget encode_budget target_budget
          source_budget event + n) 0 reduced_events +
        fold_right (fun event n => audit_sq_t_source_event_budget encode_budget target_budget
          source_budget event + n) 0 t_events +
        audit_prepare_source_body_work (audit_sq_t_internal_budget encode_budget) tp_events +
        audit_prepare_source_body_work virtual_budget virtual_prep_events +
        audit_dfs_source_body_work virtual_budget virtual_dfs_events +
        audit_semi_producer_nested_body_work virtual_budget semi_events +
        audit_lt_nested_body_work virtual_budget lt_events +
        fold_right (fun event n => audit_sq_graph_erase_budget encode_budget event + n) 0
          erase_events +
        fold_right (fun event n => audit_sq_graph_dom_budget encode_budget target_budget event + n)
          0 (audit_dom_source_events dom_receipt) +
        fold_right (fun event n => audit_sq_closure_source_event_budget encode_budget event + n) 0
          closure_events in
      work <= audit_sq_graph_input_budget EN g + external /\
      work <= audit_sq_graph_input_budget EN g + adapted.

(** The full graph contract includes its actual source phases and adapted callback bounds. *)
Definition audit_sq_graph_full_source_contract_statement : Prop :=
  audit_sq_graph_full_source_statement /\ audit_sq_reduced_source_contract_statement /\
  audit_sq_t_source_contract_statement /\ audit_sq_closure_source_contract_statement.
