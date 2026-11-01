(** * Virtual-root callback adaptation

    Relate recorded virtual callback bodies to the budgets for their original operands.
    For example, a captured entry-set insertion uses the original vertex encoder budget.
    Builds on: the virtual graph audit and source adapter models. *)

From Stdlib Require Import List Lia.
From Galois.Graph Require Import GraphCore GraphDominance GraphAuditBase GraphAuditDfs
  GraphAuditBaseAdequacy GraphAuditDfsAdequacy
  GraphAuditVirtual GraphAuditVirtualAdapter
  GraphAuditVirtualAdequacy.
From Galois.Collections Require Import CollectionsFinSet CollectionsAuditFinSet.

(** * Per-event adapter bound *)

(** An actual virtual receipt is bounded by the external budget for its captured operand. *)
Lemma audit_virtual_receipt_body_bound V E B (cb : audit_virtual_base_callbacks V E B)
    (weight : B -> nat) encode_source out_source target_source
    encode_budget out_budget target_budget event :
  audit_graph_external_callback_adapter (audit_virtual_base_encode cb) weight encode_source
    encode_budget ->
  audit_graph_external_callback_adapter (audit_virtual_base_out cb) weight out_source out_budget ->
  audit_graph_external_callback_adapter (audit_virtual_base_target cb) weight target_source
    target_budget ->
  audit_virtual_body_receipt V E B cb event ->
  audit_virtual_full_body_event_work weight event <=
    audit_virtual_adapter_call_budget encode_budget out_budget target_budget event.
Proof.
  intros Hencode Hout Htarget Hreceipt.
  destruct event as [site|v edges body|e target body|e source body|v code body|inner|size];
    cbn [audit_virtual_body_receipt audit_virtual_full_body_event_work
      audit_virtual_adapter_call_budget] in *; try lia; try contradiction.
  - exact (proj2 (audit_graph_external_callback_source _ _ _ _ Hout v edges body Hreceipt)).
  - exact (proj2 (audit_graph_external_callback_source _ _ _ _ Htarget e target body Hreceipt)).
  - exact (proj2 (audit_graph_external_callback_source _ _ _ _ Hencode v code body Hreceipt)).
  - destruct inner as [site|item]; cbn [audit_virtual_body_receipt
      audit_virtual_entries_full_body_event_work audit_virtual_adapter_call_budget] in *;
      [lia|].
    destruct item as [v code before after body trace|v code before found body trace|
      v code before after body trace|rest input];
      cbn [audit_virtual_body_receipt audit_virtual_entries_full_body_event_work
        audit_virtual_adapter_call_budget] in *; try lia;
      exact (proj2 (audit_graph_external_callback_source _ _ _ _ Hencode v code body Hreceipt)).
Qed.

(** A sequence of same-call receipts bounds the sum of its original callback bodies. *)
Lemma audit_virtual_receipts_body_bound V E B (cb : audit_virtual_base_callbacks V E B)
    (weight : B -> nat) encode_source out_source target_source
    encode_budget out_budget target_budget events :
  audit_graph_external_callback_adapter (audit_virtual_base_encode cb) weight encode_source
    encode_budget ->
  audit_graph_external_callback_adapter (audit_virtual_base_out cb) weight out_source out_budget ->
  audit_graph_external_callback_adapter (audit_virtual_base_target cb) weight target_source
    target_budget ->
  Forall (audit_virtual_body_receipt V E B cb) events ->
  fold_right (fun item n => audit_virtual_full_body_event_work weight item + n) 0 events <=
    fold_right (fun item n =>
      audit_virtual_adapter_call_budget encode_budget out_budget target_budget item + n) 0 events.
Proof.
  intros Hencode Hout Htarget Hreceipts.
  induction Hreceipts as [|event rest Hreceipt Htail IH]; cbn [List.fold_right].
  - lia.
  - pose proof (audit_virtual_receipt_body_bound V E B cb weight encode_source out_source
      target_source encode_budget out_budget target_budget event Hencode Hout Htarget Hreceipt).
    lia.
Qed.

(** Preparation source receipts bound each attached original callback body. *)
Lemma audit_virtual_prepare_bodies_bound V E B (g : GraphCore.Graph.t V E)
    (cb : audit_virtual_base_callbacks V E B) (weight : B -> nat)
    encode_source out_source target_source encode_budget out_budget target_budget events :
  audit_graph_external_callback_adapter (audit_virtual_base_encode cb) weight encode_source
    encode_budget ->
  audit_graph_external_callback_adapter (audit_virtual_base_out cb) weight out_source out_budget ->
  audit_graph_external_callback_adapter (audit_virtual_base_target cb) weight target_source
    target_budget ->
  Forall (audit_source_receipt (audit_virtual_full_prepare_callbacks g cb)) events ->
  audit_prepare_source_body_work (audit_virtual_full_body_event_work weight) events <=
    audit_prepare_source_body_work
      (audit_virtual_adapter_call_budget encode_budget out_budget target_budget) events.
Proof.
  intros Hencode Hout Htarget Hreceipts.
  induction Hreceipts as [|event rest Hreceipt Htail IH].
  - reflexivity.
  - pose proof (audit_virtual_prepare_event_receipts V E B g cb event Hreceipt) as Hbody.
    pose proof (audit_virtual_receipts_body_bound V E B cb weight encode_source out_source
      target_source encode_budget out_budget target_budget _ Hencode Hout Htarget Hbody) as Hbound.
    change (audit_prepare_source_body_event_work (audit_virtual_full_body_event_work weight) event +
      audit_prepare_source_body_work (audit_virtual_full_body_event_work weight) rest <=
      audit_prepare_source_body_event_work
        (audit_virtual_adapter_call_budget encode_budget out_budget target_budget) event +
      audit_prepare_source_body_work
        (audit_virtual_adapter_call_budget encode_budget out_budget target_budget) rest).
    destruct event as [site|v outgoing body|edge target body|item|amount|nodes edges fuel];
      cbn [audit_virtual_prepare_body audit_prepare_source_body_event_work] in Hbound |- *;
      try lia.
    destruct item; cbn [audit_virtual_prepare_body audit_prepare_source_body_event_work] in *; lia.
Qed.

(** DFS capture receipts bound each attached original callback body. *)
Lemma audit_virtual_dfs_bodies_bound V E B (cb : audit_virtual_base_callbacks V E B)
    (weight : B -> nat) encode_source out_source target_source
    encode_budget out_budget target_budget events :
  audit_graph_external_callback_adapter (audit_virtual_base_encode cb) weight encode_source
    encode_budget ->
  audit_graph_external_callback_adapter (audit_virtual_base_out cb) weight out_source out_budget ->
  audit_graph_external_callback_adapter (audit_virtual_base_target cb) weight target_source
    target_budget ->
  Forall (audit_dfs_event_receipts (audit_virtual_full_dfs_callbacks cb)) events ->
  audit_dfs_source_body_work (audit_virtual_full_body_event_work weight) events <=
    audit_dfs_source_body_work
      (audit_virtual_adapter_call_budget encode_budget out_budget target_budget) events.
Proof.
  intros Hencode Hout Htarget Hreceipts.
  induction Hreceipts as [|[event captures] rest Hcapture Htail IH].
  - reflexivity.
  - unfold audit_dfs_event_receipts in Hcapture; cbn in Hcapture.
    change (fold_right (fun capture n => audit_graph_capture_work
      (audit_virtual_full_body_event_work weight) capture + n) 0 captures +
      audit_dfs_source_body_work (audit_virtual_full_body_event_work weight) rest <=
      fold_right (fun capture n => audit_graph_capture_work
        (audit_virtual_adapter_call_budget encode_budget out_budget target_budget) capture + n)
        0 captures + audit_dfs_source_body_work
          (audit_virtual_adapter_call_budget encode_budget out_budget target_budget) rest).
    assert (Hbound : fold_right (fun capture n => audit_graph_capture_work
      (audit_virtual_full_body_event_work weight) capture + n) 0 captures <=
      fold_right (fun capture n => audit_graph_capture_work
        (audit_virtual_adapter_call_budget encode_budget out_budget target_budget) capture + n)
        0 captures).
    { induction Hcapture as [|capture captures Hreceipt Hcapture_tail IHcapture];
        cbn [List.fold_right].
      - lia.
      - pose proof (audit_virtual_dfs_capture_receipts V E B cb capture Hreceipt) as Hbody.
        pose proof (audit_virtual_receipts_body_bound V E B cb weight encode_source out_source
          target_source encode_budget out_budget target_budget _ Hencode Hout Htarget Hbody)
          as Hbody_bound.
        destruct capture; cbn [audit_graph_capture_work] in *; lia. }
    lia.
Qed.

(** The source-search theorem and same-call receipts imply its adapted external-cost form. *)
Lemma audit_virtual_source_adapter_from_source :
  audit_virtual_source_search_statement -> audit_virtual_source_search_adapted_statement.
Proof.
  intros Hsource V E B EV g p cb weight encode_source out_source target_source
    encode_budget out_budget target_budget Hcallbacks Hencode Hout Htarget.
  pose proof (audit_virtual_full_callbacks_correct V E B EV g cb Hcallbacks) as [Hprep Hdfs].
  pose proof (Hsource V E B EV g p cb weight Hcallbacks) as Hrun.
  pose proof (audit_prepare_source_with_receipts _ _ _ (virtual_encoding EV) (virtual_graph EV g)
    (audit_virtual_full_prepare_callbacks g cb) (audit_virtual_full_body_event_work weight) Hprep)
    as Hprep_run.
  unfold audit_virtual_source_search in Hrun.
  destruct (audit_prepare_source_counted (virtual_encoding EV) (virtual_graph EV g)
    (audit_virtual_full_prepare_callbacks g cb)) as [vp prepare_events] eqn:Hprepare.
  destruct Hprep_run as [_ [_ [_ Hprep_receipts]]].
  pose proof (audit_dfs_source_receipts vp (audit_virtual_full_dfs_callbacks cb)
    FinSet.empty (inr tt :: nil)) as Hdfs_receipts.
  destruct (audit_dfs_source_counted vp (audit_virtual_full_dfs_callbacks cb)
    FinSet.empty (inr tt :: nil)) as [result dfs_events] eqn:Hdfs_run.
  cbv beta iota zeta in Hrun, Hdfs_receipts |- *.
  destruct Hrun as [Hvp [Hresult Hwork]].
  pose proof (audit_virtual_prepare_bodies_bound V E B g cb weight encode_source out_source
    target_source encode_budget out_budget target_budget prepare_events Hencode Hout Htarget
    Hprep_receipts) as Hprepare_bound.
  pose proof (audit_virtual_dfs_bodies_bound V E B cb weight encode_source out_source target_source
    encode_budget out_budget target_budget dfs_events Hencode Hout Htarget Hdfs_receipts)
    as Hdfs_bound.
  unfold audit_virtual_source_search; rewrite Hprepare, Hdfs_run; cbv beta iota zeta.
  split; [exact Hvp|].
  split; [exact Hresult|].
  lia.
Qed.

(** Source search satisfies the external budgets for the callbacks actually invoked. *)
Theorem audit_virtual_source_search_adapted_holds :
  audit_virtual_source_search_adapted_statement.
Proof.
  apply audit_virtual_source_adapter_from_source.
  exact audit_virtual_source_search_holds.
Qed.
