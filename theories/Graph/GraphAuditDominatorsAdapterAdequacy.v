(** * Default dominator callback adaptation

    Bounds virtual callback bodies using the budgets of their actual operands.
    For example, a source callback receipt carries its original edge and body.
    Builds on: the virtual adapter and dominator adapter source models. *)

From Stdlib Require Import List PArith Arith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditCost CollectionsAuditTrie CollectionsAuditMap CollectionsAuditPrimitive
  CollectionsAuditFinSet CollectionsAuditElements CollectionsAuditElementsAdequacy.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphDominance
  GraphSemiDominators GraphLengauerTarjan GraphDominators GraphAuditDfs GraphAuditBase
  GraphAuditVirtual GraphAuditVirtualAdapter GraphAuditVirtualAdequacy
  GraphAuditVirtualAdapterAdequacy GraphAuditSemiDominators GraphAuditLengauerTarjan
  GraphAuditDominators GraphAuditDominatorsAdapter GraphAuditDfsAdequacy
  GraphAuditBaseAdequacy GraphAuditDominatorsAdequacy.
Import List.ListNotations.

(** A virtual receipt includes the source callback used by the dominator producer. *)
Definition audit_default_virtual_receipt V E B (cb : audit_virtual_base_callbacks V E B)
    (source : E -> V * list B) (event : audit_virtual_full_call V E B) : Prop :=
  match event with
  | VirtualFullSource edge vertex body => source edge = (vertex, body)
  | _ => audit_virtual_body_receipt V E B cb event
  end.

(** The dominator budget extends the search adapter budget with source calls. *)
Lemma audit_default_virtual_budget_extends V E B encode_budget out_budget target_budget
    source_budget (event : audit_virtual_full_call V E B) :
  audit_virtual_adapter_call_budget encode_budget out_budget target_budget event <=
    audit_default_virtual_event_budget encode_budget out_budget target_budget source_budget event.
Proof.
  destruct event as [site|v edges body|e target body|e source body|v code body|entry|size];
    cbn [audit_virtual_adapter_call_budget audit_default_virtual_event_budget]; try lia.
Qed.

(** An actual callback receipt is priced at the budget for that callback's operand. *)
Lemma audit_default_virtual_receipt_bound V E B (cb : audit_virtual_base_callbacks V E B)
    (source : E -> V * list B) (weight : B -> nat)
    encode_source out_source target_source source_source
    encode_budget out_budget target_budget source_budget event :
  audit_graph_external_callback_adapter (audit_virtual_base_encode cb) weight encode_source
    encode_budget ->
  audit_graph_external_callback_adapter (audit_virtual_base_out cb) weight out_source out_budget ->
  audit_graph_external_callback_adapter (audit_virtual_base_target cb) weight target_source
    target_budget ->
  audit_graph_external_callback_adapter source weight source_source source_budget ->
  audit_default_virtual_receipt V E B cb source event ->
  audit_virtual_full_body_event_work weight event <=
    audit_default_virtual_event_budget encode_budget out_budget target_budget source_budget event.
Proof.
  intros Hencode Hout Htarget Hsource Hreceipt.
  destruct event as [site|v edges body|e target body|e vertex body|v code body|entry|size];
    cbn [audit_default_virtual_receipt] in Hreceipt.
  all: try (eapply Nat.le_trans;
    [eapply audit_virtual_receipt_body_bound; eassumption|apply
      audit_default_virtual_budget_extends]).
  cbn [audit_virtual_full_body_event_work audit_default_virtual_event_budget].
  exact (proj2 (audit_graph_external_callback_source _ _ _ _ Hsource e vertex body Hreceipt)).
Qed.

(** A finite receipt list retains the same per-call external budget. *)
Lemma audit_default_virtual_receipts_bound V E B (cb : audit_virtual_base_callbacks V E B)
    (source : E -> V * list B) (weight : B -> nat)
    encode_source out_source target_source source_source
    encode_budget out_budget target_budget source_budget events :
  audit_graph_external_callback_adapter (audit_virtual_base_encode cb) weight encode_source
    encode_budget ->
  audit_graph_external_callback_adapter (audit_virtual_base_out cb) weight out_source out_budget ->
  audit_graph_external_callback_adapter (audit_virtual_base_target cb) weight target_source
    target_budget ->
  audit_graph_external_callback_adapter source weight source_source source_budget ->
  Forall (audit_default_virtual_receipt V E B cb source) events ->
  audit_virtual_full_events_body_work weight events <=
    fold_right (fun event n =>
      audit_default_virtual_event_budget encode_budget out_budget target_budget source_budget
        event +
        n) 0 events.
Proof.
  intros Hencode Hout Htarget Hsource Hreceipts.
  induction Hreceipts as [|event rest Hreceipt Htail IH];
    cbn [audit_virtual_full_events_body_work List.fold_right].
  - lia.
  - pose proof (audit_default_virtual_receipt_bound V E B cb source weight encode_source out_source
      target_source source_source encode_budget out_budget target_budget source_budget event
      Hencode Hout Htarget Hsource Hreceipt).
    unfold audit_virtual_full_events_body_work in IH.
    lia.
Qed.

(** A search receipt remains a dominator receipt when a source callback is also available. *)
Lemma audit_default_virtual_receipt_includes_search V E B
    (cb : audit_virtual_base_callbacks V E B) (source : E -> V * list B) event :
  audit_virtual_body_receipt V E B cb event -> audit_default_virtual_receipt V E B cb source event.
Proof.
  destruct event; cbn [audit_virtual_body_receipt audit_default_virtual_receipt]; tauto.
Qed.

(** Lifted encode and source calls carry receipts for their original callback bodies. *)
Lemma audit_default_virtual_call_receipts V E B (cb : audit_virtual_base_callbacks V E B)
    (source : E -> V * list B) :
  (forall vertex, Forall (audit_default_virtual_receipt V E B cb source)
    (snd (audit_virtual_full_encode cb vertex))) /\
  (forall edge, Forall (audit_default_virtual_receipt V E B cb source)
    (snd (audit_virtual_full_source source edge))).
Proof.
  split.
  - intro vertex.
    pose proof (proj2 (audit_virtual_target_encode_receipts V E B cb) vertex) as Hreceipts.
    eapply Forall_impl; [|exact Hreceipts].
    intros event Hreceipt; now apply audit_default_virtual_receipt_includes_search.
  - intros [edge|vertex]; cbn [audit_virtual_full_source].
    + destruct (source edge) as [result body] eqn:Hsource.
      repeat constructor; exact Hsource.
    + repeat constructor.
Qed.

(** A map receipt records the encoder call attached to its actual key. *)
Definition audit_default_map_receipt K A B (enc : K -> positive * list B)
    (event : audit_map_event K A B) : Prop :=
  match event with
  | AuditMapGet key code _ _ body _
  | AuditMapSet key _ code _ _ body _
  | AuditMapRemove key code _ _ body _ => enc key = (code, body)
  end.

(** Counted map reads and writes retain the encoder receipt at the actual key. *)
Lemma audit_default_map_call_receipts K A B (enc : K -> positive * list B)
    key (input : Map.t K A) value :
  Forall (audit_default_map_receipt K A B enc) (snd (audit_map_get enc key input)) /\
  Forall (audit_default_map_receipt K A B enc) (snd (audit_map_set enc key value input)) /\
  Forall (audit_default_map_receipt K A B enc) (snd (audit_map_remove enc key input)).
Proof.
  unfold audit_map_get, audit_map_set, audit_map_remove.
  destruct (enc key) as [code body] eqn:Henc.
  destruct (audit_map_code_get code input) as [found gets].
  destruct (audit_trie_set code (key, value) input) as [after sets].
  destruct (audit_trie_remove code input) as [removed removes].
  cbn [snd]; repeat split; repeat constructor; exact Henc.
Qed.

(** Each map event carries the original receipts from its lifted encoder call. *)
Definition audit_default_map_virtual_receipt V E B A (cb : audit_virtual_base_callbacks V E B)
    (source : E -> V * list B) (event : audit_map_event (V + unit) A
      (audit_virtual_full_call V E B)) : Prop :=
  match event with
  | AuditMapGet _ _ _ _ body _
  | AuditMapSet _ _ _ _ _ body _
  | AuditMapRemove _ _ _ _ body _ => Forall (audit_default_virtual_receipt V E B cb source) body
  end.

(** A lifted encoder receipt implies receipts for every original call in its body. *)
Lemma audit_default_map_receipt_lift V E B A (cb : audit_virtual_base_callbacks V E B)
    (source : E -> V * list B) event :
  audit_default_map_receipt (V + unit) A (audit_virtual_full_call V E B)
    (audit_virtual_full_encode cb) event ->
  audit_default_map_virtual_receipt V E B A cb source event.
Proof.
  destruct event as [key code input output body trace|key value code input output body trace|
    key code input output body trace]; cbn [audit_default_map_receipt
      audit_default_map_virtual_receipt]; intro Hencode;
    pose proof (proj1 (audit_default_virtual_call_receipts V E B cb source) key) as Hreceipts;
    rewrite Hencode in Hreceipts; exact Hreceipts.
Qed.

(** Actual virtual map calls carry their original callback receipts. *)
Lemma audit_default_virtual_map_call_receipts V E B A (cb : audit_virtual_base_callbacks V E B)
    (source : E -> V * list B) key (input : Map.t (V + unit) A) value :
  Forall (audit_default_map_virtual_receipt V E B A cb source)
    (snd (audit_map_get (audit_virtual_full_encode cb) key input)) /\
  Forall (audit_default_map_virtual_receipt V E B A cb source)
    (snd (audit_map_set (audit_virtual_full_encode cb) key value input)) /\
  Forall (audit_default_map_virtual_receipt V E B A cb source)
    (snd (audit_map_remove (audit_virtual_full_encode cb) key input)).
Proof.
  pose proof (audit_default_map_call_receipts _ _ _ (audit_virtual_full_encode cb) key input value)
    as [Hget [Hset Hremove]].
  repeat split; eapply Forall_impl; try eassumption;
    intros event Hreceipt; now apply audit_default_map_receipt_lift.
Qed.

(** A nested semidominator map event exposes the lifted encoder's original receipts. *)
Definition audit_default_semi_event_receipt V E B (cb : audit_virtual_base_callbacks V E B)
    (source : E -> V * list B) (event : audit_semi_nested_event (V + unit)
      (audit_virtual_full_call V E B)) : Prop :=
  match event with
  | SemiNestedVertexMap item => audit_default_map_virtual_receipt V E B (V + unit) cb source item
  | SemiNestedRankMap item => audit_default_map_virtual_receipt V E B positive cb source item
  | _ => True
  end.

(** A semidominator rank lookup preserves the actual encoder receipts. *)
Lemma audit_default_semi_rank_receipts V E B (cb : audit_virtual_base_callbacks V E B)
    (source : E -> V * list B) (r : dfs_result (V + unit) (E + V)) vertex :
  Forall (audit_default_semi_event_receipt V E B cb source)
    (snd (audit_semi_nested_rank (audit_virtual_full_encode cb) r vertex)).
Proof.
  unfold audit_semi_nested_rank.
  pose proof (proj1 (audit_default_virtual_map_call_receipts V E B positive cb source vertex
    (pre_num r) 1%positive)) as Hget.
  destruct (audit_map_get (audit_virtual_full_encode cb) vertex (pre_num r)) as [found events].
  cbn [snd] in Hget |- *.
  apply Forall_map; exact Hget.
Qed.

(** A semidominator label lookup retains the encoder receipt for the queried vertex. *)
Lemma audit_default_semi_label_receipts V E B (cb : audit_virtual_base_callbacks V E B)
    (source : E -> V * list B) (state : SemiLinks.t (V + unit)) vertex :
  Forall (audit_default_semi_event_receipt V E B cb source)
    (snd (audit_semi_nested_label (audit_virtual_full_encode cb) state vertex)).
Proof.
  unfold audit_semi_nested_label.
  pose proof (proj1 (audit_default_virtual_map_call_receipts V E B (V + unit) cb source vertex
    (SemiLinks.labels state) vertex)) as Hget.
  destruct (audit_map_get (audit_virtual_full_encode cb) vertex (SemiLinks.labels state))
    as [found events].
  cbn [snd] in Hget |- *; apply Forall_map; exact Hget.
Qed.

(** A score lookup retains both map and rank callback receipts. *)
Lemma audit_default_semi_score_receipts V E B (cb : audit_virtual_base_callbacks V E B)
    (source : E -> V * list B) (r : dfs_result (V + unit) (E + V)) semis vertex :
  Forall (audit_default_semi_event_receipt V E B cb source)
    (snd (audit_semi_nested_score (audit_virtual_full_encode cb) r semis vertex)).
Proof.
  unfold audit_semi_nested_score.
  pose proof (proj1 (audit_default_virtual_map_call_receipts V E B (V + unit) cb source vertex
    semis vertex)) as Hget.
  destruct (audit_map_get (audit_virtual_full_encode cb) vertex semis) as [found events].
  cbn [snd] in Hget.
  pose proof (audit_default_semi_rank_receipts V E B cb source r
    (match found with
      | Some x => x
      | None => vertex
      end)) as Hrank.
  destruct (audit_semi_nested_rank (audit_virtual_full_encode cb) r
    (match found with
      | Some x => x
      | None => vertex
      end)) as [score rank_events].
  cbn [snd] in Hrank |- *.
  apply Forall_app; split; [apply Forall_map; exact Hget|exact Hrank].
Qed.

(** Both shortcut writes retain the encoder receipts used by the actual writes. *)
Lemma audit_default_semi_shortcut_receipts V E B (cb : audit_virtual_base_callbacks V E B)
    (source : E -> V * list B) (state : SemiLinks.t (V + unit)) vertex root best :
  Forall (audit_default_semi_event_receipt V E B cb source)
    (snd (audit_semi_nested_shortcut_set (audit_virtual_full_encode cb) state vertex root best)).
Proof.
  unfold audit_semi_nested_shortcut_set.
  pose proof (proj1 (proj2 (audit_default_virtual_map_call_receipts V E B (V + unit) cb source
    vertex (SemiLinks.shortcut state) root))) as Hfirst.
  pose proof (proj1 (proj2 (audit_default_virtual_map_call_receipts V E B (V + unit) cb source
    vertex (SemiLinks.labels state) best))) as Hsecond.
  destruct (audit_map_set (audit_virtual_full_encode cb) vertex root (SemiLinks.shortcut state))
    as [shortcuts first].
  destruct (audit_map_set (audit_virtual_full_encode cb) vertex best (SemiLinks.labels state))
    as [labels second].
  cbn [snd] in Hfirst, Hsecond |- *.
  apply Forall_app; split; apply Forall_map; assumption.
Qed.

(** Compression receipts follow the actual map reads, recursive call, and shortcut writes. *)
Lemma audit_default_semi_compress_receipts V E B (cb : audit_virtual_base_callbacks V E B)
    (source : E -> V * list B) (r : dfs_result (V + unit) (E + V)) semis state vertex result
    events :
  audit_semi_nested_compress_run (audit_virtual_full_encode cb) r semis state vertex result
    events ->
  Forall (audit_default_semi_event_receipt V E B cb source) events.
Proof.
  intro Hrun.
  assert (Hget : forall key input output trace,
    audit_map_get (audit_virtual_full_encode cb) key input = (output, trace) ->
    Forall (audit_default_semi_event_receipt V E B cb source) (map SemiNestedVertexMap trace)).
  { intros key input output trace Hcall.
    pose proof (proj1 (audit_default_virtual_map_call_receipts V E B (V + unit) cb source key
      input key)) as Hreceipts.
    rewrite Hcall in Hreceipts; cbn [snd] in Hreceipts; apply Forall_map; exact Hreceipts. }
  assert (Hrank : forall v result trace,
    audit_semi_nested_rank (audit_virtual_full_encode cb) r v = (result, trace) ->
    Forall (audit_default_semi_event_receipt V E B cb source) trace).
  { intros v number trace Hcall.
    pose proof (audit_default_semi_rank_receipts V E B cb source r v) as Hreceipts.
    rewrite Hcall in Hreceipts; exact Hreceipts. }
  assert (Hlabel : forall st v result trace,
    audit_semi_nested_label (audit_virtual_full_encode cb) st v = (result, trace) ->
    Forall (audit_default_semi_event_receipt V E B cb source) trace).
  { intros st v label trace Hcall.
    pose proof (audit_default_semi_label_receipts V E B cb source st v) as Hreceipts.
    rewrite Hcall in Hreceipts; exact Hreceipts. }
  assert (Hscore : forall v result trace,
    audit_semi_nested_score (audit_virtual_full_encode cb) r semis v = (result, trace) ->
    Forall (audit_default_semi_event_receipt V E B cb source) trace).
  { intros v score trace Hcall.
    pose proof (audit_default_semi_score_receipts V E B cb source r semis v) as Hreceipts.
    rewrite Hcall in Hreceipts; exact Hreceipts. }
  assert (Hset : forall st v root best result trace,
    audit_semi_nested_shortcut_set (audit_virtual_full_encode cb) st v root best =
      (result, trace) -> Forall (audit_default_semi_event_receipt V E B cb source) trace).
  { intros st v root best after trace Hcall.
    pose proof (audit_default_semi_shortcut_receipts V E B cb source st v root best) as Hreceipts.
    rewrite Hcall in Hreceipts; exact Hreceipts. }
  induction Hrun; repeat rewrite Forall_app; repeat split;
    try solve [eauto using Hget, Hrank, Hlabel, Hscore, Hset];
    repeat constructor.
Qed.

(** A producer event retains its original source or encoder callback receipts. *)
Definition audit_default_producer_event_receipt V E B (cb : audit_virtual_base_callbacks V E B)
    (source : E -> V * list B) (event : audit_semi_producer_nested_event (V + unit) (E + V)
      (audit_virtual_full_call V E B)) : Prop :=
  match event with
  | SemiProducerSource _ _ body => Forall (audit_default_virtual_receipt V E B cb source) body
  | SemiProducerInner inner => audit_default_semi_event_receipt V E B cb source inner
  | SemiProducerTreeMap item => audit_default_map_virtual_receipt V E B (E + V) cb source item
  | SemiProducerPredMap item => audit_default_map_virtual_receipt V E B (list (E + V)) cb source
    item
  | _ => True
  end.

(** Each link write retains the actual original encoder receipt. *)
Lemma audit_default_producer_link_receipts V E B (cb : audit_virtual_base_callbacks V E B)
    (source : E -> V * list B) (state : SemiLinks.t (V + unit)) vertex parent :
  Forall (audit_default_producer_event_receipt V E B cb source)
    (snd (audit_semi_producer_link (E := E + V) (audit_virtual_full_encode cb) state vertex
      parent)).
Proof.
  unfold audit_semi_producer_link.
  pose proof (proj1 (proj2 (audit_default_virtual_map_call_receipts V E B (V + unit) cb source
    vertex (SemiLinks.original state) parent))) as Hfirst.
  pose proof (proj1 (proj2 (audit_default_virtual_map_call_receipts V E B (V + unit) cb source
    vertex (SemiLinks.shortcut state) parent))) as Hsecond.
  pose proof (proj1 (proj2 (audit_default_virtual_map_call_receipts V E B (V + unit) cb source
    vertex (SemiLinks.labels state) vertex))) as Hthird.
  destruct (audit_map_set (audit_virtual_full_encode cb) vertex parent (SemiLinks.original state))
    as [original first].
  destruct (audit_map_set (audit_virtual_full_encode cb) vertex parent (SemiLinks.shortcut state))
    as [shortcut second].
  destruct (audit_map_set (audit_virtual_full_encode cb) vertex vertex (SemiLinks.labels state))
    as [labels third].
  cbn [snd] in Hfirst, Hsecond, Hthird |- *.
  apply Forall_map; repeat rewrite Forall_app; repeat split; assumption.
Qed.

(** A predecessor run preserves receipts for every source, map, and compression callback. *)
Lemma audit_default_producer_pred_receipts V E B (cb : audit_virtual_base_callbacks V E B)
    (source : E -> V * list B) (r : dfs_result (V + unit) (E + V)) semis initial edge result
    events :
  audit_semi_producer_pred_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
    r semis initial edge result events ->
  Forall (audit_default_producer_event_receipt V E B cb source) events.
Proof.
  intro Hrun.
  assert (Hsource : forall e v body, audit_virtual_full_source source e = (v, body) ->
    Forall (audit_default_virtual_receipt V E B cb source) body).
  { intros e v body Hcall.
    pose proof (proj2 (audit_default_virtual_call_receipts V E B cb source) e) as Hreceipts.
    rewrite Hcall in Hreceipts; exact Hreceipts. }
  assert (Hrank_get : forall key input result trace,
    audit_map_get (audit_virtual_full_encode cb) key input = (result, trace) ->
    Forall (audit_default_producer_event_receipt V E B cb source)
      (map (fun item => SemiProducerInner (SemiNestedRankMap item)) trace)).
  { intros key input value trace Hcall.
    pose proof (proj1 (audit_default_virtual_map_call_receipts V E B positive cb source key
      input 1%positive)) as Hreceipts.
    rewrite Hcall in Hreceipts; cbn [snd] in Hreceipts; apply Forall_map; exact Hreceipts. }
  assert (Hvertex_get : forall key input result trace,
    audit_map_get (audit_virtual_full_encode cb) key input = (result, trace) ->
    Forall (audit_default_producer_event_receipt V E B cb source)
      (map (fun item => SemiProducerInner (SemiNestedVertexMap item)) trace)).
  { intros key input value trace Hcall.
    pose proof (proj1 (audit_default_virtual_map_call_receipts V E B (V + unit) cb source key
      input key)) as Hreceipts.
    rewrite Hcall in Hreceipts; cbn [snd] in Hreceipts; apply Forall_map; exact Hreceipts. }
  assert (Hrank : forall v number trace,
    audit_semi_nested_rank (audit_virtual_full_encode cb) r v = (number, trace) ->
    Forall (audit_default_producer_event_receipt V E B cb source) (map SemiProducerInner trace)).
  { intros v number trace Hcall.
    pose proof (audit_default_semi_rank_receipts V E B cb source r v) as Hreceipts.
    rewrite Hcall in Hreceipts; cbn [snd] in Hreceipts; apply Forall_map; exact Hreceipts. }
  assert (Hinner : forall st v after trace,
    audit_semi_nested_compress_run (audit_virtual_full_encode cb) r semis st v after trace ->
    Forall (audit_default_producer_event_receipt V E B cb source) (map SemiProducerInner trace)).
  { intros st v after trace Hcall.
    apply Forall_map; eapply audit_default_semi_compress_receipts; exact Hcall. }
  destruct Hrun; repeat rewrite Forall_app; repeat split;
    try solve [eauto using Hrank_get, Hvertex_get, Hrank, Hinner];
    repeat constructor; eauto using Hsource.
  all: cbn [audit_default_producer_event_receipt]; eauto using Hsource.
Qed.

(** Each predecessor in the finite traversal preserves its own callback receipts. *)
Lemma audit_default_producer_preds_receipts V E B (cb : audit_virtual_base_callbacks V E B)
    (source : E -> V * list B) (r : dfs_result (V + unit) (E + V)) semis edges initial result
    events :
  audit_semi_producer_preds_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
    r semis edges initial result events ->
  Forall (audit_default_producer_event_receipt V E B cb source) events.
Proof.
  intro Hrun; induction Hrun.
  - repeat constructor.
  - constructor; [exact I|].
    apply Forall_app; split; [eapply audit_default_producer_pred_receipts; eassumption|assumption].
Qed.

(** Map reads carry receipts even when the map's value type has no inhabitant. *)
Lemma audit_default_virtual_map_get_receipts V E B A (cb : audit_virtual_base_callbacks V E B)
    (source : E -> V * list B) key (input : Map.t (V + unit) A) :
  Forall (audit_default_map_virtual_receipt V E B A cb source)
    (snd (audit_map_get (audit_virtual_full_encode cb) key input)).
Proof.
  unfold audit_map_get.
  pose proof (proj1 (audit_default_virtual_call_receipts V E B cb source) key) as Hreceipts.
  destruct (audit_virtual_full_encode cb key) as [code body].
  destruct (audit_map_code_get code input) as [found trace].
  cbn [snd] in Hreceipts |- *; repeat constructor; exact Hreceipts.
Qed.

(** Map writes carry receipts from the encoder call attached to their key. *)
Lemma audit_default_virtual_map_set_receipts V E B A (cb : audit_virtual_base_callbacks V E B)
    (source : E -> V * list B) key (input : Map.t (V + unit) A) value :
  Forall (audit_default_map_virtual_receipt V E B A cb source)
    (snd (audit_map_set (audit_virtual_full_encode cb) key value input)).
Proof.
  exact (proj1 (proj2 (audit_default_virtual_map_call_receipts V E B A cb source key input value))).
Qed.

(** Settling one vertex preserves the receipts from its actual source and map operations. *)
Lemma audit_default_producer_settle_receipts V E B (cb : audit_virtual_base_callbacks V E B)
    (source : E -> V * list B) (EV : CollectionsEncoding.encoding (V + unit))
    (g : GraphCore.Graph.t (V + unit) (E + V)) (p : GraphPrepare.prepared EV g)
    (r : dfs_result (V + unit) (E + V)) state vertex result events :
  audit_semi_producer_settle_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
    p r state vertex result events ->
  Forall (audit_default_producer_event_receipt V E B cb source) events.
Proof.
  intro Hrun.
  assert (Htree : forall key input output trace,
    audit_map_get (audit_virtual_full_encode cb) key input = (output, trace) ->
    Forall (audit_default_producer_event_receipt V E B cb source) (map SemiProducerTreeMap trace)).
  { intros key input output trace Hcall.
    pose proof (audit_default_virtual_map_get_receipts V E B (E + V) cb source key input) as Hbody.
    rewrite Hcall in Hbody; cbn [snd] in Hbody; apply Forall_map; exact Hbody. }
  assert (Hpred : forall key input output trace,
    audit_map_get (audit_virtual_full_encode cb) key input = (output, trace) ->
    Forall (audit_default_producer_event_receipt V E B cb source) (map SemiProducerPredMap trace)).
  { intros key input output trace Hcall.
    pose proof (audit_default_virtual_map_get_receipts V E B (list (E + V)) cb source key input)
      as Hbody.
    rewrite Hcall in Hbody; cbn [snd] in Hbody; apply Forall_map; exact Hbody. }
  assert (Hset : forall key value input output trace,
    audit_map_set (audit_virtual_full_encode cb) key value input = (output, trace) ->
    Forall (audit_default_producer_event_receipt V E B cb source)
      (map (fun item => SemiProducerInner (SemiNestedVertexMap item)) trace)).
  { intros key value input output trace Hcall.
    pose proof (audit_default_virtual_map_set_receipts V E B (V + unit) cb source key input value)
      as Hbody.
    rewrite Hcall in Hbody; cbn [snd] in Hbody; apply Forall_map; exact Hbody. }
  assert (Hsource : forall edge parent body,
    audit_virtual_full_source source edge = (parent, body) ->
    Forall (audit_default_virtual_receipt V E B cb source) body).
  { intros edge parent body Hcall.
    pose proof (proj2 (audit_default_virtual_call_receipts V E B cb source) edge) as Hbody.
    rewrite Hcall in Hbody; exact Hbody. }
  assert (Hlink : forall st v parent output trace,
    audit_semi_producer_link (E := E + V) (audit_virtual_full_encode cb) st v parent =
      (output, trace) -> Forall (audit_default_producer_event_receipt V E B cb source) trace).
  { intros st v parent output trace Hcall.
    pose proof (audit_default_producer_link_receipts V E B cb source st v parent) as Hbody.
    rewrite Hcall in Hbody; exact Hbody. }
  destruct Hrun; repeat rewrite Forall_app; repeat split;
    try solve [eauto using Htree, Hpred, Hset, Hlink, audit_default_producer_preds_receipts];
    repeat constructor; cbn [audit_default_producer_event_receipt]; eauto using Hsource.
Qed.

(** Every settlement in the finite traversal retains its own original callback receipts. *)
Lemma audit_default_producer_settles_receipts V E B (cb : audit_virtual_base_callbacks V E B)
    (source : E -> V * list B) (EV : CollectionsEncoding.encoding (V + unit))
    (g : GraphCore.Graph.t (V + unit) (E + V)) (p : GraphPrepare.prepared EV g)
    (r : dfs_result (V + unit) (E + V)) vertices state result events :
  audit_semi_producer_settles_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
    p r vertices state result events ->
  Forall (audit_default_producer_event_receipt V E B cb source) events.
Proof.
  intro Hrun; induction Hrun.
  - repeat constructor.
  - constructor; [exact I|].
    apply Forall_app; split;
      [eapply audit_default_producer_settle_receipts; eassumption|assumption].
Qed.

(** A nested semidominator run retains the original encoder and source receipts throughout. *)
Lemma audit_default_producer_run_receipts V E B (cb : audit_virtual_base_callbacks V E B)
    (source : E -> V * list B) (EV : CollectionsEncoding.encoding (V + unit))
    (g : GraphCore.Graph.t (V + unit) (E + V)) (p : GraphPrepare.prepared EV g)
    (r : dfs_result (V + unit) (E + V)) result events :
  audit_semi_producer_nested_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
    p r result events -> Forall (audit_default_producer_event_receipt V E B cb source) events.
Proof.
  intros [inner [Hrun ->]].
  constructor; [exact I|].
  eapply audit_default_producer_settles_receipts; exact Hrun.
Qed.

(** A producer receipt prices its recorded callback body at the actual operand budget. *)
Lemma audit_default_producer_event_bound V E B (cb : audit_virtual_base_callbacks V E B)
    (source : E -> V * list B) (weight : B -> nat)
    encode_source out_source target_source source_source
    encode_budget out_budget target_budget source_budget event :
  audit_graph_external_callback_adapter (audit_virtual_base_encode cb) weight encode_source
    encode_budget ->
  audit_graph_external_callback_adapter (audit_virtual_base_out cb) weight out_source out_budget ->
  audit_graph_external_callback_adapter (audit_virtual_base_target cb) weight target_source
    target_budget ->
  audit_graph_external_callback_adapter source weight source_source source_budget ->
  audit_default_producer_event_receipt V E B cb source event ->
  audit_semi_producer_nested_body_event_work (audit_virtual_full_body_event_work weight) event <=
    audit_semi_producer_nested_body_event_work
      (audit_default_virtual_event_budget encode_budget out_budget target_budget source_budget)
      event.
Proof.
  intros Hencode Hout Htarget Hsource Hreceipt.
  destruct event as [site|edge vertex body|inner|tree|pred|size];
    cbn [audit_default_producer_event_receipt audit_semi_producer_nested_body_event_work] in *;
    try lia.
  - eapply audit_default_virtual_receipts_bound; eassumption.
  - destruct inner as [site|vertex_map|rank_map|a b result trace];
      cbn [audit_default_semi_event_receipt audit_semi_nested_body_event_work] in *; try lia.
    + destruct vertex_map; cbn [audit_default_map_virtual_receipt] in *;
        eapply audit_default_virtual_receipts_bound; eassumption.
    + destruct rank_map; cbn [audit_default_map_virtual_receipt] in *;
        eapply audit_default_virtual_receipts_bound; eassumption.
  - destruct tree; cbn [audit_default_map_virtual_receipt] in *;
      eapply audit_default_virtual_receipts_bound; eassumption.
  - destruct pred; cbn [audit_default_map_virtual_receipt] in *;
      eapply audit_default_virtual_receipts_bound; eassumption.
Qed.

(** A real semidominator run obeys the per-operand callback budget. *)
Lemma audit_default_producer_run_body_bound V E B (cb : audit_virtual_base_callbacks V E B)
    (source : E -> V * list B) (weight : B -> nat)
    encode_source out_source target_source source_source
    encode_budget out_budget target_budget source_budget
    (EV : CollectionsEncoding.encoding (V + unit)) (g : GraphCore.Graph.t (V + unit) (E + V))
    (p : GraphPrepare.prepared EV g) (r : dfs_result (V + unit) (E + V)) result events :
  audit_graph_external_callback_adapter (audit_virtual_base_encode cb) weight encode_source
    encode_budget ->
  audit_graph_external_callback_adapter (audit_virtual_base_out cb) weight out_source out_budget ->
  audit_graph_external_callback_adapter (audit_virtual_base_target cb) weight target_source
    target_budget ->
  audit_graph_external_callback_adapter source weight source_source source_budget ->
  audit_semi_producer_nested_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
    p r result events ->
  audit_semi_producer_nested_body_work (audit_virtual_full_body_event_work weight) events <=
    audit_semi_producer_nested_body_work
      (audit_default_virtual_event_budget encode_budget out_budget target_budget source_budget)
      events.
Proof.
  intros Hencode Hout Htarget Hsource Hrun.
  pose proof (audit_default_producer_run_receipts V E B cb source EV g p r result events Hrun)
    as Hreceipts.
  clear Hrun.
  induction Hreceipts as [|event rest Hreceipt Htail IH];
    cbn [audit_semi_producer_nested_body_work List.fold_right].
  - lia.
  - pose proof (audit_default_producer_event_bound V E B cb source weight encode_source out_source
      target_source source_source encode_budget out_budget target_budget source_budget event
      Hencode Hout Htarget Hsource Hreceipt) as Hbound.
    unfold audit_semi_producer_nested_body_work in IH.
    lia.
Qed.

(** An LT event retains receipts for each original callback in its attached body. *)
Definition audit_default_lt_event_receipt V E B (cb : audit_virtual_base_callbacks V E B)
    (source : E -> V * list B) (event : audit_lt_nested_event (V + unit) (E + V)
      (audit_virtual_full_call V E B)) : Prop :=
  match event with
  | LtNestedSemi inner => audit_default_semi_event_receipt V E B cb source inner
  | LtNestedProducer inner => audit_default_producer_event_receipt V E B cb source inner
  | LtNestedBucket item => audit_default_map_virtual_receipt V E B (list (V + unit)) cb source item
  | LtNestedTree item => audit_default_map_virtual_receipt V E B (E + V) cb source item
  | LtNestedSource _ _ body
  | LtNestedEncode _ _ body =>
      Forall (audit_default_virtual_receipt V E B cb source) body
  | _ => True
  end.

(** The bucket traversal retains the encoder receipts of its map operations. *)
Lemma audit_default_lt_bucket_receipts V E B (cb : audit_virtual_base_callbacks V E B)
    (source : E -> V * list B) semis vertices buckets :
  Forall (audit_default_lt_event_receipt V E B cb source)
    (snd (audit_lt_nested_buckets (E := E + V) (audit_virtual_full_encode cb)
      semis vertices buckets)).
Proof.
  revert buckets; induction vertices as [|v rest IH]; intro buckets.
  - repeat constructor.
  - cbn [audit_lt_nested_buckets].
    pose proof (audit_default_virtual_map_get_receipts V E B (V + unit) cb source v semis)
      as Hget.
    destruct (audit_map_get (audit_virtual_full_encode cb) v semis) as [found get_events].
    cbn [snd] in Hget; destruct found as [parent|].
    + pose proof (audit_default_virtual_map_get_receipts V E B (list (V + unit)) cb source parent
        buckets) as Hbucket.
      destruct (audit_map_get (audit_virtual_full_encode cb) parent buckets)
        as [old bucket_events].
      cbn [snd] in Hbucket.
      pose proof (audit_default_virtual_map_set_receipts V E B (list (V + unit)) cb source parent
        buckets (v :: match old with
        | Some xs => xs
        | None => []
        end)) as Hset.
      destruct (audit_map_set (audit_virtual_full_encode cb) parent
        (v :: match old with
        | Some xs => xs
        | None => []
        end) buckets) as [next set_events].
      cbn [snd] in Hset; specialize (IH next).
      destruct (audit_lt_nested_buckets (E := E + V) (audit_virtual_full_encode cb) semis rest next)
        as [result later].
      cbn [snd] in IH |- *; constructor; [exact I|].
      apply Forall_app; split; [apply Forall_map; exact Hget|].
      constructor; [exact I|].
      repeat rewrite Forall_app; repeat split; try (apply Forall_map; assumption); assumption.
    + specialize (IH buckets).
      destruct (audit_lt_nested_buckets (E := E + V) (audit_virtual_full_encode cb) semis rest
        buckets) as [result later].
      cbn [snd] in IH |- *; constructor; [exact I|].
      apply Forall_app; split; [apply Forall_map; exact Hget|].
      constructor; [exact I|exact IH].
Qed.

(** One bucket member preserves compression, score, rank, and map-write receipts. *)
Lemma audit_default_lt_member_receipts V E B (cb : audit_virtual_base_callbacks V E B)
    (source : E -> V * list B) (r : dfs_result (V + unit) (E + V)) semis s initial vertex result
    events :
  audit_lt_nested_member_run (audit_virtual_full_encode cb) r semis s initial vertex result
    events ->
  Forall (audit_default_lt_event_receipt V E B cb source) events.
Proof.
  intro Hrun.
  assert (Hset : forall key value input output trace,
    audit_map_set (audit_virtual_full_encode cb) key value input = (output, trace) ->
    Forall (audit_default_lt_event_receipt V E B cb source)
      (map (fun item => LtNestedSemi (SemiNestedVertexMap item)) trace)).
  { intros key value input output trace Hcall.
    pose proof (audit_default_virtual_map_set_receipts V E B (V + unit) cb source key input value)
      as Hbody.
    rewrite Hcall in Hbody; cbn [snd] in Hbody; apply Forall_map; exact Hbody. }
  assert (Hrank : forall v number trace,
    audit_semi_nested_rank (audit_virtual_full_encode cb) r v = (number, trace) ->
    Forall (audit_default_lt_event_receipt V E B cb source) (map LtNestedSemi trace)).
  { intros v number trace Hcall.
    pose proof (audit_default_semi_rank_receipts V E B cb source r v) as Hbody.
    rewrite Hcall in Hbody; cbn [snd] in Hbody; apply Forall_map; exact Hbody. }
  assert (Hscore : forall v score trace,
    audit_semi_nested_score (audit_virtual_full_encode cb) r semis v = (score, trace) ->
    Forall (audit_default_lt_event_receipt V E B cb source) (map LtNestedSemi trace)).
  { intros v score trace Hcall.
    pose proof (audit_default_semi_score_receipts V E B cb source r semis v) as Hbody.
    rewrite Hcall in Hbody; cbn [snd] in Hbody; apply Forall_map; exact Hbody. }
  assert (Hinner : forall st v after trace,
    audit_semi_nested_compress_run (audit_virtual_full_encode cb) r semis st v after trace ->
    Forall (audit_default_lt_event_receipt V E B cb source) (map LtNestedSemi trace)).
  { intros st v after trace Hcall.
    apply Forall_map; eapply audit_default_semi_compress_receipts; exact Hcall. }
  destruct Hrun; repeat rewrite Forall_app; repeat split;
    try solve [eauto using Hset, Hrank, Hscore, Hinner]; repeat constructor.
Qed.

(** A member list retains receipts for each member in the actual order. *)
Lemma audit_default_lt_members_receipts V E B (cb : audit_virtual_base_callbacks V E B)
    (source : E -> V * list B) (r : dfs_result (V + unit) (E + V)) semis s vertices initial result
    events :
  audit_lt_nested_members_run (audit_virtual_full_encode cb) r semis s vertices initial result
    events -> Forall (audit_default_lt_event_receipt V E B cb source) events.
Proof.
  intro Hrun; induction Hrun.
  - repeat constructor.
  - constructor; [exact I|].
    apply Forall_app; split; [eapply audit_default_lt_member_receipts; eassumption|assumption].
Qed.

(** One reverse LT step preserves its tree, source, link, and member receipts. *)
Lemma audit_default_lt_reverse_receipts V E B (cb : audit_virtual_base_callbacks V E B)
    (source : E -> V * list B) (r : dfs_result (V + unit) (E + V)) semis buckets initial vertex
    result events :
  audit_lt_nested_reverse_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
    r semis buckets initial vertex result events ->
  Forall (audit_default_lt_event_receipt V E B cb source) events.
Proof.
  intro Hrun.
  assert (Hbucket : forall key input output trace,
    audit_map_get (audit_virtual_full_encode cb) key input = (output, trace) ->
    Forall (audit_default_lt_event_receipt V E B cb source) (map LtNestedBucket trace)).
  { intros key input output trace Hcall.
    pose proof (audit_default_virtual_map_get_receipts V E B (list (V + unit)) cb source key input)
      as Hbody.
    rewrite Hcall in Hbody; cbn [snd] in Hbody; apply Forall_map; exact Hbody. }
  assert (Htree : forall key input output trace,
    audit_map_get (audit_virtual_full_encode cb) key input = (output, trace) ->
    Forall (audit_default_lt_event_receipt V E B cb source) (map LtNestedTree trace)).
  { intros key input output trace Hcall.
    pose proof (audit_default_virtual_map_get_receipts V E B (E + V) cb source key input) as Hbody.
    rewrite Hcall in Hbody; cbn [snd] in Hbody; apply Forall_map; exact Hbody. }
  assert (Hsource : forall edge parent body,
    audit_virtual_full_source source edge = (parent, body) ->
    Forall (audit_default_virtual_receipt V E B cb source) body).
  { intros edge parent body Hcall.
    pose proof (proj2 (audit_default_virtual_call_receipts V E B cb source) edge) as Hbody.
    rewrite Hcall in Hbody; exact Hbody. }
  assert (Hlink : forall st v parent output trace,
    audit_semi_producer_link (E := E + V) (audit_virtual_full_encode cb) st v parent =
      (output, trace) ->
    Forall (audit_default_lt_event_receipt V E B cb source) (map LtNestedProducer trace)).
  { intros st v parent output trace Hcall.
    pose proof (audit_default_producer_link_receipts V E B cb source st v parent) as Hbody.
    rewrite Hcall in Hbody; cbn [snd] in Hbody; apply Forall_map; exact Hbody. }
  destruct Hrun; repeat rewrite Forall_app; repeat split;
    try solve [eauto using Hbucket, Htree, Hlink, audit_default_lt_members_receipts];
    repeat constructor; cbn [audit_default_lt_event_receipt]; eauto using Hsource.
Qed.

(** The reverse LT traversal preserves receipts for each processed vertex. *)
Lemma audit_default_lt_reverse_fold_receipts V E B (cb : audit_virtual_base_callbacks V E B)
    (source : E -> V * list B) (r : dfs_result (V + unit) (E + V)) semis buckets vertices initial
    result events :
  audit_lt_nested_reverse_fold_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
    r semis buckets vertices initial result events ->
  Forall (audit_default_lt_event_receipt V E B cb source) events.
Proof.
  intro Hrun; induction Hrun.
  - repeat constructor.
  - constructor; [exact I|].
    apply Forall_app; split; [eapply audit_default_lt_reverse_receipts; eassumption|assumption].
Qed.

(** One correction step retains each actual map and encoder callback body. *)
Lemma audit_default_lt_correct_receipts V E B (cb : audit_virtual_base_callbacks V E B)
    (source : E -> V * list B) semis provisional corrected vertex :
  Forall (audit_default_lt_event_receipt V E B cb source)
    (snd (audit_lt_nested_correct (E := E + V) (audit_virtual_full_encode cb)
      semis provisional corrected vertex)).
Proof.
  assert (Hget : forall key input output trace,
    audit_map_get (audit_virtual_full_encode cb) key input = (output, trace) ->
    Forall (audit_default_lt_event_receipt V E B cb source)
      (map (fun item => LtNestedSemi (SemiNestedVertexMap item)) trace)).
  { intros key input output trace Hcall.
    pose proof (audit_default_virtual_map_get_receipts V E B (V + unit) cb source key input) as
      Hbody.
    rewrite Hcall in Hbody; cbn [snd] in Hbody; apply Forall_map; exact Hbody. }
  assert (Hset : forall key value input output trace,
    audit_map_set (audit_virtual_full_encode cb) key value input = (output, trace) ->
    Forall (audit_default_lt_event_receipt V E B cb source)
      (map (fun item => LtNestedSemi (SemiNestedVertexMap item)) trace)).
  { intros key value input output trace Hcall.
    pose proof (audit_default_virtual_map_set_receipts V E B (V + unit) cb source key input value)
      as Hbody.
    rewrite Hcall in Hbody; cbn [snd] in Hbody; apply Forall_map; exact Hbody. }
  assert (Hencode : forall key code body,
    audit_virtual_full_encode cb key = (code, body) ->
    Forall (audit_default_virtual_receipt V E B cb source) body).
  { intros key code body Hcall.
    pose proof (proj1 (audit_default_virtual_call_receipts V E B cb source) key) as Hbody.
    rewrite Hcall in Hbody; exact Hbody. }
  unfold audit_lt_nested_correct.
  destruct (audit_map_get (audit_virtual_full_encode cb) vertex provisional)
    as [found first] eqn:Hfirst.
  destruct found as [u|].
  - destruct (audit_virtual_full_encode cb u) as [a a_body] eqn:Ha.
    destruct (audit_map_get (audit_virtual_full_encode cb) vertex semis)
      as [found value_events] eqn:Hvalue.
    set (value := match found with
      | Some x => x
      | None => vertex
      end).
    destruct (audit_virtual_full_encode cb value) as [b b_body] eqn:Hb.
    destruct (audit_positive_eqb a b) as [equal equal_events].
    destruct equal.
    + destruct (audit_map_set (audit_virtual_full_encode cb) vertex u corrected)
        as [result set_events] eqn:Hwrite.
      cbn [snd].
      repeat rewrite Forall_app; repeat split; try solve [eauto using Hget, Hset];
        repeat constructor; cbn [audit_default_lt_event_receipt]; eauto using Hencode.
    + destruct (audit_map_get (audit_virtual_full_encode cb) u corrected)
        as [found_parent parent_events] eqn:Hparent.
      set (parent := match found_parent with
        | Some x => x
        | None => u
        end).
      destruct (audit_map_set (audit_virtual_full_encode cb) vertex parent corrected)
        as [result set_events] eqn:Hwrite.
      cbn [snd].
      repeat rewrite Forall_app; repeat split; try solve [eauto using Hget, Hset];
        repeat constructor; cbn [audit_default_lt_event_receipt]; eauto using Hencode.
  - cbn [snd]; apply Forall_app; split; [eauto using Hget|repeat constructor].
Qed.

(** The correction fold retains the receipts from every correction step. *)
Lemma audit_default_lt_correct_fold_receipts V E B (cb : audit_virtual_base_callbacks V E B)
    (source : E -> V * list B) semis provisional vertices corrected :
  Forall (audit_default_lt_event_receipt V E B cb source)
    (snd (audit_lt_nested_correct_fold (E := E + V) (audit_virtual_full_encode cb)
      semis provisional vertices corrected)).
Proof.
  revert corrected; induction vertices as [|v rest IH]; intro corrected.
  - repeat constructor.
  - cbn [audit_lt_nested_correct_fold].
    pose proof (audit_default_lt_correct_receipts V E B cb source semis provisional corrected v)
      as Hhere.
    destruct (audit_lt_nested_correct (E := E + V) (audit_virtual_full_encode cb)
      semis provisional corrected v) as [middle here].
    cbn [snd] in Hhere; specialize (IH middle).
    destruct (audit_lt_nested_correct_fold (E := E + V) (audit_virtual_full_encode cb)
      semis provisional rest middle) as [result later].
    cbn [snd] in IH |- *; constructor; [exact I|].
    apply Forall_app; split; assumption.
Qed.

(** A nested LT run retains original callback receipts in buckets, traversal, and correction. *)
Lemma audit_default_lt_run_receipts V E B (cb : audit_virtual_base_callbacks V E B)
    (source : E -> V * list B) (r : dfs_result (V + unit) (E + V)) semis result events :
  audit_lt_nested_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
    r semis result events -> Forall (audit_default_lt_event_receipt V E B cb source) events.
Proof.
  unfold audit_lt_nested_run.
  pose proof (audit_default_lt_bucket_receipts V E B cb source semis (preorder r) Map.empty)
    as Hbuckets.
  destruct (audit_lt_nested_buckets (E := E + V) (audit_virtual_full_encode cb)
    semis (preorder r) Map.empty) as [buckets bucket_events].
  cbn [snd] in Hbuckets.
  intros [settled [reverse_events [Hreverse Hcorrection]]].
  pose proof (audit_default_lt_correct_fold_receipts V E B cb source semis (LtState.parents settled)
    (preorder r) Map.empty) as Hcorrect.
  destruct (audit_lt_nested_correct_fold (E := E + V) (audit_virtual_full_encode cb)
    semis (LtState.parents settled) (preorder r) Map.empty) as [output correction_events].
  cbn [snd] in Hcorrect; destruct Hcorrection as [_ ->].
  repeat rewrite Forall_app; repeat split; try assumption.
  - repeat constructor.
  - eapply audit_default_lt_reverse_fold_receipts; exact Hreverse.
Qed.

(** An LT event prices each retained body at the budget for its actual callback operand. *)
Lemma audit_default_lt_event_bound V E B (cb : audit_virtual_base_callbacks V E B)
    (source : E -> V * list B) (weight : B -> nat)
    encode_source out_source target_source source_source
    encode_budget out_budget target_budget source_budget event :
  audit_graph_external_callback_adapter (audit_virtual_base_encode cb) weight encode_source
    encode_budget ->
  audit_graph_external_callback_adapter (audit_virtual_base_out cb) weight out_source out_budget ->
  audit_graph_external_callback_adapter (audit_virtual_base_target cb) weight target_source
    target_budget ->
  audit_graph_external_callback_adapter source weight source_source source_budget ->
  audit_default_lt_event_receipt V E B cb source event ->
  audit_lt_nested_body_event_work (audit_virtual_full_body_event_work weight) event <=
    audit_lt_nested_body_event_work
      (audit_default_virtual_event_budget encode_budget out_budget target_budget source_budget)
      event.
Proof.
  intros Hencode Hout Htarget Hsource Hreceipt.
  destruct event as [site|inner|producer|bucket|tree|edge vertex source_body|v code encode_body|
    a b result trace|size];
    cbn [audit_default_lt_event_receipt audit_lt_nested_body_event_work] in *; try lia.
  - destruct inner as [site|vertex_map|rank_map|a b result trace];
      cbn [audit_default_semi_event_receipt audit_semi_nested_body_event_work] in *; try lia.
    + destruct vertex_map; cbn [audit_default_map_virtual_receipt] in *;
        eapply audit_default_virtual_receipts_bound; eassumption.
    + destruct rank_map; cbn [audit_default_map_virtual_receipt] in *;
        eapply audit_default_virtual_receipts_bound; eassumption.
  - eapply audit_default_producer_event_bound; eassumption.
  - destruct bucket; cbn [audit_default_map_virtual_receipt] in *;
      eapply audit_default_virtual_receipts_bound; eassumption.
  - destruct tree; cbn [audit_default_map_virtual_receipt] in *;
      eapply audit_default_virtual_receipts_bound; eassumption.
  - eapply audit_default_virtual_receipts_bound; eassumption.
  - eapply audit_default_virtual_receipts_bound; eassumption.
Qed.

(** A real nested LT run obeys the per-operand callback budget. *)
Lemma audit_default_lt_run_body_bound V E B (cb : audit_virtual_base_callbacks V E B)
    (source : E -> V * list B) (weight : B -> nat)
    encode_source out_source target_source source_source
    encode_budget out_budget target_budget source_budget
    (r : dfs_result (V + unit) (E + V)) semis result events :
  audit_graph_external_callback_adapter (audit_virtual_base_encode cb) weight encode_source
    encode_budget ->
  audit_graph_external_callback_adapter (audit_virtual_base_out cb) weight out_source out_budget ->
  audit_graph_external_callback_adapter (audit_virtual_base_target cb) weight target_source
    target_budget ->
  audit_graph_external_callback_adapter source weight source_source source_budget ->
  audit_lt_nested_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
    r semis result events ->
  audit_lt_nested_body_work (audit_virtual_full_body_event_work weight) events <=
    audit_lt_nested_body_work
      (audit_default_virtual_event_budget encode_budget out_budget target_budget source_budget)
      events.
Proof.
  intros Hencode Hout Htarget Hsource Hrun.
  pose proof (audit_default_lt_run_receipts V E B cb source r semis result events Hrun) as
    Hreceipts.
  clear Hrun.
  induction Hreceipts as [|event rest Hreceipt Htail IH];
    cbn [audit_lt_nested_body_work List.fold_right].
  - lia.
  - pose proof (audit_default_lt_event_bound V E B cb source weight encode_source out_source
      target_source source_source encode_budget out_budget target_budget source_budget event
      Hencode Hout Htarget Hsource Hreceipt) as Hbound.
    unfold audit_lt_nested_body_work in IH; lia.
Qed.

(** An erasure map event records the original encoder receipt for its actual key. *)
Definition audit_default_erase_receipt V B (enc : V -> positive * list B)
    (event : audit_erase_nested_event V B) : Prop :=
  match event with
  | EraseNestedSet item => audit_default_map_receipt V V B enc item
  | _ => True
  end.

(** The finite erasure traversal retains every actual encoder receipt. *)
Lemma audit_default_erase_rows_receipts V B (enc : V -> positive * list B) rows :
  Forall (audit_default_erase_receipt V B enc) (snd (audit_erase_nested_rows enc rows)).
Proof.
  induction rows as [|[child parent] rest IH].
  - repeat constructor.
  - cbn [audit_erase_nested_rows].
    destruct (audit_erase_nested_rows enc rest) as [middle events].
    cbn [snd] in IH; destruct child as [child|[]]; destruct parent as [parent|[]];
      cbn [snd]; try (constructor; [exact I|]; apply Forall_app; split;
        [exact IH|repeat constructor]).
    pose proof (proj1 (proj2 (audit_default_map_call_receipts V V B enc child middle parent)))
      as Hset.
    destruct (audit_map_set enc child parent middle) as [result writes].
    cbn [snd] in Hset |- *; constructor; [exact I|].
    apply Forall_app; split; [exact IH|].
    constructor; [exact I|].
    apply Forall_map; exact Hset.
Qed.

(** The full erasure trace retains those same map-operation receipts. *)
Lemma audit_default_erase_run_receipts V B (enc : V -> positive * list B) parents :
  Forall (audit_default_erase_receipt V B enc) (snd (audit_erase_virtual_nested enc parents)).
Proof.
  unfold audit_erase_virtual_nested.
  destruct (audit_map_elements parents) as [rows elements].
  pose proof (audit_default_erase_rows_receipts V B enc rows) as Hrows.
  destruct (audit_erase_nested_rows enc rows) as [result events].
  cbn [snd] in Hrows |- *; apply Forall_app; split; [|exact Hrows].
  apply Forall_map; apply Forall_forall; intros event Hin; exact I.
Qed.

(** Erasure external work is bounded by the encoder budget for each recorded key. *)
Lemma audit_default_erase_body_bound V B (enc : V -> positive * list B) (weight : B -> nat)
    encode_source encode_budget parents :
  audit_graph_external_callback_adapter enc weight encode_source encode_budget ->
  let events := snd (audit_erase_virtual_nested enc parents) in
  audit_erase_nested_body_work weight events <=
    fold_right (fun event n => audit_default_erase_event_budget encode_budget event + n) 0 events.
Proof.
  intro Hencode.
  pose proof (audit_default_erase_run_receipts V B enc parents) as Hreceipts.
  destruct (audit_erase_virtual_nested enc parents) as [result events].
  cbn [snd] in Hreceipts |- *.
  induction Hreceipts as [|event rest Hreceipt Htail IH];
    cbn [audit_erase_nested_body_work List.fold_right].
  - lia.
  - unfold audit_erase_nested_body_work in IH.
    destruct event as [site|item|item];
      cbn [audit_default_erase_receipt audit_erase_nested_body_event_work
        audit_default_erase_event_budget] in *; try lia.
    destruct item; cbn [audit_default_map_receipt audit_erase_nested_body_event_work
      audit_default_erase_event_budget] in *;
      pose proof (proj2 (audit_graph_external_callback_source _ _ _ _ Hencode _ _ _ Hreceipt)); lia.
Qed.

(** A forest callback body retains the encoder return attached to its actual key. *)
Definition audit_default_forest_body_receipt V B (enc : V -> positive * list B)
    (event : audit_dom_source_body V B) : Prop :=
  match event with
  | DomSourceBodyMap item => audit_default_map_receipt V (list V) B enc item
  | DomSourceBodyEncode vertex code body => enc vertex = (code, body)
  | DomSourceBodyTarget _ => True
  end.

(** Actual forest callbacks retain the same original encoder receipts. *)
Lemma audit_default_forest_callback_receipts V B (enc : V -> positive * list B) children :
  (forall vertex, Forall (audit_default_forest_body_receipt V B enc)
    (snd (audit_dom_source_out enc children vertex))) /\
  (forall vertex, Forall (audit_default_forest_body_receipt V B enc)
    (snd (audit_dom_source_encode enc vertex))) /\
  (forall vertex, Forall (audit_default_forest_body_receipt V B enc)
    (snd (audit_dom_source_target (B := B) vertex))).
Proof.
  repeat split.
  - intro vertex; unfold audit_dom_source_out.
    pose proof (proj1 (audit_default_map_call_receipts V (list V) B enc vertex children [])) as
      Hmap.
    destruct (audit_map_get enc vertex children) as [found events].
    cbn [snd] in Hmap |- *; apply Forall_map; exact Hmap.
  - intro vertex; unfold audit_dom_source_encode.
    destruct (enc vertex) as [code body] eqn:Henc; cbn [snd]; repeat constructor; exact Henc.
  - intro vertex; repeat constructor.
Qed.

(** A forest body event is charged against the budget of its recorded encoder operand. *)
Lemma audit_default_forest_body_event_bound V B (enc : V -> positive * list B) (weight : B -> nat)
    encode_source encode_budget event :
  audit_graph_external_callback_adapter enc weight encode_source encode_budget ->
  audit_default_forest_body_receipt V B enc event ->
  audit_dom_source_body_external weight event <= audit_default_forest_body_budget encode_budget
    event.
Proof.
  intros Hencode Hreceipt; destruct event as [item|vertex|vertex code body];
    cbn [audit_default_forest_body_receipt audit_dom_source_body_external
      audit_default_forest_body_budget] in *; try lia.
  - destruct item; cbn [audit_default_map_receipt audit_dom_source_body_external
      audit_default_forest_body_budget] in *;
      exact (proj2 (audit_graph_external_callback_source _ _ _ _ Hencode _ _ _ Hreceipt)).
  - exact (proj2 (audit_graph_external_callback_source _ _ _ _ Hencode _ _ _ Hreceipt)).
Qed.

(** A finite forest body is bounded by the budgets of its actual encoder operands. *)
Lemma audit_default_forest_body_bound V B (enc : V -> positive * list B) (weight : B -> nat)
    encode_source encode_budget events :
  audit_graph_external_callback_adapter enc weight encode_source encode_budget ->
  Forall (audit_default_forest_body_receipt V B enc) events ->
  fold_right (fun event n => audit_dom_source_body_external weight event + n) 0 events <=
    fold_right (fun event n => audit_default_forest_body_budget encode_budget event + n) 0 events.
Proof.
  intros Hencode Hreceipts; induction Hreceipts as [|event rest Hreceipt Htail IH]; cbn
    [fold_right].
  - lia.
  - pose proof (audit_default_forest_body_event_bound V B enc weight encode_source encode_budget
      event Hencode Hreceipt); lia.
Qed.

(** A forest preparation receipt prices the bodies attached to that exact callback. *)
Lemma audit_default_forest_prepare_event_bound V B (enc : V -> positive * list B)
    (weight : B -> nat) encode_source encode_budget children item :
  audit_graph_external_callback_adapter enc weight encode_source encode_budget ->
  audit_source_receipt
    (AuditPrepareCallbackModel V V (audit_dom_source_body V B)
      (audit_dom_source_out enc children) audit_dom_source_target (audit_dom_source_encode enc))
    item ->
  audit_prepare_source_body_event_work (audit_dom_source_body_external weight) item <=
    audit_prepare_source_body_event_work (audit_default_forest_body_budget encode_budget) item.
Proof.
  intros Hencode Hreceipt.
  destruct (audit_default_forest_callback_receipts V B enc children) as [Hout [Henc Htarget]].
  destruct item as [site|vertex outgoing body|edge target body|map_event|amount|nodes edges fuel];
    cbn [audit_source_receipt audit_prepare_out_model audit_prepare_target_model
      audit_prepare_encode_model audit_prepare_source_body_event_work] in *; try lia.
  - specialize (Hout vertex); rewrite Hreceipt in Hout; cbn [snd] in Hout.
    eapply audit_default_forest_body_bound; eassumption.
  - specialize (Htarget edge); rewrite Hreceipt in Htarget; cbn [snd] in Htarget.
    eapply audit_default_forest_body_bound; eassumption.
  - destruct map_event as [key code input output body trace|key value code input output body trace|
      key code input output body trace];
      cbn [audit_source_receipt audit_prepare_encode_model audit_prepare_source_body_event_work]
        in *; specialize (Henc key); rewrite Hreceipt in Henc; cbn [snd] in Henc;
      eapply audit_default_forest_body_bound; eassumption.
Qed.

(** A forest preparation trace charges all recorded callbacks at their operand budgets. *)
Lemma audit_default_forest_prepare_bodies_bound V B (enc : V -> positive * list B)
    (weight : B -> nat) encode_source encode_budget children events :
  audit_graph_external_callback_adapter enc weight encode_source encode_budget ->
  Forall (audit_source_receipt
    (AuditPrepareCallbackModel V V (audit_dom_source_body V B)
      (audit_dom_source_out enc children) audit_dom_source_target (audit_dom_source_encode enc)))
    events ->
  audit_prepare_source_body_work (audit_dom_source_body_external weight) events <=
    audit_prepare_source_body_work (audit_default_forest_body_budget encode_budget) events.
Proof.
  intros Hencode Hreceipts; induction Hreceipts as [|item rest Hreceipt Htail IH].
  - reflexivity.
  - pose proof (audit_default_forest_prepare_event_bound V B enc weight encode_source encode_budget
      children item Hencode Hreceipt) as Hbound.
    unfold audit_prepare_source_body_work in *; cbn [fold_right]; lia.
Qed.

(** A forest DFS capture prices the original encoder body attached to that callback. *)
Lemma audit_default_forest_dfs_bodies_bound V B (enc : V -> positive * list B)
    (weight : B -> nat) encode_source encode_budget events :
  audit_graph_external_callback_adapter enc weight encode_source encode_budget ->
  Forall (audit_dfs_event_receipts
    (AuditDfsCallbackModel V V (audit_dom_source_body V B) audit_dom_source_target
      (audit_dom_source_encode enc))) events ->
  audit_dfs_source_body_work (audit_dom_source_body_external weight) events <=
    audit_dfs_source_body_work (audit_default_forest_body_budget encode_budget) events.
Proof.
  intros Hencode Hreceipts; induction Hreceipts as [|[event captures] rest Hcapture Htail IH].
  - reflexivity.
  - unfold audit_dfs_event_receipts in Hcapture; cbn in Hcapture.
    assert (Hbound : fold_right (fun capture n => audit_graph_capture_work
      (audit_dom_source_body_external weight) capture + n) 0 captures <=
      fold_right (fun capture n => audit_graph_capture_work
        (audit_default_forest_body_budget encode_budget) capture + n) 0 captures).
    { induction Hcapture as [|capture captures Hreceipt Hcapture_tail IHcapture]; cbn
      [fold_right]; [lia|].
      destruct (audit_default_forest_callback_receipts V B enc Map.empty) as [_ [Henc Htarget]].
      destruct capture as [edge target body|vertex code body];
        cbn [audit_dfs_capture_receipt audit_dfs_target_model audit_dfs_encode_model
          audit_graph_capture_work] in *.
      - specialize (Htarget edge); rewrite Hreceipt in Htarget; cbn [snd] in Htarget.
        pose proof (audit_default_forest_body_bound V B enc weight encode_source encode_budget
          body Hencode Htarget); lia.
      - specialize (Henc vertex); rewrite Hreceipt in Henc; cbn [snd] in Henc.
        pose proof (audit_default_forest_body_bound V B enc weight encode_source encode_budget
          body Hencode Henc); lia. }
    unfold audit_dfs_source_body_work in *; cbn [fold_right snd].
    lia.
Qed.

(** Child and root map events retain the encoder receipt for their actual operand. *)
Definition audit_default_dom_map_receipt V E B (enc : V -> positive * list B)
    (event : audit_dom_source_event V E B) : Prop :=
  match event with
  | DomSourceChild item => audit_default_map_receipt V (list V) B enc item
  | DomSourceParent item => audit_default_map_receipt V V B enc item
  | _ => True
  end.

(** Child indexing keeps the encoder receipt from every actual lookup and write. *)
Lemma audit_default_dom_children_receipts V E B (enc : V -> positive * list B) rows :
  Forall (audit_default_dom_map_receipt V E B enc)
    (snd (audit_dom_source_children (E := E) enc rows)).
Proof.
  induction rows as [|[vertex parent] rest IH].
  - repeat constructor.
  - cbn [audit_dom_source_children].
    destruct (audit_dom_source_children (E := E) enc rest) as [children events].
    cbn [snd] in IH.
    pose proof (proj1 (audit_default_map_call_receipts V (list V) B enc parent children [])) as
      Hget.
    destruct (audit_map_get enc parent children) as [found reads].
    set (row := match found with
      | Some xs => xs
      | None => []
      end).
    pose proof (proj1 (proj2 (audit_default_map_call_receipts V (list V) B enc parent children
      (vertex :: row)))) as Hset.
    destruct (audit_map_set enc parent (vertex :: row) children) as [result writes].
    cbn [snd] in Hget, Hset |- *; constructor; [exact I|].
    repeat rewrite Forall_app; repeat split; try (apply Forall_map; assumption); assumption.
Qed.

(** Root selection keeps the encoder receipt from every actual parent lookup. *)
Lemma audit_default_dom_roots_receipts V E B (enc : V -> positive * list B) parents vertices :
  Forall (audit_default_dom_map_receipt V E B enc)
    (snd (audit_dom_source_roots (E := E) enc parents vertices)).
Proof.
  induction vertices as [|vertex rest IH].
  - repeat constructor.
  - cbn [audit_dom_source_roots].
    pose proof (audit_default_map_get_receipt :=
      proj1 (audit_default_map_call_receipts V V B enc vertex parents vertex)).
    destruct (audit_map_get enc vertex parents) as [found reads].
    destruct (audit_dom_source_roots (E := E) enc parents rest) as [roots events].
    cbn [snd] in audit_default_map_get_receipt, IH |- *.
    destruct found; cbn [snd].
    all: constructor; [exact I|]; apply Forall_app; split;
      [apply Forall_map; exact audit_default_map_get_receipt|exact IH].
Qed.

(** A child or root event charges its captured encoder body to the same input key. *)
Lemma audit_default_dom_map_event_bound V E B (enc : V -> positive * list B) (weight : B -> nat)
    encode_source encode_budget target_budget event :
  audit_graph_external_callback_adapter enc weight encode_source encode_budget ->
  audit_default_dom_map_receipt V E B enc event ->
  (match event with
    | DomSourceChild _
    | DomSourceParent _ => audit_dom_source_event_external weight event
    | _ => 0
    end) <= audit_default_dom_event_budget encode_budget target_budget event.
Proof.
  intros Hencode Hreceipt.
  destruct event as [site|initial|elements|child|parent|prep|dfs];
    cbn [audit_default_dom_map_receipt audit_dom_source_event_external
      audit_default_dom_event_budget] in *; try lia;
    destruct child || destruct parent;
    cbn [audit_default_map_receipt audit_dom_source_event_external audit_default_dom_event_budget]
      in *;
    pose proof (proj2 (audit_graph_external_callback_source _ _ _ _ Hencode _ _ _ Hreceipt)); lia.
Qed.

(** Child and root traces contain only cases and their corresponding map operations. *)
Definition audit_default_dom_map_only V E B (event : audit_dom_source_event V E B) : Prop :=
  match event with
  | DomSourceCase _
  | DomSourceChild _
  | DomSourceParent _ => True
  | _ => False
  end.

(** Child construction emits only case markers and child-map operations. *)
Lemma audit_default_dom_children_map_only V E B (enc : V -> positive * list B) rows :
  Forall (audit_default_dom_map_only V E B) (snd (audit_dom_source_children (E := E) enc rows)).
Proof.
  induction rows as [|[vertex parent] rest IH]; [repeat constructor|].
  cbn [audit_dom_source_children].
  destruct (audit_dom_source_children (E := E) enc rest) as [children events].
  destruct (audit_map_get enc parent children) as [found reads].
  destruct (audit_map_set enc parent
    (vertex :: match found with
      | Some xs => xs
      | None => []
      end) children) as [result writes].
  cbn [snd] in IH |- *; constructor; [exact I|].
  repeat rewrite Forall_app; repeat split; try assumption;
    apply Forall_map; apply Forall_forall; intros item Hin; exact I.
Qed.

(** Root construction emits only case markers and parent-map operations. *)
Lemma audit_default_dom_roots_map_only V E B (enc : V -> positive * list B) parents vertices :
  Forall (audit_default_dom_map_only V E B)
    (snd (audit_dom_source_roots (E := E) enc parents vertices)).
Proof.
  induction vertices as [|vertex rest IH]; [repeat constructor|].
  cbn [audit_dom_source_roots].
  destruct (audit_map_get enc vertex parents) as [found reads].
  destruct (audit_dom_source_roots (E := E) enc parents rest) as [roots events].
  cbn [snd] in IH |- *; destruct found; cbn [snd].
  all: constructor; [exact I|]; apply Forall_app; split; [|exact IH];
    apply Forall_map; apply Forall_forall; intros item Hin; exact I.
Qed.

(** Actual child and root map traces obey their per-operand external budgets. *)
Lemma audit_default_dom_maps_body_bound V E B (enc : V -> positive * list B) (weight : B -> nat)
    encode_source encode_budget target_budget events :
  audit_graph_external_callback_adapter enc weight encode_source encode_budget ->
  Forall (audit_default_dom_map_only V E B) events ->
  Forall (audit_default_dom_map_receipt V E B enc) events ->
  audit_dom_source_external_work weight events <=
    fold_right (fun event n => audit_default_dom_event_budget encode_budget target_budget event + n)
      0 events.
Proof.
  intros Hencode Honly Hreceipts; induction Hreceipts as [|event rest Hreceipt Htail IH].
  - reflexivity.
  - inversion Honly as [|? ? Hitem Hrest]; subst; specialize (IH Hrest).
    pose proof (audit_default_dom_map_event_bound V E B enc weight encode_source encode_budget
      target_budget event Hencode Hreceipt) as Hbound.
    unfold audit_dom_source_external_work in *; cbn [fold_right].
    destruct event; cbn [audit_default_dom_map_only] in Hitem; try contradiction;
      cbn [audit_dom_source_event_external] in *; lia.
Qed.

(** Initial DFS captures charge each target or encoder callback at its actual operand. *)
Lemma audit_default_dom_initial_bodies_bound V E B (cb : audit_dfs_callback_model V E B)
    (weight : B -> nat) encode_source target_source encode_budget target_budget events :
  audit_graph_external_callback_adapter (audit_dfs_encode_model cb) weight encode_source
    encode_budget ->
  audit_graph_external_callback_adapter (audit_dfs_target_model cb) weight target_source
    target_budget ->
  Forall (audit_dfs_event_receipts cb) events ->
  audit_dfs_source_body_work weight events <=
    fold_right (fun event n => audit_default_dom_event_budget encode_budget target_budget
      (DomSourceInitialDfs event) + n) 0 events.
Proof.
  intros Hencode Htarget Hreceipts; induction Hreceipts as [|[event captures] rest Hcapture Htail
    IH].
  - reflexivity.
  - unfold audit_dfs_event_receipts in Hcapture; cbn in Hcapture.
    assert (Hbound : fold_right (fun capture n => audit_graph_capture_work weight capture + n)
      0 captures <= fold_right (fun capture n =>
        match capture with
        | AuditGraphEncodeCapture _ _ _ vertex _ _ => encode_budget vertex + n
        | AuditGraphTargetCapture _ _ _ edge _ _ => target_budget edge + n
        end) 0 captures).
    { induction Hcapture as [|capture captures Hreceipt Hcapture_tail IHcapture]; cbn [fold_right];
        [lia|].
      destruct capture as [edge target body|vertex code body];
        cbn [audit_dfs_capture_receipt audit_graph_capture_work] in *.
      - pose proof (proj2 (audit_graph_external_callback_source _ _ _ _ Htarget edge target body
          Hreceipt)); lia.
      - pose proof (proj2 (audit_graph_external_callback_source _ _ _ _ Hencode vertex code body
          Hreceipt)); lia. }
    unfold audit_dfs_source_body_work in *; unfold audit_default_dom_event_budget in IH.
    cbn [fold_right snd audit_default_dom_event_budget].
    lia.
Qed.

(** Adapter event budgets add over concatenated source traces. *)
Lemma audit_default_dom_budget_app V E B encode_budget target_budget
    (left right : list (audit_dom_source_event V E B)) :
  fold_right (fun event n => audit_default_dom_event_budget encode_budget target_budget event + n)
    0 (left ++ right) =
  fold_right (fun event n => audit_default_dom_event_budget encode_budget target_budget event + n)
    0 left +
  fold_right (fun event n => audit_default_dom_event_budget encode_budget target_budget event + n)
    0 right.
Proof.
  induction left as [|event rest IH]; cbn [List.app List.fold_right]; lia.
Qed.

(** Preparation event budgets preserve the captured forest callback body. *)
Lemma audit_default_dom_prepare_budget V E B encode_budget target_budget events :
  fold_right (fun event n => audit_default_dom_event_budget encode_budget target_budget event + n)
    0 (map (@DomSourcePrepare V E B) events) =
  audit_prepare_source_body_work (audit_default_forest_body_budget encode_budget) events.
Proof.
  induction events as [|event rest IH]; [reflexivity|].
  change (audit_prepare_source_body_work (audit_default_forest_body_budget encode_budget) [event] +
    fold_right (fun item n => audit_default_dom_event_budget encode_budget target_budget item + n)
      0 (map (@DomSourcePrepare V E B) rest) =
    audit_prepare_source_body_work (audit_default_forest_body_budget encode_budget) (event ::
      rest)).
  rewrite IH; unfold audit_prepare_source_body_work; cbn [fold_right]; lia.
Qed.

(** DFS event budgets preserve the captured forest callback body. *)
Lemma audit_default_dom_dfs_budget V E B encode_budget target_budget events :
  fold_right (fun event n => audit_default_dom_event_budget encode_budget target_budget event + n)
    0 (map (@DomSourceDfs V E B) events) =
  audit_dfs_source_body_work (audit_default_forest_body_budget encode_budget) events.
Proof.
  induction events as [|event rest IH]; [reflexivity|].
  change (audit_dfs_source_body_work (audit_default_forest_body_budget encode_budget) [event] +
    fold_right (fun item n => audit_default_dom_event_budget encode_budget target_budget item + n)
      0 (map (@DomSourceDfs V E B) rest) =
    audit_dfs_source_body_work (audit_default_forest_body_budget encode_budget) (event :: rest)).
  rewrite IH; unfold audit_dfs_source_body_work; cbn [fold_right]; lia.
Qed.

(** Map-enumeration events have no external callback budget. *)
Lemma audit_default_dom_elements_budget V E B encode_budget target_budget events :
  fold_right (fun event n => audit_default_dom_event_budget encode_budget target_budget event + n)
    0 (map (@DomSourceElements V E B) events) = 0.
Proof.
  induction events as [|event rest IH]; cbn [map fold_right audit_default_dom_event_budget]; lia.
Qed.

(** Each source segment prices its recorded callbacks and composes on the same trace. *)
Lemma audit_default_dom_segments_bound V E B (cb : audit_dfs_callback_model V E B)
    (weight : B -> nat) encode_source target_source encode_budget target_budget children
    first_events element_events child_events root_events prep_events dfs_events :
  audit_graph_external_callback_adapter (audit_dfs_encode_model cb) weight encode_source
    encode_budget ->
  audit_graph_external_callback_adapter (audit_dfs_target_model cb) weight target_source
    target_budget ->
  Forall (audit_dfs_event_receipts cb) first_events ->
  Forall (audit_default_dom_map_only V E B) child_events ->
  Forall (audit_default_dom_map_receipt V E B (audit_dfs_encode_model cb)) child_events ->
  Forall (audit_default_dom_map_only V E B) root_events ->
  Forall (audit_default_dom_map_receipt V E B (audit_dfs_encode_model cb)) root_events ->
  Forall (audit_source_receipt
    (AuditPrepareCallbackModel V V (audit_dom_source_body V B)
      (audit_dom_source_out (audit_dfs_encode_model cb) children) audit_dom_source_target
      (audit_dom_source_encode (audit_dfs_encode_model cb)))) prep_events ->
  Forall (audit_dfs_event_receipts
    (AuditDfsCallbackModel V V (audit_dom_source_body V B) audit_dom_source_target
      (audit_dom_source_encode (audit_dfs_encode_model cb)))) dfs_events ->
  let events := map DomSourceInitialDfs first_events ++ map DomSourceElements element_events ++
    child_events ++ root_events ++ map DomSourcePrepare prep_events ++ map DomSourceDfs
      dfs_events in
  audit_dom_source_external_work weight events <=
    fold_right (fun event n => audit_default_dom_event_budget encode_budget target_budget event + n)
      0 events.
Proof.
  intros Hencode Htarget Hfirst_receipts Hchildren_only Hchildren_receipts Hroots_only
    Hroots_receipts Hprepare_receipts Hforest_receipts.
  pose proof (audit_default_dom_initial_bodies_bound V E B cb weight encode_source target_source
    encode_budget target_budget first_events Hencode Htarget Hfirst_receipts) as Hfirst.
  pose proof (audit_default_dom_maps_body_bound V E B (audit_dfs_encode_model cb) weight
    encode_source encode_budget target_budget child_events Hencode Hchildren_only
    Hchildren_receipts) as Hchild.
  pose proof (audit_default_dom_maps_body_bound V E B (audit_dfs_encode_model cb) weight
    encode_source encode_budget target_budget root_events Hencode Hroots_only Hroots_receipts)
    as Hroot.
  pose proof (audit_default_forest_prepare_bodies_bound V B (audit_dfs_encode_model cb) weight
    encode_source encode_budget children prep_events Hencode Hprepare_receipts) as Hprep.
  pose proof (audit_default_forest_dfs_bodies_bound V B (audit_dfs_encode_model cb) weight
    encode_source encode_budget dfs_events Hencode Hforest_receipts) as Hdfs.
  cbn zeta. repeat rewrite audit_dom_source_external_app; repeat rewrite
    audit_default_dom_budget_app.
  rewrite (proj2 (audit_dom_initial_events_work weight first_events)).
  rewrite (proj2 (audit_dom_element_events_work (E := E) weight element_events)).
  rewrite (proj2 (audit_dom_prepare_events_work (E := E) weight prep_events)).
  rewrite (proj2 (audit_dom_dfs_events_work (E := E) weight dfs_events)).
  rewrite audit_default_dom_elements_budget, audit_default_dom_prepare_budget,
    audit_default_dom_dfs_budget, audit_dom_fold_map. lia.
Qed.

(** The actual forest preparation and DFS retain their per-callback source budgets. *)
Lemma audit_default_dom_forest_tail_bound V E B (EV : encoding V) (cb : audit_dfs_callback_model
  V E B)
    (weight : B -> nat) encode_source target_source encode_budget target_budget parents vertices
    roots children first_events element_events child_events root_events :
  (forall v, fst (audit_dfs_encode_model cb v) = encode EV v) ->
  audit_graph_external_callback_adapter (audit_dfs_encode_model cb) weight encode_source
    encode_budget ->
  audit_graph_external_callback_adapter (audit_dfs_target_model cb) weight target_source
    target_budget ->
  Forall (audit_dfs_event_receipts cb) first_events ->
  Forall (audit_default_dom_map_only V E B) child_events ->
  Forall (audit_default_dom_map_receipt V E B (audit_dfs_encode_model cb)) child_events ->
  Forall (audit_default_dom_map_only V E B) root_events ->
  Forall (audit_default_dom_map_receipt V E B (audit_dfs_encode_model cb)) root_events ->
  let forest := Graph.Make roots vertices (fun v => index_edges EV children v)
    (fun v => match Map.get EV v parents with
      | Some u => u
      | None => v
      end) (fun v => v) in
  let prepare_cb := AuditPrepareCallbackModel V V (audit_dom_source_body V B)
    (audit_dom_source_out (audit_dfs_encode_model cb) children) audit_dom_source_target
    (audit_dom_source_encode (audit_dfs_encode_model cb)) in
  let dfs_cb := AuditDfsCallbackModel V V (audit_dom_source_body V B) audit_dom_source_target
    (audit_dom_source_encode (audit_dfs_encode_model cb)) in
  let receipt :=
    (let '(fp, prep_events) := audit_prepare_source_counted EV forest prepare_cb in
      let '(result, dfs_events) := audit_dfs_source_counted fp dfs_cb FinSet.empty roots in
      AuditDomSourceReceipt forest fp result
        (map DomSourceInitialDfs first_events ++ map DomSourceElements element_events ++
        child_events ++ root_events ++ map DomSourcePrepare prep_events ++
        map DomSourceDfs dfs_events)) in
  audit_dom_source_external_work weight (audit_dom_source_events receipt) <=
    fold_right (fun event n => audit_default_dom_event_budget encode_budget target_budget event + n)
      0 (audit_dom_source_events receipt).
Proof.
  intros Hencode Hencode_adapter Htarget_adapter Hfirst Hchild_only Hchild Hroot_only Hroot.
  set (forest := Graph.Make roots vertices (fun v => index_edges EV children v)
    (fun v => match Map.get EV v parents with
      | Some u => u
      | None => v
      end) (fun v => v)).
  set (prepare_cb := AuditPrepareCallbackModel V V (audit_dom_source_body V B)
    (audit_dom_source_out (audit_dfs_encode_model cb) children) audit_dom_source_target
    (audit_dom_source_encode (audit_dfs_encode_model cb))).
  set (dfs_cb := AuditDfsCallbackModel V V (audit_dom_source_body V B) audit_dom_source_target
    (audit_dom_source_encode (audit_dfs_encode_model cb))).
  assert (Hprepare : audit_prepare_callbacks_erase EV forest prepare_cb).
  { unfold audit_prepare_callbacks_erase, prepare_cb, forest; cbn [audit_prepare_out_model
      audit_prepare_target_model audit_prepare_encode_model Graph.out Graph.target].
    repeat split; intros; try reflexivity.
    - apply audit_dom_source_out_erases; exact Hencode.
    - apply audit_dom_source_encode_erases; exact Hencode. }
  pose proof (audit_prepare_source_with_receipts V V (audit_dom_source_body V B) EV forest
    prepare_cb (audit_dom_source_body_external weight) Hprepare) as Hprepare_run.
  cbn zeta; fold forest prepare_cb dfs_cb.
  destruct (audit_prepare_source_counted EV forest prepare_cb) as [fp prep_events].
  cbn [fst snd] in Hprepare_run; destruct Hprepare_run as [_ [_ [_ Hprep]]].
  pose proof (audit_dfs_source_receipts fp dfs_cb FinSet.empty roots) as Hdfs.
  destruct (audit_dfs_source_counted fp dfs_cb FinSet.empty roots) as [result dfs_events].
  cbn [snd] in Hdfs. cbn [audit_dom_source_events].
  eapply (audit_default_dom_segments_bound V E B cb weight encode_source target_source
    encode_budget target_budget children first_events element_events child_events root_events
    prep_events dfs_events); eassumption.
Qed.

(** The actual dominator search trace charges each callback to its recorded operand. *)
Lemma audit_default_dom_search_body_bound V E B (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) parents (cb : audit_dfs_callback_model V E B) (weight : B -> nat)
    encode_source target_source encode_budget target_budget :
  audit_dfs_callbacks_erase EV g cb ->
  audit_graph_external_callback_adapter (audit_dfs_encode_model cb) weight encode_source
    encode_budget ->
  audit_graph_external_callback_adapter (audit_dfs_target_model cb) weight target_source
    target_budget ->
  let receipt := audit_dom_search_source_counted p parents cb in
  audit_dom_source_external_work weight (audit_dom_source_events receipt) <=
    fold_right (fun event n => audit_default_dom_event_budget encode_budget target_budget event + n)
      0 (audit_dom_source_events receipt).
Proof.
  intros Hcallbacks Hencode_adapter Htarget_adapter.
  destruct Hcallbacks as [Htarget Hencode].
  pose proof (audit_dfs_source_receipts p cb FinSet.empty (Graph.entries g)) as Hfirst_receipts.
  unfold audit_dom_search_source_counted.
  destruct (audit_dfs_source_counted p cb FinSet.empty (Graph.entries g))
    as [search first_events].
  cbn [snd] in Hfirst_receipts.
  destruct (audit_map_elements parents) as [rows element_events].
  pose proof (audit_default_dom_children_receipts V E B (audit_dfs_encode_model cb) rows)
    as Hchildren_receipts.
  pose proof (audit_default_dom_children_map_only V E B (audit_dfs_encode_model cb) rows)
    as Hchildren_only.
  destruct (audit_dom_source_children (E := E) (audit_dfs_encode_model cb) rows)
    as [children child_events].
  cbn [snd] in Hchildren_receipts, Hchildren_only.
  pose proof (audit_default_dom_roots_receipts V E B (audit_dfs_encode_model cb) parents
    (preorder search)) as Hroots_receipts.
  pose proof (audit_default_dom_roots_map_only V E B (audit_dfs_encode_model cb) parents
    (preorder search)) as Hroots_only.
  destruct (audit_dom_source_roots (E := E) (audit_dfs_encode_model cb) parents (preorder search))
    as [roots root_events].
  cbn [snd] in Hroots_receipts, Hroots_only.
  eapply (audit_default_dom_forest_tail_bound V E B EV cb weight encode_source target_source
    encode_budget target_budget parents (preorder search) roots children first_events element_events
    child_events root_events); eassumption.
Qed.

(** Pointwise callback prices extend to a finite body. *)
Lemma audit_default_body_budget_mono A (first second : A -> nat) events :
  (forall event, first event <= second event) ->
  fold_right (fun event n => first event + n) 0 events <=
    fold_right (fun event n => second event + n) 0 events.
Proof.
  intro Hbound; induction events as [|event rest IH]; cbn [fold_right]; [lia|].
  pose proof (Hbound event); lia.
Qed.

(** Pointwise prices extend to all preparation callback bodies. *)
Lemma audit_default_prepare_budget_mono V E B (first second : B -> nat)
    (events : list (audit_prepare_source_event V E B)) :
  (forall event, first event <= second event) ->
  audit_prepare_source_body_work first events <= audit_prepare_source_body_work second events.
Proof.
  intro Hbound; induction events as [|event rest IH]; [reflexivity|].
  unfold audit_prepare_source_body_work in *; cbn [fold_right].
  destruct event as [site|vertex outgoing body|edge target body|item|amount|nodes edges fuel];
    cbn [audit_prepare_source_body_event_work]; try lia.
  - pose proof (audit_default_body_budget_mono B first second body Hbound); lia.
  - pose proof (audit_default_body_budget_mono B first second body Hbound); lia.
  - destruct item as [key code input output body trace|key value code input output body trace|
      key code input output body trace]; cbn [audit_prepare_source_body_event_work];
      pose proof (audit_default_body_budget_mono B first second body Hbound); lia.
Qed.

(** Pointwise prices extend to all DFS callback captures. *)
Lemma audit_default_dfs_budget_mono V E B (first second : B -> nat)
    (events : list (audit_dfs_nested_event V E (audit_graph_callback_capture V E B))) :
  (forall event, first event <= second event) ->
  audit_dfs_source_body_work first events <= audit_dfs_source_body_work second events.
Proof.
  intro Hbound; induction events as [|[event captures] rest IH]; [reflexivity|].
  assert (Hcaptures : fold_right (fun capture n => audit_graph_capture_work first capture + n)
    0 captures <= fold_right (fun capture n => audit_graph_capture_work second capture + n)
    0 captures).
  { induction captures as [|capture more IHcapture]; cbn [fold_right]; [lia|].
    destruct capture as [edge target body|vertex code body]; cbn [audit_graph_capture_work];
      pose proof (audit_default_body_budget_mono B first second body Hbound); lia. }
  unfold audit_dfs_source_body_work in *; cbn [fold_right snd]; lia.
Qed.

(** Virtual search bodies obey the full dominator callback budget on the same receipt. *)
Lemma audit_default_virtual_search_bodies_bound V E B (EV : encoding V) (g : Graph.t V E)
    (cb : audit_virtual_base_callbacks V E B) (weight : B -> nat)
    encode_source out_source target_source encode_budget out_budget target_budget source_budget :
  audit_virtual_base_callbacks_erase EV g cb ->
  audit_graph_external_callback_adapter (audit_virtual_base_encode cb) weight encode_source
    encode_budget ->
  audit_graph_external_callback_adapter (audit_virtual_base_out cb) weight out_source out_budget ->
  audit_graph_external_callback_adapter (audit_virtual_base_target cb) weight target_source
    target_budget ->
  let '(_, (_, (prepare_events, dfs_events))) := audit_virtual_source_search EV g cb in
  audit_prepare_source_body_work (audit_virtual_full_body_event_work weight) prepare_events +
    audit_dfs_source_body_work (audit_virtual_full_body_event_work weight) dfs_events <=
  audit_prepare_source_body_work
    (audit_default_virtual_event_budget encode_budget out_budget target_budget source_budget)
    prepare_events +
  audit_dfs_source_body_work
    (audit_default_virtual_event_budget encode_budget out_budget target_budget source_budget)
    dfs_events.
Proof.
  intros Hcallbacks Hencode Hout Htarget.
  destruct (audit_virtual_full_callbacks_correct V E B EV g cb Hcallbacks) as [Hprep Hdfs].
  pose proof (audit_prepare_source_with_receipts _ _ _ (virtual_encoding EV) (virtual_graph EV g)
    (audit_virtual_full_prepare_callbacks g cb) (audit_virtual_full_body_event_work weight) Hprep)
    as Hprepare_run.
  unfold audit_virtual_source_search.
  destruct (audit_prepare_source_counted (virtual_encoding EV) (virtual_graph EV g)
    (audit_virtual_full_prepare_callbacks g cb)) as [vp prepare_events].
  destruct Hprepare_run as [_ [_ [_ Hprepare_receipts]]].
  pose proof (audit_dfs_source_receipts vp (audit_virtual_full_dfs_callbacks cb) FinSet.empty
    [inr tt]) as Hdfs_receipts.
  destruct (audit_dfs_source_counted vp (audit_virtual_full_dfs_callbacks cb) FinSet.empty [inr tt])
    as [result dfs_events].
  cbn [snd] in Hdfs_receipts |- *.
  pose proof (audit_virtual_prepare_bodies_bound V E B g cb weight encode_source out_source
    target_source encode_budget out_budget target_budget prepare_events Hencode Hout Htarget
    Hprepare_receipts) as Hprepare_bound.
  pose proof (audit_virtual_dfs_bodies_bound V E B cb weight encode_source out_source target_source
    encode_budget out_budget target_budget dfs_events Hencode Hout Htarget Hdfs_receipts)
    as Hdfs_bound.
  pose proof (audit_default_prepare_budget_mono _ _ _
    (audit_virtual_adapter_call_budget encode_budget out_budget target_budget)
    (audit_default_virtual_event_budget encode_budget out_budget target_budget source_budget)
    prepare_events (audit_default_virtual_budget_extends V E B encode_budget out_budget
      target_budget source_budget)) as Hprepare_mono.
  pose proof (audit_default_dfs_budget_mono _ _ _
    (audit_virtual_adapter_call_budget encode_budget out_budget target_budget)
    (audit_default_virtual_event_budget encode_budget out_budget target_budget source_budget)
    dfs_events (audit_default_virtual_budget_extends V E B encode_budget out_budget
      target_budget source_budget)) as Hdfs_mono.
  lia.
Qed.

(** Per-call adapter bounds compose the captured stages once their numerical budgets are known. *)
Lemma audit_default_dom_adapt_captured_run V E B (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (cb : audit_virtual_base_callbacks V E B) (source : E -> V * list B)
    (weight : B -> nat) encode_source out_source target_source source_source
    encode_budget out_budget target_budget source_budget vp search prepare_events dfs_events
    semi_state semi_events virtual_parents lt_events parents erase_events receipt :
  audit_virtual_base_callbacks_erase EV g cb ->
  audit_graph_external_callback_adapter (audit_virtual_base_encode cb) weight encode_source
    encode_budget ->
  audit_graph_external_callback_adapter (audit_virtual_base_out cb) weight out_source out_budget ->
  audit_graph_external_callback_adapter (audit_virtual_base_target cb) weight target_source
    target_budget ->
  audit_graph_external_callback_adapter source weight source_source source_budget ->
  audit_virtual_source_search EV g cb = (vp, (search, (prepare_events, dfs_events))) ->
  audit_semi_producer_nested_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
    vp search semi_state semi_events ->
  audit_lt_nested_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
    search (SemiState.result semi_state) virtual_parents lt_events ->
  audit_erase_virtual_nested (audit_virtual_base_encode cb) virtual_parents =
    (parents, erase_events) ->
  receipt = audit_dom_search_source_counted p parents
    (AuditDfsCallbackModel V E B (audit_virtual_base_target cb) (audit_virtual_base_encode cb)) ->
  let work := audit_prepare_source_work
    (fun event => audit_virtual_full_internal_event_work event +
      audit_virtual_full_body_event_work weight event) prepare_events +
    audit_dfs_source_work
      (fun event => audit_virtual_full_internal_event_work event +
        audit_virtual_full_body_event_work weight event) dfs_events +
    audit_virtual_semi_stage_work weight semi_events + audit_virtual_lt_stage_work weight
      lt_events +
    audit_erase_nested_work weight erase_events +
    audit_dom_source_work weight (audit_dom_source_events receipt) in
  work <= audit_virtual_lt_input_budget EV g + audit_dom_search_source_budget EV g p parents
    receipt +
    audit_prepare_source_body_work (audit_virtual_full_body_event_work weight) prepare_events +
    audit_dfs_source_body_work (audit_virtual_full_body_event_work weight) dfs_events +
    audit_virtual_semi_external_work weight semi_events + audit_virtual_lt_external_work weight
      lt_events + audit_erase_nested_body_work weight erase_events +
    audit_dom_source_external_work weight (audit_dom_source_events receipt) ->
  audit_virtual_lt_input_budget EV g + audit_dom_search_source_budget EV g p parents receipt <=
    audit_default_dom_input_budget EV g p ->
  let virtual_budget := audit_default_virtual_event_budget encode_budget out_budget target_budget
    source_budget in
  let external := audit_prepare_source_body_work virtual_budget prepare_events +
    audit_dfs_source_body_work virtual_budget dfs_events +
    audit_semi_producer_nested_body_work virtual_budget semi_events +
    audit_lt_nested_body_work virtual_budget lt_events +
    fold_right (fun event n => audit_default_erase_event_budget encode_budget event + n) 0
      erase_events +
    fold_right (fun event n => audit_default_dom_event_budget encode_budget target_budget event + n)
      0 (audit_dom_source_events receipt) in
  work <= audit_default_dom_input_budget EV g p + external /\
  work <= audit_virtual_lt_input_budget EV g + audit_dom_search_source_budget EV g p parents
    receipt + external.
Proof.
  intros Hcallbacks Hencode Hout Htarget Hsource Hsearch Hsemi Hlt Herase Hreceipt work Hwork
    Hinput.
  pose proof (audit_default_virtual_search_bodies_bound V E B EV g cb weight encode_source
    out_source target_source encode_budget out_budget target_budget source_budget Hcallbacks
    Hencode Hout Htarget) as Hvirtual.
  rewrite Hsearch in Hvirtual; cbn in Hvirtual.
  pose proof (audit_default_producer_run_body_bound V E B cb source weight encode_source out_source
    target_source source_source encode_budget out_budget target_budget source_budget
    (virtual_encoding EV) (virtual_graph EV g) vp search semi_state semi_events
    Hencode Hout Htarget Hsource Hsemi) as Hsemi_body.
  pose proof (audit_default_lt_run_body_bound V E B cb source weight encode_source out_source
    target_source source_source encode_budget out_budget target_budget source_budget
    search (SemiState.result semi_state) virtual_parents lt_events Hencode Hout Htarget Hsource Hlt)
    as Hlt_body.
  pose proof (audit_default_erase_body_bound V B (audit_virtual_base_encode cb) weight encode_source
    encode_budget virtual_parents Hencode) as Herase_body.
  rewrite Herase in Herase_body; cbn [snd] in Herase_body.
  assert (Hdfs_callbacks : audit_dfs_callbacks_erase EV g
    (AuditDfsCallbackModel V E B (audit_virtual_base_target cb) (audit_virtual_base_encode cb))).
  { destruct Hcallbacks as [_ [Htarget_erases Hencode_erases]]; split; assumption. }
  pose proof (audit_default_dom_search_body_bound V E B EV g p parents
    (AuditDfsCallbackModel V E B (audit_virtual_base_target cb) (audit_virtual_base_encode cb))
    weight encode_source target_source encode_budget target_budget Hdfs_callbacks Hencode Htarget)
    as Hforest_body.
  rewrite <- Hreceipt in Hforest_body.
  unfold audit_virtual_semi_external_work, audit_virtual_lt_external_work in Hwork.
  cbn zeta in *.
  lia.
Qed.

(** The original graph's input budget contains the virtual LT input budget. *)
Lemma audit_default_virtual_input_budget_le V E (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) :
  audit_virtual_lt_input_budget EV g <= audit_default_dom_input_budget EV g p.
Proof.
  unfold audit_virtual_lt_input_budget, audit_default_dom_input_budget,
    audit_virtual_lt_input_scale, audit_virtual_lt_input_width, audit_virtual_lt_input_support.
  set (edges := flat_map (Graph.out g) (Graph.nodes g)).
  set (vertices := Graph.nodes g ++ Graph.entries g ++ map (Graph.source g) edges ++
    map (Graph.target g) edges).
  set (width := fold_right Nat.max 0 (map (fun v => Pos.size_nat (encode EV v)) vertices)).
  set (virtual_scale := 4 + length (Graph.nodes g) + length (Graph.entries g) + length edges +
    width).
  set (full_scale := S (4 + length vertices + length edges + width + Pos.to_nat (fuel p) +
    audit_dfs_full_input_width EV g p (Graph.entries g) +
    audit_dfs_source_budget EV g p (Graph.entries g))).
  assert (Hscale : virtual_scale <= full_scale).
  { unfold virtual_scale, full_scale, vertices; repeat rewrite length_app; repeat rewrite
    length_map;
      lia. }
  assert (Hpositive : 1 <= full_scale) by (unfold full_scale; lia).
  apply Nat.mul_le_mono_l.
  eapply Nat.le_trans.
  - apply Nat.pow_le_mono_l; exact Hscale.
  - apply Nat.pow_le_mono_r; lia.
Qed.

(** * Original-input forest bounds *)

(** The concrete virtual LT output used by the default source run. *)
Definition audit_default_virtual_parents {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) :=
  lt_compute (virtual_encoding EV) (virtual_graph EV g) (virtual_dfs p)
    (SemiState.result (semi_compute (virtual_prepared p) (virtual_dfs p))).

(** Each erased binding comes from its actual virtual parent row. *)
Lemma audit_default_erased_parent_row {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) key value :
  In (key, value) (Map.elements (erase_virtual_parents EV (audit_default_virtual_parents EV g
    p))) ->
  In (inl key, inl value) (Map.elements (audit_default_virtual_parents EV g p)).
Proof.
  intro Hrow.
  pose proof (lt_compute_wf (virtual_encoding EV) (virtual_graph EV g) (virtual_dfs p)
    (SemiState.result (semi_compute (virtual_prepared p) (virtual_dfs p)))) as Hwf.
  fold (audit_default_virtual_parents EV g p) in Hwf.
  apply (Map.elements_sound EV) in Hrow; [|apply erase_virtual_parents_wf].
  apply (erase_virtual_parents_get EV _ Hwf) in Hrow.
  now apply (Map.elements_complete (virtual_encoding EV)).
Qed.

(** Both endpoints of an erased parent row fit the virtual input scale. *)
Lemma audit_default_erased_parent_width {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) key value :
  In (key, value) (Map.elements (erase_virtual_parents EV (audit_default_virtual_parents EV g
    p))) ->
  Pos.size_nat (encode EV key) <= audit_virtual_lt_input_scale EV g /\
  Pos.size_nat (encode EV value) <= audit_virtual_lt_input_scale EV g.
Proof.
  intro Hrow. apply audit_default_erased_parent_row in Hrow.
  destruct (audit_dom_virtual_parent_value_width EV g p (inl key) (inl value) Hrow) as [Hkey Hval].
  cbn [virtual_encoding sum_encoding encode Pos.size_nat] in Hkey, Hval. lia.
Qed.

(** Tagging distinct real vertices preserves their distinctness. *)
Lemma audit_default_inl_nodup {V} (keys : list V) : NoDup keys -> NoDup (map (@inl V unit) keys).
Proof.
  intro Hnodup. induction Hnodup as [|key rest Hnot Hrest IH]; cbn [map].
  - constructor.
  - constructor; [|exact IH]. intro Hin. apply in_map_iff in Hin as [value [Heq Hin]].
    inversion Heq; subst value. contradiction.
Qed.

(** The erased map has at most one row per discovered virtual vertex. *)
Lemma audit_default_erased_parent_count {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) :
  length (Map.elements (erase_virtual_parents EV (audit_default_virtual_parents EV g p))) <=
    length (preorder (virtual_dfs p)).
Proof.
  set (parents := erase_virtual_parents EV (audit_default_virtual_parents EV g p)).
  pose proof (Map.elements_nodup EV parents (erase_virtual_parents_wf EV _)) as Hnodup.
  pose proof (audit_default_inl_nodup _ Hnodup) as Hmapped.
  assert (Hincl : incl (map (@inl V unit) (map fst (Map.elements parents)))
    (preorder (virtual_dfs p))).
  { intros key Hin. apply in_map_iff in Hin as [real [Heq Hin]]. subst key.
    apply in_map_iff in Hin as [[k v] [Heq Hrow]]. cbn in Heq; subst k.
    unfold parents in Hrow. apply audit_default_erased_parent_row in Hrow.
    eapply audit_dom_lt_parent_key; exact Hrow. }
  pose proof (NoDup_incl_length Hmapped Hincl) as Hlength.
  repeat rewrite length_map in Hlength. exact Hlength.
Qed.

(** Erased rows, trie nodes and endpoint widths fit explicit virtual-scale bounds. *)
Lemma audit_default_erased_parent_bounds {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) :
  let scale := audit_virtual_lt_input_scale EV g in
  let parents := erase_virtual_parents EV (audit_default_virtual_parents EV g p) in
  length (Map.elements parents) <= 1 + 3 * scale /\
  audit_trie_nodes parents <= (1 + 3 * scale) * scale /\
  fold_right Nat.max 0 (map (fun row => Nat.max (Pos.size_nat (encode EV (fst row)))
    (Pos.size_nat (encode EV (snd row)))) (Map.elements parents)) <= scale.
Proof.
  set (parents := erase_virtual_parents EV (audit_default_virtual_parents EV g p)).
  pose proof (audit_default_erased_parent_count EV g p) as Hcount; fold parents in Hcount.
  pose proof (audit_dom_virtual_search_counts EV g p) as [Hlive _]; cbn zeta in Hlive.
  assert (Hwidth : forall key value, In (key, value) (Map.elements parents) ->
    Pos.size_nat (encode EV key) <= audit_virtual_lt_input_scale EV g /\
    Pos.size_nat (encode EV value) <= audit_virtual_lt_input_scale EV g).
  { intros key value Hrow. now apply audit_default_erased_parent_width in Hrow. }
  pose proof (audit_dom_bits_bounded EV parents (audit_virtual_lt_input_scale EV g)
    (erase_virtual_parents_wf EV _) (fun key value Hrow => proj1 (Hwidth key value Hrow))) as Hbits.
  pose proof (audit_dom_nodes_le_output_bits parents) as Hnodes.
  cbn zeta; fold parents; repeat split.
  - lia.
  - eapply Nat.le_trans; [exact Hnodes|]. eapply Nat.le_trans; [exact Hbits|].
    apply Nat.mul_le_mono_r. lia.
  - apply audit_dom_max_fold_bound; [lia|]. intros n Hin.
    apply in_map_iff in Hin as [[key value] [Heq Hrow]]. cbn in Heq; subst n.
    destruct (Hwidth key value Hrow) as [Hkey Hvalue]. now apply Nat.max_lub.
Qed.

(** Forest preparation callbacks erase to the actual child-index operations. *)
Lemma audit_default_forest_prepare_callbacks {V E B} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) parents (enc : V -> positive * list B) :
  (forall v, fst (enc v) = encode EV v) ->
  audit_prepare_callbacks_erase EV (dom_forest p parents)
    (AuditPrepareCallbackModel V V (audit_dom_source_body V B)
      (audit_dom_source_out enc (dom_children EV (Map.elements parents)))
      audit_dom_source_target (audit_dom_source_encode enc)).
Proof.
  intro Hencode; unfold audit_prepare_callbacks_erase; cbn [audit_prepare_out_model
    audit_prepare_target_model audit_prepare_encode_model].
  split.
  - intro v; unfold dom_forest; cbn [Graph.out]. now apply audit_dom_source_out_erases.
  - split; [reflexivity|]. intro v. now apply audit_dom_source_encode_erases.
Qed.

(** The captured forest and index erase to the source forest and its preparation. *)
Lemma audit_default_forest_receipt {V E B} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) parents (cb : audit_dfs_callback_model V E B) :
  audit_dfs_callbacks_erase EV g cb ->
  let receipt := audit_dom_search_source_counted p parents cb in
  audit_dom_source_forest receipt = dom_forest p parents /\
  audit_dom_source_index receipt = prepare EV (audit_dom_source_forest receipt).
Proof.
  intros [Htarget Hencode].
  pose proof (audit_dfs_source_result_and_count p cb FinSet.empty (Graph.entries g)
    (conj Htarget Hencode)) as [Hsearch _].
  pose proof (audit_map_elements_erases V V parents) as Hrows.
  pose proof (audit_dom_source_children_erases (E := E) EV (audit_dfs_encode_model cb)
    (Map.elements parents) Hencode) as Hchildren.
  pose proof (audit_dom_source_roots_erases (E := E) EV (audit_dfs_encode_model cb) parents
    (preorder (dfs p FinSet.empty (Graph.entries g))) Hencode) as Hroots.
  unfold audit_dom_search_source_counted.
  destruct (audit_dfs_source_counted p cb FinSet.empty (Graph.entries g)) as [search search_events].
  cbn [fst] in Hsearch; subst search.
  destruct (audit_map_elements parents) as [rows element_events]; cbn [fst] in Hrows; subst rows.
  destruct (audit_dom_source_children (audit_dfs_encode_model cb) (Map.elements parents))
    as [children child_events]; cbn [fst] in Hchildren; subst children.
  destruct (audit_dom_source_roots (audit_dfs_encode_model cb) parents
    (preorder (dfs p FinSet.empty (Graph.entries g)))) as [roots root_events];
    cbn [fst] in Hroots; subst roots.
  set (forest := dom_forest p parents).
  set (prepare_cb := AuditPrepareCallbackModel V V (audit_dom_source_body V B)
    (audit_dom_source_out (audit_dfs_encode_model cb) (dom_children EV (Map.elements parents)))
    audit_dom_source_target (audit_dom_source_encode (audit_dfs_encode_model cb))).
  pose proof (audit_default_forest_prepare_callbacks EV g p parents (audit_dfs_encode_model cb)
    Hencode) as Hprepare. fold forest prepare_cb in Hprepare.
  pose proof (audit_prepare_source_correct V V (audit_dom_source_body V B) EV forest prepare_cb
    (fun _ => 0) Hprepare) as Hprepared.
  change (let receipt :=
    (let '(fp, prep_events) := audit_prepare_source_counted EV forest prepare_cb in
      let dfs_cb := AuditDfsCallbackModel V V (audit_dom_source_body V B) audit_dom_source_target
        (audit_dom_source_encode (audit_dfs_encode_model cb)) in
      let '(result, dfs_events) := audit_dfs_source_counted fp dfs_cb FinSet.empty
        (Graph.entries forest) in
      AuditDomSourceReceipt forest fp result
        (map DomSourceInitialDfs search_events ++ map DomSourceElements element_events ++
        child_events ++ root_events ++ map DomSourcePrepare prep_events ++
        map DomSourceDfs dfs_events)) in
    audit_dom_source_forest receipt = forest /\
    audit_dom_source_index receipt = prepare EV (audit_dom_source_forest receipt)).
  destruct (audit_prepare_source_counted EV forest prepare_cb) as [fp prep_events].
  cbn [fst] in Hprepared; destruct Hprepared as [Hprepared _]; subst fp.
  cbv zeta.
  destruct (audit_dfs_source_counted (prepare EV forest)
    (AuditDfsCallbackModel V V (audit_dom_source_body V B) audit_dom_source_target
      (audit_dom_source_encode (audit_dfs_encode_model cb))) FinSet.empty (Graph.entries forest))
        eqn:Hdfs;
    split; reflexivity.
Qed.

(** The original adapter scale includes the supplied preparation and source DFS budget. *)
Definition audit_default_input_scale {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) : nat :=
  let edges := flat_map (Graph.out g) (Graph.nodes g) in
  let vertices := Graph.nodes g ++ Graph.entries g ++ map (Graph.source g) edges ++
    map (Graph.target g) edges in
  let width := fold_right Nat.max 0 (map (fun v => Pos.size_nat (encode EV v)) vertices) in
  S (4 + length vertices + length edges + width + Pos.to_nat (fuel p) +
    audit_dfs_full_input_width EV g p (Graph.entries g) +
    audit_dfs_source_budget EV g p (Graph.entries g)).

(** Each original graph and supplied-index component fits the adapter scale. *)
Lemma audit_default_input_scale_bounds {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) :
  let scale := audit_default_input_scale EV g p in
  4 <= scale /\ audit_virtual_lt_input_scale EV g <= scale /\
  length (Graph.entries g) <= scale /\ Pos.to_nat (fuel p) <= scale /\
  audit_dfs_full_input_width EV g p (Graph.entries g) <= scale /\
  audit_dfs_source_budget EV g p (Graph.entries g) <= scale.
Proof.
  unfold audit_default_input_scale, audit_virtual_lt_input_scale, audit_virtual_lt_input_width,
    audit_virtual_lt_input_support.
  set (edges := flat_map (Graph.out g) (Graph.nodes g)).
  set (vertices := Graph.nodes g ++ Graph.entries g ++ map (Graph.source g) edges ++
    map (Graph.target g) edges).
  set (width := fold_right Nat.max 0 (map (fun v => Pos.size_nat (encode EV v)) vertices)).
  cbn zeta; fold edges vertices width.
  unfold vertices; repeat rewrite length_app; repeat rewrite length_map. repeat split; lia.
Qed.

(** The original DFS and both erased-parent endpoints fit the adapter scale. *)
Lemma audit_default_erased_width_scale {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) :
  audit_dom_input_width EV g p (erase_virtual_parents EV (audit_default_virtual_parents EV g p)) <=
    audit_default_input_scale EV g p.
Proof.
  pose proof (audit_default_input_scale_bounds EV g p) as [_ [Hvirtual [_ [_ [Hdfs _]]]]].
  unfold audit_dom_input_width; apply Nat.max_lub; [exact Hdfs|].
  apply audit_dom_max_fold_bound; [lia|]. intros bits Hin.
  apply in_map_iff in Hin as [vertex [Heq Hvertex]]. subst bits.
  apply in_app_iff in Hvertex as [Hkey|Hvalue].
  - apply in_map_iff in Hkey as [[key value] [Heq Hrow]]; cbn in Heq; subst key.
    destruct (audit_default_erased_parent_width EV g p vertex value Hrow) as [Hbound _].
    unfold audit_key_bits_weight. lia.
  - apply in_map_iff in Hvalue as [[key value] [Heq Hrow]]; cbn in Heq; subst value.
    destruct (audit_default_erased_parent_width EV g p key vertex Hrow) as [_ Hbound].
    unfold audit_key_bits_weight. lia.
Qed.

(** Actual forest sizes, prepared fuel and key widths fit original-input polynomials. *)
Lemma audit_default_forest_size_bounds {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) :
  let scale := audit_default_input_scale EV g p in
  let parents := erase_virtual_parents EV (audit_default_virtual_parents EV g p) in
  let forest := dom_forest p parents in
  length (Map.elements parents) <= 4 * scale /\
  audit_trie_nodes parents <= 4 * scale * scale /\
  length (Graph.nodes forest) <= 2 * scale * scale /\
  length (Graph.entries forest) <= 2 * scale * scale /\
  edge_count forest <= 8 * scale * scale * scale /\
  Pos.to_nat (fuel (prepare EV forest)) <= 16 * scale * scale * scale /\
  audit_graph_prepare_input_width EV forest <= scale /\
  audit_dfs_full_input_width EV forest (prepare EV forest) (Graph.entries forest) <= scale.
Proof.
  pose proof (audit_default_input_scale_bounds EV g p) as [Hscale [Hvirtual [Hentries [Hfuel _]]]].
  pose proof (audit_default_erased_parent_bounds EV g p) as [Hrows [Hnodes _]].
  pose proof (audit_default_erased_width_scale EV g p) as Hwidth.
  set (t := audit_default_input_scale EV g p) in *.
  set (s := audit_virtual_lt_input_scale EV g) in *.
  set (parents := erase_virtual_parents EV (audit_default_virtual_parents EV g p)) in *.
  set (forest := dom_forest p parents) in *.
  cbn zeta in *.
  assert (Hrowt : length (Map.elements parents) <= 4 * t) by lia.
  assert (Hnodet : audit_trie_nodes parents <= 4 * t * t).
  { eapply Nat.le_trans; [exact Hnodes|].
    assert (Hproduct : (1 + 3 * s) * s <= (4 * t) * t).
    { apply Nat.mul_le_mono; lia. }
    lia. }
  pose proof (audit_dom_live_length EV g p) as Hlive.
  assert (Hlivet : length (Graph.nodes forest) <= 2 * t * t).
  { unfold forest, dom_forest; cbn [Graph.nodes].
    eapply Nat.le_trans; [exact Hlive|].
    assert (Hproduct : length (Graph.entries g) * S (Pos.to_nat (fuel p)) <= t * (2 * t)).
    { apply Nat.mul_le_mono; lia. }
    nia. }
  pose proof (audit_dom_forest_roots_length EV g p parents) as Hroots; fold forest in Hroots.
  assert (Hrootst : length (Graph.entries forest) <= 2 * t * t).
  { unfold forest, dom_forest in *; cbn [Graph.nodes] in *. lia. }
  pose proof (audit_dom_forest_edge_count EV g p parents) as Hedges; fold forest in Hedges.
  assert (Hedgest : edge_count forest <= 8 * t * t * t).
  { eapply Nat.le_trans; [exact Hedges|].
    assert (Hproduct : length (preorder (dfs p FinSet.empty (Graph.entries g))) *
      length (Map.elements parents) <= (2 * t * t) * (4 * t)).
    { apply Nat.mul_le_mono; [|exact Hrowt].
      unfold forest, dom_forest in Hlivet; exact Hlivet. }
    nia. }
  assert (Hft : Pos.to_nat (fuel (prepare EV forest)) <= 16 * t * t * t).
  { cbn [prepare fuel]; rewrite SuccNat2Pos.id_succ. nia. }
  pose proof (audit_dom_forest_prepare_width EV g p parents) as Hprepare.
  pose proof (audit_dom_forest_dfs_width EV g p parents) as Hdfs.
  fold forest in Hprepare, Hdfs |- *. repeat split; lia.
Qed.

(** * Scalar forest and combined input budgets *)

(** Forest preparation fits the thirtieth-power original-input reserve. *)
Lemma audit_default_forest_prepare_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) :
  let t := audit_default_input_scale EV g p in
  let parents := erase_virtual_parents EV (audit_default_virtual_parents EV g p) in
  audit_prepare_source_budget EV (dom_forest p parents) <=
    (1024 * 1024)%nat * Nat.pow t 30.
Proof.
  pose proof (audit_default_input_scale_bounds EV g p) as [Hscale _].
  pose proof (audit_default_forest_size_bounds EV g p) as
    [_ [_ [Hnodes [_ [Hedges [_ [Hwidth _]]]]]]].
  set (t := audit_default_input_scale EV g p) in *.
  set (parents := erase_virtual_parents EV (audit_default_virtual_parents EV g p)) in *.
  set (forest := dom_forest p parents) in *.
  set (q := 16 * t * t * t).
  cbn zeta in *; fold t parents forest in Hnodes, Hedges, Hwidth |- *.
  assert (Hq : 4 <= q) by (unfold q; nia).
  assert (Hnodes_q : length (Graph.nodes forest) <= q) by (unfold q; nia).
  assert (Hedges_q : edge_count forest <= q) by (unfold q; nia).
  assert (Hwidth_q : audit_graph_prepare_input_width EV forest <= q) by (unfold q; nia).
  pose proof (proj1 (audit_dom_prepare_stage_budgets EV forest q Hq Hnodes_q Hedges_q Hwidth_q))
    as Hbudget.
  assert (Hqpower : q <= Nat.pow t 5).
  { unfold q. cbn [Nat.pow]. nia. }
  eapply Nat.le_trans; [exact Hbudget|]. apply Nat.mul_le_mono_l.
  eapply Nat.le_trans; [apply Nat.pow_le_mono_l; exact Hqpower|].
  rewrite <- Nat.pow_mul_r. reflexivity.
Qed.

(** Forest roots and fuel give a scalar DFS count and clock ceiling. *)
Lemma audit_default_dfs_scalar_ceiling t roots fuel :
  4 <= t -> roots <= 2 * t * t -> fuel <= 16 * t * t * t ->
  let q := Nat.pow t 7 in
  4 <= q /\ 3 + roots * (40 * S fuel) <= 200 * q /\
    Pos.size_nat (Pos.of_succ_nat (S roots * S fuel)) <= 8 * q.
Proof.
  intros Hscale Hroots Hfuel q.
  set (square := t * t).
  set (cube := t * t * t).
  set (fifth := square * cube).
  assert (Hsquare : 16 <= square) by (unfold square; nia).
  assert (Hcube : 1 <= cube) by (unfold cube; nia).
  assert (Hfifth : 1 <= fifth) by (unfold fifth; nia).
  assert (Hq : q = square * fifth).
  { unfold q, fifth, square, cube. cbn [Nat.pow]. ring. }
  assert (Hqt : 16 * fifth <= q) by (rewrite Hq; nia).
  assert (Hroots' : roots <= 2 * square) by (unfold square; nia).
  assert (Hfuel' : fuel <= 16 * cube) by (unfold cube; nia).
  assert (Hrun : roots * S fuel <= 34 * fifth).
  { assert (Hmul : roots * S fuel <= (2 * square) * (17 * cube)).
    { apply Nat.mul_le_mono; lia. }
    unfold fifth; nia. }
  assert (Hclock : S roots * S fuel <= 51 * fifth).
  { assert (Hmul : S roots * S fuel <= (3 * square) * (17 * cube)).
    { apply Nat.mul_le_mono; lia. }
    unfold fifth; nia. }
  split; [nia|]. split; [nia|].
  eapply Nat.le_trans; [apply audit_dom_positive_width|].
  rewrite SuccNat2Pos.id_succ. nia.
Qed.

(** The prepared forest DFS fits the forty-second-power original-input reserve. *)
Lemma audit_default_forest_dfs_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) :
  let t := audit_default_input_scale EV g p in
  let parents := erase_virtual_parents EV (audit_default_virtual_parents EV g p) in
  let forest := dom_forest p parents in
  audit_dfs_source_budget EV forest (prepare EV forest) (Graph.entries forest) <=
    (1024 * 1024)%nat * Nat.pow t 42.
Proof.
  pose proof (audit_default_input_scale_bounds EV g p) as [Hscale _].
  pose proof (audit_default_forest_size_bounds EV g p) as
    [_ [_ [_ [Hroots [_ [Hfuel [_ Hwidth]]]]]]].
  set (t := audit_default_input_scale EV g p) in *.
  set (parents := erase_virtual_parents EV (audit_default_virtual_parents EV g p)) in *.
  set (forest := dom_forest p parents) in *.
  cbn zeta in *; fold t parents forest in Hroots, Hfuel, Hwidth |- *.
  pose proof (audit_default_dfs_scalar_ceiling t (length (Graph.entries forest))
    (Pos.to_nat (fuel (prepare EV forest))) Hscale Hroots Hfuel) as [Hq [Hcount Hclock]].
  set (q := Nat.pow t 7) in *.
  assert (Htq : t <= q).
  { clear - Hscale. unfold q. rewrite <- Nat.pow_1_r at 1.
    apply Nat.pow_le_mono_r; lia. }
  unfold audit_dfs_source_budget.
  eapply Nat.le_trans; [apply audit_dom_source_budget_from_width with (scale := q)|].
  - exact Hq.
  - exact Hcount.
  - apply Nat.max_lub; [|exact Hclock]. clearbody t q. clear - Hwidth Htq. lia.
  - unfold q. rewrite <- Nat.pow_mul_r. reflexivity.
Qed.

(** The explicit forest size and width reserve fits the fifty-fourth power. *)
Lemma audit_default_forest_reserve {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) :
  let t := audit_default_input_scale EV g p in
  let parents := erase_virtual_parents EV (audit_default_virtual_parents EV g p) in
  let forest := dom_forest p parents in
  let size := S (audit_trie_nodes parents + length (Graph.nodes forest) +
    length (Graph.entries forest) + Pos.to_nat (fuel p) +
    Pos.to_nat (fuel (prepare EV forest))) in
  let width := audit_dfs_full_input_width EV g p (Graph.entries g) +
    audit_graph_prepare_input_width EV forest +
    audit_dfs_full_input_width EV forest (prepare EV forest) (Graph.entries forest) +
    fold_right Nat.max 0 (map (fun row => Nat.max (Pos.size_nat (encode EV (fst row)))
      (Pos.size_nat (encode EV (snd row)))) (Map.elements parents)) in
  (1024 * 1024)%nat * Nat.pow size 8 * S width * S width <=
    (1024 * 1024)%nat * Nat.pow t 54.
Proof.
  pose proof (audit_default_input_scale_bounds EV g p) as
    [Hscale [Hvirtual [_ [Horigfuel [Horigwidth _]]]]].
  pose proof (audit_default_erased_parent_bounds EV g p) as [_ [_ Hparentwidth]].
  pose proof (audit_default_forest_size_bounds EV g p) as
    [_ [Hnodes [Hlive [Hroots [_ [Hfuel [Hprep Hdfs]]]]]]].
  set (t := audit_default_input_scale EV g p) in *.
  set (s := audit_virtual_lt_input_scale EV g) in *.
  set (parents := erase_virtual_parents EV (audit_default_virtual_parents EV g p)) in *.
  set (forest := dom_forest p parents) in *.
  set (size := S (audit_trie_nodes parents + length (Graph.nodes forest) +
    length (Graph.entries forest) + Pos.to_nat (fuel p) +
    Pos.to_nat (fuel (prepare EV forest)))).
  set (width := audit_dfs_full_input_width EV g p (Graph.entries g) +
    audit_graph_prepare_input_width EV forest +
    audit_dfs_full_input_width EV forest (prepare EV forest) (Graph.entries forest) +
    fold_right Nat.max 0 (map (fun row => Nat.max (Pos.size_nat (encode EV (fst row)))
      (Pos.size_nat (encode EV (snd row)))) (Map.elements parents))).
  cbn zeta in *; fold t s parents forest in Hscale, Hvirtual, Horigfuel, Horigwidth,
    Hparentwidth, Hnodes, Hlive, Hroots, Hfuel, Hprep, Hdfs |- *. fold size width.
  set (cube := t * t * t).
  assert (Hcube : 64 <= cube) by (unfold cube; clear - Hscale; nia).
  assert (Hsize : size <= 19 * cube).
  { unfold size, cube. clear - Hscale Hnodes Hlive Hroots Horigfuel Hfuel. nia. }
  assert (Hsize_power : size <= Nat.pow t 6).
  { replace (Nat.pow t 6) with (cube * cube) by (unfold cube; cbn [Nat.pow]; ring).
    clear - Hsize Hcube; nia. }
  assert (Hwidth_power : S width <= Nat.pow t 3).
  { assert (Hwidth : width <= 4 * t).
    { unfold width. clear - Horigwidth Hprep Hdfs Hparentwidth Hvirtual. lia. }
    change (S width <= t * (t * (t * 1))). clear - Hwidth Hscale; nia. }
  assert (Hpow : Nat.pow (Nat.pow t 6) 8 * Nat.pow t 3 * Nat.pow t 3 = Nat.pow t 54).
  { rewrite <- Nat.pow_mul_r. repeat rewrite <- Nat.pow_add_r. reflexivity. }
  rewrite <- Hpow.
  set (factor := (1024 * 1024)%nat). clearbody factor.
  replace (factor * (Nat.pow (Nat.pow t 6) 8 * Nat.pow t 3 * Nat.pow t 3))
    with (factor * Nat.pow (Nat.pow t 6) 8 * Nat.pow t 3 * Nat.pow t 3) by ring.
  apply Nat.mul_le_mono.
  - apply Nat.mul_le_mono.
    + apply Nat.mul_le_mono_l. apply Nat.pow_le_mono_l; exact Hsize_power.
    + exact Hwidth_power.
  - exact Hwidth_power.
Qed.

(** Five separate reserves fit the published sixty-fourth-power input budget. *)
Lemma audit_default_five_reserve factor t a b c d e :
  4 <= t -> a <= factor * Nat.pow t 54 -> b <= factor * Nat.pow t 54 ->
  c <= factor * Nat.pow t 54 -> d <= factor * Nat.pow t 54 ->
  e <= factor * Nat.pow t 54 -> a + (b + c + d + e) <= factor * Nat.pow t 64.
Proof.
  intros Ht Ha Hb Hc Hd He.
  set (power := Nat.pow t 54) in *.
  assert (Hsum : a + (b + c + d + e) <= 5 * (factor * power)).
  { clearbody power. lia. }
  assert (Hten : 5 <= Nat.pow t 10).
  { eapply Nat.le_trans with (m := Nat.pow 4 2); [cbn; lia|].
    eapply Nat.le_trans; [apply Nat.pow_le_mono_l; exact Ht|].
    apply Nat.pow_le_mono_r; lia. }
  eapply Nat.le_trans; [exact Hsum|].
  replace (Nat.pow t 64) with (power * Nat.pow t 10).
  2:{ unfold power. rewrite <- Nat.pow_add_r. reflexivity. }
  clearbody power.
  replace (5 * (factor * power)) with (factor * (power * 5)) by ring.
  apply Nat.mul_le_mono_l. apply Nat.mul_le_mono_l. exact Hten.
Qed.

(** Virtual LT plus the actual source-forest budget fit the original-input budget. *)
Lemma audit_default_search_sum_bound {V E B} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) :
  audit_dfs_callbacks_erase EV g cb ->
  let parents := erase_virtual_parents EV (audit_default_virtual_parents EV g p) in
  audit_virtual_lt_input_budget EV g +
    audit_dom_search_source_budget EV g p parents (audit_dom_search_source_counted p parents cb) <=
    audit_default_dom_input_budget EV g p.
Proof.
  intro Hcb.
  set (t := audit_default_input_scale EV g p).
  set (s := audit_virtual_lt_input_scale EV g).
  set (parents := erase_virtual_parents EV (audit_default_virtual_parents EV g p)).
  set (forest := dom_forest p parents).
  set (receipt := audit_dom_search_source_counted p parents cb).
  pose proof (audit_default_input_scale_bounds EV g p) as [Hscale [Hst [_ [_ [_ Horig]]]]].
  pose proof (audit_default_forest_receipt EV g p parents cb Hcb) as [Hforest Hindex].
  fold receipt forest in Hforest, Hindex.
  pose proof (audit_default_forest_prepare_budget EV g p) as Hprepare.
  pose proof (audit_default_forest_dfs_budget EV g p) as Hdfs.
  pose proof (audit_default_forest_reserve EV g p) as Hreserve.
  cbn zeta in *; fold t s parents forest in Hscale, Hst, Horig, Hprepare, Hdfs, Hreserve |- *.
  unfold audit_dom_search_source_budget; fold receipt.
  rewrite Hindex, Hforest. cbv zeta.
  set (factor := (1024 * 1024)%nat).
  set (power := Nat.pow t 54).
  assert (Hvirtual : audit_virtual_lt_input_budget EV g <= factor * power).
  { unfold audit_virtual_lt_input_budget; fold s factor power.
    apply Nat.mul_le_mono_l. eapply Nat.le_trans.
    - apply Nat.pow_le_mono_l; exact Hst.
    - apply Nat.pow_le_mono_r; lia. }
  assert (Hprept : audit_prepare_source_budget EV forest <= factor * power).
  { eapply Nat.le_trans; [exact Hprepare|]. fold factor power.
    apply Nat.mul_le_mono_l. apply Nat.pow_le_mono_r; lia. }
  assert (Hdfst : audit_dfs_source_budget EV forest (prepare EV forest) (Graph.entries forest) <=
    factor * power).
  { eapply Nat.le_trans; [exact Hdfs|]. fold factor power.
    apply Nat.mul_le_mono_l. apply Nat.pow_le_mono_r; lia. }
  assert (Hfactor : 1 <= factor) by (unfold factor; apply Nat.mul_pos_pos; lia).
  assert (Ht : t <= power).
  { unfold power. rewrite <- Nat.pow_1_r at 1. apply Nat.pow_le_mono_r; lia. }
  assert (Horigbudget : audit_dfs_source_budget EV g p (Graph.entries g) <= factor * power).
  { clearbody factor power. nia. }
  fold factor power in Hreserve.
  eapply (audit_default_five_reserve factor t); try eassumption.
Qed.

(** * Same-run original-input adaptation *)

(** The numerical comparison applies to the same captured LT and forest execution. *)
Lemma audit_default_captured_input_bound {V E B} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (cb : audit_virtual_base_callbacks V E B) (source : E -> V * list B)
    vp search prepare_events dfs_events semi_state semi_events virtual_parents lt_events
    parents erase_events receipt :
  audit_virtual_base_callbacks_erase EV g cb ->
  (forall edge, fst (source edge) = Graph.source g edge) ->
  audit_virtual_source_search EV g cb = (vp, (search, (prepare_events, dfs_events))) ->
  audit_semi_producer_nested_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
    vp search semi_state semi_events ->
  audit_lt_nested_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
    search (SemiState.result semi_state) virtual_parents lt_events ->
  audit_erase_virtual_nested (audit_virtual_base_encode cb) virtual_parents =
    (parents, erase_events) ->
  receipt = audit_dom_search_source_counted p parents
    (AuditDfsCallbackModel V E B (audit_virtual_base_target cb) (audit_virtual_base_encode cb)) ->
  audit_virtual_lt_input_budget EV g + audit_dom_search_source_budget EV g p parents receipt <=
    audit_default_dom_input_budget EV g p.
Proof.
  intros Hcallbacks Hsource Hsearch Hsemi Hlt Herase Hreceipt.
  pose proof (audit_virtual_source_search_holds V E B EV g p cb (fun _ => 0) Hcallbacks) as Hsame.
  rewrite Hsearch in Hsame; cbn [fst snd] in Hsame.
  destruct Hsame as [Hvp [Hresult _]]; subst vp search.
  pose proof (audit_dom_virtual_captured_states EV g p cb source semi_state semi_events
    virtual_parents lt_events Hcallbacks Hsource Hsemi Hlt) as [Hstate Hparents].
  assert (Hcanonical : virtual_parents = audit_default_virtual_parents EV g p).
  { unfold audit_default_virtual_parents. now rewrite Hstate in Hparents. }
  destruct Hcallbacks as [_ [Htarget Hencode]].
  pose proof (audit_erase_nested_correct V B EV (audit_virtual_base_encode cb) (fun _ => 0)
    virtual_parents Hencode) as Herases.
  rewrite Herase in Herases; cbn [fst snd] in Herases; destruct Herases as [Hreal _].
  rewrite Hcanonical in Hreal.
  assert (Hdom_callbacks : audit_dfs_callbacks_erase EV g
    (AuditDfsCallbackModel V E B (audit_virtual_base_target cb) (audit_virtual_base_encode cb)))
    by (split; assumption).
  pose proof (audit_default_search_sum_bound EV g p
    (AuditDfsCallbackModel V E B (audit_virtual_base_target cb) (audit_virtual_base_encode cb))
    Hdom_callbacks) as Hsum.
  cbn zeta in Hsum; rewrite <- Hreal, <- Hreceipt in Hsum. exact Hsum.
Qed.

(** The default dominator run obeys both adapted source-work bounds on its own receipts. *)
Theorem audit_default_dom_single_adapted_holds : audit_default_dom_single_adapted_statement.
Proof.
  intros V E B EV g p cb source weight encode_source out_source target_source source_source
    encode_budget out_budget target_budget source_budget Hcallbacks Hsource Hencode Hout Htarget
    Hsource_adapter.
  destruct (audit_default_dom_single_run_holds V E B EV g p cb source weight Hcallbacks Hsource)
    as [vp [search [prepare_events [dfs_events [semi_state [semi_events [virtual_parents
      [lt_events [parents [erase_events [receipt [result Hrun]]]]]]]]]]]].
  destruct Hrun as [Hsearch [Hsemi [Hlt [Herase [Hreceipt [Hresult [Htree Hwork]]]]]]].
  pose proof (audit_default_captured_input_bound EV g p cb source vp search prepare_events
    dfs_events
    semi_state semi_events virtual_parents lt_events parents erase_events receipt Hcallbacks Hsource
    Hsearch Hsemi Hlt Herase Hreceipt) as Hinput.
  pose proof (audit_default_dom_adapt_captured_run V E B EV g p cb source weight encode_source
    out_source target_source source_source encode_budget out_budget target_budget source_budget
    vp search prepare_events dfs_events semi_state semi_events virtual_parents lt_events parents
    erase_events receipt Hcallbacks Hencode Hout Htarget Hsource_adapter Hsearch Hsemi Hlt Herase
    Hreceipt Hwork Hinput) as [Hfirst Hsecond].
  exists vp, search, prepare_events, dfs_events, semi_state, semi_events, virtual_parents,
    lt_events,
    parents, erase_events, receipt, result.
  repeat split; assumption.
Qed.
