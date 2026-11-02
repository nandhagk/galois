(** * Adequacy of observation component order

    The counted order keeps the dependency graph, SCC callbacks and outer reversal together.
    For example, the final reversal is charged separately from Tarjan's result reversal.
    Builds on: FixpointAuditScheduleWrapperAdequacy and GraphAuditSccAdequacy. *)

From Stdlib Require Import List Arith PeanoNat Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare GraphScc GraphAuditBase GraphAuditDfs
  GraphAuditScc GraphAuditBaseAdequacy GraphAuditDfsAdequacy GraphAuditSccAdequacy.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointSchedule FixpointObserve
  FixpointAuditIndex FixpointAuditScheduleWrapper FixpointAuditScheduleWrapperAdequacy
  FixpointAuditObserveOrder.
Import List.ListNotations.

(** * SCC callback receipts *)

Lemma fx_order_scc_receipts X C B (EX : encoding X) (g : Graph.t X (X * X))
    (p : prepared EX g) (cb : fx_index_external_model X C B)
    (source : fx_index_external_source X C B) roots :
  fx_dep_source_laws cb source ->
  Forall (fun event => Forall (fx_observe_order_capture_source source) (snd event))
    (snd (audit_scc_source_counted p (fx_dep_dfs_cb cb) roots)).
Proof.
  intro Hlaws.
  pose proof (audit_scc_source_receipts p (fx_dep_dfs_cb cb) roots) as Hreceipts.
  eapply Forall_impl; [|exact Hreceipts].
  intros [event captures] Hitem; unfold audit_tarjan_event_bodies in Hitem; cbn [snd] in Hitem |- *.
  eapply Forall_impl; [|exact Hitem].
  intros capture Hcapture; destruct capture as [edge target body | vertex code body];
    cbn [audit_dfs_capture_receipt fx_dep_dfs_cb audit_dfs_target_model
      audit_dfs_encode_model fx_observe_order_capture_source] in Hcapture |- *.
  - inversion Hcapture; subst body; unfold fx_dep_body_source; constructor; [exact I | constructor].
  - pose proof (fx_dep_encoder_source X C B cb source vertex Hlaws) as Hbody.
    rewrite Hcapture in Hbody; exact Hbody.
Qed.

(** * SCC callback work *)

Lemma fx_order_encoder_body_bound X C A B (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B)
    (ib : fx_index_external_budget X C B) x code body :
  fx_index_external_bounded cb ib -> In x (Graph.nodes (dependency_graph EX S SS)) ->
  fx_dep_encoder cb x = (code, body) ->
  fx_dep_events_work ib body <= fx_rpo_callback_max EX S SS ib.
Proof.
  intros Hbounded Hin Hcall.
  pose proof (fx_dep_node_encoder_work X C A B EX S SS cb ib x Hbounded Hin) as Hwork.
  rewrite Hcall in Hwork; exact Hwork.
Qed.

(** A captured encoder call on a graph vertex fits the shared callback allowance. *)
Lemma fx_order_scc_encoder_capture X C A B (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B)
    (ib : fx_index_external_budget X C B) vertex captures :
  fx_index_external_bounded cb ib -> In vertex (Graph.nodes (dependency_graph EX S SS)) ->
  (exists code body, captures = [AuditGraphEncodeCapture X (X * X) (fx_dep_event X C B)
    vertex code body]) ->
  Forall (audit_dfs_capture_receipt (fx_dep_dfs_cb cb)) captures ->
  fold_right (fun capture n => audit_graph_capture_work (fx_dep_event_work ib) capture + n)
    0 captures <= fx_rpo_callback_max EX S SS ib.
Proof.
  intros Hbounded Hin [code [body ->]] Hreceipts.
  inversion Hreceipts as [|capture tail Hreceipt Htail]; subst capture tail.
  cbn [audit_dfs_capture_receipt fx_dep_dfs_cb audit_dfs_encode_model] in Hreceipt.
  pose proof (fx_order_encoder_body_bound X C A B EX S SS cb ib vertex code body Hbounded Hin
    Hreceipt) as Hwork.
  change (fx_dep_events_work ib body + 0 <= fx_rpo_callback_max EX S SS ib); lia.
Qed.

(** A captured comparison pays for both actual encoder bodies. *)
Lemma fx_order_scc_compare_captures X C A B (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B)
    (ib : fx_index_external_budget X C B) left right captures :
  fx_index_external_bounded cb ib ->
  In left (Graph.nodes (dependency_graph EX S SS)) ->
  In right (Graph.nodes (dependency_graph EX S SS)) ->
  (exists lc rc lb rb, captures = [AuditGraphEncodeCapture X (X * X) (fx_dep_event X C B)
    left lc lb; AuditGraphEncodeCapture X (X * X) (fx_dep_event X C B) right rc rb]) ->
  Forall (audit_dfs_capture_receipt (fx_dep_dfs_cb cb)) captures ->
  fold_right (fun capture n => audit_graph_capture_work (fx_dep_event_work ib) capture + n)
    0 captures <= 2 * fx_rpo_callback_max EX S SS ib.
Proof.
  intros Hbounded Hleft_key Hright_key [lc [rc [lb [rb ->]]]] Hreceipts.
  inversion Hreceipts as [|capture tail Hleft Htail]; subst capture tail.
  inversion Htail as [|capture tail Hright Hnil]; subst capture tail.
  cbn [audit_dfs_capture_receipt fx_dep_dfs_cb audit_dfs_encode_model] in Hleft, Hright.
  pose proof (fx_order_encoder_body_bound X C A B EX S SS cb ib left lc lb Hbounded Hleft_key Hleft)
    as Hleft_work.
  pose proof (fx_order_encoder_body_bound X C A B EX S SS cb ib right rc rb Hbounded
    Hright_key Hright)
    as Hright_work.
  change (fx_dep_events_work ib lb + (fx_dep_events_work ib rb + 0) <=
    2 * fx_rpo_callback_max EX S SS ib); lia.
Qed.

Lemma fx_order_scc_event_bound X C A B (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B)
    (ib : fx_index_external_budget X C B) item :
  fx_index_external_bounded cb ib ->
  audit_scc_source_event_wellformed item ->
  audit_tarjan_event_bodies (audit_dfs_capture_receipt (fx_dep_dfs_cb cb)) item ->
  audit_tarjan_event_keys (Graph.nodes (dependency_graph EX S SS)) (fst item) ->
  fold_right (fun capture n => audit_graph_capture_work (fx_dep_event_work ib) capture + n)
    0 (snd item) <= 2 * fx_rpo_callback_max EX S SS ib.
Proof.
  intros Hbounded Hshape Hreceipts Hkeys.
  pose proof (fx_rpo_max_floor X C A B EX S SS ib) as Hfloor.
  destruct item as [event captures].
  destruct event as [site | edge target | vertex region result | vertex map result |
    vertex before after | vertex number before after | vertex rest before after | helper |
    vertex region | components identifiers];
    cbn [fst snd audit_scc_source_event_wellformed audit_tarjan_event_bodies
      audit_tarjan_event_keys] in *.
  - subst captures; change (0 <= 2 * fx_rpo_callback_max EX S SS ib); lia.
  - destruct Hshape as [body ->].
    inversion Hreceipts as [|capture tail Hreceipt Htail]; subst capture tail.
    cbn [audit_dfs_capture_receipt fx_dep_dfs_cb audit_dfs_target_model] in Hreceipt.
    inversion Hreceipt; subst body.
    change (16 + 0 <= 2 * fx_rpo_callback_max EX S SS ib); lia.
  - pose proof (fx_order_scc_encoder_capture X C A B EX S SS cb ib vertex captures Hbounded Hkeys
      Hshape Hreceipts) as Hwork; lia.
  - pose proof (fx_order_scc_encoder_capture X C A B EX S SS cb ib vertex captures Hbounded Hkeys
      Hshape Hreceipts) as Hwork; lia.
  - subst captures; change (0 <= 2 * fx_rpo_callback_max EX S SS ib); lia.
  - subst captures; change (0 <= 2 * fx_rpo_callback_max EX S SS ib); lia.
  - subst captures; change (0 <= 2 * fx_rpo_callback_max EX S SS ib); lia.
  - destruct helper as [site | vertex map result | vertex map result | vertex value map |
      vertex map | left right result | left right result | left right result | input result |
      key members map]; cbn [audit_scc_source_event_wellformed audit_tarjan_helper_keys] in *;
      try (subst captures; change (0 <= 2 * fx_rpo_callback_max EX S SS ib); lia);
      try solve [pose proof (fx_order_scc_encoder_capture X C A B EX S SS cb ib vertex captures
        Hbounded Hkeys Hshape Hreceipts) as Hwork; lia].
    destruct Hkeys as [Hleft Hright].
    exact (fx_order_scc_compare_captures X C A B EX S SS cb ib left right captures Hbounded Hleft
      Hright Hshape Hreceipts).
  - pose proof (fx_order_scc_encoder_capture X C A B EX S SS cb ib vertex captures Hbounded Hkeys
      Hshape Hreceipts) as Hwork; lia.
  - subst captures; change (0 <= 2 * fx_rpo_callback_max EX S SS ib); lia.
Qed.

Lemma fx_order_scc_keys_incl X E vertices nodes (event : audit_tarjan_call X E) :
  incl vertices nodes -> audit_tarjan_event_keys vertices event ->
  audit_tarjan_event_keys nodes event.
Proof.
  intros Hincl Hkeys; destruct event as [site | edge target | vertex region result |
    vertex map result | vertex before after | vertex number before after |
    vertex rest before after | helper | vertex region | components identifiers];
    cbn [audit_tarjan_event_keys] in *;
    try exact I; try (apply Hincl; exact Hkeys).
  destruct helper; cbn [audit_tarjan_helper_keys] in *; try exact I;
    try (apply Hincl; exact Hkeys).
  destruct Hkeys as [Hleft Hright]; split; apply Hincl; assumption.
Qed.

(** The total SCC callback work is the sum of its per-event allowances. *)
Lemma fx_order_scc_body_sum X C B (ib : fx_index_external_budget X C B)
    (events : list (audit_tarjan_nested_event X (X * X)
      (audit_graph_callback_capture X (X * X) (fx_dep_event X C B)))) maximum :
  Forall (fun item => fold_right
    (fun capture n => audit_graph_capture_work (fx_dep_event_work ib) capture + n)
    0 (snd item) <= maximum) events ->
  audit_scc_source_body_work (fx_dep_event_work ib) events <= length events * maximum.
Proof.
  intro Hbounds; induction Hbounds as [|item rest Hitem Hrest IH].
  - reflexivity.
  - change (fold_right
      (fun capture n => audit_graph_capture_work (fx_dep_event_work ib) capture + n)
      0 (snd item) + audit_scc_source_body_work (fx_dep_event_work ib) rest <=
      Datatypes.S (length rest) * maximum).
    rewrite Nat.mul_succ_l, Nat.add_comm; apply Nat.add_le_mono; assumption.
Qed.

Lemma fx_order_scc_body_bound X C A B (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B)
    (ib : fx_index_external_budget X C B) :
  fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
  let g := dependency_graph EX S SS in let p := prepare EX g in
  let events := snd (audit_scc_source_counted p (fx_dep_dfs_cb cb) (Graph.nodes g)) in
  audit_scc_source_body_work (fx_dep_event_work ib) events <=
    2 * length events * fx_rpo_callback_max EX S SS ib.
Proof.
  intros Herase Hbounded; cbn zeta.
  set (g := dependency_graph EX S SS); set (p := prepare EX g).
  pose proof (dependency_graph_ready EX S SS) as Hready; fold g p in Hready.
  pose proof (fx_dep_dfs_erases X C A B EX S SS cb Herase) as Hcallbacks; fold g in Hcallbacks.
  pose proof (audit_scc_source_correct X (X * X)%type (fx_dep_event X C B) EX g p
    (fx_dep_dfs_cb cb) (fx_dep_event_work ib) (Graph.nodes g) Hcallbacks) as Hsource.
  pose proof (audit_scc_source_receipts p (fx_dep_dfs_cb cb) (Graph.nodes g)) as Hreceipts.
  pose proof (audit_scc_source_erases p (fx_dep_dfs_cb cb) (Graph.nodes g) Hcallbacks) as Herases.
  pose proof (audit_scc_counted_keys p (Graph.nodes g)) as Hkeys.
  destruct (audit_scc_source_counted p (fx_dep_dfs_cb cb) (Graph.nodes g)) as [result events]
    eqn:Hcall; cbn [fst snd] in Hsource, Hreceipts, Herases |- *.
  destruct Hsource as [_ [Hshape _]].
  destruct (audit_scc_within_counted p (Graph.nodes g)) as [original trace]; cbn [fst snd] in
    Hkeys, Herases.
  inversion Herases as [[Hresult Htrace]]; subst trace.
  assert (Hincl : incl (Graph.nodes g ++ map (Graph.target g)
    (flat_map snd (Map.elements (out_index p)))) (Graph.nodes g)).
  { intros x Hin; apply in_app_iff in Hin; destruct Hin as [Hin | Hin]; [exact Hin |].
    apply in_map_iff in Hin; destruct Hin as [edge [Heq Hedge]]; subst x.
    unfold p in Hedge.
    exact (fx_dep_prepared_targets_nodes X (X * X)%type EX g edge Hready Hedge). }
  assert (Hbounds : Forall (fun item =>
    fold_right (fun capture n => audit_graph_capture_work (fx_dep_event_work ib) capture + n)
      0 (snd item) <= 2 * fx_rpo_callback_max EX S SS ib) events).
  { apply Forall_forall; intros item Hin.
    apply Forall_forall with (x := item) in Hshape; [|exact Hin].
    apply Forall_forall with (x := item) in Hreceipts; [|exact Hin].
    assert (Hkey : audit_tarjan_event_keys (Graph.nodes g) (fst item)).
    { eapply fx_order_scc_keys_incl; [exact Hincl |].
      apply Forall_forall with (x := fst item) in Hkeys; [exact Hkeys |].
      apply in_map; exact Hin. }
    eapply fx_order_scc_event_bound;
      [exact Hbounded | exact Hshape | exact Hreceipts | exact Hkey]. }
  pose proof (fx_order_scc_body_sum X C B ib events (2 * fx_rpo_callback_max EX S SS ib) Hbounds)
    as Hsum.
  replace (2 * length events * fx_rpo_callback_max EX S SS ib) with
    (length events * (2 * fx_rpo_callback_max EX S SS ib)) by ring.
  exact Hsum.
Qed.

(** * Ordering composition *)

(** The order execution returns the source SCC order within its input-derived budget. *)
Theorem fx_observe_order_correct : fx_observe_order_statement.
Proof.
  intros X C A B EX S SS cb ib Herase Hbounded.
  pose proof (fx_dep_build_erasure_correct X C A B EX S SS cb Herase) as Hbuild.
  pose proof (fx_dep_build_bound_correct X C A B EX S SS cb ib Herase Hbounded) as Hbuild_work.
  unfold fx_observe_order in Hbuild, Hbuild_work |- *.
  destruct (fx_dep_graph_build EX S SS cb) as [[g ix] graph_events].
  cbn [fst snd] in Hbuild, Hbuild_work; destruct Hbuild as [Hg Hix]; subst g ix.
  pose proof (audit_prepare_source_correct X (X * X)%type (fx_dep_event X C B) EX
    (dependency_graph EX S SS) (fx_dep_prepare_cb cb (index_system EX S SS))
    (fx_dep_event_work ib) (fx_dep_prepare_erases X C A B EX S SS cb Herase)) as Hprepare.
  pose proof (fx_dep_prepare_body_bound X C A B EX S SS cb ib Herase Hbounded) as Hprepare_body.
  destruct (audit_prepare_source_counted EX (dependency_graph EX S SS)
    (fx_dep_prepare_cb cb (index_system EX S SS))) as [p prepare_events].
  cbn [fst snd] in Hprepare, Hprepare_body.
  destruct Hprepare as [Hp [Hprepare_count Hprepare_work]].
  subst p.
  pose proof (audit_scc_source_correct X (X * X)%type (fx_dep_event X C B) EX
    (dependency_graph EX S SS) (prepare EX (dependency_graph EX S SS)) (fx_dep_dfs_cb cb)
    (fx_dep_event_work ib) (Graph.nodes (dependency_graph EX S SS))
    (fx_dep_dfs_erases X C A B EX S SS cb Herase)) as Hscc.
  pose proof (fx_order_scc_body_bound X C A B EX S SS cb ib Herase Hbounded) as Hscc_body.
  destruct (audit_scc_source_counted (prepare EX (dependency_graph EX S SS)) (fx_dep_dfs_cb cb)
    (Graph.nodes (dependency_graph EX S SS))) as [result scc_events]
    eqn:Hscc_call.
  cbn zeta in Hscc_body; rewrite Hscc_call in Hscc_body.
  cbn [fst snd] in Hscc, Hscc_body; destruct Hscc as [Hresult [_ [Hscc_count Hscc_work]]].
  change (result = scc (prepare EX (dependency_graph EX S SS))) in Hresult; subst result.
  split; [reflexivity |].
  unfold fx_observe_order_work, fx_observe_order_budget.
  cbn [fold_right fx_observe_order_event_work].
  set (maximum := fx_rpo_callback_max EX S SS ib) in *.
  set (prepare_limit := audit_graph_prepare_full_event_bound (dependency_graph EX S SS)) in *.
  set (scc_limit := audit_tarjan_input_event_bound (prepare EX (dependency_graph EX S SS))
    (Graph.nodes (dependency_graph EX S SS))) in *.
  clearbody maximum prepare_limit scc_limit.
  nia.
Qed.

(** Ordering retains every graph callback body from the same preparation and SCC traversal. *)
Theorem fx_observe_order_source : fx_observe_order_source_statement.
Proof.
  intros X C A B EX S SS cb ib source Herase Hbounded Hlaws.
  pose proof (fx_observe_order_correct X C A B EX S SS cb ib Herase Hbounded) as Hcorrect.
  pose proof (fx_dep_build_source X C A B EX S SS cb source Hlaws) as Hbuild.
  unfold fx_observe_order in Hcorrect, Hbuild |- *.
  destruct (fx_dep_graph_build EX S SS cb) as [[g ix] graph_events].
  pose proof (fx_dep_prepare_source_all X C B EX g cb source ix Hlaws) as Hprepare.
  destruct (audit_prepare_source_counted EX g (fx_dep_prepare_cb cb ix)) as [p prepare_events].
  pose proof (fx_order_scc_receipts X C B EX g p cb source (Graph.nodes g) Hlaws) as Hscc.
  destruct (audit_scc_source_counted p (fx_dep_dfs_cb cb) (Graph.nodes g)) as [result scc_events]
    eqn:Hscc_call.
  cbn [fst snd] in Hcorrect, Hbuild, Hprepare, Hscc |- *.
  split; [|exact Hcorrect].
  constructor; [exact Hbuild |].
  constructor; [exact Hprepare |].
  constructor; [exact Hscc |].
  constructor; [exact I | constructor].
Qed.
