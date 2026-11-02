(** * Nested solver phase derivations

    These proofs connect the counted phases to their same-run derivation.
    For example, the machine receives the plan produced by the preceding phase.
    Builds on: FixpointAuditNested. *)

From Stdlib Require Import List PArith PeanoNat Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap.
From Galois.Graph Require Import GraphCore GraphPrepare GraphWto GraphAuditBase GraphAuditDfs
  GraphAuditScc GraphAuditSccAdequacy GraphAuditDfsAdequacy GraphAuditWto
  GraphAuditBaseAdequacy GraphAuditWtoAdequacy.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointSchedule FixpointNested
  FixpointAuditIndex
  FixpointAuditScheduleWrapper FixpointAuditScheduleWrapperAdequacy
  FixpointAuditNestedPlan FixpointAuditNestedPlanAdequacy FixpointAuditNestedMachine
  FixpointAuditNestedMachineAdequacy FixpointAuditNested.
Import List.ListNotations.

(** * Existence of a phase derivation *)

(** Every counted execution supplies its actual phase results to the model relation. *)
Theorem fx_nested_run_model_total : fx_nested_run_model_total_statement.
Proof.
  unfold fx_nested_run_model_total_statement, fx_nested_run_counted.
  intros X C A B EX L mode S SS cb fuel.
  destruct (fx_dep_graph_build EX S SS cb) as [[graph ix] graph_events] eqn:Hgraph.
  destruct (audit_prepare_source_counted EX graph (fx_dep_prepare_cb cb ix))
    as [prepared prepare_events] eqn:Hprepare.
  destruct (audit_wto_source_counted prepared (fx_dep_dfs_cb cb))
    as [tokens wto_events] eqn:Hwto.
  destruct (fx_nested_plan_from_tokens EX S tokens) as [plan plan_events] eqn:Hplan.
  destruct (fx_nested_loop EX L plan mode S fuel (nested_start plan))
    as [result machine_events] eqn:Hmachine.
  econstructor; eassumption.
Qed.

(** The counted phases return the native nested solver result. *)
Theorem fx_nested_run_erasure : fx_nested_run_erasure_statement.
Proof.
  unfold fx_nested_run_erasure_statement.
  intros X C A B EX EC L mode S SS cb fuel Herase.
  pose proof (fx_dep_build_erasure_correct X C A B EX S SS cb Herase) as Hbuild.
  unfold fx_nested_run_counted in *.
  destruct (fx_dep_graph_build EX S SS cb) as [[graph ix] graph_events].
  cbn [fst snd] in Hbuild; destruct Hbuild as [Hgraph Hix]; subst graph ix.
  pose proof (audit_prepare_source_correct X (X * X)%type (fx_dep_event X C B) EX
    (dependency_graph EX S SS) (fx_dep_prepare_cb cb (index_system EX S SS)) (fun _ => 0)
    (fx_dep_prepare_erases X C A B EX S SS cb Herase)) as Hprepare.
  destruct (audit_prepare_source_counted EX (dependency_graph EX S SS)
    (fx_dep_prepare_cb cb (index_system EX S SS))) as [prepared prepare_events].
  cbn [fst snd] in Hprepare; destruct Hprepare as [Hprepared _]; subst prepared.
  pose proof (audit_wto_source_holds X (X * X)%type (fx_dep_event X C B) EX
    (dependency_graph EX S SS) (prepare EX (dependency_graph EX S SS)) (fx_dep_dfs_cb cb)
    (fun _ => 0) (fx_dep_dfs_erases X C A B EX S SS cb Herase)) as Hwto.
  destruct (audit_wto_source_counted (prepare EX (dependency_graph EX S SS)) (fx_dep_dfs_cb cb))
    as [tokens wto_events] eqn:Hwto_call.
  cbn [fst snd] in Hwto; destruct Hwto as [Htokens _].
  change (tokens = wto_total (prepare EX (dependency_graph EX S SS))) in Htokens; subst tokens.
  pose proof (fx_nested_plan_erases X C A EX S (wto_total (prepare EX (dependency_graph EX S SS))))
    as Hplan.
  destruct (fx_nested_plan_from_tokens EX S (wto_total (prepare EX (dependency_graph EX S SS))))
    as [plan plan_events].
  cbn [fst snd] in Hplan; change (plan = nested_prepare EX S SS) in Hplan; subst plan.
  pose proof (fx_nested_loop_erases EX L (nested_prepare EX S SS) mode S fuel
    (nested_start (nested_prepare EX S SS))) as Hmachine.
  destruct (fx_nested_loop EX L (nested_prepare EX S SS) mode S fuel
    (nested_start (nested_prepare EX S SS))) as [result machine_events].
  cbn [fst snd] in Hmachine; unfold nested_run; now rewrite <- Hmachine.
Qed.

Lemma fx_nested_run_model_agrees X C A B EX L mode (S : System.t X C A) SS
    (cb : fx_index_external_model X C B) fuel out events :
  fx_nested_run_model_relation EX L mode S SS cb fuel out events ->
  fx_nested_run_counted EX L mode S SS cb fuel = (out, events).
Proof.
  intro Hmodel; inversion Hmodel as
    [graph ix graph_events prepared prepare_events tokens wto_events plan plan_events
      result machine_events Hgraph Hprepare Hwto Hplan Hmachine]; subst out events.
  unfold fx_nested_run_counted; rewrite Hgraph, Hprepare, Hwto, Hplan, Hmachine; reflexivity.
Qed.

(** * WTO callback-body bounds *)

Lemma fx_nested_encode_receipt_bound X C A B (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B)
    (ib : fx_index_external_budget X C B) x code body :
  fx_index_external_bounded cb ib ->
  In x (Graph.nodes (dependency_graph EX S SS)) ->
  fx_dep_encoder cb x = (code, body) ->
  fx_dep_events_work ib body <= fx_rpo_callback_max EX S SS ib.
Proof.
  intros Hbounded Hin Hcall.
  pose proof (fx_dep_node_encoder_work X C A B EX S SS cb ib x Hbounded Hin) as Hwork.
  rewrite Hcall in Hwork; exact Hwork.
Qed.

Lemma fx_nested_wto_body_sum X C B (ib : fx_index_external_budget X C B)
    (events : list (audit_wto_nested_event X (X * X)
      (audit_graph_callback_capture X (X * X) (fx_dep_event X C B)))) maximum :
  Forall (fun item =>
    fold_right (fun capture n => audit_graph_capture_work (fx_dep_event_work ib) capture + n)
      0 (snd item) <= 2 * maximum) events ->
  audit_wto_source_body_work (fx_dep_event_work ib) events <= 2 * length events * maximum.
Proof.
  intro Hbounds; induction Hbounds as [|item rest Hitem Hrest IH].
  - reflexivity.
  - change (fold_right (fun capture n =>
      audit_graph_capture_work (fx_dep_event_work ib) capture + n) 0 (snd item) +
      audit_wto_source_body_work (fx_dep_event_work ib) rest <=
      2 * Datatypes.S (length rest) * maximum).
    eapply Nat.le_trans with (m := 2 * maximum + 2 * length rest * maximum).
    + apply Nat.add_le_mono; assumption.
    + nia.
Qed.

(** Bound a singleton encoder receipt using its actual vertex. *)
Local Ltac fx_wto_single_encoder X C A B EX S SS cb ib maximum Hbounded Hshape Hreceipts captures :=
  let code := fresh "captured_code" in let body := fresh "captured_body" in
  destruct Hshape as [code [body Hshape]]; subst captures;
  inversion Hreceipts as [|capture tail Hreceipt Htail]; subst capture tail;
  cbn [audit_dfs_capture_receipt fx_dep_dfs_cb audit_dfs_encode_model] in Hreceipt;
  match goal with
  | Hnode : In ?vertex _, Hcall : fx_dep_encoder _ ?vertex = (?code, ?body) |- _ =>
    pose proof (fx_nested_encode_receipt_bound X C A B EX S SS cb ib vertex code body
      Hbounded Hnode Hcall) as Hbody; fold maximum in Hbody
  end;
  change (fx_dep_events_work ib body + 0 <= 2 * maximum); lia.

(** Bound a singleton target receipt, whose actual body is one case event. *)
Local Ltac fx_wto_single_target EX S SS ib maximum Hshape Hreceipts captures :=
  destruct Hshape as [body Hshape]; subst captures;
  inversion Hreceipts as [|capture tail Hreceipt Htail]; subst capture tail;
  cbn [audit_dfs_capture_receipt fx_dep_dfs_cb audit_dfs_target_model] in Hreceipt;
  inversion Hreceipt; subst body;
  change (16 + 0 <= 2 * maximum); lia.

Lemma fx_nested_wto_event_body_bound X C A B (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B)
    (ib : fx_index_external_budget X C B) item :
  fx_index_external_bounded cb ib ->
  audit_wto_source_event_wellformed item -> audit_wto_event_receipts (fx_dep_dfs_cb cb) item ->
  audit_wto_event_keys (Graph.nodes (dependency_graph EX S SS)) (fst item) ->
  fold_right (fun capture n => audit_graph_capture_work (fx_dep_event_work ib) capture + n)
    0 (snd item) <= 2 * fx_rpo_callback_max EX S SS ib.
Proof.
  intros Hbounded Hshape Hreceipts Hkeys.
  pose proof (fx_rpo_max_floor X C A B EX S SS ib) as Hfloor.
  set (maximum := fx_rpo_callback_max EX S SS ib) in *.
  destruct item as [event captures].
  destruct event as [site|dfs|scc|v m result|v m result|v value m|before after|
    a b result|v code|edge vertex|a b result|len depth|size];
    cbn [fst snd audit_wto_source_event_wellformed audit_wto_event_keys] in *.
  - subst captures; change (0 <= 2 * maximum); lia.
  - pose proof (fx_dep_dfs_event_work X C A B EX S SS cb ib (dfs, captures) Hbounded Hshape
      Hreceipts Hkeys) as Hbody; cbn [snd] in Hbody; fold maximum in Hbody; lia.
  - destruct scc as [site|edge vertex|v region result|v map result|v before after|
      v n before after|v rest before after|helper|v before|components identifiers];
      cbn [audit_scc_source_event_wellformed audit_tarjan_event_keys] in *.
    + subst captures; change (0 <= 2 * maximum); lia.
    + fx_wto_single_target EX S SS ib maximum Hshape Hreceipts captures.
    + fx_wto_single_encoder X C A B EX S SS cb ib maximum Hbounded Hshape Hreceipts captures.
    + fx_wto_single_encoder X C A B EX S SS cb ib maximum Hbounded Hshape Hreceipts captures.
    + subst captures; change (0 <= 2 * maximum); lia.
    + subst captures; change (0 <= 2 * maximum); lia.
    + subst captures; change (0 <= 2 * maximum); lia.
    + destruct helper as [site|v map result|v map result|v value map|v set|
        left right result|left right result|left right result|input result|key members map];
        cbn [audit_scc_source_event_wellformed audit_tarjan_helper_keys] in *.
      * subst captures; change (0 <= 2 * maximum); lia.
      * fx_wto_single_encoder X C A B EX S SS cb ib maximum Hbounded Hshape Hreceipts captures.
      * fx_wto_single_encoder X C A B EX S SS cb ib maximum Hbounded Hshape Hreceipts captures.
      * fx_wto_single_encoder X C A B EX S SS cb ib maximum Hbounded Hshape Hreceipts captures.
      * fx_wto_single_encoder X C A B EX S SS cb ib maximum Hbounded Hshape Hreceipts captures.
      * destruct Hkeys as [Hleft Hright].
        destruct Hshape as [left_code [right_code [left_body [right_body Hshape]]]]; subst captures.
        inversion Hreceipts as [|first tail Hfirst Htail]; subst first tail.
        inversion Htail as [|second rest Hsecond Hnil]; subst second rest.
        cbn [audit_dfs_capture_receipt fx_dep_dfs_cb audit_dfs_encode_model] in Hfirst, Hsecond.
        pose proof (fx_nested_encode_receipt_bound X C A B EX S SS cb ib left left_code left_body
          Hbounded Hleft Hfirst) as Hleft_work.
        fold maximum in Hleft_work;
        pose proof (fx_nested_encode_receipt_bound X C A B EX S SS cb ib right right_code right_body
          Hbounded Hright Hsecond) as Hright_work.
        fold maximum in Hright_work;
        change (fx_dep_events_work ib left_body + (fx_dep_events_work ib right_body + 0) <=
          2 * maximum); lia.
      * subst captures; change (0 <= 2 * maximum); lia.
      * subst captures; change (0 <= 2 * maximum); lia.
      * subst captures; change (0 <= 2 * maximum); lia.
      * subst captures; change (0 <= 2 * maximum); lia.
    + fx_wto_single_encoder X C A B EX S SS cb ib maximum Hbounded Hshape Hreceipts captures.
    + subst captures; change (0 <= 2 * maximum); lia.
  - fx_wto_single_encoder X C A B EX S SS cb ib maximum Hbounded Hshape Hreceipts captures.
  - fx_wto_single_encoder X C A B EX S SS cb ib maximum Hbounded Hshape Hreceipts captures.
  - fx_wto_single_encoder X C A B EX S SS cb ib maximum Hbounded Hshape Hreceipts captures.
  - subst captures; change (0 <= 2 * maximum); lia.
  - subst captures; change (0 <= 2 * maximum); lia.
  - destruct Hshape as [body Hshape]; subst captures.
    inversion Hreceipts as [|capture tail Hreceipt Htail]; subst capture tail.
    cbn [audit_dfs_capture_receipt fx_dep_dfs_cb audit_dfs_encode_model] in Hreceipt.
    pose proof (fx_nested_encode_receipt_bound X C A B EX S SS cb ib v code body
      Hbounded Hkeys Hreceipt) as Hbody.
    fold maximum in Hbody.
    change (fx_dep_events_work ib body + 0 <= 2 * maximum); lia.
  - fx_wto_single_target EX S SS ib maximum Hshape Hreceipts captures.
  - subst captures; change (0 <= 2 * maximum); lia.
  - subst captures; change (0 <= 2 * maximum); lia.
  - subst captures; change (0 <= 2 * maximum); lia.
Qed.

Lemma fx_nested_wto_keys_incl X E vertices nodes (event : audit_wto_call X E) :
  incl vertices nodes -> audit_wto_event_keys vertices event -> audit_wto_event_keys nodes event.
Proof.
  intros Hincl Hkeys.
  destruct event as [site|dfs|scc|v m result|v m result|v value m|before after|
    a b result|v code|edge vertex|a b result|len depth|size];
    cbn [audit_wto_event_keys] in *; try exact I; try (apply Hincl; exact Hkeys).
  - eapply fx_dep_dfs_keys_incl; eassumption.
  - destruct scc as [site|edge vertex|v region result|v map result|v before after|
      v n before after|v rest before after|helper|v before|components identifiers];
      cbn [audit_tarjan_event_keys] in *; try exact I; try (apply Hincl; exact Hkeys).
    destruct helper; cbn [audit_tarjan_helper_keys] in *; try exact I;
      try (apply Hincl; exact Hkeys).
    destruct Hkeys as [Hleft Hright]; split; apply Hincl; assumption.
Qed.

Lemma fx_nested_wto_body_bound X C A B (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B)
    (ib : fx_index_external_budget X C B) :
  fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
  let g := dependency_graph EX S SS in let p := prepare EX g in
  let events := snd (audit_wto_source_counted p (fx_dep_dfs_cb cb)) in
  audit_wto_source_body_work (fx_dep_event_work ib) events <=
    2 * length events * fx_rpo_callback_max EX S SS ib.
Proof.
  intros Herase Hbounded; cbn zeta.
  set (g := dependency_graph EX S SS); set (p := prepare EX g).
  pose proof (dependency_graph_ready EX S SS) as Hready; fold g p in Hready.
  pose proof (fx_dep_dfs_erases X C A B EX S SS cb Herase) as Hcallbacks; fold g in Hcallbacks.
  pose proof (audit_wto_source_event_correspondence_holds X (X * X)%type (fx_dep_event X C B)
    EX g p (fx_dep_dfs_cb cb) Hcallbacks) as Hshape.
  pose proof (audit_wto_source_receipts p (fx_dep_dfs_cb cb)) as Hreceipts.
  pose proof (audit_wto_source_erases p (fx_dep_dfs_cb cb) Hcallbacks) as Hsource.
  pose proof (audit_wto_counted_keys p) as Hkeys.
  destruct (audit_wto_source_counted p (fx_dep_dfs_cb cb)) as [tokens events].
  cbn [fst snd] in Hshape, Hreceipts, Hsource |- *; destruct Hshape as [Hshape _].
  destruct (audit_wto_counted p) as [original original_events]; cbn [fst snd] in Hsource, Hkeys.
  inversion Hsource as [[Hresult Htrace]]; subst original_events.
  assert (Hincl : incl (Graph.entries g ++ map (Graph.target g)
    (flat_map snd (Map.elements (out_index p)))) (Graph.nodes g)).
  { intros x Hin; apply in_app_iff in Hin; destruct Hin as [Hin|Hin].
    - exact (entries_in (proj1 Hready) x Hin).
    - apply in_map_iff in Hin; destruct Hin as [edge [Heq Hedge]]; subst x.
      unfold p in Hedge; eapply fx_dep_prepared_targets_nodes; eassumption. }
  apply fx_nested_wto_body_sum; apply Forall_forall; intros item Hin.
  apply Forall_forall with (x := item) in Hshape; [|exact Hin].
  apply Forall_forall with (x := item) in Hreceipts; [|exact Hin].
  assert (Hkey : audit_wto_event_keys (Graph.nodes g) (fst item)).
  { eapply fx_nested_wto_keys_incl; [exact Hincl|].
    apply Forall_forall with (x := fst item) in Hkeys; [exact Hkeys|].
    apply in_map; exact Hin. }
  eapply fx_nested_wto_event_body_bound; eassumption.
Qed.

(** The complete phase trace is bounded from the original system and its native intermediates. *)
Theorem fx_nested_run_input_bound : fx_nested_run_input_bound_statement.
Proof.
  intros X C A B EX EC L mode S SS cb ib fuel Herase Hbounded.
  pose proof (fx_nested_run_erasure X C A B EX EC L mode S SS cb fuel Herase) as Hresult.
  pose proof (fx_dep_build_erasure_correct X C A B EX S SS cb Herase) as Hbuild.
  pose proof (fx_dep_build_bound_correct X C A B EX S SS cb ib Herase Hbounded) as Hbuild_work.
  unfold fx_nested_run_counted in *.
  destruct (fx_dep_graph_build EX S SS cb) as [[graph ix] graph_events].
  cbn [fst snd] in Hbuild, Hbuild_work; destruct Hbuild as [Hgraph Hix]; subst graph ix.
  pose proof (audit_prepare_source_correct X (X * X)%type (fx_dep_event X C B) EX
    (dependency_graph EX S SS) (fx_dep_prepare_cb cb (index_system EX S SS))
    (fx_dep_event_work ib) (fx_dep_prepare_erases X C A B EX S SS cb Herase)) as Hprepare.
  pose proof (fx_dep_prepare_body_bound X C A B EX S SS cb ib Herase Hbounded) as Hprepare_body.
  destruct (audit_prepare_source_counted EX (dependency_graph EX S SS)
    (fx_dep_prepare_cb cb (index_system EX S SS))) as [prepared prepare_events].
  cbn [fst snd] in Hprepare, Hprepare_body; destruct Hprepare as [Hprepared [Hprepare_count
    Hprepare_work]].
  subst prepared.
  pose proof (audit_wto_source_holds X (X * X)%type (fx_dep_event X C B) EX
    (dependency_graph EX S SS) (prepare EX (dependency_graph EX S SS)) (fx_dep_dfs_cb cb)
    (fx_dep_event_work ib) (fx_dep_dfs_erases X C A B EX S SS cb Herase)) as Hwto.
  pose proof (fx_nested_wto_body_bound X C A B EX S SS cb ib Herase Hbounded) as Hwto_body.
  destruct (audit_wto_source_counted (prepare EX (dependency_graph EX S SS)) (fx_dep_dfs_cb cb))
    as [tokens wto_events] eqn:Hwto_call.
  cbn zeta in Hwto_body; rewrite Hwto_call in Hwto_body.
  cbn [fst snd] in Hwto, Hwto_body; destruct Hwto as [Htokens [Hwto_count Hwto_work]].
  change (tokens = wto_total (prepare EX (dependency_graph EX S SS))) in Htokens; subst tokens.
  pose proof (fx_nested_plan_input_bound X C A EX S
    (wto_total (prepare EX (dependency_graph EX S SS)))) as Hplan.
  destruct (fx_nested_plan_from_tokens EX S (wto_total (prepare EX (dependency_graph EX S SS))))
    as [plan plan_events].
  cbn [fst snd] in Hplan; destruct Hplan as [Hplan Hplan_work].
  change (plan = nested_prepare EX S SS) in Hplan; subst plan.
  pose proof (fx_nested_loop_input_bound X C A EX EC L (nested_prepare EX S SS) mode S fuel
    (nested_start (nested_prepare EX S SS))) as Hmachine.
  destruct (fx_nested_loop EX L (nested_prepare EX S SS) mode S fuel
    (nested_start (nested_prepare EX S SS))) as [result machine_events].
  cbn [fst snd] in Hmachine, Hresult |- *; destruct Hmachine as [_ Hmachine_work].
  split; [exact Hresult|].
  unfold fx_nested_whole_work, fx_nested_whole_event_work, fx_nested_run_input_budget.
  cbn [fold_right].
  set (maximum := fx_rpo_callback_max EX S SS ib) in *.
  set (count := audit_graph_prepare_full_event_bound (dependency_graph EX S SS) +
    audit_wto_input_event_bound (prepare EX (dependency_graph EX S SS))) in *.
  assert (Hcounts : length prepare_events + 2 * length wto_events <= 2 * count).
  { subst count; lia. }
  assert (Hproduct : (length prepare_events + 2 * length wto_events) * maximum <=
    2 * count * maximum).
  { apply Nat.mul_le_mono_r; exact Hcounts. }
  nia.
Qed.

(** A model derivation has the same result and input bound as its counted execution. *)
Theorem fx_nested_run_model_correct : fx_nested_run_model_correct_statement.
Proof.
  intros X C A B EX EC L mode S SS cb ib fuel out events Herase Hbounded Hmodel.
  pose proof (fx_nested_run_model_agrees X C A B EX L mode S SS cb fuel out events Hmodel) as Hrun.
  pose proof (fx_nested_run_input_bound X C A B EX EC L mode S SS cb ib fuel Herase Hbounded)
    as Hbound.
  now rewrite Hrun in Hbound.
Qed.
