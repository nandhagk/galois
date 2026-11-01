(** * Declared worklist callback adequacy

    Callback receipts retain the operands and results of each modeled source invocation.
    For example, each captured queue encoder entry has its own source body and allowance.
    Builds on: FixpointAuditWorklistBudgetAdequacy and recorded queue receipts. *)

From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsHeap
  CollectionsAuditCost CollectionsAuditTrie CollectionsAuditQueue CollectionsAuditQueueAdequacy.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointWorklist
  FixpointTotal FixpointAuditWorklist FixpointAuditWorklistBudget FixpointAuditWorklistCallbacks
  FixpointAuditWorklistAdequacy FixpointAuditWorklistBudgetAdequacy.
Import List.ListNotations.

(** * Budgets of the actual callback bodies *)

Lemma fx_queue_body_receipts_bound X C A B (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) entries bodies :
  (forall c result body, fx_source_encode_c source c result body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_encode_c budget c) ->
  Forall2 (fx_queue_encoder_source source) entries bodies ->
  fold_right (fun body n => fx_one_body_work (fx_body_weight budget) body + n) 0 bodies <=
    fold_right (fun entry n => fx_queue_entry_budget budget entry + n) 0 entries.
Proof.
  intros Hbound Hreceipts; induction Hreceipts as [|[c code] body entries bodies Hbody Hrest IH].
  - reflexivity.
  - cbn [fx_queue_encoder_source fx_queue_entry_budget] in *.
    specialize (Hbound c code body Hbody).
    change (fx_one_body_work (fx_body_weight budget) body +
      fold_right (fun body n => fx_one_body_work (fx_body_weight budget) body + n) 0 bodies <=
      fx_budget_encode_c budget c +
      fold_right (fun entry n => fx_queue_entry_budget budget entry + n) 0 entries).
    lia.
Qed.

Lemma fx_callback_call_bound X C A B (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) call bodies :
  fx_declared_callback_bounded source budget -> fx_declared_call_source source call bodies ->
  fold_right (fun body n => fx_one_body_work (fx_body_weight budget) body + n) 0 bodies <=
    fx_declared_external_call_budget budget call.
Proof.
  intros [Hx [Hc [Htarget [Hpriority [Hpoint [Hrhs [Hcont [Hleb [Hjoin Hwiden]]]]]]]]] Hsource.
  destruct call; cbn [fx_declared_call_source fx_declared_external_call_budget] in Hsource |- *;
    try (destruct Hsource as [witness [-> Hbody]];
      first [pose proof (Hx _ _ _ Hbody) | pose proof (Htarget _ _ _ Hbody) |
        pose proof (Hpriority _ _ _ Hbody) | pose proof (Hpoint _ _ _ Hbody) |
        pose proof (Hrhs _ _ _ Hbody) | pose proof (Hcont _ _ _ _ Hbody) |
        pose proof (Hleb _ _ _ _ Hbody) | pose proof (Hjoin _ _ _ _ Hbody) |
        pose proof (Hwiden _ _ _ _ Hbody)]; simpl in *; lia).
  all: eapply fx_queue_body_receipts_bound; eassumption.
Qed.

Lemma fx_trace_body_bound X C A B (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) events bodies :
  fx_declared_callback_bounded source budget -> fx_declared_trace_source source events bodies ->
  fx_declared_body_work (fx_body_weight budget) bodies <=
    fx_declared_external_trace_budget budget events.
Proof.
  intros Hbound Htrace; unfold fx_declared_trace_source in Htrace.
  induction Htrace as [|event group events bodies Hsource Htrace IH].
  - reflexivity.
  - destruct event as [site operands|call|site operands|bit|site operands];
      cbn [fx_declared_event_source] in Hsource.
    + subst group; cbn [fx_declared_body_work fx_declared_external_trace_budget]; exact IH.
    + pose proof (fx_callback_call_bound X C A B source budget call group Hbound Hsource) as Hcall.
      unfold fx_declared_body_work, fx_declared_external_trace_budget in *; cbn in *.
      unfold fx_one_body_work in Hcall; lia.
    + subst group; cbn [fx_declared_body_work fx_declared_external_trace_budget]; exact IH.
    + subst group; cbn [fx_declared_body_work fx_declared_external_trace_budget]; exact IH.
    + subst group; cbn [fx_declared_body_work fx_declared_external_trace_budget]; exact IH.
Qed.

(** * Queue support for reachable right-hand sides *)

Section QueueSupport.
Context {X C A : Type} (EX : encoding X) (EC : encoding C) (L : lattice A).
Context (sch : scheduler X) (mode : strategy) (S : System.t X C A).
Context (SS : System.static S) (ix : sys_index X C).
Hypothesis Hindex : sys_index_laws EX S SS ix.

Definition fx_queue_supported (queue : PQueue.t C) : Prop :=
  PQueue.wf EC queue /\ forall c, PQueue.priority EC c queue <> None -> In c (System.constraints S).

Lemma fx_enqueue_supported cs queue :
  incl cs (System.constraints S) -> fx_queue_supported queue ->
  fx_queue_supported (enqueue EC sch S cs queue).
Proof.
  intros Hincl [Hwf Hsupport]; split.
  - apply enqueue_wf; exact Hwf.
  - intros c Hpending; apply enqueue_member in Hpending; [|exact Hwf].
    destruct Hpending as [Hin|Hin]; [apply Hincl|apply Hsupport]; exact Hin.
Qed.

Lemma fx_initial_supported : fx_queue_supported (Engine.queue (initial_state EC sch S)).
Proof.
  cbn [initial_state Engine.queue]; apply fx_enqueue_supported; [apply incl_refl|].
  split; [apply PQueue.wf_empty|].
  intros c Hpending; rewrite PQueue.priority_empty in Hpending; contradiction.
Qed.

Lemma fx_update_supported xa mq recorded :
  fx_queue_supported (snd mq) ->
  fx_queue_supported (snd (engine_update EX EC L sch mode S (Declared SS ix) recorded xa mq)).
Proof.
  destruct xa as [x value], mq as [values queue]; intro Hqueue.
  unfold engine_update; cbn [fst snd].
  destruct (leb L value (lookup EX L values x)).
  - exact Hqueue.
  - apply fx_enqueue_supported; [|exact Hqueue].
    intros c Hreader; apply (readers_agree Hindex) in Hreader; tauto.
Qed.

Lemma fx_updates_supported updates mq recorded :
  fx_queue_supported (snd mq) ->
  fx_queue_supported (snd (engine_updates EX EC L sch mode S (Declared SS ix) recorded updates mq)).
Proof.
  revert mq; induction updates as [|update rest IH]; intros mq Hqueue.
  - exact Hqueue.
  - change (fx_queue_supported (snd (engine_updates EX EC L sch mode S (Declared SS ix) recorded
      rest (engine_update EX EC L sch mode S (Declared SS ix) recorded update mq)))).
    apply IH, fx_update_supported; exact Hqueue.
Qed.

Lemma fx_step_supported state next :
  fx_queue_supported (Engine.queue state) ->
  engine_step EX EC L sch mode S (Declared SS ix) state = Some next ->
  fx_queue_supported (Engine.queue next).
Proof.
  intros [Hwf Hsupport] Hstep; unfold engine_step in Hstep.
  destruct (PQueue.pop EC (Engine.queue state)) as [[[p c] queue]|] eqn:Hpop; [|discriminate].
  assert (Hqueue : fx_queue_supported queue).
  { split; [eapply PQueue.wf_pop; eassumption|].
    intros d Hd.
    destruct (PQueue.pop_rest EC _ _ _ _ Hwf Hpop) as [Hnone [Hother _]].
    destruct (Pos.eq_dec (encode EC d) (encode EC c)) as [Heq|Hne].
    - apply (encode_injective EC) in Heq; subst d; contradiction.
    - apply Hsupport; rewrite <- Hother; [exact Hd|].
      intro Heq; subst; contradiction. }
  destruct (Query.run (System.rhs S c) (lookup EX L (Engine.current state)))
    as [[value reads] sides].
  pose proof (fx_updates_supported ((System.target S c, value) :: sides)
    (Engine.current state, queue) (Engine.recorded state) Hqueue) as Hupdates.
  destruct (engine_updates EX EC L sch mode S (Declared SS ix) (Engine.recorded state)
    ((System.target S c, value) :: sides) (Engine.current state, queue)) as [values next_queue].
  inversion Hstep; subst next; exact Hupdates.
Qed.

End QueueSupport.

(** * Source receipts for each modeled operation *)

Section SourceReceipts.
Context {X C A B : Type} (EX : encoding X) (EC : encoding C) (L : lattice A).
Context (sch : scheduler X) (mode : strategy) (S : System.t X C A).
Context (SS : System.static S) (ix : sys_index X C).
Context (source : fx_declared_callback_source X C A B).
Hypothesis Hindex : sys_index_laws EX S SS ix.
Hypothesis Hsource : fx_declared_source_laws EX EC L sch S source.

Definition fx_has_receipts (events : audit_trace (fx_declared_call X C A)) : Prop :=
  exists bodies, fx_declared_trace_source source events bodies.

Lemma fx_receipts_app left right :
  fx_has_receipts left -> fx_has_receipts right -> fx_has_receipts (left ++ right).
Proof.
  intros [left_bodies Hleft] [right_bodies Hright].
  exists (left_bodies ++ right_bodies); unfold fx_declared_trace_source in *.
  now apply Forall2_app.
Qed.

Lemma fx_receipt_event event group :
  fx_declared_event_source source event group -> fx_has_receipts [event].
Proof.
  intro Hgroup; exists [group]; constructor; [exact Hgroup|constructor].
Qed.

Lemma fx_receipts_cons event group tail :
  fx_declared_event_source source event group -> fx_has_receipts tail ->
  fx_has_receipts (event :: tail).
Proof.
  intros Hgroup [bodies Htail]; exists (group :: bodies); constructor; assumption.
Qed.

Lemma fx_noncall_receipt event :
  (match event with
   | AuditCall _ =>
     False
   | _ =>
     True
   end) -> fx_has_receipts [event].
Proof.
  destruct event; cbn; try contradiction; intro Hnon; apply (fx_receipt_event _ []); reflexivity.
Qed.

Lemma fx_queue_entries_receipts events :
  queue_recorded_encoder_receipts (fx_index_encoder EC) events ->
  exists bodies, Forall2 (fx_queue_encoder_source source) (fx_queue_encoder_entries events) bodies.
Proof.
  destruct Hsource as [_ [Hencode _]].
  unfold queue_recorded_encoder_receipts, fx_queue_encoder_entries.
  intro Hall; induction Hall as [|[event [observed bodies]] rest Hbody Hall IH].
  - exists []; constructor.
  - destruct IH as [tail Htail].
    destruct event; cbn in Hbody; subst bodies; cbn [flat_map].
    all: try (exists tail; exact Htail).
    all: destruct (Hencode k) as [body Hencode_body]; exists (body :: tail); constructor;
      [exact Hencode_body|exact Htail].
Qed.

Lemma fx_lookup_receipts values x : fx_has_receipts (snd (@fx_model_lookup X C A EX L values x)).
Proof.
  destruct Hsource as [Hencode _].
  destruct (Hencode x) as [body Hbody].
  unfold fx_model_lookup; destruct (audit_map_code_get (encode EX x) values) as [raw events].
  destruct raw; cbn [snd]; exists [[body]; []].
  all: constructor; [cbn; exists body; auto|].
  all: constructor; [reflexivity|constructor].
Qed.

Lemma fx_query_receipts q values : fx_declared_query_reachable S q ->
  fx_has_receipts (snd (@fx_model_query X C A EX L q values)).
Proof.
  induction q as [a|x k IH|x a q IH]; intro Hreachable.
  - apply fx_noncall_receipt; exact I.
  - pose proof (fx_lookup_receipts values x) as Hlookup.
    destruct (fx_model_lookup EX L values x) as [value lookup_events] eqn:Hlookup_run.
    change (fx_has_receipts lookup_events) in Hlookup.
    assert (Hnext : fx_declared_query_reachable S (k value)).
    { eapply FxReachableAsk; exact Hreachable. }
    specialize (IH value Hnext).
    destruct (fx_model_query EX L (k value) values) as [[[v reads] sides] body] eqn:Hquery.
    change (fx_has_receipts body) in IH.
    destruct Hsource as [_ [_ [_ [_ [_ [_ [Hcontinuation _]]]]]]].
    destruct (Hcontinuation k value (ex_intro _ x Hreachable)) as [receipt Hreceipt].
    cbn [fx_model_query]; rewrite Hlookup_run, Hquery; cbn.
    apply fx_receipts_cons with (group := []); [reflexivity|].
    apply fx_receipts_app; [exact Hlookup|].
    apply fx_receipts_cons with (group := [receipt]); [cbn; eauto|].
    apply fx_receipts_app; [exact IH|apply fx_noncall_receipt; exact I].
  - assert (Hnext : fx_declared_query_reachable S q) by (eapply FxReachableSide; exact Hreachable).
    specialize (IH Hnext).
    destruct (fx_model_query EX L q values) as [[[v reads] sides] body] eqn:Hquery.
    change (fx_has_receipts body) in IH.
    cbn [fx_model_query]; rewrite Hquery; cbn.
    apply fx_receipts_cons with (group := []); [reflexivity|].
    apply fx_receipts_app; [exact IH|apply fx_noncall_receipt; exact I].
Qed.

Lemma fx_enqueue_receipts cs queue :
  fx_has_receipts (snd (@fx_model_enqueue X C A EC sch S cs queue)).
Proof.
  revert queue; induction cs as [|c rest IH]; intro queue.
  - apply fx_noncall_receipt; exact I.
  - pose proof (queue_recorded_push_encoder_receipts C _ (fx_index_encoder EC)
      (priority sch (System.target S c)) c queue) as Hqueue.
    destruct (audit_queue_recorded_push (fx_index_encoder EC) (priority sch (System.target S c))
      c queue) as [next events] eqn:Hpush.
    change (queue_recorded_encoder_receipts (fx_index_encoder EC) events) in Hqueue.
    destruct (fx_queue_entries_receipts events Hqueue) as [queue_bodies Hqueue_bodies].
    destruct Hsource as [_ [_ [Htarget [Hpriority _]]]].
    destruct (Htarget c) as [target_body Htarget_body].
    destruct (Hpriority (System.target S c)) as [priority_body Hpriority_body].
    specialize (IH next).
    destruct (fx_model_enqueue EC sch S rest next) as [out tail] eqn:Htail.
    change (fx_has_receipts tail) in IH.
    unfold fx_model_enqueue at 1; rewrite Hpush.
    change (fx_has_receipts (snd (let '(out, tail) := fx_model_enqueue EC sch S rest next in
      (out, [AuditCase 2 []; AuditCall (FxTarget c (System.target S c));
       AuditCall (FxPriority (System.target S c) (priority sch (System.target S c)));
       AuditCall (FxPush (priority sch (System.target S c)) c queue next events)] ++ tail)))).
    rewrite Htail; cbn [snd app].
    apply fx_receipts_cons with (group := []); [reflexivity|].
    apply fx_receipts_cons with (group := [target_body]); [cbn; eauto|].
    apply fx_receipts_cons with (group := [priority_body]); [cbn; eauto|].
    apply fx_receipts_cons with (group := queue_bodies); [exact Hqueue_bodies|exact IH].
Qed.

Lemma fx_raise_receipts x old value :
  fx_has_receipts (snd (@fx_model_raise X C A L sch mode x old value)).
Proof.
  destruct Hsource as [_ [_ [_ [_ [Hpoint [_ [_ [_ [Hjoin Hwiden]]]]]]]]].
  destruct mode.
  - destruct (Hjoin old value) as [body Hbody].
    unfold fx_model_raise; cbn [snd].
    apply fx_receipts_cons with (group := []); [reflexivity|].
    apply (fx_receipt_event _ [body]); cbn; eauto.
  - destruct (Hpoint x) as [point_body Hpoint_body].
    destruct (widening_point sch x) eqn:Hpoint_value.
    + destruct (Hwiden old value) as [body Hbody].
      unfold fx_model_raise; rewrite Hpoint_value; cbn [snd].
      apply fx_receipts_cons with (group := []); [reflexivity|].
      apply fx_receipts_cons with (group := [point_body]); [cbn; eauto|].
      apply fx_receipts_cons with (group := []); [reflexivity|].
      apply (fx_receipt_event _ [body]); cbn; eauto.
    + destruct (Hjoin old value) as [body Hbody].
      unfold fx_model_raise; rewrite Hpoint_value; cbn [snd].
      apply fx_receipts_cons with (group := []); [reflexivity|].
      apply fx_receipts_cons with (group := [point_body]); [cbn; eauto|].
      apply fx_receipts_cons with (group := []); [reflexivity|].
      apply (fx_receipt_event _ [body]); cbn; eauto.
Qed.

Lemma fx_update_receipts xa mq :
  fx_has_receipts (snd (fx_model_update EX EC L sch mode S ix xa mq)).
Proof.
  destruct xa as [x value], mq as [values queue].
  pose proof (fx_lookup_receipts values x) as Hlookup.
  destruct (fx_model_lookup EX L values x) as [old lookup_events] eqn:Hlookup_run.
  change (fx_has_receipts lookup_events) in Hlookup.
  destruct Hsource as [Hencode [_ [_ [_ [_ [_ [_ [Hleb _]]]]]]]].
  destruct (Hleb value old) as [leb_body Hleb_body].
  unfold fx_model_update; rewrite Hlookup_run.
  destruct (leb L value old) eqn:Hleb_value.
  - cbn [snd]; apply fx_receipts_app; [exact Hlookup|].
    apply fx_receipts_cons with (group := [leb_body]); [cbn; eauto|].
    apply fx_noncall_receipt; exact I.
  - pose proof (fx_raise_receipts x old value) as Hraise.
    destruct (@fx_model_raise X C A L sch mode x old value) as [raised raise_events]
      eqn:Hraise_run.
    change (fx_has_receipts raise_events) in Hraise.
    destruct (audit_trie_set (encode EX x) (x, raised) values) as [next_values write_body].
    destruct (audit_map_code_get (encode EX x) (readers ix)) as [raw read_body].
    pose proof (fx_enqueue_receipts (match raw with
      | Some cs =>
        cs
      | None =>
        []
      end) queue)
      as Henqueue.
    destruct (fx_model_enqueue EC sch S (match raw with
      | Some cs =>
        cs
      | None =>
        []
      end) queue)
      as [next_queue enqueue_events].
    change (fx_has_receipts enqueue_events) in Henqueue.
    destruct (Hencode x) as [encode_body Hencode_body].
    change (fx_has_receipts (lookup_events ++
      [AuditCall (FxLeb value old false); AuditCase 4 []] ++ raise_events ++
      [AuditCall (FxSet x (encode EX x) raised values next_values write_body);
       AuditCall (FxReaders x (encode EX x) (readers ix) raw read_body); AuditCase 5 []] ++
      enqueue_events)).
    apply fx_receipts_app; [exact Hlookup|].
    apply fx_receipts_cons with (group := [leb_body]); [cbn; eauto|].
    apply fx_receipts_cons with (group := []); [reflexivity|].
    apply fx_receipts_app; [exact Hraise|].
    apply fx_receipts_cons with (group := [encode_body]); [cbn; eauto|].
    apply fx_receipts_cons with (group := [encode_body]); [cbn; eauto|].
    apply fx_receipts_cons with (group := []); [reflexivity|exact Henqueue].
Qed.

Lemma fx_updates_receipts updates mq :
  fx_has_receipts (snd (fx_model_updates EX EC L sch mode S ix updates mq)).
Proof.
  revert mq; induction updates as [|update rest IH]; intro mq.
  - apply fx_noncall_receipt; exact I.
  - pose proof (fx_update_receipts update mq) as Hhead.
    destruct (fx_model_update EX EC L sch mode S ix update mq) as [next head] eqn:Hhead_run.
    change (fx_has_receipts head) in Hhead.
    specialize (IH next).
    destruct (fx_model_updates EX EC L sch mode S ix rest next) as [out tail] eqn:Htail.
    change (fx_has_receipts tail) in IH.
    unfold fx_model_updates at 1; rewrite Hhead_run.
    change (fx_has_receipts (snd (let '(out, tail) := fx_model_updates EX EC L sch mode S ix
      rest next in (out, [AuditCase 6 []] ++ head ++ tail)))).
    rewrite Htail; cbn [snd app].
    apply fx_receipts_cons with (group := []); [reflexivity|].
    apply fx_receipts_app; assumption.
Qed.

Lemma fx_step_receipts state : fx_queue_supported EC S (Engine.queue state) ->
  fx_has_receipts (snd (fx_model_step EX EC L sch mode S ix state)).
Proof.
  intros [Hwf Hsupport].
  pose proof (proj2 audit_queue_recorded_holds C _ EC (fx_index_encoder EC)
    (Engine.queue state) (fx_queue_encoder_erases EC)) as Hpop_erases.
  pose proof (queue_recorded_pop_fuel_encoder_receipts C _ (fx_index_encoder EC)
    (PQueue.pending_count (Engine.queue state)) (PQueue.pending (Engine.queue state))
    (PQueue.live (Engine.queue state)) (PQueue.live_count (Engine.queue state))) as Hqueue.
  change (queue_recorded_encoder_receipts (fx_index_encoder EC)
    (snd (audit_queue_recorded_pop (fx_index_encoder EC) (Engine.queue state)))) in Hqueue.
  destruct (audit_queue_recorded_pop (fx_index_encoder EC) (Engine.queue state))
    as [popped pop_events] eqn:Hpop_run.
  lazy beta iota zeta in Hpop_erases; destruct Hpop_erases as [Hpop_erases _].
  change (queue_recorded_encoder_receipts (fx_index_encoder EC) pop_events) in Hqueue.
  destruct (fx_queue_entries_receipts pop_events Hqueue) as [pop_bodies Hpop_bodies].
  unfold fx_model_step; rewrite Hpop_run.
  destruct popped as [[[priority c] queue]|].
  - assert (Hc : In c (System.constraints S)).
    { apply Hsupport; pose proof (PQueue.pop_min EC _ _ _ _ Hwf (eq_sym Hpop_erases)) as [Hp _].
      congruence. }
    assert (Hreachable : fx_declared_query_reachable S (System.rhs S c)).
    { constructor; exact Hc. }
    pose proof (fx_query_receipts (System.rhs S c) (Engine.current state) Hreachable) as Hquery.
    destruct (fx_model_query EX L (System.rhs S c) (Engine.current state))
      as [[[value reads] sides] query_events] eqn:Hquery_run.
    change (fx_has_receipts query_events) in Hquery.
    pose proof (fx_updates_receipts ((System.target S c, value) :: sides)
      (Engine.current state, queue)) as Hupdates.
    destruct (fx_model_updates EX EC L sch mode S ix ((System.target S c, value) :: sides)
      (Engine.current state, queue)) as [[values next_queue] update_events] eqn:Hupdates_run.
    change (fx_has_receipts update_events) in Hupdates.
    destruct Hsource as [_ [_ [Htarget [_ [_ [Hrhs _]]]]]].
    destruct (Htarget c) as [target_body Htarget_body].
    destruct (Hrhs c) as [rhs_body Hrhs_body].
    change (fx_has_receipts ([AuditCall (FxPop (Engine.queue state) (Some (priority, c, queue))
      pop_events); AuditCase 7 []; AuditCall (FxRhs c (System.rhs S c))] ++ query_events ++
      [AuditCall (FxTarget c (System.target S c))] ++ update_events ++ [AuditConstruct 2 []])).
    apply fx_receipts_cons with (group := pop_bodies); [exact Hpop_bodies|].
    apply fx_receipts_cons with (group := []); [reflexivity|].
    apply fx_receipts_cons with (group := [rhs_body]); [cbn; eauto|].
    apply fx_receipts_app; [exact Hquery|].
    apply fx_receipts_cons with (group := [target_body]); [cbn; eauto|].
    apply fx_receipts_app; [exact Hupdates|apply fx_noncall_receipt; exact I].
  - cbn [snd].
    apply fx_receipts_cons with (group := pop_bodies); [exact Hpop_bodies|].
    apply fx_noncall_receipt; exact I.
Qed.

Lemma fx_modeled_step_supported state next events :
  fx_queue_supported EC S (Engine.queue state) ->
  fx_model_step EX EC L sch mode S ix state = (Pending next, events) ->
  fx_queue_supported EC S (Engine.queue next).
Proof.
  intros Hqueue Hstep.
  pose proof (fx_step_erases EX EC L sch mode S SS ix state) as Herases.
  rewrite Hstep in Herases; cbn in Herases; unfold step_outcome in Herases.
  destruct (engine_step EX EC L sch mode S (Declared SS ix) state) as [next'|] eqn:Hstep_source;
    [|discriminate].
  inversion Herases; subst next'.
  eapply fx_step_supported; eassumption.
Qed.

Lemma fx_step_receipts_supported state : fx_queue_supported EC S (Engine.queue state) ->
  let '(out, events) := fx_model_step EX EC L sch mode S ix state in
  fx_has_receipts events /\
    match out with
    | Done _ =>
      True
    | Pending next =>
      fx_queue_supported EC S (Engine.queue next)
    end.
Proof.
  intro Hqueue; pose proof (fx_step_receipts state Hqueue) as Hreceipts.
  destruct (fx_model_step EX EC L sch mode S ix state) as [out events] eqn:Hstep.
  change (fx_has_receipts events) in Hreceipts.
  split; [exact Hreceipts|].
  destruct out as [values|next]; [exact I|].
  eapply fx_modeled_step_supported; eassumption.
Qed.

Lemma fx_loop_receipts_supported fuel state : fx_queue_supported EC S (Engine.queue state) ->
  let '(out, events) := fx_model_loop EX EC L sch mode S ix fuel state in
  fx_has_receipts events /\
    match out with
    | Done _ =>
      True
    | Pending next =>
      fx_queue_supported EC S (Engine.queue next)
    end.
Proof.
  revert state; induction fuel as [fuel IH|fuel IH|]; intros state Hqueue.
  - pose proof (IH state Hqueue) as Hfirst.
    destruct (fx_model_loop EX EC L sch mode S ix fuel state) as [first first_events]
      eqn:Hfirst_run.
    destruct first as [values|next].
    + change (fx_has_receipts first_events /\ True) in Hfirst.
      unfold fx_model_loop at 1; fold (fx_model_loop EX EC L sch mode S ix fuel state).
      rewrite Hfirst_run; cbn [snd fst].
      split; [|exact I].
      apply fx_receipts_cons with (group := []); [reflexivity|].
      apply fx_receipts_app; [exact (proj1 Hfirst)|].
      apply fx_receipts_cons with (group := []); [reflexivity|].
      apply fx_noncall_receipt; exact I.
    + change (fx_has_receipts first_events /\ fx_queue_supported EC S (Engine.queue next))
        in Hfirst.
      pose proof (IH next (proj2 Hfirst)) as Hsecond.
      destruct (fx_model_loop EX EC L sch mode S ix fuel next) as [second second_events]
        eqn:Hsecond_run.
      unfold fx_model_loop at 1; fold (fx_model_loop EX EC L sch mode S ix fuel state).
      rewrite Hfirst_run; fold (fx_model_loop EX EC L sch mode S ix fuel next); rewrite Hsecond_run.
      destruct second as [values|last].
      * change (fx_has_receipts second_events /\ True) in Hsecond.
        cbn [snd fst]; split; [|exact I].
        apply fx_receipts_cons with (group := []); [reflexivity|].
        apply fx_receipts_app; [exact (proj1 Hfirst)|].
        apply fx_receipts_cons with (group := []); [reflexivity|].
        apply fx_receipts_app; [exact (proj1 Hsecond)|apply fx_noncall_receipt; exact I].
      * change (fx_has_receipts second_events /\ fx_queue_supported EC S (Engine.queue last))
          in Hsecond.
        pose proof (fx_step_receipts_supported last (proj2 Hsecond)) as Hstep.
        destruct (fx_model_step EX EC L sch mode S ix last) as [out events] eqn:Hstep_run.
        destruct Hstep as [Hstep_receipts Hstep_supported].
        split; [|exact Hstep_supported].
        apply fx_receipts_cons with (group := []); [reflexivity|].
        apply fx_receipts_app; [exact (proj1 Hfirst)|].
        apply fx_receipts_cons with (group := []); [reflexivity|].
        apply fx_receipts_app; [exact (proj1 Hsecond)|].
        apply fx_receipts_cons with (group := []); [reflexivity|exact Hstep_receipts].
  - pose proof (IH state Hqueue) as Hfirst.
    destruct (fx_model_loop EX EC L sch mode S ix fuel state) as [first first_events]
      eqn:Hfirst_run.
    destruct first as [values|next].
    + change (fx_has_receipts first_events /\ True) in Hfirst.
      unfold fx_model_loop at 1; fold (fx_model_loop EX EC L sch mode S ix fuel state).
      rewrite Hfirst_run; cbn [snd fst].
      split; [|exact I].
      apply fx_receipts_cons with (group := []); [reflexivity|].
      apply fx_receipts_app; [exact (proj1 Hfirst)|apply fx_noncall_receipt; exact I].
    + change (fx_has_receipts first_events /\ fx_queue_supported EC S (Engine.queue next))
        in Hfirst.
      pose proof (IH next (proj2 Hfirst)) as Hsecond.
      destruct (fx_model_loop EX EC L sch mode S ix fuel next) as [out events] eqn:Hsecond_run.
      destruct Hsecond as [Hsecond_receipts Hsecond_supported].
      unfold fx_model_loop at 1; fold (fx_model_loop EX EC L sch mode S ix fuel state).
      rewrite Hfirst_run; fold (fx_model_loop EX EC L sch mode S ix fuel next); rewrite Hsecond_run.
      split; [|exact Hsecond_supported].
      apply fx_receipts_cons with (group := []); [reflexivity|].
      apply fx_receipts_app; [exact (proj1 Hfirst)|].
      apply fx_receipts_cons with (group := []); [reflexivity|exact Hsecond_receipts].
  - pose proof (fx_step_receipts_supported state Hqueue) as Hstep.
    destruct (fx_model_step EX EC L sch mode S ix state) as [out events] eqn:Hstep_run.
    destruct Hstep as [Hreceipts Hsupported].
    unfold fx_model_loop at 1; rewrite Hstep_run.
    split; [|exact Hsupported].
    apply fx_receipts_cons with (group := []); [reflexivity|exact Hreceipts].
Qed.

Lemma fx_run_receipts fuel :
  fx_has_receipts (snd (run_worklist_declared_model EX EC L sch mode S ix fuel)).
Proof.
  pose proof (fx_enqueue_receipts (System.constraints S) PQueue.empty) as Hinit.
  pose proof (fx_enqueue_erases EC sch S (System.constraints S) PQueue.empty) as Hinit_erases.
  destruct (fx_model_enqueue EC sch S (System.constraints S) PQueue.empty) as [queue init_events]
    eqn:Hinit_run.
  change (fx_has_receipts init_events) in Hinit.
  change (queue = enqueue EC sch S (System.constraints S) PQueue.empty) in Hinit_erases.
  assert (Hqueue : fx_queue_supported EC S queue).
  { rewrite Hinit_erases; exact (fx_initial_supported EC sch S). }
  pose proof (fx_loop_receipts_supported fuel (Engine.State Map.empty queue Map.empty) Hqueue)
    as Hloop.
  destruct (fx_model_loop EX EC L sch mode S ix fuel (Engine.State Map.empty queue Map.empty))
    as [out events] eqn:Hloop_run.
  destruct Hloop as [Hloop _].
  unfold run_worklist_declared_model; rewrite Hinit_run, Hloop_run; destruct out; cbn [snd].
  all: apply fx_receipts_app; [exact Hinit|].
  all: apply fx_receipts_cons with (group := []); [reflexivity|].
  all: apply fx_receipts_app; [exact Hloop|apply fx_noncall_receipt; exact I].
Qed.

End SourceReceipts.

(** The declared run has ordered callback witnesses with the stated same-run allowance. *)
Theorem fx_declared_external_source_holds : fx_declared_external_source_statement.
Proof.
  intros X C A B EX EC L sch mode S SS ix fuel source budget Hindex Hsource Hbounded.
  pose proof (fx_run_receipts EX EC L sch mode S SS ix source Hindex Hsource fuel) as Hreceipts.
  pose proof (fx_declared_run_input_bound X C A EX EC L sch mode S SS ix fuel) as Hrun.
  destruct (run_worklist_declared_model EX EC L sch mode S ix fuel) as [out events] eqn:Hmodel.
  change (fx_has_receipts source events) in Hreceipts.
  destruct Hreceipts as [bodies Hbodies].
  destruct Hrun as [Hout Hwork].
  pose proof (fx_trace_body_bound X C A B source budget events bodies Hbounded Hbodies) as Hbody.
  exists bodies; split; [exact Hbodies|]; split; [exact Hout|lia].
Qed.
