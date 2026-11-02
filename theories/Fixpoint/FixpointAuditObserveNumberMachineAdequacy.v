(** * Numbered observation machine adequacy

    Each ready step captures its actual label lookups and original callback bodies.
    For example, an absent occurrence invokes the declared fallback constraint.
    Builds on: numbered callbacks and nested-machine source adequacy. *)

From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditCost CollectionsAuditMap CollectionsAuditTrie CollectionsAuditFinSet
    CollectionsAuditEncoding.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointWorklist
  FixpointNested FixpointObserve FixpointAuditWorklist FixpointAuditWorklistAdequacy
  FixpointAuditWorklistBudget FixpointAuditWorklistBudgetAdequacy FixpointAuditWorklistCallbacks
  FixpointAuditNestedMachine FixpointAuditNestedMachineAdequacy FixpointAuditNestedCallbacks
  FixpointAuditNestedCallbacksAdequacy FixpointAuditObserveNumber
  FixpointAuditObserveNumberAdequacy FixpointAuditObserveNumberCallbacks
  FixpointAuditObserveNumberCallbacksAdequacy FixpointAuditObserveNumberMachine.
Import List.ListNotations.

(** * Original labels for arbitrary occurrence indices *)

Lemma fx_observe_any_label_in X C A (S : System.t X C A) fallback i :
  In fallback (System.constraints S) ->
  In (observation_label fallback (observation_number 0 (System.constraints S)) i)
    (System.constraints S).
Proof.
  intro Hfallback; unfold observation_label.
  replace i with (0 + i) by lia; rewrite observation_number_get.
  destruct (nth_error (System.constraints S) i) as [c|] eqn:Hnth; [|exact Hfallback].
  now apply nth_error_In in Hnth.
Qed.

Lemma fx_number_reachable_original X C A (S : System.t X C A) fallback q :
  In fallback (System.constraints S) ->
  fx_declared_query_reachable (observation_system S fallback) q ->
  fx_declared_query_reachable S q.
Proof.
  intros Hfallback Hreachable; induction Hreachable as [i Hi|x k a Hreach IH|x a next Hreach IH].
  - change (fx_declared_query_reachable S (System.rhs S
      (observation_label fallback (observation_number 0 (System.constraints S)) i))).
    apply FxReachableRhs.
    apply fx_observe_any_label_in; exact Hfallback.
  - now apply FxReachableAsk with (x := x) (k := k).
  - now apply FxReachableSide with (x := x) (a := a).
Qed.

(** * Non-ready traversal events *)

(** Placeholder relations describe slots that a non-ready transition cannot invoke. *)
Definition fx_number_nonready_source {X C A B} (source : fx_declared_callback_source X C A B) :
    fx_declared_callback_source X nat A B :=
  FxDeclaredCallbackSource X nat A B (fx_source_encode_x source) (fun _ _ _ => False)
    (fun _ _ body => body = []) (fx_source_priority source) (fx_source_widening_point source)
    (fun _ _ body => body = []) (fx_source_continuation source) (fx_source_leb source)
    (fx_source_join source) (fx_source_widen source).

Lemma fx_number_nonready_laws X C A B (EX : encoding X) (L : lattice A)
    (S : System.t X C A) fallback (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) :
  In fallback (System.constraints S) -> fx_nested_machine_source_laws EX L S source budget ->
  fx_nested_machine_source_laws EX L (observation_system S fallback)
    (fx_number_nonready_source source) (fx_number_passthrough_budget budget).
Proof.
  intros Hfallback Hsource.
  destruct Hsource as [Hencode [Htarget [Hrhs [Hcont [Hleb [Hjoin [Hwiden
    [Hencode_bound [Htarget_bound [Hrhs_bound [Hcont_bound [Hleb_bound [Hjoin_bound
      Hwiden_bound]]]]]]]]]]]]].
  unfold fx_nested_machine_source_laws, fx_number_nonready_source, fx_number_passthrough_budget;
    cbn.
  repeat split; try assumption.
  - intros c; exists []; reflexivity.
  - intros c; exists []; reflexivity.
  - intros k a [x Hreachable]; apply Hcont; exists x.
    eapply fx_number_reachable_original; eassumption.
  - intros c out body ->; reflexivity.
  - intros c out body ->; reflexivity.
Qed.

Definition fx_number_no_label_trace {X C A} (event : audit_event (fx_declared_call X C A)) : Prop :=
  match event with
  | AuditCall (FxRhs _ _)
  | AuditCall (FxTarget _ _) => False
  | _ => True
  end.

Definition fx_number_no_label_call {X C A} (event : fx_nested_event X C A) : Prop :=
  match event with
  | FxNestedRhs _ _
  | FxNestedTarget _ _ => False
  | FxNestedQuery events => Forall fx_number_no_label_trace events
  | _ => True
  end.

Lemma fx_number_nonready_events X C A (EX : encoding X) (L : lattice A)
    (plan : NestedPlan.t X C) mode (S : System.t X C A) state :
  NestedState.ready state = [] ->
  Forall fx_number_no_label_call (snd (fx_nested_step EX L plan mode S state)).
Proof.
  destruct state as [values ready frames dirty changed]; cbn [NestedState.ready]; intro Hready;
    subst ready.
  destruct frames as [|[code restart] frames].
  - cbn [fx_nested_step snd]; repeat constructor.
  - destruct code as [|x rest|h body rest].
    + destruct restart as [[h pass]|].
      * unfold fx_nested_step; cbn [NestedState.current NestedState.ready NestedState.frames
          NestedState.dirty NestedState.changed NestedFrame.remaining NestedFrame.restart].
        destruct (audit_finset_mem (fx_index_encoder EX) h dirty) as [present events].
        destruct present.
        -- destruct (audit_finset_remove (fx_index_encoder EX) h dirty) as [next removed].
           cbn [snd app]; repeat constructor.
        -- cbn [snd]; repeat constructor.
      * destruct changed; cbn [fx_nested_step snd]; repeat constructor.
    + unfold fx_nested_step; cbn [NestedState.current NestedState.ready NestedState.frames
        NestedState.dirty NestedState.changed NestedFrame.remaining NestedFrame.restart].
      destruct (audit_map_code_get (encode EX x) (NestedPlan.targets plan)) as [raw trace];
        cbn [snd]; repeat constructor.
    + unfold fx_nested_step; cbn [NestedState.current NestedState.ready NestedState.frames
        NestedState.dirty NestedState.changed NestedFrame.remaining NestedFrame.restart].
      destruct (audit_finset_remove (fx_index_encoder EX) h dirty) as [next removed];
        cbn [snd]; repeat constructor.
Qed.

Lemma fx_number_trace_convert X C A B (source : fx_declared_callback_source X C A B)
    events groups :
  Forall fx_number_no_label_trace events ->
  fx_declared_trace_source (fx_number_nonready_source source) events groups ->
  fx_declared_trace_source (fx_number_passthrough_source source) events groups.
Proof.
  intros Hsafe Hgroups; induction Hgroups as [|event group events groups Hevent Hrest IH].
  - constructor.
  - inversion Hsafe as [|head tail Hhead Htail]; subst head tail; constructor.
    + destruct event as [site operands|call|site operands|bit|site operands];
        cbn [fx_number_no_label_trace] in Hhead; try exact Hevent.
      destruct call; cbn [fx_number_no_label_trace] in Hhead; try contradiction; exact Hevent.
    + now apply IH.
Qed.

Lemma fx_number_nonready_convert X C A B (source : fx_declared_callback_source X C A B)
    events groups :
  Forall fx_number_no_label_call events ->
  Forall2 (fx_nested_machine_event_source (fx_number_nonready_source source)) events groups ->
  Forall2 (fx_nested_machine_event_source (fx_number_passthrough_source source)) events groups.
Proof.
  intros Hsafe Hgroups; induction Hgroups as [|event group events groups Hevent Hrest IH].
  - constructor.
  - inversion Hsafe as [|head tail Hhead Htail]; subst head tail; constructor.
    + destruct event; cbn [fx_number_no_label_call] in Hhead; try contradiction;
        try exact Hevent.
      cbn [fx_nested_machine_event_source] in Hevent |- *.
      destruct Hevent as [inner [Hinner ->]]; exists inner; split; [|reflexivity].
      eapply fx_number_trace_convert; eassumption.
    + now apply IH.
Qed.

Section UpdateEvents.
Context {X C A : Type} (EX : encoding X) (L : lattice A) (plan : NestedPlan.t X C)
  (mode : strategy).

Lemma fx_number_lookup_safe values x :
  Forall fx_number_no_label_trace (snd (@fx_model_lookup X C A EX L values x)).
Proof.
  unfold fx_model_lookup; destruct (audit_map_code_get (encode EX x) values) as [raw trace];
    destruct raw; cbn [snd]; repeat constructor.
Qed.

Lemma fx_number_mark_heads_safe heads dirty :
  Forall fx_number_no_label_call (snd (@fx_nested_mark_heads X C A EX heads dirty)).
Proof.
  revert dirty; induction heads as [|h rest IH]; intro dirty.
  - cbn [fx_nested_mark_heads snd]; repeat constructor.
  - cbn [fx_nested_mark_heads]; destruct (audit_finset_add (fx_index_encoder EX) h dirty) as
      [next events].
    specialize (IH next); destruct (@fx_nested_mark_heads X C A EX rest next) as [out later];
      cbn [snd] in IH |- *; repeat constructor; assumption.
Qed.

Lemma fx_number_mark_safe x (state : NestedState.t X C A) (values : assignment X A) :
  Forall fx_number_no_label_call (snd (fx_nested_mark EX plan x state values)).
Proof.
  unfold fx_nested_mark; destruct (audit_map_code_get (encode EX x) (NestedPlan.members plan)) as
    [raw trace].
  pose proof (fx_number_mark_heads_safe
    (match raw with
    | Some hs => hs
    | None => []
    end)
    (NestedState.dirty state)) as Hheads.
  destruct (fx_nested_mark_heads EX
    (match raw with
    | Some hs => hs
    | None => []
    end)
    (NestedState.dirty state)) as [out events]; cbn [snd] in Hheads |- *.
  repeat constructor; assumption.
Qed.

Lemma fx_number_raise_safe x old value :
  Forall fx_number_no_label_call (snd (fx_nested_raise EX L plan mode x old value)).
Proof.
  unfold fx_nested_raise; destruct mode; [cbn [snd]; repeat constructor|].
  destruct (audit_finset_mem (fx_index_encoder EX) x (NestedPlan.heads plan)) as [head events].
  destruct head; cbn [snd]; repeat constructor.
Qed.

Lemma fx_number_update_safe update state :
  Forall fx_number_no_label_call (snd (fx_nested_update EX L plan mode update state)).
Proof.
  destruct update as [x value]; pose proof (fx_number_lookup_safe (NestedState.current state) x)
    as Hlookup.
  unfold fx_nested_update; destruct (fx_model_lookup EX L (NestedState.current state) x) as
    [old reads]; cbn [snd] in Hlookup; destruct (leb L value old).
  - cbn [snd app]; repeat constructor; exact Hlookup.
  - pose proof (fx_number_raise_safe x old value) as Hraise.
    destruct (fx_nested_raise EX L plan mode x old value) as [raised events]; cbn [snd] in Hraise.
    destruct (audit_trie_set (encode EX x) (x, raised) (NestedState.current state)) as [values
      trace].
    pose proof (fx_number_mark_safe x state values) as Hmark.
    destruct (fx_nested_mark EX plan x state values) as [out later]; cbn [snd] in Hmark |- *.
    repeat rewrite Forall_app; repeat split; try assumption; repeat constructor; assumption.
Qed.

Lemma fx_number_updates_safe updates state :
  Forall fx_number_no_label_call (snd (fx_nested_updates EX L plan mode updates state)).
Proof.
  revert state; induction updates as [|update rest IH]; intro state.
  - cbn [fx_nested_updates snd]; repeat constructor.
  - pose proof (fx_number_update_safe update state) as Hfirst.
    cbn [fx_nested_updates]; destruct (fx_nested_update EX L plan mode update state) as [next
      events];
      cbn [snd] in Hfirst.
    specialize (IH next); destruct (fx_nested_updates EX L plan mode rest next) as [out later];
      cbn [snd] in IH |- *.
    constructor; [exact I|apply Forall_app; auto].
Qed.

End UpdateEvents.

Lemma fx_number_query_safe X C A (EX : encoding X) (L : lattice A) q values :
  Forall fx_number_no_label_trace (snd (@fx_model_query X C A EX L q values)).
Proof.
  induction q as [a|x k IH|x a q IH].
  - cbn [fx_model_query snd]; repeat constructor.
  - pose proof (@fx_number_lookup_safe X C A EX L values x) as Hlookup.
    destruct (fx_model_lookup EX L values x) as [value reads] eqn:Hread; cbn [snd] in Hlookup.
    specialize (IH value); destruct (fx_model_query EX L (k value) values) as
      [[[result queried] sides] events] eqn:Hrun; cbn [snd] in IH.
    cbn [fx_model_query]; rewrite Hread, Hrun; cbn [snd app].
    constructor; [exact I|].
    apply Forall_app; split; [exact Hlookup|].
    constructor; [exact I|].
    apply Forall_app; split; [exact IH|repeat constructor].
  - destruct (fx_model_query EX L q values) as [[[result queried] sides] events] eqn:Hrun;
      cbn [snd] in IH.
    cbn [fx_model_query]; rewrite Hrun; cbn [snd app].
    constructor; [exact I|].
    apply Forall_app; split; [exact IH|repeat constructor].
Qed.

Lemma fx_number_query_receipts X C A B (EX : encoding X) (L : lattice A)
    (S : System.t X C A) fallback (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) q values :
  In fallback (System.constraints S) -> fx_nested_machine_source_laws EX L S source budget ->
  fx_declared_query_reachable (observation_system S fallback) q ->
  fx_query_receipts_bounded (fx_number_passthrough_source source) (fx_number_passthrough_budget
    budget)
    (snd (@fx_model_query X nat A EX L q values)).
Proof.
  intros Hfallback Hsource Hreachable.
  pose proof (fx_number_nonready_laws X C A B EX L S fallback source budget Hfallback Hsource)
    as Haux.
  destruct Haux as [Hencode [_ [_ [Hcont [_ [_ [_ [Hencode_bound [_ [_ [Hcont_bound _]]]]]]]]]]].
  pose proof (@fx_query_all_receipts X nat A B EX L (observation_system S fallback)
    (fx_number_nonready_source source) (fx_number_passthrough_budget budget) Hencode Hcont
    Hencode_bound Hcont_bound q values Hreachable) as [groups [Hgroups Hbound]].
  exists groups; split; [|exact Hbound].
  eapply fx_number_trace_convert; [apply fx_number_query_safe|exact Hgroups].
Qed.

Lemma fx_number_updates_receipts X C A B (EX : encoding X) (L : lattice A)
    (plan : NestedPlan.t X nat) mode (S : System.t X C A) fallback
    (source : fx_declared_callback_source X C A B) (budget : fx_declared_callback_budget X C A B)
    updates state :
  In fallback (System.constraints S) -> fx_nested_machine_source_laws EX L S source budget ->
  fx_machine_has_receipts (fx_number_passthrough_source source) (fx_number_passthrough_budget
    budget)
    (snd (fx_nested_updates EX L plan mode updates state)).
Proof.
  intros Hfallback Hsource.
  pose proof (fx_number_nonready_laws X C A B EX L S fallback source budget Hfallback Hsource)
    as Haux.
  pose proof (@fx_machine_updates_receipts X nat A B EX L plan mode
    (observation_system S fallback) (fx_number_nonready_source source)
    (fx_number_passthrough_budget budget) Haux updates state) as [groups [Hgroups Hbound]].
  exists groups; split; [|exact Hbound].
  eapply fx_number_nonready_convert; [apply fx_number_updates_safe|exact Hgroups].
Qed.

(** * One captured machine step *)

Lemma fx_number_nonready_receipts X C A B (EX : encoding X) (L : lattice A)
    (plan : NestedPlan.t X nat) mode (S : System.t X C A) fallback
    (source : fx_declared_callback_source X C A B) (budget : fx_declared_callback_budget X C A B)
    state :
  In fallback (System.constraints S) -> fx_nested_machine_source_laws EX L S source budget ->
  NestedState.ready state = [] ->
  fx_machine_has_receipts (fx_number_passthrough_source source) (fx_number_passthrough_budget
    budget)
    (snd (fx_nested_step EX L plan mode (observation_system S fallback) state)).
Proof.
  intros Hfallback Hsource Hready.
  pose proof (fx_number_nonready_laws X C A B EX L S fallback source budget Hfallback Hsource)
    as Haux.
  pose proof (@fx_machine_step_receipts X nat A B EX L plan mode (observation_system S fallback)
    (fx_number_nonready_source source) (fx_number_passthrough_budget budget) Haux state) as Hstep.
  rewrite Hready in Hstep; specialize (Hstep (Forall_nil _)).
  destruct Hstep as [groups [Hgroups Hbound]]; exists groups; split; [|exact Hbound].
  eapply fx_number_nonready_convert; [apply fx_number_nonready_events; exact Hready|exact Hgroups].
Qed.

Lemma fx_number_step_bound X C A (EX : encoding X) (L : lattice A)
    (plan : NestedPlan.t X nat) mode (S : System.t X C A) fallback table state :
  let '(out, events) := fx_number_machine_step EX L plan mode S fallback table state in
  out = nested_step EX L plan mode (fx_number_system S fallback table) state /\
  fx_number_machine_work events <= fx_number_machine_step_budget EX L plan mode S fallback table
    state.
Proof.
  destruct state as [values ready frames dirty changed]; destruct ready as [|i rest].
  - pose proof (fx_nested_step_erases EX L plan mode (fx_number_system S fallback table)
      (NestedState.Make values [] frames dirty changed)) as Herase.
    pose proof (fx_nested_step_input_bound EX nat_encoding L plan mode (fx_number_system S
      fallback table)
      (NestedState.Make values [] frames dirty changed)) as Hbound.
    unfold fx_number_machine_step, fx_number_machine_step_budget; cbn [NestedState.ready].
    destruct (fx_nested_step EX L plan mode (fx_number_system S fallback table)
      (NestedState.Make values [] frames dirty changed)) as [out events]; cbn [fst] in Herase;
      cbn [snd] in Hbound; split; [exact Herase|].
    change (fx_nested_work nat_encoding events + 0 <=
      fx_nested_step_input_budget EX L plan mode (fx_number_system S fallback table)
        (NestedState.Make values [] frames dirty changed) + 0); lia.
  - pose proof (fx_observe_label_source C fallback table i) as Hlabel.
    destruct (fx_observe_label fallback table i) as [label events] eqn:Hlabel_run.
    change (label = observation_label fallback table i /\
      audit_map_source_work audit_nat_events_work events <= fx_observe_label_budget i) in Hlabel.
    destruct Hlabel as [Hlabel Hlabel_work].
    pose proof (@fx_query_erases X nat A EX L (System.rhs S label) values) as Hquery.
    pose proof (@fx_query_budget X nat A EX nat_encoding L (System.rhs S label) values) as
      Hquery_work.
    destruct (fx_model_query EX L (System.rhs S label) values) as [[[value reads] sides] query]
      eqn:Hquery_run; cbn [fst] in Hquery; cbn [snd] in Hquery_work.
    pose proof (fx_nested_updates_erases EX L plan mode ((System.target S label, value) :: sides)
      (NestedState.Make values rest frames dirty changed)) as Hupdates.
    pose proof (fx_nested_updates_input_bound EX nat_encoding L plan mode
      ((System.target S label, value) :: sides) (NestedState.Make values rest frames dirty changed))
      as Hupdates_work.
    destruct (fx_nested_updates EX L plan mode ((System.target S label, value) :: sides)
      (NestedState.Make values rest frames dirty changed)) as [out updates] eqn:Hupdates_run;
      cbn [fst] in Hupdates; cbn [snd] in Hupdates_work.
    unfold fx_number_machine_step, fx_observe_numbered_rhs, fx_observe_numbered_target,
      fx_number_machine_step_budget, nested_step, fx_number_system.
    cbn [NestedState.ready NestedState.current NestedState.frames NestedState.dirty
      NestedState.changed
      System.rhs System.target].
    rewrite Hlabel_run, Hquery_run, Hupdates_run, <- Hlabel, <- Hquery, <- Hupdates.
    split; [reflexivity|].
    cbn [fx_number_machine_work fx_number_machine_event_work fx_nested_work fx_nested_event_work
      fx_nested_step_input_budget NestedState.ready NestedState.current NestedState.frames
      NestedState.dirty NestedState.changed System.rhs System.target].
    rewrite <- Hlabel, <- Hquery; unfold fx_number_machine_work;
      cbn [fold_right fx_number_machine_event_work fx_nested_work fx_nested_event_work]; lia.
Qed.

Definition fx_number_machine_has_receipts {X C A B} (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) (events : list (fx_number_machine_event X C A))
      : Prop :=
  exists groups, Forall2 (fx_number_machine_event_source source) events groups /\
    fx_declared_body_work (fx_body_weight budget) groups <=
      fold_right (fun event n => fx_number_machine_external_budget budget event + n) 0 events.

Lemma fx_number_ready_assembly X C A B (S : System.t X C A)
    (source : fx_declared_callback_source X C A B) (budget : fx_declared_callback_budget X C A B)
    i label events query updates rhs_body target_body :
  fx_source_rhs source label (System.rhs S label) rhs_body ->
  fx_source_target source label (System.target S label) target_body ->
  fx_one_body_work (fx_body_weight budget) rhs_body <= fx_budget_rhs budget label ->
  fx_one_body_work (fx_body_weight budget) target_body <= fx_budget_target budget label ->
  fx_query_receipts_bounded (fx_number_passthrough_source source)
    (fx_number_passthrough_budget budget) query ->
  fx_machine_has_receipts (fx_number_passthrough_source source)
    (fx_number_passthrough_budget budget) updates ->
  fx_number_machine_has_receipts source budget
    [FxNumberMachineNested [FxNestedCase 6];
      FxNumberMachineRhs i label (System.rhs S label) events;
      FxNumberMachineNested [FxNestedQuery query];
      FxNumberMachineTarget i label (System.target S label) events;
      FxNumberMachineNested updates].
Proof.
  intros Hrhs_body Htarget_body Hrbound Htbound [qgroups [Hq Hqbound]]
    [ugroups [Hu Hubound]].
  exists [[]; [rhs_body]; concat qgroups; [target_body]; concat ugroups]; split.
  - repeat constructor.
    + cbn [fx_number_machine_event_source]; exists [[]]; split; [repeat constructor|reflexivity].
    + cbn [fx_number_machine_event_source]; exists rhs_body; auto.
    + cbn [fx_number_machine_event_source]; exists [concat qgroups]; split.
      * constructor; [cbn [fx_nested_machine_event_source]; exists qgroups; auto|constructor].
      * cbn [concat]; now rewrite app_nil_r.
    + cbn [fx_number_machine_event_source]; exists target_body; auto.
    + cbn [fx_number_machine_event_source]; exists ugroups; auto.
  - unfold fx_declared_body_work at 1; cbn [fold_right fx_number_machine_external_budget
      fx_nested_machine_external_budget].
    change (0 + ((fx_one_body_work (fx_body_weight budget) rhs_body + 0) +
      (fx_nested_group_work (fx_body_weight budget) (concat qgroups) +
      ((fx_one_body_work (fx_body_weight budget) target_body + 0) +
      (fx_nested_group_work (fx_body_weight budget) (concat ugroups) + 0)))) <=
      0 + 0 + (fx_budget_rhs budget label +
      (fx_declared_external_trace_budget (fx_number_passthrough_budget budget) query + 0 +
      (fx_budget_target budget label +
      (fx_machine_external_work (fx_number_passthrough_budget budget) updates + 0))))).
    rewrite !fx_nested_group_concat.
    change (fx_declared_body_work (fx_body_weight budget) qgroups <=
      fx_declared_external_trace_budget (fx_number_passthrough_budget budget) query) in Hqbound.
    change (fx_declared_body_work (fx_body_weight budget) ugroups <=
      fx_machine_external_work (fx_number_passthrough_budget budget) updates) in Hubound; lia.
Qed.

Lemma fx_number_label_query_reachable X C A (S : System.t X C A) fallback label :
  In label (System.constraints S) ->
  fx_declared_query_reachable (observation_system S fallback) (System.rhs S label).
Proof.
  intro Hlabel_in.
  destruct (observation_label_covers S fallback label Hlabel_in) as [j [Hj Hlabelj]].
  rewrite <- Hlabelj.
  change (fx_declared_query_reachable (observation_system S fallback)
    (System.rhs (observation_system S fallback) j)).
  now apply FxReachableRhs.
Qed.

Lemma fx_number_step_nonready X C A B (EX : encoding X) (L : lattice A)
    (plan : NestedPlan.t X nat) mode (S : System.t X C A) fallback
    (source : fx_declared_callback_source X C A B) (budget : fx_declared_callback_budget X C A B)
    values frames dirty changed :
  In fallback (System.constraints S) -> fx_nested_machine_source_laws EX L S source budget ->
  fx_number_machine_has_receipts source budget
    (snd (fx_number_machine_step EX L plan mode S fallback
      (observation_number 0 (System.constraints S))
      (NestedState.Make values [] frames dirty changed))).
Proof.
  intros Hfallback Hsource.
  pose proof (@fx_number_nonready_receipts X C A B EX L plan mode S fallback source budget
    (NestedState.Make values [] frames dirty changed) Hfallback Hsource eq_refl) as Hreceipts.
  unfold fx_number_machine_step; cbn [NestedState.ready].
  change (fx_machine_has_receipts (fx_number_passthrough_source source)
    (fx_number_passthrough_budget budget)
    (snd (fx_nested_step EX L plan mode
      (fx_number_system S fallback (observation_number 0 (System.constraints S)))
      (NestedState.Make values [] frames dirty changed)))) in Hreceipts.
  destruct (fx_nested_step EX L plan mode
    (fx_number_system S fallback (observation_number 0 (System.constraints S)))
    (NestedState.Make values [] frames dirty changed)) as [out events]; cbn [snd] in Hreceipts
      |- *.
  destruct Hreceipts as [groups [Hgroups Hbound]].
  exists [concat groups]; split.
  - constructor; [cbn [fx_number_machine_event_source]; exists groups; auto|constructor].
  - change (fx_nested_group_work (fx_body_weight budget) (concat groups) + 0 <=
      fx_machine_external_work (fx_number_passthrough_budget budget) events + 0).
    rewrite fx_nested_group_concat.
    change (fx_declared_body_work (fx_body_weight budget) groups <=
      fx_machine_external_work (fx_number_passthrough_budget budget) events) in Hbound; lia.
Qed.

Lemma fx_number_step_receipts X C A B (EX : encoding X) (L : lattice A)
    (plan : NestedPlan.t X nat) mode (S : System.t X C A) fallback
    (source : fx_declared_callback_source X C A B) (budget : fx_declared_callback_budget X C A B)
    state :
  In fallback (System.constraints S) -> fx_nested_machine_source_laws EX L S source budget ->
  fx_number_machine_has_receipts source budget
    (snd (fx_number_machine_step EX L plan mode S fallback
      (observation_number 0 (System.constraints S)) state)).
Proof.
  intros Hfallback Hsource.
  destruct state as [values ready frames dirty changed]; destruct ready as [|i rest].
  - now apply fx_number_step_nonready.
  - pose proof Hsource as Hlaws.
    destruct Hlaws as [Hencode [Htarget [Hrhs [Hcont [Hleb [Hjoin [Hwiden
      [Hencode_bound [Htarget_bound [Hrhs_bound [Hcont_bound [Hleb_bound [Hjoin_bound
        Hwiden_bound]]]]]]]]]]]]].
    set (table := observation_number 0 (System.constraints S)).
    pose proof (fx_observe_label_source C fallback table i) as Hlabel.
    destruct (fx_observe_label fallback table i) as [label events] eqn:Hlabel_run.
    change (label = observation_label fallback table i /\
      audit_map_source_work audit_nat_events_work events <= fx_observe_label_budget i) in Hlabel.
    destruct Hlabel as [Hlabel Hlabel_bound].
    assert (Hlabel_in : In label (System.constraints S)).
    { rewrite Hlabel; unfold table; now apply fx_observe_any_label_in. }
    pose proof (fx_number_label_query_reachable X C A S fallback label Hlabel_in) as Hreachable.
    pose proof (@fx_number_query_receipts X C A B EX L S fallback source budget
      (System.rhs S label) values Hfallback Hsource Hreachable) as Hquery.
    destruct (fx_model_query EX L (System.rhs S label) values) as [[[value reads] sides] query]
      eqn:Hquery_run; cbn [snd] in Hquery.
    pose proof (@fx_number_updates_receipts X C A B EX L plan mode S fallback source budget
      ((System.target S label, value) :: sides) (NestedState.Make values rest frames dirty changed)
      Hfallback Hsource) as Hupdates.
    destruct (fx_nested_updates EX L plan mode ((System.target S label, value) :: sides)
      (NestedState.Make values rest frames dirty changed)) as [out updates] eqn:Hupdates_run;
      cbn [snd] in Hupdates.
    destruct (Hrhs label) as [rhs_body Hrhs_body].
    destruct (Htarget label) as [target_body Htarget_body].
    pose proof (Hrhs_bound label (System.rhs S label) rhs_body Hrhs_body) as Hrbound.
    pose proof (Htarget_bound label (System.target S label) target_body Htarget_body) as Htbound.
    unfold fx_number_machine_step, fx_observe_numbered_rhs, fx_observe_numbered_target;
      cbn [NestedState.ready NestedState.current NestedState.frames NestedState.dirty
        NestedState.changed];
      fold table; rewrite Hlabel_run, Hquery_run, Hupdates_run; cbn [snd].
    eapply fx_number_ready_assembly; eassumption.
Qed.

(** The actual numbered step captures both original callback bodies and their lookup work. *)
Theorem fx_number_machine_step_source : fx_number_machine_step_source_statement.
Proof.
  intros X C A B EX L plan mode S fallback source budget state Hfallback Hsource.
  cbn zeta.
  pose proof (fx_number_step_bound X C A EX L plan mode S fallback
    (observation_number 0 (System.constraints S)) state) as Hbound.
  pose proof (fx_number_step_receipts X C A B EX L plan mode S fallback source budget state
    Hfallback Hsource) as Hreceipts.
  destruct (fx_number_machine_step EX L plan mode S fallback
    (observation_number 0 (System.constraints S)) state) as [out events]; cbn [snd] in Hreceipts.
  unfold fx_number_machine_has_receipts in Hreceipts;
  destruct Hbound as [Herase Hwork]; destruct Hreceipts as [groups [Hgroups Hbody]].
  cbn [fst snd]; exists groups; split; [exact Hgroups|].
  split; [exact Herase|lia].
Qed.
