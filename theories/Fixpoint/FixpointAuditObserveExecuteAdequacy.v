(** * Observation execution adequacy

    The counted execution follows the observation machine and charges boundary operations.
    For example, recording an output includes its lookup and persistent map write.
    Builds on: FixpointAuditObserveExecute and nested machine adequacy. *)

From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditTrie CollectionsAuditMap
  CollectionsAuditMapAdequacy.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointWorklist
  FixpointNested FixpointObserve
  FixpointAuditWorklist FixpointAuditWorklistAdequacy FixpointAuditWorklistBudget
  FixpointAuditWorklistBudgetAdequacy FixpointAuditNestedMachine FixpointAuditNestedMachineAdequacy
  FixpointAuditObserveExecute FixpointAuditWorklistCallbacks FixpointAuditNestedCallbacks
  FixpointAuditNestedCallbacksAdequacy.
Import List.ListNotations.

(** * Boundary erasure and work *)

Section Boundary.
Context {X C A : Type} (EX : encoding X) (EC : encoding C) (L : lattice A).

Lemma fx_observe_work_app (left right : list (fx_observe_event X C A)) :
  fx_observe_work EC (left ++ right) = fx_observe_work EC left + fx_observe_work EC right.
Proof.
  unfold fx_observe_work; induction left as [|event rest IH]; cbn [app fold_right]; lia.
Qed.

Lemma fx_observe_record_erases keys values output :
  fst (@fx_observe_record X C A EX L keys values output) =
    observation_record EX L keys values output.
Proof.
  unfold observation_record; revert output; induction keys as [|x rest IH]; intro output.
  - reflexivity.
  - pose proof (@fx_lookup_erases X C A EX L values x) as Hlookup.
    destruct (fx_model_lookup EX L values x) as [value reads] eqn:Hread; cbn in Hlookup.
    pose proof (audit_map_set_erases X A (fx_encoder_entry X) (fx_index_encoder EX) EX x value
      output eq_refl) as Hset.
    destruct (audit_map_set (fx_index_encoder EX) x value output) as [next writes] eqn:Hwrite.
    cbn in Hset.
    cbn [fx_observe_record fold_left]; rewrite Hread, Hwrite.
    destruct (@fx_observe_record X C A EX L rest values next) as [out later] eqn:Hrest.
    specialize (IH next); rewrite Hrest in IH; cbn in IH.
    now rewrite IH, Hset, Hlookup.
Qed.

Lemma fx_observe_evict_erases keys values :
  fst (@fx_observe_evict X C A EX keys values) = observation_evict EX keys values.
Proof.
  unfold observation_evict; revert values; induction keys as [|x rest IH]; intro values.
  - reflexivity.
  - pose proof (audit_map_remove_erases X A (fx_encoder_entry X) (fx_index_encoder EX) EX x
      values eq_refl) as Hremove.
    destruct (audit_map_remove (fx_index_encoder EX) x values) as [next events] eqn:Hrun.
    cbn in Hremove; cbn [fx_observe_evict fold_left]; rewrite Hrun.
    destruct (@fx_observe_evict X C A EX rest next) as [out later] eqn:Hrest.
    specialize (IH next); rewrite Hrest in IH; cbn in IH.
    now rewrite IH, Hremove.
Qed.

Lemma fx_observe_work_cons (event : fx_observe_event X C A) events :
  fx_observe_work EC (event :: events) = fx_observe_event_work EC event + fx_observe_work EC events.
Proof.
  reflexivity.
Qed.

Lemma fx_observe_map_work (events : list (audit_map_event X A (fx_encoder_entry X))) :
  fx_observe_work EC (map FxObserveMap events) = audit_map_source_work (@length (fx_encoder_entry
    X)) events.
Proof.
  induction events as [|event rest IH]; [reflexivity|].
  change (fx_observe_event_work EC (FxObserveMap event) +
    fx_observe_work EC (map FxObserveMap rest) = audit_map_source_work (@length (fx_encoder_entry
      X)) (event :: rest)).
  rewrite IH; destruct event as [key code input [value|] enc trie|
    key value code input output enc trie|key code input output enc trie];
    cbn [fx_observe_event_work audit_map_source_work]; lia.
Qed.

Lemma fx_observe_record_bound keys values output :
  fx_observe_work EC (snd (@fx_observe_record X C A EX L keys values output)) <=
    fx_observe_record_input_budget EX keys.
Proof.
  revert output; induction keys as [|x rest IH]; intro output.
  - reflexivity.
  - pose proof (@fx_lookup_budget X C A EX EC L values x) as Hlookup.
    destruct (fx_model_lookup EX L values x) as [value reads] eqn:Hread; cbn [snd] in Hlookup.
    pose proof (audit_map_set_source_work_bound X A (fx_encoder_entry X) (fx_index_encoder EX)
      (@length (fx_encoder_entry X)) x value output) as Hset.
    destruct (audit_map_set (fx_index_encoder EX) x value output) as [next writes] eqn:Hwrite.
    cbn [snd] in Hset; unfold fx_index_encoder in Hset; cbn in Hset.
    specialize (IH next); destruct (@fx_observe_record X C A EX L rest values next) as [out later]
      eqn:Hrest; cbn [snd] in IH.
    cbn [fx_observe_record fx_observe_record_input_budget]; rewrite Hread, Hwrite, Hrest.
    change (1 + fx_declared_model_work EC reads +
      fx_observe_work EC (map FxObserveMap writes ++ later) <=
      1 + fx_fullcheck_lookup_input_budget EX x + 3 + 16 * Pos.size_nat (encode EX x) +
        fx_observe_record_input_budget EX rest).
    rewrite fx_observe_work_app, fx_observe_map_work; lia.
Qed.

Lemma fx_observe_evict_bound keys values :
  fx_observe_work EC (snd (@fx_observe_evict X C A EX keys values)) <=
    fx_observe_evict_input_budget EX keys.
Proof.
  revert values; induction keys as [|x rest IH]; intro values.
  - reflexivity.
  - pose proof (audit_map_remove_source_work_bound X A (fx_encoder_entry X) (fx_index_encoder EX)
      (@length (fx_encoder_entry X)) x values) as Hremove.
    destruct (audit_map_remove (fx_index_encoder EX) x values) as [next events] eqn:Hrun.
    cbn [snd] in Hremove; unfold fx_index_encoder in Hremove; cbn in Hremove.
    specialize (IH next); destruct (@fx_observe_evict X C A EX rest next) as [out later] eqn:Hrest;
      cbn [snd] in IH.
    cbn [fx_observe_evict fx_observe_evict_input_budget]; rewrite Hrun, Hrest.
    change (1 + fx_observe_work EC (map FxObserveMap events ++ later) <=
      4 + 16 * Pos.size_nat (encode EX x) + fx_observe_evict_input_budget EX rest).
    rewrite fx_observe_work_app, fx_observe_map_work; lia.
Qed.

End Boundary.

(** * Tick and binary-fuel execution *)

Section Execution.
Context {X C A : Type} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (mode : strategy) (S : System.t X C A).

Lemma fx_observe_tick_erases evict state :
  fst (fx_observe_tick EX L mode S evict state) = observation_tick EX L mode S evict state.
Proof.
  destruct state as [state|finished]; [|reflexivity].
  pose proof (fx_nested_step_erases EX L (ObservationComponent.code (ObservationState.active state))
    mode S (ObservationState.local state)) as Hstep.
  unfold fx_observe_tick, observation_tick.
  destruct (fx_nested_step EX L (ObservationComponent.code (ObservationState.active state)) mode S
    (ObservationState.local state)) as [next nested] eqn:Hrun; cbn [fst] in Hstep.
  rewrite <- Hstep; destruct next as [local|]; [reflexivity|].
  pose proof (@fx_observe_record_erases X C A EX L
    (ObservationComponent.outputs (ObservationState.active state))
    (NestedState.current (ObservationState.local state)) (ObservationState.observed state)) as
      Hrecord.
  destruct (fx_observe_record EX L (ObservationComponent.outputs (ObservationState.active state))
    (NestedState.current (ObservationState.local state)) (ObservationState.observed state)) as
    [output events]; cbn in Hrecord.
  destruct evict.
  - pose proof (@fx_observe_evict_erases X C A EX
      (ObservationComponent.expire (ObservationState.active state))
      (NestedState.current (ObservationState.local state))) as Hevict.
    destruct (fx_observe_evict EX (ObservationComponent.expire (ObservationState.active state))
      (NestedState.current (ObservationState.local state))) as [retained removed]; cbn in Hevict.
    rewrite <- Hrecord, <- Hevict; destruct (ObservationState.pending state); reflexivity.
  - cbn; rewrite <- Hrecord; destruct (ObservationState.pending state); reflexivity.
Qed.

Lemma fx_observe_repeat_erases evict fuel state :
  fst (fx_observe_repeat EX L mode S evict fuel state) =
    observation_repeat (observation_tick EX L mode S evict) fuel state.
Proof.
  revert state; induction fuel as [fuel IH|fuel IH|]; intro state.
  - pose proof (IH state) as Hfirst.
    destruct (fx_observe_repeat EX L mode S evict fuel state) as [first events] eqn:Hrun;
      cbn in Hfirst.
    pose proof (IH first) as Hsecond.
    destruct (fx_observe_repeat EX L mode S evict fuel first) as [second later] eqn:Hnext;
      cbn in Hsecond.
    pose proof (fx_observe_tick_erases evict second) as Htick.
    destruct (fx_observe_tick EX L mode S evict second) as [out last] eqn:Hlast; cbn in Htick.
    cbn [fx_observe_repeat observation_repeat]; rewrite Hrun, Hnext, Hlast, <- Hfirst, <- Hsecond.
    exact Htick.
  - pose proof (IH state) as Hfirst.
    destruct (fx_observe_repeat EX L mode S evict fuel state) as [first events] eqn:Hrun;
      cbn in Hfirst.
    pose proof (IH first) as Hsecond.
    destruct (fx_observe_repeat EX L mode S evict fuel first) as [out later] eqn:Hnext;
      cbn in Hsecond.
    cbn [fx_observe_repeat observation_repeat]; rewrite Hrun, Hnext, <- Hfirst; exact Hsecond.
  - exact (fx_observe_tick_erases evict state).
Qed.

End Execution.

(** Erasing the counted execution recovers the original schedule and fuel behavior. *)
Theorem fx_observe_execute_erasure : fx_observe_execute_erasure_statement.
Proof.
  intros X0 C0 A0 EX0 L0 mode0 S0 schedule evict fuel.
  destruct schedule as [|first rest]; [reflexivity|].
  unfold fx_observe_execute, observation_execute.
  pose proof (@fx_observe_repeat_erases X0 C0 A0 EX0 L0 mode0 S0 evict fuel
    (inl (ObservationState.Make first rest (observation_start_local first Map.empty) Map.empty)))
    as Herase.
  destruct (fx_observe_repeat EX0 L0 mode0 S0 evict fuel
    (inl (ObservationState.Make first rest (observation_start_local first Map.empty) Map.empty))) as
    [out events]; cbn in Herase; now rewrite <- Herase.
Qed.

(** * Input-derived bounds for every tick *)

Section ExecutionBounds.
Context {X C A : Type} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (mode : strategy) (S : System.t X C A).

Lemma fx_observe_tick_bound evict state :
  fx_observe_work EC (snd (fx_observe_tick EX L mode S evict state)) <=
    fx_observe_tick_input_budget EX L mode S evict state.
Proof.
  destruct state as [state|finished]; [|reflexivity].
  pose proof (fx_nested_step_erases EX L (ObservationComponent.code (ObservationState.active state))
    mode S (ObservationState.local state)) as Herase.
  pose proof (fx_nested_step_input_bound EX EC L
    (ObservationComponent.code (ObservationState.active state)) mode S
    (ObservationState.local state)) as Hnested.
  unfold fx_observe_tick, fx_observe_tick_input_budget.
  destruct (fx_nested_step EX L (ObservationComponent.code (ObservationState.active state)) mode S
    (ObservationState.local state)) as [next nested] eqn:Hrun; cbn [fst] in Herase;
    cbn [snd] in Hnested; rewrite <- Herase.
  destruct next as [local|].
  - change (1 + (fx_nested_work EC nested + 0) <= 3 +
      fx_nested_step_input_budget EX L (ObservationComponent.code (ObservationState.active state))
        mode S (ObservationState.local state) + 0); lia.
  - pose proof (@fx_observe_record_bound X C A EX EC L
      (ObservationComponent.outputs (ObservationState.active state))
      (NestedState.current (ObservationState.local state)) (ObservationState.observed state)) as
        Hrecord.
    destruct (fx_observe_record EX L (ObservationComponent.outputs (ObservationState.active state))
      (NestedState.current (ObservationState.local state)) (ObservationState.observed state)) as
      [output events] eqn:Hrecord_run; cbn [snd] in Hrecord.
    destruct evict.
    + pose proof (@fx_observe_evict_bound X C A EX EC
        (ObservationComponent.expire (ObservationState.active state))
        (NestedState.current (ObservationState.local state))) as Hevict.
      destruct (fx_observe_evict EX (ObservationComponent.expire (ObservationState.active state))
        (NestedState.current (ObservationState.local state))) as [retained removed] eqn:Hevict_run;
        cbn [snd] in Hevict.
      assert (Hempty : fx_observe_work EC (@nil (fx_observe_event X C A)) = 0) by reflexivity.
      destruct (ObservationState.pending state); cbn [snd];
        repeat rewrite fx_observe_work_app; repeat rewrite fx_observe_work_cons;
        repeat rewrite fx_observe_work_app;
        cbn [fx_observe_event_work]; rewrite Hempty; lia.
    + assert (Hempty : fx_observe_work EC (@nil (fx_observe_event X C A)) = 0) by reflexivity.
      destruct (ObservationState.pending state); cbn [snd];
        repeat rewrite fx_observe_work_app; repeat rewrite fx_observe_work_cons;
        repeat rewrite fx_observe_work_app;
        cbn [fx_observe_event_work]; rewrite Hempty; lia.
Qed.

Lemma fx_observe_repeat_bound evict fuel state :
  fx_observe_work EC (snd (fx_observe_repeat EX L mode S evict fuel state)) <=
    fx_observe_repeat_input_budget EX L mode S evict fuel state.
Proof.
  revert state; induction fuel as [fuel IH|fuel IH|]; intro state.
  - pose proof (IH state) as Hfirst.
    pose proof (@fx_observe_repeat_erases X C A EX L mode S evict fuel state) as Herase.
    destruct (fx_observe_repeat EX L mode S evict fuel state) as [first events] eqn:Hrun;
      cbn [fst] in Herase; cbn [snd] in Hfirst.
    pose proof (IH first) as Hsecond.
    pose proof (@fx_observe_repeat_erases X C A EX L mode S evict fuel first) as Hnext_erase.
    destruct (fx_observe_repeat EX L mode S evict fuel first) as [second later] eqn:Hnext;
      cbn [fst] in Hnext_erase; cbn [snd] in Hsecond.
    pose proof (fx_observe_tick_bound evict second) as Htick.
    destruct (fx_observe_tick EX L mode S evict second) as [out last] eqn:Hlast; cbn [snd] in Htick.
    cbn [fx_observe_repeat fx_observe_repeat_input_budget]; rewrite Hrun, Hnext, Hlast, <- Herase,
      <- Hnext_erase.
    cbn [snd]; rewrite fx_observe_work_cons, !fx_observe_work_app; cbn [fx_observe_event_work]; lia.
  - pose proof (IH state) as Hfirst.
    pose proof (@fx_observe_repeat_erases X C A EX L mode S evict fuel state) as Herase.
    destruct (fx_observe_repeat EX L mode S evict fuel state) as [first events] eqn:Hrun;
      cbn [fst] in Herase; cbn [snd] in Hfirst.
    pose proof (IH first) as Hsecond.
    destruct (fx_observe_repeat EX L mode S evict fuel first) as [out later] eqn:Hnext;
      cbn [snd] in Hsecond.
    cbn [fx_observe_repeat fx_observe_repeat_input_budget]; rewrite Hrun, Hnext, <- Herase.
    cbn [snd]; rewrite fx_observe_work_cons, fx_observe_work_app; cbn [fx_observe_event_work]; lia.
  - exact (fx_observe_tick_bound evict state).
Qed.

End ExecutionBounds.

(** Counted execution fits the budget derived from its actual intermediate states. *)
Theorem fx_observe_execute_input_bound : fx_observe_execute_input_bound_statement.
Proof.
  intros X C A EX EC L mode S schedule evict fuel.
  destruct schedule as [|first rest]; [split; reflexivity|].
  pose proof (@fx_observe_repeat_erases X C A EX L mode S evict fuel
    (inl (ObservationState.Make first rest (observation_start_local first Map.empty) Map.empty)))
    as Herase.
  pose proof (@fx_observe_repeat_bound X C A EX EC L mode S evict fuel
    (inl (ObservationState.Make first rest (observation_start_local first Map.empty) Map.empty)))
    as Hbound.
  unfold fx_observe_execute, observation_execute, fx_observe_execute_input_budget.
  destruct (fx_observe_repeat EX L mode S evict fuel
    (inl (ObservationState.Make first rest (observation_start_local first Map.empty) Map.empty))) as
    [out events]; cbn [fst] in Herase; cbn [snd] in Hbound.
  rewrite <- Herase; split; [reflexivity|].
  rewrite fx_observe_work_cons; cbn [fx_observe_event_work]; lia.
Qed.

(** * Receipts from the execution's actual callbacks *)

Definition fx_observe_external_work {X C A B} (budget : fx_declared_callback_budget X C A B)
    (events : list (fx_observe_event X C A)) : nat :=
  fold_right (fun event n => fx_observe_event_external_budget budget event + n) 0 events.

Definition fx_observe_has_receipts {X C A B} (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) (events : list (fx_observe_event X C A)) : Prop
      :=
  exists groups, Forall2 (fx_observe_event_source source) events groups /\
    fx_declared_body_work (fx_body_weight budget) groups <= fx_observe_external_work budget events.

Lemma fx_observe_external_work_app X C A B (budget : fx_declared_callback_budget X C A B)
    left right : fx_observe_external_work budget (left ++ right) =
      fx_observe_external_work budget left + fx_observe_external_work budget right.
Proof.
  unfold fx_observe_external_work; induction left as [|event rest IH]; cbn [app fold_right]; lia.
Qed.

Lemma fx_observe_receipts_app X C A B (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) left right :
  fx_observe_has_receipts source budget left -> fx_observe_has_receipts source budget right ->
  fx_observe_has_receipts source budget (left ++ right).
Proof.
  intros [lg [Hl Hlb]] [rg [Hr Hrb]]; exists (lg ++ rg); split.
  - now apply Forall2_app.
  - rewrite fx_declared_body_work_app, fx_observe_external_work_app; lia.
Qed.

Lemma fx_observe_receipts_one X C A B (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) event group :
  fx_observe_event_source source event group ->
  fx_nested_group_work (fx_body_weight budget) group <= fx_observe_event_external_budget budget
    event ->
  fx_observe_has_receipts source budget [event].
Proof.
  intros Hsource Hbound; exists [group]; split; [constructor; [exact Hsource|constructor]|].
  change (fx_nested_group_work (fx_body_weight budget) group + 0 <=
    fx_observe_event_external_budget budget event + 0); lia.
Qed.

Lemma fx_observe_case_receipt X C A B (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) site :
  fx_observe_has_receipts source budget [FxObserveCase site].
Proof.
  apply fx_observe_receipts_one with (group := []); reflexivity.
Qed.

Lemma fx_observe_query_receipt X C A B (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) events :
  fx_query_receipts_bounded source budget events ->
  fx_observe_has_receipts source budget [FxObserveQuery events].
Proof.
  intros [groups [Hsource Hbound]].
  apply fx_observe_receipts_one with (group := concat groups).
  - cbn [fx_observe_event_source]; exists groups; auto.
  - cbn [fx_observe_event_external_budget]; now rewrite fx_nested_group_concat.
Qed.

Lemma fx_observe_nested_receipt X C A B (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) events :
  fx_machine_has_receipts source budget events ->
  fx_observe_has_receipts source budget [FxObserveNested events].
Proof.
  intros [groups [Hsource Hbound]].
  apply fx_observe_receipts_one with (group := concat groups).
  - cbn [fx_observe_event_source]; exists groups; auto.
  - cbn [fx_observe_event_external_budget]; rewrite fx_nested_group_concat; exact Hbound.
Qed.

Section BoundaryReceipts.
Context {X C A B : Type} (EX : encoding X) (L : lattice A)
  (source : fx_declared_callback_source X C A B) (budget : fx_declared_callback_budget X C A B).
Hypothesis Hencode : forall x, exists body, fx_source_encode_x source x (encode EX x) body.
Hypothesis Hencode_bound : forall x out body, fx_source_encode_x source x out body ->
  fx_one_body_work (fx_body_weight budget) body <= fx_budget_encode_x budget x.

Lemma fx_observe_set_receipt x value output :
  fx_observe_has_receipts source budget
    (map FxObserveMap (snd (audit_map_set (fx_index_encoder EX) x value output))).
Proof.
  destruct (Hencode x) as [body Hbody].
  pose proof (Hencode_bound x (encode EX x) body Hbody) as Hbound.
  unfold audit_map_set, fx_index_encoder; cbn [fst snd].
  destruct (audit_trie_set (encode EX x) (x, value) output) as [next trace].
  apply fx_observe_receipts_one with (group := [body]).
  - cbn [fx_observe_event_source fx_observe_map_entries fx_nested_entry_source];
      constructor; [exact Hbody|constructor].
  - change (fx_one_body_work (fx_body_weight budget) body + 0 <= fx_budget_encode_x budget x + 0);
      lia.
Qed.

Lemma fx_observe_remove_receipt x values :
  fx_observe_has_receipts source budget
    (map FxObserveMap (snd (audit_map_remove (fx_index_encoder EX) x values))).
Proof.
  destruct (Hencode x) as [body Hbody].
  pose proof (Hencode_bound x (encode EX x) body Hbody) as Hbound.
  unfold audit_map_remove, fx_index_encoder; cbn [fst snd].
  destruct (audit_trie_remove (encode EX x) values) as [next trace].
  apply fx_observe_receipts_one with (group := [body]).
  - cbn [fx_observe_event_source fx_observe_map_entries fx_nested_entry_source];
      constructor; [exact Hbody|constructor].
  - change (fx_one_body_work (fx_body_weight budget) body + 0 <= fx_budget_encode_x budget x + 0);
      lia.
Qed.

Lemma fx_observe_record_receipts keys values output :
  fx_observe_has_receipts source budget (snd (@fx_observe_record X C A EX L keys values output)).
Proof.
  revert output; induction keys as [|x rest IH]; intro output.
  - apply fx_observe_case_receipt.
  - pose proof (@fx_query_lookup_receipts X C A B EX L source budget Hencode Hencode_bound values x)
      as Hlookup.
    destruct (fx_model_lookup EX L values x) as [value reads] eqn:Hread; cbn [snd] in Hlookup.
    pose proof (fx_observe_set_receipt x value output) as Hset.
    destruct (audit_map_set (fx_index_encoder EX) x value output) as [next writes] eqn:Hwrite;
      cbn [snd] in Hset.
    specialize (IH next); destruct (@fx_observe_record X C A EX L rest values next) as [out later]
      eqn:Hrest; cbn [snd] in IH.
    cbn [fx_observe_record]; rewrite Hread, Hwrite, Hrest; cbn [snd].
    change (fx_observe_has_receipts source budget
      ([FxObserveCase 0] ++ [FxObserveQuery reads] ++ map FxObserveMap writes ++ later)).
    apply fx_observe_receipts_app; [apply fx_observe_case_receipt|].
    apply fx_observe_receipts_app; [now apply fx_observe_query_receipt|].
    now apply fx_observe_receipts_app.
Qed.

Lemma fx_observe_evict_receipts keys values :
  fx_observe_has_receipts source budget (snd (@fx_observe_evict X C A EX keys values)).
Proof.
  revert values; induction keys as [|x rest IH]; intro values.
  - apply fx_observe_case_receipt.
  - pose proof (fx_observe_remove_receipt x values) as Hremove.
    destruct (audit_map_remove (fx_index_encoder EX) x values) as [next events] eqn:Hrun;
      cbn [snd] in Hremove.
    specialize (IH next); destruct (@fx_observe_evict X C A EX rest next) as [out later] eqn:Hrest;
      cbn [snd] in IH.
    cbn [fx_observe_evict]; rewrite Hrun, Hrest; cbn [snd].
    change (fx_observe_has_receipts source budget ([FxObserveCase 1] ++ map FxObserveMap events ++
      later)).
    apply fx_observe_receipts_app; [apply fx_observe_case_receipt|].
    now apply fx_observe_receipts_app.
Qed.

End BoundaryReceipts.

(** * Ready constraints remain in the declared domain *)

Lemma fx_observe_updates_ready X C A (EX : encoding X) (L : lattice A)
    (plan : NestedPlan.t X C) mode updates state :
  NestedState.ready (nested_updates EX L plan mode updates state) = NestedState.ready state.
Proof.
  revert state; induction updates as [|[x value] rest IH]; intro state; [reflexivity|].
  change (NestedState.ready (nested_updates EX L plan mode rest
    (nested_update EX L plan mode (x, value) state)) = NestedState.ready state).
  rewrite IH; unfold nested_update; destruct (leb L value (lookup EX L (NestedState.current state)
    x));
    reflexivity.
Qed.

Lemma fx_observe_step_ready X C A (EX : encoding X) (L : lattice A)
    (plan : NestedPlan.t X C) mode (S : System.t X C A) state next :
  (forall x, incl (index_get EX (NestedPlan.targets plan) x) (System.constraints S)) ->
  Forall (fun c => In c (System.constraints S)) (NestedState.ready state) ->
  nested_step EX L plan mode S state = Some next ->
  Forall (fun c => In c (System.constraints S)) (NestedState.ready next).
Proof.
  intros Htargets Hready Hstep.
  destruct state as [values ready frames dirty changed]; destruct ready as [|c rest].
  - destruct frames as [|[code restart] frames]; [discriminate|].
    destruct code as [|x rest|h body rest].
    all: unfold nested_step in Hstep; cbn [NestedState.ready NestedState.current NestedState.frames
      NestedState.dirty NestedState.changed NestedFrame.remaining NestedFrame.restart] in Hstep.
    + destruct restart as [[h pass]|]; [destruct (FinSet.mem EX h dirty)|destruct changed];
        cbn [nested_step] in Hstep; inversion Hstep; constructor.
    + cbn [nested_step] in Hstep; inversion Hstep; subst next; cbn [NestedState.ready].
      apply Forall_forall; intros item Hin; now apply (Htargets x).
    + cbn [nested_step] in Hstep; inversion Hstep; constructor.
  - inversion Hready as [|head tail Hhead Htail]; subst head tail.
    unfold nested_step in Hstep; cbn [NestedState.ready NestedState.current NestedState.frames
      NestedState.dirty NestedState.changed] in Hstep.
    destruct (Query.run (System.rhs S c) (lookup EX L values)) as [[value reads] sides].
    inversion Hstep; subst next; rewrite fx_observe_updates_ready;
      destruct (leb L value (lookup EX L values (System.target S c))); exact Htail.
Qed.

Section TickReceipts.
Context {X C A B : Type} (EX : encoding X) (L : lattice A) (mode : strategy)
  (S : System.t X C A) (source : fx_declared_callback_source X C A B)
  (budget : fx_declared_callback_budget X C A B).
Hypothesis Hsource : fx_nested_machine_source_laws EX L S source budget.

Lemma fx_observe_tick_receipts evict state :
  (match state with
   | inl current => Forall (fun c => In c (System.constraints S))
       (NestedState.ready (ObservationState.local current))
   | inr _ => True
   end) -> fx_observe_has_receipts source budget (snd (fx_observe_tick EX L mode S evict state)).
Proof.
  destruct state as [state|finished]; intro Hready; [|apply fx_observe_case_receipt].
  pose proof (@fx_machine_step_receipts X C A B EX L
    (ObservationComponent.code (ObservationState.active state)) mode S source budget Hsource
    (ObservationState.local state) Hready) as Hnested.
  unfold fx_observe_tick.
  destruct (fx_nested_step EX L (ObservationComponent.code (ObservationState.active state)) mode S
    (ObservationState.local state)) as [next nested] eqn:Hrun; cbn [snd] in Hnested.
  destruct next as [local|].
  - cbn [snd]; change (fx_observe_has_receipts source budget
      ([FxObserveCase 2] ++ [FxObserveNested nested])).
    apply fx_observe_receipts_app; [apply fx_observe_case_receipt|].
    now apply fx_observe_nested_receipt.
  - pose proof Hsource as Hlaws.
    destruct Hlaws as [Hencode [_ [_ [_ [_ [_ [_ [Hencode_bound _]]]]]]]].
    pose proof (@fx_observe_record_receipts X C A B EX L source budget Hencode Hencode_bound
      (ObservationComponent.outputs (ObservationState.active state))
      (NestedState.current (ObservationState.local state)) (ObservationState.observed state)) as
        Hrecord.
    destruct (fx_observe_record EX L (ObservationComponent.outputs (ObservationState.active state))
      (NestedState.current (ObservationState.local state)) (ObservationState.observed state)) as
      [output events] eqn:Hrecord_run; cbn [snd] in Hrecord.
    destruct evict.
    + pose proof (@fx_observe_evict_receipts X C A B EX source budget Hencode Hencode_bound
        (ObservationComponent.expire (ObservationState.active state))
        (NestedState.current (ObservationState.local state))) as Hevict.
      destruct (fx_observe_evict EX (ObservationComponent.expire (ObservationState.active state))
        (NestedState.current (ObservationState.local state))) as [retained removed] eqn:Hevict_run;
        cbn [snd] in Hevict.
      destruct (ObservationState.pending state); cbn [snd].
      all: change (fx_observe_has_receipts source budget
        (([FxObserveCase 2] ++ [FxObserveNested nested] ++ events ++ removed) ++
          [FxObserveCase 3])).
      all: apply fx_observe_receipts_app; [|apply fx_observe_case_receipt].
      all: apply fx_observe_receipts_app; [apply fx_observe_case_receipt|].
      all: apply fx_observe_receipts_app; [now apply fx_observe_nested_receipt|].
      all: now apply fx_observe_receipts_app.
    + destruct (ObservationState.pending state); cbn [snd]; rewrite app_nil_r.
      all: change (fx_observe_has_receipts source budget
        (([FxObserveCase 2] ++ [FxObserveNested nested] ++ events) ++ [FxObserveCase 3])).
      all: apply fx_observe_receipts_app; [|apply fx_observe_case_receipt].
      all: apply fx_observe_receipts_app; [apply fx_observe_case_receipt|].
      all: apply fx_observe_receipts_app; [now apply fx_observe_nested_receipt|exact Hrecord].
Qed.

End TickReceipts.

(** The active and pending components come from the initial schedule and ready constraints remain
    in the original system. *)
Definition fx_observe_state_valid {X C A} (S : System.t X C A)
    (schedule : list (ObservationComponent.t X C))
    (state : ObservationState.t X C A + (assignment X A * assignment X A)) : Prop :=
  match state with
  | inr _ => True
  | inl current => In (ObservationState.active current) schedule /\
      Forall (fun component => In component schedule) (ObservationState.pending current) /\
      Forall (fun c => In c (System.constraints S)) (NestedState.ready (ObservationState.local
        current))
  end.

Lemma fx_observe_native_tick_valid X C A (EX : encoding X) (L : lattice A) mode
    (S : System.t X C A) schedule evict state :
  fx_observe_schedule_targets_within EX (System.constraints S) schedule ->
  fx_observe_state_valid S schedule state ->
  fx_observe_state_valid S schedule (observation_tick EX L mode S evict state).
Proof.
  intros Htargets Hvalid; destruct state as [current|finished]; [|exact I].
  destruct Hvalid as [Hactive [Hpending Hready]].
  unfold observation_tick.
  destruct (nested_step EX L (ObservationComponent.code (ObservationState.active current)) mode S
    (ObservationState.local current)) as [local|] eqn:Hstep.
  - repeat split; try assumption.
    eapply fx_observe_step_ready; [|exact Hready|exact Hstep].
    intros x c Hin; eapply Htargets; eassumption.
  - destruct (ObservationState.pending current) as [|next rest] eqn:Hpending_run; [exact I|].
    inversion Hpending as [|component tail Hnext Hrest]; subst component tail.
    repeat split; try assumption; constructor.
Qed.

Lemma fx_observe_repeat_valid X C A (EX : encoding X) (L : lattice A) mode
    (S : System.t X C A) schedule evict fuel state :
  fx_observe_schedule_targets_within EX (System.constraints S) schedule ->
  fx_observe_state_valid S schedule state ->
  fx_observe_state_valid S schedule
    (observation_repeat (observation_tick EX L mode S evict) fuel state).
Proof.
  intros Htargets; revert state; induction fuel as [fuel IH|fuel IH|]; intros state Hvalid.
  - cbn [observation_repeat]; apply fx_observe_native_tick_valid; [exact Htargets|].
    apply IH; apply IH; exact Hvalid.
  - cbn [observation_repeat]; apply IH; apply IH; exact Hvalid.
  - apply fx_observe_native_tick_valid; assumption.
Qed.

Lemma fx_observe_repeat_receipts X C A B (EX : encoding X) (L : lattice A) mode
    (S : System.t X C A) (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) schedule evict fuel state :
  fx_nested_machine_source_laws EX L S source budget ->
  fx_observe_schedule_targets_within EX (System.constraints S) schedule ->
  fx_observe_state_valid S schedule state ->
  fx_observe_has_receipts source budget (snd (fx_observe_repeat EX L mode S evict fuel state)).
Proof.
  intros Hsource Htargets; revert state; induction fuel as [fuel IH|fuel IH|]; intros state Hvalid.
  - pose proof (IH state Hvalid) as Hfirst.
    pose proof (@fx_observe_repeat_erases X C A EX L mode S evict fuel state) as Herase.
    pose proof (@fx_observe_repeat_valid X C A EX L mode S schedule evict fuel state Htargets
      Hvalid) as Hfirst_valid.
    destruct (fx_observe_repeat EX L mode S evict fuel state) as [first events] eqn:Hrun;
      cbn [snd] in Hfirst; cbn [fst] in Herase; rewrite <- Herase in Hfirst_valid.
    pose proof (IH first Hfirst_valid) as Hsecond.
    pose proof (@fx_observe_repeat_erases X C A EX L mode S evict fuel first) as Hnext_erase.
    pose proof (@fx_observe_repeat_valid X C A EX L mode S schedule evict fuel first Htargets
      Hfirst_valid)
      as Hsecond_valid.
    destruct (fx_observe_repeat EX L mode S evict fuel first) as [second later] eqn:Hnext;
      cbn [snd] in Hsecond; cbn [fst] in Hnext_erase; rewrite <- Hnext_erase in Hsecond_valid.
    pose proof (@fx_observe_tick_receipts X C A B EX L mode S source budget Hsource evict second)
      as Htick.
    assert (Hready : match second with
      | inl current => Forall (fun c => In c (System.constraints S))
          (NestedState.ready (ObservationState.local current))
      | inr _ => True
      end).
    { destruct second as [current|finished]; cbn [fx_observe_state_valid] in Hsecond_valid |- *;
        tauto. }
    specialize (Htick Hready).
    destruct (fx_observe_tick EX L mode S evict second) as [out last] eqn:Hlast; cbn [snd] in Htick.
    cbn [fx_observe_repeat]; rewrite Hrun, Hnext, Hlast; cbn [snd].
    change (fx_observe_has_receipts source budget ([FxObserveCase 4] ++ events ++ later ++ last)).
    apply fx_observe_receipts_app; [apply fx_observe_case_receipt|].
    apply fx_observe_receipts_app; [exact Hfirst|].
    now apply fx_observe_receipts_app.
  - pose proof (IH state Hvalid) as Hfirst.
    pose proof (@fx_observe_repeat_erases X C A EX L mode S evict fuel state) as Herase.
    pose proof (@fx_observe_repeat_valid X C A EX L mode S schedule evict fuel state Htargets
      Hvalid)
      as Hfirst_valid.
    destruct (fx_observe_repeat EX L mode S evict fuel state) as [first events] eqn:Hrun;
      cbn [snd] in Hfirst; cbn [fst] in Herase; rewrite <- Herase in Hfirst_valid.
    pose proof (IH first Hfirst_valid) as Hsecond.
    destruct (fx_observe_repeat EX L mode S evict fuel first) as [out later] eqn:Hnext;
      cbn [snd] in Hsecond.
    cbn [fx_observe_repeat]; rewrite Hrun, Hnext; cbn [snd].
    change (fx_observe_has_receipts source budget ([FxObserveCase 4] ++ events ++ later)).
    apply fx_observe_receipts_app; [apply fx_observe_case_receipt|].
    now apply fx_observe_receipts_app.
  - apply fx_observe_tick_receipts; [exact Hsource|].
    destruct state as [current|finished]; cbn [fx_observe_state_valid] in Hvalid |- *; tauto.
Qed.

(** The execution supplies receipts from the same ticks and its input-derived frame bound. *)
Theorem fx_observe_execute_source : fx_observe_execute_source_statement.
Proof.
  intros X C A B EX EC L mode S source budget schedule evict fuel Hsource Htargets.
  pose proof (fx_observe_execute_input_bound X C A EX EC L mode S schedule evict fuel) as Hbound.
  destruct schedule as [|first rest].
  - exists [[]]; split; [constructor; [reflexivity|constructor]|].
    split; reflexivity.
  - assert (Hvalid : fx_observe_state_valid S (first :: rest)
      (inl (ObservationState.Make first rest (observation_start_local first Map.empty) Map.empty))).
    { cbn [fx_observe_state_valid observation_start_local]; split; [now left|].
      split; [apply Forall_forall; intros item Hin; now right|constructor]. }
    pose proof (@fx_observe_repeat_receipts X C A B EX L mode S source budget (first :: rest)
      evict fuel _ Hsource Htargets Hvalid) as Hreceipts.
    unfold fx_observe_execute in Hbound |- *.
    destruct (fx_observe_repeat EX L mode S evict fuel
      (inl (ObservationState.Make first rest (observation_start_local first Map.empty)
        Map.empty))) as
      [out events] eqn:Hrun; cbn [snd] in Hreceipts.
    destruct Hreceipts as [groups [Hgroups Hgroup_bound]].
    destruct Hbound as [Herase Hwork].
    exists ([] :: groups); split.
    + constructor; [reflexivity|exact Hgroups].
    + split; [exact Herase|].
      rewrite fx_observe_work_cons in Hwork |- *;
        cbn [fx_observe_event_work] in Hwork |- *.
      change (1 + fx_observe_work EC events + fx_declared_body_work (fx_body_weight budget) groups
        <=
        fx_observe_execute_input_budget EX L mode S (first :: rest) evict fuel +
        fx_observe_external_work budget events); lia.
Qed.
