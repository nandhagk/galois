(** * Numbered observation execution adequacy

    The numbered execution composes captured machine callbacks with actual boundary work.
    For example, an output is recorded before its value is evicted.
    Builds on: numbered machine and observation boundary adequacy. *)

From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointSystem FixpointWorklist FixpointNested FixpointObserve
  FixpointAuditWorklistCallbacks FixpointAuditNestedMachine FixpointAuditNestedCallbacks
  FixpointAuditNestedCallbacksAdequacy FixpointAuditObserveExecute
    FixpointAuditObserveExecuteAdequacy
  FixpointAuditObserveNumber FixpointAuditObserveNumberMachine
    FixpointAuditObserveNumberMachineAdequacy
  FixpointAuditObserveNumberExecute.
Import List.ListNotations.

(** * Ordered execution receipts *)

Definition fx_number_execute_external_work {X C A B} (budget : fx_declared_callback_budget X C A B)
    (events : list (fx_number_execute_event X C A)) : nat :=
  fold_right (fun event n => fx_number_execute_external_budget budget event + n) 0 events.

Definition fx_number_execute_has_receipts {X C A B} (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) (events : list (fx_number_execute_event X C A))
      : Prop :=
  exists groups, Forall2 (fx_number_execute_event_source source) events groups /\
    fx_declared_body_work (fx_body_weight budget) groups <= fx_number_execute_external_work budget
      events.

Lemma fx_number_execute_work_app X C A (left right : list (fx_number_execute_event X C A)) :
  fx_number_execute_work (left ++ right) = fx_number_execute_work left + fx_number_execute_work
    right.
Proof.
  unfold fx_number_execute_work; induction left as [|event rest IH]; cbn [app fold_right]; lia.
Qed.

Lemma fx_number_execute_external_work_app X C A B (budget : fx_declared_callback_budget X C A B)
    left right : fx_number_execute_external_work budget (left ++ right) =
      fx_number_execute_external_work budget left + fx_number_execute_external_work budget right.
Proof.
  unfold fx_number_execute_external_work; induction left as [|event rest IH]; cbn [app
    fold_right]; lia.
Qed.

Lemma fx_number_execute_receipts_app X C A B (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) left right :
  fx_number_execute_has_receipts source budget left -> fx_number_execute_has_receipts source
    budget right ->
  fx_number_execute_has_receipts source budget (left ++ right).
Proof.
  intros [lg [Hl Hlb]] [rg [Hr Hrb]]; exists (lg ++ rg); split.
  - now apply Forall2_app.
  - rewrite fx_declared_body_work_app, fx_number_execute_external_work_app; lia.
Qed.

Lemma fx_number_execute_case X C A B (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) :
  fx_number_execute_has_receipts source budget [FxNumberExecuteCase].
Proof.
  exists [[]]; split; [constructor; [reflexivity|constructor]|reflexivity].
Qed.

Lemma fx_number_execute_machine_receipt X C A B (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) events :
  fx_number_machine_has_receipts source budget events ->
  fx_number_execute_has_receipts source budget [FxNumberExecuteMachine events].
Proof.
  intros [groups [Hsource Hbound]]; exists [concat groups]; split.
  - constructor; [cbn [fx_number_execute_event_source]; exists groups; auto|constructor].
  - change (fx_nested_group_work (fx_body_weight budget) (concat groups) + 0 <=
      fold_right (fun event n => fx_number_machine_external_budget budget event + n) 0 events + 0).
    rewrite fx_nested_group_concat; lia.
Qed.

Lemma fx_number_execute_boundary_receipt X C A B (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) events :
  fx_observe_has_receipts (fx_number_passthrough_source source) (fx_number_passthrough_budget
    budget) events ->
  fx_number_execute_has_receipts source budget [FxNumberExecuteBoundary events].
Proof.
  intros [groups [Hsource Hbound]]; exists [concat groups]; split.
  - constructor; [cbn [fx_number_execute_event_source]; exists groups; auto|constructor].
  - change (fx_nested_group_work (fx_body_weight budget) (concat groups) + 0 <=
      fx_observe_external_work (fx_number_passthrough_budget budget) events + 0).
    rewrite fx_nested_group_concat.
    change (fx_declared_body_work (fx_body_weight budget) groups <=
      fx_observe_external_work (fx_number_passthrough_budget budget) events) in Hbound; lia.
Qed.

Lemma fx_number_execute_work_cons X C A (event : fx_number_execute_event X C A) events :
  fx_number_execute_work (event :: events) = fx_number_execute_event_work event +
    fx_number_execute_work events.
Proof.
  reflexivity.
Qed.

(** * A tick returns the original state and pays its real boundary work *)

Section NumberTick.
Context {X C A : Type} (EX : encoding X) (L : lattice A) (mode : strategy)
  (S : System.t X C A) (fallback : C) (table : Map.t nat C).

Lemma fx_number_tick_erases evict state :
  fst (fx_number_execute_tick EX L mode S fallback table evict state) =
    observation_tick EX L mode (fx_number_system S fallback table) evict state.
Proof.
  destruct state as [state|finished]; [|reflexivity].
  pose proof (fx_number_step_bound X C A EX L (ObservationComponent.code (ObservationState.active
    state))
    mode S fallback table (ObservationState.local state)) as Hstep.
  unfold fx_number_execute_tick, observation_tick.
  destruct (fx_number_machine_step EX L (ObservationComponent.code (ObservationState.active state))
    mode S fallback table (ObservationState.local state)) as [next machine] eqn:Hrun.
  destruct Hstep as [Herase Hbound]; rewrite <- Herase; destruct next as [local|]; [reflexivity|].
  pose proof (@fx_observe_record_erases X nat A EX L
    (ObservationComponent.outputs (ObservationState.active state))
    (NestedState.current (ObservationState.local state)) (ObservationState.observed state)) as
      Hrecord.
  destruct (fx_observe_record EX L (ObservationComponent.outputs (ObservationState.active state))
    (NestedState.current (ObservationState.local state)) (ObservationState.observed state)) as
    [output events]; cbn in Hrecord.
  destruct evict.
  - pose proof (@fx_observe_evict_erases X nat A EX
      (ObservationComponent.expire (ObservationState.active state))
      (NestedState.current (ObservationState.local state))) as Hevict.
    destruct (fx_observe_evict EX (ObservationComponent.expire (ObservationState.active state))
      (NestedState.current (ObservationState.local state))) as [retained removed]; cbn in Hevict.
    rewrite <- Hrecord, <- Hevict; destruct (ObservationState.pending state); reflexivity.
  - cbn; rewrite <- Hrecord; destruct (ObservationState.pending state); reflexivity.
Qed.

Lemma fx_number_tick_bound evict state :
  fx_number_execute_work (snd (fx_number_execute_tick EX L mode S fallback table evict state)) <=
    fx_number_execute_tick_budget EX L mode S fallback table evict state.
Proof.
  destruct state as [state|finished]; [|reflexivity].
  pose proof (fx_number_step_bound X C A EX L (ObservationComponent.code (ObservationState.active
    state))
    mode S fallback table (ObservationState.local state)) as Hstep.
  unfold fx_number_execute_tick, fx_number_execute_tick_budget, fx_observe_tick_input_budget.
  destruct (fx_number_machine_step EX L (ObservationComponent.code (ObservationState.active state))
    mode S fallback table (ObservationState.local state)) as [next machine] eqn:Hrun.
  destruct Hstep as [Herase Hbound]; rewrite <- Herase.
  unfold fx_number_machine_step_budget in Hbound; destruct next as [local|].
  - cbn [snd]; repeat rewrite fx_number_execute_work_cons; cbn [fx_number_execute_event_work].
    assert (Hempty : fx_number_execute_work (@nil (fx_number_execute_event X C A)) = 0) by
      reflexivity.
    rewrite Hempty; lia.
  - pose proof (@fx_observe_record_bound X nat A EX nat_encoding L
      (ObservationComponent.outputs (ObservationState.active state))
      (NestedState.current (ObservationState.local state)) (ObservationState.observed state)) as
        Hrecord.
    destruct (fx_observe_record EX L (ObservationComponent.outputs (ObservationState.active state))
      (NestedState.current (ObservationState.local state)) (ObservationState.observed state)) as
      [output events] eqn:Hrecord_run; cbn [snd] in Hrecord.
    destruct evict.
    + pose proof (@fx_observe_evict_bound X nat A EX nat_encoding
        (ObservationComponent.expire (ObservationState.active state))
        (NestedState.current (ObservationState.local state))) as Hevict.
      destruct (fx_observe_evict EX (ObservationComponent.expire (ObservationState.active state))
        (NestedState.current (ObservationState.local state))) as [retained removed] eqn:Hevict_run;
        cbn [snd] in Hevict.
      assert (Hempty : fx_number_execute_work (@nil (fx_number_execute_event X C A)) = 0) by
        reflexivity.
      destruct (ObservationState.pending state); cbn [snd];
        repeat rewrite fx_number_execute_work_cons; cbn [fx_number_execute_event_work];
        rewrite fx_observe_work_app, Hempty; lia.
    + assert (Hempty : fx_number_execute_work (@nil (fx_number_execute_event X C A)) = 0) by
      reflexivity.
      destruct (ObservationState.pending state); cbn [snd]; rewrite app_nil_r;
        repeat rewrite fx_number_execute_work_cons; cbn [fx_number_execute_event_work]; rewrite
          Hempty; lia.
Qed.

End NumberTick.

Section NumberTickReceipts.
Context {X C A B : Type} (EX : encoding X) (L : lattice A) (mode : strategy)
  (S : System.t X C A) (fallback : C) (source : fx_declared_callback_source X C A B)
  (budget : fx_declared_callback_budget X C A B).
Hypothesis Hfallback : In fallback (System.constraints S).
Hypothesis Hsource : fx_nested_machine_source_laws EX L S source budget.

Lemma fx_number_tick_receipts evict state :
  fx_number_execute_has_receipts source budget
    (snd (fx_number_execute_tick EX L mode S fallback (observation_number 0 (System.constraints S))
      evict state)).
Proof.
  destruct state as [state|finished]; [|apply fx_number_execute_case].
  pose proof (@fx_number_step_receipts X C A B EX L
    (ObservationComponent.code (ObservationState.active state)) mode S fallback source budget
    (ObservationState.local state) Hfallback Hsource) as Hmachine.
  unfold fx_number_execute_tick.
  destruct (fx_number_machine_step EX L (ObservationComponent.code (ObservationState.active state))
    mode S fallback (observation_number 0 (System.constraints S)) (ObservationState.local state)) as
    [next machine] eqn:Hrun; cbn [snd] in Hmachine.
  destruct next as [local|].
  - cbn [snd]; change (fx_number_execute_has_receipts source budget
      ([FxNumberExecuteCase] ++ [FxNumberExecuteMachine machine])).
    apply fx_number_execute_receipts_app; [apply fx_number_execute_case|].
    now apply fx_number_execute_machine_receipt.
  - pose proof Hsource as Hlaws.
    destruct Hlaws as [Hencode [_ [_ [_ [_ [_ [_ [Hencode_bound _]]]]]]]].
    pose proof (@fx_observe_record_receipts X nat A B EX L (fx_number_passthrough_source source)
      (fx_number_passthrough_budget budget) Hencode Hencode_bound
      (ObservationComponent.outputs (ObservationState.active state))
      (NestedState.current (ObservationState.local state)) (ObservationState.observed state)) as
        Hrecord.
    destruct (fx_observe_record EX L (ObservationComponent.outputs (ObservationState.active state))
      (NestedState.current (ObservationState.local state)) (ObservationState.observed state)) as
      [output events] eqn:Hrecord_run; cbn [snd] in Hrecord.
    destruct evict.
    + pose proof (@fx_observe_evict_receipts X nat A B EX (fx_number_passthrough_source source)
        (fx_number_passthrough_budget budget) Hencode Hencode_bound
        (ObservationComponent.expire (ObservationState.active state))
        (NestedState.current (ObservationState.local state))) as Hevict.
      destruct (fx_observe_evict EX (ObservationComponent.expire (ObservationState.active state))
        (NestedState.current (ObservationState.local state))) as [retained removed] eqn:Hevict_run;
        cbn [snd] in Hevict.
      destruct (ObservationState.pending state); cbn [snd].
      all: change (fx_number_execute_has_receipts source budget
        ([FxNumberExecuteCase] ++ [FxNumberExecuteMachine machine] ++
          [FxNumberExecuteBoundary (events ++ removed)] ++ [FxNumberExecuteCase])).
      all: apply fx_number_execute_receipts_app; [apply fx_number_execute_case|].
      all: apply fx_number_execute_receipts_app; [now apply fx_number_execute_machine_receipt|].
      all: apply fx_number_execute_receipts_app; [|apply fx_number_execute_case].
      all: apply fx_number_execute_boundary_receipt; now apply fx_observe_receipts_app.
    + destruct (ObservationState.pending state); cbn [snd]; rewrite app_nil_r.
      all: change (fx_number_execute_has_receipts source budget
        ([FxNumberExecuteCase] ++ [FxNumberExecuteMachine machine] ++
          [FxNumberExecuteBoundary events] ++ [FxNumberExecuteCase])).
      all: apply fx_number_execute_receipts_app; [apply fx_number_execute_case|].
      all: apply fx_number_execute_receipts_app; [now apply fx_number_execute_machine_receipt|].
      all: apply fx_number_execute_receipts_app; [now apply
        fx_number_execute_boundary_receipt|apply fx_number_execute_case].
Qed.

End NumberTickReceipts.

(** * Binary repetition preserves actual intermediate states and all receipts *)

Section NumberRepeat.
Context {X C A : Type} (EX : encoding X) (L : lattice A) (mode : strategy)
  (S : System.t X C A) (fallback : C) (table : Map.t nat C).

Lemma fx_number_repeat_erases evict fuel state :
  fst (fx_number_execute_repeat EX L mode S fallback table evict fuel state) =
    observation_repeat (observation_tick EX L mode (fx_number_system S fallback table) evict) fuel
      state.
Proof.
  revert state; induction fuel as [fuel IH|fuel IH|]; intro state.
  - pose proof (IH state) as Hfirst.
    destruct (fx_number_execute_repeat EX L mode S fallback table evict fuel state) as [first
      events]
      eqn:Hrun; cbn [fst] in Hfirst.
    pose proof (IH first) as Hsecond.
    destruct (fx_number_execute_repeat EX L mode S fallback table evict fuel first) as [second
      later]
      eqn:Hnext; cbn [fst] in Hsecond.
    pose proof (fx_number_tick_erases EX L mode S fallback table evict second) as Htick.
    destruct (fx_number_execute_tick EX L mode S fallback table evict second) as [out last]
      eqn:Hlast;
      cbn [fst] in Htick.
    cbn [fx_number_execute_repeat observation_repeat]; rewrite Hrun, Hnext, Hlast, <- Hfirst, <-
      Hsecond.
    exact Htick.
  - pose proof (IH state) as Hfirst.
    destruct (fx_number_execute_repeat EX L mode S fallback table evict fuel state) as [first
      events]
      eqn:Hrun; cbn [fst] in Hfirst.
    pose proof (IH first) as Hsecond.
    destruct (fx_number_execute_repeat EX L mode S fallback table evict fuel first) as [out later]
      eqn:Hnext; cbn [fst] in Hsecond.
    cbn [fx_number_execute_repeat observation_repeat]; rewrite Hrun, Hnext, <- Hfirst; exact
      Hsecond.
  - exact (fx_number_tick_erases EX L mode S fallback table evict state).
Qed.

Lemma fx_number_repeat_bound evict fuel state :
  fx_number_execute_work (snd (fx_number_execute_repeat EX L mode S fallback table evict fuel
    state)) <=
    fx_number_execute_repeat_budget EX L mode S fallback table evict fuel state.
Proof.
  revert state; induction fuel as [fuel IH|fuel IH|]; intro state.
  - pose proof (IH state) as Hfirst.
    pose proof (fx_number_repeat_erases evict fuel state) as Herase.
    destruct (fx_number_execute_repeat EX L mode S fallback table evict fuel state) as [first
      events]
      eqn:Hrun; cbn [fst] in Herase; cbn [snd] in Hfirst.
    pose proof (IH first) as Hsecond.
    pose proof (fx_number_repeat_erases evict fuel first) as Hnext_erase.
    destruct (fx_number_execute_repeat EX L mode S fallback table evict fuel first) as [second
      later]
      eqn:Hnext; cbn [fst] in Hnext_erase; cbn [snd] in Hsecond.
    pose proof (fx_number_tick_bound EX L mode S fallback table evict second) as Htick.
    destruct (fx_number_execute_tick EX L mode S fallback table evict second) as [out last]
      eqn:Hlast;
      cbn [snd] in Htick.
    cbn [fx_number_execute_repeat fx_number_execute_repeat_budget]; rewrite Hrun, Hnext, Hlast,
      <- Herase, <- Hnext_erase; cbn [snd].
    rewrite fx_number_execute_work_cons, !fx_number_execute_work_app;
      cbn [fx_number_execute_event_work]; lia.
  - pose proof (IH state) as Hfirst.
    pose proof (fx_number_repeat_erases evict fuel state) as Herase.
    destruct (fx_number_execute_repeat EX L mode S fallback table evict fuel state) as [first
      events]
      eqn:Hrun; cbn [fst] in Herase; cbn [snd] in Hfirst.
    pose proof (IH first) as Hsecond.
    destruct (fx_number_execute_repeat EX L mode S fallback table evict fuel first) as [out later]
      eqn:Hnext; cbn [snd] in Hsecond.
    cbn [fx_number_execute_repeat fx_number_execute_repeat_budget]; rewrite Hrun, Hnext, <- Herase;
      cbn [snd].
    rewrite fx_number_execute_work_cons, fx_number_execute_work_app;
      cbn [fx_number_execute_event_work]; lia.
  - exact (fx_number_tick_bound EX L mode S fallback table evict state).
Qed.

End NumberRepeat.

Lemma fx_number_repeat_receipts X C A B (EX : encoding X) (L : lattice A) mode
    (S : System.t X C A) fallback (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) evict fuel state :
  In fallback (System.constraints S) -> fx_nested_machine_source_laws EX L S source budget ->
  fx_number_execute_has_receipts source budget
    (snd (fx_number_execute_repeat EX L mode S fallback (observation_number 0 (System.constraints
      S))
      evict fuel state)).
Proof.
  intros Hfallback Hsource; revert state; induction fuel as [fuel IH|fuel IH|]; intro state.
  - pose proof (IH state) as Hfirst.
    destruct (fx_number_execute_repeat EX L mode S fallback (observation_number 0
      (System.constraints S))
      evict fuel state) as [first events] eqn:Hrun; cbn [snd] in Hfirst.
    pose proof (IH first) as Hsecond.
    destruct (fx_number_execute_repeat EX L mode S fallback (observation_number 0
      (System.constraints S))
      evict fuel first) as [second later] eqn:Hnext; cbn [snd] in Hsecond.
    pose proof (@fx_number_tick_receipts X C A B EX L mode S fallback source budget Hfallback
      Hsource
      evict second) as Htick.
    destruct (fx_number_execute_tick EX L mode S fallback (observation_number 0
      (System.constraints S))
      evict second) as [out last] eqn:Hlast; cbn [snd] in Htick.
    cbn [fx_number_execute_repeat]; rewrite Hrun, Hnext, Hlast; cbn [snd].
    change (fx_number_execute_has_receipts source budget ([FxNumberExecuteCase] ++ events ++ later
      ++ last)).
    apply fx_number_execute_receipts_app; [apply fx_number_execute_case|].
    apply fx_number_execute_receipts_app; [exact Hfirst|].
    now apply fx_number_execute_receipts_app.
  - pose proof (IH state) as Hfirst.
    destruct (fx_number_execute_repeat EX L mode S fallback (observation_number 0
      (System.constraints S))
      evict fuel state) as [first events] eqn:Hrun; cbn [snd] in Hfirst.
    pose proof (IH first) as Hsecond.
    destruct (fx_number_execute_repeat EX L mode S fallback (observation_number 0
      (System.constraints S))
      evict fuel first) as [out later] eqn:Hnext; cbn [snd] in Hsecond.
    cbn [fx_number_execute_repeat]; rewrite Hrun, Hnext; cbn [snd].
    change (fx_number_execute_has_receipts source budget ([FxNumberExecuteCase] ++ events ++
      later)).
    apply fx_number_execute_receipts_app; [apply fx_number_execute_case|].
    now apply fx_number_execute_receipts_app.
  - now apply fx_number_tick_receipts.
Qed.

(** Numbered execution retains each callback body and both maps within its input-derived bound. *)
Theorem fx_number_execute_source : fx_number_execute_source_statement.
Proof.
  intros X C A B EX L mode S fallback source budget schedule evict fuel Hfallback Hsource.
  cbn zeta; destruct schedule as [|first rest].
  - exists [[]]; split; [constructor; [reflexivity|constructor]|].
    split; reflexivity.
  - pose proof (@fx_number_repeat_erases X C A EX L mode S fallback
      (observation_number 0 (System.constraints S)) evict fuel
      (inl (ObservationState.Make first rest (observation_start_local first Map.empty) Map.empty)))
      as Herase.
    pose proof (@fx_number_repeat_bound X C A EX L mode S fallback
      (observation_number 0 (System.constraints S)) evict fuel
      (inl (ObservationState.Make first rest (observation_start_local first Map.empty) Map.empty)))
      as Hbound.
    pose proof (@fx_number_repeat_receipts X C A B EX L mode S fallback source budget evict fuel
      (inl (ObservationState.Make first rest (observation_start_local first Map.empty) Map.empty))
      Hfallback Hsource) as Hreceipts.
    unfold fx_number_execute, observation_execute, fx_number_execute_budget.
    destruct (fx_number_execute_repeat EX L mode S fallback (observation_number 0
      (System.constraints S))
      evict fuel (inl (ObservationState.Make first rest (observation_start_local first Map.empty)
        Map.empty)))
      as [out events] eqn:Hrun; cbn [fst] in Herase; cbn [snd] in Hbound, Hreceipts.
    change (out = observation_repeat (observation_tick EX L mode (observation_system S fallback)
      evict)
      fuel (inl (ObservationState.Make first rest (observation_start_local first Map.empty)
        Map.empty)))
      in Herase.
    destruct Hreceipts as [groups [Hgroups Hbody]]; exists ([] :: groups); split.
    + constructor; [reflexivity|exact Hgroups].
    + rewrite <- Herase; split; [reflexivity|].
      rewrite fx_number_execute_work_cons; cbn [fx_number_execute_event_work].
      change (1 + fx_number_execute_work events + fx_declared_body_work (fx_body_weight budget)
        groups <=
        1 + fx_number_execute_repeat_budget EX L mode S fallback
          (observation_number 0 (System.constraints S)) evict fuel
          (inl (ObservationState.Make first rest (observation_start_local first Map.empty)
            Map.empty)) +
        fx_number_execute_external_work budget events); lia.
Qed.
