(** * Adequacy of observation plan checking

    The checker composes strict side, root, component and expiration checks in one execution.
    For example, rejecting a root still leaves the later component and expiration receipts.
    Builds on: observation preparation, component and expiration adequacy. *)

From Stdlib Require Import List Bool Arith Lia.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointSchedule FixpointObserve
  FixpointAuditIndex FixpointAuditScheduleWrapper FixpointAuditWorklistCallbacks
  FixpointAuditNestedCallbacksAdequacy FixpointAuditObserveCompare
  FixpointAuditObserveExpireCheck FixpointAuditObserveExpireCheckAdequacy
  FixpointAuditObserveExpiry FixpointAuditObserveExpiryAdequacy
  FixpointAuditObservePrepare FixpointAuditObservePrepareAdequacy
  FixpointAuditObserveComponents FixpointAuditObserveComponentsAdequacy
  FixpointAuditObservePlanCheck.
Import List.ListNotations.

(** Each checker phase keeps the bodies from that phase's actual execution. *)
Lemma fx_check_phase_receipts X C A B D (index_source : fx_index_external_source X C B)
    (source : fx_declared_callback_source X C A D) side_events root_events component_events
    calls distinct expiry_events compare_events side_groups root_groups component_groups
    expiry_groups compare_groups :
  Forall2 (fx_observe_prepare_event_source index_source source) side_events side_groups ->
  Forall2 (fx_observe_prepare_event_source index_source source) root_events root_groups ->
  Forall2 (fx_observe_component_event_source index_source source) component_events
    component_groups ->
  fx_dep_body_source index_source calls -> fx_index_external_trace_adequacy index_source distinct ->
  Forall2 (fx_observe_expiry_event_source source) expiry_events expiry_groups ->
  Forall2 (fx_expire_check_event_source source) compare_events compare_groups ->
  Forall2 (fx_observe_check_event_source index_source source)
    [FxCheckPrepare side_events; FxCheckPrepare root_events; FxCheckComponents component_events;
      FxCheckPrepare [FxPrepareDependency calls; FxPrepareIndex distinct];
      FxCheckExpiry expiry_events; FxCheckCompare compare_events; FxCheckCase]
    [concat side_groups; concat root_groups; concat component_groups; [];
      concat expiry_groups; concat compare_groups; []].
Proof.
  intros Hside Hroots Hcomponents Hcalls Hdistinct Hexpiry Hcompare.
  constructor; [cbn [fx_observe_check_event_source]; eauto |].
  constructor; [cbn [fx_observe_check_event_source]; eauto |].
  constructor; [cbn [fx_observe_check_event_source]; eauto |].
  constructor.
  - cbn [fx_observe_check_event_source].
    exists [[]; []]; split; [|reflexivity].
    constructor; [cbn [fx_observe_prepare_event_source]; auto |].
    constructor; [cbn [fx_observe_prepare_event_source]; auto | constructor].
  - constructor; [cbn [fx_observe_check_event_source]; eauto |].
    constructor; [cbn [fx_observe_check_event_source]; eauto |].
    constructor; [reflexivity | constructor].
Qed.

(** The strict checker retains each phase result, callback receipt and source-work bound. *)
Theorem fx_observe_plan_check_source : fx_observe_plan_check_source_statement.
Proof.
  intros X C A B D EX S SS ix cb ib index_source source budget roots p
    Herase Hbounded Hlaws Hexpiry.
  destruct Hexpiry as [Hencode [Htarget [Hencode_bound Htarget_bound]]].
  assert (Hexpiry : fx_observe_expiry_source_laws EX S source budget)
    by (repeat split; assumption).
  assert (Hcompare : fx_observe_compare_source_laws EX source budget) by (split; assumption).
  pose proof (fx_prepare_side_adequate EX S SS cb ib index_source source Herase Hbounded Hlaws
    (System.constraints S)) as Hside.
  pose proof (fx_prepare_roots_check_adequate EX S SS cb ib index_source source Herase
    Hbounded Hlaws roots) as Hroots.
  pose proof (fx_observe_components_source X C A B D EX S SS cb ib index_source source budget
    (observation_components p) Herase Hbounded Hlaws Hcompare) as Hcomponents.
  pose proof (fx_observe_unknowns_adequate X C A B EX S SS cb ib index_source Herase Hbounded Hlaws)
    as Hunknowns.
  unfold fx_observe_plan_check.
  destruct (fx_observe_side_free cb (System.constraints S)) as [side side_events].
  destruct (fx_observe_roots_check S cb roots) as [root root_events].
  destruct (fx_observe_components EX S SS cb (observation_components p))
    as [components component_events].
  destruct (fx_dep_unknowns_input cb (System.constraints S)) as [input calls].
  destruct (fxi_distinct_counted cb input) as [unknown distinct].
  cbn [fst snd] in Hside, Hroots, Hcomponents, Hunknowns.
  destruct Hside as [Hside_result [Hside_source Hside_work]].
  destruct Hroots as [Hroot_result [Hroot_source Hroot_work]].
  destruct Hcomponents as
    [component_groups [Hcomponent_source [Hcomponent_result Hcomponent_work]]].
  destruct Hunknowns as [Hunknown [Hcalls [Hdistinct Hunknown_work]]]; subst unknown.
  pose proof (fx_observe_expiry_fold_source X C A D EX S ix source budget
    (observation_components p) (unknowns EX S SS) Hexpiry) as Hfold.
  destruct (fx_observe_expiry_fold EX S ix (observation_components p) (unknowns EX S SS))
    as [expiration expiry_events].
  cbn [fst snd] in Hfold; destruct Hfold as [expiry_groups [Hexpiry_source [Hresult Hexpiry_work]]].
  change (expiration = observation_expirations EX S SS ix (observation_components p)) in Hresult.
  subst expiration.
  pose proof (fx_expire_check_source X C A D EX source budget (observation_expire p)
    (observation_expirations EX S SS ix (observation_components p)) Hcompare) as Hcompare_source.
  destruct (fx_expire_check EX (observation_expire p)
    (observation_expirations EX S SS ix (observation_components p))) as [expires compare_events].
  cbn [fst snd] in Hcompare_source.
  destruct Hcompare_source as [compare_groups [Hcompare_events [Hcompare_result Hcompare_work]]].
  destruct (fx_prepare_plain_receipts X C A B D index_source source budget side_events Hside_source)
    as [side_groups [Hside_receipts Hside_body]].
  destruct (fx_prepare_plain_receipts X C A B D index_source source budget root_events Hroot_source)
    as [root_groups [Hroot_receipts Hroot_body]].
  exists [concat side_groups; concat root_groups; concat component_groups; [];
    concat expiry_groups; concat compare_groups; []].
  split.
  - eapply fx_check_phase_receipts; eassumption.
  - split.
    + unfold observation_plan_check, observation_side_free.
      now rewrite Hside_result, Hroot_result, Hcomponent_result, Hcompare_result.
    + unfold fx_observe_plan_check_budget, fx_observe_prepare_budget.
      change (side = observation_side_free S SS) in Hside_result.
      rewrite <- Hside_result, <- Hroot_result.
      assert (Hconcat : forall groups,
        fold_right (fun body n => fold_right (fun x k => fx_body_weight budget x + k) 0 body + n)
          0 (concat groups) = fx_declared_body_work (fx_body_weight budget) groups).
      { intro groups; change (fx_nested_group_work (fx_body_weight budget) (concat groups) =
          fx_declared_body_work (fx_body_weight budget) groups).
        apply fx_nested_group_concat. }
      destruct (side && root).
      all: cbn [fx_observe_check_work fx_observe_check_event_work
        fx_observe_check_external_budget fx_observe_prepare_work fx_observe_prepare_event_work
        fx_observe_prepare_external_budget fx_declared_body_work fold_right];
        fold (fx_nested_group_work (fx_body_weight budget) (concat side_groups));
        fold (fx_nested_group_work (fx_body_weight budget) (concat root_groups));
        fold (fx_nested_group_work (fx_body_weight budget) (concat component_groups));
        fold (fx_nested_group_work (fx_body_weight budget) (concat expiry_groups));
        fold (fx_nested_group_work (fx_body_weight budget) (concat compare_groups));
        repeat rewrite Hconcat; lia.
Qed.
