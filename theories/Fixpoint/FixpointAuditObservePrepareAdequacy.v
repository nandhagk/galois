(** * Adequacy of observation preparation

    Preparation retains its strict checks and the selected order and lifetime computations.
    For example, repeated observation roots each retain their own membership check.
    Builds on: the observation order and expiry adequacy proofs. *)

From Stdlib Require Import List Bool PArith Arith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet CollectionsAuditFinSet
  CollectionsAuditFinSetAdequacy.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointSchedule FixpointObserve
  FixpointAuditIndex FixpointAuditIndexAdequacy FixpointAuditScheduleWrapper
  FixpointAuditScheduleWrapperAdequacy FixpointAuditWorklistCallbacks
  FixpointAuditNestedCallbacksAdequacy
  FixpointAuditObserveForwardAdequacy FixpointAuditObserveOrder FixpointAuditObserveOrderAdequacy
  FixpointAuditObserveExpiry FixpointAuditObserveExpiryAdequacy FixpointAuditObservePrepare.
Import List.ListNotations.

(** * Repeated unknown construction *)

Lemma fx_observe_unknowns_adequate X C A B (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B)
    (ib : fx_index_external_budget X C B) (source : fx_index_external_source X C B) :
  fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
  fx_dep_source_laws cb source ->
  let '(input, calls) := fx_dep_unknowns_input cb (System.constraints S) in
  let '(unknown, distinct) := fxi_distinct_counted cb input in
  unknown = unknowns EX S SS /\ fx_dep_body_source source calls /\
    fx_index_external_trace_adequacy source distinct /\
    fx_dep_events_work ib calls + fx_index_adapter_work ib distinct <=
      fx_dep_build_budget EX S SS ib.
Proof.
  intros Herase Hbounded Hlaws.
  pose proof (fx_dep_unknowns_erases X C A B EX S SS cb (System.constraints S) Herase) as Hinput.
  pose proof (fx_dep_unknowns_work X C A B EX S SS cb ib (System.constraints S) Herase Hbounded)
    as Hinput_work.
  pose proof (fx_dep_unknowns_source X C B cb source (System.constraints S) Hlaws) as Hinput_source.
  destruct (fx_dep_unknowns_input cb (System.constraints S)) as [input calls].
  cbn [fst snd] in Hinput, Hinput_work, Hinput_source; subst input.
  pose proof (fxi_distinct_adequate X C B EX cb ib (fx_dep_unknowns_native S SS)
    (proj1 Herase) (proj1 (proj2 Hbounded))) as Hdistinct.
  pose proof (fx_dep_distinct_source X C B cb source (fx_dep_unknowns_native S SS) Hlaws)
    as Hdistinct_source.
  fold (fx_dep_unknowns_native S SS).
  destruct (fxi_distinct_counted cb (fx_dep_unknowns_native S SS)) as [unknown distinct].
  cbn [fst snd] in Hdistinct, Hdistinct_source |- *.
  destruct Hdistinct as [Hunknown Hdistinct_work].
  change (unknown = unknowns EX S SS) in Hunknown.
  split; [exact Hunknown |]. split; [exact Hinput_source |]. split; [exact Hdistinct_source |].
  unfold fx_dep_build_budget; fold (fx_dep_unknowns_native S SS) in Hinput_work.
  lia.
Qed.

(** * Strict side and root checks *)

Lemma fx_prepare_work_app X C B (ib : fx_index_external_budget X C B) first last :
  fx_observe_prepare_work ib (first ++ last) =
    fx_observe_prepare_work ib first + fx_observe_prepare_work ib last.
Proof.
  induction first as [|event rest IH].
  - reflexivity.
  - change (fx_observe_prepare_event_work ib event + fx_observe_prepare_work ib (rest ++ last) =
      (fx_observe_prepare_event_work ib event + fx_observe_prepare_work ib rest) +
        fx_observe_prepare_work ib last).
    rewrite IH; lia.
Qed.

Section PrepareChecks.

Context {X C A B D : Type} (EX : encoding X) (S : System.t X C A) (SS : System.static S).

Context (cb : fx_index_external_model X C B) (ib : fx_index_external_budget X C B).

Context (index_source : fx_index_external_source X C B).

Context (source : fx_declared_callback_source X C A D).

Context (Herase : fx_index_external_erases EX S SS cb).

Context (Hbounded : fx_index_external_bounded cb ib).

Context (Hlaws : fx_dep_source_laws cb index_source).

Lemma fx_prepare_side_adequate cs :
  let '(out, events) := fx_observe_side_free cb cs in
  out = forallb (fun c =>
    match side_targets SS c with
    | [] => true
    | _ => false
    end) cs /\
    Forall (fun event => fx_observe_prepare_event_source index_source source event []) events /\
    fx_observe_prepare_work ib events <= 1 + 4 * length cs + fx_dep_callback_budget ib cs.
Proof.
  destruct Herase as [_ [_ [Hsides _]]].
  destruct Hbounded as [_ [_ [_ [Hsbound _]]]].
  destruct Hlaws as [_ [_ [Hsource _]]].
  induction cs as [|c rest IH].
  - split; [reflexivity |]. split; [constructor; [reflexivity | constructor] | reflexivity].
  - cbn [fx_observe_side_free forallb fx_dep_callback_budget].
    pose proof (Hsides c) as Hside; pose proof (Hsbound c) as Hbody.
    pose proof (Hsource c) as Hcall.
    destruct (fxi_sides cb c) as [sides body]; cbn [fst snd] in Hside, Hbody, Hcall; subst sides.
    destruct (fx_observe_side_free cb rest) as [later events].
    cbn [fst snd] in IH; destruct IH as [Hresult [Hreceipts Hwork]].
    split; [now rewrite Hresult |]. split.
    + constructor; [reflexivity |]. constructor; [|exact Hreceipts].
      cbn [fx_observe_prepare_event_source fx_index_external_trace_adequacy];
        split; [constructor; [exact Hcall | constructor] | reflexivity].
    + change (1 + ((3 + fxi_body_work ib body + 0) + fx_observe_prepare_work ib events) <=
        1 + 4 * Datatypes.S (length rest) +
          (fxi_target_bound ib c + fxi_deps_bound ib c + fxi_sides_bound ib c +
            fx_dep_callback_budget ib rest)).
      lia.
Qed.

Lemma fx_prepare_roots_mem_adequate universe roots :
  let '(out, events) := fx_observe_roots_mem cb universe roots in
  out = forallb (fun x => FinSet.mem EX x universe) roots /\
    Forall (fun event => fx_observe_prepare_event_source index_source source event []) events /\
    fx_observe_prepare_work ib events <= fx_observe_roots_mem_budget EX ib roots.
Proof.
  induction roots as [|x rest IH].
  - split; [reflexivity |]. split; [constructor; [reflexivity | constructor] | reflexivity].
  - cbn [fx_observe_roots_mem forallb fx_observe_roots_mem_budget].
    pose proof (fx_forward_mem_adequate X C B EX cb ib index_source x universe
      (proj1 Herase x) (proj1 (proj2 Hbounded) x) (proj1 Hlaws x)) as Hmem.
    destruct (audit_finset_mem (fxi_encode cb) x universe) as [present mem].
    destruct (fx_observe_roots_mem cb universe rest) as [later events].
    cbn [fst snd] in Hmem, IH; destruct Hmem as [Hpresent [Hsource Hwork]].
    destruct IH as [Hresult [Hreceipts Htail]].
    split; [now rewrite Hpresent, Hresult |]. split.
    + constructor; [reflexivity |]. constructor; [|exact Hreceipts].
      cbn [fx_observe_prepare_event_source]; split; [exact Hsource | reflexivity].
    + change (1 + (audit_finset_source_work (fxi_body_work ib) mem +
        fx_observe_prepare_work ib events) <=
        8 + 5 * Pos.size_nat (encode EX x) + fxi_encode_bound ib x +
          fx_observe_roots_mem_budget EX ib rest).
      lia.
Qed.

Lemma fx_prepare_roots_check_adequate roots :
  let '(out, events) := fx_observe_roots_check S cb roots in
  out = observation_roots_check EX S SS roots /\
    Forall (fun event => fx_observe_prepare_event_source index_source source event []) events /\
    fx_observe_prepare_work ib events <= fx_dep_build_budget EX S SS ib +
      fxi_set_input_budget EX ib (unknowns EX S SS) + fx_observe_roots_mem_budget EX ib roots.
Proof.
  pose proof (fx_observe_unknowns_adequate X C A B EX S SS cb ib index_source
    Herase Hbounded Hlaws) as Hunknowns.
  unfold fx_observe_roots_check.
  destruct (fx_dep_unknowns_input cb (System.constraints S)) as [input calls].
  destruct (fxi_distinct_counted cb input) as [unknown distinct].
  cbn [fst snd] in Hunknowns; destruct Hunknowns as [Hunknown [Hcalls [Hdistinct Hunknown_work]]].
  subst unknown.
  pose proof (audit_finset_of_list_erases X B (fxi_encode cb) EX (unknowns EX S SS)
    (fun x _ => proj1 Herase x)) as Hset.
  pose proof (audit_finset_of_list_source_bound X B (fxi_encode cb) (fxi_body_work ib)
    (unknowns EX S SS)) as Hset_work.
  pose proof (fxi_set_budget_bound X C B EX cb ib (unknowns EX S SS)
    (proj1 Herase) (proj1 (proj2 Hbounded))) as Hset_budget.
  pose proof (fx_forward_set_fold_source X C B cb index_source (unknowns EX S SS)
    (proj1 Hlaws) FinSet.empty) as Hset_source.
  unfold audit_finset_of_list in Hset_source.
  destruct (audit_finset_of_list (fxi_encode cb) (unknowns EX S SS)) as [universe set]
    eqn:Hset_call.
  unfold audit_finset_of_list in Hset_call; rewrite Hset_call in Hset_source.
  cbn [fst snd] in Hset, Hset_work, Hset_source; subst universe.
  pose proof (fx_prepare_roots_mem_adequate (FinSet.of_list EX (unknowns EX S SS)) roots) as Hmem.
  destruct (fx_observe_roots_mem cb (FinSet.of_list EX (unknowns EX S SS)) roots) as [out events].
  cbn [fst snd] in Hmem |- *; destruct Hmem as [Hresult [Hsource Hwork]].
  split; [exact Hresult |]. split.
  - constructor; [cbn [fx_observe_prepare_event_source]; auto |].
    constructor; [cbn [fx_observe_prepare_event_source]; auto |].
    constructor; [cbn [fx_observe_prepare_event_source]; auto | exact Hsource].
  - change (fx_dep_events_work ib calls + (fx_index_adapter_work ib distinct +
      (audit_finset_source_work (fxi_body_work ib) set + fx_observe_prepare_work ib events)) <=
      fx_dep_build_budget EX S SS ib + fxi_set_input_budget EX ib (unknowns EX S SS) +
        fx_observe_roots_mem_budget EX ib roots).
    lia.
Qed.

End PrepareChecks.

(** * Preparation receipts and selected branch *)

Definition fx_prepare_receipts {X C A B D} (index_source : fx_index_external_source X C B)
    (source : fx_declared_callback_source X C A D) (budget : fx_declared_callback_budget X C A D)
    (events : list (fx_observe_prepare_event X C B)) : Prop :=
  exists groups, Forall2 (fx_observe_prepare_event_source index_source source) events groups /\
    fx_declared_body_work (fx_body_weight budget) groups <=
      fold_right (fun event n => fx_observe_prepare_external_budget budget event + n) 0 events.

Lemma fx_prepare_external_app X C A B D (budget : fx_declared_callback_budget X C A D)
    (first last : list (fx_observe_prepare_event X C B)) :
  fold_right (fun event n => fx_observe_prepare_external_budget budget event + n) 0
    (first ++ last) =
    fold_right (fun event n => fx_observe_prepare_external_budget budget event + n) 0 first +
      fold_right (fun event n => fx_observe_prepare_external_budget budget event + n) 0 last.
Proof.
  induction first as [|event rest IH]; cbn [app fold_right]; [reflexivity | rewrite IH; lia].
Qed.

Lemma fx_prepare_receipts_app X C A B D (index_source : fx_index_external_source X C B)
    (source : fx_declared_callback_source X C A D) (budget : fx_declared_callback_budget X C A D)
    first last :
  fx_prepare_receipts index_source source budget first ->
  fx_prepare_receipts index_source source budget last ->
  fx_prepare_receipts index_source source budget (first ++ last).
Proof.
  intros [left [Hleft Hleft_bound]] [right [Hright Hright_bound]].
  exists (left ++ right); split.
  - now apply Forall2_app.
  - rewrite fx_declared_body_work_app, fx_prepare_external_app; lia.
Qed.

Lemma fx_prepare_plain_receipts X C A B D (index_source : fx_index_external_source X C B)
    (source : fx_declared_callback_source X C A D) (budget : fx_declared_callback_budget X C A D)
    events :
  Forall (fun event => fx_observe_prepare_event_source index_source source event []) events ->
  fx_prepare_receipts index_source source budget events.
Proof.
  intro Hsource; induction Hsource as [|event rest Hhead Htail IH].
  - exists []; split; [constructor | reflexivity].
  - destruct IH as [groups [Hgroups Hbound]].
    exists ([] :: groups); split; [constructor; assumption |].
    change (fx_declared_body_work (fx_body_weight budget) groups <=
      fx_observe_prepare_external_budget budget event +
        fold_right (fun e n => fx_observe_prepare_external_budget budget e + n) 0 rest).
    lia.
Qed.

Lemma fx_prepare_expiry_receipt X C A B D (index_source : fx_index_external_source X C B)
    (source : fx_declared_callback_source X C A D) (budget : fx_declared_callback_budget X C A D)
    events groups :
  Forall2 (fx_observe_expiry_event_source source) events groups ->
  fx_declared_body_work (fx_body_weight budget) groups <=
    fold_right (fun event n => fx_observe_expiry_external_budget budget event + n) 0 events ->
  fx_prepare_receipts index_source source budget [FxPrepareExpiry events].
Proof.
  intros Hsource Hbound; exists [concat groups]; split.
  - constructor; [|constructor]. cbn [fx_observe_prepare_event_source]; eauto.
  - change (fx_nested_group_work (fx_body_weight budget) (concat groups) + 0 <=
      fold_right (fun event n => fx_observe_expiry_external_budget budget event + n) 0 events + 0).
    rewrite fx_nested_group_concat; lia.
Qed.

(** An accepted preparation combines the strict check receipts with its selected expiry bodies. *)
Lemma fx_prepare_selected_receipts X C A B D (index_source : fx_index_external_source X C B)
    (source : fx_declared_callback_source X C A D) (budget : fx_declared_callback_budget X C A D)
    side_events root_events order_events calls distinct expiry_events groups :
  Forall (fun event => fx_observe_prepare_event_source index_source source event []) side_events ->
  Forall (fun event => fx_observe_prepare_event_source index_source source event []) root_events ->
  Forall (fx_observe_order_event_source index_source) order_events ->
  fx_dep_body_source index_source calls -> fx_index_external_trace_adequacy index_source distinct ->
  Forall2 (fx_observe_expiry_event_source source) expiry_events groups ->
  fx_declared_body_work (fx_body_weight budget) groups <=
    fold_right (fun event n => fx_observe_expiry_external_budget budget event + n) 0
      expiry_events ->
  fx_prepare_receipts index_source source budget
    (side_events ++ root_events ++ [FxPrepareOrder order_events; FxPrepareDependency calls;
      FxPrepareIndex distinct; FxPrepareExpiry expiry_events]).
Proof.
  intros Hside Hroots Horder Hcalls Hdistinct Hgroups Hwork.
  assert (Hplain : Forall
    (fun event => fx_observe_prepare_event_source index_source source event [])
    (side_events ++ root_events ++ [FxPrepareOrder order_events;
      FxPrepareDependency calls; FxPrepareIndex distinct])).
  { repeat rewrite Forall_app; repeat split; try assumption.
    constructor; [cbn [fx_observe_prepare_event_source]; auto |].
    constructor; [cbn [fx_observe_prepare_event_source]; auto |].
    constructor; [cbn [fx_observe_prepare_event_source]; auto | constructor]. }
  pose proof (fx_prepare_plain_receipts X C A B D index_source source budget _ Hplain)
    as Hplain_run.
  pose proof (fx_prepare_expiry_receipt X C A B D index_source source budget expiry_events groups
    Hgroups Hwork) as Hexpiry_run.
  pose proof (fx_prepare_receipts_app X C A B D index_source source budget _ _ Hplain_run
    Hexpiry_run)
    as Hcombined.
  unfold fx_prepare_receipts in *.
  destruct Hcombined as [bodies [Hsource Hbound]].
  exists bodies; repeat rewrite <- app_assoc in Hsource, Hbound; split; assumption.
Qed.

(** Preparation records its actual strict checks and selected lifetime construction. *)
Theorem fx_observe_prepare_source : fx_observe_prepare_source_statement.
Proof.
  intros X C A B D EX S SS ix cb ib index_source source budget roots Herase Hbounded Hlaws Hexpiry.
  pose proof (fx_prepare_side_adequate EX S SS cb ib index_source source Herase Hbounded Hlaws
    (System.constraints S)) as Hside.
  pose proof (fx_prepare_roots_check_adequate EX S SS cb ib index_source source Herase
    Hbounded Hlaws roots) as Hroots.
  unfold fx_observe_prepare.
  destruct (fx_observe_side_free cb (System.constraints S)) as [side side_events].
  destruct (fx_observe_roots_check S cb roots) as [root root_events].
  cbn [fst snd] in Hside, Hroots.
  destruct Hside as [Hside_result [Hside_source Hside_work]].
  destruct Hroots as [Hroot_result [Hroot_source Hroot_work]].
  change (side = observation_side_free S SS) in Hside_result.
  destruct (side && root) eqn:Hbranch.
  - pose proof (fx_observe_order_source X C A B EX S SS cb ib index_source Herase Hbounded Hlaws)
      as Horder.
    destruct (fx_observe_order EX S SS cb) as [order order_events].
    cbn [fst snd] in Horder; destruct Horder as [Horder_source [Horder_result Horder_work]].
    pose proof (fx_observe_unknowns_adequate X C A B EX S SS cb ib index_source Herase Hbounded
      Hlaws) as Hunknowns.
    destruct (fx_dep_unknowns_input cb (System.constraints S)) as [input calls].
    destruct (fxi_distinct_counted cb input) as [unknown distinct].
    cbn [fst snd] in Hunknowns; destruct Hunknowns as [Hunknown [Hcalls [Hdistinct Hunknown_work]]].
    subst order unknown.
    pose proof (fx_observe_expiry_fold_correct X C A EX S ix
      (observation_order EX S SS) (unknowns EX S SS)) as Hresult.
    pose proof (fx_observe_expiry_fold_bound X C A EX S ix
      (observation_order EX S SS) (unknowns EX S SS)) as Hfold_work.
    pose proof (fx_expiry_fold_receipts EX S source budget Hexpiry ix
      (observation_order EX S SS) (unknowns EX S SS)) as Hfold_receipts.
    destruct (fx_observe_expiry_fold EX S ix (observation_order EX S SS) (unknowns EX S SS))
      as [expiration expiry_events].
    cbn [fst snd] in Hresult, Hfold_work, Hfold_receipts.
    destruct Hfold_receipts as [groups [Hgroups Hgroup_work]].
    pose proof (fx_prepare_selected_receipts X C A B D index_source source budget side_events
      root_events order_events calls distinct expiry_events groups Hside_source Hroot_source
      Horder_source Hcalls Hdistinct Hgroups Hgroup_work) as Hcombined.
    destruct Hcombined as [bodies [Hsource Hbody]].
    exists bodies; split.
    + repeat rewrite <- app_assoc in Hsource; exact Hsource.
    + split.
      * unfold observation_prepare, observation_canonical, observation_expirations.
        rewrite <- Hside_result, <- Hroot_result, Hbranch; cbn; now rewrite Hresult.
      * unfold fx_observe_prepare_budget.
        rewrite <- Hside_result, <- Hroot_result, Hbranch.
        repeat rewrite fx_prepare_work_app.
        repeat rewrite <- app_assoc in Hbody.
        change (fx_declared_body_work (fx_body_weight budget) bodies <=
          fold_right (fun event n => fx_observe_prepare_external_budget budget event + n) 0
            (side_events ++ root_events ++ [FxPrepareOrder order_events;
              FxPrepareDependency calls; FxPrepareIndex distinct; FxPrepareExpiry expiry_events]))
          in Hbody.
        set (input_native := fx_dep_unknowns_native S SS) in *.
        cbn [fx_observe_prepare_work fx_observe_prepare_event_work fold_right] in *.
        lia.
  - assert (Hplain : Forall
      (fun event => fx_observe_prepare_event_source index_source source event [])
      (side_events ++ root_events ++ [FxPrepareCase])).
    { repeat rewrite Forall_app; repeat split; try assumption.
      constructor; [reflexivity | constructor]. }
    destruct (fx_prepare_plain_receipts X C A B D index_source source budget _ Hplain)
      as [bodies [Hsource Hbody]].
    exists bodies; split; [exact Hsource |]. split.
    + unfold observation_prepare; rewrite <- Hside_result, <- Hroot_result, Hbranch; reflexivity.
    + unfold fx_observe_prepare_budget; rewrite <- Hside_result, <- Hroot_result, Hbranch.
      repeat rewrite fx_prepare_work_app.
      cbn [fx_observe_prepare_work fx_observe_prepare_event_work fold_right] in *; lia.
Qed.
