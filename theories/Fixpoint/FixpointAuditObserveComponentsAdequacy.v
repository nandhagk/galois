(** * Adequacy of observation component checks

    Component checking retains all class comparisons and forward-boundary callbacks.
    For example, finding one matching class does not suppress later comparisons.
    Builds on: observation ordering, forward checks and comparison adequacy. *)

From Stdlib Require Import List Bool Arith Lia.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Fixpoint Require Import FixpointSystem FixpointSchedule FixpointObserve
  FixpointAuditIndex FixpointAuditScheduleWrapper FixpointAuditWorklistCallbacks
  FixpointAuditNestedCallbacksAdequacy FixpointAuditObserveCompare
  FixpointAuditObserveCompareAdequacy FixpointAuditObserveForward
  FixpointAuditObserveForwardAdequacy
  FixpointAuditObserveOrder FixpointAuditObserveOrderAdequacy FixpointAuditObservePrepareAdequacy
  FixpointAuditObserveComponents.
Import List.ListNotations.

(** * Component receipts *)

Definition fx_component_receipts {X C A B D} (index_source : fx_index_external_source X C B)
    (source : fx_declared_callback_source X C A D) (budget : fx_declared_callback_budget X C A D)
    (events : list (fx_observe_component_event X C B)) : Prop :=
  exists groups, Forall2 (fx_observe_component_event_source index_source source) events groups /\
    fx_declared_body_work (fx_body_weight budget) groups <=
      fold_right (fun event n => fx_observe_component_external_budget budget event + n) 0 events.

Lemma fx_component_external_app X C A B D (budget : fx_declared_callback_budget X C A D)
    (first last : list (fx_observe_component_event X C B)) :
  fold_right (fun event n => fx_observe_component_external_budget budget event + n) 0
    (first ++ last) =
    fold_right (fun event n => fx_observe_component_external_budget budget event + n) 0 first +
      fold_right (fun event n => fx_observe_component_external_budget budget event + n) 0 last.
Proof.
  induction first as [|event rest IH]; cbn [app fold_right]; [reflexivity | rewrite IH; lia].
Qed.

Lemma fx_component_receipts_app X C A B D (index_source : fx_index_external_source X C B)
    (source : fx_declared_callback_source X C A D) (budget : fx_declared_callback_budget X C A D)
    first last :
  fx_component_receipts index_source source budget first ->
  fx_component_receipts index_source source budget last ->
  fx_component_receipts index_source source budget (first ++ last).
Proof.
  intros [left [Hleft Hleft_bound]] [right [Hright Hright_bound]].
  exists (left ++ right); split.
  - now apply Forall2_app.
  - rewrite fx_declared_body_work_app, fx_component_external_app; lia.
Qed.

Lemma fx_component_plain_receipts X C A B D (index_source : fx_index_external_source X C B)
    (source : fx_declared_callback_source X C A D) (budget : fx_declared_callback_budget X C A D)
    events :
  Forall (fun event => fx_observe_component_event_source index_source source event []) events ->
  fx_component_receipts index_source source budget events.
Proof.
  intro Hsource; induction Hsource as [|event rest Hhead Htail IH].
  - exists []; split; [constructor | reflexivity].
  - destruct IH as [groups [Hgroups Hbound]].
    exists ([] :: groups); split; [constructor; assumption |].
    change (fx_declared_body_work (fx_body_weight budget) groups <=
      fx_observe_component_external_budget budget event +
        fold_right (fun e n => fx_observe_component_external_budget budget e + n) 0 rest).
    lia.
Qed.

Lemma fx_component_compare_receipt X C A B D (EX : encoding X)
    (index_source : fx_index_external_source X C B) (source : fx_declared_callback_source X C A D)
    (budget : fx_declared_callback_budget X C A D) events :
  fx_observe_compare_source_laws EX source budget -> Forall (fx_compare_codes EX) events ->
  fx_component_receipts index_source source budget [FxComponentCompare events].
Proof.
  intros Hlaws Hcodes.
  destruct (fx_compare_sources X C A D EX source budget events Hlaws Hcodes)
    as [groups [Hsource Hbound]].
  exists [concat groups]; split.
  - constructor; [|constructor]. cbn [fx_observe_component_event_source]; eauto.
  - change (fx_nested_group_work (fx_body_weight budget) (concat groups) + 0 <=
      fold_right (fun event n => fx_observe_compare_external_budget budget event + n) 0 events + 0).
    rewrite fx_nested_group_concat; lia.
Qed.

Lemma fx_components_work_app X C B (ib : fx_index_external_budget X C B) first last :
  fx_observe_components_work ib (first ++ last) =
    fx_observe_components_work ib first + fx_observe_components_work ib last.
Proof.
  induction first as [|event rest IH].
  - reflexivity.
  - change (fx_observe_component_event_work ib event +
      fx_observe_components_work ib (rest ++ last) =
      (fx_observe_component_event_work ib event + fx_observe_components_work ib rest) +
        fx_observe_components_work ib last).
    rewrite IH; lia.
Qed.

(** * Complete class scans *)

Section ClassChecks.

Context {X C A B D : Type} (EX : encoding X) (ib : fx_index_external_budget X C B).

Context (index_source : fx_index_external_source X C B).

Context (source : fx_declared_callback_source X C A D).

Context (budget : fx_declared_callback_budget X C A D).

Context (Hlaws : fx_observe_compare_source_laws EX source budget).

Lemma fx_component_class_adequate component classes :
  let '(out, events) := @fx_component_in_classes X C B EX component classes in
  out = existsb (observation_seteq EX component) classes /\
    fx_component_receipts index_source source budget events /\
    fx_observe_components_work ib events <= fx_component_in_classes_budget EX component classes.
Proof.
  induction classes as [|class rest IH].
  - split; [reflexivity |]. split.
    + apply fx_component_plain_receipts; constructor; [reflexivity | constructor].
    + reflexivity.
  - cbn [fx_component_in_classes existsb fx_component_in_classes_budget].
    pose proof (fx_observe_seteq_correct X EX component class) as Hcompare.
    pose proof (fx_seteq_codes X EX component class) as Hcodes.
    destruct (fx_observe_seteq EX component class) as [same events].
    destruct (@fx_component_in_classes X C B EX component rest) as [later tail].
    cbn [fst snd] in Hcompare, Hcodes, IH; destruct Hcompare as [Hsame Hwork].
    destruct IH as [Hlater [Hreceipts Htail]].
    split; [now rewrite Hsame, Hlater |]. split.
    + change (fx_component_receipts index_source source budget
        ([FxComponentCase] ++ [FxComponentCompare events] ++ tail)).
      apply fx_component_receipts_app.
      * apply fx_component_plain_receipts; constructor; [reflexivity | constructor].
      * apply fx_component_receipts_app; [|exact Hreceipts].
        apply (fx_component_compare_receipt X C A B D EX index_source source budget events Hlaws
          Hcodes).
    + change (1 + (fx_observe_compare_work events + fx_observe_components_work ib tail) <=
        1 + fx_observe_seteq_budget EX component class +
          fx_component_in_classes_budget EX component rest).
      lia.
Qed.

Lemma fx_components_classes_adequate order classes :
  let '(out, events) := @fx_components_in_classes X C B EX order classes in
  out = forallb (fun component => existsb (observation_seteq EX component) classes) order /\
    fx_component_receipts index_source source budget events /\
    fx_observe_components_work ib events <= fx_components_in_classes_budget EX order classes.
Proof.
  induction order as [|component rest IH].
  - split; [reflexivity |]. split.
    + apply fx_component_plain_receipts; constructor; [reflexivity | constructor].
    + reflexivity.
  - cbn [fx_components_in_classes forallb fx_components_in_classes_budget].
    pose proof (fx_component_class_adequate component classes) as Hhead.
    destruct (@fx_component_in_classes X C B EX component classes) as [found events].
    destruct (@fx_components_in_classes X C B EX rest classes) as [later tail].
    cbn [fst snd] in Hhead, IH; destruct Hhead as [Hfound [Hreceipts Hwork]].
    destruct IH as [Hlater [Htail Htail_work]].
    split; [now rewrite Hfound, Hlater |]. split.
    + change (fx_component_receipts index_source source budget
        ([FxComponentCase] ++ events ++ tail)).
      apply fx_component_receipts_app.
      * apply fx_component_plain_receipts; constructor; [reflexivity | constructor].
      * apply fx_component_receipts_app; assumption.
    + change (1 + fx_observe_components_work ib (events ++ tail) <=
        1 + fx_component_in_classes_budget EX component classes +
          fx_components_in_classes_budget EX rest classes).
      rewrite fx_components_work_app; lia.
Qed.

Lemma fx_components_nonempty_adequate order :
  let '(out, events) := @fx_components_nonempty X C B order in
  out = forallb (fun component =>
    match component with
    | [] => false
    | _ => true
    end) order /\
    Forall (fun event => fx_observe_component_event_source index_source source event []) events /\
    fx_observe_components_work ib events <= 1 + length order.
Proof.
  induction order as [|component rest IH].
  - split; [reflexivity |]. split; [constructor; [reflexivity | constructor] | reflexivity].
  - cbn [fx_components_nonempty forallb].
    destruct (@fx_components_nonempty X C B rest) as [later events].
    cbn [fst snd] in IH; destruct IH as [Hlater [Hsource Hwork]].
    split; [now rewrite Hlater |]. split.
    + constructor; [reflexivity | exact Hsource].
    + change (1 + fx_observe_components_work ib events <= 1 + length (component :: rest));
        cbn [length]; lia.
Qed.

End ClassChecks.

(** The component check assembles the receipts from each of its strict phases. *)
Lemma fx_components_phase_receipts X C A B D (EX : encoding X)
    (index_source : fx_index_external_source X C B) (source : fx_declared_callback_source X C A D)
    (budget : fx_declared_callback_budget X C A D) (order : list (list X))
    class_events nd_events dep_events unknown_events cover_events nonempty_events belongs_events
    forward_events :
  fx_observe_compare_source_laws EX source budget ->
  Forall (fx_observe_order_event_source index_source) class_events ->
  Forall (fx_compare_codes EX) nd_events -> fx_dep_body_source index_source dep_events ->
  fx_index_external_trace_adequacy index_source unknown_events ->
  Forall (fx_compare_codes EX) cover_events ->
  Forall (fun event => fx_observe_component_event_source index_source source event [])
    nonempty_events ->
  fx_component_receipts index_source source budget belongs_events ->
  Forall (fx_observe_forward_event_source index_source) forward_events ->
  fx_component_receipts index_source source budget
    ([FxComponentOrder class_events; FxComponentList (length order + length (concat order));
      FxComponentCompare nd_events; FxComponentDependency dep_events;
      FxComponentIndex unknown_events;
      FxComponentList (length order + length (concat order)); FxComponentCompare cover_events] ++
      nonempty_events ++ belongs_events ++ [FxComponentForward forward_events]).
Proof.
  intros Hcompare Horder Hnodup Hdeps Hindex Hcover Hnonempty Hbelongs Hforward.
  change (fx_component_receipts index_source source budget
    ([FxComponentOrder class_events; FxComponentList (length order + length (concat order))] ++
      [FxComponentCompare nd_events] ++
      [FxComponentDependency dep_events; FxComponentIndex unknown_events;
        FxComponentList (length order + length (concat order))] ++
      [FxComponentCompare cover_events] ++ nonempty_events ++ belongs_events ++
      [FxComponentForward forward_events])).
  apply fx_component_receipts_app.
  - apply fx_component_plain_receipts.
    constructor; [cbn [fx_observe_component_event_source]; auto |].
    constructor; [reflexivity | constructor].
  - apply fx_component_receipts_app.
    + apply (fx_component_compare_receipt X C A B D EX index_source source budget nd_events
        Hcompare Hnodup).
    + apply fx_component_receipts_app.
      * apply fx_component_plain_receipts.
        constructor; [cbn [fx_observe_component_event_source]; auto |].
        constructor; [cbn [fx_observe_component_event_source]; auto |].
        constructor; [reflexivity | constructor].
      * apply fx_component_receipts_app.
        -- apply (fx_component_compare_receipt X C A B D EX index_source source budget cover_events
             Hcompare Hcover).
        -- apply fx_component_receipts_app.
           ++ now apply fx_component_plain_receipts.
           ++ apply fx_component_receipts_app; [exact Hbelongs |].
              apply fx_component_plain_receipts; constructor;
                [cbn [fx_observe_component_event_source]; auto | constructor].
Qed.

(** Component validation keeps every strict comparison and forward-boundary invocation. *)
Theorem fx_observe_components_source : fx_observe_components_source_statement.
Proof.
  intros X C A B D EX S SS cb ib index_source source budget order Herase Hbounded Hlaws Hcompare.
  pose proof (fx_observe_order_source X C A B EX S SS cb ib index_source Herase Hbounded Hlaws)
    as Horder.
  pose proof (fx_observe_nodup_correct X EX (concat order)) as Hnodup.
  pose proof (fx_nodup_codes X EX (concat order)) as Hnodup_codes.
  pose proof (fx_observe_unknowns_adequate X C A B EX S SS cb ib index_source Herase Hbounded
    Hlaws) as Hunknowns.
  unfold fx_observe_components.
  destruct (fx_observe_order EX S SS cb) as [classes class_events].
  destruct (fx_observe_nodup EX (concat order)) as [nodup nd_events].
  destruct (fx_dep_unknowns_input cb (System.constraints S)) as [input dep_events].
  destruct (fxi_distinct_counted cb input) as [unknown unknown_events].
  cbn [fst snd] in Horder, Hnodup, Hnodup_codes, Hunknowns.
  destruct Horder as [Horder_source [Hclasses Horder_work]].
  destruct Hnodup as [Hnodup_result Hnodup_work].
  destruct Hunknowns as [Hunknown [Hdep_source [Hindex_source Hunknown_work]]].
  subst classes unknown.
  pose proof (fx_observe_seteq_correct X EX (concat order) (unknowns EX S SS)) as Hcover.
  pose proof (fx_seteq_codes X EX (concat order) (unknowns EX S SS)) as Hcover_codes.
  destruct (fx_observe_seteq EX (concat order) (unknowns EX S SS)) as [cover cover_events].
  cbn [fst snd] in Hcover, Hcover_codes; destruct Hcover as [Hcover_result Hcover_work].
  pose proof (fx_components_nonempty_adequate ib index_source source order) as Hnonempty.
  destruct (@fx_components_nonempty X C B order) as [nonempty nonempty_events].
  cbn [fst snd] in Hnonempty.
  destruct Hnonempty as [Hnonempty_result [Hnonempty_source Hnonempty_work]].
  pose proof (fx_components_classes_adequate EX ib index_source source budget Hcompare
    order (observation_order EX S SS)) as Hbelongs.
  destruct (@fx_components_in_classes X C B EX order (observation_order EX S SS))
    as [belongs belongs_events].
  cbn [fst snd] in Hbelongs.
  destruct Hbelongs as [Hbelongs_result [Hbelongs_receipts Hbelongs_work]].
  pose proof (fx_observe_forward_source X C A B EX S SS cb ib index_source order Herase Hbounded
    (proj1 Hlaws) (proj1 (proj2 Hlaws)) (proj2 (proj2 (proj2 Hlaws)))) as Hforward.
  destruct (fx_observe_forward_run cb (System.constraints S) order) as [forward forward_events].
  cbn [fst snd] in Hforward; destruct Hforward as [Hforward_source [Hforward_result Hforward_work]].
  pose proof (fx_components_phase_receipts X C A B D EX index_source source budget order
    class_events
    nd_events dep_events unknown_events cover_events nonempty_events belongs_events forward_events
    Hcompare Horder_source Hnodup_codes Hdep_source Hindex_source Hcover_codes Hnonempty_source
    Hbelongs_receipts Hforward_source) as Hall.
  destruct Hall as [bodies [Hsource Hbody]].
  exists bodies; split.
  - repeat rewrite <- app_assoc in Hsource; exact Hsource.
  - split.
    + unfold observation_components_check.
      now rewrite Hnodup_result, Hcover_result, Hnonempty_result, Hbelongs_result, Hforward_result.
    + unfold fx_observe_components_budget.
      repeat rewrite fx_components_work_app.
      repeat rewrite <- app_assoc in Hbody.
      change (fx_declared_body_work (fx_body_weight budget) bodies <=
        fold_right (fun event n => fx_observe_component_external_budget budget event + n) 0
          ([FxComponentOrder class_events; FxComponentList (length order + length (concat order));
            FxComponentCompare nd_events; FxComponentDependency dep_events;
            FxComponentIndex unknown_events; FxComponentList (length order + length (concat order));
            FxComponentCompare cover_events] ++ nonempty_events ++ belongs_events ++
            [FxComponentForward forward_events])) in Hbody.
      cbn [fx_observe_components_work fx_observe_component_event_work fold_right] in *.
      lia.
Qed.
