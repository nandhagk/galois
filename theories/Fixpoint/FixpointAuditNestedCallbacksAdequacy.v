(** * Nested callback source adequacy

    These proofs account for individual callback receipts in the counted nested solver.
    For example, each encoded set key has its own body and per-call allowance.
    Builds on: FixpointAuditNestedCallbacks and declared-worklist callback adequacy. *)

From Stdlib Require Import List PArith PeanoNat Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditCost CollectionsAuditTrie CollectionsAuditFinSet.
From Galois.Order Require Import OrderLattice.
From Galois.Graph Require Import GraphCore GraphPrepare GraphWto GraphAuditBase GraphAuditDfs
  GraphAuditBaseAdequacy GraphAuditDfsAdequacy GraphAuditWto GraphAuditWtoAdequacy.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointWorklist
  FixpointSchedule FixpointNested FixpointAuditIndex FixpointAuditWorklist
    FixpointAuditWorklistCallbacks
  FixpointAuditScheduleWrapper FixpointAuditScheduleWrapperAdequacy FixpointAuditNestedPlan
    FixpointAuditNestedPlanAdequacy
  FixpointAuditNestedMachine FixpointAuditNestedMachineAdequacy FixpointAuditNested
  FixpointAuditNestedAdequacy
  FixpointAuditNestedCallbacks.
Import List.ListNotations.

(** * Bounds for the retained external bodies *)

Definition fx_nested_group_work {B} (weight : B -> nat) (bodies : list (list B)) : nat :=
  fold_right (fun body n => fx_one_body_work weight body + n) 0 bodies.

Lemma fx_nested_entries_body_bound X C A B (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) entries bodies :
  (forall x out body, fx_source_encode_x source x out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_encode_x budget x) ->
  Forall2 (fx_nested_entry_source source) entries bodies ->
  fx_nested_group_work (fx_body_weight budget) bodies <= fx_nested_entries_budget budget entries.
Proof.
  intros Hbound Hreceipts; induction Hreceipts as [|[x code] body entries bodies Hbody Hrest IH].
  - reflexivity.
  - cbn [fx_nested_entry_source] in Hbody.
    specialize (Hbound x code body Hbody).
    change (fx_one_body_work (fx_body_weight budget) body +
      fx_nested_group_work (fx_body_weight budget) bodies <=
      fx_budget_encode_x budget x + fx_nested_entries_budget budget entries); lia.
Qed.

Lemma fx_nested_plan_body_bound X C A B (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) event bodies :
  (forall x out body, fx_source_encode_x source x out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_encode_x budget x) ->
  (forall c out body, fx_source_target source c out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_target budget c) ->
  fx_nested_plan_event_source source event bodies ->
  fx_nested_group_work (fx_body_weight budget) bodies <= fx_nested_plan_external_budget budget
    event.
Proof.
  intros Hencode Htarget Hsource.
  destruct event; cbn [fx_nested_plan_event_source fx_nested_plan_external_budget] in Hsource |- *;
    try (subst bodies; reflexivity).
  - destruct Hsource as [witness [-> Hbody]]; specialize (Htarget _ _ _ Hbody).
    change (fx_one_body_work (fx_body_weight budget) witness + 0 <= fx_budget_target budget
      constraint); lia.
  - destruct Hsource as [witness [-> Hbody]]; specialize (Hencode _ _ _ Hbody).
    change (fx_one_body_work (fx_body_weight budget) witness + 0 <= fx_budget_encode_x budget x);
      lia.
  - destruct Hsource as [witness [-> Hbody]]; specialize (Hencode _ _ _ Hbody).
    change (fx_one_body_work (fx_body_weight budget) witness + 0 <= fx_budget_encode_x budget x);
      lia.
  - destruct Hsource as [witness [-> Hbody]]; specialize (Hencode _ _ _ Hbody).
    change (fx_one_body_work (fx_body_weight budget) witness + 0 <= fx_budget_encode_x budget x);
      lia.
  - eapply fx_nested_entries_body_bound; eassumption.
Qed.

Definition fx_plan_trace_source {X C A B} (source : fx_declared_callback_source X C A B)
    (events : list (fx_nested_plan_event X C)) (groups : list (list (list B))) : Prop :=
  Forall2 (fx_nested_plan_event_source source) events groups.

Lemma fx_plan_trace_body_bound X C A B (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) events groups :
  (forall x out body, fx_source_encode_x source x out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_encode_x budget x) ->
  (forall c out body, fx_source_target source c out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_target budget c) ->
  fx_plan_trace_source source events groups ->
  fx_declared_body_work (fx_body_weight budget) groups <=
    fold_right (fun event n => fx_nested_plan_external_budget budget event + n) 0 events.
Proof.
  intros Hencode Htarget Hsource; induction Hsource as [|event group events groups Hgroup Hrest IH].
  - reflexivity.
  - pose proof (fx_nested_plan_body_bound X C A B source budget event group Hencode Htarget Hgroup)
      as Hbound.
    change (fx_nested_group_work (fx_body_weight budget) group +
      fx_declared_body_work (fx_body_weight budget) groups <=
      fx_nested_plan_external_budget budget event +
      fold_right (fun event n => fx_nested_plan_external_budget budget event + n) 0 events).
    lia.
Qed.

(** * Plan callbacks on their actual operands *)

Section PlanReceipts.
Context {X C A B : Type} (EX : encoding X) (S : System.t X C A)
  (source : fx_declared_callback_source X C A B).
Hypothesis Hencode : forall x, exists body, fx_source_encode_x source x (encode EX x) body.
Hypothesis Htarget : forall c, exists body, fx_source_target source c (System.target S c) body.

Definition fx_plan_has_receipts (events : list (fx_nested_plan_event X C)) : Prop :=
  exists groups, fx_plan_trace_source source events groups.

Lemma fx_plan_receipts_app left right :
  fx_plan_has_receipts left -> fx_plan_has_receipts right -> fx_plan_has_receipts (left ++ right).
Proof.
  intros [left_groups Hleft] [right_groups Hright].
  exists (left_groups ++ right_groups); now apply Forall2_app.
Qed.

Lemma fx_plan_receipts_cons event group rest :
  fx_nested_plan_event_source source event group -> fx_plan_has_receipts rest ->
  fx_plan_has_receipts (event :: rest).
Proof.
  intros Hgroup [groups Hrest]; exists (group :: groups); constructor; assumption.
Qed.

Lemma fx_plan_empty_event event :
  fx_nested_plan_event_source source event [] -> fx_plan_has_receipts [event].
Proof.
  intro Hsource; exists [[]]; constructor; [exact Hsource|constructor].
Qed.

Lemma fx_plan_encoded_event x event :
  (forall body, fx_source_encode_x source x (encode EX x) body ->
    fx_nested_plan_event_source source event [body]) -> fx_plan_has_receipts [event].
Proof.
  intros Hbuild; destruct (Hencode x) as [body Hbody].
  exists [[body]]; constructor; [now apply Hbuild|constructor].
Qed.

Definition fx_plan_pure (event : fx_nested_plan_event X C) : Prop :=
  fx_nested_plan_event_source source event [].

Lemma fx_plan_pure_receipts events : Forall fx_plan_pure events -> fx_plan_has_receipts events.
Proof.
  intro Hall; induction Hall as [|event rest Hhead Htail IH].
  - exists []; constructor.
  - apply fx_plan_receipts_cons with (group := []); assumption.
Qed.

Lemma fx_plan_parse_pure bound tokens :
  Forall fx_plan_pure (snd (@fx_nested_parse X C bound tokens)).
Proof.
  revert tokens; induction bound as [|bound IH]; intro tokens.
  - cbn [fx_nested_parse snd]; repeat constructor; reflexivity.
  - destruct tokens as [|token rest].
    + cbn [fx_nested_parse snd]; repeat constructor; reflexivity.
    + destruct token as [x|h|].
      * pose proof (IH rest) as Htail; cbn [fx_nested_parse].
        destruct (@fx_nested_parse X C bound rest) as [[code after] events]; cbn [snd] in Htail |-
          *.
        constructor; [reflexivity|]. constructor; [reflexivity|].
        apply Forall_app; split; [exact Htail|repeat constructor; reflexivity].
      * pose proof (IH rest) as Hbody; cbn [fx_nested_parse].
        destruct (@fx_nested_parse X C bound rest) as [[body after_body] body_events].
        cbn [snd] in Hbody; pose proof (IH after_body) as Htail.
        destruct (@fx_nested_parse X C bound after_body) as [[tail after] tail_events].
        cbn [snd] in Htail |- *; constructor; [reflexivity|]. constructor; [reflexivity|].
        repeat rewrite Forall_app; repeat split; try assumption; repeat constructor; reflexivity.
      * cbn [fx_nested_parse snd]; repeat constructor; reflexivity.
Qed.

Lemma fx_plan_rows_pure stack code : Forall fx_plan_pure (snd (@fx_nested_rows X C stack code)).
Proof.
  revert stack; induction code as [|x rest IH|h body IHbody rest IHrest]; intro stack.
  - cbn [fx_nested_rows snd]; repeat constructor; reflexivity.
  - pose proof (IH stack) as Htail; cbn [fx_nested_rows].
    destruct (@fx_nested_rows X C stack rest) as [rows events]; cbn [snd] in Htail |- *.
    constructor; [reflexivity|]. apply Forall_app; split; [exact Htail|repeat constructor;
      reflexivity].
  - pose proof (IHbody (h :: stack)) as Hbody; pose proof (IHrest stack) as Htail.
    cbn [fx_nested_rows]; destruct (@fx_nested_rows X C (h :: stack) body) as [rows events].
    destruct (@fx_nested_rows X C stack rest) as [tail later].
    cbn [snd] in Hbody, Htail |- *; constructor; [reflexivity|].
    repeat rewrite Forall_app; repeat split; try assumption; repeat constructor; reflexivity.
Qed.

Lemma fx_plan_heads_pure code : Forall fx_plan_pure (snd (@fx_nested_heads X C code)).
Proof.
  induction code as [|x rest IH|h body IHbody rest IHrest].
  - cbn [fx_nested_heads snd]; repeat constructor; reflexivity.
  - cbn [fx_nested_heads]; destruct (@fx_nested_heads X C rest) as [heads events].
    cbn [snd] in IH |- *; constructor; [reflexivity|exact IH].
  - cbn [fx_nested_heads]; destruct (@fx_nested_heads X C body) as [heads events].
    destruct (@fx_nested_heads X C rest) as [tail later].
    cbn [snd] in IHbody, IHrest |- *; constructor; [reflexivity|].
    repeat rewrite Forall_app; repeat split; try assumption; repeat constructor; reflexivity.
Qed.

Lemma fx_plan_set_entries heads set :
  fx_nested_entries (snd (audit_finset_fold (fx_index_encoder EX) heads set)) =
    map (fun x => FxEncodeEntry x (encode EX x)) heads.
Proof.
  revert set; induction heads as [|x rest IH]; intro set.
  - reflexivity.
  - cbn [audit_finset_fold audit_finset_add fx_index_encoder].
    destruct (audit_trie_set (encode EX x) (x, tt) set) as [next body].
    specialize (IH next); destruct (audit_finset_fold (fx_index_encoder EX) rest next)
      as [out events]; cbn [snd] in IH |- *.
    unfold fx_nested_entries in *; cbn [flat_map app]; now rewrite IH.
Qed.

Lemma fx_plan_entries_receipts heads :
  exists bodies, Forall2 (fx_nested_entry_source source)
    (map (fun x => FxEncodeEntry x (encode EX x)) heads) bodies.
Proof.
  induction heads as [|x rest IH].
  - exists []; constructor.
  - destruct (Hencode x) as [body Hbody]; destruct IH as [bodies Hrest].
    exists (body :: bodies); constructor; assumption.
Qed.

Lemma fx_plan_member_receipts rows :
  fx_plan_has_receipts (snd (@fx_nested_member_fold X C EX rows)).
Proof.
  induction rows as [|[x stack] rest IH].
  - cbn [fx_nested_member_fold snd]; apply fx_plan_empty_event; reflexivity.
  - cbn [fx_nested_member_fold].
    destruct (@fx_nested_member_fold X C EX rest) as [before events]; cbn [snd] in IH.
    destruct (audit_trie_set (encode EX x) (x, stack) before) as [after body]; cbn [snd].
    apply fx_plan_receipts_cons with (group := []); [reflexivity|].
    apply fx_plan_receipts_app; [exact IH|].
    apply fx_plan_encoded_event with (x := x); cbn [fx_nested_plan_event_source]; eauto.
Qed.

Lemma fx_plan_target_receipts cs : fx_plan_has_receipts (snd (fx_nested_target_fold EX S cs)).
Proof.
  induction cs as [|c rest IH].
  - cbn [fx_nested_target_fold snd]; apply fx_plan_empty_event; reflexivity.
  - cbn [fx_nested_target_fold].
    destruct (fx_nested_target_fold EX S rest) as [before events]; cbn [snd] in IH.
    destruct (audit_map_code_get (encode EX (System.target S c)) before) as [raw read_body].
    destruct (audit_trie_set (encode EX (System.target S c))
      (System.target S c, c ::
        match raw with
        | Some values => values
        | None => []
        end) before)
      as [after write_body].
    destruct (Htarget c) as [target_body Htarget_body].
    destruct (Hencode (System.target S c)) as [encode_body Hencode_body].
    cbn [snd]; apply fx_plan_receipts_cons with (group := []); [reflexivity|].
    apply fx_plan_receipts_app; [exact IH|].
    apply fx_plan_receipts_cons with (group := [target_body]); [cbn; eauto|].
    apply fx_plan_receipts_cons with (group := [encode_body]); [cbn; eauto|].
    apply fx_plan_receipts_cons with (group := []); [reflexivity|].
    exists [[encode_body]]; constructor; [cbn; eauto|constructor].
Qed.

Lemma fx_plan_set_receipts heads out events :
  audit_finset_of_list (fx_index_encoder EX) heads = (out, events) ->
  exists bodies, Forall2 (fx_nested_entry_source source) (fx_nested_entries events) bodies.
Proof.
  intro Hrun; pose proof (fx_plan_set_entries heads FinSet.empty) as Hentries.
  unfold audit_finset_of_list in Hrun; rewrite Hrun in Hentries; cbn [snd] in Hentries.
  rewrite Hentries; apply fx_plan_entries_receipts.
Qed.

Lemma fx_plan_all_receipts tokens :
  fx_plan_has_receipts (snd (fx_nested_plan_from_tokens EX S tokens)).
Proof.
  unfold fx_nested_plan_from_tokens, fx_nested_tree.
  pose proof (fx_plan_parse_pure (Datatypes.S (length tokens)) (tokens ++ [WClose])) as Hparse.
  destruct (@fx_nested_parse X C (Datatypes.S (length tokens)) (tokens ++ [WClose]))
    as [[code after] parse_events]; cbn [snd] in Hparse.
  cbn [fst].
  pose proof (fx_plan_rows_pure [] code) as Hrows.
  unfold fx_nested_members; destruct (@fx_nested_rows X C [] code) as [rows row_events].
  cbn [snd] in Hrows; pose proof (fx_plan_member_receipts rows) as Hmembers.
  destruct (@fx_nested_member_fold X C EX rows) as [members member_events]; cbn [snd] in Hmembers.
  pose proof (fx_plan_target_receipts (System.constraints S)) as Htargets.
  unfold fx_nested_targets; destruct (fx_nested_target_fold EX S (System.constraints S))
    as [targets target_events]; cbn [snd] in Htargets.
  pose proof (fx_plan_heads_pure code) as Hheads.
  destruct (@fx_nested_heads X C code) as [heads head_events]; cbn [snd] in Hheads.
  destruct (audit_finset_of_list (fx_index_encoder EX) heads) as [head_set set_events] eqn:Hset.
  destruct (fx_plan_set_receipts heads head_set set_events Hset) as [bodies Hbodies].
  cbn [snd].
  apply fx_plan_receipts_app.
  - apply fx_plan_receipts_cons with (group := []); [reflexivity|].
    apply fx_plan_receipts_cons with (group := []); [reflexivity|].
    now apply fx_plan_pure_receipts.
  - apply fx_plan_receipts_app.
    + apply fx_plan_receipts_app; [now apply fx_plan_pure_receipts|exact Hmembers].
    + apply fx_plan_receipts_app; [exact Htargets|].
      apply fx_plan_receipts_app; [now apply fx_plan_pure_receipts|].
      exists [bodies]; constructor; [exact Hbodies|constructor].
Qed.

End PlanReceipts.

(** * Query receipts and their per-call costs *)

Lemma fx_declared_body_work_app B (weight : B -> nat) left right :
  fx_declared_body_work weight (left ++ right) =
    fx_declared_body_work weight left + fx_declared_body_work weight right.
Proof.
  unfold fx_declared_body_work; induction left as [|group rest IH]; cbn [app fold_right]; lia.
Qed.

Lemma fx_declared_external_budget_app X C A B (budget : fx_declared_callback_budget X C A B)
    left right :
  fx_declared_external_trace_budget budget (left ++ right) =
    fx_declared_external_trace_budget budget left + fx_declared_external_trace_budget budget right.
Proof.
  unfold fx_declared_external_trace_budget; induction left as [|event rest IH]; cbn [app
    fold_right];
    [reflexivity|].
  destruct event; cbn; lia.
Qed.

Section QueryReceipts.
Context {X C A B : Type} (EX : encoding X) (L : lattice A) (S : System.t X C A)
  (source : fx_declared_callback_source X C A B) (budget : fx_declared_callback_budget X C A B).
Hypothesis Hencode : forall x, exists body, fx_source_encode_x source x (encode EX x) body.
Hypothesis Hcontinuation : forall k a, (exists x, fx_declared_query_reachable S (Query.Ask x k)) ->
  exists body, fx_source_continuation source k a (k a) body.
Hypothesis Hencode_bound : forall x out body, fx_source_encode_x source x out body ->
  fx_one_body_work (fx_body_weight budget) body <= fx_budget_encode_x budget x.
Hypothesis Hcontinuation_bound : forall k a out body, fx_source_continuation source k a out body ->
  fx_one_body_work (fx_body_weight budget) body <= fx_budget_continuation budget k a.

Definition fx_query_receipts_bounded (events : audit_trace (fx_declared_call X C A)) : Prop :=
  exists groups, fx_declared_trace_source source events groups /\
    fx_declared_body_work (fx_body_weight budget) groups <= fx_declared_external_trace_budget
      budget events.

Lemma fx_query_receipts_app left right :
  fx_query_receipts_bounded left -> fx_query_receipts_bounded right ->
  fx_query_receipts_bounded (left ++ right).
Proof.
  intros [left_groups [Hleft Hleft_bound]] [right_groups [Hright Hright_bound]].
  exists (left_groups ++ right_groups); split; [now apply Forall2_app|].
  rewrite fx_declared_body_work_app, fx_declared_external_budget_app; lia.
Qed.

Lemma fx_query_receipts_one event group :
  fx_declared_event_source source event group ->
  fx_nested_group_work (fx_body_weight budget) group <=
    fx_declared_external_trace_budget budget [event] ->
  fx_query_receipts_bounded [event].
Proof.
  intros Hsource Hbound; exists [group]; split; [constructor; [exact Hsource|constructor]|].
  change (fx_nested_group_work (fx_body_weight budget) group + 0 <=
    fx_declared_external_trace_budget budget [event]); lia.
Qed.

Lemma fx_query_noncall event :
  (
    match event with
    | AuditCall _ => False
    | _ => True
    end
  ) -> fx_query_receipts_bounded [event].
Proof.
  destruct event; cbn; try contradiction; intro Hnon; apply fx_query_receipts_one with (group :=
    []);
    reflexivity.
Qed.

Lemma fx_query_lookup_receipts values x :
  fx_query_receipts_bounded (snd (@fx_model_lookup X C A EX L values x)).
Proof.
  destruct (Hencode x) as [body Hbody]; pose proof (Hencode_bound x (encode EX x) body Hbody) as
    Hbound.
  unfold fx_model_lookup; destruct (audit_map_code_get (encode EX x) values) as [raw trace].
  destruct raw as [a|]; cbn [snd].
  - change (fx_query_receipts_bounded
      ([AuditCall (FxGet x (encode EX x) values (Some a) trace)] ++ [AuditCase 0 []])).
    apply fx_query_receipts_app.
    + apply fx_query_receipts_one with (group := [body]);
        [cbn; exists body; auto|change (fx_one_body_work (fx_body_weight budget) body + 0 <=
          fx_budget_encode_x budget x + 0); lia].
    + apply fx_query_noncall; exact I.
  - change (fx_query_receipts_bounded
      ([AuditCall (FxGet x (encode EX x) values None trace)] ++ [AuditCase 0 []])).
    apply fx_query_receipts_app.
    + apply fx_query_receipts_one with (group := [body]);
        [cbn; exists body; auto|change (fx_one_body_work (fx_body_weight budget) body + 0 <=
          fx_budget_encode_x budget x + 0); lia].
    + apply fx_query_noncall; exact I.

Qed.

Lemma fx_query_all_receipts q values : fx_declared_query_reachable S q ->
  fx_query_receipts_bounded (snd (@fx_model_query X C A EX L q values)).
Proof.
  induction q as [a|x k IH|x a q IH]; intro Hreachable.
  - apply fx_query_noncall; exact I.
  - pose proof (fx_query_lookup_receipts values x) as Hlookup.
    destruct (fx_model_lookup EX L values x) as [value lookup_events] eqn:Hlookup_run.
    change (fx_query_receipts_bounded lookup_events) in Hlookup.
    assert (Hnext : fx_declared_query_reachable S (k value)).
    { eapply FxReachableAsk; exact Hreachable. }
    specialize (IH value Hnext).
    destruct (fx_model_query EX L (k value) values) as [[[v reads] sides] events] eqn:Hquery.
    change (fx_query_receipts_bounded events) in IH.
    destruct (Hcontinuation k value (ex_intro _ x Hreachable)) as [body Hbody].
    pose proof (Hcontinuation_bound k value (k value) body Hbody) as Hbound.
    cbn [fx_model_query]; rewrite Hlookup_run, Hquery; cbn [snd].
    change (fx_query_receipts_bounded ([AuditCase 1 []] ++ lookup_events ++
      [AuditCall (FxContinuation x value k (k value))] ++ events ++ [AuditConstruct 0 []])).
    apply fx_query_receipts_app; [apply fx_query_noncall; exact I|].
    apply fx_query_receipts_app; [exact Hlookup|].
    apply fx_query_receipts_app.
    + apply fx_query_receipts_one with (group := [body]); [cbn; eauto|].
      change (fx_one_body_work (fx_body_weight budget) body + 0 <=
        fx_budget_continuation budget k value + 0); lia.
    + apply fx_query_receipts_app; [exact IH|apply fx_query_noncall; exact I].
  - assert (Hnext : fx_declared_query_reachable S q) by (eapply FxReachableSide; exact Hreachable).
    specialize (IH Hnext).
    destruct (fx_model_query EX L q values) as [[[v reads] sides] events] eqn:Hquery.
    change (fx_query_receipts_bounded events) in IH.
    cbn [fx_model_query]; rewrite Hquery; cbn [snd].
    change (fx_query_receipts_bounded ([AuditCase 1 []] ++ events ++ [AuditConstruct 1 []])).
    apply fx_query_receipts_app; [apply fx_query_noncall; exact I|].
    apply fx_query_receipts_app; [exact IH|apply fx_query_noncall; exact I].
Qed.

End QueryReceipts.

(** * Machine receipts and per-event allowances *)

Lemma fx_nested_group_concat B (weight : B -> nat) groups :
  fx_nested_group_work weight (concat groups) = fx_declared_body_work weight groups.
Proof.
  induction groups as [|group rest IH].
  - reflexivity.
  - cbn [concat]; unfold fx_nested_group_work at 1.
    rewrite fold_right_app; fold (fx_nested_group_work weight (concat rest)).
    rewrite IH.
    assert (Hfold : forall acc, fold_right (fun body n => fx_one_body_work weight body + n) acc
      group =
      fx_nested_group_work weight group + acc).
    { intro acc; unfold fx_nested_group_work; induction group as [|body tail IHtail];
        cbn [fold_right]; lia. }
    rewrite Hfold; unfold fx_nested_group_work, fx_declared_body_work, fx_one_body_work; cbn;
      reflexivity.
Qed.

Definition fx_machine_trace_source {X C A B} (source : fx_declared_callback_source X C A B)
    (events : list (fx_nested_event X C A)) (groups : list (list (list B))) : Prop :=
  Forall2 (fx_nested_machine_event_source source) events groups.

Definition fx_machine_external_work {X C A B} (budget : fx_declared_callback_budget X C A B)
    (events : list (fx_nested_event X C A)) : nat :=
  fold_right (fun event n => fx_nested_machine_external_budget budget event + n) 0 events.

Definition fx_machine_has_receipts {X C A B} (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) (events : list (fx_nested_event X C A)) : Prop :=
  exists groups, fx_machine_trace_source source events groups /\
    fx_declared_body_work (fx_body_weight budget) groups <= fx_machine_external_work budget events.

Lemma fx_machine_external_work_app X C A B (budget : fx_declared_callback_budget X C A B)
    left right : fx_machine_external_work budget (left ++ right) =
    fx_machine_external_work budget left + fx_machine_external_work budget right.
Proof.
  unfold fx_machine_external_work; induction left as [|event rest IH]; cbn [app fold_right]; lia.
Qed.

Lemma fx_machine_receipts_app X C A B (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) left right :
  fx_machine_has_receipts source budget left -> fx_machine_has_receipts source budget right ->
  fx_machine_has_receipts source budget (left ++ right).
Proof.
  intros [left_groups [Hleft Hleft_bound]] [right_groups [Hright Hright_bound]].
  exists (left_groups ++ right_groups); split; [now apply Forall2_app|].
  rewrite fx_declared_body_work_app, fx_machine_external_work_app; lia.
Qed.

Lemma fx_machine_receipts_one X C A B (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) event group :
  fx_nested_machine_event_source source event group ->
  fx_nested_group_work (fx_body_weight budget) group <= fx_nested_machine_external_budget budget
    event ->
  fx_machine_has_receipts source budget [event].
Proof.
  intros Hsource Hbound; exists [group]; split; [constructor; [exact Hsource|constructor]|].
  change (fx_nested_group_work (fx_body_weight budget) group + 0 <=
    fx_nested_machine_external_budget budget event + 0); lia.
Qed.

Section MachineReceipts.
Context {X C A B : Type} (EX : encoding X) (L : lattice A) (plan : NestedPlan.t X C)
  (mode : strategy) (S : System.t X C A) (source : fx_declared_callback_source X C A B)
  (budget : fx_declared_callback_budget X C A B).
Hypothesis Hsource : fx_nested_machine_source_laws EX L S source budget.

Lemma fx_machine_receipts_cons event group rest :
  fx_nested_machine_event_source source event group ->
  fx_nested_group_work (fx_body_weight budget) group <= fx_nested_machine_external_budget budget
    event ->
  fx_machine_has_receipts source budget rest -> fx_machine_has_receipts source budget (event ::
    rest).
Proof.
  intros Hevent Hbound Hrest.
  change (fx_machine_has_receipts source budget ([event] ++ rest)).
  apply fx_machine_receipts_app; [now apply fx_machine_receipts_one with (group := group)|exact
    Hrest].
Qed.

Lemma fx_machine_case site : fx_machine_has_receipts source budget [FxNestedCase site].
Proof.
  apply fx_machine_receipts_one with (group := []); reflexivity.
Qed.

Lemma fx_machine_query_event events : fx_query_receipts_bounded source budget events ->
  fx_machine_has_receipts source budget [FxNestedQuery events].
Proof.
  intros [groups [Hsource_trace Hbound]].
  apply fx_machine_receipts_one with (group := concat groups).
  - cbn [fx_nested_machine_event_source]; exists groups; auto.
  - cbn [fx_nested_machine_external_budget]; now rewrite fx_nested_group_concat.
Qed.

Lemma fx_machine_set_mem_receipt x set :
  let '(out, events) := audit_finset_mem (fx_index_encoder EX) x set in
  fx_machine_has_receipts source budget [FxNestedSetMem x set out events].
Proof.
  destruct Hsource as [Hencode [_ [_ [_ [_ [_ [_ [Hencode_bound _]]]]]]]].
  destruct (Hencode x) as [body Hbody]; pose proof (Hencode_bound x (encode EX x) body Hbody) as
    Hbound.
  unfold audit_finset_mem, fx_index_encoder.
  destruct (audit_map_code_get (encode EX x) set) as [raw trace].
  apply fx_machine_receipts_one with (group := [body]).
  - cbn [fx_nested_machine_event_source fx_nested_entries flat_map]; constructor; [exact
    Hbody|constructor].
  - cbn [fx_nested_machine_external_budget fx_nested_entries flat_map fx_nested_entries_budget].
    change (fx_one_body_work (fx_body_weight budget) body + 0 <= fx_budget_encode_x budget x + 0);
      lia.
Qed.

Lemma fx_machine_set_add_receipt x set :
  let '(out, events) := audit_finset_add (fx_index_encoder EX) x set in
  fx_machine_has_receipts source budget [FxNestedSetAdd x set out events].
Proof.
  destruct Hsource as [Hencode [_ [_ [_ [_ [_ [_ [Hencode_bound _]]]]]]]].
  destruct (Hencode x) as [body Hbody]; pose proof (Hencode_bound x (encode EX x) body Hbody) as
    Hbound.
  unfold audit_finset_add, fx_index_encoder.
  destruct (audit_trie_set (encode EX x) (x, tt) set) as [out trace].
  apply fx_machine_receipts_one with (group := [body]).
  - cbn [fx_nested_machine_event_source fx_nested_entries flat_map]; constructor; [exact
    Hbody|constructor].
  - cbn [fx_nested_machine_external_budget fx_nested_entries flat_map fx_nested_entries_budget].
    change (fx_one_body_work (fx_body_weight budget) body + 0 <= fx_budget_encode_x budget x + 0);
      lia.
Qed.

Lemma fx_machine_set_remove_receipt x set :
  let '(out, events) := audit_finset_remove (fx_index_encoder EX) x set in
  fx_machine_has_receipts source budget [FxNestedSetRemove x set out events].
Proof.
  destruct Hsource as [Hencode [_ [_ [_ [_ [_ [_ [Hencode_bound _]]]]]]]].
  destruct (Hencode x) as [body Hbody]; pose proof (Hencode_bound x (encode EX x) body Hbody) as
    Hbound.
  unfold audit_finset_remove, fx_index_encoder.
  destruct (audit_trie_remove (encode EX x) set) as [out trace].
  apply fx_machine_receipts_one with (group := [body]).
  - cbn [fx_nested_machine_event_source fx_nested_entries flat_map]; constructor; [exact
    Hbody|constructor].
  - cbn [fx_nested_machine_external_budget fx_nested_entries flat_map fx_nested_entries_budget].
    change (fx_one_body_work (fx_body_weight budget) body + 0 <= fx_budget_encode_x budget x + 0);
      lia.
Qed.

Lemma fx_machine_single event body :
  fx_nested_machine_event_source source event [body] ->
  fx_one_body_work (fx_body_weight budget) body <= fx_nested_machine_external_budget budget event ->
  fx_machine_has_receipts source budget [event].
Proof.
  intros Hreceipt Hbound; apply fx_machine_receipts_one with (group := [body]); [exact Hreceipt|].
  change (fx_one_body_work (fx_body_weight budget) body + 0 <=
    fx_nested_machine_external_budget budget event); lia.
Qed.

Lemma fx_machine_encoded x event :
  (forall body, fx_source_encode_x source x (encode EX x) body ->
    fx_nested_machine_event_source source event [body]) ->
  fx_nested_machine_external_budget budget event = fx_budget_encode_x budget x ->
  fx_machine_has_receipts source budget [event].
Proof.
  intros Hreceipt Hallowance.
  destruct Hsource as [Hencode [_ [_ [_ [_ [_ [_ [Hencode_bound _]]]]]]]].
  destruct (Hencode x) as [body Hbody]; apply fx_machine_single with (body := body).
  - now apply Hreceipt.
  - rewrite Hallowance; now apply (Hencode_bound x (encode EX x)).
Qed.

Lemma fx_machine_leb_receipt a b :
  fx_machine_has_receipts source budget [FxNestedLeb a b (leb L a b)].
Proof.
  destruct Hsource as [_ [_ [_ [_ [Hleb [_ [_ [_ [_ [_ [_ [Hbound _]]]]]]]]]]]].
  destruct (Hleb a b) as [body Hbody]; apply fx_machine_single with (body := body).
  - cbn; eauto.
  - cbn; now apply (Hbound a b (leb L a b)).
Qed.

Lemma fx_machine_join_receipt a b :
  fx_machine_has_receipts source budget [FxNestedJoin a b (join L a b)].
Proof.
  destruct Hsource as [_ [_ [_ [_ [_ [Hjoin [_ [_ [_ [_ [_ [_ [Hbound _]]]]]]]]]]]]].
  destruct (Hjoin a b) as [body Hbody]; apply fx_machine_single with (body := body).
  - cbn; eauto.
  - cbn; now apply (Hbound a b (join L a b)).
Qed.

Lemma fx_machine_widen_receipt a b :
  fx_machine_has_receipts source budget [FxNestedWiden a b (widen L a b)].
Proof.
  destruct Hsource as [_ [_ [_ [_ [_ [_ [Hwiden [_ [_ [_ [_ [_ [_ Hbound]]]]]]]]]]]]].
  destruct (Hwiden a b) as [body Hbody]; apply fx_machine_single with (body := body).
  - cbn; eauto.
  - cbn; now apply (Hbound a b (widen L a b)).
Qed.

Lemma fx_machine_target_receipt c :
  fx_machine_has_receipts source budget [FxNestedTarget c (System.target S c)].
Proof.
  destruct Hsource as [_ [Htarget [_ [_ [_ [_ [_ [_ [Hbound _]]]]]]]]].
  destruct (Htarget c) as [body Hbody]; apply fx_machine_single with (body := body).
  - cbn; eauto.
  - cbn; now apply (Hbound c (System.target S c)).
Qed.

Lemma fx_machine_rhs_receipt c :
  fx_machine_has_receipts source budget [FxNestedRhs c (System.rhs S c)].
Proof.
  destruct Hsource as [_ [_ [Hrhs [_ [_ [_ [_ [_ [_ [Hbound _]]]]]]]]]].
  destruct (Hrhs c) as [body Hbody]; apply fx_machine_single with (body := body).
  - cbn; eauto.
  - cbn; now apply (Hbound c (System.rhs S c)).
Qed.

Lemma fx_machine_empty : fx_machine_has_receipts source budget [].
Proof.
  exists []; split; [constructor|reflexivity].
Qed.

Lemma fx_machine_case_cons site rest :
  fx_machine_has_receipts source budget rest ->
  fx_machine_has_receipts source budget (FxNestedCase site :: rest).
Proof.
  intro Hrest; change (fx_machine_has_receipts source budget ([FxNestedCase site] ++ rest)).
  apply fx_machine_receipts_app; [apply fx_machine_case|exact Hrest].
Qed.

Lemma fx_machine_mark_heads_receipts heads dirty :
  fx_machine_has_receipts source budget (snd (@fx_nested_mark_heads X C A EX heads dirty)).
Proof.
  revert dirty; induction heads as [|h rest IH]; intro dirty.
  - cbn [fx_nested_mark_heads snd]; apply fx_machine_case.
  - cbn [fx_nested_mark_heads].
    pose proof (fx_machine_set_add_receipt h dirty) as Hadd.
    destruct (audit_finset_add (fx_index_encoder EX) h dirty) as [next events].
    specialize (IH next); destruct (@fx_nested_mark_heads X C A EX rest next) as [out later].
    cbn [snd] in IH |- *; apply fx_machine_case_cons.
    change (fx_machine_has_receipts source budget ([FxNestedSetAdd h dirty next events] ++ later)).
    now apply fx_machine_receipts_app.
Qed.

Lemma fx_machine_mark_receipts x (state : NestedState.t X C A) values :
  fx_machine_has_receipts source budget (snd (fx_nested_mark EX plan x state values)).
Proof.
  unfold fx_nested_mark.
  destruct (audit_map_code_get (encode EX x) (NestedPlan.members plan)) as [raw body].
  pose proof (fx_machine_mark_heads_receipts (
    match raw with
    | Some hs => hs
    | None => []
    end)
    (NestedState.dirty state)) as Hheads.
  destruct (fx_nested_mark_heads EX (
    match raw with
    | Some hs => hs
    | None => []
    end)
    (NestedState.dirty state)) as [dirty events]; cbn [snd] in Hheads |- *.
  change (fx_machine_has_receipts source budget
    ([FxNestedMapGet x (encode EX x) (NestedPlan.members plan) raw body] ++ FxNestedCase 1 ::
      events)).
  apply fx_machine_receipts_app.
  - apply fx_machine_encoded with (x := x); [cbn; eauto|reflexivity].
  - now apply fx_machine_case_cons.
Qed.

Lemma fx_machine_raise_receipts x old value :
  fx_machine_has_receipts source budget (snd (fx_nested_raise EX L plan mode x old value)).
Proof.
  unfold fx_nested_raise; destruct mode.
  - cbn [snd]; apply fx_machine_case_cons; apply fx_machine_join_receipt.
  - pose proof (fx_machine_set_mem_receipt x (NestedPlan.heads plan)) as Hmem.
    destruct (audit_finset_mem (fx_index_encoder EX) x (NestedPlan.heads plan)) as [head events].
    destruct head; cbn [snd].
    + apply fx_machine_case_cons.
      change (fx_machine_has_receipts source budget
        ([FxNestedSetMem x (NestedPlan.heads plan) true events] ++
          [FxNestedCase 3; FxNestedWiden old value (widen L old value)])).
      apply fx_machine_receipts_app; [exact Hmem|].
      apply fx_machine_case_cons; apply fx_machine_widen_receipt.
    + apply fx_machine_case_cons.
      change (fx_machine_has_receipts source budget
        ([FxNestedSetMem x (NestedPlan.heads plan) false events] ++
          [FxNestedCase 3; FxNestedJoin old value (join L old value)])).
      apply fx_machine_receipts_app; [exact Hmem|].
      apply fx_machine_case_cons; apply fx_machine_join_receipt.
Qed.

Lemma fx_machine_update_receipts update state :
  fx_machine_has_receipts source budget (snd (fx_nested_update EX L plan mode update state)).
Proof.
  destruct update as [x value].
  pose proof Hsource as Hlaws.
  destruct Hlaws as [Hencode [_ [_ [_ [_ [_ [_ [Hencode_bound _]]]]]]]].
  pose proof (@fx_query_lookup_receipts X C A B EX L source budget Hencode Hencode_bound
    (NestedState.current state) x) as Hlookup.
  unfold fx_nested_update.
  destruct (fx_model_lookup EX L (NestedState.current state) x) as [old events].
  cbn [snd] in Hlookup.
  pose proof (fx_machine_query_event events Hlookup) as Hquery.
  pose proof (fx_machine_leb_receipt value old) as Hleb.
  destruct (leb L value old) eqn:Hleb_run.
  - cbn [snd]; change (fx_machine_has_receipts source budget
      ([FxNestedQuery events] ++ [FxNestedLeb value old true] ++ [FxNestedCase 4])).
    apply fx_machine_receipts_app; [exact Hquery|].
    apply fx_machine_receipts_app; [exact Hleb|apply fx_machine_case].
  - pose proof (fx_machine_raise_receipts x old value) as Hraise.
    destruct (fx_nested_raise EX L plan mode x old value) as [raised raise_events].
    cbn [snd] in Hraise.
    destruct (audit_trie_set (encode EX x) (x, raised) (NestedState.current state)) as [values
      body].
    pose proof (fx_machine_mark_receipts x state values) as Hmark.
    destruct (fx_nested_mark EX plan x state values) as [out mark_events]; cbn [snd] in Hmark |- *.
    change (fx_machine_has_receipts source budget
      ([FxNestedQuery events] ++ [FxNestedLeb value old false] ++ [FxNestedCase 4] ++
        raise_events ++ [FxNestedValueSet x raised (encode EX x) (NestedState.current state)
          values body] ++ mark_events)).
    apply fx_machine_receipts_app; [exact Hquery|].
    apply fx_machine_receipts_app; [exact Hleb|].
    apply fx_machine_receipts_app; [apply fx_machine_case|].
    apply fx_machine_receipts_app; [exact Hraise|].
    apply fx_machine_receipts_app; [|exact Hmark].
    apply fx_machine_encoded with (x := x); [cbn; eauto|reflexivity].
Qed.

Lemma fx_machine_updates_receipts updates state :
  fx_machine_has_receipts source budget (snd (fx_nested_updates EX L plan mode updates state)).
Proof.
  revert state; induction updates as [|update rest IH]; intro state.
  - cbn [fx_nested_updates snd]; apply fx_machine_case.
  - pose proof (fx_machine_update_receipts update state) as Hfirst.
    cbn [fx_nested_updates]; destruct (fx_nested_update EX L plan mode update state) as [next
      events].
    cbn [snd] in Hfirst; specialize (IH next).
    destruct (fx_nested_updates EX L plan mode rest next) as [out later]; cbn [snd] in IH |- *.
    apply fx_machine_case_cons; now apply fx_machine_receipts_app.
Qed.

Lemma fx_machine_step_receipts state :
  Forall (fun c => In c (System.constraints S)) (NestedState.ready state) ->
  fx_machine_has_receipts source budget (snd (fx_nested_step EX L plan mode S state)).
Proof.
  intro Hready; destruct state as [values ready frames dirty changed]; destruct ready as [|c rest].
  - destruct frames as [|[code restart] frames].
    + cbn [fx_nested_step snd]; apply fx_machine_case_cons; apply fx_machine_case.
    + destruct code as [|x rest|h body rest].
      * destruct restart as [[h pass]|].
        -- pose proof (fx_machine_set_mem_receipt h dirty) as Hmem.
            pose proof (fx_machine_set_remove_receipt h dirty) as Hremove.
            unfold fx_nested_step; cbn [NestedState.current NestedState.ready NestedState.frames
              NestedState.dirty NestedState.changed NestedFrame.remaining NestedFrame.restart].
            destruct (audit_finset_mem (fx_index_encoder EX) h dirty) as [present events].
            destruct present.
            ++ destruct (audit_finset_remove (fx_index_encoder EX) h dirty) as [next later].
              cbn [snd app]; repeat apply fx_machine_case_cons.
              change (fx_machine_has_receipts source budget
                ([FxNestedSetMem h dirty true events] ++ [FxNestedCase 11] ++
                  [FxNestedSetRemove h dirty next later])).
              apply fx_machine_receipts_app; [exact Hmem|].
              apply fx_machine_receipts_app; [apply fx_machine_case|exact Hremove].
            ++ cbn [snd]; repeat apply fx_machine_case_cons.
              change (fx_machine_has_receipts source budget
                ([FxNestedSetMem h dirty false events] ++ [FxNestedCase 11])).
              apply fx_machine_receipts_app; [exact Hmem|apply fx_machine_case].
        -- destruct changed; cbn [fx_nested_step snd]; repeat apply fx_machine_case_cons;
              apply fx_machine_empty.
      * unfold fx_nested_step; cbn [NestedState.current NestedState.ready NestedState.frames
          NestedState.dirty NestedState.changed NestedFrame.remaining NestedFrame.restart].
        destruct (audit_map_code_get (encode EX x) (NestedPlan.targets plan)) as [raw body].
        cbn [snd]; repeat apply fx_machine_case_cons.
        change (fx_machine_has_receipts source budget
          ([FxNestedTargetsGet x (encode EX x) (NestedPlan.targets plan) raw body] ++
            [FxNestedCase 9])).
        apply fx_machine_receipts_app; [|apply fx_machine_case].
        apply fx_machine_encoded with (x := x); [cbn; eauto|reflexivity].
      * pose proof (fx_machine_set_remove_receipt h dirty) as Hremove.
        unfold fx_nested_step; cbn [NestedState.current NestedState.ready NestedState.frames
          NestedState.dirty NestedState.changed NestedFrame.remaining NestedFrame.restart].
        destruct (audit_finset_remove (fx_index_encoder EX) h dirty) as [next events].
        cbn [snd]; repeat apply fx_machine_case_cons; exact Hremove.
  - inversion Hready as [|head tail Hc Htail]; subst head tail.
    pose proof Hsource as Hlaws.
    destruct Hlaws as [Hencode [_ [_ [Hcont [_ [_ [_ [Hencode_bound [_ [_ [Hcont_bound _]]]]]]]]]]].
    assert (Hreachable : fx_declared_query_reachable S (System.rhs S c)).
    { apply FxReachableRhs; exact Hc. }
    pose proof (@fx_query_all_receipts X C A B EX L S source budget Hencode Hcont Hencode_bound
      Hcont_bound (System.rhs S c) values Hreachable) as Hquery.
    unfold fx_nested_step; cbn [NestedState.current NestedState.ready NestedState.frames
      NestedState.dirty NestedState.changed].
    destruct (fx_model_query EX L (System.rhs S c) values) as [[[value reads] sides] events].
    cbn [snd] in Hquery.
    pose proof (fx_machine_updates_receipts ((System.target S c, value) :: sides)
      (NestedState.Make values rest frames dirty changed)) as Hupdates.
    destruct (fx_nested_updates EX L plan mode ((System.target S c, value) :: sides)
      (NestedState.Make values rest frames dirty changed)) as [out later]; cbn [snd] in Hupdates
        |- *.
    apply fx_machine_case_cons.
    change (fx_machine_has_receipts source budget
      ([FxNestedRhs c (System.rhs S c)] ++ [FxNestedQuery events] ++
        [FxNestedTarget c (System.target S c)] ++ later)).
    apply fx_machine_receipts_app; [apply fx_machine_rhs_receipt|].
    apply fx_machine_receipts_app; [now apply fx_machine_query_event|].
    apply fx_machine_receipts_app; [apply fx_machine_target_receipt|exact Hupdates].
Qed.

Hypothesis Htargets : forall x, incl (index_get EX (NestedPlan.targets plan) x)
  (System.constraints S).

Definition fx_machine_result_valid (result : NestedState.t X C A + assignment X A) : Prop :=
  match result with
  | inl state => nested_control_valid EX plan S state
  | inr _ => True
  end.

Lemma fx_machine_tick_valid result : fx_machine_result_valid result ->
  fx_machine_result_valid (nested_tick (nested_step EX L plan mode S) result).
Proof.
  destruct result as [state|values]; [|exact (fun _ => I)].
  intro Hvalid; unfold nested_tick.
  destruct (nested_step EX L plan mode S state) as [next|] eqn:Hstep; [|exact I].
  eapply nested_step_control; eassumption.
Qed.

Lemma fx_machine_native_loop_valid fuel state : nested_control_valid EX plan S state ->
  fx_machine_result_valid (nested_loop (nested_step EX L plan mode S) fuel state).
Proof.
  revert state; induction fuel as [fuel IH|fuel IH|]; intros state Hvalid.
  - cbn [nested_loop].
    pose proof (IH state Hvalid) as Hfirst.
    destruct (nested_loop (nested_step EX L plan mode S) fuel state) as [next|values].
    + apply fx_machine_tick_valid; apply IH; exact Hfirst.
    + apply fx_machine_tick_valid; exact I.
  - cbn [nested_loop].
    pose proof (IH state Hvalid) as Hfirst.
    destruct (nested_loop (nested_step EX L plan mode S) fuel state) as [next|values].
    + apply IH; exact Hfirst.
    + exact I.
  - cbn [nested_loop]; apply fx_machine_tick_valid; exact Hvalid.
Qed.

Lemma fx_machine_loop_valid fuel state : nested_control_valid EX plan S state ->
  fx_machine_result_valid (fst (fx_nested_loop EX L plan mode S fuel state)).
Proof.
  intro Hvalid; rewrite fx_nested_loop_erases; now apply fx_machine_native_loop_valid.
Qed.

Lemma fx_machine_tick_receipts result : fx_machine_result_valid result ->
  fx_machine_has_receipts source budget (snd (fx_nested_tick EX L plan mode S result)).
Proof.
  destruct result as [state|values].
  - intro Hvalid.
    pose proof (fx_machine_step_receipts state (proj1 (proj2 Hvalid))) as Hstep.
    unfold fx_nested_tick; destruct (fx_nested_step EX L plan mode S state) as [next events].
    cbn [snd] in Hstep; destruct next; cbn [snd].
    + apply fx_machine_case_cons; apply fx_machine_receipts_app; [exact Hstep|apply
      fx_machine_case].
    + apply fx_machine_case_cons; apply fx_machine_receipts_app; [exact Hstep|apply
      fx_machine_case].
  - intro Hvalid; cbn [fx_nested_tick snd]; apply fx_machine_case.
Qed.

Lemma fx_machine_loop_receipts fuel state : nested_control_valid EX plan S state ->
  fx_machine_has_receipts source budget (snd (fx_nested_loop EX L plan mode S fuel state)).
Proof.
  revert state; induction fuel as [fuel IH|fuel IH|]; intros state Hvalid.
  - pose proof (IH state Hvalid) as Hfirst.
    pose proof (fx_machine_loop_valid fuel state Hvalid) as Hfirst_valid.
    cbn [fx_nested_loop]; destruct (fx_nested_loop EX L plan mode S fuel state) as [first events].
    cbn [fst snd] in Hfirst, Hfirst_valid.
    destruct first as [next|values].
    + pose proof (IH next Hfirst_valid) as Hsecond.
      pose proof (fx_machine_loop_valid fuel next Hfirst_valid) as Hsecond_valid.
      destruct (fx_nested_loop EX L plan mode S fuel next) as [second later].
      cbn [fst snd] in Hsecond, Hsecond_valid.
      pose proof (fx_machine_tick_receipts second Hsecond_valid) as Htick.
      destruct (fx_nested_tick EX L plan mode S second) as [out last]; cbn [snd] in Htick |- *.
      apply fx_machine_case_cons; apply fx_machine_receipts_app; [exact Hfirst|].
      apply fx_machine_receipts_app; [now apply fx_machine_case_cons|exact Htick].
    + pose proof (fx_machine_tick_receipts (inr values) I) as Htick.
      destruct (fx_nested_tick EX L plan mode S (inr values)) as [out last]; cbn [snd] in Htick |-
        *.
      apply fx_machine_case_cons; apply fx_machine_receipts_app; [exact Hfirst|].
      apply fx_machine_receipts_app; [apply fx_machine_case|exact Htick].
  - pose proof (IH state Hvalid) as Hfirst.
    pose proof (fx_machine_loop_valid fuel state Hvalid) as Hfirst_valid.
    cbn [fx_nested_loop]; destruct (fx_nested_loop EX L plan mode S fuel state) as [first events].
    cbn [fst snd] in Hfirst, Hfirst_valid.
    destruct first as [next|values].
    + pose proof (IH next Hfirst_valid) as Hsecond.
      destruct (fx_nested_loop EX L plan mode S fuel next) as [out later]; cbn [snd] in Hsecond |-
        *.
      apply fx_machine_case_cons; apply fx_machine_receipts_app; [exact Hfirst|].
      now apply fx_machine_case_cons.
    + cbn [snd]; apply fx_machine_case_cons; apply fx_machine_receipts_app;
        [exact Hfirst|apply fx_machine_case].
  - pose proof (fx_machine_tick_receipts (inl state) Hvalid) as Htick.
    cbn [fx_nested_loop]; destruct (fx_nested_tick EX L plan mode S (inl state)) as [out events].
    cbn [snd] in Htick |- *; now apply fx_machine_case_cons.
Qed.

End MachineReceipts.

(** * Captured WTO callbacks *)

Lemma fx_nested_wto_source_all X C B (EX : encoding X) (g : Graph.t X (X * X))
    (p : prepared EX g) (cb : fx_index_external_model X C B)
    (source : fx_index_external_source X C B) :
  fx_dep_source_laws cb source ->
  Forall (fx_nested_wto_event_source source) (snd (audit_wto_source_counted p (fx_dep_dfs_cb cb))).
Proof.
  intro Hlaws; pose proof (audit_wto_source_receipts p (fx_dep_dfs_cb cb)) as Hreceipts.
  eapply Forall_impl; [|exact Hreceipts].
  intros [event captures] Hitem; unfold audit_wto_event_receipts in Hitem; cbn [snd] in Hitem.
  unfold fx_nested_wto_event_source; cbn [snd].
  eapply Forall_impl; [|exact Hitem].
  intros capture Hcapture; destruct capture as [edge target body|v code body];
    cbn [audit_dfs_capture_receipt fx_dep_dfs_cb audit_dfs_target_model
      audit_dfs_encode_model] in Hcapture |- *.
  - inversion Hcapture; subst body; unfold fx_dep_body_source; constructor; [exact I|constructor].
  - pose proof (fx_dep_encoder_source X C B cb source v Hlaws) as Hbody.
    rewrite Hcapture in Hbody; exact Hbody.
Qed.

(** The actual nested execution has all callback witnesses and their per-call allowances. *)
Theorem fx_nested_external_source : fx_nested_external_source_statement.
Proof.
  intros X C A B D EX EC L mode S SS cb ib index_source source budget fuel
    Herase Hbounded Hindex Hsource.
  pose proof (fx_nested_run_input_bound X C A B EX EC L mode S SS cb ib fuel Herase Hbounded) as
    Hrun.
  pose proof (fx_dep_build_erasure_correct X C A B EX S SS cb Herase) as Hbuild_erases.
  pose proof (fx_dep_build_source X C A B EX S SS cb index_source Hindex) as Hbuild.
  unfold fx_nested_run_counted in *.
  destruct (fx_dep_graph_build EX S SS cb) as [[graph ix] graph_events].
  cbn [fst snd] in Hbuild_erases, Hbuild; destruct Hbuild_erases as [Hgraph Hix]; subst graph ix.
  pose proof (fx_dep_prepare_source_all X C B EX (dependency_graph EX S SS) cb index_source
    (index_system EX S SS) Hindex) as Hprepare.
  pose proof (audit_prepare_source_correct X (X * X)%type (fx_dep_event X C B) EX
    (dependency_graph EX S SS) (fx_dep_prepare_cb cb (index_system EX S SS)) (fun _ => 0)
    (fx_dep_prepare_erases X C A B EX S SS cb Herase)) as Hprepare_erases.
  destruct (audit_prepare_source_counted EX (dependency_graph EX S SS)
    (fx_dep_prepare_cb cb (index_system EX S SS))) as [prepared prepare_events].
  cbn [fst snd] in Hprepare, Hprepare_erases; destruct Hprepare_erases as [Hprepared _]; subst
    prepared.
  pose proof (fx_nested_wto_source_all X C B EX (dependency_graph EX S SS)
    (prepare EX (dependency_graph EX S SS)) cb index_source Hindex) as Hwto_source.
  pose proof (audit_wto_source_holds X (X * X)%type (fx_dep_event X C B) EX
    (dependency_graph EX S SS) (prepare EX (dependency_graph EX S SS)) (fx_dep_dfs_cb cb)
    (fun _ => 0) (fx_dep_dfs_erases X C A B EX S SS cb Herase)) as Hwto_erases.
  destruct (audit_wto_source_counted (prepare EX (dependency_graph EX S SS)) (fx_dep_dfs_cb cb))
    as [tokens wto_events].
  cbn [fst snd] in Hwto_source, Hwto_erases; destruct Hwto_erases as [Htokens _].
  change (tokens = wto_total (prepare EX (dependency_graph EX S SS))) in Htokens; subst tokens.
  pose proof Hsource as Hlaws.
  destruct Hlaws as [Hencode [Htarget [_ [_ [_ [_ [_ [Hencode_bound [Htarget_bound _]]]]]]]]].
  pose proof (@fx_plan_all_receipts X C A D EX S source Hencode Htarget
    (wto_total (prepare EX (dependency_graph EX S SS)))) as Hplan_source.
  pose proof (fx_nested_plan_erases X C A EX S (wto_total (prepare EX (dependency_graph EX S SS))))
    as Hplan_erases.
  destruct (fx_nested_plan_from_tokens EX S (wto_total (prepare EX (dependency_graph EX S SS))))
    as [plan plan_events].
  cbn [fst snd] in Hplan_source, Hplan_erases.
  change (plan = nested_prepare EX S SS) in Hplan_erases; subst plan.
  assert (Htargets : forall x, incl (index_get EX (NestedPlan.targets (nested_prepare EX S SS)) x)
    (System.constraints S)).
  { intros x c Hin; change (In c (index_get EX (nested_targets EX S) x)) in Hin.
    rewrite nested_targets_agree in Hin; apply filter_In in Hin; exact (proj1 Hin). }
  pose proof (@fx_machine_loop_receipts X C A D EX L (nested_prepare EX S SS) mode S source budget
    Hsource Htargets fuel (nested_start (nested_prepare EX S SS))
    (nested_control_start EX (nested_prepare EX S SS) S)) as Hmachine_source.
  destruct (fx_nested_loop EX L (nested_prepare EX S SS) mode S fuel
    (nested_start (nested_prepare EX S SS))) as [result machine_events].
  cbn [fst snd] in Hrun, Hmachine_source |- *; destruct Hrun as [Hresult Hwork].
  destruct Hplan_source as [plan_groups Hplan_groups].
  destruct Hmachine_source as [machine_groups [Hmachine_groups Hmachine_budget]].
  pose proof (fx_plan_trace_body_bound X C A D source budget plan_events plan_groups
    Hencode_bound Htarget_bound Hplan_groups) as Hplan_budget.
  exists [[]; []; []; concat plan_groups; concat machine_groups; []].
  split.
  - unfold fx_nested_trace_source; constructor; [split; [exact Hbuild|reflexivity]|].
    constructor; [split; [exact Hprepare|reflexivity]|].
    constructor; [split; [exact Hwto_source|reflexivity]|].
    constructor; [exists plan_groups; auto|].
    constructor; [exists machine_groups; auto|].
    constructor; [reflexivity|constructor].
  - split; [exact Hresult|].
    unfold fx_nested_external_trace_budget; cbn [fold_right].
    assert (Hgroups : fx_declared_body_work (fx_body_weight budget)
      [[]; []; []; concat plan_groups; concat machine_groups; []] =
      fx_declared_body_work (fx_body_weight budget) plan_groups +
      fx_declared_body_work (fx_body_weight budget) machine_groups).
    { change (fx_nested_group_work (fx_body_weight budget) (concat plan_groups) +
        (fx_nested_group_work (fx_body_weight budget) (concat machine_groups) + 0) =
          fx_declared_body_work (fx_body_weight budget) plan_groups +
        fx_declared_body_work (fx_body_weight budget) machine_groups).
      repeat rewrite fx_nested_group_concat; lia. }
    rewrite Hgroups; unfold fx_machine_external_work in Hmachine_budget; lia.
Qed.
