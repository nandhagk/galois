(** * Rooted full checker receipts

    The strict checker records a body for each callback it actually invokes.
    For example, a query continuation is witnessed at its returned query and input value.
    Builds on: the counted full checker and declared worklist callback model. *)

From Stdlib Require Import List Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsAuditCost
  CollectionsAuditTrie.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointCheck
  FixpointAuditWorklist FixpointAuditWorklistCallbacks FixpointAuditCheckCallbacks
  FixpointAuditNarrowCheck FixpointAuditNarrowCheckAdequacy.
Import List.ListNotations.

(** * Receipts for declared query events *)

Section Rooted.
Context {X C A B : Type} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (S : System.t X C A) (m : assignment X A)
  (source : fx_declared_callback_source X C A B) (budget : fx_declared_callback_budget X C A B).
Hypothesis Hlaws : fx_fullcheck_rooted_laws EX L S source budget.

Definition root_group_work (group : list (list B)) : nat :=
  fold_right (fun body n => fx_one_body_work (fx_body_weight budget) body + n) 0 group.

Definition root_query_good (events : audit_trace (fx_declared_call X C A)) : Prop :=
  exists bodies, fx_declared_trace_source source events bodies /\
    fx_declared_body_work (fx_body_weight budget) bodies <=
      fx_declared_external_trace_budget budget events.

Lemma root_body_app left right :
  fx_declared_body_work (fx_body_weight budget) (left ++ right) =
    fx_declared_body_work (fx_body_weight budget) left +
    fx_declared_body_work (fx_body_weight budget) right.
Proof.
  unfold fx_declared_body_work; induction left as [|group rest IH]; cbn; [reflexivity|].
  rewrite IH; lia.
Qed.

Lemma root_external_app left right :
  fx_declared_external_trace_budget budget (left ++ right) =
    fx_declared_external_trace_budget budget left + fx_declared_external_trace_budget budget right.
Proof.
  unfold fx_declared_external_trace_budget; induction left as [|event rest IH]; cbn; [reflexivity|].
  destruct event; cbn; rewrite IH; lia.
Qed.

Lemma root_query_app left right : root_query_good left -> root_query_good right ->
  root_query_good (left ++ right).
Proof.
  intros [lb [Hl Hbl]] [rb [Hr Hbr]].
  exists (lb ++ rb); split.
  - apply Forall2_app; assumption.
  - rewrite root_body_app, root_external_app; lia.
Qed.

Lemma root_query_one event group : fx_declared_event_source source event group ->
  root_group_work group <= fx_declared_external_trace_budget budget [event] ->
  root_query_good [event].
Proof.
  intros Hsource Hwork; exists [group]; split.
  - constructor; [exact Hsource|constructor].
  - unfold root_group_work, fx_declared_body_work, fx_one_body_work in *; cbn in *; lia.
Qed.

Lemma root_query_empty_event event :
  (match event with AuditCall _ => False | _ => True end) -> root_query_good [event].
Proof.
  destruct event; cbn; try contradiction; intro H; apply (root_query_one _ []); reflexivity.
Qed.

Lemma root_query_cons event tail : root_query_good [event] -> root_query_good tail ->
  root_query_good (event :: tail).
Proof.
  change (root_query_good [event] -> root_query_good tail -> root_query_good ([event] ++ tail)).
  apply root_query_app.
Qed.

Lemma root_lookup_receipts x : root_query_good (snd (@fx_model_lookup X C A EX L m x)).
Proof.
  destruct Hlaws as [Hencode [_ [_ [_ [_ [Hbound _]]]]]].
  destruct (Hencode x) as [body Hbody].
  pose proof (Hbound x (encode EX x) body Hbody) as Hwork.
  unfold fx_model_lookup; destruct (audit_map_code_get (encode EX x) m) as [raw trace].
  destruct raw; cbn [snd].
  all: apply root_query_app with (left := [AuditCall (FxGet x (encode EX x) m _ trace)])
    (right := [AuditCase 0 []]);
    [apply (root_query_one _ [body]); [cbn; eauto|
      change (fx_one_body_work (fx_body_weight budget) body + 0 <=
        fx_budget_encode_x budget x + 0); lia]|
      apply root_query_empty_event; exact I].
Qed.

Lemma root_query_receipts q : fx_declared_query_reachable S q ->
  root_query_good (snd (@fx_model_query X C A EX L q m)).
Proof.
  induction q as [a|x k IH|x a q IH]; intro Hreachable.
  - apply root_query_empty_event; exact I.
  - pose proof (root_lookup_receipts x) as Hlookup.
    destruct (fx_model_lookup EX L m x) as [value lookup_events] eqn:Hlookup_run.
    change (root_query_good lookup_events) in Hlookup.
    assert (Hnext : fx_declared_query_reachable S (k value)).
    { eapply FxReachableAsk; exact Hreachable. }
    specialize (IH value Hnext).
    destruct (fx_model_query EX L (k value) m) as [[[v reads] sides] body] eqn:Hquery.
    change (root_query_good body) in IH.
    destruct Hlaws as [_ [_ [_ [Hcontinuation [_ [_ [_ [_ [Hbound _]]]]]]]]].
    destruct (Hcontinuation k value (ex_intro _ x Hreachable)) as [receipt Hreceipt].
    pose proof (Hbound k value (k value) receipt Hreceipt) as Hwork.
    cbn [fx_model_query]; rewrite Hlookup_run, Hquery; cbn.
    apply root_query_cons; [apply root_query_empty_event; exact I|].
    apply root_query_app; [exact Hlookup|].
    apply root_query_cons.
    + apply (root_query_one _ [receipt]); [cbn; eauto|].
      change (fx_one_body_work (fx_body_weight budget) receipt + 0 <=
        fx_budget_continuation budget k value + 0); lia.
    + apply root_query_app; [exact IH|apply root_query_empty_event; exact I].
  - assert (Hnext : fx_declared_query_reachable S q) by (eapply FxReachableSide; exact Hreachable).
    specialize (IH Hnext).
    destruct (fx_model_query EX L q m) as [[[v reads] sides] body] eqn:Hquery.
    change (root_query_good body) in IH.
    cbn [fx_model_query]; rewrite Hquery; cbn.
    apply root_query_cons; [apply root_query_empty_event; exact I|].
    apply root_query_app; [exact IH|apply root_query_empty_event; exact I].
Qed.

(** * Receipts for the full checker trace *)

Definition root_check_good (events : list (fx_fullcheck_event X C A)) : Prop :=
  exists bodies, fx_fullcheck_rooted_trace_source source events bodies /\
    fx_declared_body_work (fx_body_weight budget) bodies <=
      fx_fullcheck_rooted_external_budget budget events.

Lemma root_group_app left right : root_group_work (left ++ right) =
  root_group_work left + root_group_work right.
Proof.
  unfold root_group_work; induction left as [|body rest IH]; cbn; [reflexivity|].
  rewrite IH; lia.
Qed.

Lemma root_flatten_work groups : root_group_work (concat groups) =
  fx_declared_body_work (fx_body_weight budget) groups.
Proof.
  induction groups as [|group rest IH]; cbn [concat].
  - reflexivity.
  - rewrite root_group_app, IH.
    unfold root_group_work, fx_declared_body_work, fx_one_body_work; cbn; lia.
Qed.

Lemma root_check_external_app left right :
  fx_fullcheck_rooted_external_budget budget (left ++ right) =
    fx_fullcheck_rooted_external_budget budget left +
    fx_fullcheck_rooted_external_budget budget right.
Proof.
  unfold fx_fullcheck_rooted_external_budget; induction left as [|event rest IH]; cbn;
    [reflexivity|].
  rewrite IH; lia.
Qed.

Lemma root_check_app left right : root_check_good left -> root_check_good right ->
  root_check_good (left ++ right).
Proof.
  intros [lb [Hl Hbl]] [rb [Hr Hbr]].
  exists (lb ++ rb); split.
  - apply Forall2_app; assumption.
  - rewrite root_body_app, root_check_external_app; lia.
Qed.

Lemma root_check_one event group : fx_narrow_check_source source event group ->
  root_group_work group <= fx_narrow_check_budget budget event -> root_check_good [event].
Proof.
  intros Hsource Hwork; exists [group]; split.
  - constructor; [exact Hsource|constructor].
  - unfold fx_declared_body_work, root_group_work, fx_one_body_work,
      fx_fullcheck_rooted_external_budget in *; cbn in *; lia.
Qed.

Lemma root_check_cons event tail : root_check_good [event] -> root_check_good tail ->
  root_check_good (event :: tail).
Proof.
  change (root_check_good [event] -> root_check_good tail -> root_check_good ([event] ++ tail)).
  apply root_check_app.
Qed.

Lemma root_check_query events : root_query_good events -> root_check_good [FfcQuery events].
Proof.
  intros [groups [Hsource Hwork]].
  apply (root_check_one _ (concat groups)).
  - cbn; exists groups; auto.
  - cbn [fx_narrow_check_budget]; rewrite root_flatten_work; exact Hwork.
Qed.

Lemma root_check_sides sides : root_check_good (snd (@fx_fullcheck_sides X C A EX L m sides)).
Proof.
  induction sides as [|[x value] rest IH].
  - apply (root_check_one _ []); reflexivity.
  - pose proof (root_lookup_receipts x) as Hlookup.
    destruct (fx_model_lookup EX L m x) as [old events] eqn:Hlookup_run.
    change (root_query_good events) in Hlookup.
    destruct Hlaws as (_ & _ & _ & _ & Hleb & _ & _ & _ & _ & Hbound).
    destruct (Hleb value old) as [receipt Hreceipt].
    pose proof (Hbound value old (leb L value old) receipt Hreceipt) as Hwork.
    destruct (fx_fullcheck_sides EX L m rest) as [tail later] eqn:Htail.
    change (root_check_good later) in IH.
    cbn [fx_fullcheck_sides]; rewrite Hlookup_run, Htail; cbn.
    apply root_check_cons; [apply (root_check_one _ []); reflexivity|].
    apply root_check_cons; [now apply root_check_query|].
    apply root_check_cons.
    + apply (root_check_one _ [receipt]); [cbn; eauto|].
      change (fx_one_body_work (fx_body_weight budget) receipt + 0 <=
        fx_budget_leb budget value old); lia.
    + apply root_check_app; [exact IH|apply (root_check_one _ []); reflexivity].
Qed.

Lemma root_check_constraints cs : incl cs (System.constraints S) ->
  root_check_good (snd (@fx_fullcheck_constraints X C A EX L S m cs)).
Proof.
  induction cs as [|c rest IH]; intro Hincl.
  - apply (root_check_one _ []); reflexivity.
  - assert (Hc : In c (System.constraints S)) by (apply Hincl; left; reflexivity).
    assert (Hrest : incl rest (System.constraints S)).
    { intros d Hd; apply Hincl; right; exact Hd. }
    destruct Hlaws as (_ & Htarget & Hrhs & _ & Hleb & _ & Htarget_bound & Hrhs_bound & _ &
      Hleb_bound).
    destruct (Hrhs c Hc) as [rhs_body Hrhs_body].
    destruct (Htarget c Hc) as [target_body Htarget_body].
    pose proof (root_query_receipts (System.rhs S c) (FxReachableRhs S c Hc)) as Hquery.
    destruct (fx_model_query EX L (System.rhs S c) m) as [[[value reads] sides] query_events]
      eqn:Hquery_run.
    change (root_query_good query_events) in Hquery.
    pose proof (root_lookup_receipts (System.target S c)) as Hlookup.
    destruct (fx_model_lookup EX L m (System.target S c)) as [old lookup_events] eqn:Hlookup_run.
    change (root_query_good lookup_events) in Hlookup.
    destruct (Hleb value old) as [leb_body Hleb_body].
    pose proof (root_check_sides sides) as Hsides.
    destruct (fx_fullcheck_sides EX L m sides) as [side_ok side_events] eqn:Hsides_run.
    change (root_check_good side_events) in Hsides.
    specialize (IH Hrest).
    destruct (fx_fullcheck_constraints EX L S m rest) as [tail later] eqn:Htail.
    change (root_check_good later) in IH.
    cbn [fx_fullcheck_constraints]; rewrite Hquery_run, Hlookup_run, Hsides_run, Htail; cbn.
    apply root_check_cons; [apply (root_check_one _ []); reflexivity|].
    apply root_check_cons.
    + apply (root_check_one _ [rhs_body]); [cbn; eauto|].
      change (fx_one_body_work (fx_body_weight budget) rhs_body + 0 <= fx_budget_rhs budget c).
      specialize (Hrhs_bound c _ _ Hrhs_body); lia.
    + apply root_check_cons; [now apply root_check_query|].
      apply root_check_cons.
      * apply (root_check_one _ [target_body]); [cbn; eauto|].
        change (fx_one_body_work (fx_body_weight budget) target_body + 0 <=
          fx_budget_target budget c).
        specialize (Htarget_bound c _ _ Htarget_body); lia.
      * apply root_check_cons; [now apply root_check_query|].
        apply root_check_cons.
        -- apply (root_check_one _ [leb_body]); [cbn; eauto|].
           change (fx_one_body_work (fx_body_weight budget) leb_body + 0 <=
             fx_budget_leb budget value old).
           specialize (Hleb_bound value old _ _ Hleb_body); lia.
        -- apply root_check_app; [exact Hsides|].
           apply root_check_cons; [apply (root_check_one _ []); reflexivity|].
           apply root_check_app; [exact IH|apply (root_check_one _ []); reflexivity].
Qed.

End Rooted.

(** Every actual strict-check trace has rooted callback receipts and an input-derived bound. *)
Theorem fx_fullcheck_rooted_source : fx_fullcheck_rooted_source_statement.
Proof.
  intros X C A B EX EC L S m source budget Hlaws.
  pose proof (root_check_constraints EX L S m source budget Hlaws
    (System.constraints S) (incl_refl _)) as Hreceipts.
  pose proof (fx_fullcheck_input_bound X C A EX EC L S m) as Hbound.
  unfold fx_fullcheck_counted in *.
  destruct (fx_fullcheck_constraints EX L S m (System.constraints S)) as [out events].
  cbn in Hreceipts; destruct Hreceipts as [bodies [Hsource Hbody]].
  destruct Hbound as [Hout Hwork].
  exists bodies; split; [exact Hsource|]; split; [exact Hout|lia].
Qed.
