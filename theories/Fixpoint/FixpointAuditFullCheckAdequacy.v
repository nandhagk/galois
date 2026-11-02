(** * Nested full checker adequacy

    A nested checker derivation preserves callback results and charges their actual bodies.
    For example, each query read includes its concrete trie lookup.
    Builds on: the nested checker and collection trie adequacy. *)

From Stdlib Require Import List Bool PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsAuditTrie
  CollectionsAuditTrieAdequacy.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointCheck
  FixpointAuditFullCheck FixpointAuditWorklistBudgetAdequacy.
Import List.ListNotations.

(** * Lookup and query derivations *)

Section Nested.
Context {X C A B : Type} (EX : encoding X) (L : lattice A) (S : System.t X C A)
  (m : assignment X A) (cb : fx_check_external_model X C A B).
Hypothesis Herase : fx_check_external_erases EX L S cb.

Lemma fcn_lookup_erases x : fst (fcn_lookup L m cb x) = lookup EX L m x.
Proof.
  destruct Herase as [Henc _].
  pose proof (Henc x) as Hcode.
  destruct (fx_check_encode_model cb x) as [code body] eqn:Hencode; cbn in Hcode; subst code.
  pose proof (audit_map_code_get_erases X A (encode EX x) m) as Hget.
  unfold fcn_lookup; rewrite Hencode.
  unfold lookup, Map.get.
  destruct (audit_map_code_get (encode EX x) m) as [raw events]; cbn in Hget; now rewrite <- Hget.
Qed.

Lemma fcn_query_erases q out events : fcn_query_run L m cb q out events ->
  out = Query.run q (lookup EX L m).
Proof.
  intro Hrun; induction Hrun as
    [a|x k value read_events next cont_body out reads sides later Hlookup Hcont Hrun IH|
     x a next out reads sides later Hrun IH].
  - reflexivity.
  - pose proof (fcn_lookup_erases x) as Hvalue; rewrite Hlookup in Hvalue; cbn in Hvalue.
    destruct Herase as [_ [_ [_ [Hcontinue _]]]].
    pose proof (Hcontinue k value) as Hnext; rewrite Hcont in Hnext; cbn in Hnext.
    subst value next; cbn [Query.run]; rewrite <- IH; reflexivity.
  - cbn [Query.run]; rewrite <- IH; reflexivity.
Qed.

Lemma fcn_query_total q : exists out events, fcn_query_run L m cb q out events.
Proof.
  induction q as [a|x k IH|x a q IH].
  - exists (a, [], []), [FcnCase 1]; constructor.
  - destruct (fcn_lookup L m cb x) as [value read_events] eqn:Hlookup.
    destruct (fx_check_continue_model cb k value) as [next body] eqn:Hcont.
    destruct Herase as [_ [_ [_ [Hcontinue _]]]].
    pose proof (Hcontinue k value) as Hnext; rewrite Hcont in Hnext; cbn in Hnext; subst next.
    destruct (IH value) as [[[out reads] sides] [events Hrun]].
    eexists _, _; eapply FcnQueryAsk; eassumption.
  - destruct IH as [[[out reads] sides] [events Hrun]].
    eexists _, _; apply FcnQuerySide; exact Hrun.
Qed.

Lemma fcn_constraints_total cs : exists out events, fcn_constraints_run L m cb cs out events.
Proof.
  induction cs as [|c rest IH].
  - exists true, [FcnCase 6]; constructor.
  - destruct (fx_check_rhs_model cb c) as [rhs rhs_body] eqn:Hrhs.
    destruct (fcn_query_total rhs) as [[[value reads] sides] [query_events Hquery]].
    destruct (fx_check_target_model cb c) as [target target_body] eqn:Htarget.
    destruct (fcn_lookup L m cb target) as [old lookup_events] eqn:Hlookup.
    destruct (fx_check_leb_model cb value old) as [direct leb_body] eqn:Hleb.
    destruct (fcn_sides L m cb sides) as [side_ok side_events] eqn:Hsides.
    destruct IH as [tail [later Htail]].
    eexists _, _; eapply FcnConstraintsCons; eassumption.
Qed.

End Nested.

(** Each callback-erasing model has a finite nested checker derivation. *)
Theorem fx_fullcheck_nested_total : fx_fullcheck_nested_total_statement.
Proof.
  intros X C A B EX L S m cb Herase.
  apply (fcn_constraints_total EX L S m cb Herase).
Qed.

(** * Source input bounds *)

Section Bounds.
Context {X C A B : Type} (EX : encoding X) (L : lattice A) (S : System.t X C A)
  (m : assignment X A) (cb : fx_check_external_model X C A B)
  (budget : fx_check_external_budget X C A B).
Hypothesis Herase : fx_check_external_erases EX L S cb.
Hypothesis Hbounded : fx_check_external_bounded cb budget.

Lemma fcn_work_app (left right : list (fx_check_nested_event X C A B)) :
  fx_check_nested_work budget (left ++ right) =
    fx_check_nested_work budget left + fx_check_nested_work budget right.
Proof.
  unfold fx_check_nested_work; induction left as [|event rest IH]; cbn; [reflexivity|].
  rewrite IH; lia.
Qed.

Lemma fcn_work_cons (event : fx_check_nested_event X C A B) rest :
  fx_check_nested_work budget (event :: rest) =
    fx_check_nested_event_work budget event + fx_check_nested_work budget rest.
Proof.
  reflexivity.
Qed.

Lemma fcn_lookup_bound x :
  fx_check_nested_work budget (snd (fcn_lookup L m cb x)) <=
    fx_check_nested_lookup_budget EX budget x.
Proof.
  destruct Herase as [Hencode _].
  destruct Hbounded as [_ [Hbody _]].
  pose proof (Hencode x) as Hcode; pose proof (Hbody x) as Hwork.
  destruct (fx_check_encode_model cb x) as [code enc_body] eqn:Henc; cbn in Hcode, Hwork.
  subst code.
  pose proof (fx_map_get_body_bound X A (encode EX x) m) as Htrie.
  unfold fcn_lookup; rewrite Henc.
  destruct (audit_map_code_get (encode EX x) m) as [raw trie_body] eqn:Hget.
  cbn in Htrie |- *.
  change (fx_check_body_work budget enc_body <= fx_check_encode_bound budget x) in Hwork.
  unfold fx_check_nested_work, fx_check_nested_lookup_budget; cbn [fx_check_nested_event_work].
  lia.
Qed.

Lemma fcn_query_bound q out events : fcn_query_run L m cb q out events ->
  fx_check_nested_work budget events <= fx_check_nested_query_budget EX L budget m q.
Proof.
  intro Hrun; induction Hrun as
    [a|x k value read_events next cont_body out reads sides later Hlookup Hcont Hrun IH|
     x a next out reads sides later Hrun IH].
  - reflexivity.
  - pose proof (fcn_lookup_erases EX L S m cb Herase x) as Hvalue.
    pose proof (fcn_lookup_bound x) as Hread.
    rewrite Hlookup in Hvalue, Hread; cbn in Hvalue, Hread; subst value.
    change (fx_check_nested_work budget read_events <= fx_check_nested_lookup_budget EX budget x)
      in Hread.
    destruct Herase as [_ [_ [_ [Hcontinue _]]]].
    destruct Hbounded as [_ [_ [_ [_ [Hcont_bound _]]]]].
    pose proof (Hcontinue k (lookup EX L m x)) as Hnext.
    pose proof (Hcont_bound k (lookup EX L m x)) as Hcont_work.
    rewrite Hcont in Hnext, Hcont_work; cbn in Hnext, Hcont_work; subst next.
    cbn [fx_check_nested_query_budget].
    repeat (rewrite fcn_work_cons || rewrite fcn_work_app).
    cbn [fx_check_nested_event_work].
    change (fx_check_body_work budget cont_body <=
      fx_check_continue_bound budget k (lookup EX L m x)) in Hcont_work.
    assert (Hnil : @fx_check_nested_work X C A B budget [] = 0) by reflexivity.
    rewrite Hnil; lia.
  - cbn [fx_check_nested_query_budget].
    repeat (rewrite fcn_work_cons || rewrite fcn_work_app).
    cbn [fx_check_nested_event_work].
    assert (Hnil : @fx_check_nested_work X C A B budget [] = 0) by reflexivity.
    rewrite Hnil; lia.
Qed.

Lemma fcn_sides_correct sides :
  let '(out, events) := fcn_sides L m cb sides in
  out = forallb (fun xa => leb L (snd xa) (lookup EX L m (fst xa))) sides /\
  fx_check_nested_work budget events <= fx_check_nested_sides_budget EX L budget m sides.
Proof.
  induction sides as [|[x value] rest IH].
  - split; reflexivity.
  - pose proof (fcn_lookup_erases EX L S m cb Herase x) as Hvalue.
    pose proof (fcn_lookup_bound x) as Hread.
    destruct (fcn_lookup L m cb x) as [old events] eqn:Hlookup.
    cbn in Hvalue, Hread; subst old.
    destruct Herase as [_ [_ [_ [_ Hleb]]]].
    destruct Hbounded as [_ [_ [_ [_ [_ Hleb_bound]]]]].
    pose proof (Hleb value (lookup EX L m x)) as Hhead.
    pose proof (Hleb_bound value (lookup EX L m x)) as Hhead_work.
    destruct (fx_check_leb_model cb value (lookup EX L m x)) as [head body] eqn:Hleb_run.
    cbn in Hhead, Hhead_work; subst head.
    destruct (fcn_sides L m cb rest) as [tail later] eqn:Htail.
    cbn in IH; destruct IH as [IHout IHwork].
    cbn [fcn_sides]; rewrite Hlookup, Hleb_run, Htail; cbn [fx_check_nested_sides_budget].
    split.
    + cbn; now rewrite IHout.
    + change (fx_check_nested_work budget events <= fx_check_nested_lookup_budget EX budget x)
        in Hread.
      change (fx_check_body_work budget body <=
        fx_check_leb_bound budget value (lookup EX L m x)) in Hhead_work.
      repeat (rewrite fcn_work_cons || rewrite fcn_work_app).
      cbn [fx_check_nested_event_work].
      assert (Hnil : @fx_check_nested_work X C A B budget [] = 0) by reflexivity.
      rewrite Hnil; lia.
Qed.

Lemma fcn_constraints_correct cs out events : fcn_constraints_run L m cb cs out events ->
  out = forallb (fun c =>
    let '(v, _, ss) := Query.run (System.rhs S c) (lookup EX L m) in
    leb L v (lookup EX L m (System.target S c)) &&
      forallb (fun xa => leb L (snd xa) (lookup EX L m (fst xa))) ss) cs /\
  fx_check_nested_work budget events <= fx_check_nested_constraints_budget EX L S budget m cs.
Proof.
  intro Hrun; induction Hrun as
    [|c rest rhs rhs_body value reads sides query_events target target_body old lookup_events
      direct leb_body side_ok side_events tail later Hrhs Hquery Htarget Hlookup Hleb Hsides Htail
      IH].
  - split; reflexivity.
  - pose proof (fcn_query_erases EX L S m cb Herase _ _ _ Hquery) as Hquery_result.
    pose proof (fcn_query_bound _ _ _ Hquery) as Hquery_work.
    pose proof (fcn_lookup_erases EX L S m cb Herase target) as Hlookup_result.
    pose proof (fcn_lookup_bound target) as Hlookup_work.
    rewrite Hlookup in Hlookup_result, Hlookup_work; cbn in Hlookup_result, Hlookup_work.
    subst old.
    pose proof (fcn_sides_correct sides) as Hside_correct.
    rewrite Hsides in Hside_correct; cbn in Hside_correct.
    destruct Hside_correct as [Hside_result Hside_work].
    destruct Herase as [_ [Hrhs_erase [Htarget_erase [_ Hleb_erase]]]].
    destruct Hbounded as [_ [_ [Hrhs_bound [Htarget_bound [_ Hleb_bound]]]]].
    pose proof (Hrhs_erase c) as Hrhs_result; rewrite Hrhs in Hrhs_result; cbn in Hrhs_result.
    pose proof (Htarget_erase c) as Htarget_result; rewrite Htarget in Htarget_result;
      cbn in Htarget_result.
    pose proof (Hleb_erase value (lookup EX L m target)) as Hleb_result.
    pose proof (Hrhs_bound c) as Hrhs_work; rewrite Hrhs in Hrhs_work; cbn in Hrhs_work.
    pose proof (Htarget_bound c) as Htarget_work; rewrite Htarget in Htarget_work;
      cbn in Htarget_work.
    pose proof (Hleb_bound value (lookup EX L m target)) as Hleb_work.
    rewrite Hleb in Hleb_result, Hleb_work; cbn in Hleb_result, Hleb_work.
    subst rhs target direct.
    change (fx_check_body_work budget rhs_body <= fx_check_rhs_bound budget c) in Hrhs_work.
    change (fx_check_body_work budget target_body <= fx_check_target_bound budget c)
      in Htarget_work.
    change (fx_check_body_work budget leb_body <=
      fx_check_leb_bound budget value (lookup EX L m (System.target S c))) in Hleb_work.
    change (fx_check_nested_work budget lookup_events <=
      fx_check_nested_lookup_budget EX budget (System.target S c)) in Hlookup_work.
    destruct IH as [IHresult IHwork].
    cbn [fx_check_nested_constraints_budget]; rewrite <- Hquery_result.
    split.
    + cbn; rewrite <- Hquery_result; cbn; now rewrite Hside_result, IHresult.
    + repeat (rewrite fcn_work_cons || rewrite fcn_work_app).
      cbn [fx_check_nested_event_work].
      assert (Hnil : @fx_check_nested_work X C A B budget [] = 0) by reflexivity.
      rewrite Hnil; lia.
Qed.

End Bounds.

(** A nested run returns the original result and meets its input-derived source budget. *)
Theorem fx_fullcheck_nested_input_bound : fx_fullcheck_nested_input_bound_statement.
Proof.
  intros X C A B EX L S m cb budget Herase Hbounded out events Hrun.
  pose proof (fcn_constraints_correct EX L S m cb budget Herase Hbounded _ _ _ Hrun) as H.
  unfold fx_fullcheck_nested_input_budget, check_post; exact H.
Qed.

(** Erasing a nested derivation preserves the original full checker result. *)
Theorem fx_fullcheck_nested_erasure : fx_fullcheck_nested_erasure_statement.
Proof.
  intros X C A B EX L S m cb Herase out events Hrun.
  set (budget := FxCheckExternalBudget X C A B (fun _ => 1)
    (fun x => length (snd (fx_check_encode_model cb x)))
    (fun c => length (snd (fx_check_rhs_model cb c)))
    (fun c => length (snd (fx_check_target_model cb c)))
    (fun k a => length (snd (fx_check_continue_model cb k a)))
    (fun a b => length (snd (fx_check_leb_model cb a b)))).
  assert (Hlength : forall xs : list B, fx_check_body_work budget xs = length xs).
  { intro xs; induction xs as [|x rest IH]; [reflexivity|].
    change (1 + fx_check_body_work budget rest = Datatypes.S (length rest)); now rewrite IH. }
  assert (Hbounded : fx_check_external_bounded cb budget).
  { unfold fx_check_external_bounded; split.
    - intro b; unfold budget; cbn; lia.
    - repeat split; intros; rewrite Hlength; unfold budget; cbn; lia. }
  pose proof (fcn_constraints_correct EX L S m cb budget Herase Hbounded _ _ _ Hrun) as Hcorrect.
  unfold check_post; exact (proj1 Hcorrect).
Qed.

(** Trace-local source adequacy composes with the derived nested work bound. *)
Theorem fx_fullcheck_external_source : fx_fullcheck_external_source_statement.
Proof.
  intros X C A B EX L S m cb budget source Herase Hbounded out events Hrun Hsource.
  eapply fx_fullcheck_nested_input_bound; eassumption.
Qed.
