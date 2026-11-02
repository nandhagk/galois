(** * Strict full checker adequacy

    The counted checker preserves the result and input work bound of each constraint.
    For example, it retains the later trace even when an earlier comparison fails.
    Builds on: the full checker and declared worklist adequacy. *)

From Stdlib Require Import List Bool Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsAuditCost.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointCheck
  FixpointAuditWorklist FixpointAuditWorklistBudget FixpointAuditWorklistAdequacy
  FixpointAuditWorklistBudgetAdequacy FixpointAuditNarrowCheck FixpointAuditContractClosures.
Import List.ListNotations.

(** * Erasure and input bounds *)

Section Check.
Context {X C A : Type} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (S : System.t X C A) (m : assignment X A).

Lemma ffc_work_app (left right : list (fx_fullcheck_event X C A)) :
  fx_fullcheck_work EC (left ++ right) = fx_fullcheck_work EC left + fx_fullcheck_work EC right.
Proof.
  unfold fx_fullcheck_work; induction left as [|event rest IH]; cbn; [reflexivity|].
  rewrite IH; lia.
Qed.

Lemma ffc_work_cons (event : fx_fullcheck_event X C A) rest :
  fx_fullcheck_work EC (event :: rest) =
    fx_fullcheck_event_work EC event + fx_fullcheck_work EC rest.
Proof.
  reflexivity.
Qed.

Lemma ffc_sides_correct sides :
  let '(out, events) := @fx_fullcheck_sides X C A EX L m sides in
  out = forallb (fun xa => leb L (snd xa) (lookup EX L m (fst xa))) sides /\
  fx_fullcheck_work EC events <= fx_fullcheck_sides_input_budget EX sides.
Proof.
  induction sides as [|[x value] rest IH].
  - split; reflexivity.
  - pose proof (@fx_lookup_erases X C A EX L m x) as Herase.
    pose proof (@fx_lookup_budget X C A EX EC L m x) as Hbound.
    destruct (fx_model_lookup EX L m x) as [old events] eqn:Hlookup.
    change (old = lookup EX L m x) in Herase; subst old.
    change (fx_declared_model_work EC events <= fx_fullcheck_lookup_input_budget EX x) in Hbound.
    destruct (fx_fullcheck_sides EX L m rest) as [tail later] eqn:Htail.
    cbn in IH; destruct IH as [IHout IHwork].
    cbn [fx_fullcheck_sides]; rewrite Hlookup, Htail.
    cbn [fx_fullcheck_sides_input_budget]; split.
    + cbn; now rewrite IHout.
    + change (1 + (fx_declared_model_work EC events + (1 +
        fx_fullcheck_work EC (later ++ [FfcAnd (leb L value (lookup EX L m x)) tail
          (andb (leb L value (lookup EX L m x)) tail)]))) <=
        3 + fx_fullcheck_lookup_input_budget EX x + fx_fullcheck_sides_input_budget EX rest).
      rewrite ffc_work_app.
      change (1 + (fx_declared_model_work EC events + (1 +
        (fx_fullcheck_work EC later + 1))) <=
        3 + fx_fullcheck_lookup_input_budget EX x + fx_fullcheck_sides_input_budget EX rest).
      lia.
Qed.

Lemma ffc_constraints_correct cs :
  let '(out, events) := @fx_fullcheck_constraints X C A EX L S m cs in
  out = forallb (fun c =>
    let '(v, _, ss) := Query.run (System.rhs S c) (lookup EX L m) in
    leb L v (lookup EX L m (System.target S c)) &&
      forallb (fun xa => leb L (snd xa) (lookup EX L m (fst xa))) ss) cs /\
  fx_fullcheck_work EC events <= fx_fullcheck_constraints_input_budget EX L S m cs.
Proof.
  induction cs as [|c rest IH].
  - split; reflexivity.
  - pose proof (@fx_query_erases X C A EX L (System.rhs S c) m) as Hquery.
    pose proof (@fx_query_budget X C A EX EC L (System.rhs S c) m) as Hquery_bound.
    destruct (fx_model_query EX L (System.rhs S c) m)
      as [[[value reads] sides] query_events] eqn:Hquery_run.
    change ((value, reads, sides) = Query.run (System.rhs S c) (lookup EX L m)) in Hquery.
    change (fx_declared_model_work EC query_events <=
      fx_fullcheck_query_input_budget EX L m (System.rhs S c)) in Hquery_bound.
    pose proof (@fx_lookup_erases X C A EX L m (System.target S c)) as Hlookup.
    pose proof (@fx_lookup_budget X C A EX EC L m (System.target S c)) as Hlookup_bound.
    destruct (fx_model_lookup EX L m (System.target S c)) as [old lookup_events] eqn:Hlookup_run.
    change (old = lookup EX L m (System.target S c)) in Hlookup; subst old.
    change (fx_declared_model_work EC lookup_events <=
      fx_fullcheck_lookup_input_budget EX (System.target S c)) in Hlookup_bound.
    pose proof (ffc_sides_correct sides) as Hsides.
    destruct (fx_fullcheck_sides EX L m sides) as [side_ok side_events] eqn:Hsides_run.
    cbn in Hsides; destruct Hsides as [Hsides_out Hsides_work].
    destruct (fx_fullcheck_constraints EX L S m rest) as [tail later] eqn:Htail.
    cbn in IH; destruct IH as [IHout IHwork].
    cbn [fx_fullcheck_constraints]; rewrite Hquery_run, Hlookup_run, Hsides_run, Htail.
    cbn [fx_fullcheck_constraints_input_budget]; rewrite <- Hquery; split.
    + cbn; rewrite Hsides_out, IHout, <- Hquery; reflexivity.
    + repeat (rewrite ffc_work_cons || rewrite ffc_work_app).
      cbn [fx_fullcheck_event_work].
      assert (Hnil : @fx_fullcheck_work X C A EC [] = 0) by reflexivity.
      rewrite Hnil; lia.
Qed.

End Check.

Lemma ffc_sides_erases X C A (EX : encoding X) (L : lattice A) m sides :
  fst (@fx_fullcheck_sides X C A EX L m sides) =
    forallb (fun xa => leb L (snd xa) (lookup EX L m (fst xa))) sides.
Proof.
  induction sides as [|[x a] rest IH]; [reflexivity|].
  cbn [fx_fullcheck_sides].
  pose proof (@fx_lookup_erases X C A EX L m x) as Hread.
  destruct (fx_model_lookup EX L m x) as [v ev].
  change (v = lookup EX L m x) in Hread; subst v.
  destruct (fx_fullcheck_sides EX L m rest); cbn in *; now rewrite IH.
Qed.

(** Erasing the strict counted checker returns the original checker result. *)
Theorem fx_fullcheck_erasure : fx_fullcheck_erasure_contract.

Proof.
  intros X C A EX L S m.
  unfold fx_fullcheck_erasure_statement, fx_fullcheck_counted, check_post.
  induction (System.constraints S) as [|c rest IH].
  - reflexivity.
  - cbn [fx_fullcheck_constraints].
    pose proof (@fx_query_erases X C A EX L (System.rhs S c) m) as Hquery.
    destruct (fx_model_query EX L (System.rhs S c) m)
      as [[[value reads] sides] query_events] eqn:Hquery_run.
    change ((value, reads, sides) = Query.run (System.rhs S c) (lookup EX L m)) in Hquery.
    pose proof (@fx_lookup_erases X C A EX L m (System.target S c)) as Hlookup.
    destruct (fx_model_lookup EX L m (System.target S c)) as [old lookup_events].
    change (old = lookup EX L m (System.target S c)) in Hlookup; subst old.
    pose proof (ffc_sides_erases X C A EX L m sides) as Hsides.
    destruct (fx_fullcheck_sides EX L m sides) as [ok body]; cbn in Hsides.
    destruct (fx_fullcheck_constraints EX L S m rest) as [tail later]; cbn in IH.
    cbn; rewrite <- Hquery; cbn; now rewrite Hsides, IH.
Qed.

(** The strict checker work is bounded by the source input recurrence. *)
Theorem fx_fullcheck_input_bound : fx_fullcheck_input_bound_statement.
Proof.
  intros X C A EX EC L S m.
  pose proof (ffc_constraints_correct EX EC L S m (System.constraints S)) as H.
  unfold fx_fullcheck_counted, fx_fullcheck_input_budget, check_post.
  destruct (fx_fullcheck_constraints EX L S m (System.constraints S)); exact H.
Qed.

(** The selected trace budget accounts for the strict checker's work. *)
Theorem fx_fullcheck_selected_cost : fx_fullcheck_selected_cost_statement.
Proof.
  intros X C A EX EC L S m.
  pose proof (fx_fullcheck_erasure X C A EX L S m) as Herase.
  unfold fx_fullcheck_erasure_statement in Herase.
  destruct (fx_fullcheck_counted EX L S m) as [out events].
  cbn in Herase; split; [exact Herase|].
  unfold fx_fullcheck_work, fx_fullcheck_budget.
  induction events as [|event rest IH]; cbn; [lia|].
  destruct event; cbn [fx_fullcheck_event_work fx_fullcheck_event_budget];
    try lia.
  rewrite fx_work_equation; lia.
Qed.
