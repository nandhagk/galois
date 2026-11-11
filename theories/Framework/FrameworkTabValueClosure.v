(** * Closure of stopped prefix-value worklists

    Every uncovered transition is either pending at its source or still in the current scan.
    For example, a self-update reschedules its source instead of silently discarding a dirty row.
    Builds on: FrameworkTabValues, FrameworkTabQueue and FrameworkTabValueProgress. *)

From Stdlib Require Import List Bool PArith.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseIndex.
From Galois.Lattice Require Import LatticeCore LatticeHeight.
From Galois.Program Require Import ProgramCfg ProgramIcfg.
From Galois.Fixpoint Require Import FixpointSystem FixpointAnalysis.
From Galois.Framework Require Import FrameworkUtil FrameworkMicro FrameworkIfds FrameworkIde
  FrameworkTabValues FrameworkTabQueue FrameworkTabValueProgress FrameworkTabValueSound
  FrameworkTabCost.
Import List.ListNotations.

Module TabValueClosure.

(** A covered transition bounds its actual application at its actual destination. *)
Definition covered {N E P D A F} (I : Ide.t N E P D A F) (s : TabValues.state N D A)
    (a : TabValues.arc N D F) :=
  leb (Ide.values I)
    (Micro.apply (Ide.micro I) (snd a)
      (TabValues.lookup I (TabValues.values s) (fst (fst a))))
    (TabValues.lookup I (TabValues.values s) (snd (fst a))) = true.

(** Uncovered rows remain pending either in the real queue or in the unfinished local scan. *)
Definition backlog {N E P D A F} (I : Ide.t N E P D A F) J start s todo :=
  forall a, In a (TabValues.transitions I J start) ->
    covered I s a \/ In (fst (fst a)) (TabValues.work s) \/ In a todo.

(** The actual seed remains covered while all subsequent joins ascend. *)
Definition seeded {N E P D A F} (I : Ide.t N E P D A F) start a0 s :=
  leb (Ide.values I) a0 (TabValues.lookup I (TabValues.values s) start) = true.

Local Lemma lookup_set {N E P D A F} (I : Ide.t N E P D A F) m key value query :
  Map.wf (IdeValue.key_enc I) m ->
  TabValues.lookup I (Map.set (IdeValue.key_enc I) key value m) query =
    if eqb (IdeValue.key_enc I) query key then value else TabValues.lookup I m query.
Proof.
  intro Hwf; rewrite !TabValues.lookup_equation, !Map.find_or_equation.
  rewrite Map.get_set by exact Hwf.
  destruct (eqb (IdeValue.key_enc I) query key); reflexivity.
Qed.

Local Lemma schedule_effect {N E P D A F} (I : Ide.t N E P D A F) key s :
  TabQueue.coherent (IdeValue.key_enc I) (TabValues.work s) (TabValues.pending s) ->
  let after := Cost.value (TabValues.schedule_c I key s) in
  TabValues.values after = TabValues.values s /\
    incl (TabValues.work s) (TabValues.work after) /\ In key (TabValues.work after).
Proof.
  intro Hqueue; rewrite TabValues.schedule_equation.
  destruct (FinSet.mem (IdeValue.key_enc I) key (TabValues.pending s)) eqn:Hqueued.
  - split; [reflexivity|]; split; [intros q Hq; exact Hq|].
    exact (TabQueue.queued_in_work (IdeValue.key_enc I) key
      (TabValues.work s) (TabValues.pending s) Hqueue Hqueued).
  - split; [reflexivity|]; split.
    + intros q Hq; right; exact Hq.
    + left; reflexivity.
Qed.

Local Lemma update_effects {N E P D A F} (I : Ide.t N E P D A F) key candidate s :
  encoding_laws (IdeValue.key_enc I) -> lattice_laws (Ide.values I) ->
  TabValueProgress.shape I s ->
  let after := Cost.value (TabValues.update_c I key candidate s) in
  (forall q, leb (Ide.values I) (TabValues.lookup I (TabValues.values s) q)
    (TabValues.lookup I (TabValues.values after) q) = true) /\
  incl (TabValues.work s) (TabValues.work after) /\
  (forall q, TabValues.lookup I (TabValues.values after) q =
    TabValues.lookup I (TabValues.values s) q \/ In q (TabValues.work after)) /\
  leb (Ide.values I) candidate (TabValues.lookup I (TabValues.values after) key) = true.
Proof.
  intros HE HL [Hwf Hqueue]; rewrite TabValues.update_equation.
  destruct (leb (Ide.values I) candidate (TabValues.lookup I (TabValues.values s) key))
    eqn:Hcovered.
  - split; [intro q; apply leb_refl; exact HL|].
    split; [intros q Hq; exact Hq|]; split; [intro q; left; reflexivity|exact Hcovered].
  - set (updated := Map.set (IdeValue.key_enc I) key
      (join (Ide.values I) (TabValues.lookup I (TabValues.values s) key) candidate)
      (TabValues.values s)).
    remember (Cost.value (TabValues.schedule_c I key
      (TabValues.State updated (TabValues.work s) (TabValues.pending s)))) as after eqn:Hafter.
    pose proof (schedule_effect I key
      (TabValues.State updated (TabValues.work s) (TabValues.pending s)) Hqueue) as Heffect.
    rewrite <- Hafter in Heffect; destruct Heffect as [Hvalues [Hwork Hkey]].
    cbn [TabValues.values TabValues.work] in Hvalues, Hwork, Hkey.
    split.
    + intro q; rewrite Hvalues; unfold updated; rewrite lookup_set by exact Hwf.
      destruct (eqb (IdeValue.key_enc I) q key) eqn:Heq.
      * apply (eqb_true_iff (IdeValue.key_enc I) HE) in Heq; subst q.
        apply join_upper_l; exact HL.
      * apply leb_refl; exact HL.
    + split; [exact Hwork|]; split.
      * intro q; rewrite Hvalues; unfold updated; rewrite lookup_set by exact Hwf.
        destruct (eqb (IdeValue.key_enc I) q key) eqn:Heq; [|left; reflexivity].
        apply (eqb_true_iff (IdeValue.key_enc I) HE) in Heq; subst q; right; exact Hkey.
      * rewrite Hvalues; unfold updated; rewrite lookup_set by exact Hwf.
        rewrite eqb_refl; apply join_upper_r; exact HL.
Qed.

Section Run.
Context {N E P D A F} (I : Ide.t N E P D A F) (J : Map.t positive F)
  (start : N * option D) (a0 : A).
Context (HE : encoding_laws (IdeValue.key_enc I)) (HL : lattice_laws (Ide.values I)).

Local Lemma update_preserves_covered s key candidate row :
  TabValueProgress.shape I s -> covered I s row ->
  let after := Cost.value (TabValues.update_c I key candidate s) in
    covered I after row \/ In (fst (fst row)) (TabValues.work after).
Proof.
  intros Hshape Hcovered.
  destruct (update_effects I key candidate s HE HL Hshape) as
    [Hgrow [Hwork [Hsource Hcandidate]]].
  destruct (Hsource (fst (fst row))) as [Hsame|Hpending]; [left|right; exact Hpending].
  unfold covered; rewrite Hsame.
  eapply leb_trans; [exact HL|exact Hcovered|apply Hgrow].
Qed.

Local Lemma arc_backlog s row todo :
  TabValueProgress.shape I s -> backlog I J start s (row :: todo) ->
  backlog I J start (Cost.value (TabValues.arc_c I row s)) todo.
Proof.
  intros Hshape Hbacklog; rewrite TabValues.arc_equation.
  set (candidate := Micro.apply (Ide.micro I) (snd row)
    (TabValues.lookup I (TabValues.values s) (fst (fst row)))).
  set (after := Cost.value (TabValues.update_c I (snd (fst row)) candidate s)).
  destruct (update_effects I (snd (fst row)) candidate s HE HL Hshape) as
    [Hgrow [Hwork [Hsource Hcandidate]]].
  fold after in Hgrow, Hwork, Hsource, Hcandidate.
  assert (Hrow : covered I after row \/ In (fst (fst row)) (TabValues.work after)).
  { destruct (Hsource (fst (fst row))) as [Hsame|Hpending]; [left|right; exact Hpending].
    unfold covered; rewrite Hsame; exact Hcandidate. }
  intros other Hother; destruct (Hbacklog other Hother) as [Hold|[Hpending|Htodo]].
  - destruct (update_preserves_covered s (snd (fst row)) candidate other Hshape Hold)
      as [Hcovered|Hqueued]; [left; exact Hcovered|right; left; exact Hqueued].
  - right; left; apply Hwork; exact Hpending.
  - destruct Htodo as [Heq|Htodo].
    + subst other; destruct Hrow; [left|right; left]; assumption.
    + right; right; exact Htodo.
Qed.

Local Lemma arc_shape s a :
  TabValueProgress.shape I s ->
  TabValueProgress.shape I (Cost.value (TabValues.arc_c I a s)).
Proof.
  intro Hshape; rewrite TabValues.arc_equation, TabValues.update_equation.
  destruct (leb (Ide.values I) _ _); [exact Hshape|].
  destruct Hshape as [Hwf Hqueue]; rewrite TabValues.schedule_equation.
  cbn [TabValues.pending TabValues.work TabValues.values].
  destruct (FinSet.mem (IdeValue.key_enc I) (snd (fst a)) (TabValues.pending s))
    eqn:Hqueued; split.
  - apply Map.wf_set; exact Hwf.
  - exact Hqueue.
  - apply Map.wf_set; exact Hwf.
  - apply TabQueue.insert_coherent; assumption.
Qed.

Local Lemma arc_seeded s a :
  TabValueProgress.shape I s -> seeded I start a0 s ->
  seeded I start a0 (Cost.value (TabValues.arc_c I a s)).
Proof.
  intros Hshape Hseed; rewrite TabValues.arc_equation.
  pose proof (update_effects I (snd (fst a))
    (Micro.apply (Ide.micro I) (snd a)
      (TabValues.lookup I (TabValues.values s) (fst (fst a)))) s HE HL Hshape) as Heffect.
  eapply leb_trans; [exact HL|exact Hseed|apply (proj1 Heffect)].
Qed.

Local Lemma fold_backlog todo s :
  TabValueProgress.shape I s -> seeded I start a0 s -> backlog I J start s todo ->
  TabValueProgress.shape I (fold_left (fun s a => Cost.value (TabValues.arc_c I a s)) todo s) /\
  seeded I start a0 (fold_left (fun s a => Cost.value (TabValues.arc_c I a s)) todo s) /\
  backlog I J start (fold_left (fun s a => Cost.value (TabValues.arc_c I a s)) todo s) [].
Proof.
  revert s; induction todo as [|row todo IH]; intros s Hshape Hseed Hbacklog; cbn [fold_left].
  - split; [exact Hshape|split; assumption].
  - apply IH.
    + apply arc_shape; exact Hshape.
    + apply arc_seeded; assumption.
    + apply arc_backlog; assumption.
Qed.

Local Lemma schedule_shape key s :
  TabValueProgress.shape I s ->
  TabValueProgress.shape I (Cost.value (TabValues.schedule_c I key s)).
Proof.
  intros [Hwf Hqueue]; rewrite TabValues.schedule_equation.
  destruct (FinSet.mem (IdeValue.key_enc I) key (TabValues.pending s)) eqn:Hqueued;
    split; try exact Hwf; try exact Hqueue.
  apply TabQueue.insert_coherent; assumption.
Qed.

Local Lemma schedule_all keys s :
  TabValueProgress.shape I s ->
  let final := fold_left (fun s key => Cost.value (TabValues.schedule_c I key s)) keys s in
  TabValueProgress.shape I final /\ incl (TabValues.work s) (TabValues.work final) /\
    forall key, In key keys -> In key (TabValues.work final).
Proof.
  revert s; induction keys as [|key keys IH]; intros s Hshape; cbn [fold_left].
  - split; [exact Hshape|]; split; [intros q Hq; exact Hq|intros q Hq; inversion Hq].
  - destruct (schedule_effect I key s (proj2 Hshape)) as [Hvalues [Hwork Hkey]].
    pose proof (schedule_shape key s Hshape) as Hscheduled.
    destruct (IH _ Hscheduled) as [Hfinal [Hnext Hkeys]]; split; [exact Hfinal|]; split.
    + intros q Hq; apply Hnext, Hwork; exact Hq.
    + intros q [Heq|Hq]; [subst q; apply Hnext; exact Hkey|apply Hkeys; exact Hq].
Qed.

Local Lemma initial_backlog :
  seeded I start a0
    (Cost.value (TabValues.initial_c I (TabValues.prepare I J start) start a0)) /\
  backlog I J start
    (Cost.value (TabValues.initial_c I (TabValues.prepare I J start) start a0)) [].
Proof.
  rewrite TabValues.initial_equation.
  pose proof (schedule_all (TabValues.sources (TabValues.prepare I J start))
    (TabValues.State Map.empty [] FinSet.empty)
    (conj (Map.wf_empty (IdeValue.key_enc I))
      (TabQueue.empty_coherent (IdeValue.key_enc I)))) as Hscheduled.
  destruct Hscheduled as [Hshape [Hwork Hsources]].
  pose proof (update_effects I start a0 _ HE HL Hshape) as Heffect.
  split; [exact (proj2 (proj2 (proj2 Heffect)))|].
  intros a Ha; right; left; apply (proj1 (proj2 Heffect)).
  apply Hsources; rewrite TabValues.prepare_equation; cbn [TabValues.sources].
  right; apply in_map_iff; exists a; split; [reflexivity|exact Ha].
Qed.

Local Lemma step_backlog s :
  TabValueProgress.shape I s -> seeded I start a0 s -> backlog I J start s [] ->
  match Cost.value (TabValues.step_c I (TabValues.prepare I J start) s) with
  | inl next | inr next =>
    TabValueProgress.shape I next /\ seeded I start a0 next /\ backlog I J start next []
  end.
Proof.
  intros Hshape Hseed Hbacklog; rewrite TabValues.step_equation.
  destruct (TabValues.work s) as [|key rest] eqn:Hwork.
  - split; [exact Hshape|split; assumption].
  - apply fold_backlog.
    + destruct Hshape as [Hwf Hqueue]; split; [exact Hwf|].
      cbn [TabValues.work TabValues.pending].
      apply TabQueue.pop_coherent; [exact HE|rewrite Hwork in Hqueue; exact Hqueue].
    + exact Hseed.
    + intros a Ha; destruct (Hbacklog a Ha) as [Hcovered|[Hpending|Hbad]].
      * left; exact Hcovered.
      * rewrite Hwork in Hpending; destruct Hpending as [Hsource|Htail].
        -- right; right; rewrite TabValues.prepare_equation; cbn [TabValues.outgoing].
           rewrite Index.find_group_by; apply filter_In; split; [exact Ha|].
           cbn beta; apply (proj2 (eqb_true_iff (IdeValue.key_enc I) HE _ _)).
           symmetry; exact Hsource.
        -- right; left; exact Htail.
      * inversion Hbad.
Qed.

(** Every raw state retains the actual seed and closure up to its actual pending sources. *)
Theorem raw_backlog fuel :
  match TabValues.raw I J start a0 fuel with
  | inl s | inr s => seeded I start a0 s /\ backlog I J start s []
  end.
Proof.
  rewrite TabValues.raw_equation.
  pose proof (iterate_value (TabValues.step_c I (TabValues.prepare I J start)) fuel
    (Cost.value (TabValues.initial_c I (TabValues.prepare I J start) start a0))) as Hrun.
  assert (Hpreserved : forall n s result,
    runs (TabValues.step_c I (TabValues.prepare I J start)) n s result ->
    (TabValueProgress.shape I s /\ seeded I start a0 s /\ backlog I J start s []) ->
    match result with
    | inl next | inr next =>
      TabValueProgress.shape I next /\ seeded I start a0 next /\ backlog I J start next []
    end).
  { intros n s result Hr; induction Hr as [s|n s r Hstop|n s next result Hnext Hr IH];
      intros [Hshape [Hseed Hbacklog]].
    - split; [exact Hshape|split; assumption].
    - pose proof (step_backlog s Hshape Hseed Hbacklog) as Hstep.
      rewrite Hstop in Hstep; exact Hstep.
    - apply IH; pose proof (step_backlog s Hshape Hseed Hbacklog) as Hstep.
      rewrite Hnext in Hstep; exact Hstep. }
  specialize (Hpreserved _ _ _ Hrun
    (conj (proj1 (TabValueProgress.initial_invariant I J start a0 HE)) initial_backlog)).
  destruct (Cost.value (iterate _ fuel _)); exact (proj2 Hpreserved).
Qed.

Local Lemma raw_stopped_empty fuel stopped :
  TabValues.raw I J start a0 fuel = inr stopped -> TabValues.work stopped = [].
Proof.
  rewrite TabValues.raw_equation; intro Hresult.
  destruct (iterate_inr_stops (TabValues.step_c I (TabValues.prepare I J start)) fuel
    (Cost.value (TabValues.initial_c I (TabValues.prepare I J start) start a0))
    stopped Hresult) as [used [last [Hused [Hprefix Hstop]]]].
  rewrite TabValues.step_equation in Hstop.
  destruct (TabValues.work last) as [|key rest] eqn:Hwork; [|discriminate].
  injection Hstop as Hsame; subst stopped; exact Hwork.
Qed.

(** Every actually stopped raw map satisfies the public value analysis before certification. *)
Theorem stopped_post fuel stopped :
  encoding_laws (Cfg.node_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) ->
  encoding_laws (Cfg.edge_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) ->
  encoding_laws (Ifds.fact_enc (Ide.ifds I)) ->
  TabValues.raw I J start a0 fuel = inr stopped ->
  TabValues.post I J start a0 (TabValues.values stopped).
Proof.
  intros HN HEedge HD Hrun.
  pose proof (raw_backlog fuel) as Hclosed; rewrite Hrun in Hclosed.
  destruct Hclosed as [Hseed Hbacklog].
  pose proof (raw_stopped_empty fuel stopped Hrun) as Hempty.
  assert (Hall : forall a, In a (TabValues.transitions I J start) -> covered I stopped a).
  { intros a Ha; destruct (Hbacklog a Ha) as [Hcovered|[Hpending|Hbad]].
    - exact Hcovered.
    - rewrite Hempty in Hpending; inversion Hpending.
    - inversion Hbad. }
  apply (proj2 (value_analysis_post_solution_iff I (Jump.lookup_c I J) start a0
    (TabValues.lookup I (TabValues.values stopped)) HN HEedge HD)).
  split; [exact Hseed|]; split.
  - intros root dst Hroot Hdst.
    apply (Hall ((root, dst), Jump.lookup I J (root, dst))), TabValues.transitions_spec; left.
    exists root, dst; repeat split; assumption || reflexivity.
  - intros call p Hcall Hkind.
    apply (Hall ((Jump.source call, Jump.target call), Jump.weight call)).
    apply TabValues.transitions_spec; right.
    exists call, p; repeat split; assumption || reflexivity.
Qed.

End Run.

(** Finite-height value completion actually certifies without any successful-run or postcondition premise. *)
Theorem complete_certified {N E P D A F} (I : Ide.t N E P D A F) J start a0
    (H : height (Ide.values I)) :
  encoding_laws (Cfg.node_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) ->
  encoding_laws (Cfg.edge_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) ->
  encoding_laws (Ifds.fact_enc (Ide.ifds I)) ->
  lattice_laws (Ide.values I) ->
  exists c, TabValueProgress.complete I J start a0 H = TabValues.Certified c.
Proof.
  intros HN HEedge HD HL.
  assert (Hkey : encoding_laws (IdeValue.key_enc I)).
  { apply FrameworkKey.pair_laws; [exact HN|apply FrameworkKey.option_laws; exact HD]. }
  destruct (TabValueProgress.complete_raw_stops I J start a0 H Hkey HL) as
    [stopped [Hraw Hempty]].
  pose proof Hraw as Hrun; rewrite TabValueProgress.complete_raw_equation in Hrun.
  pose proof (stopped_post I J start a0 Hkey HL _ stopped HN HEedge HD Hrun) as Hpost.
  destruct (TabValues.certify_accepts I J start a0 stopped Hpost) as [c Hcertified].
  exists c; rewrite TabValueProgress.complete_equation, Hraw; exact Hcertified.
Qed.

(** Actual finite-height completion is least among the public value post-solutions under value lub laws. *)
Theorem complete_least {N E P D A F} (I : Ide.t N E P D A F) J start a0
    (H : height (Ide.values I)) sigma :
  encoding_laws (Cfg.node_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) ->
  encoding_laws (Cfg.edge_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) ->
  encoding_laws (Ifds.fact_enc (Ide.ifds I)) ->
  lattice_laws (Ide.values I) -> lub_laws (Ide.values I) ->
  micro_laws (Ide.values I) (Ide.micro I) ->
  post_solution (Ide.values I)
    (Analysis.system (value_analysis I (Jump.lookup_c I J) start a0)) sigma ->
  exists c, TabValueProgress.complete I J start a0 H = TabValues.Certified c /\
    forall v, leb (Ide.values I) (TabValues.lookup I (proj1_sig c) v) (sigma v) = true.
Proof.
  intros HN HE HD HL HJ HM Hpost.
  destruct (complete_certified I J start a0 H HN HE HD HL) as [c Hrun].
  exists c; split; [exact Hrun|].
  apply (TabValueSound.tabulate_values_least I J start a0 sigma HN HE HD HL HJ HM Hpost
    (TabCost.inventory_fuel (TabValues.inventory (TabValues.prepare I J start)) (bound H)) c).
  rewrite <- TabValueProgress.complete_agrees; exact Hrun.
Qed.

End TabValueClosure.
