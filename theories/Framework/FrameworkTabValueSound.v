(** * Leastness of the actual prefix-value worklist

    Every intermediate value map is below every post-solution of the public value analysis.
    For example, exhaustion retains the same pointwise lower-bound invariant as a stopped run.
    Builds on: FrameworkTabValues and public IDE value-row reflection. *)

From Stdlib Require Import List Bool PArith.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseIndex.
From Galois.Lattice Require Import LatticeCore.
From Galois.Program Require Import ProgramCfg ProgramIcfg.
From Galois.Fixpoint Require Import FixpointSystem FixpointAnalysis.
From Galois.Framework Require Import FrameworkUtil FrameworkMicro FrameworkIfds FrameworkIde
  FrameworkTabValues.
Import List.ListNotations.

Module TabValueSound.

(** Intermediate maps are bounded on all queries, including absent and unlisted keys. *)
Definition bounded {N E P D A F} (I : Ide.t N E P D A F) sigma
    (s : TabValues.state N D A) :=
  Map.wf (IdeValue.key_enc I) (TabValues.values s) /\
  forall v, leb (Ide.values I) (TabValues.lookup I (TabValues.values s) v) (sigma v) = true.

Local Lemma fold_valid {X S} (P : S -> Prop) (f : S -> X -> S) xs s :
  (forall s x, P s -> In x xs -> P (f s x)) -> P s -> P (fold_left f xs s).
Proof.
  revert s; induction xs as [|x xs IH]; intros s Hstep Hs; cbn [fold_left].
  - exact Hs.
  - apply IH.
    + intros t y Ht Hy; apply Hstep; [exact Ht|right; exact Hy].
    + apply Hstep; [exact Hs|left; reflexivity].
Qed.

Local Lemma schedule_bounded {N E P D A F} (I : Ide.t N E P D A F) sigma v s :
  bounded I sigma s -> bounded I sigma (Cost.value (TabValues.schedule_c I v s)).
Proof.
  intro Hbound; rewrite TabValues.schedule_equation.
  destruct (FinSet.mem (IdeValue.key_enc I) v (TabValues.pending s)); exact Hbound.
Qed.

(** Value leastness requires the value lattice's own least-join laws. *)
Theorem update_bounded {N E P D A F} (I : Ide.t N E P D A F) sigma v a s :
  encoding_laws (IdeValue.key_enc I) -> lub_laws (Ide.values I) ->
  bounded I sigma s -> leb (Ide.values I) a (sigma v) = true ->
  bounded I sigma (Cost.value (TabValues.update_c I v a s)).
Proof.
  intros HE Hlub [Hwf Hbound] Ha; rewrite TabValues.update_equation.
  destruct (leb (Ide.values I) a (TabValues.lookup I (TabValues.values s) v)).
  - split; assumption.
  - apply schedule_bounded; split; [apply Map.wf_set; exact Hwf|].
    intro q; cbn [TabValues.values].
    rewrite TabValues.lookup_equation, Map.find_or_equation, Map.get_set by exact Hwf.
    destruct (eqb (IdeValue.key_enc I) q v) eqn:Hkey.
    + apply (eqb_true_iff (IdeValue.key_enc I) HE) in Hkey; subst q.
      apply join_least; [exact Hlub|apply Hbound|exact Ha].
    + specialize (Hbound q).
      rewrite TabValues.lookup_equation, Map.find_or_equation in Hbound; exact Hbound.
Qed.

Section Run.
Context {N E P D A F} (I : Ide.t N E P D A F) (J : Map.t positive F)
  (start : N * option D) (a0 : A) (sigma : (N * option D) -> A).
Context (HN : encoding_laws (Cfg.node_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I))))).
Context (HE : encoding_laws (Cfg.edge_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I))))).
Context (HD : encoding_laws (Ifds.fact_enc (Ide.ifds I))).
Context (HL : lattice_laws (Ide.values I)) (HJ : lub_laws (Ide.values I)).
Context (HM : micro_laws (Ide.values I) (Ide.micro I)).
Context (Hpost : post_solution (Ide.values I)
  (Analysis.system (value_analysis I (Jump.lookup_c I J) start a0)) sigma).

Local Lemma key_laws : encoding_laws (IdeValue.key_enc I).
Proof.
  apply FrameworkKey.pair_laws; [exact HN|apply FrameworkKey.option_laws; exact HD].
Qed.

Local Lemma transition_bound a :
  In a (TabValues.transitions I J start) ->
  leb (Ide.values I)
    (Micro.apply (Ide.micro I) (snd a) (sigma (fst (fst a))))
    (sigma (snd (fst a))) = true.
Proof.
  pose proof (proj1 (value_analysis_post_solution_iff I (Jump.lookup_c I J) start a0 sigma
    HN HE HD) Hpost) as Hrows.
  destruct Hrows as [Hseed [Hjumps Hcalls]].
  rewrite TabValues.transitions_spec.
  intros [[root [dst [Hroot [Hdst Heq]]]]|[call [p [Hcall [Hkind Heq]]]]]; subst a.
  - apply Hjumps; assumption.
  - apply Hcalls with (p := p); assumption.
Qed.

Local Lemma arc_bounded a s :
  bounded I sigma s -> In a (TabValues.transitions I J start) ->
  bounded I sigma (Cost.value (TabValues.arc_c I a s)).
Proof.
  intros Hbound Ha; rewrite TabValues.arc_equation.
  apply update_bounded; [exact key_laws|exact HJ|exact Hbound|].
  eapply leb_trans; [exact HL| |exact (transition_bound a Ha)].
  apply (apply_mono _ _ HM); apply (proj2 Hbound).
Qed.

Local Lemma outgoing_member v a :
  In a (Index.find (IdeValue.key_enc I) v
    (TabValues.outgoing (TabValues.prepare I J start))) ->
  In a (TabValues.transitions I J start).
Proof.
  rewrite TabValues.prepare_equation; cbn [TabValues.outgoing].
  rewrite Index.find_group_by; intro Hin; apply filter_In in Hin; exact (proj1 Hin).
Qed.

Local Lemma initial_bounded :
  bounded I sigma (Cost.value (TabValues.initial_c I (TabValues.prepare I J start) start a0)).
Proof.
  rewrite TabValues.initial_equation; apply update_bounded.
  - exact key_laws.
  - exact HJ.
  - apply fold_valid.
    + intros s v Hs Hv; apply schedule_bounded; exact Hs.
    + split; [apply Map.wf_empty|].
      intro v; cbn [TabValues.values].
      rewrite TabValues.lookup_equation, Map.find_or_equation, Map.get_empty.
      apply bot_least; exact HL.
  - exact (proj1 (proj1 (value_analysis_post_solution_iff I (Jump.lookup_c I J)
      start a0 sigma HN HE HD) Hpost)).
Qed.

Local Lemma step_bounded s :
  bounded I sigma s ->
  match Cost.value (TabValues.step_c I (TabValues.prepare I J start) s) with
  | inl next | inr next => bounded I sigma next
  end.
Proof.
  intro Hbound; rewrite TabValues.step_equation.
  destruct (TabValues.work s) as [|v rest]; [exact Hbound|].
  apply fold_valid.
  - intros t a Ht Ha; apply arc_bounded; [exact Ht|].
    apply outgoing_member with (v := v); exact Ha.
  - exact Hbound.
Qed.

(** Every raw value state is below every actual public value post-solution under value lub laws. *)
Theorem raw_bounded fuel :
  match TabValues.raw I J start a0 fuel with
  | inl s | inr s => bounded I sigma s
  end.
Proof.
  rewrite TabValues.raw_equation.
  pose proof (iterate_value (TabValues.step_c I (TabValues.prepare I J start)) fuel
    (Cost.value (TabValues.initial_c I (TabValues.prepare I J start) start a0))) as Hrun.
  assert (Hpreserved : forall n s result,
    runs (TabValues.step_c I (TabValues.prepare I J start)) n s result ->
    bounded I sigma s ->
    match result with
    | inl next | inr next => bounded I sigma next
    end).
  { intros n s result Hr; induction Hr as [s|n s r Hstop|n s next result Hnext Hr IH];
      intro Hbound.
    - exact Hbound.
    - pose proof (step_bounded s Hbound) as Hstep; rewrite Hstop in Hstep; exact Hstep.
    - apply IH; pose proof (step_bounded s Hbound) as Hstep.
      rewrite Hnext in Hstep; exact Hstep. }
  exact (Hpreserved _ _ _ Hrun initial_bounded).
Qed.

(** Certified fueled value outcomes are least among post-solutions of the actual value analysis. *)
Theorem tabulate_values_least fuel c :
  TabValues.tabulate_values I J start a0 fuel = TabValues.Certified c ->
  forall v, leb (Ide.values I)
    (TabValues.lookup I (proj1_sig c) v) (sigma v) = true.
Proof.
  intros Hresult v; pose proof (raw_bounded fuel) as Hbound.
  rewrite TabValues.outcome_equation in Hresult.
  destruct (TabValues.raw I J start a0 fuel) as [s|s] eqn:Hraw; [discriminate|].
  apply TabValues.certify_candidate in Hresult; rewrite Hresult.
  exact (proj2 Hbound v).
Qed.

End Run.

End TabValueSound.
