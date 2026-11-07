(** * Dense backward agreement

    Backward constraints turn local agreement obligations into behavioural equivalence.
    For example, two stores can differ on data that no later observation needs.
    Builds on: FrameworkDense, ProgramRuns, ProgramSimulation and LatticeConcrete. *)

From Stdlib Require Import List.
From Galois.Lattice Require Import LatticeCore LatticeConcrete.
From Galois.Graph Require Import GraphModel.
From Galois.Fixpoint Require Import FixpointSystem.
From Galois.Program Require Import ProgramSemantics ProgramSteps ProgramCfg ProgramLink
  ProgramRuns ProgramSimulation.
From Galois.Framework Require Import FrameworkDense.
Import List.ListNotations.

Module DenseAgreement.

(** Symmetry is an explicit additional duty beyond the weak agreement laws. *)
Definition agreement_symmetric {A C} (R : agreement A C) : Prop :=
  forall a x y, agree R a x y -> agree R a y x.

(** Swapping agreement reverses its concrete arguments and keeps its abstract need. *)
Definition agreement_swap {A C} (R : agreement A C) : agreement A C :=
  Agreement A C (fun a x y => agree R a y x).

(** An invariant contains initials, is step-closed and implies reachability. *)
Record invariant_of {S O} (m : semantics S O) (inv : S -> Prop) : Prop := {
  inv_initial : forall s, initial m s -> inv s;
  inv_step : forall s l s', inv s -> step m s l s' -> inv s';
  inv_reachable : forall s, inv s -> reachable_state m s
}.
Arguments inv_initial {S O m inv}.
Arguments inv_step {S O m inv}.
Arguments inv_reachable {S O m inv}.

(** Absent boundaries impose the bottom need, without requiring bottom agreement to be full. *)
Definition exit_fact {N E A} (D : Dense.t N E A) n : A :=
  match Dense.boundary D n with
  | Some a => a
  | None => bot (Dense.lat D)
  end.

(** Backward inputs are graph targets. *)
Theorem from_backward {N E A} (D : Dense.t N E A) e :
  Dense.dir D = Backward -> Dense.from D e = Graph.target (Cfg.graph (Dense.cfg D)) e.
Proof.
  intro Hdir; unfold Dense.from, Dense.from_c; rewrite Hdir; reflexivity.
Qed.

(** Backward outputs are graph sources. *)
Theorem into_backward {N E A} (D : Dense.t N E A) e :
  Dense.dir D = Backward -> Dense.into D e = Graph.source (Cfg.graph (Dense.cfg D)) e.
Proof.
  intro Hdir; unfold Dense.into, Dense.into_c; rewrite Hdir; reflexivity.
Qed.

(** Backward seeds include every listed node, regardless of reachability or terminal status. *)
Theorem seeds_backward {N E A} (D : Dense.t N E A) :
  Dense.dir D = Backward -> Dense.seeds D = Graph.nodes (Cfg.graph (Dense.cfg D)).
Proof.
  intro Hdir; unfold Dense.seeds; rewrite Hdir; reflexivity.
Qed.

(** Every listed backward boundary, including an absent one, is below the solution. *)
Theorem boundary_bound {N E A} (D : Dense.t N E A) sigma n :
  Dense.dir D = Backward -> lattice_laws (Dense.lat D) ->
  post_solution (Dense.lat D) (Dense.system D) sigma ->
  In n (Graph.nodes (Cfg.graph (Dense.cfg D))) ->
  leb (Dense.lat D) (exit_fact D n) (sigma n) = true.
Proof.
  intros Hdir HL Hpost Hn; unfold exit_fact.
  destruct (Dense.boundary D n) as [a|] eqn:Ha.
  - destruct (proj1 (Dense.post_solution_iff D sigma HL) Hpost) as [Hseed _].
    apply Hseed; [rewrite (seeds_backward D Hdir); exact Hn|exact Ha].
  - apply (bot_least HL).
Qed.

(** Local lock-step matches preserve agreement at the destination need. *)
Definition step_agrees {S O N E A} (m : semantics S O) (D : Dense.t N E A)
    (lk : Link.t S O N E) (R : agreement A S) (inv : S -> Prop) (sigma : N -> A) : Prop :=
  (forall e t, on_steps m (fun s l s' =>
    inv s -> inv t -> Link.point lk t = Link.point lk s -> Link.taken lk s l s' e ->
    agree R (Dense.transfer D e (sigma (Graph.target (Cfg.graph (Dense.cfg D)) e))) s t ->
    exists t', step m t l t' /\ Link.taken lk t l t' e /\
      agree R (sigma (Graph.target (Cfg.graph (Dense.cfg D)) e)) s' t')) /\
  (forall t, on_steps m (fun s l s' =>
    inv s -> inv t -> Link.point lk t = Link.point lk s -> Link.stays lk s l s' ->
    agree R (sigma (Link.point lk s)) s t ->
    exists t', step m t l t' /\ Link.stays lk t l t' /\
      agree R (sigma (Link.point lk s)) s' t')).

(** Boundary agreement determines the three declared endings on invariant states. *)
Definition ends_agree {S O N E A} (en : endings S) (D : Dense.t N E A)
    (lk : Link.t S O N E) (R : agreement A S) (inv : S -> Prop) : Prop :=
  forall s t, inv s -> inv t -> Link.point lk t = Link.point lk s ->
    agree R (exit_fact D (Link.point lk s)) s t ->
    (final en s <-> final en t) /\ (trapped en s <-> trapped en t) /\
    (stopped en s <-> stopped en t).

(** Related states share a point, satisfy the invariant and agree at its solution fact. *)
Definition agreeing {S O N E A} (lk : Link.t S O N E) (R : agreement A S)
    (inv : S -> Prop) (sigma : N -> A) (s t : S) : Prop :=
  Link.point lk t = Link.point lk s /\ inv s /\ inv t /\
    agree R (sigma (Link.point lk s)) s t.

(** Reachability is an invariant for every semantics. *)
Theorem reachable_invariant {S O} (m : semantics S O) : invariant_of m (reachable_state m).
Proof.
  constructor.
  - intros s Hinitial; exists s, []; split; [exact Hinitial|constructor].
  - intros s l s' Hreachable Hstep; eapply reachable_state_step; eassumption.
  - intros s Hreachable; exact Hreachable.
Qed.

Lemma invariant_exec {S O} (m : semantics S O) inv :
  invariant_of m inv -> forall s tr t, exec m s tr t -> inv s -> inv t.
Proof.
  intros Hinv s tr t Hrun; induction Hrun as [s|s l s' tr t Hstep Hrun IH]; intro Hs.
  - exact Hs.
  - apply IH; eapply inv_step; eassumption.
Qed.

Lemma agreement_swap_laws {A C} (L : lattice A) (R : agreement A C) :
  agreement_laws L R -> agreement_laws L (agreement_swap R).
Proof.
  intro HR; constructor.
  - intros a c; apply (agree_refl HR).
  - intros a b x y Hab Hxy; exact (agree_antitone HR a b y x Hab Hxy).
Qed.

Lemma agreeing_sym {S O N E A} (lk : Link.t S O N E) (R : agreement A S)
    inv sigma s t :
  agreement_symmetric R -> agreeing lk R inv sigma s t -> agreeing lk R inv sigma t s.
Proof.
  intros Hsym [Hpoint [Hs [Ht Hagree]]]; unfold agreeing.
  split; [symmetry; exact Hpoint|]; split; [exact Ht|]; split; [exact Hs|].
  rewrite Hpoint; apply Hsym; exact Hagree.
Qed.

Lemma agreement_step {S O N E A} (m : semantics S O) (D : Dense.t N E A)
    (lk : Link.t S O N E) R inv sigma :
  Dense.dir D = Backward -> lattice_laws (Dense.lat D) ->
  link_laws m (Cfg.graph (Dense.cfg D)) lk -> agreement_laws (Dense.lat D) R ->
  invariant_of m inv -> step_agrees m D lk R inv sigma ->
  post_solution (Dense.lat D) (Dense.system D) sigma ->
  forall s t l s', agreeing lk R inv sigma s t -> step m s l s' ->
    exists t', step m t l t' /\ agreeing lk R inv sigma s' t'.
Proof.
  intros Hdir HL Hlink HR Hinv [Hedge Hstay] Hpost s t l s'
    [Hpoint [Hs [Ht Hagree]]] Hstep.
  pose proof (inv_reachable Hinv s Hs) as Hreachable.
  destruct (edge_covers Hlink s l s' Hreachable Hstep) as [Hstays|[e Htaken]].
  - destruct (Hstay t s l s' Hreachable Hstep Hs Ht Hpoint Hstays Hagree)
      as [t' [Hmatch [Hstays' Hagree']]].
    exists t'; split; [exact Hmatch|].
    pose proof (stays_point Hlink s l s' Hreachable Hstep Hstays) as Hsource.
    pose proof (stays_point Hlink t l t' (inv_reachable Hinv t Ht) Hmatch Hstays')
      as Htarget.
    unfold agreeing; rewrite Hsource, Htarget; repeat split; try assumption.
    + exact (inv_step Hinv s l s' Hs Hstep).
    + exact (inv_step Hinv t l t' Ht Hmatch).
  - destruct (link_taken_edge m (Dense.cfg D) lk s l s' e Hlink Hreachable Hstep Htaken)
      as [He [Hsource Htarget]].
    destruct (proj1 (Dense.post_solution_iff D sigma HL) Hpost) as [_ Hflow].
    assert (Hinput :
      agree R (Dense.transfer D e (sigma (Graph.target (Cfg.graph (Dense.cfg D)) e))) s t).
    { pose proof (Hflow e He) as Hbound.
      rewrite (from_backward D e Hdir), (into_backward D e Hdir) in Hbound.
      eapply (agree_antitone HR); [exact Hbound|rewrite Hsource; exact Hagree]. }
    destruct (Hedge e t s l s' Hreachable Hstep Hs Ht Hpoint Htaken Hinput)
      as [t' [Hmatch [Htaken' Hagree']]].
    destruct (taken_edge Hlink e t l t' (inv_reachable Hinv t Ht) Hmatch Htaken')
      as [_ Htarget'].
    exists t'; split; [exact Hmatch|]; unfold agreeing; repeat split.
    + congruence.
    + exact (inv_step Hinv s l s' Hs Hstep).
    + exact (inv_step Hinv t l t' Ht Hmatch).
    + rewrite <- Htarget; exact Hagree'.
Qed.

(** A backward post-solution and local obligations give a lock-step bisimulation. *)
Theorem agreement_bisimulation {S O N E A} (m : semantics S O) (en : endings S)
    (D : Dense.t N E A) (lk : Link.t S O N E)
    (R : (N -> A) -> agreement A S) (inv : S -> Prop) (sigma : N -> A) :
  Dense.dir D = Backward -> lattice_laws (Dense.lat D) ->
  link_laws m (Cfg.graph (Dense.cfg D)) lk -> agreement_laws (Dense.lat D) (R sigma) ->
  agreement_symmetric (R sigma) -> invariant_of m inv ->
  step_agrees m D lk (R sigma) inv sigma -> ends_agree en D lk (R sigma) inv ->
  post_solution (Dense.lat D) (Dense.system D) sigma ->
  bisimulation m en m en (agreeing lk (R sigma) inv sigma).
Proof.
  intros Hdir HL Hlink HR Hsym Hinv Hstep Hends Hpost.
  pose proof (agreement_step m D lk (R sigma) inv sigma
    Hdir HL Hlink HR Hinv Hstep Hpost) as Hmatch.
  constructor.
  - intros s t k Hrel; destruct Hrel as [Hpoint [Hs [Ht Hagree]]].
    assert (Hexit : agree (R sigma) (exit_fact D (Link.point lk s)) s t).
    { eapply (agree_antitone HR); [eapply boundary_bound; eauto|exact Hagree].
      eapply reachable_point_in_nodes; [exact Hlink|exact (inv_reachable Hinv s Hs)]. }
    destruct (Hends s t Hs Ht Hpoint Hexit) as [Hfinal [Htrap Hstop]].
    assert (Hrel : agreeing lk (R sigma) inv sigma s t) by (repeat split; assumption).
    assert (Hreverse : agreeing lk (R sigma) inv sigma t s).
    { apply agreeing_sym; assumption. }
    assert (Hrunning : running m s <-> running m t).
    { split; intros [l [u Hrun]].
      - destruct (Hmatch s t l u Hrel Hrun) as [v [Hrun' _]]; exists l, v; exact Hrun'.
      - destruct (Hmatch t s l u Hreverse Hrun) as [v [Hrun' _]]; exists l, v; exact Hrun'. }
    destruct k; cbn; [exact Hfinal|exact Htrap|exact Hstop|].
    change ((~ running m s /\ ~ final en s /\ ~ trapped en s /\ ~ stopped en s) <->
      (~ running m t /\ ~ final en t /\ ~ trapped en t /\ ~ stopped en t)).
    tauto.
  - exact Hmatch.
  - intros s t l t' Hrel Hrun.
    destruct (Hmatch t s l t' (agreeing_sym _ _ _ _ _ _ Hsym Hrel) Hrun)
      as [s' [Hrun' Hrel']].
    exists s'; split; [exact Hrun'|apply agreeing_sym; assumption].
Qed.

(** Initially agreeing states have equal finishes, traces and diverging prefixes. *)
Theorem agreement_same_behaviour {S O N E A} (m : semantics S O) (en : endings S)
    (D : Dense.t N E A) (lk : Link.t S O N E)
    (R : (N -> A) -> agreement A S) (inv : S -> Prop) (sigma : N -> A) s0 t0 :
  Dense.dir D = Backward -> lattice_laws (Dense.lat D) ->
  link_laws m (Cfg.graph (Dense.cfg D)) lk -> agreement_laws (Dense.lat D) (R sigma) ->
  agreement_symmetric (R sigma) -> invariant_of m inv ->
  step_agrees m D lk (R sigma) inv sigma -> ends_agree en D lk (R sigma) inv ->
  post_solution (Dense.lat D) (Dense.system D) sigma ->
  initial m s0 -> initial m t0 -> Link.point lk t0 = Link.point lk s0 ->
  agree (R sigma) (sigma (Link.point lk s0)) s0 t0 ->
  same_behaviour m en s0 m en t0.
Proof.
  intros Hdir HL Hlink HR Hsym Hinv Hstep Hends Hpost Hs Ht Hpoint Hagree.
  eapply bisimilar_same_behaviour.
  - eapply agreement_bisimulation; eassumption.
  - unfold agreeing; repeat split; try assumption; apply (inv_initial Hinv); assumption.
Qed.

(** One program's steps match silently or decrease the measure of an unmatched stay. *)
Definition forth_agrees {S O N E A} (ma mb : semantics S O) (D : Dense.t N E A)
    (lka lkb : Link.t S O N E) (R : agreement A S) (inva invb : S -> Prop)
    (sigma : N -> A) (mua : S -> S -> nat) : Prop :=
  (forall e t, on_steps ma (fun s l s' =>
    inva s -> invb t -> Link.point lkb t = Link.point lka s -> Link.taken lka s l s' e ->
    agree R (Dense.transfer D e (sigma (Graph.target (Cfg.graph (Dense.cfg D)) e))) s t ->
    exists t1 t', exec mb t [] t1 /\ step mb t1 l t' /\
      Link.point lkb t' = Link.point lka s' /\
      agree R (sigma (Link.point lka s')) s' t')) /\
  (forall t, on_steps ma (fun s l s' =>
    inva s -> invb t -> Link.point lkb t = Link.point lka s -> Link.stays lka s l s' ->
    agree R (sigma (Link.point lka s)) s t ->
    (l = [] /\ agree R (sigma (Link.point lka s)) s' t /\ mua s' t < mua s t) \/
    (exists t1 t', exec mb t [] t1 /\ step mb t1 l t' /\
      Link.point lkb t' = Link.point lka s' /\
      agree R (sigma (Link.point lka s')) s' t'))).

(** All four ending tags must match after a silent run. *)
Definition ends_forth {S O N E A} (ma mb : semantics S O) (ea eb : endings S)
    (D : Dense.t N E A) (lka lkb : Link.t S O N E) (R : agreement A S)
    (inva invb : S -> Prop) : Prop :=
  forall s t k, inva s -> invb t -> Link.point lkb t = Link.point lka s ->
    agree R (exit_fact D (Link.point lka s)) s t -> ends_as ma ea k s ->
    exists t1, exec mb t [] t1 /\ ends_as mb eb k t1.

(** Two-way step obligations reverse the concrete arguments of agreement on return. *)
Definition step_agrees2 {S O N E A} (m1 m2 : semantics S O) (D : Dense.t N E A)
    (lk1 lk2 : Link.t S O N E) (R : agreement A S) (inv1 inv2 : S -> Prop)
    (sigma : N -> A) (mu1 mu2 : S -> S -> nat) : Prop :=
  forth_agrees m1 m2 D lk1 lk2 R inv1 inv2 sigma mu1 /\
  forth_agrees m2 m1 D lk2 lk1 (agreement_swap R) inv2 inv1 sigma (fun t s => mu2 s t).

(** Two-way ending obligations retain final, trapped, stopped and stuck observations. *)
Definition ends_agree2 {S O N E A} (m1 m2 : semantics S O) (en1 en2 : endings S)
    (D : Dense.t N E A) (lk1 lk2 : Link.t S O N E)
    (R : agreement A S) (inv1 inv2 : S -> Prop) : Prop :=
  ends_forth m1 m2 en1 en2 D lk1 lk2 R inv1 inv2 /\
  ends_forth m2 m1 en2 en1 D lk2 lk1 (agreement_swap R) inv2 inv1.

(** Each side of a two-program relation satisfies its own invariant. *)
Definition agreeing2 {S O N E A} (lk1 lk2 : Link.t S O N E) (R : agreement A S)
    (inv1 inv2 : S -> Prop) (sigma : N -> A) (s t : S) : Prop :=
  Link.point lk2 t = Link.point lk1 s /\ inv1 s /\ inv2 t /\
    agree R (sigma (Link.point lk1 s)) s t.

Lemma agreeing2_swap {S O N E A} (lk1 lk2 : Link.t S O N E)
    (R : agreement A S) inv1 inv2 sigma s t :
  agreeing2 lk1 lk2 R inv1 inv2 sigma s t <->
  agreeing2 lk2 lk1 (agreement_swap R) inv2 inv1 sigma t s.
Proof.
  unfold agreeing2, agreement_swap; cbn; split; intros [Hpoint [Hs [Ht Hagree]]].
  - rewrite Hpoint; repeat split; try assumption; symmetry; exact Hpoint.
  - rewrite Hpoint; repeat split; try assumption; symmetry; exact Hpoint.
Qed.

Lemma agreement_forth {S O N E A} (ma mb : semantics S O) (D : Dense.t N E A)
    (lka lkb : Link.t S O N E) R inva invb sigma mua :
  Dense.dir D = Backward -> lattice_laws (Dense.lat D) ->
  link_laws ma (Cfg.graph (Dense.cfg D)) lka -> agreement_laws (Dense.lat D) R ->
  invariant_of ma inva -> invariant_of mb invb ->
  forth_agrees ma mb D lka lkb R inva invb sigma mua ->
  post_solution (Dense.lat D) (Dense.system D) sigma ->
  forall s t l s', agreeing2 lka lkb R inva invb sigma s t -> step ma s l s' ->
    (l = [] /\ agreeing2 lka lkb R inva invb sigma s' t /\ mua s' t < mua s t) \/
    (exists t1 t', exec mb t [] t1 /\ step mb t1 l t' /\
      agreeing2 lka lkb R inva invb sigma s' t').
Proof.
  intros Hdir HL Hlink HR Hinva Hinvb [Hedge Hstay] Hpost s t l s'
    [Hpoint [Hs [Ht Hagree]]] Hstep.
  pose proof (inv_reachable Hinva s Hs) as Hreachable.
  assert (Hs' : inva s') by (eapply inv_step; eassumption).
  destruct (edge_covers Hlink s l s' Hreachable Hstep) as [Hstays|[e Htaken]].
  - destruct (Hstay t s l s' Hreachable Hstep Hs Ht Hpoint Hstays Hagree)
      as [[Hsilent [Hagree' Hdecrease]]|[t1 [t' [Hprefix [Hmatch [Hpoint' Hagree']]]]]].
    + left; split; [exact Hsilent|]; split; [|exact Hdecrease].
      unfold agreeing2; rewrite (stays_point Hlink s l s' Hreachable Hstep Hstays).
      repeat split; assumption.
    + right; exists t1, t'; split; [exact Hprefix|]; split; [exact Hmatch|].
      unfold agreeing2; repeat split; try assumption.
      eapply inv_step; [exact Hinvb| |exact Hmatch]; eapply invariant_exec; eassumption.
  - destruct (link_taken_edge ma (Dense.cfg D) lka s l s' e
      Hlink Hreachable Hstep Htaken) as [He [Hsource Htarget]].
    destruct (proj1 (Dense.post_solution_iff D sigma HL) Hpost) as [_ Hflow].
    assert (Hinput :
      agree R (Dense.transfer D e (sigma (Graph.target (Cfg.graph (Dense.cfg D)) e))) s t).
    { pose proof (Hflow e He) as Hbound.
      rewrite (from_backward D e Hdir), (into_backward D e Hdir) in Hbound.
      eapply (agree_antitone HR); [exact Hbound|rewrite Hsource; exact Hagree]. }
    destruct (Hedge e t s l s' Hreachable Hstep Hs Ht Hpoint Htaken Hinput)
      as [t1 [t' [Hprefix [Hmatch [Hpoint' Hagree']]]]].
    right; exists t1, t'; split; [exact Hprefix|]; split; [exact Hmatch|].
    unfold agreeing2; repeat split; try assumption.
    eapply inv_step; [exact Hinvb| |exact Hmatch]; eapply invariant_exec; eassumption.
Qed.

Lemma agreement_ends_forth {S O N E A} (ma mb : semantics S O) ea eb
    (D : Dense.t N E A) (lka lkb : Link.t S O N E) R inva invb sigma :
  Dense.dir D = Backward -> lattice_laws (Dense.lat D) ->
  link_laws ma (Cfg.graph (Dense.cfg D)) lka -> agreement_laws (Dense.lat D) R ->
  invariant_of ma inva -> ends_forth ma mb ea eb D lka lkb R inva invb ->
  post_solution (Dense.lat D) (Dense.system D) sigma ->
  forall s t k, agreeing2 lka lkb R inva invb sigma s t -> ends_as ma ea k s ->
    exists t1, exec mb t [] t1 /\ ends_as mb eb k t1.
Proof.
  intros Hdir HL Hlink HR Hinv Hends Hpost s t k [Hpoint [Hs [Ht Hagree]]] Hend.
  apply (Hends s t k Hs Ht Hpoint); [|exact Hend].
  eapply (agree_antitone HR); [eapply boundary_bound; eauto|exact Hagree].
  eapply reachable_point_in_nodes; [exact Hlink|exact (inv_reachable Hinv s Hs)].
Qed.

(** Two-program local obligations and decreasing stays give equal observable behaviours. *)
Theorem agreement_simulation2 {S O N E A} (m1 m2 : semantics S O) (en1 en2 : endings S)
    (D : Dense.t N E A) (lk1 lk2 : Link.t S O N E)
    (R : (N -> A) -> agreement A S) (inv1 inv2 : S -> Prop) (sigma : N -> A)
    (mu1 mu2 : S -> S -> nat) s0 t0 :
  Dense.dir D = Backward -> lattice_laws (Dense.lat D) ->
  link_laws m1 (Cfg.graph (Dense.cfg D)) lk1 ->
  link_laws m2 (Cfg.graph (Dense.cfg D)) lk2 -> agreement_laws (Dense.lat D) (R sigma) ->
  invariant_of m1 inv1 -> invariant_of m2 inv2 ->
  step_agrees2 m1 m2 D lk1 lk2 (R sigma) inv1 inv2 sigma mu1 mu2 ->
  ends_agree2 m1 m2 en1 en2 D lk1 lk2 (R sigma) inv1 inv2 ->
  post_solution (Dense.lat D) (Dense.system D) sigma ->
  initial m1 s0 -> initial m2 t0 -> Link.point lk2 t0 = Link.point lk1 s0 ->
  agree (R sigma) (sigma (Link.point lk1 s0)) s0 t0 ->
  same_behaviour m1 en1 s0 m2 en2 t0.
Proof.
  intros Hdir HL Hlink1 Hlink2 HR Hinv1 Hinv2 [Hforth Hback] [Hends1 Hends2]
    Hpost Hs0 Ht0 Hpoint Hagree.
  pose proof (agreement_swap_laws (Dense.lat D) (R sigma) HR) as HRswap.
  eapply stuttering_same_behaviour with (R := agreeing2 lk1 lk2 (R sigma) inv1 inv2 sigma)
    (mu1 := mu1) (mu2 := mu2).
  - constructor.
    + eapply agreement_ends_forth; eassumption.
    + intros s t k Hrel Hend.
      eapply (agreement_ends_forth m2 m1 en2 en1 D lk2 lk1 (agreement_swap (R sigma))
        inv2 inv1 sigma Hdir HL Hlink2 HRswap Hinv2 Hends2 Hpost t s k).
      * apply agreeing2_swap; exact Hrel.
      * exact Hend.
    + eapply agreement_forth; eassumption.
    + intros s t l t' Hrel Hstep.
      destruct (agreement_forth m2 m1 D lk2 lk1 (agreement_swap (R sigma)) inv2 inv1
        sigma (fun t s => mu2 s t) Hdir HL Hlink2 HRswap Hinv2 Hinv1 Hback Hpost
        t s l t' (proj1 (agreeing2_swap _ _ _ _ _ _ _ _) Hrel) Hstep)
        as [[Hsilent [Hrel' Hdecrease]]|[s1 [s' [Hprefix [Hmatch Hrel']]]]].
      * left; split; [exact Hsilent|]; split; [apply agreeing2_swap; exact Hrel'|exact Hdecrease].
      * right; exists s1, s'; split; [exact Hprefix|]; split; [exact Hmatch|].
        apply agreeing2_swap; exact Hrel'.
  - unfold agreeing2; repeat split; try assumption.
    + apply (inv_initial Hinv1); exact Hs0.
    + apply (inv_initial Hinv2); exact Ht0.
Qed.

End DenseAgreement.
