(** * Dense witnesses and covers

    Fact interpretations connect dense solutions to histories and continuations.
    For example, a must fact can require an earlier computation with the current value.
    Builds on: FrameworkDenseForward, FrameworkDenseAgreement and ProgramRuns. *)

From Stdlib Require Import List.
From Galois.Lattice Require Import LatticeCore LatticeConcrete.
From Galois.Graph Require Import GraphModel.
From Galois.Fixpoint Require Import FixpointSystem.
From Galois.Program Require Import ProgramSemantics ProgramSteps ProgramCfg ProgramLink ProgramRuns.
From Galois.Framework Require Import FrameworkDense FrameworkDenseForward FrameworkDenseAgreement.
Import List.ListNotations.

Module DenseWitness.

(** May membership grows with the lattice order. *)
Definition holds_monotone {A F} (L : lattice A) (holds : A -> F -> Prop) : Prop :=
  forall a b u, leb L a b = true -> holds a u -> holds b u.

(** Must membership shrinks with the lattice order. *)
Definition holds_antitone {A F} (L : lattice A) (holds : A -> F -> Prop) : Prop :=
  forall a b u, leb L a b = true -> holds b u -> holds a u.

(** Must facts have witnesses on every actual run from an initial state. *)
Theorem forward_witness_sound {S O N E A F} (m : semantics S O) (D : Dense.t N E A)
    (lk : Link.t S O N E) (holds : A -> F -> Prop)
    (W : S -> list E -> S -> F -> Prop) (sigma : N -> A) :
  Dense.dir D = Forward -> lattice_laws (Dense.lat D) ->
  link_laws m (Cfg.graph (Dense.cfg D)) lk ->
  holds_antitone (Dense.lat D) holds -> DenseForward.boundary_covers D ->
  (forall s a u, initial m s -> Dense.boundary D (Link.point lk s) = Some a ->
    holds a u -> W s [] s u) ->
  (forall e s0 es a, on_steps m (fun s l s' =>
    initial m s0 -> run_edges m lk s0 es s -> Link.taken lk s l s' e ->
    (forall u, holds a u -> W s0 es s u) ->
    forall u, holds (Dense.transfer D e a) u -> W s0 (es ++ [e]) s' u)) ->
  (forall s0 es a, on_steps m (fun s l s' =>
    initial m s0 -> run_edges m lk s0 es s -> Link.stays lk s l s' ->
    (forall u, holds a u -> W s0 es s u) -> forall u, holds a u -> W s0 es s' u)) ->
  post_solution (Dense.lat D) (Dense.system D) sigma ->
  forall s0 es s u, initial m s0 -> run_edges m lk s0 es s ->
    holds (sigma (Link.point lk s)) u -> W s0 es s u.
Proof.
  intros Hdir HL Hlink Horder Hcovers Hinitial Hedge Hstay Hpost s0 es s u Hs0 Hrun Hu.
  destruct (proj1 (Dense.post_solution_iff D sigma HL) Hpost) as [Hseed Hflow].
  assert (Hfacts : forall origin fs t, initial m origin -> run_edges m lk origin fs t ->
    forall v, holds (sigma (Link.point lk t)) v -> W origin fs t v).
  { apply (DenseForward.history_induction m lk
      (fun origin fs t => forall v, holds (sigma (Link.point lk t)) v -> W origin fs t v)).
    - intros t Ht v Hv.
      destruct (Hcovers _ (entry_points Hlink t Ht)) as [a Ha].
      apply (Hinitial t a v Ht Ha); eapply Horder; [|exact Hv].
      apply Hseed; [rewrite (DenseForward.seeds_forward D Hdir);
        exact (entry_points Hlink t Ht)|exact Ha].
    - intros e origin fs t l t' Hr Hstep Hi Hprefix Htaken Hfact v Hv.
      destruct (link_taken_edge m (Dense.cfg D) lk t l t' e Hlink Hr Hstep Htaken)
        as [He [Hsource Htarget]].
      eapply Hedge; try eassumption.
      eapply Horder; [|exact Hv].
      pose proof (Hflow e He) as Hbound.
      rewrite (DenseForward.from_forward D e Hdir),
        (DenseForward.into_forward D e Hdir), Hsource, Htarget in Hbound.
      exact Hbound.
    - intros origin fs t l t' Hr Hstep Hi Hprefix Hstays Hfact v Hv.
      eapply Hstay; try eassumption.
      rewrite <- (stays_point Hlink t l t' Hr Hstep Hstays); exact Hv. }
  exact (Hfacts s0 es s Hs0 Hrun u Hu).
Qed.

(** May solutions cover every history witness under local forward production obligations. *)
Theorem forward_cover_sound {S O N E A F} (m : semantics S O) (D : Dense.t N E A)
    (lk : Link.t S O N E) (holds : A -> F -> Prop)
    (W : S -> list E -> S -> F -> Prop) (sigma : N -> A) :
  Dense.dir D = Forward -> lattice_laws (Dense.lat D) ->
  link_laws m (Cfg.graph (Dense.cfg D)) lk ->
  holds_monotone (Dense.lat D) holds -> DenseForward.boundary_covers D ->
  (forall s a u, initial m s -> Dense.boundary D (Link.point lk s) = Some a ->
    W s [] s u -> holds a u) ->
  (forall e s0 es a, on_steps m (fun s l s' =>
    initial m s0 -> run_edges m lk s0 es s -> Link.taken lk s l s' e ->
    (forall u, W s0 es s u -> holds a u) ->
    forall u, W s0 (es ++ [e]) s' u -> holds (Dense.transfer D e a) u)) ->
  (forall s0 es a, on_steps m (fun s l s' =>
    initial m s0 -> run_edges m lk s0 es s -> Link.stays lk s l s' ->
    (forall u, W s0 es s u -> holds a u) -> forall u, W s0 es s' u -> holds a u)) ->
  post_solution (Dense.lat D) (Dense.system D) sigma ->
  forall s0 es s u, initial m s0 -> run_edges m lk s0 es s ->
    W s0 es s u -> holds (sigma (Link.point lk s)) u.
Proof.
  intros Hdir HL Hlink Horder Hcovers Hinitial Hedge Hstay Hpost s0 es s u Hs0 Hrun Hu.
  destruct (proj1 (Dense.post_solution_iff D sigma HL) Hpost) as [Hseed Hflow].
  assert (Hfacts : forall origin fs t, initial m origin -> run_edges m lk origin fs t ->
    forall v, W origin fs t v -> holds (sigma (Link.point lk t)) v).
  { apply (DenseForward.history_induction m lk
      (fun origin fs t => forall v, W origin fs t v -> holds (sigma (Link.point lk t)) v)).
    - intros t Ht v Hv.
      destruct (Hcovers _ (entry_points Hlink t Ht)) as [a Ha].
      eapply Horder.
      + apply Hseed; [rewrite (DenseForward.seeds_forward D Hdir);
          exact (entry_points Hlink t Ht)|exact Ha].
      + eapply Hinitial; eassumption.
    - intros e origin fs t l t' Hr Hstep Hi Hprefix Htaken Hfact v Hv.
      destruct (link_taken_edge m (Dense.cfg D) lk t l t' e Hlink Hr Hstep Htaken)
        as [He [Hsource Htarget]].
      eapply Horder.
      + pose proof (Hflow e He) as Hbound.
        rewrite (DenseForward.from_forward D e Hdir),
          (DenseForward.into_forward D e Hdir), Hsource, Htarget in Hbound.
        exact Hbound.
      + eapply Hedge; eassumption.
    - intros origin fs t l t' Hr Hstep Hi Hprefix Hstays Hfact v Hv.
      rewrite (stays_point Hlink t l t' Hr Hstep Hstays); eapply Hstay; eassumption. }
  exact (Hfacts s0 es s Hs0 Hrun u Hu).
Qed.

(** Backward must facts witness every finite continuation ending in the selected predicate. *)
Theorem backward_witness_sound {S O N E A F} (m : semantics S O) (D : Dense.t N E A)
    (lk : Link.t S O N E) (holds : A -> F -> Prop) (Q : S -> Prop)
    (W : S -> list E -> S -> F -> Prop) (sigma : N -> A) :
  Dense.dir D = Backward -> lattice_laws (Dense.lat D) ->
  link_laws m (Cfg.graph (Dense.cfg D)) lk -> holds_antitone (Dense.lat D) holds ->
  (forall t u, reachable_state m t -> Q t ->
    holds (DenseAgreement.exit_fact D (Link.point lk t)) u -> W t [] t u) ->
  (forall e es t a, on_steps m (fun s l s' =>
    run_edges m lk s' es t -> Q t -> Link.taken lk s l s' e ->
    (forall u, holds a u -> W s' es t u) ->
    forall u, holds (Dense.transfer D e a) u -> W s (e :: es) t u)) ->
  (forall es t a, on_steps m (fun s l s' =>
    run_edges m lk s' es t -> Q t -> Link.stays lk s l s' ->
    (forall u, holds a u -> W s' es t u) -> forall u, holds a u -> W s es t u)) ->
  post_solution (Dense.lat D) (Dense.system D) sigma ->
  forall s es t u, reachable_state m s -> run_edges m lk s es t -> Q t ->
    holds (sigma (Link.point lk s)) u -> W s es t u.
Proof.
  intros Hdir HL Hlink Horder Hterminal Hedge Hstay Hpost s es t u Hs Hrun.
  revert Hs u; induction Hrun as
    [s|s l s' e es t Hstep Htaken Hrun IH|s l s' es t Hstep Hstays Hrun IH];
    intros Hs u HQ Hu.
  - apply Hterminal; [exact Hs|exact HQ|].
    eapply Horder; [eapply DenseAgreement.boundary_bound; eauto|exact Hu].
    eapply reachable_point_in_nodes; eassumption.
  - destruct (link_taken_edge m (Dense.cfg D) lk s l s' e Hlink Hs Hstep Htaken)
      as [He [Hsource Htarget]].
    destruct (proj1 (Dense.post_solution_iff D sigma HL) Hpost) as [_ Hflow].
    eapply (Hedge e es t (sigma (Link.point lk s')) s l s' Hs Hstep);
      try eassumption.
    + intros v Hv; apply IH; [eapply reachable_state_step; eassumption|exact HQ|exact Hv].
    + eapply Horder; [|exact Hu].
      pose proof (Hflow e He) as Hbound.
      rewrite (DenseAgreement.from_backward D e Hdir),
        (DenseAgreement.into_backward D e Hdir), Hsource, Htarget in Hbound.
      exact Hbound.
  - eapply (Hstay es t (sigma (Link.point lk s)) s l s' Hs Hstep); try eassumption.
    intros v Hv; apply IH; [eapply reachable_state_step; eassumption|exact HQ|].
    rewrite (stays_point Hlink s l s' Hs Hstep Hstays); exact Hv.
Qed.

End DenseWitness.
