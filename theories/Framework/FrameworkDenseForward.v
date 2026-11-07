(** * Dense forward invariants and histories

    Forward post-solutions contain states and ordered histories of reachable runs.
    For example, a history interpretation can track the last writing edge.
    Builds on: FrameworkDense, ProgramRuns and LatticeConcrete. *)

From Stdlib Require Import List.
From Galois.Lattice Require Import LatticeCore LatticeConcrete.
From Galois.Graph Require Import GraphModel.
From Galois.Fixpoint Require Import FixpointSystem.
From Galois.Program Require Import ProgramSemantics ProgramSteps ProgramCfg ProgramLink ProgramRuns.
From Galois.Framework Require Import FrameworkDense FrameworkDenseAgreement.
Import List.ListNotations.

Module DenseForward.

(** Every graph entry has a present boundary fact, including entries outside raw node lists. *)
Definition boundary_covers {N E A} (D : Dense.t N E A) : Prop :=
  forall n, In n (Graph.entries (Cfg.graph (Dense.cfg D))) ->
    exists a, Dense.boundary D n = Some a.

(** A forward invariant combines reachability and the solution's concrete interpretation. *)
Definition forward_inv {S O N E A} (m : semantics S O) (lk : Link.t S O N E)
    (G : concretisation A S) (sigma : N -> A) (s : S) : Prop :=
  reachable_state m s /\ gamma G (sigma (Link.point lk s)) s.

(** Forward inputs are the graph sources. *)
Theorem from_forward {N E A} (D : Dense.t N E A) e :
  Dense.dir D = Forward -> Dense.from D e = Graph.source (Cfg.graph (Dense.cfg D)) e.
Proof.
  intro Hdir; unfold Dense.from, Dense.from_c; rewrite Hdir; reflexivity.
Qed.

(** Forward outputs are the graph targets. *)
Theorem into_forward {N E A} (D : Dense.t N E A) e :
  Dense.dir D = Forward -> Dense.into D e = Graph.target (Cfg.graph (Dense.cfg D)) e.
Proof.
  intro Hdir; unfold Dense.into, Dense.into_c; rewrite Hdir; reflexivity.
Qed.

(** Forward seeds range over the listed entry occurrences. *)
Theorem seeds_forward {N E A} (D : Dense.t N E A) :
  Dense.dir D = Forward -> Dense.seeds D = Graph.entries (Cfg.graph (Dense.cfg D)).
Proof.
  intro Hdir; unfold Dense.seeds; rewrite Hdir; reflexivity.
Qed.

(** A history from an initial state ends at a reachable state. *)
Theorem history_reachable {S O N E} (m : semantics S O) (lk : Link.t S O N E) s0 es s :
  initial m s0 -> run_edges m lk s0 es s -> reachable_state m s.
Proof.
  intros Hinitial Hhistory.
  destruct (run_edges_exec m lk s0 s es Hhistory) as [tr Hrun].
  exists s0, tr; split; assumption.
Qed.

(** Prefix-local obligations extend a history predicate through taken and stationary steps. *)
Theorem history_induction {S O N E} (m : semantics S O) (lk : Link.t S O N E)
    (P : S -> list E -> S -> Prop) :
  (forall s, initial m s -> P s [] s) ->
  (forall e s0 es, on_steps m (fun s l s' =>
    initial m s0 -> run_edges m lk s0 es s -> Link.taken lk s l s' e ->
    P s0 es s -> P s0 (es ++ [e]) s')) ->
  (forall s0 es, on_steps m (fun s l s' =>
    initial m s0 -> run_edges m lk s0 es s -> Link.stays lk s l s' ->
    P s0 es s -> P s0 es s')) ->
  forall s0 es s, initial m s0 -> run_edges m lk s0 es s -> P s0 es s.
Proof.
  intros Hinitial Hedge Hstay s0 es s Hs0 Hhistory.
  assert (Hextend : forall mid fs t, run_edges m lk mid fs t -> forall pre,
    run_edges m lk s0 pre mid -> P s0 pre mid -> P s0 (pre ++ fs) t).
  { intros mid fs t Hsuffix; induction Hsuffix as
      [mid|mid l mid' e fs t Hstep Htaken Hsuffix IH|
       mid l mid' fs t Hstep Hstays Hsuffix IH]; intros pre Hprefix Hfact.
    - rewrite app_nil_r; exact Hfact.
    - replace (pre ++ e :: fs) with ((pre ++ [e]) ++ fs) by
        (rewrite <- app_assoc; reflexivity).
      apply IH.
      + eapply run_edges_app; [exact Hprefix|].
        econstructor; [exact Hstep|exact Htaken|constructor].
      + eapply Hedge; try eassumption; eapply history_reachable; eassumption.
    - apply IH.
      + rewrite <- (app_nil_r pre); eapply run_edges_app; [exact Hprefix|].
        eapply run_stay; [exact Hstep|exact Hstays|constructor].
      + eapply Hstay; try eassumption; eapply history_reachable; eassumption. }
  apply (Hextend s0 es s Hhistory []); [constructor|apply Hinitial; exact Hs0].
Qed.

(** A present entry fact transports its interpretation to the post-solution. *)
Theorem forward_initial_fact {S O N E A C} (m : semantics S O)
    (D : Dense.t N E A) (lk : Link.t S O N E) (G : concretisation A C)
    sigma s c a :
  Dense.dir D = Forward -> lattice_laws (Dense.lat D) ->
  link_laws m (Cfg.graph (Dense.cfg D)) lk -> concretisation_laws (Dense.lat D) G ->
  initial m s -> Dense.boundary D (Link.point lk s) = Some a ->
  gamma G a c -> post_solution (Dense.lat D) (Dense.system D) sigma ->
  gamma G (sigma (Link.point lk s)) c.
Proof.
  intros Hdir HL Hlink HG Hinitial Hboundary Hfact Hpost.
  destruct (proj1 (Dense.post_solution_iff D sigma HL) Hpost) as [Hseed _].
  eapply (gamma_monotone HG); [apply Hseed|exact Hfact].
  - rewrite (seeds_forward D Hdir); apply (entry_points Hlink); exact Hinitial.
  - exact Hboundary.
Qed.

(** Local transfer and stay obligations preserve a solution-relative state fact. *)
Theorem forward_fact_step {S O N E A} (m : semantics S O) (D : Dense.t N E A)
    (lk : Link.t S O N E) (G : concretisation A S) (sigma : N -> A) :
  Dense.dir D = Forward -> lattice_laws (Dense.lat D) ->
  link_laws m (Cfg.graph (Dense.cfg D)) lk -> concretisation_laws (Dense.lat D) G ->
  (forall e, on_steps m (fun s l s' => Link.taken lk s l s' e ->
    gamma G (sigma (Link.point lk s)) s ->
    gamma G (Dense.transfer D e (sigma (Link.point lk s))) s')) ->
  (on_steps m (fun s l s' => Link.stays lk s l s' ->
    gamma G (sigma (Link.point lk s)) s -> gamma G (sigma (Link.point lk s)) s')) ->
  post_solution (Dense.lat D) (Dense.system D) sigma ->
  on_steps m (fun s _ s' =>
    gamma G (sigma (Link.point lk s)) s -> gamma G (sigma (Link.point lk s')) s').
Proof.
  intros Hdir HL Hlink HG Hedge Hstay Hpost s l s' Hreachable Hstep Hfact.
  destruct (edge_covers Hlink s l s' Hreachable Hstep) as [Hstays|[e Htaken]].
  - rewrite (stays_point Hlink s l s' Hreachable Hstep Hstays).
    eapply Hstay; eassumption.
  - destruct (link_taken_edge m (Dense.cfg D) lk s l s' e
      Hlink Hreachable Hstep Htaken) as [He [Hsource Htarget]].
    destruct (proj1 (Dense.post_solution_iff D sigma HL) Hpost) as [_ Hflow].
    eapply (gamma_monotone HG).
    + pose proof (Hflow e He) as Hbound.
      rewrite (from_forward D e Hdir), (into_forward D e Hdir),
        Hsource, Htarget in Hbound; exact Hbound.
    + eapply Hedge; eassumption.
Qed.

(** A forward post-solution contains every reachable state under its local obligations. *)
Theorem forward_invariant_sound {S O N E A} (m : semantics S O) (D : Dense.t N E A)
    (lk : Link.t S O N E) (G : (N -> A) -> concretisation A S) (sigma : N -> A) :
  Dense.dir D = Forward -> lattice_laws (Dense.lat D) ->
  link_laws m (Cfg.graph (Dense.cfg D)) lk ->
  concretisation_laws (Dense.lat D) (G sigma) -> boundary_covers D ->
  (forall s a, initial m s -> Dense.boundary D (Link.point lk s) = Some a ->
    gamma (G sigma) a s) ->
  (forall e, on_steps m (fun s l s' => Link.taken lk s l s' e ->
    gamma (G sigma) (sigma (Link.point lk s)) s ->
    gamma (G sigma) (Dense.transfer D e (sigma (Link.point lk s))) s')) ->
  on_steps m (fun s l s' => Link.stays lk s l s' ->
    gamma (G sigma) (sigma (Link.point lk s)) s ->
    gamma (G sigma) (sigma (Link.point lk s)) s') ->
  post_solution (Dense.lat D) (Dense.system D) sigma ->
  forall s, reachable_state m s -> gamma (G sigma) (sigma (Link.point lk s)) s.
Proof.
  intros Hdir HL Hlink HG Hcovers Hinitial Hedge Hstay Hpost.
  apply reachable_ind.
  - intros s Hs.
    destruct (Hcovers _ (entry_points Hlink s Hs)) as [a Ha].
    eapply forward_initial_fact; eauto.
  - intros s l s' Hs Hfact Hstep.
    eapply forward_fact_step; eassumption.
Qed.

(** Reachability together with a sound forward fact is an inductive invariant. *)
Theorem forward_inv_invariant {S O N E A} (m : semantics S O) (D : Dense.t N E A)
    (lk : Link.t S O N E) (G : (N -> A) -> concretisation A S) (sigma : N -> A) :
  Dense.dir D = Forward -> lattice_laws (Dense.lat D) ->
  link_laws m (Cfg.graph (Dense.cfg D)) lk ->
  concretisation_laws (Dense.lat D) (G sigma) -> boundary_covers D ->
  (forall s a, initial m s -> Dense.boundary D (Link.point lk s) = Some a ->
    gamma (G sigma) a s) ->
  (forall e, on_steps m (fun s l s' => Link.taken lk s l s' e ->
    gamma (G sigma) (sigma (Link.point lk s)) s ->
    gamma (G sigma) (Dense.transfer D e (sigma (Link.point lk s))) s')) ->
  on_steps m (fun s l s' => Link.stays lk s l s' ->
    gamma (G sigma) (sigma (Link.point lk s)) s ->
    gamma (G sigma) (sigma (Link.point lk s)) s') ->
  post_solution (Dense.lat D) (Dense.system D) sigma ->
  DenseAgreement.invariant_of m (forward_inv m lk (G sigma) sigma).
Proof.
  intros Hdir HL Hlink HG Hcovers Hinitial Hedge Hstay Hpost.
  pose proof (forward_invariant_sound m D lk G sigma
    Hdir HL Hlink HG Hcovers Hinitial Hedge Hstay Hpost) as Hsound.
  constructor.
  - intros s Hs; assert (Hr : reachable_state m s).
    { exists s, []; split; [exact Hs|constructor]. }
    split; [exact Hr|apply Hsound; exact Hr].
  - intros s l s' [Hr Hfact] Hstep.
    assert (Hr' : reachable_state m s') by (eapply reachable_state_step; eassumption).
    split; [exact Hr'|apply Hsound; exact Hr'].
  - intros s [Hr _]; exact Hr.
Qed.

(** History soundness retains every taken edge and permits arbitrary stationary transitions. *)
Theorem forward_history_sound {S O N E A} (m : semantics S O) (D : Dense.t N E A)
    (lk : Link.t S O N E) (G : (N -> A) -> concretisation A (S * list E))
    (sigma : N -> A) :
  Dense.dir D = Forward -> lattice_laws (Dense.lat D) ->
  link_laws m (Cfg.graph (Dense.cfg D)) lk ->
  concretisation_laws (Dense.lat D) (G sigma) -> boundary_covers D ->
  (forall s a, initial m s -> Dense.boundary D (Link.point lk s) = Some a ->
    gamma (G sigma) a (s, [])) ->
  (forall e s0 es, on_steps m (fun s l s' =>
    initial m s0 -> run_edges m lk s0 es s -> Link.taken lk s l s' e ->
    gamma (G sigma) (sigma (Link.point lk s)) (s, es) ->
    gamma (G sigma) (Dense.transfer D e (sigma (Link.point lk s))) (s', es ++ [e]))) ->
  (forall s0 es, on_steps m (fun s l s' =>
    initial m s0 -> run_edges m lk s0 es s -> Link.stays lk s l s' ->
    gamma (G sigma) (sigma (Link.point lk s)) (s, es) ->
    gamma (G sigma) (sigma (Link.point lk s)) (s', es))) ->
  post_solution (Dense.lat D) (Dense.system D) sigma ->
  forall s0 es s, initial m s0 -> run_edges m lk s0 es s ->
    gamma (G sigma) (sigma (Link.point lk s)) (s, es).
Proof.
  intros Hdir HL Hlink HG Hcovers Hinitial Hedge Hstay Hpost.
  destruct (proj1 (Dense.post_solution_iff D sigma HL) Hpost) as [_ Hflow].
  apply (history_induction m lk
    (fun _ es s => gamma (G sigma) (sigma (Link.point lk s)) (s, es))).
  - intros s Hs.
    destruct (Hcovers _ (entry_points Hlink s Hs)) as [a Ha].
    eapply forward_initial_fact; eauto.
  - intros e s0 es s l s' Hs Hstep Hs0 Hprefix Htaken Hfact.
    destruct (link_taken_edge m (Dense.cfg D) lk s l s' e Hlink Hs Hstep Htaken)
      as [He [Hsource Htarget]].
    eapply (gamma_monotone HG).
    + pose proof (Hflow e He) as Hbound.
      rewrite (from_forward D e Hdir), (into_forward D e Hdir),
        Hsource, Htarget in Hbound; exact Hbound.
    + eapply Hedge; eassumption.
  - intros s0 es s l s' Hs Hstep Hs0 Hprefix Hstays Hfact.
    rewrite (stays_point Hlink s l s' Hs Hstep Hstays).
    eapply Hstay; eassumption.
Qed.

End DenseForward.
