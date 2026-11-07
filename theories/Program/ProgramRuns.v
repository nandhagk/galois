(** * Semantic histories and graph paths

    Edge histories retain taken edges in order and omit stationary transitions.
    For example, two taken edges separated by a silent stay give a two-edge path.
    Builds on: ProgramLink, ProgramSteps and GraphModel. *)

From Stdlib Require Import List.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramSemantics ProgramSteps ProgramCfg ProgramLink.
Import List.ListNotations.

(** Histories record actual transitions and their taken or stationary classifications. *)
Inductive run_edges {S O N E} (m : semantics S O) (lk : Link.t S O N E) :
    S -> list E -> S -> Prop :=
  | run_refl : forall s, run_edges m lk s [] s
  | run_take : forall s l s' e es t, step m s l s' -> Link.taken lk s l s' e ->
      run_edges m lk s' es t -> run_edges m lk s (e :: es) t
  | run_stay : forall s l s' es t, step m s l s' -> Link.stays lk s l s' ->
      run_edges m lk s' es t -> run_edges m lk s es t.
Arguments run_refl {S O N E m lk}.
Arguments run_take {S O N E m lk}.
Arguments run_stay {S O N E m lk}.

(** Every history has a traced semantic run with the same endpoints. *)
Theorem run_edges_exec {S O N E} (m : semantics S O) (lk : Link.t S O N E) s t es :
  run_edges m lk s es t -> exists tr, exec m s tr t.
Proof.
  intro Hhistory; induction Hhistory as
    [s|s l s' e es t Hstep Htaken Hhistory IH|s l s' es t Hstep Hstays Hhistory IH].
  - exists []; constructor.
  - destruct IH as [tr Hrun]; exists (l ++ tr); econstructor; eassumption.
  - destruct IH as [tr Hrun]; exists (l ++ tr); econstructor; eassumption.
Qed.

(** Runs from reachable states admit histories by the link's coverage law. *)
Theorem exec_run_edges {S O N E} (m : semantics S O) g (lk : Link.t S O N E) s t tr :
  link_laws m g lk -> reachable_state m s -> exec m s tr t ->
  exists es, run_edges m lk s es t.
Proof.
  intros Hlink Hreachable Hrun; revert Hreachable.
  induction Hrun as [s|s l s' tr t Hstep Hrun IH]; intro Hreachable.
  - exists []; constructor.
  - destruct (IH (reachable_state_step m s l s' Hreachable Hstep)) as [es Hhistory].
    destruct (edge_covers Hlink s l s' Hreachable Hstep) as [Hstays|[e Htaken]].
    + exists es; eapply run_stay; eassumption.
    + exists (e :: es); econstructor; eassumption.
Qed.

(** A history from a reachable state follows a graph path between its points. *)
Theorem run_edges_path {S O N E} (m : semantics S O) g (lk : Link.t S O N E) s t es :
  link_laws m g lk -> reachable_state m s -> run_edges m lk s es t ->
  path g (Link.point lk s) es (Link.point lk t).
Proof.
  intros Hlink Hreachable Hhistory; revert Hreachable.
  induction Hhistory as
    [s|s l s' e es t Hstep Htaken Hhistory IH|s l s' es t Hstep Hstays Hhistory IH];
    intro Hreachable.
  - constructor.
  - destruct (taken_edge Hlink e s l s' Hreachable Hstep Htaken) as [Hout Htarget].
    pose proof (out_source (cfg_wf Hlink) _ _ Hout) as Hsource.
    rewrite <- Hsource; constructor.
    + rewrite Hsource; exact Hout.
    + rewrite Htarget; apply IH; eapply reachable_state_step; eassumption.
  - rewrite <- (stays_point Hlink s l s' Hreachable Hstep Hstays).
    apply IH; eapply reachable_state_step; eassumption.
Qed.

(** Every semantic run from a reachable state projects to some graph path. *)
Theorem exec_path {S O N E} (m : semantics S O) g (lk : Link.t S O N E) s t tr :
  link_laws m g lk -> reachable_state m s -> exec m s tr t ->
  exists es, run_edges m lk s es t /\ path g (Link.point lk s) es (Link.point lk t).
Proof.
  intros Hlink Hreachable Hrun.
  destruct (exec_run_edges m g lk s t tr Hlink Hreachable Hrun) as [es Hhistory].
  exists es; split; [exact Hhistory|eapply run_edges_path; eassumption].
Qed.

(** Reachable states have reachable graph points. *)
Theorem reachable_point {S O N E} (m : semantics S O) g (lk : Link.t S O N E) s :
  link_laws m g lk -> reachable_state m s -> reachable g (Link.point lk s).
Proof.
  intros Hlink [s0 [tr [Hinitial Hrun]]].
  assert (Hreachable : reachable_state m s0).
  { exists s0, []; split; [exact Hinitial|constructor]. }
  destruct (exec_path m g lk s0 s tr Hlink Hreachable Hrun) as [es [_ Hpath]].
  apply reachable_iff_path; exists (Link.point lk s0), es; split.
  - apply (entry_points Hlink); exact Hinitial.
  - exact Hpath.
Qed.

(** Every reachable point belongs to the presentation's listed node domain. *)
Theorem reachable_point_in_nodes {S O N E} (m : semantics S O) g
    (lk : Link.t S O N E) s :
  link_laws m g lk -> reachable_state m s -> In (Link.point lk s) (Graph.nodes g).
Proof.
  intros Hlink Hreachable; apply reachable_in_nodes; [apply (cfg_wf Hlink)|].
  eapply reachable_point; eassumption.
Qed.

(** A taken edge is listed and has the actual semantic source and target points. *)
Theorem link_taken_edge {S O N E} (m : semantics S O) (c : Cfg.t N E)
    (lk : Link.t S O N E) s l s' e :
  link_laws m (Cfg.graph c) lk -> reachable_state m s ->
  step m s l s' -> Link.taken lk s l s' e ->
  In e (Cfg.edges c) /\ Graph.source (Cfg.graph c) e = Link.point lk s /\
    Graph.target (Cfg.graph c) e = Link.point lk s'.
Proof.
  intros Hlink Hreachable Hstep Htaken.
  destruct (taken_edge Hlink e s l s' Hreachable Hstep Htaken) as [Hout Htarget].
  split.
  - apply Cfg.edges_spec; exists (Link.point lk s); split.
    + eapply reachable_point_in_nodes; eassumption.
    + exact Hout.
  - split; [eapply out_source; [apply (cfg_wf Hlink)|exact Hout]|exact Htarget].
Qed.

(** Histories concatenate through their actual shared endpoint. *)
Theorem run_edges_app {S O N E} (m : semantics S O) (lk : Link.t S O N E)
    s u t es1 es2 :
  run_edges m lk s es1 u -> run_edges m lk u es2 t -> run_edges m lk s (es1 ++ es2) t.
Proof.
  intro Hhistory; induction Hhistory as
    [s|s l s' e es u Hstep Htaken Hhistory IH|s l s' es u Hstep Hstays Hhistory IH];
    intro Htail.
  - exact Htail.
  - cbn; eapply run_take; [exact Hstep|exact Htaken|apply IH; exact Htail].
  - eapply run_stay; [exact Hstep|exact Hstays|apply IH; exact Htail].
Qed.

(** A run satisfies a step predicate at each of its actual transitions. *)
Inductive run_steps {S O} (m : semantics S O) (P : S -> list O -> S -> Prop) :
    S -> list O -> S -> Prop :=
  | run_steps_refl : forall s, run_steps m P s [] s
  | run_steps_cons : forall s l u tr t, P s l u -> step m s l u ->
      run_steps m P u tr t -> run_steps m P s (l ++ tr) t.

(** A step-local law holds throughout any run starting at a reachable state. *)
Theorem on_steps_run {S O} (m : semantics S O) P s tr t :
  on_steps m P -> reachable_state m s -> exec m s tr t -> run_steps m P s tr t.
Proof.
  intros Hlaw Hreach Hrun; revert Hreach.
  induction Hrun as [s|s l u tr t Hstep Hrun IH]; intro Hreach.
  - constructor.
  - eapply run_steps_cons with (l := l) (u := u) (tr := tr).
    + apply Hlaw; assumption.
    + exact Hstep.
    + apply IH; eapply reachable_state_step; eassumption.
Qed.
