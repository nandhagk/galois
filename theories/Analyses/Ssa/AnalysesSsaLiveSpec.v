(** * Point liveness and a shared oracle contract

    Liveness follows a finite kill-free prefix to an edge use or an exit use.
    For example, an edge that reads and defines one value makes that value live at its source.
    Builds on: ProgramSsaPoints, FrameworkBitvector and FrameworkGenkillLeast. *)

From Stdlib Require Import List Bool NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding.
From Galois.Lattice Require Import LatticeSet.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg ProgramSsaPoints.
From Galois.Fixpoint Require Import FixpointLeast FixpointAnalysis.
From Galois.Framework Require Import FrameworkDense FrameworkBitvector FrameworkDenseAgreement
  FrameworkGenkillSound FrameworkGenkillLeast.
Import List.ListNotations Cost.Notations.

Module Live.

(** The finite inventory is computational data and its coverage is a separate law. *)
Record model (N E V : Type) := Model {
  vars : Vars.t N E V;
  values : list V
}.
Arguments Model {N E V}.
Arguments vars {N E V}.
Arguments values {N E V}.

(** A live value reaches a use before a definition along the original point graph. *)
Definition live_at {N E V} (p : model N E V) n x : Prop :=
  syntactic_live (vars p) x n.

(** The local dense reference retains uses before kills and seeds every listed exit reader. *)
Definition problem {N E V} (p : model N E V) : Bitvector.t N E V :=
  Bitvector.Make (Vars.cfg (vars p)) (Vars.var_enc (vars p)) (values p) Backward
    (Vars.uses_c (vars p)) (Vars.defs_c (vars p))
    (fun n => Cost.step ;; Cost.map (@Some (list V)) (Vars.exits_c (vars p) n)).

(** Source laws require lawful dictionaries, graph closure and actual finite occurrence support. *)
Record laws {N E V} (p : model N E V) : Prop := Laws {
  node_keys : encoding_laws (Cfg.node_enc (Vars.cfg (vars p)));
  edge_keys : encoding_laws (Cfg.edge_enc (Vars.cfg (vars p)));
  value_keys : encoding_laws (Vars.var_enc (vars p));
  graph_closed : graph_wf (live_graph (vars p));
  edge_support : forall e, In e (Cfg.edges (Vars.cfg (vars p))) ->
    incl (Vars.uses (vars p) e) (values p) /\
    incl (Vars.defs (vars p) e) (values p);
  exit_support : forall n, In n (Graph.nodes (live_graph (vars p))) ->
    incl (Vars.exits (vars p) n) (values p)
}.
Arguments node_keys {N E V p}.
Arguments edge_keys {N E V p}.
Arguments value_keys {N E V p}.
Arguments graph_closed {N E V p}.
Arguments edge_support {N E V p}.
Arguments exit_support {N E V p}.

(** An oracle exposes charged point/value queries without semantic or termination evidence. *)
Record oracle (N V : Type) := Oracle {
  live_c : N -> V -> Cost.t bool
}.
Arguments Oracle {N V}.
Arguments live_c {N V}.

Definition live {N V} (o : oracle N V) n x := Cost.value (live_c o n x).

(** Exact query oracles decide the original specification at every reachable point. *)
Definition oracle_exact {N E V} (p : model N E V) (o : oracle N V) : Prop :=
  forall n x, reachable (live_graph (vars p)) n ->
    (live o n x = true <-> live_at p n x).

(** Materialized oracles additionally decide every listed point in unreachable components. *)
Definition oracle_all_exact {N E V} (p : model N E V) (o : oracle N V) : Prop :=
  forall n x, In n (Graph.nodes (live_graph (vars p))) ->
    (live o n x = true <-> live_at p n x).

(** The local problem uses the original presentation and the supplied finite inventory. *)
Theorem problem_data {N E V} (p : model N E V) :
  Bitvector.cfg (problem p) = Vars.cfg (vars p) /\
  Bitvector.fact_enc (problem p) = Vars.var_enc (vars p) /\
  Bitvector.universe (problem p) = values p /\
  Bitvector.dir (problem p) = Backward.
Proof.
  repeat split; reflexivity.
Qed.

(** Generation reads the same edge uses as the original point specification. *)
Theorem problem_gen {N E V} (p : model N E V) e :
  Bitvector.gen (problem p) e = Vars.uses (vars p) e.
Proof.
  reflexivity.
Qed.

(** Killing reads the same edge definitions as the original point specification. *)
Theorem problem_kill {N E V} (p : model N E V) e :
  Bitvector.kill (problem p) e = Vars.defs (vars p) e.
Proof.
  reflexivity.
Qed.

(** Every original exit reader becomes a present boundary, including at nonterminal points. *)
Theorem problem_boundary {N E V} (p : model N E V) n :
  Bitvector.boundary (problem p) n = Some (Vars.exits (vars p) n).
Proof.
  reflexivity.
Qed.

(** Exit adaptation retains the complete reader charge and one callback-dispatch tick. *)
Theorem problem_boundary_cost {N E V} (p : model N E V) n :
  Cost.ticks (Bitvector.boundary_c (problem p) n) =
    (1 + Cost.ticks (Vars.exits_c (vars p) n))%N.
Proof.
  unfold problem; cbn [Bitvector.boundary_c].
  rewrite Cost.ticks_bind, Cost.ticks_map, Cost.ticks_step.
  reflexivity.
Qed.

(** The local backward problem reads the target of the original edge. *)
Theorem problem_from {N E V} (p : model N E V) e :
  GenkillLeast.from (problem p) e = Graph.target (live_graph (vars p)) e.
Proof.
  exact (DenseAgreement.from_backward
    (Bitvector.may_dense (problem p) (Bitvector.prepare (problem p))) e eq_refl).
Qed.

(** The local backward problem writes the source of the original edge. *)
Theorem problem_into {N E V} (p : model N E V) e :
  GenkillLeast.into (problem p) e = Graph.source (live_graph (vars p)) e.
Proof.
  exact (DenseAgreement.into_backward
    (Bitvector.may_dense (problem p) (Bitvector.prepare (problem p))) e eq_refl).
Qed.

(** The local backward problem seeds all listed points, including unreachable points. *)
Theorem problem_seeds {N E V} (p : model N E V) :
  Bitvector.seeds (problem p) = Graph.nodes (live_graph (vars p)).
Proof.
  exact (DenseAgreement.seeds_backward
    (Bitvector.may_dense (problem p) (Bitvector.prepare (problem p))) eq_refl).
Qed.

(** Source occurrence coverage supplies the framework's finite-support duty. *)
Theorem problem_supported {N E V} (p : model N E V) :
  laws p -> Bitvector.supported (problem p).
Proof.
  intro Hlaws; split.
  - intros e He; rewrite problem_gen, problem_kill.
    exact (edge_support Hlaws e He).
  - intros n xs Hn Hb.
    rewrite problem_seeds in Hn; rewrite problem_boundary in Hb.
    injection Hb as <-.
    exact (exit_support Hlaws n Hn).
Qed.

(** Generated dense liveness rules imply the original finite-use specification. *)
Lemma problem_live_sound {N E V} (p : model N E V) n x :
  graph_wf (live_graph (vars p)) ->
  GenkillLeast.syntactic_live (problem p) x n -> live_at p n x.
Proof.
  intros Hwf Hlive.
  induction Hlive as [n xs Hn Hb Hx|e He Hx|e He Hkill Hlive IH].
  - rewrite problem_boundary in Hb; injection Hb as <-.
    apply live_exit; exact Hx.
  - rewrite problem_into; apply Cfg.edges_spec in He as [n [Hn He]].
    rewrite (out_source Hwf n e He).
    eapply live_edge_use; [exact He|].
    rewrite problem_gen in Hx; exact Hx.
  - rewrite problem_into; apply Cfg.edges_spec in He as [n [Hn He]].
    rewrite (out_source Hwf n e He).
    eapply live_edge_next; [exact He| |].
    + rewrite problem_kill in Hkill; exact Hkill.
    + rewrite problem_from in IH; exact IH.
Qed.

(** Original finite-use derivations at listed points satisfy the generated dense liveness rules. *)
Lemma problem_live_complete {N E V} (p : model N E V) n x :
  graph_wf (live_graph (vars p)) ->
  live_at p n x -> In n (Graph.nodes (live_graph (vars p))) ->
  GenkillLeast.syntactic_live (problem p) x n.
Proof.
  intros Hwf Hlive; induction Hlive as [n Hx|n e He Hx|n e He Hkill Hlive IH];
    intro Hn.
  - eapply GenkillLeast.live_seed.
    + rewrite problem_seeds; exact Hn.
    + apply problem_boundary.
    + exact Hx.
  - rewrite <- (out_source Hwf n e He), <- (problem_into p e).
    apply GenkillLeast.live_use.
    + apply Cfg.edges_spec; exists n; split; assumption.
    + rewrite problem_gen; exact Hx.
  - rewrite <- (out_source Hwf n e He), <- (problem_into p e).
    apply GenkillLeast.live_next.
    + apply Cfg.edges_spec; exists n; split; assumption.
    + rewrite problem_kill; exact Hkill.
    + rewrite problem_from; apply IH.
      exact (out_target_in Hwf n e Hn He).
Qed.

(** Every least local dense solution decides the original path specification at listed points. *)
Theorem problem_least_live_at {N E V} (p : model N E V) sigma :
  laws p ->
  least_solution (Analysis.lat (Bitvector.may_analysis (problem p)))
    (Analysis.system (Bitvector.may_analysis (problem p))) sigma ->
  forall n x, In n (Graph.nodes (live_graph (vars p))) ->
    (GenkillSound.member (sigma n) x <-> live_at p n x).
Proof.
  intros Hlaws Hleast n x Hn.
  rewrite (GenkillLeast.syntactic_live_least (problem p)
    (node_keys Hlaws) (edge_keys Hlaws) (value_keys Hlaws) sigma
    (graph_closed Hlaws) (problem_supported p Hlaws) eq_refl Hleast n x Hn).
  split.
  - apply problem_live_sound; exact (graph_closed Hlaws).
  - intro Hlive; exact (problem_live_complete p n x (graph_closed Hlaws) Hlive Hn).
Qed.

(** Any exact producer agrees with the same least dense solution at every reachable query. *)
Theorem oracle_dense {N E V} (p : model N E V) o sigma :
  laws p -> oracle_exact p o ->
  least_solution (Analysis.lat (Bitvector.may_analysis (problem p)))
    (Analysis.system (Bitvector.may_analysis (problem p))) sigma ->
  forall n x, reachable (live_graph (vars p)) n ->
    (live o n x = true <-> GenkillSound.member (sigma n) x).
Proof.
  intros Hlaws Hexact Hleast n x Hreachable.
  rewrite (Hexact n x Hreachable).
  symmetry; apply (problem_least_live_at p sigma Hlaws Hleast).
  exact (reachable_in_nodes _ _ (graph_closed Hlaws) Hreachable).
Qed.

(** A kill-free original path ends at an exit use or an outgoing edge use. *)
Theorem live_at_path {N E V} (p : model N E V) n x :
  graph_wf (live_graph (vars p)) ->
  (live_at p n x <->
    exists m es, path (live_graph (vars p)) n es m /\
      Forall (fun e => ~ In x (Vars.defs (vars p) e)) es /\
      point_use_at (vars p) m x).
Proof.
  apply syntactic_live_path_iff.
Qed.

(** A listed exact oracle also meets the reachable query contract on a closed graph. *)
Theorem oracle_all_reachable {N E V} (p : model N E V) o :
  graph_wf (live_graph (vars p)) -> oracle_all_exact p o -> oracle_exact p o.
Proof.
  intros Hwf Hexact n x Hreachable.
  apply Hexact.
  apply (reachable_in_nodes _ _ Hwf Hreachable).
Qed.

(** Two exact producers agree pointwise on the original reachable query domain. *)
Theorem oracle_agrees {N E V} (p : model N E V) a b :
  oracle_exact p a -> oracle_exact p b ->
  forall n x, reachable (live_graph (vars p)) n -> live a n x = live b n x.
Proof.
  intros Ha Hb n x Hreachable.
  pose proof (Ha n x Hreachable) as Hleft.
  pose proof (Hb n x Hreachable) as Hright.
  destruct (live a n x), (live b n x); intuition discriminate.
Qed.

End Live.
Import Live.
