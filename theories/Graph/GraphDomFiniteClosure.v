(** * Raw finite-closure transport

    Normalized graphs recognize the same finite closure as the compatibility reachability operation.
    For example, malformed original fuel and inconsistent interpreted arcs do not enter this proof.
    Builds on: GraphDomFiniteView and the public shared closure specification. *)

From Stdlib Require Import List Bool PArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphReach
  GraphFrontierSweep GraphDomFiniteView.
Import Cost.Notations.

Module DomFiniteClosure.

Local Lemma member_spec v xs : Reach.member v xs = true <-> In v xs.
Proof.
  unfold Reach.member. rewrite existsb_exists. split.
  - intros [x [Hx Heq]]. apply Pos.eqb_eq in Heq. now subst x.
  - intro Hv. exists v. split; [exact Hv|apply Pos.eqb_refl].
Qed.

(** Raw root filtering depends on the actual universe, supplied roots and admission Boolean alone. *)
Theorem raw_roots {V E} (p : Prepared.t V E) scope roots v :
  In v (Reach.roots_in p scope roots) <->
    In v (Reach.universe p) /\ In v roots /\ Scope.admits scope v = true.
Proof.
  unfold Reach.roots_in. rewrite filter_In, andb_true_iff, member_spec. tauto.
Qed.

(** Raw successor membership reads cached labelled occurrences without interpreted-graph assumptions. *)
Theorem raw_successors {V E} (p : Prepared.t V E) scope u v :
  In v (Reach.successors p scope u) <->
    Scope.admits scope v = true /\ In v (Reach.universe p) /\
      exists e, In (e, v) (Prepared.succ_edges p u).
Proof.
  unfold Reach.successors.
  rewrite filter_In, andb_true_iff, member_spec, in_map_iff. split.
  - intros [[ev [Heq Hin]] [Hallowed Hvalid]].
    destruct ev as [e target]. cbn [snd] in Heq. subst target.
    split; [exact Hallowed|]. split; [exact Hvalid|now exists e].
  - intros [Hallowed [Hvalid [e Hin]]]. split; [|auto].
    exists (e, v). auto.
Qed.

Local Lemma closure_simulate next roots next' roots' all :
  incl roots all ->
  (forall u v, In u all -> In v (next u) -> In v all) ->
  incl roots roots' ->
  (forall u v, In u all -> In v (next u) -> In v (next' u)) ->
  forall v, Reach.closure next roots v ->
    In v all /\ Reach.closure next' roots' v.
Proof.
  intros Hroots Hclosed Hstarts Hnext v Hreachable.
  induction Hreachable as [v Hv|u v Hreach [Hu IH] Hedge].
  - split; [now apply Hroots|apply Reach.root; now apply Hstarts].
  - split; [eapply Hclosed; eassumption|].
    apply (Reach.edge next' roots' u v IH). eapply Hnext; eassumption.
Qed.

(** Raw closure cannot leave the actual finite universe, even when the original record is malformed. *)
Theorem raw_support {V E} (p : Prepared.t V E) scope roots v :
  Reach.closure (Reach.successors p scope) (Reach.roots_in p scope roots) v ->
    In v (Reach.universe p).
Proof.
  intro Hreach. induction Hreach as [v Hv|u v Hreach IH Hedge].
  - apply raw_roots in Hv. exact (proj1 Hv).
  - apply raw_successors in Hedge. exact (proj1 (proj2 Hedge)).
Qed.

(** The compatibility result computes its finite closure on every computational input. *)
Theorem raw_set_closure {V E} (p : Prepared.t V E) scope roots v :
  FinSet.mem positive_encoding v (Reach.set p scope roots) = true <->
    Reach.closure (Reach.successors p scope) (Reach.roots_in p scope roots) v.
Proof.
  set (all := Reach.universe p).
  set (next := FrontierSweep.successors_c p scope all).
  set (starts := Reach.roots_in p scope roots).
  assert (Hroots : incl starts all).
  { intros u Hu. exact (proj1 (proj1 (raw_roots p scope roots u) Hu)). }
  assert (Hnext : forall u, incl (Cost.value (next u)) all).
  { intros u x Hx. unfold next, all in Hx.
    rewrite FrontierSweep.successors_value in Hx.
    exact (proj1 (proj2 (proj1 (raw_successors p scope u x) Hx))). }
  assert (Hvalue : Cost.value (FrontierSweep.reach_c p scope roots) =
    Cost.value (FrontierSweep.closure_c next all starts)).
  { unfold FrontierSweep.reach_c.
    rewrite Cost.value_bind, FrontierSweep.universe_value, Cost.value_bind,
      FrontierSweep.roots_value. reflexivity. }
  rewrite <- FrontierSweep.reach_value, Hvalue.
  rewrite (FrontierSweep.closure_exact next all starts
    (NoDup_nodup Pos.eq_dec _) Hroots Hnext).
  split; intro Hreach.
  - exact (proj2 (closure_simulate (fun u => Cost.value (next u)) starts
      (Reach.successors p scope) starts all Hroots
      ltac:(intros u x Hu Hx; exact (Hnext u x Hx))
      ltac:(intros u Hu; exact Hu)
      ltac:(intros u x Hu Hx; unfold next, all in Hx;
        now rewrite FrontierSweep.successors_value in Hx) v Hreach)).
  - exact (proj2 (closure_simulate (Reach.successors p scope) starts
      (fun u => Cost.value (next u)) starts all Hroots
      ltac:(intros u x Hu Hx; exact (proj1 (proj2
        (proj1 (raw_successors p scope u x) Hx))))
      ltac:(intros u Hu; exact Hu)
      ltac:(intros u x Hu Hx; unfold next, all;
        now rewrite FrontierSweep.successors_value) v Hreach)).
Qed.

Definition starts {V E} (p : Prepared.t V E) scope roots :=
  filter (Scope.admits scope) (Graph.entries (DomFiniteView.graph (DomFiniteView.view p roots))).

Definition next {V E} (p : Prepared.t V E) scope roots u :=
  filter (Scope.admits scope)
    (map snd (Graph.out (DomFiniteView.graph (DomFiniteView.view p roots)) u)).

(** Normalization keeps the raw admitted root membership despite canonical universe reordering. *)
Theorem starts_spec {V E} (p : Prepared.t V E) scope roots v :
  In v (starts p scope roots) <-> In v (Reach.roots_in p scope roots).
Proof.
  unfold starts. rewrite filter_In, DomFiniteView.graph_entries, raw_roots. tauto.
Qed.

(** Normalized adjacency agrees with raw admitted cached adjacency at every universe source. *)
Theorem next_spec {V E} (p : Prepared.t V E) scope roots u v :
  In v (next p scope roots u) <->
    In u (Reach.universe p) /\ In v (Reach.successors p scope u).
Proof.
  unfold next. rewrite filter_In, in_map_iff, raw_successors. split.
  - intros [[uv [Heq Hedge]] Hallowed]. apply DomFiniteView.graph_edge in Hedge.
    destruct Hedge as [Hsource [Hu [Htarget Hin]]].
    rewrite Heq in Htarget, Hin.
    split; [exact Hu|]. split; [exact Hallowed|]. now split.
  - intros [Hu [Hallowed [Hv [e Hin]]]]. split; [|exact Hallowed].
    exists (u, v). split; [reflexivity|]. apply DomFiniteView.graph_edge. cbn [fst snd].
    split; [reflexivity|]. split; [exact Hu|]. split; [exact Hv|now exists e].
Qed.

(** Normalization preserves finite closure for arbitrary raw data and every scope. *)
Theorem normalized_closure {V E} (p : Prepared.t V E) scope roots v :
  Reach.closure (next p scope roots) (starts p scope roots) v <->
    Reach.closure (Reach.successors p scope) (Reach.roots_in p scope roots) v.
Proof.
  assert (Hroots : incl (Reach.roots_in p scope roots) (Reach.universe p)).
  { intros u Hu. apply raw_roots in Hu. exact (proj1 Hu). }
  split; intro Hreach.
  - exact (proj2 (closure_simulate (next p scope roots) (starts p scope roots)
      (Reach.successors p scope) (Reach.roots_in p scope roots) (Reach.universe p)
      ltac:(intros u Hu; apply Hroots; now apply starts_spec in Hu)
      ltac:(intros u x Hu Hx; apply next_spec in Hx; destruct Hx as [_ Hx];
        apply raw_successors in Hx;
        exact (proj1 (proj2 Hx)))
      ltac:(intros u Hu; now apply starts_spec in Hu)
      ltac:(intros u x Hu Hx; apply next_spec in Hx; exact (proj2 Hx)) v Hreach)).
  - exact (proj2 (closure_simulate (Reach.successors p scope) (Reach.roots_in p scope roots)
      (next p scope roots) (starts p scope roots) (Reach.universe p) Hroots
      ltac:(intros u x Hu Hx; apply raw_successors in Hx; exact (proj1 (proj2 Hx)))
      ltac:(intros u Hu; now apply starts_spec)
      ltac:(intros u x Hu Hx; apply next_spec; now split) v Hreach)).
Qed.

End DomFiniteClosure.
