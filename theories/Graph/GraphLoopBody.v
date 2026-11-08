(** * Natural-loop bodies by a stopped reverse search

    A natural-loop query includes its header and searches predecessors without crossing that header.
    For example, the back edge from 3 to 2 yields the header 2 and the body vertex 3.
    Builds on: GraphPrepared, GraphSearch and GraphReach. *)

From Stdlib Require Import List PArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq BaseSet.
From Galois.Graph Require Import GraphPrepared GraphVisitor GraphSearchSpec GraphSearch
  GraphSearchExact GraphReach GraphTarjanLow.
Import List.ListNotations Cost.Notations.

Module LoopBody.

(** Natural-loop membership includes the header or an admitted forward path to the tail. *)
Definition natural_loop_spec {V E} (p : Prepared.t V E) header tail v :=
  v = header \/ exists es, Search.scoped_path p (Reach.blocked header) v es tail.

(** The query shares prepared predecessor indexes and uses the one search engine. *)
Definition natural_loop_c {V E} (p : Prepared.t V E) header tail :=
  let* blocked := FinSet.add_c positive_encoding header FinSet.empty in
  let* reversed := Prepared.reverse_c p [tail] in
  let* answer := SearchRun.run_c reversed (@Visitor.noop E unit)
    (Scope.Make blocked None) [tail] tt in
  FinSet.add_c positive_encoding header (Search.visited (fst answer)).

Definition natural_loop {V E} (p : Prepared.t V E) header tail :=
  Cost.value (natural_loop_c p header tail).

(** The value query adds its header to the actual stopped reverse-search result. *)
Theorem natural_loop_equation {V E} (p : Prepared.t V E) header tail :
  natural_loop p header tail =
    FinSet.add positive_encoding header (Search.visited
      (SearchRun.dfs (Prepared.reverse p [tail]) (Reach.blocked header) [tail])).
Proof.
  reflexivity.
Qed.

Local Lemma path_source {V E} (p : Prepared.t V E) scope u es v :
  Search.scoped_path p scope u es v ->
    Prepared.valid_id p u /\ Scope.admits scope u = true.
Proof.
  intro Hpath. destruct Hpath; auto.
Qed.

(** Scoped paths reverse their label order while retaining the same admitted-ID predicate. *)
Theorem path_reverse {V E} (p : Prepared.t V E) exits scope u es v :
  Prepared.ready p -> Search.scoped_path p scope u es v ->
    Search.scoped_path (Prepared.reverse p exits) scope v (rev es) u.
Proof.
  intros Hready Hpath.
  induction Hpath as [v Hv Ha|u e v es z Hu Ha Harc Htail IH].
  - apply Search.scoped_nil; [now apply Prepared.reverse_valid_id|exact Ha].
  - cbn [rev]. eapply TarjanLow.path_append; [exact IH|].
    destruct (path_source p scope v es z Htail) as [Hv Hallowed].
    eapply Search.scoped_cons.
    + now apply Prepared.reverse_valid_id.
    + exact Hallowed.
    + apply (proj2 (Prepared.reverse_arc p exits u e v Hready)). exact Harc.
    + apply Search.scoped_nil; [now apply Prepared.reverse_valid_id|exact Ha].
Qed.

(** Reversed-view scoped paths recover original forward paths without requiring valid exits. *)
Theorem path_unreverse {V E} (p : Prepared.t V E) exits scope u es v :
  Prepared.ready p -> Search.scoped_path (Prepared.reverse p exits) scope u es v ->
    Search.scoped_path p scope v (rev es) u.
Proof.
  intros Hready Hpath.
  induction Hpath as [v Hv Ha|u e v es z Hu Ha Harc Htail IH].
  - apply Search.scoped_nil; [now apply Prepared.reverse_valid_id in Hv|exact Ha].
  - cbn [rev]. eapply TarjanLow.path_append; [exact IH|].
    destruct (path_source (Prepared.reverse p exits) scope v es z Htail) as [Hv Hallowed].
    eapply Search.scoped_cons.
    + now apply Prepared.reverse_valid_id in Hv.
    + exact Hallowed.
    + apply (proj1 (Prepared.reverse_arc p exits v e u Hready)). exact Harc.
    + apply Search.scoped_nil; [now apply Prepared.reverse_valid_id in Hu|exact Ha].
Qed.

(** For a valid tail, the actual stopped reverse search computes precisely natural-loop membership. *)
Theorem natural_loop_exact {V E} (p : Prepared.t V E) header tail v :
  Prepared.ready p -> Prepared.valid_id p tail ->
  (FinSet.mem positive_encoding v (natural_loop p header tail) = true <->
    natural_loop_spec p header tail v).
Proof.
  intros Hready Htail.
  assert (Hreverse : Prepared.ready (Prepared.reverse p [tail])).
  { apply Prepared.reverse_ready; [exact Hready|].
    intros i [<-|Hfalse]; [exact Htail|contradiction]. }
  pose proof (SearchExact.dfs_exact (Prepared.reverse p [tail]) (Reach.blocked header)
    [tail] Hreverse) as Hexact.
  rewrite natural_loop_equation, FinSet.mem_add_raw, Bool.orb_true_iff.
  rewrite (eqb_true_iff positive_encoding positive_encoding_laws),
    (Search.visited_complete _ _ _ _ Hexact), (Search.pre_complete _ _ _ _ Hexact).
  unfold natural_loop_spec. split.
  - intros [Heq|[root [es [Hroot Hpath]]]]; [now left|].
    destruct Hroot as [<-|Hfalse]; [|contradiction].
    right. exists (rev es). exact (path_unreverse p [tail] _ tail es v Hready Hpath).
  - intros [Heq|[es Hpath]]; [now left|].
    right. exists tail, (rev es). split; [now left|].
    exact (path_reverse p [tail] _ v es tail Hready Hpath).
Qed.

End LoopBody.
