(** * Scoped cycle members

    Proof-only member observations record the start ID and the IDs of actual labelled edge targets.
    For example, a self-loop's target observation is its starting ID.
    Builds on: GraphSearchSpec, GraphPrepared and GraphTarjanLow. *)

From Stdlib Require Import List PArith.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearchSpec
  GraphSccSpec GraphTarjanLow.
Import List.ListNotations.

Module HierCycles.

(** This proof-only listing contains the start and each successful original edge-target ID. *)
Definition points {V E} (p : Prepared.t V E) start es :=
  start :: Prepared.present (fun e => Prepared.id_of p (Graph.target (Prepared.graph p) e)) es.

(** An interpreted arc fixes the ID of its original labelled edge target. *)
Theorem arc_target {V E} (p : Prepared.t V E) u e v :
  Prepared.arc p u e v -> Prepared.id_of p (Graph.target (Prepared.graph p) e) = Some v.
Proof.
  intros [a [b [Ha [Hia [Hib [Hsource [Htarget Hedge]]]]]]].
  now rewrite Htarget.
Qed.

Local Lemma source_domain {V E} (p : Prepared.t V E) scope u es v :
  Search.scoped_path p scope u es v ->
    Prepared.valid_id p u /\ Scope.admits scope u = true.
Proof.
  intro Hpath. destruct Hpath; auto.
Qed.

(** Each listed edge splits its scoped path at the actual target ID of that occurrence. *)
Theorem split_edge {V E} (p : Prepared.t V E) scope u es z e :
  Search.scoped_path p scope u es z -> In e es ->
  exists v first last, es = first ++ last /\
    Search.scoped_path p scope u first v /\ Search.scoped_path p scope v last z /\
    Prepared.id_of p (Graph.target (Prepared.graph p) e) = Some v.
Proof.
  intro Hpath.
  induction Hpath as [v Hv Ha|u edge v es z Hu Ha Harc Htail IH]; intro Hin.
  - contradiction.
  - destruct Hin as [<-|Hin].
    + exists v, [edge], es. split; [reflexivity|]. split.
      * eapply Search.scoped_cons; [exact Hu|exact Ha|exact Harc|].
        destruct (source_domain p scope v es z Htail). now apply Search.scoped_nil.
      * split; [exact Htail|now apply (arc_target p u edge v)].
    + destruct (IH Hin) as [w [first [last [Hsplit [Hfirst [Hlast Htarget]]]]]].
      exists w, (edge :: first), last. split; [cbn [app]; now rewrite Hsplit|].
      split; [eapply Search.scoped_cons; eauto|exact (conj Hlast Htarget)].
Qed.

(** Every listed cycle point has the cycle's actual prefix and suffix paths. *)
Theorem point_paths {V E} (p : Prepared.t V E) scope v es x :
  Search.scoped_path p scope v es v -> In x (points p v es) ->
    exists first last, es = first ++ last /\
      Search.scoped_path p scope v first x /\ Search.scoped_path p scope x last v.
Proof.
  intros Hcycle [<-|Hin].
  - exists [], es. split; [reflexivity|]. split; [|exact Hcycle].
    destruct (source_domain p scope v es v Hcycle). now apply Search.scoped_nil.
  - apply Prepared.present_spec in Hin. destruct Hin as [e [Hin Htarget]].
    destruct (split_edge p scope v es v e Hcycle Hin)
      as [w [first [last [Hsplit [Hfirst [Hlast Hactual]]]]]].
    rewrite Htarget in Hactual. inversion Hactual; subst w.
    exists first, last. auto.
Qed.

(** Every cycle point shares the maximal scoped block containing the cycle's start. *)
Theorem points_in_block {V E} (p : Prepared.t V E) scope roots c v es :
  Scc.block p scope roots c -> In v c -> Search.scoped_path p scope v es v ->
    forall x, In x (points p v es) -> In x c.
Proof.
  intros [_ [_ [Hreach Hmutual]]] Hv Hcycle x Hx.
  destruct (point_paths p scope v es x Hcycle Hx) as [first [last [_ [Hfirst Hlast]]]].
  apply (proj2 (Hmutual v x Hv)). split.
  - destruct (Hreach v Hv) as [root [prefix [Hroot Hpath]]].
    exists root, (prefix ++ first). split; [exact Hroot|].
    eapply TarjanLow.path_append; eassumption.
  - split; [now exists first|now exists last].
Qed.

(** A nonempty cycle whose listed points are one ID contains an actual self arc at that ID. *)
Theorem singleton_cycle {V E} (p : Prepared.t V E) scope v es :
  Search.scoped_path p scope v es v -> es <> [] ->
  (forall x, In x (points p v es) -> x = v) ->
    exists e, Prepared.arc p v e v.
Proof.
  intros Hcycle Hnonempty Hpoints.
  destruct es as [|e rest]; [contradiction|].
  inversion Hcycle as [|u edge w tail z Hu Ha Harc Htail]; subst.
  assert (Hw : In w (points p v (e :: rest))).
  { right. apply Prepared.present_spec. exists e.
    split; [now left|now apply (arc_target p v e w)]. }
  specialize (Hpoints w Hw). subst w. now exists e.
Qed.

End HierCycles.
