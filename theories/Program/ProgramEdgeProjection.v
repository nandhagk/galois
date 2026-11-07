(** * Ordered edge-occurrence projection

    Projection preserves graph paths while retaining parallel occurrences in the source.
    For example, two equal client edges receive distinct occurrence numbers.
    Builds on: GraphModel and CostMonad. *)

From Stdlib Require Import List Arith.
From Galois.Cost Require Import CostMonad.
From Galois.Graph Require Import GraphModel GraphDomSpec GraphFrontierSpec.
Import List.ListNotations Cost.Notations.

Module EdgeProjection.

(** A projection keeps nodes and every outgoing occurrence in its original order. *)
Record graph_laws {N E F} (g : Graph.t N E) (h : Graph.t N F) (f : E -> F) : Prop := {
  entries_agree : Graph.entries h = Graph.entries g;
  nodes_agree : Graph.nodes h = Graph.nodes g;
  out_agree : forall n, Graph.out h n = map f (Graph.out g n);
  source_agree : forall e, Graph.source h (f e) = Graph.source g e;
  target_agree : forall e, Graph.target h (f e) = Graph.target g e
}.
Arguments entries_agree {N E F g h f}.
Arguments nodes_agree {N E F g h f}.
Arguments out_agree {N E F g h f}.
Arguments source_agree {N E F g h f}.
Arguments target_agree {N E F g h f}.

(** Projecting a path retains its endpoints, edge order and multiplicity. *)
Theorem path_project {N E F} (g : Graph.t N E) (h : Graph.t N F) f s es t :
  graph_laws g h f -> path g s es t -> path h s (map f es) t.
Proof.
  intros Hgraph Hpath; induction Hpath as [n|e es t Hedge Hpath IH].
  - constructor.
  - cbn; rewrite <- (source_agree Hgraph e).
    constructor.
    + rewrite (source_agree Hgraph e), (out_agree Hgraph).
      apply in_map; exact Hedge.
    + rewrite (target_agree Hgraph e); exact IH.
Qed.

(** Every projected path lifts to actual source occurrences in the same order. *)
Theorem path_lift {N E F} (g : Graph.t N E) (h : Graph.t N F) f s es t :
  graph_laws g h f -> path h s es t ->
  exists lifted, path g s lifted t /\ map f lifted = es.
Proof.
  intros Hgraph Hpath; induction Hpath as [n|a es t Hedge Hpath IH].
  - exists []; split; [constructor|reflexivity].
  - destruct IH as [lifted [Hlifted Hmap]].
    rewrite (out_agree Hgraph) in Hedge.
    apply in_map_iff in Hedge; destruct Hedge as [e [Heq Hin]]; subst a.
    exists (e :: lifted); split.
    + rewrite (source_agree Hgraph) in Hin |- *.
      constructor; [exact Hin|].
      rewrite <- (target_agree Hgraph); exact Hlifted.
    + cbn; rewrite Hmap; reflexivity.
Qed.

(** Source edge dominance projects to client edge dominance without edge injectivity. *)
Theorem edge_dominance_project {N E F} (g : Graph.t N E) (h : Graph.t N F) f e n :
  graph_laws g h f -> edge_dominates g e n -> edge_dominates h (f e) n.
Proof.
  intros Hgraph Hdom s es Hentry Hpath.
  destruct (path_lift g h f s es n Hgraph Hpath) as [lifted [Hlifted Hmap]].
  rewrite <- Hmap; apply in_map; apply Hdom with s.
  - rewrite <- (entries_agree Hgraph); exact Hentry.
  - exact Hlifted.
Qed.

(** Node dominance is invariant under an ordered surjective edge projection. *)
Theorem dominance_agrees {N E F} (g : Graph.t N E) (h : Graph.t N F) f d n :
  graph_laws g h f -> (dominates g d n <-> dominates h d n).
Proof.
  intro Hgraph; split; intros Hdom s es Hentry Hpath.
  - destruct (path_lift g h f s es n Hgraph Hpath) as [lifted [Hlifted Hmap]].
    rewrite (entries_agree Hgraph) in Hentry.
    destruct (Hdom s lifted Hentry Hlifted) as [Heq|[e [Hin Htarget]]].
    + left; exact Heq.
    + right; exists (f e); split; [rewrite <- Hmap; apply in_map; exact Hin|].
      rewrite (target_agree Hgraph); exact Htarget.
  - pose proof (path_project g h f s es n Hgraph Hpath) as Hprojected.
    rewrite <- (entries_agree Hgraph) in Hentry.
    destruct (Hdom s (map f es) Hentry Hprojected) as [Heq|[e [Hin Htarget]]].
    + left; exact Heq.
    + apply in_map_iff in Hin; destruct Hin as [a [<- Hin]].
      right; exists a; split; [exact Hin|rewrite <- (target_agree Hgraph); exact Htarget].
Qed.

(** Enumerating outgoing cells charges each cell and numbers repeated values separately. *)
Fixpoint occurrences_c {E} (es : list E) (i : nat) : Cost.t (list (E * nat)) :=
  match es with
  | [] => Cost.ret []
  | e :: rest => Cost.step ;; Cost.map (cons (e, i)) (occurrences_c rest (S i))
  end.

Definition occurrences {E} (es : list E) i := Cost.value (occurrences_c es i).

(** Occurrence enumeration prepends the current value and advances the occurrence counter. *)
Theorem occurrences_equation {E} (es : list E) i :
  occurrences es i =
  match es with [] => [] | e :: rest => (e, i) :: occurrences rest (S i) end.
Proof.
  destruct es; reflexivity.
Qed.

(** Projecting occurrence values recovers the complete original list. *)
Theorem occurrences_project {E} (es : list E) i : map fst (occurrences es i) = es.
Proof.
  revert i; induction es as [|e es IH]; intro i; rewrite occurrences_equation;
    cbn [map fst]; rewrite ?IH; reflexivity.
Qed.

(** The occurrence counters form a contiguous sequence. *)
Theorem occurrences_positions {E} (es : list E) i :
  map snd (occurrences es i) = seq i (length es).
Proof.
  revert i; induction es as [|e es IH]; intro i; rewrite occurrences_equation;
    cbn [map snd seq length]; rewrite ?IH; reflexivity.
Qed.

(** Occurrence keys are distinct even when every client edge value is equal. *)
Theorem occurrences_nodup {E} (es : list E) i : NoDup (occurrences es i).
Proof.
  apply (NoDup_map_inv snd); rewrite occurrences_positions; apply seq_NoDup.
Qed.

(** The occurrence graph retains original callback charges and separately charges enumeration. *)
Definition occurrence_graph {N E} (g : Graph.t N E) : Graph.t N (E * nat) :=
  Graph.Make (Graph.entries g) (Graph.nodes g)
    (fun n => Cost.step ;; let* es := Graph.out_c g n in occurrences_c es 0)
    (fun ei => Cost.step ;; Graph.source_c g (fst ei))
    (fun ei => Cost.step ;; Graph.target_c g (fst ei)).

(** Outgoing occurrence callbacks enumerate exactly the original outgoing cells. *)
Theorem occurrence_out {N E} (g : Graph.t N E) n :
  Graph.out (occurrence_graph g) n = occurrences (Graph.out g n) 0.
Proof.
  change (Cost.value (Cost.step ;;
    Cost.bind (Graph.out_c g n) (fun es => occurrences_c es 0)) =
    occurrences (Graph.out g n) 0).
  rewrite !Cost.value_bind; reflexivity.
Qed.

(** Forgetting occurrence numbers gives an ordered projection onto the client graph. *)
Theorem occurrence_projection {N E} (g : Graph.t N E) :
  graph_laws (occurrence_graph g) g fst.
Proof.
  constructor; try reflexivity.
  intro n; rewrite occurrence_out, occurrences_project; reflexivity.
Qed.

(** Original graph well-formedness is retained by occurrence enumeration. *)
Theorem occurrence_graph_wf {N E} (g : Graph.t N E) :
  graph_wf g -> graph_wf (occurrence_graph g).
Proof.
  intro Hwf; constructor.
  - exact (nodes_nodup Hwf).
  - exact (entries_in Hwf).
  - intros n ei Hin; rewrite occurrence_out in Hin.
    apply (out_source Hwf n (fst ei)).
    rewrite <- (occurrences_project (Graph.out g n) 0); apply in_map; exact Hin.
  - intros n ei Hn Hin; rewrite occurrence_out in Hin.
    apply (out_target_in Hwf n (fst ei) Hn).
    rewrite <- (occurrences_project (Graph.out g n) 0); apply in_map; exact Hin.
Qed.

End EdgeProjection.
Import EdgeProjection.
