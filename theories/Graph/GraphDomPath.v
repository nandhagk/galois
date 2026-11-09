(** * Label-preserving discovery-rank paths

    Ranked paths are the discovered part of the actual virtual search graph.
    For example, an incoming edge from an unvisited source has no ranked path occurrence.
    Builds on: GraphDomTransport and the public exact scoped-search contract. *)

From Stdlib Require Import List PArith.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearchSpec GraphReach
  GraphDomSemi GraphDomTransport GraphDomVirtual.
Import List.ListNotations.

Module DomPath.

(** A ranked vertex denotes a present discovery number in the shared labelled search. *)
Definition vertex {V E} (shared : DomSemi.semi V E) rank :=
  exists v, Map.get positive_encoding v (Search.pre_num (DomSemi.search shared)) = Some rank.

(** Paths retain every original edge label and both actual ranked endpoints. *)
Inductive path {V E} (shared : DomSemi.semi V E) :
    positive -> list (E + V) -> positive -> Prop :=
  | RankedNil : forall v, vertex shared v -> path shared v [] v
  | RankedCons : forall u e v es z, vertex shared u ->
      DomSemi.ranked_arc shared u e v ->
      path shared v es z -> path shared u (e :: es) z.

Local Lemma start_vertex {V E} (shared : DomSemi.semi V E) u es v :
  path shared u es v -> vertex shared u.
Proof.
  intro Hpath. destruct Hpath; assumption.
Qed.

Local Lemma endpoint_valid {V E} (q : Prepared.t V E) scope u es v :
  Search.scoped_path q scope u es v -> Prepared.valid_id q v.
Proof.
  intro Hpath. induction Hpath; assumption.
Qed.

Local Lemma recorded {V E} (p : Prepared.t V E) u rank :
  Prepared.ready p ->
  Map.get positive_encoding u (Search.pre_num (DomSemi.search (DomSemi.compute p))) = Some rank ->
  In u (Search.preorder (DomSemi.search (DomSemi.compute p))).
Proof.
  intros Hready Hrank.
  apply (Search.pre_num_index _ _ _ _ (DomSemi.search_exact p Hready)) in Hrank.
  now apply nth_error_In in Hrank.
Qed.

Local Lemma recorded_valid {V E} (p : Prepared.t V E) u rank :
  Prepared.ready p ->
  Map.get positive_encoding u (Search.pre_num (DomSemi.search (DomSemi.compute p))) = Some rank ->
  Prepared.valid_id (DomSemi.prepared (DomSemi.compute p)) u.
Proof.
  intros Hready Hrank.
  pose proof (recorded p u rank Hready Hrank) as Hin.
  apply (Search.pre_complete _ _ _ _ (DomSemi.search_exact p Hready)) in Hin.
  destruct Hin as [root [es [Hroot Hpath]]]. now apply endpoint_valid in Hpath.
Qed.

Local Lemma scoped_snoc {V E} (q : Prepared.t V E) scope u es v e z :
  Search.scoped_path q scope u es v -> Prepared.arc q v e z ->
  Prepared.valid_id q z -> Scope.admits scope z = true ->
  Search.scoped_path q scope u (es ++ [e]) z.
Proof.
  intros Hpath Hedge Hz Hallowed.
  induction Hpath as [v Hv Hallow|u a v es target Hu Hallow Huv Htail IH]; cbn [app].
  - econstructor; [exact Hv|exact Hallow|exact Hedge|now constructor].
  - econstructor; [exact Hu|exact Hallow|exact Huv|now apply IH].
Qed.

(** Every actual successor of a discovered source has its own recorded discovery rank. *)
Theorem rank_after_arc {V E} (p : Prepared.t V E) u rank e v :
  Prepared.ready p ->
  Map.get positive_encoding u (Search.pre_num (DomSemi.search (DomSemi.compute p))) = Some rank ->
  Prepared.arc (DomSemi.prepared (DomSemi.compute p)) u e v ->
  exists next_rank,
    Map.get positive_encoding v (Search.pre_num (DomSemi.search (DomSemi.compute p))) =
      Some next_rank.
Proof.
  intros Hready Hrank Hedge.
  pose proof (DomSemi.search_exact p Hready) as Hsearch.
  pose proof (recorded p u rank Hready Hrank) as Hin.
  apply (Search.pre_complete _ _ _ _ Hsearch) in Hin.
  destruct Hin as [root [es [Hroot Hpath]]].
  assert (Hv : Prepared.valid_id (DomSemi.prepared (DomSemi.compute p)) v).
  { destruct Hedge as [a [b [Ha [Hi [Hj Hrest]]]]].
    pose proof (DomVirtual.virtual_ready p Hready) as Hq.
    rewrite <- DomSemi.prepared_equation in Hq.
    exists b. split; [|exact Hj].
    apply (Prepared.ids_domain _ (proj2 (proj2 Hq))).
    now exists v. }
  assert (Hreachable : Search.scoped_reachable (DomSemi.prepared (DomSemi.compute p))
    Reach.unrestricted (Prepared.entry_ids (DomSemi.prepared (DomSemi.compute p))) v).
  { exists root, (es ++ [e]). split; [exact Hroot|].
    apply scoped_snoc with (v := u).
    - exact Hpath.
    - exact Hedge.
    - exact Hv.
    - apply Reach.admits_unrestricted. }
  apply (Search.pre_complete _ _ _ _ Hsearch) in Hreachable.
  apply In_nth_error in Hreachable. destruct Hreachable as [i Hi].
  exists (Pos.of_succ_nat i).
  apply (Search.pre_num_index _ _ _ _ Hsearch).
  rewrite SuccNat2Pos.id_succ. exact Hi.
Qed.

(** Every discovered scoped path lifts with the same label sequence and actual endpoint ranks. *)
Theorem lift {V E} (p : Prepared.t V E) u es v source_rank target_rank :
  Prepared.ready p ->
  Search.scoped_path (DomSemi.prepared (DomSemi.compute p)) Reach.unrestricted u es v ->
  Map.get positive_encoding u (Search.pre_num (DomSemi.search (DomSemi.compute p))) =
    Some source_rank ->
  Map.get positive_encoding v (Search.pre_num (DomSemi.search (DomSemi.compute p))) =
    Some target_rank ->
  path (DomSemi.compute p) source_rank es target_rank.
Proof.
  intros Hready Hpath. revert source_rank target_rank.
  induction Hpath as [u Hu Hallowed|u e v es z Hu Hallowed Hedge Htail IH];
    intros source_rank target_rank Hsource Htarget.
  - assert (source_rank = target_rank) by congruence. subst target_rank.
    constructor. now exists u.
  - destruct (rank_after_arc p u source_rank e v Hready Hsource Hedge) as [middle Hmiddle].
    econstructor.
    + now exists u.
    + apply (proj2 (DomTransport.ranked_arc_spec p v middle e source_rank Hready Hmiddle)).
      exists u. auto.
    + exact (IH middle target_rank Hmiddle Htarget).
Qed.

(** Every ranked path lowers to the same labelled scoped path between its actual named IDs. *)
Theorem lower {V E} (p : Prepared.t V E) source_rank es target_rank :
  Prepared.ready p -> path (DomSemi.compute p) source_rank es target_rank ->
  forall u v,
  Map.get positive_encoding u (Search.pre_num (DomSemi.search (DomSemi.compute p))) =
    Some source_rank ->
  Map.get positive_encoding v (Search.pre_num (DomSemi.search (DomSemi.compute p))) =
    Some target_rank ->
  Search.scoped_path (DomSemi.prepared (DomSemi.compute p)) Reach.unrestricted u es v.
Proof.
  intros Hready Hpath.
  induction Hpath as [rank Hvertex|rank e middle es target Hvertex Hedge Htail IH];
    intros u v Hsource Htarget.
  - assert (u = v) by
      (exact (DomSemi.discovery_rank_injective p u v rank Hready Hsource Htarget)).
    subst v. constructor.
    + exact (recorded_valid p u rank Hready Hsource).
    + apply Reach.admits_unrestricted.
  - destruct (start_vertex _ _ _ _ Htail) as [next Hnext].
    apply (proj1 (DomTransport.ranked_arc_spec p next middle e rank Hready Hnext)) in Hedge.
    destruct Hedge as [source [Harc Hrank]].
    assert (source = u) by
      (exact (DomSemi.discovery_rank_injective p source u rank Hready Hrank Hsource)).
    subst source. econstructor.
    + exact (recorded_valid p u rank Hready Hsource).
    + apply Reach.admits_unrestricted.
    + exact Harc.
    + exact (IH next v Hnext Htarget).
Qed.

End DomPath.
