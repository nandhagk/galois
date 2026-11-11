(** * Semantic transport of the shared closed cuts

    Avoiding ranked paths correspond to the public blocked reachability of the actual virtual graph.
    For example, a cut query names its endpoints through that preparation's own interner.
    Builds on: GraphDomCutPath, GraphDomPath and the public Reach.avoiding theorem. *)

From Stdlib Require Import List Bool PArith.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearchSpec GraphReach GraphDomSpec
  GraphDomVirtual GraphDomSemi GraphDomTransport GraphDomPath GraphDomDfs
  GraphDomSemiExact GraphDomCut GraphDomCutPath.
Import List.ListNotations.

Module DomCutTransport.

Local Lemma admits_blocked deleted v :
  Scope.admits (Reach.blocked deleted) v = true <-> v <> deleted.
Proof.
  rewrite Scope.admits_equation, Reach.blocked_equation.
  cbn [Scope.blocked Scope.within].
  rewrite andb_true_r, negb_true_iff, <- not_true_iff_false.
  rewrite FinSet.mem_add by apply FinSet.wf_empty.
  rewrite FinSet.mem_empty, orb_false_r, (eqb_true_iff _ positive_encoding_laws).
  reflexivity.
Qed.

Local Lemma lift_blocked {V E} (p : Prepared.t V E) deleted rank_deleted u es v :
  Prepared.ready p ->
  Map.get positive_encoding deleted (Search.pre_num (DomSemi.search (DomSemi.compute p))) =
    Some rank_deleted ->
  Search.scoped_path (DomSemi.prepared (DomSemi.compute p)) (Reach.blocked deleted) u es v ->
  forall source target,
  Map.get positive_encoding u (Search.pre_num (DomSemi.search (DomSemi.compute p))) = Some source ->
  Map.get positive_encoding v (Search.pre_num (DomSemi.search (DomSemi.compute p))) = Some target ->
  source <> rank_deleted /\
    DomSemiExact.bounded_path (DomSemi.compute p) (fun x => x <> rank_deleted) source es target.
Proof.
  intros Hready Hdeleted Hpath.
  induction Hpath as [u Hu Hallow|u e v es z Hu Hallow Hedge Htail IH];
    intros source target Hsource Htarget.
  - apply admits_blocked in Hallow.
    assert (Hfree : source <> rank_deleted).
    { intro Heq. subst source. apply Hallow.
      exact (DomSemi.discovery_rank_injective p u deleted rank_deleted Hready Hsource Hdeleted). }
    split; [exact Hfree|]. assert (source = target) by congruence. subst target.
    constructor. now exists u.
  - apply admits_blocked in Hallow.
    assert (Hfree : source <> rank_deleted).
    { intro Heq. subst source. apply Hallow.
      exact (DomSemi.discovery_rank_injective p u deleted rank_deleted Hready Hsource Hdeleted). }
    destruct (DomPath.rank_after_arc p u source e v Hready Hsource Hedge) as [middle Hmiddle].
    destruct (IH middle target Hmiddle Htarget) as [Hmiddle_free Hrest].
    split; [exact Hfree|]. econstructor.
    + now exists u.
    + apply (proj2 (DomTransport.ranked_arc_spec p v middle e source Hready Hmiddle)).
      exists u. auto.
    + exact Hmiddle_free.
    + exact Hrest.
Qed.

Local Lemma scoped_start_valid {V E} (q : Prepared.t V E) scope u es v :
  Search.scoped_path q scope u es v -> Prepared.valid_id q u.
Proof.
  intro Hpath. destruct Hpath; assumption.
Qed.

Local Lemma lower_blocked {V E} (p : Prepared.t V E) deleted rank_deleted source es target :
  Prepared.ready p ->
  Map.get positive_encoding deleted (Search.pre_num (DomSemi.search (DomSemi.compute p))) =
    Some rank_deleted ->
  DomSemiExact.bounded_path (DomSemi.compute p) (fun x => x <> rank_deleted) source es target ->
  source <> rank_deleted ->
  forall u v,
  Map.get positive_encoding u (Search.pre_num (DomSemi.search (DomSemi.compute p))) = Some source ->
  Map.get positive_encoding v (Search.pre_num (DomSemi.search (DomSemi.compute p))) = Some target ->
  Search.scoped_path (DomSemi.prepared (DomSemi.compute p)) (Reach.blocked deleted) u es v.
Proof.
  intros Hready Hdeleted Hpath.
  induction Hpath as [source Hvertex|source e middle es target Hvertex Hedge Hmiddle_free Htail IH];
    intros Hsource_free u v Hsource Htarget.
  - assert (u = v) by
      (exact (DomSemi.discovery_rank_injective p u v source Hready Hsource Htarget)).
    subst v. constructor.
    + apply (scoped_start_valid _ Reach.unrestricted u [] u).
      exact (DomPath.lower p source [] source Hready
        (DomPath.RankedNil _ source Hvertex) u u Hsource Hsource).
    + apply admits_blocked. congruence.
  - destruct (DomSemiExact.bounded_start _ _ _ _ _ Htail) as [next Hnext].
    apply (proj1 (DomTransport.ranked_arc_spec p next middle e source Hready Hnext)) in Hedge.
    destruct Hedge as [raw_source [Harc Hrank]].
    assert (raw_source = u) by
      (exact (DomSemi.discovery_rank_injective p raw_source u source Hready Hrank Hsource)).
    subst raw_source. econstructor.
    + destruct Harc as [a [b [Ha [Hi Hrest]]]]. now exists a.
    + apply admits_blocked. congruence.
    + exact Harc.
    + exact (IH Hmiddle_free next v Hnext Htarget).
Qed.

Local Lemma root_entry {V E} (p : Prepared.t V E) root :
  Prepared.ready p ->
  Prepared.id_of (DomSemi.prepared (DomSemi.compute p)) None = Some root ->
  In root (Prepared.entry_ids (DomSemi.prepared (DomSemi.compute p))).
Proof.
  intros Hready Hroot.
  pose proof (DomVirtual.virtual_ready p Hready) as Hq.
  rewrite <- DomSemi.prepared_equation in Hq.
  apply (Prepared.entry_ids_spec _ root (proj2 (proj2 Hq))). exists None.
  split; [|exact Hroot].
  rewrite DomSemi.prepared_equation, DomVirtual.prepared_graph, DomVirtual.graph_equation.
  now left.
Qed.

(** Avoiding the actual discovery rank is equivalent to blocking that same recorded virtual ID. *)
Theorem no_avoiding_iff {V E} (p : Prepared.t V E) deleted target rank_deleted rank_target :
  Prepared.ready p ->
  Map.get positive_encoding deleted (Search.pre_num (DomSemi.search (DomSemi.compute p))) =
    Some rank_deleted ->
  Map.get positive_encoding target (Search.pre_num (DomSemi.search (DomSemi.compute p))) =
    Some rank_target ->
  (DomCutPath.no_avoiding p rank_deleted rank_target <->
    ~ Search.scoped_reachable (DomSemi.prepared (DomSemi.compute p)) (Reach.blocked deleted)
      (Prepared.entry_ids (DomSemi.prepared (DomSemi.compute p))) target).
Proof.
  intros Hready Hdeleted Htarget. split.
  - intros Hno [root [es [Hentry Hpath]]].
    pose proof (DomDfs.entry_id_unique p root Hready Hentry) as Hroot.
    pose proof (DomDfs.root_rank p root Hready Hroot) as Hrank.
    destruct (lift_blocked p deleted rank_deleted root es target Hready Hdeleted Hpath
      1%positive rank_target Hrank Htarget) as [Hstart Hbounded].
    exact (Hno es Hbounded Hstart).
  - intros Hno es Hpath Hstart. apply Hno.
    pose proof (DomVirtual.root_id p Hready) as Hroot.
    rewrite <- DomSemi.prepared_equation in Hroot.
    set (root := Pos.of_succ_nat (length (Graph.nodes (Prepared.graph p)))) in *.
    pose proof (DomDfs.root_rank p root Hready Hroot) as Hrank.
    exists root, es. split.
    + exact (root_entry p root Hready Hroot).
    + exact (lower_blocked p deleted rank_deleted 1%positive es rank_target Hready
        Hdeleted Hpath Hstart root target Hrank Htarget).
Qed.

(** Closed cuts express the fixed semantic dominance predicate at the actual named discovered endpoints. *)
Theorem cut_dominates {V E} (p : Prepared.t V E) d n deleted target rank_deleted rank_target :
  Prepared.ready p ->
  Prepared.id_of (DomSemi.prepared (DomSemi.compute p)) d = Some deleted ->
  Prepared.id_of (DomSemi.prepared (DomSemi.compute p)) n = Some target ->
  Map.get positive_encoding deleted (Search.pre_num (DomSemi.search (DomSemi.compute p))) =
    Some rank_deleted ->
  Map.get positive_encoding target (Search.pre_num (DomSemi.search (DomSemi.compute p))) =
    Some rank_target ->
  (DomCut.cut p rank_deleted rank_target <->
    dominates (Prepared.graph (DomSemi.prepared (DomSemi.compute p))) d n).
Proof.
  intros Hready Hd Hn Hdeleted Htarget.
  pose proof (DomVirtual.virtual_ready p Hready) as Hq.
  rewrite <- DomSemi.prepared_equation in Hq.
  rewrite (DomCutPath.cut_exact p rank_deleted rank_target Hready ltac:(now exists target)).
  rewrite (no_avoiding_iff p deleted target rank_deleted rank_target Hready Hdeleted Htarget).
  rewrite (Reach.avoiding _ d n deleted target Hq Hd Hn), <- not_true_iff_false.
  now rewrite (Reach.exact _ _ _ target Hq).
Qed.

Local Lemma scoped_end_valid {V E} (q : Prepared.t V E) scope u es v :
  Search.scoped_path q scope u es v -> Prepared.valid_id q v.
Proof.
  intro Hpath. induction Hpath; assumption.
Qed.

(** Every recorded discovery rank has a name in the same actual virtual preparation. *)
Theorem vertex_name {V E} (p : Prepared.t V E) rank :
  Prepared.ready p -> DomPath.vertex (DomSemi.compute p) rank ->
  exists name id, Prepared.id_of (DomSemi.prepared (DomSemi.compute p)) name = Some id /\
    Map.get positive_encoding id (Search.pre_num (DomSemi.search (DomSemi.compute p))) = Some rank.
Proof.
  intros Hready [id Hrank].
  pose proof (DomSemi.search_exact p Hready) as Hsearch.
  pose proof Hrank as Hin. apply (Search.pre_num_index _ _ _ _ Hsearch) in Hin.
  apply nth_error_In in Hin. apply (Search.pre_complete _ _ _ _ Hsearch) in Hin.
  destruct Hin as [root [es [Hentry Hpath]]].
  destruct (scoped_end_valid _ _ _ _ _ Hpath) as [name [Hnode Hname]].
  exists name, id. auto.
Qed.

(** A named recorded vertex is semantically reachable in the actual virtual graph. *)
Theorem recorded_reachable {V E} (p : Prepared.t V E) name id rank :
  Prepared.ready p ->
  Prepared.id_of (DomSemi.prepared (DomSemi.compute p)) name = Some id ->
  Map.get positive_encoding id (Search.pre_num (DomSemi.search (DomSemi.compute p))) = Some rank ->
  reachable (Prepared.graph (DomSemi.prepared (DomSemi.compute p))) name.
Proof.
  intros Hready Hname Hrank.
  pose proof (DomVirtual.virtual_ready p Hready) as Hq.
  rewrite <- DomSemi.prepared_equation in Hq.
  apply (proj1 (Reach.entries_exact _ name id Hq Hname)).
  apply (proj2 (Reach.exact _ _ _ id Hq)).
  apply (Search.pre_complete _ _ _ _ (DomSemi.search_exact p Hready)).
  apply (Search.pre_num_index _ _ _ _ (DomSemi.search_exact p Hready)) in Hrank.
  now apply nth_error_In in Hrank.
Qed.

(** Semantic reachability supplies actual naming and discovery records without a rank default. *)
Theorem reachable_rank {V E} (p : Prepared.t V E) name :
  Prepared.ready p ->
  reachable (Prepared.graph (DomSemi.prepared (DomSemi.compute p))) name ->
  exists id rank, Prepared.id_of (DomSemi.prepared (DomSemi.compute p)) name = Some id /\
    Map.get positive_encoding id (Search.pre_num (DomSemi.search (DomSemi.compute p))) = Some rank.
Proof.
  intros Hready Hreach.
  pose proof (DomVirtual.virtual_ready p Hready) as Hq.
  rewrite <- DomSemi.prepared_equation in Hq.
  destruct (proj1 (Prepared.ids_domain _ (proj2 (proj2 Hq)) name)
    (reachable_in_nodes _ _ (proj1 Hq) Hreach)) as [id Hname].
  apply (proj2 (Reach.entries_exact _ name id Hq Hname)) in Hreach.
  apply (proj1 (Reach.exact _ _ _ id Hq)) in Hreach.
  apply (Search.pre_complete _ _ _ _ (DomSemi.search_exact p Hready)) in Hreach.
  apply In_nth_error in Hreach. destruct Hreach as [index Hindex].
  exists id, (Pos.of_succ_nat index). split; [exact Hname|].
  apply (Search.pre_num_index _ _ _ _ (DomSemi.search_exact p Hready)).
  rewrite SuccNat2Pos.id_succ. exact Hindex.
Qed.

(** Equal actual discovery ranks identify their original virtual names under readiness. *)
Theorem named_rank_injective {V E} (p : Prepared.t V E) a b i j rank :
  Prepared.ready p ->
  Prepared.id_of (DomSemi.prepared (DomSemi.compute p)) a = Some i ->
  Prepared.id_of (DomSemi.prepared (DomSemi.compute p)) b = Some j ->
  Map.get positive_encoding i (Search.pre_num (DomSemi.search (DomSemi.compute p))) = Some rank ->
  Map.get positive_encoding j (Search.pre_num (DomSemi.search (DomSemi.compute p))) = Some rank ->
  a = b.
Proof.
  intros Hready Ha Hb Hi Hj.
  pose proof (DomSemi.discovery_rank_injective p i j rank Hready Hi Hj) as Heq. subst j.
  pose proof (DomVirtual.virtual_ready p Hready) as Hq.
  rewrite <- DomSemi.prepared_equation in Hq.
  pose proof (Prepared.name_of_id_of _ a i (proj2 (proj2 Hq)) Ha).
  pose proof (Prepared.name_of_id_of _ b i (proj2 (proj2 Hq)) Hb). congruence.
Qed.

End DomCutTransport.
