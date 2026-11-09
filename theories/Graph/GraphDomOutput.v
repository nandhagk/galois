(** * Sentinel-free exactness of actual dominance output

    The shared inverse transports the proved ranked LT parents into original reachable IDs.
    For example, the virtual root has no inverse binding and its children become forest roots.
    Builds on: GraphDomLtProof, GraphDomTransport and actual parent-forest numbering. *)

From Stdlib Require Import List PArith.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphSearchSpec GraphDomSpec
  GraphDomVirtual GraphDomSemi GraphDomErase GraphDomTransport GraphDomPath GraphDomDfs
  GraphDomCutTransport GraphDomLt GraphDomLtProof GraphDomNcaProof GraphDomNumber GraphReach.
Import List.ListNotations.

Module DomOutput.

(** This observer uses exactly the actual discovered inverse and output order of tree construction. *)
Definition live {V E} (p : Prepared.t V E) :=
  Prepared.present (fun rank => Map.get positive_encoding rank
    (DomSemi.real_ids (DomSemi.ranked (DomSemi.compute p))))
    (rev (DomSemi.reverse_order (DomSemi.ranked (DomSemi.compute p)))).

(** This observer erases the same actual ranked LT map through the same shared inverse. *)
Definition parents {V E} (p : Prepared.t V E) :=
  DomSemi.erase (DomSemi.compute p) (DomLt.finish (DomSemi.compute p)).

Local Lemma virtual_ready {V E} (p : Prepared.t V E) :
  Prepared.ready p -> Prepared.ready (DomSemi.prepared (DomSemi.compute p)).
Proof.
  intro Hready. rewrite DomSemi.prepared_equation. now apply DomVirtual.virtual_ready.
Qed.

Local Lemma virtual_graph {V E} (p : Prepared.t V E) :
  Prepared.graph (DomSemi.prepared (DomSemi.compute p)) =
    DomVirtual.graph (Prepared.node_enc p) (Prepared.graph p).
Proof.
  rewrite DomSemi.prepared_equation. apply DomVirtual.prepared_graph.
Qed.

(** Successful inverse lookup identifies the same real name in both actual prepared tables. *)
Theorem inverse_real {V E} (p : Prepared.t V E) rank original :
  Prepared.ready p ->
  (Map.get positive_encoding rank (DomSemi.real_ids (DomSemi.ranked (DomSemi.compute p))) =
    Some original <->
    exists name raw, Prepared.id_of p name = Some original /\
      Prepared.id_of (DomSemi.prepared (DomSemi.compute p)) (Some name) = Some raw /\
      Map.get positive_encoding raw (Search.pre_num (DomSemi.search (DomSemi.compute p))) =
        Some rank).
Proof.
  intro Hready. pose proof (proj2 (proj2 (virtual_ready p Hready))) as Hq.
  split.
  - intro Hget. apply DomTransport.inverse_sound in Hget.
    destruct Hget as [raw [Hin [Hrank Hreal]]].
    apply DomErase.real_id_spec in Hreal. destruct Hreal as [name [Hname Horiginal]].
    exists name, raw. split; [exact Horiginal|]. split; [|exact Hrank].
    exact (Prepared.id_of_name_of _ raw (Some name) Hq Hname).
  - intros [name [raw [Horiginal [Hname Hrank]]]].
    apply (DomTransport.inverse_complete p raw rank original Hready).
    + pose proof Hrank as Hin.
      apply (Search.pre_num_index _ _ _ _ (DomSemi.search_exact p Hready)) in Hin.
      now apply nth_error_In in Hin.
    + exact Hrank.
    + apply DomErase.real_id_spec. exists name. split; [|exact Horiginal].
      exact (Prepared.name_of_id_of _ (Some name) raw Hq Hname).
Qed.

Local Lemma real_reachable {V E} (p : Prepared.t V E) name raw rank :
  Prepared.ready p ->
  Prepared.id_of (DomSemi.prepared (DomSemi.compute p)) (Some name) = Some raw ->
  Map.get positive_encoding raw (Search.pre_num (DomSemi.search (DomSemi.compute p))) = Some rank ->
  reachable (Prepared.graph p) name.
Proof.
  intros Hready Hname Hrank.
  pose proof (DomCutTransport.recorded_reachable p (Some name) raw rank Hready Hname Hrank) as Hr.
  rewrite virtual_graph in Hr.
  apply (proj1 (DomVirtual.virtual_reachable_iff _ _ name
    (Prepared.encoding_valid p (proj2 (proj2 Hready))))). exact Hr.
Qed.

(** Every reachable original ID has a successful inverse at its actual discovered virtual rank. *)
Theorem reachable_inverse {V E} (p : Prepared.t V E) name original :
  Prepared.ready p -> reachable (Prepared.graph p) name -> Prepared.id_of p name = Some original ->
  exists rank raw,
    Map.get positive_encoding rank (DomSemi.real_ids (DomSemi.ranked (DomSemi.compute p))) =
      Some original /\
    Prepared.id_of (DomSemi.prepared (DomSemi.compute p)) (Some name) = Some raw /\
    Map.get positive_encoding raw (Search.pre_num (DomSemi.search (DomSemi.compute p))) = Some rank.
Proof.
  intros Hready Hreach Horiginal.
  assert (Hvirtual : reachable (Prepared.graph (DomSemi.prepared (DomSemi.compute p))) (Some name)).
  { rewrite virtual_graph. apply (proj2 (DomVirtual.virtual_reachable_iff _ _ name
      (Prepared.encoding_valid p (proj2 (proj2 Hready))))). exact Hreach. }
  destruct (DomCutTransport.reachable_rank p (Some name) Hready Hvirtual)
    as [raw [rank [Hname Hrank]]].
  exists rank, raw. split; [|auto].
  apply (proj2 (inverse_real p rank original Hready)). exists name, raw. auto.
Qed.

(** The fresh virtual root has no original-ID binding in the actual shared inverse. *)
Theorem root_inverse_none {V E} (p : Prepared.t V E) :
  Prepared.ready p ->
  Map.get positive_encoding 1%positive
    (DomSemi.real_ids (DomSemi.ranked (DomSemi.compute p))) = None.
Proof.
  intro Hready. destruct (Map.get positive_encoding 1%positive
    (DomSemi.real_ids (DomSemi.ranked (DomSemi.compute p)))) as [original|] eqn:Hget; [|reflexivity].
  apply (inverse_real p 1%positive original Hready) in Hget.
  destruct Hget as [name [raw [Horiginal [Hname Hrank]]]].
  pose proof (DomVirtual.root_id p Hready) as Hroot.
  rewrite <- DomSemi.prepared_equation in Hroot.
  pose proof (DomDfs.root_rank p _ Hready Hroot) as Hroot_rank.
  pose proof (DomCutTransport.named_rank_injective p (Some name) None raw _ 1%positive
    Hready Hname Hroot Hrank Hroot_rank) as Hfalse. discriminate.
Qed.

(** The actual output live list contains precisely all reachable original named IDs. *)
Theorem live_spec {V E} (p : Prepared.t V E) original :
  Prepared.ready p ->
  (In original (live p) <->
    exists name, Prepared.id_of p name = Some original /\ reachable (Prepared.graph p) name).
Proof.
  intro Hready. unfold live. rewrite Prepared.present_spec. split.
  - intros [rank [Hin Hget]]. apply (inverse_real p rank original Hready) in Hget.
    destruct Hget as [name [raw [Horiginal [Hname Hrank]]]].
    exists name. split; [exact Horiginal|exact (real_reachable p name raw rank Hready Hname Hrank)].
  - intros [name [Horiginal Hreach]].
    destruct (reachable_inverse p name original Hready Hreach Horiginal)
      as [rank [raw [Hinverse [Hname Hrank]]]].
    exists rank. split; [|exact Hinverse].
    apply (proj1 (in_rev _ _)). apply (proj1 (DomDfs.vertex_member p rank Hready)).
    now exists raw.
Qed.

(** Output live IDs are duplicate free because actual discovery ranks and successful inverses are injective. *)
Theorem live_nodup {V E} (p : Prepared.t V E) :
  Prepared.ready p -> NoDup (live p).
Proof.
  intro Hready. unfold live. apply Prepared.present_nodup.
  - apply NoDup_rev. exact (DomDfs.settlement_nodup p Hready).
  - exact (DomTransport.inverse_injective p Hready).
Qed.

(** Every erased binding has reachable original endpoints and is a semantic immediate dominator. *)
Theorem parent_sound {V E} (p : Prepared.t V E) v u :
  Prepared.ready p -> Map.get positive_encoding v (parents p) = Some u ->
  exists n d, Prepared.id_of p n = Some v /\ Prepared.id_of p d = Some u /\
    reachable (Prepared.graph p) n /\ reachable (Prepared.graph p) d /\
    immediately_dominates (Prepared.graph p) d n.
Proof.
  intros Hready Hget. apply (DomTransport.erase_get p _ v u Hready (DomLt.finish_wf _)) in Hget.
  destruct Hget as [i [j [Hparent [Hi Hj]]]].
  apply (inverse_real p i v Hready) in Hi. apply (inverse_real p j u Hready) in Hj.
  destruct Hi as [n [raw_n [Hn [Hraw_n Hrank_n]]]].
  destruct Hj as [d [raw_d [Hd [Hraw_d Hrank_d]]]].
  exists n, d. split; [exact Hn|]. split; [exact Hd|].
  split; [exact (real_reachable p n raw_n i Hready Hraw_n Hrank_n)|].
  split; [exact (real_reachable p d raw_d j Hready Hraw_d Hrank_d)|].
  apply (proj2 (DomVirtual.virtual_immediate_iff _ _ d n
    (Prepared.encoding_valid p (proj2 (proj2 Hready))))).
  pose proof (proj1 (DomLtProof.finish_immediate p (Some d) (Some n) raw_d raw_n j i
    Hready Hraw_d Hraw_n Hrank_d Hrank_n) Hparent) as Himmediate.
  now rewrite virtual_graph in Himmediate.
Qed.

Local Lemma real_cannot_dominate_root {V E} (p : Prepared.t V E) d :
  ~ dominates (Prepared.graph (DomSemi.prepared (DomSemi.compute p))) (Some d) None.
Proof.
  rewrite virtual_graph. intros Hdom.
  assert (Hentry : In None
    (Graph.entries (DomVirtual.graph (Prepared.node_enc p) (Prepared.graph p)))).
  { rewrite DomVirtual.graph_equation. now left. }
  destruct (Hdom None [] Hentry (path_nil None)) as [Hfalse|[edge [Hin Htarget]]];
    [discriminate|contradiction].
Qed.

(** A strict real dominator forces the actual ranked parent to survive sentinel erasure. *)
Theorem strict_has_parent {V E} (p : Prepared.t V E) n v d :
  Prepared.ready p -> reachable (Prepared.graph p) n -> Prepared.id_of p n = Some v ->
  strictly_dominates (Prepared.graph p) d n ->
  exists u, Map.get positive_encoding v (parents p) = Some u.
Proof.
  intros Hready Hreach Hn [Hdom Hne].
  destruct (reachable_inverse p n v Hready Hreach Hn) as [i [raw_n [Hi [Hraw_n Hrank_n]]]].
  assert (Hnonroot : i <> 1%positive).
  { intro Heq. subst i. rewrite (root_inverse_none p Hready) in Hi. discriminate. }
  destruct (proj2 (DomLtProof.finish_parents p Hready) i ltac:(now exists raw_n) Hnonroot)
    as [j Hparent].
  pose proof (proj1 (proj2 (proj2 (proj1 (DomLtProof.finish_parents p Hready) i j Hparent)))) as Hj.
  destruct (DomCutTransport.vertex_name p j Hready Hj) as [[parent|] [raw_parent [Hname Hrank]]].
  - pose proof (real_reachable p parent raw_parent j Hready Hname Hrank) as Hparent_reach.
    destruct (proj1 (Prepared.ids_domain p (proj2 (proj2 Hready)) parent)
      (reachable_in_nodes _ _ (proj1 Hready) Hparent_reach)) as [u Hu].
    exists u. apply (DomTransport.erase_get p _ v u Hready (DomLt.finish_wf _)).
    exists i, j. split; [exact Hparent|]. split; [exact Hi|].
    apply (proj2 (inverse_real p j u Hready)). exists parent, raw_parent. auto.
  - pose proof (proj1 (DomLtProof.finish_immediate p None (Some n) raw_parent raw_n j i
      Hready Hname Hraw_n Hrank Hrank_n) Hparent) as Himmediate.
    assert (Hstrict : strictly_dominates
      (Prepared.graph (DomSemi.prepared (DomSemi.compute p))) (Some d) (Some n)).
    { split.
      - rewrite virtual_graph. apply (proj1 (DomVirtual.virtual_dominates_iff _ _ d n
          (Prepared.encoding_valid p (proj2 (proj2 Hready))))). exact Hdom.
      - congruence. }
    exact (False_rect _ (real_cannot_dominate_root p d (proj2 Himmediate (Some d) Hstrict))).
Qed.

(** Erased parentlessness is equivalent to absence of every strict dominator for reachable real children. *)
Theorem parent_complete {V E} (p : Prepared.t V E) n v :
  Prepared.ready p -> reachable (Prepared.graph p) n -> Prepared.id_of p n = Some v ->
  (Map.get positive_encoding v (parents p) = None <->
    forall d, ~ strictly_dominates (Prepared.graph p) d n).
Proof.
  intros Hready Hreach Hn. split.
  - intros Hnone d Hstrict.
    destruct (strict_has_parent p n v d Hready Hreach Hn Hstrict) as [u Hu]. congruence.
  - intros Hnone. destruct (Map.get positive_encoding v (parents p)) as [u|] eqn:Hget;
      [|reflexivity].
    destruct (parent_sound p v u Hready Hget) as [child [d [Hchild [Hd [Hr [Hdr Himm]]]]]].
    pose proof (Prepared.name_of_id_of p n v (proj2 (proj2 Hready)) Hn).
    pose proof (Prepared.name_of_id_of p child v (proj2 (proj2 Hready)) Hchild).
    assert (child = n) by congruence. subst child.
    exact (False_rect _ (Hnone d (proj1 Himm))).
Qed.

(** The actual shared inverse preserves the strict parent forest's well-foundedness. *)
Theorem parent_finite {V E} (p : Prepared.t V E) :
  Prepared.ready p ->
  well_founded (fun u v => Map.get positive_encoding v (parents p) = Some u).
Proof.
  intro Hready. apply DomErase.with_finite.
  - exact (DomTransport.inverse_injective p Hready).
  - apply DomLt.finish_wf.
  - rewrite DomLtProof.finish_agrees by exact Hready. now apply DomNcaProof.finish_well_founded.
Qed.

(** Actual shared erasure followed by actual forest annotation satisfies the unchanged public tree specification. *)
Theorem numbered_exact {V E} (p : Prepared.t V E) :
  Prepared.ready p -> Dom.exact p (DomNumber.of_parents (live p) (parents p)).
Proof.
  intro Hready. pose proof (proj2 (proj2 Hready)) as Hp.
  assert (Hmap : Map.wf positive_encoding (parents p)).
  { exact (DomSemi.erase_wf (DomSemi.compute p) (DomLt.finish (DomSemi.compute p))). }
  assert (Hdomain : forall v u, Map.get positive_encoding v (parents p) = Some u ->
    In v (live p) /\ In u (live p)).
  { intros v u Hget. destruct (parent_sound p v u Hready Hget)
      as [n [d [Hn [Hd [Hrn [Hrd Himm]]]]]].
    split; apply (proj2 (live_spec p _ Hready)); [exists n|exists d]; auto. }
  constructor.
  - exact (DomNumber.of_parents_wf (live p) (parents p) Hmap).
  - intros v u n d Hget Hn Hd.
    rewrite DomNumber.of_parents_idom in Hget.
    destruct (parent_sound p v u Hready Hget) as [n' [d' [Hn' [Hd' [Hr [Hdr Himm]]]]]].
    pose proof (Prepared.name_of_id_of p n' v Hp Hn').
    pose proof (Prepared.name_of_id_of p d' u Hp Hd').
    assert (n' = n) by congruence. assert (d' = d) by congruence. now subst n' d'.
  - intros n v Hreach Hn. rewrite DomNumber.of_parents_idom.
    exact (parent_complete p n v Hready Hreach Hn).
  - intros v u Hget. rewrite DomNumber.of_parents_idom in Hget.
    destruct (parent_sound p v u Hready Hget) as [n [d [Hn [Hd [Hr [Hdr Himm]]]]]].
    exists n, d. repeat split; try assumption; now apply Prepared.name_of_id_of.
  - rewrite DomNumber.of_parents_idom. exact (parent_finite p Hready).
  - intros n d v u Hn Hd Hv Hu. rewrite DomNumber.of_parents_idom.
    apply (DomNumber.of_parents_numbering _ _ (live_nodup p Hready)
      Hmap Hdomain (parent_finite p Hready) u v).
    + apply (proj2 (live_spec p u Hready)). exists d. auto.
    + apply (proj2 (live_spec p v Hready)). exists n. auto.
Qed.

Local Lemma scoped_endpoint {V E} (p : Prepared.t V E) scope root es v :
  Search.scoped_path p scope root es v -> Prepared.valid_id p v.
Proof.
  intro Hpath. induction Hpath; assumption.
Qed.

(** Enumerating the public unrestricted closure yields precisely reachable named original IDs. *)
Theorem reachable_ids_spec {V E} (p : Prepared.t V E) v :
  Prepared.ready p ->
  (In v (FinSet.elements (Reach.set p Reach.unrestricted (Prepared.entry_ids p))) <->
    exists n, Prepared.id_of p n = Some v /\ reachable (Prepared.graph p) n).
Proof.
  intro Hready.
  rewrite (FinSet.elements_spec positive_encoding positive_encoding_laws) by apply Reach.set_wf.
  split.
  - intro Hmember. pose proof (proj1 (Reach.exact p _ _ v Hready) Hmember) as Hreach.
    destruct Hreach as [root [es [Hentry Hpath]]].
    destruct (scoped_endpoint _ _ _ _ _ Hpath) as [n [Hnode Hname]].
    exists n. split; [exact Hname|].
    exact (proj1 (Reach.entries_exact p n v Hready Hname) Hmember).
  - intros [n [Hname Hreach]].
    exact (proj2 (Reach.entries_exact p n v Hready Hname) Hreach).
Qed.

(** Actual forest annotation preserves an exact parent map over any duplicate-free exact reachable-ID list. *)
Theorem renumber_exact {V E} (p : Prepared.t V E) t listed :
  Prepared.ready p -> Dom.exact p t -> NoDup listed ->
  (forall v, In v listed <->
    exists n, Prepared.id_of p n = Some v /\ reachable (Prepared.graph p) n) ->
  Dom.exact p (DomNumber.of_parents listed (Dom.idom t)).
Proof.
  intros Hready Htree Hlisted Hcover. pose proof (proj2 (proj2 Hready)) as Hp.
  pose proof (proj1 (Dom.maps_wf p t Htree)) as Hmap.
  assert (Hdomain : forall v u, Map.get positive_encoding v (Dom.idom t) = Some u ->
    In v listed /\ In u listed).
  { intros v u Hget.
    destruct (Dom.idom_domain p t Htree v u Hget) as [n [d [Hn [Hd [Hrn Hrd]]]]].
    split; apply (proj2 (Hcover _)); [exists n|exists d]; split;
      try assumption; now apply Prepared.id_of_name_of. }
  constructor.
  - exact (DomNumber.of_parents_wf listed (Dom.idom t) Hmap).
  - intros v u n d Hget Hn Hd. rewrite DomNumber.of_parents_idom in Hget.
    exact (Dom.idom_sound p t Htree v u n d Hget Hn Hd).
  - intros n v Hreach Hname. rewrite DomNumber.of_parents_idom.
    exact (Dom.idom_complete p t Htree n v Hreach Hname).
  - intros v u Hget. rewrite DomNumber.of_parents_idom in Hget.
    exact (Dom.idom_domain p t Htree v u Hget).
  - rewrite DomNumber.of_parents_idom. exact (Dom.parent_finite p t Htree).
  - intros n d v u Hn Hd Hv Hu. rewrite DomNumber.of_parents_idom.
    apply (DomNumber.of_parents_numbering listed (Dom.idom t) Hlisted Hmap Hdomain
      (Dom.parent_finite p t Htree) u v).
    + apply (proj2 (Hcover u)). exists d. auto.
    + apply (proj2 (Hcover v)). exists n. auto.
Qed.

End DomOutput.
