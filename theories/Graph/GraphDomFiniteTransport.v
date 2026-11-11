(** * Indexed-search transport to raw finite closure

    The normalized dictionary transports scoped searches back to raw cached-adjacency reachability.
    For example, an invalid original fuel is replaced by proved preparation of the finite view.
    Builds on: GraphDomFiniteClosure and GraphDomFiniteSearch. *)

From Stdlib Require Import List Bool PArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearchSpec GraphReach
  GraphDomFiniteView GraphDomFiniteClosure GraphDomFiniteSearch.

Module DomFiniteTransport.
Section Transport.
Context {V E : Type} (p : Prepared.t V E) (roots : list positive).
Local Abbreviation q := (DomFiniteView.prepared p roots).

Local Lemma same_name u v i :
  Prepared.id_of q u = Some i -> Prepared.id_of q v = Some i -> u = v.
Proof.
  intros Hu Hv.
  pose proof (Prepared.name_of_id_of q u i
    (proj2 (proj2 (DomFiniteView.prepared_ready p roots))) Hu).
  pose proof (Prepared.name_of_id_of q v i
    (proj2 (proj2 (DomFiniteView.prepared_ready p roots))) Hv). congruence.
Qed.

Local Lemma name_exists v :
  In v (Reach.universe p) -> exists i, Prepared.id_of q v = Some i.
Proof.
  intro Hv.
  apply (Prepared.ids_domain q (proj2 (proj2 (DomFiniteView.prepared_ready p roots)))).
  rewrite DomFiniteView.prepared_graph, DomFiniteView.graph_nodes. exact Hv.
Qed.

Local Lemma name_domain v i :
  Prepared.id_of q v = Some i -> In v (Reach.universe p).
Proof.
  intro Hi. rewrite <- (DomFiniteView.graph_nodes p roots v), <- DomFiniteView.prepared_graph.
  apply (Prepared.ids_domain q (proj2 (proj2 (DomFiniteView.prepared_ready p roots)))).
  now exists i.
Qed.

Local Lemma valid_name v i :
  Prepared.id_of q v = Some i -> Prepared.valid_id q i.
Proof.
  intro Hi. exists v. split; [|exact Hi].
  rewrite DomFiniteView.prepared_graph, DomFiniteView.graph_nodes.
  now apply (name_domain v i).
Qed.

Local Lemma arc_names i edge j :
  Prepared.arc q i edge j <->
    Prepared.id_of q (fst edge) = Some i /\
    Prepared.id_of q (snd edge) = Some j /\
    In edge (Graph.out (DomFiniteView.graph (DomFiniteView.view p roots)) (fst edge)).
Proof.
  split.
  - intros [a [b [Ha [Hi [Hj [Hsource [Htarget Hedge]]]]]]].
    rewrite DomFiniteView.prepared_graph in Hsource, Htarget, Hedge.
    change (fst edge = a) in Hsource. change (snd edge = b) in Htarget.
    now subst a b.
  - intros [Hi [Hj Hedge]]. exists (fst edge), (snd edge). split.
    + rewrite DomFiniteView.prepared_graph, DomFiniteView.graph_nodes.
      now apply (name_domain (fst edge) i).
    + split; [exact Hi|]. split; [exact Hj|].
      rewrite DomFiniteView.prepared_graph. split; [reflexivity|].
      split; [reflexivity|exact Hedge].
Qed.

Local Lemma path_start scope i es j :
  Search.scoped_path q scope i es j -> Scope.admits scope i = true.
Proof.
  intro Hpath. destruct Hpath; assumption.
Qed.

Local Lemma path_snoc scope i es j edge k :
  Search.scoped_path q scope i es j -> Prepared.arc q j edge k ->
  Prepared.valid_id q k -> Scope.admits scope k = true ->
  Search.scoped_path q scope i (es ++ edge :: nil) k.
Proof.
  intros Hpath Hedge Hvalid Hallowed.
  induction Hpath as [v Hv Ha|u e v tail z Hu Ha Huv Htail IH].
  - cbn [app]. econstructor; [exact Hv|exact Ha|exact Hedge|now constructor].
  - cbn [app]. econstructor; [exact Hu|exact Ha|exact Huv|now apply IH].
Qed.

Local Lemma closure_search scope v :
  Reach.closure (DomFiniteClosure.next p scope roots)
    (DomFiniteClosure.starts p scope roots) v ->
  exists i, Prepared.id_of q v = Some i /\
    Search.scoped_reachable q (DomFiniteSearch.translate q scope) (Prepared.entry_ids q) i.
Proof.
  intro Hreach. induction Hreach as [v Hv|u v Hreach [i [Hi [r [es [Hr Hpath]]]]] Hedge].
  - unfold DomFiniteClosure.starts in Hv. apply filter_In in Hv.
    destruct Hv as [Hentry Hallowed].
    pose proof (DomFiniteView.graph_entries p roots v) as Hentry_spec.
    apply Hentry_spec in Hentry as Hsource.
    destruct (name_exists v (proj2 Hsource)) as [i Hi]. exists i. split; [exact Hi|].
    exists i, nil. split.
    + apply (Prepared.entry_ids_spec q i (proj2 (proj2 (DomFiniteView.prepared_ready p roots)))).
      exists v. rewrite DomFiniteView.prepared_graph. auto.
    + constructor; [now apply (valid_name v i)|].
      rewrite (DomFiniteSearch.translated_admits q scope v i
        (DomFiniteView.prepared_ready p roots) Hi). exact Hallowed.
  - apply DomFiniteClosure.next_spec in Hedge as Hraw.
    destruct Hraw as [Hu Hraw].
    apply DomFiniteClosure.raw_successors in Hraw.
    destruct Hraw as [Hallowed [Hv Hedges]].
    destruct (name_exists v Hv) as [j Hj]. exists j. split; [exact Hj|].
    exists r, (es ++ (u, v) :: nil). split; [exact Hr|].
    apply (path_snoc _ _ _ i).
    + exact Hpath.
    + apply arc_names. cbn [fst snd]. split; [exact Hi|]. split; [exact Hj|].
      apply DomFiniteView.graph_edge. cbn [fst snd]. auto.
    + now apply (valid_name v j).
    + rewrite (DomFiniteSearch.translated_admits q scope v j
        (DomFiniteView.prepared_ready p roots) Hj). exact Hallowed.
Qed.

Local Lemma follow_path scope i es j :
  Search.scoped_path q (DomFiniteSearch.translate q scope) i es j ->
  forall u, Prepared.id_of q u = Some i ->
  Reach.closure (DomFiniteClosure.next p scope roots) (DomFiniteClosure.starts p scope roots) u ->
  exists v, Prepared.id_of q v = Some j /\
    Reach.closure (DomFiniteClosure.next p scope roots) (DomFiniteClosure.starts p scope roots) v.
Proof.
  intro Hpath.
  induction Hpath as [i Hvalid Hallowed|i edge k es j Hvalid Hallowed Hedge Htail IH];
    intros u Hu Hreach.
  - now exists u.
  - apply arc_names in Hedge. destruct Hedge as [Hsource [Htarget Hout]].
    assert (Hname : fst edge = u) by (eapply same_name; eassumption).
    apply (IH (snd edge) Htarget). apply (Reach.edge _ _ u (snd edge) Hreach).
    unfold DomFiniteClosure.next. apply filter_In. split.
    + apply in_map_iff. exists edge. split; [reflexivity|]. now rewrite <- Hname.
    + pose proof (path_start _ _ _ _ Htail) as Htranslated.
      rewrite (DomFiniteSearch.translated_admits q scope (snd edge) k
        (DomFiniteView.prepared_ready p roots) Htarget) in Htranslated. exact Htranslated.
Qed.

(** Scoped reachability in the indexed normalized view equals the same raw finite closure. *)
Theorem scoped_closure scope v i :
  Prepared.id_of q v = Some i ->
  (Search.scoped_reachable q (DomFiniteSearch.translate q scope) (Prepared.entry_ids q) i <->
    Reach.closure (Reach.successors p scope) (Reach.roots_in p scope roots) v).
Proof.
  intro Hi. rewrite <- (DomFiniteClosure.normalized_closure p scope roots v). split.
  - intros [r [es [Hr Hpath]]].
    apply (Prepared.entry_ids_spec q r (proj2 (proj2 (DomFiniteView.prepared_ready p roots)))) in Hr.
    destruct Hr as [u [Hentry Hu]].
    assert (Hstart : Reach.closure (DomFiniteClosure.next p scope roots)
      (DomFiniteClosure.starts p scope roots) u).
    { apply Reach.root. unfold DomFiniteClosure.starts. apply filter_In. split.
      - now rewrite <- DomFiniteView.prepared_graph.
      - pose proof (path_start _ _ _ _ Hpath) as Htranslated.
        rewrite (DomFiniteSearch.translated_admits q scope u r
          (DomFiniteView.prepared_ready p roots) Hu) in Htranslated. exact Htranslated. }
    destruct (follow_path scope r es i Hpath u Hu Hstart) as [w [Hw Hclosure]].
    assert (w = v) by (eapply same_name; eassumption). now subst w.
  - intro Hclosure. destruct (closure_search scope v Hclosure) as [j [Hj Hreachable]].
    assert (j = i) by congruence. now subst j.
Qed.

(** Indexed membership agrees with raw reference reachability on every computational input. *)
Theorem member_value scope v :
  Cost.value (DomFiniteSearch.member_c q (DomFiniteSearch.run q scope) v) =
    FinSet.mem positive_encoding v (Reach.set p scope roots).
Proof.
  destruct (Prepared.id_of q v) as [i|] eqn:Hi.
  - apply Bool.eq_true_iff_eq.
    rewrite (DomFiniteSearch.member_reachable q scope v i
      (DomFiniteView.prepared_ready p roots) Hi), (scoped_closure scope v i Hi).
    symmetry. apply DomFiniteClosure.raw_set_closure.
  - change (Cost.value
      (match Prepared.id_of q v with
      | None => Cost.ret false
      | Some id => FinSet.mem_c positive_encoding id
          (Search.visited (DomFiniteSearch.run q scope))
      end) = FinSet.mem positive_encoding v (Reach.set p scope roots)).
    rewrite Hi. apply Bool.eq_true_iff_eq. split; [discriminate|].
    intro Hmember. apply DomFiniteClosure.raw_set_closure in Hmember.
    apply DomFiniteClosure.raw_support in Hmember.
    destruct (name_exists v Hmember) as [i Hid]. congruence.
Qed.

End Transport.
End DomFiniteTransport.
