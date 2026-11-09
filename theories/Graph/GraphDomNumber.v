(** * Search annotation of the actual parent forest

    A single search of the parent forest supplies entry and exit numbers in the original ID space.
    For example, a line's tail is numbered inside each of its parent intervals.
    Builds on: GraphSearch, GraphDomSpec and charged preparation and grouping. *)

From Stdlib Require Import List Bool PArith Permutation.
From Stdlib.Relations Require Import Relation_Operators.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseIndex.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearchSpec
  GraphSearch GraphSearchExact GraphReach GraphDomSpec.
Import List.ListNotations Cost.Notations.

Module DomNumber.

Definition children_c (children : Map.t positive (list (positive * positive))) v :=
  let* row := Index.find_c positive_encoding v children in
  map_c (fun vu => Cost.ret (fst vu)) row.

Definition source_c (parents : Map.t positive positive) v :=
  let* parent := Map.get_c positive_encoding v parents in
  Cost.ret (match parent with
    | None => v
    | Some u => u
    end).

(** Parentless live nodes are roots and each child serves as its incoming forest-edge label. *)
Definition forest_c live (parents : Map.t positive positive) :=
  let* bindings := Map.elements_c parents in
  let* children := Index.group_by_c positive_encoding
    (fun vu => Cost.ret (snd vu)) bindings in
  let* roots := filter_c (fun v =>
    Cost.map negb (Map.mem_c positive_encoding v parents)) live in
  Cost.ret (Graph.Make roots live (children_c children) (source_c parents)
    (fun v => Cost.ret v)).

Definition forest live parents := Cost.value (forest_c live parents).

(** The forest graph uses the actual grouped parent bindings and parentless listed roots. *)
Theorem forest_equation live parents :
  forest live parents =
    Graph.Make (filter (fun v => negb (Map.mem positive_encoding v parents)) live) live
      (children_c (Index.group_by positive_encoding (@snd positive positive)
        (Map.elements parents))) (source_c parents) (fun v => Cost.ret v).
Proof.
  unfold forest, forest_c. autorewrite with galois_cost.
  fold (Map.elements parents). rewrite Index.group_by_c_value. reflexivity.
Qed.

(** A forest child is its own edge target. *)
Theorem forest_target live parents v :
  Graph.target (forest live parents) v = v.
Proof.
  rewrite forest_equation, Graph.make_target. reflexivity.
Qed.

(** A listed child edge reads its actual parent, while an absent edge keeps its own endpoint. *)
Theorem forest_source live parents v :
  Graph.source (forest live parents) v =
    match Map.get positive_encoding v parents with
    | None => v
    | Some u => u
    end.
Proof.
  rewrite forest_equation, Graph.make_source.
  unfold source_c. rewrite Cost.value_bind.
  fold (Map.get positive_encoding v parents).
  destruct (Map.get positive_encoding v parents); reflexivity.
Qed.

(** Outgoing forest lists retain the filtered original map-enumeration order. *)
Theorem forest_out live parents u :
  Graph.out (forest live parents) u =
    map fst (filter (fun vu => eqb positive_encoding (snd vu) u) (Map.elements parents)).
Proof.
  rewrite forest_equation, Graph.make_out.
  unfold children_c. autorewrite with galois_cost.
  fold (Index.find positive_encoding u
    (Index.group_by positive_encoding (@snd positive positive) (Map.elements parents))).
  rewrite Index.find_group_by. reflexivity.
Qed.

(** Forest edges are exactly the represented parent bindings. *)
Theorem forest_edge live parents u v :
  Map.wf positive_encoding parents ->
  (In v (Graph.out (forest live parents) u) <->
    Map.get positive_encoding v parents = Some u).
Proof.
  intro Hmap. rewrite forest_out, in_map_iff.
  split.
  - intros [[a b] [Heq Hin]]. cbn [fst] in Heq. subst a.
    apply filter_In in Hin. destruct Hin as [Hin Hparent].
    apply (eqb_true_iff _ positive_encoding_laws) in Hparent. cbn [snd] in Hparent.
    subst b. apply (Map.elements_spec positive_encoding positive_encoding_laws).
    + exact Hmap.
    + exact Hin.
  - intro Hget. exists (v, u). split; [reflexivity|].
    apply filter_In. split.
    + apply (Map.elements_spec positive_encoding positive_encoding_laws).
      * exact Hmap.
      * exact Hget.
    + cbn [snd]. apply eqb_refl.
Qed.

Local Lemma missing_parent (parents : Map.t positive positive) v :
  Map.mem positive_encoding v parents = false <-> Map.get positive_encoding v parents = None.
Proof.
  rewrite <- not_true_iff_false, Map.mem_spec. split.
  - intro Hnone. destruct (Map.get positive_encoding v parents) as [u|] eqn:Hget;
      [exfalso; apply Hnone; now exists u|reflexivity].
  - intros Hnone [u Hget]. congruence.
Qed.

(** Forest roots are exactly the listed vertices with no represented strict parent. *)
Theorem forest_roots live parents v :
  In v (Graph.entries (forest live parents)) <->
    In v live /\ Map.get positive_encoding v parents = None.
Proof.
  rewrite forest_equation. cbn [Graph.entries].
  rewrite filter_In, negb_true_iff, missing_parent. reflexivity.
Qed.

Local Lemma filtered_keys_nodup
    (bindings : list (positive * positive)) (keep : positive * positive -> bool) :
  NoDup (map fst bindings) -> NoDup (map fst (filter keep bindings)).
Proof.
  induction bindings as [|[v u] rest IH]; intro Hnodup; [constructor|].
  inversion Hnodup as [|a tail Hfresh Hrest]; subst.
  cbn [filter]. destruct (keep (v, u)); [|now apply IH].
  cbn [map fst]. constructor; [|now apply IH].
  intro Hin. apply in_map_iff in Hin. destruct Hin as [[a b] [Heq Hin]].
  cbn [fst] in Heq. subst a. apply filter_In in Hin.
  apply Hfresh. apply in_map_iff. exists (v, b).
  split; [reflexivity|exact (proj1 Hin)].
Qed.

(** Canonical parent storage gives duplicate-free forest outgoing labels at every source. *)
Theorem forest_out_nodup live parents :
  Map.wf positive_encoding parents ->
  forall u, NoDup (Graph.out (forest live parents) u).
Proof.
  intros Hmap u. rewrite forest_out. apply filtered_keys_nodup.
  exact (Map.elements_nodup positive_encoding parents Hmap).
Qed.

(** A finite listed parent domain gives a well-formed graph for the annotation search. *)
Theorem forest_wf live parents :
  NoDup live -> Map.wf positive_encoding parents ->
  (forall v u, Map.get positive_encoding v parents = Some u -> In v live /\ In u live) ->
  graph_wf (forest live parents).
Proof.
  intros Hlive Hmap Hdomain. constructor.
  - rewrite forest_equation. exact Hlive.
  - intros v Hv. apply forest_roots in Hv. exact (proj1 Hv).
  - intros u v Hedge. apply (forest_edge live parents u v Hmap) in Hedge.
    rewrite forest_equation, Graph.make_source.
    unfold source_c. rewrite Cost.value_bind.
    fold (Map.get positive_encoding v parents). now rewrite Hedge.
  - intros u v Hu Hedge. rewrite forest_target.
    apply (forest_edge live parents u v Hmap) in Hedge.
    exact (proj1 (Hdomain v u Hedge)).
Qed.

(** Charged forest preparation satisfies the public search input contract on the finite parent domain. *)
Theorem forest_prepared_ready live parents :
  NoDup live -> Map.wf positive_encoding parents ->
  (forall v u, Map.get positive_encoding v parents = Some u -> In v live /\ In u live) ->
  Prepared.ready (Prepared.prepare positive_encoding (forest live parents)).
Proof.
  intros Hlive Hmap Hdomain. apply Prepared.prepare_ready.
  - exact positive_encoding_laws.
  - now apply forest_wf.
  - now apply forest_out_nodup.
Qed.

(** Well-founded parents connect every listed vertex to a parentless listed root. *)
Theorem forest_reachable live parents :
  NoDup live -> Map.wf positive_encoding parents ->
  (forall v u, Map.get positive_encoding v parents = Some u -> In v live /\ In u live) ->
  well_founded (fun u v => Map.get positive_encoding v parents = Some u) ->
  forall v, In v live <-> reachable (forest live parents) v.
Proof.
  intros Hlive Hmap Hdomain Hfinite v. split.
  - induction (Hfinite v) as [v Hparents IH]. intro Hv.
    destruct (Map.get positive_encoding v parents) as [u|] eqn:Hparent.
    + rewrite <- (forest_target live parents v).
      apply reachable_step.
      * rewrite forest_source, Hparent. apply IH.
        -- reflexivity.
        -- exact (proj2 (Hdomain v u Hparent)).
      * rewrite forest_source, Hparent.
        apply (forest_edge live parents u v Hmap). exact Hparent.
    + apply reachable_entry. apply forest_roots. auto.
  - intro Hreach.
    pose proof (reachable_in_nodes _ _ (forest_wf live parents Hlive Hmap Hdomain) Hreach)
      as Hnode.
    rewrite forest_equation in Hnode. exact Hnode.
Qed.

(** Annotation converts the forest preparation's own IDs back to the actual original vertex IDs. *)
Definition annotation_c (q : Prepared.t positive positive)
    (index : Map.t positive positive) live :=
  fold_right_c (fun v tail =>
    let* prepared_id := Prepared.id_of_c q v in
    match prepared_id with
    | None => Cost.ret tail
    | Some i =>
      let* number := Map.get_c positive_encoding i index in
      match number with
      | None => Cost.ret tail
      | Some number => Map.set_c positive_encoding v number tail
      end
    end) Map.empty live.

Definition lookup (q : Prepared.t positive positive) (index : Map.t positive positive) v :=
  match Prepared.id_of q v with
  | None => None
  | Some i => Map.get positive_encoding i index
  end.

(** Annotation inserts the actual successful numeric lookups under the original vertex keys. *)
Theorem annotation_equation q index live :
  Cost.value (annotation_c q index live) =
    fold_right (fun v tail =>
      match lookup q index v with
      | None => tail
      | Some number => Map.set positive_encoding v number tail
      end) Map.empty live.
Proof.
  unfold annotation_c. rewrite value_fold_right_c.
  induction live as [|v rest IH]; [reflexivity|].
  cbn [fold_right]. autorewrite with galois_cost.
  fold (Prepared.id_of q v). unfold lookup at 1.
  destruct (Prepared.id_of q v) as [i|]; autorewrite with galois_cost;
    [|exact IH].
  fold (Map.get positive_encoding i index).
  destruct (Map.get positive_encoding i index); autorewrite with galois_cost;
    now rewrite IH.
Qed.

Local Lemma reference_wf (f : positive -> option positive) xs :
  Map.wf positive_encoding
    (fold_right (fun v tail =>
      match f v with
      | None => tail
      | Some number => Map.set positive_encoding v number tail
      end) Map.empty xs).
Proof.
  induction xs as [|v rest IH]; [apply Map.wf_empty|].
  cbn [fold_right]. destruct (f v); [now apply Map.wf_set|exact IH].
Qed.

Local Lemma reference_none (f : positive -> option positive) xs v :
  f v = None ->
  Map.get positive_encoding v
    (fold_right (fun x tail =>
      match f x with
      | None => tail
      | Some number => Map.set positive_encoding x number tail
      end) Map.empty xs) = None.
Proof.
  intro Hnone. induction xs as [|x rest IH]; [apply Map.get_empty|].
  cbn [fold_right]. destruct (f x) as [number|] eqn:Hx; [|exact IH].
  rewrite Map.get_set_other.
  - exact IH.
  - exact positive_encoding_laws.
  - apply reference_wf.
  - congruence.
Qed.

Local Lemma reference_present (f : positive -> option positive) xs v :
  In v xs ->
  Map.get positive_encoding v
    (fold_right (fun x tail =>
      match f x with
      | None => tail
      | Some number => Map.set positive_encoding x number tail
      end) Map.empty xs) = f v.
Proof.
  induction xs as [|x rest IH]; intro Hin; [contradiction|].
  cbn [fold_right]. destruct (Pos.eq_dec v x) as [->|Hne].
  - destruct (f x) as [number|] eqn:Hx.
    + apply Map.get_set_same. apply reference_wf.
    + apply reference_none. exact Hx.
  - assert (Htail : In v rest) by (destruct Hin; [congruence|assumption]).
    destruct (f x).
    + rewrite Map.get_set_other by
        (try exact positive_encoding_laws; try apply reference_wf; exact Hne).
      now apply IH.
    + now apply IH.
Qed.

(** Every listed original vertex receives precisely its own converted numeric lookup. *)
Theorem annotation_get q index live v :
  In v live ->
  Map.get positive_encoding v (Cost.value (annotation_c q index live)) = lookup q index v.
Proof.
  intro Hin. rewrite annotation_equation. now apply reference_present.
Qed.

(** A successful forest preparation ID transports its numeric entry back to the original ID. *)
Theorem annotation_number q index live v i :
  In v live -> Prepared.id_of q v = Some i ->
  Map.get positive_encoding v (Cost.value (annotation_c q index live)) =
    Map.get positive_encoding i index.
Proof.
  intros Hin Hi. rewrite annotation_get by exact Hin.
  unfold lookup. now rewrite Hi.
Qed.

(** Annotation construction establishes canonical storage independently of numeric-map validity. *)
Theorem annotation_wf q index live :
  Map.wf positive_encoding (Cost.value (annotation_c q index live)).
Proof.
  unfold annotation_c. rewrite value_fold_right_c.
  induction live as [|v rest IH]; [apply Map.wf_empty|].
  cbn [fold_right]. autorewrite with galois_cost.
  fold (Prepared.id_of q v).
  destruct (Prepared.id_of q v) as [i|]; autorewrite with galois_cost; [|exact IH].
  fold (Map.get positive_encoding i index).
  destruct (Map.get positive_encoding i index); autorewrite with galois_cost;
    [now apply Map.wf_set|exact IH].
Qed.

(** The output keeps the actual input parent map and numbers its forest with one search. *)
Definition of_parents_c live (parents : Map.t positive positive) :=
  let* forest := forest_c live parents in
  let* prepared := Prepared.prepare_c positive_encoding forest in
  let* answer := SearchRun.run_c prepared Visitor.noop Reach.unrestricted
    (Prepared.entry_ids prepared) tt in
  let r := fst answer in
  let* tin := annotation_c prepared (Search.pre_num r) live in
  let* tout := annotation_c prepared (Search.post_num r) live in
  Cost.ret (Dom.Tree parents tin tout).

Definition of_parents live parents := Cost.value (of_parents_c live parents).

Definition prepared live parents :=
  Prepared.prepare positive_encoding (forest live parents).

Definition search live parents :=
  fst (Cost.value (SearchRun.run_c (prepared live parents) Visitor.noop Reach.unrestricted
    (Prepared.entry_ids (prepared live parents)) tt)).

(** Both output annotation maps come from the same actual parent-forest search. *)
Theorem of_parents_equation live parents :
  of_parents live parents =
    Dom.Tree parents
      (Cost.value (annotation_c (prepared live parents) (Search.pre_num (search live parents)) live))
      (Cost.value
        (annotation_c (prepared live parents) (Search.post_num (search live parents)) live)).
Proof.
  reflexivity.
Qed.

(** Forest annotation never replaces the parent map selected by the backend. *)
Theorem of_parents_idom live parents :
  Dom.idom (of_parents live parents) = parents.
Proof.
  reflexivity.
Qed.

(** Every numbered tree has canonical annotation maps whenever its retained parent map is canonical. *)
Theorem of_parents_wf live parents :
  Map.wf positive_encoding parents ->
  Map.wf positive_encoding (Dom.idom (of_parents live parents)) /\
    Map.wf positive_encoding (Dom.tin (of_parents live parents)) /\
    Map.wf positive_encoding (Dom.tout (of_parents live parents)).
Proof.
  intro Hparents. split; [now rewrite of_parents_idom|].
  unfold of_parents, of_parents_c.
  autorewrite with galois_cost.
  cbn [Dom.tin Dom.tout]. split; apply annotation_wf.
Qed.

(** The parent-forest search satisfies the public exactness contract on a valid finite listed domain. *)
Theorem search_exact live parents :
  NoDup live -> Map.wf positive_encoding parents ->
  (forall v u, Map.get positive_encoding v parents = Some u -> In v live /\ In u live) ->
  Search.exact (prepared live parents) Reach.unrestricted
    (Prepared.entry_ids (prepared live parents)) (search live parents).
Proof.
  intros Hlive Hmap Hdomain. apply SearchExact.run_exact.
  now apply forest_prepared_ready.
Qed.

Local Lemma prepared_graph live parents :
  Prepared.graph (prepared live parents) = forest live parents.
Proof.
  unfold prepared. apply Prepared.prepare_graph.
Qed.

(** The annotation search visits exactly the listed finite-forest vertices in its own prepared IDs. *)
Theorem search_live live parents v i :
  NoDup live -> Map.wf positive_encoding parents ->
  (forall v u, Map.get positive_encoding v parents = Some u -> In v live /\ In u live) ->
  well_founded (fun u v => Map.get positive_encoding v parents = Some u) ->
  Prepared.id_of (prepared live parents) v = Some i ->
  (In i (Search.preorder (search live parents)) <-> In v live).
Proof.
  intros Hlive Hmap Hdomain Hfinite Hi.
  pose proof (forest_prepared_ready live parents Hlive Hmap Hdomain) as Hready.
  pose proof (search_exact live parents Hlive Hmap Hdomain) as Hsearch.
  rewrite (Search.pre_complete _ _ _ _ Hsearch).
  rewrite <- (Reach.exact (prepared live parents) _ _ i Hready).
  rewrite (Reach.entries_exact (prepared live parents) v i Hready Hi), prepared_graph.
  symmetry. now apply forest_reachable.
Qed.

(** A recorded search parent names exactly the corresponding original parent binding. *)
Theorem search_parent_named live parents child i e j :
  NoDup live -> Map.wf positive_encoding parents ->
  (forall v u, Map.get positive_encoding v parents = Some u -> In v live /\ In u live) ->
  Prepared.id_of (prepared live parents) child = Some i ->
  Map.get positive_encoding i (Search.parent_edge (search live parents)) = Some (e, j) ->
  exists parent, Prepared.id_of (prepared live parents) parent = Some j /\
    Map.get positive_encoding child parents = Some parent.
Proof.
  intros Hlive Hmap Hdomain Hi Hedge.
  pose proof (forest_prepared_ready live parents Hlive Hmap Hdomain) as Hready.
  pose proof (proj2 (proj2 Hready)) as Hp.
  pose proof (Search.parent_edge_valid _ _ _ _
    (search_exact live parents Hlive Hmap Hdomain) i e j Hedge) as [Harc _].
  destruct Harc as [a [b [Ha [Hia [Hib [Hsource [Htarget Hout]]]]]]].
  rewrite prepared_graph in Htarget, Hout.
  rewrite forest_target in Htarget. subst b.
  pose proof (Prepared.name_of_id_of _ child i Hp Hi) as Hchild.
  pose proof (Prepared.name_of_id_of _ e i Hp Hib) as Hlabel.
  assert (e = child) by congruence. subst e.
  exists a. split; [exact Hia|].
  now apply (forest_edge live parents a child Hmap).
Qed.

(** Every represented parent becomes the corresponding search parent on the finite forest domain. *)
Theorem search_parent_complete live parents child parent i j :
  NoDup live -> Map.wf positive_encoding parents ->
  (forall v u, Map.get positive_encoding v parents = Some u -> In v live /\ In u live) ->
  well_founded (fun u v => Map.get positive_encoding v parents = Some u) ->
  Prepared.id_of (prepared live parents) child = Some i ->
  Prepared.id_of (prepared live parents) parent = Some j ->
  Map.get positive_encoding child parents = Some parent ->
  exists e, Map.get positive_encoding i (Search.parent_edge (search live parents)) = Some (e, j).
Proof.
  intros Hlive Hmap Hdomain Hfinite Hi Hj Hparent.
  pose proof (forest_prepared_ready live parents Hlive Hmap Hdomain) as Hready.
  pose proof (proj2 (proj2 Hready)) as Hp.
  pose proof (search_exact live parents Hlive Hmap Hdomain) as Hsearch.
  destruct (Map.get positive_encoding i (Search.parent_edge (search live parents)))
    as [[e k]|] eqn:Hedge.
  - destruct (search_parent_named live parents child i e k Hlive Hmap Hdomain Hi Hedge)
      as [a [Ha Hget]].
    assert (a = parent) by congruence. subst a.
    assert (k = j) by congruence. subst k. now exists e.
  - assert (Hvisited : In i (Search.preorder (search live parents))).
    { apply (search_live live parents child i Hlive Hmap Hdomain Hfinite Hi).
      exact (proj1 (Hdomain child parent Hparent)). }
    pose proof (Search.parent_roots _ _ _ _ Hsearch i Hvisited Hedge) as Hroot.
    apply (Prepared.entry_ids_spec _ i Hp) in Hroot.
    destruct Hroot as [root [Hentry Hname]].
    pose proof (Prepared.name_of_id_of _ root i Hp Hname).
    pose proof (Prepared.name_of_id_of _ child i Hp Hi).
    assert (root = child) by congruence. subst root.
    fold (prepared live parents) in Hentry.
    rewrite prepared_graph in Hentry. apply forest_roots in Hentry.
    destruct Hentry as [_ Hnone]. congruence.
Qed.

Local Lemma named_id_valid {V E} (q : Prepared.t V E) n i :
  Prepared.laws q -> Prepared.id_of q n = Some i -> Prepared.valid_id q i.
Proof.
  intros Hq Hi. exists n. split; [|exact Hi].
  apply (Prepared.ids_domain q Hq). now exists i.
Qed.

Local Lemma named_id_injective {V E} (q : Prepared.t V E) a b i :
  Prepared.laws q ->
  Prepared.id_of q a = Some i -> Prepared.id_of q b = Some i -> a = b.
Proof.
  intros Hq Ha Hb.
  pose proof (Prepared.name_of_id_of q a i Hq Ha).
  pose proof (Prepared.name_of_id_of q b i Hq Hb). congruence.
Qed.

Local Lemma ancestor_valid {V E} (q : Prepared.t V E) scope roots r :
  Search.exact q scope roots r ->
  forall i j, Search.ancestor r i j -> Prepared.valid_id q j -> Prepared.valid_id q i.
Proof.
  intros Hsearch i j Hancestor.
  induction Hancestor as [i j [e Hget]|i|i k j Hik IHik Hkj IHkj]; intro Hj.
  - destruct (Search.parent_edge_valid _ _ _ _ Hsearch j e i Hget)
      as [[a [b [Ha [Hia Hrest]]]] Hrecorded].
    exists a. auto.
  - exact Hj.
  - apply IHik. now apply IHkj.
Qed.

Local Lemma ancestor_listed live parents d n :
  (forall v u, Map.get positive_encoding v parents = Some u -> In v live /\ In u live) ->
  idom_ancestor parents d n -> In n live -> In d live.
Proof.
  intros Hdomain Hancestor.
  induction Hancestor as [d n Hget|n|d u n Hdu IHdu Hun IHun]; intro Hn.
  - exact (proj2 (Hdomain n d Hget)).
  - exact Hn.
  - apply IHdu. now apply IHun.
Qed.

Local Lemma listed_id live parents v :
  NoDup live -> Map.wf positive_encoding parents ->
  (forall v u, Map.get positive_encoding v parents = Some u -> In v live /\ In u live) ->
  In v live -> exists i, Prepared.id_of (prepared live parents) v = Some i.
Proof.
  intros Hlive Hmap Hdomain Hv.
  pose proof (proj2 (proj2 (forest_prepared_ready live parents Hlive Hmap Hdomain))) as Hq.
  apply (Prepared.ids_domain _ Hq).
  fold (prepared live parents). rewrite prepared_graph, forest_equation. exact Hv.
Qed.

Local Lemma lower_ancestor live parents :
  NoDup live -> Map.wf positive_encoding parents ->
  (forall v u, Map.get positive_encoding v parents = Some u -> In v live /\ In u live) ->
  forall i j, Search.ancestor (search live parents) i j ->
  forall d n, Prepared.id_of (prepared live parents) d = Some i ->
    Prepared.id_of (prepared live parents) n = Some j -> idom_ancestor parents d n.
Proof.
  intros Hlive Hmap Hdomain i j Hancestor.
  pose proof (search_exact live parents Hlive Hmap Hdomain) as Hsearch.
  pose proof (proj2 (proj2 (forest_prepared_ready live parents Hlive Hmap Hdomain))) as Hq.
  induction Hancestor as [i j [e Hget]|i|i k j Hik IHik Hkj IHkj];
    intros d n Hd Hn.
  - destruct (search_parent_named live parents n j e i Hlive Hmap Hdomain Hn Hget)
      as [a [Ha Hparent]].
    assert (a = d) by (eapply named_id_injective; eauto). subst a.
    apply rt_step. exact Hparent.
  - assert (d = n) by (eapply named_id_injective; eauto). subst n. apply rt_refl.
  - destruct (ancestor_valid _ _ _ _ Hsearch k j Hkj (named_id_valid _ n j Hq Hn))
      as [u [Hu Hiu]].
    eapply rt_trans; [apply (IHik d u); eassumption|apply (IHkj u n); eassumption].
Qed.

Local Lemma raise_ancestor live parents :
  NoDup live -> Map.wf positive_encoding parents ->
  (forall v u, Map.get positive_encoding v parents = Some u -> In v live /\ In u live) ->
  well_founded (fun u v => Map.get positive_encoding v parents = Some u) ->
  forall d n, idom_ancestor parents d n -> In n live ->
  forall i j, Prepared.id_of (prepared live parents) d = Some i ->
    Prepared.id_of (prepared live parents) n = Some j ->
    Search.ancestor (search live parents) i j.
Proof.
  intros Hlive Hmap Hdomain Hfinite d n Hancestor.
  induction Hancestor as [d n Hget|n|d u n Hdu IHdu Hun IHun]; intros Hn i j Hi Hj.
  - destruct (search_parent_complete live parents n d j i Hlive Hmap Hdomain Hfinite
      Hj Hi Hget) as [e He]. apply rt_step. now exists e.
  - assert (i = j) by congruence. subst j. apply rt_refl.
  - pose proof (ancestor_listed live parents u n Hdomain Hun Hn) as Hu.
    destruct (listed_id live parents u Hlive Hmap Hdomain Hu) as [k Hk].
    eapply rt_trans; [apply (IHdu Hu i k); eassumption|apply (IHun Hn k j); eassumption].
Qed.

(** Named search ancestry is precisely ancestry of the actual original finite parent map. *)
Theorem named_ancestry live parents d n i j :
  NoDup live -> Map.wf positive_encoding parents ->
  (forall v u, Map.get positive_encoding v parents = Some u -> In v live /\ In u live) ->
  well_founded (fun u v => Map.get positive_encoding v parents = Some u) ->
  In n live ->
  Prepared.id_of (prepared live parents) d = Some i ->
  Prepared.id_of (prepared live parents) n = Some j ->
  (Search.ancestor (search live parents) i j <-> idom_ancestor parents d n).
Proof.
  intros Hlive Hmap Hdomain Hfinite Hn Hi Hj. split.
  - intro Hancestor. exact (lower_ancestor live parents Hlive Hmap Hdomain i j Hancestor d n Hi Hj).
  - intro Hancestor.
    exact (raise_ancestor live parents Hlive Hmap Hdomain Hfinite d n Hancestor Hn i j Hi Hj).
Qed.

(** Every listed finite-forest vertex receives both numeric annotations from that actual search. *)
Theorem of_parents_covers live parents :
  NoDup live -> Map.wf positive_encoding parents ->
  (forall v u, Map.get positive_encoding v parents = Some u -> In v live /\ In u live) ->
  well_founded (fun u v => Map.get positive_encoding v parents = Some u) ->
  forall v, In v live ->
  exists a b, Map.get positive_encoding v (Dom.tin (of_parents live parents)) = Some a /\
    Map.get positive_encoding v (Dom.tout (of_parents live parents)) = Some b.
Proof.
  intros Hlive Hmap Hdomain Hfinite v Hv.
  pose proof (forest_prepared_ready live parents Hlive Hmap Hdomain) as Hready.
  fold (prepared live parents) in Hready.
  pose proof (proj2 (proj2 Hready)) as Hprepared.
  assert (Hnode : In v (Graph.nodes (Prepared.graph (prepared live parents)))).
  { unfold prepared. rewrite Prepared.prepare_graph, forest_equation. exact Hv. }
  destruct (proj1 (Prepared.ids_domain _ Hprepared v) Hnode) as [i Hi].
  assert (Hreach : reachable (Prepared.graph (prepared live parents)) v).
  { unfold prepared. rewrite Prepared.prepare_graph.
    apply (forest_reachable live parents Hlive Hmap Hdomain Hfinite v). exact Hv. }
  apply (proj2 (Reach.entries_exact _ v i Hready Hi)) in Hreach.
  apply (Reach.exact _ _ _ i Hready) in Hreach.
  pose proof (search_exact live parents Hlive Hmap Hdomain) as Hsearch.
  apply (Search.pre_complete _ _ _ _ Hsearch) in Hreach.
  pose proof (Permutation_in i (Search.post_perm _ _ _ _ Hsearch) Hreach) as Hpost.
  apply In_nth_error in Hreach, Hpost.
  destruct Hreach as [entry Hentry]. destruct Hpost as [exit Hexit].
  exists (Pos.of_succ_nat entry), (Pos.of_succ_nat exit).
  rewrite of_parents_equation. cbn [Dom.tin Dom.tout].
  rewrite !annotation_number with (i := i) by assumption.
  split.
  - apply (Search.pre_num_index _ _ _ _ Hsearch).
    rewrite SuccNat2Pos.id_succ. exact Hentry.
  - apply (Search.post_num_index _ _ _ _ Hsearch).
    rewrite SuccNat2Pos.id_succ. exact Hexit.
Qed.

Local Lemma tin_number live parents v i :
  In v live -> Prepared.id_of (prepared live parents) v = Some i ->
  Map.get positive_encoding v (Dom.tin (of_parents live parents)) =
    Map.get positive_encoding i (Search.pre_num (search live parents)).
Proof.
  intros Hv Hi. rewrite of_parents_equation. cbn [Dom.tin].
  exact (annotation_number _ _ live v i Hv Hi).
Qed.

Local Lemma tout_number live parents v i :
  In v live -> Prepared.id_of (prepared live parents) v = Some i ->
  Map.get positive_encoding v (Dom.tout (of_parents live parents)) =
    Map.get positive_encoding i (Search.post_num (search live parents)).
Proof.
  intros Hv Hi. rewrite of_parents_equation. cbn [Dom.tout].
  exact (annotation_number _ _ live v i Hv Hi).
Qed.

Local Lemma interval_numbers {L} (r : Search.result L) i j a b c e :
  Map.get positive_encoding i (Search.pre_num r) = Some a ->
  Map.get positive_encoding j (Search.pre_num r) = Some b ->
  Map.get positive_encoding j (Search.post_num r) = Some c ->
  Map.get positive_encoding i (Search.post_num r) = Some e ->
  (Search.interval r i j <-> (a <= b /\ c <= e)%positive).
Proof.
  intros Ha Hb Hc He. unfold Search.interval. split.
  - intros [a' [b' [c' [e' [Ha' [Hb' [Hc' [He' Horder]]]]]]]].
    assert (a' = a) by congruence. subst a'.
    assert (b' = b) by congruence. subst b'.
    assert (c' = c) by congruence. subst c'.
    assert (e' = e) by congruence. subst e'. exact Horder.
  - intro Horder. exists a, b, c, e. repeat split; tauto.
Qed.

(** The actual parent-forest annotation has exactly the finite parent map's ancestry intervals. *)
Theorem of_parents_numbering live parents :
  NoDup live -> Map.wf positive_encoding parents ->
  (forall v u, Map.get positive_encoding v parents = Some u -> In v live /\ In u live) ->
  well_founded (fun u v => Map.get positive_encoding v parents = Some u) ->
  forall d n, In d live -> In n live ->
  exists a b c e,
    Map.get positive_encoding d (Dom.tin (of_parents live parents)) = Some a /\
    Map.get positive_encoding n (Dom.tin (of_parents live parents)) = Some b /\
    Map.get positive_encoding n (Dom.tout (of_parents live parents)) = Some c /\
    Map.get positive_encoding d (Dom.tout (of_parents live parents)) = Some e /\
    ((a <= b /\ c <= e)%positive <-> idom_ancestor parents d n).
Proof.
  intros Hlive Hmap Hdomain Hfinite d n Hd Hn.
  destruct (listed_id live parents d Hlive Hmap Hdomain Hd) as [i Hi].
  destruct (listed_id live parents n Hlive Hmap Hdomain Hn) as [j Hj].
  destruct (of_parents_covers live parents Hlive Hmap Hdomain Hfinite d Hd)
    as [a [e [Ha He]]].
  destruct (of_parents_covers live parents Hlive Hmap Hdomain Hfinite n Hn)
    as [b [c [Hb Hc]]].
  pose proof Ha as Hpre_i. rewrite (tin_number live parents d i Hd Hi) in Hpre_i.
  pose proof Hb as Hpre_j. rewrite (tin_number live parents n j Hn Hj) in Hpre_j.
  pose proof He as Hpost_i. rewrite (tout_number live parents d i Hd Hi) in Hpost_i.
  pose proof Hc as Hpost_j. rewrite (tout_number live parents n j Hn Hj) in Hpost_j.
  exists a, b, c, e. split; [exact Ha|]. split; [exact Hb|].
  split; [exact Hc|]. split; [exact He|].
  apply iff_trans with (Search.interval (search live parents) i j).
  - symmetry. exact (interval_numbers _ i j a b c e Hpre_i Hpre_j Hpost_j Hpost_i).
  - pose proof (search_exact live parents Hlive Hmap Hdomain) as Hsearch.
    pose proof (proj2 (search_live live parents d i Hlive Hmap Hdomain Hfinite Hi) Hd) as Hvi.
    pose proof (proj2 (search_live live parents n j Hlive Hmap Hdomain Hfinite Hj) Hn) as Hvj.
    rewrite (Search.ancestor_iff _ _ _ _ Hsearch i j Hvi Hvj).
    exact (named_ancestry live parents d n i j Hlive Hmap Hdomain Hfinite Hn Hi Hj).
Qed.

End DomNumber.
