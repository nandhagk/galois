(** * Dominating incoming edges

    A non-entry node selects its sole reachable incoming edge from outside its own subtree.
    For example, a loop's back edge does not disqualify its unique first-arrival edge.
    Builds on: GraphWalk, GraphFrontierSweep and GraphReach. *)

From Stdlib Require Import List Bool PArith NArith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearchSpec
  GraphReach GraphDomSpec GraphCheckDom GraphFrontierSpec GraphFrontierSweep.
Import List.ListNotations Cost.Notations.

Module FrontierEdge.

Local Open Scope N_scope.

Definition candidate_c t seen v {E} (edge : E * positive) :=
  let* live := FinSet.mem_c positive_encoding (snd edge) seen in
  if live then
    let* ancestors := FrontierSweep.ancestors_c t (snd edge) in
    let* back := FinSet.mem_c positive_encoding v ancestors in
    Cost.ret (negb back)
  else Cost.ret false.

Definition candidates_c {V E} (p : Prepared.t V E) t seen v :=
  let* incoming := Prepared.pred_edges_c p v in
  let* selected := filter_c (candidate_c t seen v) incoming in
  map_c (fun edge => Cost.ret (fst edge)) selected.

Definition candidates {V E} (p : Prepared.t V E) t v :=
  Cost.value (candidates_c p t
    (Reach.set p Reach.unrestricted (Prepared.entry_ids p)) v).

Local Lemma candidates_equation {V E} (p : Prepared.t V E) t v :
  candidates p t v =
    map fst (filter (fun edge =>
      FinSet.mem positive_encoding (snd edge)
        (Reach.set p Reach.unrestricted (Prepared.entry_ids p)) &&
      negb (FinSet.mem positive_encoding v
        (FrontierSweep.ancestors t (snd edge)))) (Prepared.pred_edges p v)).
Proof.
  unfold candidates, candidates_c. autorewrite with galois_cost.
  f_equal. apply filter_ext. intros [e u]. unfold candidate_c.
  cbn [snd]. rewrite Cost.value_bind.
  fold (FinSet.mem positive_encoding u
    (Reach.set p Reach.unrestricted (Prepared.entry_ids p))).
  destruct (FinSet.mem positive_encoding u
    (Reach.set p Reach.unrestricted (Prepared.entry_ids p))); [|reflexivity].
  rewrite !Cost.value_bind. reflexivity.
Qed.

(** Candidate membership retains the labelled edge and excludes dominated sources. *)
Theorem candidates_exact {V E} (p : Prepared.t V E) t n v e :
  Prepared.ready p -> Dom.exact p t -> Prepared.id_of p n = Some v ->
  (In e (candidates p t v) <->
    In e (Graph.out (Prepared.graph p) (Graph.source (Prepared.graph p) e)) /\
    Graph.target (Prepared.graph p) e = n /\
    reachable (Prepared.graph p) (Graph.source (Prepared.graph p) e) /\
    ~ dominates (Prepared.graph p) n (Graph.source (Prepared.graph p) e)).
Proof.
  intros Hready Htree Hn.
  pose proof (proj2 (proj2 Hready)) as Hp.
  rewrite candidates_equation, in_map_iff. split.
  - intros [[a u] [Heq Hin]]. cbn in Heq. subst a.
    apply filter_In in Hin. destruct Hin as [Hin Htest].
    apply (Prepared.pred_agrees p Hp n v e u Hn) in Hin.
    destruct Hin as [Hs [He [Ht Hu]]].
    apply andb_true_iff in Htest. destruct Htest as [Hlive Hback].
    cbn [snd] in Hlive, Hback.
    apply (Reach.entries_exact p _ u Hready Hu) in Hlive.
    apply negb_true_iff in Hback.
    split; [exact He|]. split; [exact Ht|]. split; [exact Hlive|].
    intro Hdom.
    assert (Hanc : idom_ancestor (Dom.idom t) v u).
    { apply (proj2 (DomCheck.ancestry_spec p t _ n u v Hready Htree Hlive Hu Hn)).
      exact Hdom. }
    apply (FrontierSweep.ancestors_spec t u v (proj1 (Dom.maps_wf p t Htree))
      (Dom.parent_finite p t Htree)) in Hanc.
    congruence.
  - intros [He [Ht [Hsource Hnot]]].
    assert (Hs : In (Graph.source (Prepared.graph p) e) (Graph.nodes (Prepared.graph p)))
      by (eapply reachable_in_nodes; [exact (proj1 Hready)|exact Hsource]).
    destruct (proj1 (Prepared.ids_domain p Hp _) Hs) as [u Hu].
    exists (e, u). split; [reflexivity|]. apply filter_In. split.
    + apply (Prepared.pred_agrees p Hp n v e u Hn). auto.
    + apply andb_true_iff. cbn [snd]. split.
      * now apply (Reach.entries_exact p _ u Hready Hu).
      * apply negb_true_iff, Bool.not_true_iff_false.
        rewrite (FrontierSweep.ancestors_spec t u v (proj1 (Dom.maps_wf p t Htree))
          (Dom.parent_finite p t Htree)).
        intro Hanc. apply Hnot.
        now apply (proj1 (DomCheck.ancestry_spec p t _ n u v Hready Htree Hsource Hu Hn)).
Qed.

Definition choice_c {V E} (p : Prepared.t V E) t entries seen v :=
  let* entry := FinSet.mem_c positive_encoding v entries in
  if entry then Cost.ret None else
  let* incoming := candidates_c p t seen v in
  match incoming with
  | [e] => Cost.ret (Some e)
  | _ => Cost.ret None
  end.

Definition choice {V E} (p : Prepared.t V E) t v :=
  Cost.value (choice_c p t (FinSet.of_list positive_encoding (Prepared.entry_ids p))
    (Reach.set p Reach.unrestricted (Prepared.entry_ids p)) v).

Fixpoint build_c {E} (choose : positive -> Cost.t (option E)) vs :=
  match vs with
  | [] => Cost.ret Map.empty
  | v :: rest =>
    Cost.step ;;
    let* m := build_c choose rest in
    Cost.step ;;
    let* selected := choose v in
    match selected with
    | None => Cost.ret m
    | Some e => Map.set_c positive_encoding v e m
    end
  end.

Local Lemma build_equation {E} choose v rest :
  Cost.value (@build_c E choose (v :: rest)) =
    match Cost.value (choose v) with
    | None => Cost.value (build_c choose rest)
    | Some e => Map.set positive_encoding v e (Cost.value (build_c choose rest))
    end.
Proof.
  cbn [build_c]. autorewrite with galois_cost.
  destruct (Cost.value (choose v)); reflexivity.
Qed.

Local Lemma build_wf {E} choose vs :
  Map.wf positive_encoding (Cost.value (@build_c E choose vs)).
Proof.
  induction vs as [|v rest IH]; [apply Map.wf_empty|].
  rewrite build_equation. destruct (Cost.value (choose v));
    [now apply Map.wf_set|exact IH].
Qed.

Local Lemma build_lookup {E} choose vs v :
  Map.get positive_encoding v (Cost.value (@build_c E choose vs)) =
    if existsb (Pos.eqb v) vs then Cost.value (choose v) else None.
Proof.
  induction vs as [|a rest IH].
  - change (Map.get positive_encoding v (@Map.empty positive E) = None).
    apply Map.get_empty.
  - rewrite build_equation. cbn [existsb].
    destruct (Pos.eq_dec v a) as [->|Hne].
    + rewrite Pos.eqb_refl. cbn [orb].
      destruct (Cost.value (choose a)) as [e|] eqn:Hchoice.
      * apply Map.get_set_same, build_wf.
      * rewrite IH. destruct (existsb (Pos.eqb a) rest); reflexivity.
    + rewrite (proj2 (Pos.eqb_neq v a) Hne). cbn [orb].
      destruct (Cost.value (choose a)).
      * rewrite Map.get_set_other by (try apply build_wf; try exact Hne;
          exact positive_encoding_laws). exact IH.
      * exact IH.
Qed.

(** The map selects dominating incoming labels and does not identify them with ancestor edge dominators. *)
Definition edge_dominators_c {V E} (p : Prepared.t V E) t :=
  let* seen := FrontierSweep.reach_c p Reach.unrestricted (Prepared.entry_ids p) in
  let* entries := FinSet.of_list_c positive_encoding (Prepared.entry_ids p) in
  let* all := FrontierSweep.universe_c p in
  build_c (choice_c p t entries seen) all.

Definition edge_dominators {V E} (p : Prepared.t V E) t :=
  Cost.value (edge_dominators_c p t).

Local Lemma build_cost {E} (choose : positive -> Cost.t (option E)) vs :
  Cost.ticks (build_c choose vs) =
    fold_right (fun v n => 2 + Cost.ticks (choose v) +
      match Cost.value (choose v) with
      | None => n
      | Some _ => FrontierSweep.key_charge v + n
      end)%N 0%N vs.
Proof.
  induction vs as [|v rest IH]; [reflexivity|].
  cbn [build_c fold_right]. autorewrite with galois_cost. rewrite IH.
  destruct (Cost.value (choose v)); autorewrite with galois_cost; [|lia].
  rewrite Map.set_cost.
  change ((1 + (fold_right
    (fun v n => 2 + Cost.ticks (choose v) +
      match Cost.value (choose v) with
      | None => n
      | Some _ => FrontierSweep.key_charge v + n
      end)%N 0%N rest +
    (1 + (Cost.ticks (choose v) + (2 + N.pos (Pos.size v)))))) =
    2 + Cost.ticks (choose v) +
      (FrontierSweep.key_charge v + fold_right
        (fun v n => 2 + Cost.ticks (choose v) +
          match Cost.value (choose v) with
          | None => n
          | Some _ => FrontierSweep.key_charge v + n
          end)%N 0%N rest))%N.
  unfold FrontierSweep.key_charge. lia.
Qed.

(** Edge-index accounting retains reachability, entry construction, enumeration and candidate work. *)
Theorem edge_dominators_cost {V E} (p : Prepared.t V E) t :
  Cost.ticks (edge_dominators_c p t) =
    (Cost.ticks (FrontierSweep.reach_c p Reach.unrestricted (Prepared.entry_ids p)) +
      Cost.ticks (FinSet.of_list_c positive_encoding (Prepared.entry_ids p)) +
      Cost.ticks (FrontierSweep.universe_c p) +
      fold_right (fun v n => 2 +
        Cost.ticks (choice_c p t
          (FinSet.of_list positive_encoding (Prepared.entry_ids p))
          (Reach.set p Reach.unrestricted (Prepared.entry_ids p)) v) +
        match choice p t v with
        | None => n
        | Some _ => FrontierSweep.key_charge v + n
        end)%N 0%N (Reach.universe p))%N.
Proof.
  unfold edge_dominators_c. rewrite !Cost.ticks_bind.
  rewrite FrontierSweep.reach_value, FrontierSweep.universe_value.
  rewrite build_cost, !N.add_assoc. reflexivity.
Qed.

Local Lemma index_lookup {V E} (p : Prepared.t V E) t n v :
  Prepared.ready p -> Prepared.id_of p n = Some v ->
  Map.get positive_encoding v (edge_dominators p t) = choice p t v.
Proof.
  intros Hready Hn. unfold edge_dominators, edge_dominators_c.
  rewrite !Cost.value_bind, FrontierSweep.reach_value, FrontierSweep.universe_value.
  rewrite build_lookup.
  assert (Hv : In v (Reach.universe p)).
  { apply Reach.universe_spec. exists n. split; [|exact Hn].
    apply (Prepared.ids_domain p (proj2 (proj2 Hready))). now exists v. }
  assert (Hmem : existsb (Pos.eqb v) (Reach.universe p) = true).
  { apply existsb_exists. exists v. split; [exact Hv|apply Pos.eqb_refl]. }
  rewrite Hmem. reflexivity.
Qed.

Local Lemma entry_ids_spec {V E} (p : Prepared.t V E) n v :
  Prepared.ready p -> Prepared.id_of p n = Some v ->
  (FinSet.mem positive_encoding v
    (FinSet.of_list positive_encoding (Prepared.entry_ids p)) = true <->
    In n (Graph.entries (Prepared.graph p))).
Proof.
  intros Hready Hn. rewrite FinSet.mem_of_list, existsb_exists.
  setoid_rewrite (eqb_true_iff _ positive_encoding_laws).
  split.
  - intros [i [Hi Heq]]. subst i.
    apply (Prepared.entry_ids_spec p v (proj2 (proj2 Hready))) in Hi.
    destruct Hi as [s [Hs Hsi]].
    assert (s = n).
    { pose proof (Prepared.name_of_id_of p s v (proj2 (proj2 Hready)) Hsi).
      pose proof (Prepared.name_of_id_of p n v (proj2 (proj2 Hready)) Hn). congruence. }
    now subst s.
  - intro Hentry. exists v. split; [|reflexivity].
    apply (Prepared.entry_ids_spec p v (proj2 (proj2 Hready))). now exists n.
Qed.

Local Lemma path_snoc {V E} (g : Graph.t V E) s es v e :
  path g s es v -> v = Graph.source g e -> In e (Graph.out g v) ->
  path g s (es ++ [e]) (Graph.target g e).
Proof.
  intro Hpath. induction Hpath as [v|a rest v Ha Hpath IH]; intros Hsource He.
  - subst v. cbn. constructor; [exact He|constructor].
  - cbn. constructor; [exact Ha|now apply IH].
Qed.

Local Lemma first_arrival_aux {V E} (enc : encoding V) (Henc : encoding_laws enc)
    (g : Graph.t V E) v s pre u es :
  path g s pre u -> In s (Graph.entries g) -> v <> s ->
  (forall a, In a pre -> Graph.target g a <> v) -> v <> u -> path g u es v ->
  exists e, In e es /\ In e (Graph.out g (Graph.source g e)) /\
    Graph.target g e = v /\ reachable g (Graph.source g e) /\
    ~ dominates g v (Graph.source g e).
Proof.
  intros Hpre Hentry Hstart Hfree Hcurrent Hpath.
  remember v as dest eqn:Hdest in Hpath.
  revert s pre Hpre Hentry Hstart Hfree Hcurrent Hdest.
  induction Hpath as [u|e rest w He Hpath IH];
    intros s pre Hpre Hentry Hstart Hfree Hcurrent Hdest.
  - congruence.
  - destruct (eqb_dec enc Henc (Graph.target g e) v) as [Ht|Ht].
    + exists e. split; [now left|]. split; [exact He|]. split; [exact Ht|].
      split.
      * apply reachable_iff_path. exists s, pre. auto.
      * intros Hdom. destruct (Hdom s pre Hentry Hpre) as [Heq|[a [Hin Ha]]].
        -- contradiction.
        -- exact (Hfree a Hin Ha).
    + destruct (IH s (pre ++ [e])
        (path_snoc g s pre (Graph.source g e) e Hpre eq_refl He) Hentry Hstart)
        as [a [Hin Hrest]].
      * intros a Hin. apply in_app_iff in Hin. destruct Hin as [Hin|[<-|Hin]];
          [now apply Hfree|exact Ht|contradiction].
      * congruence.
      * exact Hdest.
      * exists a. split; [now right|exact Hrest].
Qed.

Local Lemma first_arrival {V E} (p : Prepared.t V E) n s es :
  Prepared.ready p -> ~ In n (Graph.entries (Prepared.graph p)) ->
  In s (Graph.entries (Prepared.graph p)) -> path (Prepared.graph p) s es n ->
  exists e, In e es /\ In e (Graph.out (Prepared.graph p) (Graph.source (Prepared.graph p) e)) /\
    Graph.target (Prepared.graph p) e = n /\
    reachable (Prepared.graph p) (Graph.source (Prepared.graph p) e) /\
    ~ dominates (Prepared.graph p) n (Graph.source (Prepared.graph p) e).
Proof.
  intros Hready Hnot Hentry Hpath.
  apply (first_arrival_aux (Prepared.node_enc p)
    (Prepared.encoding_valid p (proj2 (proj2 Hready))) (Prepared.graph p) n s [] s es).
  - constructor.
  - exact Hentry.
  - intro Heq. subst n. contradiction.
  - intros a Hin. contradiction.
  - intro Heq. subst n. contradiction.
  - exact Hpath.
Qed.

Local Lemma choice_singleton {V E} (p : Prepared.t V E) t n v e :
  Prepared.ready p -> Prepared.id_of p n = Some v ->
  choice p t v = Some e ->
  ~ In n (Graph.entries (Prepared.graph p)) /\ candidates p t v = [e].
Proof.
  intros Hready Hn Hchoice. unfold choice, choice_c in Hchoice.
  rewrite Cost.value_bind in Hchoice.
  fold (FinSet.mem positive_encoding v
    (FinSet.of_list positive_encoding (Prepared.entry_ids p))) in Hchoice.
  destruct (FinSet.mem positive_encoding v
    (FinSet.of_list positive_encoding (Prepared.entry_ids p))) eqn:Hentry;
    [discriminate|].
  rewrite Cost.value_bind in Hchoice. fold (candidates p t v) in Hchoice.
  split.
  - intro Hin. apply (entry_ids_spec p n v Hready Hn) in Hin. congruence.
  - destruct (candidates p t v) as [|a [|b rest]]; inversion Hchoice. reflexivity.
Qed.

(** Every selected binding is an incoming edge that dominates its named node. *)
Theorem edge_dominators_sound {V E} (p : Prepared.t V E) t n v e :
  Prepared.ready p -> Dom.exact p t -> Prepared.id_of p n = Some v ->
  Map.get positive_encoding v (edge_dominators p t) = Some e ->
  Graph.target (Prepared.graph p) e = n /\ edge_dominates (Prepared.graph p) e n.
Proof.
  intros Hready Htree Hn Hget. rewrite (index_lookup p t n v Hready Hn) in Hget.
  destruct (choice_singleton p t n v e Hready Hn Hget) as [Hnot Hsingle].
  assert (Hcandidate : In e (candidates p t v)) by (rewrite Hsingle; now left).
  apply (candidates_exact p t n v e Hready Htree Hn) in Hcandidate.
  split; [exact (proj1 (proj2 Hcandidate))|].
  intros s es Hentry Hpath.
  destruct (first_arrival p n s es Hready Hnot Hentry Hpath) as [a [Ha Hcandidate']].
  apply (candidates_exact p t n v a Hready Htree Hn) in Hcandidate'.
  rewrite Hsingle in Hcandidate'. destruct Hcandidate' as [<-|Hfalse];
    [exact Ha|contradiction].
Qed.

Local Lemma admits_blocked d v :
  Scope.admits (Reach.blocked d) v = true <-> v <> d.
Proof.
  rewrite Scope.admits_equation. cbn [Reach.blocked Scope.blocked Scope.within].
  rewrite andb_true_r, negb_true_iff, <- not_true_iff_false.
  rewrite FinSet.mem_add by apply FinSet.wf_empty.
  rewrite FinSet.mem_empty, orb_false_r, (eqb_true_iff _ positive_encoding_laws).
  reflexivity.
Qed.

Local Lemma id_injective {V E} (p : Prepared.t V E) a b i :
  Prepared.laws p -> Prepared.id_of p a = Some i -> Prepared.id_of p b = Some i -> a = b.
Proof.
  intros Hp Ha Hb.
  pose proof (Prepared.name_of_id_of p a i Hp Ha).
  pose proof (Prepared.name_of_id_of p b i Hp Hb). congruence.
Qed.

Local Lemma lower_avoiding {V E} (p : Prepared.t V E) d block i es j :
  Prepared.laws p -> Prepared.id_of p d = Some block ->
  Search.scoped_path p (Reach.blocked block) i es j ->
  forall a b, Prepared.id_of p a = Some i -> Prepared.id_of p b = Some j ->
    path (Prepared.graph p) a es b /\ d <> a /\
      forall e, In e es -> Graph.target (Prepared.graph p) e <> d.
Proof.
  intros Hp Hd Hpath.
  induction Hpath as [v Hv Hfree|u e v rest z Hu Hfree Harc Hpath IH];
    intros a b Ha Hb.
  - assert (a = b) by (eapply id_injective; eauto). subst b.
    apply admits_blocked in Hfree.
    split; [constructor|]. split.
    + intro Heq. subst d. congruence.
    + intros e Hin. contradiction.
  - destruct Harc as [x [y [Hx [Hix [Hiy [Hs [Ht He]]]]]]].
    assert (a = x) by (eapply id_injective; eauto). subst a.
    destruct (IH y b Hiy Hb) as [Htail [Hdy Htargets]].
    apply admits_blocked in Hfree.
    split.
    + rewrite <- Hs. constructor; [now rewrite Hs|now rewrite Ht].
    + split.
      * intro Heq. subst d. congruence.
      * intros edge [<-|Hin]; [rewrite Ht; congruence|now apply Htargets].
Qed.

Local Lemma nondominated_path {V E} (p : Prepared.t V E) n v s u :
  Prepared.ready p -> Prepared.id_of p n = Some v -> Prepared.id_of p s = Some u ->
  ~ dominates (Prepared.graph p) n s ->
  exists root es, In root (Graph.entries (Prepared.graph p)) /\
    path (Prepared.graph p) root es s /\
    forall e, In e es -> Graph.target (Prepared.graph p) e <> n.
Proof.
  intros Hready Hn Hs Hnot.
  assert (Hmem : FinSet.mem positive_encoding u
    (Reach.set p (Reach.blocked v) (Prepared.entry_ids p)) = true).
  { destruct (FinSet.mem positive_encoding u
      (Reach.set p (Reach.blocked v) (Prepared.entry_ids p))) eqn:Hmem; [reflexivity|].
    exfalso. apply Hnot. now apply (Reach.avoiding p n s v u Hready Hn Hs). }
  apply (Reach.exact p _ _ u Hready) in Hmem.
  destruct Hmem as [r [es [Hr Hpath]]].
  apply (Prepared.entry_ids_spec p r (proj2 (proj2 Hready))) in Hr.
  destruct Hr as [root [Hentry Hroot]].
  destruct (lower_avoiding p n v r es u (proj2 (proj2 Hready)) Hn Hpath
    root s Hroot Hs) as [Horiginal [_ Hfree]].
  exists root, es. auto.
Qed.

Local Lemma candidate_unique {V E} (p : Prepared.t V E) t n v e a :
  Prepared.ready p -> Dom.exact p t -> Prepared.id_of p n = Some v ->
  edge_dominates (Prepared.graph p) e n -> Graph.target (Prepared.graph p) e = n ->
  In a (candidates p t v) -> a = e.
Proof.
  intros Hready Htree Hn Hdom Het Ha.
  apply (candidates_exact p t n v a Hready Htree Hn) in Ha.
  destruct Ha as [Ha [Hat [Hreach Hnot]]].
  destruct (proj1 (Prepared.ids_domain p (proj2 (proj2 Hready)) _)
    (reachable_in_nodes _ _ (proj1 Hready) Hreach)) as [u Hu].
  destruct (nondominated_path p n v (Graph.source (Prepared.graph p) a) u
    Hready Hn Hu Hnot) as [s [es [Hs [Hpath Hfree]]]].
  pose proof (path_snoc _ s es _ a Hpath eq_refl Ha) as Hfull.
  rewrite Hat in Hfull.
  specialize (Hdom s (es ++ [a]) Hs Hfull).
  apply in_app_iff in Hdom. destruct Hdom as [Hin|[Heq|Hfalse]].
  - exfalso. exact (Hfree e Hin Het).
  - exact Heq.
  - contradiction.
Qed.

Local Lemma selected_nodup {E} (keep : E * positive -> bool) es :
  NoDup (map fst es) -> NoDup (map fst (filter keep es)).
Proof.
  induction es as [|[e u] rest IH]; intro Hnodup; cbn [filter map]; [constructor|].
  inversion Hnodup as [|head tail Hfresh Hrest]; subst.
  destruct (keep (e, u)); [|now apply IH].
  cbn [map]. constructor; [|now apply IH].
  intro Hin. apply Hfresh.
  apply in_map_iff in Hin. destruct Hin as [edge [Heq Hin]].
  apply filter_In in Hin. apply in_map_iff. exists edge. tauto.
Qed.

(** On reachable named nodes the selected binding is exactly a dominating incoming edge. *)
Theorem edge_dominators_exact {V E} (p : Prepared.t V E) t n v e :
  Prepared.ready p -> Dom.exact p t -> Prepared.id_of p n = Some v ->
  reachable (Prepared.graph p) n ->
  (Map.get positive_encoding v (edge_dominators p t) = Some e <->
    Graph.target (Prepared.graph p) e = n /\ edge_dominates (Prepared.graph p) e n).
Proof.
  intros Hready Htree Hn Hreach. split.
  - now apply edge_dominators_sound.
  - intros [Ht Hdom].
    assert (Hnot : ~ In n (Graph.entries (Prepared.graph p))).
    { intro Hentry. exact (Hdom n [] Hentry (path_nil n)). }
    apply reachable_iff_path in Hreach. destruct Hreach as [s [es [Hs Hpath]]].
    destruct (first_arrival p n s es Hready Hnot Hs Hpath) as [a [_ Ha]].
    apply (candidates_exact p t n v a Hready Htree Hn) in Ha.
    assert (Hae : a = e) by (eapply candidate_unique; eassumption). subst a.
    assert (Huniq : forall a, In a (candidates p t v) -> a = e).
    { intros a Hin. eapply candidate_unique; eassumption. }
    assert (Hnodup : NoDup (candidates p t v)).
    { rewrite candidates_equation. apply selected_nodup.
      exact (Prepared.pred_nodup p (proj2 (proj2 Hready)) v). }
    assert (Hsingle : candidates p t v = [e]).
    { destruct (candidates p t v) as [|a rest]; [contradiction|].
      assert (a = e) by (apply Huniq; now left). subst a.
      inversion Hnodup as [|head tail Hfresh Hrest]; subst.
      destruct rest as [|b rest]; [reflexivity|].
      exfalso. apply Hfresh.
      assert (b = e) by (apply Huniq; right; now left). subst b. now left. }
    rewrite (index_lookup p t n v Hready Hn).
    unfold choice, choice_c. rewrite Cost.value_bind.
    fold (FinSet.mem positive_encoding v
      (FinSet.of_list positive_encoding (Prepared.entry_ids p))).
    assert (Hentry : FinSet.mem positive_encoding v
      (FinSet.of_list positive_encoding (Prepared.entry_ids p)) = false).
    { apply Bool.not_true_iff_false. now rewrite (entry_ids_spec p n v Hready Hn). }
    rewrite Hentry, Cost.value_bind. fold (candidates p t v). now rewrite Hsingle.
Qed.

End FrontierEdge.
