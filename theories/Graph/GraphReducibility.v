(** * Reducibility checks on actual search events

    One search visitor checks dominance for every actual Back occurrence.
    For example, the two-entry cycle fails because neither cycle entry dominates the other.
    Builds on: GraphSearch, GraphDomSpec and GraphCheckDom. *)

From Stdlib Require Import List Bool PArith Arith Lia Permutation Relation_Operators.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearchSpec GraphSearch
  GraphSearchExact GraphSearchOrder GraphSearchInvariant GraphDomSpec GraphHierSpec GraphCheckDom
  GraphReach GraphHierFacts GraphHierCycles GraphTarjanLow.
Import List.ListNotations Cost.Notations.

Module Reducibility.

(** Dominance queries retain all four optional interval lookups and return false on missing ranks. *)
Definition dominates_c (t : Dom.tree) d n :=
  let* a := Map.get_c positive_encoding d (Dom.tin t) in
  let* b := Map.get_c positive_encoding n (Dom.tin t) in
  let* c := Map.get_c positive_encoding n (Dom.tout t) in
  let* e := Map.get_c positive_encoding d (Dom.tout t) in
  Cost.ret
    (match a, b, c, e with
    | Some a, Some b, Some c, Some e => (Pos.leb a b && Pos.leb c e)%bool
    | _, _, _, _ => false
    end).

Definition dominates t d n := Cost.value (dominates_c t d n).

(** The interval query exposes missing observations without substituting a rank. *)
Theorem dominates_equation t d n :
  dominates t d n =
  match Map.get positive_encoding d (Dom.tin t),
      Map.get positive_encoding n (Dom.tin t),
      Map.get positive_encoding n (Dom.tout t),
      Map.get positive_encoding d (Dom.tout t) with
  | Some a, Some b, Some c, Some e => (Pos.leb a b && Pos.leb c e)%bool
  | _, _, _, _ => false
  end.
Proof.
  unfold dominates, dominates_c. rewrite !Cost.value_bind, Cost.value_ret. reflexivity.
Qed.

(** Exact dominator numbering makes the charged interval query reflect semantic dominance. *)
Theorem dominates_correct {V E} (p : Prepared.t V E) t n d v u :
  Prepared.ready p -> Dom.exact p t ->
  reachable (Prepared.graph p) n -> reachable (Prepared.graph p) d ->
  Prepared.id_of p n = Some v -> Prepared.id_of p d = Some u ->
  (dominates t u v = true <-> GraphDomSpec.dominates (Prepared.graph p) d n).
Proof.
  intros Hready Htree Hn Hd Hv Hu.
  destruct (Dom.numbering p t Htree n d v u Hn Hd Hv Hu)
    as [a [b [c [e [Ha [Hb [Hc [He Hnumber]]]]]]]].
  rewrite dominates_equation, Ha, Hb, Hc, He, andb_true_iff, !Pos.leb_le, Hnumber.
  exact (DomCheck.ancestry_spec p t n d v u Hready Htree Hn Hv Hu).
Qed.

Definition edge_c t u v k state :=
  match k with
  | Search.Back =>
    let* back := dominates_c t v u in Cost.ret (state && back)%bool
  | _ => Cost.ret state
  end.

Definition visitor {E} t : Visitor.t E bool :=
  Visitor.Make (fun _ _ state => Cost.ret state)
    (fun _ => edge_c t) (fun _ _ state => Cost.ret state).

(** Event dispatch tests only Back occurrences and leaves all other notifications unchanged. *)
Theorem visitor_equation {E} t (ev : Search.event E) state :
  Visitor.apply (visitor t) ev state =
  match ev with
  | Search.Edge _ u v Search.Back => (state && dominates t v u)%bool
  | _ => state
  end.
Proof.
  destruct ev as [v via|e u v [| | |]|v parent]; reflexivity.
Qed.

(** Reducibility computation runs the shared engine once with its Boolean checking visitor. *)
Definition test_c {V E} (p : Prepared.t V E) t :=
  let* answer := SearchRun.run_c p (visitor t) (Scope.Make FinSet.empty None)
    (Prepared.entry_ids p) true in
  Cost.ret (snd answer).

Definition test {V E} (p : Prepared.t V E) t := Cost.value (test_c p t).

Definition passes {E} t (ev : Search.event E) :=
  match ev with
  | Search.Edge _ u v Search.Back => dominates t v u
  | _ => true
  end.

Local Lemma visitor_passes {E} t (ev : Search.event E) state :
  Visitor.apply (visitor t) ev state = (state && passes t ev)%bool.
Proof.
  rewrite visitor_equation.
  destruct ev as [v via|e u v [| | |]|v parent]; cbn [passes];
    now rewrite ?andb_true_r.
Qed.

Local Lemma events_pass {E} t (evs : list (Search.event E)) state :
  SearchRun.apply_events (visitor t) evs state = true <->
    state = true /\ Forall (fun ev => passes t ev = true) evs.
Proof.
  revert state. induction evs as [|ev rest IH]; intro state.
  - rewrite SearchRun.apply_events_nil. split; [intro Hstate; split|intros [Hstate _]];
      auto using Forall_nil.
  - rewrite SearchRun.apply_events_cons, IH, visitor_passes, andb_true_iff, Forall_cons_iff.
    tauto.
Qed.

(** Acceptance is exactly successful dominance testing of every actual Back event in the one run. *)
Theorem test_events {V E} (p : Prepared.t V E) t :
  test p t = true <->
  forall e u v,
    In (Search.Edge e u v Search.Back)
      (SearchRun.events p (Scope.Make FinSet.empty None) (Prepared.entry_ids p)) ->
    dominates t v u = true.
Proof.
  unfold test, test_c. rewrite Cost.value_bind, SearchRun.run_events.
  rewrite Cost.value_ret. cbn [snd].
  rewrite events_pass, Forall_forall. split.
  - intros [_ Hall] e u v Hin. exact (Hall (Search.Edge e u v Search.Back) Hin).
  - intro Hback. split; [reflexivity|].
    intros ev Hin. destruct ev as [v via|e u v [| | |]|v parent];
      try reflexivity.
    exact (Hback e u v Hin).
Qed.

Local Lemma id_unique {V E} (p : Prepared.t V E) a b i :
  Prepared.ready p -> Prepared.id_of p a = Some i -> Prepared.id_of p b = Some i -> a = b.
Proof.
  intros Hready Ha Hb.
  pose proof (Prepared.name_of_id_of p a i (proj2 (proj2 Hready)) Ha).
  pose proof (Prepared.name_of_id_of p b i (proj2 (proj2 Hready)) Hb). congruence.
Qed.

Local Lemma path_original {V E} (p : Prepared.t V E) scope u es v :
  Prepared.ready p -> Search.scoped_path p scope u es v ->
  forall a b, Prepared.id_of p a = Some u -> Prepared.id_of p b = Some v ->
    path (Prepared.graph p) a es b.
Proof.
  intros Hready Hpath.
  induction Hpath as [v Hv Ha|u e v es z Hu Ha Harc Htail IH]; intros a b Hia Hib.
  - assert (a = b) by (exact (id_unique p a b v Hready Hia Hib)). subst b. constructor.
  - destruct Harc as [source [target [Hsource [His [Hit [Hse [Hte Hedge]]]]]]].
    assert (Hsame : source = a) by (exact (id_unique p source a u Hready His Hia)).
    rewrite Hsame in Hse, Hedge.
    rewrite <- Hse. apply path_cons.
    + now rewrite Hse.
    + rewrite Hte. exact (IH target b Hit Hib).
Qed.

Local Lemma path_ids {V E} (p : Prepared.t V E) a es b :
  Prepared.ready p -> path (Prepared.graph p) a es b ->
  In a (Graph.nodes (Prepared.graph p)) ->
  forall u v, Prepared.id_of p a = Some u -> Prepared.id_of p b = Some v ->
    Search.scoped_path p Reach.unrestricted u es v.
Proof.
  intros Hready Hpath.
  induction Hpath as [a|e es z Hedge Htail IH]; intros Hlisted u v Hu Hv.
  - rewrite Hu in Hv. inversion Hv; subst v.
    apply Search.scoped_nil; [now exists a|apply Reach.admits_unrestricted].
  - assert (Htarget : In (Graph.target (Prepared.graph p) e)
      (Graph.nodes (Prepared.graph p))).
    { exact (out_target_in (proj1 Hready) _ e Hlisted Hedge). }
    destruct (proj1 (Prepared.ids_domain p (proj2 (proj2 Hready)) _) Htarget) as [w Hw].
    eapply Search.scoped_cons with (v := w).
    + exists (Graph.source (Prepared.graph p) e). auto.
    + apply Reach.admits_unrestricted.
    + exists (Graph.source (Prepared.graph p) e), (Graph.target (Prepared.graph p) e).
      repeat split; try reflexivity; assumption.
    + exact (IH Htarget w v Hw Hv).
Qed.

Local Lemma reachable_ids {V E} (p : Prepared.t V E) n i :
  Prepared.ready p -> Prepared.id_of p n = Some i ->
  (Search.scoped_reachable p Reach.unrestricted (Prepared.entry_ids p) i <->
    reachable (Prepared.graph p) n).
Proof.
  intros Hready Hi.
  pose proof (Reach.entries_exact p n i Hready Hi) as Hreach.
  rewrite Reach.exact in Hreach by exact Hready. exact Hreach.
Qed.

Local Lemma arc_source {V E} (p : Prepared.t V E) u e v :
  Prepared.arc p u e v -> Prepared.id_of p (Graph.source (Prepared.graph p) e) = Some u.
Proof.
  intros [a [b [Ha [Hia [Hib [Hsource [Htarget Hedge]]]]]]]. now rewrite Hsource.
Qed.

Local Lemma arc_endpoints {V E} (p : Prepared.t V E) u e v a b :
  Prepared.arc p u e v -> Prepared.arc p a e b -> u = a /\ v = b.
Proof.
  intros Hfirst Hlast.
  pose proof (arc_source p u e v Hfirst). pose proof (arc_source p a e b Hlast).
  pose proof (HierCycles.arc_target p u e v Hfirst).
  pose proof (HierCycles.arc_target p a e b Hlast). split; congruence.
Qed.

Local Lemma path_edge {V E} (p : Prepared.t V E) scope u es v e :
  Search.scoped_path p scope u es v -> In e es -> exists a b, Prepared.arc p a e b.
Proof.
  intro Hpath.
  induction Hpath as [v Hv Ha|u edge v es z Hu Ha Harc Htail IH]; intro Hin.
  - contradiction.
  - destruct Hin as [<-|Hin]; [now exists u, v|exact (IH Hin)].
Qed.

Local Lemma ancestor_member {V E} (p : Prepared.t V E) scope roots r u v :
  Search.exact p scope roots r -> Search.ancestor r u v ->
    In u (Search.preorder r) -> In v (Search.preorder r).
Proof.
  intros Hexact Hancestor.
  induction Hancestor as [u v [e Hparent]|u|u middle v Hfirst IHfirst Hlast IHlast]; intro Hu.
  - exact (proj2 (proj2 (Search.parent_edge_valid _ _ _ _ Hexact v e u Hparent))).
  - exact Hu.
  - exact (IHlast (IHfirst Hu)).
Qed.

Local Lemma root_ancestor {V E} (p : Prepared.t V E) scope roots r v :
  Search.exact p scope roots r -> In v (Search.preorder r) ->
  exists root, In root roots /\ In root (Search.preorder r) /\ Search.ancestor r root v.
Proof.
  intros Hexact. revert v.
  refine (well_founded_induction (Search.parent_finite _ _ _ _ Hexact)
    (fun v => In v (Search.preorder r) ->
      exists root, In root roots /\ In root (Search.preorder r) /\ Search.ancestor r root v) _).
  intros v IH Hv. destruct (Map.get positive_encoding v (Search.parent_edge r))
    as [[e u]|] eqn:Hparent.
  - destruct (Search.parent_edge_valid _ _ _ _ Hexact v e u Hparent) as [_ [Hu Hvv]].
    destruct (IH u (ex_intro _ e eq_refl) Hu) as [root [Hroot [Hpre Hanc]]].
    exists root. split; [exact Hroot|]. split; [exact Hpre|].
    eapply rt_trans; [exact Hanc|apply rt_step; now exists e].
  - exists v. split; [exact (Search.parent_roots _ _ _ _ Hexact v Hv Hparent)|].
    split; [exact Hv|apply rt_refl].
Qed.

Local Lemma ancestor_path {V E} (p : Prepared.t V E) scope roots r u v :
  Search.exact p scope roots r -> Search.ancestor r u v ->
  In u (Search.preorder r) -> In v (Search.preorder r) ->
  exists es, Search.scoped_path p scope u es v /\
    forall a e b, In e es -> Prepared.arc p a e b ->
      Map.get positive_encoding b (Search.parent_edge r) = Some (e, a).
Proof.
  intros Hexact Hancestor.
  induction Hancestor as [u v [edge Hparent]|u|
    u middle v Hfirst IHfirst Hlast IHlast]; intros Hu Hv.
  - destruct (Search.parent_edge_valid _ _ _ _ Hexact v edge u Hparent) as [Harc _].
    destruct (SearchOrder.recorded_admitted p scope roots r u Hexact Hu) as [Huv Hua].
    destruct (SearchOrder.recorded_admitted p scope roots r v Hexact Hv) as [Hvv Hva].
    exists [edge]. split.
    + eapply Search.scoped_cons; [exact Huv|exact Hua|exact Harc|].
      now apply Search.scoped_nil.
    + intros a e b [<-|Hfalse] Hab; [|contradiction].
      destruct (arc_endpoints p u edge v a b Harc Hab) as [<- <-]. exact Hparent.
  - exists []. split.
    + destruct (SearchOrder.recorded_admitted p scope roots r u Hexact Hu).
      now apply Search.scoped_nil.
    + intros a e b Hfalse. contradiction.
  - assert (Hmiddle : In middle (Search.preorder r)) by
      (exact (ancestor_member p scope roots r u middle Hexact Hfirst Hu)).
    destruct (IHfirst Hu Hmiddle) as [first [Hpathfirst Htreefirst]].
    destruct (IHlast Hmiddle Hv) as [last [Hpathlast Htreelast]].
    exists (first ++ last). split; [eapply TarjanLow.path_append; eassumption|].
    intros a e b Hin Harc. apply in_app_iff in Hin.
    destruct Hin as [Hin|Hin]; [exact (Htreefirst a e b Hin Harc)|exact (Htreelast a e b Hin Harc)].
Qed.

Local Lemma tree_path_ancestors {V E} (p : Prepared.t V E) scope r u es v :
  Search.scoped_path p scope u es v ->
  (forall a e b, In e es -> Prepared.arc p a e b ->
    Map.get positive_encoding b (Search.parent_edge r) = Some (e, a)) ->
  Search.ancestor r u v /\
  forall a e b, In e es -> Prepared.arc p a e b -> Search.ancestor r b v.
Proof.
  intro Hpath.
  induction Hpath as [v Hv Ha|u edge v es z Hu Ha Harc Htail IH]; intro Htree.
  - split; [apply rt_refl|intros a e b Hfalse; contradiction].
  - destruct (IH ltac:(intros a e b Hin Hab; apply Htree; [now right|exact Hab]))
      as [Hanc Htargets]. split.
    + eapply rt_trans; [apply rt_step; exists edge; apply Htree; [now left|exact Harc]|exact Hanc].
    + intros a e b [<-|Hin] Hab.
      * destruct (arc_endpoints p u edge v a b Harc Hab) as [<- <-]. exact Hanc.
      * exact (Htargets a e b Hin Hab).
Qed.

Local Lemma dominance_ancestor {V E} (p : Prepared.t V E) n d v u :
  Prepared.ready p -> reachable (Prepared.graph p) n ->
  Prepared.id_of p n = Some v -> Prepared.id_of p d = Some u ->
  GraphDomSpec.dominates (Prepared.graph p) d n ->
  Search.ancestor (SearchRun.dfs p Reach.unrestricted (Prepared.entry_ids p)) u v.
Proof.
  intros Hready Hreach Hn Hd Hdominates.
  set (r := SearchRun.dfs p Reach.unrestricted (Prepared.entry_ids p)).
  pose proof (SearchExact.dfs_exact p Reach.unrestricted (Prepared.entry_ids p) Hready) as Hexact.
  assert (Hv : In v (Search.preorder r)).
  { apply (Search.pre_complete _ _ _ _ Hexact).
    apply (proj2 (reachable_ids p n v Hready Hn)). exact Hreach. }
  destruct (root_ancestor p Reach.unrestricted _ r v Hexact Hv) as [root [Hroot [Hr Hanc]]].
  destruct (ancestor_path p Reach.unrestricted _ r root v Hexact Hanc Hr Hv)
    as [es [Hpath Htree]].
  destruct (proj1 (Prepared.entry_ids_spec p root (proj2 (proj2 Hready))) Hroot)
    as [start [Hentry Hstart]].
  destruct (Hdominates start es Hentry
    (path_original p Reach.unrestricted root es v Hready Hpath start n Hstart Hn))
    as [Heq|[e [Hin Htarget]]].
  - subst d. rewrite Hd in Hstart. inversion Hstart; subst root. exact Hanc.
  - destruct (path_edge p Reach.unrestricted root es v e Hpath Hin) as [a [b Harc]].
    pose proof (HierCycles.arc_target p a e b Harc) as Hid.
    rewrite Htarget, Hd in Hid. inversion Hid; subst b.
    exact (proj2 (tree_path_ancestors p Reach.unrestricted r root es v Hpath Htree)
      a e u Hin Harc).
Qed.

Local Lemma pre_present {V E} (p : Prepared.t V E) scope roots r v :
  Search.exact p scope roots r -> In v (Search.preorder r) ->
    exists i, Map.get positive_encoding v (Search.pre_num r) = Some i.
Proof.
  intros Hexact Hv. apply In_nth_error in Hv. destruct Hv as [n Hnth].
  exists (Pos.of_succ_nat n). apply (Search.pre_num_index _ _ _ _ Hexact).
  rewrite SuccNat2Pos.id_succ. exact Hnth.
Qed.

Local Lemma ancestor_pre_le {V E} (p : Prepared.t V E) scope roots r u v a b :
  Search.exact p scope roots r -> In u (Search.preorder r) -> In v (Search.preorder r) ->
  Search.ancestor r u v ->
  Map.get positive_encoding u (Search.pre_num r) = Some a ->
  Map.get positive_encoding v (Search.pre_num r) = Some b -> (a <= b)%positive.
Proof.
  intros Hexact Hu Hv Hancestor Ha Hb.
  apply (proj2 (Search.ancestor_iff _ _ _ _ Hexact u v Hu Hv)) in Hancestor.
  destruct Hancestor as [first [last [exit [finish [Hfirst [Hlast [_ [_ [Hle _]]]]]]]]].
  rewrite Ha in Hfirst. rewrite Hb in Hlast. inversion Hfirst; inversion Hlast; subst. exact Hle.
Qed.

Local Lemma selected_not_back {V E} (p : Prepared.t V E) v e u :
  Prepared.ready p ->
  Map.get positive_encoding v
    (Search.parent_edge (SearchRun.dfs p Reach.unrestricted (Prepared.entry_ids p))) = Some (e, u) ->
    ~ back_edge (Prepared.graph p) e.
Proof.
  intros Hready Hparent [_ Hdom].
  set (r := SearchRun.dfs p Reach.unrestricted (Prepared.entry_ids p)) in *.
  pose proof (SearchExact.dfs_exact p Reach.unrestricted (Prepared.entry_ids p) Hready) as Hexact.
  destruct (Search.parent_edge_valid _ _ _ _ Hexact v e u Hparent) as [Harc [Hu Hv]].
  assert (Hreach : reachable (Prepared.graph p) (Graph.source (Prepared.graph p) e)).
  { apply (proj1 (reachable_ids p _ u Hready (arc_source p u e v Harc))).
    apply (Search.pre_complete _ _ _ _ Hexact), Hu. }
  pose proof (dominance_ancestor p _ _ u v Hready Hreach
    (arc_source p u e v Harc) (HierCycles.arc_target p u e v Harc) Hdom) as Hancestor.
  destruct (pre_present p Reach.unrestricted _ r u Hexact Hu) as [a Ha].
  destruct (pre_present p Reach.unrestricted _ r v Hexact Hv) as [b Hb].
  pose proof (SearchOrder.parent_rank p Reach.unrestricted _ r v e u a b Hexact Hparent Ha Hb) as Hlt.
  pose proof (ancestor_pre_le p Reach.unrestricted _ r v u b a Hexact Hv Hu Hancestor Hb Ha) as Hle.
  apply Pos2Nat.inj_lt in Hlt. apply Pos2Nat.inj_le in Hle. lia.
Qed.

Local Lemma before_irrefl {A} (xs : list A) v : NoDup xs -> ~ before xs v v.
Proof.
  intros Hnodup Hbefore. apply SearchInvariant.before_indices in Hbefore.
  destruct Hbefore as [i [j [Hlt [Hi Hj]]]].
  assert (Hbound : i < length xs) by (apply nth_error_Some; rewrite Hi; discriminate).
  pose proof (proj1 (NoDup_nth_error xs) Hnodup i j Hbound ltac:(congruence)). lia.
Qed.

Local Lemma before_trans {A} (xs : list A) u v w :
  NoDup xs -> before xs u v -> before xs v w -> before xs u w.
Proof.
  intros Hnodup Hfirst Hlast. apply SearchInvariant.before_indices in Hfirst, Hlast.
  destruct Hfirst as [i [j [Hij [Hi Hj]]]], Hlast as [k [l [Hkl [Hk Hl]]]].
  assert (Hbound : j < length xs) by (apply nth_error_Some; rewrite Hj; discriminate).
  pose proof (proj1 (NoDup_nth_error xs) Hnodup j k Hbound ltac:(congruence)) as Heq.
  subst k. apply SearchInvariant.before_indices. exists i, l. repeat split; auto; lia.
Qed.

Local Lemma rpo_nodup {V E} (p : Prepared.t V E) scope roots :
  Prepared.ready p -> NoDup (SearchOrder.rpo (SearchRun.dfs p scope roots)).
Proof.
  intro Hready. rewrite SearchOrder.rpo_equation. apply NoDup_rev.
  pose proof (SearchExact.dfs_exact p scope roots Hready) as Hexact.
  exact (Permutation_NoDup (Search.post_perm _ _ _ _ Hexact)
    (Search.pre_nodup _ _ _ _ Hexact)).
Qed.

Local Lemma path_order_or_retreat {V E} (p : Prepared.t V E) scope roots u es v :
  Prepared.ready p -> Search.scoped_reachable p scope roots u ->
  Search.scoped_path p scope u es v ->
  (es = [] \/ before (SearchOrder.rpo (SearchRun.dfs p scope roots)) u v) \/
  exists a e b, In e es /\ Search.scoped_reachable p scope roots a /\
    Prepared.arc p a e b /\ Search.ancestor (SearchRun.dfs p scope roots) b a.
Proof.
  intros Hready Hreach Hpath. revert Hreach.
  induction Hpath as [v Hv Ha|u edge v es z Hu Ha Harc Htail IH]; intro Hreach.
  - left. now left.
  - assert (Hallowed : Scope.admits scope v = true) by (destruct Htail; assumption).
    assert (Hpre : In u (Search.preorder (SearchRun.dfs p scope roots))).
    { apply (Search.pre_complete _ _ _ _ (SearchExact.dfs_exact p scope roots Hready)), Hreach. }
    destruct (SearchOrder.rpo_edge_spec p scope roots u edge v Hready Hpre Harc Hallowed)
      as [Hforward|Hretreat].
    + destruct (IH (HierFacts.reachable_step p scope roots u edge v (proj1 Hready)
        Hreach Harc Hallowed)) as [[Hnil|Hbefore]|[a [e [b [Hin Hfacts]]]]].
      * subst es. inversion Htail; subst. left. now right.
      * left. right. exact (before_trans _ u v z (rpo_nodup p scope roots Hready)
          Hforward Hbefore).
      * right. exists a, e, b. split; [now right|exact Hfacts].
    + right. exists u, edge, v. split; [now left|]. auto.
Qed.

Local Lemma cycle_retreat {V E} (p : Prepared.t V E) scope roots v es :
  Prepared.ready p -> Search.scoped_reachable p scope roots v ->
  Search.scoped_path p scope v es v -> es <> [] ->
  exists a e b, In e es /\ Search.scoped_reachable p scope roots a /\
    Prepared.arc p a e b /\ Search.ancestor (SearchRun.dfs p scope roots) b a.
Proof.
  intros Hready Hreach Hcycle Hnonempty.
  destruct (path_order_or_retreat p scope roots v es v Hready Hreach Hcycle)
    as [[Hnil|Hbefore]|Hretreat].
  - contradiction.
  - exfalso. exact (before_irrefl _ v (rpo_nodup p scope roots Hready) Hbefore).
  - exact Hretreat.
Qed.

(** Semantic reducibility is equivalent to dominance back edges at every reachable DFS retreat. *)
Theorem reducible_iff_retreating_back {V E} (p : Prepared.t V E) :
  Prepared.ready p ->
  (reducible (Prepared.graph p) <->
    forall u e v, Prepared.arc p u e v ->
    Search.scoped_reachable p Reach.unrestricted (Prepared.entry_ids p) u ->
    Search.ancestor (SearchRun.dfs p Reach.unrestricted (Prepared.entry_ids p)) v u ->
      back_edge (Prepared.graph p) e).
Proof.
  intro Hready. split.
  - intros Hreducible u e v Harc Hreach Hancestor.
    set (r := SearchRun.dfs p Reach.unrestricted (Prepared.entry_ids p)).
    pose proof (SearchExact.dfs_exact p Reach.unrestricted (Prepared.entry_ids p) Hready) as Hexact.
    assert (Hu : In u (Search.preorder r)) by
      (apply (Search.pre_complete _ _ _ _ Hexact); exact Hreach).
    assert (Htarget : Search.scoped_reachable p Reach.unrestricted (Prepared.entry_ids p) v).
    { apply (HierFacts.reachable_step p Reach.unrestricted _ u e v (proj1 Hready)
        Hreach Harc), Reach.admits_unrestricted. }
    assert (Hv : In v (Search.preorder r)) by
      (apply (Search.pre_complete _ _ _ _ Hexact); exact Htarget).
    destruct (ancestor_path p Reach.unrestricted _ r v u Hexact Hancestor Hv Hu)
      as [es [Hpath Htree]].
    assert (Hcycle : Search.scoped_path p Reach.unrestricted v (es ++ [e]) v).
    { eapply TarjanLow.path_append; [exact Hpath|].
      destruct (SearchOrder.recorded_admitted p Reach.unrestricted _ r u Hexact Hu) as [Huv Hua].
      destruct (SearchOrder.recorded_admitted p Reach.unrestricted _ r v Hexact Hv) as [Hvv Hva].
      eapply Search.scoped_cons; [exact Huv|exact Hua|exact Harc|].
      now apply Search.scoped_nil. }
    assert (Hlisted : In (Graph.target (Prepared.graph p) e) (Graph.nodes (Prepared.graph p))).
    { destruct Harc as [a [b [Ha [Hia [Hib [Hsource [Htargete Hedge]]]]]]].
      exact (out_target_in (proj1 Hready) a e Ha Hedge). }
    destruct (Hreducible _ _ Hlisted
      (path_original p Reach.unrestricted v (es ++ [e]) v Hready Hcycle _ _
        (HierCycles.arc_target p u e v Harc) (HierCycles.arc_target p u e v Harc))
      ltac:(intro Hnil; apply app_eq_nil in Hnil; destruct Hnil as [_ Hnil]; discriminate))
      as [edge [Hin Hback]].
    apply in_app_iff in Hin. destruct Hin as [Hin|[Heq|Hfalse]].
    + destruct (path_edge p Reach.unrestricted v es u edge Hpath Hin) as [a [b Hab]].
      exfalso. exact (selected_not_back p b edge a Hready (Htree a edge b Hin Hab) Hback).
    + now subst edge.
    + contradiction.
  - intros Hback n es Hlisted Hpath Hnonempty.
    destruct (proj1 (Prepared.ids_domain p (proj2 (proj2 Hready)) n) Hlisted) as [i Hi].
    destruct (FinSet.mem positive_encoding i
      (Reach.set p Reach.unrestricted (Prepared.entry_ids p))) eqn:Hmem.
    + pose proof (proj1 (Reach.exact p Reach.unrestricted (Prepared.entry_ids p) i Hready) Hmem)
        as Hreach.
      destruct (cycle_retreat p Reach.unrestricted (Prepared.entry_ids p) i es Hready Hreach
        (path_ids p n es n Hready Hpath Hlisted i i Hi Hi) Hnonempty)
        as [u [edge [v [Hin [Hsource [Harc Hancestor]]]]]].
      exists edge. split; [exact Hin|exact (Hback u edge v Harc Hsource Hancestor)].
    + assert (Hunreachable : ~ reachable (Prepared.graph p) n).
      { intro Hreach. apply (proj2 (Reach.entries_exact p n i Hready Hi)) in Hreach. congruence. }
      destruct es as [|e rest]; [contradiction|].
      inversion Hpath as [|edge tail z Hedge Htail]; subst.
      exists e. split; [now left|]. split; [exact Hedge|].
      intros start prefix Hentry Hprefix. exfalso. apply Hunreachable.
      apply reachable_iff_path. exists start, prefix. auto.
Qed.

Local Lemma retreat_event {V E} (p : Prepared.t V E) scope roots u e v :
  Prepared.ready p ->
  In u (Search.preorder (SearchRun.dfs p scope roots)) ->
  Prepared.arc p u e v -> Scope.admits scope v = true ->
  Search.ancestor (SearchRun.dfs p scope roots) v u ->
    In (Search.Edge e u v Search.Back) (SearchRun.events p scope roots).
Proof.
  intros Hready Hu Harc Hallowed Hancestor.
  set (r := SearchRun.dfs p scope roots) in *.
  pose proof (SearchExact.dfs_exact p scope roots Hready) as Hexact.
  assert (Hv : In v (Search.preorder r)).
  { apply (Search.pre_complete _ _ _ _ Hexact).
    exact (HierFacts.reachable_step p scope roots u e v (proj1 Hready)
      (proj1 (Search.pre_complete _ _ _ _ Hexact u) Hu) Harc Hallowed). }
  pose proof (proj2 (Search.ancestor_iff _ _ _ _ Hexact v u Hv Hu) Hancestor) as Hinterval.
  destruct Hinterval as [a [b [c [d [Hpre_v [Hpre_u [Hpost_u [Hpost_v [Hpre Hpost]]]]]]]]].
  destruct (SearchOrder.edge_event_complete p scope roots u e v Hready Hu Harc Hallowed)
    as [kind Hevent].
  destruct (SearchOrder.classify_spec p scope roots e u v kind Hready Hevent)
    as [_ [_ [_ Hkind]]].
  destruct kind.
  - pose proof (SearchOrder.parent_rank p scope roots r v e u b a Hexact Hkind Hpre_u Hpre_v)
      as Hlt.
    apply Pos2Nat.inj_lt in Hlt. apply Pos2Nat.inj_le in Hpre. lia.
  - exact Hevent.
  - destruct Hkind as [first [last [exit [finish [Hfirst [Hlast [Hlt Hmore]]]]]]].
    rewrite Hpre_u in Hfirst. rewrite Hpre_v in Hlast.
    injection Hfirst as Hfirst. injection Hlast as Hlast.
    rewrite <- Hfirst, <- Hlast in Hlt.
    apply Pos2Nat.inj_lt in Hlt. apply Pos2Nat.inj_le in Hpre. lia.
  - destruct Hkind as [first [last [exit [finish [Hfirst [Hlast [Hlt [Hexit [Hfinish Hexitlt]]]]]]]]].
    rewrite Hpost_v in Hexit. rewrite Hpost_u in Hfinish.
    injection Hexit as Hexit. injection Hfinish as Hfinish.
    rewrite <- Hexit, <- Hfinish in Hexitlt.
    apply Pos2Nat.inj_lt in Hexitlt. apply Pos2Nat.inj_le in Hpost. lia.
Qed.

Local Lemma arc_out {V E} (p : Prepared.t V E) u e v :
  Prepared.arc p u e v -> In e (Graph.out (Prepared.graph p) (Graph.source (Prepared.graph p) e)).
Proof.
  intros [a [b [Ha [Hia [Hib [Hsource [Htarget Hedge]]]]]]]. now rewrite Hsource.
Qed.

Local Lemma back_bool_spec {V E} (p : Prepared.t V E) t u e v :
  Prepared.ready p -> Dom.exact p t -> Prepared.arc p u e v ->
  Search.scoped_reachable p Reach.unrestricted (Prepared.entry_ids p) u ->
    (dominates t v u = true <-> back_edge (Prepared.graph p) e).
Proof.
  intros Hready Htree Harc Hreach.
  assert (Hsource : reachable (Prepared.graph p) (Graph.source (Prepared.graph p) e)).
  { apply (proj1 (reachable_ids p _ u Hready (arc_source p u e v Harc))). exact Hreach. }
  assert (Htarget : reachable (Prepared.graph p) (Graph.target (Prepared.graph p) e)).
  { exact (reachable_step e Hsource (arc_out p u e v Harc)). }
  pose proof (dominates_correct p t _ _ u v Hready Htree Hsource Htarget
    (arc_source p u e v Harc) (HierCycles.arc_target p u e v Harc)) as Hdominance.
  split.
  - intro Htest. split; [exact (arc_out p u e v Harc)|now apply Hdominance].
  - intros [_ Hdom]. now apply Hdominance.
Qed.

(** An exact dominator tree makes the one-search event test decide the fixed semantic reducibility predicate. *)
Theorem reducible_b_correct {V E} (p : Prepared.t V E) t :
  Prepared.ready p -> Dom.exact p t ->
    (test p t = true <-> reducible (Prepared.graph p)).
Proof.
  intros Hready Htree. rewrite reducible_iff_retreating_back by exact Hready.
  rewrite test_events. split.
  - intros Htest u e v Harc Hreach Hancestor.
    apply (proj1 (back_bool_spec p t u e v Hready Htree Harc Hreach)).
    apply (Htest e u v).
    apply (retreat_event p Reach.unrestricted (Prepared.entry_ids p) u e v Hready).
    + apply (Search.pre_complete _ _ _ _
        (SearchExact.dfs_exact p Reach.unrestricted (Prepared.entry_ids p) Hready)), Hreach.
    + exact Harc.
    + apply Reach.admits_unrestricted.
    + exact Hancestor.
  - intros Hback e u v Hin.
    destruct (SearchOrder.classify_spec p Reach.unrestricted (Prepared.entry_ids p)
      e u v Search.Back Hready Hin) as [Harc [_ [_ [Hancestor Hpre]]]].
    assert (Hreach : Search.scoped_reachable p Reach.unrestricted (Prepared.entry_ids p) u).
    { apply (Search.pre_complete _ _ _ _
        (SearchExact.dfs_exact p Reach.unrestricted (Prepared.entry_ids p) Hready)), Hpre. }
    apply (proj2 (back_bool_spec p t u e v Hready Htree Harc Hreach)).
    exact (Hback u e v Harc Hreach Hancestor).
Qed.

(** Acceptance with an exact supplied dominator tree implies semantic reducibility. *)
Theorem reducible_b_sound {V E} (p : Prepared.t V E) t :
  Prepared.ready p -> Dom.exact p t -> test p t = true -> reducible (Prepared.graph p).
Proof.
  intros Hready Htree Htest. exact (proj1 (reducible_b_correct p t Hready Htree) Htest).
Qed.

End Reducibility.
