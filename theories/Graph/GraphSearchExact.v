(** * Search representation invariants

    Search maintains canonical maps and a duplicate-free discovery list independently of visitors.
    For example, repeated roots cannot insert a second discovery occurrence.
    Builds on: GraphSearch and the public map and set laws. *)

From Stdlib Require Import List Bool PArith Arith Lia Permutation.
From Galois.Cost Require Import CostMonad CostList CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearchSpec GraphSearch.
Import List.ListNotations.

Module SearchExact.
Local Open Scope nat_scope.

(** Representation invariants do not assume semantic readiness or adequate fuel. *)
Record representation {E} (c : SearchRun.core E) : Prop := {
  parents_wf : Map.wf positive_encoding (SearchRun.parents c);
  pre_index_wf : Map.wf positive_encoding (SearchRun.pre_index c);
  post_index_wf : Map.wf positive_encoding (SearchRun.post_index c);
  seen_wf : FinSet.wf positive_encoding (SearchRun.seen c);
  discovered_nodup : NoDup (SearchRun.pre_rev c);
  seen_discovered : forall v,
    FinSet.mem positive_encoding v (SearchRun.seen c) = true <->
      In v (SearchRun.pre_rev c)
}.

Local Lemma initial_representation {E} : representation (@SearchRun.initial E).
Proof.
  constructor; cbn [SearchRun.initial].
  - apply Map.wf_empty.
  - apply Map.wf_empty.
  - apply Map.wf_empty.
  - apply FinSet.wf_empty.
  - constructor.
  - intro v.
    change (FinSet.mem positive_encoding v FinSet.empty = true <-> False).
    rewrite FinSet.mem_empty. split; [discriminate|contradiction].
Qed.

Local Lemma discover_representation {E} (c : SearchRun.core E) v via :
  representation c ->
  FinSet.mem positive_encoding v (SearchRun.seen c) = false ->
  representation (SearchRun.discover v via c).
Proof.
  intros Hrep Hfresh. rewrite SearchRun.discover_equation.
  constructor; cbn [SearchRun.parents SearchRun.pre_index SearchRun.post_index
    SearchRun.seen SearchRun.pre_rev].
  - destruct via; [apply Map.wf_set|]; exact (parents_wf _ Hrep).
  - apply Map.wf_set. exact (pre_index_wf _ Hrep).
  - exact (post_index_wf _ Hrep).
  - apply FinSet.wf_add. exact (seen_wf _ Hrep).
  - constructor; [|exact (discovered_nodup _ Hrep)].
    intro Hin. apply (seen_discovered _ Hrep) in Hin. congruence.
  - intro u. rewrite FinSet.mem_add by exact (seen_wf _ Hrep).
    rewrite orb_true_iff, (seen_discovered _ Hrep).
    rewrite (eqb_true_iff positive_encoding positive_encoding_laws).
    cbn [In]. split; intros [H|H]; auto.
Qed.

Local Lemma finish_representation {E} (c : SearchRun.core E) v :
  representation c -> representation (SearchRun.finish v c).
Proof.
  intro Hrep. rewrite SearchRun.finish_equation.
  destruct Hrep. constructor; cbn; auto using Map.wf_set.
Qed.

(** A Tree event is possible only at a currently white target. *)
Theorem tree_is_white {E} (c : SearchRun.core E) u v :
  SearchRun.edge_kind c u v = Search.Tree <->
    FinSet.mem positive_encoding v (SearchRun.seen c) = false.
Proof.
  unfold SearchRun.edge_kind, SearchRun.edge_kind_c.
  rewrite Cost.value_bind. fold (FinSet.mem positive_encoding v (SearchRun.seen c)).
  destruct (FinSet.mem positive_encoding v (SearchRun.seen c)); [|split; reflexivity].
  rewrite Cost.value_bind. fold (Map.get positive_encoding v (SearchRun.post_index c)).
  destruct (Map.get positive_encoding v (SearchRun.post_index c)).
  - rewrite !Cost.value_bind. fold (Map.get positive_encoding u (SearchRun.pre_index c)).
    fold (Map.get positive_encoding v (SearchRun.pre_index c)).
    destruct (Map.get positive_encoding u (SearchRun.pre_index c)) as [a|];
      destruct (Map.get positive_encoding v (SearchRun.pre_index c)) as [b|];
      cbn [Cost.value Cost.ret]; try destruct (Pos.ltb a b); split; discriminate.
  - split; discriminate.
Qed.

(** Every transition maintains canonical storage and duplicate-free discovery. *)
Theorem transition_representation {V E} (p : Prepared.t V E) scope w :
  representation (snd w) ->
    representation (snd (SearchRun.unwrap (fst (SearchRun.transition p scope w)))).
Proof.
  destruct w as [stack c]. intro Hrep. rewrite SearchRun.step_equation.
  destruct stack as [|[u [|[e v] pending]] rest]; cbn [fst snd SearchRun.unwrap].
  - exact Hrep.
  - now apply finish_representation.
  - destruct (Scope.admits scope v); [|exact Hrep].
    destruct (Prepared.name_of p v); [|exact Hrep].
    destruct (SearchRun.edge_kind c u v) eqn:Hkind; cbn [fst snd SearchRun.unwrap];
      try exact Hrep.
    apply discover_representation; [exact Hrep|]. now apply (tree_is_white c u v).
Qed.

Local Lemma loop_representation {V E} (p : Prepared.t V E) scope n w :
  representation (snd w) -> representation (snd (fst (SearchRun.reference_loop p scope n w))).
Proof.
  revert w. induction n as [|n IH]; intros w Hrep; [exact Hrep|].
  pose proof (transition_representation p scope w Hrep) as Hnext.
  cbn [SearchRun.reference_loop].
  destruct (SearchRun.transition p scope w) as [[w'|w'] evs];
    cbn [fst snd SearchRun.unwrap] in Hnext.
  - specialize (IH w' Hnext).
    destruct (SearchRun.reference_loop p scope n w') as [final later]. exact IH.
  - exact Hnext.
Qed.

Local Lemma root_representation {V E} (p : Prepared.t V E) scope c v :
  representation c -> representation (fst (SearchRun.reference_root p scope c v)).
Proof.
  intro Hrep. unfold SearchRun.reference_root.
  destruct (Scope.admits scope v); [|exact Hrep].
  destruct (FinSet.mem positive_encoding v (SearchRun.seen c)) eqn:Hfresh; [exact Hrep|].
  destruct (Prepared.name_of p v); [|exact Hrep].
  pose proof (loop_representation p scope (Pos.to_nat (Prepared.fuel p))
    ([(v, Prepared.succ_edges p v)], SearchRun.discover v None c)
    (discover_representation c v None Hrep Hfresh)) as Hloop.
  destruct (SearchRun.reference_loop p scope (Pos.to_nat (Prepared.fuel p))
    ([(v, Prepared.succ_edges p v)], SearchRun.discover v None c)) as [w evs].
  exact Hloop.
Qed.

Local Lemma roots_representation {V E} (p : Prepared.t V E) scope roots c :
  representation c -> representation (fst (SearchRun.reference_roots p scope roots c)).
Proof.
  revert c. induction roots as [|v rest IH]; intros c Hrep; [exact Hrep|].
  pose proof (root_representation p scope c v Hrep) as Hroot.
  cbn [SearchRun.reference_roots].
  destruct (SearchRun.reference_root p scope c v) as [c' here].
  specialize (IH c' Hroot).
  destruct (SearchRun.reference_roots p scope rest c') as [final later]. exact IH.
Qed.

(** Every search result has canonical maps, a canonical visited set and unique preorder IDs. *)
Theorem run_representation {V E} (p : Prepared.t V E) scope roots :
  let r := SearchRun.dfs p scope roots in
  Map.wf positive_encoding (Search.parent_edge r) /\
  Map.wf positive_encoding (Search.pre_num r) /\
  Map.wf positive_encoding (Search.post_num r) /\
  FinSet.wf positive_encoding (Search.visited r) /\
  NoDup (Search.preorder r) /\
  forall v, FinSet.mem positive_encoding v (Search.visited r) = true <->
    In v (Search.preorder r).
Proof.
  unfold SearchRun.dfs. rewrite SearchRun.run_equation.
  pose proof (roots_representation p scope roots _ (@initial_representation E)) as Hrep.
  destruct (SearchRun.reference_roots p scope roots SearchRun.initial) as [c evs].
  cbn [fst] in Hrep |- *.
  unfold SearchRun.result, SearchRun.result_c. autorewrite with galois_cost.
  cbn [Search.parent_edge Search.pre_num Search.post_num Search.visited Search.preorder].
  split; [exact (parents_wf _ Hrep)|]. split; [exact (pre_index_wf _ Hrep)|].
  split; [exact (post_index_wf _ Hrep)|]. split; [exact (seen_wf _ Hrep)|].
  split; [apply NoDup_rev; exact (discovered_nodup _ Hrep)|].
  intro v. rewrite (seen_discovered _ Hrep). apply in_rev.
Qed.

(** The work universe contains each successful node-ID lookup in source node order. *)
Definition vertices {V E} (p : Prepared.t V E) :=
  Prepared.present (Prepared.id_of p) (Graph.nodes (Prepared.graph p)).

Local Lemma present_member {A B} (f : A -> option B) xs y :
  In y (Prepared.present f xs) <-> exists x, In x xs /\ f x = Some y.
Proof.
  induction xs as [|x rest IH]; cbn [Prepared.present].
  - split; [contradiction|intros [a [Hfalse _]]; contradiction].
  - destruct (f x) as [z|] eqn:Hx; cbn [In]; rewrite IH.
    + split.
      * intros [<-|[a [Ha Hfind]]]; [exists x; auto|exists a; auto].
      * intros [a [[<-|Ha] Hfind]]; [left; congruence|right; exists a; auto].
    + split.
      * intros [a [Ha Hfind]]. exists a. auto.
      * intros [a [[<-|Ha] Hfind]]; [congruence|exists a; auto].
Qed.

Local Lemma present_nodup {A B} (f : A -> option B) xs :
  NoDup xs -> (forall a b y, f a = Some y -> f b = Some y -> a = b) ->
  NoDup (Prepared.present f xs).
Proof.
  intros Hnodup Hinjective. induction Hnodup as [|x xs Hnot Hnodup IH].
  - constructor.
  - cbn [Prepared.present]. destruct (f x) as [y|] eqn:Hx; [|exact IH].
    constructor; [|exact IH]. rewrite present_member.
    intros [a [Ha Hfind]]. apply Hnot.
    assert (Heq : a = x) by (eapply Hinjective; eassumption). now subst a.
Qed.

(** Valid IDs are precisely the IDs in the finite work universe. *)
Theorem vertices_spec {V E} (p : Prepared.t V E) v :
  In v (vertices p) <-> Prepared.valid_id p v.
Proof.
  unfold vertices, Prepared.valid_id. apply present_member.
Qed.

(** Readiness makes the finite work universe duplicate-free. *)
Theorem vertices_nodup {V E} (p : Prepared.t V E) :
  Prepared.ready p -> NoDup (vertices p).
Proof.
  intros [Hgraph [_ Hlaws]]. unfold vertices.
  apply present_nodup; [exact (nodes_nodup Hgraph)|].
  intros a b i Ha Hb.
  apply (Prepared.ids_inverse p Hlaws) in Ha.
  apply (Prepared.ids_inverse p Hlaws) in Hb. congruence.
Qed.

Definition vertex_work {V E} (p : Prepared.t V E) v :=
  S (length (Prepared.succ_edges p v)).

Definition capacity {V E} (p : Prepared.t V E) :=
  fold_right (fun v n => vertex_work p v + n) 0 (vertices p).

(** The total vertex credit is one frame plus each outgoing occurrence per source node. *)
Theorem capacity_equation {V E} (p : Prepared.t V E) :
  Prepared.ready p ->
    capacity p = length (Graph.nodes (Prepared.graph p)) + edge_count (Prepared.graph p).
Proof.
  intros [_ [_ Hlaws]]. unfold capacity, vertices, vertex_work, edge_count.
  assert (Hsum : forall vs, incl vs (Graph.nodes (Prepared.graph p)) ->
    fold_right (fun v n => S (length (Prepared.succ_edges p v)) + n) 0
      (Prepared.present (Prepared.id_of p) vs) =
      length vs + fold_right (fun v n => length (Graph.out (Prepared.graph p) v) + n) 0 vs).
  { induction vs as [|v rest IH]; intro Hnodes; [reflexivity|].
    destruct (proj1 (Prepared.ids_domain p Hlaws v) (Hnodes v (or_introl eq_refl)))
      as [i Hi].
    cbn [Prepared.present]. rewrite Hi. cbn [fold_right length].
    rewrite IH by (intros x Hx; apply Hnodes; now right).
    pose proof (Prepared.succ_agrees p Hlaws v i Hi) as Hsucc.
    apply (f_equal (@length E)) in Hsucc. rewrite length_map in Hsucc. lia. }
  apply Hsum. intros v Hv. exact Hv.
Qed.

Fixpoint white_work {V E} (p : Prepared.t V E) (todo : list positive)
    (seen : FinSet.t positive) :=
  match todo with
  | [] => 0
  | v :: rest =>
    (if FinSet.mem positive_encoding v seen then 0 else vertex_work p v) +
      white_work p rest seen
  end.

Fixpoint pending_work {E} (stack : list (SearchRun.frame E)) :=
  match stack with
  | [] => 0
  | (_, pending) :: rest => S (length pending) + pending_work rest
  end.

(** White credit pays for every future frame and adjacency occurrence exactly once. *)
Definition work_measure {V E} (p : Prepared.t V E) (w : SearchRun.work E) :=
  pending_work (fst w) + white_work p (vertices p) (SearchRun.seen (snd w)).

Local Lemma white_bound {V E} (p : Prepared.t V E) todo seen :
  white_work p todo seen <= fold_right (fun v n => vertex_work p v + n) 0 todo.
Proof.
  induction todo as [|v rest IH]; cbn [white_work fold_right]; [lia|].
  destruct (FinSet.mem positive_encoding v seen); lia.
Qed.

Local Lemma white_add_absent {V E} (p : Prepared.t V E) todo seen v :
  FinSet.wf positive_encoding seen -> ~ In v todo ->
    white_work p todo (FinSet.add positive_encoding v seen) = white_work p todo seen.
Proof.
  intros Hwf Habsent. induction todo as [|u rest IH]; [reflexivity|].
  cbn [white_work]. rewrite FinSet.mem_add by exact Hwf.
  assert (Hne : eqb positive_encoding u v = false).
  { apply (proj2 (eqb_false_iff positive_encoding positive_encoding_laws u v)).
    intro Heq. apply Habsent. now left. }
  rewrite Hne. cbn [orb]. rewrite IH; [reflexivity|].
  intro Hin. apply Habsent. now right.
Qed.

Local Lemma white_add_present {V E} (p : Prepared.t V E) todo seen v :
  FinSet.wf positive_encoding seen -> NoDup todo -> In v todo ->
  FinSet.mem positive_encoding v seen = false ->
    white_work p todo (FinSet.add positive_encoding v seen) + vertex_work p v =
      white_work p todo seen.
Proof.
  intros Hwf Hnodup. induction Hnodup as [|u rest Hnot Hnodup IH];
    intros Hin Hfresh; [contradiction|].
  cbn [white_work]. destruct Hin as [<-|Hin].
  - rewrite FinSet.mem_add by exact Hwf.
    rewrite eqb_refl, Hfresh. cbn [orb].
    rewrite white_add_absent by assumption. lia.
  - assert (Hne : eqb positive_encoding u v = false).
    { apply (proj2 (eqb_false_iff positive_encoding positive_encoding_laws u v)).
      intro Heq. subst u. contradiction. }
    rewrite FinSet.mem_add by exact Hwf. rewrite Hne. cbn [orb].
    specialize (IH Hin Hfresh).
    destruct (FinSet.mem positive_encoding u seen); lia.
Qed.

(** Every successful inverse lookup is covered by the prepared work universe. *)
Theorem named_in_vertices {V E} (p : Prepared.t V E) i name :
  Prepared.ready p -> Prepared.name_of p i = Some name -> In i (vertices p).
Proof.
  intros [_ [_ Hlaws]] Hname. apply vertices_spec.
  pose proof (Prepared.id_of_name_of p i name Hlaws Hname) as Hi.
  exists name. split; [|exact Hi]. apply (Prepared.ids_domain p Hlaws). now exists i.
Qed.

(** Every continuing stack transition spends one unit of global pending-plus-white credit. *)
Theorem transition_decreases {V E} (p : Prepared.t V E) scope w next evs :
  Prepared.ready p -> representation (snd w) ->
  SearchRun.transition p scope w = (inl next, evs) ->
    work_measure p next < work_measure p w.
Proof.
  intros Hready Hrep Htransition. destruct w as [stack c].
  rewrite SearchRun.step_equation in Htransition.
  destruct stack as [|[u [|[e v] pending]] rest]; [discriminate| |].
  - inversion Htransition; subst next evs.
    unfold work_measure. rewrite SearchRun.finish_equation.
    cbn [fst snd pending_work SearchRun.seen]. lia.
  - destruct (Scope.admits scope v).
    + destruct (Prepared.name_of p v) as [name|] eqn:Hname.
      * destruct (SearchRun.edge_kind c u v) eqn:Hkind;
          inversion Htransition; subst next evs; unfold work_measure;
          cbn [fst snd pending_work length]; try lia.
        rewrite SearchRun.discover_equation. cbn [SearchRun.seen].
        pose proof (white_add_present p (vertices p) (SearchRun.seen c) v
          (seen_wf _ Hrep) (vertices_nodup p Hready)
          (named_in_vertices p v name Hready Hname)
          (proj1 (tree_is_white c u v) Hkind)) as Hwhite.
        unfold vertex_work in Hwhite. lia.
      * inversion Htransition; subst next evs.
        unfold work_measure. cbn [fst snd pending_work length]. lia.
    + inversion Htransition; subst next evs.
      unfold work_measure. cbn [fst snd pending_work length]. lia.
Qed.

(** A stopped stack transition always returns an empty stack. *)
Theorem transition_stops_empty {V E} (p : Prepared.t V E) scope w final evs :
  SearchRun.transition p scope w = (inr final, evs) -> fst final = [].
Proof.
  destruct w as [stack c]. rewrite SearchRun.step_equation.
  destruct stack as [|[u [|[e v] pending]] rest]; [intro H; inversion H; reflexivity|discriminate|].
  destruct (Scope.admits scope v); [|discriminate].
  destruct (Prepared.name_of p v); [|discriminate].
  destruct (SearchRun.edge_kind c u v); discriminate.
Qed.

(** Exhaustion accounts for every spent transition, and stopping returns an empty stack. *)
Theorem runs_work {V E S} (p : Prepared.t V E) (vis : Visitor.t E S) scope n state answer :
  Prepared.ready p -> runs (SearchRun.step_c p vis scope) n state answer ->
  representation (snd (fst state)) ->
    match answer with
    | inl (w, _) =>
      representation (snd w) /\ n + work_measure p w <= work_measure p (fst state)
    | inr (w, _) => representation (snd w) /\ fst w = []
    end.
Proof.
  intros Hready Hrun.
  induction Hrun as [state|n state answer Hstop|n state next answer Hnext Hrun IH];
    intro Hrep.
  - destruct state as [w s]. cbn [fst snd]. auto.
  - destruct state as [w s]. rewrite SearchRun.step_erases in Hstop.
    pose proof (transition_representation p scope w Hrep) as Hnextrep.
    destruct (SearchRun.transition p scope w) as [[w'|w'] evs] eqn:Htransition;
      [discriminate|].
    inversion Hstop; subst answer. split; [exact Hnextrep|].
    eapply transition_stops_empty. exact Htransition.
  - destruct state as [w s]. rewrite SearchRun.step_erases in Hnext.
    pose proof (transition_representation p scope w Hrep) as Hnextrep.
    destruct (SearchRun.transition p scope w) as [[w'|w'] evs] eqn:Htransition;
      [|discriminate].
    inversion Hnext; subst next. specialize (IH Hnextrep).
    destruct answer as [[final s']|[final s']]; [|exact IH].
    destruct IH as [Hfinal Hbound]. split; [exact Hfinal|].
    pose proof (transition_decreases p scope w w' evs Hready Hrep Htransition).
    cbn [fst snd] in *. lia.
Qed.

(** A budget greater than pending-plus-white credit cannot exhaust the binary driver. *)
Theorem loop_adequate {V E S} (p : Prepared.t V E) (vis : Visitor.t E S) scope fuel w s :
  Prepared.ready p -> representation (snd w) ->
  work_measure p w < Pos.to_nat fuel ->
    exists final s',
      Cost.value (iterate (SearchRun.step_c p vis scope) fuel (w, s)) = inr (final, s') /\
      fst final = [] /\ representation (snd final).
Proof.
  intros Hready Hrep Hbudget.
  pose proof (runs_work p vis scope _ _ _ Hready
    (iterate_value (SearchRun.step_c p vis scope) fuel (w, s)) Hrep) as Hrun.
  destruct (Cost.value (iterate (SearchRun.step_c p vis scope) fuel (w, s)))
    as [[final s']|[final s']] eqn:Hanswer.
  - destruct Hrun as [_ Hbound]. cbn [fst] in Hbound. lia.
  - destruct Hrun as [Hfinal Hempty]. exists final, s'. auto.
Qed.

(** Starting a fresh named root transfers its white credit to its actual adjacency frame. *)
Theorem root_work {V E} (p : Prepared.t V E) (c : SearchRun.core E) v name :
  Prepared.ready p -> representation c ->
  Prepared.name_of p v = Some name ->
  FinSet.mem positive_encoding v (SearchRun.seen c) = false ->
    work_measure p ([(v, Prepared.succ_edges p v)], SearchRun.discover v None c) =
      white_work p (vertices p) (SearchRun.seen c).
Proof.
  intros Hready Hrep Hname Hfresh.
  pose proof (white_add_present p (vertices p) (SearchRun.seen c) v
    (seen_wf _ Hrep) (vertices_nodup p Hready)
    (named_in_vertices p v name Hready Hname) Hfresh) as Hwhite.
  unfold work_measure. rewrite SearchRun.discover_equation.
  cbn [fst snd pending_work SearchRun.seen]. unfold vertex_work in Hwhite. lia.
Qed.

(** The prepared fuel is adequate for every fresh root and every visitor, with no visitor premise. *)
Theorem root_loop_adequate {V E S} (p : Prepared.t V E) (vis : Visitor.t E S) scope
    (c : SearchRun.core E) v name s :
  Prepared.ready p -> representation c ->
  Prepared.name_of p v = Some name ->
  FinSet.mem positive_encoding v (SearchRun.seen c) = false ->
    exists final s',
      Cost.value (iterate (SearchRun.step_c p vis scope) (Prepared.fuel p)
        (([(v, Prepared.succ_edges p v)], SearchRun.discover v None c), s)) =
        inr (final, s') /\
      fst final = [] /\ representation (snd final).
Proof.
  intros Hready Hrep Hname Hfresh.
  apply loop_adequate; [exact Hready|now apply discover_representation|].
  rewrite (root_work p c v name Hready Hrep Hname Hfresh).
  pose proof (white_bound p (vertices p) (SearchRun.seen c)) as Hwhite.
  change (white_work p (vertices p) (SearchRun.seen c) <= capacity p) in Hwhite.
  rewrite (capacity_equation p Hready) in Hwhite.
  destruct Hready as [_ [_ Hlaws]]. rewrite (Prepared.fuel_value p Hlaws). lia.
Qed.

(** Every admitted fresh reference root drains its entire stack with the actual prepared budget. *)
Theorem reference_root_drains {V E} (p : Prepared.t V E) scope
    (c : SearchRun.core E) v name :
  Prepared.ready p -> representation c ->
  Prepared.name_of p v = Some name ->
  FinSet.mem positive_encoding v (SearchRun.seen c) = false ->
    fst (fst (SearchRun.reference_loop p scope (Pos.to_nat (Prepared.fuel p))
      ([(v, Prepared.succ_edges p v)], SearchRun.discover v None c))) = [].
Proof.
  intros Hready Hrep Hname Hfresh.
  destruct (root_loop_adequate p (@Visitor.noop E unit) scope c v name tt
    Hready Hrep Hname Hfresh) as [final [s' [Hanswer [Hempty Hfinal]]]].
  pose proof (SearchRun.loop_erases p (@Visitor.noop E unit) scope (Prepared.fuel p)
    ([(v, Prepared.succ_edges p v)], SearchRun.discover v None c) tt) as Herase.
  assert (Heq : (final, s') =
    let '(last, evs) := SearchRun.reference_loop p scope (Pos.to_nat (Prepared.fuel p))
      ([(v, Prepared.succ_edges p v)], SearchRun.discover v None c) in
    (last, SearchRun.apply_events (@Visitor.noop E unit) evs tt)).
  { transitivity (SearchRun.unwrap
      (Cost.value (iterate (SearchRun.step_c p (@Visitor.noop E unit) scope)
        (Prepared.fuel p)
        (([(v, Prepared.succ_edges p v)], SearchRun.discover v None c), tt)))).
    - symmetry. exact (f_equal (@SearchRun.unwrap _) Hanswer).
    - exact Herase. }
  destruct (SearchRun.reference_loop p scope (Pos.to_nat (Prepared.fuel p))
    ([(v, Prepared.succ_edges p v)], SearchRun.discover v None c)) as [last evs].
  inversion Heq; subst last. exact Hempty.
Qed.

(** Numbering records fresh successive insertions, newest first. *)
Inductive numbering : list positive -> Map.t positive positive -> positive -> Prop :=
  | numbering_empty : numbering [] Map.empty 1%positive
  | numbering_add : forall xs m next v,
      numbering xs m next -> ~ In v xs ->
      numbering (v :: xs) (Map.set positive_encoding v next m) (Pos.succ next).

Local Lemma numbering_wf xs m next :
  numbering xs m next -> Map.wf positive_encoding m.
Proof.
  intro Hnum. induction Hnum; auto using Map.wf_empty, Map.wf_set.
Qed.

Local Lemma numbering_nodup xs m next : numbering xs m next -> NoDup xs.
Proof.
  intro Hnum. induction Hnum; constructor; assumption.
Qed.

Local Lemma numbering_size xs m next :
  numbering xs m next -> Pos.to_nat next = S (length xs).
Proof.
  intro Hnum. induction Hnum; [reflexivity|].
  rewrite Pos2Nat.inj_succ. cbn [length]. lia.
Qed.

Local Lemma numbering_domain xs m next :
  numbering xs m next -> forall v, (exists k, Map.get positive_encoding v m = Some k) <->
    In v xs.
Proof.
  intro Hnum. induction Hnum as [|xs m next v Hnum IH Hfresh]; intro u.
  - rewrite Map.get_empty. cbn. split; [intros [k Hk]; discriminate|contradiction].
  - destruct (Pos.eq_dec u v) as [->|Hne].
    + rewrite Map.get_set_same by now apply numbering_wf in Hnum. cbn. split; eauto.
    + rewrite (Map.get_set_other positive_encoding positive_encoding_laws)
        by (first [exact (numbering_wf xs m next Hnum)|exact Hne]).
      rewrite IH. cbn. intuition congruence.
Qed.

Local Lemma numbering_position xs m next :
  numbering xs m next -> forall v k, Map.get positive_encoding v m = Some k ->
    exists newer older, xs = newer ++ v :: older /\ Pos.to_nat k = S (length older).
Proof.
  intro Hnum. induction Hnum as [|xs m next w Hnum IH Hfresh]; intros v k Hget.
  - rewrite Map.get_empty in Hget. discriminate.
  - destruct (Pos.eq_dec v w) as [->|Hne].
    + rewrite Map.get_set_same in Hget by now apply numbering_wf in Hnum.
      inversion Hget; subst k.
      exists [], xs. split; [reflexivity|now apply numbering_size in Hnum].
    + rewrite (Map.get_set_other positive_encoding positive_encoding_laws) in Hget
        by (first [exact (numbering_wf xs m next Hnum)|exact Hne]).
      destruct (IH v k Hget) as [newer [older [Heq Hpos]]].
      exists (w :: newer), older. split; [cbn; now rewrite Heq|exact Hpos].
Qed.

Local Lemma numbering_nth xs m next :
  numbering xs m next -> forall v k, Map.get positive_encoding v m = Some k ->
    nth_error (rev xs) (Nat.pred (Pos.to_nat k)) = Some v.
Proof.
  intros Hnum v k Hget.
  destruct (numbering_position xs m next Hnum v k Hget) as [newer [older [Heq Hpos]]].
  rewrite Heq, rev_app_distr. cbn [rev].
  rewrite <- app_assoc, Hpos. cbn [Nat.pred].
  rewrite <- length_rev at 1. rewrite nth_error_app2 by lia.
  rewrite Nat.sub_diag. reflexivity.
Qed.

(** Successive fresh insertion gives both directions of the public one-based indexing contract. *)
Theorem numbering_index xs m next :
  numbering xs m next -> forall v i, Map.get positive_encoding v m = Some i <->
    nth_error (rev xs) (Nat.pred (Pos.to_nat i)) = Some v.
Proof.
  intros Hnum v i. split; [now apply numbering_nth with (next := next)|].
  intro Hi. pose proof (nth_error_In _ _ Hi) as Hin.
  apply (proj2 (in_rev xs v)) in Hin.
  destruct (proj2 (numbering_domain xs m next Hnum v) Hin) as [k Hk].
  pose proof (numbering_nth xs m next Hnum v k Hk) as Hnth.
  assert (Hindices : Nat.pred (Pos.to_nat k) = Nat.pred (Pos.to_nat i)).
  { apply (proj1 (NoDup_nth_error _) (NoDup_rev (numbering_nodup xs m next Hnum))).
    - apply nth_error_Some. congruence.
    - congruence. }
  assert (Heq : k = i).
  { apply Pos2Nat.inj. pose proof (Pos2Nat.is_pos k). pose proof (Pos2Nat.is_pos i). lia. }
  now subst k.
Qed.

(** Unfinished frames and finished vertices partition the complete discovery history. *)
Record history {E} (w : SearchRun.work E) : Prop := {
  pre_numbering : numbering (SearchRun.pre_rev (snd w))
    (SearchRun.pre_index (snd w)) (SearchRun.pre_clock (snd w));
  post_numbering : numbering (SearchRun.post_rev (snd w))
    (SearchRun.post_index (snd w)) (SearchRun.post_clock (snd w));
  partition : Permutation (SearchRun.pre_rev (snd w))
    (map fst (fst w) ++ SearchRun.post_rev (snd w))
}.

Local Lemma initial_history {E} : history ([], @SearchRun.initial E).
Proof.
  constructor; cbn [SearchRun.initial fst snd]; constructor.
Qed.

Local Lemma finish_history {E} u rest (c : SearchRun.core E) :
  history ((u, []) :: rest, c) -> history (rest, SearchRun.finish u c).
Proof.
  intros [Hpre Hpost Hpartition]. cbn [fst snd map] in Hpre, Hpost, Hpartition.
  assert (Hfresh : ~ In u (SearchRun.post_rev c)).
  { pose proof (Permutation_NoDup Hpartition (numbering_nodup _ _ _ Hpre)) as Hnodup.
    inversion Hnodup as [|x xs Hnot Htail]; subst x xs.
    intro Hin. apply Hnot. apply in_or_app. now right. }
  rewrite SearchRun.finish_equation. constructor; cbn [fst snd]; try assumption.
  - now apply numbering_add.
  - eapply Permutation_trans; [exact Hpartition|]. apply Permutation_middle.
Qed.

Local Lemma discover_history {E} stack (c : SearchRun.core E) v via es :
  history (stack, c) -> ~ In v (SearchRun.pre_rev c) ->
    history ((v, es) :: stack, SearchRun.discover v via c).
Proof.
  intros [Hpre Hpost Hpartition] Hfresh. rewrite SearchRun.discover_equation.
  constructor; cbn [fst snd map app].
  - now apply numbering_add.
  - exact Hpost.
  - apply perm_skip. exact Hpartition.
Qed.

Local Lemma history_stack {E} stack stack' (c : SearchRun.core E) :
  map fst stack = map fst stack' -> history (stack, c) -> history (stack', c).
Proof.
  intros Heq [Hpre Hpost Hpartition]. constructor; try assumption.
  cbn [fst snd] in *. now rewrite <- Heq.
Qed.

(** Each transition preserves numbering and the pending/finished history partition. *)
Theorem transition_history {V E} (p : Prepared.t V E) scope w :
  representation (snd w) -> history w ->
    history (SearchRun.unwrap (fst (SearchRun.transition p scope w))).
Proof.
  destruct w as [stack c]. intros Hrep Hhistory. rewrite SearchRun.step_equation.
  destruct stack as [|[u [|[e v] pending]] rest]; cbn [fst SearchRun.unwrap].
  - exact Hhistory.
  - now apply finish_history.
  - assert (Htail : history ((u, pending) :: rest, c)).
    { exact (history_stack ((u, (e, v) :: pending) :: rest)
        ((u, pending) :: rest) c eq_refl Hhistory). }
    destruct (Scope.admits scope v); [|exact Htail].
    destruct (Prepared.name_of p v); [|exact Htail].
    destruct (SearchRun.edge_kind c u v) eqn:Hkind; cbn [fst SearchRun.unwrap];
      try exact Htail.
    apply discover_history; [exact Htail|].
    intro Hin. apply (seen_discovered _ Hrep) in Hin.
    pose proof (proj1 (tree_is_white c u v) Hkind) as Hwhite.
    change (FinSet.mem positive_encoding v (SearchRun.seen c) = true) in Hin.
    rewrite Hwhite in Hin. discriminate.
Qed.

Local Lemma loop_history {V E} (p : Prepared.t V E) scope n w :
  representation (snd w) -> history w ->
    history (fst (SearchRun.reference_loop p scope n w)).
Proof.
  revert w. induction n as [|n IH]; intros w Hrep Hhistory; [exact Hhistory|].
  pose proof (transition_representation p scope w Hrep) as Hrep'.
  pose proof (transition_history p scope w Hrep Hhistory) as Hhistory'.
  cbn [SearchRun.reference_loop].
  destruct (SearchRun.transition p scope w) as [[w'|w'] evs];
    cbn [fst snd SearchRun.unwrap] in Hrep', Hhistory'.
  - specialize (IH w' Hrep' Hhistory').
    destruct (SearchRun.reference_loop p scope n w') as [final later]. exact IH.
  - exact Hhistory'.
Qed.

Local Lemma root_history {V E} (p : Prepared.t V E) scope c v :
  Prepared.ready p -> representation c -> history ([], c) ->
    history ([], fst (SearchRun.reference_root p scope c v)).
Proof.
  intros Hready Hrep Hhistory. unfold SearchRun.reference_root.
  destruct (Scope.admits scope v); [|exact Hhistory].
  destruct (FinSet.mem positive_encoding v (SearchRun.seen c)) eqn:Hfresh; [exact Hhistory|].
  destruct (Prepared.name_of p v) as [name|] eqn:Hname; [|exact Hhistory].
  pose proof (reference_root_drains p scope c v name Hready Hrep Hname Hfresh) as Hdrain.
  assert (Hfreshpre : ~ In v (SearchRun.pre_rev c)).
  { intro Hin. apply (seen_discovered _ Hrep) in Hin. congruence. }
  pose proof (loop_history p scope (Pos.to_nat (Prepared.fuel p))
    ([(v, Prepared.succ_edges p v)], SearchRun.discover v None c)
    (discover_representation c v None Hrep Hfresh)
    (discover_history [] c v None (Prepared.succ_edges p v) Hhistory Hfreshpre)) as Hloop.
  destruct (SearchRun.reference_loop p scope (Pos.to_nat (Prepared.fuel p))
    ([(v, Prepared.succ_edges p v)], SearchRun.discover v None c)) as [[stack final] evs].
  cbn [fst] in Hdrain. subst stack. exact Hloop.
Qed.

Local Lemma roots_history {V E} (p : Prepared.t V E) scope roots c :
  Prepared.ready p -> representation c -> history ([], c) ->
    history ([], fst (SearchRun.reference_roots p scope roots c)).
Proof.
  intro Hready. revert c. induction roots as [|v rest IH]; intros c Hrep Hhistory;
    [exact Hhistory|].
  pose proof (root_representation p scope c v Hrep) as Hrep'.
  pose proof (root_history p scope c v Hready Hrep Hhistory) as Hhistory'.
  cbn [SearchRun.reference_roots].
  destruct (SearchRun.reference_root p scope c v) as [c' here].
  specialize (IH c' Hrep' Hhistory').
  destruct (SearchRun.reference_roots p scope rest c') as [final later]. exact IH.
Qed.

(** Adequate search numbers both orders exactly and finishes every discovered vertex. *)
Theorem run_numbering {V E} (p : Prepared.t V E) scope roots :
  Prepared.ready p ->
  let r := SearchRun.dfs p scope roots in
  Permutation (Search.preorder r) (Search.postorder r) /\
  (forall v i, Map.get positive_encoding v (Search.pre_num r) = Some i <->
    nth_error (Search.preorder r) (Nat.pred (Pos.to_nat i)) = Some v) /\
  (forall v i, Map.get positive_encoding v (Search.post_num r) = Some i <->
    nth_error (Search.postorder r) (Nat.pred (Pos.to_nat i)) = Some v).
Proof.
  intro Hready. unfold SearchRun.dfs. rewrite SearchRun.run_equation.
  pose proof (roots_history p scope roots _ Hready
    (@initial_representation E) (@initial_history E)) as Hhistory.
  destruct (SearchRun.reference_roots p scope roots SearchRun.initial) as [c evs].
  destruct Hhistory as [Hpre Hpost Hpartition].
  cbn [fst snd map app] in Hpre, Hpost, Hpartition.
  unfold SearchRun.result, SearchRun.result_c. autorewrite with galois_cost.
  cbn [fst Search.preorder Search.postorder Search.pre_num Search.post_num].
  split.
  - eapply Permutation_trans; [apply Permutation_sym, Permutation_rev|].
    eapply Permutation_trans; [exact Hpartition|apply Permutation_rev].
  - split.
    + exact (numbering_index _ _ _ Hpre).
    + exact (numbering_index _ _ _ Hpost).
Qed.

End SearchExact.
