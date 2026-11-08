(** * Oriented frontier accumulation

    Each reachable edge contributes its unblocked source ancestors to one shared sweep.
    For example, either branch of a diamond contributes its join.
    Builds on: GraphWalk, GraphReach, GraphPrepared and GraphFrontierSpec. *)

From Stdlib Require Import List Bool PArith NArith Arith Lia.
From Stdlib.Relations Require Import Relation_Operators.
From Galois.Cost Require Import CostMonad CostList CostBound.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseMapCost BaseTrieCost.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphReach
  GraphDomSpec GraphCheckDom GraphFrontierSpec GraphWalk.
Import List.ListNotations Cost.Notations.

Module FrontierSweep.

Definition eq_c x y :=
  Cost.map (fun c => match c with Eq => true | _ => false end) (Map.code_compare_c x y).

Local Lemma eq_value x y : Cost.value (eq_c x y) = Pos.eqb x y.
Proof.
  unfold eq_c. rewrite Cost.value_map. fold (Map.code_compare x y).
  destruct (Pos.eq_dec x y) as [->|Hne].
  - rewrite (proj2 (Map.code_compare_eq y y) eq_refl). symmetry. apply Pos.eqb_refl.
  - destruct (Map.code_compare x y) eqn:Hcmp;
      [apply Map.code_compare_eq in Hcmp; contradiction| |];
      symmetry; now apply Pos.eqb_neq.
Qed.

Definition member_c v xs := existsb_c (eq_c v) xs.

Local Lemma member_value v xs : Cost.value (member_c v xs) = Reach.member v xs.
Proof.
  unfold member_c, Reach.member. rewrite value_existsb_c.
  induction xs as [|x rest IH]; cbn [existsb]; [reflexivity|].
  now rewrite eq_value, IH.
Qed.

Fixpoint remove_c v xs :=
  match xs with
  | [] => Cost.ret []
  | x :: rest =>
    Cost.step ;;
    let* same := eq_c v x in
    let* tail := remove_c v rest in
    Cost.ret (if same then tail else x :: tail)
  end.

Local Lemma remove_value v xs :
  Cost.value (remove_c v xs) = remove Pos.eq_dec v xs.
Proof.
  induction xs as [|x rest IH]; cbn [remove_c remove]; [reflexivity|].
  autorewrite with galois_cost. rewrite eq_value, IH.
  destruct (Pos.eq_dec v x) as [->|Hne].
  - now rewrite Pos.eqb_refl.
  - now rewrite (proj2 (Pos.eqb_neq v x) Hne).
Qed.

Fixpoint nodup_c xs :=
  match xs with
  | [] => Cost.ret []
  | x :: rest =>
    Cost.step ;;
    let* duplicate := member_c x rest in
    let* tail := nodup_c rest in
    Cost.ret (if duplicate then tail else x :: tail)
  end.

Local Lemma member_spec v xs : Reach.member v xs = true <-> In v xs.
Proof.
  unfold Reach.member. rewrite existsb_exists.
  split.
  - intros [x [Hx Heq]]. apply Pos.eqb_eq in Heq. now subst x.
  - intro Hx. exists v. split; [exact Hx|apply Pos.eqb_refl].
Qed.

Local Lemma nodup_value xs : Cost.value (nodup_c xs) = nodup Pos.eq_dec xs.
Proof.
  induction xs as [|x rest IH]; cbn [nodup_c nodup]; [reflexivity|].
  autorewrite with galois_cost. rewrite member_value, IH.
  destruct (Reach.member x rest) eqn:Hmem, (in_dec Pos.eq_dec x rest);
    try reflexivity; exfalso.
  - apply member_spec in Hmem. tauto.
  - assert (Reach.member x rest = true) by (apply member_spec; assumption).
    congruence.
Qed.

Definition universe_c {V E} (p : Prepared.t V E) :=
  let* ids := filter_map_c (Prepared.id_of_c p) (Graph.nodes (Prepared.graph p)) in
  nodup_c ids.

Local Lemma present_filter_map {A B} (f : A -> option B) xs :
  filter_map f xs = Prepared.present f xs.
Proof.
  unfold filter_map. induction xs as [|x rest IH];
    cbn [fold_right Prepared.present]; [reflexivity|].
  destruct (f x); now rewrite IH.
Qed.

(** Costed universe enumeration preserves the reference order and invalid-ID filtering. *)
Theorem universe_value {V E} (p : Prepared.t V E) :
  Cost.value (universe_c p) = Reach.universe p.
Proof.
  unfold universe_c, Reach.universe. rewrite Cost.value_bind, nodup_value,
    value_filter_map_c, present_filter_map. reflexivity.
Qed.

Definition successors_c {V E} (p : Prepared.t V E) scope all v :=
  let* edges := Prepared.succ_edges_c p v in
  let* targets := map_c (fun ej => Cost.ret (snd ej)) edges in
  filter_c (fun x =>
    let* admitted := Scope.admits_c scope x in
    let* valid := member_c x all in
    Cost.ret (admitted && valid)) targets.

(** Costed successor filtering preserves the reference checker adjacency. *)
Theorem successors_value {V E} (p : Prepared.t V E) scope v :
  Cost.value (successors_c p scope (Reach.universe p) v) = Reach.successors p scope v.
Proof.
  unfold successors_c, Reach.successors. autorewrite with galois_cost.
  apply filter_ext. intro x. autorewrite with galois_cost.
  rewrite member_value. reflexivity.
Qed.

Definition roots_c scope all roots :=
  filter_c (fun x =>
    let* root := member_c x roots in
    let* admitted := Scope.admits_c scope x in
    Cost.ret (root && admitted)) all.

(** Costed root filtering preserves every reference root occurrence decision. *)
Theorem roots_value {V E} (p : Prepared.t V E) scope roots :
  Cost.value (roots_c scope (Reach.universe p) roots) = Reach.roots_in p scope roots.
Proof.
  unfold roots_c, Reach.roots_in. rewrite value_filter_c.
  apply filter_ext. intro x. autorewrite with galois_cost. rewrite member_value.
  reflexivity.
Qed.

Definition credit_c (next : positive -> Cost.t (list positive)) all :=
  fold_right_c (fun v credit =>
    Cost.step ;;
    let* children := next v in
    let* size := length_c children in
    Cost.ret (S size + credit)%nat) O all.

(** The costed adjacency-credit pass computes the reference loop budget. *)
Theorem credit_value next all :
  Cost.value (credit_c next all) = Reach.credit (fun v => Cost.value (next v)) all.
Proof.
  unfold credit_c. rewrite value_fold_right_c.
  induction all as [|v rest IH]; cbn [fold_right Reach.credit]; [reflexivity|].
  autorewrite with galois_cost. now rewrite IH.
Qed.

(** Finite closure charges its budget calculation and the shared work-stack driver. *)
Definition closure_c (next : positive -> Cost.t (list positive)) all roots :=
  let* credit := credit_c next all in
  let* size := length_c roots in
  let* fuel := Prepared.budget_c (credit + size) in
  let* result := Walk.closure_c next member_c remove_c
    fuel roots all [] in
  FinSet.of_list_c positive_encoding (snd result).

(** A closed finite universe gives exact least-closure membership
    without a successful-run premise. *)
Theorem closure_exact next all roots :
  NoDup all -> incl roots all ->
  (forall u, incl (Cost.value (next u)) all) ->
  forall v, FinSet.mem positive_encoding v (Cost.value (closure_c next all roots)) = true <->
    Reach.closure (fun u => Cost.value (next u)) roots v.
Proof.
  intros Hnodup Hroots Hnext v.
  unfold closure_c. rewrite Cost.value_bind, credit_value,
    Cost.value_bind, value_length_c, Cost.value_bind.
  rewrite Prepared.budget_value, Cost.value_bind.
  rewrite Walk.closure_spec by (intros; first [apply member_value|apply remove_value]).
  rewrite SuccNat2Pos.id_succ.
  change (FinSet.mem positive_encoding v (FinSet.of_list positive_encoding
    (snd (Reach.loop (fun u => Cost.value (next u))
      (S (Reach.credit (fun u => Cost.value (next u)) all + length roots))
      roots all []))) = true <->
    Reach.closure (fun u => Cost.value (next u)) roots v).
  rewrite FinSet.mem_of_list, existsb_exists.
  setoid_rewrite (eqb_true_iff _ positive_encoding_laws).
  assert (Hmember : forall xs, (exists x, In x xs /\ v = x) <-> In v xs).
  { intro xs. split; [intros [x [Hx ->]]; exact Hx|intro Hv; exists v; auto]. }
  rewrite Hmember.
  apply (proj2 (Walk.closure_complete (fun u => Cost.value (next u)) all roots
    (S (Reach.credit (fun u => Cost.value (next u)) all + length roots))
    Hnodup Hroots Hnext ltac:(lia)) v).
Qed.

(** Costed reference reachability retains preparation, adjacency, list and visited-work costs. *)
Definition reach_c {V E} (p : Prepared.t V E) scope roots :=
  let* all := universe_c p in
  let next := successors_c p scope all in
  let* initial := roots_c scope all roots in
  let* credit := credit_c next all in
  let* size := length_c initial in
  let* fuel := Prepared.budget_c (credit + size) in
  let* result := Walk.closure_c next member_c remove_c
    fuel initial all [] in
  FinSet.of_list_c positive_encoding (snd result).

Local Lemma loop_extra next n pending unseen seen :
  fst (Reach.loop next n pending unseen seen) = [] ->
  Reach.loop next (S n) pending unseen seen = Reach.loop next n pending unseen seen.
Proof.
  revert pending unseen seen. induction n as [|n IH];
    intros [|v rest] unseen seen Hdone; try reflexivity; [discriminate|].
  cbn [Reach.loop] in Hdone |- *.
  destruct (Reach.member v unseen); now apply IH.
Qed.

Local Lemma credit_ext f g all :
  (forall v, f v = g v) -> Reach.credit f all = Reach.credit g all.
Proof.
  intro Hfg. induction all as [|v rest IH]; cbn [Reach.credit]; [reflexivity|].
  now rewrite Hfg, IH.
Qed.

Local Lemma loop_ext f g n pending unseen seen :
  (forall v, f v = g v) ->
  Reach.loop f n pending unseen seen = Reach.loop g n pending unseen seen.
Proof.
  intro Hfg. revert pending unseen seen.
  induction n as [|n IH]; intros [|v rest] unseen seen; try reflexivity.
  cbn [Reach.loop]. destruct (Reach.member v unseen); [rewrite Hfg|]; apply IH.
Qed.

(** Reference reachability and the costed bridge have exactly the same set value. *)
Theorem reach_value {V E} (p : Prepared.t V E) scope roots :
  Cost.value (reach_c p scope roots) = Reach.set p scope roots.
Proof.
  unfold reach_c. rewrite Cost.value_bind, universe_value.
  rewrite Cost.value_bind, roots_value, Cost.value_bind, credit_value.
  rewrite Cost.value_bind, value_length_c, Cost.value_bind.
  rewrite Prepared.budget_value, Cost.value_bind.
  rewrite Walk.closure_spec by (intros; first [apply member_value|apply remove_value]).
  rewrite SuccNat2Pos.id_succ.
  rewrite (credit_ext _ (Reach.successors p scope)) by apply successors_value.
  rewrite (loop_ext _ (Reach.successors p scope)) by apply successors_value.
  fold (FinSet.of_list positive_encoding
    (snd (Reach.loop (Reach.successors p scope)
      (S (Reach.credit (Reach.successors p scope) (Reach.universe p) +
        length (Reach.roots_in p scope roots))) (Reach.roots_in p scope roots)
      (Reach.universe p) []))).
  rewrite loop_extra by apply Reach.fuel_adequate.
  reflexivity.
Qed.

Definition budget_c t :=
  let* size := Map.size_c (Dom.idom t) in Prepared.budget_c size.

Definition ancestors_c t q :=
  let* fuel := budget_c t in
  let* chain := Walk.until_c (Walk.up_c t) (fun _ => Cost.ret false) fuel q in
  FinSet.of_list_c positive_encoding chain.

Definition ancestors t q := Cost.value (ancestors_c t q).

Local Lemma ancestors_wf t q : FinSet.wf positive_encoding (ancestors t q).
Proof.
  unfold ancestors, ancestors_c. rewrite !Cost.value_bind.
  apply FinSet.wf_of_list.
Qed.

(** The boundary cache is exact parent ancestry for any finite well-formed forest. *)
Theorem ancestors_spec t q d :
  Map.wf positive_encoding (Dom.idom t) ->
  well_founded (fun u v => Map.get positive_encoding v (Dom.idom t) = Some u) ->
  (FinSet.mem positive_encoding d (ancestors t q) = true <->
    idom_ancestor (Dom.idom t) d q).
Proof.
  intros Hmap Hforest. unfold ancestors, ancestors_c, budget_c.
  rewrite !Cost.value_bind, Prepared.budget_value. fold (Map.size (Dom.idom t)).
  change (FinSet.mem positive_encoding d (FinSet.of_list positive_encoding
    (Walk.until (Walk.up_c t) (fun _ => Cost.ret false)
      (Pos.of_succ_nat (Map.size (Dom.idom t))) q)) = true <->
    idom_ancestor (Dom.idom t) d q).
  rewrite FinSet.mem_of_list.
  rewrite existsb_exists.
  setoid_rewrite (eqb_true_iff _ positive_encoding_laws).
  assert (Hmember : forall xs, (exists x, In x xs /\ d = x) <-> In d xs).
  { intro xs. split; [intros [x [Hx ->]]; exact Hx|intro Hd; exists d; auto]. }
  rewrite Hmember, Walk.up_spec; try assumption; [tauto|discriminate].
Qed.

Definition blocked_set_c t boundary :=
  match boundary with
  | None => FinSet.empty_c
  | Some q => ancestors_c t q
  end.

Definition runner_c t start boundary :=
  let* fuel := budget_c t in
  let* blocked := blocked_set_c t boundary in
  Walk.until_c (Walk.up_c t) (fun v => FinSet.mem_c positive_encoding v blocked) fuel start.

Definition runner t start boundary := Cost.value (runner_c t start boundary).

(** A runner emits exactly source ancestors outside the boundary's ancestor cone. *)
Theorem runner_exact t start boundary d :
  Map.wf positive_encoding (Dom.idom t) ->
  well_founded (fun u v => Map.get positive_encoding v (Dom.idom t) = Some u) ->
  (In d (runner t start boundary) <->
    idom_ancestor (Dom.idom t) d start /\
      forall q, boundary = Some q -> ~ idom_ancestor (Dom.idom t) d q).
Proof.
  intros Hmap Hforest. unfold runner, runner_c, budget_c.
  rewrite !Cost.value_bind, Prepared.budget_value. fold (Map.size (Dom.idom t)).
  change (In d (Walk.until (Walk.up_c t)
    (fun v => FinSet.mem_c positive_encoding v (Cost.value (blocked_set_c t boundary)))
    (Pos.of_succ_nat (Map.size (Dom.idom t))) start) <->
    idom_ancestor (Dom.idom t) d start /\
      forall q, boundary = Some q -> ~ idom_ancestor (Dom.idom t) d q).
  rewrite Walk.up_spec; try assumption.
  - change ((idom_ancestor (Dom.idom t) d start /\
      FinSet.mem positive_encoding d (Cost.value (blocked_set_c t boundary)) = false) <->
      idom_ancestor (Dom.idom t) d start /\
        forall q, boundary = Some q -> ~ idom_ancestor (Dom.idom t) d q).
    destruct boundary as [q|]; cbn [blocked_set_c].
    + fold (ancestors t q).
      rewrite <- Bool.not_true_iff_false, ancestors_spec by assumption.
      split.
      * intros [Ha Hb]. split; [exact Ha|].
        intros q' Heq. inversion Heq; subst q'. exact Hb.
      * intros [Ha Hb]. split; [exact Ha|exact (Hb q eq_refl)].
    + fold (@FinSet.empty positive). rewrite FinSet.mem_empty. intuition discriminate.
  - intros a v Hav.
    change (FinSet.mem positive_encoding v (Cost.value (blocked_set_c t boundary)) = true ->
      FinSet.mem positive_encoding a (Cost.value (blocked_set_c t boundary)) = true).
    destruct boundary as [q|]; cbn [blocked_set_c].
    + fold (ancestors t q).
      rewrite !ancestors_spec by assumption.
      intro Hvq. eapply rt_trans; eassumption.
    + fold (@FinSet.empty positive). rewrite FinSet.mem_empty. discriminate.
Qed.

Local Lemma no_return m n :
  Acc (fun u v => Map.get positive_encoding v m = Some u) n ->
  forall v, Map.get positive_encoding v m = Some n -> ~ idom_ancestor m v n.
Proof.
  intro Hacc. induction Hacc as [n Hacc IH]. intros v Hnv Hanc.
  assert (Hcases : forall d x, idom_ancestor m d x ->
    d = x \/ exists u, Map.get positive_encoding x m = Some u /\ idom_ancestor m d u).
  { intros d x H. induction H as [a b Hab|b|a c b Hac IHac Hcb IHcb].
    - right. exists a. split; [exact Hab|apply rt_refl].
    - now left.
    - destruct IHcb as [->|[p [Hp Hcp]]]; [exact IHac|].
      right. exists p. split; [exact Hp|]. eapply rt_trans; eassumption. }
  destruct (Hcases v n Hanc) as [->|[p [Hp Hvp]]].
  - apply (IH n Hnv n Hnv). apply rt_refl.
  - apply (IH p Hp n Hp). eapply rt_trans; [apply rt_step; exact Hnv|exact Hvp].
Qed.

(** Strict dominance is precisely ancestry above the supplied node's immediate parent. *)
Theorem strict_parent {V E} (p : Prepared.t V E) t n d v u :
  Prepared.ready p -> Dom.exact p t -> reachable (Prepared.graph p) n ->
  Prepared.id_of p n = Some v -> Prepared.id_of p d = Some u ->
  (strictly_dominates (Prepared.graph p) d n <->
    exists q, Map.get positive_encoding v (Dom.idom t) = Some q /\
      idom_ancestor (Dom.idom t) u q).
Proof.
  intros Hready Htree Hn Hv Hu.
  destruct (Map.get positive_encoding v (Dom.idom t)) as [q|] eqn:Hparent.
  - destruct (Dom.idom_domain p t Htree v q Hparent)
      as [n' [b [Hnv [Hqb [Hnr Hbr]]]]].
    pose proof (Prepared.id_of_name_of p q b (proj2 (proj2 Hready)) Hqb) as Hb.
    pose proof (Dom.idom_sound p t Htree v q n b Hparent
      (Prepared.name_of_id_of p n v (proj2 (proj2 Hready)) Hv) Hqb) as Himmediate.
    split.
    + intro Hstrict. exists q. split; [reflexivity|].
      apply (proj2 (DomCheck.ancestry_spec p t b d q u Hready Htree Hbr Hb Hu)).
      exact (proj2 Himmediate d Hstrict).
    + intros [q' [Heq Hanc]]. inversion Heq; subst q'.
      split.
      * eapply dominates_trans; [|exact (proj1 (proj1 Himmediate))].
        apply (proj1 (DomCheck.ancestry_spec p t b d q u Hready Htree Hbr Hb Hu)).
        exact Hanc.
      * intro Heqdn. subst d. assert (u = v) by congruence. subst u.
        exact (no_return _ q (Dom.parent_finite p t Htree q) v Hparent Hanc).
  - split.
    + intro Hstrict.
      exfalso. exact (proj1 (Dom.idom_complete p t Htree n v Hn Hv) Hparent d Hstrict).
    + intros [q [Hfalse _]]. discriminate.
Qed.

Definition edge_events_c t seen u {E} (edge : E * positive) :=
  let '(e, v) := edge in
  let* live := FinSet.mem_c positive_encoding u seen in
  if live then
    let* boundary := Map.get_c positive_encoding v (Dom.idom t) in
    let* chain := runner_c t u boundary in
    map_c (fun d => Cost.ret (d, (e, v))) chain
  else Cost.ret [].

Definition node_events_c {V E} (p : Prepared.t V E) t seen u :=
  let* edges := Prepared.succ_edges_c p u in
  fold_right_c (fun edge events =>
    let* fresh := edge_events_c t seen u edge in
    app_c fresh events) [] edges.

(** The oriented sweep retains edge labels so control dependence uses the same events. *)
Definition events_c {V E} (p : Prepared.t V E) t :=
  let* seen := reach_c p Reach.unrestricted (Prepared.entry_ids p) in
  let* all := universe_c p in
  fold_right_c (fun u events =>
    let* fresh := node_events_c p t seen u in
    app_c fresh events) [] all.

Definition events {V E} (p : Prepared.t V E) t := Cost.value (events_c p t).

(** Sweep events enumerate the reachable labelled edges and each stopped source-ancestor trace. *)
Theorem events_equation {V E} (p : Prepared.t V E) t :
  events p t =
    flat_map (fun u => flat_map (fun edge =>
      let '(e, v) := edge in
      if FinSet.mem positive_encoding u
        (Reach.set p Reach.unrestricted (Prepared.entry_ids p))
      then map (fun d => (d, (e, v)))
        (runner t u (Map.get positive_encoding v (Dom.idom t)))
      else []) (Prepared.succ_edges p u)) (Reach.universe p).
Proof.
  unfold events, events_c. rewrite Cost.value_bind, reach_value,
    Cost.value_bind, universe_value, value_fold_right_c.
  induction (Reach.universe p) as [|u rest IH]; cbn [fold_right flat_map];
    [reflexivity|].
  rewrite Cost.value_bind, value_app_c, IH. f_equal.
  unfold node_events_c. rewrite Cost.value_bind, value_fold_right_c.
  fold (Prepared.succ_edges p u).
  induction (Prepared.succ_edges p u) as [|[e v] rest' IH']; cbn [fold_right flat_map];
    [reflexivity|].
  rewrite Cost.value_bind, value_app_c, IH'. f_equal.
  unfold edge_events_c. rewrite Cost.value_bind.
  fold (FinSet.mem positive_encoding u (Reach.set p Reach.unrestricted (Prepared.entry_ids p))).
  destruct (FinSet.mem positive_encoding u
    (Reach.set p Reach.unrestricted (Prepared.entry_ids p))); [|reflexivity].
  rewrite !Cost.value_bind, value_map_c. reflexivity.
Qed.

Local Lemma id_injective {V E} (p : Prepared.t V E) a b i :
  Prepared.ready p -> Prepared.id_of p a = Some i -> Prepared.id_of p b = Some i ->
  a = b.
Proof.
  intros Hready Ha Hb.
  pose proof (Prepared.name_of_id_of p a i (proj2 (proj2 Hready)) Ha).
  pose proof (Prepared.name_of_id_of p b i (proj2 (proj2 Hready)) Hb).
  congruence.
Qed.

(** One labelled sweep event states its reachable edge and exact semantic boundary. *)
Theorem events_exact {V E} (p : Prepared.t V E) t d x i j e :
  Prepared.ready p -> Dom.exact p t ->
  Prepared.id_of p d = Some i -> Prepared.id_of p x = Some j ->
  (In (i, (e, j)) (events p t) <->
    reachable (Prepared.graph p) (Graph.source (Prepared.graph p) e) /\
    In e (Graph.out (Prepared.graph p) (Graph.source (Prepared.graph p) e)) /\
    Graph.target (Prepared.graph p) e = x /\
    dominates (Prepared.graph p) d (Graph.source (Prepared.graph p) e) /\
    ~ strictly_dominates (Prepared.graph p) d x).
Proof.
  intros Hready Htree Hd Hx. rewrite events_equation, in_flat_map.
  assert (Hmap := proj1 (Dom.maps_wf p t Htree)).
  assert (Hforest := Dom.parent_finite p t Htree).
  split.
  - intros [u [Hu Hin]]. apply in_flat_map in Hin.
    destruct Hin as [[a v] [Hedge Hin]].
    destruct (proj1 (Reach.universe_spec p u) Hu) as [s [Hs Hsu]].
    destruct (FinSet.mem positive_encoding u
      (Reach.set p Reach.unrestricted (Prepared.entry_ids p))) eqn:Hlive;
      [|contradiction].
    apply in_map_iff in Hin. destruct Hin as [z [Heq Hchain]].
    inversion Heq; subst z a v.
    pose proof (proj1 (Reach.entries_exact p s u Hready Hsu) Hlive) as Hsreach.
    apply (Prepared.succ_spec p s u e j (proj2 (proj2 Hready)) Hsu) in Hedge.
    destruct Hedge as [He Htarget].
    pose proof (out_source (proj1 Hready) s e He) as Hsource.
    assert (Htargetx : Graph.target (Prepared.graph p) e = x).
    { eapply id_injective; eassumption. }
    assert (Hxr : reachable (Prepared.graph p) x).
    { rewrite <- Htargetx. eapply reachable_step; [rewrite Hsource; exact Hsreach|].
      rewrite Hsource. exact He. }
    apply (runner_exact t u _ i Hmap Hforest) in Hchain.
    destruct Hchain as [Hanc Hfree].
    split; [now rewrite Hsource|]. split; [now rewrite Hsource|].
    split; [exact Htargetx|]. split.
    + rewrite Hsource. apply (proj1
        (DomCheck.ancestry_spec p t s d u i Hready Htree Hsreach Hsu Hd)). exact Hanc.
    + rewrite (strict_parent p t x d j i Hready Htree Hxr Hx Hd).
      intros [q [Hq Hiq]]. exact (Hfree q Hq Hiq).
  - intros [Hsource [Hedge [Htarget [Hdom Hnot]]]].
    assert (Hsn : In (Graph.source (Prepared.graph p) e) (Graph.nodes (Prepared.graph p))).
    { eapply reachable_in_nodes; [exact (proj1 Hready)|exact Hsource]. }
    destruct (proj1 (Prepared.ids_domain p (proj2 (proj2 Hready)) _) Hsn) as [u Hu].
    exists u. split.
    + apply Reach.universe_spec. exists (Graph.source (Prepared.graph p) e). auto.
    + apply in_flat_map. exists (e, j). split.
      * apply (Prepared.succ_spec p _ u e j (proj2 (proj2 Hready)) Hu).
        split; [exact Hedge|now rewrite Htarget].
      * rewrite (proj2 (Reach.entries_exact p _ u Hready Hu) Hsource).
        apply in_map_iff. exists i. split; [reflexivity|].
        apply (runner_exact t u _ i Hmap Hforest). split.
        -- apply (proj2 (DomCheck.ancestry_spec p t _ d u i
            Hready Htree Hsource Hu Hd)). exact Hdom.
        -- intros q Hq Hiq. apply Hnot.
           apply (proj2 (strict_parent p t x d j i Hready Htree
             ltac:(rewrite <- Htarget; eapply reachable_step; eassumption) Hx Hd)).
           now exists q.
Qed.

Definition add_c (m : Map.t positive (FinSet.t positive)) (event : positive * positive) :=
  let '(d, x) := event in
  let* old := Map.find_or_c positive_encoding FinSet.empty d m in
  let* row := FinSet.add_c positive_encoding x old in
  Map.set_c positive_encoding d row m.

Definition add m event := Cost.value (add_c m event).

(** Frontier observations are successful row lookup followed by membership. *)
Definition frontier_at (m : Map.t positive (FinSet.t positive)) d x :=
  exists row, Map.get positive_encoding d m = Some row /\
    FinSet.mem positive_encoding x row = true.

Definition rows_wf (m : Map.t positive (FinSet.t positive)) :=
  Map.wf positive_encoding m /\
    forall d row, Map.get positive_encoding d m = Some row ->
      FinSet.wf positive_encoding row.

Local Lemma add_equation m d x :
  add m (d, x) = Map.set positive_encoding d
    (FinSet.add positive_encoding x (Map.find_or positive_encoding FinSet.empty d m)) m.
Proof.
  unfold add, add_c. rewrite !Cost.value_bind. reflexivity.
Qed.

Local Lemma add_wf m event : rows_wf m -> rows_wf (add m event).
Proof.
  intros [Hmap Hrows]. destruct event as [d x]. rewrite add_equation.
  split; [now apply Map.wf_set|].
  intros a row Hget. rewrite Map.get_set in Hget by
    (try assumption; exact positive_encoding_laws).
  destruct (eqb positive_encoding a d) eqn:Had.
  - inversion Hget; subst row. apply FinSet.wf_add.
    rewrite Map.find_or_equation.
    destruct (Map.get positive_encoding d m) as [old|] eqn:Hold;
      [now apply (Hrows d old)|apply FinSet.wf_empty].
  - now apply (Hrows a row).
Qed.

Local Lemma add_spec m a b d x : rows_wf m ->
  (frontier_at (add m (a, b)) d x <-> (d = a /\ x = b) \/ frontier_at m d x).
Proof.
  intros [Hmap Hrows]. rewrite add_equation.
  unfold frontier_at.
  rewrite Map.get_set by (try assumption; exact positive_encoding_laws).
  rewrite Map.find_or_equation.
  destruct (Pos.eq_dec d a) as [->|Hne].
  - rewrite (proj2 (eqb_true_iff _ positive_encoding_laws a a) eq_refl).
    assert (Hmem : forall old, FinSet.wf positive_encoding old ->
      (FinSet.mem positive_encoding x (FinSet.add positive_encoding b old) = true <->
        x = b \/ FinSet.mem positive_encoding x old = true)).
    { intros old Hwf. rewrite FinSet.mem_add by exact Hwf.
      now rewrite orb_true_iff, (eqb_true_iff _ positive_encoding_laws). }
    destruct (Map.get positive_encoding a m) as [old|] eqn:Hold.
    + assert (Holdwf := Hrows a old Hold).
      split.
      * intros [row [Heq Hmember]]. inversion Heq; subst row.
        apply (Hmem old Holdwf) in Hmember.
        destruct Hmember as [->|Hmember]; [auto|right; exists old; auto].
      * intros [[_ Heq]|[row [Heq Hmember]]].
        -- subst x. exists (FinSet.add positive_encoding b old).
           split; [reflexivity|]. apply Hmem; [exact Holdwf|auto].
        -- inversion Heq; subst row. exists (FinSet.add positive_encoding b old).
           split; [reflexivity|]. apply Hmem; [exact Holdwf|auto].
    + split.
      * intros [row [Heq Hmember]]. inversion Heq; subst row.
        apply (Hmem _ (FinSet.wf_empty _)) in Hmember.
        rewrite FinSet.mem_empty in Hmember. destruct Hmember as [->|Hfalse];
          [auto|discriminate].
      * intros [[_ ->]|[row [Hfalse _]]]; [|discriminate].
        exists (FinSet.add positive_encoding b FinSet.empty). split; [reflexivity|].
        apply Hmem; [apply FinSet.wf_empty|auto].
  - rewrite (proj2 (eqb_false_iff _ positive_encoding_laws d a) Hne).
    split; [auto|intros [[Heq _]|H]; [congruence|exact H]].
Qed.

Local Lemma fold_wf es m : rows_wf m -> rows_wf (fold_left add es m).
Proof.
  revert m. induction es as [|e rest IH]; intros m Hwf; [exact Hwf|].
  cbn [fold_left]. apply IH, add_wf, Hwf.
Qed.

Local Lemma fold_spec es m d x : rows_wf m ->
  (frontier_at (fold_left add es m) d x <-> In (d, x) es \/ frontier_at m d x).
Proof.
  revert m. induction es as [|[a b] rest IH]; intros m Hwf; cbn [fold_left In].
  - tauto.
  - rewrite IH by now apply add_wf.
    rewrite add_spec by exact Hwf.
    intuition congruence.
Qed.

(** One oriented event sweep accumulates the target set for each visited ancestor. *)
Definition sweep_c {V E} (p : Prepared.t V E) t :=
  let* es := events_c p t in
  fold_left_c (fun m event => add_c m (fst event, snd (snd event))) es Map.empty.

Definition dominance_frontier_c {V E} (p : Prepared.t V E) t := sweep_c p t.
Definition dominance_frontier {V E} (p : Prepared.t V E) t :=
  Cost.value (dominance_frontier_c p t).

(** An ID access pays its encoding callback and its complete trie descent. *)
Definition key_charge i :=
  (2 + N.pos (Pos.size i))%N.

Local Lemma add_cost m d x :
  Cost.ticks (add_c m (d, x)) = (2 * key_charge d + key_charge x)%N.
Proof.
  unfold add_c.
  rewrite !Cost.ticks_bind, Map.find_or_cost, Map.get_cost, Map.set_cost, FinSet.add_cost.
  change ((2 + N.pos (Pos.size d) +
    (2 + N.pos (Pos.size x) + (2 + N.pos (Pos.size d)))) =
    2 * key_charge d + key_charge x)%N.
  unfold key_charge. lia.
Qed.

Local Lemma accumulation_cost {E} (es : list (positive * (E * positive))) m :
  Cost.ticks (fold_left_c (fun m event => add_c m (fst event, snd (snd event))) es m) =
    fold_right (fun event n =>
      1 + 2 * key_charge (fst event) + key_charge (snd (snd event)) + n)%N 0%N es.
Proof.
  revert m. induction es as [|[d [e x]] rest IH]; intro m.
  - reflexivity.
  - rewrite ticks_fold_left_c_cons, IH. cbn [fst snd fold_right].
    rewrite add_cost. lia.
Qed.

(** Total sweep accounting retains event production and charges every row lookup and insertion. *)
Theorem frontier_cost {V E} (p : Prepared.t V E) t :
  Cost.ticks (dominance_frontier_c p t) =
    (Cost.ticks (events_c p t) +
      fold_right (fun event n =>
        1 + 2 * key_charge (fst event) + key_charge (snd (snd event)) + n)%N
        0%N (events p t))%N.
Proof.
  unfold dominance_frontier_c, sweep_c. rewrite Cost.ticks_bind, accumulation_cost.
  reflexivity.
Qed.

Local Lemma fold_project {A B C} (f : C -> B -> C) (g : A -> B) xs initial :
  fold_left (fun acc x => f acc (g x)) xs initial =
    fold_left f (map g xs) initial.
Proof.
  revert initial. induction xs as [|x rest IH]; intro initial; cbn; auto.
Qed.

(** Every supplied exact tree yields exactly the semantic frontier on all named queries. *)
Theorem dominance_frontier_exact {V E} (p : Prepared.t V E) t d x i j :
  Prepared.ready p -> Dom.exact p t ->
  Prepared.id_of p d = Some i -> Prepared.id_of p x = Some j ->
  (frontier_at (dominance_frontier p t) i j <-> in_df (Prepared.graph p) d x).
Proof.
  intros Hready Htree Hd Hx.
  unfold dominance_frontier, dominance_frontier_c, sweep_c.
  rewrite Cost.value_bind, value_fold_left_c.
  change (frontier_at (fold_left (fun m event => add m (fst event, snd (snd event)))
    (events p t) Map.empty) i j <-> in_df (Prepared.graph p) d x).
  rewrite fold_project.
  rewrite fold_spec by (split; [apply Map.wf_empty|intros; rewrite Map.get_empty in *;
    discriminate]).
  unfold frontier_at. rewrite Map.get_empty.
  rewrite in_map_iff. split.
  - intros [[event [Heq Hin]]|[row [Hfalse _]]]; [|discriminate].
    destruct event as [a [e b]]. cbn in Heq. inversion Heq; subst a b.
    apply (events_exact p t d x i j e Hready Htree Hd Hx) in Hin.
    exists e. exact Hin.
  - intros [e He]. left. exists (i, (e, j)). split; [reflexivity|].
    now apply (events_exact p t d x i j e Hready Htree Hd Hx).
Qed.

(** Every materialized frontier row and its containing map are well formed. *)
Theorem dominance_frontier_wf {V E} (p : Prepared.t V E) t :
  rows_wf (dominance_frontier p t).
Proof.
  unfold dominance_frontier, dominance_frontier_c, sweep_c.
  rewrite Cost.value_bind, value_fold_left_c.
  change (rows_wf (fold_left (fun m event => add m (fst event, snd (snd event)))
    (events p t) Map.empty)).
  rewrite fold_project. apply fold_wf.
  split; [apply Map.wf_empty|intros d row Hget; rewrite Map.get_empty in Hget;
    discriminate].
Qed.

(** A row observation comes from an actual labelled event, even for malformed trees. *)
Theorem frontier_event {V E} (p : Prepared.t V E) t i j :
  frontier_at (dominance_frontier p t) i j <->
    exists e, In (i, (e, j)) (events p t).
Proof.
  unfold dominance_frontier, dominance_frontier_c, sweep_c.
  rewrite Cost.value_bind, value_fold_left_c.
  change (frontier_at (fold_left (fun m event => add m (fst event, snd (snd event)))
    (events p t) Map.empty) i j <-> exists e, In (i, (e, j)) (events p t)).
  rewrite fold_project, fold_spec by
    (split; [apply Map.wf_empty|intros d row Hget; rewrite Map.get_empty in Hget;
      discriminate]).
  unfold frontier_at. rewrite Map.get_empty, in_map_iff.
  split.
  - intros [[event [Heq Hin]]|[row [Hfalse _]]]; [|discriminate].
    destruct event as [a [e b]]. cbn in Heq. inversion Heq; subst a b.
    now exists e.
  - intros [e Hin]. left. exists (i, (e, j)). auto.
Qed.

(** Frontier targets are valid prepared IDs, independently of tree exactness. *)
Theorem frontier_target_valid {V E} (p : Prepared.t V E) t i j :
  Prepared.ready p -> frontier_at (dominance_frontier p t) i j ->
  Prepared.valid_id p j.
Proof.
  intros Hready Hin. apply frontier_event in Hin. destruct Hin as [e Hin].
  rewrite events_equation in Hin. apply in_flat_map in Hin.
  destruct Hin as [u [Hu Hin]]. apply in_flat_map in Hin.
  destruct Hin as [[a v] [Hedge Hin]].
  destruct (FinSet.mem positive_encoding u
    (Reach.set p Reach.unrestricted (Prepared.entry_ids p))); [|contradiction].
  apply in_map_iff in Hin. destruct Hin as [d [Heq _]].
  inversion Heq; subst a v.
  pose proof (Prepared.succ_targets p (proj2 (proj2 Hready)) u e j Hedge) as Hj.
  exists (Graph.target (Prepared.graph p) e). split; [|exact Hj].
  apply (Prepared.ids_domain p (proj2 (proj2 Hready))). now exists j.
Qed.

(** Reference resource premises describe storage and genuine external accessor callbacks. *)
Record resources {V E} (p : Prepared.t V E) t
    (n m l b : nat) (w a q h s : N) : Prop := Resources {
  nodes_bound : (length (Graph.nodes (Prepared.graph p)) <= n)%nat;
  universe_bound : (length (Reach.universe p) <= n)%nat;
  entries_bound : (length (Prepared.entry_ids p) <= l)%nat;
  bindings_bound : (Map.size (Dom.idom t) <= b)%nat;
  skeleton_bound : (MapCost.skeleton_nodes (Dom.idom t) <= s)%N;
  width_bound : forall i, Prepared.valid_id p i -> (N.pos (Pos.size i) <= w)%N;
  name_lookup_bound : forall v, In v (Graph.nodes (Prepared.graph p)) ->
    (Cost.ticks (Prepared.id_of_c p v) <= a)%N;
  successor_lookup_bound : forall i, Prepared.valid_id p i ->
    (Cost.ticks (Prepared.succ_edges_c p i) <= q)%N;
  predecessor_lookup_bound : forall i, Prepared.valid_id p i ->
    (Cost.ticks (Prepared.pred_edges_c p i) <= q)%N;
  successor_length_bound : forall i, Prepared.valid_id p i ->
    (length (Prepared.succ_edges p i) <= m)%nat;
  predecessor_length_bound : forall i, Prepared.valid_id p i ->
    (length (Prepared.pred_edges p i) <= m)%nat;
  admission_bound : forall i, Prepared.valid_id p i ->
    (Cost.ticks (Scope.admits_c Reach.unrestricted i) <= h)%N
}.

Arguments nodes_bound {V E p t n m l b w a q h s} _.
Arguments universe_bound {V E p t n m l b w a q h s} _.
Arguments entries_bound {V E p t n m l b w a q h s} _.
Arguments bindings_bound {V E p t n m l b w a q h s} _.
Arguments skeleton_bound {V E p t n m l b w a q h s} _.
Arguments width_bound {V E p t n m l b w a q h s} _ _ _.
Arguments name_lookup_bound {V E p t n m l b w a q h s} _ _ _.
Arguments successor_lookup_bound {V E p t n m l b w a q h s} _ _ _.
Arguments predecessor_lookup_bound {V E p t n m l b w a q h s} _ _ _.
Arguments successor_length_bound {V E p t n m l b w a q h s} _ _ _.
Arguments predecessor_length_bound {V E p t n m l b w a q h s} _ _ _.
Arguments admission_bound {V E p t n m l b w a q h s} _ _ _.

(** Universe work includes callback lookup, list filtering and quadratic duplicate removal. *)
Definition universe_work n w a := (n * (a + 2 + n * (w + 1)))%N.

(** A reference successor query pays its index, admission and universe-membership traversals. *)
Definition successor_work n m w q h := (q + m * (h + 2 + n * (w + 1)))%N.

(** Reference reachability includes its complete adjacency-credit pass and bounded work stack. *)
Definition reach_work n m l w a q h :=
  let next := successor_work n m w q h in
  (universe_work n w a + n * (1 + h + l * (w + 1)) +
    n * (2 + next + m) + n +
    (n * (m + 2) + 1) * (12 + next + m + 2 * n * (w + 1) + w))%N.

(** Parent-budget construction scans the supplied physical map skeleton on every call. *)
Definition scan_work s := (TrieCost.trie_k * (1 + s))%N.

(** A boundary cache pays its full parent walk and set construction. *)
Definition ancestor_work b w s := (scan_work s + (b + 1) * (2 * w + 13))%N.

(** A stopped source walk also pays the boundary cache and both map-size scans. *)
Definition runner_work b w s := (2 * scan_work s + (b + 1) * (4 * w + 25))%N.

(** Event production includes reference reachability, all edge walks and every event-list copy. *)
Definition events_work n m l b w a q h s :=
  (reach_work n m l w a q h + universe_work n w a +
    n * (1 + q + m * (5 + 2 * w + runner_work b w s + 3 * (b + 1))))%N.

(** The delivered sweep has a coarse polynomial bound including complete event production. *)
Definition sweep_work n m l b w a q h s :=
  (events_work n m l b w a q h s + n * m * (b + 1) * (7 + 3 * w))%N.

(** A list sum needs callback bounds on the traversed input domain alone. *)
Theorem sum_bound_on {A} (f : A -> N) k xs :
  (forall x, In x xs -> (f x <= k)%N) ->
  (fold_right (fun x n => 1 + f x + n)%N 0%N xs <=
    N.of_nat (length xs) * (k + 1))%N.
Proof.
  induction xs as [|x rest IH]; intro Hf; cbn [fold_right length]; [lia|].
  rewrite Nat2N.inj_succ.
  pose proof (Hf x (or_introl eq_refl)) as Hhead.
  specialize (IH ltac:(intros y Hy; apply Hf; now right)). nia.
Qed.

(** Charged right folds inherit callback bounds on their actual list domain. *)
Theorem fold_right_bound_on {A B} (f : A -> B -> Cost.t B) k xs initial :
  (forall x acc, In x xs -> (Cost.ticks (f x acc) <= k)%N) ->
  (Cost.ticks (fold_right_c f initial xs) <= N.of_nat (length xs) * (k + 1))%N.
Proof.
  induction xs as [|x rest IH]; intro Hf; [reflexivity|].
  rewrite ticks_fold_right_c_cons.
  pose proof (Hf x (Cost.value (fold_right_c f initial rest)) (or_introl eq_refl)) as Hhead.
  specialize (IH ltac:(intros y acc Hy; apply Hf; now right)).
  cbn [length]. rewrite Nat2N.inj_succ. nia.
Qed.

Local Lemma filter_map_length {A B} (f : A -> option B) xs :
  (length (filter_map f xs) <= length xs)%nat.
Proof.
  unfold filter_map. induction xs as [|x rest IH]; cbn [fold_right length]; [lia|].
  destruct (f x); cbn [length]; lia.
Qed.

Local Lemma filter_map_forall {A B} (f : A -> option B) (P : B -> Prop) xs :
  (forall x y, In x xs -> f x = Some y -> P y) -> Forall P (filter_map f xs).
Proof.
  unfold filter_map. induction xs as [|x rest IH]; intro Hf;
    cbn [fold_right]; [constructor|].
  destruct (f x) as [y|] eqn:Hy.
  - constructor; [eapply Hf; [now left|exact Hy]|].
    apply IH. intros a b Ha Hb. exact (Hf a b (or_intror Ha) Hb).
  - apply IH. intros a b Ha Hb. exact (Hf a b (or_intror Ha) Hb).
Qed.

(** Valid prepared IDs are exactly the universe's finite support. *)
Theorem universe_support {V E} (p : Prepared.t V E) :
  Forall (Prepared.valid_id p) (Reach.universe p).
Proof.
  apply Forall_forall. intros i Hi. now apply Reach.universe_spec.
Qed.

(** Every cached successor target stays inside the valid prepared-ID domain. *)
Theorem successor_support {V E} (p : Prepared.t V E) i :
  Prepared.ready p ->
  Forall (fun edge => Prepared.valid_id p (snd edge)) (Prepared.succ_edges p i).
Proof.
  intro Hready. apply Forall_forall. intros [e j] Hin. cbn [snd].
  pose proof (Prepared.succ_targets p (proj2 (proj2 Hready)) i e j Hin) as Hj.
  exists (Graph.target (Prepared.graph p) e). split; [|exact Hj].
  apply (Prepared.ids_domain p (proj2 (proj2 Hready))). now exists j.
Qed.

(** Every cached predecessor source stays inside the valid prepared-ID domain. *)
Theorem predecessor_support {V E} (p : Prepared.t V E) i :
  Prepared.ready p -> Prepared.valid_id p i ->
  Forall (fun edge => Prepared.valid_id p (snd edge)) (Prepared.pred_edges p i).
Proof.
  intros Hready [v [Hv Hi]]. apply Forall_forall. intros [e j] Hin. cbn [snd].
  apply (Prepared.pred_agrees p (proj2 (proj2 Hready)) v i e j Hi) in Hin.
  destruct Hin as [Hs [_ [_ Hj]]]. exists (Graph.source (Prepared.graph p) e). auto.
Qed.

(** Exact supplied trees keep every followed parent inside the prepared-ID domain. *)
Theorem parent_support {V E} (p : Prepared.t V E) t i j :
  Prepared.ready p -> Dom.exact p t ->
  Map.get positive_encoding i (Dom.idom t) = Some j -> Prepared.valid_id p j.
Proof.
  intros Hready Htree Hget.
  destruct (Dom.idom_domain p t Htree i j Hget)
    as [v [d [_ [Hd _]]]].
  pose proof (Prepared.id_of_name_of p j d (proj2 (proj2 Hready)) Hd) as Hj.
  exists d. split; [|exact Hj].
  apply (Prepared.ids_domain p (proj2 (proj2 Hready))). now exists j.
Qed.

(** List membership charges every visited comparison and its traversal overhead. *)
Theorem member_cost v xs w :
  (forall x, (Cost.ticks (Map.code_compare_c v x) <= w)%N) ->
  (Cost.ticks (member_c v xs) <= N.of_nat (length xs) * (w + 1))%N.
Proof.
  intro Hcompare. unfold member_c. apply ticks_existsb_c_le.
  intro x. unfold eq_c. rewrite Cost.ticks_map. apply Hcompare.
Qed.

(** List removal pays its complete traversal and cannot lengthen its input. *)
Theorem remove_cost v xs w :
  (forall x, (Cost.ticks (Map.code_compare_c v x) <= w)%N) ->
  (Cost.ticks (remove_c v xs) <= N.of_nat (length xs) * (w + 1))%N /\
    (length (Cost.value (remove_c v xs)) <= length xs)%nat.
Proof.
  intro Hcompare. induction xs as [|x rest [IHcost IHlength]].
  - split; [reflexivity|cbn; lia].
  - cbn [remove_c]. autorewrite with galois_cost.
    pose proof (Hcompare x) as Hhead.
    assert (Heqcost : (Cost.ticks (eq_c v x) <= w)%N)
      by (unfold eq_c; rewrite Cost.ticks_map; exact Hhead).
    cbn [length]. rewrite Nat2N.inj_succ.
    destruct (Cost.value (eq_c v x)); cbn [length]; split; nia.
Qed.

Local Lemma nodup_cost (P : positive -> Prop) xs n w :
  Forall P xs -> (length xs <= n)%nat ->
  (forall v, P v -> forall x, (Cost.ticks (Map.code_compare_c v x) <= w)%N) ->
  (Cost.ticks (nodup_c xs) <=
    N.of_nat (length xs) * (1 + N.of_nat n * (w + 1)))%N /\
  Forall P (Cost.value (nodup_c xs)) /\
    (length (Cost.value (nodup_c xs)) <= length xs)%nat.
Proof.
  intros Hsupport Hlength Hcompare. induction Hsupport as [|v rest Hv Hrest IH].
  - split; [reflexivity|]. split; [constructor|cbn; lia].
  - cbn [length] in Hlength.
    destruct (IH ltac:(lia)) as [IHcost [IHsupport IHlength]].
    cbn [nodup_c]. autorewrite with galois_cost.
    pose proof (member_cost v rest w (Hcompare v Hv)) as Hmember.
    cbn [length]. rewrite Nat2N.inj_succ.
    destruct (Cost.value (member_c v rest)); cbn [length]; split;
      [nia|split; [exact IHsupport|lia]|nia|split; [constructor; assumption|lia]].
Qed.

(** Positive-key lookup charges are independent of map shape and stored values. *)
Theorem positive_get_cost {A} (table : Map.t positive A) i w :
  (N.pos (Pos.size i) <= w)%N ->
  (Cost.ticks (Map.get_c positive_encoding i table) <= 2 + w)%N.
Proof.
  intro Hwidth. rewrite Map.get_cost.
  change (2 + N.pos (Pos.size i) <= 2 + w)%N. lia.
Qed.

(** Positive set membership retains its encoder and full key traversal. *)
Theorem positive_mem_cost table i w :
  (N.pos (Pos.size i) <= w)%N ->
  (Cost.ticks (FinSet.mem_c positive_encoding i table) <= 2 + w)%N.
Proof.
  intro Hwidth. rewrite FinSet.mem_cost.
  change (2 + N.pos (Pos.size i) <= 2 + w)%N. lia.
Qed.

(** Universe cost includes every ID callback and the complete quadratic duplicate pass. *)
Theorem universe_cost {V E} (p : Prepared.t V E) t n m l b w a q h s :
  Prepared.ready p -> resources p t n m l b w a q h s ->
  (forall v, Prepared.valid_id p v ->
    forall x, (Cost.ticks (Map.code_compare_c v x) <= w)%N) ->
  (Cost.ticks (universe_c p) <= universe_work (N.of_nat n) w a)%N.
Proof.
  intros Hready Hr Hcompare.
  set (raw := Cost.value (filter_map_c (Prepared.id_of_c p)
    (Graph.nodes (Prepared.graph p)))).
  assert (Hrawsupport : Forall (Prepared.valid_id p) raw).
  { unfold raw. rewrite value_filter_map_c.
    apply filter_map_forall. intros v i Hv Hi. exists v. split; [exact Hv|exact Hi]. }
  assert (Hrawlength : (length raw <= n)%nat).
  { unfold raw. rewrite value_filter_map_c.
    eapply Nat.le_trans; [apply filter_map_length|exact (nodes_bound Hr)]. }
  assert (Hfilter : (Cost.ticks (filter_map_c (Prepared.id_of_c p)
    (Graph.nodes (Prepared.graph p))) <= N.of_nat n * (a + 1))%N).
  { rewrite ticks_filter_map_c.
    eapply N.le_trans.
    - apply sum_bound_on. intros v Hv. now apply (name_lookup_bound Hr).
    - pose proof (nodes_bound Hr). nia. }
  unfold universe_c. rewrite Cost.ticks_bind.
  fold raw. destruct (nodup_cost (Prepared.valid_id p) raw n w
    Hrawsupport Hrawlength Hcompare) as [Hnodup _].
  assert (HrawN : (N.of_nat (length raw) <= N.of_nat n)%N) by lia.
  assert (Hnodup' : (Cost.ticks (nodup_c raw) <=
    N.of_nat n * (1 + N.of_nat n * (w + 1)))%N).
  { eapply N.le_trans; [exact Hnodup|].
    apply N.mul_le_mono; [exact HrawN|apply N.le_refl]. }
  unfold universe_work.
  nia.
Qed.

(** Successor cost expands index lookup, admission and list-membership work. *)
Theorem successors_cost {V E} (p : Prepared.t V E) t n m l b w a q h s i :
  Prepared.ready p -> resources p t n m l b w a q h s ->
  (forall v, Prepared.valid_id p v ->
    forall x, (Cost.ticks (Map.code_compare_c v x) <= w)%N) ->
  Prepared.valid_id p i ->
  (Cost.ticks (successors_c p Reach.unrestricted (Reach.universe p) i) <=
    successor_work (N.of_nat n) (N.of_nat m) w q h)%N /\
  Forall (Prepared.valid_id p)
    (Cost.value (successors_c p Reach.unrestricted (Reach.universe p) i)) /\
  (length (Cost.value (successors_c p Reach.unrestricted (Reach.universe p) i)) <= m)%nat.
Proof.
  intros Hready Hr Hcompare Hi.
  assert (Htargets : Forall (Prepared.valid_id p) (map snd (Prepared.succ_edges p i))).
  { apply Forall_forall. intros v Hv. apply in_map_iff in Hv.
    destruct Hv as [[e j] [Heq Hin]]. cbn in Heq. subst j.
    exact (proj1 (Forall_forall _ _) (successor_support p i Hready) (e, v) Hin). }
  assert (Hlength := successor_length_bound Hr i Hi).
  assert (Hmap : (Cost.ticks (map_c (fun edge => Cost.ret (snd edge))
    (Prepared.succ_edges p i)) <= N.of_nat m)%N).
  { pose proof (ticks_map_c_le (fun edge : E * positive => Cost.ret (snd edge))
      0%N (Prepared.succ_edges p i) ltac:(intros; reflexivity)) as Hmap.
    nia. }
  assert (Hfilter : (Cost.ticks (filter_c (fun x =>
    let* admitted := Scope.admits_c Reach.unrestricted x in
    let* valid := member_c x (Reach.universe p) in
    Cost.ret (admitted && valid)) (map snd (Prepared.succ_edges p i))) <=
      N.of_nat m * (h + N.of_nat n * (w + 1) + 1))%N).
  { rewrite ticks_filter_c. eapply N.le_trans.
    - apply (sum_bound_on _ (h + N.of_nat n * (w + 1))%N). intros v Hv.
      pose proof (proj1 (Forall_forall _ _) Htargets v Hv) as Hvalid.
      pose proof (admission_bound Hr v Hvalid) as Hadmission.
      pose proof (member_cost v (Reach.universe p) w (Hcompare v Hvalid)) as Hmember.
      pose proof (universe_bound Hr).
      rewrite !Cost.ticks_bind. autorewrite with galois_cost. nia.
    - rewrite length_map. apply N.mul_le_mono; [lia|apply N.le_refl]. }
  split.
  - unfold successors_c. rewrite !Cost.ticks_bind, value_map_c.
    fold (Prepared.succ_edges p i).
    pose proof (successor_lookup_bound Hr i Hi). unfold successor_work.
    replace (map (fun x : E * positive => Cost.value (Cost.ret (snd x)))
      (Prepared.succ_edges p i)) with (map snd (Prepared.succ_edges p i)) by reflexivity.
    nia.
  - rewrite successors_value. unfold Reach.successors.
    split.
    + apply Forall_forall. intros v Hv. apply filter_In in Hv.
      exact (proj1 (Forall_forall _ _) Htargets v (proj1 Hv)).
    + eapply Nat.le_trans; [apply List.filter_length_le|].
      rewrite length_map. exact Hlength.
Qed.

(** Root filtering pays supplied-root multiplicity even when duplicate IDs are rejected. *)
Theorem roots_cost {V E} (p : Prepared.t V E) t n m l b w a q h s :
  resources p t n m l b w a q h s ->
  (forall v, Prepared.valid_id p v ->
    forall x, (Cost.ticks (Map.code_compare_c v x) <= w)%N) ->
  (Cost.ticks (roots_c Reach.unrestricted (Reach.universe p) (Prepared.entry_ids p)) <=
    N.of_nat n * (1 + h + N.of_nat l * (w + 1)))%N /\
  Forall (Prepared.valid_id p)
    (Cost.value (roots_c Reach.unrestricted (Reach.universe p) (Prepared.entry_ids p))) /\
  (length (Cost.value (roots_c Reach.unrestricted
    (Reach.universe p) (Prepared.entry_ids p))) <= n)%nat.
Proof.
  intros Hr Hcompare. split.
  - unfold roots_c. rewrite ticks_filter_c.
    eapply N.le_trans.
    + apply (sum_bound_on _ (h + N.of_nat l * (w + 1))%N). intros v Hv.
      pose proof (proj1 (Reach.universe_spec p v) Hv) as Hvalid.
      pose proof (member_cost v (Prepared.entry_ids p) w (Hcompare v Hvalid)) as Hmember.
      pose proof (admission_bound Hr v Hvalid) as Hadmission.
      pose proof (entries_bound Hr).
      rewrite !Cost.ticks_bind. autorewrite with galois_cost. nia.
    + apply N.mul_le_mono; [pose proof (universe_bound Hr); lia|lia].
  - rewrite roots_value. unfold Reach.roots_in. split.
    + apply Forall_forall. intros v Hv. apply filter_In in Hv.
      now apply Reach.universe_spec, (proj1 Hv).
    + eapply Nat.le_trans; [apply List.filter_length_le|exact (universe_bound Hr)].
Qed.

(** Budget construction visits every candidate adjacency and counts every successor cell. *)
Theorem credit_cost next (P : positive -> Prop) all n m k :
  Forall P all -> (length all <= n)%nat ->
  (forall v, P v -> (length (Cost.value (next v)) <= m)%nat /\
    (Cost.ticks (next v) <= k)%N) ->
  (Cost.ticks (credit_c next all) <= N.of_nat n * (2 + k + N.of_nat m))%N /\
  (Cost.value (credit_c next all) <= n * (m + 1))%nat.
Proof.
  intros Hsupport Hlength Hnext. split.
  - unfold credit_c. eapply N.le_trans.
    + apply (fold_right_bound_on _ (1 + k + N.of_nat m)%N). intros v credit Hv.
      destruct (Hnext v (proj1 (Forall_forall _ _) Hsupport v Hv)) as [Hlen Hcost].
      autorewrite with galois_cost. nia.
    + apply N.mul_le_mono; lia.
  - rewrite credit_value.
    assert (Hcredit : (Reach.credit (fun v => Cost.value (next v)) all <=
      length all * (m + 1))%nat).
    { clear Hlength. induction Hsupport as [|v rest Hv Hrest IH];
        cbn [Reach.credit length]; [lia|].
      destruct (Hnext v Hv) as [Hlen _]. nia. }
    nia.
Qed.

End FrontierSweep.
