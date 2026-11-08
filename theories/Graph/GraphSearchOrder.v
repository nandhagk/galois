(** * Search orders and parent paths

    Reverse postorder and topological inspection consume the same result and labelled trace.
    For example, a cyclic search returns the first actual back-edge event.
    Builds on: GraphSearch, GraphSearchSpec and CostLoop. *)

From Stdlib Require Import List Bool PArith NArith Lia Permutation Relation_Operators.
From Galois.Cost Require Import CostMonad CostList CostLoop.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearchSpec GraphSearch
  GraphSearchInvariant GraphSearchExact.
Import List.ListNotations Cost.Notations.

Module SearchOrder.
Local Open Scope nat_scope.

Definition rpo_c {E} (r : Search.result E) := rev_c (Search.postorder r).
Definition rpo {E} (r : Search.result E) := Cost.value (rpo_c r).

(** Reverse postorder reverses the actual finishing order. *)
Theorem rpo_equation {E} (r : Search.result E) : rpo r = rev (Search.postorder r).
Proof.
  apply value_rev_c.
Qed.

Local Lemma before_from_indices {A} (xs : list A) i j u v :
  i < j -> nth_error xs i = Some u -> nth_error xs j = Some v -> before xs u v.
Proof.
  revert i j. induction xs as [|a rest IH]; intros [|i] [|j] Hlt Hu Hv;
    cbn [nth_error] in *; try lia; try discriminate.
  - inversion Hu; subst a.
    apply nth_error_split in Hv. destruct Hv as [left [right [Hrest Hlength]]].
    subst rest. exists [], left, right. reflexivity.
  - destruct (IH i j ltac:(lia) Hu Hv) as [left [middle [right Hrest]]].
    exists (a :: left), middle, right. cbn. now rewrite Hrest.
Qed.

Local Lemma before_reverse {A} (xs : list A) u v :
  before xs u v -> before (rev xs) v u.
Proof.
  intros [left [middle [right ->]]].
  exists (rev right), (rev middle), (rev left).
  rewrite rev_app_distr. cbn [rev].
  rewrite rev_app_distr. cbn [rev].
  rewrite <- !app_assoc. reflexivity.
Qed.

(** A strict recorded tree ancestor precedes its descendant in reverse postorder. *)
Theorem rpo_ancestor {V E} (p : Prepared.t V E) scope roots r u v :
  Search.exact p scope roots r ->
  In u (Search.preorder r) -> In v (Search.preorder r) ->
  Search.ancestor r u v -> u <> v -> before (rpo r) u v.
Proof.
  intros Hexact Hu Hv Hancestor Hne.
  apply (proj2 (Search.ancestor_iff _ _ _ _ Hexact u v Hu Hv)) in Hancestor.
  destruct Hancestor as [a [b [c [d [_ [_ [Hc [Hd [_ Hle]]]]]]]]].
  pose proof (proj1 (Search.post_num_index _ _ _ _ Hexact v c) Hc) as Hiv.
  pose proof (proj1 (Search.post_num_index _ _ _ _ Hexact u d) Hd) as Hiu.
  assert (Hcd : c <> d).
  { intro Heq. subst d. apply Hne. congruence. }
  rewrite rpo_equation. apply before_reverse.
  eapply before_from_indices; [|exact Hiv|exact Hiu].
  apply Pos2Nat.inj_le in Hle.
  pose proof (Pos2Nat.is_pos c). pose proof (Pos2Nat.is_pos d).
  assert (Hnatne : Pos.to_nat c <> Pos.to_nat d).
  { intro Heq. apply Hcd. now apply Pos2Nat.inj. }
  lia.
Qed.

(** Every selected parent precedes its child in reverse postorder. *)
Theorem rpo_parent {V E} (p : Prepared.t V E) scope roots r v e u :
  Search.exact p scope roots r ->
  Map.get positive_encoding v (Search.parent_edge r) = Some (e, u) ->
    before (rpo r) u v.
Proof.
  intros Hexact Hparent.
  destruct (Search.parent_edge_valid _ _ _ _ Hexact v e u Hparent) as [_ [Hu Hv]].
  eapply rpo_ancestor; [exact Hexact|exact Hu|exact Hv| |].
  - apply rt_step. now exists e.
  - intro Heq. subst u.
    pose proof (Search.parent_finite _ _ _ _ Hexact v) as Hacc.
    assert (Hself : forall x, Acc
      (fun u v => exists e, Map.get positive_encoding v (Search.parent_edge r) = Some (e, u)) x ->
      Map.get positive_encoding x (Search.parent_edge r) <> Some (e, x)).
    { intros x Ha. induction Ha as [x Ha IH].
      intro Hget. apply (IH x); [now exists e|exact Hget]. }
    exact (Hself v Hacc Hparent).
Qed.

(** Every eligible edge from a discovered source goes forward in RPO or retreats to an ancestor. *)
Theorem rpo_edge_spec {V E} (p : Prepared.t V E) scope roots u e v :
  Prepared.ready p ->
  let r := SearchRun.dfs p scope roots in
  In u (Search.preorder r) -> Prepared.arc p u e v -> Scope.admits scope v = true ->
    before (rpo r) u v \/ Search.ancestor r v u.
Proof.
  intros Hready.
  pose proof (SearchExact.final_intervals p scope roots Hready) as Hinterval.
  pose proof (SearchInvariant.roots_history p scope roots _ Hready
    SearchInvariant.initial_representation SearchInvariant.initial_history) as Hhistory.
  unfold SearchRun.dfs. rewrite SearchRun.run_equation.
  destruct (SearchRun.reference_roots p scope roots SearchRun.initial) as [c evs].
  cbn [fst] in Hinterval, Hhistory |- *. intros Hu Harc Hallowed.
  rewrite SearchRun.result_equation in Hu. cbn [Search.preorder] in Hu.
  apply (proj2 (in_rev _ _)) in Hu.
  assert (Hpost : In u (SearchRun.post_rev c)).
  { exact (Permutation_in u (SearchInvariant.partition _ Hhistory) Hu). }
  destruct (SearchExact.finished_edges _ _ _ _ Hinterval u Hpost e v
    (SearchInvariant.arc_successor p u e v Hready Harc) Hallowed)
    as [[j [k [Hj [Hk Hlt]]]]|Hback].
  - left. rewrite rpo_equation, SearchRun.result_equation.
    cbn [Search.postorder]. rewrite rev_involutive.
    pose proof (proj2 (SearchInvariant.numbering_order _ _ _
      (SearchInvariant.post_numbering _ Hhistory) v u j k Hj Hk) Hlt) as Hbefore.
    apply before_reverse in Hbefore. now rewrite rev_involutive in Hbefore.
  - right. rewrite SearchRun.result_equation. exact Hback.
Qed.

(** Ready search orders parents before strict descendants and every semantically non-back edge forward. *)
Theorem rpo_spec {V E} (p : Prepared.t V E) scope roots :
  Prepared.ready p ->
  let r := SearchRun.dfs p scope roots in
  (forall u v, In u (Search.preorder r) -> In v (Search.preorder r) ->
    Search.ancestor r u v -> u <> v -> before (rpo r) u v) /\
  (forall u e v, In u (Search.preorder r) -> Prepared.arc p u e v ->
    Scope.admits scope v = true -> ~ Search.ancestor r v u -> before (rpo r) u v).
Proof.
  intro Hready. split.
  - intros u v Hu Hv Hancestor Hne.
    exact (rpo_ancestor p scope roots _ u v (SearchExact.dfs_exact p scope roots Hready)
      Hu Hv Hancestor Hne).
  - intros u e v Hu Harc Hallowed Hnot.
    destruct (rpo_edge_spec p scope roots u e v Hready Hu Harc Hallowed); tauto.
Qed.

(** The first back-edge inspection keeps its actual label and endpoints. *)
Fixpoint first_back {E} (evs : list (Search.event E)) : option (E * positive * positive) :=
  match evs with
  | [] => None
  | Search.Edge e u v Search.Back :: _ => Some (e, u, v)
  | _ :: rest => first_back rest
  end.

Definition topological {V E} (p : Prepared.t V E) scope roots
    : list positive + (E * positive * positive) :=
  match first_back (SearchRun.events p scope roots) with
  | None => inl (rpo (SearchRun.dfs p scope roots))
  | Some edge => inr edge
  end.

Definition dag_ok {V E} (p : Prepared.t V E) scope roots :=
  match first_back (SearchRun.events p scope roots) with None => true | Some _ => false end.

(** Every returned obstruction is a back-edge occurrence in the inspected trace. *)
Theorem first_back_sound {E} (evs : list (Search.event E)) e u v :
  first_back evs = Some (e, u, v) -> In (Search.Edge e u v Search.Back) evs.
Proof.
  induction evs as [|ev rest IH]; [discriminate|].
  destruct ev as [w via|a x y k|w parent]; cbn [first_back];
    try (intro H; right; now apply IH).
  destruct k; cbn [first_back]; try (intro H; right; now apply IH).
  intro H. inversion H. now left.
Qed.

(** Absence of a returned obstruction means there are no back-edge events anywhere in the trace. *)
Theorem first_back_none {E} (evs : list (Search.event E)) :
  first_back evs = None <->
    forall e u v, ~ In (Search.Edge e u v Search.Back) evs.
Proof.
  induction evs as [|ev rest IH].
  - split; [intros _ e u v Hin; exact Hin|reflexivity].
  - destruct ev as [w via|a x y k|w parent]; try destruct k;
      cbn [first_back In] in *;
      try (split; [discriminate|intro H; exfalso; apply (H a x y); now left]);
      rewrite IH; split.
    all: try (intros H e u v [Heq|Hin]; [discriminate|eapply H; exact Hin]).
    all: intros H e u v Hin; apply (H e u v); now right.
Qed.

(** The obstruction alternative preserves its exact labelled trace witness. *)
Theorem topological_back_event {V E} (p : Prepared.t V E) scope roots e u v :
  topological p scope roots = inr (e, u, v) ->
    In (Search.Edge e u v Search.Back) (SearchRun.events p scope roots).
Proof.
  unfold topological. destruct (first_back (SearchRun.events p scope roots)) as [edge|]
    eqn:Hback; [|discriminate].
  intro H. inversion H; subst edge. now apply first_back_sound.
Qed.

(** The order alternative contains the same RPO and a trace without back-edge events. *)
Theorem topological_order_event {V E} (p : Prepared.t V E) scope roots order :
  topological p scope roots = inl order ->
    order = rpo (SearchRun.dfs p scope roots) /\
    forall e u v, ~ In (Search.Edge e u v Search.Back) (SearchRun.events p scope roots).
Proof.
  unfold topological. destruct (first_back (SearchRun.events p scope roots)) eqn:Hback;
    [discriminate|].
  intro H. inversion H; subst order. split; [reflexivity|].
  now apply first_back_none.
Qed.

(** Parent walking follows the stored labelled edge, without reclassifying its endpoints. *)
Definition path_step_c {E} (r : Search.result E) (state : positive * list E)
    : Cost.t ((positive * list E) + (positive * list E)) :=
  let '(v, es) := state in
  let* parent := Map.get_c positive_encoding v (Search.parent_edge r) in
  Cost.ret
    (match parent with
    | None => inr (v, es)
    | Some (e, u) => inl (u, e :: es)
    end).

(** A path walk step reads precisely the selected parent binding. *)
Theorem path_step_equation {E} (r : Search.result E) v es :
  Cost.value (path_step_c r (v, es)) =
    match Map.get positive_encoding v (Search.parent_edge r) with
    | None => inr (v, es)
    | Some (e, u) => inl (u, e :: es)
    end.
Proof.
  reflexivity.
Qed.

(** The caller supplies no fuel and malformed cyclic parent data produces explicit failure. *)
Definition tree_path_c {V E} (_p : Prepared.t V E) (r : Search.result E) v :=
  let* visited := FinSet.mem_c positive_encoding v (Search.visited r) in
  if visited then
    let* n := length_c (Search.preorder r) in
    let* budget := Prepared.budget_c n in
    let* answer := iterate (path_step_c r) budget (v, []) in
    Cost.ret (match answer with inl _ => None | inr (_, es) => Some es end)
  else Cost.ret None.

Definition tree_path {V E} (p : Prepared.t V E) (r : Search.result E) v :=
  Cost.value (tree_path_c p r v).

(** Path reconstruction uses a budget greater than the number of recorded vertices. *)
Theorem tree_path_equation {V E} (p : Prepared.t V E) (r : Search.result E) v :
  tree_path p r v =
    if FinSet.mem positive_encoding v (Search.visited r) then
      match Cost.value
        (iterate (path_step_c r) (Pos.of_succ_nat (length (Search.preorder r))) (v, [])) with
      | inl _ => None
      | inr (_, es) => Some es
      end
    else None.
Proof.
  unfold tree_path, tree_path_c. autorewrite with galois_cost.
  fold (FinSet.mem positive_encoding v (Search.visited r)).
  destruct (FinSet.mem positive_encoding v (Search.visited r)); [|reflexivity].
  autorewrite with galois_cost. rewrite Prepared.budget_value. reflexivity.
Qed.

Local Lemma scoped_path_end {V E} (p : Prepared.t V E) scope u es v :
  Search.scoped_path p scope u es v ->
    Prepared.valid_id p v /\ Scope.admits scope v = true.
Proof.
  intro Hpath. induction Hpath as [v Hvalid Hadmit|u e v es z Hvalid Hadmit Harc Hpath IH].
  - auto.
  - exact IH.
Qed.

(** Every recorded vertex is a valid admitted endpoint. *)
Theorem recorded_admitted {V E} (p : Prepared.t V E) scope roots r v :
  Search.exact p scope roots r -> In v (Search.preorder r) ->
    Prepared.valid_id p v /\ Scope.admits scope v = true.
Proof.
  intros Hexact Hin. apply (Search.pre_complete _ _ _ _ Hexact) in Hin.
  destruct Hin as [root [es [_ Hpath]]]. now apply scoped_path_end in Hpath.
Qed.

Local Lemma wf_no_self {A} (R : A -> A -> Prop) :
  well_founded R -> forall x, ~ R x x.
Proof.
  intro Hwf. assert (Hacc : forall x, Acc R x -> ~ R x x).
  { intros x Ha. induction Ha as [x Ha IH].
    intro Hself. exact (IH x Hself Hself). }
  intro x. apply Hacc, Hwf.
Qed.

(** Every stored parent has a strictly smaller actual entry rank. *)
Theorem parent_rank {V E} (p : Prepared.t V E) scope roots r v e u a b :
  Search.exact p scope roots r ->
  Map.get positive_encoding v (Search.parent_edge r) = Some (e, u) ->
  Map.get positive_encoding u (Search.pre_num r) = Some a ->
  Map.get positive_encoding v (Search.pre_num r) = Some b -> (a < b)%positive.
Proof.
  intros Hexact Hparent Ha Hb.
  destruct (Search.parent_edge_valid _ _ _ _ Hexact v e u Hparent) as [_ [Hu Hv]].
  assert (Hancestor : Search.ancestor r u v).
  { apply rt_step. now exists e. }
  apply (proj2 (Search.ancestor_iff _ _ _ _ Hexact u v Hu Hv)) in Hancestor.
  destruct Hancestor as [x [y [z [t [Hx [Hy [_ [_ [Hle _]]]]]]]]].
  rewrite Ha in Hx. rewrite Hb in Hy. inversion Hx; inversion Hy; subst x y.
  destruct (Pos.eq_dec a b) as [Heq|Hne].
  - subst b. exfalso.
    pose proof (proj1 (Search.pre_num_index _ _ _ _ Hexact u a) Ha) as Hiu.
    pose proof (proj1 (Search.pre_num_index _ _ _ _ Hexact v a) Hb) as Hiv.
    assert (Heq : u = v) by congruence. subst u.
    apply (wf_no_self _ (Search.parent_finite _ _ _ _ Hexact) v).
    now exists e.
  - apply Pos2Nat.inj_lt. apply Pos2Nat.inj_le in Hle.
    assert (Hnatne : Pos.to_nat a <> Pos.to_nat b).
    { intro Heq. apply Hne. now apply Pos2Nat.inj. }
    lia.
Qed.

Definition path_rank {E} (r : Search.result E) v :=
  match Map.get positive_encoding v (Search.pre_num r) with
  | None => 0
  | Some k => Pos.to_nat k
  end.

(** Recorded vertices have positive entry rank bounded by the preorder length. *)
Theorem path_rank_bound {V E} (p : Prepared.t V E) scope roots r v :
  Search.exact p scope roots r -> In v (Search.preorder r) ->
    0 < path_rank r v <= length (Search.preorder r).
Proof.
  intros Hexact Hin. apply In_nth_error in Hin. destruct Hin as [i Hi].
  assert (Hindex : Nat.pred (Pos.to_nat (Pos.of_succ_nat i)) = i).
  { rewrite SuccNat2Pos.id_succ. reflexivity. }
  assert (Hget : Map.get positive_encoding v (Search.pre_num r) = Some (Pos.of_succ_nat i)).
  { apply (proj2 (Search.pre_num_index _ _ _ _ Hexact v (Pos.of_succ_nat i))).
    now rewrite Hindex. }
  unfold path_rank. rewrite Hget, SuccNat2Pos.id_succ.
  assert (Hlt : i < length (Search.preorder r)).
  { apply nth_error_Some. congruence. }
  lia.
Qed.

(** Following a selected parent strictly decreases the recorded entry rank. *)
Theorem path_rank_decreases {V E} (p : Prepared.t V E) scope roots r v e u :
  Search.exact p scope roots r ->
  Map.get positive_encoding v (Search.parent_edge r) = Some (e, u) ->
    path_rank r u < path_rank r v.
Proof.
  intros Hexact Hparent.
  destruct (Search.parent_edge_valid _ _ _ _ Hexact v e u Hparent) as [_ [Hu Hv]].
  pose proof (path_rank_bound p scope roots r u Hexact Hu) as Hru.
  pose proof (path_rank_bound p scope roots r v Hexact Hv) as Hrv.
  unfold path_rank in *.
  destruct (Map.get positive_encoding u (Search.pre_num r)) as [a|] eqn:Ha; [|lia].
  destruct (Map.get positive_encoding v (Search.pre_num r)) as [b|] eqn:Hb; [|lia].
  apply Pos2Nat.inj_lt. eapply parent_rank; eassumption.
Qed.

(** Parent-walk runs preserve a scoped path and terminate at an actual supplied root. *)
Theorem path_runs_sound {V E} (p : Prepared.t V E) scope roots r target n state answer :
  Search.exact p scope roots r -> runs (path_step_c r) n state answer ->
  In (fst state) (Search.preorder r) ->
  Search.scoped_path p scope (fst state) (snd state) target ->
    match answer with
    | inl (v, es) =>
      In v (Search.preorder r) /\ Search.scoped_path p scope v es target /\
        n + path_rank r v <= path_rank r (fst state)
    | inr (v, es) => In v roots /\ Search.scoped_path p scope v es target
    end.
Proof.
  intros Hexact Hrun. induction Hrun as [state|n state answer Hstop|n state next answer Hnext Hrun IH];
    intros Hin Hpath.
  - destruct state. cbn in *. auto.
  - destruct state as [v es], answer as [u path].
    rewrite path_step_equation in Hstop.
    destruct (Map.get positive_encoding v (Search.parent_edge r)) as [[e parent]|] eqn:Hparent;
      [discriminate|].
    inversion Hstop; subst u path. split; [|exact Hpath].
    eapply Search.parent_roots; eassumption.
  - destruct state as [v es]. rewrite path_step_equation in Hnext.
    destruct (Map.get positive_encoding v (Search.parent_edge r)) as [[e u]|] eqn:Hparent;
      [|discriminate].
    inversion Hnext; subst next.
    destruct (Search.parent_edge_valid _ _ _ _ Hexact v e u Hparent) as [Harc [Hu Hv]].
    destruct (recorded_admitted p scope roots r u Hexact Hu) as [Hvalid Hadmit].
    assert (Hnew : Search.scoped_path p scope u (e :: es) target).
    { eapply Search.scoped_cons; eassumption. }
    specialize (IH Hu Hnew).
    destruct answer as [[last path]|[last path]]; [|exact IH].
    destruct IH as [Hlast [Hpath' Hbound]]. split; [exact Hlast|].
    split; [exact Hpath'|].
    pose proof (path_rank_decreases p scope roots r v e u Hexact Hparent). cbn in *. lia.
Qed.

(** Every visited vertex has a complete selected-edge path from a supplied root. *)
Theorem tree_path_valid {V E} (p : Prepared.t V E) scope roots r v :
  Search.exact p scope roots r ->
  In v (Search.preorder r) ->
    exists root es, tree_path p r v = Some es /\
      In root roots /\ Search.scoped_path p scope root es v.
Proof.
  intros Hexact Hin.
  destruct (recorded_admitted p scope roots r v Hexact Hin) as [Hvalid Hadmit].
  pose proof (path_runs_sound p scope roots r v _ _ _ Hexact
    (iterate_value (path_step_c r)
      (Pos.of_succ_nat (length (Search.preorder r))) (v, [])) Hin
    (Search.scoped_nil p scope v Hvalid Hadmit)) as Hrun.
  rewrite tree_path_equation.
  rewrite (proj2 (Search.visited_complete _ _ _ _ Hexact v) Hin).
  destruct (Cost.value (iterate (path_step_c r)
    (Pos.of_succ_nat (length (Search.preorder r))) (v, []))) as [[last es]|[root es]].
  - destruct Hrun as [_ [_ Hbound]]. cbn [fst] in Hbound.
    pose proof (path_rank_bound p scope roots r v Hexact Hin).
    rewrite SuccNat2Pos.id_succ in Hbound. lia.
  - destruct Hrun as [Hroot Hpath]. exists root, es. auto.
Qed.

End SearchOrder.
