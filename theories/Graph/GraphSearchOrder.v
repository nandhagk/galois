(** * Search orders and parent paths

    One visitor run produces topological outcomes certified by the same labelled trace.
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

(** Ready search orders strict descendants after parents and sends each non-back edge forward. *)
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

(** This visitor records the first actual Back occurrence and retains its label and endpoints. *)
Definition back_visitor {E} : Visitor.t E (option (E * positive * positive)) :=
  Visitor.Make (fun _ _ s => Cost.ret s)
    (fun e u v k s =>
      Cost.ret
        (match s with
        | Some edge => Some edge
        | None => match k with Search.Back => Some (e, u, v) | _ => None end
        end))
    (fun _ _ s => Cost.ret s).

Local Lemma back_visitor_fold {E} (evs : list (Search.event E)) s :
  SearchRun.apply_events back_visitor evs s =
    match s with Some edge => Some edge | None => first_back evs end.
Proof.
  unfold SearchRun.apply_events.
  revert s. induction evs as [|ev rest IH]; intro s; [destruct s; reflexivity|].
  cbn [fold_left]. rewrite IH.
  destruct ev as [v via|e u v k|v parent]; destruct s as [edge|];
    cbn [Visitor.apply Visitor.apply_c back_visitor first_back
      Visitor.on_enter_c Visitor.on_edge_c Visitor.on_exit_c];
    autorewrite with galois_cost;
    try reflexivity.
  destruct k; reflexivity.
Qed.

(** Topological production runs the engine once and reverses its result only on the order branch. *)
Definition topological_c {V E} (p : Prepared.t V E) scope roots :=
  let* state := SearchRun.run_c p back_visitor scope roots None in
  match snd state with
  | Some edge => Cost.ret (inr edge)
  | None => let* order := rpo_c (fst state) in Cost.ret (inl order)
  end.

Definition topological {V E} (p : Prepared.t V E) scope roots :=
  Cost.value (topological_c p scope roots).

Definition dag_ok_c {V E} (p : Prepared.t V E) scope roots :=
  Cost.map (fun state =>
    match snd state with None => true | Some _ => false end)
    (SearchRun.run_c p back_visitor scope roots None).

Definition dag_ok {V E} (p : Prepared.t V E) scope roots :=
  Cost.value (dag_ok_c p scope roots).

(** The single-run producer keeps the original first-Back-or-RPO observation. *)
Theorem topological_equation {V E} (p : Prepared.t V E) scope roots :
  topological p scope roots =
    match first_back (SearchRun.events p scope roots) with
    | None => inl (rpo (SearchRun.dfs p scope roots))
    | Some edge => inr edge
    end.
Proof.
  pose proof (SearchRun.run_result p (@back_visitor E) scope roots None) as Hresult.
  rewrite SearchRun.run_events, back_visitor_fold in Hresult.
  cbn [fst] in Hresult.
  unfold topological, topological_c. rewrite Cost.value_bind, SearchRun.run_events.
  rewrite back_visitor_fold. cbn [fst snd]. rewrite Hresult.
  destruct (first_back (SearchRun.events p scope roots)); reflexivity.
Qed.

(** The costed DAG flag observes the same actual Back events as topological production. *)
Theorem dag_ok_equation {V E} (p : Prepared.t V E) scope roots :
  dag_ok p scope roots =
    match first_back (SearchRun.events p scope roots) with None => true | Some _ => false end.
Proof.
  unfold dag_ok, dag_ok_c. rewrite Cost.value_map, SearchRun.run_events, back_visitor_fold.
  reflexivity.
Qed.

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
  rewrite topological_equation. destruct (first_back (SearchRun.events p scope roots)) as [edge|]
    eqn:Hback; [|discriminate].
  intro H. inversion H; subst edge. now apply first_back_sound.
Qed.

(** The order alternative contains the same RPO and a trace without back-edge events. *)
Theorem topological_order_event {V E} (p : Prepared.t V E) scope roots order :
  topological p scope roots = inl order ->
    order = rpo (SearchRun.dfs p scope roots) /\
    forall e u v, ~ In (Search.Edge e u v Search.Back) (SearchRun.events p scope roots).
Proof.
  rewrite topological_equation. destruct (first_back (SearchRun.events p scope roots)) eqn:Hback;
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
  intros Hexact Hrun.
  induction Hrun as [state|n state answer Hstop|n state next answer Hnext Hrun IH];
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

(** Numbering extensions preserve assigned ranks and place new ranks beyond the old clock. *)
Record numbering_extension (m : Map.t positive positive) clock
    (m' : Map.t positive positive) clock' : Prop := {
  clock_forward : (clock <= clock')%positive;
  rank_preserved : forall v k, Map.get positive_encoding v m = Some k ->
    Map.get positive_encoding v m' = Some k;
  rank_fresh : forall v k, Map.get positive_encoding v m = None ->
    Map.get positive_encoding v m' = Some k -> (clock <= k)%positive
}.

Local Lemma numbering_extension_refl m clock : numbering_extension m clock m clock.
Proof.
  constructor.
  - apply Pos.le_refl.
  - auto.
  - intros v k Hnone Hsome. congruence.
Qed.

Local Lemma numbering_extension_trans m clock mid middle last final :
  numbering_extension m clock mid middle -> numbering_extension mid middle last final ->
    numbering_extension m clock last final.
Proof.
  intros Hfirst Hlast. constructor.
  - eapply Pos.le_trans; [exact (clock_forward _ _ _ _ Hfirst)|
      exact (clock_forward _ _ _ _ Hlast)].
  - intros v k Hget. apply (rank_preserved _ _ _ _ Hlast),
      (rank_preserved _ _ _ _ Hfirst), Hget.
  - intros v k Hnone Hget.
    destruct (Map.get positive_encoding v mid) as [j|] eqn:Hmid.
    + pose proof (rank_preserved _ _ _ _ Hlast v j Hmid).
      assert (Heq : j = k) by congruence. subst j.
      exact (rank_fresh _ _ _ _ Hfirst v k Hnone Hmid).
    + eapply Pos.le_trans; [exact (clock_forward _ _ _ _ Hfirst)|].
      exact (rank_fresh _ _ _ _ Hlast v k Hmid Hget).
Qed.

Local Lemma numbering_extension_set m clock v :
  Map.wf positive_encoding m -> Map.get positive_encoding v m = None ->
    numbering_extension m clock (Map.set positive_encoding v clock m) (Pos.succ clock).
Proof.
  intros Hwf Hnone. constructor.
  - apply Pos.lt_le_incl, Pos.lt_succ_diag_r.
  - intros u k Hget.
    rewrite (Map.get_set_other positive_encoding positive_encoding_laws);
      [exact Hget|exact Hwf|intro Heq; subst u; congruence].
  - intros u k Hmissing Hget. destruct (Pos.eq_dec u v) as [->|Hne].
    + rewrite Map.get_set_same in Hget by exact Hwf.
      inversion Hget; subst k. apply Pos.le_refl.
    + rewrite (Map.get_set_other positive_encoding positive_encoding_laws) in Hget
        by assumption. congruence.
Qed.

(** Core extensions retain every selected labelled parent and both temporal numbering histories. *)
Record core_extension {E} (c c' : SearchRun.core E) : Prop := {
  parent_preserved : forall v e u,
    Map.get positive_encoding v (SearchRun.parents c) = Some (e, u) ->
      Map.get positive_encoding v (SearchRun.parents c') = Some (e, u);
  pre_extension : numbering_extension (SearchRun.pre_index c) (SearchRun.pre_clock c)
    (SearchRun.pre_index c') (SearchRun.pre_clock c');
  post_extension : numbering_extension (SearchRun.post_index c) (SearchRun.post_clock c)
    (SearchRun.post_index c') (SearchRun.post_clock c')
}.

Local Lemma core_extension_refl {E} (c : SearchRun.core E) : core_extension c c.
Proof.
  constructor; auto using numbering_extension_refl.
Qed.

Local Lemma core_extension_trans {E} (a b c : SearchRun.core E) :
  core_extension a b -> core_extension b c -> core_extension a c.
Proof.
  intros Hab Hbc. constructor.
  - intros v e u Hget. apply (parent_preserved _ _ Hbc), (parent_preserved _ _ Hab), Hget.
  - eapply numbering_extension_trans; [exact (pre_extension _ _ Hab)|exact (pre_extension _ _ Hbc)].
  - eapply numbering_extension_trans.
    + exact (post_extension _ _ Hab).
    + exact (post_extension _ _ Hbc).
Qed.

Local Lemma discover_extension {V E} (p : Prepared.t V E) roots stack c v via :
  SearchInvariant.representation c -> SearchInvariant.history (stack, c) ->
  SearchExact.parent_laws p roots c -> ~ In v (SearchRun.pre_rev c) ->
    core_extension c (SearchRun.discover v via c).
Proof.
  intros Hrep Hhistory Hparents Hfresh.
  assert (Hnone : Map.get positive_encoding v (SearchRun.pre_index c) = None).
  { destruct (Map.get positive_encoding v (SearchRun.pre_index c)) as [k|] eqn:Hget;
      [|reflexivity]. exfalso. apply Hfresh.
    apply (SearchInvariant.numbering_domain _ _ _ (SearchInvariant.pre_numbering _ Hhistory)).
    now exists k. }
  rewrite SearchRun.discover_equation. constructor.
  - intros u e parent Hget. destruct via as [edge|]; [|exact Hget].
    cbn [SearchRun.parents].
    rewrite (Map.get_set_other positive_encoding positive_encoding_laws).
    + exact Hget.
    + exact (SearchInvariant.parents_wf _ Hrep).
    + intro Heq. subst u.
      destruct (SearchExact.selected_parent _ _ _ Hparents v e parent Hget)
        as [_ [Hin _]]. contradiction.
  - apply numbering_extension_set; [exact (SearchInvariant.pre_index_wf _ Hrep)|exact Hnone].
  - apply numbering_extension_refl.
Qed.

Local Lemma finish_extension {E} u es rest (c : SearchRun.core E) :
  SearchInvariant.representation c -> SearchInvariant.history ((u, es) :: rest, c) ->
    core_extension c (SearchRun.finish u c).
Proof.
  intros Hrep Hhistory. rewrite SearchRun.finish_equation. constructor.
  - auto.
  - apply numbering_extension_refl.
  - apply numbering_extension_set; [exact (SearchInvariant.post_index_wf _ Hrep)|].
    exact (SearchExact.top_post_absent u es rest c Hhistory).
Qed.

(** Trace blocks have exactly the same ordered state transition as the costed engine. *)
Theorem trace_step_equation {V E} (p : Prepared.t V E) scope w here next :
  SearchRun.trace_step p scope w here next -> SearchRun.transition p scope w = (inl next, here).
Proof.
  intro Hstep.
  destruct Hstep as [u rest c|u e v pending rest c Hscope|
    u e v pending rest c Hscope Hname|u e v pending rest c name Hscope Hname Hcolor|
    u e v pending rest c name k Hscope Hname Hcolor Hnot].
  all: match goal with
  | |- SearchRun.transition ?prep ?region (?stack, ?current) = _ =>
    pose proof (SearchRun.step_equation prep region stack current) as Htransition
  end.
  all: cbn beta iota zeta in Htransition.
  - exact Htransition.
  - rewrite Hscope in Htransition. exact Htransition.
  - rewrite Hscope, Hname in Htransition. exact Htransition.
  - rewrite Hscope, Hname, (SearchRun.color_edge_kind _ _ _ _ Hcolor) in Htransition.
    exact Htransition.
  - rewrite Hscope, Hname, (SearchRun.color_edge_kind _ _ _ _ Hcolor) in Htransition.
    destruct k; [contradiction|exact Htransition|exact Htransition|exact Htransition].
Qed.

(** Every inspected trace block extends the same parent and numbering maps. *)
Theorem trace_step_extension {V E} (p : Prepared.t V E) scope roots w here next :
  SearchInvariant.representation (snd w) -> SearchInvariant.history w ->
  SearchExact.parent_laws p roots (snd w) ->
  SearchRun.trace_step p scope w here next -> core_extension (snd w) (snd next).
Proof.
  intros Hrep Hhistory Hparents Hstep.
  pose proof (trace_step_equation p scope w here next Hstep) as Htransition.
  destruct w as [stack c]. rewrite SearchRun.step_equation in Htransition.
  destruct stack as [|[u [|[e v] pending]] rest]; [discriminate| |].
  - inversion Htransition; subst. now apply finish_extension with (es := []) (rest := rest).
  - destruct (Scope.admits scope v); [|inversion Htransition; subst; apply core_extension_refl].
    destruct (Prepared.name_of p v); [|inversion Htransition; subst; apply core_extension_refl].
    destruct (SearchRun.edge_kind c u v) eqn:Hkind;
      inversion Htransition; subst; try apply core_extension_refl.
    apply discover_extension with (p := p) (roots := roots)
      (stack := (u, (e, v) :: pending) :: rest);
      try assumption.
    intro Hin. apply (SearchInvariant.seen_discovered _ Hrep) in Hin.
    pose proof (proj1 (SearchInvariant.tree_is_white c u v) Hkind) as Hwhite.
    change (FinSet.mem positive_encoding v (SearchRun.seen c) = true) in Hin.
    rewrite Hwhite in Hin. discriminate.
Qed.

(** Trace reasoning carries the same maintained semantic and storage invariants as the engine. *)
Record consistent {V E} (p : Prepared.t V E) scope roots (w : SearchRun.work E) : Prop := {
  consistent_rep : SearchInvariant.representation (snd w);
  consistent_history : SearchInvariant.history w;
  consistent_sound : SearchInvariant.sound_work p scope roots w;
  consistent_closed : SearchInvariant.closed_work p scope w;
  consistent_parents : SearchExact.parent_laws p roots (snd w);
  consistent_intervals : SearchExact.interval_laws p scope (fst w) (snd w)
}.

(** Independently specified trace blocks preserve all maintained engine invariants. *)
Theorem trace_step_consistent {V E} (p : Prepared.t V E) scope roots w here next :
  Prepared.ready p -> consistent p scope roots w ->
  SearchRun.trace_step p scope w here next -> consistent p scope roots next.
Proof.
  intros Hready HI Hstep.
  pose proof (trace_step_equation p scope w here next Hstep) as Htransition.
  destruct HI as [Hrep Hhistory Hsound Hclosed Hparents Hinterval].
  pose proof (SearchInvariant.transition_representation p scope w Hrep) as Hrep'.
  pose proof (SearchInvariant.transition_history p scope w Hrep Hhistory) as Hhistory'.
  pose proof (SearchInvariant.transition_sound p scope roots w Hready Hrep Hsound) as Hsound'.
  pose proof (SearchInvariant.transition_closed p scope roots w Hready Hrep Hsound Hclosed)
    as Hclosed'.
  pose proof (SearchExact.transition_parents p scope roots w Hready Hrep Hhistory Hsound Hparents)
    as Hparents'.
  pose proof (SearchExact.transition_intervals p scope roots w Hrep Hhistory Hparents
    Hclosed Hinterval) as Hinterval'.
  rewrite Htransition in Hrep', Hhistory', Hsound', Hclosed', Hparents', Hinterval'.
  constructor; assumption.
Qed.

Local Lemma trace_segment_consistent {V E} (p : Prepared.t V E) scope roots w evs final :
  Prepared.ready p -> SearchRun.trace_segment p scope w evs final ->
  consistent p scope roots w ->
    consistent p scope roots final /\ core_extension (snd w) (snd final).
Proof.
  intros Hready Htrace.
  induction Htrace as [w|w here next later final Hstep Htail IH]; intro HI.
  - split; [exact HI|apply core_extension_refl].
  - pose proof (trace_step_consistent p scope roots w here next Hready HI Hstep) as Hnext.
    destruct (IH Hnext) as [Hfinal Hextension]. split; [exact Hfinal|].
    eapply core_extension_trans; [|exact Hextension].
    exact (trace_step_extension p scope roots w here next
      (consistent_rep _ _ _ _ HI) (consistent_history _ _ _ _ HI)
      (consistent_parents _ _ _ _ HI) Hstep).
Qed.

Local Lemma root_start_consistent {V E} (p : Prepared.t V E) scope roots c v name :
  Prepared.ready p -> consistent p scope roots ([], c) -> In v roots ->
  Scope.admits scope v = true -> FinSet.mem positive_encoding v (SearchRun.seen c) = false ->
  Prepared.name_of p v = Some name ->
    consistent p scope roots ([(v, Prepared.succ_edges p v)], SearchRun.discover v None c).
Proof.
  intros Hready [Hrep Hhistory Hsound Hclosed Hparents Hinterval] Hroot Hallowed Hfresh Hname.
  assert (Hvalid : Prepared.valid_id p v).
  { apply SearchInvariant.vertices_spec.
    exact (SearchInvariant.named_in_vertices p v name Hready Hname). }
  assert (Hreach : Search.scoped_reachable p scope roots v).
  { exists v, []. split; [exact Hroot|now apply Search.scoped_nil]. }
  assert (Hfreshpre : ~ In v (SearchRun.pre_rev c)).
  { intro Hin. apply (SearchInvariant.seen_discovered _ Hrep) in Hin.
    change (FinSet.mem positive_encoding v (SearchRun.seen c) = true) in Hin.
    rewrite Hfresh in Hin. discriminate. }
  constructor.
  - now apply SearchInvariant.discover_representation.
  - exact (SearchInvariant.discover_history [] c v None (Prepared.succ_edges p v)
      Hhistory Hfreshpre).
  - exact (SearchInvariant.sound_push p scope roots [] c v None
      Hrep Hsound Hreach Hvalid Hallowed).
  - now apply SearchInvariant.root_start_closed.
  - exact (SearchExact.discover_parents p roots [] c v None Hrep Hhistory Hparents Hfreshpre Hroot).
  - exact (SearchExact.discover_intervals p scope roots [] c v None (Prepared.succ_edges p v)
      Hrep Hhistory Hparents Hinterval Hfreshpre eq_refl).
Qed.

Local Lemma trace_root_consistent {V E} (p : Prepared.t V E) scope roots c v evs final :
  Prepared.ready p -> SearchRun.trace_root p scope c v evs final ->
  consistent p scope roots ([], c) -> In v roots ->
    consistent p scope roots ([], final) /\ core_extension c final.
Proof.
  intros Hready Htrace.
  destruct Htrace as [c v Hscope|c v Hscope Hseen|c v Hscope Hseen Hname|
    c v name evs final Hscope Hseen Hname Hsegment]; intros HI Hroot.
  - split; [exact HI|apply core_extension_refl].
  - split; [exact HI|apply core_extension_refl].
  - split; [exact HI|apply core_extension_refl].
  - pose proof (root_start_consistent p scope roots c v name Hready HI Hroot Hscope Hseen Hname)
      as Hstart.
    destruct (trace_segment_consistent p scope roots _ _ _ Hready Hsegment Hstart)
      as [Hfinal Hextension].
    split; [exact Hfinal|]. eapply core_extension_trans; [|exact Hextension].
    apply discover_extension with (p := p) (roots := roots) (stack := []).
    + exact (consistent_rep _ _ _ _ HI).
    + exact (consistent_history _ _ _ _ HI).
    + exact (consistent_parents _ _ _ _ HI).
    + intro Hin. apply (SearchInvariant.seen_discovered _ (consistent_rep _ _ _ _ HI)) in Hin.
      change (FinSet.mem positive_encoding v (SearchRun.seen c) = true) in Hin.
      congruence.
Qed.

Local Lemma trace_roots_consistent {V E} (p : Prepared.t V E) scope roots todo c evs final :
  Prepared.ready p -> SearchRun.trace_roots p scope todo c evs final ->
  consistent p scope roots ([], c) -> incl todo roots ->
    consistent p scope roots ([], final) /\ core_extension c final.
Proof.
  intros Hready Htrace.
  induction Htrace as [c|v rest c here next later final Hroot Htail IH];
    intros HI Hincl.
  - split; [exact HI|apply core_extension_refl].
  - destruct (trace_root_consistent p scope roots c v here next Hready Hroot HI
      (Hincl v (or_introl eq_refl))) as [Hnext Hextension].
    destruct (IH Hnext ltac:(intros x Hx; apply Hincl; now right)) as [Hfinal Hextension'].
    split; [exact Hfinal|]. eapply core_extension_trans; eassumption.
Qed.

Local Lemma initial_consistent {V E} (p : Prepared.t V E) scope roots :
  consistent p scope roots ([], @SearchRun.initial E).
Proof.
  constructor.
  - apply SearchInvariant.initial_representation.
  - apply SearchInvariant.initial_history.
  - constructor.
    + intros v Hv. change (FinSet.mem positive_encoding v FinSet.empty = true) in Hv.
      rewrite FinSet.mem_empty in Hv. discriminate.
    + intros u es Hin. contradiction.
  - constructor; intros u Hu; contradiction.
  - constructor.
    + intros v e u Hget. change (Map.get positive_encoding v Map.empty = Some (e, u)) in Hget.
      rewrite Map.get_empty in Hget. discriminate.
    + intros v Hin. contradiction.
  - apply SearchExact.initial_intervals.
Qed.

(** Labelled classes use the selected tree label and final traversal facts independently of aliases. *)
Definition labelled_kind {E} (r : Search.result E) e u v k :=
  match k with
  | Search.Tree => Map.get positive_encoding v (Search.parent_edge r) = Some (e, u)
  | Search.Back => Search.ancestor r v u /\ In u (Search.preorder r)
  | Search.Forward =>
    exists a b j z, Map.get positive_encoding u (Search.pre_num r) = Some a /\
      Map.get positive_encoding v (Search.pre_num r) = Some b /\ (a < b)%positive /\
      Map.get positive_encoding v (Search.post_num r) = Some j /\
      Map.get positive_encoding u (Search.post_num r) = Some z /\ (j < z)%positive
  | Search.Cross =>
    exists a b j z, Map.get positive_encoding v (Search.pre_num r) = Some a /\
      Map.get positive_encoding u (Search.pre_num r) = Some b /\ (a < b)%positive /\
      Map.get positive_encoding v (Search.post_num r) = Some j /\
      Map.get positive_encoding u (Search.post_num r) = Some z /\ (j < z)%positive
  end.

Local Lemma extension_ancestry {E} (c final : SearchRun.core E) u v :
  core_extension c final -> SearchExact.ancestry c u v -> SearchExact.ancestry final u v.
Proof.
  intros Hextension Hancestor.
  induction Hancestor as [u v [e Hget]|u|u x v Hux IHux Hxv IHxv].
  - apply rt_step. exists e. now apply (parent_preserved _ _ Hextension).
  - apply rt_refl.
  - eapply rt_trans; eassumption.
Qed.

Local Lemma extension_numbers {E} stack (c final : SearchRun.core E) u :
  SearchInvariant.history (stack, c) -> SearchInvariant.history ([], final) ->
  core_extension c final -> In u (SearchRun.pre_rev c) ->
    exists a z, Map.get positive_encoding u (SearchRun.pre_index c) = Some a /\
      Map.get positive_encoding u (SearchRun.pre_index final) = Some a /\
      Map.get positive_encoding u (SearchRun.post_index final) = Some z.
Proof.
  intros Hhistory Hfinal Hextension Hu.
  destruct (proj2 (SearchInvariant.numbering_domain _ _ _
    (SearchInvariant.pre_numbering _ Hhistory) u) Hu) as [a Ha].
  cbn [snd] in Ha.
  pose proof (rank_preserved _ _ _ _ (pre_extension _ _ Hextension) u a Ha) as Ha'.
  assert (Hpre : In u (SearchRun.pre_rev final)).
  { apply (SearchInvariant.numbering_domain _ _ _ (SearchInvariant.pre_numbering _ Hfinal)).
    now exists a. }
  assert (Hpost : In u (SearchRun.post_rev final)).
  { exact (Permutation_in u (SearchInvariant.partition _ Hfinal) Hpre). }
  destruct (proj2 (SearchInvariant.numbering_domain _ _ _
    (SearchInvariant.post_numbering _ Hfinal) u) Hpost) as [z Hz].
  exists a, z. auto.
Qed.

Local Lemma posted_after_open {E} stack (c final : SearchRun.core E) u v j z :
  SearchInvariant.history (stack, c) -> core_extension c final ->
  Map.get positive_encoding v (SearchRun.post_index c) = Some j ->
  Map.get positive_encoding u (SearchRun.post_index c) = None ->
  Map.get positive_encoding u (SearchRun.post_index final) = Some z -> (j < z)%positive.
Proof.
  intros Hhistory Hextension Hj Hu Hz.
  pose proof (SearchInvariant.numbering_bound _ _ _
    (SearchInvariant.post_numbering _ Hhistory) v j Hj) as Hbound.
  pose proof (rank_fresh _ _ _ _ (post_extension _ _ Hextension) u z Hu Hz) as Hnew.
  eapply Pos.lt_le_trans; eassumption.
Qed.

Local Lemma examined_edge {V E} (p : Prepared.t V E) scope roots u e v pending rest c :
  Prepared.ready p -> consistent p scope roots ((u, (e, v) :: pending) :: rest, c) ->
    Prepared.arc p u e v /\ Scope.admits scope u = true /\ In u (SearchRun.pre_rev c).
Proof.
  intros Hready HI.
  destruct (SearchInvariant.valid_frames _ _ _ _ (consistent_sound _ _ _ _ HI)
    u ((e, v) :: pending) (or_introl eq_refl)) as [Hseen [Hvalid [Hallowed Hedges]]].
  split.
  - exact (proj1 (SearchInvariant.successor_arc p u e v Hready Hvalid
      (Hedges _ (or_introl eq_refl)))).
  - split; [exact Hallowed|].
    now apply (SearchInvariant.seen_discovered _ (consistent_rep _ _ _ _ HI)).
Qed.

Local Lemma cross_pre_lt {E} u es rest (c : SearchRun.core E) v a b finished :
  SearchInvariant.history ((u, es) :: rest, c) ->
  Map.get positive_encoding u (SearchRun.pre_index c) = Some a ->
  Map.get positive_encoding v (SearchRun.pre_index c) = Some b ->
  Map.get positive_encoding v (SearchRun.post_index c) = Some finished ->
  Pos.ltb a b = false -> (b < a)%positive.
Proof.
  intros Hhistory Ha Hb Hpost Hcross. apply Pos.ltb_ge in Hcross.
  pose proof (SearchExact.top_post_absent u es rest c Hhistory) as Hopen.
  assert (Hne : b <> a).
  { intro Heq. subst b.
    pose proof (SearchInvariant.numbering_injective _ _ _ u v a
      (SearchInvariant.pre_numbering _ Hhistory) Ha Hb) as ->. congruence. }
  apply Pos2Nat.inj_lt. apply Pos2Nat.inj_le in Hcross.
  assert (Hnatne : Pos.to_nat b <> Pos.to_nat a).
  { intro Heq. apply Hne. now apply Pos2Nat.inj. }
  lia.
Qed.

Local Lemma seen_color_final {V E} (p : Prepared.t V E) scope roots u e v pending rest c final k :
  consistent p scope roots ((u, (e, v) :: pending) :: rest, c) ->
  consistent p scope roots ([], final) -> core_extension c final ->
  SearchRun.edge_color c u v k -> k <> Search.Tree ->
    labelled_kind (SearchRun.result final) e u v k.
Proof.
  intros HI Hfinal Hextension Hcolor Hnot.
  pose proof (consistent_history _ _ _ _ HI) as Hhistory.
  pose proof (consistent_rep _ _ _ _ HI) as Hrep.
  pose proof (SearchExact.top_post_absent u ((e, v) :: pending) rest c Hhistory) as Hopen.
  assert (Hu : In u (SearchRun.pre_rev c)).
  { apply (Permutation_in u (Permutation_sym (SearchInvariant.partition _ Hhistory))).
    apply in_or_app. left. now left. }
  destruct (extension_numbers _ c final u Hhistory (consistent_history _ _ _ _ Hfinal)
    Hextension Hu) as [a [z [Ha [Ha' Hz]]]].
  destruct Hcolor as [Hseen|Hseen Hpost|j x y Hseen Hpost Hx Hy Hlt|j Hseen Hpost Hcross];
    [contradiction| | |].
  - assert (Hv : In v (SearchRun.pre_rev c)).
    { now apply (SearchInvariant.seen_discovered _ Hrep). }
    pose proof (proj2 (SearchExact.active_ancestor p scope u ((e, v) :: pending) rest c v
      Hhistory (consistent_intervals _ _ _ _ HI) Hv) Hpost) as Hancestor.
    rewrite SearchRun.result_equation. unfold labelled_kind.
    cbn [Search.parent_edge Search.preorder]. split.
    + now apply (extension_ancestry c final v u Hextension).
    + apply (proj1 (in_rev _ _)).
      apply (SearchInvariant.numbering_domain _ _ _
        (SearchInvariant.pre_numbering _ (consistent_history _ _ _ _ Hfinal))).
      now exists a.
  - pose proof (rank_preserved _ _ _ _ (pre_extension _ _ Hextension) u x Hx) as Hx'.
    pose proof (rank_preserved _ _ _ _ (pre_extension _ _ Hextension) v y Hy) as Hy'.
    pose proof (rank_preserved _ _ _ _ (post_extension _ _ Hextension) v j Hpost) as Hj'.
    pose proof (posted_after_open _ c final u v j z Hhistory Hextension Hpost Hopen Hz) as Hpostlt.
    rewrite SearchRun.result_equation. unfold labelled_kind.
    cbn [Search.pre_num Search.post_num]. exists x, y, j, z.
    apply Pos.ltb_lt in Hlt. repeat split; assumption.
  - assert (Hv : In v (SearchRun.pre_rev c)).
    { now apply (SearchInvariant.seen_discovered _ Hrep). }
    destruct (proj2 (SearchInvariant.numbering_domain _ _ _
      (SearchInvariant.pre_numbering _ Hhistory) v) Hv) as [b Hb].
    cbn [snd] in Hb. rewrite Ha, Hb in Hcross.
    pose proof (cross_pre_lt u ((e, v) :: pending) rest c v a b j
      Hhistory Ha Hb Hpost Hcross) as Hlt.
    pose proof (rank_preserved _ _ _ _ (pre_extension _ _ Hextension) v b Hb) as Hb'.
    pose proof (rank_preserved _ _ _ _ (post_extension _ _ Hextension) v j Hpost) as Hj'.
    pose proof (posted_after_open _ c final u v j z Hhistory Hextension Hpost Hopen Hz) as Hpostlt.
    rewrite SearchRun.result_equation. unfold labelled_kind.
    cbn [Search.pre_num Search.post_num]. exists b, a, j, z. repeat split; assumption.
Qed.

Local Lemma trace_step_edge_fact {V E} (p : Prepared.t V E) scope roots w here next final e u v k :
  Prepared.ready p -> consistent p scope roots w -> consistent p scope roots ([], final) ->
  SearchRun.trace_step p scope w here next -> core_extension (snd next) final ->
  In (Search.Edge e u v k) here ->
    Prepared.arc p u e v /\ Scope.admits scope u = true /\ Scope.admits scope v = true /\
      labelled_kind (SearchRun.result final) e u v k.
Proof.
  intros Hready HI Hfinal Hstep Hextension Hin.
  destruct Hstep as [a rest c|a edge b pending rest c Hscope|
    a edge b pending rest c Hscope Hname|a edge b pending rest c name Hscope Hname Hcolor|
    a edge b pending rest c name color Hscope Hname Hcolor Hnot];
    cbn [In] in Hin.
  - destruct Hin as [Heq|Hfalse]; [discriminate|contradiction].
  - contradiction.
  - contradiction.
  - destruct Hin as [Heq|[Hfalse|Hfalse]]; [|discriminate|contradiction].
    inversion Heq; subst e u v k.
    destruct (examined_edge p scope roots a edge b pending rest c Hready HI)
      as [Harc [Hallowed Hpre]].
    split; [exact Harc|]. split; [exact Hallowed|]. split; [exact Hscope|].
    rewrite SearchRun.result_equation. unfold labelled_kind. cbn [Search.parent_edge].
    apply (parent_preserved _ _ Hextension).
    rewrite SearchRun.discover_equation. cbn [SearchRun.parents].
    apply Map.get_set_same. exact (SearchInvariant.parents_wf _ (consistent_rep _ _ _ _ HI)).
  - destruct Hin as [Heq|Hfalse]; [|contradiction]. inversion Heq; subst e u v k.
    destruct (examined_edge p scope roots a edge b pending rest c Hready HI)
      as [Harc [Hallowed Hpre]].
    split; [exact Harc|]. split; [exact Hallowed|]. split; [exact Hscope|].
    eapply seen_color_final; eassumption.
Qed.

Local Lemma trace_segment_edge_fact {V E} (p : Prepared.t V E) scope roots w evs last final
    e u v k :
  Prepared.ready p -> SearchRun.trace_segment p scope w evs last ->
  consistent p scope roots w -> consistent p scope roots ([], final) ->
  core_extension (snd last) final -> In (Search.Edge e u v k) evs ->
    Prepared.arc p u e v /\ Scope.admits scope u = true /\ Scope.admits scope v = true /\
      labelled_kind (SearchRun.result final) e u v k.
Proof.
  intros Hready Htrace.
  induction Htrace as [w|w here next later last Hstep Htail IH];
    intros HI Hfinal Hextension Hin; [contradiction|].
  pose proof (trace_step_consistent p scope roots w here next Hready HI Hstep) as Hnext.
  apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
  - destruct (trace_segment_consistent p scope roots next later last Hready Htail Hnext)
      as [Hlast HtailExtension].
    eapply trace_step_edge_fact; [exact Hready|exact HI|exact Hfinal|exact Hstep| |exact Hin].
    eapply core_extension_trans; eassumption.
  - exact (IH Hnext Hfinal Hextension Hin).
Qed.

Local Lemma trace_root_edge_fact {V E} (p : Prepared.t V E) scope roots c root evs last final
    e u v k :
  Prepared.ready p -> SearchRun.trace_root p scope c root evs last ->
  consistent p scope roots ([], c) -> consistent p scope roots ([], final) ->
  In root roots -> core_extension last final -> In (Search.Edge e u v k) evs ->
    Prepared.arc p u e v /\ Scope.admits scope u = true /\ Scope.admits scope v = true /\
      labelled_kind (SearchRun.result final) e u v k.
Proof.
  intros Hready Htrace.
  destruct Htrace as [c root Hscope|c root Hscope Hseen|c root Hscope Hseen Hname|
    c root name evs last Hscope Hseen Hname Hsegment];
    intros HI Hfinal Hroot Hextension Hin; try contradiction.
  destruct Hin as [Hfalse|Hin]; [discriminate|].
  eapply trace_segment_edge_fact; [exact Hready|exact Hsegment| |exact Hfinal|exact Hextension|
    exact Hin].
  exact (root_start_consistent p scope roots c root name Hready HI Hroot Hscope Hseen Hname).
Qed.

Local Lemma trace_roots_edge_fact {V E} (p : Prepared.t V E) scope roots todo c evs last final
    e u v k :
  Prepared.ready p -> SearchRun.trace_roots p scope todo c evs last ->
  consistent p scope roots ([], c) -> consistent p scope roots ([], final) ->
  incl todo roots -> core_extension last final -> In (Search.Edge e u v k) evs ->
    Prepared.arc p u e v /\ Scope.admits scope u = true /\ Scope.admits scope v = true /\
      labelled_kind (SearchRun.result final) e u v k.
Proof.
  intros Hready Htrace.
  induction Htrace as [c|root rest c here next later last Hroot Htail IH];
    intros HI Hfinal Hincl Hextension Hin; [contradiction|].
  destruct (trace_root_consistent p scope roots c root here next Hready Hroot HI
    (Hincl root (or_introl eq_refl))) as [Hnext HrootExtension].
  assert (Hrest : incl rest roots) by (intros x Hx; apply Hincl; now right).
  apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
  - destruct (trace_roots_consistent p scope roots rest next later last Hready Htail Hnext Hrest)
      as [Hlast HtailExtension].
    eapply trace_root_edge_fact; [exact Hready|exact Hroot|exact HI|exact Hfinal|
      exact (Hincl root (or_introl eq_refl))| |exact Hin].
    eapply core_extension_trans; eassumption.
  - exact (IH Hnext Hfinal Hrest Hextension Hin).
Qed.

(** Every labelled edge event agrees with its selected label or final temporal interval facts. *)
Theorem classify_spec {V E} (p : Prepared.t V E) scope roots e u v k :
  Prepared.ready p -> In (Search.Edge e u v k) (SearchRun.events p scope roots) ->
    Prepared.arc p u e v /\ Scope.admits scope u = true /\ Scope.admits scope v = true /\
      labelled_kind (SearchRun.dfs p scope roots) e u v k.
Proof.
  intros Hready Hin.
  destruct (SearchExact.events_wf p scope roots Hready) as [final [Hresult Htrace]].
  pose proof (initial_consistent p scope roots) as Hinitial.
  destruct (trace_roots_consistent p scope roots roots SearchRun.initial _ final
    Hready Htrace Hinitial ltac:(intros x Hx; exact Hx)) as [Hfinal Hextension].
  rewrite Hresult.
  eapply trace_roots_edge_fact; [exact Hready|exact Htrace|exact Hinitial|exact Hfinal|
    intros x Hx; exact Hx|apply core_extension_refl|exact Hin].
Qed.

(** Each eligible discovered outgoing occurrence is either emitted or still unread in a frame. *)
Definition accounted {V E} (p : Prepared.t V E) scope
    (stack : list (SearchRun.frame E)) nodes prefix :=
  forall u, In u nodes -> forall e v, In (e, v) (Prepared.succ_edges p u) ->
    Scope.admits scope v = true ->
    (exists k, In (Search.Edge e u v k) prefix) \/
      exists pending, In (u, pending) stack /\ In (e, v) pending.

Local Lemma accounted_append {V E} (p : Prepared.t V E) scope stack nodes prefix later :
  accounted p scope stack nodes prefix -> accounted p scope stack nodes (prefix ++ later).
Proof.
  intros Haccount u Hu e v Hedge Hallowed.
  destruct (Haccount u Hu e v Hedge Hallowed) as [[k Hk]|Hpending]; [|now right].
  left. exists k. apply in_or_app. now left.
Qed.

Local Lemma accounted_push {V E} (p : Prepared.t V E) scope stack nodes prefix v :
  accounted p scope stack nodes prefix ->
    accounted p scope ((v, Prepared.succ_edges p v) :: stack) (v :: nodes) prefix.
Proof.
  intros Haccount u [<-|Hu] e w Hedge Hallowed.
  - right. exists (Prepared.succ_edges p v). split; [now left|exact Hedge].
  - destruct (Haccount u Hu e w Hedge Hallowed) as [Hemitted|[pending [Hin Hpending]]];
      [now left|right; exists pending; split; [now right|exact Hpending]].
Qed.

Local Lemma accounted_consume {V E} (p : Prepared.t V E) scope u e v pending rest
    nodes prefix here :
  accounted p scope ((u, (e, v) :: pending) :: rest) nodes prefix ->
  (Scope.admits scope v = true -> exists k, In (Search.Edge e u v k) here) ->
    accounted p scope ((u, pending) :: rest) nodes (prefix ++ here).
Proof.
  intros Haccount Hcurrent x Hx edge y Hedge Hallowed.
  destruct (Haccount x Hx edge y Hedge Hallowed) as [[k Hk]|[es [[Heq|Hin] Hpending]]].
  - left. exists k. apply in_or_app. now left.
  - inversion Heq; subst x es. destruct Hpending as [Hpair|Hin].
    + inversion Hpair; subst edge y.
      destruct (Hcurrent Hallowed) as [k Hk]. left. exists k. apply in_or_app. now right.
    + right. exists pending. split; [now left|exact Hin].
  - right. exists es. split; [now right|exact Hpending].
Qed.

Local Lemma accounted_pop {V E} (p : Prepared.t V E) scope u rest nodes prefix here :
  accounted p scope ((u, []) :: rest) nodes prefix ->
    accounted p scope rest nodes (prefix ++ here).
Proof.
  intros Haccount x Hx e v Hedge Hallowed.
  destruct (Haccount x Hx e v Hedge Hallowed) as [[k Hk]|[es [[Heq|Hin] Hpending]]].
  - left. exists k. apply in_or_app. now left.
  - inversion Heq; subst es. contradiction.
  - right. now exists es.
Qed.

Local Lemma trace_step_accounted {V E} (p : Prepared.t V E) scope roots w here next prefix :
  Prepared.ready p -> consistent p scope roots w -> SearchRun.trace_step p scope w here next ->
  accounted p scope (fst w) (SearchRun.pre_rev (snd w)) prefix ->
    accounted p scope (fst next) (SearchRun.pre_rev (snd next)) (prefix ++ here).
Proof.
  intros Hready HI Hstep Haccount.
  destruct Hstep as [u rest c|u e v pending rest c Hscope|
    u e v pending rest c Hscope Hname|u e v pending rest c name Hscope Hname Hcolor|
    u e v pending rest c name k Hscope Hname Hcolor Hnot].
  - apply accounted_pop with (u := u). exact Haccount.
  - eapply accounted_consume; [exact Haccount|]. intro Hfalse. congruence.
  - eapply accounted_consume; [exact Haccount|]. intro Hallowed.
    destruct (SearchInvariant.valid_frames _ _ _ _ (consistent_sound _ _ _ _ HI)
      u ((e, v) :: pending) (or_introl eq_refl)) as [_ [Hu [_ Hedges]]].
    destruct (SearchInvariant.successor_arc p u e v Hready Hu (Hedges _ (or_introl eq_refl)))
      as [_ [node [_ Hfind]]].
    destruct Hready as [_ [_ Hlaws]].
    pose proof (Prepared.name_of_id_of p node v Hlaws Hfind). congruence.
  - change (accounted p scope
      ((v, Prepared.succ_edges p v) :: (u, pending) :: rest) (v :: SearchRun.pre_rev c)
      (prefix ++ [Search.Edge e u v Search.Tree; Search.Enter v (Some (e, u))])).
    apply accounted_push. eapply accounted_consume; [exact Haccount|].
    intros _. exists Search.Tree. now left.
  - eapply accounted_consume; [exact Haccount|]. intros _. exists k. now left.
Qed.

Local Lemma trace_segment_accounted {V E} (p : Prepared.t V E) scope roots w evs final prefix :
  Prepared.ready p -> SearchRun.trace_segment p scope w evs final ->
  consistent p scope roots w -> accounted p scope (fst w) (SearchRun.pre_rev (snd w)) prefix ->
    accounted p scope (fst final) (SearchRun.pre_rev (snd final)) (prefix ++ evs).
Proof.
  intros Hready Htrace.
  revert prefix. induction Htrace as [w|w here next later final Hstep Htail IH];
    intros prefix HI Haccount; [now rewrite app_nil_r|].
  pose proof (trace_step_consistent p scope roots w here next Hready HI Hstep) as Hnext.
  pose proof (trace_step_accounted p scope roots w here next prefix Hready HI Hstep Haccount)
    as Haccount'.
  specialize (IH (prefix ++ here) Hnext Haccount').
  now rewrite <- app_assoc in IH.
Qed.

Local Lemma trace_root_accounted {V E} (p : Prepared.t V E) scope roots c root evs final prefix :
  Prepared.ready p -> SearchRun.trace_root p scope c root evs final ->
  consistent p scope roots ([], c) -> In root roots ->
  accounted p scope [] (SearchRun.pre_rev c) prefix ->
    accounted p scope [] (SearchRun.pre_rev final) (prefix ++ evs).
Proof.
  intros Hready Htrace.
  destruct Htrace as [c root Hscope|c root Hscope Hseen|c root Hscope Hseen Hname|
    c root name evs final Hscope Hseen Hname Hsegment];
    intros HI Hroot Haccount; try (now rewrite app_nil_r).
  pose proof (root_start_consistent p scope roots c root name Hready HI Hroot Hscope Hseen Hname)
    as Hstart.
  assert (HstartAccount : accounted p scope [(root, Prepared.succ_edges p root)]
    (SearchRun.pre_rev (SearchRun.discover root None c)) (prefix ++ [Search.Enter root None])).
  { change (accounted p scope [(root, Prepared.succ_edges p root)]
      (root :: SearchRun.pre_rev c) (prefix ++ [Search.Enter root None])).
    apply accounted_push. now apply accounted_append. }
  pose proof (trace_segment_accounted p scope roots _ _ _ _ Hready Hsegment Hstart HstartAccount)
    as Hfinal.
  cbn [fst snd] in Hfinal. rewrite <- app_assoc in Hfinal. exact Hfinal.
Qed.

Local Lemma trace_roots_accounted {V E} (p : Prepared.t V E) scope roots todo c evs final prefix :
  Prepared.ready p -> SearchRun.trace_roots p scope todo c evs final ->
  consistent p scope roots ([], c) -> incl todo roots ->
  accounted p scope [] (SearchRun.pre_rev c) prefix ->
    accounted p scope [] (SearchRun.pre_rev final) (prefix ++ evs).
Proof.
  intros Hready Htrace. revert prefix.
  induction Htrace as [c|root rest c here next later final Hroot Htail IH];
    intros prefix HI Hincl Haccount; [now rewrite app_nil_r|].
  destruct (trace_root_consistent p scope roots c root here next Hready Hroot HI
    (Hincl root (or_introl eq_refl))) as [Hnext Hextension].
  pose proof (trace_root_accounted p scope roots c root here next prefix Hready Hroot HI
    (Hincl root (or_introl eq_refl)) Haccount) as Haccount'.
  specialize (IH (prefix ++ here) Hnext ltac:(intros x Hx; apply Hincl; now right) Haccount').
  now rewrite <- app_assoc in IH.
Qed.

(** Every eligible labelled arc of a discovered source occurs in the actual event sequence. *)
Theorem edge_event_complete {V E} (p : Prepared.t V E) scope roots u e v :
  Prepared.ready p -> In u (Search.preorder (SearchRun.dfs p scope roots)) ->
  Prepared.arc p u e v -> Scope.admits scope v = true ->
    exists k, In (Search.Edge e u v k) (SearchRun.events p scope roots).
Proof.
  intros Hready Hu Harc Hallowed.
  destruct (SearchExact.events_wf p scope roots Hready) as [final [Hresult Htrace]].
  assert (Hinitial : accounted p scope [] (@SearchRun.pre_rev E SearchRun.initial) []).
  { intros x Hx. contradiction. }
  pose proof (trace_roots_accounted p scope roots roots SearchRun.initial _ final []
    Hready Htrace (initial_consistent p scope roots) ltac:(intros x Hx; exact Hx) Hinitial)
    as Haccount.
  rewrite Hresult, SearchRun.result_equation in Hu. cbn [Search.preorder] in Hu.
  apply (proj2 (in_rev _ _)) in Hu.
  destruct (Haccount u Hu e v (SearchInvariant.arc_successor p u e v Hready Harc) Hallowed)
    as [Hemitted|[pending [Hfalse _]]]; [exact Hemitted|contradiction].
Qed.

(** Topological orders cover the scoped reachable region and advance every eligible arc. *)
Definition topological_order {V E} (p : Prepared.t V E) scope roots order :=
  NoDup order /\
  (forall v, In v order <-> Search.scoped_reachable p scope roots v) /\
  forall u e v, In u order -> Prepared.arc p u e v -> Scope.admits scope v = true ->
    before order u v.

(** Scoped acyclicity excludes nonempty cycles in the region reached from the supplied roots. *)
Definition scoped_acyclic {V E} (p : Prepared.t V E) scope roots :=
  forall v es, Search.scoped_reachable p scope roots v ->
    Search.scoped_path p scope v es v -> es = [].

(** A returned back edge closes a scoped tree path to form a reachable nonempty cycle. *)
Definition back_witness {V E} (p : Prepared.t V E) scope roots e u v :=
  Search.scoped_reachable p scope roots u /\ Prepared.arc p u e v /\
    exists es, Search.scoped_path p scope v es u.

Local Lemma before_irrefl {A} (order : list A) v :
  NoDup order -> ~ before order v v.
Proof.
  intros Hnodup Hbefore. apply SearchInvariant.before_indices in Hbefore.
  destruct Hbefore as [i [j [Hlt [Hi Hj]]]].
  assert (Heq : i = j).
  { apply (proj1 (NoDup_nth_error _) Hnodup).
    - apply nth_error_Some. congruence.
    - congruence. }
  lia.
Qed.

Local Lemma before_trans {A} (order : list A) u v w :
  NoDup order -> before order u v -> before order v w -> before order u w.
Proof.
  intros Hnodup Huv Hvw. apply SearchInvariant.before_indices in Huv, Hvw.
  destruct Huv as [i [j [Hij [Hi Hj]]]], Hvw as [j' [k [Hjk [Hj' Hk]]]].
  assert (Heq : j = j').
  { apply (proj1 (NoDup_nth_error _) Hnodup).
    - apply nth_error_Some. congruence.
    - congruence. }
  apply SearchInvariant.before_indices. exists i, k. split; [lia|auto].
Qed.

Local Lemma rpo_post_ranks {V E} (p : Prepared.t V E) scope roots r u v j z :
  Search.exact p scope roots r ->
  Map.get positive_encoding v (Search.post_num r) = Some j ->
  Map.get positive_encoding u (Search.post_num r) = Some z ->
  (j < z)%positive -> before (rpo r) u v.
Proof.
  intros Hexact Hj Hz Hlt. rewrite rpo_equation. apply before_reverse.
  eapply before_from_indices with (i := Nat.pred (Pos.to_nat j)) (j := Nat.pred (Pos.to_nat z)).
  - apply Pos2Nat.inj_lt in Hlt. pose proof (Pos2Nat.is_pos j). pose proof (Pos2Nat.is_pos z). lia.
  - exact (proj1 (Search.post_num_index _ _ _ _ Hexact v j) Hj).
  - exact (proj1 (Search.post_num_index _ _ _ _ Hexact u z) Hz).
Qed.

Local Lemma nonback_event_forward {V E} (p : Prepared.t V E) scope roots e u v k :
  Prepared.ready p -> In (Search.Edge e u v k) (SearchRun.events p scope roots) ->
  k <> Search.Back -> before (rpo (SearchRun.dfs p scope roots)) u v.
Proof.
  intros Hready Hin Hnot.
  destruct (classify_spec p scope roots e u v k Hready Hin) as [_ [_ [_ Hkind]]].
  pose proof (SearchExact.dfs_exact p scope roots Hready) as Hexact.
  destruct k; [|contradiction| |].
  - eapply rpo_parent; [exact Hexact|exact Hkind].
  - destruct Hkind as [a [b [j [z [_ [_ [_ [Hj [Hz Hlt]]]]]]]]].
    eapply rpo_post_ranks; eassumption.
  - destruct Hkind as [a [b [j [z [_ [_ [_ [Hj [Hz Hlt]]]]]]]]].
    eapply rpo_post_ranks; eassumption.
Qed.

Local Lemma no_back_order {V E} (p : Prepared.t V E) scope roots :
  Prepared.ready p -> first_back (SearchRun.events p scope roots) = None ->
    topological_order p scope roots (rpo (SearchRun.dfs p scope roots)).
Proof.
  intros Hready Hnone. pose proof (SearchExact.dfs_exact p scope roots Hready) as Hexact.
  assert (Hcoverage : forall v, In v (rpo (SearchRun.dfs p scope roots)) <->
    Search.scoped_reachable p scope roots v).
  { intro v. rewrite rpo_equation, <- in_rev.
    rewrite <- (Search.pre_complete _ _ _ _ Hexact v).
    split; intro Hin.
    - exact (Permutation_in v (Permutation_sym (Search.post_perm _ _ _ _ Hexact)) Hin).
    - exact (Permutation_in v (Search.post_perm _ _ _ _ Hexact) Hin). }
  split.
  - rewrite rpo_equation. apply NoDup_rev.
    exact (Permutation_NoDup (Search.post_perm _ _ _ _ Hexact) (Search.pre_nodup _ _ _ _ Hexact)).
  - split; [exact Hcoverage|]. intros u e v Hu Harc Hallowed.
    apply Hcoverage in Hu. apply (Search.pre_complete _ _ _ _ Hexact) in Hu.
    destruct (edge_event_complete p scope roots u e v Hready Hu Harc Hallowed) as [k Hk].
    apply (nonback_event_forward p scope roots e u v k Hready Hk).
    intro Heq. subst k. exact (proj1 (first_back_none _) Hnone e u v Hk).
Qed.

Local Lemma ancestor_source {V E} (p : Prepared.t V E) scope roots r u v :
  Search.exact p scope roots r -> Search.ancestor r u v -> In v (Search.preorder r) ->
    In u (Search.preorder r).
Proof.
  intros Hexact Hancestor. unfold Search.ancestor in Hancestor.
  induction Hancestor as [u v [e Hget]|u|u x v Hux IHux Hxv IHxv]; intro Hv.
  - exact (proj1 (proj2 (Search.parent_edge_valid _ _ _ _ Hexact v e u Hget))).
  - exact Hv.
  - now apply IHux, IHxv.
Qed.

Local Lemma back_event_witness {V E} (p : Prepared.t V E) scope roots e u v :
  Prepared.ready p -> In (Search.Edge e u v Search.Back) (SearchRun.events p scope roots) ->
    back_witness p scope roots e u v.
Proof.
  intros Hready Hin.
  destruct (classify_spec p scope roots e u v Search.Back Hready Hin)
    as [Harc [_ [_ [Hancestor Hu]]]].
  pose proof (SearchExact.dfs_exact p scope roots Hready) as Hexact.
  pose proof (ancestor_source p scope roots _ v u Hexact Hancestor Hu) as Hv.
  destruct (proj1 (Search.white_path _ _ _ _ Hexact v u Hv Hu) Hancestor)
    as [es [Hpath _]].
  split; [now apply (Search.pre_complete _ _ _ _ Hexact)|]. split; [exact Harc|now exists es].
Qed.

(** Results are complete scoped topological orders or actual labelled cycle obstructions. *)
Theorem topological_correct {V E} (p : Prepared.t V E) scope roots :
  Prepared.ready p ->
  match topological p scope roots with
  | inl order => topological_order p scope roots order
  | inr (e, u, v) =>
    In (Search.Edge e u v Search.Back) (SearchRun.events p scope roots) /\
      back_witness p scope roots e u v
  end.
Proof.
  intro Hready. rewrite topological_equation.
  destruct (first_back (SearchRun.events p scope roots)) as [[[e u] v]|] eqn:Hback.
  - pose proof (first_back_sound _ e u v Hback) as Hin. split; [exact Hin|].
    now apply back_event_witness.
  - now apply no_back_order.
Qed.

Local Lemma path_forward {V E} (p : Prepared.t V E) scope roots order u es v :
  topological_order p scope roots order ->
  Search.scoped_path p scope u es v -> Search.scoped_reachable p scope roots u ->
    (es = [] /\ u = v) \/ before order u v.
Proof.
  intros [Hnodup [Hcoverage Hedges]] Hpath.
  induction Hpath as [u Hvalid Hallowed|u e x es v Hu Hallowed Harc Hpath IH]; intro Hreach.
  - now left.
  - assert (Htarget : Scope.admits scope x = true) by (inversion Hpath; assumption).
    pose proof (Hedges u e x (proj2 (Hcoverage u) Hreach) Harc Htarget) as Hbefore.
    assert (Hx : Search.scoped_reachable p scope roots x).
    { apply Hcoverage. apply SearchInvariant.before_indices in Hbefore.
      destruct Hbefore as [i [j [_ [_ Hj]]]]. now apply nth_error_In in Hj. }
    destruct (IH Hx) as [[Hnil Heq]|Hlater].
    + right. now rewrite <- Heq.
    + right. eapply before_trans; eassumption.
Qed.

(** Scoped acyclicity is equivalent to absence of actual Back events in the complete trace. *)
Theorem acyclic_iff_no_back {V E} (p : Prepared.t V E) scope roots :
  Prepared.ready p ->
    (scoped_acyclic p scope roots <->
      forall e u v, ~ In (Search.Edge e u v Search.Back) (SearchRun.events p scope roots)).
Proof.
  intro Hready. split.
  - intros Hacyclic e u v Hin.
    destruct (back_event_witness p scope roots e u v Hready Hin) as [Hreach [Harc [es Hpath]]].
    pose proof Harc as [a [b [Ha [Hid [Htarget [Hsource [Hend Hedge]]]]]]].
    assert (Hvalid : Prepared.valid_id p u) by (exists a; auto).
    destruct (classify_spec p scope roots e u v Search.Back Hready Hin) as [_ [Hallowed _]].
    assert (Hcycle : Search.scoped_path p scope u (e :: es) u).
    { eapply Search.scoped_cons; [exact Hvalid|exact Hallowed|exact Harc|exact Hpath]. }
    specialize (Hacyclic u (e :: es) Hreach Hcycle). discriminate.
  - intro Hnone. apply (proj2 (first_back_none _)) in Hnone.
    pose proof (no_back_order p scope roots Hready Hnone) as Horder.
    intros v es Hreach Hpath.
    destruct (path_forward p scope roots _ v es v Horder Hpath Hreach)
      as [[Hnil _]|Hbefore]; [exact Hnil|].
    exfalso. exact (before_irrefl _ v (proj1 Horder) Hbefore).
Qed.

(** The executable DAG test recognizes acyclicity on the same scoped reachable domain. *)
Theorem dag_ok_correct {V E} (p : Prepared.t V E) scope roots :
  Prepared.ready p -> (dag_ok p scope roots = true <-> scoped_acyclic p scope roots).
Proof.
  intro Hready. rewrite dag_ok_equation.
  rewrite (acyclic_iff_no_back p scope roots Hready), <- first_back_none.
  destruct (first_back (SearchRun.events p scope roots)); split; congruence.
Qed.

End SearchOrder.
