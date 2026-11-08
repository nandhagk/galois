(** * Search producer guarantees

    Producer theorems connect the actual costed run to scoped graph and numbering contracts.
    For example, the adequate root budget finishes every discovered vertex.
    Builds on: GraphSearchInvariant and GraphSearch. *)

From Stdlib Require Import List Bool PArith Arith Lia Permutation Relation_Operators.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearchSpec GraphSearch
  GraphSearchInvariant.
Import List.ListNotations Cost.Notations SearchInvariant.

Module SearchExact.
Local Open Scope nat_scope.

(** Arbitrary prepared records still produce canonical storage and unique discovery. *)
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
  apply SearchInvariant.run_representation.
Qed.

(** Ready search finishes the complete preorder and numbers both orders exactly. *)
Theorem run_numbering {V E} (p : Prepared.t V E) scope roots :
  Prepared.ready p ->
  let r := SearchRun.dfs p scope roots in
  Permutation (Search.preorder r) (Search.postorder r) /\
  (forall v i, Map.get positive_encoding v (Search.pre_num r) = Some i <->
    nth_error (Search.preorder r) (Nat.pred (Pos.to_nat i)) = Some v) /\
  (forall v i, Map.get positive_encoding v (Search.post_num r) = Some i <->
    nth_error (Search.postorder r) (Nat.pred (Pos.to_nat i)) = Some v).
Proof.
  apply SearchInvariant.run_numbering.
Qed.

(** Ready search covers precisely the admitted valid vertices reachable from the supplied roots. *)
Theorem run_reachable {V E} (p : Prepared.t V E) scope roots v :
  Prepared.ready p ->
    (In v (Search.preorder (SearchRun.dfs p scope roots)) <->
      Search.scoped_reachable p scope roots v).
Proof.
  intro Hready. split.
  - now apply SearchInvariant.run_reachable_sound.
  - now apply SearchInvariant.run_reachable_complete.
Qed.

(** A parent fact retains the selected labelled arc and the strict actual discovery ranks. *)
Definition parent_fact {V E} (p : Prepared.t V E) (c : SearchRun.core E) v e u :=
  Prepared.arc p u e v /\ In v (SearchRun.pre_rev c) /\ In u (SearchRun.pre_rev c) /\
  exists a b, Map.get positive_encoding u (SearchRun.pre_index c) = Some a /\
    Map.get positive_encoding v (SearchRun.pre_index c) = Some b /\ (a < b)%positive.

(** Parent bindings and parentless discoveries retain their original graph and root provenance. *)
Record parent_laws {V E} (p : Prepared.t V E) roots (c : SearchRun.core E) : Prop := {
  selected_parent : forall v e u,
    Map.get positive_encoding v (SearchRun.parents c) = Some (e, u) ->
      parent_fact p c v e u;
  selected_root : forall v, In v (SearchRun.pre_rev c) ->
    Map.get positive_encoding v (SearchRun.parents c) = None -> In v roots
}.

Local Lemma parent_absent {V E} (p : Prepared.t V E) roots c v :
  parent_laws p roots c -> ~ In v (SearchRun.pre_rev c) ->
    Map.get positive_encoding v (SearchRun.parents c) = None.
Proof.
  intros Hparents Hfresh.
  destruct (Map.get positive_encoding v (SearchRun.parents c)) as [[e u]|] eqn:Hget;
    [|reflexivity].
  destruct (selected_parent _ _ _ Hparents v e u Hget) as [_ [Hin _]]. contradiction.
Qed.

Local Lemma discover_old_fact {V E} (p : Prepared.t V E) c w via v e u :
  representation c -> ~ In w (SearchRun.pre_rev c) -> parent_fact p c v e u ->
    parent_fact p (SearchRun.discover w via c) v e u.
Proof.
  intros Hrep Hfresh [Harc [Hv [Hu [a [b [Ha [Hb Hlt]]]]]]].
  rewrite SearchRun.discover_equation. unfold parent_fact. cbn.
  split; [exact Harc|]. split; [now right|]. split; [now right|].
  exists a, b.
  rewrite (Map.get_set_other positive_encoding positive_encoding_laws)
    by (first [exact (pre_index_wf _ Hrep)|intro Heq; subst u; contradiction]).
  rewrite (Map.get_set_other positive_encoding positive_encoding_laws)
    by (first [exact (pre_index_wf _ Hrep)|intro Heq; subst v; contradiction]).
  auto.
Qed.

Local Lemma discover_new_fact {V E} (p : Prepared.t V E) stack c v e u :
  representation c -> history (stack, c) -> ~ In v (SearchRun.pre_rev c) ->
  Prepared.arc p u e v -> In u (SearchRun.pre_rev c) ->
    parent_fact p (SearchRun.discover v (Some (e, u)) c) v e u.
Proof.
  intros Hrep Hhistory Hfresh Harc Hu.
  destruct (proj2 (numbering_domain _ _ _ (pre_numbering _ Hhistory) u) Hu) as [a Ha].
  pose proof (numbering_bound _ _ _ (pre_numbering _ Hhistory) u a Ha) as Hlt.
  rewrite SearchRun.discover_equation. unfold parent_fact. cbn.
  split; [exact Harc|]. split; [now left|]. split; [now right|].
  exists a, (SearchRun.pre_clock c).
  rewrite (Map.get_set_other positive_encoding positive_encoding_laws)
    by (first [exact (pre_index_wf _ Hrep)|intro Heq; subst u; contradiction]).
  rewrite Map.get_set_same by exact (pre_index_wf _ Hrep). auto.
Qed.

Local Lemma discover_parents {V E} (p : Prepared.t V E) roots stack c v via :
  representation c -> history (stack, c) -> parent_laws p roots c ->
  ~ In v (SearchRun.pre_rev c) ->
  (match via with
  | None => In v roots
  | Some (e, u) => Prepared.arc p u e v /\ In u (SearchRun.pre_rev c)
  end) ->
    parent_laws p roots (SearchRun.discover v via c).
Proof.
  intros Hrep Hhistory Hparents Hfresh Hvia.
  pose proof (parent_absent p roots c v Hparents Hfresh) as Hnone.
  constructor.
  - intros x e u Hget. destruct via as [[edge parent]|].
    + rewrite SearchRun.discover_equation in Hget. cbn [SearchRun.parents] in Hget.
      destruct (Pos.eq_dec x v) as [->|Hne].
      * rewrite Map.get_set_same in Hget by exact (parents_wf _ Hrep).
        inversion Hget; subst e u. destruct Hvia as [Harc Hparent].
        eapply discover_new_fact; eassumption.
      * rewrite (Map.get_set_other positive_encoding positive_encoding_laws) in Hget
          by (first [exact (parents_wf _ Hrep)|exact Hne]).
        apply discover_old_fact; [exact Hrep|exact Hfresh|].
        exact (selected_parent _ _ _ Hparents x e u Hget).
    + apply discover_old_fact; [exact Hrep|exact Hfresh|].
      rewrite SearchRun.discover_equation in Hget.
      exact (selected_parent _ _ _ Hparents x e u Hget).
  - intros x Hin Hget. rewrite SearchRun.discover_equation in Hin, Hget.
    cbn [SearchRun.pre_rev SearchRun.parents] in Hin, Hget.
    destruct Hin as [<-|Hin].
    + destruct via as [edge|]; [rewrite Map.get_set_same in Hget
        by exact (parents_wf _ Hrep); discriminate|exact Hvia].
    + apply (selected_root _ _ _ Hparents x Hin).
      destruct via as [edge|]; [|exact Hget].
      rewrite (Map.get_set_other positive_encoding positive_encoding_laws) in Hget
        by (first [exact (parents_wf _ Hrep)|intro Heq; subst x; contradiction]).
      exact Hget.
Qed.

Local Lemma finish_parents {V E} (p : Prepared.t V E) roots c v :
  parent_laws p roots c -> parent_laws p roots (SearchRun.finish v c).
Proof.
  intros [Hparents Hroots]. rewrite SearchRun.finish_equation.
  constructor; [exact Hparents|exact Hroots].
Qed.

(** A transition preserves labelled parent provenance and strict parent ranks. *)
Theorem transition_parents {V E} (p : Prepared.t V E) scope roots w :
  Prepared.ready p -> representation (snd w) -> history w ->
  sound_work p scope roots w -> parent_laws p roots (snd w) ->
    parent_laws p roots (snd (SearchRun.unwrap (fst (SearchRun.transition p scope w)))).
Proof.
  intros Hready. destruct w as [stack c]. intros Hrep Hhistory Hsound Hparents.
  rewrite SearchRun.step_equation.
  destruct stack as [|[u [|[e v] pending]] rest]; cbn [fst snd SearchRun.unwrap].
  - exact Hparents.
  - now apply finish_parents.
  - destruct (Scope.admits scope v); [|exact Hparents].
    destruct (Prepared.name_of p v); [|exact Hparents].
    destruct (SearchRun.edge_kind c u v) eqn:Hkind; cbn [fst snd SearchRun.unwrap];
      try exact Hparents.
    assert (Hfresh : ~ In v (SearchRun.pre_rev c)).
    { intro Hin. apply (seen_discovered _ Hrep) in Hin.
      pose proof (proj1 (tree_is_white c u v) Hkind) as Hwhite.
      change (FinSet.mem positive_encoding v (SearchRun.seen c) = true) in Hin.
      rewrite Hwhite in Hin. discriminate. }
    destruct (valid_frames _ _ _ _ Hsound u ((e, v) :: pending) (or_introl eq_refl))
      as [Hu [Hvalid [_ Hedges]]].
    eapply discover_parents; [exact Hrep|exact Hhistory|exact Hparents|exact Hfresh|].
    split.
    + exact (proj1 (successor_arc p u e v Hready Hvalid (Hedges _ (or_introl eq_refl)))).
    + now apply (seen_discovered _ Hrep).
Qed.

Local Lemma loop_parents {V E} (p : Prepared.t V E) scope roots n w :
  Prepared.ready p -> representation (snd w) -> history w ->
  sound_work p scope roots w -> parent_laws p roots (snd w) ->
    parent_laws p roots (snd (fst (SearchRun.reference_loop p scope n w))).
Proof.
  intro Hready. revert w. induction n as [|n IH];
    intros w Hrep Hhistory Hsound Hparents; [exact Hparents|].
  pose proof (transition_representation p scope w Hrep) as Hrep'.
  pose proof (transition_history p scope w Hrep Hhistory) as Hhistory'.
  pose proof (transition_sound p scope roots w Hready Hrep Hsound) as Hsound'.
  pose proof (transition_parents p scope roots w Hready Hrep Hhistory Hsound Hparents)
    as Hparents'.
  cbn [SearchRun.reference_loop].
  destruct (SearchRun.transition p scope w) as [[w'|w'] evs];
    cbn [fst snd SearchRun.unwrap] in Hrep', Hhistory', Hsound', Hparents'.
  - specialize (IH w' Hrep' Hhistory' Hsound' Hparents').
    destruct (SearchRun.reference_loop p scope n w') as [final later]. exact IH.
  - exact Hparents'.
Qed.

Local Lemma root_parents {V E} (p : Prepared.t V E) scope roots c v :
  Prepared.ready p -> representation c -> history ([], c) ->
  sound_work p scope roots ([], c) -> parent_laws p roots c -> In v roots ->
    parent_laws p roots (fst (SearchRun.reference_root p scope c v)).
Proof.
  intros Hready Hrep Hhistory Hsound Hparents Hroot. unfold SearchRun.reference_root.
  destruct (Scope.admits scope v) eqn:Hallowed; [|exact Hparents].
  destruct (FinSet.mem positive_encoding v (SearchRun.seen c)) eqn:Hfresh;
    [exact Hparents|].
  destruct (Prepared.name_of p v) as [name|] eqn:Hname; [|exact Hparents].
  assert (Hvalid : Prepared.valid_id p v).
  { apply vertices_spec. exact (named_in_vertices p v name Hready Hname). }
  assert (Hreach : Search.scoped_reachable p scope roots v).
  { exists v, []. split; [exact Hroot|now apply Search.scoped_nil]. }
  assert (Hfreshpre : ~ In v (SearchRun.pre_rev c)).
  { intro Hin. apply (seen_discovered _ Hrep) in Hin. congruence. }
  pose proof (loop_parents p scope roots (Pos.to_nat (Prepared.fuel p))
    ([(v, Prepared.succ_edges p v)], SearchRun.discover v None c) Hready
    (discover_representation c v None Hrep Hfresh)
    (discover_history [] c v None (Prepared.succ_edges p v) Hhistory Hfreshpre)
    (sound_push p scope roots [] c v None Hrep Hsound Hreach Hvalid Hallowed)
    (discover_parents p roots [] c v None Hrep Hhistory Hparents Hfreshpre Hroot))
    as Hloop.
  destruct (SearchRun.reference_loop p scope (Pos.to_nat (Prepared.fuel p))
    ([(v, Prepared.succ_edges p v)], SearchRun.discover v None c)) as [w evs].
  exact Hloop.
Qed.

Local Lemma roots_parents {V E} (p : Prepared.t V E) scope roots todo c :
  Prepared.ready p -> incl todo roots -> representation c -> history ([], c) ->
  sound_work p scope roots ([], c) -> parent_laws p roots c ->
    parent_laws p roots (fst (SearchRun.reference_roots p scope todo c)).
Proof.
  intro Hready. revert c. induction todo as [|v rest IH];
    intros c Htodo Hrep Hhistory Hsound Hparents; [exact Hparents|].
  pose proof (root_representation p scope c v Hrep) as Hrep'.
  pose proof (root_history p scope c v Hready Hrep Hhistory) as Hhistory'.
  pose proof (root_sound p scope roots c v Hready Hrep Hsound
    (Htodo v (or_introl eq_refl))) as Hsound'.
  pose proof (root_parents p scope roots c v Hready Hrep Hhistory Hsound Hparents
    (Htodo v (or_introl eq_refl))) as Hparents'.
  cbn [SearchRun.reference_roots].
  destruct (SearchRun.reference_root p scope c v) as [c' here].
  specialize (IH c' ltac:(intros x Hx; apply Htodo; now right)
    Hrep' Hhistory' Hsound' Hparents').
  destruct (SearchRun.reference_roots p scope rest c') as [final later]. exact IH.
Qed.

(** The final core retains the actual labelled parents and strictly earlier parent ranks. *)
Theorem final_parents {V E} (p : Prepared.t V E) scope roots :
  Prepared.ready p ->
    parent_laws p roots (fst (SearchRun.reference_roots p scope roots SearchRun.initial)).
Proof.
  intro Hready. apply roots_parents; try assumption.
  - intros v Hv. exact Hv.
  - apply initial_representation.
  - apply initial_history.
  - constructor.
    + intros v Hv. change (FinSet.mem positive_encoding v FinSet.empty = true) in Hv.
      rewrite FinSet.mem_empty in Hv. discriminate.
    + intros u es Hin. contradiction.
  - constructor.
    + intros v e u Hget. change (Map.get positive_encoding v Map.empty = Some (e, u)) in Hget.
      rewrite Map.get_empty in Hget. discriminate.
    + intros v Hin. contradiction.
Qed.

Local Lemma parent_relation_finite {V E} (p : Prepared.t V E) roots c :
  parent_laws p roots c ->
    well_founded
      (fun u v => exists e, Map.get positive_encoding v (SearchRun.parents c) = Some (e, u)).
Proof.
  intro Hparents.
  set (rank := fun v =>
    match Map.get positive_encoding v (SearchRun.pre_index c) with
    | None => 0
    | Some k => Pos.to_nat k
    end).
  assert (Hacc : forall n v, rank v = n ->
    Acc (fun u v => exists e,
      Map.get positive_encoding v (SearchRun.parents c) = Some (e, u)) v).
  { intro n. induction n using lt_wf_ind. intros v Hrank. constructor.
    intros u [e Hget]. apply (H (rank u)); [|reflexivity].
    destruct (selected_parent _ _ _ Hparents v e u Hget)
      as [_ [_ [_ [a [b [Ha [Hb Hlt]]]]]]].
    unfold rank in *. rewrite Ha. rewrite Hb in Hrank.
    apply Pos2Nat.inj_lt in Hlt. lia. }
  intro v. exact (Hacc (rank v) v eq_refl).
Qed.

(** Search retains genuine selected parents, actual roots and a finite discovery forest. *)
Theorem run_parents {V E} (p : Prepared.t V E) scope roots :
  Prepared.ready p ->
  let r := SearchRun.dfs p scope roots in
  (forall v e u, Map.get positive_encoding v (Search.parent_edge r) = Some (e, u) ->
    Prepared.arc p u e v /\ In u (Search.preorder r) /\ In v (Search.preorder r)) /\
  (forall v, In v (Search.preorder r) ->
    Map.get positive_encoding v (Search.parent_edge r) = None -> In v roots) /\
  well_founded
    (fun u v => exists e, Map.get positive_encoding v (Search.parent_edge r) = Some (e, u)).
Proof.
  intro Hready. pose proof (final_parents p scope roots Hready) as Hparents.
  unfold SearchRun.dfs. rewrite SearchRun.run_equation.
  destruct (SearchRun.reference_roots p scope roots SearchRun.initial) as [c evs].
  cbn [fst] in Hparents |- *.
  unfold SearchRun.result, SearchRun.result_c. autorewrite with galois_cost.
  cbn [Search.parent_edge Search.preorder].
  split.
  - intros v e u Hget.
    destruct (selected_parent _ _ _ Hparents v e u Hget) as [Harc [Hv [Hu Hrank]]].
    split; [exact Harc|]. split.
    + exact (proj1 (in_rev _ _) Hu).
    + exact (proj1 (in_rev _ _) Hv).
  - split.
    + intros v Hv Hnone. apply (selected_root _ _ _ Hparents v); [|exact Hnone].
      now apply (proj2 (in_rev _ _)).
    + now apply parent_relation_finite with (p := p) (roots := roots).
Qed.

Definition ancestry {E} (c : SearchRun.core E) :=
  clos_refl_trans positive
    (fun u v => exists e, Map.get positive_encoding v (SearchRun.parents c) = Some (e, u)).

Local Lemma ancestry_no_out {V E} (p : Prepared.t V E) roots c w :
  parent_laws p roots c -> ~ In w (SearchRun.pre_rev c) ->
  forall u v, ancestry c u v -> u = w -> v = w.
Proof.
  intros Hparents Hfresh u v Hancestor.
  induction Hancestor as [u v [e Hget]|u|u x v Hux IHux Hxv IHxv]; intro Hu.
  - subst u. destruct (selected_parent _ _ _ Hparents v e w Hget) as [_ [_ [Hin _]]].
    contradiction.
  - exact Hu.
  - apply IHxv, IHux, Hu.
Qed.

Local Lemma ancestry_no_in {V E} (p : Prepared.t V E) roots c w :
  parent_laws p roots c -> ~ In w (SearchRun.pre_rev c) ->
  forall u v, ancestry c u v -> v = w -> u = w.
Proof.
  intros Hparents Hfresh u v Hancestor.
  induction Hancestor as [u v [e Hget]|u|u x v Hux IHux Hxv IHxv]; intro Hv.
  - subst v. destruct (selected_parent _ _ _ Hparents w e u Hget) as [_ [Hin _]].
    contradiction.
  - exact Hv.
  - apply IHux, IHxv, Hv.
Qed.

Local Lemma ancestry_embed {V E} (p : Prepared.t V E) roots c w edge :
  representation c -> parent_laws p roots c -> ~ In w (SearchRun.pre_rev c) ->
  forall u v, ancestry c u v ->
    ancestry (SearchRun.discover w (Some edge) c) u v.
Proof.
  intros Hrep Hparents Hfresh u v Hancestor.
  induction Hancestor as [u v [e Hget]|u|u x v Hux IHux Hxv IHxv].
  - apply rt_step. exists e. rewrite SearchRun.discover_equation. cbn [SearchRun.parents].
    rewrite (Map.get_set_other positive_encoding positive_encoding_laws).
    + exact Hget.
    + exact (parents_wf _ Hrep).
    + intro Heq. subst v.
      destruct (selected_parent _ _ _ Hparents w e u Hget) as [_ [Hin _]]. contradiction.
  - apply rt_refl.
  - eapply rt_trans; eassumption.
Qed.

Local Lemma ancestry_discover {V E} (p : Prepared.t V E) roots c w edge parent :
  representation c -> parent_laws p roots c -> ~ In w (SearchRun.pre_rev c) ->
  forall u v,
  ancestry (SearchRun.discover w (Some (edge, parent)) c) u v <->
    ancestry c u v \/ (v = w /\ ancestry c u parent).
Proof.
  intros Hrep Hparents Hfresh u v. split.
  - intro Hancestor.
    induction Hancestor as [u v [e Hget]|u|u x v Hux IHux Hxv IHxv].
    + rewrite SearchRun.discover_equation in Hget. cbn [SearchRun.parents] in Hget.
      destruct (Pos.eq_dec v w) as [->|Hne].
      * rewrite Map.get_set_same in Hget by exact (parents_wf _ Hrep).
        inversion Hget; subst u e. right. split; [reflexivity|apply rt_refl].
      * rewrite (Map.get_set_other positive_encoding positive_encoding_laws) in Hget
          by (first [exact (parents_wf _ Hrep)|exact Hne]).
        left. apply rt_step. now exists e.
    + left. apply rt_refl.
    + destruct IHux as [Hux'|[Hx Hux']], IHxv as [Hxv'|[Hv Hxv']].
      * left. eapply rt_trans; eassumption.
      * right. split; [exact Hv|]. eapply rt_trans; eassumption.
      * right. split; [|exact Hux'].
        eapply ancestry_no_out; [exact Hparents|exact Hfresh|exact Hxv'|exact Hx].
      * right. auto.
  - intros [Hancestor|[-> Hancestor]].
    + eapply ancestry_embed; eassumption.
    + eapply rt_trans; [eapply ancestry_embed; eassumption|].
      apply rt_step. exists edge. rewrite SearchRun.discover_equation.
      cbn [SearchRun.parents]. apply Map.get_set_same. exact (parents_wf _ Hrep).
Qed.

(** Unfinished intervals extend beyond every already closed interval. *)
Definition open_interval {E} (c : SearchRun.core E) u v :=
  match Map.get positive_encoding u (SearchRun.pre_index c),
    Map.get positive_encoding v (SearchRun.pre_index c) with
  | Some a, Some b =>
    (Pos.leb a b &&
      match Map.get positive_encoding u (SearchRun.post_index c),
        Map.get positive_encoding v (SearchRun.post_index c) with
      | None, _ => true
      | Some x, Some y => Pos.leb y x
      | Some _, None => false
      end)%bool
  | _, _ => false
  end.

Local Lemma post_in_pre {E} stack (c : SearchRun.core E) v :
  history (stack, c) -> In v (SearchRun.post_rev c) -> In v (SearchRun.pre_rev c).
Proof.
  intros Hhistory Hin.
  apply (Permutation_in v (Permutation_sym (partition _ Hhistory))).
  apply in_or_app. now right.
Qed.

Local Lemma unfinished_in_stack {E} stack (c : SearchRun.core E) v :
  history (stack, c) -> In v (SearchRun.pre_rev c) -> ~ In v (SearchRun.post_rev c) ->
    In v (map fst stack).
Proof.
  intros Hhistory Hin Hnot.
  apply (Permutation_in v (partition _ Hhistory)) in Hin.
  apply in_app_iff in Hin. tauto.
Qed.

Local Lemma fresh_post_absent {E} stack (c : SearchRun.core E) v :
  history (stack, c) -> ~ In v (SearchRun.pre_rev c) ->
    Map.get positive_encoding v (SearchRun.post_index c) = None.
Proof.
  intros Hhistory Hfresh.
  destruct (Map.get positive_encoding v (SearchRun.post_index c)) as [k|] eqn:Hget;
    [|reflexivity].
  exfalso. apply Hfresh. eapply post_in_pre; [exact Hhistory|].
  apply (numbering_domain _ _ _ (post_numbering _ Hhistory)). now exists k.
Qed.

Local Lemma top_post_absent {E} u es rest (c : SearchRun.core E) :
  history ((u, es) :: rest, c) ->
    Map.get positive_encoding u (SearchRun.post_index c) = None.
Proof.
  intro Hhistory.
  destruct (Map.get positive_encoding u (SearchRun.post_index c)) as [k|] eqn:Hget;
    [|reflexivity].
  assert (Hu : In u (SearchRun.post_rev c)).
  { apply (numbering_domain _ _ _ (post_numbering _ Hhistory)). now exists k. }
  pose proof (Permutation_NoDup (partition _ Hhistory)
    (numbering_nodup _ _ _ (pre_numbering _ Hhistory))) as Hnodup.
  cbn [fst snd map app] in Hnodup.
  inversion Hnodup as [|x xs Hnot Htail]; subst x xs.
  exfalso. apply Hnot. apply in_or_app. now right.
Qed.

Definition stack_order {E} (stack : list (SearchRun.frame E)) (c : SearchRun.core E) :=
  forall u v, before (map fst stack) u v ->
    exists a b, Map.get positive_encoding u (SearchRun.pre_index c) = Some a /\
      Map.get positive_encoding v (SearchRun.pre_index c) = Some b /\ (b < a)%positive.

Local Lemma before_cons {A} (x u v : A) xs :
  before (x :: xs) u v <-> (u = x /\ In v xs) \/ before xs u v.
Proof.
  split.
  - intros [[|a left] [middle [right Heq]]].
    + cbn in Heq. inversion Heq; subst x xs. left. split; [reflexivity|].
      apply in_or_app. right. now left.
    + cbn in Heq. inversion Heq; subst a xs.
      right. now exists left, middle, right.
  - intros [[-> Hin]|[left [middle [right ->]]]].
    + apply in_split in Hin. destruct Hin as [left [right ->]]. now exists [], left, right.
    + exists (x :: left), middle, right. reflexivity.
Qed.

Local Lemma top_rank {E} top es rest (c : SearchRun.core E) v a b :
  history ((top, es) :: rest, c) -> stack_order ((top, es) :: rest) c ->
  In v (SearchRun.pre_rev c) ->
  Map.get positive_encoding v (SearchRun.post_index c) = None ->
  Map.get positive_encoding v (SearchRun.pre_index c) = Some a ->
  Map.get positive_encoding top (SearchRun.pre_index c) = Some b -> (a <= b)%positive.
Proof.
  intros Hhistory Horder Hv Hpost Ha Hb.
  assert (Hnot : ~ In v (SearchRun.post_rev c)).
  { intro Hin. apply (numbering_domain _ _ _ (post_numbering _ Hhistory)) in Hin.
    destruct Hin as [k Hk].
    change (Map.get positive_encoding v (SearchRun.post_index c) = Some k) in Hk.
    rewrite Hpost in Hk. discriminate. }
  pose proof (unfinished_in_stack _ _ v Hhistory Hv Hnot) as Hstack.
  cbn [map fst] in Hstack. destruct Hstack as [Heq|Hin].
  - subst v. rewrite Ha in Hb. inversion Hb. apply Pos.le_refl.
  - assert (Hbefore : before (map fst ((top, es) :: rest)) top v).
    { cbn [map fst]. apply before_cons. left. auto. }
    destruct (Horder top v Hbefore) as [x [y [Hx [Hy Hlt]]]].
    rewrite Hb in Hx. rewrite Ha in Hy. inversion Hx; inversion Hy; subst x y.
    now apply Pos.lt_le_incl.
Qed.

Local Lemma discover_interval_old {E} (c : SearchRun.core E) w via u v :
  representation c -> ~ In w (SearchRun.pre_rev c) ->
  In u (SearchRun.pre_rev c) -> In v (SearchRun.pre_rev c) ->
    open_interval (SearchRun.discover w via c) u v = open_interval c u v.
Proof.
  intros Hrep Hfresh Hu Hv. rewrite SearchRun.discover_equation.
  unfold open_interval. cbn [SearchRun.pre_index SearchRun.post_index].
  rewrite (Map.get_set_other positive_encoding positive_encoding_laws)
    by (first [exact (pre_index_wf _ Hrep)|intro Heq; subst u; contradiction]).
  rewrite (Map.get_set_other positive_encoding positive_encoding_laws)
    by (first [exact (pre_index_wf _ Hrep)|intro Heq; subst v; contradiction]).
  reflexivity.
Qed.

Local Lemma discover_interval_left {E} stack (c : SearchRun.core E) w via v :
  representation c -> history (stack, c) -> ~ In w (SearchRun.pre_rev c) ->
  In v (SearchRun.pre_rev c) ->
    open_interval (SearchRun.discover w via c) w v = false.
Proof.
  intros Hrep Hhistory Hfresh Hv.
  destruct (proj2 (numbering_domain _ _ _ (pre_numbering _ Hhistory) v) Hv) as [k Hk].
  change (Map.get positive_encoding v (SearchRun.pre_index c) = Some k) in Hk.
  rewrite SearchRun.discover_equation. unfold open_interval.
  cbn [SearchRun.pre_index SearchRun.post_index].
  rewrite Map.get_set_same by exact (pre_index_wf _ Hrep).
  rewrite (Map.get_set_other positive_encoding positive_encoding_laws)
    by (first [exact (pre_index_wf _ Hrep)|intro Heq; subst v; contradiction]).
  rewrite Hk.
  assert (Hfalse : Pos.leb (SearchRun.pre_clock c) k = false).
  { apply Pos.leb_gt. exact (numbering_bound _ _ _ (pre_numbering _ Hhistory) v k Hk). }
  rewrite Hfalse. reflexivity.
Qed.

Local Lemma discover_interval_right {E} stack (c : SearchRun.core E) w via u :
  representation c -> history (stack, c) -> ~ In w (SearchRun.pre_rev c) ->
  In u (SearchRun.pre_rev c) ->
    (open_interval (SearchRun.discover w via c) u w = true <->
      Map.get positive_encoding u (SearchRun.post_index c) = None).
Proof.
  intros Hrep Hhistory Hfresh Hu.
  destruct (proj2 (numbering_domain _ _ _ (pre_numbering _ Hhistory) u) Hu) as [k Hk].
  change (Map.get positive_encoding u (SearchRun.pre_index c) = Some k) in Hk.
  pose proof (fresh_post_absent stack c w Hhistory Hfresh) as Hnone.
  rewrite SearchRun.discover_equation. unfold open_interval.
  cbn [SearchRun.pre_index SearchRun.post_index].
  rewrite (Map.get_set_other positive_encoding positive_encoding_laws)
    by (first [exact (pre_index_wf _ Hrep)|intro Heq; subst u; contradiction]).
  rewrite Map.get_set_same by exact (pre_index_wf _ Hrep).
  rewrite Hk, Hnone.
  assert (Hle : Pos.leb k (SearchRun.pre_clock c) = true).
  { apply Pos.leb_le, Pos.lt_le_incl.
    exact (numbering_bound _ _ _ (pre_numbering _ Hhistory) u k Hk). }
  rewrite Hle. destruct (Map.get positive_encoding u (SearchRun.post_index c)); cbn;
    split; congruence.
Qed.

Local Lemma discover_interval_self {E} (c : SearchRun.core E) w via :
  representation c -> open_interval (SearchRun.discover w via c) w w = true.
Proof.
  intro Hrep. rewrite SearchRun.discover_equation. unfold open_interval.
  cbn [SearchRun.pre_index SearchRun.post_index].
  rewrite Map.get_set_same by exact (pre_index_wf _ Hrep). rewrite Pos.leb_refl.
  destruct (Map.get positive_encoding w (SearchRun.post_index c)); cbn;
    [apply Pos.leb_refl|reflexivity].
Qed.

Local Lemma finish_interval {E} top es rest (c : SearchRun.core E) u v :
  representation c -> history ((top, es) :: rest, c) ->
  stack_order ((top, es) :: rest) c ->
  In u (SearchRun.pre_rev c) -> In v (SearchRun.pre_rev c) ->
    open_interval (SearchRun.finish top c) u v = open_interval c u v.
Proof.
  intros Hrep Hhistory Horder Hu Hv.
  destruct (proj2 (numbering_domain _ _ _ (pre_numbering _ Hhistory) u) Hu) as [a Ha].
  destruct (proj2 (numbering_domain _ _ _ (pre_numbering _ Hhistory) v) Hv) as [b Hb].
  cbn [snd] in Ha, Hb.
  pose proof (top_post_absent top es rest c Hhistory) as Hnone.
  rewrite SearchRun.finish_equation. unfold open_interval.
  cbn [SearchRun.pre_index SearchRun.post_index]. rewrite Ha, Hb.
  destruct (Pos.eq_dec u top) as [->|Hu']; destruct (Pos.eq_dec v top) as [->|Hv'].
  - rewrite Map.get_set_same by exact (post_index_wf _ Hrep).
    rewrite Hnone, Pos.leb_refl. reflexivity.
  - rewrite Map.get_set_same by exact (post_index_wf _ Hrep).
    rewrite (Map.get_set_other positive_encoding positive_encoding_laws)
      by (first [exact (post_index_wf _ Hrep)|exact Hv']).
    rewrite Hnone. destruct (Map.get positive_encoding v (SearchRun.post_index c))
      as [d|] eqn:Hd.
    + assert (Hle : Pos.leb d (SearchRun.post_clock c) = true).
      { apply Pos.leb_le, Pos.lt_le_incl.
        exact (numbering_bound _ _ _ (post_numbering _ Hhistory) v d Hd). }
      now rewrite Hle.
    + assert (Hfalse : Pos.leb a b = false).
      { apply not_true_is_false. intro Hle. apply Pos.leb_le in Hle.
        pose proof (top_rank top es rest c v b a Hhistory Horder Hv Hd Hb Ha) as Hback.
        assert (Heq : a = b) by (apply Pos.le_antisym; assumption).
        exfalso. apply Hv'. apply (numbering_injective _ _ _ v top b
          (pre_numbering _ Hhistory) Hb). now rewrite Heq in Ha. }
      now rewrite Hfalse.
  - rewrite (Map.get_set_other positive_encoding positive_encoding_laws)
      by (first [exact (post_index_wf _ Hrep)|exact Hu']).
    rewrite Map.get_set_same by exact (post_index_wf _ Hrep).
    rewrite Hnone. destruct (Map.get positive_encoding u (SearchRun.post_index c))
      as [d|] eqn:Hd; [|reflexivity].
    assert (Hfalse : Pos.leb (SearchRun.post_clock c) d = false).
    { apply Pos.leb_gt. exact (numbering_bound _ _ _ (post_numbering _ Hhistory) u d Hd). }
    now rewrite Hfalse.
  - rewrite !(Map.get_set_other positive_encoding positive_encoding_laws)
      by (first [exact (post_index_wf _ Hrep)|assumption]). reflexivity.
Qed.

(** Stack order, open ancestry intervals and finished-edge facts describe one evolving DFS forest. *)
Record interval_laws {V E} (p : Prepared.t V E) scope stack (c : SearchRun.core E) : Prop := {
  ordered_stack : stack_order stack c;
  interval_tree : forall u v, In u (SearchRun.pre_rev c) -> In v (SearchRun.pre_rev c) ->
    (open_interval c u v = true <-> ancestry c u v);
  finished_edges : forall u, In u (SearchRun.post_rev c) ->
    forall e v, In (e, v) (Prepared.succ_edges p u) -> Scope.admits scope v = true ->
      (exists j k, Map.get positive_encoding v (SearchRun.post_index c) = Some j /\
        Map.get positive_encoding u (SearchRun.post_index c) = Some k /\ (j < k)%positive) \/
      ancestry c v u
}.

Local Lemma active_ancestor {V E} (p : Prepared.t V E) scope top es rest c u :
  history ((top, es) :: rest, c) -> interval_laws p scope ((top, es) :: rest) c ->
  In u (SearchRun.pre_rev c) ->
    (ancestry c u top <-> Map.get positive_encoding u (SearchRun.post_index c) = None).
Proof.
  intros Hhistory Hinterval Hu.
  assert (Htop : In top (SearchRun.pre_rev c)).
  { apply (Permutation_in top (Permutation_sym (partition _ Hhistory))).
    apply in_or_app. left. now left. }
  rewrite <- (interval_tree _ _ _ _ Hinterval u top Hu Htop).
  destruct (proj2 (numbering_domain _ _ _ (pre_numbering _ Hhistory) u) Hu) as [a Ha].
  destruct (proj2 (numbering_domain _ _ _ (pre_numbering _ Hhistory) top) Htop) as [b Hb].
  cbn [snd] in Ha, Hb.
  pose proof (top_post_absent top es rest c Hhistory) as Hnone.
  unfold open_interval. rewrite Ha, Hb, Hnone.
  destruct (Map.get positive_encoding u (SearchRun.post_index c)) as [d|] eqn:Hpost.
  - rewrite andb_false_r. split; discriminate.
  - assert (Hle : Pos.leb a b = true).
    { apply Pos.leb_le.
      exact (top_rank top es rest c u a b Hhistory (ordered_stack _ _ _ _ Hinterval)
        Hu Hpost Ha Hb). }
    rewrite Hle. split; reflexivity.
Qed.

Local Lemma discover_ancestry {V E} (p : Prepared.t V E) roots c w via :
  representation c -> parent_laws p roots c -> ~ In w (SearchRun.pre_rev c) ->
  forall u v, ancestry (SearchRun.discover w via c) u v <->
    ancestry c u v \/
      match via with
      | None => False
      | Some (_, parent) => v = w /\ ancestry c u parent
      end.
Proof.
  intros Hrep Hparents Hfresh u v. destruct via as [[edge parent]|].
  - eapply ancestry_discover; eassumption.
  - rewrite SearchRun.discover_equation. unfold ancestry. cbn [SearchRun.parents]. tauto.
Qed.

Local Lemma discover_old_to_new {V E} (p : Prepared.t V E) roots c w via u :
  representation c -> parent_laws p roots c -> ~ In w (SearchRun.pre_rev c) ->
  In u (SearchRun.pre_rev c) ->
    (ancestry (SearchRun.discover w via c) u w <->
      match via with None => False | Some (_, parent) => ancestry c u parent end).
Proof.
  intros Hrep Hparents Hfresh Hu.
  rewrite (discover_ancestry p roots c w via Hrep Hparents Hfresh).
  assert (Hnot : ~ ancestry c u w).
  { intro Hancestor. apply Hfresh.
    assert (Heq : u = w) by
      (eapply ancestry_no_in; [exact Hparents|exact Hfresh|exact Hancestor|reflexivity]).
    now subst u. }
  destruct via as [[edge parent]|]; cbn; tauto.
Qed.

Local Lemma discover_tree_intervals {V E} (p : Prepared.t V E) scope roots stack c w via :
  representation c -> history (stack, c) -> parent_laws p roots c ->
  interval_laws p scope stack c -> ~ In w (SearchRun.pre_rev c) ->
  (match via with
  | None => stack = []
  | Some (_, parent) => exists es rest, stack = (parent, es) :: rest
  end) ->
  forall u v, In u (w :: SearchRun.pre_rev c) -> In v (w :: SearchRun.pre_rev c) ->
    (open_interval (SearchRun.discover w via c) u v = true <->
      ancestry (SearchRun.discover w via c) u v).
Proof.
  intros Hrep Hhistory Hparents Hinterval Hfresh Hvia u v Hu Hv.
  destruct Hu as [<-|Hu], Hv as [<-|Hv].
  - rewrite discover_interval_self by exact Hrep. split; [intros _; apply rt_refl|reflexivity].
  - rewrite (discover_interval_left stack c w via v Hrep Hhistory Hfresh Hv).
    rewrite (discover_ancestry p roots c w via Hrep Hparents Hfresh).
    split; [discriminate|intros [Hancestor|Hancestor]].
    + exfalso. apply Hfresh.
      assert (Heq : v = w) by
        (eapply ancestry_no_out; [exact Hparents|exact Hfresh|exact Hancestor|reflexivity]).
      now subst v.
    + destruct via as [[edge parent]|]; [destruct Hancestor as [Heq _]; subst v; contradiction|
        contradiction].
  - rewrite (discover_interval_right stack c w via u Hrep Hhistory Hfresh Hu).
    rewrite (discover_old_to_new p roots c w via u Hrep Hparents Hfresh Hu).
    destruct via as [[edge parent]|].
    + destruct Hvia as [es [rest ->]]. symmetry.
      exact (active_ancestor p scope parent es rest c u Hhistory Hinterval Hu).
    + subst stack. split; [|contradiction].
      intro Hnone.
      assert (Hpost : In u (SearchRun.post_rev c)).
      { exact (Permutation_in u (partition _ Hhistory) Hu). }
      apply (numbering_domain _ _ _ (post_numbering _ Hhistory)) in Hpost.
      destruct Hpost as [k Hk].
      change (Map.get positive_encoding u (SearchRun.post_index c) = Some k) in Hk.
      rewrite Hnone in Hk. discriminate.
  - rewrite (discover_interval_old c w via u v Hrep Hfresh Hu Hv).
    rewrite (interval_tree _ _ _ _ Hinterval u v Hu Hv).
    rewrite (discover_ancestry p roots c w via Hrep Hparents Hfresh).
    destruct via as [[edge parent]|]; [cbn; split; [auto|intros [H|[Heq _]];
      [exact H|subst v; contradiction]]|tauto].
Qed.

Local Lemma discover_stack_order {E} stack (c : SearchRun.core E) w via :
  representation c -> history (stack, c) -> stack_order stack c ->
  ~ In w (SearchRun.pre_rev c) ->
    forall es, stack_order ((w, es) :: stack) (SearchRun.discover w via c).
Proof.
  intros Hrep Hhistory Horder Hfresh es u v Hbefore.
  cbn [map fst] in Hbefore. apply before_cons in Hbefore.
  rewrite SearchRun.discover_equation. cbn [SearchRun.pre_index].
  destruct Hbefore as [[-> Hin]|Hbefore].
  - assert (Hv : In v (SearchRun.pre_rev c)).
    { apply (Permutation_in v (Permutation_sym (partition _ Hhistory))).
      apply in_or_app. now left. }
    destruct (proj2 (numbering_domain _ _ _ (pre_numbering _ Hhistory) v) Hv) as [b Hb].
    exists (SearchRun.pre_clock c), b.
    rewrite Map.get_set_same by exact (pre_index_wf _ Hrep).
    rewrite (Map.get_set_other positive_encoding positive_encoding_laws)
      by (first [exact (pre_index_wf _ Hrep)|intro Heq; subst v; contradiction]).
    split; [reflexivity|]. split; [exact Hb|].
    exact (numbering_bound _ _ _ (pre_numbering _ Hhistory) v b Hb).
  - destruct (Horder u v Hbefore) as [a [b [Ha [Hb Hlt]]]].
    assert (Hu : In u (SearchRun.pre_rev c)).
    { apply (numbering_domain _ _ _ (pre_numbering _ Hhistory)). now exists a. }
    assert (Hv : In v (SearchRun.pre_rev c)).
    { apply (numbering_domain _ _ _ (pre_numbering _ Hhistory)). now exists b. }
    exists a, b.
    rewrite !(Map.get_set_other positive_encoding positive_encoding_laws)
      by (first [exact (pre_index_wf _ Hrep)|intro Heq; subst; contradiction]).
    auto.
Qed.

Local Lemma discover_intervals {V E} (p : Prepared.t V E) scope roots stack c w via es :
  representation c -> history (stack, c) -> parent_laws p roots c ->
  interval_laws p scope stack c -> ~ In w (SearchRun.pre_rev c) ->
  (match via with
  | None => stack = []
  | Some (_, parent) => exists pending rest, stack = (parent, pending) :: rest
  end) ->
    interval_laws p scope ((w, es) :: stack) (SearchRun.discover w via c).
Proof.
  intros Hrep Hhistory Hparents Hinterval Hfresh Hvia. constructor.
  - apply discover_stack_order; try assumption. exact (ordered_stack _ _ _ _ Hinterval).
  - change (forall u v, In u (w :: SearchRun.pre_rev c) -> In v (w :: SearchRun.pre_rev c) ->
      (open_interval (SearchRun.discover w via c) u v = true <->
        ancestry (SearchRun.discover w via c) u v)).
    exact (discover_tree_intervals p scope roots stack c w via Hrep Hhistory Hparents
      Hinterval Hfresh Hvia).
  - intros u Hu e v Hedge Hallowed.
    rewrite SearchRun.discover_equation in Hu. cbn [SearchRun.post_rev] in Hu.
    destruct (finished_edges _ _ _ _ Hinterval u Hu e v Hedge Hallowed) as [Hforward|Hback].
    + left. exact Hforward.
    + right. apply (discover_ancestry p roots c w via Hrep Hparents Hfresh). now left.
Qed.

Local Lemma finish_intervals {V E} (p : Prepared.t V E) scope top rest c :
  representation c -> history ((top, []) :: rest, c) ->
  SearchInvariant.closed_work p scope ((top, []) :: rest, c) ->
  interval_laws p scope ((top, []) :: rest) c ->
    interval_laws p scope rest (SearchRun.finish top c).
Proof.
  intros Hrep Hhistory Hclosed Hinterval.
  pose proof (top_post_absent top [] rest c Hhistory) as Hnone.
  constructor.
  - intros u v Hbefore. apply (ordered_stack _ _ _ _ Hinterval).
    cbn [map fst]. apply before_cons. now right.
  - intros u v Hu Hv.
    change (In u (SearchRun.pre_rev c)) in Hu.
    change (In v (SearchRun.pre_rev c)) in Hv.
    rewrite (finish_interval top [] rest c u v Hrep Hhistory
      (ordered_stack _ _ _ _ Hinterval) Hu Hv).
    exact (interval_tree _ _ _ _ Hinterval u v Hu Hv).
  - intros u Hu e v Hedge Hallowed.
    change (In u (top :: SearchRun.post_rev c)) in Hu.
    destruct Hu as [<-|Hu].
    + destruct (SearchInvariant.frame_closed _ _ _ Hclosed top [] (or_introl eq_refl)
        e v Hedge Hallowed) as [Hfalse|Hseen]; [contradiction|].
      change (FinSet.mem positive_encoding v (SearchRun.seen c) = true) in Hseen.
      apply (seen_discovered _ Hrep) in Hseen.
      destruct (Map.get positive_encoding v (SearchRun.post_index c)) as [j|] eqn:Hj.
      * left. exists j, (SearchRun.post_clock c). rewrite SearchRun.finish_equation.
        cbn [SearchRun.post_index].
        rewrite (Map.get_set_other positive_encoding positive_encoding_laws)
          by (first [exact (post_index_wf _ Hrep)|intro Heq; subst v; congruence]).
        rewrite Map.get_set_same by exact (post_index_wf _ Hrep).
        split; [exact Hj|]. split; [reflexivity|].
        exact (numbering_bound _ _ _ (post_numbering _ Hhistory) v j Hj).
      * right. change (ancestry c v top).
        exact (proj2 (active_ancestor p scope top [] rest c v Hhistory Hinterval Hseen) Hj).
    + destruct (finished_edges _ _ _ _ Hinterval u Hu e v Hedge Hallowed)
        as [[j [k [Hj [Hk Hlt]]]]|Hback]; [|right; exact Hback].
      left. exists j, k. rewrite SearchRun.finish_equation. cbn [SearchRun.post_index].
      rewrite !(Map.get_set_other positive_encoding positive_encoding_laws)
        by (first [exact (post_index_wf _ Hrep)|intro Heq; subst; congruence]).
      auto.
Qed.

Local Lemma intervals_stack {V E} (p : Prepared.t V E) scope stack stack' c :
  map fst stack = map fst stack' ->
  interval_laws p scope stack c -> interval_laws p scope stack' c.
Proof.
  intros Heq [Horder Htree Hfinished]. constructor; try assumption.
  intros u v Hbefore. apply Horder. now rewrite Heq.
Qed.

Local Lemma initial_intervals {V E} (p : Prepared.t V E) scope :
  interval_laws p scope [] (@SearchRun.initial E).
Proof.
  constructor.
  - intros u v [left [middle [right Hfalse]]].
    destruct left; discriminate.
  - intros u v Hu. contradiction.
  - intros u Hu. contradiction.
Qed.

(** Every real stack transition preserves open intervals and the finished-edge dichotomy. *)
Theorem transition_intervals {V E} (p : Prepared.t V E) scope roots w :
  representation (snd w) -> history w -> parent_laws p roots (snd w) ->
  SearchInvariant.closed_work p scope w ->
  interval_laws p scope (fst w) (snd w) ->
    interval_laws p scope
      (fst (SearchRun.unwrap (fst (SearchRun.transition p scope w))))
      (snd (SearchRun.unwrap (fst (SearchRun.transition p scope w)))).
Proof.
  destruct w as [stack c]. intros Hrep Hhistory Hparents Hclosed Hinterval.
  rewrite SearchRun.step_equation.
  destruct stack as [|[u [|[e v] pending]] rest]; cbn [fst snd SearchRun.unwrap].
  - exact Hinterval.
  - eapply finish_intervals; eassumption.
  - pose proof (intervals_stack p scope ((u, (e, v) :: pending) :: rest)
      ((u, pending) :: rest) c eq_refl Hinterval) as Htail.
    destruct (Scope.admits scope v); [|exact Htail].
    destruct (Prepared.name_of p v); [|exact Htail].
    destruct (SearchRun.edge_kind c u v) eqn:Hkind; cbn [fst snd SearchRun.unwrap];
      try exact Htail.
    eapply discover_intervals; [exact Hrep| |exact Hparents|exact Htail| |].
    + exact (SearchInvariant.history_stack ((u, (e, v) :: pending) :: rest)
        ((u, pending) :: rest) c eq_refl Hhistory).
    + intro Hin. apply (seen_discovered _ Hrep) in Hin.
      pose proof (proj1 (tree_is_white c u v) Hkind) as Hwhite.
      change (FinSet.mem positive_encoding v (SearchRun.seen c) = true) in Hin.
      rewrite Hwhite in Hin. discriminate.
    + now exists pending, rest.
Qed.

Local Lemma loop_intervals {V E} (p : Prepared.t V E) scope roots n w :
  Prepared.ready p -> representation (snd w) -> history w ->
  sound_work p scope roots w -> SearchInvariant.closed_work p scope w ->
  parent_laws p roots (snd w) -> interval_laws p scope (fst w) (snd w) ->
    let final := fst (SearchRun.reference_loop p scope n w) in
    interval_laws p scope (fst final) (snd final).
Proof.
  intro Hready. revert w. induction n as [|n IH];
    intros w Hrep Hhistory Hsound Hclosed Hparents Hinterval; [exact Hinterval|].
  pose proof (transition_representation p scope w Hrep) as Hrep'.
  pose proof (transition_history p scope w Hrep Hhistory) as Hhistory'.
  pose proof (transition_sound p scope roots w Hready Hrep Hsound) as Hsound'.
  pose proof (SearchInvariant.transition_closed p scope roots w Hready Hrep Hsound Hclosed)
    as Hclosed'.
  pose proof (transition_parents p scope roots w Hready Hrep Hhistory Hsound Hparents)
    as Hparents'.
  pose proof (transition_intervals p scope roots w Hrep Hhistory Hparents Hclosed Hinterval)
    as Hinterval'.
  cbn [SearchRun.reference_loop].
  destruct (SearchRun.transition p scope w) as [[w'|w'] evs];
    cbn [fst snd SearchRun.unwrap] in Hrep', Hhistory', Hsound', Hclosed', Hparents', Hinterval'.
  - specialize (IH w' Hrep' Hhistory' Hsound' Hclosed' Hparents' Hinterval').
    destruct (SearchRun.reference_loop p scope n w') as [final later]. exact IH.
  - exact Hinterval'.
Qed.

Local Lemma root_intervals {V E} (p : Prepared.t V E) scope roots c v :
  Prepared.ready p -> representation c -> history ([], c) ->
  sound_work p scope roots ([], c) -> SearchInvariant.closed_work p scope ([], c) ->
  parent_laws p roots c -> interval_laws p scope [] c -> In v roots ->
    interval_laws p scope [] (fst (SearchRun.reference_root p scope c v)).
Proof.
  intros Hready Hrep Hhistory Hsound Hclosed Hparents Hinterval Hroot.
  unfold SearchRun.reference_root.
  destruct (Scope.admits scope v) eqn:Hallowed; [|exact Hinterval].
  destruct (FinSet.mem positive_encoding v (SearchRun.seen c)) eqn:Hfresh; [exact Hinterval|].
  destruct (Prepared.name_of p v) as [name|] eqn:Hname; [|exact Hinterval].
  assert (Hvalid : Prepared.valid_id p v).
  { apply vertices_spec. exact (named_in_vertices p v name Hready Hname). }
  assert (Hreach : Search.scoped_reachable p scope roots v).
  { exists v, []. split; [exact Hroot|now apply Search.scoped_nil]. }
  assert (Hfreshpre : ~ In v (SearchRun.pre_rev c)).
  { intro Hin. apply (seen_discovered _ Hrep) in Hin. congruence. }
  pose proof (reference_root_drains p scope c v name Hready Hrep Hname Hfresh) as Hdrain.
  pose proof (loop_intervals p scope roots (Pos.to_nat (Prepared.fuel p))
    ([(v, Prepared.succ_edges p v)], SearchRun.discover v None c) Hready
    (discover_representation c v None Hrep Hfresh)
    (discover_history [] c v None (Prepared.succ_edges p v) Hhistory Hfreshpre)
    (sound_push p scope roots [] c v None Hrep Hsound Hreach Hvalid Hallowed)
    (SearchInvariant.root_start_closed p scope c v Hrep Hclosed)
    (discover_parents p roots [] c v None Hrep Hhistory Hparents Hfreshpre Hroot)
    (discover_intervals p scope roots [] c v None (Prepared.succ_edges p v)
      Hrep Hhistory Hparents Hinterval Hfreshpre eq_refl)) as Hloop.
  destruct (SearchRun.reference_loop p scope (Pos.to_nat (Prepared.fuel p))
    ([(v, Prepared.succ_edges p v)], SearchRun.discover v None c)) as [[stack final] evs].
  cbn [fst] in Hdrain. subst stack. exact Hloop.
Qed.

Local Lemma roots_intervals {V E} (p : Prepared.t V E) scope roots todo c :
  Prepared.ready p -> incl todo roots -> representation c -> history ([], c) ->
  sound_work p scope roots ([], c) -> SearchInvariant.closed_work p scope ([], c) ->
  parent_laws p roots c -> interval_laws p scope [] c ->
    interval_laws p scope [] (fst (SearchRun.reference_roots p scope todo c)).
Proof.
  intro Hready. revert c. induction todo as [|v rest IH];
    intros c Htodo Hrep Hhistory Hsound Hclosed Hparents Hinterval; [exact Hinterval|].
  pose proof (root_representation p scope c v Hrep) as Hrep'.
  pose proof (root_history p scope c v Hready Hrep Hhistory) as Hhistory'.
  pose proof (root_sound p scope roots c v Hready Hrep Hsound
    (Htodo v (or_introl eq_refl))) as Hsound'.
  pose proof (SearchInvariant.root_closed p scope roots c v Hready Hrep Hsound Hclosed
    (Htodo v (or_introl eq_refl))) as Hclosed'.
  pose proof (root_parents p scope roots c v Hready Hrep Hhistory Hsound Hparents
    (Htodo v (or_introl eq_refl))) as Hparents'.
  pose proof (root_intervals p scope roots c v Hready Hrep Hhistory Hsound Hclosed Hparents
    Hinterval (Htodo v (or_introl eq_refl))) as Hinterval'.
  cbn [SearchRun.reference_roots].
  destruct (SearchRun.reference_root p scope c v) as [c' here].
  specialize (IH c' ltac:(intros x Hx; apply Htodo; now right)
    Hrep' Hhistory' Hsound' Hclosed' Hparents' Hinterval').
  destruct (SearchRun.reference_roots p scope rest c') as [final later]. exact IH.
Qed.

(** The actual completed forest has exact open ancestry intervals and finished-edge facts. *)
Theorem final_intervals {V E} (p : Prepared.t V E) scope roots :
  Prepared.ready p ->
    interval_laws p scope [] (fst (SearchRun.reference_roots p scope roots SearchRun.initial)).
Proof.
  intro Hready. apply roots_intervals with (roots := roots); try assumption.
  - intros v Hv. exact Hv.
  - apply initial_representation.
  - apply initial_history.
  - constructor.
    + intros v Hv. change (FinSet.mem positive_encoding v FinSet.empty = true) in Hv.
      rewrite FinSet.mem_empty in Hv. discriminate.
    + intros u es Hin. contradiction.
  - constructor; intros u Hu; contradiction.
  - constructor.
    + intros v e u Hget. change (Map.get positive_encoding v Map.empty = Some (e, u)) in Hget.
      rewrite Map.get_empty in Hget. discriminate.
    + intros v Hin. contradiction.
  - apply initial_intervals.
Qed.

Local Lemma core_numbers {E} (c : SearchRun.core E) u :
  history ([], c) -> In u (SearchRun.pre_rev c) ->
    exists a b, Map.get positive_encoding u (SearchRun.pre_index c) = Some a /\
      Map.get positive_encoding u (SearchRun.post_index c) = Some b.
Proof.
  intros Hhistory Hu.
  destruct (proj2 (numbering_domain _ _ _ (pre_numbering _ Hhistory) u) Hu) as [a Ha].
  assert (Hpost : In u (SearchRun.post_rev c)).
  { exact (Permutation_in u (partition _ Hhistory) Hu). }
  destruct (proj2 (numbering_domain _ _ _ (post_numbering _ Hhistory) u) Hpost) as [b Hb].
  now exists a, b.
Qed.

Local Lemma core_ancestor_correct {V E} (p : Prepared.t V E) scope c u v :
  history ([], c) -> interval_laws p scope [] c ->
  In u (SearchRun.pre_rev c) -> In v (SearchRun.pre_rev c) ->
    (Search.interval (SearchRun.result c) u v <-> Search.ancestor (SearchRun.result c) u v).
Proof.
  intros Hhistory Hinterval Hu Hv.
  destruct (core_numbers c u Hhistory Hu) as [a [x [Ha Hx]]].
  destruct (core_numbers c v Hhistory Hv) as [b [y [Hb Hy]]].
  pose proof (interval_tree _ _ _ _ Hinterval u v Hu Hv) as Htree.
  unfold open_interval in Htree. rewrite Ha, Hb, Hx, Hy in Htree.
  rewrite andb_true_iff, !Pos.leb_le in Htree.
  rewrite SearchRun.result_equation. unfold Search.interval, Search.ancestor.
  cbn [Search.pre_num Search.post_num Search.parent_edge]. split.
  - intros [a' [b' [y' [x' [Ha' [Hb' [Hy' [Hx' Hle]]]]]]]].
    rewrite Ha in Ha'. rewrite Hb in Hb'. rewrite Hx in Hx'. rewrite Hy in Hy'.
    inversion Ha'; inversion Hb'; inversion Hx'; inversion Hy'; subst a' b' x' y'.
    now apply Htree.
  - intro Hancestor. apply Htree in Hancestor. exists a, b, y, x. auto.
Qed.

Local Lemma core_paren {E} (c : SearchRun.core E) u v :
  history ([], c) -> In u (SearchRun.pre_rev c) -> In v (SearchRun.pre_rev c) ->
  Search.interval (SearchRun.result c) u v \/ Search.interval (SearchRun.result c) v u \/
  (before (Search.preorder (SearchRun.result c)) u v /\
    before (Search.postorder (SearchRun.result c)) u v) \/
  (before (Search.preorder (SearchRun.result c)) v u /\
    before (Search.postorder (SearchRun.result c)) v u).
Proof.
  intros Hhistory Hu Hv.
  destruct (core_numbers c u Hhistory Hu) as [a [x [Ha Hx]]].
  destruct (core_numbers c v Hhistory Hv) as [b [y [Hb Hy]]].
  rewrite SearchRun.result_equation. cbn [Search.preorder Search.postorder].
  destruct (Pos.compare_spec a b) as [Heq|Hlt|Hgt].
  - subst b. assert (Heq : u = v).
    { exact (numbering_injective _ _ _ u v a (pre_numbering _ Hhistory) Ha Hb). }
    subst v. rewrite Hx in Hy. inversion Hy; subst y.
    left. exists a, a, x, x. cbn [Search.pre_num Search.post_num].
    repeat split; auto using Pos.le_refl.
  - destruct (Pos.leb y x) eqn:Hpost.
    + apply Pos.leb_le in Hpost. left. exists a, b, y, x. cbn [Search.pre_num Search.post_num].
      repeat split; auto using Pos.lt_le_incl.
    + apply Pos.leb_gt in Hpost. right; right; left. split.
      * apply (proj2 (numbering_order _ _ _ (pre_numbering _ Hhistory) u v a b Ha Hb)), Hlt.
      * apply (proj2 (numbering_order _ _ _ (post_numbering _ Hhistory) u v x y Hx Hy)), Hpost.
  - destruct (Pos.leb x y) eqn:Hpost.
    + apply Pos.leb_le in Hpost. right; left. exists b, a, x, y.
      cbn [Search.pre_num Search.post_num].
      repeat split; auto using Pos.lt_le_incl.
    + apply Pos.leb_gt in Hpost. right; right; right. split.
      * apply (proj2 (numbering_order _ _ _ (pre_numbering _ Hhistory) v u b a Hb Ha)), Hgt.
      * apply (proj2 (numbering_order _ _ _ (post_numbering _ Hhistory) v u y x Hy Hx)), Hpost.
Qed.

(** Actual search intervals identify exactly the recorded discovery-tree ancestry. *)
Theorem run_ancestor {V E} (p : Prepared.t V E) scope roots u v :
  Prepared.ready p ->
  let r := SearchRun.dfs p scope roots in
  In u (Search.preorder r) -> In v (Search.preorder r) ->
    (Search.interval r u v <-> Search.ancestor r u v).
Proof.
  intro Hready.
  pose proof (final_intervals p scope roots Hready) as Hinterval.
  pose proof (roots_history p scope roots _ Hready initial_representation initial_history)
    as Hhistory.
  unfold SearchRun.dfs. rewrite SearchRun.run_equation.
  destruct (SearchRun.reference_roots p scope roots SearchRun.initial) as [c evs].
  cbn [fst] in Hinterval, Hhistory |- *. intros Hu Hv.
  rewrite SearchRun.result_equation in Hu, Hv. cbn [Search.preorder] in Hu, Hv.
  apply (proj2 (in_rev _ _)) in Hu, Hv. eapply core_ancestor_correct; eassumption.
Qed.

Local Lemma ancestry_tail {E} (c : SearchRun.core E) u v :
  ancestry c u v -> u = v \/
    exists e parent, Map.get positive_encoding v (SearchRun.parents c) = Some (e, parent) /\
      ancestry c u parent.
Proof.
  intro Hancestor.
  induction Hancestor as [u v [e Hget]|u|u x v Hux IHux Hxv IHxv].
  - right. exists e, u. split; [exact Hget|apply rt_refl].
  - now left.
  - destruct IHxv as [->|[e [parent [Hget Hancestor]]]]; [exact IHux|].
    right. exists e, parent. split; [exact Hget|]. eapply rt_trans; eassumption.
Qed.

Local Lemma ancestry_comparable {V E} (p : Prepared.t V E) roots c target u v :
  parent_laws p roots c -> ancestry c u target -> ancestry c v target ->
    ancestry c u v \/ ancestry c v u.
Proof.
  intro Hparents.
  assert (Hacc : forall target, Acc
    (fun u v => exists e, Map.get positive_encoding v (SearchRun.parents c) = Some (e, u))
    target -> forall u v, ancestry c u target -> ancestry c v target ->
      ancestry c u v \/ ancestry c v u).
  { intros terminal Ha. induction Ha as [terminal Ha IH]. intros x y Hx Hy.
    destruct (ancestry_tail c x terminal Hx) as [->|[e [parent [Hget Hxp]]]];
      [now right|].
    destruct (ancestry_tail c y terminal Hy) as [->|[edge [other [Hother Hyp]]]];
      [now left|].
    rewrite Hget in Hother. inversion Hother; subst edge other.
    apply (IH parent); [now exists e|exact Hxp|exact Hyp]. }
  apply Hacc. now apply parent_relation_finite with (p := p) (roots := roots).
Qed.

Local Lemma ancestor_target {V E} (p : Prepared.t V E) roots c u v :
  parent_laws p roots c -> ancestry c u v -> In u (SearchRun.pre_rev c) ->
    In v (SearchRun.pre_rev c).
Proof.
  intros Hparents Hancestor.
  induction Hancestor as [u v [e Hget]|u|u x v Hux IHux Hxv IHxv]; intro Hu.
  - exact (proj1 (proj2 (selected_parent _ _ _ Hparents v e u Hget))).
  - exact Hu.
  - now apply IHxv, IHux.
Qed.

Local Lemma ancestry_pre_le {V E} (p : Prepared.t V E) scope c u v a b :
  interval_laws p scope [] c -> In u (SearchRun.pre_rev c) -> In v (SearchRun.pre_rev c) ->
  ancestry c u v ->
  Map.get positive_encoding u (SearchRun.pre_index c) = Some a ->
  Map.get positive_encoding v (SearchRun.pre_index c) = Some b -> (a <= b)%positive.
Proof.
  intros Hinterval Hu Hv Hancestor Ha Hb.
  apply (interval_tree _ _ _ _ Hinterval u v Hu Hv) in Hancestor.
  unfold open_interval in Hancestor. rewrite Ha, Hb in Hancestor.
  apply andb_true_iff in Hancestor. apply Pos.leb_le. exact (proj1 Hancestor).
Qed.

Local Lemma ancestry_precedes {V E} (p : Prepared.t V E) scope c u v :
  history ([], c) -> interval_laws p scope [] c ->
  In u (SearchRun.pre_rev c) -> In v (SearchRun.pre_rev c) -> ancestry c u v ->
    u = v \/ before (rev (SearchRun.pre_rev c)) u v.
Proof.
  intros Hhistory Hinterval Hu Hv Hancestor.
  destruct (core_numbers c u Hhistory Hu) as [a [x [Ha Hx]]].
  destruct (core_numbers c v Hhistory Hv) as [b [y [Hb Hy]]].
  pose proof (ancestry_pre_le p scope c u v a b Hinterval Hu Hv Hancestor Ha Hb) as Hle.
  destruct (Pos.eq_dec a b) as [->|Hne].
  - left. exact (numbering_injective _ _ _ u v b (pre_numbering _ Hhistory) Ha Hb).
  - right. apply (proj2 (numbering_order _ _ _ (pre_numbering _ Hhistory) u v a b Ha Hb)).
    apply Pos2Nat.inj_lt. apply Pos2Nat.inj_le in Hle.
    assert (Hnatne : Pos.to_nat a <> Pos.to_nat b).
    { intro Heq. apply Hne. now apply Pos2Nat.inj. }
    lia.
Qed.

Local Lemma core_admitted {V E} (p : Prepared.t V E) scope roots c v :
  representation c -> sound_work p scope roots ([], c) -> In v (SearchRun.pre_rev c) ->
    Prepared.valid_id p v /\ Scope.admits scope v = true.
Proof.
  intros Hrep Hsound Hv. apply (seen_discovered _ Hrep) in Hv.
  apply (seen_reachable _ _ _ _ Hsound) in Hv.
  destruct Hv as [root [es [_ Hpath]]]. induction Hpath; auto.
Qed.

Local Lemma scoped_app {V E} (p : Prepared.t V E) scope u xs v ys z :
  Search.scoped_path p scope u xs v -> Search.scoped_path p scope v ys z ->
    Search.scoped_path p scope u (xs ++ ys) z.
Proof.
  intros Hpath Htail.
  induction Hpath; cbn; [exact Htail|]. eapply Search.scoped_cons; eauto.
Qed.

Local Lemma arc_source_unique {V E} (p : Prepared.t V E) u e v a b :
  Prepared.arc p u e v -> Prepared.arc p a e b -> a = u.
Proof.
  intros [x [y [_ [Hx [_ [Hsource _]]]]]] [z [w [_ [Hz [_ [Hsource' _]]]]]].
  assert (Heq : z = x) by congruence. subst z. congruence.
Qed.

Local Lemma ancestry_path {V E} (p : Prepared.t V E) scope roots c u v :
  representation c -> sound_work p scope roots ([], c) -> parent_laws p roots c ->
  ancestry c u v -> In u (SearchRun.pre_rev c) ->
    exists es, Search.scoped_path p scope u es v /\
      forall a e b, In e es -> Prepared.arc p a e b -> ancestry c u a.
Proof.
  intros Hrep Hsound Hparents Hancestor.
  induction Hancestor as [u v [e Hget]|u|u x v Hux IHux Hxv IHxv]; intro Hu.
  - destruct (selected_parent _ _ _ Hparents v e u Hget) as [Harc [Hv _]].
    destruct (core_admitted p scope roots c u Hrep Hsound Hu) as [Hvalid Hallowed].
    destruct (core_admitted p scope roots c v Hrep Hsound Hv) as [Hvalid' Hallowed'].
    exists [e]. split.
    + eapply Search.scoped_cons; [exact Hvalid|exact Hallowed|exact Harc|].
      now apply Search.scoped_nil.
    + intros a edge b [<-|Hfalse] Hedge; [|contradiction].
      pose proof (arc_source_unique p u e v a b Harc Hedge) as ->. apply rt_refl.
  - destruct (core_admitted p scope roots c u Hrep Hsound Hu) as [Hvalid Hallowed].
    exists []. split; [now apply Search.scoped_nil|intros a e b Hin; contradiction].
  - destruct (IHux Hu) as [xs [Hpath Hsources]].
    destruct (IHxv (ancestor_target p roots c u x Hparents Hux Hu)) as [ys [Htail Hsources']].
    exists (xs ++ ys). split; [eapply scoped_app; eassumption|].
    intros a e b Hin Harc. apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
    + now apply (Hsources a e b).
    + eapply rt_trans; [exact Hux|now apply (Hsources' a e b)].
Qed.

Local Lemma white_edge_closed {V E} (p : Prepared.t V E) scope roots c u a e b :
  Prepared.ready p -> representation c -> history ([], c) ->
  sound_work p scope roots ([], c) -> parent_laws p roots c -> interval_laws p scope [] c ->
  In u (SearchRun.pre_rev c) -> ancestry c u a -> Prepared.arc p a e b ->
  (b = u \/ before (rev (SearchRun.pre_rev c)) u b) -> ancestry c u b.
Proof.
  intros Hready Hrep Hhistory Hsound Hparents Hinterval Hu Hancestor Harc [->|Hbefore];
    [apply rt_refl|].
  assert (Ha : In a (SearchRun.pre_rev c)) by
    (eapply ancestor_target; [exact Hparents|exact Hancestor|exact Hu]).
  assert (Hb : In b (SearchRun.pre_rev c)).
  { apply before_indices in Hbefore. destruct Hbefore as [i [j [_ [_ Hj]]]].
    apply (proj2 (in_rev _ _)). now apply nth_error_In in Hj. }
  destruct (core_numbers c u Hhistory Hu) as [x [finishu [Hx Hfinishu]]].
  destruct (core_numbers c a Hhistory Ha) as [y [finisha [Hy Hfinisha]]].
  destruct (core_numbers c b Hhistory Hb) as [z [finishb [Hz Hfinishb]]].
  pose proof (proj1 (numbering_order _ _ _ (pre_numbering _ Hhistory) u b x z Hx Hz)
    Hbefore) as Hpre.
  destruct (core_admitted p scope roots c b Hrep Hsound Hb) as [_ Hallowed].
  assert (Hposta : In a (SearchRun.post_rev c)) by
    exact (Permutation_in a (partition _ Hhistory) Ha).
  destruct (finished_edges _ _ _ _ Hinterval a Hposta e b
    (arc_successor p a e b Hready Harc) Hallowed) as [[j [k [Hj [Hk Hlt]]]]|Hback].
  - rewrite Hfinishb in Hj. rewrite Hfinisha in Hk. inversion Hj; inversion Hk; subst j k.
    apply (proj1 (interval_tree _ _ _ _ Hinterval u b Hu Hb)).
    apply (proj2 (interval_tree _ _ _ _ Hinterval u a Hu Ha)) in Hancestor.
    unfold open_interval in Hancestor |- *.
    rewrite Hx, Hy, Hfinishu, Hfinisha in Hancestor.
    rewrite Hx, Hz, Hfinishu, Hfinishb.
    apply andb_true_iff in Hancestor. destruct Hancestor as [_ Hpost].
    apply Pos.leb_le in Hpost. apply andb_true_iff. split; apply Pos.leb_le.
    + now apply Pos.lt_le_incl.
    + eapply Pos.le_trans; [exact (Pos.lt_le_incl _ _ Hlt)|exact Hpost].
  - destruct (ancestry_comparable p roots c a u b Hparents Hancestor Hback)
      as [Hforward|Hreverse]; [exact Hforward|].
    pose proof (ancestry_pre_le p scope c b u z x Hinterval Hb Hu Hreverse Hz Hx) as Hle.
    exfalso. apply (Pos.lt_irrefl x). eapply Pos.lt_le_trans; eassumption.
Qed.

Local Lemma path_start_white {V E} (p : Prepared.t V E) scope
    (c : SearchRun.core E) u a es b :
  Search.scoped_path p scope a es b ->
  (b = u \/ before (rev (SearchRun.pre_rev c)) u b) ->
  (forall x edge y, In edge es -> Prepared.arc p x edge y ->
    x = u \/ before (rev (SearchRun.pre_rev c)) u x) ->
    a = u \/ before (rev (SearchRun.pre_rev c)) u a.
Proof.
  intros Hpath Htarget Hsources. destruct Hpath.
  - exact Htarget.
  - eapply Hsources; [now left|eassumption].
Qed.

Local Lemma white_path_closed {V E} (p : Prepared.t V E) scope roots c u a es b :
  Prepared.ready p -> representation c -> history ([], c) ->
  sound_work p scope roots ([], c) -> parent_laws p roots c -> interval_laws p scope [] c ->
  In u (SearchRun.pre_rev c) -> Search.scoped_path p scope a es b ->
  ancestry c u a -> (b = u \/ before (rev (SearchRun.pre_rev c)) u b) ->
  (forall x edge y, In edge es -> Prepared.arc p x edge y ->
    x = u \/ before (rev (SearchRun.pre_rev c)) u x) -> ancestry c u b.
Proof.
  intros Hready Hrep Hhistory Hsound Hparents Hinterval Hu Hpath.
  induction Hpath as [v Hvalid Hallowed|a edge v es b Ha Hallowed Harc Hpath IH];
    intros Hancestor Htarget Hsources; [exact Hancestor|].
  assert (Htail : forall x e y, In e es -> Prepared.arc p x e y ->
    x = u \/ before (rev (SearchRun.pre_rev c)) u x).
  { intros x e y Hin Hedge. apply (Hsources x e y); [now right|exact Hedge]. }
  pose proof (path_start_white p scope c u v es b Hpath Htarget Htail) as Hwhite.
  apply IH; [|exact Htarget|exact Htail].
  eapply white_edge_closed; eassumption.
Qed.

Local Lemma core_white_path {V E} (p : Prepared.t V E) scope roots c u v :
  Prepared.ready p -> representation c -> history ([], c) ->
  sound_work p scope roots ([], c) -> parent_laws p roots c -> interval_laws p scope [] c ->
  In u (SearchRun.pre_rev c) -> In v (SearchRun.pre_rev c) ->
  (Search.ancestor (SearchRun.result c) u v <->
    exists es, Search.scoped_path p scope u es v /\
      (v = u \/ before (Search.preorder (SearchRun.result c)) u v) /\
      forall a e b, In e es -> Prepared.arc p a e b ->
        a = u \/ before (Search.preorder (SearchRun.result c)) u a).
Proof.
  intros Hready Hrep Hhistory Hsound Hparents Hinterval Hu Hv.
  rewrite SearchRun.result_equation. cbn [Search.preorder].
  unfold Search.ancestor. cbn [Search.parent_edge]. fold (ancestry c u v).
  split.
  - intro Hancestor.
    destruct (ancestry_path p scope roots c u v Hrep Hsound Hparents Hancestor Hu)
      as [es [Hpath Hsources]].
    exists es. split; [exact Hpath|]. split.
    + destruct (ancestry_precedes p scope c u v Hhistory Hinterval Hu Hv Hancestor)
        as [Heq|Hbefore]; [left; symmetry; exact Heq|now right].
    + intros a e b Hin Harc. pose proof (Hsources a e b Hin Harc) as Hancestor'.
      pose proof (ancestor_target p roots c u a Hparents Hancestor' Hu) as Ha.
      destruct (ancestry_precedes p scope c u a Hhistory Hinterval Hu Ha Hancestor')
        as [Heq|Hbefore]; [left; symmetry; exact Heq|now right].
  - intros [es [Hpath [Htarget Hsources]]].
    eapply white_path_closed; try eassumption. apply rt_refl.
Qed.

(** Search intervals nest or are disjoint in the two actual traversal orders. *)
Theorem run_paren {V E} (p : Prepared.t V E) scope roots u v :
  Prepared.ready p ->
  let r := SearchRun.dfs p scope roots in
  In u (Search.preorder r) -> In v (Search.preorder r) ->
  Search.interval r u v \/ Search.interval r v u \/
  (before (Search.preorder r) u v /\ before (Search.postorder r) u v) \/
  (before (Search.preorder r) v u /\ before (Search.postorder r) v u).
Proof.
  intro Hready.
  pose proof (roots_history p scope roots _ Hready initial_representation initial_history)
    as Hhistory.
  unfold SearchRun.dfs. rewrite SearchRun.run_equation.
  destruct (SearchRun.reference_roots p scope roots SearchRun.initial) as [c evs].
  cbn [fst] in Hhistory |- *. intros Hu Hv.
  rewrite SearchRun.result_equation in Hu, Hv. cbn [Search.preorder] in Hu, Hv.
  apply (proj2 (in_rev _ _)) in Hu, Hv. now apply core_paren.
Qed.

(** Tree ancestry is exactly scoped reachability through vertices white at the ancestor's entry. *)
Theorem run_white_path {V E} (p : Prepared.t V E) scope roots u v :
  Prepared.ready p ->
  let r := SearchRun.dfs p scope roots in
  In u (Search.preorder r) -> In v (Search.preorder r) ->
  (Search.ancestor r u v <->
    exists es, Search.scoped_path p scope u es v /\
      (v = u \/ before (Search.preorder r) u v) /\
      forall a e b, In e es -> Prepared.arc p a e b ->
        a = u \/ before (Search.preorder r) u a).
Proof.
  intro Hready.
  pose proof (final_intervals p scope roots Hready) as Hinterval.
  pose proof (final_parents p scope roots Hready) as Hparents.
  pose proof (roots_history p scope roots _ Hready initial_representation initial_history)
    as Hhistory.
  pose proof (roots_representation p scope roots _ (@initial_representation E)) as Hrep.
  assert (Hinitial : sound_work p scope roots ([], @SearchRun.initial E)).
  { constructor.
    - intros x Hx. change (FinSet.mem positive_encoding x FinSet.empty = true) in Hx.
      rewrite FinSet.mem_empty in Hx. discriminate.
    - intros x es Hin. contradiction. }
  pose proof (roots_sound p scope roots roots _ Hready ltac:(intros x Hx; exact Hx)
    initial_representation Hinitial) as Hsound.
  unfold SearchRun.dfs. rewrite SearchRun.run_equation.
  destruct (SearchRun.reference_roots p scope roots SearchRun.initial) as [c evs].
  cbn [fst] in Hinterval, Hparents, Hhistory, Hrep, Hsound |- *. intros Hu Hv.
  rewrite SearchRun.result_equation in Hu, Hv. cbn [Search.preorder] in Hu, Hv.
  apply (proj2 (in_rev _ _)) in Hu, Hv. eapply core_white_path; eassumption.
Qed.

(** The no-op search satisfies every existing scoped exactness field from readiness alone. *)
Theorem dfs_exact {V E} (p : Prepared.t V E) scope roots :
  Prepared.ready p -> Search.exact p scope roots (SearchRun.dfs p scope roots).
Proof.
  intro Hready.
  destruct (run_representation p scope roots) as [Hparentswf [Hprewf [Hpostwf
    [Hseenwf [Hnodup Hseen]]]]].
  destruct (run_numbering p scope roots Hready) as [Hperm [Hpre Hpost]].
  destruct (run_parents p scope roots Hready) as [Hparents [Hroots Hfinite]].
  constructor.
  - exact Hnodup.
  - intro v. now apply run_reachable.
  - exact Hseen.
  - auto.
  - exact Hperm.
  - exact Hpre.
  - exact Hpost.
  - exact Hparents.
  - exact Hroots.
  - exact Hfinite.
  - intros u v Hu Hv. exact (run_paren p scope roots u v Hready Hu Hv).
  - intros u v Hu Hv. exact (run_ancestor p scope roots u v Hready Hu Hv).
  - intros u v Hu Hv. exact (run_white_path p scope roots u v Hready Hu Hv).
Qed.

(** Every visitor run has the same fully exact scoped forest, without any visitor-law premise. *)
Theorem run_exact {V E S} (p : Prepared.t V E) (vis : Visitor.t E S) scope roots s0 :
  Prepared.ready p ->
    Search.exact p scope roots (fst (Cost.value (SearchRun.run_c p vis scope roots s0))).
Proof.
  intro Hready. rewrite SearchRun.run_result. now apply dfs_exact.
Qed.

(** Events are a complete ordered DFS trace with the same selected labels and final result. *)
Theorem events_wf {V E} (p : Prepared.t V E) scope roots :
  Prepared.ready p ->
    exists final, SearchRun.dfs p scope roots = SearchRun.result final /\
      SearchRun.trace_roots p scope roots SearchRun.initial
        (SearchRun.events p scope roots) final.
Proof.
  intro Hready.
  pose proof (roots_trace p scope roots _ Hready (@initial_representation E)) as Htrace.
  unfold SearchRun.dfs, SearchRun.events. rewrite SearchRun.run_equation.
  destruct (SearchRun.reference_roots p scope roots SearchRun.initial) as [final evs].
  exists final. split; [reflexivity|exact Htrace].
Qed.

End SearchExact.
