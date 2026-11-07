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

End SearchExact.
