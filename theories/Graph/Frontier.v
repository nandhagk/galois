(** * Dominance frontiers

    Frontier columns share a visited table across the predecessors of each target.
    For example, parallel edges do not duplicate a target in a frontier row.
    Builds on: prepared graphs, dominator trees and binary-fuel loops. *)

From Stdlib Require Import PArith NArith List Bool Arith Lia.
From Stdlib.Sorting Require Import Permutation.
From Argent Require Import Time Tactics Std BigO Loop.
From Galois.Base Require Import Trie Loop.
From Galois.Graph Require Import Data Spec DigraphSig DomSig DomProducer DomOrder FrontierSig.
Import List.ListNotations.

(** A prepared predecessor occurrence is exactly an edge from a listed source. *)
Lemma frontier_preds_member : forall g y x,
  prepared_ok g ->
  (In x (preds g y) <-> In x (nodes g) /\ edge (base g) x y).
Proof.
  intros g y x [_ [_ Hpred]].
  split.
  - intro Hin. apply (Permutation_in _ (Hpred y)) in Hin.
    apply in_flat_map in Hin. destruct Hin as [u [Hu Hin]].
    apply in_map_iff in Hin. destruct Hin as [v [Heq Hv]]. subst u.
    apply filter_In in Hv. destruct Hv as [Hv Heq].
    apply Pos.eqb_eq in Heq. subst v. split; assumption.
  - intros [Hx Hedge]. eapply Permutation_in; [apply Permutation_sym, Hpred|].
    apply in_flat_map. exists x. split; [exact Hx|].
    apply in_map_iff. exists y. split; [reflexivity|].
    apply filter_In. split; [exact Hedge|apply Pos.eqb_refl].
Qed.

(** Private semantic facts for the enabled parent runners. *)
Lemma frontier_path_listed : forall g a vs b,
  wf_graph g -> In a (verts g) -> path g a vs b -> In b (verts g).
Proof.
  intros g a vs b [Hunique Hclosed] Ha Hpath. revert Ha.
  induction Hpath as [v|u v vs w Hedge Hpath IH]; intro Ha.
  - exact Ha.
  - apply IH. eapply Hclosed; eassumption.
Qed.

Lemma frontier_reach_listed : forall g r v,
  wf_graph (base g) -> In r (verts (base g)) -> reach (base g) [r] v ->
  In v (nodes g).
Proof.
  intros g r v Hgraph Hr [a [vs [Ha Hpath]]].
  destruct Ha as [<-|[]].
  replace (nodes g) with (verts (base g)) by (destruct g as [[]]; reflexivity).
  eapply frontier_path_listed; eassumption.
Qed.

Lemma frontier_reach_edge : forall g r p y,
  reach g [r] p -> edge g p y -> reach g [r] y.
Proof.
  intros g r p y [a [vs [Ha Hpath]]] Hedge.
  exists a, (vs ++ [y]). split; [exact Ha|].
  eapply dom_cert_path_snoc; eassumption.
Qed.

Lemma frontier_anc_reachable : forall g r m x v,
  dom_exact g r m -> tree_anc m x v -> reach (base g) [r] v ->
  reach (base g) [r] x.
Proof.
  intros g r m x v Hexact Hanc. induction Hanc as [|p v Hparent Hanc IH]; intro Hv.
  - exact Hv.
  - apply IH. exact (proj1 (proj1 Hexact v p Hparent)).
Qed.

Definition df_enabled (t : domtree) (y x : positive) : Prop :=
  (exists a, trie_get x (pre t) = Some a) /\
  forall b, trie_get y (idom t) = Some b -> x <> b.

Inductive df_route (g : prepared) (t : domtree) (y : positive) : positive -> Prop :=
  | df_route_seed : forall x, In x (preds g y) -> df_enabled t y x -> df_route g t y x
  | df_route_parent : forall x q,
      df_route g t y x -> trie_get x (idom t) = Some q ->
      df_enabled t y q -> df_route g t y q.

Lemma df_route_witness : forall g t r y x,
  prepared_ok g -> domtree_exact g r t -> df_route g t y x ->
  exists p, In p (preds g y) /\ reach (base g) [r] p /\
    tree_anc (idom t) x p /\
    forall b, trie_get y (idom t) = Some b -> ~ tree_anc (idom t) x b.
Proof.
  intros g t r y x Hprepared Htree Hroute.
  destruct Htree as [Hr [Hexact [Hwidth [Hkids [Hsort [Hpre Hrest]]]]]].
  induction Hroute as [x Hpred [Hpresent Hboundary]|v q Hroute IH Hparent [Hpresent Hboundary]].
  - assert (Hp : reach (base g) [r] x) by now apply (proj1 (Hpre x)).
    exists x. split; [exact Hpred|]. split; [exact Hp|]. split; [constructor|].
    intros b Hget Hxb.
    pose proof (dom_exact_edge_parent g r (idom t) x y b Hexact Hp
      (proj2 (proj1 (frontier_preds_member g y x Hprepared) Hpred)) Hget) as Hbx.
    apply (Hboundary b Hget).
    eapply dom_anc_wf_antisym; [exact (proj2 (proj2 Hexact))|exact Hxb|exact Hbx].
  - destruct IH as [p [Hpred [Hp [Hvp Hboundaryv]]]].
    exists p. split; [exact Hpred|]. split; [exact Hp|]. split.
    + eapply dom_cert_anc_trans; [|exact Hvp].
      eapply tree_anc_step; [exact Hparent|constructor].
    + intros b Hget Hqb.
      pose proof (dom_exact_edge_parent g r (idom t) p y b Hexact Hp
        (proj2 (proj1 (frontier_preds_member g y p Hprepared) Hpred)) Hget) as Hbp.
      destruct (dom_anc_chain_comparable (idom t) b v p Hbp Hvp) as [Hbv|Hvb].
      * assert (Hne : b <> v).
        { intro Heq. subst b. apply (Hboundaryv v Hget). constructor. }
        pose proof (dom_cert_anc_parent (idom t) b v q Hparent Hbv Hne) as Hbq.
        apply (Hboundary b Hget).
        eapply dom_anc_wf_antisym; [exact (proj2 (proj2 Hexact))|exact Hqb|exact Hbq].
      * exact (Hboundaryv b Hget Hvb).
Qed.

Lemma df_route_climb : forall g t r y x v,
  domtree_exact g r t -> tree_anc (idom t) x v -> df_route g t y v ->
  (forall b, trie_get y (idom t) = Some b -> ~ tree_anc (idom t) x b) ->
  df_route g t y x.
Proof.
  intros g t r y x v Htree Hanc.
  destruct Htree as [Hr [Hexact [Hwidth [Hkids [Hsort [Hpre Hrest]]]]]].
  induction Hanc as [|p v Hparent Hanc IH]; intros Hroute Hboundary.
  - exact Hroute.
  - apply IH; [|exact Hboundary].
    eapply df_route_parent; [exact Hroute|exact Hparent|].
    split.
    + apply (proj2 (Hpre p)). exact (proj1 (proj1 Hexact v p Hparent)).
    + intros b Hget Heq. subst b. exact (Hboundary p Hget Hanc).
Qed.

Lemma df_route_spec : forall g t r x y,
  wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
  (df_route g t y x <-> in_frontier (base g) r x y).
Proof.
  intros g t r x y Hgraph Hprepared Htree.
  pose proof Htree as [Hr [Hexact [Hwidth [Hkids [Hsort [Hpre Hrest]]]]]].
  split.
  - intro Hroute.
    destruct (df_route_witness g t r y x Hprepared Htree Hroute)
      as [p [Hpred [Hp [Hxp Hboundary]]]].
    pose proof (proj2 (proj1 (frontier_preds_member g y p Hprepared) Hpred)) as Hedge.
    split.
    + exists p. split; [exact Hp|]. split; [exact Hedge|].
      eapply dom_exact_anc_dominates; eassumption.
    + intro Hstrict. destruct (trie_get y (idom t)) as [b|] eqn:Hget.
      * apply (Hboundary b eq_refl).
        now apply (proj1 (dom_exact_parent_strict g r (idom t) x y b Hexact Hget)).
      * apply (proj1 (proj1 (proj2 Hexact) y
          (frontier_reach_edge (base g) r p y Hp Hedge)) Hget).
        exists x. exact Hstrict.
  - intros [[p [Hp [Hedge Hdom]]] Hnotstrict].
    pose proof (dom_exact_dominates_anc g r (idom t) x p Hexact Hp Hdom) as Hxp.
    assert (Hboundary : forall b, trie_get y (idom t) = Some b ->
      ~ tree_anc (idom t) x b).
    { intros b Hget Hxb. apply Hnotstrict.
      now apply (proj2 (dom_exact_parent_strict g r (idom t) x y b Hexact Hget)). }
    eapply df_route_climb; [exact Htree|exact Hxp| |exact Hboundary].
    apply df_route_seed.
    + apply (proj2 (frontier_preds_member g y p Hprepared)). split; [|exact Hedge].
      eapply frontier_reach_listed; eassumption.
    + split; [now apply (proj2 (Hpre p))|].
      intros b Hget Heq. subst b. exact (Hboundary p Hget Hxp).
Qed.

Definition df_step (g : prepared) (t : domtree) (y : positive) (st : df_state) :
    df_state + list positive :=
  match st with
  | DfState [] _ answer => inr (rev_append answer [])
  | DfState (x :: rest) seen answer =>
    match trie_get x (pre t), trie_get x seen with
    | Some _, None =>
      match trie_get y (idom t) with
      | Some parent =>
        if Pos.eqb x parent then inl (DfState rest seen answer)
        else match trie_get x (idom t) with
          | Some next => inl (DfState (next :: rest) (PTrieCode.set x tt seen) (x :: answer))
          | None => inl (DfState rest (PTrieCode.set x tt seen) (x :: answer))
          end
      | None =>
        match trie_get x (idom t) with
        | Some next => inl (DfState (next :: rest) (PTrieCode.set x tt seen) (x :: answer))
        | None => inl (DfState rest (PTrieCode.set x tt seen) (x :: answer))
        end
      end
    | _, _ => inl (DfState rest seen answer)
    end
  end.
TimeFun df_step.

(** A runner pushes its immediate parent when one is present. *)
Definition df_follow (t : domtree) (x : positive) (rest : list positive) : list positive :=
  match trie_get x (idom t) with Some q => q :: rest | None => rest end.
TimeFun df_follow.

Lemma df_follow_member : forall t x rest u,
  In u (df_follow t x rest) <-> In u rest \/ trie_get x (idom t) = Some u.
Proof.
  intros t x rest u. unfold df_follow.
  destruct (trie_get x (idom t)) as [q|] eqn:Hget; cbn [In]; intuition congruence.
Qed.

Lemma df_follow_length : forall t x rest, length (df_follow t x rest) <= S (length rest).
Proof.
  intros t x rest. unfold df_follow. destruct (trie_get x (idom t)); cbn [length]; lia.
Qed.

Definition df_ready (st : df_state) (x : positive) : Prop :=
  In x (df_column_answer st) \/ In x (df_pending st).

(** Every enabled seed or parent of an emitted vertex is already recorded or pending. *)
Record df_valid (g : prepared) (t : domtree) (y : positive) (st : df_state) : Prop := {
  df_valid_unique : NoDup (df_column_answer st);
  df_valid_marks : forall x, trie_get x (df_seen st) = Some tt <-> In x (df_column_answer st);
  df_valid_answer_nodes : incl (df_column_answer st) (nodes g);
  df_valid_pending_nodes : incl (df_pending st) (nodes g);
  df_valid_answer_routes : forall x, In x (df_column_answer st) -> df_route g t y x;
  df_valid_pending_routes : forall x, In x (df_pending st) ->
    df_enabled t y x -> df_route g t y x;
  df_valid_seeds_covered : forall x, In x (preds g y) -> df_enabled t y x -> df_ready st x;
  df_valid_parents_covered : forall x q, In x (df_column_answer st) ->
    trie_get x (idom t) = Some q -> df_enabled t y q -> df_ready st q
}.

Lemma df_valid_initial : forall g t y,
  prepared_ok g -> df_valid g t y (DfState (preds g y) Empty []).
Proof.
  intros g t y Hprepared. constructor; cbn [df_column_answer df_pending df_seen].
  - constructor.
  - intro x. rewrite PTrie.get_empty. cbn [In]. split; [discriminate|contradiction].
  - apply incl_nil_l.
  - intros x Hx. exact (proj1 (proj1 (frontier_preds_member g y x Hprepared) Hx)).
  - intros x Hx. contradiction.
  - intros x Hx Henabled. now apply df_route_seed.
  - intros x Hx Henabled. right. exact Hx.
  - intros x q Hx. contradiction.
Qed.

Lemma df_valid_retire : forall g t y x rest seen answer,
  df_valid g t y (DfState (x :: rest) seen answer) ->
  (df_enabled t y x -> In x answer) ->
  df_valid g t y (DfState rest seen answer).
Proof.
  intros g t y x rest seen answer Hvalid Hretire.
  destruct Hvalid as [Hunique Hmarks Hansnodes Hpendingnodes Hansroute Hpendingroute Hseeds Hparents].
  cbn [df_column_answer df_pending df_seen] in *.
  assert (Hready : forall u, df_enabled t y u ->
    df_ready (DfState (x :: rest) seen answer) u -> df_ready (DfState rest seen answer) u).
  { intros u Hu [Hanswer|[Heq|Hrest]].
    - left. exact Hanswer.
    - subst u. left. now apply Hretire.
    - right. exact Hrest. }
  constructor; cbn [df_column_answer df_pending df_seen]; try assumption.
  - intros u Hu. apply Hpendingnodes. now right.
  - intros u Hu Henabled. apply Hpendingroute; [now right|exact Henabled].
  - intros u Hu Henabled. apply Hready; [exact Henabled|now apply Hseeds].
  - intros u q Hu Hparent Henabled. apply Hready; [exact Henabled|].
    eapply Hparents; eassumption.
Qed.

Lemma df_valid_emit : forall g t r y x rest seen answer,
  wf_graph (base g) -> domtree_exact g r t ->
  df_valid g t y (DfState (x :: rest) seen answer) ->
  df_enabled t y x -> trie_get x seen = None ->
  df_valid g t y
    (DfState (df_follow t x rest) (PTrieCode.set x tt seen) (x :: answer)).
Proof.
  intros g t r y x rest seen answer Hgraph Htree Hvalid Henabled Hfresh.
  destruct Htree as [Hr [Hexact Htree]].
  destruct Hvalid as [Hunique Hmarks Hansnodes Hpendingnodes Hansroute Hpendingroute Hseeds Hparents].
  cbn [df_column_answer df_pending df_seen] in *.
  assert (Hxroute : df_route g t y x) by (apply Hpendingroute; [now left|exact Henabled]).
  assert (Hready : forall u,
    df_ready (DfState (x :: rest) seen answer) u ->
    df_ready (DfState (df_follow t x rest) (PTrieCode.set x tt seen) (x :: answer)) u).
  { intros u [Hanswer|[Heq|Hrest]].
    - left. now right.
    - left. now left.
    - right. apply df_follow_member. now left. }
  constructor; cbn [df_column_answer df_pending df_seen].
  - constructor; [|exact Hunique]. intro Hin. apply (proj2 (Hmarks x)) in Hin. congruence.
  - intro u. destruct (Pos.eq_dec u x) as [->|Hne].
    + rewrite PTrie.get_set_same. cbn [In]. tauto.
    + rewrite PTrie.get_set_other by exact Hne. rewrite Hmarks. cbn [In]. intuition congruence.
  - intros u [<-|Hu]; [apply Hpendingnodes; now left|now apply Hansnodes].
  - intros u Hu. apply df_follow_member in Hu. destruct Hu as [Hu|Hparent].
    + apply Hpendingnodes. now right.
    + apply (frontier_reach_listed g r u Hgraph Hr).
      exact (proj1 (proj1 Hexact x u Hparent)).
  - intros u [<-|Hu]; [exact Hxroute|now apply Hansroute].
  - intros u Hu Hallowed. apply df_follow_member in Hu. destruct Hu as [Hu|Hparent].
    + apply Hpendingroute; [now right|exact Hallowed].
    + eapply df_route_parent; eassumption.
  - intros u Hu Hallowed. apply Hready. now apply Hseeds.
  - intros u q [<-|Hu] Hparent Hallowed.
    + right. apply df_follow_member. now right.
    + apply Hready. eapply Hparents; eassumption.
Qed.

(** The raw callback either retires a disabled/seen runner or records one enabled vertex. *)
Lemma df_step_behavior : forall g t y x rest seen answer next,
  df_step g t y (DfState (x :: rest) seen answer) = inl next ->
  (next = DfState rest seen answer /\
    (trie_get x seen = Some tt \/ ~ df_enabled t y x)) \/
  (next = DfState (df_follow t x rest) (PTrieCode.set x tt seen) (x :: answer) /\
    trie_get x seen = None /\ df_enabled t y x).
Proof.
  intros g t y x rest seen answer next Hstep. cbn [df_step] in Hstep.
  destruct (trie_get x (pre t)) as [a|] eqn:Hpre;
    destruct (trie_get x seen) as [[]|] eqn:Hseen.
  - injection Hstep as <-. left. split; [reflexivity|now left].
  - destruct (trie_get y (idom t)) as [b|] eqn:Hparent.
    + destruct (Pos.eqb x b) eqn:Heq.
      * injection Hstep as <-. left. split; [reflexivity|]. right.
        intros [_ Hboundary]. apply (Hboundary b Hparent). now apply Pos.eqb_eq.
      * right. split.
        -- unfold df_follow. destruct (trie_get x (idom t)); now injection Hstep as <-.
        -- split; [reflexivity|]. split; [now exists a|].
           intros q Hq. rewrite Hparent in Hq. injection Hq as <-. now apply Pos.eqb_neq.
    + right. split.
      * unfold df_follow. destruct (trie_get x (idom t)); now injection Hstep as <-.
      * split; [reflexivity|]. split; [now exists a|].
        intros q Hq. rewrite Hparent in Hq. discriminate.
  - injection Hstep as <-. left. split; [reflexivity|now left].
  - injection Hstep as <-. left. split; [reflexivity|]. right.
    intros [[a Ha] _]. congruence.
Qed.

Lemma df_valid_step : forall g t r y st next,
  wf_graph (base g) -> domtree_exact g r t -> df_valid g t y st ->
  df_step g t y st = inl next -> df_valid g t y next.
Proof.
  intros g t r y [pending seen answer] next Hgraph Htree Hvalid Hstep.
  destruct pending as [|x rest]; [discriminate Hstep|].
  destruct (df_step_behavior g t y x rest seen answer next Hstep)
    as [[-> [Hseen|Hdisabled]]|[-> [Hfresh Henabled]]].
  - apply df_valid_retire with (x := x); [exact Hvalid|]. intro Henabled.
    now apply (proj1 (df_valid_marks _ _ _ _ Hvalid x)).
  - apply df_valid_retire with (x := x); [exact Hvalid|]. intro Henabled. contradiction.
  - eapply df_valid_emit; eassumption.
Qed.

(** At exhaustion of the worklist, its local coverage conditions close every enabled route. *)
Lemma df_valid_closed : forall g t y seen answer,
  df_valid g t y (DfState [] seen answer) ->
  forall x, In x answer <-> df_route g t y x.
Proof.
  intros g t y seen answer Hvalid x. split.
  - exact (df_valid_answer_routes _ _ _ _ Hvalid x).
  - intro Hroute. induction Hroute as [x Hpred Henabled|x q Hroute IH Hparent Henabled].
    + destruct (df_valid_seeds_covered _ _ _ _ Hvalid x Hpred Henabled) as [Hx|[]]. exact Hx.
    + destruct (df_valid_parents_covered _ _ _ _ Hvalid x q IH Hparent Henabled) as [Hq|[]]. exact Hq.
Qed.


Definition df_column (g : prepared) (t : domtree) (y : positive) : list positive :=
  let initial := DfState (preds g y) Empty [] in
  match loopN (df_step g t y) (4 * (nv g + N.of_nat (length (preds g y)) + 1))%N initial with
  | inl st => rev_append (df_column_answer st) []
  | inr answer => answer
  end.
TimeFun df_column.

Definition df_transpose (columns : list (positive * list positive)) : ptrie (list positive) :=
  fst (fold_left (fun state entry =>
    let '(rows, seen) := state in
    let '(y, xs) := entry in
    fold_left (fun state x =>
      let '(acc, marks) := state in
      let marked := match trie_get x marks with Some row => row | None => Empty end in
      match trie_get y marked with
      | Some _ => (acc, marks)
      | None =>
        let row := match trie_get x acc with Some vs => vs | None => [] end in
        (PTrieCode.set x (y :: row) acc,
          PTrieCode.set x (PTrieCode.set y tt marked) marks)
      end) xs (rows, seen)) columns (Empty, Empty)).
TimeFun df_transpose.

Definition df (g : prepared) (t : domtree) : ptrie (list positive) :=
  df_transpose (map (fun y => (y, df_column g t y)) (nodes g)).
TimeFun df.

(** A transposition insertion maintains a separate membership table for each row. *)
Definition df_insert (y x : positive)
    (state : ptrie (list positive) * ptrie (ptrie unit)) :=
  let '(rows, marks) := state in
  let marked := match trie_get x marks with Some row => row | None => Empty end in
  match trie_get y marked with
  | Some _ => (rows, marks)
  | None =>
    (PTrieCode.set x (y :: frontier_row rows x) rows,
      PTrieCode.set x (PTrieCode.set y tt marked) marks)
  end.
TimeFun df_insert.

Definition df_insert_column (state : ptrie (list positive) * ptrie (ptrie unit))
    (entry : positive * list positive) :=
  let '(rows, marks) := state in
  let '(y, xs) := entry in
  fold_left (fun acc x => df_insert y x acc) xs (rows, marks).
TimeFun df_insert_column.

Definition df_rows_valid (state : ptrie (list positive) * ptrie (ptrie unit)) : Prop :=
  (forall x, NoDup (frontier_row (fst state) x)) /\
  forall x y,
    trie_get y (match trie_get x (snd state) with Some row => row | None => Empty end) =
      Some tt <-> In y (frontier_row (fst state) x).

(** A fold preserves any invariant preserved by its individual transitions. *)
Lemma frontier_fold_invariant {A S : Type} (step : S -> A -> S) (Inv : S -> Prop) :
  (forall st x, Inv st -> Inv (step st x)) ->
  forall xs st, Inv st -> Inv (fold_left step xs st).
Proof.
  intros Hstep xs. induction xs as [|x rest IH]; intros st Hst.
  - exact Hst.
  - cbn [fold_left]. apply IH. now apply Hstep.
Qed.

(** An accessibility loop returns a result certified by its state invariant. *)
Lemma frontier_loop_invariant {S R : Type} (lt : S -> S -> Prop)
    (step : forall st, {next : S | lt next st} + R)
    (Inv : S -> Prop) (Result : R -> Prop) :
  (forall st next Hnext, Inv st -> step st = inl (exist _ next Hnext) -> Inv next) ->
  (forall st result, Inv st -> step st = inr result -> Result result) ->
  forall st Hacc, Inv st -> Result (Argent.Loop.loop lt step st Hacc).
Proof.
  intros Hcontinue Hstop st Hacc.
  induction Hacc as [st Hnext IH] using Acc_ind_dep. intro Hinv.
  cbn [Argent.Loop.loop]. destruct (step st) as [[next Hlt]|result] eqn:Hstep.
  - apply IH. eapply Hcontinue; eassumption.
  - eapply Hstop; eassumption.
Qed.

(** Unseen listed vertices provide a finite private fuel measure. *)
Definition df_unseen (vertices : list positive) (seen : ptrie unit) : nat :=
  length (filter (fun x => match trie_get x seen with None => true | Some _ => false end) vertices).

Lemma df_unseen_other : forall vertices seen x,
  ~ In x vertices -> df_unseen vertices (PTrieCode.set x tt seen) = df_unseen vertices seen.
Proof.
  intros vertices seen x Hnot. unfold df_unseen. f_equal.
  apply filter_ext_in. intros u Hu. rewrite PTrie.get_set_other; [reflexivity|].
  intro Heq. subst u. contradiction.
Qed.

Lemma df_unseen_fresh : forall vertices seen x,
  NoDup vertices -> In x vertices -> trie_get x seen = None ->
  df_unseen vertices seen = S (df_unseen vertices (PTrieCode.set x tt seen)).
Proof.
  intro vertices. induction vertices as [|v rest IH]; intros seen x Hunique Hin Hfresh.
  - contradiction.
  - inversion Hunique as [|? ? Hnot Hrest]; subst.
    destruct Hin as [Heq|Hin].
    + subst v. unfold df_unseen at 1 2. cbn [filter].
      rewrite Hfresh, PTrie.get_set_same. cbn [length].
      fold (df_unseen rest seen) (df_unseen rest (PTrieCode.set x tt seen)).
      now rewrite df_unseen_other.
    + assert (Hvx : v <> x) by (intro Heq; subst v; contradiction).
      specialize (IH seen x Hrest Hin Hfresh).
      unfold df_unseen at 1 2. cbn [filter]. rewrite PTrie.get_set_other by exact Hvx.
      destruct (trie_get v seen) as [[]|] eqn:Hget.
      * change (PTrie.get v seen = Some tt) in Hget. rewrite Hget. cbn [length]. exact IH.
      * change (PTrie.get v seen = None) in Hget. rewrite Hget. cbn [length].
        fold (df_unseen rest seen) (df_unseen rest (PTrieCode.set x tt seen)). now rewrite IH.
Qed.

Lemma df_unseen_empty : forall vertices, df_unseen vertices Empty = length vertices.
Proof.
  intro vertices. induction vertices as [|v rest IH]; [reflexivity|].
  unfold df_unseen. cbn [filter]. rewrite PTrie.get_empty. cbn [length].
  fold (df_unseen rest Empty). now rewrite IH.
Qed.

Definition df_progress (g : prepared) (st : df_state) : nat :=
  2 * df_unseen (nodes g) (df_seen st) + length (df_pending st).

Lemma df_progress_step : forall g t r y st next,
  wf_graph (base g) -> domtree_exact g r t -> df_valid g t y st ->
  df_step g t y st = inl next -> df_progress g next < df_progress g st.
Proof.
  intros g t r y [pending seen answer] next Hgraph Htree Hvalid Hstep.
  destruct pending as [|x rest]; [discriminate Hstep|].
  destruct (df_step_behavior g t y x rest seen answer next Hstep)
    as [[-> Hretire]|[-> [Hfresh Henabled]]].
  - unfold df_progress. cbn [df_seen df_pending length]. lia.
  - assert (Hnodes : NoDup (nodes g)).
    { destruct g as [[vertices adjacency] predecessors vertices_count edges_count].
      exact (proj1 Hgraph). }
    pose proof (df_unseen_fresh (nodes g) seen x Hnodes
      (df_valid_pending_nodes _ _ _ _ Hvalid x (or_introl eq_refl)) Hfresh) as Hcredit.
    pose proof (df_follow_length t x rest) as Hlength.
    unfold df_progress. cbn [df_seen df_pending length]. lia.
Qed.

Lemma df_progress_initial : forall g y,
  prepared_ok g ->
  (N.of_nat (df_progress g (DfState (preds g y) Empty [])) <
    4 * (nv g + N.of_nat (length (preds g y)) + 1))%N.
Proof.
  intros g y [Hnv Hprepared]. unfold df_progress. cbn [df_seen df_pending].
  rewrite df_unseen_empty.
  replace (graph_n (base g)) with (length (nodes g)) in Hnv by
    (destruct g as [[vertices adjacency] predecessors vertices_count edges_count]; reflexivity).
  lia.
Qed.

(** A bounded driver preserves the state invariant and certifies every normal return. *)
Lemma frontier_loopN_invariant {S R : Type} (step : S -> S + R)
    (Inv : S -> Prop) (Out : R -> Prop) :
  (forall st next, Inv st -> step st = inl next -> Inv next) ->
  (forall st result, Inv st -> step st = inr result -> Out result) ->
  forall fuel st, Inv st ->
    match loopN step fuel st with inl next => Inv next | inr result => Out result end.
Proof.
  intros Hcontinue Hstop fuel st Hinv.
  assert (Hloop : forall fs Hacc, Inv (snd fs) ->
    match Argent.Loop.loop loopN_lt (loopN_step step) fs Hacc with
    | inl next => Inv next | inr result => Out result
    end).
  { apply (frontier_loop_invariant loopN_lt (loopN_step step)
      (fun fs => Inv (snd fs))
      (fun answer => match answer with inl next => Inv next | inr result => Out result end)).
    - intros [fuel0 st0] [fuel1 st1] Hlt Hvalid Hnext.
      destruct fuel0 as [|p]; [discriminate Hnext|].
      cbn [loopN_step] in Hnext.
      destruct (step st0) as [next|result] eqn:Hstep; [|discriminate Hnext].
      injection Hnext as Heq. inversion Heq; subst.
      eapply Hcontinue; eassumption.
    - intros [fuel0 st0] answer Hvalid Hdone.
      destruct fuel0 as [|p].
      + cbn [loopN_step] in Hdone. injection Hdone as <-. exact Hvalid.
      + cbn [loopN_step] in Hdone.
        destruct (step st0) as [next|result] eqn:Hstep; [discriminate Hdone|].
        injection Hdone as <-. eapply Hstop; eassumption. }
  unfold loopN.
  match goal with
  | |- context [Argent.Loop.loop _ _ ?fs ?Hacc] => exact (Hloop fs Hacc Hinv)
  end.
Qed.

Lemma df_step_stopping : forall g t y st result,
  df_step g t y st = inr result ->
  df_pending st = [] /\ result = rev (df_column_answer st).
Proof.
  intros g t y [pending seen answer] result Hstep.
  destruct pending as [|x rest]; cbn [df_step] in Hstep.
  - injection Hstep as <-. split; [reflexivity|]. now rewrite rev_append_rev, app_nil_r.
  - destruct (trie_get x (pre t)); [|discriminate Hstep].
    destruct (trie_get x seen); [discriminate Hstep|].
    destruct (trie_get y (idom t)) as [b|].
    + destruct (Pos.eqb x b); [discriminate Hstep|].
      destruct (trie_get x (idom t)); discriminate Hstep.
    + destruct (trie_get x (idom t)); discriminate Hstep.
Qed.

(* Opaque drivers keep conversion from expanding their concrete accessibility proofs. *)
Local Opaque Argent.Loop.loop Acc_intro_generator.

Lemma df_column_finished : forall g t r y,
  wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
  exists st result,
    df_valid g t y st /\ df_step g t y st = inr result /\
    loopN (df_step g t y) (4 * (nv g + N.of_nat (length (preds g y)) + 1))%N
      (DfState (preds g y) Empty []) = inr result /\ df_column g t y = result.
Proof.
  intros g t r y Hgraph Hprepared Htree.
  pose proof (df_valid_initial g t y Hprepared) as Hinitial.
  assert (Hcontinue : forall st next, df_valid g t y st -> df_step g t y st = inl next ->
    df_valid g t y next /\ df_progress g next < df_progress g st).
  { intros st next Hvalid Hstep. split.
    - eapply df_valid_step; eassumption.
    - eapply df_progress_step; eassumption. }
  destruct (loopN_done df_state (list positive) (df_step g t y) (df_valid g t y)
    (df_progress g) (4 * (nv g + N.of_nat (length (preds g y)) + 1))%N
    (DfState (preds g y) Empty []) Hcontinue Hinitial (df_progress_initial g y Hprepared))
    as [result Hrun].
  pose proof (frontier_loopN_invariant (df_step g t y) (df_valid g t y)
    (fun result => exists st, df_valid g t y st /\ df_step g t y st = inr result)
    (fun st next Hvalid Hstep => proj1 (Hcontinue st next Hvalid Hstep))
    (fun st result Hvalid Hstop => ex_intro _ st (conj Hvalid Hstop))
    (4 * (nv g + N.of_nat (length (preds g y)) + 1))%N
    (DfState (preds g y) Empty []) Hinitial) as Hresult.
  rewrite Hrun in Hresult. destruct Hresult as [st [Hvalid Hstop]].
  exists st, result. split; [exact Hvalid|]. split; [exact Hstop|]. split; [exact Hrun|].
  unfold df_column. now rewrite Hrun.
Qed.

Lemma df_column_correct : forall g t r y,
  wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
  NoDup (df_column g t y) /\ incl (df_column g t y) (nodes g) /\
    forall x, In x (df_column g t y) <-> in_frontier (base g) r x y.
Proof.
  intros g t r y Hgraph Hprepared Htree.
  destruct (df_column_finished g t r y Hgraph Hprepared Htree)
    as [[pending seen answer] [result [Hvalid [Hstop [Hrun Hcolumn]]]]].
  destruct (df_step_stopping g t y _ result Hstop) as [Hpending Hresult].
  cbn [df_pending df_column_answer] in Hpending, Hresult. subst pending.
  rewrite Hresult in Hcolumn.
  rewrite Hcolumn. split.
  - apply NoDup_rev. exact (df_valid_unique _ _ _ _ Hvalid).
  - split.
    + intros x Hx. apply (proj2 (in_rev answer x)) in Hx.
      exact (df_valid_answer_nodes _ _ _ _ Hvalid x Hx).
    + intro x. rewrite <- (in_rev answer x). rewrite (df_valid_closed g t y seen answer Hvalid x).
      apply (df_route_spec g t r x y Hgraph Hprepared Htree).
Qed.

(** Inserting one previously unseen pair preserves row uniqueness and exact marks. *)
Lemma df_insert_valid : forall y x state,
  df_rows_valid state -> df_rows_valid (df_insert y x state).
Proof.
  intros y x [rows marks] [Hunique Hmarks].
  cbn [fst snd] in Hunique, Hmarks.
  unfold df_insert.
  set (marked := match trie_get x marks with Some row => row | None => Empty end).
  destruct (trie_get y marked) as [[]|] eqn:Hmarked.
  - split; assumption.
  - assert (Hfresh : ~ In y (frontier_row rows x)).
    { intro Hy. apply (proj2 (Hmarks x y)) in Hy.
      change (trie_get y marked = Some tt) in Hy. congruence. }
    split; cbn [fst snd].
    + intro u. unfold frontier_row.
      destruct (Pos.eq_dec u x) as [->|Hux].
      * rewrite PTrie.get_set_same. constructor; [exact Hfresh|apply Hunique].
      * rewrite PTrie.get_set_other by exact Hux. apply Hunique.
    + intros u v. destruct (Pos.eq_dec u x) as [->|Hux].
      * rewrite PTrie.get_set_same. unfold frontier_row.
        rewrite PTrie.get_set_same. cbn [In].
        destruct (Pos.eq_dec v y) as [->|Hvy].
        -- rewrite PTrie.get_set_same. tauto.
        -- rewrite PTrie.get_set_other by exact Hvy.
           change (trie_get v marked = Some tt <-> y = v \/
             In v (frontier_row rows x)).
           unfold marked. rewrite Hmarks. intuition congruence.
      * rewrite PTrie.get_set_other by exact Hux.
        unfold frontier_row at 1.
        rewrite PTrie.get_set_other by exact Hux. apply Hmarks.
Qed.

(** Transposition removes repeated source-target pairs on arbitrary raw columns. *)
Lemma df_transpose_unique : forall columns x,
  NoDup (frontier_row (df_transpose columns) x).
Proof.
  intros columns x. unfold df_transpose.
  change (NoDup (frontier_row (fst
    (fold_left df_insert_column columns (Empty, Empty))) x)).
  assert (Hvalid : df_rows_valid
    (fold_left df_insert_column columns (Empty, Empty))).
  { apply frontier_fold_invariant.
    - intros [rows marks] [y xs] Hst. cbn [df_insert_column].
      apply frontier_fold_invariant; [intros; now apply df_insert_valid|exact Hst].
    - split.
      + intro u. unfold frontier_row. rewrite PTrie.get_empty. constructor.
      + intros u v. rewrite !PTrie.get_empty. cbn [fst snd].
        unfold frontier_row. rewrite PTrie.get_empty. cbn. split; [discriminate|contradiction]. }
  exact (proj1 Hvalid x).
Qed.

(** One insertion adds precisely its source-target pair to the observed rows. *)
Lemma df_insert_member : forall y x state u v,
  df_rows_valid state ->
  (In v (frontier_row (fst (df_insert y x state)) u) <->
    In v (frontier_row (fst state) u) \/ (u = x /\ v = y)).
Proof.
  intros y x [rows marks] u v [_ Hmarks]. cbn [fst snd] in *.
  unfold df_insert.
  set (marked := match trie_get x marks with Some row => row | None => Empty end).
  destruct (trie_get y marked) as [[]|] eqn:Hmarked; cbn [fst].
  - split; [now left|]. intros [Hin|[-> ->]]; [exact Hin|].
    apply (proj1 (Hmarks x y)). exact Hmarked.
  - destruct (Pos.eq_dec u x) as [->|Hux].
    + unfold frontier_row at 1. rewrite PTrie.get_set_same. cbn [In].
      intuition congruence.
    + unfold frontier_row at 1. rewrite PTrie.get_set_other by exact Hux.
      change (In v (frontier_row rows u) <->
        In v (frontier_row rows u) \/ (u = x /\ v = y)). tauto.
Qed.

(** Inserting a whole column adds its target to exactly the listed source rows. *)
Lemma df_column_insert_member : forall y xs state u v,
  df_rows_valid state ->
  (In v (frontier_row (fst
      (fold_left (fun acc x => df_insert y x acc) xs state)) u) <->
    In v (frontier_row (fst state) u) \/ (v = y /\ In u xs)).
Proof.
  intros y xs. induction xs as [|x rest IH]; intros state u v Hvalid.
  - cbn [fold_left In]. tauto.
  - cbn [fold_left]. rewrite IH by now apply df_insert_valid.
    rewrite df_insert_member by exact Hvalid. cbn [In]. intuition congruence.
Qed.

(** Transposition from a valid accumulator preserves exactly the accumulated pairs. *)
Lemma df_columns_insert_member : forall columns state u v,
  df_rows_valid state ->
  (In v (frontier_row (fst
      (fold_left df_insert_column columns state)) u) <->
    In v (frontier_row (fst state) u) \/
      exists column, In (v, column) columns /\ In u column).
Proof.
  intro columns. induction columns as [|[y xs] rest IH]; intros [rows marks] u v Hvalid.
  - cbn [fold_left In]. split; [now left|]. intros [Hin|[column [Hbad _]]]; tauto.
  - cbn [fold_left df_insert_column].
    rewrite IH by
      (apply frontier_fold_invariant; [intros; now apply df_insert_valid|exact Hvalid]).
    rewrite df_column_insert_member by exact Hvalid. cbn [In].
    split.
    + intros [[Hin|[-> Hin]]|[column [Hcolumn Hin]]].
      * now left.
      * right. exists xs. auto.
      * right. exists column. auto.
    + intros [Hin|[column [[Heq|Hcolumn] Hin]]].
      * left. now left.
      * inversion Heq; subst. left. right. auto.
      * right. exists column. auto.
Qed.

(** A row contains a target exactly when the corresponding column contains its source. *)
Lemma df_transpose_member : forall columns x y,
  In y (frontier_row (df_transpose columns) x) <->
    exists column, In (y, column) columns /\ In x column.
Proof.
  intros columns x y. unfold df_transpose.
  change (In y (frontier_row (fst
    (fold_left df_insert_column columns (Empty, Empty))) x) <->
    exists column, In (y, column) columns /\ In x column).
  rewrite df_columns_insert_member.
  - cbn [fst]. unfold frontier_row. rewrite PTrie.get_empty. cbn [In]. tauto.
  - split.
    + intro u. unfold frontier_row. rewrite PTrie.get_empty. constructor.
    + intros u v. cbn [fst snd]. rewrite PTrie.get_empty.
      unfold frontier_row. rewrite !PTrie.get_empty. cbn [In].
      split; [discriminate|contradiction].
Qed.

(** Finite row sizes count each stored source-target pair once. *)
Definition df_rows_size (vertices : list positive) (rows : ptrie (list positive)) : nat :=
  fold_right (fun x total => length (frontier_row rows x) + total) 0 vertices.

Lemma frontier_sum_ext {A : Type} : forall (xs : list A) (f g : A -> nat),
  (forall x, In x xs -> f x = g x) ->
  fold_right (fun x total => f x + total) 0 xs =
  fold_right (fun x total => g x + total) 0 xs.
Proof.
  intro xs. induction xs as [|x rest IH]; intros f g Heq; [reflexivity|].
  cbn [fold_right]. rewrite (Heq x (or_introl eq_refl)). f_equal.
  apply IH. intros u Hu. apply Heq. now right.
Qed.

Lemma frontier_sum_update {A : Type} : forall (xs : list A) x (f g : A -> nat),
  NoDup xs -> In x xs -> g x = S (f x) -> (forall u, u <> x -> g u = f u) ->
  fold_right (fun u total => g u + total) 0 xs =
  S (fold_right (fun u total => f u + total) 0 xs).
Proof.
  intro xs. induction xs as [|v rest IH]; intros x f g Hunique Hin Hx Hother.
  - contradiction.
  - inversion Hunique as [|? ? Hnot Hrest]; subst.
    destruct Hin as [Heq|Hin].
    + subst v. cbn [fold_right]. rewrite Hx.
      assert (Htail : fold_right (fun u total => g u + total) 0 rest =
        fold_right (fun u total => f u + total) 0 rest).
      { apply frontier_sum_ext. intros u Hu. apply Hother. intro Heq. subst u. contradiction. }
      now rewrite Htail.
    + assert (Hvx : v <> x) by (intro Heq; subst v; contradiction).
      cbn [fold_right]. rewrite (Hother v Hvx), (IH x f g Hrest Hin Hx Hother). lia.
Qed.

Lemma df_rows_empty : df_rows_valid (Empty, Empty).
Proof.
  split.
  - intro x. unfold frontier_row. rewrite PTrie.get_empty. constructor.
  - intros x y. cbn [fst snd]. rewrite PTrie.get_empty.
    unfold frontier_row. rewrite !PTrie.get_empty. cbn [In].
    split; [discriminate|contradiction].
Qed.

Lemma df_insert_size : forall vertices y x state,
  NoDup vertices -> In x vertices -> df_rows_valid state ->
  ~ In y (frontier_row (fst state) x) ->
  df_rows_size vertices (fst (df_insert y x state)) =
    S (df_rows_size vertices (fst state)).
Proof.
  intros vertices y x [rows marks] Hunique Hin Hvalid Hfresh.
  destruct Hvalid as [Hrows Hmarks]. cbn [fst snd] in *.
  assert (Hget : trie_get y
    (match trie_get x marks with Some row => row | None => Empty end) = None).
  { destruct (trie_get y (match trie_get x marks with Some row => row | None => Empty end))
      as [[]|] eqn:Hget; [|reflexivity].
    exfalso. apply Hfresh. now apply (proj1 (Hmarks x y)). }
  unfold df_insert. rewrite Hget. cbn [fst]. unfold df_rows_size.
  apply frontier_sum_update with x; [exact Hunique|exact Hin| |].
  - unfold frontier_row at 1. rewrite PTrie.get_set_same. reflexivity.
  - intros u Hne. unfold frontier_row at 1. now rewrite PTrie.get_set_other.
Qed.

Lemma df_column_insert_size : forall vertices y xs state,
  NoDup vertices -> NoDup xs -> incl xs vertices -> df_rows_valid state ->
  (forall x, In x xs -> ~ In y (frontier_row (fst state) x)) ->
  df_rows_size vertices (fst (fold_left (fun acc x => df_insert y x acc) xs state)) =
    length xs + df_rows_size vertices (fst state).
Proof.
  intros vertices y xs. induction xs as [|x rest IH];
    intros state Hvertices Hunique Hincl Hvalid Hclear; [reflexivity|].
  inversion Hunique as [|? ? Hnot Hrest]; subst.
  assert (Hinclrest : incl rest vertices) by (intros u Hu; apply Hincl; now right).
  assert (Hclearrest : forall u, In u rest ->
    ~ In y (frontier_row (fst (df_insert y x state)) u)).
  { intros u Hu Hmember. apply (proj1 (df_insert_member y x state u y Hvalid)) in Hmember.
    destruct Hmember as [Hmember|[Heq _]].
    - apply (Hclear u (or_intror Hu)). exact Hmember.
    - subst u. contradiction. }
  cbn [fold_left length].
  rewrite (IH (df_insert y x state) Hvertices Hrest Hinclrest
    (df_insert_valid y x state Hvalid) Hclearrest).
  rewrite (df_insert_size vertices y x state Hvertices (Hincl x (or_introl eq_refl))
    Hvalid (Hclear x (or_introl eq_refl))). lia.
Qed.

Lemma df_columns_insert_size : forall vertices columns state,
  NoDup vertices -> NoDup (map fst columns) ->
  Forall (fun entry => NoDup (snd entry) /\ incl (snd entry) vertices) columns ->
  df_rows_valid state ->
  (forall y xs, In (y, xs) columns -> forall x, ~ In y (frontier_row (fst state) x)) ->
  df_rows_size vertices (fst (fold_left df_insert_column columns state)) =
    fold_right (fun entry total => length (snd entry) + total) 0 columns +
      df_rows_size vertices (fst state).
Proof.
  intros vertices columns. induction columns as [|[y xs] rest IH];
    intros [rows marks] Hvertices Htargets Hcolumns Hvalid Hclear; [reflexivity|].
  inversion Htargets as [|? ? Hnot Hrest]; subst.
  inversion Hcolumns as [|? ? Hcolumn Hcolumnsrest]; subst.
  destruct Hcolumn as [Hxs Hwithin]. cbn [snd] in Hxs, Hwithin.
  assert (Hvalidnext : df_rows_valid
    (fold_left (fun acc x => df_insert y x acc) xs (rows, marks))).
  { apply frontier_fold_invariant; [intros; now apply df_insert_valid|exact Hvalid]. }
  assert (Hclearnext : forall target column, In (target, column) rest ->
    forall x, ~ In target (frontier_row
      (fst (fold_left (fun acc x => df_insert y x acc) xs (rows, marks))) x)).
  { intros target column Hcolumn x Hmember.
    apply (proj1 (df_column_insert_member y xs (rows, marks) x target Hvalid)) in Hmember.
    destruct Hmember as [Hmember|[Heq Hin]].
    - exact (Hclear target column (or_intror Hcolumn) x Hmember).
    - subst target. apply Hnot. apply in_map_iff. exists (y, column). now split. }
  cbn [fold_left df_insert_column fold_right snd].
  rewrite (IH _ Hvertices Hrest Hcolumnsrest Hvalidnext Hclearnext).
  rewrite (df_column_insert_size vertices y xs (rows, marks) Hvertices Hxs Hwithin Hvalid).
  - lia.
  - intros x Hx. exact (Hclear y xs (or_introl eq_refl) x).
Qed.

Lemma df_transpose_size : forall vertices columns,
  NoDup vertices -> NoDup (map fst columns) ->
  Forall (fun entry => NoDup (snd entry) /\ incl (snd entry) vertices) columns ->
  df_rows_size vertices (df_transpose columns) =
    fold_right (fun entry total => length (snd entry) + total) 0 columns.
Proof.
  intros vertices columns Hvertices Htargets Hcolumns.
  assert (Hempty : df_rows_size vertices Empty = 0).
  { clear Hvertices Htargets Hcolumns columns.
    induction vertices as [|v rest IH]; [reflexivity|].
    unfold df_rows_size in *. cbn [fold_right]. unfold frontier_row at 1.
    rewrite PTrie.get_empty. cbn [length]. exact IH. }
  pose proof (df_columns_insert_size vertices columns (Empty, Empty)
    Hvertices Htargets Hcolumns df_rows_empty) as Hsize.
  specialize (Hsize (fun y xs Hin x =>
    ltac:(unfold frontier_row; rewrite PTrie.get_empty; cbn [In]; tauto))).
  cbn [fst] in Hsize. rewrite Hempty in Hsize.
  unfold df_transpose. change (df_rows_size vertices
    (fst (fold_left df_insert_column columns (Empty, Empty))) =
      fold_right (fun entry total => length (snd entry) + total) 0 columns).
  lia.
Qed.

Definition idf_step (rows : ptrie (list positive)) (st : idf_state) :
    idf_state + list positive :=
  match st with
  | IdfState [] _ _ answer => inr (rev_append answer [])
  | IdfState (task :: rest) expanded discovered answer =>
    let '(v, target) := match task with
      | IdfSeed v => (v, false)
      | IdfTarget v => (v, true)
      end in
    let '(discovered', answer') :=
      if target then
        match trie_get v discovered with
        | Some _ => (discovered, answer)
        | None => (PTrieCode.set v tt discovered, v :: answer)
        end
      else (discovered, answer) in
    match trie_get v expanded with
    | Some _ => inl (IdfState rest expanded discovered' answer')
    | None => inl (IdfState (map IdfTarget (frontier_row rows v) ++ rest)
        (PTrieCode.set v tt expanded) discovered' answer')
    end
  end.
TimeFun idf_step.

Definition idf_initial (seeds : list positive) := IdfState (map IdfSeed seeds) Empty Empty [].
TimeFun idf_initial.

Definition idf_advance rows st :=
  match idf_step rows st with
  | inl next => next
  | inr _ => st
  end.
TimeFun idf_advance.

Definition idf_reachable rows seeds st : Prop :=
  exists n, Nat.iter n (idf_advance rows) (idf_initial seeds) = st.

Definition idf_universe rows seeds :=
  nodup Pos.eq_dec (seeds ++ flat_map snd (PTrieCode.elements rows)).

Definition idf_measure rows seeds st : N :=
  N.of_nat (2 * fold_right (fun v n =>
    match trie_get v (idf_expanded st) with
    | Some _ => n
    | None => 2 + length (frontier_row rows v) + n
    end) 0 (idf_universe rows seeds) + length (idf_pending st)).

(** Every seed and every supplied row target belongs to the finite proof universe. *)
Lemma idf_universe_contains : forall rows seeds,
  NoDup (idf_universe rows seeds) /\ incl seeds (idf_universe rows seeds) /\
    forall x y, In y (frontier_row rows x) -> In y (idf_universe rows seeds).
Proof.
  intros rows seeds. unfold idf_universe. split; [apply NoDup_nodup|]. split.
  - intros x Hx. apply nodup_In. apply in_or_app. now left.
  - intros x y Hy. apply nodup_In. apply in_or_app. right.
    unfold frontier_row in Hy. destruct (trie_get x rows) as [row|] eqn:Hrow;
      [|contradiction].
    apply in_flat_map. exists (x, row). split; [|exact Hy].
    apply PTrie.elements_spec. exact Hrow.
Qed.

Definition idf_tasks_within (universe : list positive) (st : idf_state) : Prop :=
  Forall (fun task =>
    match task with IdfSeed v | IdfTarget v => In v universe end) (idf_pending st).

(** Row expansion preserves a universe containing all supplied targets. *)
Lemma idf_step_within : forall rows universe st next,
  (forall x y, In y (frontier_row rows x) -> In y universe) ->
  idf_tasks_within universe st -> idf_step rows st = inl next ->
  idf_tasks_within universe next.
Proof.
  intros rows universe [pending expanded discovered answer] next Hrows Hwithin Hstep.
  destruct pending as [|task rest]; [discriminate Hstep|].
  inversion Hwithin as [|? ? Htask Hrest]; subst.
  unfold idf_tasks_within. destruct task as [v|v]; cbn [idf_step] in Hstep;
    [|destruct (trie_get v discovered) as [[]|] eqn:Hdiscovered];
    destruct (trie_get v expanded) as [[]|] eqn:Hexpanded;
    inversion Hstep; subst next; cbn [idf_pending]; try exact Hrest.
  all: apply Forall_app; split; [|exact Hrest].
  all: apply Forall_forall; intros task Htask'; apply in_map_iff in Htask';
    destruct Htask' as [target [<- Htarget]]; now apply (Hrows v).
Qed.

(** Every reachable task is supported by a seed or a target in the supplied row map. *)
Lemma idf_reachable_within : forall rows seeds st,
  idf_reachable rows seeds st -> idf_tasks_within (idf_universe rows seeds) st.
Proof.
  intros rows seeds st [n <-].
  destruct (idf_universe_contains rows seeds) as [_ [Hseeds Hrows]].
  induction n as [|n IH].
  - unfold idf_tasks_within. cbn [Nat.iter idf_initial idf_pending].
    apply Forall_forall. intros task Htask. apply in_map_iff in Htask.
    destruct Htask as [v [<- Hv]]. now apply Hseeds.
  - rewrite Nat.iter_succ. unfold idf_advance at 1.
    destruct (idf_step rows (Nat.iter n (idf_advance rows) (idf_initial seeds)))
      as [next|result] eqn:Hstep.
    + exact (idf_step_within rows (idf_universe rows seeds) _ next Hrows IH Hstep).
    + exact IH.
Qed.

Definition idf_unexpanded rows vertices (expanded : ptrie unit) : nat :=
  fold_right (fun v n =>
    match trie_get v expanded with
    | Some _ => n
    | None => 2 + length (frontier_row rows v) + n
    end) 0 vertices.

(** Marking a key outside a vertex list leaves its unused row credit unchanged. *)
Lemma idf_unexpanded_other : forall rows vertices expanded x,
  ~ In x vertices ->
  idf_unexpanded rows vertices (PTrieCode.set x tt expanded) =
    idf_unexpanded rows vertices expanded.
Proof.
  intros rows vertices. induction vertices as [|v rest IH]; intros expanded x Hout.
  - reflexivity.
  - cbn [idf_unexpanded fold_right].
    fold (idf_unexpanded rows rest (PTrieCode.set x tt expanded))
      (idf_unexpanded rows rest expanded).
    rewrite PTrie.get_set_other by (intro Heq; apply Hout; subst; now left).
    rewrite IH by (intro Hin; apply Hout; now right). reflexivity.
Qed.

(** Marking a fresh listed key spends exactly its row-expansion credit. *)
Lemma idf_unexpanded_fresh : forall rows vertices expanded x,
  NoDup vertices -> In x vertices -> trie_get x expanded = None ->
  idf_unexpanded rows vertices (PTrieCode.set x tt expanded) +
    (2 + length (frontier_row rows x)) = idf_unexpanded rows vertices expanded.
Proof.
  intros rows vertices. induction vertices as [|v rest IH];
    intros expanded x Hunique Hin Hfresh; [contradiction|].
  inversion Hunique as [|? ? Hout Hrest]; subst.
  destruct Hin as [->|Hin].
  - cbn [idf_unexpanded fold_right].
    fold (idf_unexpanded rows rest (PTrieCode.set x tt expanded))
      (idf_unexpanded rows rest expanded).
    rewrite PTrie.get_set_same, Hfresh.
    rewrite idf_unexpanded_other by exact Hout. lia.
  - assert (Hvx : v <> x) by (intro Heq; apply Hout; now rewrite Heq).
    cbn [idf_unexpanded fold_right].
    fold (idf_unexpanded rows rest (PTrieCode.set x tt expanded))
      (idf_unexpanded rows rest expanded).
    rewrite PTrie.get_set_other by exact Hvx.
    specialize (IH expanded x Hrest Hin Hfresh).
    destruct (trie_get v expanded) as [value|] eqn:Hget.
    + change (PTrie.get v expanded = Some value) in Hget. rewrite Hget. exact IH.
    + change (PTrie.get v expanded = None) in Hget. rewrite Hget. lia.
Qed.

Lemma idf_reachable_initial : forall rows seeds,
  idf_reachable rows seeds (idf_initial seeds).
Proof.
  intros rows seeds. exists 0. reflexivity.
Qed.

Lemma idf_reachable_step : forall rows seeds st next,
  idf_reachable rows seeds st -> idf_step rows st = inl next ->
  idf_reachable rows seeds next.
Proof.
  intros rows seeds st next [n Hreach] Hstep.
  exists (S n). rewrite Nat.iter_succ, Hreach.
  unfold idf_advance. now rewrite Hstep.
Qed.

Lemma idf_measure_step : forall rows seeds st next,
  idf_reachable rows seeds st -> idf_step rows st = inl next ->
  (idf_measure rows seeds next < idf_measure rows seeds st)%N.
Proof.
  intros rows seeds [pending expanded discovered answer] next Hreach Hstep.
  pose proof (idf_reachable_within rows seeds _ Hreach) as Hwithin.
  destruct (idf_universe_contains rows seeds) as [Hunique _].
  destruct pending as [|task rest]; [discriminate Hstep|].
  inversion Hwithin as [|? ? Htask Hrest]; subst.
  destruct task as [v|v]; cbn [idf_step] in Hstep;
    [|destruct (trie_get v discovered) as [[]|] eqn:Hdiscovered];
    destruct (trie_get v expanded) as [[]|] eqn:Hexpanded;
    inversion Hstep; subst next; unfold idf_measure; cbn [idf_expanded idf_pending].
  all: try (cbn [length]; lia).
  all: pose proof (idf_unexpanded_fresh rows (idf_universe rows seeds) expanded v
    Hunique Htask Hexpanded) as Hcredit.
  all: unfold idf_unexpanded in Hcredit;
    rewrite length_app, length_map; cbn [length]; lia.
Qed.

Definition idf_private_state rows seeds := { st : idf_state | idf_reachable rows seeds st }.

Definition idf_state_of {rows seeds} (st : idf_private_state rows seeds) : idf_state :=
  match st with
  | exist _ state _ => state
  end.
TimeFun idf_state_of.

Definition idf_private_lt rows seeds (next st : idf_private_state rows seeds) : Prop :=
  (idf_measure rows seeds (proj1_sig next) < idf_measure rows seeds (proj1_sig st))%N.

Definition idf_checked_step rows seeds (st : idf_private_state rows seeds) :
    { next : idf_private_state rows seeds | idf_private_lt rows seeds next st } + list positive :=
  let state := idf_state_of st in
  match idf_step rows state as result
    return idf_step rows state = result ->
      { next : idf_private_state rows seeds | idf_private_lt rows seeds next st } + list positive
  with
  | inl next => fun Hstep =>
    inl (exist _
      (exist _ next (idf_reachable_step rows seeds state next (proj2_sig st) Hstep))
      (idf_measure_step rows seeds state next (proj2_sig st) Hstep))
  | inr result => fun _ => inr result
  end eq_refl.
TimeFun idf_checked_step.

(** Erasing private loop evidence exposes exactly the raw IDF transition. *)
Lemma idf_checked_step_raw : forall rows seeds st,
  match idf_checked_step rows seeds st with
  | inl next => inl (proj1_sig (proj1_sig next))
  | inr result => inr result
  end = idf_step rows (proj1_sig st).
Proof.
  intros rows seeds [st Hreach]. unfold idf_checked_step, idf_state_of.
  cbn [proj1_sig proj2_sig].
  assert (Hproject : forall (result : idf_state + list positive)
      (Hresult : idf_step rows st = result),
    match
      (match result as answer return idf_step rows st = answer ->
        {next : idf_private_state rows seeds |
          idf_private_lt rows seeds next (exist _ st Hreach)} + list positive
      with
      | inl next => fun Hstep =>
        inl (exist _
          (exist _ next (idf_reachable_step rows seeds st next Hreach Hstep))
          (idf_measure_step rows seeds st next Hreach Hstep))
      | inr answer => fun _ => inr answer
      end Hresult)
    with
    | inl next => inl (proj1_sig (proj1_sig next))
    | inr answer => inr answer
    end = result).
  { intros [next|answer] Hresult; reflexivity. }
  exact (Hproject _ eq_refl).
Qed.

Definition idf_accessible rows seeds (st : idf_private_state rows seeds) :
    Acc (idf_private_lt rows seeds) st :=
  Acc_intro_generator 32
    (Wellfounded.Inverse_Image.wf_inverse_image _ N N.lt
      (fun state => idf_measure rows seeds (proj1_sig state)) N.lt_wf_0) st.
Definition idf (rows : ptrie (list positive)) (seeds : list positive) : list positive :=
  let initial := exist _ (idf_initial seeds) (idf_reachable_initial rows seeds) in
  Argent.Loop.loop (idf_private_lt rows seeds) (idf_checked_step rows seeds)
    initial (idf_accessible rows seeds initial).
TimeFun idf.

Definition idf_distinct (st : idf_state) : Prop :=
  NoDup (idf_answer st) /\
    forall v, trie_get v (idf_discovered st) = Some tt <-> In v (idf_answer st).

(** Recording a fresh target keeps the accumulated answer and its table in agreement. *)
Lemma idf_record_distinct : forall expanded pending discovered answer v,
  idf_distinct (IdfState pending expanded discovered answer) ->
  trie_get v discovered = None ->
  NoDup (v :: answer) /\
    forall x, trie_get x (PTrieCode.set v tt discovered) = Some tt <-> In x (v :: answer).
Proof.
  intros expanded pending discovered answer v [Hunique Hmarks] Hfresh.
  cbn [idf_answer idf_discovered] in Hunique, Hmarks.
  split.
  - constructor; [|exact Hunique]. intro Hin.
    apply (proj2 (Hmarks v)) in Hin. congruence.
  - intro x. destruct (Pos.eq_dec x v) as [->|Hneq].
    + rewrite PTrie.get_set_same. cbn [In]. tauto.
    + rewrite PTrie.get_set_other by exact Hneq. rewrite Hmarks. cbn [In].
      intuition congruence.
Qed.

(** Every raw IDF step preserves a duplicate-free answer and exact discovery marks. *)
Lemma idf_step_distinct : forall rows st next,
  idf_distinct st -> idf_step rows st = inl next -> idf_distinct next.
Proof.
  intros rows [pending expanded discovered answer] next Hdistinct Hstep.
  destruct pending as [|task rest]; [discriminate Hstep|].
  destruct task as [v|v]; cbn [idf_step] in Hstep.
  - destruct (trie_get v expanded); inversion Hstep; subst; exact Hdistinct.
  - destruct (trie_get v discovered) as [[]|] eqn:Hdiscovered;
      destruct (trie_get v expanded); inversion Hstep; subst.
    + exact Hdistinct.
    + exact Hdistinct.
    + apply (idf_record_distinct expanded (IdfTarget v :: rest)); assumption.
    + apply (idf_record_distinct expanded (IdfTarget v :: rest)); assumption.
Qed.

(** The lazy driver always returns a duplicate-free list, including on raw row maps. *)
Lemma idf_result_unique : forall rows seeds, NoDup (idf rows seeds).
Proof.
  intros rows seeds. unfold idf.
  refine (frontier_loop_invariant (idf_private_lt rows seeds)
    (idf_checked_step rows seeds)
    (fun st => idf_distinct (proj1_sig st)) (@NoDup positive) _ _
    (exist _ (idf_initial seeds) (idf_reachable_initial rows seeds))
    (idf_accessible rows seeds
      (exist _ (idf_initial seeds) (idf_reachable_initial rows seeds))) _).
  - intros st next Hnext Hdistinct Hstep.
    pose proof (idf_checked_step_raw rows seeds st) as Hraw.
    rewrite Hstep in Hraw. cbn [proj1_sig] in Hraw.
    eapply idf_step_distinct; [exact Hdistinct|symmetry; exact Hraw].
  - intros state result Hdistinct Hstep.
    pose proof (idf_checked_step_raw rows seeds state) as Hraw.
    rewrite Hstep in Hraw. destruct state as [st Hreach]. cbn [proj1_sig] in Hraw.
    destruct st as [pending expanded discovered answer].
    destruct pending as [|task rest]; cbn [idf_step] in Hraw.
    + inversion Hraw; subst result. rewrite rev_append_rev, app_nil_r.
      apply NoDup_rev. exact (proj1 Hdistinct).
    + destruct task as [v|v]; cbn [idf_step] in Hraw;
        [|destruct (trie_get v discovered) as [[]|] eqn:Hdiscovered];
        destruct (trie_get v expanded) as [[]|] eqn:Hexpanded; discriminate.
  - split; [constructor|]. intro v. cbn [proj1_sig idf_initial idf_discovered idf_answer].
    rewrite PTrie.get_empty. cbn [In]. split; [discriminate|contradiction].
Qed.

(** Graph node observations agree with the underlying vertex list. *)
Lemma frontier_nodes_verts : forall g, nodes g = verts (base g).
Proof.
  intros [[vertices adjacency] predecessors vertices_count edges_count]. reflexivity.
Qed.

Lemma frontier_nodes_unique : forall g, wf_graph (base g) -> NoDup (nodes g).
Proof.
  intros g Hgraph. rewrite frontier_nodes_verts. exact (proj1 Hgraph).
Qed.

Lemma frontier_sum_add {A : Type} : forall (xs : list A) (f g : A -> nat),
  fold_right (fun x total => f x + g x + total) 0 xs =
  fold_right (fun x total => f x + total) 0 xs +
    fold_right (fun x total => g x + total) 0 xs.
Proof.
  intro xs. induction xs as [|x rest IH]; intros f g; [reflexivity|].
  cbn [fold_right]. rewrite IH. lia.
Qed.

Lemma frontier_sum_swap {A B : Type} : forall (xs : list A) (ys : list B) (f : A -> B -> nat),
  fold_right (fun x total => fold_right (fun y subtotal => f x y + subtotal) 0 ys + total) 0 xs =
  fold_right (fun y total => fold_right (fun x subtotal => f x y + subtotal) 0 xs + total) 0 ys.
Proof.
  intro xs. induction xs as [|x rest IH]; intros ys f.
  - cbn [fold_right]. induction ys; cbn [fold_right]; assumption || reflexivity.
  - cbn [fold_right]. rewrite IH. symmetry. apply frontier_sum_add.
Qed.

Lemma frontier_flat_map_length {A B : Type} : forall (f : A -> list B) xs,
  length (flat_map f xs) = fold_right (fun x total => length (f x) + total) 0 xs.
Proof.
  intros f xs. induction xs as [|x rest IH]; [reflexivity|].
  cbn [flat_map fold_right]. now rewrite length_app, IH.
Qed.

(** Filtering once for each distinct listed target counts every successor occurrence once. *)
Lemma frontier_filter_partition : forall vertices successors,
  NoDup vertices -> incl successors vertices ->
  fold_right (fun y total => length (filter (Pos.eqb y) successors) + total) 0 vertices =
    length successors.
Proof.
  intros vertices successors Hunique. induction successors as [|v rest IH]; intro Hincl.
  - assert (Hzero : forall xs, fold_right
      (fun y total => length (filter (Pos.eqb y) []) + total) 0 xs = 0).
    { intro xs. induction xs; cbn [fold_right filter length]; assumption || reflexivity. }
    apply Hzero.
  - assert (Hrest : incl rest vertices) by (intros u Hu; apply Hincl; now right).
    specialize (IH Hrest).
    pose proof (frontier_sum_update vertices v
      (fun y => length (filter (Pos.eqb y) rest))
      (fun y => length (filter (Pos.eqb y) (v :: rest))) Hunique
      (Hincl v (or_introl eq_refl))) as Hsum.
    assert (Hsame : length (filter (Pos.eqb v) (v :: rest)) =
      S (length (filter (Pos.eqb v) rest))).
    { cbn [filter]. now rewrite Pos.eqb_refl. }
    assert (Hother : forall u, u <> v ->
      length (filter (Pos.eqb u) (v :: rest)) = length (filter (Pos.eqb u) rest)).
    { intros u Hne. cbn [filter]. apply Pos.eqb_neq in Hne. now rewrite Hne. }
    specialize (Hsum Hsame Hother). cbn [length]. now rewrite Hsum, IH.
Qed.

Lemma frontier_preds_length : forall g y,
  prepared_ok g -> length (preds g y) =
    fold_right (fun x total => length (filter (Pos.eqb y) (succs (base g) x)) + total) 0 (nodes g).
Proof.
  intros g y [_ [_ Hpreds]]. rewrite (Permutation_length (Hpreds y)).
  rewrite frontier_flat_map_length. apply frontier_sum_ext. intros x Hx. apply length_map.
Qed.

(** Preparation preserves the total number of predecessor occurrences, including parallel edges. *)
Lemma frontier_predecessor_sum : forall g,
  wf_graph (base g) -> prepared_ok g ->
  fold_right (fun y total => length (preds g y) + total) 0 (nodes g) = graph_e (base g).
Proof.
  intros g Hgraph Hprepared.
  rewrite (frontier_sum_ext (nodes g) (fun y => length (preds g y))
    (fun y => fold_right (fun x total => length (filter (Pos.eqb y) (succs (base g) x)) + total)
      0 (nodes g))) by (intros y Hy; now apply frontier_preds_length).
  rewrite frontier_sum_swap.
  replace (graph_e (base g)) with
    (fold_right (fun x total => length (succs (base g) x) + total) 0 (nodes g)) by
    (destruct g as [[vertices adjacency] predecessors vertices_count edges_count]; reflexivity).
  apply frontier_sum_ext. intros x Hx. apply frontier_filter_partition.
  - now apply frontier_nodes_unique.
  - intros y Hy. rewrite frontier_nodes_verts in *. eapply (proj2 Hgraph); eassumption.
Qed.

Definition df_column_progress (g : prepared) (t : domtree) (y : positive) (st : df_state) : nat :=
  2 * df_unseen (df_column g t y) (df_seen st) + length (df_pending st).

(** Each continuing runner consumes credit from its actual output column. *)
Lemma df_column_progress_step : forall g t r y st next,
  wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
  df_valid g t y st -> df_step g t y st = inl next ->
  df_column_progress g t y next < df_column_progress g t y st.
Proof.
  intros g t r y [pending seen answer] next Hgraph Hprepared Htree Hvalid Hstep.
  destruct pending as [|x rest]; [discriminate Hstep|].
  destruct (df_step_behavior g t y x rest seen answer next Hstep)
    as [[-> Hretire]|[-> [Hfresh Henabled]]].
  - unfold df_column_progress. cbn [df_seen df_pending length]. lia.
  - pose proof (df_column_correct g t r y Hgraph Hprepared Htree) as [Hunique [Hwithin Hcolumn]].
    assert (Hx : In x (df_column g t y)).
    { apply (proj2 (Hcolumn x)), (proj1 (df_route_spec g t r x y Hgraph Hprepared Htree)).
      apply (df_valid_pending_routes _ _ _ _ Hvalid x); [now left|exact Henabled]. }
    pose proof (df_unseen_fresh (df_column g t y) seen x Hunique Hx Hfresh) as Hcredit.
    pose proof (df_follow_length t x rest) as Hlength.
    unfold df_column_progress. cbn [df_seen df_pending length]. lia.
Qed.

Lemma df_column_progress_initial : forall g t y,
  df_column_progress g t y (DfState (preds g y) Empty []) =
    2 * length (df_column g t y) + length (preds g y).
Proof.
  intros g t y. unfold df_column_progress. cbn [df_seen df_pending]. now rewrite df_unseen_empty.
Qed.

Module FrontierCode <: FRONTIER_OPS.
  Definition df := df.
  Definition idf := idf.
End FrontierCode.

Module Frontier <: FRONTIER.
  Include FrontierCode.
  Include FRONTIER_SPEC.

  Lemma df_spec : forall g t r x y,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    In y (frontier_row (df g t) x) <-> in_frontier (base g) r x y.
  Proof.
    intros g t r x y Hgraph Hprepared Htree.
    change (In y (frontier_row
      (df_transpose (map (fun v => (v, df_column g t v)) (nodes g))) x) <->
      in_frontier (base g) r x y).
    rewrite df_transpose_member. split.
    - intros [column [Hcolumn Hx]]. apply in_map_iff in Hcolumn.
      destruct Hcolumn as [v [Heq Hv]]. injection Heq as Heqv Heqcolumn. subst v column.
      exact (proj1 (proj2 (proj2 (df_column_correct g t r y Hgraph Hprepared Htree)) x) Hx).
    - intro Hfrontier. exists (df_column g t y). split.
      + apply in_map_iff. exists y. split; [reflexivity|].
        destruct Hfrontier as [[p [Hp [Hedge Hdom]]] Hstrict].
        apply (frontier_reach_listed g r y Hgraph (proj1 Htree)).
        eapply frontier_reach_edge; eassumption.
      + exact (proj2 (proj2 (proj2 (df_column_correct g t r y Hgraph Hprepared Htree)) x) Hfrontier).
  Qed.

  Lemma df_unique : forall g t x, NoDup (frontier_row (df g t) x).
  Proof.
    intros g t x. apply df_transpose_unique.
  Qed.

  Lemma idf_spec : forall g t r seeds y,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    In y (idf (df g t) seeds) <-> in_iterated_frontier (base g) r seeds y.
  Proof. Admitted. (* STUB *)

  Lemma idf_unique : forall rows seeds, NoDup (idf rows seeds).
  Proof.
    exact idf_result_unique.
  Qed.
End Frontier.

(** Closed scales reserve lookup, mutation, callback and binary-driver overhead. *)
Definition frontier_unit_cost : N := (PTrieT.c_trie + c_loopN + 1)%N.
Definition frontier_step_cost : N := (64 * frontier_unit_cost)%N.
Definition frontier_column_cost : N := (256 * (c_loopN + 1) * frontier_unit_cost)%N.
Definition frontier_transpose_cost : N := (64 * frontier_unit_cost)%N.
Definition frontier_total_cost : N := (16 * 4096 * (c_loopN + 1) * frontier_unit_cost)%N.

Lemma frontier_positive_add_width : forall p q,
  Pos.size_nat (p + q) <= Pos.size_nat p + Pos.size_nat q.
Proof.
  intros p q. apply Pos.size_nat_least. rewrite Pos2Nat.inj_add, Nat.pow_add_r.
  pose proof (Pos.size_nat_upper p) as Hp. pose proof (Pos.size_nat_upper q) as Hq.
  pose proof (Nat.pow_le_mono_r 2 1 (Pos.size_nat p) ltac:(lia) (Pos.size_nat_pos p)) as Hp2.
  pose proof (Nat.pow_le_mono_r 2 1 (Pos.size_nat q) ltac:(lia) (Pos.size_nat_pos q)) as Hq2.
  change (2 <= Nat.pow 2 (Pos.size_nat p)) in Hp2.
  change (2 <= Nat.pow 2 (Pos.size_nat q)) in Hq2. nia.
Qed.

Lemma frontier_add_width : forall n m,
  N.size_nat (n + m) <= N.size_nat n + N.size_nat m.
Proof.
  intros [|p] [|q]; cbn [N.add N.size_nat]; try lia. apply frontier_positive_add_width.
Qed.

Lemma frontier_four_width : forall n, N.size_nat (4 * n) <= N.size_nat n + 2.
Proof.
  intros [|p]; cbn [N.mul Pos.mul N.size_nat Pos.size_nat]; lia.
Qed.

Lemma frontier_four_time : forall n, (Code.N.T_mul 4 n <= 4)%N.
Proof.
  intros [|p]; time_unfold Code.N.T_mul; try lia.
  do 3 time_unfold Pos.T_mul. time_cbn. lia.
Qed.

Lemma frontier_fuel_width : forall n degree width,
  N.size_nat n <= width ->
  N.size_nat (4 * (n + N.of_nat degree + 1)) <= width + degree + 3.
Proof.
  intros n degree width Hwidth.
  pose proof (frontier_four_width (n + N.of_nat degree + 1)) as Hfour.
  pose proof (frontier_add_width n (N.of_nat degree)) as Hsum.
  pose proof (frontier_add_width (n + N.of_nat degree) 1) as Hlast.
  pose proof (dom_size_value (N.of_nat degree)) as Hdegree.
  change (N.size_nat 1) with 1 in Hlast. lia.
Qed.

(** A nonempty runner performs only a bounded number of key operations. *)
Lemma frontier_df_step_time : forall g t y x rest seen answer width,
  Pos.size_nat x <= width -> Pos.size_nat y <= width ->
  (T_df_step g t y (DfState (x :: rest) seen answer) + c_loopN + 1 <=
    frontier_step_cost * N.of_nat (width + 1))%N.
Proof.
  intros g t y x rest seen answer width Hx Hy.
  apply time_of_nat_le in Hx, Hy.
  pose proof (PTrieT.T_set_le unit x tt seen) as Hset.
  unfold frontier_step_cost, frontier_unit_cost.
  time_unfold T_df_step. time_unfold T_pre. time_unfold T_idom.
  rewrite !PTrieT.trie_get_clock.
  rewrite !Nat2N.inj_add in Hset |- *.
  destruct (trie_get x (pre t)) as [a|]; [|nia].
  destruct (trie_get x seen) as [[]|]; [nia|].
  destruct (trie_get y (idom t)) as [b|].
  - pose proof (Pos.T_eqb_le x b) as Heq.
    destruct (Pos.eqb x b); [nia|]. destruct (trie_get x (idom t)); nia.
  - destruct (trie_get x (idom t)); nia.
Qed.

Lemma frontier_df_stop_time : forall g t y seen answer,
  (T_df_step g t y (DfState [] seen answer) + 1 <= N.of_nat (length answer + 3))%N.
Proof.
  intros g t y seen answer. pose proof (List.T_rev_append_le answer []) as Hreverse.
  time_unfold T_df_step. rewrite Nat2N.inj_add. lia.
Qed.

Lemma frontier_preds_time : forall g y,
  (T_preds g y <= 2 * N.of_nat (Pos.size_nat y) + 1)%N.
Proof.
  intros [graph predecessors vertices_count edges_count] y.
  unfold T_preds. time_simpl. rewrite PTrieT.trie_get_clock. lia.
Qed.

Lemma frontier_nv_width : forall g,
  wf_graph (base g) -> prepared_ok g -> N.size_nat (nv g) <= graph_width (base g).
Proof.
  intros g Hgraph Hprepared.
  apply (dom_distinct_value_width (nodes g) (graph_width (base g)) (nv g)).
  - now apply frontier_nodes_unique.
  - intros v Hv. now apply dom_listed_key_width.
  - destruct Hprepared as [Hnv _]. rewrite Hnv.
    replace (graph_n (base g)) with (length (nodes g)) by
      (destruct g as [[vertices adjacency] predecessors vertices_count edges_count]; reflexivity).
    reflexivity.
Qed.

Lemma df_valid_answer_subset : forall g t r y st,
  wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> df_valid g t y st ->
  incl (df_column_answer st) (df_column g t y).
Proof.
  intros g t r y st Hgraph Hprepared Htree Hvalid x Hx.
  apply (proj2 (proj2 (proj2 (df_column_correct g t r y Hgraph Hprepared Htree)) x)).
  apply (proj1 (df_route_spec g t r x y Hgraph Hprepared Htree)).
  exact (df_valid_answer_routes _ _ _ _ Hvalid x Hx).
Qed.

(** The binary driver charges only actual output-column credit and its fuel width. *)
Lemma frontier_df_loop_time : forall g t r y fuel,
  wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In y (nodes g) ->
  (T_loopN (df_step g t y) (fun st => T_df_step g t y st) fuel
      (DfState (preds g y) Empty []) <=
    c_loopN *
      ((frontier_step_cost * N.of_nat (graph_width (base g) + 1) + 1) *
        N.of_nat (2 * length (df_column g t y) + length (preds g y)) +
       16 * N.of_nat (length (df_column g t y) + 1) +
       N.of_nat (N.size_nat fuel) + 1))%N.
Proof.
  intros g t r y fuel Hgraph Hprepared Htree Hy.
  pose proof (dom_listed_key_width g y Hy) as Hywidth.
  pose proof (T_loopN_le df_state (list positive) (df_step g t y)
    (fun st => T_df_step g t y st) (df_valid g t y)
    (fun st => ((frontier_step_cost * N.of_nat (graph_width (base g) + 1) + 1) *
      N.of_nat (df_column_progress g t y st))%N)
    (16 * N.of_nat (length (df_column g t y) + 1))%N fuel
    (DfState (preds g y) Empty [])) as Hloop.
  cbn beta in Hloop. rewrite df_column_progress_initial in Hloop. apply Hloop.
  - intros [pending seen answer] next Hvalid Hstep.
    split; [eapply df_valid_step; eassumption|].
    pose proof (df_column_progress_step g t r y _ next Hgraph Hprepared Htree Hvalid Hstep)
      as Hprogress.
    destruct pending as [|x rest]; [discriminate Hstep|].
    pose proof (dom_listed_key_width g x
      (df_valid_pending_nodes _ _ _ _ Hvalid x (or_introl eq_refl))) as Hxwidth.
    pose proof (frontier_df_step_time g t y x rest seen answer _ Hxwidth Hywidth) as Htime.
    nia.
  - intros [pending seen answer] result Hvalid Hstep.
    destruct (df_step_stopping g t y _ result Hstep) as [Hpending Hanswer].
    cbn [df_pending] in Hpending. subst pending.
    pose proof (NoDup_incl_length (df_valid_unique _ _ _ _ Hvalid)
      (df_valid_answer_subset g t r y _ Hgraph Hprepared Htree Hvalid)) as Hlength.
    pose proof (frontier_df_stop_time g t y seen answer) as Htime.
    cbn [df_column_answer] in Hlength. rewrite !Nat2N.inj_add in Htime |- *. lia.
  - now apply df_valid_initial.
Qed.

(** Separate the numeric loop estimate from its executable clock expression. *)
Lemma frontier_column_arithmetic : forall overhead scale width degree output,
  (1 <= scale -> 1 <= width ->
   overhead * ((64 * scale * width + 1) * (2 * output + degree) +
      16 * (output + 1) + width + degree + 3) + 16 * (width + degree + 1) <=
    256 * (overhead + 1) * scale * (degree + output + 1) * width)%N.
Proof.
  intros overhead scale width degree output Hscale Hwidth.
  assert (Hproduct : (width <= scale * width)%N) by nia.
  assert (Hpositive : (1 <= scale * width)%N) by nia.
  set (unit := (scale * width)%N) in *.
  replace (64 * scale * width)%N with (64 * unit)%N by (unfold unit; nia).
  replace (256 * (overhead + 1) * scale * (degree + output + 1) * width)%N with
    (256 * (overhead + 1) * unit * (degree + output + 1))%N by (unfold unit; nia).
  assert (Hinside : ((64 * unit + 1) * (2 * output + degree) +
      16 * (output + 1) + width + degree + 3 <=
      192 * unit * (degree + output + 1))%N) by nia.
  assert (Hsetup : (16 * (width + degree + 1) <=
    64 * unit * (degree + output + 1))%N) by nia.
  assert (Hloop : (overhead * ((64 * unit + 1) * (2 * output + degree) +
      16 * (output + 1) + width + degree + 3) <=
    overhead * (192 * unit * (degree + output + 1)))%N).
  { apply N.mul_le_mono_l. exact Hinside. }
  nia.
Qed.

(** Setup includes key width even for an empty column, and each output member is charged once. *)
Lemma frontier_df_column_time : forall g t r y,
  wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In y (nodes g) ->
  (T_df_column g t y + 1 <= frontier_column_cost *
    N.of_nat (length (preds g y) + length (df_column g t y) + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
Proof.
  intros g t r y Hgraph Hprepared Htree Hy.
  pose proof (dom_listed_key_width g y Hy) as Hywidth.
  pose proof (frontier_nv_width g Hgraph Hprepared) as Hnvwidth.
  pose proof (frontier_fuel_width (nv g) (length (preds g y)) _ Hnvwidth) as Hfuelwidth.
  pose proof (frontier_add_width (nv g) (N.of_nat (length (preds g y)))) as Hsumwidth.
  pose proof (dom_size_value (N.of_nat (length (preds g y)))) as Hdegreewidth.
  pose proof (frontier_preds_time g y) as Hpreds.
  pose proof (Datatypes.T_length_le (preds g y)) as Hlength.
  pose proof (dom_time_of_nat (length (preds g y))) as Hconvert.
  pose proof (N.T_add_le (nv g) (N.of_nat (length (preds g y)))) as Hsum.
  pose proof (N.T_add_le (nv g + N.of_nat (length (preds g y))) 1) as Hlast.
  pose proof (frontier_four_time (nv g + N.of_nat (length (preds g y)) + 1)) as Hfour.
  pose proof (frontier_df_loop_time g t r y
    (4 * (nv g + N.of_nat (length (preds g y)) + 1))%N
    Hgraph Hprepared Htree Hy) as Hloop.
  destruct (df_column_finished g t r y Hgraph Hprepared Htree)
    as [st [result [Hvalid [Hstop [Hrun Hcolumn]]]]].
  apply time_of_nat_le in Hywidth, Hnvwidth, Hfuelwidth, Hsumwidth.
  change (N.size_nat 1) with 1 in Hlast.
  repeat rewrite Nat2N.inj_add in Hfuelwidth.
  repeat rewrite Nat2N.inj_add in Hsumwidth.
  repeat rewrite Nat2N.inj_add in Hsum.
  repeat rewrite Nat2N.inj_add in Hlast.
  repeat rewrite Nat2N.inj_add in Hloop.
  repeat rewrite Nat2N.inj_add.
  repeat rewrite Nat2N.inj_mul in Hloop.
  time_unfold T_df_column.
  rewrite Hrun. time_unfold T_nv.
  unfold frontier_column_cost, frontier_step_cost, frontier_unit_cost in Hloop |- *.
  clear Hgraph Hprepared Htree Hy Hvalid Hstop Hrun Hcolumn.
  remember (N.of_nat (graph_width (base g))) as width eqn:Hwidth in *.
  remember (N.of_nat (length (preds g y))) as degree eqn:Hdegree in *.
  remember (N.of_nat (length (df_column g t y))) as output eqn:Houtput in *.
  clear Hwidth Hdegree Houtput.
  match type of Hloop with
  | (?runtime <= _)%N =>
      assert (Hloop_upper : (runtime <= c_loopN *
        ((64 * (PTrieT.c_trie + c_loopN + 1) * (width + 1) + 1) *
          (2 * output + degree) + 16 * (output + 1) + (width + 1) + degree + 3))%N)
  end.
  { eapply N.le_trans; [exact Hloop|]. apply N.mul_le_mono_l.
    clear Hloop Hpreds Hlength Hconvert Hsum Hlast Hfour Hdegreewidth Hywidth Hnvwidth Hsumwidth.
    nia. }
  clear Hloop.
  eapply N.le_trans with (m := (c_loopN *
    ((64 * (PTrieT.c_trie + c_loopN + 1) * (width + 1) + 1) *
      (2 * output + degree) + 16 * (output + 1) + (width + 1) + degree + 3) +
        16 * ((width + 1) + degree + 1))%N).
  - lia.
  - apply frontier_column_arithmetic; lia.
Qed.

(** Varying callback costs sum over precisely the entries passed to a left fold. *)
Lemma frontier_fold_time_sum {A B : Type} (f : A -> B -> A) (T_f : A -> B -> N)
    (cost : B -> N) : forall xs acc,
  (forall x, In x xs -> forall state, (T_f state x <= cost x)%N) ->
  (List.T_fold_left f T_f xs acc <=
    N.of_nat (length xs + 1) + fold_right (fun x total => cost x + total)%N 0%N xs)%N.
Proof.
  intro xs. induction xs as [|x rest IH]; intros acc Hbound.
  - time_unfold List.T_fold_left. cbn [length fold_right]. lia.
  - pose proof (Hbound x (or_introl eq_refl) acc) as Hhead.
    specialize (IH (f acc x) (fun y Hy => Hbound y (or_intror Hy))).
    time_unfold List.T_fold_left. cbn [length fold_right]. try rewrite Nat2N.inj_succ. lia.
Qed.

(** Mapping a clocked function pays its individual calls and one traversal. *)
Lemma frontier_map_time_sum {A B : Type} (f : A -> B) (T_f : A -> N) : forall xs,
  (ListDef.T_map f T_f xs =
    N.of_nat (length xs + 1) + fold_right (fun x total => T_f x + total)%N 0%N xs)%N.
Proof.
  intro xs. induction xs as [|x rest IH].
  - time_unfold ListDef.T_map. reflexivity.
  - time_unfold ListDef.T_map. cbn [length fold_right]. rewrite IH.
    try rewrite Nat2N.inj_succ. lia.
Qed.

Lemma frontier_weighted_sum {A : Type} : forall (xs : list A) (size : A -> nat) (scale : N),
  (fold_right (fun x total => scale * N.of_nat (size x) + total)%N 0%N xs =
    scale * N.of_nat (fold_right (fun x total => (size x + total)%nat) 0%nat xs))%N.
Proof.
  intro xs. induction xs as [|x rest IH]; intros size scale.
  - cbn [fold_right]. lia.
  - cbn [fold_right]. rewrite IH, Nat2N.inj_add. nia.
Qed.

Lemma frontier_sum_le {A : Type} : forall (xs : list A) (f g : A -> N),
  (forall x, In x xs -> (f x <= g x)%N) ->
  (fold_right (fun x total => f x + total)%N 0%N xs <=
    fold_right (fun x total => g x + total)%N 0%N xs)%N.
Proof.
  intro xs. induction xs as [|x rest IH]; intros f g Hbound; [reflexivity|].
  pose proof (Hbound x (or_introl eq_refl)) as Hhead.
  specialize (IH f g (fun y Hy => Hbound y (or_intror Hy))). cbn [fold_right]. lia.
Qed.

Lemma frontier_sum_one_more {A : Type} : forall (xs : list A) (size : A -> nat),
  fold_right (fun x total => size x + 1 + total) 0 xs =
    fold_right (fun x total => size x + total) 0 xs + length xs.
Proof.
  intro xs. induction xs as [|x rest IH]; intro size; [reflexivity|].
  cbn [fold_right length]. rewrite IH. lia.
Qed.

(** Inserting a pair has bounded key cost independently of the accumulated rows. *)
Lemma frontier_df_insert_time : forall y x state width,
  Pos.size_nat x <= width -> Pos.size_nat y <= width ->
  (T_df_insert y x state <= 16 * frontier_unit_cost * N.of_nat (width + 1))%N.
Proof.
  intros y x [rows marks] width Hx Hy. apply time_of_nat_le in Hx, Hy.
  set (marked := match trie_get x marks with Some row => row | None => Empty end).
  pose proof (PTrieT.T_set_le (list positive) x (y :: frontier_row rows x) rows) as Hrows.
  pose proof (PTrieT.T_set_le unit y tt marked) as Hpair.
  pose proof (PTrieT.T_set_le (ptrie unit) x (PTrieCode.set y tt marked) marks) as Hmarks.
  change (PTrieCode.T_set x (y :: frontier_row rows x) rows <=
    PTrieT.c_trie * N.of_nat (Pos.size_nat x + 1))%N in Hrows.
  change (PTrieCode.T_set y tt marked <=
    PTrieT.c_trie * N.of_nat (Pos.size_nat y + 1))%N in Hpair.
  change (PTrieCode.T_set x (PTrieCode.set y tt marked) marks <=
    PTrieT.c_trie * N.of_nat (Pos.size_nat x + 1))%N in Hmarks.
  time_unfold T_df_insert. time_unfold T_frontier_row.
  fold marked. repeat rewrite PTrieT.trie_get_clock.
  unfold frontier_unit_cost. rewrite !Nat2N.inj_add in Hrows, Hpair, Hmarks |- *.
  destruct (trie_get y marked); nia.
Qed.

(** Transposition charges each listed column and each emitted pair with their key width. *)
Lemma frontier_df_transpose_time : forall columns width,
  Forall (fun entry => Pos.size_nat (fst entry) <= width /\
    forall x, In x (snd entry) -> Pos.size_nat x <= width) columns ->
  (T_df_transpose columns + 1 <= frontier_transpose_cost *
    N.of_nat (length columns +
      fold_right (fun entry total => (length (snd entry) + total)%nat) 0%nat columns + 1) *
    N.of_nat (width + 1))%N.
Proof.
  intros columns width Hwidth. rewrite Forall_forall in Hwidth.
  time_unfold T_df_transpose. time_unfold @Datatypes.T_fst.
  match goal with
  | |- context [List.T_fold_left ?f ?Tf columns ?state] =>
      assert (Hfold : (List.T_fold_left f Tf columns state <=
        N.of_nat (length columns + 1) + fold_right (fun entry total =>
          32 * frontier_unit_cost * N.of_nat (width + 1) *
            N.of_nat (length (snd entry) + 1) + total)%N 0%N columns)%N)
  end.
  { apply frontier_fold_time_sum. intros [y xs] Hin [rows marks].
    destruct (Hwidth (y, xs) Hin) as [Hy Hxs]. cbn [fst snd] in Hy, Hxs.
    cbn beta iota zeta. cbn [snd].
    match goal with
    | |- context [List.T_fold_left ?f ?Tf xs ?state] =>
        assert (Hinner : (List.T_fold_left f Tf xs state <=
          (16 * frontier_unit_cost * N.of_nat (width + 1) + 1) *
            N.of_nat (length xs) + 1)%N)
    end.
    { apply dom_time_fold_left. intros x Hx [acc seen].
      pose proof (frontier_df_insert_time y x (acc, seen) width (Hxs x Hx) Hy) as Hinsert.
      unfold T_df_insert, T_frontier_row in Hinsert.
      unfold frontier_row in Hinsert. cbn beta iota zeta in Hinsert |- *.
      destruct (trie_get y (match trie_get x seen with Some row => row | None => Empty end)); lia. }
    unfold frontier_unit_cost in *. rewrite Nat2N.inj_add. nia. }
  rewrite frontier_weighted_sum, frontier_sum_one_more in Hfold.
  unfold frontier_transpose_cost, frontier_unit_cost in *.
  repeat rewrite Nat2N.inj_add in Hfold. repeat rewrite Nat2N.inj_add. nia.
Qed.

Lemma frontier_column_pairs : forall g t r,
  wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
  fold_right (fun y total => length (df_column g t y) + total) 0 (nodes g) = Frontier.df_size g t.
Proof.
  intros g t r Hgraph Hprepared Htree.
  assert (Hnodes : NoDup (nodes g)) by now apply frontier_nodes_unique.
  assert (Htargets : NoDup (map fst (map (fun y => (y, df_column g t y)) (nodes g)))).
  { rewrite map_map. change (NoDup (map (fun y : positive => y) (nodes g))). now rewrite map_id. }
  assert (Hcolumns : Forall (fun entry => NoDup (snd entry) /\ incl (snd entry) (nodes g))
    (map (fun y => (y, df_column g t y)) (nodes g))).
  { apply Forall_forall. intros [y xs] Hin. apply in_map_iff in Hin.
    destruct Hin as [v [Heq Hv]]. injection Heq as Heqv Heqxs. subst v xs.
    pose proof (df_column_correct g t r y Hgraph Hprepared Htree) as [Hunique [Hwithin Hspec]].
    now split. }
  symmetry. change (df_rows_size (nodes g)
    (df_transpose (map (fun y => (y, df_column g t y)) (nodes g))) =
    fold_right (fun y total => length (df_column g t y) + total) 0 (nodes g)).
  rewrite (df_transpose_size _ _ Hnodes Htargets Hcolumns).
  clear Hnodes Htargets Hcolumns Hgraph Hprepared Htree.
  induction (nodes g) as [|y rest IH]; cbn [map fold_right snd]; [reflexivity|now rewrite IH].
Qed.

Lemma frontier_df_columns_time : forall g t r,
  wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
  (fold_right (fun y total => (1 + T_df_column g t y) + total)%N 0%N (nodes g) <=
    frontier_column_cost *
      N.of_nat (graph_n (base g) + graph_e (base g) + Frontier.df_size g t + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
Proof.
  intros g t r Hgraph Hprepared Htree.
  pose proof (frontier_sum_le (nodes g) (fun y => (1 + T_df_column g t y)%N)
    (fun y => ((frontier_column_cost * N.of_nat (graph_width (base g) + 1)) *
      N.of_nat (length (preds g y) + length (df_column g t y) + 1))%N)) as Hsum.
  assert (Hcolumns : forall y, In y (nodes g) ->
    (1 + T_df_column g t y <=
      (frontier_column_cost * N.of_nat (graph_width (base g) + 1)) *
        N.of_nat (length (preds g y) + length (df_column g t y) + 1))%N).
  { intros y Hy. pose proof (frontier_df_column_time g t r y Hgraph Hprepared Htree Hy). nia. }
  specialize (Hsum Hcolumns). cbn beta in Hsum. rewrite frontier_weighted_sum in Hsum.
  rewrite frontier_sum_one_more, frontier_sum_add in Hsum.
  rewrite (frontier_predecessor_sum g Hgraph Hprepared),
    (frontier_column_pairs g t r Hgraph Hprepared Htree) in Hsum.
  replace (length (nodes g)) with (graph_n (base g)) in Hsum by
    (destruct g as [[vertices adjacency] predecessors vertices_count edges_count]; reflexivity).
  repeat rewrite Nat2N.inj_add in Hsum. repeat rewrite Nat2N.inj_add. nia.
Qed.

Lemma frontier_fold_map {A B C : Type} : forall (f : B -> C -> C) (g : A -> B) initial xs,
  fold_right f initial (map g xs) = fold_right (fun x total => f (g x) total) initial xs.
Proof.
  intros f g initial xs. induction xs as [|x rest IH]; cbn [map fold_right]; [reflexivity|].
  now rewrite IH.
Qed.

Lemma frontier_df_rows_time : forall g t r,
  wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
  (T_df_transpose (map (fun y => (y, df_column g t y)) (nodes g)) + 1 <=
    frontier_transpose_cost * N.of_nat (graph_n (base g) + Frontier.df_size g t + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
Proof.
  intros g t r Hgraph Hprepared Htree.
  assert (Hwidth : Forall (fun entry => Pos.size_nat (fst entry) <= graph_width (base g) /\
    forall x, In x (snd entry) -> Pos.size_nat x <= graph_width (base g))
    (map (fun y => (y, df_column g t y)) (nodes g))).
  { apply Forall_forall. intros [y xs] Hin. apply in_map_iff in Hin.
    destruct Hin as [v [Heq Hv]]. injection Heq as Heqv Heqxs. subst v xs.
    split; cbn [fst snd].
    - now apply dom_listed_key_width.
    - intros x Hx. apply dom_listed_key_width.
      exact (proj1 (proj2 (df_column_correct g t r y Hgraph Hprepared Htree)) x Hx). }
  pose proof (frontier_df_transpose_time _ _ Hwidth) as Htime.
  rewrite length_map, frontier_fold_map in Htime. cbn [snd] in Htime.
  rewrite (frontier_column_pairs g t r Hgraph Hprepared Htree) in Htime.
  replace (length (nodes g)) with (graph_n (base g)) in Htime by
    (destruct g as [[vertices adjacency] predecessors vertices_count edges_count]; reflexivity).
  exact Htime.
Qed.

(** The outer constructor adds one traversal and the already bounded column and transpose calls. *)
Lemma frontier_df_wrapper_time : forall g t,
  (T_df g t + 1 <= 16 *
    (N.of_nat (length (nodes g) + 1) +
      fold_right (fun y total => (1 + T_df_column g t y) + total)%N 0%N (nodes g) +
      (1 + T_df_transpose (map (fun y => (y, df_column g t y)) (nodes g)))))%N.
Proof.
  intros g t. time_unfold T_df. time_unfold T_nodes. rewrite frontier_map_time_sum.
  lia.
Qed.

Lemma frontier_time_combine : forall setup columns transpose bound,
  (setup <= bound -> columns <= frontier_column_cost * bound ->
   transpose <= frontier_transpose_cost * bound ->
   16 * (setup + columns + transpose) <= frontier_total_cost * bound)%N.
Proof.
  intros setup columns transpose bound Hsetup Hcolumns Htranspose.
  assert (Hscale : (16 * (1 + frontier_column_cost + frontier_transpose_cost) <=
    frontier_total_cost)%N).
  { unfold frontier_column_cost, frontier_transpose_cost, frontier_total_cost, frontier_unit_cost. nia. }
  assert (Hjoined : (16 * (setup + columns + transpose) <=
    (16 * (1 + frontier_column_cost + frontier_transpose_cost)) * bound)%N) by nia.
  eapply N.le_trans; [exact Hjoined|]. now apply N.mul_le_mono_r.
Qed.

(** Construction pays graph occurrences and its actual emitted frontier pairs. *)
Lemma frontier_df_total_time : forall g t r,
  wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
  (T_df g t + 1 <= frontier_total_cost *
    N.of_nat (graph_n (base g) + graph_e (base g) + Frontier.df_size g t + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
Proof.
  intros g t r Hgraph Hprepared Htree.
  pose proof (frontier_df_wrapper_time g t) as Hwrapper.
  pose proof (frontier_df_columns_time g t r Hgraph Hprepared Htree) as Hcolumns.
  pose proof (frontier_df_rows_time g t r Hgraph Hprepared Htree) as Htranspose.
  rewrite <- N.mul_assoc in Hcolumns |- *.
  eapply N.le_trans; [exact Hwrapper|]. apply frontier_time_combine.
  - replace (length (nodes g)) with (graph_n (base g)) by
      (destruct g as [[vertices adjacency] predecessors vertices_count edges_count]; reflexivity).
    repeat rewrite Nat2N.inj_add. nia.
  - exact Hcolumns.
  - eapply N.le_trans with (m :=
      (frontier_transpose_cost * N.of_nat (graph_n (base g) + Frontier.df_size g t + 1) *
        N.of_nat (graph_width (base g) + 1))%N).
    + lia.
    + rewrite <- N.mul_assoc. apply N.mul_le_mono_l. apply N.mul_le_mono_r.
      repeat rewrite Nat2N.inj_add. lia.
Qed.

(** Iteration preserves an invariant when stopped states remain fixed. *)
Lemma frontier_iter_invariant {S R : Type} (step : S -> S + R)
    (Inv : S -> Prop) :
  (forall st next, Inv st -> step st = inl next -> Inv next) ->
  forall initial, Inv initial -> forall n,
    Inv (Nat.iter n (fun st => match step st with inl next => next | inr _ => st end)
      initial).
Proof.
  intros Hcontinue initial Hinitial n. induction n as [|n IH]; [exact Hinitial|].
  rewrite Nat.iter_succ. destruct (step (Nat.iter n
    (fun st => match step st with inl next => next | inr _ => st end) initial))
    as [next|result] eqn:Hstep; [eapply Hcontinue; eassumption|exact IH].
Qed.

(** Every normal bounded-loop return occurs at a finite deterministic trace position. *)
Lemma frontier_loopN_trace {S R : Type} (step : S -> S + R) : forall fuel initial result,
  loopN step fuel initial = inr result ->
  exists n st,
    Nat.iter n (fun st => match step st with inl next => next | inr _ => st end) initial = st /\
    step st = inr result.
Proof.
  intros fuel initial result Hrun.
  set (advance := fun state => match step state with inl next => next | inr _ => state end).
  assert (Hcontinue : forall st next,
    (exists n, Nat.iter n advance initial = st) -> step st = inl next ->
    exists n, Nat.iter n advance initial = next).
  { intros st next [n Hreach] Hstep. exists (Nat.succ n). rewrite Nat.iter_succ, Hreach.
    unfold advance. now rewrite Hstep. }
  assert (Hstop : forall st answer,
    (exists n, Nat.iter n advance initial = st) -> step st = inr answer ->
    exists n state, Nat.iter n advance initial = state /\ step state = inr answer).
  { intros st answer [n Hreach] Hstep. exists n, st. now split. }
  pose proof (frontier_loopN_invariant step
    (fun st => exists n, Nat.iter n advance initial = st)
    (fun answer => exists n st, Nat.iter n advance initial = st /\ step st = inr answer)
    Hcontinue Hstop fuel initial (ex_intro _ 0 eq_refl)) as Htrace.
  rewrite Hrun in Htrace. exact Htrace.
Qed.

Lemma frontier_iter_fixed {S : Type} (advance : S -> S) : forall st,
  advance st = st -> forall n, Nat.iter n advance st = st.
Proof.
  intros st Hfixed n. induction n as [|n IH]; [reflexivity|].
  rewrite Nat.iter_succ, IH. exact Hfixed.
Qed.

(** Two stopped points on one deterministic trace return exactly the same result. *)
Lemma frontier_trace_result {S R : Type} (step : S -> S + R) :
  forall initial n m st st' result result',
  Nat.iter n (fun state => match step state with inl next => next | inr _ => state end)
    initial = st ->
  Nat.iter m (fun state => match step state with inl next => next | inr _ => state end)
    initial = st' ->
  step st = inr result -> step st' = inr result' -> result = result'.
Proof.
  intros initial n m st st' result result' Hreach Hreach' Hstop Hstop'.
  set (advance := fun state => match step state with inl next => next | inr _ => state end)
    in Hreach, Hreach'.
  assert (Hfixed : advance st = st) by (unfold advance; now rewrite Hstop).
  assert (Hfixed' : advance st' = st') by (unfold advance; now rewrite Hstop').
  assert (Hsame : st = st').
  { transitivity (Nat.iter (m + n) advance initial).
    - rewrite Nat.iter_add, Hreach. symmetry. now apply frontier_iter_fixed.
    - rewrite Nat.add_comm, Nat.iter_add, Hreach'. now apply frontier_iter_fixed. }
  subst st'. congruence.
Qed.

Module FrontierT <: FRONTIER_ALL.
  Include Frontier.

  TimeFun df.
  TimeFun idf.

  Definition c_frontier : N := frontier_total_cost.

  Lemma T_df_le : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    (T_df g t <= c_frontier * N.of_nat
      (graph_n (base g) + graph_e (base g) + df_size g t + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
  Proof.
    intros g t r Hgraph Hprepared Htree.
    pose proof (frontier_df_total_time g t r Hgraph Hprepared Htree) as Hbound.
    change (Frontier.df_size g t) with (df_size g t) in Hbound.
    unfold c_frontier. time_unfold T_df. lia.
  Qed.

  Lemma T_idf_le : forall rows seeds,
    (T_idf rows seeds <= c_frontier * N.of_nat
      (length seeds + idf_work idf rows seeds + 1) *
      N.of_nat (vertex_width
        (seeds ++ flat_map (frontier_row rows) (seeds ++ idf rows seeds)) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma df_bigO : bigO (fun '(g, t, r) =>
      wf_graph (base g) /\ prepared_ok g /\ domtree_exact g r t)
    (fun '(g, t, _) => N.of_nat
      ((graph_n (base g) + graph_e (base g) + df_size g t + 1) *
        (graph_width (base g) + 1))) (fun '(g, t, _) => T_df g t).
  Proof.
    exists c_frontier. intros [[g t] r] [Hgraph [Hprepared Htree]].
    pose proof (T_df_le g t r Hgraph Hprepared Htree) as Hbound.
    rewrite Nat2N.inj_mul. nia.
  Qed.

  Lemma idf_bigO : bigO (fun _ : ptrie (list positive) * list positive => True)
    (fun '(rows, seeds) => N.of_nat
      ((length seeds + idf_work idf rows seeds + 1) *
        (vertex_width (seeds ++ flat_map (frontier_row rows) (seeds ++ idf rows seeds)) + 1)))
    (fun '(rows, seeds) => T_idf rows seeds).
  Proof. Admitted. (* STUB *)

  Definition df_step := df_step.
  TimeFun df_step.
  Definition df_column := df_column.
  TimeFun df_column.
  Definition df_transpose := df_transpose.
  TimeFun df_transpose.
  Definition k_df_step : N := frontier_step_cost.
  Definition k_df_stop : N := 16.
  Definition k_df_column : N := frontier_column_cost.
  Definition k_df_transpose : N := frontier_transpose_cost.
  Definition k_df : N := 16.

  Definition df_initial g y := DfState (preds g y) Empty [].

  Definition df_advance g t y st :=
    match df_step g t y st with
    | inl next => next
    | inr _ => st
    end.

  Definition df_invariant g t y st : Prop :=
    (exists n, Nat.iter n (df_advance g t y) (df_initial g y) = st) /\
    NoDup (df_column_answer st) /\
    (forall x, trie_get x (df_seen st) = Some tt <-> In x (df_column_answer st)) /\
    incl (df_column_answer st) (df_column g t y) /\ incl (df_pending st) (nodes g).

  Definition df_potential g t y st : N :=
    N.of_nat (2 * length (filter (fun x =>
      match trie_get x (df_seen st) with
      | None => true
      | Some _ => false
      end) (df_column g t y)) + length (df_pending st)).

  Definition df_credit g t y st :=
    ((k_df_step * N.of_nat (graph_width (base g) + 1) + 1) *
      df_potential g t y st)%N.

  Definition df_fuel g y : N :=
    (4 * (nv g + N.of_nat (length (preds g y)) + 1))%N.

  Definition df_columns g t : list (positive * list positive) :=
    map (fun y => (y, df_column g t y)) (nodes g).

  Lemma F1_df_initial : forall g t r y,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In y (nodes g) ->
    df_invariant g t y (df_initial g y).
  Proof.
    intros g t r y Hgraph Hprepared Htree Hy.
    refine (conj (ex_intro _ 0 eq_refl) (conj (NoDup_nil _) (conj _ (conj _ _)))).
    - intro x. change (trie_get x Empty = Some tt <-> In x []).
      rewrite PTrie.get_empty. cbn [In]. split; [discriminate|contradiction].
    - exact (@incl_nil_l positive (df_column g t y)).
    - intros x Hx. exact (proj1 (proj1 (frontier_preds_member g y x Hprepared) Hx)).
  Qed.

  Lemma F2_df_step : forall g t r y st next,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In y (nodes g) ->
    df_invariant g t y st -> df_step g t y st = inl next ->
    df_invariant g t y next /\ (df_potential g t y next < df_potential g t y st)%N.
  Proof.
    intros g t r y st next Hgraph Hprepared Htree Hy Hinv Hstep.
    assert (Hvalid : df_valid g t y st).
    { destruct Hinv as [[n <-] Hrest].
      exact (frontier_iter_invariant (df_step g t y) (df_valid g t y)
        (fun state next Hvalid Hstep =>
          df_valid_step g t r y state next Hgraph Htree Hvalid Hstep)
        (df_initial g y) (df_valid_initial g t y Hprepared) n). }
    pose proof (df_valid_step g t r y st next Hgraph Htree Hvalid Hstep) as Hnext.
    split.
    - destruct Hinv as [[n Hreach] Hrest].
      refine (conj _ (conj (df_valid_unique _ _ _ _ Hnext)
        (conj (df_valid_marks _ _ _ _ Hnext) (conj _ _)))).
      + exists (S n). rewrite Nat.iter_succ, Hreach. unfold df_advance. now rewrite Hstep.
      + exact (df_valid_answer_subset g t r y next Hgraph Hprepared Htree Hnext).
      + exact (df_valid_pending_nodes _ _ _ _ Hnext).
    - change (N.of_nat (df_column_progress g t y next) <
        N.of_nat (df_column_progress g t y st))%N.
      pose proof (df_column_progress_step g t r y st next
        Hgraph Hprepared Htree Hvalid Hstep). lia.
  Qed.

  Lemma F3_df_stop : forall g t r y st result,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In y (nodes g) ->
    df_invariant g t y st -> df_step g t y st = inr result ->
    df_pending st = [] /\ result = rev (df_column_answer st) /\ result = df_column g t y.
  Proof.
    intros g t r y st result Hgraph Hprepared Htree Hy [[n Hreach] Hrest] Hstep.
    destruct (df_step_stopping g t y st result Hstep) as [Hpending Hresult].
    split; [exact Hpending|]. split; [exact Hresult|].
    destruct (df_column_finished g t r y Hgraph Hprepared Htree)
      as [finished [answer [Hvalid [Hstop [Hrun Hcolumn]]]]].
    destruct (frontier_loopN_trace (df_step g t y) _ _ _ Hrun)
      as [m [finished' [Hreach' Hstop']]].
    unfold df_column. rewrite Hcolumn. exact (frontier_trace_result (df_step g t y)
      (df_initial g y) n m st finished' result answer Hreach Hreach' Hstep Hstop').
  Qed.

  Lemma F4_df_driver : forall g t r y,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In y (nodes g) ->
    loopN (df_step g t y) (df_fuel g y) (df_initial g y) = inr (df_column g t y).
  Proof.
    intros g t r y Hgraph Hprepared Htree Hy.
    destruct (df_column_finished g t r y Hgraph Hprepared Htree)
      as [st [result [Hvalid [Hstop [Hrun Hcolumn]]]]].
    exact (eq_trans Hrun (f_equal (fun answer : list positive =>
      @inr df_state (list positive) answer) (eq_sym Hcolumn))).
  Qed.

  Lemma F5_df_column : forall g t r y,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    NoDup (df_column g t y) /\ incl (df_column g t y) (nodes g) /\
      forall x, In x (df_column g t y) <-> in_frontier (base g) r x y.
  Proof.
    exact df_column_correct.
  Qed.

  Lemma F6_df_transpose : forall columns x y,
    In y (frontier_row (df_transpose columns) x) <->
      exists column, In (y, column) columns /\ In x column.
  Proof.
    exact df_transpose_member.
  Qed.

  Lemma F7_df_equation : forall g t, df g t = df_transpose (df_columns g t).
  Proof.
    reflexivity.
  Qed.

  Lemma F8_df_pairs : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    fold_right (fun entry n => length (snd entry) + n) 0 (df_columns g t) = df_size g t.
  Proof.
    intros g t r Hgraph Hprepared Htree.
    assert (Hnodes : NoDup (nodes g)).
    { destruct g as [[vertices adjacency] predecessors vertices_count edges_count].
      exact (proj1 Hgraph). }
    symmetry. change (df_rows_size (nodes g) (df_transpose (df_columns g t)) =
      fold_right (fun entry n => length (snd entry) + n) 0 (df_columns g t)).
    apply df_transpose_size; [exact Hnodes| |].
    - unfold df_columns. rewrite map_map.
      change (NoDup (map (fun y : positive => y) (nodes g))). now rewrite map_id.
    - apply Forall_forall. intros [y xs] Hin.
      unfold df_columns in Hin. apply in_map_iff in Hin.
      destruct Hin as [v [Heq Hv]]. injection Heq as Heqv Heqxs. subst v xs.
      pose proof (df_column_correct g t r y Hgraph Hprepared Htree) as [Hunique [Hwithin Hspec]].
      now split.
  Qed.

  Lemma T1_df_step : forall g t r y st next,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In y (nodes g) ->
    df_invariant g t y st -> df_step g t y st = inl next ->
    (T_df_step g t y st + df_credit g t y next + c_loopN <= df_credit g t y st)%N.
  Proof.
    intros g t r y st next Hgraph Hprepared Htree Hy Hinv Hstep.
    pose proof (proj2 (F2_df_step g t r y st next
      Hgraph Hprepared Htree Hy Hinv Hstep)) as Hdecrease.
    destruct Hinv as [Hreach [Hunique [Hmarks [Hsubset Hpending]]]].
    destruct st as [pending seen answer]. destruct pending as [|x rest];
      [discriminate Hstep|].
    pose proof (dom_listed_key_width g y Hy) as Hywidth.
    pose proof (dom_listed_key_width g x (Hpending x (or_introl eq_refl))) as Hxwidth.
    pose proof (frontier_df_step_time g t y x rest seen answer
      (graph_width (base g)) Hxwidth Hywidth) as Htime.
    unfold df_credit, k_df_step. time_unfold T_df_step. nia.
  Qed.

  Lemma T2_df_stop : forall g t r y st result,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In y (nodes g) ->
    df_invariant g t y st -> df_step g t y st = inr result ->
    (T_df_step g t y st <= k_df_stop * N.of_nat (length (df_column g t y) + 1))%N.
  Proof.
    intros g t r y st result Hgraph Hprepared Htree Hy Hinv Hstep.
    destruct (df_step_stopping g t y st result Hstep) as [Hpending Hresult].
    destruct Hinv as [Hreach [Hunique [Hmarks [Hsubset Hnodes]]]].
    assert (Hlength : length (df_column_answer st) <= length (df_column g t y)).
    { eapply NoDup_incl_length; eassumption. }
    destruct st as [pending seen answer]. cbn [df_pending df_column_answer] in Hpending, Hlength.
    subst pending. pose proof (frontier_df_stop_time g t y seen answer) as Htime.
    unfold k_df_stop. time_unfold T_df_step.
    repeat rewrite Nat2N.inj_add in Htime. repeat rewrite Nat2N.inj_add. lia.
  Qed.

  Lemma T3_df_loop : forall g t r y,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In y (nodes g) ->
    (T_df_column g t y <= k_df_column *
      (df_credit g t y (df_initial g y) +
        k_df_stop * N.of_nat (length (df_column g t y) + 1) +
        N.of_nat (length (preds g y) + N.size_nat (df_fuel g y) + 1)))%N.
  Proof. Admitted. (* PLAN-DEFECT: take a single isolated root y with arbitrarily many key bits,
     prepared predecessor map Empty and its exact one-node tree. The column and
     initial credit are empty, and fuel is 8, so this bound has constant RHS.
     Each predecessor lookup costs 2 * Pos.size_nat y even on Empty. A private
     column bound must also charge graph_width for this setup work. *)

  Lemma T4_df_columns : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    (fold_right (fun y cost => T_df_column g t y + cost)%N 0%N (nodes g) <=
      k_df_column * N.of_nat
        (graph_n (base g) + graph_e (base g) + df_size g t + 1) *
        N.of_nat (graph_width (base g) + 1))%N.
  Proof.
    intros g t r Hgraph Hprepared Htree.
    exact (frontier_df_columns_time g t r Hgraph Hprepared Htree).
  Qed.

  Lemma T5_df_transpose : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    (T_df_transpose (df_columns g t) <= k_df_transpose *
      N.of_nat (graph_n (base g) + df_size g t + 1) *
        N.of_nat (graph_width (base g) + 1))%N.
  Proof.
    intros g t r Hgraph Hprepared Htree.
    pose proof (frontier_df_rows_time g t r Hgraph Hprepared Htree) as Hbound.
    change (Frontier.df_size g t) with (df_size g t) in Hbound.
    unfold k_df_transpose, df_columns, df_column. time_unfold T_df_transpose. lia.
  Qed.

  Lemma T6_df_wrapper : forall g t,
    (T_df g t <= k_df * (N.of_nat (length (nodes g) + 1) +
      fold_right (fun y cost => T_df_column g t y + cost)%N 0%N (nodes g) +
      T_df_transpose (df_columns g t)))%N.
  Proof.
    intros g t. pose proof (frontier_df_wrapper_time g t) as Hbound.
    unfold k_df, df_columns, df_column. time_unfold T_df. time_unfold T_df_transpose.
    unfold T_df_column. lia.
  Qed.

  Lemma T7_df_public : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    (T_df g t <= c_frontier *
      N.of_nat (graph_n (base g) + graph_e (base g) + df_size g t + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
  Proof.
    exact T_df_le.
  Qed.

  Definition idf_step := idf_step.
  TimeFun idf_step.
  Definition idf_walk := idf.
  TimeFun idf_walk.
  Definition k_idf_step : N := 1. (* STUB *)
  Definition k_idf_stop : N := 1. (* STUB *)
  Definition k_idf_walk : N := 1. (* STUB *)

  Definition idf_initial (seeds : list positive) : idf_state :=
    IdfState (map IdfSeed seeds) Empty Empty [].

  Definition idf_advance rows st :=
    match idf_step rows st with
    | inl next => next
    | inr _ => st
    end.

  Definition idf_reachable rows seeds st : Prop :=
    exists n, Nat.iter n (idf_advance rows) (idf_initial seeds) = st.

  Definition idf_task_supported rows seeds task : Prop :=
    match task with
    | IdfSeed v => In v seeds
    | IdfTarget v => in_row_closure rows seeds v
    end.

  Definition idf_invariant rows seeds st : Prop :=
    idf_reachable rows seeds st /\ NoDup (idf_answer st) /\
    (forall v, trie_get v (idf_discovered st) = Some tt <-> In v (idf_answer st)) /\
    (forall v, In v (idf_answer st) -> in_row_closure rows seeds v) /\
    (forall v, trie_get v (idf_expanded st) = Some tt ->
      In v seeds \/ in_row_closure rows seeds v) /\
    Forall (idf_task_supported rows seeds) (idf_pending st).

  Definition idf_support rows seeds : list positive :=
    nodup Pos.eq_dec (seeds ++ idf rows seeds).

  Definition idf_white rows seeds st : nat :=
    fold_right (fun v n =>
      match trie_get v (idf_expanded st) with
      | None => 2 + length (frontier_row rows v) + n
      | Some _ => n
      end) 0 (idf_support rows seeds).

  Definition idf_potential rows seeds st : N :=
    N.of_nat (2 * idf_white rows seeds st + length (idf_pending st)).

  Definition idf_width rows seeds : nat :=
    vertex_width (seeds ++ flat_map (frontier_row rows) (seeds ++ idf rows seeds)).

  Definition idf_credit rows seeds st : N :=
    ((k_idf_step * N.of_nat (idf_width rows seeds + 1) + 1) *
      idf_potential rows seeds st)%N.

  Definition idf_guard rows seeds := { st : idf_state | idf_invariant rows seeds st }.

  Definition idf_guard_state {rows seeds} (st : idf_guard rows seeds) : idf_state :=
    match st with
    | exist _ state _ => state
    end.
  TimeFun idf_guard_state.

  Definition idf_decreases rows seeds (next st : idf_guard rows seeds) : Prop :=
    (idf_potential rows seeds (proj1_sig next) <
      idf_potential rows seeds (proj1_sig st))%N.

  Definition idf_loop_credit rows seeds (st : idf_guard rows seeds) : N :=
    (k_idf_walk * idf_credit rows seeds (proj1_sig st))%N.

  Lemma F1_idf_finite : forall rows seeds,
    exists universe, NoDup universe /\ incl seeds universe /\
      forall x y, In y (frontier_row rows x) -> In y universe.
  Proof.
    intros rows seeds. exists (idf_universe rows seeds). apply idf_universe_contains.
  Qed.

  Lemma F2_idf_done : forall rows seeds,
    exists n st result,
      Nat.iter n (idf_advance rows) (idf_initial seeds) = st /\
      idf_step rows st = inr result /\ result = idf_walk rows seeds.
  Proof. Admitted. (* STUB *)

  Lemma F3_idf_closure : forall rows seeds y,
    In y (idf_walk rows seeds) <-> in_row_closure rows seeds y.
  Proof. Admitted. (* STUB *)

  Lemma F4_idf_equation : forall rows seeds, idf rows seeds = idf_walk rows seeds.
  Proof.
    reflexivity.
  Qed.

  Lemma F5_idf_transport : forall g t r seeds y,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    (in_row_closure (df g t) seeds y <-> in_iterated_frontier (base g) r seeds y).
  Proof.
    intros g t r seeds y Hgraph Hprepared Htree. split; intro Hclosure.
    - induction Hclosure as [x y Hseed Hrow|x y Hprevious IH Hrow].
      + apply frontier_seed with x; [exact Hseed|].
        now apply (proj1 (df_spec g t r x y Hgraph Hprepared Htree)).
      + apply frontier_step with x; [exact IH|].
        now apply (proj1 (df_spec g t r x y Hgraph Hprepared Htree)).
    - induction Hclosure as [x y Hseed Hfrontier|x y Hprevious IH Hfrontier].
      + apply row_seed with x; [exact Hseed|].
        now apply (proj2 (df_spec g t r x y Hgraph Hprepared Htree)).
      + apply row_step with x; [exact IH|].
        now apply (proj2 (df_spec g t r x y Hgraph Hprepared Htree)).
  Qed.

  Lemma F6_idf_initial : forall rows seeds,
    idf_invariant rows seeds (idf_initial seeds).
  Proof.
    intros rows seeds. unfold idf_invariant, idf_reachable, idf_initial.
    cbn [idf_answer idf_discovered idf_expanded idf_pending].
    split; [exists 0; reflexivity|]. split; [constructor|]. split.
    - intro v. rewrite PTrie.get_empty. cbn [In]. split; [discriminate|contradiction].
    - split; [intros v Hfalse; contradiction|]. split.
      + intros v Hget. rewrite PTrie.get_empty in Hget. discriminate.
      + apply Forall_forall. intros task Hin. apply in_map_iff in Hin.
        destruct Hin as [v [<- Hv]]. exact Hv.
  Qed.

  Lemma F7_idf_step : forall rows seeds st next,
    idf_invariant rows seeds st -> idf_step rows st = inl next ->
    idf_invariant rows seeds next /\
      (idf_potential rows seeds next < idf_potential rows seeds st)%N.
  Proof. Admitted. (* STUB *)

  Definition idf_checked_step rows seeds (st : idf_guard rows seeds) :
      { next : idf_guard rows seeds | idf_decreases rows seeds next st } + list positive :=
    let state := idf_guard_state st in
    match idf_step rows state as result
      return idf_step rows state = result ->
        { next : idf_guard rows seeds | idf_decreases rows seeds next st } + list positive
    with
    | inl next => fun Hstep =>
      let Hstep_inv := F7_idf_step rows seeds state next (proj2_sig st) Hstep in
      inl (exist _ (exist _ next (proj1 Hstep_inv)) (proj2 Hstep_inv))
    | inr result => fun _ => inr result
    end eq_refl.
  TimeFun idf_checked_step.

  Lemma F8_idf_stop : forall rows seeds st result,
    idf_invariant rows seeds st -> idf_step rows st = inr result ->
    idf_pending st = [] /\ result = rev (idf_answer st) /\ result = idf rows seeds.
  Proof. Admitted. (* STUB *)

  Lemma F8a_idf_checked : forall rows seeds st,
    match idf_checked_step rows seeds st with
    | inl next => inl (proj1_sig (proj1_sig next))
    | inr result => inr result
    end = idf_step rows (proj1_sig st).
  Proof. Admitted. (* STUB *)

  Lemma F8b_idf_accessible : forall rows seeds st,
    Acc (idf_decreases rows seeds) st.
  Proof.
    intros rows seeds st.
    exact (Wellfounded.Inverse_Image.wf_inverse_image _ N N.lt
      (fun state => idf_potential rows seeds (proj1_sig state)) N.lt_wf_0 st).
  Qed.

  Lemma F8c_idf_loop : forall rows seeds,
    idf_walk rows seeds = Argent.Loop.loop (idf_decreases rows seeds)
      (idf_checked_step rows seeds)
      (exist _ (idf_initial seeds) (F6_idf_initial rows seeds))
      (F8b_idf_accessible rows seeds _).
  Proof. Admitted. (* STUB *)

  Lemma F9_idf_output : forall rows seeds,
    length (idf rows seeds) <= idf_work idf rows seeds.
  Proof. Admitted. (* STUB *)

  Lemma F10_idf_credit : forall rows seeds,
    (idf_potential rows seeds (idf_initial seeds) <=
      7 * N.of_nat (length seeds + idf_work idf rows seeds + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T1_idf_step : forall rows seeds st next,
    idf_invariant rows seeds st -> idf_step rows st = inl next ->
    (T_idf_step rows st + idf_credit rows seeds next <
      idf_credit rows seeds st)%N.
  Proof. Admitted. (* STUB *)

  Lemma T2_idf_stop : forall rows seeds st result,
    idf_invariant rows seeds st -> idf_step rows st = inr result ->
    (T_idf_step rows st <= k_idf_stop * N.of_nat (length (idf rows seeds) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T2a_idf_checked_step : forall rows seeds st next Hnext,
    idf_checked_step rows seeds st = inl (exist _ next Hnext) ->
    (T_idf_checked_step rows seeds st + idf_loop_credit rows seeds next <
      idf_loop_credit rows seeds st)%N.
  Proof. Admitted. (* STUB *)

  Lemma T2b_idf_checked_stop : forall rows seeds st result,
    idf_checked_step rows seeds st = inr result ->
    (T_idf_checked_step rows seeds st <=
      k_idf_walk * (k_idf_stop * N.of_nat (length (idf rows seeds) + 1) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T2c_idf_loop : forall rows seeds st Hacc,
    (Argent.Loop.T_loop (idf_decreases rows seeds) (idf_checked_step rows seeds)
      (T_idf_checked_step rows seeds) st Hacc <= idf_loop_credit rows seeds st +
      k_idf_walk * (k_idf_stop * N.of_nat (length (idf rows seeds) + 1) + 1) + 1)%N.
  Proof. Admitted. (* STUB *)

  Lemma T3_idf_walk : forall rows seeds,
    (T_idf_walk rows seeds <= k_idf_walk *
      (idf_credit rows seeds (idf_initial seeds) +
        k_idf_stop * N.of_nat (length (idf rows seeds) + 1) +
        N.of_nat (length seeds) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T4_idf_wrapper : forall rows seeds,
    (T_idf rows seeds <= k_idf_walk * (T_idf_walk rows seeds + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T5_idf_public : forall rows seeds,
    (T_idf rows seeds <= c_frontier *
      N.of_nat (length seeds + idf_work idf rows seeds + 1) *
      N.of_nat (idf_width rows seeds + 1))%N.
  Proof. Admitted. (* STUB *)
End FrontierT.
