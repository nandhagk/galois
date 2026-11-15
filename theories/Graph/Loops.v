(** * Natural loop forests

    Dominator-tree traversal classifies back edges and builds their reverse closures.
    For example, a self-edge produces a one-vertex natural loop.
    Builds on: prepared graphs, dominator trees and depth-first traces. *)

From Stdlib Require Import PArith NArith Arith Lia List Bool.
From Stdlib.Sorting Require Import Permutation.
From Argent Require Import Time Tactics Std BigO Loop.
From Galois.Base Require Import Trie Loop.
From Galois.Graph Require Import Data Spec DigraphSig SearchSig Search DomSig LoopsSig.
Import List.ListNotations.

Definition loop_tail {A : Type} (xs : list A) : list A :=
  match xs with
  | [] => []
  | _ :: rest => rest
  end.
TimeFun loop_tail.

Definition loop_first (xs : list positive) : list positive :=
  match xs with
  | [] => []
  | x :: _ => [x]
  end.
TimeFun loop_first.

(** Root discovery takes the same singleton prefix as the public plan. *)
Local Lemma loop_first_equation : forall xs, loop_first xs = firstn 1 xs.
Proof.
  intros [|v rest]; reflexivity.
Qed.

Local Lemma loop_first_head : forall (xs : list positive) r,
  hd_error xs = Some r -> firstn 1 xs = [r].
Proof.
  intros [|v rest] r Hhead; [discriminate|].
  cbn in Hhead. injection Hhead as <-. reflexivity.
Qed.

(** The singleton-prefix helper has a uniform derived cost. *)
Local Lemma loop_first_clock_bound : forall xs, (T_loop_first xs <= 4)%N.
Proof.
  intros [|v rest]; unfold T_loop_first; time_simpl; lia.
Qed.

Definition tree_step (g : prepared) (t : domtree) (st : loop_tree_state) :
    loop_tree_state + loop_scan :=
  match st with
  | LoopTreeState [] _ _ (LoopScan order latches backs) =>
    inr (LoopScan (rev_append order []) latches backs)
  | LoopTreeState (task :: rest) stack active scan =>
    match task with
    | LoopTreeRoot v =>
      match trie_get v (pre t), trie_get v (idom t) with
      | Some _, None => inl (LoopTreeState (LoopTreeEnter v :: rest) stack active scan)
      | _, _ => inl (LoopTreeState rest stack active scan)
      end
    | LoopTreeEnter v =>
      let '(LoopScan order latches backs) := scan in
      inl (LoopTreeState
        (LoopTreeEdges v (succs (base g) v) :: LoopTreeChildren (children t v) ::
          LoopTreeLeave v :: rest) (v :: stack) (PTrieCode.set v tt active)
        (LoopScan (v :: order) latches backs))
    | LoopTreeChildren [] => inl (LoopTreeState rest stack active scan)
    | LoopTreeChildren (v :: vs) =>
      inl (LoopTreeState (LoopTreeEnter v :: LoopTreeChildren vs :: rest) stack active scan)
    | LoopTreeEdges _ [] => inl (LoopTreeState rest stack active scan)
    | LoopTreeEdges u (v :: vs) =>
      match trie_get v active with
      | None => inl (LoopTreeState (LoopTreeEdges u vs :: rest) stack active scan)
      | Some _ =>
        let '(LoopScan order latches backs) := scan in
        let sources := match trie_get v latches with Some xs => xs | None => [] end in
        let row := match trie_get u backs with Some xs => xs | None => Empty end in
        inl (LoopTreeState (LoopTreeEdges u vs :: rest) stack active
          (LoopScan order (PTrieCode.set v (u :: sources) latches)
            (PTrieCode.set u (PTrieCode.set v tt row) backs)))
      end
    | LoopTreeLeave v =>
      inl (LoopTreeState rest (loop_tail stack) (PTrieCode.remove v active) scan)
    end
  end.
TimeFun tree_step.

Definition classify (g : prepared) (t : domtree) : loop_scan :=
  let initial := LoopTreeState (map LoopTreeRoot (nodes g)) [] Empty (LoopScan [] Empty Empty) in
  match loopN (tree_step g t) (8 * (nv g + ne g + 1))%N initial with
  | inl st => let '(LoopScan order latches backs) := loop_tree_output st in
      LoopScan (rev_append order []) latches backs
  | inr scan => scan
  end.
TimeFun classify.

Definition body_step (g : prepared) (t : domtree) (_ : positive) (st : loop_body_state) :
    loop_body_state + list positive :=
  match st with
  | LoopBodyState [] _ answer => inr (rev_append answer [])
  | LoopBodyState (v :: rest) seen answer =>
    match trie_get v seen, trie_get v (pre t) with
    | None, Some _ =>
      inl (LoopBodyState (filter (fun u => match trie_get u (pre t) with
        | Some _ => true
        | None => false
        end) (preds g v) ++ rest) (PTrieCode.set v tt seen) (v :: answer))
    | _, _ => inl (LoopBodyState rest seen answer)
    end
  end.
TimeFun body_step.

Definition collect (g : prepared) (t : domtree) (h : positive) (sources : list positive) :=
  let initial := LoopBodyState sources (PTrieCode.set h tt Empty) [h] in
  match loopN (body_step g t h) (4 * (nv g + ne g + N.of_nat (length sources) + 1))%N initial with
  | inl st => rev_append (loop_body_answer st) []
  | inr answer => answer
  end.
TimeFun collect.

Definition loop_header_map (l : loops) : ptrie positive :=
  match l with
  | Loops headers _ _ => headers
  end.
TimeFun loop_header_map.

Definition loop_parent_map (l : loops) : ptrie positive :=
  match l with
  | Loops _ parents _ => parents
  end.
TimeFun loop_parent_map.

Definition loop_body_map (l : loops) : ptrie (list positive) :=
  match l with
  | Loops _ _ bodies => bodies
  end.
TimeFun loop_body_map.

Definition install (l : loops) (entry : positive * list positive) : loops :=
  let '(h, vs) := entry in
  let outer := match trie_get h (loop_header_map l) with
    | Some p => PTrieCode.set h p (loop_parent_map l)
    | None => loop_parent_map l
    end in
  Loops (fold_left (fun owners v => PTrieCode.set v h owners) vs (loop_header_map l)) outer
    (PTrieCode.set h vs (loop_body_map l)).
TimeFun install.

Definition assemble (rows : list (positive * list positive)) :=
  fold_left install rows (Loops Empty Empty Empty).
TimeFun assemble.

(** Assembly unfolds without reducing the computation that supplied its rows. *)
Local Lemma loop_assemble_equation : forall rows,
  assemble rows = fold_left install rows (Loops Empty Empty Empty).
Proof.
  reflexivity.
Qed.

Definition test_back (rows : ptrie (ptrie unit)) (es : list event) : bool :=
  forallb (fun e => match e with
    | Edge Back u v => match trie_get u rows with
      | Some row => match trie_get v row with Some _ => true | None => false end
      | None => false
      end
    | _ => true
    end) es.
TimeFun test_back.

(** Successor order fixes both the emitted trace and the final visited list. *)
Scheme loop_dfs_visit_ind := Induction for dfs_visit Sort Prop
with loop_dfs_rows_ind := Induction for dfs_rows Sort Prop.
Combined Scheme loop_dfs_ind from loop_dfs_visit_ind, loop_dfs_rows_ind.

Local Lemma loop_dfs_deterministic (g : digraph) :
  (forall active seen v es final, dfs_visit g active seen v es final ->
    forall es' final', dfs_visit g active seen v es' final' -> es = es' /\ final = final') /\
  (forall active seen u vs es final, dfs_rows g active seen u vs es final ->
    forall es' final', dfs_rows g active seen u vs es' final' -> es = es' /\ final = final').
Proof.
  apply loop_dfs_ind.
  - intros active seen v inside final Hfresh Hrows IH es' final' Hother.
    inversion Hother as [active' seen' v' inside' final'' Hfresh' Hrows']; subst.
    destruct (IH _ _ Hrows') as [-> ->]. split; reflexivity.
  - intros active seen u es' final' Hother.
    inversion Hother. split; reflexivity.
  - intros active seen u v rest inside middle outside final Hfresh Hvisit IHvisit
      Hrows IHrows es' final' Hother.
    inversion Hother as [|active' seen' u' v' rest' inside' middle' outside' final''
      Hfresh' Hvisit' Hrows'|active' seen' u' v' rest' kind' outside' final''
      Hseen' Hkind' Hrows']; subst.
    + destruct (IHvisit _ _ Hvisit') as [Hinside Hmiddle]. subst inside' middle'.
      destruct (IHrows _ _ Hrows') as [-> ->]. split; reflexivity.
    + contradiction.
  - intros active seen u v rest kind outside final Hseen Hkind Hrows IH
      es' final' Hother.
    inversion Hother as [|active' seen' u' v' rest' inside' middle' outside' final''
      Hfresh' Hvisit' Hrows'|active' seen' u' v' rest' kind' outside' final''
      Hseen' Hkind' Hrows']; subst.
    + contradiction.
    + assert (Hsame : kind = kind').
      { destruct Hkind as [[-> Hin]|[-> Hnot]], Hkind' as [[-> Hin']|[-> Hnot']];
          try reflexivity; contradiction. }
      subst kind'. destruct (IH _ _ Hrows') as [-> ->]. split; reflexivity.
Qed.

Local Lemma loop_dfs_roots_deterministic : forall g seen roots es final,
  dfs_roots g seen roots es final ->
  forall es' final', dfs_roots g seen roots es' final' -> es = es' /\ final = final'.
Proof.
  intros g seen roots es final Hdfs.
  induction Hdfs as [seen|seen v rest es final Hseen Hrest IH|
    seen v rest inside middle outside final Hfresh Hvisit Hrest IH];
    intros es' final' Hother.
  - inversion Hother. split; reflexivity.
  - inversion Hother as [|seen' v' rest' es'' final'' Hseen' Hrest'|
      seen' v' rest' inside' middle' outside' final'' Hfresh' Hvisit' Hrest']; subst.
    + now apply IH.
    + contradiction.
  - inversion Hother as [|seen' v' rest' es'' final'' Hseen' Hrest'|
      seen' v' rest' inside' middle' outside' final'' Hfresh' Hvisit' Hrest']; subst.
    + contradiction.
    + destruct (proj1 (loop_dfs_deterministic g) [] seen v inside middle Hvisit
        inside' middle' Hvisit') as [Hinside Hmiddle].
      subst inside' middle'. destruct (IH _ _ Hrest') as [-> ->]. split; reflexivity.
Qed.

(** Search's trace laws do not depend on which visitor observes the events. *)
Module LoopTraceVisitor <: VISITOR.
  Definition state := unit.
  Definition enter (_ : positive) (s : state) := s.
  Definition leave (_ : positive) (s : state) := s.
  Definition edge (_ : edge_kind) (_ _ : positive) (s : state) := s.
  TimeFun enter.
  TimeFun leave.
  TimeFun edge.
End LoopTraceVisitor.

Module LoopTrace := Galois.Graph.Search.Search LoopTraceVisitor.

Local Opaque Acc_intro_generator.

Local Lemma loop_trace_valid : forall g roots,
  counts_ok g -> wf_graph (base g) ->
  (forall r, In r roots -> In r (nodes g)) ->
  exists final, dfs_roots (base g) [] roots (prepared_search_trace g roots) final.
Proof.
  intros g roots Hcounts Hgraph Hlisted.
  pose proof (LoopTrace.trace_depth_first g roots Hcounts Hgraph Hlisted) as Htrace.
  cbv beta delta [LoopTrace.trace] in Htrace. exact Htrace.
Qed.

Local Lemma loop_tree_root_listed : forall g r t,
  domtree_exact g r t -> In r (nodes g).
Proof.
  intros [[vertices successors] predecessors n e] r t Htree. exact (proj1 Htree).
Qed.

(** Simple paths expose the order of dominators without assumptions on raw graphs. *)
Local Lemma loop_path_start : forall g a xs b, path g a xs b -> In a xs.
Proof.
  intros g a xs b Hpath. destruct Hpath; now left.
Qed.

Local Lemma loop_path_end : forall g a xs b, path g a xs b -> In b xs.
Proof.
  intros g a xs b Hpath. induction Hpath; [now left|now right].
Qed.

Local Lemma loop_path_join : forall g a xs b ys c,
  path g a xs b -> path g b ys c ->
  exists zs, path g a zs c /\ forall x, In x zs -> In x xs \/ In x ys.
Proof.
  intros g a xs b ys c Hfirst. revert ys c.
  induction Hfirst as [b|a v xs b Hedge Hpath IH]; intros ys c Hlast.
  - exists ys. split; [exact Hlast|]. intros x Hin. now right.
  - destruct (IH ys c Hlast) as [zs [Hz Hmembers]].
    exists (a :: zs). split; [now apply path_step with v|].
    intros x [<-|Hin]; [left; now left|].
    destruct (Hmembers x Hin) as [Hleft|Hright]; [left; now right|now right].
Qed.

Local Lemma loop_path_snoc : forall g a xs b c,
  path g a xs b -> edge g b c -> path g a (xs ++ [c]) c.
Proof.
  intros g a xs b c Hpath. induction Hpath as [v|u v xs w Hfirst Hpath IH]; intro Hedge.
  - cbn. apply path_step with c; [exact Hedge|constructor].
  - cbn. apply path_step with v; [exact Hfirst|now apply IH].
Qed.

Local Lemma loop_path_split : forall g a xs b,
  path g a xs b -> forall x, In x xs ->
  exists before after, xs = before ++ after /\
    path g a (before ++ [x]) x /\ path g x after b.
Proof.
  intros g a xs b Hpath.
  induction Hpath as [v|a v xs b Hedge Hpath IH]; intros x Hin.
  - destruct Hin as [<-|Hin]; [|contradiction].
    exists [], [v]. split; [reflexivity|]. split; constructor.
  - destruct Hin as [<-|Hin].
    + exists [], (a :: xs). split; [reflexivity|].
      split; [constructor|now apply path_step with v].
    + destruct (IH x Hin) as [before [after [Hxs [Hprefix Hsuffix]]]].
      exists (a :: before), after. split; [now cbn; rewrite Hxs|].
      split; [cbn; now apply path_step with v|exact Hsuffix].
Qed.

Local Lemma loop_nodup_disjoint : forall (before after : list positive),
  NoDup (before ++ after) -> forall x, In x before -> ~ In x after.
Proof.
  intros before. induction before as [|v before IH]; intros after Hunique x Hin.
  - contradiction.
  - cbn in Hunique. inversion Hunique as [|head tail Hfresh Hrest]; subst.
    destruct Hin as [<-|Hin].
    + intro Hafter. apply Hfresh, in_or_app. now right.
    + now apply (IH after Hrest x Hin).
Qed.

Local Lemma loop_path_simple : forall g a xs b,
  path g a xs b -> exists ys, path g a ys b /\ NoDup ys.
Proof.
  intros g a xs b Hpath.
  induction Hpath as [v|a v xs b Hedge Hpath IH].
  - exists [v]. split; [constructor|]. constructor; [simpl; tauto|constructor].
  - destruct IH as [ys [Hys Hunique]].
    destruct (in_dec Pos.eq_dec a ys) as [Hin|Hfresh].
    + destruct (loop_path_split g v ys b Hys a Hin)
        as [before [after [Heq [Hprefix Hsuffix]]]].
      exists after. split; [exact Hsuffix|].
      rewrite Heq in Hunique. now apply NoDup_app_remove_l in Hunique.
    + exists (a :: ys). split; [now apply path_step with v|].
      now constructor.
Qed.

Local Lemma loop_reach_path : forall g r v,
  reach g [r] v -> exists xs, path g r xs v.
Proof.
  intros g r v [root [xs [Hin Hpath]]].
  destruct Hin as [<-|Hin]; [now exists xs|contradiction].
Qed.

Local Lemma loop_root_dominates : forall g r v, dominates g r r v.
Proof.
  intros g r v xs Hpath. now apply loop_path_start in Hpath.
Qed.

Local Lemma loop_self_dominates : forall g r v, dominates g r v v.
Proof.
  intros g r v xs Hpath. now apply loop_path_end in Hpath.
Qed.

Local Lemma loop_backward_dominates : forall g r h a xs b,
  dominates g r h b -> path g a xs b -> (forall x, In x xs -> x <> h) ->
  dominates g r h a.
Proof.
  intros g r h a xs b Hdom Hpath Havoid prefix Hprefix.
  destruct (loop_path_join g r prefix a xs b Hprefix Hpath) as [ys [Hys Hmembers]].
  destruct (Hmembers h (Hdom ys Hys)) as [Hin|Hin]; [exact Hin|].
  exfalso. exact (Havoid h Hin eq_refl).
Qed.

Local Lemma loop_simple_suffix : forall g r outer inner v xs,
  path g r xs v -> NoDup xs -> dominates g r outer inner -> inner <> outer ->
  In inner xs -> exists suffix, path g inner suffix v /\
    forall x, In x suffix -> x <> outer.
Proof.
  intros g r outer inner v xs Hpath Hunique Hdom Hne Hin.
  destruct (loop_path_split g r xs v Hpath inner Hin)
    as [before [after [Heq [Hprefix Hsuffix]]]].
  assert (Hbefore : In outer before).
  { destruct (in_app_or before [inner] outer (Hdom _ Hprefix)) as [Hfirst|Hlast].
    - exact Hfirst.
    - destruct Hlast as [Hequal|Hfalse]; [congruence|contradiction]. }
  exists after. split; [exact Hsuffix|].
  intros x Hafter Hequal. subst x. rewrite Heq in Hunique.
  exact (loop_nodup_disjoint before after Hunique outer Hbefore Hafter).
Qed.

Local Lemma loop_strict_dominance_asym : forall g r outer inner,
  reach g [r] inner -> dominates g r outer inner -> inner <> outer ->
  ~ dominates g r inner outer.
Proof.
  intros g r outer inner Hreach Hdom Hne Hreverse.
  destruct (loop_reach_path g r inner Hreach) as [xs Hpath].
  destruct (loop_path_simple g r xs inner Hpath) as [ys [Hys Hunique]].
  destruct (loop_simple_suffix g r inner outer inner ys Hys Hunique Hreverse
    ltac:(congruence) (Hdom ys Hys)) as [suffix [Hsuffix Havoid]].
  exact (Havoid inner (loop_path_end g outer suffix inner Hsuffix) eq_refl).
Qed.

Local Lemma loop_dominators_comparable : forall g r a b v,
  reach g [r] v -> dominates g r a v -> dominates g r b v ->
  dominates g r a b \/ dominates g r b a.
Proof.
  intros g r a b v Hreach Ha Hb.
  destruct (Pos.eq_dec a b) as [->|Hne]; [left; apply loop_self_dominates|].
  destruct (loop_reach_path g r v Hreach) as [xs Hpath].
  destruct (loop_path_simple g r xs v Hpath) as [ys [Hys Hunique]].
  destruct (loop_path_split g r ys v Hys a (Ha ys Hys))
    as [before [after [Heq [Hprefix Hsuffix]]]].
  assert (Hbmember : In b (before ++ after)) by (rewrite <- Heq; apply Hb; exact Hys).
  destruct (in_app_or before after b Hbmember) as [Hbefore|Hafter].
  - right. eapply loop_backward_dominates; [exact Hb|exact Hsuffix|].
    intros x Hin Hequal. subst x. rewrite Heq in Hunique.
    exact (loop_nodup_disjoint before after Hunique b Hbefore Hin).
  - assert (Hafter_unique : NoDup after).
    { rewrite Heq in Hunique. now apply NoDup_app_remove_l in Hunique. }
    destruct (loop_simple_suffix g a a b v after Hsuffix Hafter_unique
      (loop_root_dominates g a b) ltac:(congruence) Hafter)
      as [suffix [Htail Havoid]].
    left. eapply loop_backward_dominates; eassumption.
Qed.

Local Lemma loop_header_reachable : forall g r h,
  natural_header g r h -> reach g [r] h.
Proof.
  intros g r h [latch [Hreach [Hedge Hdom]]].
  destruct (loop_reach_path g r latch Hreach) as [xs Hpath].
  exists r, (xs ++ [h]). split; [now left|].
  now apply loop_path_snoc with latch.
Qed.

Local Lemma loop_member_reachable : forall g r h v,
  natural_loop g r h v -> reach g [r] v.
Proof.
  intros g r h v [Hheader [->|[latch [xs [Hreach Hrest]]]]].
  - now apply loop_header_reachable.
  - exact Hreach.
Qed.

Local Lemma loop_header_dominates : forall g r h v,
  natural_loop g r h v -> dominates g r h v.
Proof.
  intros g r h v [Hheader [->|[latch [xs [Hreach [Hlatch [Hedge [Hdom [Hpath Havoid]]]]]]]]].
  - apply loop_self_dominates.
  - eapply loop_backward_dominates; eassumption.
Qed.

(** Every body vertex reaches its header through vertices dominated by that header. *)
Local Lemma loop_member_header_path : forall g r h v,
  natural_loop g r h v -> exists xs, path g v xs h /\
    forall x, In x xs -> dominates g r h x.
Proof.
  intros g r h v [Hheader [->|[latch [xs [Hreach [Hlatch [Hedge [Hdom [Hpath Havoid]]]]]]]]].
  - exists [h]. split; [constructor|].
    intros x [<-|Hin]; [apply loop_self_dominates|contradiction].
  - exists (xs ++ [h]). split; [now apply loop_path_snoc with latch|].
    intros x Hin. destruct (in_app_or xs [h] x Hin) as [Hxs|Hlast].
    + destruct (loop_path_split g v xs latch Hpath x Hxs)
        as [before [after [Heq [Hprefix Hsuffix]]]].
      eapply loop_backward_dominates; [exact Hdom|exact Hsuffix|].
      intros y Hy. apply Havoid. rewrite Heq. apply in_or_app. now right.
    + destruct Hlast as [<-|Hfalse]; [apply loop_self_dominates|contradiction].
Qed.

Local Lemma loop_meeting_header : forall g r inner outer v,
  natural_loop g r inner v -> natural_loop g r outer v ->
  dominates g r outer inner -> inner <> outer -> natural_loop g r outer inner.
Proof.
  intros g r inner outer v Hinner Houter Hdom Hne.
  pose proof (loop_member_reachable g r inner v Hinner) as Hreach.
  pose proof (loop_header_dominates g r inner v Hinner) as Hinnerdom.
  destruct (loop_reach_path g r v Hreach) as [xs Hpath].
  destruct (loop_path_simple g r xs v Hpath) as [ys [Hys Hunique]].
  destruct (loop_simple_suffix g r outer inner v ys Hys Hunique Hdom Hne
    (Hinnerdom ys Hys)) as [suffix [Hsuffix Havoid]].
  destruct Houter as [Houterheader [Hequal|[latch [zs [Hv [Hlatch [Hedge [Hldom [Hlast Hlastavoid]]]]]]]]].
  - subst v. exfalso. exact (Havoid outer (loop_path_end g inner suffix outer Hsuffix) eq_refl).
  - destruct (loop_path_join g inner suffix v zs latch Hsuffix Hlast)
      as [joined [Hjoined Hmembers]].
    split; [exact Houterheader|]. right. exists latch, joined.
    split; [apply loop_header_reachable; exact (proj1 Hinner)|].
    split; [exact Hlatch|]. split; [exact Hedge|]. split; [exact Hldom|].
    split; [exact Hjoined|]. intros x Hin.
    destruct (Hmembers x Hin) as [Hfirst|Hsecond]; [now apply Havoid|now apply Hlastavoid].
Qed.

Local Lemma loop_member_containment : forall g r inner outer,
  natural_header g r inner -> natural_loop g r outer inner ->
  dominates g r outer inner -> inner <> outer -> loop_inside g r inner outer.
Proof.
  intros g r inner outer Hinner Houter Hdom Hne.
  pose proof (loop_header_reachable g r inner Hinner) as Hreach.
  pose proof (loop_strict_dominance_asym g r outer inner Hreach Hdom Hne) as Hreverse.
  split; [exact Hne|]. split; [exact Hinner|]. split; [exact (proj1 Houter)|].
  intros v Hbody.
  destruct (loop_member_header_path g r inner v Hbody) as [xs [Hpath Hdominated]].
  assert (Havoid : forall x, In x xs -> x <> outer).
  { intros x Hin Hequal. subst x. exact (Hreverse (Hdominated outer Hin)). }
  destruct Houter as [Houterheader [Hequal|[latch [ys [Hinnerreach [Hlatch [Hedge [Hldom [Hlast Hlastavoid]]]]]]]]];
    [contradiction|].
  destruct (loop_path_join g v xs inner ys latch Hpath Hlast)
    as [joined [Hjoined Hmembers]].
  split; [exact Houterheader|]. right. exists latch, joined.
  split; [now apply loop_member_reachable with inner|].
  split; [exact Hlatch|]. split; [exact Hedge|]. split; [exact Hldom|].
  split; [exact Hjoined|]. intros x Hin.
  destruct (Hmembers x Hin) as [Hfirst|Hsecond]; [now apply Havoid|now apply Hlastavoid].
Qed.

Local Lemma loop_order_cons : forall xs u v x,
  order_before xs u v -> order_before (x :: xs) u v.
Proof.
  intros xs u v x [i [j [Hi [Hj Hij]]]].
  exists (S i), (S j). split; [exact Hi|]. split; [exact Hj|].
  exact (proj1 (Nat.succ_lt_mono i j) Hij).
Qed.

Local Lemma loop_order_first : forall xs u v,
  In v xs -> order_before (u :: xs) u v.
Proof.
  intros xs u v Hin. apply In_nth_error in Hin. destruct Hin as [j Hj].
  exists 0, (S j). split; [reflexivity|]. split; [exact Hj|apply Nat.lt_0_succ].
Qed.

Local Lemma loop_order_filter : forall (p : positive -> bool) xs u v,
  order_before xs u v -> p u = true -> p v = true ->
  order_before (filter p xs) u v.
Proof.
  intros p xs. induction xs as [|x xs IH]; intros u v [i [j [Hi [Hj Hij]]]] Hu Hv.
  - destruct i; discriminate.
  - destruct i as [|i], j as [|j].
    + inversion Hij.
    + cbn in Hi, Hj. injection Hi as <-. cbn. rewrite Hu.
      apply loop_order_first, filter_In. split; [now apply nth_error_In in Hj|exact Hv].
    + inversion Hij.
    + cbn in Hi, Hj. apply (proj2 (Nat.succ_lt_mono i j)) in Hij.
      assert (Htail : order_before (filter p xs) u v).
      { apply IH; [now exists i, j|exact Hu|exact Hv]. }
      cbn. destruct (p x); [now apply loop_order_cons|exact Htail].
Qed.

(** A body step preserves every answer vertex, including the premarked header. *)
Local Lemma loop_body_step_member : forall g t h x st,
  In x (loop_body_answer st) ->
  match body_step g t h st with
  | inl next => In x (loop_body_answer next)
  | inr result => In x result
  end.
Proof.
  intros g t h x [pending seen answer] Hmember. cbn [loop_body_answer] in Hmember.
  destruct pending as [|v rest].
  - cbn [body_step]. rewrite rev_append_rev, app_nil_r.
    now apply (proj1 (in_rev answer x)).
  - cbn [body_step].
    destruct (trie_get v seen) as [present|]; destruct (trie_get v (pre t)) as [number|];
      cbn [loop_body_answer]; try exact Hmember.
    now right.
Qed.

Local Lemma loop_body_loop_member : forall g t h fs (Hacc : Acc loopN_lt fs),
  forall x, In x (loop_body_answer (snd fs)) ->
  match Argent.Loop.loop loopN_lt (loopN_step (body_step g t h)) fs Hacc with
  | inl final => In x (loop_body_answer final)
  | inr result => In x result
  end.
Proof.
  intros g t h fs Hacc.
  induction Hacc as [[fuel st] Hnext IH] using Acc_ind_dep.
  cbn [snd]. intros x Hmember. destruct fuel as [|fuel].
  - exact Hmember.
  - cbn [Argent.Loop.loop loopN_step Acc_inv].
    pose proof (loop_body_step_member g t h x st Hmember) as Hstep.
    destruct (body_step g t h st) as [next|result] eqn:Hresult.
    + apply IH. exact Hstep.
    + exact Hstep.
Qed.

(** Even an exhausted raw collection retains the header installed before traversal. *)
Local Lemma loop_collect_header : forall g t h sources, In h (collect g t h sources).
Proof.
  intros g t h sources.
  assert (Hinitial : In h (loop_body_answer
    (LoopBodyState sources (PTrieCode.set h tt Empty) [h]))) by now left.
  unfold collect, loopN.
  match goal with
  | |- context [Argent.Loop.loop _ _ ?fs ?Hacc] =>
      pose proof (loop_body_loop_member g t h fs Hacc h Hinitial) as Hloop
  end.
  match goal with
  | Hloop : context [Argent.Loop.loop ?lt ?step ?fs ?Hacc] |- _ =>
      destruct (Argent.Loop.loop lt step fs Hacc) as [final|result]
  end.
  - rewrite rev_append_rev, app_nil_r. now apply (proj1 (in_rev _ h)).
  - exact Hloop.
Qed.

(** A traversal returns only after its pending task list is empty. *)
Local Lemma loop_tree_stopping : forall g t st result,
  tree_step g t st = inr result -> loop_tree_pending st = [].
Proof.
  intros g t [pending stack active [order latches backs]] result Hstep.
  destruct pending as [|task rest]; [reflexivity|].
  destruct task as [v|v|vs|u vs|v]; cbn [tree_step] in Hstep; try discriminate.
  - destruct (trie_get v (pre t)), (trie_get v (idom t)); discriminate.
  - destruct vs; discriminate.
  - destruct vs as [|v vs]; [discriminate|].
    destruct (trie_get v active); discriminate.
Qed.

(** The reverse collector likewise stops only with an empty pending list. *)
Local Lemma loop_body_stopping : forall g t h st result,
  body_step g t h st = inr result -> loop_body_pending st = [].
Proof.
  intros g t h [pending seen answer] result Hstep.
  destruct pending as [|v rest]; [reflexivity|].
  cbn [body_step] in Hstep.
  destruct (trie_get v seen), (trie_get v (pre t)); discriminate.
Qed.

Local Lemma loop_path_listed : forall g a xs b,
  wf_graph g -> path g a xs b -> In a (verts g) -> In b (verts g).
Proof.
  intros g a xs b [_ Hclosed] Hpath.
  induction Hpath as [v|u v xs w Hedge Hpath IH]; intro Hlisted.
  - exact Hlisted.
  - apply IH. now apply (Hclosed u v).
Qed.

Local Lemma loop_reachable_listed : forall g r v,
  wf_graph g -> In r (verts g) -> reach g [r] v -> In v (verts g).
Proof.
  intros g r v Hgraph Hroot Hreach.
  destruct (loop_reach_path g r v Hreach) as [xs Hpath].
  now apply (loop_path_listed g r xs v Hgraph Hpath).
Qed.

(** Stopping pays for one reversal of the accumulated answer. *)
Local Lemma loop_tree_stop_clock : forall g t stack active order latches backs,
  (T_tree_step g t (LoopTreeState [] stack active (LoopScan order latches backs)) <=
    N.of_nat (length order + 3))%N.
Proof.
  intros g t stack active order latches backs.
  pose proof (List.T_rev_append_le order []) as Hreverse.
  unfold T_tree_step. time_simpl. rewrite Nat2N.inj_add. lia.
Qed.

Local Lemma loop_body_stop_clock : forall g t h seen answer,
  (T_body_step g t h (LoopBodyState [] seen answer) <= N.of_nat (length answer + 3))%N.
Proof.
  intros g t h seen answer. pose proof (List.T_rev_append_le answer []) as Hreverse.
  unfold T_body_step. time_simpl. rewrite Nat2N.inj_add. lia.
Qed.

(** Reverse edges preserve membership until the premarked header is reached. *)
Local Lemma loop_natural_predecessor : forall g r h v u,
  natural_loop g r h v -> v <> h -> edge g u v -> reach g [r] u ->
  natural_loop g r h u.
Proof.
  intros g r h v u [Hheader Hmember] Hne Hedge Hreach.
  split; [exact Hheader|]. destruct (Pos.eq_dec u h) as [Heq|Hune]; [now left|].
  right. destruct Hmember as [Heq|[latch [xs [Hv [Hlatch [Hback [Hdom [Hpath Havoid]]]]]]]];
    [contradiction|].
  exists latch, (u :: xs). repeat split; try assumption.
  - now apply path_step with v.
  - intros x [<-|Hin]; [exact Hune|now apply Havoid].
Qed.

Local Lemma loop_natural_latch : forall g r h latch,
  reach g [r] latch -> edge g latch h -> dominates g r h latch ->
  natural_loop g r h latch.
Proof.
  intros g r h latch Hreach Hedge Hdom. split.
  - now exists latch.
  - destruct (Pos.eq_dec latch h) as [Heq|Hne]; [now left|].
    right. exists latch, [latch]. repeat split; try assumption.
    + constructor.
    + intros x [<-|Hfalse]; [exact Hne|contradiction].
Qed.

Local Lemma loop_tree_pre_reachable : forall g r t v,
  domtree_exact g r t ->
  ((exists a, trie_get v (pre t) = Some a) <-> reach (base g) [r] v).
Proof.
  intros g r t v [_ [_ [_ [_ [_ [Hpre _]]]]]]. apply Hpre.
Qed.

Local Lemma loop_predecessor_edge : forall g u v,
  prepared_ok g -> In u (preds g v) -> edge (base g) u v.
Proof.
  intros g u v [_ [_ Hpred]] Hin.
  apply (Permutation_in u (Hpred v)) in Hin.
  apply in_flat_map in Hin. destruct Hin as [source [Hsource Hrow]].
  apply in_map_iff in Hrow. destruct Hrow as [target [Heq Htarget]]. subst source.
  apply filter_In in Htarget. destruct Htarget as [Hedge Heq].
  apply Pos.eqb_eq in Heq. now subst target.
Qed.

Local Lemma loop_edge_predecessor : forall g u v,
  prepared_ok g -> In u (nodes g) -> edge (base g) u v -> In u (preds g v).
Proof.
  intros g u v [_ [_ Hpred]] Hlisted Hedge.
  apply (Permutation_in u (Permutation_sym (Hpred v))).
  apply in_flat_map. exists u. split; [exact Hlisted|].
  apply in_map_iff. exists v. split; [reflexivity|].
  apply filter_In. split; [exact Hedge|apply Pos.eqb_refl].
Qed.

Local Definition loop_body_covered (st : loop_body_state) (v : positive) : Prop :=
  In v (loop_body_answer st) \/ In v (loop_body_pending st).

(** Sound members and queued predecessor obligations describe every collector prefix. *)
Local Definition loop_body_semantic g (t : domtree) r h sources (st : loop_body_state) : Prop :=
  In h (loop_body_answer st) /\
  NoDup (loop_body_answer st) /\
  (forall v, trie_get v (loop_body_seen st) = Some tt <-> In v (loop_body_answer st)) /\
  Forall (natural_loop (base g) r h) (loop_body_answer st) /\
  Forall (natural_loop (base g) r h) (loop_body_pending st) /\
  (forall v, In v sources -> loop_body_covered st v) /\
  (forall v u, In v (loop_body_answer st) -> v <> h ->
    In u (preds g v) -> reach (base g) [r] u -> loop_body_covered st u).

Local Lemma loop_body_semantic_initial : forall g t r h sources,
  natural_header (base g) r h -> Forall (natural_loop (base g) r h) sources ->
  loop_body_semantic g t r h sources
    (LoopBodyState sources (PTrieCode.set h tt Empty) [h]).
Proof.
  intros g t r h sources Hheader Hsources. split; [now left|].
  split; [constructor; [simpl; tauto|constructor]|]. split.
  - intro v. destruct (Pos.eq_dec v h) as [->|Hne].
    + change (PTrie.get h (PTrie.set h tt PTrie.empty) = Some tt <-> In h [h]).
      rewrite PTrie.get_set_same. split; [intros _; now left|intros _; reflexivity].
    + change (PTrie.get v (PTrie.set h tt PTrie.empty) = Some tt <-> In v [h]).
      rewrite PTrie.get_set_other by exact Hne. rewrite PTrie.get_empty.
      split; [discriminate|]. intros [Heq|Hfalse]; [congruence|contradiction].
  - split; [constructor; [split; [exact Hheader|now left]|constructor]|].
    split; [exact Hsources|]. split.
    + intros v Hin. now right.
    + intros v u [<-|Hfalse] Hne; [contradiction|contradiction].
Qed.

Local Lemma loop_body_semantic_skip : forall g t r h sources v rest seen answer,
  loop_body_semantic g t r h sources (LoopBodyState (v :: rest) seen answer) ->
  trie_get v seen = Some tt ->
  loop_body_semantic g t r h sources (LoopBodyState rest seen answer).
Proof.
  intros g t r h sources v rest seen answer
    [Hheader [Hunique [Hseen [Hanswer [Hpending [Hsources Hclosed]]]]]] Hmarked.
  cbn [loop_body_answer loop_body_seen loop_body_pending] in Hheader, Hunique, Hseen,
    Hanswer, Hpending, Hclosed.
  assert (Hmember : In v answer) by now apply (proj1 (Hseen v)).
  assert (Hcovered : forall x,
    loop_body_covered (LoopBodyState (v :: rest) seen answer) x ->
    loop_body_covered (LoopBodyState rest seen answer) x).
  { intros x [Hin|[<-|Hin]]; [now left|now left|now right]. }
  split; [exact Hheader|]. split; [exact Hunique|].
  split; [exact Hseen|]. split; [exact Hanswer|].
  split; [now inversion Hpending|]. split.
  - intros x Hin. now apply Hcovered, Hsources.
  - intros x u Hin Hne Hpred Hreach. apply Hcovered.
    now apply (Hclosed x u).
Qed.

Local Lemma loop_body_semantic_fresh : forall g t r h sources v rest seen answer,
  prepared_ok g -> domtree_exact g r t ->
  loop_body_semantic g t r h sources (LoopBodyState (v :: rest) seen answer) ->
  trie_get v seen = None ->
  loop_body_semantic g t r h sources
    (LoopBodyState (filter (fun u => match trie_get u (pre t) with
      | Some _ => true | None => false end) (preds g v) ++ rest)
      (PTrieCode.set v tt seen) (v :: answer)).
Proof.
  intros g t r h sources v rest seen answer Hprepared Htree
    [Hheader [Hunique [Hseen [Hanswer [Hpending [Hsources Hclosed]]]]]] Hfresh.
  cbn [loop_body_answer loop_body_seen loop_body_pending] in Hheader, Hunique, Hseen,
    Hanswer, Hpending, Hclosed.
  inversion Hpending as [|v' rest' Hmember Hrest]; subst v' rest'.
  assert (Hne : v <> h).
  { intro Heq. subst v. apply (proj2 (Hseen h)) in Hheader. congruence. }
  assert (Hcovered : forall x,
    loop_body_covered (LoopBodyState (v :: rest) seen answer) x ->
    loop_body_covered
      (LoopBodyState (filter (fun u => match trie_get u (pre t) with
        | Some _ => true | None => false end) (preds g v) ++ rest)
        (PTrieCode.set v tt seen) (v :: answer)) x).
  { intros x [Hin|[<-|Hin]]; [left; now right|left; now left|].
    right. now apply in_or_app; right. }
  split; [now right|]. split.
  - constructor; [|exact Hunique].
    intro Hin. apply (proj2 (Hseen v)) in Hin. congruence.
  - split.
    + intro x. destruct (Pos.eq_dec x v) as [->|Hneq].
      * change (PTrie.get v (PTrie.set v tt seen) = Some tt <-> In v (v :: answer)).
        rewrite PTrie.get_set_same. split; [intros _; now left|intros _; reflexivity].
      * change (PTrie.get x (PTrie.set v tt seen) = Some tt <-> In x (v :: answer)).
        rewrite PTrie.get_set_other by exact Hneq. rewrite (Hseen x).
        split; [now right|]. intros [Heq|Hin]; [congruence|exact Hin].
    + split; [now constructor|]. split.
      * apply Forall_app. split; [|exact Hrest]. apply Forall_forall.
        intros u Hin. apply filter_In in Hin. destruct Hin as [Hpred Hpre].
        destruct (trie_get u (pre t)) as [a|] eqn:Hnumber; [|discriminate].
        apply (loop_natural_predecessor (base g) r h v u Hmember Hne).
        -- now apply loop_predecessor_edge.
        -- apply (proj1 (loop_tree_pre_reachable g r t u Htree)). now exists a.
      * split.
        -- intros x Hin. now apply Hcovered, Hsources.
        -- intros x u [<-|Hin] Hneq Hpred Hreach.
           ++ right. apply in_or_app. left. apply filter_In. split; [exact Hpred|].
              destruct (proj2 (loop_tree_pre_reachable g r t u Htree) Hreach) as [a Ha].
              now rewrite Ha.
           ++ apply Hcovered. now apply (Hclosed x u).
Qed.

(** An empty worklist leaves a sound body closed under every required reverse edge. *)
Local Definition loop_body_result g r h sources (result : list positive) : Prop :=
  In h result /\ NoDup result /\ Forall (natural_loop (base g) r h) result /\ incl sources result /\
  forall v u, In v result -> v <> h -> In u (preds g v) ->
    reach (base g) [r] u -> In u result.

Local Lemma loop_body_semantic_stop : forall g t r h sources seen answer,
  loop_body_semantic g t r h sources (LoopBodyState [] seen answer) ->
  loop_body_result g r h sources (rev_append answer []).
Proof.
  intros g t r h sources seen answer
    [Hheader [Hunique [Hseen [Hanswer [Hpending [Hsources Hclosed]]]]]].
  rewrite rev_append_rev, app_nil_r. split.
  - now apply (proj1 (in_rev answer h)).
  - split; [now apply NoDup_rev|]. split.
    + apply Forall_forall. intros v Hin. apply (proj2 (in_rev answer v)) in Hin.
      now apply (proj1 (Forall_forall _ _) Hanswer v).
    + split.
      * intros v Hin. apply (proj1 (in_rev answer v)).
        destruct (Hsources v Hin) as [Hfound|Hempty]; [exact Hfound|contradiction].
      * intros v u Hin Hne Hpred Hreach. apply (proj1 (in_rev answer u)).
        apply (proj2 (in_rev answer v)) in Hin.
        destruct (Hclosed v u Hin Hne Hpred Hreach) as [Hfound|Hempty];
          [exact Hfound|contradiction].
Qed.

Local Lemma loop_body_step_semantic : forall g t r h sources st,
  prepared_ok g -> domtree_exact g r t -> loop_body_semantic g t r h sources st ->
  match body_step g t h st with
  | inl next => loop_body_semantic g t r h sources next
  | inr result => loop_body_result g r h sources result
  end.
Proof.
  intros g t r h sources [pending seen answer] Hprepared Htree Hinv.
  destruct pending as [|v rest].
  - cbn [body_step]. now apply (loop_body_semantic_stop g t r h sources seen answer).
  - cbn [body_step]. destruct (trie_get v seen) as [[]|] eqn:Hseen.
    + destruct (trie_get v (pre t)); now apply (loop_body_semantic_skip g t r h sources v).
    + destruct (trie_get v (pre t)) as [a|] eqn:Hpre.
      * now apply (loop_body_semantic_fresh g t r h sources v).
      * exfalso. destruct Hinv as [_ [_ [_ [_ [Hpending _]]]]].
        inversion Hpending as [|v' rest' Hmember Hrest]; subst v' rest'.
        pose proof (loop_member_reachable (base g) r h v Hmember) as Hreach.
        destruct (proj2 (loop_tree_pre_reachable g r t v Htree) Hreach) as [a Ha].
        congruence.
Qed.

Local Lemma loop_body_loop_semantic : forall g t r h sources,
  prepared_ok g -> domtree_exact g r t ->
  forall fs (Hacc : Acc loopN_lt fs), loop_body_semantic g t r h sources (snd fs) ->
  match Argent.Loop.loop loopN_lt (loopN_step (body_step g t h)) fs Hacc with
  | inl final => loop_body_semantic g t r h sources final
  | inr result => loop_body_result g r h sources result
  end.
Proof.
  intros g t r h sources Hprepared Htree fs Hacc.
  induction Hacc as [[fuel st] Hnext IH] using Acc_ind_dep.
  cbn [snd]. intro Hinv. destruct fuel as [|fuel].
  - exact Hinv.
  - cbn [Argent.Loop.loop loopN_step Acc_inv].
    pose proof (loop_body_step_semantic g t r h sources st Hprepared Htree Hinv) as Hstep.
    destruct (body_step g t h st) as [next|result] eqn:Hresult.
    + apply IH. exact Hstep.
    + exact Hstep.
Qed.

Local Lemma loop_body_finished_semantic : forall g t r h sources fuel result,
  prepared_ok g -> domtree_exact g r t -> natural_header (base g) r h ->
  Forall (natural_loop (base g) r h) sources ->
  loopN (body_step g t h) fuel
    (LoopBodyState sources (PTrieCode.set h tt Empty) [h]) = inr result ->
  loop_body_result g r h sources result.
Proof.
  intros g t r h sources fuel result Hprepared Htree Hheader Hsources Hdone.
  pose proof (loop_body_semantic_initial g t r h sources Hheader Hsources) as Hinitial.
  assert (Hloop : match loopN (body_step g t h) fuel
    (LoopBodyState sources (PTrieCode.set h tt Empty) [h]) with
    | inl final => loop_body_semantic g t r h sources final
    | inr found => loop_body_result g r h sources found
    end).
  { unfold loopN. now apply loop_body_loop_semantic. }
  now rewrite Hdone in Hloop.
Qed.

Local Lemma loop_reachable_edge : forall g r u v,
  reach g [r] u -> edge g u v -> reach g [r] v.
Proof.
  intros g r u v Hreach Hedge. destruct (loop_reach_path g r u Hreach) as [xs Hpath].
  exists r, (xs ++ [v]). split; [now left|]. now apply loop_path_snoc with u.
Qed.

Local Lemma loop_reverse_closed_path : forall g r h body,
  (forall u v, reach g [r] u -> edge g u v -> v <> h -> In v body -> In u body) ->
  forall v xs latch, path g v xs latch ->
  (forall x, In x xs -> x <> h) -> reach g [r] v -> In latch body -> In v body.
Proof.
  intros g r h body Hclosed v xs latch Hpath.
  induction Hpath as [v|u v xs latch Hedge Hpath IH]; intros Havoid Hreach Hlast.
  - exact Hlast.
  - apply (Hclosed u v Hreach Hedge).
    + apply Havoid. right. now apply loop_path_start in Hpath.
    + apply IH.
      * intros x Hin. apply Havoid. now right.
      * now apply (loop_reachable_edge g r u v).
      * exact Hlast.
Qed.

(** Soundness and reverse closure characterize exactly the natural-loop paths. *)
Local Lemma loop_body_result_exact : forall g r h sources result,
  wf_graph (base g) -> prepared_ok g -> In r (verts (base g)) ->
  (forall latch, reach (base g) [r] latch -> edge (base g) latch h ->
    dominates (base g) r h latch -> In latch sources) ->
  loop_body_result g r h sources result ->
  forall v, In v result <-> natural_loop (base g) r h v.
Proof.
  intros g r h sources result Hgraph Hprepared Hroot Hlatches
    [Hheader [Hunique [Hsound [Hsources Hclosed]]]] v. split.
  - intro Hin. now apply (proj1 (Forall_forall _ _) Hsound v).
  - intros [_ [->|[latch [xs [Hreach [Hlatch [Hedge [Hdom [Hpath Havoid]]]]]]]]];
      [exact Hheader|].
    apply (loop_reverse_closed_path (base g) r h result) with (xs := xs) (latch := latch);
      try assumption.
    + intros u target Hureach Hutarget Hne Hin.
      apply (Hclosed target u Hin Hne); [|exact Hureach].
      apply loop_edge_predecessor; [exact Hprepared| |exact Hutarget].
      assert (Hlisted : In u (verts (base g))).
      { now apply (loop_reachable_listed (base g) r u). }
      destruct g as [[vertices edges] predecessors vertex_count edge_count]. exact Hlisted.
    + apply Hsources. now apply Hlatches.
Qed.

Local Lemma loop_sum_ext {A : Type} : forall (xs : list A) (f g : A -> nat),
  (forall x, In x xs -> f x = g x) ->
  fold_right (fun x total => f x + total) 0 xs =
  fold_right (fun x total => g x + total) 0 xs.
Proof.
  intro xs. induction xs as [|x rest IH]; intros f g Heq; [reflexivity|].
  cbn [fold_right]. rewrite (Heq x (or_introl eq_refl)). f_equal.
  apply IH. intros u Hu. apply Heq. now right.
Qed.

Local Lemma loop_sum_update {A : Type} : forall (xs : list A) x (f g : A -> nat),
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
      { apply loop_sum_ext. intros u Hu. apply Hother. intro Heq. subst u. contradiction. }
      now rewrite Htail.
    + assert (Hvx : v <> x) by (intro Heq; subst v; contradiction).
      cbn [fold_right]. rewrite (Hother v Hvx), (IH x f g Hrest Hin Hx Hother). lia.
Qed.

Local Lemma loop_nodes_verts : forall g, nodes g = verts (base g).
Proof.
  intros [[vertices adjacency] predecessors vertices_count edges_count]. reflexivity.
Qed.

Local Lemma loop_nodes_unique : forall g, wf_graph (base g) -> NoDup (nodes g).
Proof.
  intros g Hgraph. rewrite loop_nodes_verts. exact (proj1 Hgraph).
Qed.

Local Lemma loop_sum_add {A : Type} : forall (xs : list A) (f g : A -> nat),
  fold_right (fun x total => f x + g x + total) 0 xs =
  fold_right (fun x total => f x + total) 0 xs +
    fold_right (fun x total => g x + total) 0 xs.
Proof.
  intro xs. induction xs as [|x rest IH]; intros f g; [reflexivity|].
  cbn [fold_right]. rewrite IH. lia.
Qed.

Local Lemma loop_sum_swap {A B : Type} : forall (xs : list A) (ys : list B) (f : A -> B -> nat),
  fold_right (fun x total => fold_right (fun y subtotal => f x y + subtotal) 0 ys + total) 0 xs =
  fold_right (fun y total => fold_right (fun x subtotal => f x y + subtotal) 0 xs + total) 0 ys.
Proof.
  intro xs. induction xs as [|x rest IH]; intros ys f.
  - cbn [fold_right]. induction ys; cbn [fold_right]; assumption || reflexivity.
  - cbn [fold_right]. rewrite IH. symmetry. apply loop_sum_add.
Qed.

Local Lemma loop_flat_map_length {A B : Type} : forall (f : A -> list B) xs,
  length (flat_map f xs) = fold_right (fun x total => length (f x) + total) 0 xs.
Proof.
  intros f xs. induction xs as [|x rest IH]; [reflexivity|].
  cbn [flat_map fold_right]. now rewrite length_app, IH.
Qed.

Local Lemma loop_filter_partition : forall vertices successors,
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
    pose proof (loop_sum_update vertices v
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

Local Lemma loop_preds_length : forall g y,
  prepared_ok g -> length (preds g y) =
    fold_right (fun x total => length (filter (Pos.eqb y) (succs (base g) x)) + total) 0 (nodes g).
Proof.
  intros g y [_ [_ Hpreds]]. rewrite (Permutation_length (Hpreds y)).
  rewrite loop_flat_map_length. apply loop_sum_ext. intros x Hx. apply length_map.
Qed.

Local Lemma loop_predecessor_sum : forall g,
  wf_graph (base g) -> prepared_ok g ->
  fold_right (fun y total => length (preds g y) + total) 0 (nodes g) = graph_e (base g).
Proof.
  intros g Hgraph Hprepared.
  rewrite (loop_sum_ext (nodes g) (fun y => length (preds g y))
    (fun y => fold_right (fun x total => length (filter (Pos.eqb y) (succs (base g) x)) + total)
      0 (nodes g))) by (intros y Hy; now apply loop_preds_length).
  rewrite loop_sum_swap.
  replace (graph_e (base g)) with
    (fold_right (fun x total => length (succs (base g) x) + total) 0 (nodes g)) by
    (destruct g as [[vertices adjacency] predecessors vertices_count edges_count]; reflexivity).
  apply loop_sum_ext. intros x Hx. apply loop_filter_partition.
  - now apply loop_nodes_unique.
  - intros y Hy. rewrite loop_nodes_verts in *. eapply (proj2 Hgraph); eassumption.
Qed.


(** Each unseen vertex reserves credit for its eventual predecessor expansion. *)
Local Definition loop_unseen_work (weight : positive -> nat) (vertices : list positive)
    (seen : ptrie unit) : nat :=
  fold_right (fun v total => match trie_get v seen with
    | Some _ => total | None => weight v + total end) 0 vertices.

Local Lemma loop_unseen_work_absent : forall weight vertices seen x,
  ~ In x vertices ->
  loop_unseen_work weight vertices (PTrieCode.set x tt seen) =
    loop_unseen_work weight vertices seen.
Proof.
  intros weight vertices. induction vertices as [|v rest IH]; intros seen x Hnot; [reflexivity|].
  unfold loop_unseen_work at 1 2. cbn [fold_right].
  rewrite PTrie.get_set_other by (intro Heq; subst v; apply Hnot; now left).
  fold (loop_unseen_work weight rest seen)
    (loop_unseen_work weight rest (PTrieCode.set x tt seen)).
  rewrite IH by (intro Hin; apply Hnot; now right). reflexivity.
Qed.

Local Lemma loop_unseen_work_fresh : forall weight vertices seen x,
  NoDup vertices -> In x vertices -> trie_get x seen = None ->
  loop_unseen_work weight vertices seen =
    weight x + loop_unseen_work weight vertices (PTrieCode.set x tt seen).
Proof.
  intros weight vertices. induction vertices as [|v rest IH]; intros seen x Hunique Hin Hfresh.
  - contradiction.
  - inversion Hunique as [|? ? Hnot Hrest]; subst.
    destruct Hin as [<-|Hin].
    + unfold loop_unseen_work at 1 2. cbn [fold_right].
      rewrite Hfresh, PTrie.get_set_same.
      fold (loop_unseen_work weight rest seen)
        (loop_unseen_work weight rest (PTrieCode.set v tt seen)).
      now rewrite loop_unseen_work_absent.
    + assert (Hne : v <> x) by (intro Heq; subst v; contradiction).
      specialize (IH seen x Hrest Hin Hfresh).
      unfold loop_unseen_work at 1 2. cbn [fold_right].
      rewrite PTrie.get_set_other by exact Hne.
      fold (loop_unseen_work weight rest seen)
        (loop_unseen_work weight rest (PTrieCode.set x tt seen)).
      destruct (trie_get v seen) as [[]|] eqn:Hget.
      * change (PTrie.get v seen = Some tt) in Hget. rewrite Hget. lia.
      * change (PTrie.get v seen = None) in Hget. rewrite Hget. lia.
Qed.

Local Lemma loop_unseen_work_bound : forall weight vertices seen,
  loop_unseen_work weight vertices seen <= fold_right (fun v n => weight v + n) 0 vertices.
Proof.
  intros weight vertices. induction vertices as [|v rest IH]; intro seen; [reflexivity|].
  specialize (IH seen). unfold loop_unseen_work in *. cbn [fold_right].
  destruct (trie_get v seen); lia.
Qed.

Local Definition loop_body_global_potential (g : prepared) (st : loop_body_state) : nat :=
  2 * loop_unseen_work (fun v => 2 + length (preds g v)) (nodes g) (loop_body_seen st) +
    length (loop_body_pending st).

Local Lemma loop_body_global_step : forall g t r h st next,
  wf_graph (base g) -> domtree_exact g r t -> body_step g t h st = inl next ->
  loop_body_global_potential g next < loop_body_global_potential g st.
Proof.
  intros g t r h [pending seen answer] next Hgraph Htree Hstep.
  destruct pending as [|v rest]; [discriminate Hstep|].
  cbn [body_step] in Hstep.
  destruct (trie_get v seen) as [[]|] eqn:Hseen;
    destruct (trie_get v (pre t)) as [a|] eqn:Hpre;
    injection Hstep as <-;
    try (unfold loop_body_global_potential; cbn [loop_body_seen loop_body_pending length]; lia).
  assert (Hlisted : In v (nodes g)).
  { rewrite loop_nodes_verts. apply (loop_reachable_listed (base g) r v Hgraph (proj1 Htree)).
    apply (proj1 (loop_tree_pre_reachable g r t v Htree)). now exists a. }
  pose proof (loop_unseen_work_fresh (fun x => 2 + length (preds g x))
    (nodes g) seen v (loop_nodes_unique g Hgraph) Hlisted Hseen) as Hcredit.
  pose proof (filter_length_le (fun u => match trie_get u (pre t) with
    | Some _ => true | None => false end) (preds g v)) as Hlength.
  unfold loop_body_global_potential. cbn [loop_body_seen loop_body_pending].
  rewrite length_app, Hcredit. cbn beta. cbn [length]. lia.
Qed.

Local Lemma loop_body_global_initial : forall g h sources,
  wf_graph (base g) -> prepared_ok g ->
  loop_body_global_potential g (LoopBodyState sources (PTrieCode.set h tt Empty) [h]) <=
    4 * graph_n (base g) + 2 * graph_e (base g) + length sources.
Proof.
  intros g h sources Hgraph Hprepared.
  pose proof (loop_unseen_work_bound (fun v => 2 + length (preds g v))
    (nodes g) (PTrieCode.set h tt Empty)) as Hwhite.
  assert (Hweight : forall vertices,
    fold_right (fun v n => 2 + length (preds g v) + n) 0 vertices =
      2 * length vertices + fold_right (fun v n => length (preds g v) + n) 0 vertices).
  { intro vertices. induction vertices as [|v rest IH]; cbn [fold_right length]; lia. }
  rewrite Hweight, (loop_predecessor_sum g Hgraph Hprepared) in Hwhite.
  assert (Hnodes : length (nodes g) = graph_n (base g)).
  { destruct g as [[vertices edges] predecessors vertex_count edge_count]. reflexivity. }
  rewrite Hnodes in Hwhite.
  unfold loop_body_global_potential. cbn [loop_body_seen loop_body_pending]. lia.
Qed.

(** The public binary fuel exceeds a private decreasing worklist measure. *)
Local Lemma loop_collect_finishes : forall g t r h sources,
  wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
  exists result, loopN (body_step g t h)
    (4 * (nv g + ne g + N.of_nat (length sources) + 1))%N
    (LoopBodyState sources (PTrieCode.set h tt Empty) [h]) = inr result.
Proof.
  intros g t r h sources Hgraph Hprepared Htree.
  apply (loopN_done loop_body_state (list positive) (body_step g t h)
    (fun _ => True) (loop_body_global_potential g)).
  - intros st next _ Hstep. split; [exact I|].
    now apply (loop_body_global_step g t r h st next Hgraph Htree).
  - exact I.
  - pose proof (loop_body_global_initial g h sources Hgraph Hprepared) as Hbound.
    destruct Hprepared as [Hn [He _]]. rewrite Hn, He. lia.
Qed.

Local Lemma loop_collect_driver : forall g t r h sources,
  wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
  loopN (body_step g t h) (4 * (nv g + ne g + N.of_nat (length sources) + 1))%N
    (LoopBodyState sources (PTrieCode.set h tt Empty) [h]) = inr (collect g t h sources).
Proof.
  intros g t r h sources Hgraph Hprepared Htree.
  destruct (loop_collect_finishes g t r h sources Hgraph Hprepared Htree) as [result Hdone].
  unfold collect. now rewrite Hdone.
Qed.

(** Any complete latch row produces precisely its semantic natural-loop body. *)
Local Lemma loop_collect_exact : forall g t r h sources,
  wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
  natural_header (base g) r h ->
  (forall v, In v sources <->
    reach (base g) [r] v /\ edge (base g) v h /\ dominates (base g) r h v) ->
  NoDup (collect g t h sources) /\ incl (collect g t h sources) (nodes g) /\
    forall v, In v (collect g t h sources) <-> natural_loop (base g) r h v.
Proof.
  intros g t r h sources Hgraph Hprepared Htree Hheader Hlatches.
  assert (Hsources : Forall (natural_loop (base g) r h) sources).
  { apply Forall_forall. intros v Hin. apply Hlatches in Hin.
    destruct Hin as [Hreach [Hedge Hdom]]. now apply loop_natural_latch. }
  pose proof (loop_collect_driver g t r h sources Hgraph Hprepared Htree) as Hdone.
  pose proof (loop_body_finished_semantic g t r h sources _ _ Hprepared Htree
    Hheader Hsources Hdone) as Hresult.
  assert (Hexact : forall v, In v (collect g t h sources) <-> natural_loop (base g) r h v).
  { apply (loop_body_result_exact g r h sources _ Hgraph Hprepared (proj1 Htree));
      [|exact Hresult].
    intros v Hreach Hedge Hdom. apply Hlatches. now repeat split. }
  split; [exact (proj1 (proj2 Hresult))|]. split; [|exact Hexact].
  intros v Hin. rewrite loop_nodes_verts.
  apply (loop_reachable_listed (base g) r v Hgraph (proj1 Htree)).
  apply (loop_member_reachable (base g) r h v), Hexact, Hin.
Qed.

Local Lemma loop_body_semantic_iteration : forall g t r h sources,
  prepared_ok g -> domtree_exact g r t -> natural_header (base g) r h ->
  Forall (natural_loop (base g) r h) sources -> forall n,
  loop_body_semantic g t r h sources
    (Nat.iter n (fun st => match body_step g t h st with
      | inl next => next | inr _ => st end)
      (LoopBodyState sources (PTrieCode.set h tt Empty) [h])).
Proof.
  intros g t r h sources Hprepared Htree Hheader Hsources n.
  induction n as [|n IH].
  - now apply loop_body_semantic_initial.
  - rewrite Nat.iter_succ.
    pose proof (loop_body_step_semantic g t r h sources _ Hprepared Htree IH) as Hstep.
    destruct (body_step g t h
      (Nat.iter n (fun st => match body_step g t h st with
        | inl next => next | inr _ => st end)
        (LoopBodyState sources (PTrieCode.set h tt Empty) [h])));
      [exact Hstep|exact IH].
Qed.


(** Charging only a closed output set still pays every queued expansion. *)
Local Lemma loop_body_work_step : forall g t h vertices st next,
  NoDup vertices -> incl (loop_body_pending st) vertices -> body_step g t h st = inl next ->
  2 * loop_unseen_work (fun v => 2 + length (preds g v)) vertices (loop_body_seen next) +
      length (loop_body_pending next) <
    2 * loop_unseen_work (fun v => 2 + length (preds g v)) vertices (loop_body_seen st) +
      length (loop_body_pending st).
Proof.
  intros g t h vertices [pending seen answer] next Hunique Hpending Hstep.
  destruct pending as [|v rest]; [discriminate Hstep|].
  cbn [body_step] in Hstep.
  destruct (trie_get v seen) as [[]|] eqn:Hseen;
    destruct (trie_get v (pre t)) as [a|] eqn:Hpre;
    injection Hstep as <-;
    try (cbn [loop_body_seen loop_body_pending length]; lia).
  pose proof (loop_unseen_work_fresh (fun x => 2 + length (preds g x))
    vertices seen v Hunique (Hpending v (or_introl eq_refl)) Hseen) as Hcredit.
  pose proof (filter_length_le (fun u => match trie_get u (pre t) with
    | Some _ => true | None => false end) (preds g v)) as Hlength.
  cbn [loop_body_seen loop_body_pending]. rewrite length_app, Hcredit.
  cbn beta. cbn [length]. lia.
Qed.


(** A present parentless vertex of an exact tree is its distinguished root. *)
Local Lemma loop_exact_root_iff g t r v : domtree_exact g r t ->
  ((exists n, trie_get v (pre t) = Some n) /\ trie_get v (idom t) = None <-> v = r).
Proof.
  intros [Hr [Hexact [Hwidth [Hchildren [Hunique [Hpre [Hpost Hinter]]]]]]].
  assert (Hreach_root : reach (base g) [r] r).
  { exists r, [r]. split; [now left|constructor]. }
  destruct Hexact as [Hparents [Hnone Hwf]]. split.
  - intros [Hpresent Hparent]. apply Hpre in Hpresent.
    destruct (Pos.eq_dec v r) as [Heq|Hne]; [exact Heq|].
    exfalso. apply (proj1 (Hnone v Hpresent) Hparent).
    exists r. split; [apply loop_root_dominates|congruence].
  - intros ->. split; [now apply Hpre|]. apply (proj2 (Hnone r Hreach_root)).
    intros [u [Hdom Hne]]. specialize (Hdom [r] (path_refl (base g) r)).
    destruct Hdom as [Heq|Hfalse]; [congruence|contradiction].
Qed.

(** Pending cursors describe a balanced sequence of child visits and ancestor returns. *)
Inductive loop_tasks_wf (g : prepared) (t : domtree) (r : positive)
    : list positive -> list loop_tree_task -> Prop :=
| loop_tasks_nil : loop_tasks_wf g t r [] []
| loop_tasks_root : forall v rest,
    In v (nodes g) -> loop_tasks_wf g t r [] rest ->
    loop_tasks_wf g t r [] (LoopTreeRoot v :: rest)
| loop_tasks_enter : forall v stack rest,
    (match stack with [] => v = r | p :: _ => trie_get v (idom t) = Some p end) ->
    loop_tasks_wf g t r stack rest ->
    loop_tasks_wf g t r stack (LoopTreeEnter v :: rest)
| loop_tasks_children : forall p stack vs rest,
    Forall (fun v => trie_get v (idom t) = Some p) vs ->
    loop_tasks_wf g t r (p :: stack) rest ->
    loop_tasks_wf g t r (p :: stack) (LoopTreeChildren vs :: rest)
| loop_tasks_edges : forall u stack vs rest,
    incl vs (succs (base g) u) -> loop_tasks_wf g t r (u :: stack) rest ->
    loop_tasks_wf g t r (u :: stack) (LoopTreeEdges u vs :: rest)
| loop_tasks_leave : forall v stack rest,
    loop_tasks_wf g t r stack rest ->
    loop_tasks_wf g t r (v :: stack) (LoopTreeLeave v :: rest).

Local Lemma loop_tasks_initial g t r :
  loop_tasks_wf g t r [] (map LoopTreeRoot (nodes g)).
Proof.
  assert (Hroots : forall xs, incl xs (nodes g) ->
    loop_tasks_wf g t r [] (map LoopTreeRoot xs)).
  { intro xs. induction xs as [|v xs IH]; intro Hincl; cbn [map]; [constructor|].
    constructor; [apply Hincl; now left|]. apply IH. intros x Hx. apply Hincl. now right. }
  apply Hroots. intros x Hx. exact Hx.
Qed.

Local Lemma loop_tasks_step g t r st next : domtree_exact g r t ->
  loop_tasks_wf g t r (loop_tree_stack st) (loop_tree_pending st) ->
  tree_step g t st = inl next ->
  loop_tasks_wf g t r (loop_tree_stack next) (loop_tree_pending next).
Proof.
  intros Hexact Htasks Hstep. destruct st as [tasks stack active scan].
  cbn [loop_tree_stack loop_tree_pending] in Htasks.
  inversion Htasks as [|v rest Hv Hrest|v stk rest Hv Hrest|
    p stk vs rest Hvs Hrest|u stk vs rest Hvs Hrest|v stk rest Hrest];
    subst; cbn [tree_step] in Hstep.
  - destruct scan. discriminate Hstep.
  - destruct (trie_get v (pre t)) as [n|] eqn:Hpre;
      destruct (trie_get v (idom t)) as [p|] eqn:Hparent;
      injection Hstep as <-; cbn [loop_tree_stack loop_tree_pending]; try assumption.
    constructor; [|assumption]. apply (proj1 (loop_exact_root_iff g t r v Hexact)).
    split; [now exists n|exact Hparent].
  - destruct scan as [order latches backs]. injection Hstep as <-.
    cbn [loop_tree_stack loop_tree_pending].
    apply loop_tasks_edges; [intros x Hx; exact Hx|].
    apply loop_tasks_children.
    + apply Forall_forall. intros x Hx. exact (proj1 (proj1 (proj2 (proj2 (proj2 Hexact))) v x) Hx).
    + now apply loop_tasks_leave.
  - destruct vs as [|v vs].
    + injection Hstep as <-. cbn [loop_tree_stack loop_tree_pending]. assumption.
    + inversion Hvs; subst. injection Hstep as <-. cbn [loop_tree_stack loop_tree_pending].
      apply loop_tasks_enter; [assumption|]. now apply loop_tasks_children.
  - destruct vs as [|v vs].
    + injection Hstep as <-. cbn [loop_tree_stack loop_tree_pending]. assumption.
    + destruct (trie_get v active) as [[]|].
      * destruct scan as [order latches backs]. injection Hstep as <-.
        cbn [loop_tree_stack loop_tree_pending]. apply loop_tasks_edges; [|assumption].
        intros x Hx. apply Hvs. now right.
      * injection Hstep as <-. cbn [loop_tree_stack loop_tree_pending].
        apply loop_tasks_edges; [|assumption]. intros x Hx. apply Hvs. now right.
  - injection Hstep as <-. cbn [loop_tail loop_tree_stack loop_tree_pending]. assumption.
Qed.

Module LoopsCode <: LOOPS_OPS.
  Definition forest (g : prepared) (t : domtree) :=
    let scan := classify g t in
    assemble (map (fun h => (h, collect g t h (loop_latches_at scan h)))
      (loop_headers_of scan)).

  Definition reducible_b (g : prepared) (t : domtree) :=
    let scan := classify g t in
    test_back (loop_back_rows scan)
      (prepared_search_trace g (loop_first (loop_order scan))).
End LoopsCode.

Module Loops <: LOOPS.
  Include LoopsCode.

  (** Every accumulated body vertex is marked before another pending task can add it. *)
  Local Definition body_distinct (st : loop_body_state) : Prop :=
    NoDup (loop_body_answer st) /\
    forall v, In v (loop_body_answer st) -> trie_get v (loop_body_seen st) = Some tt.

  Local Lemma body_step_distinct : forall g t h st,
    body_distinct st ->
    match body_step g t h st with
    | inl next => body_distinct next
    | inr result => NoDup result
    end.
  Proof.
    intros g t h [pending seen answer] [Hunique Hmarked].
    cbn [loop_body_answer loop_body_seen] in Hunique, Hmarked.
    destruct pending as [|v rest].
    - cbn [body_step]. rewrite rev_append_rev, app_nil_r. now apply NoDup_rev.
    - cbn [body_step].
      destruct (trie_get v seen) as [present|] eqn:Hseen;
        destruct (trie_get v (pre t)) as [number|] eqn:Hpre;
        try exact (conj Hunique Hmarked).
      cbn [body_distinct loop_body_answer loop_body_seen].
      split.
      + constructor; [|exact Hunique].
        intro Hin. specialize (Hmarked v Hin). congruence.
      + intros x [Heq|Hin].
        * subst x. apply PTrie.get_set_same.
        * destruct (Pos.eq_dec x v) as [->|Hne].
          -- apply PTrie.get_set_same.
          -- change (PTrie.get x (PTrie.set v tt seen) = Some tt).
             rewrite PTrie.get_set_other by exact Hne. now apply Hmarked.
  Qed.

  Local Lemma body_loop_distinct : forall g t h fs (Hacc : Acc loopN_lt fs),
    body_distinct (snd fs) ->
    match Argent.Loop.loop loopN_lt (loopN_step (body_step g t h)) fs Hacc with
    | inl final => body_distinct final
    | inr result => NoDup result
    end.
  Proof.
    intros g t h fs Hacc.
    induction Hacc as [[fuel st] Hnext IH] using Acc_ind_dep.
    cbn [snd]. intro Hdistinct. destruct fuel as [|fuel].
    - exact Hdistinct.
    - cbn [Argent.Loop.loop loopN_step Acc_inv].
      pose proof (body_step_distinct g t h st Hdistinct) as Hstep.
      destruct (body_step g t h st) as [next|result] eqn:Hresult.
      + apply IH. exact Hstep.
      + exact Hstep.
  Qed.

  (** Raw graphs and trees still produce distinct body rows, even when fuel expires. *)
  Local Lemma collect_distinct : forall g t h sources, NoDup (collect g t h sources).
  Proof.
    intros g t h sources.
    assert (Hinitial : body_distinct (LoopBodyState sources (PTrieCode.set h tt Empty) [h])).
    { split.
      - constructor; [simpl; tauto|constructor].
      - intros v [Heq|Hin]; [subst v; apply PTrie.get_set_same|contradiction]. }
    unfold collect, loopN.
    match goal with
    | |- context [Argent.Loop.loop _ _ ?fs ?Hacc] =>
        pose proof (body_loop_distinct g t h fs Hacc Hinitial) as Hloop
    end.
    match goal with
    | Hloop : context [Argent.Loop.loop ?lt ?step ?fs ?Hacc] |- _ =>
        destruct (Argent.Loop.loop lt step fs Hacc) as [final|result]
    end.
    - rewrite rev_append_rev, app_nil_r. apply NoDup_rev. exact (proj1 Hloop).
    - exact Hloop.
  Qed.

  Local Lemma install_distinct : forall l h vs,
    (forall key row, trie_get key (body l) = Some row -> NoDup row) -> NoDup vs ->
    forall key row, trie_get key (body (install l (h, vs))) = Some row -> NoDup row.
  Proof.
    intros [owners parents rows] h vs Hrows Hunique key row Hget.
    cbn [install loop_header_map loop_parent_map loop_body_map body] in Hget.
    change (PTrie.get key (PTrie.set h vs rows) = Some row) in Hget.
    destruct (Pos.eq_dec key h) as [->|Hne].
    - rewrite PTrie.get_set_same in Hget. now injection Hget as <-.
    - rewrite PTrie.get_set_other in Hget by exact Hne. now apply (Hrows key row).
  Qed.

  Local Lemma assemble_distinct : forall rows,
    Forall (fun entry => NoDup (snd entry)) rows ->
    forall l, (forall key row, trie_get key (body l) = Some row -> NoDup row) ->
    forall key row, trie_get key (body (fold_left install rows l)) = Some row -> NoDup row.
  Proof.
    intros rows Hrows. induction Hrows as [|[h vs] rows Hunique Hrows IH];
      intros l Hinitial key row Hget.
    - exact (Hinitial key row Hget).
    - eapply (IH (install l (h, vs))); [|exact Hget].
      apply install_distinct; assumption.
  Qed.

  Lemma headers_spec : forall g t r h,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    (exists vs, trie_get h (body (forest g t)) = Some vs) <-> natural_header (base g) r h.
  Proof. Admitted. (* STUB *)

  Lemma body_spec : forall g t r h v,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    In v (loop_body (forest g t) h) <-> natural_loop (base g) r h v.
  Proof. Admitted. (* STUB *)

  Lemma body_unique : forall g t h, NoDup (loop_body (forest g t) h).
  Proof.
    intros g t h.
    assert (Hrows : forall key row, trie_get key (body (forest g t)) = Some row -> NoDup row).
    { unfold forest, assemble. apply assemble_distinct.
      - apply Forall_forall. intros entry Hin. apply in_map_iff in Hin.
        destruct Hin as [key [<- Hkey]]. apply collect_distinct.
      - intros key row Hget. change (PTrie.get key PTrie.empty = Some row) in Hget.
        rewrite PTrie.get_empty in Hget. discriminate. }
    unfold loop_body. destruct (forest g t) as [owners parents rows].
    cbn [body] in Hrows.
    destruct (trie_get h rows) as [vs|] eqn:Hget; [now apply (Hrows h vs)|constructor].
  Qed.

  Lemma header_spec : forall g t r v h,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    trie_get v (header (forest g t)) = Some h <-> innermost_header (base g) r v h.
  Proof. Admitted. (* STUB *)

  Lemma parent_spec : forall g t r inner outer,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    trie_get inner (parent (forest g t)) = Some outer <->
    immediate_outer (base g) r inner outer.
  Proof. Admitted. (* STUB *)

  Lemma reducible_b_spec : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    reflect (reducible (base g) r) (reducible_b g t).
  Proof. Admitted. (* STUB *)
End Loops.

Module LoopsT <: LOOPS_ALL.
  Include Loops.

  TimeFun forest.
  TimeFun reducible_b.

  Definition c_loops : N := 1. (* STUB *)

  Lemma T_forest_le : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    (T_forest g t <= c_loops * N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
      N.of_nat (loop_depth g (forest g t) + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T_reducible_b_le : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    (T_reducible_b g t <= c_loops * N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
      N.of_nat (loop_depth g (forest g t) + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma forest_bigO : bigO (fun '(g, t, r) =>
      wf_graph (base g) /\ prepared_ok g /\ domtree_exact g r t)
    (fun '(g, t, _) => N.of_nat
      ((graph_n (base g) + graph_e (base g) + 1) *
        (loop_depth g (forest g t) + 1) * (graph_width (base g) + 1)))
    (fun '(g, t, _) => T_forest g t).
  Proof. Admitted. (* STUB *)

  Lemma reducible_b_bigO : bigO (fun '(g, t, r) =>
      wf_graph (base g) /\ prepared_ok g /\ domtree_exact g r t)
    (fun '(g, t, _) => N.of_nat
      ((graph_n (base g) + graph_e (base g) + 1) *
        (loop_depth g (forest g t) + 1) * (graph_width (base g) + 1)))
    (fun '(g, t, _) => T_reducible_b g t).
  Proof. Admitted. (* STUB *)

  Definition tree_step := tree_step.
  TimeFun tree_step.
  Definition classify := classify.
  TimeFun classify.
  Definition body_step := body_step.
  TimeFun body_step.
  Definition collect := collect.
  TimeFun collect.
  Definition install := install.
  TimeFun install.
  Definition assemble := assemble.
  TimeFun assemble.
  Definition retreat_trace := prepared_search_trace.
  TimeFun retreat_trace.
  Definition test_back := test_back.
  TimeFun test_back.

  (** Proof wrappers use the driver laws without expanding accessibility witnesses. *)
  Local Opaque loopN Argent.Loop.loop.

  Definition k_tree_step : N := 1. (* STUB *)
  Definition k_tree_stop : N := 8.
  Definition k_classify : N := 1. (* STUB *)
  Definition k_body_step : N := 1. (* STUB *)
  Definition k_body_stop : N := 8.
  Definition k_collect : N := 1. (* STUB *)
  Definition k_install : N := 1. (* STUB *)
  Definition k_trace : N := 1. (* STUB *)
  Definition k_test : N := 1. (* STUB *)
  Definition k_forest : N := 1. (* STUB *)
  Definition k_reducible : N := 16.

  Definition latches := loop_latches_at.
  Definition back_member scan u v : Prop :=
    exists row, trie_get u (loop_back_rows scan) = Some row /\ trie_get v row = Some tt.

  Definition tree_initial g :=
    LoopTreeState (map LoopTreeRoot (nodes g)) [] Empty (LoopScan [] Empty Empty).

  Definition tree_advance g t st :=
    match tree_step g t st with
    | inl next => next
    | inr _ => st
    end.

  Definition tree_invariant g t r st : Prop :=
    (exists n, Nat.iter n (tree_advance g t) (tree_initial g) = st) /\
    NoDup (loop_order (loop_tree_output st)) /\
    (forall v, In v (loop_order (loop_tree_output st)) -> reach (base g) [r] v) /\
    NoDup (loop_tree_stack st) /\
    (forall v, trie_get v (loop_tree_active st) = Some tt <-> In v (loop_tree_stack st)) /\
    Forall (fun uv => trie_get (fst uv) (idom t) = Some (snd uv))
      (combine (loop_tree_stack st) (tl (loop_tree_stack st))).

  Definition tree_pending st : nat :=
    fold_right (fun task n =>
      match task with
      | LoopTreeRoot _ => 2 + n
      | LoopTreeEnter _ | LoopTreeLeave _ => 1 + n
      | LoopTreeChildren vs => 2 * length vs + 1 + n
      | LoopTreeEdges _ vs => length vs + 1 + n
      end) 0 (loop_tree_pending st).

  Definition tree_white g t st : nat :=
    fold_right (fun v n =>
      if existsb (Pos.eqb v) (loop_order (loop_tree_output st)) then n
      else 4 + length (succs (base g) v) + 2 * length (children t v) + n) 0 (nodes g).

  Definition tree_potential g t st := N.of_nat (tree_white g t st + tree_pending st).

  Definition tree_credit g t st :=
    ((k_tree_step * N.of_nat (graph_width (base g) + 1) + 1) *
      tree_potential g t st)%N.

  Definition tree_fuel g : N := (8 * (nv g + ne g + 1))%N.

  Definition headers g t : list positive := loop_headers_of (classify g t).

  Definition collected g t h := collect g t h (latches (classify g t) h).

  Definition forest_rows g t : list (positive * list positive) :=
    let scan := classify g t in
    map (fun h => (h, collect g t h (latches scan h))) (loop_headers_of scan).

  Definition body_initial h sources :=
    LoopBodyState sources (PTrieCode.set h tt Empty) [h].

  Definition body_advance g t h st :=
    match body_step g t h st with
    | inl next => next
    | inr _ => st
    end.

  Definition body_invariant g t r h st : Prop :=
    (exists n, Nat.iter n (body_advance g t h)
      (body_initial h (latches (classify g t) h)) = st) /\
    NoDup (loop_body_answer st) /\ In h (loop_body_answer st) /\
    (forall v, trie_get v (loop_body_seen st) = Some tt <-> In v (loop_body_answer st)) /\
    incl (loop_body_answer st) (collected g t h) /\
    (forall v, In v (loop_body_pending st) -> reach (base g) [r] v).

  Definition body_white g t h st : nat :=
    fold_right (fun v n =>
      match trie_get v (loop_body_seen st) with
      | Some _ => n
      | None => 2 + length (preds g v) + n
      end) 0 (collected g t h).

  Definition body_potential g t h st :=
    N.of_nat (2 * body_white g t h st + length (loop_body_pending st)).

  Definition body_credit g t h st :=
    ((k_body_step * N.of_nat (graph_width (base g) + 1) + 1) *
      body_potential g t h st)%N.

  Definition body_fuel g (sources : list positive) : N :=
    (4 * (nv g + ne g + N.of_nat (length sources) + 1))%N.

  Definition body_work g vs : nat :=
    fold_right (fun v n => 1 + length (preds g v) + n) 0 vs.

  Definition forest_supported g l : Prop :=
    (forall v h, trie_get v (header l) = Some h -> In v (nodes g) /\ In h (nodes g)) /\
    (forall h p, trie_get h (parent l) = Some p -> In h (nodes g) /\ In p (nodes g)) /\
    forall h vs, trie_get h (body l) = Some vs -> In h (nodes g) /\ incl vs (nodes g).

  Definition assembly_prefix g t n :=
    fold_left install (firstn n (forest_rows g t)) (Loops Empty Empty Empty).

  Lemma F1_tree_initial : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    tree_invariant g t r (tree_initial g).
  Proof.
    intros g t r Hgraph Hprepared Htree.
    unfold tree_invariant, tree_initial.
    cbn [loop_tree_output loop_order loop_tree_stack loop_tree_active tl combine].
    split; [exists 0%nat; reflexivity|].
    split; [constructor|].
    split; [intros v Hin; contradiction|].
    split; [constructor|].
    split; [|constructor].
    intro v. change (PTrie.get v PTrie.empty = Some tt <-> In v []).
    rewrite PTrie.get_empty. simpl. split; [discriminate|contradiction].
  Qed.

  Lemma F2_tree_step : forall g t r st next,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    tree_invariant g t r st -> tree_step g t st = inl next ->
    tree_invariant g t r next /\ (tree_potential g t next < tree_potential g t st)%N.
  Proof. Admitted. (* STUB *)

  Lemma F3_tree_driver : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    loopN (tree_step g t) (tree_fuel g) (tree_initial g) = inr (classify g t).
  Proof. Admitted. (* STUB *)

  Lemma F4_tree_order : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    NoDup (loop_order (classify g t)) /\ hd_error (loop_order (classify g t)) = Some r /\
    (forall v, In v (loop_order (classify g t)) <-> reach (base g) [r] v) /\
    forall u v, reach (base g) [r] v -> strictly_dominates (base g) r u v ->
      order_before (loop_order (classify g t)) u v.
  Proof. Admitted. (* STUB *)

  Lemma F5_back_edges : forall g t r u v,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    (back_member (classify g t) u v <->
      reach (base g) [r] u /\ edge (base g) u v /\ dominates (base g) r v u) /\
    (In u (latches (classify g t) v) <-> back_member (classify g t) u v).
  Proof. Admitted. (* STUB *)

  Lemma F6_latch_count : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    NoDup (headers g t) /\ incl (headers g t) (nodes g) /\
    fold_right (fun h n => length (latches (classify g t) h) + n) 0 (headers g t) <=
      graph_e (base g).
  Proof. Admitted. (* STUB *)

  Local Lemma latch_exact : forall g t r h v,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    (In v (latches (classify g t) h) <->
      reach (base g) [r] v /\ edge (base g) v h /\ dominates (base g) r h v).
  Proof.
    intros g t r h v Hgraph Hprepared Htree.
    destruct (F5_back_edges g t r v h Hgraph Hprepared Htree) as [Hback Hlatch].
    now rewrite Hlatch, Hback.
  Qed.

  Local Lemma selected_header : forall g t r h,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In h (headers g t) ->
    natural_header (base g) r h.
  Proof.
    intros g t r h Hgraph Hprepared Htree Hin.
    unfold headers, loop_headers_of in Hin. apply filter_In in Hin.
    destruct Hin as [Horder Hselected].
    destruct (loop_latches_at (classify g t) h) as [|v rest] eqn:Hrow; [discriminate|].
    assert (Hmember : In v (latches (classify g t) h)).
    { unfold latches. rewrite Hrow. now left. }
    apply (proj1 (latch_exact g t r h v Hgraph Hprepared Htree)) in Hmember.
    now exists v.
  Qed.

  Local Lemma collected_exact : forall g t r h,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In h (headers g t) ->
    NoDup (collected g t h) /\ incl (collected g t h) (nodes g) /\
      forall v, In v (collected g t h) <-> natural_loop (base g) r h v.
  Proof.
    intros g t r h Hgraph Hprepared Htree Hheader.
    unfold collected, collect. apply (loop_collect_exact g t r h).
    - exact Hgraph.
    - exact Hprepared.
    - exact Htree.
    - now apply (selected_header g t r h).
    - intro v. now apply (latch_exact g t r h v).
  Qed.

  Local Lemma body_history_semantic : forall g t r h st,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In h (headers g t) ->
    (exists n, Nat.iter n (body_advance g t h)
      (body_initial h (latches (classify g t) h)) = st) ->
    loop_body_semantic g t r h (latches (classify g t) h) st.
  Proof.
    intros g t r h st Hgraph Hprepared Htree Hheader [n Hhistory].
    assert (Hsources : Forall (natural_loop (base g) r h) (latches (classify g t) h)).
    { apply Forall_forall. intros v Hin.
      apply (proj1 (latch_exact g t r h v Hgraph Hprepared Htree)) in Hin.
      destruct Hin as [Hreach [Hedge Hdom]]. now apply loop_natural_latch. }
    pose proof (loop_body_semantic_iteration g t r h (latches (classify g t) h)
      Hprepared Htree (selected_header g t r h Hgraph Hprepared Htree Hheader)
      Hsources n) as Hsemantic.
    change (loop_body_semantic g t r h (latches (classify g t) h)
      (Nat.iter n (body_advance g t h)
        (body_initial h (latches (classify g t) h)))) in Hsemantic.
    now rewrite Hhistory in Hsemantic.
  Qed.

  Local Lemma body_semantic_observed : forall g t r h st,
    (exists n, Nat.iter n (body_advance g t h)
      (body_initial h (latches (classify g t) h)) = st) ->
    (forall v, natural_loop (base g) r h v -> In v (collected g t h)) ->
    loop_body_semantic g t r h (latches (classify g t) h) st ->
    body_invariant g t r h st.
  Proof.
    intros g t r h st Hhistory Hcomplete
      [Hheader [Hunique [Hseen [Hanswer [Hpending [Hsources Hclosed]]]]]].
    split; [exact Hhistory|]. split; [exact Hunique|]. split; [exact Hheader|].
    split; [exact Hseen|]. split.
    - intros v Hin. apply Hcomplete. now apply (proj1 (Forall_forall _ _) Hanswer v).
    - intros v Hin. apply (loop_member_reachable (base g) r h v).
      now apply (proj1 (Forall_forall _ _) Hpending v).
  Qed.

  Lemma F7_body_initial : forall g t r h,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In h (headers g t) ->
    body_invariant g t r h (body_initial h (latches (classify g t) h)).
  Proof.
    intros g t r h Hgraph Hprepared Htree Hheader.
    unfold body_invariant, body_initial.
    cbn [loop_body_answer loop_body_seen loop_body_pending].
    split; [exists 0%nat; reflexivity|].
    split; [constructor; [simpl; tauto|constructor]|].
    split; [now left|]. split.
    - intro v. destruct (Pos.eq_dec v h) as [->|Hne].
      + change (PTrie.get h (PTrie.set h tt PTrie.empty) = Some tt <-> In h [h]).
        rewrite PTrie.get_set_same. split; [intros _; now left|intros _; reflexivity].
      + change (PTrie.get v (PTrie.set h tt PTrie.empty) = Some tt <-> In v [h]).
        rewrite PTrie.get_set_other by exact Hne. rewrite PTrie.get_empty.
        split; [discriminate|]. intros [Heq|Hfalse].
        * exfalso. apply Hne. now symmetry.
        * contradiction.
    - split.
      + intros v [<-|Hin]; [|contradiction]. unfold collected. apply loop_collect_header.
      + intros v Hin.
        destruct (F5_back_edges g t r v h Hgraph Hprepared Htree) as [Hback Hlatch].
        exact (proj1 (proj1 Hback (proj1 Hlatch Hin))).
  Qed.

  Lemma F8_body_step : forall g t r h st next,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In h (headers g t) ->
    body_invariant g t r h st -> body_step g t h st = inl next ->
    body_invariant g t r h next /\ (body_potential g t h next < body_potential g t h st)%N.
  Proof.
    intros g t r h st next Hgraph Hprepared Htree Hheader Hinv Hstep.
    pose proof (proj1 Hinv) as Hhistory.
    pose proof (body_history_semantic g t r h st Hgraph Hprepared Htree Hheader Hhistory)
      as Hsemantic.
    pose proof (loop_body_step_semantic g t r h (latches (classify g t) h) st
      Hprepared Htree Hsemantic) as Hnext.
    change (match body_step g t h st with
      | inl after => loop_body_semantic g t r h (latches (classify g t) h) after
      | inr result => loop_body_result g r h (latches (classify g t) h) result
      end) in Hnext.
    rewrite Hstep in Hnext.
    destruct (collected_exact g t r h Hgraph Hprepared Htree Hheader)
      as [Hunique [Hlisted Hexact]].
    split.
    - apply body_semantic_observed; [|intros v Hv; now apply Hexact|exact Hnext].
      destruct Hhistory as [n Hhistory]. exists (S n). rewrite Nat.iter_succ, Hhistory.
      unfold body_advance. now rewrite Hstep.
    - assert (Hpending : incl (loop_body_pending st) (collected g t h)).
      { intros v Hin. apply Hexact.
        destruct Hsemantic as [_ [_ [_ [_ [Hpending _]]]]].
        now apply (proj1 (Forall_forall _ _) Hpending v). }
      pose proof (loop_body_work_step g t h (collected g t h) st next
        Hunique Hpending Hstep) as Hprogress.
      unfold body_potential, body_white. unfold loop_unseen_work in Hprogress. lia.
  Qed.


  Lemma F9_body_driver : forall g t r h,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In h (headers g t) ->
    loopN (body_step g t h) (body_fuel g (latches (classify g t) h))
      (body_initial h (latches (classify g t) h)) = inr (collected g t h).
  Proof.
    intros g t r h Hgraph Hprepared Htree Hheader.
    unfold body_fuel, body_initial, collected, collect, body_step.
    exact (loop_collect_driver g t r h _ Hgraph Hprepared Htree).
  Qed.


  Lemma F10_body_exact : forall g t r h,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In h (headers g t) ->
    NoDup (collected g t h) /\ incl (collected g t h) (nodes g) /\
      forall v, In v (collected g t h) <-> natural_loop (base g) r h v.
  Proof.
    intros g t r h Hgraph Hprepared Htree Hheader.
    now apply (collected_exact g t r h).
  Qed.


  Lemma F11_laminar : forall g r h outer v,
    natural_loop g r h v -> natural_loop g r outer v -> h <> outer ->
    loop_inside g r h outer \/ loop_inside g r outer h.
  Proof.
    intros g r h outer v Hinner Houter Hne.
    pose proof (loop_member_reachable g r h v Hinner) as Hreach.
    pose proof (loop_header_dominates g r h v Hinner) as Hinnerdom.
    pose proof (loop_header_dominates g r outer v Houter) as Houterdom.
    destruct (loop_dominators_comparable g r h outer v Hreach Hinnerdom Houterdom)
      as [Hfirst|Hsecond].
    - right. assert (Hreverse : outer <> h) by congruence.
      exact (loop_member_containment g r outer h (proj1 Houter)
        (loop_meeting_header g r outer h v Houter Hinner Hfirst Hreverse) Hfirst Hreverse).
    - left. exact (loop_member_containment g r h outer (proj1 Hinner)
        (loop_meeting_header g r h outer v Hinner Houter Hsecond Hne) Hsecond Hne).
  Qed.

  Lemma F12_header_order : forall g t r inner outer,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    loop_inside (base g) r inner outer -> order_before (headers g t) outer inner.
  Proof.
    intros g t r inner outer Hgraph Hprepared Htree
      [Hne [Hinner [Houter Hcontained]]].
    assert (Hselected : forall h, natural_header (base g) r h ->
      match loop_latches_at (classify g t) h with [] => false | _ => true end = true).
    { intros h [latch [Hreach [Hedge Hdom]]].
      destruct (F5_back_edges g t r latch h Hgraph Hprepared Htree) as [Hback Hlatch].
      assert (Hin : In latch (latches (classify g t) h)).
      { apply (proj2 Hlatch), (proj2 Hback). repeat split; assumption. }
      change (In latch (loop_latches_at (classify g t) h)) in Hin.
      destruct (loop_latches_at (classify g t) h); [contradiction|reflexivity]. }
    assert (Hmember : natural_loop (base g) r outer inner).
    { apply Hcontained. split; [exact Hinner|now left]. }
    pose proof (loop_header_dominates (base g) r outer inner Hmember) as Hdom.
    destruct (F4_tree_order g t r Hgraph Hprepared Htree) as [_ [_ [_ Horder]]].
    cbv beta delta [headers loop_headers_of]. apply loop_order_filter.
    - apply Horder.
      + now apply loop_header_reachable.
      + split; [exact Hdom|congruence].
    - now apply Hselected.
    - now apply Hselected.
  Qed.

  Lemma F13_install : forall l h vs,
    body (install l (h, vs)) = PTrieCode.set h vs (body l) /\
    parent (install l (h, vs)) =
      match trie_get h (header l) with
      | Some outer => PTrieCode.set h outer (parent l)
      | None => parent l
      end /\
    header (install l (h, vs)) =
      fold_left (fun owners v => PTrieCode.set v h owners) vs (header l).
  Proof.
    intros [owners parents rows] h vs.
    repeat split; reflexivity.
  Qed.

  Lemma F14_assembly : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    (forall n, forest_supported g (assembly_prefix g t n)) /\
    (forall v h,
      trie_get v (header (assembly_prefix g t (length (headers g t)))) = Some h <->
        innermost_header (base g) r v h) /\
    forall h outer,
      trie_get h (parent (assembly_prefix g t (length (headers g t)))) = Some outer <->
        immediate_outer (base g) r h outer.
  Proof. Admitted. (* STUB *)

  Lemma F15_forest_equation : forall g t,
    forest g t = fold_left install (forest_rows g t) (Loops Empty Empty Empty).
  Proof.
    intros g t. unfold forest_rows, install, collect, classify, latches.
    unfold forest. apply loop_assemble_equation.
  Qed.

  Lemma F15a_assemble : forall rows,
    assemble rows = fold_left install rows (Loops Empty Empty Empty).
  Proof.
    reflexivity.
  Qed.

  Lemma F16_nesting_charge : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    fold_right (fun h n => body_work g (collected g t h) + n) 0 (headers g t) <=
      (graph_n (base g) + graph_e (base g)) * loop_depth g (forest g t).
  Proof. Admitted. (* STUB *)

  Lemma F17_retreat_trace : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    exists final, dfs_roots (base g) []
      (firstn 1 (loop_order (classify g t)))
      (retreat_trace g (firstn 1 (loop_order (classify g t)))) final.
  Proof.
    intros g t r Hgraph Hprepared Htree.
    destruct (F4_tree_order g t r Hgraph Hprepared Htree) as [_ [Hroot _]].
    pose proof (loop_first_head (loop_order (classify g t)) r Hroot) as Hfirst.
    assert (Hlisted : forall v,
      In v (firstn 1 (loop_order (classify g t))) -> In v (nodes g)).
    { intros v Hin. rewrite Hfirst in Hin.
      destruct Hin as [<-|Hin]; [|contradiction].
      exact (loop_tree_root_listed g r t Htree). }
    apply loop_trace_valid.
    - exact (conj (proj1 Hprepared) (proj1 (proj2 Hprepared))).
    - exact Hgraph.
    - exact Hlisted.
  Qed.

  Lemma F18_test_back : forall scan es,
    test_back (loop_back_rows scan) es = true <->
      forall u v, In (Edge Back u v) es -> back_member scan u v.
  Proof.
    intros scan es.
    change ((forallb (fun e => match e with
      | Edge Back u v => match trie_get u (loop_back_rows scan) with
        | Some row => match trie_get v row with Some _ => true | None => false end
        | None => false
        end
      | _ => true
      end) es = true) <->
      forall u v, In (Edge Back u v) es -> back_member scan u v).
    rewrite forallb_forall. split.
    - intros Hall u v Hin. specialize (Hall (Edge Back u v) Hin).
      cbn in Hall. unfold back_member.
      destruct (trie_get u (loop_back_rows scan)) as [row|] eqn:Hrow;
        [|discriminate].
      destruct (trie_get v row) as [[]|] eqn:Hget; [|discriminate].
      now exists row.
    - intros Hall e Hin. destruct e as [v|v|kind u v]; try reflexivity.
      destruct kind; try reflexivity.
      destruct (Hall u v Hin) as [row [Hrow Hget]]. now rewrite Hrow, Hget.
  Qed.

  Lemma F19_retreat_reflect : forall g r es final,
    dfs_roots g [] [r] es final ->
    ((forall u v, In (Edge Back u v) es -> dominates g r v u) <-> reducible g r).
  Proof.
    intros g r es final Hdfs. split.
    - intros Hback u v [other [last [Hother Hin]]].
      destruct (loop_dfs_roots_deterministic g [] [r] es final Hdfs other last Hother)
        as [Hsame _]. subst other. now apply Hback.
    - intros Hreducible u v Hin. apply Hreducible. now exists es, final.
  Qed.

  Lemma F20_reducible_equation : forall g t,
    reducible_b g t = test_back (loop_back_rows (classify g t))
      (retreat_trace g (firstn 1 (loop_order (classify g t)))).
  Proof.
    intros g t. unfold reducible_b, classify, test_back, retreat_trace.
    now rewrite loop_first_equation.
  Qed.

  Lemma T1_tree_step : forall g t r st next,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    tree_invariant g t r st -> tree_step g t st = inl next ->
    (T_tree_step g t st + tree_credit g t next + c_loopN <= tree_credit g t st)%N.
  Proof. Admitted. (* STUB *)

  Lemma T2_tree_stop : forall g t r st scan,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    tree_invariant g t r st -> tree_step g t st = inr scan ->
    (T_tree_step g t st <= k_tree_stop * N.of_nat (graph_n (base g) + 1))%N.
  Proof.
    intros g t r st scan Hgraph Hprepared Htree Hinv Hstep.
    pose proof (loop_tree_stopping g t st scan Hstep) as Hempty.
    destruct st as [pending stack active [order latches backs]].
    cbn [loop_tree_pending] in Hempty. subst pending.
    destruct Hinv as [_ [Hunique [Hreach _]]].
    cbn [loop_tree_output loop_order] in Hunique, Hreach.
    assert (Hlisted : incl order (verts (base g))).
    { intros v Hin. apply (loop_reachable_listed (base g) r v Hgraph (proj1 Htree)).
      now apply Hreach. }
    pose proof (@NoDup_incl_length positive order (verts (base g)) Hunique Hlisted) as Hlength.
    assert (Hsize : length (verts (base g)) = graph_n (base g)).
    { destruct (base g); reflexivity. }
    rewrite Hsize in Hlength.
    pose proof (loop_tree_stop_clock g t stack active order latches backs) as Hclock.
    unfold T_tree_step. time_simpl.
    unfold k_tree_stop. rewrite !Nat2N.inj_add in Hclock |- *. lia.
  Qed.

  Lemma T3_classify : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    (T_classify g t <= k_classify *
      N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T4_body_step : forall g t r h st next,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In h (headers g t) ->
    body_invariant g t r h st -> body_step g t h st = inl next ->
    (T_body_step g t h st + body_credit g t h next + c_loopN <= body_credit g t h st)%N.
  Proof. Admitted. (* STUB *)

  Lemma T5_body_stop : forall g t r h st result,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In h (headers g t) ->
    body_invariant g t r h st -> body_step g t h st = inr result ->
    (T_body_step g t h st <= k_body_stop * N.of_nat (length (collected g t h) + 1))%N.
  Proof.
    intros g t r h st result Hgraph Hprepared Htree Hheader Hinv Hstep.
    pose proof (loop_body_stopping g t h st result Hstep) as Hempty.
    destruct st as [pending seen answer].
    cbn [loop_body_pending] in Hempty. subst pending.
    destruct Hinv as [_ [Hunique [_ [_ [Hsubset _]]]]].
    cbn [loop_body_answer] in Hunique, Hsubset.
    pose proof (@NoDup_incl_length positive answer (collected g t h) Hunique Hsubset) as Hlength.
    pose proof (loop_body_stop_clock g t h seen answer) as Hclock.
    unfold T_body_step. time_simpl.
    unfold k_body_stop. rewrite !Nat2N.inj_add in Hclock |- *. lia.
  Qed.

  Lemma T6_collect : forall g t r h,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In h (headers g t) ->
    (T_collect g t h (latches (classify g t) h) <= k_collect *
      (N.of_nat (body_work g (collected g t h) +
        length (latches (classify g t) h) + 1) *
        N.of_nat (graph_width (base g) + 1) +
        N.of_nat (N.size_nat (body_fuel g (latches (classify g t) h)))))%N.
  Proof. Admitted. (* STUB *)

  Lemma T7_install : forall g l h vs,
    forest_supported g l -> In h (nodes g) -> incl vs (nodes g) ->
    (T_install l (h, vs) <= k_install * N.of_nat (length vs + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T7a_assemble : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    (T_assemble (forest_rows g t) <= k_install *
      N.of_nat
        (fold_right (fun h n => (length (collected g t h) + 1 + n)%nat)
          0%nat (headers g t) + 1) * N.of_nat (graph_width (base g) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T7b_fuel_widths : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    (fold_right (fun h cost =>
      N.of_nat (N.size_nat (body_fuel g (latches (classify g t) h))) + cost)%N
        0%N (headers g t) <= k_collect *
      N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
        N.of_nat (graph_width (base g) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T7c_forest_wrapper : forall g t,
    (T_forest g t <= k_forest * (T_classify g t +
      fold_right (fun h cost =>
        T_collect g t h (latches (classify g t) h) + cost)%N 0%N (headers g t) +
      T_assemble (forest_rows g t) +
      N.of_nat (graph_n (base g) + 1) * N.of_nat (graph_width (base g) + 1) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T8_forest : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    (T_forest g t <= c_loops *
      N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
      N.of_nat (loop_depth g (forest g t) + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T9_retreat_test : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    (T_retreat_trace g (firstn 1 (loop_order (classify g t))) +
      T_test_back (loop_back_rows (classify g t))
        (retreat_trace g (firstn 1 (loop_order (classify g t)))) <=
      (k_trace + k_test) * N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
        N.of_nat (graph_width (base g) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T10_reducible_wrapper : forall g t,
    (T_reducible_b g t <= k_reducible * (T_classify g t +
      T_retreat_trace g (firstn 1 (loop_order (classify g t))) +
      T_test_back (loop_back_rows (classify g t))
        (retreat_trace g (firstn 1 (loop_order (classify g t)))) + 1))%N.
  Proof.
    intros g t.
    pose proof (loop_first_clock_bound (loop_order (classify g t))) as Hfirst.
    unfold classify in Hfirst.
    unfold T_reducible_b, T_classify, T_retreat_trace, T_test_back,
      classify, retreat_trace, k_reducible.
    time_simpl. rewrite !loop_first_equation. lia.
  Qed.

  Lemma T11_reducible_public : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    (T_reducible_b g t <= c_loops *
      N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
      N.of_nat (loop_depth g (forest g t) + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
  Proof. Admitted. (* STUB *)
End LoopsT.
