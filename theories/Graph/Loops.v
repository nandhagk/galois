(** * Natural loop forests

    Dominator-tree traversal classifies back edges and builds their reverse closures.
    For example, a self-edge produces a one-vertex natural loop.
    Builds on: prepared graphs, dominator trees and depth-first traces. *)

From Stdlib Require Import PArith NArith Arith Lia List Bool.
From Stdlib.Sorting Require Import Permutation.
From Argent Require Import Time Tactics Std BigO Loop.
From Galois.Base Require Import Key Trie Loop.
From Galois.Graph Require Import Data Spec DigraphSig SearchSig Search DomSig DomOrder LoopsSig.
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


(** Key operations and loop dispatch have one fixed unit scale. *)
Local Definition loop_body_unit_cost : N := (PTrieT.c_trie + c_loopN + 1)%N.
Local Definition loop_body_step_cost : N := (64 * loop_body_unit_cost)%N.

Local Lemma loop_predecessor_listed : forall g u v,
  prepared_ok g -> In u (preds g v) -> In u (nodes g).
Proof.
  intros g u v [_ [_ Hpred]] Hin. apply (Permutation_in u (Hpred v)) in Hin.
  apply in_flat_map in Hin. destruct Hin as [source [Hsource Hrow]].
  apply in_map_iff in Hrow. destruct Hrow as [target [Heq Htarget]]. now subst source.
Qed.

Local Lemma loop_vertex_width_member : forall vertices v,
  In v vertices -> Pos.size_nat v <= vertex_width vertices.
Proof.
  intros vertices. induction vertices as [|u rest IH]; intros v Hin; [contradiction|].
  unfold vertex_width at 1. cbn [fold_right]. fold (vertex_width rest).
  change graph_max with Nat.max. destruct Hin as [<-|Hin].
  - apply Nat.le_max_l.
  - eapply Nat.le_trans; [now apply IH|apply Nat.le_max_r].
Qed.

Local Lemma loop_listed_width : forall g v,
  In v (nodes g) -> Pos.size_nat v <= graph_width (base g).
Proof.
  intros [[vertices adjacency] predecessors vertex_count edge_count] v Hin.
  cbn [nodes base graph_width] in Hin |- *. change graph_max with Nat.max.
  eapply Nat.le_trans; [exact (loop_vertex_width_member vertices v Hin)|apply Nat.le_max_l].
Qed.

Local Lemma loop_filter_clock_bound {A : Type} (test : A -> bool) (clock : A -> N) :
  forall xs cost,
  (forall x, In x xs -> (clock x <= cost)%N) ->
  (List.T_filter test clock xs <= (cost + 1) * N.of_nat (length xs) + 1)%N.
Proof.
  intro xs. induction xs as [|x rest IH]; intros cost Hclock.
  - time_unfold List.T_filter. cbn [length]. lia.
  - pose proof (Hclock x (or_introl eq_refl)) as Hhead.
    specialize (IH cost (fun y Hy => Hclock y (or_intror Hy))).
    time_unfold List.T_filter. cbn [length]. rewrite Nat2N.inj_succ.
    destruct (test x); lia.
Qed.

Local Lemma loop_preds_clock : forall g v,
  (T_preds g v <= 2 * N.of_nat (Pos.size_nat v) + 1)%N.
Proof.
  intros [graph predecessors vertex_count edge_count] v.
  unfold T_preds. time_simpl. rewrite PTrieT.trie_get_clock. lia.
Qed.

(** Retiring an already marked or unreachable task only reads its two key cells. *)
Local Lemma loop_body_skip_clock : forall g t h v rest seen answer width,
  Pos.size_nat v <= width ->
  (trie_get v seen = Some tt \/ trie_get v (pre t) = None) ->
  (T_body_step g t h (LoopBodyState (v :: rest) seen answer) + c_loopN + 1 <=
    loop_body_step_cost * N.of_nat (width + 1))%N.
Proof.
  intros g t h v rest seen answer width Hv Hskip.
  apply time_of_nat_le in Hv. unfold loop_body_step_cost, loop_body_unit_cost.
  unfold T_body_step, T_pre. time_simpl. rewrite !PTrieT.trie_get_clock.
  rewrite Nat2N.inj_add. destruct Hskip as [Hseen|Hpre].
  - rewrite Hseen. destruct (trie_get v (pre t)); nia.
  - rewrite Hpre. destruct (trie_get v seen); nia.
Qed.

(** A fresh task charges each filtered predecessor and append cell once. *)
Local Lemma loop_body_fresh_clock : forall g t h v rest seen answer width a,
  Pos.size_nat v <= width ->
  (forall u, In u (preds g v) -> Pos.size_nat u <= width) ->
  trie_get v seen = None -> trie_get v (pre t) = Some a ->
  (T_body_step g t h (LoopBodyState (v :: rest) seen answer) + c_loopN + 1 <=
    loop_body_step_cost * N.of_nat (width + 1) * N.of_nat (length (preds g v) + 1))%N.
Proof.
  intros g t h v rest seen answer width a Hv Hwidth Hseen Hpre.
  pose proof (PTrieT.T_set_le unit v tt seen) as Hset.
  pose proof (loop_preds_clock g v) as Hpreds.
  pose proof (filter_length_le (fun u => match trie_get u (pre t) with
    | Some _ => true | None => false end) (preds g v)) as Hlength.
  apply time_of_nat_le in Hv.
  unfold T_body_step, T_pre. time_simpl. rewrite Hseen, Hpre.
  rewrite !PTrieT.trie_get_clock.
  match goal with
  | |- context [List.T_filter ?test ?clock (preds g v)] =>
      assert (Hfilter : (List.T_filter test clock (preds g v) <=
        (8 * N.of_nat (width + 1) + 1) * N.of_nat (length (preds g v)) + 1)%N)
  end.
  { apply loop_filter_clock_bound. intros u Hin.
    pose proof (Hwidth u Hin) as Hu. apply time_of_nat_le in Hu.
    cbn beta. rewrite PTrieT.trie_get_clock. rewrite Nat2N.inj_add. nia. }
  match goal with
  | |- context [Datatypes.T_app ?xs rest] =>
      pose proof (Datatypes.T_app_le xs rest) as Happ
  end.
  unfold loop_body_step_cost, loop_body_unit_cost.
  rewrite !Nat2N.inj_add in Hset, Hfilter |- *. nia.
Qed.

Local Lemma loop_body_fresh_work : forall g vertices v rest seen,
  NoDup vertices -> In v vertices -> trie_get v seen = None -> forall queued,
  length queued <= length (preds g v) ->
  2 * loop_unseen_work (fun x => 2 + length (preds g x)) vertices
        (PTrieCode.set v tt seen) + length (queued ++ rest) + length (preds g v) + 1 <=
    2 * loop_unseen_work (fun x => 2 + length (preds g x)) vertices seen +
      length (v :: rest).
Proof.
  intros g vertices v rest seen Hunique Hin Hfresh queued Hlength.
  pose proof (loop_unseen_work_fresh (fun x => 2 + length (preds g x))
    vertices seen v Hunique Hin Hfresh) as Hwork.
  rewrite length_app, Hwork. cbn beta. cbn [length]. lia.
Qed.

Local Lemma loop_body_step_behavior : forall g t h v rest seen answer next,
  body_step g t h (LoopBodyState (v :: rest) seen answer) = inl next ->
  (next = LoopBodyState rest seen answer /\
    (trie_get v seen = Some tt \/ trie_get v (pre t) = None)) \/
  exists a, next = LoopBodyState
    (filter (fun u => match trie_get u (pre t) with
      | Some _ => true | None => false end) (preds g v) ++ rest)
    (PTrieCode.set v tt seen) (v :: answer) /\
    trie_get v seen = None /\ trie_get v (pre t) = Some a.
Proof.
  intros g t h v rest seen answer next Hstep. cbn [body_step] in Hstep.
  destruct (trie_get v seen) as [[]|] eqn:Hseen;
    destruct (trie_get v (pre t)) as [a|] eqn:Hpre; injection Hstep as <-.
  - left. split; [reflexivity|now left].
  - left. split; [reflexivity|now left].
  - right. exists a. repeat split; reflexivity.
  - left. split; [reflexivity|now right].
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

(** Exact-root discovery supplies the absent parent at the bottom of every stack. *)
Local Lemma loop_exact_root_none g t r : domtree_exact g r t ->
  trie_get r (idom t) = None.
Proof.
  intro Htree. exact (proj2 (proj2 (loop_exact_root_iff g t r r Htree) eq_refl)).
Qed.

(** A nonempty active stack is the parent chain from its head down to the root. *)
Inductive loop_stack_chain (m : ptrie positive) (r : positive) : list positive -> Prop :=
| loop_stack_empty : loop_stack_chain m r []
| loop_stack_root : loop_stack_chain m r [r]
| loop_stack_push : forall v p stack, trie_get v m = Some p ->
    loop_stack_chain m r (p :: stack) -> loop_stack_chain m r (v :: p :: stack).

Local Lemma loop_stack_tail m r stack : loop_stack_chain m r stack ->
  loop_stack_chain m r (loop_tail stack).
Proof.
  intro Hchain. destruct Hchain; cbn [loop_tail]; constructor || assumption.
Qed.

Local Lemma loop_stack_links m r stack : loop_stack_chain m r stack ->
  Forall (fun uv => trie_get (fst uv) m = Some (snd uv)) (combine stack (tl stack)).
Proof.
  intro Hchain. induction Hchain; cbn [combine tl fst snd] in *;
    constructor; assumption.
Qed.

Local Lemma loop_stack_ancestors m r stack : trie_get r m = None ->
  loop_stack_chain m r stack -> forall v, hd_error stack = Some v ->
  forall x, In x stack <-> tree_anc m x v.
Proof.
  intros Hroot Hchain. induction Hchain as [| |v p stack Hparent Hchain IH];
    intros head Hhead x.
  - discriminate Hhead.
  - cbn [hd_error] in Hhead. injection Hhead as <-. cbn [In]. split.
    + intros [Heq|Hfalse]; [subst x; constructor|contradiction].
    + intro Hanc. destruct (dom_cert_anc_cases m x r Hanc) as [Heq|[q [Hq Hancq]]].
      * now left.
      * rewrite Hroot in Hq. discriminate Hq.
  - cbn [hd_error] in Hhead. injection Hhead as <-.
    specialize (IH p eq_refl x). change (v = x \/ In x (p :: stack) <-> tree_anc m x v).
    split.
    + intros [Heq|Hin]; [subst x; constructor|].
      eapply tree_anc_step; [exact Hparent|now apply IH].
    + intro Hanc. destruct (dom_cert_anc_cases m x v Hanc) as [Heq|[q [Hq Hancq]]].
      * now left.
      * rewrite Hparent in Hq. injection Hq as <-. right. now apply IH.
Qed.

Local Lemma loop_stack_unique m r stack :
  well_founded (fun u v => trie_get v m = Some u) -> trie_get r m = None ->
  loop_stack_chain m r stack -> NoDup stack.
Proof.
  intros Hwf Hroot Hchain. induction Hchain as [| |v p stack Hparent Hchain IH].
  - constructor.
  - constructor; [intro H; contradiction|constructor].
  - constructor; [|exact IH]. intro Hin.
    pose proof (proj1 (loop_stack_ancestors m r (p :: stack) Hroot Hchain p eq_refl v) Hin)
      as Hanc.
    exact (dom_map_no_return m p (Hwf p) v Hparent Hanc).
Qed.

Local Lemma loop_stack_reachable g r m stack : dom_exact g r m ->
  loop_stack_chain m r stack -> Forall (reach (base g) [r]) stack.
Proof.
  intros Hexact Hchain. induction Hchain as [| |v p stack Hparent Hchain IH].
  - constructor.
  - constructor; [exists r, [r]; split; [now left|constructor]|constructor].
  - constructor; [exact (proj1 (proj2 (proj1 Hexact v p Hparent)))|exact IH].
Qed.

Local Lemma loop_active_push active stack v :
  (forall x, trie_get x active = Some tt <-> In x stack) ->
  forall x, trie_get x (PTrieCode.set v tt active) = Some tt <-> In x (v :: stack).
Proof.
  intros Hagree x. destruct (Pos.eq_dec x v) as [->|Hne].
  - rewrite PTrie.get_set_same. cbn [In]. tauto.
  - rewrite PTrie.get_set_other by exact Hne. rewrite Hagree. cbn [In].
    split; [now right|]. intros [Heq|Hin]; [congruence|exact Hin].
Qed.

Local Lemma loop_active_pop active stack v : ~ In v stack ->
  (forall x, trie_get x active = Some tt <-> In x (v :: stack)) ->
  forall x, trie_get x (PTrieCode.remove v active) = Some tt <-> In x stack.
Proof.
  intros Hfresh Hagree x. destruct (Pos.eq_dec x v) as [->|Hne].
  - rewrite PTrie.get_remove_same. split; [discriminate|intro Hin; contradiction].
  - rewrite PTrie.get_remove_other by exact Hne. rewrite Hagree. cbn [In].
    split; [|now right]. intros [Heq|Hin]; [congruence|exact Hin].
Qed.

Local Definition loop_stack_state t r st : Prop :=
  loop_stack_chain (idom t) r (loop_tree_stack st) /\
  forall x, trie_get x (loop_tree_active st) = Some tt <-> In x (loop_tree_stack st).

Local Lemma loop_stack_state_step g t r st next : domtree_exact g r t ->
  loop_tasks_wf g t r (loop_tree_stack st) (loop_tree_pending st) ->
  loop_stack_state t r st -> tree_step g t st = inl next -> loop_stack_state t r next.
Proof.
  intros Htree Htasks [Hchain Hagree] Hstep. destruct st as [tasks stack active scan].
  cbn [loop_tree_stack loop_tree_pending loop_tree_active] in Htasks, Hchain, Hagree.
  pose proof (loop_exact_root_none g t r Htree) as Hroot.
  pose proof (proj2 (proj2 (proj1 (proj2 Htree)))) as Hwf.
  inversion Htasks as [|v rest Hv Hrest|v stk rest Hv Hrest|
    p stk vs rest Hvs Hrest|u stk vs rest Hvs Hrest|v stk rest Hrest];
    subst; cbn [tree_step] in Hstep.
  - destruct scan. discriminate Hstep.
  - destruct (trie_get v (pre t)) as [n|]; destruct (trie_get v (idom t)) as [p|];
      injection Hstep as <-; split; cbn [loop_tree_stack loop_tree_active]; assumption.
  - destruct scan as [order latches backs]. injection Hstep as <-. split.
    + cbn [loop_tree_stack]. destruct stack as [|p stack].
      * cbn in Hv. subst v. constructor.
      * cbn in Hv. now apply loop_stack_push.
    + cbn [loop_tree_stack loop_tree_active]. now apply loop_active_push.
  - destruct vs as [|v vs]; injection Hstep as <-;
      split; cbn [loop_tree_stack loop_tree_active]; assumption.
  - destruct vs as [|v vs].
    + injection Hstep as <-. split; cbn [loop_tree_stack loop_tree_active]; assumption.
    + destruct (trie_get v active) as [[]|]; [destruct scan as [order latches backs]|];
        injection Hstep as <-; split; cbn [loop_tree_stack loop_tree_active]; assumption.
  - injection Hstep as <-. split.
    + cbn [loop_tree_stack]. exact (loop_stack_tail (idom t) r (v :: stk) Hchain).
    + cbn [loop_tree_stack loop_tree_active loop_tail]. apply loop_active_pop; [|exact Hagree].
      pose proof (loop_stack_unique (idom t) r (v :: stk) Hwf Hroot Hchain) as Hunique.
      now inversion Hunique.
Qed.

(** Every ancestor of a reachable target is reachable in an exact parent map. *)
Local Lemma loop_ancestor_reachable g r m u v : dom_exact g r m ->
  tree_anc m u v -> reach (base g) [r] v -> reach (base g) [r] u.
Proof.
  intros Hexact Hanc. induction Hanc as [|p v Hparent Hanc IH]; intro Hreach.
  - exact Hreach.
  - apply IH. exact (proj1 (proj1 Hexact v p Hparent)).
Qed.

(** A subtree consists of its root and the subtrees of its immediate children. *)
Local Lemma loop_ancestor_children t v x :
  (forall p c, In c (children t p) <-> trie_get c (idom t) = Some p) ->
  (tree_anc (idom t) v x <-> x = v \/
    exists c, In c (children t v) /\ tree_anc (idom t) c x).
Proof.
  intro Hchildren. split.
  - intro Hanc. induction Hanc as [|p x Hparent Hanc IH]; [now left|].
    destruct IH as [->|[c [Hc Hcx]]].
    + right. exists x. split; [now apply Hchildren|constructor].
    + right. exists c. split; [exact Hc|]. eapply tree_anc_step; eassumption.
  - intros [->|[c [Hc Hcx]]]; [constructor|].
    eapply dom_cert_anc_trans; [|exact Hcx].
    eapply tree_anc_step; [exact (proj1 (Hchildren v c) Hc)|constructor].
Qed.

(** Two siblings cannot be distinct ancestors of the same vertex. *)
Local Lemma loop_sibling_ancestor m p a b :
  well_founded (fun u v => trie_get v m = Some u) ->
  trie_get a m = Some p -> trie_get b m = Some p -> tree_anc m a b -> a = b.
Proof.
  intros Hwf Ha Hb Hanc. destruct (Pos.eq_dec a b) as [Heq|Hne]; [exact Heq|].
  exfalso. apply (dom_map_no_return m p (Hwf p) a Ha).
  eapply dom_cert_anc_parent; eassumption.
Qed.

Local Lemma loop_sibling_disjoint m p a b x :
  well_founded (fun u v => trie_get v m = Some u) ->
  trie_get a m = Some p -> trie_get b m = Some p ->
  tree_anc m a x -> tree_anc m b x -> a = b.
Proof.
  intros Hwf Ha Hb Hax Hbx.
  destruct (dom_anc_chain_comparable m a b x Hax Hbx) as [Hab|Hba].
  - eapply loop_sibling_ancestor; eassumption.
  - symmetry. eapply loop_sibling_ancestor; eassumption.
Qed.

(** Entered vertices and pairwise disjoint pending subtrees partition the reachable tree. *)
Record loop_partition (g : prepared) (t : domtree) (r : positive)
    (seen future : list positive) : Prop := {
  loop_partition_seen_unique : NoDup seen;
  loop_partition_future_unique : NoDup future;
  loop_partition_seen_live : forall x, In x seen -> reach (base g) [r] x;
  loop_partition_future_live : forall x, In x future -> reach (base g) [r] x;
  loop_partition_separate : forall a x, In a future -> tree_anc (idom t) a x -> ~ In x seen;
  loop_partition_disjoint : forall a b x, In a future -> In b future ->
    tree_anc (idom t) a x -> tree_anc (idom t) b x -> a = b;
  loop_partition_cover : forall x, reach (base g) [r] x ->
    In x seen \/ exists a, In a future /\ tree_anc (idom t) a x
}.

Local Lemma loop_partition_root g t r : domtree_exact g r t ->
  loop_partition g t r [] [r].
Proof.
  intro Htree. pose proof (proj1 (proj2 Htree)) as Hexact. constructor.
  - constructor.
  - constructor; [intro H; contradiction|constructor].
  - intros x H; contradiction.
  - intros x [<-|H]; [|contradiction]. exists r, [r]. split; [now left|constructor].
  - intros a x Ha Hanc Hseen. contradiction.
  - intros a b x [<-|Ha] [<-|Hb] Hax Hbx; try contradiction; reflexivity.
  - intros x Hreach. right. exists r. split; [now left|].
    apply (dom_exact_dominates_anc g r (idom t) r x Hexact Hreach).
    apply loop_root_dominates.
Qed.

(** Entering one root replaces its future subtree by distinct child subtrees. *)
Local Lemma loop_partition_enter g t r seen v future : domtree_exact g r t ->
  loop_partition g t r seen (v :: future) ->
  loop_partition g t r (v :: seen) (children t v ++ future).
Proof.
  intros Htree Hpart.
  destruct Htree as [Hr [Hexact [Hwidth [Hchildren [Hrows [Hpre [Hpost Hinter]]]]]]].
  pose proof (proj2 (proj2 Hexact)) as Hwf.
  destruct Hpart as [Hseen Hfuture Hseen_live Hfuture_live Hseparate Hdisjoint Hcover].
  inversion Hfuture as [|head tail Hfresh Htail]; subst head tail.
  assert (Hv_live : reach (base g) [r] v) by (apply Hfuture_live; now left).
  assert (Hv_seen : ~ In v seen).
  { apply (Hseparate v v); [now left|constructor]. }
  assert (Hchild_anc : forall c, In c (children t v) -> tree_anc (idom t) v c).
  { intros c Hc. eapply tree_anc_step; [exact (proj1 (Hchildren v c) Hc)|constructor]. }
  assert (Hchild_old : forall c, In c (children t v) -> ~ In c future).
  { intros c Hc Hcfuture.
    assert (Heq : v = c).
    { apply (Hdisjoint v c c); [now left|now right|now apply Hchild_anc|constructor]. }
    subst c. contradiction. }
  constructor.
  - now constructor.
  - apply NoDup_app; [exact (proj1 (Hrows v))|exact Htail|exact Hchild_old].
  - intros x [<-|Hx]; [exact Hv_live|now apply Hseen_live].
  - intros x Hx. apply in_app_iff in Hx as [Hchild|Hfuturex].
    + exact (proj1 (proj2 (proj1 Hexact x v (proj1 (Hchildren v x) Hchild)))).
    + apply Hfuture_live. now right.
  - intros a x Ha Hax Hx. apply in_app_iff in Ha as [Hchild|Ha].
    + destruct Hx as [Heq|Hx].
      * subst x. apply (dom_map_no_return (idom t) v (Hwf v) a
          (proj1 (Hchildren v a) Hchild)). exact Hax.
      * apply (Hseparate v x (or_introl eq_refl)); [|exact Hx].
        eapply dom_cert_anc_trans; [exact (Hchild_anc a Hchild)|exact Hax].
    + destruct Hx as [Heq|Hx].
      * subst x. assert (Heq : a = v).
        { apply (Hdisjoint a v v); [now right|now left|exact Hax|constructor]. }
        subst a. contradiction.
      * apply (Hseparate a x (or_intror Ha) Hax Hx).
  - intros a b x Ha Hb Hax Hbx.
    apply in_app_iff in Ha as [Ha|Ha]; apply in_app_iff in Hb as [Hb|Hb].
    + apply (loop_sibling_disjoint (idom t) v a b x Hwf);
        [now apply Hchildren|now apply Hchildren|exact Hax|exact Hbx].
    + exfalso. assert (Heq : v = b).
      { apply (Hdisjoint v b x); [now left|now right| |exact Hbx].
        eapply dom_cert_anc_trans; [exact (Hchild_anc a Ha)|exact Hax]. }
      subst b. contradiction.
    + exfalso. assert (Heq : a = v).
      { apply (Hdisjoint a v x); [now right|now left|exact Hax|].
        eapply dom_cert_anc_trans; [exact (Hchild_anc b Hb)|exact Hbx]. }
      subst a. contradiction.
    + apply (Hdisjoint a b x); [now right|now right|exact Hax|exact Hbx].
  - intros x Hlive. destruct (Hcover x Hlive) as [Hx|[a [[Ha|Ha] Hax]]].
    + left. now right.
    + subst a. apply (proj1 (loop_ancestor_children t v x Hchildren)) in Hax.
      destruct Hax as [->|[c [Hc Hcx]]].
      * left. now left.
      * right. exists c. split; [apply in_or_app; now left|exact Hcx].
    + right. exists a. split; [apply in_or_app; now right|exact Hax].
Qed.

(** Proper ancestors of a pending root have already been entered. *)
Local Lemma loop_partition_ancestors_seen g t r seen future v u :
  dom_exact g r (idom t) -> loop_partition g t r seen future ->
  In v future -> tree_anc (idom t) u v -> u <> v -> In u seen.
Proof.
  intros Hexact Hpart Hv Hanc Hne.
  destruct Hpart as [Hseen Hfuture Hseen_live Hfuture_live Hseparate Hdisjoint Hcover].
  assert (Hu : reach (base g) [r] u).
  { eapply loop_ancestor_reachable; [exact Hexact|exact Hanc|now apply Hfuture_live]. }
  destruct (Hcover u Hu) as [Hu_seen|[a [Ha Hau]]]; [exact Hu_seen|].
  assert (Hav : tree_anc (idom t) a v) by (eapply dom_cert_anc_trans; eassumption).
  assert (Heq : a = v) by (apply (Hdisjoint a v v Ha Hv Hav); constructor).
  subst a. exfalso. apply Hne.
  eapply dom_anc_wf_antisym; [exact (proj2 (proj2 Hexact))|exact Hanc|exact Hau].
Qed.


(** Unary source counts pay for binary conversion through amortized carries. *)
Local Fixpoint loop_positive_credit (p : positive) : N :=
  match p with
  | xH => 1%N
  | xO q => loop_positive_credit q
  | xI q => (1 + loop_positive_credit q)%N
  end.

Local Lemma loop_positive_succ_clock : forall p,
  (Pos.T_succ p + loop_positive_credit (Pos.succ p) <=
    2 + loop_positive_credit p)%N.
Proof.
  intro p. induction p as [p IH|p IH|]; time_unfold Pos.T_succ;
    cbn [Pos.succ loop_positive_credit]; lia.
Qed.

Local Lemma loop_of_succ_nat_clock : forall n,
  (Key.Pos.T_of_succ_nat n + loop_positive_credit (Pos.of_succ_nat n) <=
    3 * N.of_nat n + 2)%N.
Proof.
  intro n. induction n as [|n IH]; time_unfold Key.Pos.T_of_succ_nat.
  - reflexivity.
  - pose proof (loop_positive_succ_clock (Pos.of_succ_nat n)) as Hcarry.
    cbn [Pos.of_succ_nat]. lia.
Qed.

Local Lemma loop_of_nat_clock : forall n,
  (TimeHelpers.N.T_of_nat n <= 3 * N.of_nat n + 2)%N.
Proof.
  intros [|n]; time_unfold TimeHelpers.N.T_of_nat; [lia|].
  pose proof (loop_of_succ_nat_clock n). lia.
Qed.

Local Lemma loop_size_monotone : forall n m,
  (n <= m)%N -> N.size_nat n <= N.size_nat m.
Proof.
  intros [|p] [|q] Hle; cbn [N.size_nat]; try lia.
  destruct (Pos.eq_dec p q) as [->|Hne]; [reflexivity|].
  apply Pos.size_nat_monotone. change (N.pos p < N.pos q)%N. lia.
Qed.

Local Lemma loop_four_clock : forall n, (Code.N.T_mul 4 n <= 4)%N.
Proof.
  intros [|p]; time_unfold Code.N.T_mul; try lia.
  do 3 time_unfold Pos.T_mul. time_cbn. lia.
Qed.

(** Every intermediate binary sum fits the fuel whose bit count the plan charges. *)
Local Lemma loop_fuel_setup_clock : forall vertices edges sources,
  (N.T_add vertices edges + N.T_add (vertices + edges) sources +
    N.T_add (vertices + edges + sources) 1 + Code.N.T_mul 4 (vertices + edges + sources + 1) <=
    8 * N.of_nat (N.size_nat (4 * (vertices + edges + sources + 1))) + 8)%N.
Proof.
  intros vertices edges sources.
  pose proof (N.T_add_le vertices edges) as Hfirst.
  pose proof (N.T_add_le (vertices + edges) sources) as Hsecond.
  pose proof (N.T_add_le (vertices + edges + sources) 1) as Hlast.
  pose proof (loop_four_clock (vertices + edges + sources + 1)) as Hfour.
  set (fuel := (4 * (vertices + edges + sources + 1))%N) in *.
  assert (Hwidth : forall n, (n <= fuel)%N ->
    (N.of_nat (N.size_nat n) <= N.of_nat (N.size_nat fuel))%N).
  { intros n Hn. apply time_of_nat_le. now apply loop_size_monotone. }
  pose proof (Hwidth vertices ltac:(unfold fuel; lia)) as Hv.
  pose proof (Hwidth edges ltac:(unfold fuel; lia)) as He.
  pose proof (Hwidth (vertices + edges)%N ltac:(unfold fuel; lia)) as Hve.
  pose proof (Hwidth sources ltac:(unfold fuel; lia)) as Hs.
  pose proof (Hwidth (vertices + edges + sources)%N ltac:(unfold fuel; lia)) as Hves.
  pose proof (Hwidth 1%N ltac:(unfold fuel; lia)) as Hone.
  rewrite !Nat2N.inj_add in Hfirst, Hsecond, Hlast. lia.
Qed.

Local Definition loop_body_clock g t h := fun st => T_body_step g t h st.
Local Definition loop_collect_cost : N := (4096 * (c_loopN + 1) * loop_body_unit_cost)%N.

(** Successful collection pays setup once and exposes the actual binary-loop clock. *)
Local Lemma loop_collect_clock_wrapper : forall g t h sources result width,
  Pos.size_nat h <= width ->
  loopN (body_step g t h) (4 * (nv g + ne g + N.of_nat (length sources) + 1))%N
    (LoopBodyState sources (PTrieCode.set h tt Empty) [h]) = inr result ->
  (T_collect g t h sources + 1 <=
    T_loopN (body_step g t h) (loop_body_clock g t h)
      (4 * (nv g + ne g + N.of_nat (length sources) + 1))%N
      (LoopBodyState sources (PTrieCode.set h tt Empty) [h]) +
    32 * loop_body_unit_cost *
      (N.of_nat (width + length sources + 1) +
        N.of_nat (N.size_nat (4 * (nv g + ne g + N.of_nat (length sources) + 1)))))%N.
Proof.
  intros g t h sources result width Hwidth Hdone.
  pose proof (PTrieT.T_set_le unit h tt Empty) as Hset.
  pose proof (Datatypes.T_length_le sources) as Hlength.
  pose proof (loop_of_nat_clock (length sources)) as Hconvert.
  pose proof (loop_fuel_setup_clock (nv g) (ne g) (N.of_nat (length sources))) as Hfuel.
  apply time_of_nat_le in Hwidth.
  unfold T_collect, loop_body_clock. time_simpl. rewrite Hdone.
  unfold T_nv, T_ne. time_simpl.
  unfold loop_body_unit_cost. repeat rewrite Nat2N.inj_add in Hset |- *. nia.
Qed.

Local Lemma loop_unseen_body_work : forall g vertices seen,
  loop_unseen_work (fun v => 2 + length (preds g v)) vertices seen <=
    2 * fold_right (fun v n => 1 + length (preds g v) + n) 0 vertices.
Proof.
  intros g vertices seen. eapply Nat.le_trans; [apply loop_unseen_work_bound|].
  induction vertices as [|v rest IH]; cbn [fold_right]; lia.
Qed.

(** Callback, stop, setup and fuel-bit costs fit one closed collection scale. *)
Local Lemma loop_collect_arithmetic : forall overhead unit width work inputs bits,
  (1 <= unit -> 1 <= width ->
    overhead * ((64 * unit * width + 1) * (4 * work + inputs) +
      8 * (work + 1) + bits + 1) + 32 * unit * (width + inputs + bits) <=
    4096 * (overhead + 1) * unit * ((work + inputs + 1) * width + bits))%N.
Proof.
  intros overhead unit width work inputs bits Hunit Hwidth.
  set (total := ((work + inputs + 1) * width + bits)%N).
  assert (Hinside : ((64 * unit * width + 1) * (4 * work + inputs) +
    8 * (work + 1) + bits + 1 <= 512 * unit * total)%N) by (unfold total; nia).
  assert (Hsetup : (32 * unit * (width + inputs + bits) <= 32 * unit * total)%N)
    by (unfold total; nia).
  assert (Hpaid : (overhead * ((64 * unit * width + 1) * (4 * work + inputs) +
    8 * (work + 1) + bits + 1) <= overhead * (512 * unit * total))%N).
  { apply N.mul_le_mono_l. exact Hinside. }
  nia.
Qed.


(** A geometric tail pays the bit positions beyond the graph's key width. *)
Local Lemma loop_width_geometric : forall width extra,
  width + extra + 1 <= (width + 1) * 2 ^ extra.
Proof.
  intros width extra. induction extra as [|extra IH]; cbn [Nat.pow]; nia.
Qed.

Local Lemma loop_positive_size_lower : forall p,
  2 ^ (Pos.size_nat p - 1) <= Pos.to_nat p.
Proof.
  intro p. destruct (Nat.le_gt_cases (2 ^ (Pos.size_nat p - 1)) (Pos.to_nat p))
    as [Hle|Hlt]; [exact Hle|].
  pose proof (Pos.size_nat_least p (Pos.size_nat p - 1) Hlt) as Hsize.
  assert (Hpositive : 0 < Pos.size_nat p) by (destruct p; cbn [Pos.size_nat]; lia).
  lia.
Qed.

Local Lemma loop_size_lower : forall n,
  n <> 0%N -> 2 ^ (N.size_nat n - 1) <= N.to_nat n.
Proof.
  intros [|p] Hne; [contradiction|]. apply loop_positive_size_lower.
Qed.

(** Distinct graph keys pay a logarithm for every header even when edge multiplicity is large. *)
Local Lemma loop_count_log_product : forall count total width,
  count < 2 ^ width -> count <= total ->
  count * N.size_nat (N.of_nat total) <= total * (width + 1).
Proof.
  intros count total width Hcount Htotal.
  set (bits := N.size_nat (N.of_nat total)).
  destruct (Nat.le_gt_cases bits width) as [Hsmall|Hlarge]; [nia|].
  assert (Hpositive : N.of_nat total <> 0%N).
  { intro Heq. unfold bits in Hlarge. rewrite Heq in Hlarge.
    cbn [N.size_nat] in Hlarge. lia. }
  pose proof (loop_size_lower (N.of_nat total) Hpositive) as Hlower.
  rewrite Nat2N.id in Hlower. fold bits in Hlower.
  set (extra := bits - S width).
  assert (Hbits : bits = width + extra + 1) by (unfold extra; lia).
  pose proof (loop_width_geometric width extra) as Hgeometric.
  assert (Hpower : 2 ^ (bits - 1) = 2 ^ width * 2 ^ extra).
  { replace (bits - 1) with (width + extra) by lia. apply Nat.pow_add_r. }
  eapply Nat.le_trans with (2 ^ width * bits).
  - apply Nat.mul_le_mono_r. lia.
  - eapply Nat.le_trans with (2 ^ width * ((width + 1) * 2 ^ extra)).
    + apply Nat.mul_le_mono_l. now rewrite Hbits.
    + replace (2 ^ width * ((width + 1) * 2 ^ extra)) with
        ((width + 1) * 2 ^ (bits - 1)) by (rewrite Hpower; nia).
      rewrite (Nat.mul_comm total (width + 1)). now apply Nat.mul_le_mono_l.
Qed.

Local Lemma loop_size_eight : forall n,
  N.size_nat (8 * n) <= N.size_nat n + 3.
Proof.
  intros [|p]; cbn [N.mul Pos.mul N.size_nat Pos.size_nat]; lia.
Qed.

Local Lemma loop_sum_member_le {A : Type} : forall (xs : list A) (f : A -> nat) x,
  In x xs -> f x <= fold_right (fun y total => f y + total) 0 xs.
Proof.
  intro xs. induction xs as [|y rest IH]; intros f x Hin; [contradiction|].
  cbn [fold_right]. destruct Hin as [<-|Hin]; [lia|].
  specialize (IH f x Hin). lia.
Qed.

Local Lemma loop_sum_uniform {A : Type} : forall (xs : list A) (f : A -> nat) bound,
  (forall x, In x xs -> f x <= bound) ->
  fold_right (fun x total => f x + total) 0 xs <= length xs * bound.
Proof.
  intro xs. induction xs as [|x rest IH]; intros f bound Hbound; [cbn; lia|].
  cbn [fold_right length]. pose proof (Hbound x (or_introl eq_refl)) as Hhead.
  specialize (IH f bound ltac:(intros y Hy; apply Hbound; now right)). lia.
Qed.

Local Lemma loop_sum_of_nat {A : Type} : forall (xs : list A) (f : A -> nat),
  fold_right (fun x total => N.of_nat (f x) + total)%N 0%N xs =
    N.of_nat (fold_right (fun x total => f x + total) 0 xs).
Proof.
  intro xs. induction xs as [|x rest IH]; intro f; [reflexivity|].
  cbn [fold_right]. now rewrite IH, Nat2N.inj_add.
Qed.

(** Fold clocks only need a callback bound at keys that occur in their input list. *)
Local Lemma loop_fold_clock_bound {A B : Type} (f : A -> B -> A) (clock : A -> B -> N) :
  forall xs cost initial,
  (forall acc x, In x xs -> (clock acc x <= cost)%N) ->
  (List.T_fold_left f clock xs initial <= (cost + 1) * N.of_nat (length xs) + 1)%N.
Proof.
  intro xs. induction xs as [|x rest IH]; intros cost initial Hclock.
  - time_unfold List.T_fold_left. cbn [length]. lia.
  - pose proof (Hclock initial x (or_introl eq_refl)) as Hhead.
    specialize (IH cost (f initial x)
      (fun acc y Hy => Hclock acc y (or_intror Hy))).
    time_unfold List.T_fold_left. cbn [length]. rewrite Nat2N.inj_succ. lia.
Qed.

Local Definition loop_install_step_cost : N := (64 * (PTrieT.c_trie + 1))%N.
Local Definition loop_install_cost : N := (128 * (PTrieT.c_trie + 1))%N.

(** Installing a row only uses its header and body members as trie keys. *)
Local Lemma loop_install_clock : forall l h vertices width,
  Pos.size_nat h <= width ->
  (forall v, In v vertices -> Pos.size_nat v <= width) ->
  (T_install l (h, vertices) + 2 <= loop_install_step_cost *
    N.of_nat (length vertices + 1) * N.of_nat (width + 1))%N.
Proof.
  intros [owners parents bodies] h vertices width Hheader Hvertices.
  pose proof (PTrieT.T_set_le (list positive) h vertices bodies) as Hbody.
  apply time_of_nat_le in Hheader.
  unfold T_install, T_loop_header_map, T_loop_parent_map, T_loop_body_map. time_simpl.
  cbn [loop_header_map loop_parent_map loop_body_map].
  rewrite PTrieT.trie_get_clock.
  match goal with
  | |- context [List.T_fold_left ?f ?clock vertices owners] =>
      assert (Hfold : (List.T_fold_left f clock vertices owners <=
        (8 * (PTrieT.c_trie + 1) * N.of_nat (width + 1) + 1) * N.of_nat (length vertices) + 1)%N)
  end.
  { apply loop_fold_clock_bound. intros acc v Hin.
    pose proof (PTrieT.T_set_le positive v h acc) as Hset.
    pose proof (Hvertices v Hin) as Hwidth. apply time_of_nat_le in Hwidth.
    cbn beta. repeat rewrite Nat2N.inj_add in Hset |- *. nia. }
  unfold loop_install_step_cost. repeat rewrite Nat2N.inj_add in Hbody, Hfold |- *.
  destruct (trie_get h owners) as [outer|].
  - pose proof (PTrieT.T_set_le positive h outer parents) as Hparent.
    repeat rewrite Nat2N.inj_add in Hparent. nia.
  - nia.
Qed.

(** The outer fold adds one constant per row to the sum of installation costs. *)
Local Lemma loop_assemble_clock : forall rows width,
  (forall h vertices, In (h, vertices) rows ->
    Pos.size_nat h <= width /\ forall v, In v vertices -> Pos.size_nat v <= width) ->
  (T_assemble rows + 1 <= loop_install_cost *
    N.of_nat (fold_right (fun entry total => (length (snd entry) + 1 + total)%nat) 0%nat rows + 1) *
      N.of_nat (width + 1))%N.
Proof.
  intros rows width Hwidth.
  assert (Hfold : forall entries initial,
    (forall h vertices, In (h, vertices) entries ->
      Pos.size_nat h <= width /\ forall v, In v vertices -> Pos.size_nat v <= width) ->
    (List.T_fold_left install (fun acc entry => T_install acc entry) entries initial <=
      loop_install_step_cost *
        N.of_nat (fold_right (fun entry total => (length (snd entry) + 1 + total)%nat) 0%nat entries) *
          N.of_nat (width + 1) + 1)%N).
  { intro entries. induction entries as [|[h vertices] rest IH]; intros initial Hentries.
    - time_unfold List.T_fold_left. cbn [fold_right]. lia.
    - destruct (Hentries h vertices (or_introl eq_refl)) as [Hheader Hvertices].
      pose proof (loop_install_clock initial h vertices width Hheader Hvertices) as Hinstall.
      specialize (IH (install initial (h, vertices))
        (fun k vs Hin => Hentries k vs (or_intror Hin))).
      time_unfold List.T_fold_left. cbn [fold_right snd].
      repeat rewrite Nat2N.inj_add in Hinstall |- *. nia. }
  specialize (Hfold rows (Loops Empty Empty Empty) Hwidth).
  unfold T_assemble. time_simpl.
  unfold loop_install_cost, loop_install_step_cost in Hfold |- *.
  repeat rewrite Nat2N.inj_add. nia.
Qed.

Local Lemma loop_fold_map {A B C : Type} (f : B -> C -> C) (key : A -> B) (zero : C) :
  forall xs, fold_right f zero (map key xs) =
    fold_right (fun x total => f (key x) total) zero xs.
Proof.
  intro xs. induction xs as [|x rest IH]; cbn [map fold_right]; [reflexivity|now rewrite IH].
Qed.

(** Root tasks contribute a subtree only when their vertex has no parent and is present. *)
Local Definition loop_root_test (t : domtree) (v : positive) : bool :=
  match trie_get v (pre t), trie_get v (idom t) with
  | Some _, None => true
  | _, _ => false
  end.

Local Lemma loop_root_test_spec t v : loop_root_test t v = true <->
  (exists n, trie_get v (pre t) = Some n) /\ trie_get v (idom t) = None.
Proof.
  unfold loop_root_test.
  destruct (trie_get v (pre t)) as [n|]; destruct (trie_get v (idom t)) as [p|].
  - split; [discriminate|intros [_ Hnone]; discriminate].
  - split; [intros _; split; [now exists n|reflexivity]|intros _; reflexivity].
  - split; [discriminate|intros [[a Ha] _]; discriminate].
  - split; [discriminate|intros [[a Ha] _]; discriminate].
Qed.

Local Lemma loop_root_test_exact g t r v : domtree_exact g r t ->
  (loop_root_test t v = true <-> v = r).
Proof.
  intro Htree. rewrite loop_root_test_spec. exact (loop_exact_root_iff g t r v Htree).
Qed.

Local Definition loop_task_roots (t : domtree) (task : loop_tree_task) : list positive :=
  match task with
  | LoopTreeRoot v => if loop_root_test t v then [v] else []
  | LoopTreeEnter v => [v]
  | LoopTreeChildren vs => vs
  | LoopTreeEdges _ _ | LoopTreeLeave _ => []
  end.

Local Definition loop_future (t : domtree) (tasks : list loop_tree_task) : list positive :=
  flat_map (loop_task_roots t) tasks.

Local Lemma loop_future_roots t vertices :
  loop_future t (map LoopTreeRoot vertices) = filter (loop_root_test t) vertices.
Proof.
  unfold loop_future. induction vertices as [|v rest IH];
    cbn [map flat_map loop_task_roots filter]; [reflexivity|].
  rewrite IH. destruct (loop_root_test t v); reflexivity.
Qed.

Local Lemma loop_unique_singleton (xs : list positive) r : NoDup xs -> In r xs ->
  (forall x, In x xs -> x = r) -> xs = [r].
Proof.
  intros Hunique Hr Hall. destruct xs as [|v xs]; [contradiction|].
  assert (Hv : v = r) by (apply Hall; now left). subst v.
  inversion Hunique as [|head tail Hfresh Htail]; subst head tail.
  f_equal. destruct xs as [|x xs]; [reflexivity|]. exfalso. apply Hfresh.
  assert (Hx : x = r) by (apply Hall; now right; left). subst x. now left.
Qed.

Local Lemma loop_future_initial g t r : wf_graph (base g) -> domtree_exact g r t ->
  loop_future t (map LoopTreeRoot (nodes g)) = [r].
Proof.
  intros Hgraph Htree. rewrite loop_future_roots. apply loop_unique_singleton.
  - apply NoDup_filter. now apply loop_nodes_unique.
  - apply filter_In. split.
    + rewrite loop_nodes_verts. exact (proj1 Htree).
    + apply (proj2 (loop_root_test_exact g t r r Htree)). reflexivity.
  - intros x Hx. apply filter_In in Hx as [_ Htest].
    exact (proj1 (loop_root_test_exact g t r x Htree) Htest).
Qed.

Local Definition loop_partition_state g t r st : Prop :=
  loop_partition g t r (loop_order (loop_tree_output st))
    (loop_future t (loop_tree_pending st)).

Local Lemma loop_partition_initial g t r : wf_graph (base g) -> domtree_exact g r t ->
  loop_partition_state g t r
    (LoopTreeState (map LoopTreeRoot (nodes g)) [] Empty (LoopScan [] Empty Empty)).
Proof.
  intros Hgraph Htree. unfold loop_partition_state.
  cbn [loop_tree_output loop_tree_pending loop_order].
  rewrite (loop_future_initial g t r Hgraph Htree). now apply loop_partition_root.
Qed.

(** Only entry changes the partition; all other cursors preserve the same pending roots. *)
Local Lemma loop_partition_step g t r st next : domtree_exact g r t ->
  loop_partition_state g t r st -> tree_step g t st = inl next ->
  loop_partition_state g t r next.
Proof.
  intros Htree Hpart Hstep. destruct st as [tasks stack active [order latches backs]].
  destruct tasks as [|task rest]; [discriminate Hstep|].
  destruct task as [v|v|vs|u vs|v]; cbn [tree_step] in Hstep.
  - destruct (trie_get v (pre t)) as [n|] eqn:Hpre;
      destruct (trie_get v (idom t)) as [p|] eqn:Hparent;
      injection Hstep as <-; unfold loop_partition_state in *;
      cbn [loop_tree_output loop_tree_pending loop_order loop_future flat_map
        loop_task_roots loop_root_test app] in *;
      unfold loop_root_test in Hpart; rewrite Hpre in Hpart;
      try rewrite Hparent in Hpart; exact Hpart.
  - injection Hstep as <-. unfold loop_partition_state in *.
    cbn [loop_tree_output loop_tree_pending loop_order loop_future flat_map
      loop_task_roots app] in *.
    now apply loop_partition_enter.
  - destruct vs as [|v vs]; injection Hstep as <-; unfold loop_partition_state in *;
      cbn [loop_tree_output loop_tree_pending loop_order loop_future flat_map
        loop_task_roots app] in *; exact Hpart.
  - destruct vs as [|v vs].
    + injection Hstep as <-. unfold loop_partition_state in *.
      cbn [loop_tree_output loop_tree_pending loop_order loop_future flat_map
        loop_task_roots app] in *; exact Hpart.
    + destruct (trie_get v active) as [[]|]; injection Hstep as <-;
        unfold loop_partition_state in *;
        cbn [loop_tree_output loop_tree_pending loop_order loop_future flat_map
          loop_task_roots app] in *; exact Hpart.
  - injection Hstep as <-. unfold loop_partition_state in *.
    cbn [loop_tree_output loop_tree_pending loop_order loop_future flat_map
      loop_task_roots app] in *; exact Hpart.
Qed.

(** The reachable-state invariant combines balanced tasks, the ancestor stack and a partition. *)
Local Definition loop_tree_core g t r st : Prop :=
  loop_tasks_wf g t r (loop_tree_stack st) (loop_tree_pending st) /\
  loop_stack_state t r st /\ loop_partition_state g t r st.

Local Lemma loop_tree_core_initial g t r : wf_graph (base g) -> domtree_exact g r t ->
  loop_tree_core g t r
    (LoopTreeState (map LoopTreeRoot (nodes g)) [] Empty (LoopScan [] Empty Empty)).
Proof.
  intros Hgraph Htree. split.
  - apply loop_tasks_initial.
  - split; [|now apply loop_partition_initial].
    split; [constructor|]. intro x. cbn [loop_tree_active loop_tree_stack].
    rewrite PTrie.get_empty. split; [discriminate|contradiction].
Qed.

Local Lemma loop_tree_core_step g t r st next : domtree_exact g r t ->
  loop_tree_core g t r st -> tree_step g t st = inl next -> loop_tree_core g t r next.
Proof.
  intros Htree [Htasks [Hstack Hpartition]] Hstep. split.
  - exact (loop_tasks_step g t r st next Htree Htasks Hstep).
  - split.
    + exact (loop_stack_state_step g t r st next Htree Htasks Hstack Hstep).
    + exact (loop_partition_step g t r st next Htree Hpartition Hstep).
Qed.

Local Lemma loop_tree_core_iteration g t r : wf_graph (base g) -> domtree_exact g r t ->
  forall n, loop_tree_core g t r
    (Nat.iter n (fun st => match tree_step g t st with inl next => next | inr _ => st end)
      (LoopTreeState (map LoopTreeRoot (nodes g)) [] Empty (LoopScan [] Empty Empty))).
Proof.
  intros Hgraph Htree n. induction n as [|n IH].
  - now apply loop_tree_core_initial.
  - rewrite Nat.iter_succ.
    destruct (tree_step g t (Nat.iter n
      (fun st => match tree_step g t st with inl next => next | inr _ => st end)
      (LoopTreeState (map LoopTreeRoot (nodes g)) [] Empty (LoopScan [] Empty Empty))))
      as [next|result] eqn:Hstep; [|exact IH].
    eapply loop_tree_core_step; [exact Htree|exact IH|exact Hstep].
Qed.

(** A fresh tree entry spends exactly its weighted unvisited-node allowance. *)
Local Fixpoint loop_unseen_order (weight : positive -> nat)
    (vertices seen : list positive) : nat :=
  match vertices with
  | [] => 0
  | v :: rest => if existsb (Pos.eqb v) seen then loop_unseen_order weight rest seen
      else weight v + loop_unseen_order weight rest seen
  end.

Local Lemma loop_existsb_member v seen : existsb (Pos.eqb v) seen = true <-> In v seen.
Proof.
  rewrite existsb_exists. split.
  - intros [x [Hin Heq]]. apply Pos.eqb_eq in Heq. now subst x.
  - intro Hin. exists v. split; [exact Hin|apply Pos.eqb_refl].
Qed.

Local Lemma loop_existsb_fresh v seen : ~ In v seen -> existsb (Pos.eqb v) seen = false.
Proof.
  intro Hfresh. destruct (existsb (Pos.eqb v) seen) eqn:Htest; [|reflexivity].
  exfalso. apply Hfresh. now apply loop_existsb_member.
Qed.

Local Lemma loop_unseen_order_absent weight vertices seen v : ~ In v vertices ->
  loop_unseen_order weight vertices (v :: seen) = loop_unseen_order weight vertices seen.
Proof.
  induction vertices as [|x rest IH]; intro Habsent; [reflexivity|].
  assert (Hne : x <> v) by (intro Heq; apply Habsent; now left).
  assert (Htest : Pos.eqb x v = false) by now apply Pos.eqb_neq.
  cbn [loop_unseen_order existsb]. rewrite Htest. cbn [orb].
  rewrite IH by (intro Hin; apply Habsent; now right). reflexivity.
Qed.

Local Lemma loop_unseen_order_mark weight vertices : NoDup vertices ->
  forall seen v, In v vertices -> ~ In v seen ->
  loop_unseen_order weight vertices seen =
    weight v + loop_unseen_order weight vertices (v :: seen).
Proof.
  intro Hunique. induction Hunique as [|x rest Hfresh Hunique IH];
    intros seen v Hin Hseen; [contradiction|].
  cbn [loop_unseen_order]. destruct Hin as [<-|Hin].
  - rewrite (loop_existsb_fresh x seen Hseen). cbn [existsb].
    rewrite Pos.eqb_refl. cbn [orb].
    now rewrite (loop_unseen_order_absent weight rest seen x Hfresh).
  - assert (Hne : x <> v) by (intro Heq; subst v; contradiction).
    assert (Htest : Pos.eqb x v = false) by now apply Pos.eqb_neq.
    cbn [existsb]. rewrite Htest. cbn [orb].
    rewrite (IH seen v Hin Hseen). destruct (existsb (Pos.eqb x) seen); lia.
Qed.

Local Definition loop_entry_weight g t v : nat :=
  4 + length (succs (base g) v) + 2 * length (children t v).

Local Definition loop_task_weight task : nat :=
  match task with
  | LoopTreeRoot _ => 2
  | LoopTreeEnter _ | LoopTreeLeave _ => 1
  | LoopTreeChildren vs => 2 * length vs + 1
  | LoopTreeEdges _ vs => length vs + 1
  end.

Local Definition loop_tree_work g t st : nat :=
  loop_unseen_order (loop_entry_weight g t) (nodes g) (loop_order (loop_tree_output st)) +
  fold_right (fun task n => loop_task_weight task + n) 0 (loop_tree_pending st).

Local Lemma loop_tree_work_step g t r st next : wf_graph (base g) -> domtree_exact g r t ->
  loop_partition_state g t r st -> tree_step g t st = inl next ->
  loop_tree_work g t next < loop_tree_work g t st.
Proof.
  intros Hgraph Htree Hpart Hstep. destruct st as [tasks stack active [order latches backs]].
  destruct tasks as [|task rest]; [discriminate Hstep|].
  destruct task as [v|v|vs|u vs|v]; cbn [tree_step] in Hstep.
  - destruct (trie_get v (pre t)); destruct (trie_get v (idom t));
      injection Hstep as <-; unfold loop_tree_work;
      cbn [loop_tree_output loop_order loop_tree_pending fold_right loop_task_weight]; lia.
  - assert (Hin : In v (nodes g)).
    { rewrite loop_nodes_verts. apply (loop_reachable_listed (base g) r v Hgraph (proj1 Htree)).
      destruct Hpart as [_ _ _ Hlive _ _ _]. apply Hlive. now left. }
    assert (Hfresh : ~ In v order).
    { destruct Hpart as [_ _ _ _ Hseparate _ _].
      exact (Hseparate v v (or_introl eq_refl) (tree_anc_refl (idom t) v)). }
    pose proof (loop_unseen_order_mark (loop_entry_weight g t) (nodes g)
      (loop_nodes_unique g Hgraph) order v Hin Hfresh) as Hmark.
    injection Hstep as <-. unfold loop_tree_work.
    cbn [loop_tree_output loop_order loop_tree_pending fold_right loop_task_weight].
    rewrite Hmark. unfold loop_entry_weight. lia.
  - destruct vs as [|v vs]; injection Hstep as <-; unfold loop_tree_work;
      cbn [loop_tree_output loop_order loop_tree_pending fold_right loop_task_weight length]; lia.
  - destruct vs as [|v vs].
    + injection Hstep as <-. unfold loop_tree_work.
      cbn [loop_tree_output loop_order loop_tree_pending fold_right loop_task_weight length]; lia.
    + destruct (trie_get v active) as [[]|]; injection Hstep as <-; unfold loop_tree_work;
        cbn [loop_tree_output loop_order loop_tree_pending fold_right loop_task_weight length]; lia.
  - injection Hstep as <-. unfold loop_tree_work.
    cbn [loop_tree_output loop_order loop_tree_pending fold_right loop_task_weight]; lia.
Qed.

(** Exact child rows contain each non-root tree vertex at most once in total. *)
Local Lemma loop_children_flat_unique g t r : domtree_exact g r t ->
  forall vertices, NoDup vertices -> NoDup (flat_map (children t) vertices).
Proof.
  intros Htree vertices Hunique.
  pose proof (proj1 (proj2 (proj2 (proj2 Htree)))) as Hchildren.
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 Htree))))) as Hrows.
  induction Hunique as [|v rest Hfresh Hunique IH]; cbn [flat_map]; [constructor|].
  apply NoDup_app; [exact (proj1 (Hrows v))|exact IH|].
  intros x Hleft Hright. apply in_flat_map in Hright as [p [Hp Hright]].
  apply (proj1 (Hchildren v x)) in Hleft.
  apply (proj1 (Hchildren p x)) in Hright.
  assert (Heq : v = p) by congruence. subst p. contradiction.
Qed.

Local Lemma loop_children_total g t r : wf_graph (base g) -> domtree_exact g r t ->
  fold_right (fun v n => length (children t v) + n) 0 (nodes g) <= graph_n (base g).
Proof.
  intros Hgraph Htree.
  pose proof (loop_children_flat_unique g t r Htree (nodes g) (loop_nodes_unique g Hgraph))
    as Hunique.
  assert (Hincluded : incl (flat_map (children t) (nodes g)) (nodes g)).
  { intros x Hin. apply in_flat_map in Hin as [p [Hp Hchild]].
    pose proof (proj1 (proj1 (proj2 (proj2 (proj2 Htree))) p x) Hchild) as Hparent.
    rewrite loop_nodes_verts. apply (loop_reachable_listed (base g) r x Hgraph (proj1 Htree)).
    exact (proj1 (proj2 (proj1 (proj1 (proj2 Htree)) x p Hparent))). }
  pose proof (NoDup_incl_length Hunique Hincluded) as Hlength.
  assert (Hsum : forall vertices,
    length (flat_map (children t) vertices) =
      fold_right (fun v n => length (children t v) + n) 0 vertices).
  { intro vertices. induction vertices as [|v rest IH]; cbn [flat_map fold_right length];
      [reflexivity|now rewrite length_app, IH]. }
  rewrite Hsum in Hlength.
  assert (Hnodes : length (nodes g) = graph_n (base g)).
  { destruct g as [[vertices adjacency] predecessors vertex_count edge_count]. reflexivity. }
  now rewrite Hnodes in Hlength.
Qed.

Local Lemma loop_tree_work_initial g t r : wf_graph (base g) -> domtree_exact g r t ->
  loop_tree_work g t
    (LoopTreeState (map LoopTreeRoot (nodes g)) [] Empty (LoopScan [] Empty Empty)) <=
      8 * graph_n (base g) + graph_e (base g).
Proof.
  intros Hgraph Htree. pose proof (loop_children_total g t r Hgraph Htree) as Hchildren.
  assert (Hwhite : forall vertices,
    loop_unseen_order (loop_entry_weight g t) vertices [] =
      4 * length vertices + fold_right (fun v n => length (succs (base g) v) + n) 0 vertices +
      2 * fold_right (fun v n => length (children t v) + n) 0 vertices).
  { intro vertices. induction vertices as [|v rest IH]; [reflexivity|].
    cbn [loop_unseen_order existsb length fold_right]. rewrite IH.
    unfold loop_entry_weight. lia. }
  assert (Hpending : forall vertices,
    fold_right (fun task n => loop_task_weight task + n) 0 (map LoopTreeRoot vertices) =
      2 * length vertices).
  { intro vertices. induction vertices as [|v rest IH]; [reflexivity|].
    cbn [map fold_right length]. rewrite IH. cbn [loop_task_weight]. lia. }
  assert (Hnodes : length (nodes g) = graph_n (base g)).
  { destruct g as [[vertices adjacency] predecessors vertex_count edge_count]. reflexivity. }
  assert (Hedges : fold_right (fun v n => length (succs (base g) v) + n) 0 (nodes g) =
    graph_e (base g)).
  { destruct g as [[vertices adjacency] predecessors vertex_count edge_count]. reflexivity. }
  unfold loop_tree_work. cbn [loop_tree_output loop_order loop_tree_pending].
  rewrite Hwhite, Hpending, Hnodes, Hedges. lia.
Qed.

Local Lemma loop_classify_finishes g t r :
  wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
  exists result, loopN (tree_step g t) (8 * (nv g + ne g + 1))%N
    (LoopTreeState (map LoopTreeRoot (nodes g)) [] Empty (LoopScan [] Empty Empty)) = inr result.
Proof.
  intros Hgraph Hprepared Htree.
  apply (loopN_done loop_tree_state loop_scan (tree_step g t)
    (loop_tree_core g t r) (loop_tree_work g t)).
  - intros st next Hcore Hstep. split.
    + exact (loop_tree_core_step g t r st next Htree Hcore Hstep).
    + exact (loop_tree_work_step g t r st next Hgraph Htree (proj2 (proj2 Hcore)) Hstep).
  - now apply loop_tree_core_initial.
  - pose proof (loop_tree_work_initial g t r Hgraph Htree) as Hbound.
    destruct Hprepared as [Hn [He _]]. rewrite Hn, He. lia.
Qed.

Local Lemma loop_classify_driver g t r :
  wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
  loopN (tree_step g t) (8 * (nv g + ne g + 1))%N
    (LoopTreeState (map LoopTreeRoot (nodes g)) [] Empty (LoopScan [] Empty Empty)) =
      inr (classify g t).
Proof.
  intros Hgraph Hprepared Htree.
  destruct (loop_classify_finishes g t r Hgraph Hprepared Htree) as [result Hdone].
  unfold classify. now rewrite Hdone.
Qed.

(** Appending later visits preserves every earlier strict list position. *)
Local Lemma loop_order_append xs suffix u v :
  order_before xs u v -> order_before (xs ++ suffix) u v.
Proof.
  intros [i [j [Hi [Hj Hij]]]]. exists i, j. split.
  - rewrite nth_error_app1; [exact Hi|]. apply nth_error_Some. rewrite Hi. discriminate.
  - split; [|exact Hij]. rewrite nth_error_app1; [exact Hj|].
    apply nth_error_Some. rewrite Hj. discriminate.
Qed.

Local Lemma loop_order_append_last xs u v : In u xs -> order_before (xs ++ [v]) u v.
Proof.
  intro Hin. apply In_nth_error in Hin as [i Hi]. exists i, (length xs). split.
  - rewrite nth_error_app1; [exact Hi|]. apply nth_error_Some. rewrite Hi. discriminate.
  - split.
    + rewrite nth_error_app2 by lia. now rewrite Nat.sub_diag.
    + apply nth_error_Some. rewrite Hi. discriminate.
Qed.

Local Definition loop_tree_ordered t st : Prop :=
  forall u v, In v (loop_order (loop_tree_output st)) -> tree_anc (idom t) u v -> u <> v ->
    order_before (rev (loop_order (loop_tree_output st))) u v.

Local Lemma loop_tree_ordered_initial g t :
  loop_tree_ordered t
    (LoopTreeState (map LoopTreeRoot (nodes g)) [] Empty (LoopScan [] Empty Empty)).
Proof. intros u v Hin. contradiction. Qed.

Local Lemma loop_tree_ordered_step g t r st next : domtree_exact g r t ->
  loop_partition_state g t r st -> loop_tree_ordered t st -> tree_step g t st = inl next ->
  loop_tree_ordered t next.
Proof.
  intros Htree Hpart Hordered Hstep. destruct st as [tasks stack active [order latches backs]].
  destruct tasks as [|task rest]; [discriminate Hstep|].
  destruct task as [v|v|vs|u vs|v]; cbn [tree_step] in Hstep.
  - destruct (trie_get v (pre t)); destruct (trie_get v (idom t));
      injection Hstep as <-; exact Hordered.
  - injection Hstep as <-. intros u x Hx Hanc Hne.
    cbn [loop_tree_output loop_order In] in Hx. destruct Hx as [<-|Hx].
    + cbn [loop_tree_output loop_order rev]. apply loop_order_append_last.
      apply (proj1 (in_rev order u)).
      exact (loop_partition_ancestors_seen g t r order (v :: loop_future t rest)
        v u (proj1 (proj2 Htree)) Hpart (or_introl eq_refl) Hanc Hne).
    + cbn [loop_tree_output loop_order rev]. apply loop_order_append.
      exact (Hordered u x Hx Hanc Hne).
  - destruct vs; injection Hstep as <-; exact Hordered.
  - destruct vs as [|v vs]; [injection Hstep as <-; exact Hordered|].
    destruct (trie_get v active) as [[]|]; injection Hstep as <-; exact Hordered.
  - injection Hstep as <-. exact Hordered.
Qed.

Local Lemma loop_tree_stop_pending g t st result : tree_step g t st = inr result ->
  loop_tree_pending st = [].
Proof.
  destruct st as [tasks stack active [order latches backs]]. destruct tasks as [|task rest].
  - reflexivity.
  - destruct task as [v|v|vs|u vs|v]; cbn [tree_step].
    + destruct (trie_get v (pre t)); destruct (trie_get v (idom t)); discriminate.
    + discriminate.
    + destruct vs; discriminate.
    + destruct vs as [|v vs]; [discriminate|]. destruct (trie_get v active); discriminate.
    + discriminate.
Qed.

Local Definition loop_order_result g (t : domtree) r (result : loop_scan) : Prop :=
  NoDup (loop_order result) /\ hd_error (loop_order result) = Some r /\
  (forall v, In v (loop_order result) <-> reach (base g) [r] v) /\
  forall u v, reach (base g) [r] v -> strictly_dominates (base g) r u v ->
    order_before (loop_order result) u v.

Local Lemma loop_tree_order_stop g t r st result : domtree_exact g r t ->
  loop_tree_core g t r st -> loop_tree_ordered t st -> tree_step g t st = inr result ->
  loop_order_result g t r result.
Proof.
  intros Htree Hcore Hordered Hstep.
  pose proof (loop_tree_stop_pending g t st result Hstep) as Hempty.
  destruct st as [tasks stack active [order latches backs]]. cbn in Hempty. subst tasks.
  cbn [tree_step] in Hstep. injection Hstep as <-.
  rewrite rev_append_rev, app_nil_r. unfold loop_order_result.
  cbn [loop_order]. destruct Hcore as [_ [_ Hpart]].
  destruct Hpart as [Hunique Hfuture Hlive Hfuturelive Hseparate Hdisjoint Hcover].
  cbn [loop_tree_output loop_order loop_tree_pending loop_future flat_map] in *.
  assert (Hmembers : forall v, In v (rev order) <-> reach (base g) [r] v).
  { intro v. rewrite <- in_rev. split; [apply Hlive|]. intro Hreach.
    destruct (Hcover v Hreach) as [Hin|[a [Hin Hanc]]]; [exact Hin|contradiction]. }
  assert (Hstrict : forall u v, reach (base g) [r] v -> strictly_dominates (base g) r u v ->
    order_before (rev order) u v).
  { intros u v Hreach [Hdom Hne]. apply Hordered.
    - apply (proj2 (in_rev order v)). now apply Hmembers.
    - exact (dom_exact_dominates_anc g r (idom t) u v (proj1 (proj2 Htree)) Hreach Hdom).
    - exact Hne. }
  assert (Hrevunique : NoDup (rev order)) by now apply NoDup_rev.
  split; [exact Hrevunique|]. split.
  - assert (Hr : In r (rev order)).
    { apply Hmembers. exists r, [r]. split; [now left|constructor]. }
    destruct (rev order) as [|v rest] eqn:Horder; [contradiction|].
    cbn [hd_error]. destruct (Pos.eq_dec v r) as [->|Hne]; [reflexivity|].
    exfalso. assert (Hreach : reach (base g) [r] v) by (apply Hmembers; now left).
    assert (Hrv : r <> v) by congruence.
    pose proof (Hstrict r v Hreach (conj (loop_root_dominates (base g) r v) Hrv)) as Hbefore.
    pose proof (dom_cert_before_positions (v :: rest) r v Hrevunique Hbefore) as Hlt.
    rewrite (dom_cert_position_nth (v :: rest) Hrevunique 0 v eq_refl) in Hlt. lia.
  - split; assumption.
Qed.

(** The raw loop invariant handles both early fuel exhaustion and normal termination. *)
Local Lemma loop_state_result {S R : Type} (step : S -> S + R)
    (Inv : S -> Prop) (Result : R -> Prop) :
  (forall st next, Inv st -> step st = inl next -> Inv next) ->
  (forall st result, Inv st -> step st = inr result -> Result result) ->
  forall fs (Hacc : Acc loopN_lt fs), Inv (snd fs) ->
  match Argent.Loop.loop loopN_lt (loopN_step step) fs Hacc with
  | inl final => Inv final | inr result => Result result end.
Proof.
  intros Hcontinue Hstop fs Hacc.
  induction Hacc as [[fuel st] Hnext IH] using Acc_ind_dep.
  cbn [snd]. intro Hinv. destruct fuel as [|fuel]; [exact Hinv|].
  cbn [Argent.Loop.loop loopN_step Acc_inv].
  destruct (step st) as [next|result] eqn:Hstep.
  - apply IH. eapply Hcontinue; eassumption.
  - eapply Hstop; eassumption.
Qed.

Local Lemma loop_classify_order g t r :
  wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
  loop_order_result g t r (classify g t).
Proof.
  intros Hgraph Hprepared Htree.
  pose proof (loop_classify_driver g t r Hgraph Hprepared Htree) as Hdone.
  assert (Hloop : match loopN (tree_step g t) (8 * (nv g + ne g + 1))%N
    (LoopTreeState (map LoopTreeRoot (nodes g)) [] Empty (LoopScan [] Empty Empty)) with
    | inl final => loop_tree_core g t r final /\ loop_tree_ordered t final
    | inr result => loop_order_result g t r result end).
  { unfold loopN. apply (loop_state_result (tree_step g t)
      (fun st => loop_tree_core g t r st /\ loop_tree_ordered t st) (loop_order_result g t r)).
    - intros st next [Hcore Hordered] Hstep. split.
      + exact (loop_tree_core_step g t r st next Htree Hcore Hstep).
      + exact (loop_tree_ordered_step g t r st next Htree (proj2 (proj2 Hcore)) Hordered Hstep).
    - intros st result [Hcore Hordered] Hstep.
      exact (loop_tree_order_stop g t r st result Htree Hcore Hordered Hstep).
    - split; [now apply loop_tree_core_initial|apply loop_tree_ordered_initial]. }
  now rewrite Hdone in Hloop.
Qed.

(** A constant-cost visitor exposes Search's public trace clock without extra observations. *)
Module LoopTraceClockVisitor <: VISITOR_T.
  Include LoopTraceVisitor.
  Definition vwork (_ : state) : nat := 0.
  Definition c_vis : N := 1%N.

  Lemma T_enter_le : forall v s, (T_enter v s <= c_vis * N.of_nat (vwork s + 1))%N.
  Proof. intros v s. unfold T_enter, c_vis, vwork. time_simpl. lia. Qed.

  Lemma T_leave_le : forall v s, (T_leave v s <= c_vis * N.of_nat (vwork s + 1))%N.
  Proof. intros v s. unfold T_leave, c_vis, vwork. time_simpl. lia. Qed.

  Lemma T_edge_le : forall kind u v s,
    (T_edge kind u v s <= c_vis * N.of_nat (vwork s + 1))%N.
  Proof. intros kind u v s. unfold T_edge, c_vis, vwork. time_simpl. lia. Qed.
End LoopTraceClockVisitor.

Module LoopTraceClock := Galois.Graph.Search.SearchT LoopTraceClockVisitor.

Local Definition loop_trace_cost : N := (16 * (LoopTraceClock.k_trace + 1))%N.
Local Definition loop_test_cost : N := 64%N.
Local Opaque LoopTraceClock.k_trace.

Local Lemma loop_vertex_width_bound : forall vertices width,
  (forall v, In v vertices -> Pos.size_nat v <= width) -> vertex_width vertices <= width.
Proof.
  intro vertices. induction vertices as [|v rest IH]; intros width Hwidth; [cbn; lia|].
  cbn [vertex_width]. change graph_max with Nat.max. apply Nat.max_lub.
  - apply Hwidth. now left.
  - apply IH. intros u Hu. apply Hwidth. now right.
Qed.

Local Lemma loop_successor_width : forall g u,
  wf_graph (base g) -> In u (nodes g) ->
  vertex_width (succs (base g) u) <= graph_width (base g).
Proof.
  intros g u Hgraph Hu. apply loop_vertex_width_bound. intros v Hv.
  apply loop_listed_width. rewrite loop_nodes_verts in Hu |- *.
  exact (proj2 Hgraph u v Hu Hv).
Qed.

Local Lemma loop_trace_support : forall g r,
  wf_graph (base g) -> counts_ok g -> In r (nodes g) ->
  NoDup (entered (prepared_search_trace g [r])) /\
    incl (entered (prepared_search_trace g [r])) (nodes g).
Proof.
  intros g r Hgraph Hcounts Hroot.
  assert (Hroots : forall v, In v [r] -> In v (nodes g)).
  { intros v [<-|Hin]; [exact Hroot|contradiction]. }
  split.
  - exact (LoopTrace.trace_unique g [r] Hcounts Hgraph Hroots).
  - intros v Hin. rewrite loop_nodes_verts in Hroot |- *.
    apply (loop_reachable_listed (base g) r v Hgraph Hroot).
    exact (proj1 (LoopTrace.trace_reach g [r] v Hcounts Hgraph Hroots) Hin).
Qed.

(** A single listed-root trace stays within the graph's vertex, edge and key budgets. *)
Local Lemma loop_trace_measures : forall g r,
  wf_graph (base g) -> counts_ok g -> In r (nodes g) ->
  LoopTraceClock.n_reach g [r] <= graph_n (base g) /\
  LoopTraceClock.e_reach g [r] <= graph_e (base g) /\
  LoopTraceClock.run_width g [r] <= graph_width (base g) /\
  length (prepared_search_trace g [r]) <= 2 * graph_n (base g) + graph_e (base g).
Proof.
  intros g r Hgraph Hcounts Hroot.
  destruct (loop_trace_support g r Hgraph Hcounts Hroot) as [Hunique Hlisted].
  pose proof (NoDup_incl_length Hunique Hlisted) as Hvertices.
  assert (Hnodes : length (nodes g) = graph_n (base g)).
  { destruct g as [[vertices adjacency] predecessors vertex_count edge_count]. reflexivity. }
  rewrite Hnodes in Hvertices.
  pose proof (DomProducer.dom_nodup_sum_incl (fun v => length (succs (base g) v))
    _ _ Hunique Hlisted) as Hedges.
  assert (Hrows : fold_right (fun v total => length (succs (base g) v) + total)
    0 (nodes g) = graph_e (base g)).
  { destruct g as [[vertices adjacency] predecessors vertex_count edge_count]. reflexivity. }
  cbn beta in Hedges. rewrite Hrows in Hedges.
  assert (Hwidth : LoopTraceClock.run_width g [r] <= graph_width (base g)).
  { unfold LoopTraceClock.run_width. change graph_max with Nat.max. apply Nat.max_lub.
    - apply loop_vertex_width_bound. intros v [<-|Hin]; [now apply loop_listed_width|contradiction].
    - assert (Hall : forall vertices, incl vertices (nodes g) ->
        fold_right (fun u width => Nat.max (vertex_width (succs (base g) u)) width)
          0 vertices <= graph_width (base g)).
      { intro vertices. induction vertices as [|v rest IH]; intros Hincl; [cbn; lia|].
        cbn [fold_right]. apply Nat.max_lub.
        - apply loop_successor_width; [exact Hgraph|apply Hincl; now left].
        - apply IH. intros u Hu. apply Hincl. now right. }
      exact (Hall _ Hlisted). }
  pose proof (LoopTraceClock.F7b_events_raw g [r]) as Hevents.
  unfold LoopTraceClock.n_reach, LoopTraceClock.e_reach, LoopTraceClock.trace in *.
  repeat split; try assumption. lia.
Qed.

Local Lemma loop_trace_edge_width : forall g r u v,
  wf_graph (base g) -> counts_ok g -> In r (nodes g) ->
  In (Edge Back u v) (prepared_search_trace g [r]) ->
  Pos.size_nat u <= graph_width (base g) /\ Pos.size_nat v <= graph_width (base g).
Proof.
  intros g r u v Hgraph Hcounts Hroot Hin.
  assert (Hroots : forall x, In x [r] -> In x (nodes g)).
  { intros x [<-|Hfalse]; [exact Hroot|contradiction]. }
  destruct (LoopTrace.trace_edges_sound g [r] Back u v Hcounts Hgraph Hroots Hin)
    as [Hreach Hedge].
  assert (Hu : In u (nodes g)).
  { rewrite loop_nodes_verts in Hroot |- *.
    now apply (loop_reachable_listed (base g) r u). }
  split; [now apply loop_listed_width|].
  apply loop_listed_width. rewrite loop_nodes_verts in Hu |- *.
  exact (proj2 Hgraph u v Hu Hedge).
Qed.

Local Lemma loop_forallb_clock_bound {A : Type} (test : A -> bool) (clock : A -> N) :
  forall xs cost,
  (forall x, In x xs -> (clock x <= cost)%N) ->
  (List.T_forallb test clock xs <= (cost + 2) * N.of_nat (length xs) + 1)%N.
Proof.
  intro xs. induction xs as [|x rest IH]; intros cost Hclock.
  - time_unfold List.T_forallb. cbn [length]. lia.
  - pose proof (Hclock x (or_introl eq_refl)) as Hhead.
    specialize (IH cost (fun y Hy => Hclock y (or_intror Hy))).
    time_unfold List.T_forallb. time_simpl. cbn [length]. rewrite Nat2N.inj_succ.
    destruct (test x); lia.
Qed.

Local Lemma loop_test_clock : forall rows events width,
  (forall u v, In (Edge Back u v) events -> Pos.size_nat u <= width /\ Pos.size_nat v <= width) ->
  (T_test_back rows events + 1 <=
    16 * N.of_nat (length events + 1) * N.of_nat (width + 1))%N.
Proof.
  intros rows events width Hwidth. unfold T_test_back. time_simpl.
  match goal with
  | |- context [List.T_forallb ?test ?clock events] =>
      assert (Htest : (List.T_forallb test clock events <=
        (8 * N.of_nat (width + 1) + 2) * N.of_nat (length events) + 1)%N)
  end.
  { apply loop_forallb_clock_bound. intros [v|v|kind u v] Hin;
      cbn beta iota zeta; try lia.
    destruct kind; cbn beta iota zeta; try lia.
    destruct (Hwidth u v Hin) as [Hu Hv].
    apply time_of_nat_le in Hu. apply time_of_nat_le in Hv.
    rewrite PTrieT.trie_get_clock.
    destruct (trie_get u rows) as [row|]; [rewrite PTrieT.trie_get_clock|];
      rewrite Nat2N.inj_add; lia. }
  repeat rewrite Nat2N.inj_add in Htest |- *. nia.
Qed.

Local Lemma loop_trace_clock_bound : forall g r,
  wf_graph (base g) -> counts_ok g -> In r (nodes g) ->
  (T_prepared_search_trace g [r] + 1 <= loop_trace_cost *
    N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
Proof.
  intros g r Hgraph Hcounts Hroot.
  destruct (loop_trace_measures g r Hgraph Hcounts Hroot) as [Hvertices [Hedges [Hwidth _]]].
  pose proof (LoopTraceClock.T4_raw g [r]) as Hclock.
  pose proof (DomProducer.dom_size_value (nv g)) as Hnv.
  pose proof (DomProducer.dom_size_value (ne g)) as Hne.
  destruct Hcounts as [Hcachev Hcachee].
  apply time_of_nat_le in Hvertices. apply time_of_nat_le in Hedges.
  apply time_of_nat_le in Hwidth.
  unfold LoopTraceClock.T_search_trace in Hclock. cbn beta iota zeta in Hclock.
  cbn [length] in Hclock. unfold loop_trace_cost.
  repeat rewrite Nat2N.inj_add in Hclock |- *. nia.
Qed.

Local Lemma loop_retreat_test_clock : forall g r rows,
  wf_graph (base g) -> counts_ok g -> In r (nodes g) ->
  (T_test_back rows (prepared_search_trace g [r]) + 1 <= loop_test_cost *
    N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
Proof.
  intros g r rows Hgraph Hcounts Hroot.
  pose proof (loop_test_clock rows (prepared_search_trace g [r]) (graph_width (base g))
    (fun u v Hin => loop_trace_edge_width g r u v Hgraph Hcounts Hroot Hin)) as Hclock.
  destruct (loop_trace_measures g r Hgraph Hcounts Hroot) as [_ [_ [_ Hevents]]].
  apply time_of_nat_le in Hevents.
  unfold loop_test_cost. repeat rewrite Nat2N.inj_add in Hclock, Hevents |- *.
  repeat rewrite Nat2N.inj_mul in Hevents. nia.
Qed.


(** Recording a classified edge updates two equivalent incidence indexes. *)
Local Definition loop_back_present (scan : loop_scan) (u v : positive) : Prop :=
  match trie_get u (loop_back_rows scan) with
  | Some row => trie_get v row = Some tt
  | None => False
  end.

Local Definition loop_scan_push (scan : loop_scan) (u v : positive) : loop_scan :=
  match scan with
  | LoopScan order latches backs =>
    let sources := match trie_get v latches with Some xs => xs | None => [] end in
    let row := match trie_get u backs with Some xs => xs | None => Empty end in
    LoopScan order (PTrieCode.set v (u :: sources) latches)
      (PTrieCode.set u (PTrieCode.set v tt row) backs)
  end.
TimeFun loop_scan_push.

Local Lemma loop_back_present_row scan u v :
  loop_back_present scan u v <->
    exists row, trie_get u (loop_back_rows scan) = Some row /\ trie_get v row = Some tt.
Proof.
  unfold loop_back_present. destruct (trie_get u (loop_back_rows scan)) as [row|] eqn:Hrow.
  - split; [intro Hv; exists row; now split|]. intros [other [Heq Hv]].
    injection Heq as <-. exact Hv.
  - split; [contradiction|]. intros [row [Hrow' Hv]]. discriminate Hrow'.
Qed.

Local Lemma loop_back_push scan u v x y :
  loop_back_present (loop_scan_push scan u v) x y <->
    (x = u /\ y = v) \/ loop_back_present scan x y.
Proof.
  destruct scan as [order latches backs]. unfold loop_back_present, loop_scan_push.
  cbn [loop_back_rows]. destruct (Pos.eq_dec x u) as [->|Hxu].
  - rewrite PTrie.get_set_same. destruct (Pos.eq_dec y v) as [->|Hyv].
    + rewrite PTrie.get_set_same. tauto.
    + rewrite PTrie.get_set_other by exact Hyv.
      destruct (trie_get u backs) as [row|] eqn:Hrow; [tauto|].
      rewrite PTrie.get_empty. split; [discriminate|tauto].
  - rewrite PTrie.get_set_other by exact Hxu. tauto.
Qed.

Local Lemma loop_latches_push scan u v x y :
  In x (loop_latches_at (loop_scan_push scan u v) y) <->
    (x = u /\ y = v) \/ In x (loop_latches_at scan y).
Proof.
  destruct scan as [order latches backs]. unfold loop_scan_push, loop_latches_at.
  cbn [loop_latches]. destruct (Pos.eq_dec y v) as [->|Hyv].
  - rewrite PTrie.get_set_same. cbn [In]. intuition congruence.
  - rewrite PTrie.get_set_other by exact Hyv. tauto.
Qed.

Local Definition loop_task_edge (task : loop_tree_task) (u v : positive) : Prop :=
  match task with LoopTreeEdges x vs => x = u /\ In v vs | _ => False end.

Local Fixpoint loop_pending_edge (tasks : list loop_tree_task) (u v : positive) : Prop :=
  match tasks with
  | [] => False
  | task :: rest => loop_task_edge task u v \/ loop_pending_edge rest u v
  end.

Local Definition loop_back_sound g t r scan : Prop :=
  forall u v, loop_back_present scan u v ->
    reach (base g) [r] u /\ edge (base g) u v /\ tree_anc (idom t) v u.

Local Definition loop_latches_agree scan : Prop :=
  forall u v, In u (loop_latches_at scan v) <-> loop_back_present scan u v.

Local Definition loop_back_complete g t st : Prop :=
  forall u v, In u (loop_order (loop_tree_output st)) ->
    edge (base g) u v -> tree_anc (idom t) v u ->
    loop_pending_edge (loop_tree_pending st) u v \/ loop_back_present (loop_tree_output st) u v.

Local Definition loop_back_invariant g t r st : Prop :=
  loop_back_sound g t r (loop_tree_output st) /\
  loop_latches_agree (loop_tree_output st) /\ loop_back_complete g t st.

Local Lemma loop_back_initial g t r :
  loop_back_invariant g t r
    (LoopTreeState (map LoopTreeRoot (nodes g)) [] Empty (LoopScan [] Empty Empty)).
Proof.
  split.
  - intros u v Hback. unfold loop_back_present in Hback.
    cbn [loop_tree_output loop_back_rows] in Hback. rewrite PTrie.get_empty in Hback.
    contradiction.
  - split.
    + intros u v. unfold loop_latches_at, loop_back_present.
      cbn [loop_tree_output loop_latches loop_back_rows]. rewrite !PTrie.get_empty. tauto.
    + intros u v Hin. contradiction.
Qed.

(** The balanced task grammar identifies the current source with the active stack head. *)
Local Lemma loop_edges_stack g t r u vs rest stack :
  loop_tasks_wf g t r stack (LoopTreeEdges u vs :: rest) ->
  hd_error stack = Some u /\ incl vs (succs (base g) u).
Proof.
  intro Htasks. inversion Htasks; subst. now split.
Qed.

Local Lemma loop_active_ancestor g t r st u : domtree_exact g r t ->
  loop_stack_state t r st -> hd_error (loop_tree_stack st) = Some u ->
  forall v, trie_get v (loop_tree_active st) = Some tt <-> tree_anc (idom t) v u.
Proof.
  intros Htree [Hchain Hagree] Hhead v. rewrite Hagree.
  exact (loop_stack_ancestors (idom t) r (loop_tree_stack st)
    (loop_exact_root_none g t r Htree) Hchain u Hhead v).
Qed.

Local Lemma loop_back_push_sound g t r scan u v :
  loop_back_sound g t r scan -> reach (base g) [r] u -> edge (base g) u v ->
  tree_anc (idom t) v u -> loop_back_sound g t r (loop_scan_push scan u v).
Proof.
  intros Hsound Hreach Hedge Hanc x y Hback. apply loop_back_push in Hback.
  destruct Hback as [[-> ->]|Hback]; [now repeat split|now apply Hsound].
Qed.

Local Lemma loop_back_push_agree scan u v : loop_latches_agree scan ->
  loop_latches_agree (loop_scan_push scan u v).
Proof.
  intros Hagree x y. rewrite loop_latches_push, loop_back_push, (Hagree x y). reflexivity.
Qed.

Local Lemma loop_stack_head_reachable g t r stack u : domtree_exact g r t ->
  loop_stack_chain (idom t) r stack -> hd_error stack = Some u -> reach (base g) [r] u.
Proof.
  intros Htree Hchain Hhead.
  pose proof (loop_stack_reachable g r (idom t) stack (proj1 (proj2 Htree)) Hchain) as Hlive.
  destruct stack as [|v rest]; [discriminate Hhead|]. cbn in Hhead.
  injection Hhead as <-. now inversion Hlive.
Qed.

(** Tasks with no unprocessed edge change only the worklist representation. *)
Local Lemma loop_back_pending_transfer g t r scan tasks stack active tasks' stack' active' :
  loop_back_invariant g t r (LoopTreeState tasks stack active scan) ->
  (forall u v, tree_anc (idom t) v u ->
    loop_pending_edge tasks u v -> loop_pending_edge tasks' u v) ->
  loop_back_invariant g t r (LoopTreeState tasks' stack' active' scan).
Proof.
  intros [Hsound [Hagree Hcomplete]] Hpending. split; [exact Hsound|].
  split; [exact Hagree|]. intros u v Hin Hedge Hanc.
  destruct (Hcomplete u v Hin Hedge Hanc) as [Hwork|Hback].
  - left. now apply Hpending.
  - now right.
Qed.

Local Lemma loop_back_enter g t r v rest stack active order latches backs :
  loop_back_invariant g t r
    (LoopTreeState (LoopTreeEnter v :: rest) stack active (LoopScan order latches backs)) ->
  loop_back_invariant g t r
    (LoopTreeState (LoopTreeEdges v (succs (base g) v) :: LoopTreeChildren (children t v) ::
      LoopTreeLeave v :: rest) (v :: stack) (PTrieCode.set v tt active)
      (LoopScan (v :: order) latches backs)).
Proof.
  intros [Hsound [Hagree Hcomplete]]. split; [exact Hsound|]. split; [exact Hagree|].
  intros u x Hin Hedge Hanc. cbn [loop_tree_output loop_order In] in Hin.
  cbn [loop_tree_pending loop_pending_edge loop_task_edge]. destruct Hin as [<-|Hin].
  - left. left. split; [reflexivity|exact Hedge].
  - destruct (Hcomplete u x Hin Hedge Hanc) as [Hwork|Hback]; [|now right].
    cbn [loop_tree_pending loop_pending_edge loop_task_edge] in Hwork. tauto.
Qed.

Local Lemma loop_back_record g t r scan u v vs rest stack active :
  loop_back_invariant g t r
    (LoopTreeState (LoopTreeEdges u (v :: vs) :: rest) stack active scan) ->
  reach (base g) [r] u -> edge (base g) u v -> tree_anc (idom t) v u ->
  loop_back_invariant g t r
    (LoopTreeState (LoopTreeEdges u vs :: rest) stack active (loop_scan_push scan u v)).
Proof.
  intros [Hsound [Hagree Hcomplete]] Hreach Hedge Hanc. split.
  - now apply loop_back_push_sound.
  - split; [now apply loop_back_push_agree|]. intros x y Hin Hxy Hyx.
    destruct scan as [order latches backs].
    cbn [loop_scan_push loop_tree_output loop_order] in Hin.
    destruct (Hcomplete x y Hin Hxy Hyx) as [Hwork|Hback].
    + cbn [loop_tree_pending loop_pending_edge loop_task_edge In] in Hwork.
      destruct Hwork as [[Hux [Hvy|Htail]]|Hrest].
      * subst x y. right. apply loop_back_push. left. now split.
      * left. cbn [loop_tree_pending loop_pending_edge loop_task_edge]. now left.
      * left. cbn [loop_tree_pending loop_pending_edge loop_task_edge]. now right.
    + right. apply loop_back_push. now right.
Qed.

Local Lemma loop_back_step g t r st next : domtree_exact g r t ->
  loop_tree_core g t r st -> loop_back_invariant g t r st ->
  tree_step g t st = inl next -> loop_back_invariant g t r next.
Proof.
  intros Htree [Htasks [Hstack Hpart]] Hback Hstep.
  destruct st as [tasks stack active [order latches backs]].
  destruct tasks as [|task rest]; [discriminate Hstep|].
  destruct task as [v|v|vs|u vs|v]; cbn [tree_step] in Hstep.
  - destruct (trie_get v (pre t)); destruct (trie_get v (idom t));
      injection Hstep as <-; (eapply loop_back_pending_transfer; [exact Hback|]);
      intros x y Hanc; cbn [loop_pending_edge loop_task_edge]; tauto.
  - injection Hstep as <-. now apply loop_back_enter.
  - destruct vs as [|v vs]; injection Hstep as <-;
      (eapply loop_back_pending_transfer; [exact Hback|]);
      intros x y Hanc; cbn [loop_pending_edge loop_task_edge]; tauto.
  - destruct (loop_edges_stack g t r u vs rest stack Htasks) as [Hhead Hrow].
    pose proof (loop_active_ancestor g t r
      (LoopTreeState (LoopTreeEdges u vs :: rest) stack active (LoopScan order latches backs))
      u Htree Hstack Hhead) as Hactive.
    destruct vs as [|v vs].
    + injection Hstep as <-. eapply loop_back_pending_transfer; [exact Hback|].
      intros x y Hanc. cbn [loop_pending_edge loop_task_edge In]. tauto.
    + destruct (trie_get v active) as [[]|] eqn:Hget.
      * injection Hstep as <-. change (loop_back_invariant g t r
          (LoopTreeState (LoopTreeEdges u vs :: rest) stack active
            (loop_scan_push (LoopScan order latches backs) u v))).
        apply loop_back_record; [exact Hback| | |].
        -- exact (loop_stack_head_reachable g t r stack u Htree (proj1 Hstack) Hhead).
        -- apply Hrow. now left.
        -- exact (proj1 (Hactive v) Hget).
      * injection Hstep as <-. eapply loop_back_pending_transfer; [exact Hback|].
        intros x y Hanc Hwork. cbn [loop_pending_edge loop_task_edge In] in Hwork |- *.
        destruct Hwork as [[Hux [Hvy|Htail]]|Hrest].
        -- subst x y. pose proof (proj2 (Hactive v) Hanc) as Hpresent.
           cbn [loop_tree_active] in Hpresent. congruence.
        -- left. now split.
        -- now right.
  - injection Hstep as <-. eapply loop_back_pending_transfer; [exact Hback|].
    intros x y Hanc. cbn [loop_pending_edge loop_task_edge]. tauto.
Qed.

Local Definition loop_back_result g r (scan : loop_scan) : Prop :=
  forall u v,
    (loop_back_present scan u v <->
      reach (base g) [r] u /\ edge (base g) u v /\ dominates (base g) r v u) /\
    (In u (loop_latches_at scan v) <-> loop_back_present scan u v).

Local Lemma loop_back_stop g t r st result : domtree_exact g r t ->
  loop_tree_core g t r st -> loop_back_invariant g t r st ->
  tree_step g t st = inr result -> loop_back_result g r result.
Proof.
  intros Htree Hcore [Hsound [Hagree Hcomplete]] Hstep.
  pose proof (loop_tree_stop_pending g t st result Hstep) as Hempty.
  destruct st as [tasks stack active [order latches backs]]. cbn in Hempty. subst tasks.
  cbn [tree_step] in Hstep. injection Hstep as <-.
  intros u v. split; [|exact (Hagree u v)]. split.
  - intro Hback. destruct (Hsound u v Hback) as [Hreach [Hedge Hanc]].
    split; [exact Hreach|]. split; [exact Hedge|].
    exact (dom_exact_anc_dominates g r (idom t) v u (proj1 (proj2 Htree)) Hanc).
  - intros [Hreach [Hedge Hdom]].
    assert (Hseen : In u order).
    { destruct Hcore as [_ [_ Hpart]].
      destruct Hpart as [_ _ _ _ _ _ Hcover].
      destruct (Hcover u Hreach) as [Hin|[a [Hin Hanc]]]; [exact Hin|contradiction]. }
    pose proof (dom_exact_dominates_anc g r (idom t) v u
      (proj1 (proj2 Htree)) Hreach Hdom) as Hanc.
    destruct (Hcomplete u v Hseen Hedge Hanc) as [Hwork|Hback]; [contradiction|exact Hback].
Qed.

Local Lemma loop_classify_backs g t r :
  wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
  loop_back_result g r (classify g t).
Proof.
  intros Hgraph Hprepared Htree.
  pose proof (loop_classify_driver g t r Hgraph Hprepared Htree) as Hdone.
  assert (Hloop : match loopN (tree_step g t) (8 * (nv g + ne g + 1))%N
    (LoopTreeState (map LoopTreeRoot (nodes g)) [] Empty (LoopScan [] Empty Empty)) with
    | inl final => loop_tree_core g t r final /\ loop_back_invariant g t r final
    | inr result => loop_back_result g r result end).
  { unfold loopN. apply (loop_state_result (tree_step g t)
      (fun st => loop_tree_core g t r st /\ loop_back_invariant g t r st) (loop_back_result g r)).
    - intros st next [Hcore Hback] Hstep. split.
      + exact (loop_tree_core_step g t r st next Htree Hcore Hstep).
      + exact (loop_back_step g t r st next Htree Hcore Hback Hstep).
    - intros st result [Hcore Hback] Hstep.
      exact (loop_back_stop g t r st result Htree Hcore Hback Hstep).
    - split; [now apply loop_tree_core_initial|apply loop_back_initial]. }
  now rewrite Hdone in Hloop.
Qed.

(** Stored latch occurrences consume the original graph's edge occurrences. *)
Local Definition loop_latch_row (rows : ptrie (list positive)) h : list positive :=
  match trie_get h rows with Some vs => vs | None => [] end.

Local Definition loop_latch_mass (vertices : list positive) rows : nat :=
  fold_right (fun h n => length (loop_latch_row rows h) + n) 0 vertices.

Local Lemma loop_latch_mass_push vertices rows u v : NoDup vertices -> In v vertices ->
  loop_latch_mass vertices (PTrieCode.set v (u :: loop_latch_row rows v) rows) =
    S (loop_latch_mass vertices rows).
Proof.
  intros Hunique Hin. unfold loop_latch_mass. apply (loop_sum_update vertices v);
    [exact Hunique|exact Hin| |].
  - unfold loop_latch_row. rewrite PTrie.get_set_same. reflexivity.
  - intros x Hne. unfold loop_latch_row. now rewrite PTrie.get_set_other by exact Hne.
Qed.

Local Lemma loop_latch_mass_empty vertices : loop_latch_mass vertices Empty = 0.
Proof.
  induction vertices as [|v rest IH]; [reflexivity|].
  unfold loop_latch_mass in *. cbn [fold_right]. unfold loop_latch_row.
  rewrite PTrie.get_empty. cbn [length]. exact IH.
Qed.

Local Definition loop_task_edge_count task : nat :=
  match task with LoopTreeEdges _ vs => length vs | _ => 0 end.

Local Definition loop_edge_budget g st : nat :=
  loop_unseen_order (fun v => length (succs (base g) v)) (nodes g)
    (loop_order (loop_tree_output st)) +
  fold_right (fun task n => loop_task_edge_count task + n) 0 (loop_tree_pending st) +
  loop_latch_mass (nodes g) (loop_latches (loop_tree_output st)).

Local Lemma loop_active_listed g t r st v : wf_graph (base g) -> domtree_exact g r t ->
  loop_stack_state t r st -> trie_get v (loop_tree_active st) = Some tt -> In v (nodes g).
Proof.
  intros Hgraph Htree [Hchain Hagree] Hget. rewrite loop_nodes_verts.
  apply (loop_reachable_listed (base g) r v Hgraph (proj1 Htree)).
  pose proof (loop_stack_reachable g r (idom t) (loop_tree_stack st)
    (proj1 (proj2 Htree)) Hchain) as Hlive.
  apply (proj1 (Forall_forall _ _) Hlive v). now apply Hagree.
Qed.

Local Lemma loop_edge_budget_step g t r st next : wf_graph (base g) -> domtree_exact g r t ->
  loop_tree_core g t r st -> tree_step g t st = inl next ->
  loop_edge_budget g next <= loop_edge_budget g st.
Proof.
  intros Hgraph Htree [Htasks [Hstack Hpart]] Hstep.
  destruct st as [tasks stack active [order latches backs]].
  destruct tasks as [|task rest]; [discriminate Hstep|].
  destruct task as [v|v|vs|u vs|v]; cbn [tree_step] in Hstep.
  - destruct (trie_get v (pre t)); destruct (trie_get v (idom t));
      injection Hstep as <-; unfold loop_edge_budget;
      cbn [loop_tree_output loop_order loop_tree_pending loop_latches fold_right loop_task_edge_count]; lia.
  - assert (Hin : In v (nodes g)).
    { rewrite loop_nodes_verts. apply (loop_reachable_listed (base g) r v Hgraph (proj1 Htree)).
      destruct Hpart as [_ _ _ Hlive _ _ _]. apply Hlive. now left. }
    assert (Hfresh : ~ In v order).
    { destruct Hpart as [_ _ _ _ Hseparate _ _].
      exact (Hseparate v v (or_introl eq_refl) (tree_anc_refl (idom t) v)). }
    pose proof (loop_unseen_order_mark (fun x => length (succs (base g) x)) (nodes g)
      (loop_nodes_unique g Hgraph) order v Hin Hfresh) as Hmark.
    injection Hstep as <-. unfold loop_edge_budget.
    cbn [loop_tree_output loop_order loop_tree_pending loop_latches fold_right loop_task_edge_count].
    rewrite Hmark. lia.
  - destruct vs as [|v vs]; injection Hstep as <-; unfold loop_edge_budget;
      cbn [loop_tree_output loop_order loop_tree_pending loop_latches fold_right loop_task_edge_count]; lia.
  - destruct vs as [|v vs].
    + injection Hstep as <-. unfold loop_edge_budget.
      cbn [loop_tree_output loop_order loop_tree_pending loop_latches fold_right loop_task_edge_count length]; lia.
    + destruct (trie_get v active) as [[]|] eqn:Hget.
      * assert (Hlisted : In v (nodes g)).
        { exact (loop_active_listed g t r
            (LoopTreeState (LoopTreeEdges u (v :: vs) :: rest) stack active
              (LoopScan order latches backs)) v Hgraph Htree Hstack Hget). }
        pose proof (loop_latch_mass_push (nodes g) latches u v
          (loop_nodes_unique g Hgraph) Hlisted) as Hmass.
        injection Hstep as <-. unfold loop_edge_budget.
        cbn [loop_tree_output loop_order loop_tree_pending loop_latches fold_right loop_task_edge_count length].
        change (loop_latch_mass (nodes g)
          (PTrieCode.set v (u :: match trie_get v latches with Some xs => xs | None => [] end) latches) =
          S (loop_latch_mass (nodes g) latches)) in Hmass.
        rewrite Hmass. lia.
      * injection Hstep as <-. unfold loop_edge_budget.
        cbn [loop_tree_output loop_order loop_tree_pending loop_latches fold_right loop_task_edge_count length]; lia.
  - injection Hstep as <-. unfold loop_edge_budget.
    cbn [loop_tree_output loop_order loop_tree_pending loop_latches fold_right loop_task_edge_count]; lia.
Qed.

Local Lemma loop_edge_budget_initial g :
  loop_edge_budget g
    (LoopTreeState (map LoopTreeRoot (nodes g)) [] Empty (LoopScan [] Empty Empty)) =
    graph_e (base g).
Proof.
  assert (Hwhite : forall vertices,
    loop_unseen_order (fun v => length (succs (base g) v)) vertices [] =
      fold_right (fun v n => length (succs (base g) v) + n) 0 vertices).
  { intro vertices. induction vertices as [|v rest IH];
      cbn [loop_unseen_order existsb fold_right]; [reflexivity|now rewrite IH]. }
  assert (Hpending : forall vertices,
    fold_right (fun task n => loop_task_edge_count task + n) 0 (map LoopTreeRoot vertices) = 0).
  { intro vertices. induction vertices as [|v rest IH];
      cbn [map fold_right loop_task_edge_count]; assumption || reflexivity. }
  unfold loop_edge_budget. cbn [loop_tree_output loop_order loop_tree_pending loop_latches].
  rewrite Hwhite, Hpending, loop_latch_mass_empty. rewrite !Nat.add_0_r.
  destruct g as [[vertices adjacency] predecessors vertex_count edge_count]. reflexivity.
Qed.

Local Lemma loop_classify_latch_mass g t r :
  wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
  loop_latch_mass (nodes g) (loop_latches (classify g t)) <= graph_e (base g).
Proof.
  intros Hgraph Hprepared Htree.
  pose proof (loop_classify_driver g t r Hgraph Hprepared Htree) as Hdone.
  assert (Hloop : match loopN (tree_step g t) (8 * (nv g + ne g + 1))%N
    (LoopTreeState (map LoopTreeRoot (nodes g)) [] Empty (LoopScan [] Empty Empty)) with
    | inl final => loop_tree_core g t r final /\ loop_edge_budget g final <= graph_e (base g)
    | inr result => loop_latch_mass (nodes g) (loop_latches result) <= graph_e (base g) end).
  { unfold loopN. apply (loop_state_result (tree_step g t)
      (fun st => loop_tree_core g t r st /\ loop_edge_budget g st <= graph_e (base g))
      (fun result => loop_latch_mass (nodes g) (loop_latches result) <= graph_e (base g))).
    - intros st next [Hcore Hbudget] Hstep. split.
      + exact (loop_tree_core_step g t r st next Htree Hcore Hstep).
      + pose proof (loop_edge_budget_step g t r st next Hgraph Htree Hcore Hstep). lia.
    - intros st result [Hcore Hbudget] Hstep.
      pose proof (loop_tree_stop_pending g t st result Hstep) as Hempty.
      destruct st as [tasks stack active [order latches backs]]. cbn in Hempty. subst tasks.
      cbn [tree_step] in Hstep. injection Hstep as <-. cbn [loop_latches].
      unfold loop_edge_budget in Hbudget.
      cbn [loop_tree_output loop_order loop_tree_pending loop_latches fold_right] in Hbudget. lia.
    - split; [now apply loop_tree_core_initial|]. rewrite loop_edge_budget_initial. lia. }
  now rewrite Hdone in Hloop.
Qed.

Local Lemma loop_classify_headers_count g t r :
  wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
  NoDup (loop_headers_of (classify g t)) /\ incl (loop_headers_of (classify g t)) (nodes g) /\
    fold_right (fun h n => length (loop_latches_at (classify g t) h) + n) 0
      (loop_headers_of (classify g t)) <= graph_e (base g).
Proof.
  intros Hgraph Hprepared Htree.
  destruct (loop_classify_order g t r Hgraph Hprepared Htree) as [Hunique [Hroot [Hmembers Horder]]].
  assert (Hheaders : NoDup (loop_headers_of (classify g t))).
  { unfold loop_headers_of. now apply NoDup_filter. }
  assert (Hlisted : incl (loop_headers_of (classify g t)) (nodes g)).
  { intros h Hin. unfold loop_headers_of in Hin. apply filter_In in Hin as [Hin Htest].
    rewrite loop_nodes_verts. apply (loop_reachable_listed (base g) r h Hgraph (proj1 Htree)).
    now apply Hmembers. }
  split; [exact Hheaders|]. split; [exact Hlisted|].
  pose proof (DomProducer.dom_nodup_sum_incl (fun h => length (loop_latches_at (classify g t) h))
    (loop_headers_of (classify g t)) (nodes g) Hheaders Hlisted) as Hsum.
  pose proof (loop_classify_latch_mass g t r Hgraph Hprepared Htree) as Hmass.
  eapply Nat.le_trans; [exact Hsum|exact Hmass].
Qed.

(** The Boolean scan tests exactly the stored membership of back-edge events. *)
Local Lemma loop_test_back_spec scan events :
  test_back (loop_back_rows scan) events = true <->
    forall u v, In (Edge Back u v) events -> loop_back_present scan u v.
Proof.
  unfold test_back. rewrite forallb_forall. split.
  - intros Hall u v Hin. specialize (Hall (Edge Back u v) Hin).
    cbn in Hall. unfold loop_back_present.
    destruct (trie_get u (loop_back_rows scan)) as [row|] eqn:Hrow; [|discriminate].
    destruct (trie_get v row) as [[]|] eqn:Hget; [reflexivity|discriminate].
  - intros Hall event Hin. destruct event as [v|v|kind u v]; try reflexivity.
    destruct kind; try reflexivity. specialize (Hall u v Hin).
    unfold loop_back_present in Hall.
    destruct (trie_get u (loop_back_rows scan)) as [row|] eqn:Hrow; [|contradiction].
    now rewrite Hall.
Qed.

Local Lemma loop_reducible_test g t r :
  wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
  (test_back (loop_back_rows (classify g t)) (prepared_search_trace g [r]) = true <->
    reducible (base g) r).
Proof.
  intros Hgraph Hprepared Htree. rewrite loop_test_back_spec.
  assert (Hcounts : counts_ok g) by (exact (conj (proj1 Hprepared) (proj1 (proj2 Hprepared)))).
  assert (Hroots : forall x, In x [r] -> In x (nodes g)).
  { intros x [<-|Hfalse]; [exact (loop_tree_root_listed g r t Htree)|contradiction]. }
  destruct (loop_trace_valid g [r] Hcounts Hgraph Hroots) as [final Hdfs].
  split.
  - intros Htest u v [events [last [Hother Hin]]].
    destruct (loop_dfs_roots_deterministic (base g) [] [r]
      (prepared_search_trace g [r]) final Hdfs events last Hother) as [Hsame _].
    subst events. specialize (Htest u v Hin).
    destruct (loop_classify_backs g t r Hgraph Hprepared Htree u v) as [Hback Hlatches].
    exact (proj2 (proj2 (proj1 Hback Htest))).
  - intros Hreducible u v Hin.
    destruct (LoopTrace.trace_edges_sound g [r] Back u v Hcounts Hgraph Hroots Hin)
      as [Hreach Hedge].
    destruct (loop_classify_backs g t r Hgraph Hprepared Htree u v) as [Hback Hlatches].
    apply (proj2 Hback). split; [exact Hreach|]. split; [exact Hedge|].
    apply Hreducible. now exists (prepared_search_trace g [r]), final.
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
  Proof.
    intros g t r Hgraph Hprepared Htree.
    destruct (loop_classify_order g t r Hgraph Hprepared Htree) as [_ [Hroot _]].
    unfold reducible_b. rewrite loop_first_equation.
    rewrite (loop_first_head (loop_order (classify g t)) r Hroot).
    pose proof (loop_reducible_test g t r Hgraph Hprepared Htree) as Hspec.
    destruct (test_back (loop_back_rows (classify g t)) (prepared_search_trace g [r])) eqn:Htest.
    - constructor. now apply (proj1 Hspec).
    - constructor. intro Hreducible. apply (proj2 Hspec) in Hreducible. discriminate.
  Qed.
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
  Definition k_body_step : N := loop_body_step_cost.
  Definition k_body_stop : N := 8.
  Definition k_collect : N := loop_collect_cost.
  Definition k_install : N := loop_install_cost.
  Definition k_trace : N := loop_trace_cost.
  Definition k_test : N := loop_test_cost.
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

  Local Lemma tree_history_core : forall g t r st,
    wf_graph (base g) -> domtree_exact g r t ->
    (exists n, Nat.iter n (tree_advance g t) (tree_initial g) = st) ->
    loop_tree_core g t r st.
  Proof.
    intros g t r st Hgraph Htree [n Hhistory].
    pose proof (loop_tree_core_iteration g t r Hgraph Htree n) as Hcore.
    change (loop_tree_core g t r (Nat.iter n (tree_advance g t) (tree_initial g))) in Hcore.
    now rewrite Hhistory in Hcore.
  Qed.

  Local Lemma tree_core_observed : forall g t r st,
    domtree_exact g r t ->
    (exists n, Nat.iter n (tree_advance g t) (tree_initial g) = st) ->
    loop_tree_core g t r st -> tree_invariant g t r st.
  Proof.
    intros g t r st Htree Hhistory [Htasks [[Hchain Hagree] Hpart]].
    destruct Hpart as [Hunique Hfuture Hlive Hfuturelive Hseparate Hdisjoint Hcover].
    split; [exact Hhistory|]. split; [exact Hunique|]. split; [exact Hlive|].
    split.
    - apply (loop_stack_unique (idom t) r (loop_tree_stack st)); [| |exact Hchain].
      + exact (proj2 (proj2 (proj1 (proj2 Htree)))).
      + exact (loop_exact_root_none g t r Htree).
    - split; [exact Hagree|]. exact (loop_stack_links (idom t) r (loop_tree_stack st) Hchain).
  Qed.

  Local Lemma tree_potential_work : forall g t st,
    tree_potential g t st = N.of_nat (loop_tree_work g t st).
  Proof.
    intros g t st. unfold tree_potential, tree_white, tree_pending, loop_tree_work.
    assert (Hwhite : forall vertices seen,
      fold_right (fun v n => if existsb (Pos.eqb v) seen then n
        else 4 + length (succs (base g) v) + 2 * length (children t v) + n) 0 vertices =
      loop_unseen_order (loop_entry_weight g t) vertices seen).
    { intro vertices. induction vertices as [|v rest IH]; intro seen; [reflexivity|].
      cbn [fold_right loop_unseen_order loop_entry_weight]. now rewrite IH. }
    assert (Hpending : forall tasks,
      fold_right (fun task n => match task with
        | LoopTreeRoot _ => 2 + n
        | LoopTreeEnter _ | LoopTreeLeave _ => 1 + n
        | LoopTreeChildren vs => 2 * length vs + 1 + n
        | LoopTreeEdges _ vs => length vs + 1 + n
        end) 0 tasks = fold_right (fun task n => loop_task_weight task + n) 0 tasks).
    { intro tasks. induction tasks as [|task rest IH]; [reflexivity|].
      destruct task; cbn [fold_right loop_task_weight]; now rewrite IH. }
    now rewrite Hwhite, Hpending.
  Qed.

  Lemma F2_tree_step : forall g t r st next,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    tree_invariant g t r st -> tree_step g t st = inl next ->
    tree_invariant g t r next /\ (tree_potential g t next < tree_potential g t st)%N.
  Proof.
    intros g t r st next Hgraph Hprepared Htree Hinv Hstep.
    pose proof (proj1 Hinv) as Hhistory.
    pose proof (tree_history_core g t r st Hgraph Htree Hhistory) as Hcore.
    pose proof (loop_tree_core_step g t r st next Htree Hcore Hstep) as Hnext.
    split.
    - apply (tree_core_observed g t r next Htree); [|exact Hnext].
      destruct Hhistory as [n Hhistory]. exists (S n). rewrite Nat.iter_succ, Hhistory.
      unfold tree_advance. now rewrite Hstep.
    - pose proof (loop_tree_work_step g t r st next Hgraph Htree
        (proj2 (proj2 Hcore)) Hstep) as Hprogress.
      rewrite !tree_potential_work. lia.
  Qed.

  Lemma F3_tree_driver : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    loopN (tree_step g t) (tree_fuel g) (tree_initial g) = inr (classify g t).
  Proof.
    intros g t r Hgraph Hprepared Htree.
    exact (loop_classify_driver g t r Hgraph Hprepared Htree).
  Qed.

  Lemma F4_tree_order : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    NoDup (loop_order (classify g t)) /\ hd_error (loop_order (classify g t)) = Some r /\
    (forall v, In v (loop_order (classify g t)) <-> reach (base g) [r] v) /\
    forall u v, reach (base g) [r] v -> strictly_dominates (base g) r u v ->
      order_before (loop_order (classify g t)) u v.
  Proof.
    intros g t r Hgraph Hprepared Htree.
    exact (loop_classify_order g t r Hgraph Hprepared Htree).
  Qed.

  Lemma F5_back_edges : forall g t r u v,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    (back_member (classify g t) u v <->
      reach (base g) [r] u /\ edge (base g) u v /\ dominates (base g) r v u) /\
    (In u (latches (classify g t) v) <-> back_member (classify g t) u v).
  Proof.
    intros g t r u v Hgraph Hprepared Htree.
    destruct (loop_classify_backs g t r Hgraph Hprepared Htree u v) as [Hback Hlatches].
    unfold back_member. rewrite <- loop_back_present_row. now split.
  Qed.

  Lemma F6_latch_count : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    NoDup (headers g t) /\ incl (headers g t) (nodes g) /\
    fold_right (fun h n => length (latches (classify g t) h) + n) 0 (headers g t) <=
      graph_e (base g).
  Proof.
    intros g t r Hgraph Hprepared Htree.
    exact (loop_classify_headers_count g t r Hgraph Hprepared Htree).
  Qed.

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

  Local Lemma body_retire_amort : forall g t h v rest seen answer,
    Pos.size_nat v <= graph_width (base g) ->
    (trie_get v seen = Some tt \/ trie_get v (pre t) = None) ->
    (T_body_step g t h (LoopBodyState (v :: rest) seen answer) +
      body_credit g t h (LoopBodyState rest seen answer) + c_loopN <=
      body_credit g t h (LoopBodyState (v :: rest) seen answer))%N.
  Proof.
    intros g t h v rest seen answer Hwidth Hskip.
    pose proof (loop_body_skip_clock g t h v rest seen answer _ Hwidth Hskip) as Hclock.
    unfold T_body_step. time_simpl.
    unfold body_credit, body_potential, body_white, k_body_step.
    cbn [loop_body_seen loop_body_pending length]. rewrite !Nat2N.inj_add.
    nia.
  Qed.

  Local Lemma body_fresh_amort : forall g t r h v rest seen answer a,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In h (headers g t) ->
    Pos.size_nat v <= graph_width (base g) -> In v (collected g t h) ->
    trie_get v seen = None -> trie_get v (pre t) = Some a ->
    (T_body_step g t h (LoopBodyState (v :: rest) seen answer) +
      body_credit g t h
        (LoopBodyState (filter (fun u => match trie_get u (pre t) with
          | Some _ => true | None => false end) (preds g v) ++ rest)
          (PTrieCode.set v tt seen) (v :: answer)) + c_loopN <=
      body_credit g t h (LoopBodyState (v :: rest) seen answer))%N.
  Proof.
    intros g t r h v rest seen answer a Hgraph Hprepared Htree Hheader
      Hwidth Hin Hseen Hpre.
    assert (Hpredwidth : forall u, In u (preds g v) ->
      Pos.size_nat u <= graph_width (base g)).
    { intros u Hu. apply loop_listed_width. now apply (loop_predecessor_listed g u v). }
    pose proof (loop_body_fresh_clock g t h v rest seen answer _ a
      Hwidth Hpredwidth Hseen Hpre) as Hclock.
    pose proof (filter_length_le (fun u => match trie_get u (pre t) with
      | Some _ => true | None => false end) (preds g v)) as Hlength.
    pose proof (loop_body_fresh_work g (collected g t h) v rest seen
      (proj1 (F10_body_exact g t r h Hgraph Hprepared Htree Hheader)) Hin Hseen _ Hlength)
      as Hwork.
    rewrite length_app in Hwork. cbn [length] in Hwork.
    apply time_of_nat_le in Hwork. rewrite !Nat2N.inj_add in Hwork, Hclock.
    unfold T_body_step. time_simpl.
    unfold body_credit, body_potential, body_white, k_body_step.
    cbn [loop_body_seen loop_body_pending]. rewrite length_app.
    cbn [length]. rewrite !Nat2N.inj_add.
    unfold loop_unseen_work in Hwork. cbn beta in Hwork. nia.
  Qed.

  Lemma T4_body_step : forall g t r h st next,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In h (headers g t) ->
    body_invariant g t r h st -> body_step g t h st = inl next ->
    (T_body_step g t h st + body_credit g t h next + c_loopN <= body_credit g t h st)%N.
  Proof.
    intros g t r h [pending seen answer] next Hgraph Hprepared Htree Hheader Hinv Hstep.
    pose proof (F8_body_step g t r h _ next Hgraph Hprepared Htree Hheader Hinv Hstep)
      as [Hnext _].
    destruct Hinv as [_ [_ [_ [_ [_ Hpending]]]]].
    destruct Hnext as [_ [_ [_ [_ [Hsubset _]]]]].
    destruct pending as [|v rest]; [discriminate Hstep|].
    assert (Hwidth : Pos.size_nat v <= graph_width (base g)).
    { apply loop_listed_width. rewrite loop_nodes_verts.
      apply (loop_reachable_listed (base g) r v Hgraph (proj1 Htree)).
      now apply Hpending; left. }
    destruct (loop_body_step_behavior g t h v rest seen answer next Hstep)
      as [[-> Hskip]|[a [-> [Hseen Hpre]]]].
    - now apply body_retire_amort.
    - apply (body_fresh_amort g t r h v rest seen answer a); try assumption.
      apply Hsubset. now left.
  Qed.


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

  Local Lemma body_work_length : forall g vertices,
    length vertices <= body_work g vertices.
  Proof.
    intros g vertices. induction vertices as [|v rest IH]; unfold body_work in *;
      cbn [fold_right length]; lia.
  Qed.

  Local Lemma body_credit_initial : forall g t h sources,
    (body_credit g t h (body_initial h sources) <=
      (k_body_step * N.of_nat (graph_width (base g) + 1) + 1) *
        N.of_nat (4 * body_work g (collected g t h) + length sources))%N.
  Proof.
    intros g t h sources. unfold body_credit. apply N.mul_le_mono_l.
    unfold body_potential, body_white, body_initial.
    cbn [loop_body_seen loop_body_pending]. apply time_of_nat_le.
    pose proof (loop_unseen_body_work g (collected g t h) (PTrieCode.set h tt Empty)) as Hwork.
    unfold loop_unseen_work, body_work in *. lia.
  Qed.

  Local Lemma body_loop_clock : forall g t r h fuel,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In h (headers g t) ->
    (T_loopN (body_step g t h) (loop_body_clock g t h) fuel
      (body_initial h (latches (classify g t) h)) <=
      c_loopN * (body_credit g t h (body_initial h (latches (classify g t) h)) +
        k_body_stop * N.of_nat (length (collected g t h) + 1) +
        N.of_nat (N.size_nat fuel) + 1))%N.
  Proof.
    intros g t r h fuel Hgraph Hprepared Htree Hheader.
    apply (T_loopN_le loop_body_state (list positive) (body_step g t h)
      (loop_body_clock g t h) (body_invariant g t r h) (body_credit g t h)
      (k_body_stop * N.of_nat (length (collected g t h) + 1))%N).
    - intros st next Hinv Hstep. split.
      + exact (proj1 (F8_body_step g t r h st next Hgraph Hprepared Htree Hheader Hinv Hstep)).
      + pose proof (T4_body_step g t r h st next Hgraph Hprepared Htree Hheader Hinv Hstep)
          as Hclock.
        unfold T_body_step in Hclock. cbn beta iota zeta in Hclock.
        unfold loop_body_clock. lia.
    - intros st result Hinv Hstep.
      pose proof (T5_body_stop g t r h st result Hgraph Hprepared Htree Hheader Hinv Hstep)
        as Hclock.
      unfold T_body_step in Hclock. cbn beta iota zeta in Hclock.
      unfold loop_body_clock. lia.
    - now apply (F7_body_initial g t r h).
  Qed.

  Lemma T6_collect : forall g t r h,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In h (headers g t) ->
    (T_collect g t h (latches (classify g t) h) <= k_collect *
      (N.of_nat (body_work g (collected g t h) +
        length (latches (classify g t) h) + 1) *
        N.of_nat (graph_width (base g) + 1) +
        N.of_nat (N.size_nat (body_fuel g (latches (classify g t) h)))))%N.
  Proof.
    intros g t r h Hgraph Hprepared Htree Hheader.
    pose proof (F9_body_driver g t r h Hgraph Hprepared Htree Hheader) as Hdone.
    assert (Hheaderwidth : Pos.size_nat h <= graph_width (base g)).
    { apply loop_listed_width. rewrite loop_nodes_verts.
      apply (loop_reachable_listed (base g) r h Hgraph (proj1 Htree)).
      apply loop_header_reachable. now apply (selected_header g t r h). }
    pose proof (loop_collect_clock_wrapper g t h (latches (classify g t) h)
      (collected g t h) _ Hheaderwidth Hdone) as Hwrapper.
    fold (body_fuel g (latches (classify g t) h)) in Hwrapper.
    fold (body_initial h (latches (classify g t) h)) in Hwrapper.
    fold body_step in Hwrapper.
    pose proof (body_loop_clock g t r h (body_fuel g (latches (classify g t) h))
      Hgraph Hprepared Htree Hheader) as Hloop.
    pose proof (body_credit_initial g t h (latches (classify g t) h)) as Hinitial.
    pose proof (body_work_length g (collected g t h)) as Hlength.
    match type of Hloop with
    | (?runtime <= _)%N =>
        assert (Hloop_upper : (runtime <= c_loopN *
          ((k_body_step * N.of_nat (graph_width (base g) + 1) + 1) *
            N.of_nat (4 * body_work g (collected g t h) +
              length (latches (classify g t) h)) +
            8 * N.of_nat (body_work g (collected g t h) + 1) +
            N.of_nat (N.size_nat (body_fuel g (latches (classify g t) h))) + 1))%N)
    end.
    { eapply N.le_trans; [exact Hloop|]. apply N.mul_le_mono_l.
      unfold k_body_stop. rewrite !Nat2N.inj_add in Hinitial |- *. nia. }
    assert (Hunit : (1 <= loop_body_unit_cost)%N) by (unfold loop_body_unit_cost; lia).
    assert (Hwidth : (1 <= N.of_nat (graph_width (base g) + 1))%N) by lia.
    pose proof (loop_collect_arithmetic c_loopN loop_body_unit_cost
      (N.of_nat (graph_width (base g) + 1)) (N.of_nat (body_work g (collected g t h)))
      (N.of_nat (length (latches (classify g t) h)))
      (N.of_nat (N.size_nat (body_fuel g (latches (classify g t) h)))) Hunit Hwidth)
      as Hnumeric.
    clear Hgraph Hprepared Htree Hheader Hdone Hheaderwidth Hloop Hinitial Hlength Hunit Hwidth.
    unfold T_collect. time_simpl.
    unfold k_collect, loop_collect_cost, k_body_step, loop_body_step_cost in Hloop_upper |- *.
    repeat rewrite Nat2N.inj_add in Hloop_upper, Hwrapper, Hnumeric |- *.
    repeat rewrite Nat2N.inj_mul in Hloop_upper. nia.
  Qed.


  Lemma T7_install : forall g l h vs,
    forest_supported g l -> In h (nodes g) -> incl vs (nodes g) ->
    (T_install l (h, vs) <= k_install * N.of_nat (length vs + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
  Proof.
    intros g l h vs Hsupported Hheader Hvertices.
    pose proof (loop_install_clock l h vs (graph_width (base g))
      (loop_listed_width g h Hheader)
      (fun v Hin => loop_listed_width g v (Hvertices v Hin))) as Hclock.
    unfold T_install. time_simpl.
    unfold k_install, loop_install_cost, loop_install_step_cost in Hclock |- *. nia.
  Qed.


  Lemma T7a_assemble : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    (T_assemble (forest_rows g t) <= k_install *
      N.of_nat
        (fold_right (fun h n => (length (collected g t h) + 1 + n)%nat)
          0%nat (headers g t) + 1) * N.of_nat (graph_width (base g) + 1))%N.
  Proof.
    intros g t r Hgraph Hprepared Htree.
    destruct (F6_latch_count g t r Hgraph Hprepared Htree) as [_ [Hheaders _]].
    assert (Hrows : forall h vertices, In (h, vertices) (forest_rows g t) ->
      Pos.size_nat h <= graph_width (base g) /\
        forall v, In v vertices -> Pos.size_nat v <= graph_width (base g)).
    { intros h vertices Hin. unfold forest_rows in Hin. apply in_map_iff in Hin.
      destruct Hin as [key [Heq Hin]]. inversion Heq; subst h vertices.
      split; [apply loop_listed_width; now apply Hheaders|].
      intros v Hv. apply loop_listed_width.
      apply (proj1 (proj2 (F10_body_exact g t r key Hgraph Hprepared Htree Hin))).
      exact Hv. }
    pose proof (loop_assemble_clock (forest_rows g t) (graph_width (base g)) Hrows) as Hclock.
    unfold forest_rows in Hclock. rewrite loop_fold_map in Hclock.
    cbn beta iota zeta in Hclock. cbn [snd] in Hclock.
    unfold T_assemble. time_simpl. rewrite (N.add_comm 1). exact Hclock.
  Qed.


  Lemma T7b_fuel_widths : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    (fold_right (fun h cost =>
      N.of_nat (N.size_nat (body_fuel g (latches (classify g t) h))) + cost)%N
        0%N (headers g t) <= k_collect *
      N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
        N.of_nat (graph_width (base g) + 1))%N.
  Proof.
    intros g t r Hgraph Hprepared Htree.
    destruct (F6_latch_count g t r Hgraph Hprepared Htree)
      as [Hunique [Hlisted Hedges]].
    assert (Hnodes : length (nodes g) = graph_n (base g)).
    { destruct g as [[vertices adjacency] predecessors vertex_count edge_count]. reflexivity. }
    pose proof (dom_distinct_keys_cardinality (nodes g) (graph_width (base g))
      (loop_nodes_unique g Hgraph) (loop_listed_width g)) as Hcapacity.
    rewrite Hnodes in Hcapacity.
    pose proof (NoDup_incl_length Hunique Hlisted) as Hheaders.
    rewrite Hnodes in Hheaders.
    set (total := graph_n (base g) + graph_e (base g) + 1).
    pose proof (loop_count_log_product (graph_n (base g)) total (graph_width (base g))
      Hcapacity ltac:(unfold total; lia)) as Hlogarithm.
    assert (Hsources : forall h, In h (headers g t) ->
      length (latches (classify g t) h) <= graph_e (base g)).
    { intros h Hin. eapply Nat.le_trans; [|exact Hedges].
      exact (loop_sum_member_le (headers g t)
        (fun h => length (latches (classify g t) h)) h Hin). }
    assert (Hbits : forall h, In h (headers g t) ->
      N.size_nat (body_fuel g (latches (classify g t) h)) <=
        N.size_nat (N.of_nat total) + 3).
    { intros h Hin. eapply Nat.le_trans; [|apply loop_size_eight].
      apply loop_size_monotone. unfold body_fuel.
      destruct Hprepared as [Hnv [Hne Hpreds]]. rewrite Hnv, Hne.
      specialize (Hsources h Hin). unfold total. repeat rewrite Nat2N.inj_add. lia. }
    pose proof (loop_sum_uniform (headers g t)
      (fun h => N.size_nat (body_fuel g (latches (classify g t) h)))
      (N.size_nat (N.of_nat total) + 3) Hbits) as Hsum.
    assert (Hpaid : fold_right (fun h cost =>
      N.size_nat (body_fuel g (latches (classify g t) h)) + cost) 0 (headers g t) <=
      4 * total * (graph_width (base g) + 1)).
    { assert (Hcount : graph_n (base g) <= total) by (unfold total; lia). nia. }
    apply time_of_nat_le in Hpaid.
    rewrite loop_sum_of_nat. fold total.
    unfold k_collect, loop_collect_cost, loop_body_unit_cost.
    repeat rewrite Nat2N.inj_mul in Hpaid. nia.
  Qed.


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
  Proof.
    intros g t r Hgraph Hprepared Htree.
    destruct (F4_tree_order g t r Hgraph Hprepared Htree) as [_ [Hroot _]].
    rewrite (loop_first_head (loop_order (classify g t)) r Hroot).
    assert (Hcounts : counts_ok g) by (exact (conj (proj1 Hprepared) (proj1 (proj2 Hprepared)))).
    pose proof (loop_tree_root_listed g r t Htree) as Hlisted.
    pose proof (loop_trace_clock_bound g r Hgraph Hcounts Hlisted) as Htrace.
    pose proof (loop_retreat_test_clock g r (loop_back_rows (classify g t))
      Hgraph Hcounts Hlisted) as Htest.
    unfold T_retreat_trace, T_test_back. time_simpl.
    unfold retreat_trace, k_trace, k_test. nia.
  Qed.


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
