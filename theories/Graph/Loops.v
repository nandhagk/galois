(** * Natural loop forests

    Dominator-tree traversal classifies back edges and builds their reverse closures.
    For example, a self-edge produces a one-vertex natural loop.
    Builds on: prepared graphs, dominator trees and depth-first traces. *)

From Stdlib Require Import PArith NArith List Bool.
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

Module LoopTrace := Search LoopTraceVisitor.

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

  Definition k_tree_step : N := 1. (* STUB *)
  Definition k_tree_stop : N := 1. (* STUB *)
  Definition k_classify : N := 1. (* STUB *)
  Definition k_body_step : N := 1. (* STUB *)
  Definition k_body_stop : N := 1. (* STUB *)
  Definition k_collect : N := 1. (* STUB *)
  Definition k_install : N := 1. (* STUB *)
  Definition k_trace : N := 1. (* STUB *)
  Definition k_test : N := 1. (* STUB *)
  Definition k_forest : N := 1. (* STUB *)
  Definition k_reducible : N := 1. (* STUB *)

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

  Lemma F7_body_initial : forall g t r h,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In h (headers g t) ->
    body_invariant g t r h (body_initial h (latches (classify g t) h)).
  Proof. Admitted. (* STUB *)

  Lemma F8_body_step : forall g t r h st next,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In h (headers g t) ->
    body_invariant g t r h st -> body_step g t h st = inl next ->
    body_invariant g t r h next /\ (body_potential g t h next < body_potential g t h st)%N.
  Proof. Admitted. (* STUB *)

  Lemma F9_body_driver : forall g t r h,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In h (headers g t) ->
    loopN (body_step g t h) (body_fuel g (latches (classify g t) h))
      (body_initial h (latches (classify g t) h)) = inr (collected g t h).
  Proof. Admitted. (* STUB *)

  Lemma F10_body_exact : forall g t r h,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In h (headers g t) ->
    NoDup (collected g t h) /\ incl (collected g t h) (nodes g) /\
      forall v, In v (collected g t h) <-> natural_loop (base g) r h v.
  Proof. Admitted. (* STUB *)

  Lemma F11_laminar : forall g r h outer v,
    natural_loop g r h v -> natural_loop g r outer v -> h <> outer ->
    loop_inside g r h outer \/ loop_inside g r outer h.
  Proof. Admitted. (* STUB *)

  Lemma F12_header_order : forall g t r inner outer,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    loop_inside (base g) r inner outer -> order_before (headers g t) outer inner.
  Proof. Admitted. (* STUB *)

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
  Proof. Admitted. (* STUB *)

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
  Proof. Admitted. (* STUB *)

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
  Proof. Admitted. (* STUB *)

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
  Proof. Admitted. (* STUB *)

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
  Proof. Admitted. (* STUB *)

  Lemma T11_reducible_public : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    (T_reducible_b g t <= c_loops *
      N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
      N.of_nat (loop_depth g (forest g t) + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
  Proof. Admitted. (* STUB *)
End LoopsT.
