(** * Natural loop forests

    Dominator-tree traversal classifies back edges and builds their reverse closures.
    For example, a self-edge produces a one-vertex natural loop.
    Builds on: prepared graphs, dominator trees and depth-first traces. *)

From Stdlib Require Import PArith NArith List Bool.
From Galois.Base Require Import Trie Loop.
From Galois.Graph Require Import Data Spec DigraphSig SearchSig Search DomSig LoopsSig.
Import List.ListNotations.

Definition tree_step (g : prepared) (t : domtree) (st : loop_tree_state) :
    loop_tree_state + loop_scan :=
  match st with
  | LoopTreeState [] _ _ (LoopScan order latches backs) =>
    inr (LoopScan (rev order) latches backs)
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
      inl (LoopTreeState rest (tl stack) (PTrieCode.remove v active) scan)
    end
  end.

Definition classify (g : prepared) (t : domtree) : loop_scan :=
  let initial := LoopTreeState (map LoopTreeRoot (nodes g)) [] Empty (LoopScan [] Empty Empty) in
  match loopN (tree_step g t) (8 * (nv g + ne g + 1))%N initial with
  | inl st => let '(LoopScan order latches backs) := loop_tree_output st in
      LoopScan (rev order) latches backs
  | inr scan => scan
  end.

Definition body_step (g : prepared) (t : domtree) (_ : positive) (st : loop_body_state) :
    loop_body_state + list positive :=
  match st with
  | LoopBodyState [] _ answer => inr (rev answer)
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

Definition collect (g : prepared) (t : domtree) (h : positive) (sources : list positive) :=
  let initial := LoopBodyState sources (PTrieCode.set h tt Empty) [h] in
  match loopN (body_step g t h) (4 * (nv g + ne g + N.of_nat (length sources) + 1))%N initial with
  | inl st => rev (loop_body_answer st)
  | inr answer => answer
  end.

Definition install (l : loops) (entry : positive * list positive) : loops :=
  let '(h, vs) := entry in
  let outer := match trie_get h (header l) with
    | Some p => PTrieCode.set h p (parent l)
    | None => parent l
    end in
  Loops (fold_left (fun owners v => PTrieCode.set v h owners) vs (header l)) outer
    (PTrieCode.set h vs (body l)).

Definition assemble (rows : list (positive * list positive)) :=
  fold_left install rows (Loops Empty Empty Empty).

Definition test_back (rows : ptrie (ptrie unit)) (es : list event) : bool :=
  forallb (fun e => match e with
    | Edge Back u v => match trie_get u rows with
      | Some row => match trie_get v row with Some _ => true | None => false end
      | None => false
      end
    | _ => true
    end) es.

Module LoopsCode <: LOOPS_OPS.
  Definition forest (g : prepared) (t : domtree) :=
    let scan := classify g t in
    assemble (map (fun h => (h, collect g t h (loop_latches_at scan h)))
      (loop_headers_of scan)).

  Definition reducible_b (g : prepared) (t : domtree) :=
    let scan := classify g t in
    test_back (loop_back_rows scan) (prepared_search_trace g (firstn 1 (loop_order scan))).
End LoopsCode.

Module Loops <: LOOPS.
  Include LoopsCode.

  Lemma headers_spec : forall g t r h,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    (exists vs, trie_get h (body (forest g t)) = Some vs) <-> natural_header (base g) r h.
  Proof. Admitted.

  Lemma body_spec : forall g t r h v,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    In v (loop_body (forest g t) h) <-> natural_loop (base g) r h v.
  Proof. Admitted.

  Lemma body_unique : forall g t h, NoDup (loop_body (forest g t) h).
  Proof. Admitted.

  Lemma header_spec : forall g t r v h,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    trie_get v (header (forest g t)) = Some h <-> innermost_header (base g) r v h.
  Proof. Admitted.

  Lemma parent_spec : forall g t r inner outer,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    trie_get inner (parent (forest g t)) = Some outer <->
    immediate_outer (base g) r inner outer.
  Proof. Admitted.

  Lemma reducible_b_spec : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    reflect (reducible (base g) r) (reducible_b g t).
  Proof. Admitted.
End Loops.
