(** * Dominance frontiers

    Frontier columns share a visited table across the predecessors of each target.
    For example, parallel edges do not duplicate a target in a frontier row.
    Builds on: prepared graphs, dominator trees and binary-fuel loops. *)

From Stdlib Require Import PArith NArith List Bool.
From Galois.Base Require Import Trie Loop.
From Galois.Graph Require Import Data Spec DigraphSig DomSig FrontierSig.
Import List.ListNotations.

Definition df_step (g : prepared) (t : domtree) (y : positive) (st : df_state) :
    df_state + list positive :=
  match st with
  | DfState [] _ answer => inr (rev answer)
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

Definition df_column (g : prepared) (t : domtree) (y : positive) : list positive :=
  let initial := DfState (preds g y) Empty [] in
  match loopN (df_step g t y) (4 * (nv g + N.of_nat (length (preds g y)) + 1))%N initial with
  | inl st => rev (df_column_answer st)
  | inr answer => answer
  end.

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

Definition df (g : prepared) (t : domtree) : ptrie (list positive) :=
  df_transpose (map (fun y => (y, df_column g t y)) (nodes g)).

Definition idf_step (rows : ptrie (list positive)) (st : idf_state) :
    idf_state + list positive :=
  match st with
  | IdfState [] _ _ answer => inr (rev answer)
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

Definition idf_initial (seeds : list positive) := IdfState (map IdfSeed seeds) Empty Empty [].

Definition idf_advance rows st :=
  match idf_step rows st with
  | inl next => next
  | inr _ => st
  end.

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

Lemma idf_reachable_initial : forall rows seeds,
  idf_reachable rows seeds (idf_initial seeds).
Proof. Admitted.

Lemma idf_reachable_step : forall rows seeds st next,
  idf_reachable rows seeds st -> idf_step rows st = inl next ->
  idf_reachable rows seeds next.
Proof. Admitted.

Lemma idf_measure_step : forall rows seeds st next,
  idf_reachable rows seeds st -> idf_step rows st = inl next ->
  (idf_measure rows seeds next < idf_measure rows seeds st)%N.
Proof. Admitted.

Definition idf_private_state rows seeds := { st : idf_state | idf_reachable rows seeds st }.

Definition idf_private_lt rows seeds (next st : idf_private_state rows seeds) : Prop :=
  (idf_measure rows seeds (proj1_sig next) < idf_measure rows seeds (proj1_sig st))%N.

Definition idf_checked_step rows seeds (st : idf_private_state rows seeds) :
    { next : idf_private_state rows seeds | idf_private_lt rows seeds next st } + list positive.
Proof.
  destruct st as [st Hreachable].
  destruct (idf_step rows st) as [next | result] eqn:Hstep.
  - left. exists (exist _ next (idf_reachable_step rows seeds st next Hreachable Hstep)).
    exact (idf_measure_step rows seeds st next Hreachable Hstep).
  - right. exact result.
Defined.

Definition idf_accessible rows seeds (st : idf_private_state rows seeds) :
    Acc (idf_private_lt rows seeds) st :=
  Wellfounded.Inverse_Image.wf_inverse_image _ N N.lt
    (fun state => idf_measure rows seeds (proj1_sig state)) N.lt_wf_0 st.

Definition idf (rows : ptrie (list positive)) (seeds : list positive) : list positive :=
  let initial := exist _ (idf_initial seeds) (idf_reachable_initial rows seeds) in
  Argent.Loop.loop (idf_private_lt rows seeds) (idf_checked_step rows seeds)
    initial (idf_accessible rows seeds initial).

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
  Proof. Admitted.

  Lemma df_unique : forall g t x, NoDup (frontier_row (df g t) x).
  Proof. Admitted.

  Lemma idf_spec : forall g t r seeds y,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    In y (idf (df g t) seeds) <-> in_iterated_frontier (base g) r seeds y.
  Proof. Admitted.

  Lemma idf_unique : forall rows seeds, NoDup (idf rows seeds).
  Proof. Admitted.
End Frontier.
