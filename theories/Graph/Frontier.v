(** * Dominance frontiers

    Frontier columns share a visited table across the predecessors of each target.
    For example, parallel edges do not duplicate a target in a frontier row.
    Builds on: prepared graphs, dominator trees and binary-fuel loops. *)

From Stdlib Require Import PArith NArith List Bool.
From Argent Require Import Time Tactics Std BigO.
From Galois.Base Require Import Trie Loop.
From Galois.Graph Require Import Data Spec DigraphSig DomSig FrontierSig.
Import List.ListNotations.

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

Lemma idf_reachable_initial : forall rows seeds,
  idf_reachable rows seeds (idf_initial seeds).
Proof. Admitted. (* STUB *)

Lemma idf_reachable_step : forall rows seeds st next,
  idf_reachable rows seeds st -> idf_step rows st = inl next ->
  idf_reachable rows seeds next.
Proof. Admitted. (* STUB *)

Lemma idf_measure_step : forall rows seeds st next,
  idf_reachable rows seeds st -> idf_step rows st = inl next ->
  (idf_measure rows seeds next < idf_measure rows seeds st)%N.
Proof. Admitted. (* STUB *)

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
  Proof. Admitted. (* STUB *)

  Lemma df_unique : forall g t x, NoDup (frontier_row (df g t) x).
  Proof. Admitted. (* STUB *)

  Lemma idf_spec : forall g t r seeds y,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    In y (idf (df g t) seeds) <-> in_iterated_frontier (base g) r seeds y.
  Proof. Admitted. (* STUB *)

  Lemma idf_unique : forall rows seeds, NoDup (idf rows seeds).
  Proof. Admitted. (* STUB *)
End Frontier.

Module FrontierT <: FRONTIER_ALL.
  Include Frontier.

  TimeFun df.
  TimeFun idf.

  Definition c_frontier : N := 1. (* STUB *)

  Lemma T_df_le : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    (T_df g t <= c_frontier * N.of_nat
      (graph_n (base g) + graph_e (base g) + df_size g t + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
  Proof. Admitted. (* STUB *)

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
  Proof. Admitted. (* STUB *)

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
  Definition k_df_step : N := 1. (* STUB *)
  Definition k_df_stop : N := 1. (* STUB *)
  Definition k_df_column : N := 1. (* STUB *)
  Definition k_df_transpose : N := 1. (* STUB *)
  Definition k_df : N := 1. (* STUB *)

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
  Proof. Admitted. (* STUB *)

  Lemma F2_df_step : forall g t r y st next,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In y (nodes g) ->
    df_invariant g t y st -> df_step g t y st = inl next ->
    df_invariant g t y next /\ (df_potential g t y next < df_potential g t y st)%N.
  Proof. Admitted. (* STUB *)

  Lemma F3_df_stop : forall g t r y st result,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In y (nodes g) ->
    df_invariant g t y st -> df_step g t y st = inr result ->
    df_pending st = [] /\ result = rev (df_column_answer st) /\ result = df_column g t y.
  Proof. Admitted. (* STUB *)

  Lemma F4_df_driver : forall g t r y,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In y (nodes g) ->
    loopN (df_step g t y) (df_fuel g y) (df_initial g y) = inr (df_column g t y).
  Proof. Admitted. (* STUB *)

  Lemma F5_df_column : forall g t r y,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    NoDup (df_column g t y) /\ incl (df_column g t y) (nodes g) /\
      forall x, In x (df_column g t y) <-> in_frontier (base g) r x y.
  Proof. Admitted. (* STUB *)

  Lemma F6_df_transpose : forall columns x y,
    In y (frontier_row (df_transpose columns) x) <->
      exists column, In (y, column) columns /\ In x column.
  Proof. Admitted. (* STUB *)

  Lemma F7_df_equation : forall g t, df g t = df_transpose (df_columns g t).
  Proof. Admitted. (* STUB *)

  Lemma F8_df_pairs : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    fold_right (fun entry n => length (snd entry) + n) 0 (df_columns g t) = df_size g t.
  Proof. Admitted. (* STUB *)

  Lemma T1_df_step : forall g t r y st next,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In y (nodes g) ->
    df_invariant g t y st -> df_step g t y st = inl next ->
    (T_df_step g t y st + df_credit g t y next + c_loopN <= df_credit g t y st)%N.
  Proof. Admitted. (* STUB *)

  Lemma T2_df_stop : forall g t r y st result,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In y (nodes g) ->
    df_invariant g t y st -> df_step g t y st = inr result ->
    (T_df_step g t y st <= k_df_stop * N.of_nat (length (df_column g t y) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T3_df_loop : forall g t r y,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t -> In y (nodes g) ->
    (T_df_column g t y <= k_df_column *
      (df_credit g t y (df_initial g y) +
        k_df_stop * N.of_nat (length (df_column g t y) + 1) +
        N.of_nat (length (preds g y) + N.size_nat (df_fuel g y) + 1)))%N.
  Proof. Admitted. (* STUB *)

  Lemma T4_df_columns : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    (fold_right (fun y cost => T_df_column g t y + cost)%N 0%N (nodes g) <=
      k_df_column * N.of_nat
        (graph_n (base g) + graph_e (base g) + df_size g t + 1) *
        N.of_nat (graph_width (base g) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T5_df_transpose : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    (T_df_transpose (df_columns g t) <= k_df_transpose *
      N.of_nat (graph_n (base g) + df_size g t + 1) *
        N.of_nat (graph_width (base g) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T6_df_wrapper : forall g t,
    (T_df g t <= k_df * (N.of_nat (length (nodes g) + 1) +
      fold_right (fun y cost => T_df_column g t y + cost)%N 0%N (nodes g) +
      T_df_transpose (df_columns g t)))%N.
  Proof. Admitted. (* STUB *)

  Lemma T7_df_public : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    (T_df g t <= c_frontier *
      N.of_nat (graph_n (base g) + graph_e (base g) + df_size g t + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
  Proof. Admitted. (* STUB *)

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
  Proof. Admitted. (* STUB *)

  Lemma F2_idf_done : forall rows seeds,
    exists n st result,
      Nat.iter n (idf_advance rows) (idf_initial seeds) = st /\
      idf_step rows st = inr result /\ result = idf_walk rows seeds.
  Proof. Admitted. (* STUB *)

  Lemma F3_idf_closure : forall rows seeds y,
    In y (idf_walk rows seeds) <-> in_row_closure rows seeds y.
  Proof. Admitted. (* STUB *)

  Lemma F4_idf_equation : forall rows seeds, idf rows seeds = idf_walk rows seeds.
  Proof. Admitted. (* STUB *)

  Lemma F5_idf_transport : forall g t r seeds y,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    (in_row_closure (df g t) seeds y <-> in_iterated_frontier (base g) r seeds y).
  Proof. Admitted. (* STUB *)

  Lemma F6_idf_initial : forall rows seeds,
    idf_invariant rows seeds (idf_initial seeds).
  Proof. Admitted. (* STUB *)

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
  Proof. Admitted. (* STUB *)

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
