(** * Depth-first search

    Search visits roots and successor occurrences in their supplied order.
    For example, an edge to an active vertex produces a back-edge event.
    Builds on: graph data, binary-fuel loops and the search signature. *)

From Stdlib Require Import List NArith PArith Sorting.Permutation.
From Argent Require Import Time Tactics Std BigO.
From Galois.Base Require Import Trie Loop.
From Galois.Graph Require Import Data Spec DigraphSig SearchSig.
Import List.ListNotations.

Definition search_step (g : digraph) (s : search_state) : search_state + (list event) :=
  match s with
  | SearchState [] _ es => inr (rev es)
  | SearchState (task :: tasks) colours es =>
    match task with
    | SearchRoot v =>
      match trie_get v colours with
      | Some _ => inl (SearchState tasks colours es)
      | None => inl (SearchState (SearchRow v (succs g v) :: SearchLeave v :: tasks)
          (PTrieCode.set v true colours) (Enter v :: es))
      end
    | SearchRow u [] => inl (SearchState tasks colours es)
    | SearchRow u (v :: vs) =>
      match trie_get v colours with
      | None => inl (SearchState (SearchRoot v :: SearchRow u vs :: tasks) colours
          (Edge Tree u v :: es))
      | Some active => inl (SearchState (SearchRow u vs :: tasks) colours
          (Edge (if active then Back else Done) u v :: es))
      end
    | SearchLeave v => inl (SearchState tasks (PTrieCode.set v false colours) (Leave v :: es))
    end
  end.
TimeFun search_step.

Definition raw_search_budget (g : digraph) (roots : list positive) : N :=
  N.of_nat (4 * (length roots +
    fold_right (fun entry n => length (snd entry) + n) 0 (PTrieCode.elements (succ g)) + 1)).
TimeFun raw_search_budget.

Definition search_trace (g : digraph) (roots : list positive) : list event :=
  match loopN (search_step g) (raw_search_budget g roots)
      (SearchState (map SearchRoot roots) Empty []) with
  | inl s => rev (search_events s)
  | inr es => es
  end.
TimeFun search_trace.

Definition search_budget (g : prepared) (roots : list positive) : N :=
  N.double (N.double (nv g + ne g + N.of_nat (length roots) + 1))%N.
TimeFun search_budget.

Definition prepared_search_trace (g : prepared) (roots : list positive) : list event :=
  match loopN (search_step (base g)) (search_budget g roots)
      (SearchState (map SearchRoot roots) Empty []) with
  | inl s => rev (search_events s)
  | inr es => es
  end.
TimeFun prepared_search_trace.

Module SearchCode (V : VISITOR_OPS) <: SEARCH_OPS V.
  Definition dfs (g : prepared) (roots : list positive) (s : V.state) : V.state :=
    fold_events V.enter V.leave V.edge (prepared_search_trace g roots) s.
End SearchCode.

Opaque search_trace.

Module Search (V : VISITOR) <: SEARCH V.
  Include SearchCode V.

  Definition trace (g : prepared) (roots : list positive) := prepared_search_trace g roots.

  Lemma trace_depth_first : forall g roots,
    prepared_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) ->
    exists final, dfs_roots (base g) [] roots (trace g roots) final.
  Proof. Admitted. (* CONVERT: GraphSearch: validity premises require the prepared machine proof. *)

  Lemma dfs_fold : forall g roots s,
    prepared_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) ->
    dfs g roots s = fold_events V.enter V.leave V.edge (trace g roots) s.
  Proof. Admitted. (* CONVERT: GraphSearch: preserve the visitor-fold equation. *)

  Lemma trace_reach : forall g roots v,
    prepared_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) ->
    In v (entered (trace g roots)) <-> reach (base g) roots v.
  Proof. Admitted. (* CONVERT: GraphSearch: validity premises require the prepared machine proof. *)

  Lemma trace_unique : forall g roots,
    prepared_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) -> NoDup (entered (trace g roots)).
  Proof. Admitted. (* CONVERT: GraphSearch: validity premises require the prepared machine proof. *)

  Lemma trace_nested : forall g roots,
    prepared_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) -> trace_stack [] (trace g roots) [].
  Proof. Admitted. (* CONVERT: GraphSearch: validity premises require the prepared machine proof. *)

  Lemma trace_edges : forall g roots u,
    prepared_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) -> reach (base g) roots u ->
    Permutation (edge_targets u (trace g roots)) (succs (base g) u).
  Proof. Admitted. (* CONVERT: GraphSearch: validity premises require the prepared machine proof. *)

  Lemma trace_edges_sound : forall g roots kind u v,
    prepared_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) ->
    In (Edge kind u v) (trace g roots) -> reach (base g) roots u /\ edge (base g) u v.
  Proof. Admitted. (* CONVERT: GraphSearch: validity premises require the prepared machine proof. *)

  Lemma trace_kinds : forall g roots prefix kind u v suffix,
    prepared_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) ->
    trace g roots = prefix ++ Edge kind u v :: suffix -> event_kind_correct prefix kind v.
  Proof. Admitted. (* CONVERT: GraphSearch: validity premises require the prepared machine proof. *)
End Search.

Module SearchT (V : VISITOR_T) <: SEARCH_ALL V.
  Include Search V.
  TimeFun dfs.
  Definition c_dfs : N := 1%N. (* STUB *)

  Definition n_reach (g : prepared) (roots : list positive) : nat :=
    length (entered (trace g roots)).
  Definition e_reach (g : prepared) (roots : list positive) : nat :=
    fold_right (fun u n => length (succs (base g) u) + n) 0 (entered (trace g roots)).
  Definition run_width (g : prepared) (roots : list positive) : nat :=
    graph_max (vertex_width roots)
      (fold_right (fun u w => graph_max (vertex_width (succs (base g) u)) w) 0
        (entered (trace g roots))).
  Definition work_bounded (g : prepared) (roots : list positive) (s : V.state) (B : nat) :=
    forall prefix suffix, trace g roots = prefix ++ suffix ->
      V.vwork (fold_events V.enter V.leave V.edge prefix s) <= B.

  Lemma T_dfs_le : forall g roots s B, work_bounded g roots s B ->
    (T_dfs g roots s <=
      c_dfs * (N.of_nat (n_reach g roots + e_reach g roots + length roots + 1) *
      (N.of_nat (run_width g roots) + V.c_vis * N.of_nat (B + 1)) +
        N.of_nat (N.size_nat (nv g) + N.size_nat (ne g) + 1)))%N.
  Proof. Admitted. (* STUB *)

  Lemma dfs_bigO : bigO
    (fun '(g, roots, s, B) => work_bounded g roots s B)
    (fun '(g, roots, _, B) =>
      (N.of_nat (n_reach g roots + e_reach g roots + length roots + 1) *
        (N.of_nat (run_width g roots) + V.c_vis * N.of_nat (B + 1)) +
          N.of_nat (N.size_nat (nv g) + N.size_nat (ne g) + 1))%N)
    (fun '(g, roots, s, _) => T_dfs g roots s).
  Proof. Admitted. (* STUB *)

  Definition search_step := search_step.
  TimeFun search_step.
  Definition search_budget := search_budget.
  TimeFun search_budget.
  Definition search_trace := prepared_search_trace.
  TimeFun search_trace.
  Definition k_step : N := 1%N. (* STUB *)
  Definition k_trace : N := 1%N. (* STUB *)
  Definition k_fold : N := 1%N. (* STUB *)
  Definition k_budget : N := 1%N. (* STUB *)

  Definition initial (roots : list positive) : search_state :=
    SearchState (map SearchRoot roots) Empty [].
  Definition advance (g : digraph) (s : search_state) : search_state :=
    match search_step g s with inl next => next | inr _ => s end.
  Definition machine_reachable (g : prepared) roots st : Prop :=
    exists n, Nat.iter n (advance (base g)) (initial roots) = st.
  Definition support (g : prepared) roots := entered (trace g roots).
  Definition unvisited (g : prepared) roots (st : search_state) : nat :=
    fold_right (fun v n =>
      match trie_get v (search_colours st) with
      | None => 2 + length (succs (base g) v) + n
      | Some _ => n
      end) 0 (support g roots).
  Definition pending (st : search_state) : nat :=
    fold_right (fun task n =>
      match task with
      | SearchRoot _ => 1 + n
      | SearchRow _ vs => 2 * length vs + 1 + n
      | SearchLeave _ => 1 + n
      end) 0 (search_tasks st).
  Definition potential g roots st : N := N.of_nat (2 * unvisited g roots st + pending st).
  Definition planned_fuel (g : prepared) : N := (2 * (nv g + ne g) + 1)%N.
  Definition event_width (w : nat) (e : event) : Prop :=
    match e with
    | Enter v | Leave v => Pos.size_nat v <= w
    | Edge _ u v => Pos.size_nat u <= w /\ Pos.size_nat v <= w
    end.
  Definition representation (st : search_state) : Prop :=
    NoDup (entered (rev (search_events st))) /\
    forall v,
      (trie_get v (search_colours st) = None <->
        ~ In (Enter v) (search_events st)) /\
      (trie_get v (search_colours st) = Some true <->
        In (Enter v) (search_events st) /\ ~ In (Leave v) (search_events st)) /\
      (trie_get v (search_colours st) = Some false <->
        In (Leave v) (search_events st)).
  Definition invariant g roots st : Prop :=
    machine_reachable g roots st /\ representation st /\
    exists suffix, trace g roots = rev (search_events st) ++ suffix.
  Definition all_rows (g : digraph) : nat :=
    fold_right (fun entry n => length (snd entry) + n) 0 (PTrieCode.elements (succ g)).
  Definition driver_credit g roots w st :=
    ((k_step * N.of_nat (w + 1) + 1) * potential g roots st)%N.
  Definition stop_budget g roots := (k_trace * N.of_nat (length (trace g roots) + 1))%N.

  Lemma F1_budget : forall g roots,
    search_budget g roots = (4 * (nv g + ne g + N.of_nat (length roots) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma F2_trace : forall g roots,
    trace g roots = search_trace g roots /\
    search_trace g roots =
      match loopN (search_step (base g)) (search_budget g roots) (initial roots) with
      | inl st => rev (search_events st)
      | inr es => es
      end.
  Proof. Admitted. (* STUB *)

  Lemma F3_initial : forall g roots,
    prepared_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) ->
    invariant g roots (initial roots) /\
    potential g roots (initial roots) =
      N.of_nat (4 * n_reach g roots + 2 * e_reach g roots + length roots).
  Proof. Admitted. (* STUB *)

  Lemma F4_step : forall g roots st next,
    prepared_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) ->
    invariant g roots st -> search_step (base g) st = inl next ->
    invariant g roots next /\ (potential g roots next < potential g roots st)%N.
  Proof. Admitted. (* STUB *)

  Lemma F5_stop : forall g roots st es,
    prepared_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) ->
    invariant g roots st -> search_step (base g) st = inr es ->
    search_tasks st = [] /\ es = trace g roots.
  Proof. Admitted. (* STUB *)

  Lemma F6_width : forall g roots st,
    prepared_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) ->
    invariant g roots st -> Forall (event_width (run_width g roots)) (search_events st).
  Proof. Admitted. (* STUB *)

  Lemma F7_events : forall g roots,
    prepared_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) ->
    length (trace g roots) = 2 * n_reach g roots + e_reach g roots.
  Proof. Admitted. (* STUB *)

  Lemma F8_fuel : forall g roots,
    prepared_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) ->
    exists es, loopN (search_step (base g)) (search_budget g roots)
      (initial roots) = inr es.
  Proof. Admitted. (* STUB *)

  Lemma T1_step : forall g roots st next w,
    prepared_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) ->
    invariant g roots st -> Forall (event_width w) (trace g roots) ->
    vertex_width roots <= w -> search_step (base g) st = inl next ->
    (T_search_step (base g) st <= k_step * N.of_nat (w + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T2_stop : forall g roots st es,
    prepared_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) ->
    invariant g roots st -> search_step (base g) st = inr es ->
    (T_search_step (base g) st <= stop_budget g roots)%N.
  Proof. Admitted. (* STUB *)

  Lemma T3_loop : forall g roots w,
    prepared_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) ->
    Forall (event_width w) (trace g roots) -> vertex_width roots <= w ->
    (T_loopN (search_step (base g)) (T_search_step (base g))
      (search_budget g roots) (initial roots) <=
    c_loopN * (driver_credit g roots w (initial roots) + stop_budget g roots +
      N.of_nat (N.size_nat (search_budget g roots)) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T4_trace : forall g roots w,
    prepared_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) ->
    Forall (event_width w) (trace g roots) -> vertex_width roots <= w ->
    (T_search_trace g roots <= k_trace *
      (T_search_budget g roots + N.of_nat (length roots) +
        T_loopN (search_step (base g)) (T_search_step (base g))
          (search_budget g roots) (initial roots) +
        N.of_nat (length (trace g roots)) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T5_fold : forall g roots s B,
    work_bounded g roots s B ->
    (T_fold_events V.enter V.T_enter V.leave V.T_leave V.edge V.T_edge
      (trace g roots) s <=
    k_fold * N.of_nat (length (trace g roots) + 1) *
      (V.c_vis * N.of_nat (B + 1) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T6_dfs : forall g roots s,
    (T_dfs g roots s <= k_trace * (T_search_trace g roots +
      T_fold_events V.enter V.T_enter V.leave V.T_leave V.edge V.T_edge
        (trace g roots) s + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T7_public : forall g roots s B, work_bounded g roots s B ->
    (T_dfs g roots s <= c_dfs * (N.of_nat (n_reach g roots + e_reach g roots + length roots + 1) *
      (N.of_nat (run_width g roots) + V.c_vis * N.of_nat (B + 1)) +
        N.of_nat (N.size_nat (nv g) + N.size_nat (ne g) + 1)))%N.
  Proof. Admitted. (* STUB *)
End SearchT.

Transparent search_trace.
