(** * Depth-first search signatures

    Search folds a visitor over one exact depth-first trace.
    For example, a self-loop produces a back-edge event between entering and leaving its vertex.
    Builds on: graph data, graph semantics and preparation measures. *)

From Stdlib Require Import PArith NArith List Bool Sorting.Permutation.
From Argent Require Import Time Std BigO.
From Galois.Base Require Import Trie Loop.
From Galois.Graph Require Import Data Spec DigraphSig.
Import List.ListNotations.

Inductive event :=
  | Enter (v : positive)
  | Leave (v : positive)
  | Edge (kind : edge_kind) (source target : positive).

Definition visit_event {S : Type} (enter leave : positive -> S -> S)
    (on_edge : edge_kind -> positive -> positive -> S -> S) (s : S) (e : event) : S :=
  match e with
  | Enter v => enter v s
  | Leave v => leave v s
  | Edge kind u v => on_edge kind u v s
  end.
TimeFun visit_event.

Definition fold_events {S : Type} (enter leave : positive -> S -> S)
    (on_edge : edge_kind -> positive -> positive -> S -> S) (es : list event) (s : S) : S :=
  fold_left (visit_event enter leave on_edge) es s.
TimeFun fold_events.

Fixpoint entered (es : list event) : list positive :=
  match es with
  | [] => []
  | Enter v :: rest => v :: entered rest
  | _ :: rest => entered rest
  end.
TimeFun entered.

Fixpoint edge_targets (u : positive) (es : list event) : list positive :=
  match es with
  | [] => []
  | Edge _ v w :: rest =>
    if Pos.eqb u v then w :: edge_targets u rest else edge_targets u rest
  | _ :: rest => edge_targets u rest
  end.
TimeFun edge_targets.

(** Enter and leave events obey the active DFS stack. *)
Inductive trace_stack : list positive -> list event -> list positive -> Prop :=
  | stack_nil : forall stack, trace_stack stack [] stack
  | stack_enter : forall stack v rest final,
      trace_stack (v :: stack) rest final -> trace_stack stack (Enter v :: rest) final
  | stack_leave : forall stack v rest final,
      trace_stack stack rest final -> trace_stack (v :: stack) (Leave v :: rest) final
  | stack_edge : forall stack kind u v rest final,
      trace_stack (u :: stack) rest final ->
      trace_stack (u :: stack) (Edge kind u v :: rest) final.

(** Edge kinds describe the target's colour immediately before the event. *)
Definition event_kind_correct (prefix : list event) (kind : edge_kind) (v : positive) : Prop :=
  match kind with
  | Tree => ~ In (Enter v) prefix
  | Back => In (Enter v) prefix /\ ~ In (Leave v) prefix
  | Done => In (Leave v) prefix
  end.

(** DFS derivations preserve successor order and pair tree edges with recursive visits. *)
Inductive dfs_visit (g : digraph) :
    list positive -> list positive -> positive -> list event -> list positive -> Prop :=
  | dfs_visit_node : forall active seen v inside final,
      ~ In v seen ->
      dfs_rows g (v :: active) (v :: seen) v (succs g v) inside final ->
      dfs_visit g active seen v (Enter v :: inside ++ [Leave v]) final
with dfs_rows (g : digraph) : list positive -> list positive -> positive ->
    list positive -> list event -> list positive -> Prop :=
  | dfs_rows_nil : forall active seen u, dfs_rows g active seen u [] [] seen
  | dfs_rows_tree : forall active seen u v rest inside middle outside final,
      ~ In v seen -> dfs_visit g active seen v inside middle ->
      dfs_rows g active middle u rest outside final ->
      dfs_rows g active seen u (v :: rest) (Edge Tree u v :: inside ++ outside) final
  | dfs_rows_seen : forall active seen u v rest kind outside final,
      In v seen ->
      ((kind = Back /\ In v active) \/ (kind = Done /\ ~ In v active)) ->
      dfs_rows g active seen u rest outside final ->
      dfs_rows g active seen u (v :: rest) (Edge kind u v :: outside) final.

(** Root traversal skips roots that an earlier traversal has already visited. *)
Inductive dfs_roots (g : digraph) :
    list positive -> list positive -> list event -> list positive -> Prop :=
  | dfs_roots_nil : forall seen, dfs_roots g seen [] [] seen
  | dfs_roots_seen : forall seen v rest es final,
      In v seen -> dfs_roots g seen rest es final -> dfs_roots g seen (v :: rest) es final
  | dfs_roots_new : forall seen v rest inside middle outside final,
      ~ In v seen -> dfs_visit g [] seen v inside middle ->
      dfs_roots g middle rest outside final ->
      dfs_roots g seen (v :: rest) (inside ++ outside) final.

Inductive search_task :=
  | SearchRoot (v : positive)
  | SearchRow (u : positive) (vs : list positive)
  | SearchLeave (v : positive).

Record search_state := SearchState {
  search_tasks : list search_task;
  search_colours : ptrie bool;
  search_events : list event
}.

Module Type VISITOR_OPS.
  Parameter state : Type.
  Parameter enter : positive -> state -> state.
  Parameter leave : positive -> state -> state.
  Parameter edge : edge_kind -> positive -> positive -> state -> state.
End VISITOR_OPS.

Module Type VISITOR := VISITOR_OPS.

Module Type VISITOR_TIME (Import V : VISITOR).
  (* spec: vwork *)
  Parameter vwork : state -> nat.
  Parameter T_enter : positive -> state -> N.
  Parameter T_leave : positive -> state -> N.
  Parameter T_edge : edge_kind -> positive -> positive -> state -> N.
  Parameter c_vis : N.
  (** Entering charges the visitor's current work measure. *)
  Parameter T_enter_le : forall v s, (T_enter v s <= c_vis * N.of_nat (vwork s + 1))%N.
  (** Leaving charges the visitor's current work measure. *)
  Parameter T_leave_le : forall v s, (T_leave v s <= c_vis * N.of_nat (vwork s + 1))%N.
  (** Edge callbacks charge the visitor's current work measure. *)
  Parameter T_edge_le : forall kind u v s,
    (T_edge kind u v s <= c_vis * N.of_nat (vwork s + 1))%N.
End VISITOR_TIME.

Module Type VISITOR_T := VISITOR <+ VISITOR_TIME.

Module Type SEARCH_OPS (V : VISITOR_OPS).
  Parameter dfs : prepared -> list positive -> V.state -> V.state.
End SEARCH_OPS.

Module Type SEARCH_LAWS (V : VISITOR) (Import S : SEARCH_OPS V).
  (* spec: trace *)
  Parameter trace : prepared -> list positive -> list event.
  (** The trace follows graph successor order and the supplied root order. *)
  Parameter trace_depth_first : forall g roots,
    exists final, dfs_roots (base g) [] roots (trace g roots) final.
  (** The visitor observes precisely the trace, in order. *)
  Parameter dfs_fold : forall g roots s,
    dfs g roots s = fold_events V.enter V.leave V.edge (trace g roots) s.
  (** Entered vertices are precisely the vertices reachable from the supplied roots. *)
  Parameter trace_reach : forall g roots v,
    In v (entered (trace g roots)) <-> reach (base g) roots v.
  (** Each reachable vertex is entered once. *)
  Parameter trace_unique : forall g roots, NoDup (entered (trace g roots)).
  (** Every entering event has a properly nested leaving event. *)
  Parameter trace_nested : forall g roots, trace_stack [] (trace g roots) [].
  (** Visited adjacency rows retain every successor occurrence. *)
  Parameter trace_edges : forall g roots u, reach (base g) roots u ->
    Permutation (edge_targets u (trace g roots)) (succs (base g) u).
  (** Every edge event comes from a reachable source and a real successor. *)
  Parameter trace_edges_sound : forall g roots kind u v,
    In (Edge kind u v) (trace g roots) -> reach (base g) roots u /\ edge (base g) u v.
  (** Edge colours agree with the preceding entering and leaving events. *)
  Parameter trace_kinds : forall g roots prefix kind u v suffix,
    trace g roots = prefix ++ Edge kind u v :: suffix -> event_kind_correct prefix kind v.
End SEARCH_LAWS.

Module Type SEARCH (V : VISITOR) := SEARCH_OPS V <+ SEARCH_LAWS V.

Module Type SEARCH_TIME (V : VISITOR_T) (Import S : SEARCH V).
  Parameter T_dfs : prepared -> list positive -> V.state -> N.
  Parameter c_dfs : N.
  Definition n_reach (g : prepared) (roots : list positive) : nat :=
    length (entered (trace g roots)).
  Definition e_reach (g : prepared) (roots : list positive) : nat :=
    fold_right (fun u n => length (succs (base g) u) + n) 0 (entered (trace g roots)).
  Definition run_width (g : prepared) (roots : list positive) : nat :=
    graph_max (graph_width (base g)) (vertex_width roots).
  (** Every prefix includes the callback state before its next event. *)
  Definition work_bounded (g : prepared) (roots : list positive) (s : V.state) (B : nat) :=
    forall prefix suffix, trace g roots = prefix ++ suffix ->
      V.vwork (fold_events V.enter V.leave V.edge prefix s) <= B.
  (** Search charges each visited vertex, edge occurrence, root and callback. *)
  Parameter T_dfs_le : forall g roots s B, work_bounded g roots s B ->
    (T_dfs g roots s <=
      c_dfs * N.of_nat (n_reach g roots + e_reach g roots + length roots + 1) *
      (N.of_nat (run_width g roots) + V.c_vis * N.of_nat (B + 1)))%N.
  (** Search has the reachable-size bound when visitor work stays bounded. *)
  Parameter dfs_bigO : bigO
    (fun '(g, roots, s, B) => work_bounded g roots s B)
    (fun '(g, roots, _, B) =>
      (N.of_nat (n_reach g roots + e_reach g roots + length roots + 1) *
        (N.of_nat (run_width g roots) + V.c_vis * N.of_nat (B + 1)))%N)
    (fun '(g, roots, s, _) => T_dfs g roots s).
End SEARCH_TIME.

Module Type SEARCH_T (V : VISITOR_T) := SEARCH V <+ SEARCH_TIME V.

(** * Search proof plan

    The weighted white work comes from [GraphSearchScopedCost] at [87192fe].
    The task machine also charges root, empty-row and leave tasks.
    Its continuing-step credit is distinct from the design's compact-machine fuel.
    The current fuel constructor scans every stored successor row.
    [T7_public] is therefore an open implementation obligation. *)

Module Type SEARCH_PLAN (V : VISITOR_T) (Import S : SEARCH_T V).
  Parameter search_step : digraph -> search_state -> search_state + list event.
  Parameter T_search_step : digraph -> search_state -> N.
  Parameter search_budget : digraph -> list positive -> N.
  Parameter T_search_budget : digraph -> list positive -> N.
  Parameter search_trace : digraph -> list positive -> list event.
  Parameter T_search_trace : digraph -> list positive -> N.
  Parameter k_step k_trace k_fold k_budget : N.

  Definition initial (roots : list positive) : search_state :=
    SearchState (map SearchRoot roots) Empty [].

  Definition advance (g : digraph) (s : search_state) : search_state :=
    match search_step g s with inl next => next | inr _ => s end.

  (** Reachable states are generated by the actual transition from empty colours. *)
  Definition machine_reachable (g : prepared) roots st : Prop :=
    exists n, Nat.iter n (advance (base g)) (initial roots) = st.

  Definition support (g : prepared) roots := entered (trace g roots).

  (** White work includes outgoing occurrences before discovery transfers them to tasks. *)
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

  (** This task potential has the requested form and retains administrative work. *)
  Definition potential g roots st : N := N.of_nat (2 * unvisited g roots st + pending st).

  (** The compact design fuel uses cached graph counts and omits the supplied root scan. *)
  Definition planned_fuel (g : prepared) : N := (2 * (nv g + ne g) + 1)%N.

  Definition event_width (w : nat) (e : event) : Prop :=
    match e with
    | Enter v | Leave v => Pos.size_nat v <= w
    | Edge _ u v => Pos.size_nat u <= w /\ Pos.size_nat v <= w
    end.

  (** Every stored colour is the colour determined by the emitted event prefix. *)
  Definition representation (st : search_state) : Prop :=
    NoDup (entered (rev (search_events st))) /\
    forall v,
      (trie_get v (search_colours st) = None <->
        ~ In (Enter v) (search_events st)) /\
      (trie_get v (search_colours st) = Some true <->
        In (Enter v) (search_events st) /\ ~ In (Leave v) (search_events st)) /\
      (trie_get v (search_colours st) = Some false <->
        In (Leave v) (search_events st)).

  (** Prefix agreement connects machine states to visitor callback bounds. *)
  Definition invariant g roots st : Prop :=
    machine_reachable g roots st /\ representation st /\
    exists suffix, trace g roots = rev (search_events st) ++ suffix.

  Definition all_rows (g : digraph) : nat :=
    fold_right (fun entry n => length (snd entry) + n) 0 (PTrieCode.elements (succ g)).

  Definition driver_credit g roots w st :=
    ((k_step * N.of_nat (w + 1) + 1) * potential g roots st)%N.

  (** The stopping step reverses at most the whole final event trace. *)
  Definition stop_budget g roots := (k_trace * N.of_nat (length (trace g roots) + 1))%N.

  (** The code uses all stored rows to construct its binary fuel. *)
  Parameter F1_budget : forall g roots,
    search_budget g roots = N.of_nat (4 * (length roots + all_rows g + 1)).

  (** The trace is the loop result and retains the partial prefix on exhaustion. *)
  Parameter F2_trace : forall g roots,
    trace g roots = search_trace (base g) roots /\
    search_trace (base g) roots =
      match loopN (search_step (base g)) (search_budget (base g) roots) (initial roots) with
      | inl st => rev (search_events st)
      | inr es => es
      end.

  (** Initialization supplies all white work and the ordered root tasks. *)
  Parameter F3_initial : forall g roots,
    invariant g roots (initial roots) /\
    potential g roots (initial roots) =
      N.of_nat (4 * n_reach g roots + 2 * e_reach g roots + length roots).

  (** Continuing steps maintain colour and prefix agreement and spend task credit. *)
  Parameter F4_step : forall g roots st next,
    invariant g roots st -> search_step (base g) st = inl next ->
    invariant g roots next /\ (potential g roots next < potential g roots st)%N.

  (** A terminal state has no tasks and emits the full trace. *)
  Parameter F5_stop : forall g roots st es,
    invariant g roots st -> search_step (base g) st = inr es ->
    search_tasks st = [] /\ es = trace g roots.

  (** Identifier bounds must cover every reachable key, including unlisted successors. *)
  Parameter F6_width : forall g roots st,
    invariant g roots st -> Forall (event_width (run_width g roots)) (search_events st).

  (** Event counts include two events per reached vertex and every successor occurrence. *)
  Parameter F7_events : forall g roots,
    length (trace g roots) = 2 * n_reach g roots + e_reach g roots.

  (** The concrete task fuel needs a step-count proof separate from the compact design fuel. *)
  Parameter F8_fuel : forall g roots,
    exists es, loopN (search_step (base g)) (search_budget (base g) roots)
      (initial roots) = inr es.

  (** Continuing steps have bounded local trie work before visitor folding. *)
  Parameter T1_step : forall g roots st next w,
    invariant g roots st -> Forall (event_width w) (trace g roots) ->
    vertex_width roots <= w -> search_step (base g) st = inl next ->
    (T_search_step (base g) st <= k_step * N.of_nat (w + 1))%N.

  (** The stopping callback pays the final event reversal. *)
  Parameter T2_stop : forall g roots st es,
    invariant g roots st -> search_step (base g) st = inr es ->
    (T_search_step (base g) st <= stop_budget g roots)%N.

  (** The loop theorem adds the actual fuel width once. *)
  Parameter T3_loop : forall g roots w,
    Forall (event_width w) (trace g roots) -> vertex_width roots <= w ->
    (T_loopN (search_step (base g)) (T_search_step (base g))
      (search_budget (base g) roots) (initial roots) <=
    c_loopN * (driver_credit g roots w (initial roots) + stop_budget g roots +
      N.of_nat (N.size_nat (search_budget (base g) roots)) + 1))%N.

  (** Constructing fuel also pays the raw successor-trie traversal. *)
  Parameter T4_trace : forall g roots w,
    Forall (event_width w) (trace g roots) -> vertex_width roots <= w ->
    (T_search_trace (base g) roots <= k_trace *
      (T_search_budget (base g) roots + N.of_nat (length roots) +
        T_loopN (search_step (base g)) (T_search_step (base g))
          (search_budget (base g) roots) (initial roots) +
        N.of_nat (length (trace g roots)) + 1))%N.

  (** Prefix work bounds pay each callback and the event-fold driver. *)
  Parameter T5_fold : forall g roots s B,
    work_bounded g roots s B ->
    (T_fold_events V.enter V.T_enter V.leave V.T_leave V.edge V.T_edge
      (trace g roots) s <=
    k_fold * N.of_nat (length (trace g roots) + 1) * (V.c_vis * N.of_nat (B + 1) + 1))%N.

  (** The wrapper composes trace construction and the callback fold. *)
  Parameter T6_dfs : forall g roots s,
    (T_dfs g roots s <= k_trace * (T_search_trace (base g) roots +
      T_fold_events V.enter V.T_enter V.leave V.T_leave V.edge V.T_edge
        (trace g roots) s + 1))%N.

  (** The unchanged public target needs fuel-scan, width and zero-factor repairs in the code. *)
  Parameter T7_public : forall g roots s B, work_bounded g roots s B ->
    (T_dfs g roots s <= c_dfs * N.of_nat (n_reach g roots + e_reach g roots + length roots + 1) *
      (N.of_nat (run_width g roots) + V.c_vis * N.of_nat (B + 1)))%N.
End SEARCH_PLAN.

Module Type SEARCH_ALL (V : VISITOR_T) := SEARCH_T V <+ SEARCH_PLAN V.
