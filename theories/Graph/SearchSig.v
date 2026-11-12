(** * Depth-first search signatures

    Search folds a visitor over one exact depth-first trace.
    For example, a self-loop produces a back-edge event between entering and leaving its vertex.
    Builds on: graph data, graph semantics and preparation measures. *)

From Stdlib Require Import PArith List Bool Sorting.Permutation.
From Argent Require Import Time Std BigO.
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
  Parameter T_enter : positive -> state -> nat.
  Parameter T_leave : positive -> state -> nat.
  Parameter T_edge : edge_kind -> positive -> positive -> state -> nat.
  Parameter c_vis : nat.
  (** Entering charges the visitor's current work measure. *)
  Parameter T_enter_le : forall v s, T_enter v s <= c_vis * (vwork s + 1).
  (** Leaving charges the visitor's current work measure. *)
  Parameter T_leave_le : forall v s, T_leave v s <= c_vis * (vwork s + 1).
  (** Edge callbacks charge the visitor's current work measure. *)
  Parameter T_edge_le : forall kind u v s, T_edge kind u v s <= c_vis * (vwork s + 1).
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
  Parameter T_dfs : prepared -> list positive -> V.state -> nat.
  Parameter c_dfs : nat.
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
    T_dfs g roots s <= c_dfs * (n_reach g roots + e_reach g roots + length roots + 1) *
      (run_width g roots + V.c_vis * (B + 1)).
  (** Search has the reachable-size bound when visitor work stays bounded. *)
  Parameter dfs_bigO : bigO
    (fun '(g, roots, s, B) => work_bounded g roots s B)
    (fun '(g, roots, _, B) => (n_reach g roots + e_reach g roots + length roots + 1) *
      (run_width g roots + V.c_vis * (B + 1)))
    (fun '(g, roots, s, _) => T_dfs g roots s).
End SEARCH_TIME.

Module Type SEARCH_T (V : VISITOR_T) := SEARCH V <+ SEARCH_TIME V.
