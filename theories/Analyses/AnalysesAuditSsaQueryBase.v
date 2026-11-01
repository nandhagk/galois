(** * SSA liveness and SEG portfolio choices

    These definitions select liveness and expression-availability queries and state their
    agreement boundaries. For example, a one-shot liveness query searches the graph after
    removing edges that define the requested value.
    Builds on: SSA point uses, graph preparation, liveness and SEG analyses. *)

From Stdlib Require Import List Bool PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet.
From Galois.Order Require Import OrderLattice OrderPowerset.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphDominators.
From Galois.Fixpoint Require Import FixpointSystem FixpointLeast FixpointWorklist FixpointTotal
  FixpointSchedule.
From Galois.Views Require Import ViewsGraph ViewsSsaPoints.
From Galois.Analyses Require Import AnalysesLiveness AnalysesAvailable AnalysesSsaLiveQuery
  AnalysesSsaLiveSets AnalysesSeg.
Import List.ListNotations.

(** * Liveness queries *)

Definition audit_list_has {V} (EV : encoding V) (x : V) (xs : list V) : bool :=
  existsb (fun y => Pos.eqb (encode EV x) (encode EV y)) xs.

Definition audit_live_surviving_graph {N E V} (EV : encoding V)
    (p : point_uses N E V) (x : V) : Graph.t N E :=
  let g := live_graph p in
  Graph.Make (Graph.entries g) (Graph.nodes g)
    (fun n => filter (fun e => negb (audit_list_has EV x (edge_def p e))) (Graph.out g n))
    (Graph.source g) (Graph.target g).

Definition audit_live_use_at {N E V} (EV : encoding V) (p : point_uses N E V) (x : V) (n : N)
    : bool :=
  audit_list_has EV x (exit_use p n) ||
    existsb (fun e => audit_list_has EV x (edge_use p e)) (Graph.out (live_graph p) n).

Definition audit_live_one_shot {N E V} (EN : encoding N) (EV : encoding V)
    (p : point_uses N E V) (n : N) (x : V) : bool :=
  let g := audit_live_surviving_graph EV p x in
  let seen := preorder (dfs (prepare EN g) FinSet.empty [n]) in
  existsb (audit_live_use_at EV p x) seen.

(** On a listed node of a well-formed graph with distinct outgoing edges, one-shot search decides
    syntactic liveness. *)
Definition audit_live_one_shot_exact_statement : Prop :=
  forall N E V (EN : encoding N) (EV : encoding V) (p : point_uses N E V) n x,
    graph_wf (live_graph p) -> (forall z, NoDup (Graph.out (live_graph p) z)) ->
    In n (Graph.nodes (live_graph p)) ->
    (audit_live_one_shot EN EV p n x = true <-> syntactic_live p x n).

(** Build value rows from the DFS already stored by graph preparation. *)
Definition audit_live_values_from_graph {B BE N E V} (EN : encoding N) (EV : encoding V)
    (s : ssa_points B BE N E V) (idx : ssa_query_graph N E) : ssa_query_values N V :=
  let p := point_model s in
  let ns := preorder (query_dfs idx) in
  let us := fold_right (fun n m =>
    fold_right (fun x acc => Map.set EV x (FinSet.add EN n (live_index_get EV x acc)) acc)
      m (exit_use p n ++ flat_map (edge_use p) (Graph.out (live_graph p) n))) Map.empty ns in
  let ds := fold_right (fun binding m =>
    match point_definition s (fst binding) with
    | Some d => Map.set EV (fst binding) d m
    | None => m
    end) Map.empty (Map.elements us) in
  SsaQueryValues ds us.

(** Value preparation from a freshly prepared graph agrees with the original value index. *)
Definition audit_live_values_reuse_statement : Prop :=
  forall B BE N E V (EN : encoding N) (EE : encoding E) (EV : encoding V)
    (s : ssa_points B BE N E V),
    audit_live_values_from_graph EN EV s
      (prepare_ssa_query_graph EN EE (live_graph (point_model s))) =
      prepare_ssa_query_values EN EV s.

(** A graph index with matching graph and DFS gives the original value index for the new view. *)
Definition audit_live_values_refresh_statement : Prop :=
  forall B BE N E V (EN : encoding N) (EV : encoding V)
    (s : ssa_points B BE N E V) (idx : ssa_query_graph N E),
    query_cfg idx = live_graph (point_model s) ->
    query_dfs idx = dfs (prepare EN (live_graph (point_model s))) FinSet.empty
      (Graph.entries (live_graph (point_model s))) ->
    audit_live_values_from_graph EN EV s idx = prepare_ssa_query_values EN EV s.

(** With a fresh graph index, SSA laws and readiness, refresh decides liveness at reachable
    nodes. *)
Definition audit_live_refresh_query_exact_statement : Prop :=
  forall B BE N E V (EN : encoding N) (EE : encoding E) (EV : encoding V)
    (s : ssa_points B BE N E V) (idx : ssa_query_graph N E),
    idx = prepare_ssa_query_graph EN EE (live_graph (point_model s)) ->
    ssa_point_laws s -> reachable_point_ssa s ->
    ready EN (live_graph (point_model s)) (prepare EN (live_graph (point_model s))) ->
    forall n x, reachable (live_graph (point_model s)) n ->
      (ssa_live_query EN EV idx (audit_live_values_from_graph EN EV s idx) n x = true <->
        syntactic_live (point_model s) x n).

(** Prepared queries retain the graph index and the value index together. *)
Record audit_live_prepared (N E V : Type) : Type := AuditLiveIndexes {
  audit_live_graph_index : ssa_query_graph N E;
  audit_live_value_index : ssa_query_values N V
}.

Definition audit_live_prepare {B BE N E V} (EN : encoding N) (EE : encoding E) (EV : encoding V)
    (s : ssa_points B BE N E V) : audit_live_prepared N E V :=
  let idx := prepare_ssa_query_graph EN EE (live_graph (point_model s)) in
  AuditLiveIndexes N E V idx (audit_live_values_from_graph EN EV s idx).

Definition audit_live_prepared_query {N E V} (EN : encoding N) (EV : encoding V)
    (p : audit_live_prepared N E V) : N -> V -> bool :=
  ssa_live_query EN EV (audit_live_graph_index N E V p) (audit_live_value_index N E V p).

(** A freshly prepared query agrees with separately prepared graph and value indexes. *)
Definition audit_live_prepared_agrees_statement : Prop :=
  forall B BE N E V (EN : encoding N) (EE : encoding E) (EV : encoding V)
    (s : ssa_points B BE N E V) n x,
    audit_live_prepared_query EN EV (audit_live_prepare EN EE EV s) n x =
      ssa_live_query EN EV (prepare_ssa_query_graph EN EE (live_graph (point_model s)))
        (prepare_ssa_query_values EN EV s) n x.

Definition audit_live_prepared_batch {N E V} (EN : encoding N) (EV : encoding V)
    (p : audit_live_prepared N E V) (queries : list (N * V)) : list bool :=
  map (fun query => audit_live_prepared_query EN EV p (fst query) (snd query)) queries.

(** A prepared batch preserves query count and maps each query through the stored indexes. *)
Definition audit_live_prepared_batch_statement : Prop :=
  forall N E V (EN : encoding N) (EV : encoding V) p queries,
    length (audit_live_prepared_batch EN EV p queries) = length queries /\
    audit_live_prepared_batch EN EV p queries =
      map (fun query => ssa_live_query EN EV (audit_live_graph_index N E V p)
        (audit_live_value_index N E V p) (fst query) (snd query)) queries.

(** Reference input occurrences for value preparation, including parallel edges. *)
Definition audit_live_use_occurrences {N E V} (p : point_uses N E V) (ns : list N) : list (N * V) :=
  flat_map (fun n => map (fun x => (n, x))
    (exit_use p n ++ flat_map (edge_use p) (Graph.out (live_graph p) n))) ns.

(** The occurrence list counts exit uses and every outgoing edge's uses at each supplied node. *)
Definition audit_live_occurrence_count_statement : Prop := forall N E V (p : point_uses N E V) ns,
    length (audit_live_use_occurrences p ns) = fold_right (fun n count =>
      length (exit_use p n) + fold_right (fun e k => length (edge_use p e) + k)
        0 (Graph.out (live_graph p) n) + count) 0 ns.

Inductive audit_live_choice : Type :=
  | AuditLiveGeneral
  | AuditLiveOneShot
  | AuditLivePrepared
  | AuditLiveSparse.

Definition audit_live_select {B BE S O N E V C} (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (choice : audit_live_choice) (s : ssa_points B BE N E V)
    (vv : var_view S O N E V C) : N -> V -> bool :=
  match choice with
  | AuditLiveGeneral => general_live_query EN EE EV vv
  | AuditLiveOneShot => audit_live_one_shot EN EV (point_model s)
  | AuditLivePrepared => audit_live_prepared_query EN EV (audit_live_prepare EN EE EV s)
  | AuditLiveSparse => sparse_live_at EN EV (sparse_live_materialize EN EE EV (point_model s))
  end.

(** With matching point views, SSA laws and readiness, each choice decides reachable liveness. *)
Definition audit_live_select_exact_statement : Prop :=
  forall B BE S O N E V C (EN : encoding N) (EE : encoding E) (EV : encoding V)
      (s : ssa_points B BE N E V) (vv : var_view S O N E V C),
    point_model s = var_point_uses vv -> ssa_point_laws s -> reachable_point_ssa s ->
    ready EN (live_graph (point_model s)) (prepare EN (live_graph (point_model s))) ->
    forall n x, reachable (live_graph (point_model s)) n ->
      forall choice, audit_live_select EN EE EV choice s vv n x = true <->
        syntactic_live (point_model s) x n.

(** With matching views and readiness, general and sparse queries decide liveness at listed
    nodes. *)
Definition audit_live_all_points_agrees_statement : Prop :=
  forall B BE S O N E V C (EN : encoding N) (EE : encoding E) (EV : encoding V)
      (s : ssa_points B BE N E V) (vv : var_view S O N E V C),
    point_model s = var_point_uses vv ->
    ready EN (live_graph (point_model s)) (prepare EN (live_graph (point_model s))) ->
    forall n x, In n (Graph.nodes (live_graph (point_model s))) ->
      audit_live_select EN EE EV AuditLiveGeneral s vv n x =
      audit_live_select EN EE EV AuditLiveSparse s vv n x /\
      (audit_live_select EN EE EV AuditLiveSparse s vv n x = true <->
        syntactic_live (point_model s) x n).

(** With matching views and readiness, general, one-shot and sparse queries agree at listed nodes
    and decide syntactic liveness. *)
Definition audit_live_all_points_three_statement : Prop :=
  forall B BE S O N E V C (EN : encoding N) (EE : encoding E) (EV : encoding V)
      (s : ssa_points B BE N E V) (vv : var_view S O N E V C),
    point_model s = var_point_uses vv ->
    ready EN (live_graph (point_model s)) (prepare EN (live_graph (point_model s))) ->
    forall n x, In n (Graph.nodes (live_graph (point_model s))) ->
      audit_live_select EN EE EV AuditLiveGeneral s vv n x =
      audit_live_select EN EE EV AuditLiveOneShot s vv n x /\
      audit_live_select EN EE EV AuditLiveOneShot s vv n x =
      audit_live_select EN EE EV AuditLiveSparse s vv n x /\
      (audit_live_select EN EE EV AuditLiveOneShot s vv n x = true <->
        syntactic_live (point_model s) x n).

(** Enumerating the constructed expression set gives a duplicate-free universe. *)
Definition audit_universe_nodup {S O N E U C} (EU : encoding U)
    (gk : genkill_view S O N E U C) : NoDup (expr_universe EU gk) :=
  FinSet.elements_nodup EU _ (FinSet.wf_fold_add EU _ _ (Map.wf_empty EU)).

Definition audit_dense_available {S O N E U C} (EN : encoding N) (EE : encoding E)
    (EU : encoding U) (gk : genkill_view S O N E U C) : N -> avail_set EU gk :=
  let sys := available_system EU gk in
  let ss := forward_static _ _ _ in
  proj1_sig (solve_total EN (dense_constraint_encoding EN EE)
    (avail_lattice EU gk) (finite_must_laws _ _)
    (rpo_scheduler EN sys ss) Joining sys ss
    (inhabits (base_height (finite_must_height _ _ (audit_universe_nodup EU gk))))).

Definition audit_dense_busy {S O N E U C} (EN : encoding N) (EE : encoding E)
    (EU : encoding U) (gk : genkill_view S O N E U C) : N -> avail_set EU gk :=
  let sys := busy_system EU gk in
  let ss := backward_static _ _ _ in
  proj1_sig (solve_total EN (dense_constraint_encoding EN EE)
    (avail_lattice EU gk) (finite_must_laws _ _)
    (rpo_scheduler EN sys ss) Joining sys ss
    (inhabits (base_height (finite_must_height _ _ (audit_universe_nodup EU gk))))).

(** The actual joining choices meet their respective least dense constraint systems. *)
Definition audit_dense_least_statement : Prop :=
  forall S O N E U C (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (gk : genkill_view S O N E U C),
    least_solution (avail_lattice EU gk) (available_system EU gk)
      (audit_dense_available EN EE EU gk) /\
      least_solution (avail_lattice EU gk) (busy_system EU gk) (audit_dense_busy EN EE EU gk).

(** Under readiness, sparse and dense available and busy facts agree at each listed point. *)
Definition audit_dense_seg_agrees_statement : Prop :=
  forall S O N E U C (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (gk : genkill_view S O N E U C),
    ready EN (cfg (gkview gk)) (prepare EN (cfg (gkview gk))) ->
    forall n u, In n (Graph.nodes (cfg (gkview gk))) ->
      seg_available EN EE EU gk u n = fmem EU u (audit_dense_available EN EE EU gk n) /\
      seg_busy EN EE EU gk u n = fmem EU u (audit_dense_busy EN EE EU gk n).

Inductive audit_seg_direction : Type :=
  | AuditAvailable
  | AuditBusy.

Inductive audit_seg_choice : Type :=
  | AuditSparse
  | AuditDense.

(** One dense solve can answer a batch spanning different expressions. *)
Definition audit_seg_dense_query {S O N E U C} (EN : encoding N) (EE : encoding E)
    (EU : encoding U) (gk : genkill_view S O N E U C) (direction : audit_seg_direction)
    : N -> U -> bool :=
  let sigma := match direction with
  | AuditAvailable => audit_dense_available EN EE EU gk
  | AuditBusy => audit_dense_busy EN EE EU gk
  end in
  fun n u => fmem EU u (sigma n).

Definition audit_seg_select {S O N E U C} (EN : encoding N) (EE : encoding E)
    (EU : encoding U) (gk : genkill_view S O N E U C) (direction : audit_seg_direction)
    (choice : audit_seg_choice) (u : U) : N -> bool :=
  match direction, choice with
  | AuditAvailable, AuditSparse => seg_available EN EE EU gk u
  | AuditBusy, AuditSparse => seg_busy EN EE EU gk u
  | AuditAvailable, AuditDense =>
    let query := audit_seg_dense_query EN EE EU gk AuditAvailable in fun n => query n u
  | AuditBusy, AuditDense =>
    let query := audit_seg_dense_query EN EE EU gk AuditBusy in fun n => query n u
  end.

(** Under readiness, dense and sparse choices agree at each original listed point. *)
Definition audit_seg_choice_agrees_statement : Prop :=
  forall S O N E U C (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (gk : genkill_view S O N E U C) direction n u,
    ready EN (cfg (gkview gk)) (prepare EN (cfg (gkview gk))) ->
    In n (Graph.nodes (cfg (gkview gk))) ->
    audit_seg_select EN EE EU gk direction AuditSparse u n =
      audit_seg_select EN EE EU gk direction AuditDense u n.

(** The portfolio combines reachable SSA agreement with three-choice agreement at listed nodes. *)
Definition liveness_portfolio_agrees : Prop :=
  (forall B BE S O N E V C (EN : encoding N) (EE : encoding E) (EV : encoding V)
      (s : ssa_points B BE N E V) (vv : var_view S O N E V C),
    point_model s = var_point_uses vv -> ssa_point_laws s -> reachable_point_ssa s ->
    ready EN (live_graph (point_model s)) (prepare EN (live_graph (point_model s))) ->
    forall n x, reachable (live_graph (point_model s)) n -> forall choice,
      audit_live_select EN EE EV choice s vv n x = true <-> syntactic_live (point_model s) x n) /\
  (forall B BE S O N E V C (EN : encoding N) (EE : encoding E) (EV : encoding V)
      (s : ssa_points B BE N E V) (vv : var_view S O N E V C),
    point_model s = var_point_uses vv ->
    ready EN (live_graph (point_model s)) (prepare EN (live_graph (point_model s))) ->
    forall n x, In n (Graph.nodes (live_graph (point_model s))) ->
      audit_live_select EN EE EV AuditLiveGeneral s vv n x =
        audit_live_select EN EE EV AuditLiveOneShot s vv n x /\
      audit_live_select EN EE EV AuditLiveOneShot s vv n x =
        audit_live_select EN EE EV AuditLiveSparse s vv n x /\
      (audit_live_select EN EE EV AuditLiveOneShot s vv n x = true <->
        syntactic_live (point_model s) x n)).

(** Under readiness, either choice returns the selected least solution's fact at each listed
    node. *)
Definition seg_portfolio_agrees : Prop :=
  forall S O N E U C (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (gk : genkill_view S O N E U C) direction (sigma : N -> avail_set EU gk) n u,
    ready EN (cfg (gkview gk)) (prepare EN (cfg (gkview gk))) ->
    (match direction with
    | AuditAvailable => least_solution (avail_lattice EU gk) (available_system EU gk) sigma
    | AuditBusy => least_solution (avail_lattice EU gk) (busy_system EU gk) sigma
    end) ->
    In n (Graph.nodes (cfg (gkview gk))) -> forall choice,
      audit_seg_select EN EE EU gk direction choice u n = fmem EU u (sigma n).
