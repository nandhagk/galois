(** * Dominance frontier signatures

    Frontiers identify dominated predecessors across a strict-dominance boundary.
    For example, either arm of a diamond has the join in its frontier.
    Builds on: graph semantics, dominator predicates and preparation measures. *)

From Stdlib Require Import PArith NArith List.
From Argent Require Import Time Std BigO.
From Galois.Base Require Import Trie.
From Galois.Graph Require Import Data Spec DigraphSig DomSig.
Import List.ListNotations.

Definition frontier_row (rows : ptrie (list positive)) (u : positive) : list positive :=
  match trie_get u rows with
  | Some vs => vs
  | None => []
  end.
TimeFun frontier_row.

(** Frontier membership is the requested dominated-predecessor boundary. *)
Definition in_frontier (g : digraph) (r x y : positive) : Prop :=
  (exists p, reach g [r] p /\ edge g p y /\ dominates g r x p) /\
  ~ strictly_dominates g r x y.

(** Iteration work counts the entries in rows visited from seeds and discovered targets. *)
Definition idf_work
    (idf : ptrie (list positive) -> list positive -> list positive)
    (rows : ptrie (list positive)) (seeds : list positive) : nat :=
  fold_right (fun x n => length (frontier_row rows x) + n) 0 (seeds ++ idf rows seeds).
TimeFun idf_work.

(** Iterated frontiers form the least nonreflexive closure reached from the seeds. *)
Inductive in_iterated_frontier (g : digraph) (r : positive) (seeds : list positive) :
    positive -> Prop :=
  | frontier_seed : forall x y,
      In x seeds -> in_frontier g r x y -> in_iterated_frontier g r seeds y
  | frontier_step : forall x y,
      in_iterated_frontier g r seeds x -> in_frontier g r x y ->
      in_iterated_frontier g r seeds y.

(** Row closure starts with a row edge from a seed and keeps following row edges. *)
Inductive in_row_closure (rows : ptrie (list positive)) (seeds : list positive) :
    positive -> Prop :=
  | row_seed : forall x y,
      In x seeds -> In y (frontier_row rows x) -> in_row_closure rows seeds y
  | row_step : forall x y,
      in_row_closure rows seeds x -> In y (frontier_row rows x) ->
      in_row_closure rows seeds y.

(** A target task records a discovered row edge even when its vertex was a seed. *)
Inductive idf_task :=
  | IdfSeed (v : positive)
  | IdfTarget (v : positive).

Record idf_state := IdfState {
  idf_pending : list idf_task;
  idf_expanded : ptrie unit;
  idf_discovered : ptrie unit;
  idf_answer : list positive
}.
TimeFun idf_pending.
TimeFun idf_expanded.
TimeFun idf_discovered.
TimeFun idf_answer.

(** Entry counts retain every row occurrence, including repeated targets. *)
Definition frontier_entries (rows : ptrie (list positive)) (vs : list positive) : nat :=
  fold_right (fun v n => length (frontier_row rows v) + n) 0 vs.
TimeFun frontier_entries.

Module Type FRONTIER_OPS.
  Parameter df : prepared -> domtree -> ptrie (list positive).
  Parameter idf : ptrie (list positive) -> list positive -> list positive.
End FRONTIER_OPS.

Module Type FRONTIER_SPEC (Import F : FRONTIER_OPS).
  Definition df_size (g : prepared) (t : domtree) : nat :=
    fold_right (fun x n => length (frontier_row (df g t) x) + n) 0 (nodes g).
End FRONTIER_SPEC.

Module Type FRONTIER_LAWS (Import F : FRONTIER_OPS).
  (** Frontier rows meet the requested semantic boundary for the root argument. *)
  Parameter df_spec : forall g t r x y,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    In y (frontier_row (df g t) x) <-> in_frontier (base g) r x y.
  (** Frontier rows contain no repeated targets. *)
  Parameter df_unique : forall g t x, NoDup (frontier_row (df g t) x).
  (** Iteration returns precisely the least frontier closure seeded by definitions. *)
  Parameter idf_spec : forall g t r seeds y,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    In y (idf (df g t) seeds) <-> in_iterated_frontier (base g) r seeds y.
  (** Iterated frontiers contain each discovered target once. *)
  Parameter idf_unique : forall rows seeds, NoDup (idf rows seeds).
End FRONTIER_LAWS.

Module Type FRONTIER := FRONTIER_OPS <+ FRONTIER_SPEC <+ FRONTIER_LAWS.

Module Type FRONTIER_TIME (Import F : FRONTIER).
  Parameter T_df : prepared -> domtree -> N.
  Parameter T_idf : ptrie (list positive) -> list positive -> N.
  Parameter c_frontier : N.
  (** Frontier construction charges graph occurrences and emitted frontier members. *)
  Parameter T_df_le : forall g t r,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    (T_df g t <= c_frontier * N.of_nat (graph_n (base g) + graph_e (base g) + df_size g t + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
  (** Iteration charges the frontier rows visited from seeds and newly found targets. *)
  Parameter T_idf_le : forall rows seeds,
    (T_idf rows seeds <= c_frontier * N.of_nat (length seeds + idf_work idf rows seeds + 1) *
      N.of_nat (vertex_width
        (seeds ++ flat_map (frontier_row rows) (seeds ++ idf rows seeds)) + 1))%N.
  (** Frontier construction has the published output-sensitive bound. *)
  Parameter df_bigO : bigO (fun '(g, t, r) =>
      wf_graph (base g) /\ prepared_ok g /\ domtree_exact g r t)
    (fun '(g, t, _) => N.of_nat ((graph_n (base g) + graph_e (base g) + df_size g t + 1) *
      (graph_width (base g) + 1))) (fun '(g, t, _) => T_df g t).
  (** Iteration has the published visited-frontier bound. *)
  Parameter idf_bigO : bigO (fun _ : ptrie (list positive) * list positive => True)
    (fun '(rows, seeds) => N.of_nat ((length seeds + idf_work idf rows seeds + 1) *
      (vertex_width (seeds ++ flat_map (frontier_row rows) (seeds ++ idf rows seeds)) + 1)))
    (fun '(rows, seeds) => T_idf rows seeds).
End FRONTIER_TIME.

Module Type FRONTIER_T := FRONTIER <+ FRONTIER_TIME.

(** * Frontier proof plan *)

Module Type FRONTIER_PLAN (Import F : FRONTIER_T).
  Parameter idf_step : ptrie (list positive) -> idf_state -> idf_state + list positive.
  Parameter T_idf_step : ptrie (list positive) -> idf_state -> N.
  Parameter idf_walk : ptrie (list positive) -> list positive -> list positive.
  Parameter T_idf_walk : ptrie (list positive) -> list positive -> N.
  Parameter k_idf_step k_idf_stop k_idf_walk : N.

  Definition idf_initial (seeds : list positive) : idf_state :=
    IdfState (map IdfSeed seeds) Empty Empty [].

  Definition idf_advance rows st :=
    match idf_step rows st with
    | inl next => next
    | inr _ => st
    end.

  (** The worklist starts with seed tasks and records target tasks separately. *)
  Definition idf_reachable rows seeds st : Prop :=
    exists n, Nat.iter n (idf_advance rows) (idf_initial seeds) = st.

  Definition idf_task_supported rows seeds task : Prop :=
    match task with
    | IdfSeed v => In v seeds
    | IdfTarget v => in_row_closure rows seeds v
    end.

  (** Expansion and discovery are separate so a returning seed enters the answer. *)
  Definition idf_invariant rows seeds st : Prop :=
    idf_reachable rows seeds st /\ NoDup (idf_answer st) /\
    (forall v, trie_get v (idf_discovered st) = Some tt <-> In v (idf_answer st)) /\
    (forall v, In v (idf_answer st) -> in_row_closure rows seeds v) /\
    (forall v, trie_get v (idf_expanded st) = Some tt ->
      In v seeds \/ in_row_closure rows seeds v) /\
    Forall (idf_task_supported rows seeds) (idf_pending st).

  (** This support is a ghost list and is never scanned to choose executable fuel. *)
  Definition idf_support rows seeds : list positive :=
    nodup Pos.eq_dec (seeds ++ idf rows seeds).

  Definition idf_white rows seeds st : nat :=
    fold_right (fun v n =>
      match trie_get v (idf_expanded st) with
      | None => 2 + length (frontier_row rows v) + n
      | Some _ => n
      end) 0 (idf_support rows seeds).

  (** Expanding a row transfers its occurrences from white credit to pending tasks. *)
  Definition idf_potential rows seeds st : N :=
    N.of_nat (2 * idf_white rows seeds st + length (idf_pending st)).

  Definition idf_width rows seeds : nat :=
    vertex_width (seeds ++ flat_map (frontier_row rows) (seeds ++ idf rows seeds)).

  Definition idf_credit rows seeds st : N :=
    ((k_idf_step * N.of_nat (idf_width rows seeds + 1) + 1) *
      idf_potential rows seeds st)%N.

  (** Finite row bindings give a ghost universe without an executable whole-map scan. *)
  Parameter F1_idf_finite : forall rows seeds,
    exists universe, NoDup universe /\ incl seeds universe /\
      forall x y, In y (frontier_row rows x) -> In y universe.

  (** The lazy closure driver terminates from every finite row map and seed list. *)
  Parameter F2_idf_done : forall rows seeds,
    exists n st result,
      Nat.iter n (idf_advance rows) (idf_initial seeds) = st /\
      idf_step rows st = inr result /\ result = idf_walk rows seeds.

  (** The driver computes the least nonreflexive closure of the supplied rows. *)
  Parameter F3_idf_closure : forall rows seeds y,
    In y (idf_walk rows seeds) <-> in_row_closure rows seeds y.

  (** The public operation is the lazy row driver with no frontier reconstruction. *)
  Parameter F4_idf_equation : forall rows seeds, idf rows seeds = idf_walk rows seeds.

  (** Semantic frontier rows transport row closure to iterated graph frontiers. *)
  Parameter F5_idf_transport : forall g t r seeds y,
    wf_graph (base g) -> prepared_ok g -> domtree_exact g r t ->
    (in_row_closure (df g t) seeds y <-> in_iterated_frontier (base g) r seeds y).

  (** Initialization starts with empty expansion and discovery tables. *)
  Parameter F6_idf_initial : forall rows seeds,
    idf_invariant rows seeds (idf_initial seeds).

  (** Continuing transitions keep supported tasks and spend pending or white work. *)
  Parameter F7_idf_step : forall rows seeds st next,
    idf_invariant rows seeds st -> idf_step rows st = inl next ->
    idf_invariant rows seeds next /\
      (idf_potential rows seeds next < idf_potential rows seeds st)%N.

  (** Stopping reverses the accumulated answer after all pending tasks are consumed. *)
  Parameter F8_idf_stop : forall rows seeds st result,
    idf_invariant rows seeds st -> idf_step rows st = inr result ->
    idf_pending st = [] /\ result = rev (idf_answer st) /\ result = idf rows seeds.

  (** Every output target has an occurrence in a visited frontier row. *)
  Parameter F9_idf_output : forall rows seeds,
    length (idf rows seeds) <= idf_work idf rows seeds.

  (** Initial credit counts supplied seeds and the rows of discovered vertices. *)
  Parameter F10_idf_credit : forall rows seeds,
    (idf_potential rows seeds (idf_initial seeds) <=
      7 * N.of_nat (length seeds + idf_work idf rows seeds + 1))%N.

  (** Continuing steps pay row lookup, occurrence tasks and both membership tables. *)
  Parameter T1_idf_step : forall rows seeds st next,
    idf_invariant rows seeds st -> idf_step rows st = inl next ->
    (T_idf_step rows st + idf_credit rows seeds next < idf_credit rows seeds st)%N.

  (** The stopping callback pays one reversal of the unique discovered targets. *)
  Parameter T2_idf_stop : forall rows seeds st result,
    idf_invariant rows seeds st -> idf_step rows st = inr result ->
    (T_idf_step rows st <= k_idf_stop * N.of_nat (length (idf rows seeds) + 1))%N.

  (** Accessibility recursion charges its decreasing credit and final reversal. *)
  Parameter T3_idf_walk : forall rows seeds,
    (T_idf_walk rows seeds <= k_idf_walk *
      (idf_credit rows seeds (idf_initial seeds) +
        k_idf_stop * N.of_nat (length (idf rows seeds) + 1) +
        N.of_nat (length seeds) + 1))%N.

  (** The public wrapper forwards the supplied row map and seeds once. *)
  Parameter T4_idf_wrapper : forall rows seeds,
    (T_idf rows seeds <= k_idf_walk * (T_idf_walk rows seeds + 1))%N.

  (** Combining worklist credit and output size gives the published row bound. *)
  Parameter T5_idf_public : forall rows seeds,
    (T_idf rows seeds <= c_frontier * N.of_nat (length seeds + idf_work idf rows seeds + 1) *
      N.of_nat (idf_width rows seeds + 1))%N.
End FRONTIER_PLAN.

Module Type FRONTIER_ALL := FRONTIER_T <+ FRONTIER_PLAN.
