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
