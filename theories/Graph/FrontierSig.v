(** * Dominance frontier signatures

    Frontiers identify dominated predecessors across a strict-dominance boundary.
    For example, either arm of a diamond has the join in its frontier.
    Builds on: graph semantics, dominator predicates and preparation measures. *)

From Stdlib Require Import PArith List.
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
  (exists p, edge g p y /\ dominates g r x p) /\ ~ strictly_dominates g r x y.

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
  Parameter idf : prepared -> domtree -> list positive -> list positive.
End FRONTIER_OPS.

Module Type FRONTIER_SPEC (Import F : FRONTIER_OPS).
  Definition df_size (g : prepared) (t : domtree) : nat :=
    fold_right (fun x n => length (frontier_row (df g t) x) + n) 0 (nodes g).
  Definition idf_work (g : prepared) (t : domtree) (seeds : list positive) : nat :=
    fold_right (fun x n => length (frontier_row (df g t) x) + n) 0
      (seeds ++ idf g t seeds).
End FRONTIER_SPEC.

Module Type FRONTIER_LAWS (Import F : FRONTIER_OPS).
  (** Frontier rows meet the requested semantic boundary for the root argument. *)
  Parameter df_spec : forall g t r x y,
    In y (frontier_row (df g t) x) <-> in_frontier (base g) r x y.
  (** Frontier rows contain no repeated targets. *)
  Parameter df_unique : forall g t x, NoDup (frontier_row (df g t) x).
  (** Iteration returns precisely the least frontier closure seeded by definitions. *)
  Parameter idf_spec : forall g t r seeds y,
    In y (idf g t seeds) <-> in_iterated_frontier (base g) r seeds y.
  (** Iterated frontiers contain each discovered target once. *)
  Parameter idf_unique : forall g t seeds, NoDup (idf g t seeds).
End FRONTIER_LAWS.

Module Type FRONTIER := FRONTIER_OPS <+ FRONTIER_SPEC <+ FRONTIER_LAWS.

Module Type FRONTIER_TIME (Import F : FRONTIER).
  Parameter T_df : prepared -> domtree -> nat.
  Parameter T_idf : prepared -> domtree -> list positive -> nat.
  Parameter c_frontier : nat.
  (** Frontier construction charges graph occurrences and emitted frontier members. *)
  Parameter T_df_le : forall g t,
    T_df g t <= c_frontier * (graph_n (base g) + graph_e (base g) + df_size g t + 1) *
      (graph_width (base g) + 1).
  (** Iteration charges the frontier rows visited from seeds and newly found targets. *)
  Parameter T_idf_le : forall g t seeds,
    T_idf g t seeds <= c_frontier * (idf_work g t seeds + 1) * (graph_width (base g) + 1).
  (** Frontier construction has the published output-sensitive bound. *)
  Parameter df_bigO : bigO (fun _ : prepared * domtree => True)
    (fun '(g, t) => (graph_n (base g) + graph_e (base g) + df_size g t + 1) *
      (graph_width (base g) + 1)) (fun '(g, t) => T_df g t).
  (** Iteration has the published visited-frontier bound. *)
  Parameter idf_bigO : bigO (fun _ : prepared * domtree * list positive => True)
    (fun '(g, t, seeds) => (idf_work g t seeds + 1) * (graph_width (base g) + 1))
    (fun '(g, t, seeds) => T_idf g t seeds).
End FRONTIER_TIME.

Module Type FRONTIER_T := FRONTIER <+ FRONTIER_TIME.
