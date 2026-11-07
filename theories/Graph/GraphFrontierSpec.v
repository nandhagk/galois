(** * Frontiers and dependence

    Frontier membership records a dominated predecessor across a dominance boundary.
    For example, both arms of a diamond have the join in their dominance frontier.
    Builds on: GraphDomSpec. *)

From Stdlib Require Import List.
From Galois.Graph Require Import GraphModel GraphDomSpec.
Import List.ListNotations.

(** A frontier node has a reachable dominated predecessor and escapes strict dominance. *)
Definition in_df {V E} (g : Graph.t V E) d x :=
  exists e, reachable g (Graph.source g e) /\
    In e (Graph.out g (Graph.source g e)) /\ Graph.target g e = x /\
    dominates g d (Graph.source g e) /\ ~ strictly_dominates g d x.

(** Iterated frontiers are the least nonreflexive frontier closure seeded by definitions. *)
Inductive in_idf {V E} (g : Graph.t V E) (defs : list V) : V -> Prop :=
  | idf_seed : forall d x, In d defs -> in_df g d x -> in_idf g defs x
  | idf_step : forall d x, in_idf g defs d -> in_df g d x -> in_idf g defs x.

(** An edge controls a node when its target forces that node and its source does not strictly do so. *)
Definition control_dependent {V E} (g : Graph.t V E) exits e n :=
  In e (Graph.out g (Graph.source g e)) /\
  post_dominates g exits n (Graph.target g e) /\
  ~ (post_dominates g exits n (Graph.source g e) /\ n <> Graph.source g e).

(** An edge dominator occurs on every entry path to its dominated node. *)
Definition edge_dominates {V E} (g : Graph.t V E) e n :=
  forall s es, In s (Graph.entries g) -> path g s es n -> In e es.
