(** * Graph semantics

    Paths record their vertices in traversal order and include both endpoints.
    For example, a singleton path witnesses reachability of any supplied root.
    Builds on: first-order graph data. *)

From Stdlib Require Import PArith List.
From Galois.Graph Require Import Data.
Import List.ListNotations.

(** An edge occurs in the source vertex's successor list. *)
Definition edge (g : digraph) (u v : positive) : Prop := In v (succs g u).

(** A path includes its starting vertex and every subsequent vertex. *)
Inductive path (g : digraph) : positive -> list positive -> positive -> Prop :=
  | path_refl : forall v, path g v [v] v
  | path_step : forall u v vs w,
      edge g u v -> path g v vs w -> path g u (u :: vs) w.

(** Reachability starts at any supplied root, including an unlisted root. *)
Definition reach (g : digraph) (roots : list positive) (v : positive) : Prop :=
  exists r vs, In r roots /\ path g r vs v.

(** A cycle has at least one edge and records its closing vertex. *)
Definition cycle (g : digraph) (vs : list positive) : Prop :=
  exists u v tail, vs = u :: v :: tail /\ edge g u v /\ path g v (v :: tail) u.

(** A vertex dominates a target when it occurs on every root-to-target path. *)
Definition dominates (g : digraph) (r u v : positive) : Prop :=
  forall vs, path g r vs v -> In u vs.

(** Listed vertices are distinct and their successors are listed vertices. *)
Definition wf_graph (g : digraph) : Prop :=
  NoDup (verts g) /\
  forall u v, In u (verts g) -> edge g u v -> In v (verts g).
