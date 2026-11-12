(** * Graph preparation signatures

    Preparation caches predecessor occurrences and graph sizes.
    For example, two parallel successor occurrences give two predecessor occurrences.
    Builds on: graph data, graph semantics and Argent time interfaces. *)

From Stdlib Require Import PArith NArith List Arith Sorting.Permutation.
From Argent Require Import Time Std BigO.
From Galois.Graph Require Import Data Spec.
Import List.ListNotations.
Fixpoint graph_max (a b : nat) : nat :=
  match a, b with
  | 0, _ => b
  | _, 0 => a
  | S a1, S b1 => S (graph_max a1 b1)
  end.
TimeFun graph_max.

Definition graph_n (g : digraph) : nat :=
  match g with Digraph vs _ => length vs end.
TimeFun graph_n.

Definition graph_e (g : digraph) : nat :=
  match g with
  | Digraph vs _ => fold_right (fun v n => length (succs g v) + n) 0 vs
  end.
TimeFun graph_e.

Definition vertex_width (vs : list positive) : nat :=
  fold_right (fun v w => graph_max (Pos.size_nat v) w) 0 vs.
TimeFun vertex_width.

Definition graph_width (g : digraph) : nat :=
  match g with
  | Digraph vs _ => graph_max (vertex_width vs)
      (fold_right (fun v w => graph_max (vertex_width (succs g v)) w) 0 vs)
  end.
TimeFun graph_width.

(** Cached sizes and predecessor multiplicities agree with the source graph. *)
Definition prepared_ok (g : prepared) : Prop :=
  nv g = N.of_nat (graph_n (base g)) /\
  ne g = N.of_nat (graph_e (base g)) /\
  forall v, Permutation (preds g v)
    (flat_map (fun u => map (fun _ => u) (filter (Pos.eqb v) (succs (base g) u)))
      (nodes g)).

Module Type DIGRAPH_OPS.
  Parameter prepare : digraph -> prepared.
End DIGRAPH_OPS.

Module Type DIGRAPH_LAWS (Import D : DIGRAPH_OPS).
  (** Preparation retains the supplied source graph. *)
  Parameter prepare_base : forall g, base (prepare g) = g.
  (** Preparation computes caches even when vertex or edge lists contain duplicates. *)
  Parameter prepare_correct : forall g, prepared_ok (prepare g).
End DIGRAPH_LAWS.

Module Type DIGRAPH := DIGRAPH_OPS <+ DIGRAPH_LAWS.

Module Type DIGRAPH_TIME (Import D : DIGRAPH).
  Parameter T_prepare : digraph -> nat.
  Parameter c_prepare : nat.
  (** Preparation charges source vertices, edge occurrences and their key widths. *)
  Parameter T_prepare_le : forall g,
    T_prepare g <= c_prepare * (graph_n g + graph_e g + 1) * (graph_width g + 1).
  (** Preparation has the published linear bit-cost bound. *)
  Parameter prepare_bigO : bigO (fun _ => True)
    (fun g => (graph_n g + graph_e g + 1) * (graph_width g + 1)) T_prepare.
End DIGRAPH_TIME.

Module Type DIGRAPH_T := DIGRAPH <+ DIGRAPH_TIME.
