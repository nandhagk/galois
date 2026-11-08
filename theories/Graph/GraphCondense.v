(** * Charged component condensation

    Condensation groups cross-component arcs and removes duplicate targets in each bucket.
    For example, parallel labels between two components produce one successor.
    Builds on: GraphSccSpec, GraphPrepared and BaseIndex. *)

From Stdlib Require Import List Bool PArith NArith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseIndex.
From Galois.Graph Require Import GraphPrepared GraphVisitor GraphSearchSpec GraphSccSpec.
Import List.ListNotations Cost.Notations.

Module Condense.

Local Lemma present_ext {A B} (f g : A -> option B) xs :
  (forall x, f x = g x) -> Prepared.present f xs = Prepared.present g xs.
Proof.
  intro Hfg. induction xs as [|x rest IH]; [reflexivity|].
  cbn [Prepared.present]. rewrite Hfg, IH. reflexivity.
Qed.

(** Mapping an inspected occurrence retains it exactly when both owners exist and differ. *)
Definition target_c {E} (r : Scc.result) i (ev : E * positive) :=
  let* owner := Map.get_c positive_encoding (snd ev) (Scc.comp_of r) in
  match owner with
  | None => Cost.ret None
  | Some j => Cost.ret (if Pos.eqb i j then None else Some (i, j))
  end.

Definition target {E} r i (ev : E * positive) := Cost.value (target_c r i ev).

(** Target filtering distinguishes missing ownership from a self edge. *)
Theorem target_equation {E} r i (ev : E * positive) :
  target r i ev =
    match Map.get positive_encoding (snd ev) (Scc.comp_of r) with
    | None => None
    | Some j => if Pos.eqb i j then None else Some (i, j)
    end.
Proof.
  unfold target, target_c. autorewrite with galois_cost.
  fold (Map.get positive_encoding (snd ev) (Scc.comp_of r)).
  destruct (Map.get positive_encoding (snd ev) (Scc.comp_of r)); reflexivity.
Qed.

(** Each owned vertex reads its prepared adjacency once and charges every inspected occurrence. *)
Definition vertex_c {V E} (p : Prepared.t V E) (r : Scc.result) u :=
  let* owner := Map.get_c positive_encoding u (Scc.comp_of r) in
  match owner with
  | None => Cost.ret []
  | Some i =>
    let* es := Prepared.succ_edges_c p u in
    Prepared.present_c (target_c r i) es
  end.

Definition vertex {V E} (p : Prepared.t V E) r u := Cost.value (vertex_c p r u).

(** The vertex equation preserves outgoing occurrence order while excluding missing owners. *)
Theorem vertex_equation {V E} (p : Prepared.t V E) r u :
  vertex p r u =
    match Map.get positive_encoding u (Scc.comp_of r) with
    | None => []
    | Some i =>
      Prepared.present (fun ev =>
        match Map.get positive_encoding (snd ev) (Scc.comp_of r) with
        | None => None
        | Some j => if Pos.eqb i j then None else Some (i, j)
        end) (Prepared.succ_edges p u)
    end.
Proof.
  unfold vertex, vertex_c. autorewrite with galois_cost.
  fold (Map.get positive_encoding u (Scc.comp_of r)).
  destruct (Map.get positive_encoding u (Scc.comp_of r)); [|reflexivity].
  autorewrite with galois_cost. rewrite Prepared.present_c_value.
  apply present_ext. intro ev. apply target_equation.
Qed.

Definition vertices_c {V E} (p : Prepared.t V E) r vs :=
  fold_right_c (fun u tail =>
    let* es := vertex_c p r u in app_c es tail) [] vs.

Definition vertices {V E} (p : Prepared.t V E) r vs := Cost.value (vertices_c p r vs).

(** Vertex concatenation visits only supplied component members. *)
Theorem vertices_equation {V E} (p : Prepared.t V E) r vs :
  vertices p r vs = flat_map (vertex p r) vs.
Proof.
  unfold vertices, vertices_c. rewrite value_fold_right_c.
  induction vs as [|u rest IH]; [reflexivity|].
  cbn [fold_right flat_map]. autorewrite with galois_cost. now rewrite IH.
Qed.

Definition cross_edges_c {V E} (p : Prepared.t V E) r :=
  fold_right_c (fun vs tail =>
    let* es := vertices_c p r vs in app_c es tail) [] (Scc.components r).

Definition cross_edges {V E} (p : Prepared.t V E) r := Cost.value (cross_edges_c p r).

(** Cross-edge collection scans components directly and performs no global preparation pass. *)
Theorem cross_edges_equation {V E} (p : Prepared.t V E) r :
  cross_edges p r = flat_map (vertex p r) (concat (Scc.components r)).
Proof.
  unfold cross_edges, cross_edges_c. rewrite value_fold_right_c.
  induction (Scc.components r) as [|vs rest IH]; [reflexivity|].
  cbn [fold_right concat]. autorewrite with galois_cost.
  fold (vertices p r vs).
  rewrite vertices_equation, IH, flat_map_app. reflexivity.
Qed.

(** A set records every retained target, preserving the first occurrence in each bucket. *)
Fixpoint unique_c (xs : list (positive * positive)) (seen : FinSet.t positive)
    : Cost.t (list positive) :=
  match xs with
  | [] => Cost.ret []
  | (_, j) :: rest =>
    Cost.step ;;
    let* present := FinSet.mem_c positive_encoding j seen in
    if present then unique_c rest seen else
    let* seen' := FinSet.add_c positive_encoding j seen in
    let* ys := unique_c rest seen' in Cost.ret (j :: ys)
  end.

Definition unique xs seen := Cost.value (unique_c xs seen).

(** Deduplication performs exactly the charged membership and insertion decisions. *)
Theorem unique_equation xs seen :
  unique xs seen =
    match xs with
    | [] => []
    | (_, j) :: rest =>
      if FinSet.mem positive_encoding j seen then unique rest seen else
      j :: unique rest (FinSet.add positive_encoding j seen)
    end.
Proof.
  destruct xs as [|[i j] rest]; [reflexivity|].
  unfold unique at 1. cbn [unique_c]. autorewrite with galois_cost.
  fold (FinSet.mem positive_encoding j seen).
  destruct (FinSet.mem positive_encoding j seen); reflexivity.
Qed.

(** Condensation retains every owned arc regardless of the redundant producer scope argument. *)
Definition of_scc_c {V E} (p : Prepared.t V E) (_scope : Scope.t) r :=
  let* es := cross_edges_c p r in
  let* buckets := Index.group_by_c positive_encoding
    (fun ev => Cost.ret (fst ev)) es in
  let* successors := Map.map_c (fun xs => unique_c xs FinSet.empty) buckets in
  let* count := length_c (Scc.components r) in
  Cost.ret (Condensation.Make count successors).

Definition of_scc {V E} (p : Prepared.t V E) scope r := Cost.value (of_scc_c p scope r).

(** Condensation has stable grouped buckets and a natural component count, including zero. *)
Theorem of_scc_equation {V E} (p : Prepared.t V E) scope r :
  of_scc p scope r =
    Condensation.Make (length (Scc.components r))
      (Map.map (fun xs => unique xs FinSet.empty)
        (Index.group_by positive_encoding fst (cross_edges p r))).
Proof.
  unfold of_scc, of_scc_c. autorewrite with galois_cost.
  rewrite Index.group_by_c_value, Map.map_c_value. reflexivity.
Qed.

End Condense.
