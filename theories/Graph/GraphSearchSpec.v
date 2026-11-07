(** * Search result contracts

    Search results describe scoped reachability, parent edges and traversal intervals.
    For example, an edge to an unexited ancestor is classified as a back edge.
    Builds on: GraphPrepared and GraphVisitor. *)

From Stdlib Require Import List Bool PArith Permutation.
From Stdlib.Relations Require Import Relation_Operators.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor.
Import List.ListNotations Cost.Notations.

Module Search.
Include GraphVisitor.Search.

(** A scoped path stays inside admitted, valid IDs, including its starting node. *)
Inductive scoped_path {V E} (p : Prepared.t V E) (scope : Scope.t) :
    positive -> list E -> positive -> Prop :=
  | scoped_nil : forall v, Prepared.valid_id p v -> Scope.admits scope v = true ->
      scoped_path p scope v [] v
  | scoped_cons : forall u e v es z, Prepared.valid_id p u ->
      Scope.admits scope u = true -> Prepared.arc p u e v ->
      scoped_path p scope v es z -> scoped_path p scope u (e :: es) z.

(** Scoped reachability starts at one of the supplied roots. *)
Definition scoped_reachable {V E} (p : Prepared.t V E) scope roots v :=
  exists r es, In r roots /\ scoped_path p scope r es v.

(** A result stores traversal orders, labelled parents, independent ranks and visited IDs. *)
Record result (E : Type) := Result {
  preorder : list positive;
  postorder : list positive;
  parent_edge : Map.t positive (E * positive);
  pre_num : Map.t positive positive;
  post_num : Map.t positive positive;
  visited : FinSet.t positive
}.
Arguments Result {E}.
Arguments preorder {E}.
Arguments postorder {E}.
Arguments parent_edge {E}.
Arguments pre_num {E}.
Arguments post_num {E}.
Arguments visited {E}.

(** Tree ancestry includes a node itself and every recorded parent chain. *)
Definition ancestor {E} (r : result E) :=
  clos_refl_trans positive
    (fun u v => exists e, Map.get positive_encoding v (parent_edge r) = Some (e, u)).

(** Containment uses increasing entry ranks and decreasing exit ranks. *)
Definition interval {E} (r : result E) u v :=
  exists a b c d, Map.get positive_encoding u (pre_num r) = Some a /\
    Map.get positive_encoding v (pre_num r) = Some b /\
    Map.get positive_encoding v (post_num r) = Some c /\
    Map.get positive_encoding u (post_num r) = Some d /\
    (a <= b /\ c <= d)%positive.

(** Exact search results cover precisely the admitted reachable domain and its DFS forest. *)
Record exact {V E} (p : Prepared.t V E) scope roots (r : result E) : Prop := {
  pre_nodup : NoDup (preorder r);
  pre_complete : forall v, In v (preorder r) <-> scoped_reachable p scope roots v;
  visited_complete : forall v, FinSet.mem positive_encoding v (visited r) = true <->
    In v (preorder r);
  result_wf : Map.wf positive_encoding (parent_edge r) /\
    Map.wf positive_encoding (pre_num r) /\ Map.wf positive_encoding (post_num r) /\
    FinSet.wf positive_encoding (visited r);
  post_perm : Permutation (preorder r) (postorder r);
  pre_num_index : forall v i, Map.get positive_encoding v (pre_num r) = Some i <->
    nth_error (preorder r) (Nat.pred (Pos.to_nat i)) = Some v;
  post_num_index : forall v i, Map.get positive_encoding v (post_num r) = Some i <->
    nth_error (postorder r) (Nat.pred (Pos.to_nat i)) = Some v;
  parent_edge_valid : forall v e u,
    Map.get positive_encoding v (parent_edge r) = Some (e, u) ->
    Prepared.arc p u e v /\ In u (preorder r) /\ In v (preorder r);
  parent_roots : forall v, In v (preorder r) ->
    (Map.get positive_encoding v (parent_edge r) = None -> In v roots);
  parent_finite : well_founded
    (fun u v => exists e, Map.get positive_encoding v (parent_edge r) = Some (e, u));
  paren : forall u v, In u (preorder r) -> In v (preorder r) ->
    interval r u v \/ interval r v u \/
    (before (preorder r) u v /\ before (postorder r) u v) \/
    (before (preorder r) v u /\ before (postorder r) v u);
  ancestor_iff : forall u v, In u (preorder r) -> In v (preorder r) ->
    (interval r u v <-> ancestor r u v);
  white_path : forall u v, In u (preorder r) -> In v (preorder r) ->
    (ancestor r u v <->
      exists es, scoped_path p scope u es v /\
        (v = u \/ before (preorder r) u v) /\
        forall a e b, In e es -> Prepared.arc p a e b ->
          a = u \/ before (preorder r) u a)
}.

(** Classification retains each numeric-map lookup and does not inspect edge labels. *)
Definition classify_c {E} (r : result E) u v : Cost.t (option kind) :=
  Cost.step ;;
  let* a := Map.get_c positive_encoding u (pre_num r) in
  let* b := Map.get_c positive_encoding v (pre_num r) in
  let* c := Map.get_c positive_encoding u (post_num r) in
  let* d := Map.get_c positive_encoding v (post_num r) in
  match a, b, c, d with
  | Some a, Some b, Some c, Some d =>
    let* parent := Map.get_c positive_encoding v (parent_edge r) in
    Cost.ret
      (match parent with
      | Some (_, parent) =>
        if Pos.eqb parent u then Some Tree
        else if (Pos.leb b a && Pos.leb c d)%bool then Some Back
        else if Pos.ltb a b then Some Forward else Some Cross
      | None =>
        if (Pos.leb b a && Pos.leb c d)%bool then Some Back
        else if Pos.ltb a b then Some Forward else Some Cross
      end)
  | _, _, _, _ => Cost.ret None
  end.

Definition classify {E} (r : result E) u v := Cost.value (classify_c r u v).

(** Parent endpoint relations take precedence over interval-based edge classes. *)
Theorem classify_equation {E} (r : result E) u v :
  classify r u v =
  match Map.get positive_encoding u (pre_num r),
        Map.get positive_encoding v (pre_num r),
        Map.get positive_encoding u (post_num r),
        Map.get positive_encoding v (post_num r) with
  | Some a, Some b, Some c, Some d =>
    match Map.get positive_encoding v (parent_edge r) with
    | Some (_, parent) =>
      if Pos.eqb parent u then Some Tree
      else if (Pos.leb b a && Pos.leb c d)%bool then Some Back
      else if Pos.ltb a b then Some Forward else Some Cross
    | None =>
      if (Pos.leb b a && Pos.leb c d)%bool then Some Back
      else if Pos.ltb a b then Some Forward else Some Cross
    end
  | _, _, _, _ => None
  end.
Proof.
  unfold classify, classify_c. autorewrite with galois_cost.
  fold (Map.get positive_encoding u (pre_num r)).
  fold (Map.get positive_encoding v (pre_num r)).
  fold (Map.get positive_encoding u (post_num r)).
  fold (Map.get positive_encoding v (post_num r)).
  destruct (Map.get positive_encoding u (pre_num r));
    destruct (Map.get positive_encoding v (pre_num r));
    destruct (Map.get positive_encoding u (post_num r));
    destruct (Map.get positive_encoding v (post_num r));
    autorewrite with galois_cost; reflexivity.
Qed.

(** Numbered endpoints always receive one of the four classes, without a missing-number default. *)
Theorem classify_exhaustive {E} (r : result E) u v a b c d :
  Map.get positive_encoding u (pre_num r) = Some a ->
  Map.get positive_encoding v (pre_num r) = Some b ->
  Map.get positive_encoding u (post_num r) = Some c ->
  Map.get positive_encoding v (post_num r) = Some d ->
  classify r u v = Some Tree \/ classify r u v = Some Back \/
    classify r u v = Some Forward \/ classify r u v = Some Cross.
Proof.
  intros Ha Hb Hc Hd. rewrite classify_equation, Ha, Hb, Hc, Hd.
  destruct (Map.get positive_encoding v (parent_edge r)) as [[e parent]|];
    [destruct (Pos.eqb parent u)|];
    try destruct (Pos.leb b a && Pos.leb c d)%bool;
    try destruct (Pos.ltb a b); auto.
Qed.

Arguments classify {E} r u v : simpl never.
Arguments classify_c {E} r u v : simpl never.

End Search.
