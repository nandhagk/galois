(** * Dominator certificate signatures

    An independent checker validates immediate-parent maps before tree interval queries.
    For example, the root has no strict parent and a reachable nonroot has its immediate parent.
    Builds on: graph semantics, canonical tries and preparation measures. *)

From Stdlib Require Import PArith NArith List Bool Sorting.Sorted.
From Argent Require Import Time BigO.
From Galois.Base Require Import Trie.
From Galois.Graph Require Import Data Spec DigraphSig.
Import List.ListNotations.

(** Strict dominance excludes equality of the queried vertices. *)
Definition strictly_dominates (g : digraph) (r u v : positive) : Prop :=
  dominates g r u v /\ u <> v.

(** Every strict dominator of a child dominates its immediate parent. *)
Definition immediately_dominates (g : digraph) (r u v : positive) : Prop :=
  strictly_dominates g r u v /\
  forall x, strictly_dominates g r x v -> dominates g r x u.

(** Exactness concerns the candidate map, independently of any producer or numbering. *)
Definition dom_exact (g : prepared) (r : positive) (m : ptrie positive) : Prop :=
  (forall v u, trie_get v m = Some u ->
    reach (base g) [r] u /\ reach (base g) [r] v /\
    immediately_dominates (base g) r u v) /\
  (forall v, reach (base g) [r] v ->
    (trie_get v m = None <-> ~ exists u, strictly_dominates (base g) r u v)) /\
  well_founded (fun u v => trie_get v m = Some u).

(** A child row is empty when its binding is absent. *)
Definition children (t : domtree) (u : positive) : list positive :=
  match t with
  | DomTree _ rows _ _ =>
    match trie_get u rows with
    | Some vs => vs
    | None => []
    end
  end.
TimeFun children.

(** Tree preorder compares present binary discovery numbers. *)
Definition preorder_before (t : domtree) (u v : positive) : Prop :=
  exists a b, trie_get u (pre t) = Some a /\ trie_get v (pre t) = Some b /\ (a < b)%N.

(** Exact trees expose the intended boundary for consumers of raw tree records. *)
Definition domtree_exact (g : prepared) (r : positive) (t : domtree) : Prop :=
  dom_exact g r (idom t) /\
  (forall u v, In v (children t u) <-> trie_get v (idom t) = Some u) /\
  (forall u, NoDup (children t u) /\ StronglySorted (preorder_before t) (children t u)) /\
  (forall v, (exists a, trie_get v (pre t) = Some a) <-> reach (base g) [r] v) /\
  (forall v, (exists a, trie_get v (post t) = Some a) <-> reach (base g) [r] v) /\
  forall u v, reach (base g) [r] v ->
    (dominates (base g) r u v <->
      exists a b c d, trie_get u (pre t) = Some a /\ trie_get u (post t) = Some b /\
        trie_get v (pre t) = Some c /\ trie_get v (post t) = Some d /\
        (a <= c)%N /\ (d <= b)%N).

Module Type DOM_OPS.
  Parameter build : prepared -> positive -> ptrie positive.
  Parameter check : prepared -> positive -> ptrie positive -> bool.
  Parameter tree : prepared -> positive -> ptrie positive -> domtree.
  Parameter dominates_b : domtree -> positive -> positive -> bool.
End DOM_OPS.

Module Type DOM_SPEC (Import D : DOM_OPS).
  Definition exact := dom_exact.
  (** Query width includes the queried keys and the actual supplied interval values. *)
  Definition query_width (t : domtree) (u v : positive) : nat :=
    let width := fun value => match value with Some n => N.size_nat n | None => 0 end in
    graph_max (Pos.size_nat u) (graph_max (Pos.size_nat v)
      (graph_max (width (trie_get u (pre t)))
        (graph_max (width (trie_get u (post t)))
          (graph_max (width (trie_get v (pre t))) (width (trie_get v (post t))))))).
End DOM_SPEC.

Module Type DOM_LAWS (Import D : DOM_OPS).
  (** Acceptance establishes semantic exactness without a trusted producer or cache premise. *)
  Parameter check_sound : forall g r m, check g r m = true -> dom_exact g r m.
  (** Numbering retains the accepted parent map. *)
  Parameter tree_idom : forall g r m, check g r m = true -> idom (tree g r m) = m.
  (** An accepted map gives an exact numbered tree over the semantic reachable domain. *)
  Parameter tree_exact : forall g r m, check g r m = true -> domtree_exact g r (tree g r m).
  (** Interval queries reflect dominance for every reachable target. *)
  Parameter dominates_b_spec : forall g r m u v,
    check g r m = true -> reach (base g) [r] v ->
    reflect (dominates (base g) r u v) (dominates_b (tree g r m) u v).
  (** Child rows invert the supplied accepted map and follow increasing tree preorder. *)
  Parameter kids_spec : forall g r m, check g r m = true -> forall u,
    (forall v, In v (children (tree g r m) u) <-> trie_get v m = Some u) /\
    NoDup (children (tree g r m) u) /\
    StronglySorted (preorder_before (tree g r m)) (children (tree g r m) u).
End DOM_LAWS.

Module Type DOM := DOM_OPS <+ DOM_SPEC <+ DOM_LAWS.

Module Type DOM_TIME (Import D : DOM).
  Parameter T_build : prepared -> positive -> N.
  Parameter T_check : prepared -> positive -> ptrie positive -> N.
  Parameter T_tree : prepared -> positive -> ptrie positive -> N.
  Parameter T_dominates_b : domtree -> positive -> positive -> N.
  Parameter c_dom : N.
  (** Checking keeps the published linear bound for arbitrary candidates, including rejection. *)
  Parameter T_check_le : forall g r m,
    (T_check g r m <= c_dom * N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
  (** Tree construction keeps the published linear graph bound. *)
  Parameter T_tree_le : forall g r m,
    (T_tree g r m <= c_dom * N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
  (** Interval queries charge their queried key and interval widths. *)
  Parameter T_dominates_b_le : forall t u v,
    (T_dominates_b t u v <= c_dom * N.of_nat (query_width t u v + 1))%N.
  (** Simple Lengauer--Tarjan has the aggregate logarithmic producer target. *)
  Parameter T_build_le : forall g r,
    (T_build g r <= c_dom * N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
      N.of_nat (Nat.log2 (graph_n (base g)) + 1) * N.of_nat (graph_width (base g) + 1))%N.
  (** Checking has the published linear bit-cost bound. *)
  Parameter check_bigO : bigO (fun _ : prepared * positive * ptrie positive => True)
    (fun '(g, _, _) => N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (graph_width (base g) + 1))) (fun '(g, r, m) => T_check g r m).
  (** Numbering has the published linear bit-cost bound. *)
  Parameter tree_bigO : bigO (fun _ : prepared * positive * ptrie positive => True)
    (fun '(g, _, _) => N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (graph_width (base g) + 1))) (fun '(g, r, m) => T_tree g r m).
  (** Query costs depend on the supplied interval and key widths. *)
  Parameter dominates_b_bigO : bigO (fun _ : domtree * positive * positive => True)
    (fun '(t, u, v) => N.of_nat (query_width t u v + 1))
    (fun '(t, u, v) => T_dominates_b t u v).
  (** Building keeps the graph-size times logarithmic bit-cost target. *)
  Parameter build_bigO : bigO (fun _ : prepared * positive => True)
    (fun '(g, _) => N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (Nat.log2 (graph_n (base g)) + 1) * (graph_width (base g) + 1)))
    (fun '(g, r) => T_build g r).
End DOM_TIME.

Module Type DOM_T := DOM <+ DOM_TIME.
