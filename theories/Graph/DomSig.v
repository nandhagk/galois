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
  In r (verts (base g)) /\
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

(** The reflexive ancestor relation of a candidate parent map. *)
Inductive tree_anc (m : ptrie positive) (u : positive) : positive -> Prop :=
  | tree_anc_refl : tree_anc m u u
  | tree_anc_step : forall p v, trie_get v m = Some p -> tree_anc m u p -> tree_anc m u v.

(** A strict position comparison in the certificate list. *)
Definition order_before (o : list positive) (u v : positive) : Prop :=
  exists i j, nth_error o i = Some u /\ nth_error o j = Some v /\ i < j.

(** The list is a preorder of the candidate tree rooted at [r]. *)
Definition cert_preorder (r : positive) (m : ptrie positive) (o : list positive) : Prop :=
  NoDup o /\ hd_error o = Some r /\ trie_get r m = None /\
  (forall v, In v o -> v <> r -> exists p, trie_get v m = Some p /\ order_before o p v) /\
  (forall v p, trie_get v m = Some p -> In v o) /\
  (forall u v w, tree_anc m u w -> order_before o u v -> order_before o v w -> tree_anc m u v).

(** Listed vertices are closed under edges, and each edge source lies below the target's parent. *)
Definition cert_parent (g : digraph) (m : ptrie positive) (o : list positive) : Prop :=
  forall u v, In u o -> edge g u v ->
    In v o /\ forall p, trie_get v m = Some p -> tree_anc m p u.

(** Every child has an edge from its parent or a low and a high listed predecessor. *)
Definition cert_low_high (g : digraph) (m : ptrie positive) (o : list positive) : Prop :=
  forall v p, trie_get v m = Some p ->
    edge g p v \/
    exists u w, In u o /\ In w o /\ edge g u v /\ edge g w v /\
      order_before o u v /\ order_before o v w /\ ~ tree_anc m v w.

Definition dom_cert (g : digraph) (r : positive) (m : ptrie positive) (o : list positive)
    : Prop :=
  cert_preorder r m o /\ cert_parent g m o /\ cert_low_high g m o.

Inductive lt_op :=
  | LtLink (child parent : N)
  | LtEval (v : N).

(** The initial scan supplies bounded data to the certificate phases. *)
Record dom_scan_data := DomScanData {
  dom_listed : ptrie bool;
  dom_count : nat;
  dom_edge_count : nat;
  dom_width : nat
}.
TimeFun dom_listed.
TimeFun dom_count.
TimeFun dom_edge_count.
TimeFun dom_width.

Module Type DOM_OPS.
  Parameter build : prepared -> positive -> ptrie positive * list positive.
  Parameter check : prepared -> positive -> ptrie positive -> list positive -> bool.
  Parameter tree : prepared -> positive -> ptrie positive -> list positive -> domtree.
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
  Parameter check_sound : forall g r m o, check g r m o = true -> dom_exact g r m.
  (** Numbering retains the accepted parent map. *)
  Parameter tree_idom : forall g r m o, check g r m o = true -> idom (tree g r m o) = m.
  (** An accepted map gives an exact numbered tree over the semantic reachable domain. *)
  Parameter tree_exact : forall g r m o, check g r m o = true -> domtree_exact g r (tree g r m o).
  (** Interval queries reflect dominance for every reachable target. *)
  Parameter dominates_b_spec : forall g r m o u v,
    check g r m o = true -> reach (base g) [r] v ->
    reflect (dominates (base g) r u v) (dominates_b (tree g r m o) u v).
  (** Child rows invert the supplied accepted map and follow increasing tree preorder. *)
  Parameter kids_spec : forall g r m o, check g r m o = true -> forall u,
    (forall v, In v (children (tree g r m o) u) <-> trie_get v m = Some u) /\
    NoDup (children (tree g r m o) u) /\
    StronglySorted (preorder_before (tree g r m o)) (children (tree g r m o) u).
End DOM_LAWS.

Module Type DOM := DOM_OPS <+ DOM_SPEC <+ DOM_LAWS.

Module Type DOM_TIME (Import D : DOM).
  Parameter T_build : prepared -> positive -> N.
  Parameter T_check : prepared -> positive -> ptrie positive -> list positive -> N.
  Parameter T_tree : prepared -> positive -> ptrie positive -> list positive -> N.
  Parameter T_dominates_b : domtree -> positive -> positive -> N.
  Parameter c_dom : N.
  (** Checking keeps the published linear bound for arbitrary candidates, including rejection. *)
  Parameter T_check_le : forall g r m o,
    (T_check g r m o <= c_dom * N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
  (** Tree construction keeps the published linear graph bound. *)
  Parameter T_tree_le : forall g r m o, check g r m o = true ->
    (T_tree g r m o <= c_dom * N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
  (** Interval queries charge their queried key and interval widths. *)
  Parameter T_dominates_b_le : forall t u v,
    (T_dominates_b t u v <= c_dom * N.of_nat (query_width t u v + 1))%N.
  (** Simple Lengauer--Tarjan has the aggregate logarithmic producer target. *)
  Parameter T_build_le : forall g r, prepared_ok g ->
    (T_build g r <= c_dom * N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
      N.of_nat (Nat.log2 (graph_n (base g)) + 1) * N.of_nat (graph_width (base g) + 1))%N.
  (** Checking has the published linear bit-cost bound. *)
  Parameter check_bigO : bigO (fun _ : prepared * positive * ptrie positive * list positive => True)
    (fun '(g, _, _, _) => N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (graph_width (base g) + 1))) (fun '(g, r, m, o) => T_check g r m o).
  (** Numbering has the published linear bit-cost bound. *)
  Parameter tree_bigO : bigO (fun '(g, r, m, o) => check g r m o = true)
    (fun '(g, _, _, _) => N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (graph_width (base g) + 1))) (fun '(g, r, m, o) => T_tree g r m o).
  (** Query costs depend on the supplied interval and key widths. *)
  Parameter dominates_b_bigO : bigO (fun _ : domtree * positive * positive => True)
    (fun '(t, u, v) => N.of_nat (query_width t u v + 1))
    (fun '(t, u, v) => T_dominates_b t u v).
  (** Building keeps the graph-size times logarithmic bit-cost target. *)
  Parameter build_bigO : bigO (fun '(g, _) => prepared_ok g)
    (fun '(g, _) => N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (Nat.log2 (graph_n (base g)) + 1) * (graph_width (base g) + 1)))
    (fun '(g, r) => T_build g r).
End DOM_TIME.

Module Type DOM_T := DOM <+ DOM_TIME.

Module Type DOM_PLAN (Import D : DOM_T).
  Parameter pos_of : list positive -> positive -> N.
  Parameter T_pos_of : list positive -> positive -> N.
  Parameter size_of : ptrie positive -> list positive -> positive -> N.
  Parameter T_size_of : ptrie positive -> list positive -> positive -> N.
  Parameter scan : prepared -> dom_scan_data.
  Parameter T_scan : prepared -> N.
  Parameter read : dom_scan_data -> positive -> list positive -> option (ptrie N).
  Parameter T_read : dom_scan_data -> positive -> list positive -> N.
  Parameter map_check : dom_scan_data -> positive -> ptrie positive -> list positive -> bool.
  Parameter T_map_check : dom_scan_data -> positive -> ptrie positive -> list positive -> N.
  Parameter sizes : ptrie positive -> list positive -> ptrie N.
  Parameter T_sizes : ptrie positive -> list positive -> N.
  Parameter edges : prepared -> ptrie positive -> list positive -> bool.
  Parameter T_edges : prepared -> ptrie positive -> list positive -> N.
  Parameter lt_dfs : prepared -> positive -> list positive.
  Parameter T_lt_dfs : prepared -> positive -> N.
  Parameter lt_semi : prepared -> positive -> ptrie positive.
  Parameter T_lt_semi : prepared -> positive -> N.
  Parameter lt_order : prepared -> positive -> list positive.
  Parameter T_lt_order : prepared -> positive -> N.
  Parameter k_scan k_read k_map k_size k_edge k_tree k_dfs k_semi k_le k_order : N.

(** A path ends with an edge into its target, unless it is a single vertex. *)
Parameter F0_path_last : forall g a vs b, path g a vs b ->
  (vs = [b] /\ a = b) \/
  exists vs' c, path g a vs' c /\ edge g c b /\ vs = vs' ++ [b].

(** A dominator of a dominator dominates. *)
Parameter F1_dominates_trans : forall g r x y v,
  dominates g r x y -> dominates g r y v -> dominates g r x v.

(** Acceptance establishes the certificate. *)
Parameter F2_check_cert : forall g r m o, check g r m o = true -> dom_cert (base g) r m o.

(** An accepted order holds listed vertices only. *)
Parameter F2b_check_listed : forall g r m o, check g r m o = true ->
  forall v, In v o -> In v (verts (base g)).

(** Ancestors precede their proper descendants. *)
Parameter F3_anc_before : forall g r m o u v, dom_cert g r m o ->
  tree_anc m u v -> u <> v -> order_before o u v.

(** The root is an ancestor of every listed vertex. *)
Parameter F4_root_anc : forall g r m o v, dom_cert g r m o -> In v o -> tree_anc m r v.

(** Every reachable vertex is listed. *)
Parameter F5_reach_listed : forall g r m o v, dom_cert g r m o ->
  reach g [r] v -> In v o.

(** Every listed vertex is reachable. *)
Parameter F6_listed_reach : forall g r m o v, dom_cert g r m o ->
  In v o -> reach g [r] v.

(** Ancestors in the candidate tree dominate. *)
Parameter F7_anc_dominates : forall g r m o u v, dom_cert g r m o ->
  In v o -> tree_anc m u v -> dominates g r u v.

(** Ancestry in the candidate tree is decidable. *)
Parameter F8_anc_dec : forall g r m o u v, dom_cert g r m o -> In v o ->
  tree_anc m u v \/ ~ tree_anc m u v.

(** Every listed vertex has a path from the root through vertices that are not after it. *)
Parameter F9a_low_path : forall g r m o v, dom_cert g r m o -> In v o ->
  exists vs, path g r vs v /\ forall y, In y vs -> y = v \/ order_before o y v.

(** Every child has a path from its parent through vertices that are not before it. *)
Parameter F9b_high_path : forall g r m o v p, dom_cert g r m o -> trie_get v m = Some p ->
  exists vs, path g p vs v /\
    forall y, In y vs -> y = p \/ y = v \/ order_before o v y.

(** A vertex that is no ancestor is avoided by some path from the root. *)
Parameter F9c_avoid : forall g r m o x v, dom_cert g r m o -> In v o ->
  ~ tree_anc m x v -> exists vs, path g r vs v /\ ~ In x vs.

(** Every dominator of a listed vertex is a candidate ancestor. *)
Parameter F9_dominates_anc : forall g r m o x v, dom_cert g r m o ->
  In v o -> dominates g r x v -> tree_anc m x v.

(** The certificate makes the parent map exact. *)
Parameter F10_cert_exact : forall g r m o, dom_cert (base g) r m o -> dom_exact g r m.

(** Positions and subtree sizes decide ancestry by intervals. *)
Parameter F11_intervals : forall g r m o u v, dom_cert g r m o -> In u o -> In v o ->
  (tree_anc m u v <->
   (pos_of o u <= pos_of o v /\ pos_of o v + size_of m o v <= pos_of o u + size_of m o u)%N).

(** Numbering an accepted certificate gives an exact tree. *)
Parameter F12_tree_exact : forall g r m o, check g r m o = true ->
  domtree_exact g r (tree g r m o).

  Parameter lt_ops : prepared -> positive -> list lt_op.
  Parameter lt_forest : Type.
  Parameter lt_init : prepared -> positive -> lt_forest.
  Parameter run_ops : list lt_op -> lt_forest -> lt_forest.
  Parameter T_run_ops : list lt_op -> lt_forest -> N.

  (** Scanning reads listed rows and constructs the membership trie. *)
  Parameter T1_scan : forall g,
    (T_scan g <= k_scan * N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (graph_width (base g) + 1)))%N.
  (** Reading stops at the graph-sized certificate budget. *)
  Parameter T2_read : forall g r o,
    (T_read (scan g) r o <= k_read * N.of_nat ((graph_n (base g) + 1) *
      (graph_width (base g) + 1)))%N.
  (** Parent reconstruction rejects extra candidate bindings by structural comparison. *)
  Parameter T3_map : forall g r m o,
    (T_map_check (scan g) r m o <= k_map * N.of_nat ((graph_n (base g) + 1) *
      (graph_width (base g) + 1)))%N.
  (** Subtree sizes and low-high tests charge each accepted order entry. *)
  Parameter T4_sizes : forall g m o, NoDup o -> length o <= graph_n (base g) ->
    (forall v, In v o -> In v (nodes g)) ->
    (forall v p, In v o -> trie_get v m = Some p -> In p o) ->
    (T_sizes m o <= k_size * N.of_nat ((graph_n (base g) + 1) *
      (graph_width (base g) + 1)))%N.
  (** Edge checks read only rows whose sources are listed. *)
  Parameter T5_edges : forall g m o, length o <= graph_n (base g) ->
    (forall v, In v o -> In v (verts (base g))) ->
    (forall v p, In v o -> trie_get v m = Some p -> In p o) ->
    (T_edges g m o <= k_edge * N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (graph_width (base g) + 1)))%N.
  (** Numbering and inverse-parent grouping make one pass over accepted entries. *)
  Parameter T6_tree : forall g r m o, check g r m o = true ->
    (T_tree g r m o <= k_tree * N.of_nat ((graph_n (base g) + 1) *
      (graph_width (base g) + 1)))%N.
  (** DFS numbers reached vertices using binary counters. *)
  Parameter T7_dfs : forall g r, prepared_ok g ->
    (T_lt_dfs g r <= k_dfs * N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (graph_width (base g) + 1)))%N.
  (** The actual link-and-evaluate sequence is bounded by reached incidences. *)
  Parameter F13_ops_length : forall g r, prepared_ok g ->
    length (lt_ops g r) <= 2 * (graph_n (base g) + graph_e (base g)) + 1.
  (** Path compression has an aggregate logarithmic bound over the actual sequence. *)
  Parameter T8_link_eval : forall g r, prepared_ok g ->
    (T_run_ops (lt_ops g r) (lt_init g r) <= k_le *
      N.of_nat ((length (lt_ops g r) + graph_n (base g) + 1) *
        (Nat.log2 (graph_n (base g)) + 1) * (graph_width (base g) + 1)))%N.
  (** Semidominators and bucket correction charge the aggregate forest work once. *)
  Parameter T9_semi : forall g r, prepared_ok g ->
    (T_lt_semi g r <= k_semi * N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (graph_width (base g) + 1)) + T_run_ops (lt_ops g r) (lt_init g r))%N.
  (** Divergent trees, derived sources and offline insertion produce the low-high order. *)
  Parameter T10_order : forall g r, prepared_ok g ->
    (T_lt_order g r <= k_order *
      N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
        (Nat.log2 (graph_n (base g)) + 1) * (graph_width (base g) + 1)))%N.
End DOM_PLAN.

Module Type DOM_ALL := DOM_T <+ DOM_PLAN.
