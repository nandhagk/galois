# Galois.Graph

Graph provides edge-labelled graphs with entry nodes, and the standard algorithms over them, each
with an exactness theorem: depth-first search and reverse postorder, dominators and
post-dominators, strongly connected components, loop forests, Bourdoncle's weak topological order,
dominance frontiers, control dependence and register colouring. Nothing assumes node ids: a node
type supplies an `encoding`. For example, with entries `[1]` and edges `1→2`, `2→3`, `3→2`, the
search visits `[1; 2; 3]`, `3→2` is a retreating edge, `2` dominates `3`, and the loop forest has
one loop with header `2` and nodes `{2, 3}`. Every producer is total. Dominator backends and the
weak topological order have direct correctness proofs. Independent checkers remain available for
external candidates; colouring also retains its checked fallback.

Conventions of this document. The graph record is `Graph.t V E` in module `Graph`, with the
projections `Graph.entries`, `Graph.nodes`, `Graph.out`, `Graph.source` and `Graph.target`, always
written qualified (a constraint system also has a `target`). `reachable`, `graph_wf` and every other
definition are top-level names. Sets are `FinSet.t`; `FinSet.mem EV v s` takes the encoding first,
as in Collections. Statements sit in `Section`s whose `Context` and `Variables` declare what they
mention; a theorem is generalised over exactly the ones it uses, in declaration order. Stdlib
imports (`List`, `Bool`, `ZArith`, `Permutation`, `Relations.Relation_Operators`) are implicit,
`ListNotations` is open. Every `Inductive` and `Record` takes its parameters implicitly in
constructors and projections (`Arguments` declarations are omitted).

## Files

Prerequisites: GRA-1a needs COL-1c; GRA-1b needs GRA-1a; GRA-2a needs GRA-1b;
GRA-2c needs GRA-2a; GRA-2d and GRA-2e need GRA-2c; GRA-2f needs GRA-2d and GRA-2e;
GRA-2b needs GRA-2f; GRA-7 needs GRA-5 and GRA-2f;
GRA-3a needs GRA-1b; GRA-3b needs GRA-3a; GRA-4a needs GRA-2f and GRA-1b; GRA-4b needs GRA-3a and
GRA-4a; GRA-4c needs GRA-3a; GRA-5 needs GRA-2b; GRA-6a needs GRA-1a; GRA-6b needs GRA-6a.

| File | Contents | Card |
|---|---|---|
| `GraphCore.v` | module `Graph`, `reachable`, `graph_wf` (anchors); `path`, `reaches`, `mutual`, `before`, `acyclic`, `set_entries`, `without`, `induced`, `edge_count` | GRA-1a |
| `GraphPrepare.v` | `prepared` (with `fuel`), `prepare`, `prepared_laws`, `ready`, `reverse_graph`, `prepared_reverse` | GRA-1a |
| `GraphDfs.v` | `dfs`, `dfs_result`, `rpo`, `retreating`, tree ancestry, interval ancestry test | GRA-1b |
| `GraphCertificate.v` | `check_path`, `tree_path` | GRA-1b |
| `GraphDominance.v` | semantic dominance, `idom_ancestor`, `forest_on`, virtual-root reduction | GRA-2a |
| `GraphSemiDominators.v` | shared DFS numbering, semidominators and link/eval proofs | GRA-2c |
| `GraphLengauerTarjan.v` | `simple_lt_idom`, `simple_lt_idom_exact` | GRA-2d |
| `GraphSemiNca.v` | `semi_nca_idom`, `semi_nca_idom_exact` | GRA-2e |
| `GraphDominators.v` | `dom_tree`, `chk_idom`, boundary checker, selector and exact trees | GRA-2f |
| `GraphEdgeDominance.v` | `edge_dominates`, `edge_dom_index`, `dominating_edges` | GRA-2b |
| `GraphPostDominators.v` | `post_dominates`, `post_dominator_tree` | GRA-2b |
| `GraphScc.v` | iterative Tarjan: `scc_within`, `scc`, `condensation`, `topological_order` | GRA-3a |
| `GraphDag.v` | `topological_sort`, `max_paths` | GRA-3b |
| `GraphChain.v` | `resolve`, `resolve_all` (forwarding chains) | GRA-3b |
| `GraphReducible.v` | `back_edge`, `reducible`, `reducible_b` | GRA-4a |
| `GraphNaturalLoops.v` | `natural_loop`, `natural_loop_nodes` | GRA-4a |
| `GraphLoops.v` | `loop_forest`, `loop_forest_of` | GRA-4b |
| `GraphWto.v` | `wto`, `wto_of`, `check_wto`, `wto_all_heads`, `wto_total` | GRA-4c |
| `GraphFrontier.v` | `dominance_chain`, `dominance_frontier`, `iterated_frontier` | GRA-5 |
| `GraphIdf.v` | `in_pruned_idf`, `direct_idf`, `direct_pruned_idf` | GRA-7 |
| `GraphControlDependence.v` | `control_deps`, `cdep` | GRA-5 |
| `GraphInterference.v` | `interference`, `add_point` (an observer step) | GRA-6a |
| `GraphColour.v` | `greedy_colour`, `check_colouring`, `all_spilled` | GRA-6a |
| `GraphBriggs.v` | `briggs_colour`, `colour_checked`, `degenerate` | GRA-6b |

## Definitions

### GRA-1a: core, preparation, reverse graph, fuel

`reachable` and `graph_wf` are the anchors, with the projections written qualified:

```coq
Module Graph.
Record t (V E : Type) : Type := Make {
  entries : list V;
  nodes : list V;
  out : V -> list E;
  source : E -> V;
  target : E -> V
}.
End Graph.
Inductive reachable {V E} (g : Graph.t V E) : V -> Prop :=
  | reachable_entry : forall v, In v (Graph.entries g) -> reachable g v
  | reachable_step : forall e, reachable g (Graph.source g e) ->
      In e (Graph.out g (Graph.source g e)) -> reachable g (Graph.target g e).
Record graph_wf {V E} (g : Graph.t V E) : Prop := {
  nodes_nodup : NoDup (Graph.nodes g);
  entries_in : forall v, In v (Graph.entries g) -> In v (Graph.nodes g);
  out_source : forall v e, In e (Graph.out g v) -> Graph.source g e = v;
  out_target_in : forall v e, In v (Graph.nodes g) -> In e (Graph.out g v) ->
    In (Graph.target g e) (Graph.nodes g)
}.
```

Additions to `GraphCore.v`:

```coq
Inductive path {V E} (g : Graph.t V E) : V -> list E -> V -> Prop :=
  | path_nil : forall v, path g v [] v
  | path_cons : forall e es w, In e (Graph.out g (Graph.source g e)) ->
      path g (Graph.target g e) es w -> path g (Graph.source g e) (e :: es) w.
Definition reaches {V E} (g : Graph.t V E) (u v : V) : Prop := exists es, path g u es v.
Definition mutual {V E} (g : Graph.t V E) (u v : V) : Prop := reaches g u v /\ reaches g v u.
Definition acyclic {V E} (g : Graph.t V E) : Prop :=
  forall v es, In v (Graph.nodes g) -> path g v es v -> es = [].
Definition before {A} (l : list A) (u v : A) : Prop := exists l1 l2 l3, l = l1 ++ u :: l2 ++ v :: l3.
Definition set_entries {V E} (g : Graph.t V E) (roots : list V) : Graph.t V E :=
  {| Graph.entries := roots; Graph.nodes := Graph.nodes g; Graph.out := Graph.out g;
     Graph.source := Graph.source g; Graph.target := Graph.target g |}.
(* delete the blocked nodes, and the edges into them *)
Definition without {V E} (EV : encoding V) (blocked : FinSet.t V) (g : Graph.t V E) : Graph.t V E :=
  {| Graph.entries := filter (fun v => negb (FinSet.mem EV v blocked)) (Graph.entries g);
     Graph.nodes := filter (fun v => negb (FinSet.mem EV v blocked)) (Graph.nodes g);
     Graph.out := fun v => filter (fun e => negb (FinSet.mem EV (Graph.target g e) blocked)) (Graph.out g v);
     Graph.source := Graph.source g; Graph.target := Graph.target g |}.
(* keep only the nodes of `keep`, and the edges between them; no entries *)
Definition induced {V E} (EV : encoding V) (keep : FinSet.t V) (g : Graph.t V E) : Graph.t V E :=
  {| Graph.entries := []; Graph.nodes := filter (fun v => FinSet.mem EV v keep) (Graph.nodes g);
     Graph.out := fun v => filter (fun e => FinSet.mem EV (Graph.target g e) keep) (Graph.out g v);
     Graph.source := Graph.source g; Graph.target := Graph.target g |}.
(* the number of edges listed in the out lists of the nodes *)
Definition edge_count {V E} (g : Graph.t V E) : nat :=
  fold_right (fun v n => length (Graph.out g v) + n) 0 (Graph.nodes g).
```

`prepare` runs once per graph. The index maps are built from `Graph.out g` over `Graph.nodes g`, so
every later algorithm reads adjacency and predecessors by map lookup. The record also carries the
fuel of every explicit-stack walk: one run visits each node at most once, and each step takes an
edge, pushes a new node or pops one, so `2 * length (Graph.nodes g) + edge_count g + 2` steps
suffice.

```coq
Record prepared {V E} (EV : encoding V) (g : Graph.t V E) : Type := Prepared {
  out_index : Map.t V (list E);          (* Graph.out g v, stored per node *)
  in_index : Map.t V (list E);           (* the edges whose target is v, in order of Graph.nodes g *)
  fuel : positive                        (* 2 * |nodes| + edge_count g + 2, in binary *)
}.
Definition prepare {V E} (EV : encoding V) (g : Graph.t V E) : prepared EV g.
Definition succ_edges {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g) (v : V) : list E.
Definition pred_edges {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g) (v : V) : list E.
(* both are the stored list, or [] when v has no entry *)
Record prepared_laws {V E} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) : Prop := {
  succ_agrees : forall v, In v (Graph.nodes g) -> succ_edges p v = Graph.out g v;
  succ_domain : forall v, ~ In v (Graph.nodes g) -> succ_edges p v = [];
  pred_agrees : forall v e, In v (Graph.nodes g) ->
    (In e (pred_edges p v) <->
     exists u, In u (Graph.nodes g) /\ In e (Graph.out g u) /\ Graph.target g e = v);
  pred_domain : forall v, ~ In v (Graph.nodes g) -> pred_edges p v = [];
  pred_nodup : forall v, NoDup (pred_edges p v);
  fuel_value : Pos.to_nat (fuel p) = 2 * length (Graph.nodes g) + edge_count g + 2
}.
(* the standing premise of every algorithm below: the graph is well formed, no out list repeats an
   edge, and p is its index *)
Definition ready {V E} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) : Prop :=
  graph_wf g /\ (forall v, NoDup (Graph.out g v)) /\ prepared_laws EV g p.
(* the reverse graph: entries become the exits, edges keep their identity and swap direction *)
Definition reverse_graph {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
    (exits : list V) : Graph.t V E :=
  {| Graph.entries := exits; Graph.nodes := Graph.nodes g; Graph.out := pred_edges p;
     Graph.source := Graph.target g; Graph.target := Graph.source g |}.
Definition prepared_reverse {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
    (exits : list V) : prepared EV (reverse_graph p exits) :=
  {| out_index := in_index p; in_index := out_index p; fuel := fuel p |}.
```

### GRA-1b: depth-first search, certificates

`dfs` is depth-first search from `roots` in the given order, never entering a node of `blocked`
(use `FinSet.empty` for the plain search). It loops over the roots; a root that is blocked or
already visited is skipped, and every other root starts one explicit-stack run, with
`(node, remaining successor edges)` frames and fuel `fuel p`.

```coq
Record dfs_result (V E : Type) : Type := DfsResult {
  preorder : list V;
  postorder : list V;
  tree_edge : Map.t V E;                 (* the edge by which v was first reached; absent for a root *)
  pre_num : Map.t V positive;            (* 1-based position in preorder *)
  post_num : Map.t V positive;           (* 1-based position in postorder *)
  visited : FinSet.t V
}.
Definition dfs {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
  (blocked : FinSet.t V) (roots : list V) : dfs_result V E.
Definition rpo {V E} (r : dfs_result V E) : list V := rev (postorder r).
Definition tree_parent {V E} (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E) (u v : V) : Prop :=
  exists e, Map.get EV v (tree_edge r) = Some e /\ Graph.source g e = u.
(* u is v or a DFS-tree ancestor of v *)
Definition dfs_ancestor {V E} (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E) : V -> V -> Prop :=
  clos_refl_trans V (tree_parent EV g r).
(* constant-time ancestry by DFS intervals *)
Definition ancestor_b {V E} (EV : encoding V) (r : dfs_result V E) (u v : V) : bool :=
  match Map.get EV u (pre_num r), Map.get EV v (pre_num r),
        Map.get EV u (post_num r), Map.get EV v (post_num r) with
  | Some a, Some b, Some c, Some d => Pos.leb a b && Pos.leb d c
  | _, _, _, _ => false
  end.
(* an edge is retreating when it goes from a node to itself or to one of its tree ancestors *)
Definition retreating {V E} (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E) (e : E) : Prop :=
  dfs_ancestor EV g r (Graph.target g e) (Graph.source g e).
```

```coq
(* GraphCertificate.v *)
(* a certificate that `es` is a path from s to v: each edge leaves the current node and is one of
   its successor edges; eqE decides equality of edges *)
Definition check_path {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
  (eqE : E -> E -> bool) (s : V) (es : list E) (v : V) : bool.
(* the tree path from a root to v, read off tree_edge in time linear in its length *)
Definition tree_path {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
  (r : dfs_result V E) (v : V) : option (V * list E).
```

### GRA-2a, GRA-2c–2f: the dominator tree

`dominates` is semantic: every path from an entry to `n` passes through `d` (as its first node, or
as the target of one of its edges). With several entries a node can have no strict dominator.

```coq
Definition dominates {V E} (g : Graph.t V E) (d n : V) : Prop :=
  forall s es, In s (Graph.entries g) -> path g s es n ->
    d = s \/ exists e, In e es /\ Graph.target g e = d.
Definition strictly_dominates {V E} (g : Graph.t V E) (d n : V) : Prop := dominates g d n /\ d <> n.
Definition immediately_dominates {V E} (g : Graph.t V E) (d n : V) : Prop :=
  strictly_dominates g d n /\ forall x, strictly_dominates g x n -> dominates g x d.
```

The dominator tree is a forest: the roots are the reachable nodes with no strict dominator, and
`idom` omits them.

`GraphDominance.v` also supplies a fresh virtual root. The type `V + unit` keeps the root
distinct from every client vertex; `E + V` keeps synthetic entry edges distinct from client
edges. `virtual_entries` removes duplicate entries in first-occurrence order, using `EV`.

```coq
Definition virtual_entries {V E} (EV : encoding V) (g : Graph.t V E) : list V.
Definition virtual_graph {V E} (EV : encoding V) (g : Graph.t V E) : Graph.t (V + unit) (E + V) :=
  {| Graph.entries := [inr tt];
     Graph.nodes := map (@inl V unit) (Graph.nodes g) ++ [inr tt];
     Graph.out := fun v => match v with
       | inl x => map (@inl E V) (Graph.out g x)
       | inr _ => map (@inr E V) (virtual_entries EV g)
       end;
     Graph.source := fun e => match e with
       | inl x => inl (Graph.source g x)
       | inr _ => inr tt
       end;
     Graph.target := fun e => match e with
       | inl x => inl (Graph.target g x)
       | inr x => inl x
       end |}.
Definition virtual_encoding {V} (EV : encoding V) : encoding (V + unit) :=
  sum_encoding EV unit_encoding.
Definition virtual_prepared {V E} {EV : encoding V} {g : Graph.t V E}
  (p : prepared EV g) : prepared (virtual_encoding EV) (virtual_graph EV g) :=
  prepare (virtual_encoding EV) (virtual_graph EV g).
```

GRA-2c builds the shared semidominator map on that graph. A semidominator path has at least one
edge; every internal vertex has a DFS preorder number strictly greater than the target's. The
first and last vertices are excluded from that internal-vertex test. The semidominator is the
candidate with least preorder number. The root and unreachable vertices have no map entry.

```coq
Definition semidom_path {V E} (EV : encoding V) (g : Graph.t V E)
  (r : dfs_result V E) (u n : V) : Prop :=
  exists es k h, es <> [] /\ path g u es n /\ Map.get EV n (pre_num r) = Some k /\
    Map.get EV u (pre_num r) = Some h /\
    forall pre e post, es = pre ++ e :: post -> post <> [] ->
      exists j, Map.get EV (Graph.target g e) (pre_num r) = Some j /\ Pos.lt k j.
Definition semidominator {V E} (EV : encoding V) (g : Graph.t V E)
  (r : dfs_result V E) (u n : V) : Prop :=
  semidom_path EV g r u n /\
  exists k, Map.get EV u (pre_num r) = Some k /\
    forall v, semidom_path EV g r v n ->
      exists j, Map.get EV v (pre_num r) = Some j /\ Pos.le k j.
Definition virtual_dfs {V E} {EV : encoding V} {g : Graph.t V E}
  (p : prepared EV g) : dfs_result (V + unit) (E + V) :=
  dfs (virtual_prepared p) FinSet.empty [inr tt].
Definition semidominators {V E} {EV : encoding V} {g : Graph.t V E}
  (p : prepared EV g) : Map.t (V + unit) (V + unit).
```

Compute semidominators in reverse DFS order using predecessor indexes and shared link/eval;
both direct backends consume this same result. For each compressed link, the implementation
maintains the minimum semidominator-rank label on the corresponding segment of the original
uncompressed linked forest. `eval` returns a minimum on the queried linked path; compression
preserves that fact for all subsequent queries. Prove the segment invariant, minimum query,
rank-decreasing termination, semidominator path characterization and virtual-root path reduction
before either backend proof. These proof helpers and the link/eval state are internal.

```coq
Record dom_tree (V : Type) : Type := DomTree {
  idom : Map.t V V;                      (* parent in the forest; absent for a root *)
  tin : Map.t V positive;                (* DFS interval of the node in the forest *)
  tout : Map.t V positive
}.
Definition idom_ancestor {V} (EV : encoding V) (m : Map.t V V) : V -> V -> Prop :=
  clos_refl_trans V (fun u v => Map.get EV v m = Some u).      (* u is v or an ancestor of v *)
(* m is a forest on the reachable nodes: keys and parents are reachable and no parent chain is infinite *)
Definition forest_on {V E} (EV : encoding V) (g : Graph.t V E) (m : Map.t V V) : Prop :=
  (forall v u, Map.get EV v m = Some u -> reachable g v /\ reachable g u) /\
  well_founded (fun u v => Map.get EV v m = Some u).
Inductive dom_algorithm : Type := SimpleLT | SemiNCA.
Definition simple_lt_idom {V E} {EV : encoding V} {g : Graph.t V E}
  (p : prepared EV g) : Map.t V V.
Definition semi_nca_idom {V E} {EV : encoding V} {g : Graph.t V E}
  (p : prepared EV g) : Map.t V V.
Definition chk_idom {V E} {EV : encoding V} {g : Graph.t V E}
  (p : prepared EV g) : Map.t V V := simple_lt_idom p.
(* The compatibility name is directly proved, not an unchecked CHK candidate. *)
(* Both use one DFS on a fresh tagged virtual root, shared semidominators and link/eval.
   Erase virtual-root parent bindings. LT settles buckets and corrects provisional parents;
   Semi-NCA finds the nearest common ancestor of each semidominator and DFS parent. *)
Definition dom_tree_of {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
  (m : Map.t V V) : dom_tree V.
(* idom is m; tin and tout come from one DFS of the forest m, from the reachable nodes that have no
   parent, over children lists built from m *)
Definition check_idom {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
  (m : Map.t V V) : bool.
(* first: every key and value of m is reachable, and the numbering of m visits every key, so m is a
   forest; then, for every reachable d, runs dfs p {d} (Graph.entries g) and requires, for every
   reachable n: n is missed by that search  iff  dominates_b (dom_tree_of p m) d n *)
Definition dominates_b {V} (EV : encoding V) (t : dom_tree V) (d n : V) : bool :=
  match Map.get EV d (tin t), Map.get EV n (tin t), Map.get EV d (tout t), Map.get EV n (tout t) with
  | Some a, Some b, Some c, Some e => Pos.leb a b && Pos.leb e c
  | _, _, _, _ => false
  end.
(* the fallback: no parents, except that when every entry is one node s each other reachable node
   has parent s (a sole entry dominates everything reachable) *)
Definition flat_idom {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g) : Map.t V V :=
  match Graph.entries g with
  | s :: rest =>
      if forallb (fun x => Pos.eqb (encode EV x) (encode EV s)) rest
      then fold_left (fun m n => if Pos.eqb (encode EV n) (encode EV s) then m else Map.set EV n s m)
             (preorder (dfs p FinSet.empty (Graph.entries g))) Map.empty
      else Map.empty
  | [] => Map.empty
  end.
Definition flat_tree {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g) : dom_tree V :=
  dom_tree_of p (flat_idom p).
(* did the independent checker accept the directly constructed default map? *)
Definition dominator_exact {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g) : bool :=
  check_idom p (chk_idom p).
(* Explicit boundary query. Direct constructors do not call this expensive checker. *)
Definition dominator_tree_with {V E} {EV : encoding V} {g : Graph.t V E}
  (p : prepared EV g) (algorithm : dom_algorithm) : dom_tree V :=
  dom_tree_of p (match algorithm with SimpleLT => simple_lt_idom p | SemiNCA => semi_nca_idom p end).
Definition dominator_tree {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g) : dom_tree V :=
  dominator_tree_with p SimpleLT.
```

### GRA-2b: edge dominance and post-dominators

```coq
(* GraphEdgeDominance.v: every entry path to n contains the edge e *)
Definition edge_dominates {V E} (g : Graph.t V E) (e : E) (n : V) : Prop :=
  forall s es, In s (Graph.entries g) -> path g s es n -> In e es.
```

Edge dominance rides on the tree. `edge_dom_index` maps a node `v` to the edge that dominates `v`:
among the edges of `pred_edges p v` whose source is reachable and for which `dominates_b t v
(source e)` is false, the only one, provided `v` is not an entry and there is exactly one. One pass
over `Graph.nodes g` builds it. `dominating_edges` walks the `idom` chain of `n` once.

```coq
Definition edge_dom_index {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
  (t : dom_tree V) : Map.t V E.
Definition dominating_edges {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
  (t : dom_tree V) (ix : Map.t V E) (n : V) : list E.
(* the index entries of n and of every ancestor of n in t *)

(* GraphPostDominators.v: every path from n to an exit passes through d *)
Definition post_dominates {V E} (g : Graph.t V E) (exits : list V) (d n : V) : Prop :=
  forall es x, path g n es x -> In x exits -> d = n \/ exists e, In e es /\ Graph.target g e = d.
(* post-dominators: the total dominator tree of the reverse graph, from an explicit list of exits *)
Definition post_dominator_tree {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
    (exits : list V) : dom_tree V :=
  dominator_tree (prepared_reverse p exits).
```

### GRA-3a: components and condensation

```coq
Definition topological_order {V E} (g : Graph.t V E) (l : list V) : Prop :=
  NoDup l /\ (forall v, In v l <-> In v (Graph.nodes g)) /\
  forall e, In (Graph.source g e) (Graph.nodes g) -> In e (Graph.out g (Graph.source g e)) ->
    before l (Graph.source g e) (Graph.target g e).

Record scc_result (V : Type) : Type := SccResult {
  components : list (list V);            (* in Tarjan's emission order: after every component it reaches *)
  component_ids : list positive;         (* IDs in the same emission order *)
  component_at : Trie.t (list V);       (* component indexed by its ID *)
  comp_of : Map.t V positive             (* component ID of each node *)
}.
Definition scc_within {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
  (region : list V) : scc_result V.
(* iterative Tarjan over the nodes of region in list order, ignoring every edge whose target is
   outside region (a set built once from region). A call costs O(|region| + the edges of its nodes);
   no filtered copy of the graph is built. On emission, a positive counter starts at 1 and advances
   once per component; the component, its ID, and its trie binding are recorded together *)
Definition scc {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g) : scc_result V :=
  scc_within p (Graph.nodes g).
```

The machine behind `scc_within`; its invariant is the spine of the exactness proof.

```coq
Record tarjan_frame (V E : Type) : Type := TarjanFrame {
  frame_node : V;
  frame_edges : list E                   (* the successor edges of frame_node not yet taken *)
}.
Record tarjan_state (V E : Type) : Type := TarjanState {
  frames : list (tarjan_frame V E);      (* the open nodes: the depth-first path from the current root, innermost first *)
  disc : Map.t V positive;               (* discovery number of every visited node, from a positive clock *)
  low : Map.t V positive;                (* lowlink of every visited node not yet in a component *)
  pending : list V;                      (* visited nodes not yet in a component, newest first *)
  clock : positive;                      (* the next discovery number *)
  emitted : scc_result V                 (* the components emitted so far *)
}.
(* Invariant, for the induced graph G of region, at every step:
   I1  every emitted component is a strong component of G, and every edge of G that leaves it enters
       a component emitted earlier;
   I2  pending is exactly the visited nodes outside the emitted components, newest first, with disc
       strictly decreasing; frames lists the open nodes, a subsequence of pending, each open node
       the tree parent of the open node before it;
   I3  for every pending w: low w <= disc w, and low w = disc x for a pending x in the strong
       component of w (x = w when nothing older was found);
   I4  when the frame of v closes: low v = disc v exactly when no pending node older than v lies in
       the strong component of v, and then the pending nodes down to v are that whole component,
       emitted as one; otherwise low v is folded into the low of the node below it on frames. *)
```

```coq
Definition condensation {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
  (r : scc_result V) : Graph.t positive E.
(* nodes = rev (component_ids r); entries = the distinct components of the entries of g;
   out c = the edges of g that leave a member of c for another component (edges keep their
   identity and labels), kept in a trie built in one pass; source e, target e = the components of
   the ends of e *)
```

### GRA-3b: topological sort, maximum-weight paths, forwarding chains

```coq
Definition topological_sort {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g) :
  option (list V).      (* rpo of dfs p FinSet.empty (Graph.nodes g); None if some edge retreats *)
Definition path_weight {E} (w : E -> Z) (es : list E) : Z := fold_right (fun e acc => (w e + acc)%Z) 0%Z es.
Record dag_paths (V E : Type) : Type := DagPaths {
  best : Map.t V Z;                      (* maximum weight of an entry path to v; present iff reachable *)
  via : Map.t V E                        (* last edge of one such path; absent when the empty path wins *)
}.
Definition max_paths {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g) (w : E -> Z) :
  option (dag_paths V E).
(* one pass in the rpo of the reachable part, rpo (dfs p FinSet.empty (Graph.entries g)); None iff
   an edge out of a reachable node retreats, that is, iff a reachable cycle exists *)
Definition max_path_to {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
  (r : dag_paths V E) (v : V) : option (V * list E).      (* follows via back to an entry *)

(* a forwarding step: v satisfies fwd and has exactly one outgoing edge *)
Definition forward_step {V E} (g : Graph.t V E) (fwd : V -> bool) (v : V) : option E :=
  if fwd v then match Graph.out g v with [e] => Some e | _ => None end else None.
Inductive chain {V E} (g : Graph.t V E) (fwd : V -> bool) : V -> list E -> V -> Prop :=
  | chain_stop : forall v, forward_step g fwd v = None -> chain g fwd v [] v
  | chain_move : forall v e es w, forward_step g fwd v = Some e ->
      chain g fwd (Graph.target g e) es w -> chain g fwd v (e :: es) w.
Inductive resolution (V : Type) : Type := Landing (w : V) | Cyclic.
Definition resolve {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g) (fwd : V -> bool)
  (v : V) : resolution V.                 (* follows forward_step; a visited set is the cycle guard *)
Definition resolve_all {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
  (fwd : V -> bool) : Map.t V (resolution V).      (* every node of g; each chain walked once *)
```

### GRA-4a: reducibility and natural loops

```coq
Definition back_edge {V E} (g : Graph.t V E) (e : E) : Prop :=
  In e (Graph.out g (Graph.source g e)) /\ reachable g (Graph.source g e) /\
  dominates g (Graph.target g e) (Graph.source g e).
(* Hecht-Ullman: every cycle through a reachable node contains a back edge *)
Definition reducible {V E} (g : Graph.t V E) : Prop :=
  forall v es, reachable g v -> es <> [] -> path g v es v -> exists e, In e es /\ back_edge g e.
Definition reducible_b {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g) (t : dom_tree V) : bool.
(* every retreating edge of dfs p FinSet.empty (Graph.entries g) out of a visited node has a target
   that dominates_b its source, by one interval test per edge *)

(* the natural loop of a back edge: its target, and what reaches its source without the target *)
Definition natural_loop {V E} (EV : encoding V) (g : Graph.t V E) (e : E) (n : V) : Prop :=
  n = Graph.target g e \/
  exists es, path (without EV (FinSet.add EV (Graph.target g e) FinSet.empty) g) n es (Graph.source g e).
Definition natural_loop_nodes {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g) (e : E) :
  FinSet.t V.
(* the target of e together with one reverse search from the source of e that never enters the
   target *)
```

### GRA-4b: the loop nesting forest

```coq
Record loop_forest (V : Type) : Type := LoopForest {
  loop_headers : list V;                 (* every header, once; an outer loop before the loops inside it *)
  loop_nodes : Map.t V (FinSet.t V);     (* header -> every node of its loop, nested loops included *)
  loop_parent : Map.t V V;               (* header -> header of the next enclosing loop; absent at top *)
  loop_of : Map.t V V                    (* node -> header of its innermost loop; absent outside loops *)
}.
Definition loop_forest_of {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g) : loop_forest V.
(* Steensgaard/Ramalingam recursion on node lists: the loops of a region are the non-trivial
   components of scc_within p region (a component is trivial when it is one node with no self loop);
   the header of one is its first node in rpo (dfs p FinSet.empty (Graph.entries g)); its children
   are the loops of its node list without the header. The top region is the preorder of that search.
   Each call costs O(|region| + the edges of its nodes). Irreducible loops are covered. *)
Definition in_loop {V} (EV : encoding V) (f : loop_forest V) (h x : V) : Prop :=
  exists s, Map.get EV h (loop_nodes f) = Some s /\ FinSet.mem EV x s = true.
(* the set a loop lives in: its parent's loop without the parent's header, or, at top level, the
   nodes reachable from the entries *)
Definition outer_nodes {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
    (f : loop_forest V) (h : V) : FinSet.t V :=
  match Map.get EV h (loop_parent f) with
  | Some h' => match Map.get EV h' (loop_nodes f) with
               | Some s => FinSet.remove EV h' s | None => FinSet.empty end
  | None => visited (dfs p FinSet.empty (Graph.entries g))
  end.
Definition strong_component {V E} (g : Graph.t V E) (S : V -> Prop) : Prop :=
  (exists v, S v) /\ (forall u v, S u -> S v -> mutual g u v) /\ (forall u v, S u -> mutual g u v -> S v).
```

### GRA-4c: the weak topological order

A weak topological order is a flat token list: `a (b c (d) e) f` is `WVertex a`, `WOpen b`,
`WVertex c`, `WOpen d`, `WClose`, `WVertex e`, `WClose`, `WVertex f`.

```coq
Inductive wto_token (V : Type) : Type :=
  | WVertex (v : V)
  | WOpen (h : V)                        (* a component begins; h is its head and first vertex *)
  | WClose.                              (* the innermost open component ends *)
Definition wto (V : Type) : Type := list (wto_token V).
Fixpoint balanced_from {V} (d : nat) (w : wto V) : bool :=
  match w with
  | [] => Nat.eqb d 0
  | WVertex _ :: w' => balanced_from d w'
  | WOpen _ :: w' => balanced_from (S d) w'
  | WClose :: w' => match d with O => false | S d' => balanced_from d' w' end
  end.
(* each vertex in textual order with the stack of heads of the components containing it,
   innermost first; a head's own stack starts with itself *)
Fixpoint annotate {V} (stack : list V) (w : wto V) : list (V * list V) :=
  match w with
  | [] => []
  | WVertex v :: w' => (v, stack) :: annotate stack w'
  | WOpen h :: w' => (h, h :: stack) :: annotate (h :: stack) w'
  | WClose :: w' => annotate (tl stack) w'
  end.
Definition wto_order {V} (w : wto V) : list V := map fst (annotate [] w).
(* Bourdoncle's definition over the reachable nodes: every edge goes forward, or its target is
   the head of a component that contains its source *)
Definition wto_valid {V E} (g : Graph.t V E) (w : wto V) : Prop :=
  balanced_from 0 w = true /\ NoDup (wto_order w) /\
  (forall v, In v (wto_order w) <-> reachable g v) /\
  forall e, reachable g (Graph.source g e) -> In e (Graph.out g (Graph.source g e)) ->
    before (wto_order w) (Graph.source g e) (Graph.target g e) \/
    exists st, In (Graph.source g e, st) (annotate [] w) /\ In (Graph.target g e) st.
Definition check_wto {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g) (w : wto V) : bool.
(* One token pass assigns positive positions and stores (pos, end) for every vertex. For a head,
   end is the position of its matching WClose; for a vertex, end is its own position. A separate
   set records heads. For each edge u -> v, accept when pos u < pos v, or when v is a head and
   pos v <= pos u <= end v. The checker also verifies balance, uniqueness and exact reachability.
   Each edge uses map and set lookups, without scanning a head stack. *)
Definition wto_of {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g) : wto V.
(* Bourdoncle's recursion on node lists, from the reachable nodes in rpo: the components of
   scc_within p region in reverse emission order (a topological order of the condensation); a
   non-trivial component with header h, the first of its nodes in rpo, becomes WOpen h, the order
   of its node list without h, then WClose; a singleton with a self-loop also opens a component.
   An acyclic singleton becomes WVertex. The producer is proved valid directly. *)
(* the fallback in which every node is a head, nested: the vertices of order become heads in turn *)
Definition wto_all_heads {V} (order : list V) : wto V :=
  map (fun h => WOpen h) order ++ repeat (WClose : wto_token V) (length order).
(* total: the directly proved order; the checker and fallback remain boundary utilities *)
Definition wto_total {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g) : wto V :=
  wto_of p.
```

### GRA-5: frontiers and control dependence

```coq
Definition in_df {V E} (g : Graph.t V E) (d n : V) : Prop :=
  exists e, In e (Graph.out g (Graph.source g e)) /\ Graph.target g e = n /\
    reachable g (Graph.source g e) /\
    dominates g d (Graph.source g e) /\ ~ strictly_dominates g d n.
Inductive in_idf {V E} (g : Graph.t V E) (defs : list V) : V -> Prop :=
  | idf_step : forall d n, (In d defs \/ in_idf g defs d) -> in_df g d n -> in_idf g defs n.
Definition dominance_frontier {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
  (t : dom_tree V) : Map.t V (FinSet.t V).
(* Cooper-Harvey-Kennedy runner walk, with no two-predecessor shortcut: for each node b and each
   reachable predecessor of b, walk up the tree from that predecessor to idom b exclusive, or to the
   root inclusive when b has no idom, adding b to the frontier of every node on the walk; the walk is
   charged to the frontier it fills. Specified for an exact tree only *)
Definition iterated_frontier {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
  (df : Map.t V (FinSet.t V)) (defs : list V) : FinSet.t V.      (* worklist over df with a seen set *)

(* GraphIdf.v: direct single-query IDF, without materializing all frontiers. *)
Inductive in_pruned_idf {V E} (g : Graph.t V E) (defs : list V) (live : V -> bool) : V -> Prop :=
  | pruned_idf_step : forall d n, (In d defs \/ in_pruned_idf g defs live d) ->
      in_df g d n -> live n = true -> in_pruned_idf g defs live n.
Definition direct_idf {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
  (t : dom_tree V) (defs : list V) : FinSet.t V.
Definition direct_pruned_idf {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
  (t : dom_tree V) (defs : list V) (live : V -> bool) : FinSet.t V.
(* A dominator-tree priority worklist visits DJ edges and processes each discovered node once.
   The pruned variant enqueues and emits only live nodes. Build indexes once; charge priority
   operations, visited edges, encoding, and output separately. *)

(* GraphControlDependence.v: edge e = (b -> s) makes n control dependent on b when n
   post-dominates s and does not strictly post-dominate b *)
Definition control_dependent {V E} (g : Graph.t V E) (exits : list V) (n : V) (e : E) : Prop :=
  In e (Graph.out g (Graph.source g e)) /\ post_dominates g exits n (Graph.target g e) /\
  ~ (post_dominates g exits n (Graph.source g e) /\ n <> Graph.source g e).
Definition cdep {V E} (g : Graph.t V E) (exits : list V) (b n : V) : Prop :=
  exists e, Graph.source g e = b /\ control_dependent g exits n e.
(* every node of g reaches an exit; a client adds exits for infinite loops *)
Definition exits_reachable {V E} (g : Graph.t V E) (exits : list V) : Prop :=
  forall v, In v (Graph.nodes g) -> exists es x, path g v es x /\ In x exits.
Definition control_deps {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
  (exits : list V) (pt : dom_tree V) : Map.t V (list E).
(* n -> the edges n is control dependent on: the frontier of n in the reverse graph, edge by edge *)
```

### GRA-6a: interference and greedy colouring

```coq
Record interference (V : Type) : Type := Interference {
  vertices : FinSet.t V;
  adjacent : Map.t V (FinSet.t V)        (* symmetric; no self loops *)
}.
Definition empty_interference {V} : interference V.
Definition neighbours {V} (EV : encoding V) (ig : interference V) (v : V) : FinSet.t V :=
  match Map.get EV v (adjacent ig) with Some s => s | None => FinSet.empty end.
Definition interferes {V} (EV : encoding V) (ig : interference V) (u v : V) : Prop :=
  FinSet.mem EV v (neighbours EV ig u) = true.
Record interference_wf {V} (EV : encoding V) (ig : interference V) : Prop := {
  interferes_sym : forall u v, interferes EV ig u v -> interferes EV ig v u;
  interferes_irrefl : forall v, ~ interferes EV ig v v;
  interferes_vertex : forall u v, interferes EV ig u v -> FinSet.mem EV u (vertices ig) = true;
  vertices_wf : FinSet.wf EV (vertices ig);
  adjacent_wf : Map.wf EV (adjacent ig);
  neighbours_wf : forall v, FinSet.wf EV (neighbours EV ig v)
}.
(* an observer step for Fixpoint's replay: at a point that writes `defs`, with `src` the source
   when the point is a move, and `live` the set live after it, add (d, x) for every d in defs and
   x in FinSet.elements live with x <> d and Some x <> src; every defined and live vertex becomes a vertex *)
Definition add_point {V} (EV : encoding V) (defs : list V) (src : option V) (live : FinSet.t V)
  (ig : interference V) : interference V.

Record colour_result (V : Type) : Type := ColourResult {
  colours : Map.t V nat;                 (* colour numbers 0 .. k-1 *)
  spilled : list V
}.
Record proper_colouring {V} (EV : encoding V) (ig : interference V) (k : nat) (pre : Map.t V nat)
    (res : colour_result V) : Prop := {
  colour_below_k : forall v c, Map.get EV v (colours res) = Some c -> c < k;
  vertex_decided : forall v, FinSet.mem EV v (vertices ig) = true ->
    (exists c, Map.get EV v (colours res) = Some c) \/ In v (spilled res);
  spilled_uncoloured : forall v, In v (spilled res) -> Map.get EV v (colours res) = None;
  adjacent_differ : forall u v cu cv, interferes EV ig u v ->
    Map.get EV u (colours res) = Some cu -> Map.get EV v (colours res) = Some cv -> cu <> cv;
  precoloured_kept : forall v c, Map.get EV v pre = Some c -> Map.get EV v (colours res) = Some c
}.
Definition check_colouring {V} (EV : encoding V) (ig : interference V) (k : nat)
  (pre : Map.t V nat) (res : colour_result V) : bool.      (* one pass over vertices and neighbours *)
(* the precoloured vertices use colours below k, and no two adjacent ones share a colour *)
Definition precolour_ok {V} (EV : encoding V) (ig : interference V) (k : nat) (pre : Map.t V nat) : Prop :=
  (forall v c, Map.get EV v pre = Some c -> c < k) /\
  forall u v cu cv, interferes EV ig u v -> Map.get EV u pre = Some cu -> Map.get EV v pre = Some cv -> cu <> cv.
Definition greedy_colour {V} (EV : encoding V) (ig : interference V) (k : nat) (pre : Map.t V nat)
  (moves : list (V * V)) (order : list V) : colour_result V.
(* in `order`: the preferred colour of a move partner if free, else the lowest free colour, else spill *)
(* keeps the precoloured vertices (colours := pre) and spills every other vertex of ig *)
Definition all_spilled {V} (EV : encoding V) (ig : interference V) (pre : Map.t V nat) : colour_result V :=
  {| colours := pre;
     spilled := filter (fun v => negb (Map.mem EV v pre)) (FinSet.elements (vertices ig)) |}.
```

### GRA-6b: Chaitin-Briggs colouring

```coq
Definition briggs_colour {V} (EV : encoding V) (ig : interference V) (k : nat) (pre : Map.t V nat)
  (moves : list (V * V)) : colour_result V.
(* Chaitin-Briggs: simplify vertices of degree < k, push a spill candidate optimistically when none
   remains, then select in reverse order with the move bias; a failed select is an actual spill *)
Definition colour_checked {V} (EV : encoding V) (ig : interference V) (k : nat) (pre : Map.t V nat)
  (moves : list (V * V)) : colour_result V :=
  let r := briggs_colour EV ig k pre moves in
  if check_colouring EV ig k pre r then r else all_spilled EV ig pre.
(* the elimination-order form of "k-colourable by simplification" *)
Definition degenerate {V} (EV : encoding V) (ig : interference V) (k : nat) : Prop :=
  exists order, NoDup order /\ (forall v, FinSet.mem EV v (vertices ig) = true <-> In v order) /\
    forall l1 v l2, order = l1 ++ v :: l2 ->
      length (filter (fun u => FinSet.mem EV u (neighbours EV ig v)) l2) < k.
```

## Theorems

`ready EV g p` is the standing premise: the graph is well formed, no out list repeats an edge, and
`p` is its prepared form with its laws. In a statement, `R` stands for `dfs p blocked roots` where a
`Local Notation` says so. Theorems about `dominator_tree`, `wto_total` and `colour_checked` are
total: soundness holds without a premise, exactness under `dominator_exact p = true`.

### GRA-1a

```coq
Section Gra1a.
Context {V E : Type} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g).
Variables (u v : V) (es : list E) (exits : list V).

(** Reachability is the existence of an entry path, and a reachable node of a well-formed graph is one of its nodes. *)
Theorem reachable_iff_path : reachable g v <-> exists s es, In s (Graph.entries g) /\ path g s es v.
Theorem reachable_in_nodes : graph_wf g -> reachable g v -> In v (Graph.nodes g).
(* Proof idea: induction on reachable and on the path from the entry; entries_in and out_target_in. Card: GRA-1a. *)

(** The prepared indexes agree with the graph, and no predecessor list repeats an edge. *)
Theorem prepare_ready : graph_wf g -> (forall x, NoDup (Graph.out g x)) -> ready EV g (prepare EV g).
(* Proof idea: a fold of Map.set over Graph.nodes g builds both indexes. The graph's unique nodes,
   out_source and the NoDup out lists give pred_nodup; fuel_value follows by arithmetic.
   Card: GRA-1a. *)
Theorem pred_edges_nodup : ready EV g p -> NoDup (pred_edges p v).
(* Proof idea: project pred_nodup from prepared_laws. Card: GRA-1a. *)

(** Reversal keeps the standing premise and reverses paths. *)
Theorem reverse_graph_ready :
  ready EV g p -> incl exits (Graph.nodes g) -> ready EV (reverse_graph p exits) (prepared_reverse p exits).
(* Proof idea: pred_agrees and out_source give each graph law; pred_nodup gives NoDup reverse out
   lists. The original NoDup out lists and succ_agrees give reverse pred_nodup at graph nodes;
   succ_domain gives it outside them. The edge lists on both sides have no repeats and contain the
   same edges, so their total lengths agree and fuel_value carries over. The swapped indexes agree
   by symmetry. Card: GRA-1a. *)
Theorem reverse_path :
  ready EV g p -> In u (Graph.nodes g) -> In v (Graph.nodes g) ->
  (path g u es v <-> path (reverse_graph p exits) v (rev es) u).
(* Proof idea: induction on es, with pred_agrees for each edge. Card: GRA-1a. *)
End Gra1a.
```

### GRA-1b

```coq
Section Gra1b.
Context {V E : Type} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g).
Variables (u v s : V) (es : list E) (roots : list V) (blocked : FinSet.t V) (eqE : E -> E -> bool).
Local Notation R := (dfs p blocked roots).

(** The search visits exactly what the roots reach without entering a blocked node, each once, within `fuel p`. *)
Theorem dfs_exact : ready EV g p -> incl roots (Graph.nodes g) ->
  (FinSet.mem EV v (visited R) = true <->
   reachable (without EV blocked (set_entries g roots)) v) /\
  NoDup (preorder R) /\ Permutation (preorder R) (postorder R) /\
  (In v (preorder R) <-> FinSet.mem EV v (visited R) = true).
(* Proof idea: the stack invariant: finished nodes have all successors visited or blocked, visited nodes were reached by a path; a run that visits k new nodes takes at most 2k + (edges of those nodes) + 1 steps, within fuel p, so the fuel never runs out. Card: GRA-1b. *)
(** The plain search from the entries visits exactly the reachable nodes. *)
Theorem reachable_dfs : ready EV g p ->
  (FinSet.mem EV v (visited (dfs p FinSet.empty (Graph.entries g))) = true <-> reachable g v).
(* Proof idea: dfs_exact with nothing blocked; filtering by the empty set leaves every list unchanged, so reachability is that of g. Card: GRA-1b. *)

(** Every visited node is a root or has a tree edge from a visited parent that precedes it. *)
Theorem dfs_tree : ready EV g p -> incl roots (Graph.nodes g) -> FinSet.mem EV v (visited R) = true ->
  (In v roots /\ Map.get EV v (tree_edge R) = None) \/
  (exists e, Map.get EV v (tree_edge R) = Some e /\ In e (Graph.out g (Graph.source g e)) /\
     Graph.target g e = v /\ FinSet.mem EV (Graph.source g e) (visited R) = true /\
     before (preorder R) (Graph.source g e) v).
(* Proof idea: tree_edge is set exactly when a node is first reached through an edge. Card: GRA-1b. *)

(** In reverse postorder a parent precedes its child and a root precedes its whole tree. *)
Theorem rpo_order : ready EV g p -> incl roots (Graph.nodes g) ->
  (forall e, Map.get EV v (tree_edge R) = Some e -> before (rpo R) (Graph.source g e) v) /\
  (forall w, In v roots -> Map.get EV v (tree_edge R) = None -> FinSet.mem EV v (visited R) = true ->
     dfs_ancestor EV g R v w -> w = v \/ before (rpo R) v w).
(* Proof idea: a node finishes after its tree descendants, so it comes first in the reverse. Card: GRA-1b. *)
(** With one entry, reverse postorder starts at it. *)
Theorem rpo_single_entry : ready EV g p -> Graph.entries g = [s] ->
  exists rest, rpo (dfs p FinSet.empty (Graph.entries g)) = s :: rest.
(* Proof idea: s is the only root, and rpo_order puts it before its tree. Card: GRA-1b. *)
(** From the entries, every reachable node that is not an entry has a DFS parent earlier in reverse postorder. *)
Theorem rpo_parent_of_non_entry : ready EV g p -> reachable g v -> ~ In v (Graph.entries g) ->
  exists e, Map.get EV v (tree_edge (dfs p FinSet.empty (Graph.entries g))) = Some e /\
    before (rpo (dfs p FinSet.empty (Graph.entries g))) (Graph.source g e) v.
(* Proof idea: reachable_dfs makes v visited; only entries are roots, so dfs_tree gives a tree edge, and rpo_order orders it. Card: GRA-1b. *)

(** Every edge out of a visited node goes forward in reverse postorder or retreats to an ancestor. *)
Theorem rpo_edge_classes : ready EV g p -> incl roots (Graph.nodes g) -> forall e,
  FinSet.mem EV (Graph.source g e) (visited (dfs p FinSet.empty roots)) = true ->
  In e (Graph.out g (Graph.source g e)) ->
  before (rpo (dfs p FinSet.empty roots)) (Graph.source g e) (Graph.target g e) \/
  retreating EV g (dfs p FinSet.empty roots) e.
(* Proof idea: by finish times: tree, forward and cross edges finish their target first; an edge to an open node is retreating. Card: GRA-1b. *)
(** Every cycle through a visited node contains a retreating edge. *)
Theorem cycle_has_retreating_edge : ready EV g p -> incl roots (Graph.nodes g) ->
  FinSet.mem EV v (visited (dfs p FinSet.empty roots)) = true -> es <> [] -> path g v es v ->
  exists e, In e es /\ retreating EV g (dfs p FinSet.empty roots) e.
(* Proof idea: if every edge went forward, positions in rpo would increase strictly around the cycle. Card: GRA-1b. *)
(** The interval test decides ancestry in constant time. *)
Theorem ancestor_b_agrees : ready EV g p -> incl roots (Graph.nodes g) ->
  FinSet.mem EV u (visited R) = true -> FinSet.mem EV v (visited R) = true ->
  (ancestor_b EV R u v = true <-> dfs_ancestor EV g R u v).
(* Proof idea: tree intervals nest, and pre_num and post_num are positions in the two orders. Card: GRA-1b. *)

(** A certificate checks exactly when it is a path, and a tree path is a path from a root. *)
Theorem check_path_correct : ready EV g p -> (forall a b, eqE a b = true <-> a = b) -> In s (Graph.nodes g) ->
  (check_path p eqE s es v = true <-> path g s es v).
(* Proof idea: induction on es; the membership test is succ_agrees. Card: GRA-1b. *)
Theorem tree_path_valid : ready EV g p -> incl roots (Graph.nodes g) ->
  FinSet.mem EV v (visited R) = true ->
  exists s es, tree_path p R v = Some (s, es) /\ In s roots /\ path g s es v.
(* Proof idea: follow tree_edge to a root; each edge is a successor edge by dfs_tree. Card: GRA-1b. *)
End Gra1b.
```

### GRA-2a

```coq
Section Gra2a.
Context {V E : Type} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g).
Variables (d n s : V) (m : Map.t V V).

(** Dominance is reflexive and transitive. *)
Theorem dominates_refl : dominates g n n.
Theorem dominates_trans : forall a b c, dominates g a b -> dominates g b c -> dominates g a c.
(* Proof idea: refl: an entry path ends at n, as its start or as an edge target. Trans: a path to c passes b; its prefix to b is an entry path to b, so it passes a. Card: GRA-2a. *)

(** Dominance is unreachability once the dominator is deleted; this is what the checker runs. *)
Theorem dominates_iff_unreachable_without :
  dominates g d n <-> ~ reachable (without EV (FinSet.add EV d FinSet.empty) g) n.
(* Proof idea: a path of g from an entry that avoids d, as start and as every target, is a path of the filtered graph and conversely. Card: GRA-2a. *)

Theorem virtual_entries_exact : NoDup (virtual_entries EV g) /\
  (forall v, In v (virtual_entries EV g) <-> In v (Graph.entries g)).
(* Proof idea: a set-indexed first-occurrence traversal preserves membership and order.
   Card: GRA-2a. *)
Theorem virtual_graph_ready : ready EV g p ->
  ready (virtual_encoding EV) (virtual_graph EV g) (virtual_prepared p).
(* Proof idea: tagged constructors are disjoint and injective; virtual_entries_exact gives
   unique synthetic edges and graph closure; apply prepare_ready. Card: GRA-2a. *)
Theorem virtual_path_iff : ready EV g p -> forall s es n,
  (path (virtual_graph EV g) (inr tt) (inr s :: map (@inl E V) es) (inl n) <->
   In s (Graph.entries g) /\ path g s es n).
(* Proof idea: invert the first synthetic edge, then induct on the original edge list.
   Card: GRA-2a. *)
Theorem virtual_dominates_iff : ready EV g p -> forall d n,
  (dominates g d n <-> dominates (virtual_graph EV g) (inl d) (inl n)).
(* Proof idea: every root-to-real-node path begins with one synthetic entry edge and otherwise
   contains only original edges; translate both directions using virtual_path_iff. Card: GRA-2a. *)

Theorem semidominators_wf : ready EV g p ->
  Map.wf (virtual_encoding EV) (semidominators p).
Theorem semidominators_exact : ready EV g p -> forall u n,
  (Map.get (virtual_encoding EV) n (semidominators p) = Some u <->
   reachable (virtual_graph EV g) n /\ n <> inr tt /\
   semidominator (virtual_encoding EV) (virtual_graph EV g) (virtual_dfs p) u n).
(* Proof idea: DFS numbering and the semidominator path characterization reduce every candidate
   to a predecessor and a linked-tree minimum. Prove the compression segment invariant and
   reverse-order induction, including root and unreachable omissions. Card: GRA-2c. *)

Theorem simple_lt_idom_exact : ready EV g p ->
  Map.wf EV (simple_lt_idom p) /\ forest_on EV g (simple_lt_idom p) /\
  (forall d n, reachable g n ->
    (dominates g d n <-> idom_ancestor EV (simple_lt_idom p) d n)).
(* Proof idea: semidominator path characterization, link/eval minimum-label invariant, bucket
   settlement and final parent correction; translate paths through the fresh virtual root.
   Card: GRA-2d. *)
Theorem semi_nca_idom_exact : ready EV g p ->
  Map.wf EV (semi_nca_idom p) /\ forest_on EV g (semi_nca_idom p) /\
  (forall d n, reachable g n ->
    (dominates g d n <-> idom_ancestor EV (semi_nca_idom p) d n)).
(* Proof idea: shared semidominator and link/eval invariants and the nearest-common-ancestor
   theorem; the parent walk decreases DFS rank. Card: GRA-2e. *)
Theorem dominator_tree_with_exact : ready EV g p -> forall algorithm,
  (forall d n, reachable g n ->
    (dominates_b EV (dominator_tree_with p algorithm) d n = true <-> dominates g d n)) /\
  (forall d n, reachable g n ->
    (Map.get EV n (idom (dominator_tree_with p algorithm)) = Some d <->
     immediately_dominates g d n)) /\
  (forall n, reachable g n ->
    (Map.get EV n (idom (dominator_tree_with p algorithm)) = None <->
     forall d, ~ strictly_dominates g d n)).
(* Proof idea: apply the selected backend's exactness and forest numbering; strict dominators
   form a chain. Card: GRA-2f. *)
Theorem dominator_exact_true : ready EV g p -> dominator_exact p = true.
(* Proof idea: simple_lt_idom_exact and check_idom_complete. Card: GRA-2f. *)

(** The producer's map is well formed. *)
Theorem chk_idom_wf : ready EV g p -> Map.wf EV (chk_idom p).
(* Proof idea: simple_lt_idom_exact. Card: GRA-2f. *)

(** The checker decides exactness: an accepted map is a forest whose ancestry is dominance on every reachable node, and every such map is accepted. *)
Theorem check_idom_sound : ready EV g p -> Map.wf EV m -> check_idom p m = true ->
  forest_on EV g m /\ forall d n, reachable g n -> (dominates g d n <-> idom_ancestor EV m d n).
(* Proof idea: the numbering check gives the forest; dominates_iff_unreachable_without and dfs_exact for each blocked search give the iff for reachable d; an unreachable d dominates no reachable node and is no ancestor of one. Card: GRA-2f. *)
Theorem check_idom_complete : ready EV g p -> Map.wf EV m -> forest_on EV g m ->
  (forall d n, reachable g n -> (dominates g d n <-> idom_ancestor EV m d n)) -> check_idom p m = true.
(* Proof idea: each test of the checker is an instance of the hypothesis, by the same two theorems read backwards; well-foundedness makes the numbering reach every key. Card: GRA-2f. *)

(** The numbering of a forest is the interval encoding of its ancestry on the reachable nodes. *)
Theorem dom_tree_of_agrees : ready EV g p -> Map.wf EV m -> forest_on EV g m ->
  (forall n, (exists a, Map.get EV n (tin (dom_tree_of p m)) = Some a) <-> reachable g n) /\
  (forall d n, reachable g n -> (dominates_b EV (dom_tree_of p m) d n = true <-> idom_ancestor EV m d n)).
(* Proof idea: the DFS of the forest visits every node below a root; intervals of a DFS nest exactly along ancestry (ancestor_b_agrees on the forest). Card: GRA-2f. *)

(** The fallback is a forest: no parents, or the sole entry as the parent of every other reachable node. *)
Theorem flat_idom_shape : ready EV g p ->
  Map.wf EV (flat_idom p) /\ forest_on EV g (flat_idom p) /\
  ((Graph.entries g <> [] /\ forall x, In x (Graph.entries g) -> x = s) ->
     forall n, Map.get EV n (flat_idom p) = Some s <-> (reachable g n /\ n <> s)) /\
  ((forall s', ~ (Graph.entries g <> [] /\ forall x, In x (Graph.entries g) -> x = s')) ->
     forall n, Map.get EV n (flat_idom p) = None).
(* Proof idea: unfold the fold over the preorder (reachable_dfs): each key is a reachable non-entry with the entry as its parent, which is a root. Card: GRA-2f. *)

(** The total tree is always sound: it covers the reachable nodes, its ancestry and its interval test imply dominance, and each parent strictly dominates its child. *)
Theorem dominator_tree_sound : ready EV g p ->
  (forall n, (exists a, Map.get EV n (tin (dominator_tree p)) = Some a) <-> reachable g n) /\
  (forall d n, idom_ancestor EV (idom (dominator_tree p)) d n -> dominates g d n) /\
  (forall d n, dominates_b EV (dominator_tree p) d n = true -> dominates g d n) /\
  (forall n d, Map.get EV n (idom (dominator_tree p)) = Some d -> strictly_dominates g d n).
(* Proof idea: simple_lt_idom_exact, dom_tree_of_agrees and dominance reflexivity. Card: GRA-2f. *)

(** When the checker accepted the map, the tree is exact: interval dominance is dominance, the parent of a node is its immediate dominator, and the roots have no strict dominator. *)
Theorem dominator_tree_exact : ready EV g p -> dominator_exact p = true ->
  (forall d n, reachable g n -> (dominates_b EV (dominator_tree p) d n = true <-> dominates g d n)) /\
  (forall d n, reachable g n ->
     (Map.get EV n (idom (dominator_tree p)) = Some d <-> immediately_dominates g d n)) /\
  (forall n, reachable g n ->
     (Map.get EV n (idom (dominator_tree p)) = None <-> forall d, ~ strictly_dominates g d n)).
(* Proof idea: dominator_tree_with_exact for SimpleLT. Card: GRA-2f. *)
End Gra2a.
```

### GRA-2b

```coq
Section Gra2b.
Context {V E : Type} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g).
Variables (d n : V) (e : E) (exits : list V).

(** With an exact tree, an edge dominates n exactly when it is the dominating edge of a node that dominates n. *)
Theorem edge_dominates_iff : ready EV g p -> dominator_exact p = true -> reachable g n ->
  (edge_dominates g e n <->
   exists v, Map.get EV v (edge_dom_index p (dominator_tree p)) = Some e /\
             dominates_b EV (dominator_tree p) v n = true).
(* Proof idea: e dominates n iff e dominates its target v and v dominates n (take the last occurrence of e on an entry path to n); e dominates v iff v is not an entry and e is the sole in-edge of v from a reachable source that v does not dominate (a shortest entry path to v ends in such an edge). pred_edges_nodup makes the count exact. Card: GRA-2b. *)
(** `dominating_edges` returns only edges that dominate n, with no premise that the checker accepted the tree. *)
Theorem dominating_edges_sound : ready EV g p ->
  In e (dominating_edges p (dominator_tree p) (edge_dom_index p (dominator_tree p)) n) ->
  edge_dominates g e n.
(* Proof idea: an imprecise tree can only count too many in-edges as not dominated by v, which drops the index entry and never invents one; each ancestor of n dominates n by dominator_tree_sound, and dominates_trans composes. Card: GRA-2b. *)
(** With an exact tree, `dominating_edges` lists exactly the edges that dominate n. *)
Theorem dominating_edges_exact : ready EV g p -> dominator_exact p = true -> reachable g n ->
  (In e (dominating_edges p (dominator_tree p) (edge_dom_index p (dominator_tree p)) n) <->
   edge_dominates g e n).
(* Proof idea: the dominators of n are its idom chain, then edge_dominates_iff. Card: GRA-2b. *)
(** A self-loop never dominates its own node: the first arrival does not use it. *)
Theorem self_loop_not_edge_dominating :
  reachable g n -> Graph.source g e = n -> Graph.target g e = n -> ~ edge_dominates g e n.
(* Proof idea: a shortest entry path to n contains no edge out of n. Card: GRA-2b. *)

(** Post-dominance is dominance in the reverse graph, and the post-dominator tree answers it soundly always and exactly when its checker accepted. *)
Theorem post_dominates_iff_reverse : ready EV g p -> incl exits (Graph.nodes g) -> In n (Graph.nodes g) ->
  (post_dominates g exits d n <-> dominates (reverse_graph p exits) d n).
(* Proof idea: reverse_path, with the exits as the entries; the nodes visited are the same set read in the other direction. Card: GRA-2b. *)
Theorem post_dominator_tree_sound : ready EV g p -> incl exits (Graph.nodes g) -> In n (Graph.nodes g) ->
  dominates_b EV (post_dominator_tree p exits) d n = true -> post_dominates g exits d n.
(* Proof idea: reverse_graph_ready, dominator_tree_sound on the reverse graph, then the previous theorem. Card: GRA-2b. *)
Theorem post_dominator_tree_exact : ready EV g p -> incl exits (Graph.nodes g) -> In n (Graph.nodes g) ->
  dominator_exact (prepared_reverse p exits) = true -> (exists es x, path g n es x /\ In x exits) ->
  (dominates_b EV (post_dominator_tree p exits) d n = true <-> post_dominates g exits d n).
(* Proof idea: reverse_graph_ready, dominator_tree_exact on the reverse graph (n is reachable there by reverse_path), then the previous theorem. Card: GRA-2b. *)
End Gra2b.
```

### GRA-3a

```coq
Section Gra3a.
Context {V E : Type} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g).
Variables (u v : V) (e : E) (region : list V).
Local Abbreviation R := (scc p).

(** The components partition the region, and two nodes share one exactly when each reaches the other inside it. *)
Theorem scc_within_exact : ready EV g p -> incl region (Graph.nodes g) ->
  NoDup (concat (components (scc_within p region))) /\
  (forall x, In x (concat (components (scc_within p region))) <-> In x region) /\
  (forall c, In c (components (scc_within p region)) -> c <> []) /\
  length (component_ids (scc_within p region)) = length (components (scc_within p region)) /\
  (forall i c, Trie.get i (component_at (scc_within p region)) = Some c <->
     In (i, c) (combine (component_ids (scc_within p region))
                        (components (scc_within p region)))) /\
  NoDup (component_ids (scc_within p region)) /\
  (forall x i, Map.get EV x (comp_of (scc_within p region)) = Some i <->
     exists c, Trie.get i (component_at (scc_within p region)) = Some c /\ In x c) /\
  (In u region -> In v region ->
     ((exists i, Map.get EV u (comp_of (scc_within p region)) = Some i /\
                 Map.get EV v (comp_of (scc_within p region)) = Some i) <->
      mutual (induced EV (FinSet.of_list EV region) g) u v)).
(* Proof idea: the invariant I1 to I4 of the machine, with the fuel bound 2|region| + edges + 1 of fuel p; a node is popped with its root's component iff it reaches and is reached from the root inside the region. Card: GRA-3a. *)
(** Components are emitted after every component they reach. *)
Theorem scc_reverse_topological : ready EV g p -> incl region (Graph.nodes g) ->
  In e (Graph.out g (Graph.source g e)) -> In (Graph.source g e) region -> In (Graph.target g e) region ->
  exists i j, Map.get EV (Graph.source g e) (comp_of (scc_within p region)) = Some i /\
    Map.get EV (Graph.target g e) (comp_of (scc_within p region)) = Some j /\ (j <= i)%positive.
(* Proof idea: I1: an edge leaving an emitted component enters an earlier one, and an edge inside a component has equal indices. Card: GRA-3a. *)
(** On the whole graph the components are the mutual-reachability classes of g. *)
Theorem scc_exact : ready EV g p ->
  NoDup (concat (components R)) /\ (forall x, In x (concat (components R)) <-> In x (Graph.nodes g)) /\
  (In u (Graph.nodes g) -> In v (Graph.nodes g) ->
     ((exists i, Map.get EV u (comp_of R) = Some i /\ Map.get EV v (comp_of R) = Some i) <-> mutual g u v)).
(* Proof idea: scc_within_exact with region = nodes g; the induced graph keeps every edge of g, since out_target_in puts every target in nodes g. Card: GRA-3a. *)
(** The condensation is a well-formed DAG with the stated edges, entries and a topological order. *)
Theorem condensation_correct : ready EV g p ->
  graph_wf (condensation p R) /\ (forall c, NoDup (Graph.out (condensation p R) c)) /\
  acyclic (condensation p R) /\
  topological_order (condensation p R) (rev (component_ids R)) /\
  (forall c e', In e' (Graph.out (condensation p R) c) <->
     exists x j, In x (Graph.nodes g) /\ In e' (Graph.out g x) /\ Map.get EV x (comp_of R) = Some c /\
       Map.get EV (Graph.target g e') (comp_of R) = Some j /\ j <> c) /\
  (forall c, In c (Graph.entries (condensation p R)) <->
     exists s, In s (Graph.entries g) /\ Map.get EV s (comp_of R) = Some c) /\
  NoDup (Graph.entries (condensation p R)) /\
  (forall e', In (Graph.source g e') (Graph.nodes g) -> In (Graph.target g e') (Graph.nodes g) ->
     exists i j, Map.get EV (Graph.source g e') (comp_of R) = Some i /\
       Map.get EV (Graph.target g e') (comp_of R) = Some j /\
       Graph.source (condensation p R) e' = i /\ Graph.target (condensation p R) e' = j).
(* Proof idea: a cycle of components would merge them by scc_exact; the order is scc_reverse_topological; the out lists are sublists of out lists of g, kept whole. Card: GRA-3a. *)
End Gra3a.
```

### GRA-3b

```coq
Section Gra3b.
Context {V E : Type} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g).
Variables (v : V) (w : E -> Z) (fwd : V -> bool).

(** A topological sort exists exactly when the graph is acyclic. *)
Theorem topological_sort_correct : ready EV g p ->
  (forall l, topological_sort p = Some l -> topological_order g l) /\
  (topological_sort p = None <-> ~ acyclic g).
(* Proof idea: rpo of a search from every node; an edge goes forward unless it retreats, and a retreating edge closes a cycle with the tree path. Card: GRA-3b. *)

(** On a graph whose reachable part is acyclic, `max_paths` is exact and attained; it fails only on a reachable cycle. *)
Theorem max_paths_exact : ready EV g p ->
  (forall v es, reachable g v -> es <> [] -> ~ path g v es v) ->
  exists r, max_paths p w = Some r /\ forall v,
    (reachable g v <-> exists b, Map.get EV v (best r) = Some b) /\
    forall b, Map.get EV v (best r) = Some b ->
      (exists s es, max_path_to p r v = Some (s, es) /\ In s (Graph.entries g) /\ path g s es v /\
         path_weight w es = b) /\
      (forall s es, In s (Graph.entries g) -> path g s es v -> (path_weight w es <= b)%Z).
(* Proof idea: dynamic programming in the rpo of the reachable part, where every edge goes forward (rpo_edge_classes with no retreating edge); via records an arg-max edge. Card: GRA-3b. *)
Theorem max_paths_cycle : ready EV g p -> max_paths p w = None ->
  exists v es, reachable g v /\ es <> [] /\ path g v es v.
(* Proof idea: None arises only from a retreating edge out of a reachable node, which closes a cycle with the tree path. Card: GRA-3b. *)

(** `resolve` lands where the forwarding chain ends, is Cyclic exactly when it never ends, and `resolve_all` agrees with it. *)
Theorem resolve_correct : ready EV g p -> In v (Graph.nodes g) ->
  (forall x, resolve p fwd v = Landing x <-> exists es, chain g fwd v es x) /\
  (resolve p fwd v = Cyclic <-> forall es x, ~ chain g fwd v es x) /\
  Map.get EV v (resolve_all p fwd) = Some (resolve p fwd v).
(* Proof idea: forward_step is a function, so a chain is unique; a repeated node proves a cycle, and the walk visits at most |nodes| nodes, within fuel p. Card: GRA-3b. *)
End Gra3b.
```

### GRA-4a

```coq
Section Gra4a.
Context {V E : Type} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g).
Variables (x : V) (e : E).

(** Back edges retreat in every search, and every retreating edge is a back edge exactly when the graph is reducible. *)
Theorem back_edge_retreating : ready EV g p -> back_edge g e ->
  retreating EV g (dfs p FinSet.empty (Graph.entries g)) e.
(* Proof idea: the target dominates the source, so it lies on the tree path to the source (tree_path_valid). Card: GRA-4a. *)
Theorem reducible_iff_retreating_back : ready EV g p ->
  (reducible g <-> forall e, In e (Graph.out g (Graph.source g e)) -> reachable g (Graph.source g e) ->
     retreating EV g (dfs p FinSet.empty (Graph.entries g)) e -> back_edge g e).
(* Proof idea: right to left: cycle_has_retreating_edge puts a retreating edge on every cycle, and it is a back edge. Left to right: the tree path from the target to the source and the edge form a cycle; a tree edge is never a back edge, since the entry path of tree edges to its source does not contain its target, so the retreating edge must be the back edge. Card: GRA-4a. *)
(** The interval check is sound always and decides reducibility under an exact tree. *)
Theorem reducible_b_sound : ready EV g p -> reducible_b p (dominator_tree p) = true -> reducible g.
(* Proof idea: dominates_b is sound (dominator_tree_sound), so every retreating edge is a back edge; reducible_iff_retreating_back. Card: GRA-4a. *)
Theorem reducible_b_correct : ready EV g p -> dominator_exact p = true ->
  (reducible_b p (dominator_tree p) = true <-> reducible g).
(* Proof idea: reducible_iff_retreating_back, with dominates_b equal to dominates on reachable nodes by dominator_tree_exact. Card: GRA-4a. *)

(** One reverse search computes a natural loop. *)
Theorem natural_loop_nodes_exact : ready EV g p -> In (Graph.source g e) (Graph.nodes g) ->
  In x (Graph.nodes g) ->
  (FinSet.mem EV x (natural_loop_nodes p e) = true <-> natural_loop EV g e x).
(* Proof idea: dfs_exact on prepared_reverse with the target blocked, and reverse_path; the target is added by hand. Card: GRA-4a. *)
End Gra4a.
```

### GRA-4b

```coq
Section Gra4b.
Context {V E : Type} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g).
Local Notation F := (loop_forest_of p).

(** The loop forest nests strictly, lists each header once with an outer loop first, and `loop_of` names the innermost loop. *)
Theorem loop_forest_nested : ready EV g p ->
  (forall h, In h (loop_headers F) <-> exists s, Map.get EV h (loop_nodes F) = Some s) /\
  NoDup (loop_headers F) /\
  (forall h, In h (loop_headers F) -> In h (Graph.nodes g) /\ in_loop EV F h h) /\
  (forall h h', Map.get EV h (loop_parent F) = Some h' ->
     before (loop_headers F) h' h /\
     (forall y, in_loop EV F h y -> in_loop EV F h' y) /\ ~ in_loop EV F h h') /\
  (forall y h, Map.get EV y (loop_of F) = Some h ->
     in_loop EV F h y /\ forall h', in_loop EV F h' y -> in_loop EV F h' h) /\
  (forall y, Map.get EV y (loop_of F) = None -> forall h, ~ in_loop EV F h y).
(* Proof idea: induction on the recursion depth of loop_forest_of; each level removes one header, and the headers of a level are emitted after the header whose loop contains them. Card: GRA-4b. *)
(** Each loop is a non-trivial strongly connected component of the set it lives in, headed by its first node in rpo. *)
Theorem loop_forest_exact : ready EV g p -> forall h, In h (loop_headers F) ->
  strong_component (induced EV (outer_nodes p F h) g) (in_loop EV F h) /\
  (exists es, es <> [] /\ path (induced EV (outer_nodes p F h) g) h es h) /\
  (forall y, in_loop EV F h y -> y = h \/ before (rpo (dfs p FinSet.empty (Graph.entries g))) h y).
(* Proof idea: each level computes scc_within of its list (scc_within_exact); the header is the rpo-first member by construction. Card: GRA-4b. *)
(** Every cycle through a reachable node lies in the loop of one of its own nodes, irreducible graphs included. *)
Theorem loop_forest_covers : ready EV g p -> forall v es, reachable g v -> es <> [] -> path g v es v ->
  exists h, In h (loop_headers F) /\ (h = v \/ In h (map (Graph.target g) es)) /\
    forall y, (y = v \/ In y (map (Graph.target g) es)) -> in_loop EV F h y.
(* Proof idea: take the outermost level whose set contains the cycle; either its header is on the cycle, or the cycle survives the header's removal and the recursion applies. Card: GRA-4b. *)
End Gra4b.
```

### GRA-4c

```coq
Section Gra4c.
Context {V E : Type} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g).
Variables (w : wto V) (order : list V).

(** The WTO check decides Bourdoncle's definition, and in a valid order every cycle lies in a component whose head is on the cycle. *)
Theorem check_wto_correct : ready EV g p -> (check_wto p w = true <-> wto_valid g w).
(* Proof idea: the token pass records each head's matching close; its interval contains exactly the
   positions whose annotation includes that head. Card: GRA-4c. *)
Theorem wto_valid_cycles : wto_valid g w -> forall v es, reachable g v -> es <> [] -> path g v es v ->
  exists h, (h = v \/ In h (map (Graph.target g) es)) /\
    forall y st, (y = v \/ In y (map (Graph.target g) es)) -> In (y, st) (annotate [] w) -> In h st.
(* Proof idea: the textually first node m of the cycle has its incoming cycle edge going backward, so m is the head of a component containing that edge's source; well-nesting then forces the component to contain the whole cycle. Card: GRA-4c. *)

(** The all-heads order is valid for every listing of the reachable nodes, so the fallback is valid. *)
Theorem wto_all_heads_valid : ready EV g p -> NoDup order -> (forall v, In v order <-> reachable g v) ->
  wto_valid g (wto_all_heads order).
(* Proof idea: annotate gives the i-th node the stack of the heads up to itself, so an edge goes forward in the list or has its target among the heads before and including its source. Card: GRA-4c. *)
(** The recursive SCC producer itself produces a valid order. *)
Theorem wto_of_valid : ready EV g p -> wto_valid g (wto_of p).
(* Proof idea: induct on the strictly decreasing region; SCC emission orders cross-component
   edges forward, and removing the selected head encloses each remaining backward edge.
   Card: GRA-4c. *)
(** The total order is always valid. *)
Theorem wto_total_valid : ready EV g p -> wto_valid g (wto_total p).
(* Proof idea: wto_of_valid. Card: GRA-4c. *)
End Gra4c.
```

### GRA-5

```coq
Section Gra5.
Context {V E : Type} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g).
Variables (n : V) (e : E) (defs exits : list V).

(** The runner chain contains exactly the dominance-frontier witnesses for one incoming edge. *)
Theorem dominance_chain : ready EV g p -> dominator_exact p = true ->
  In e (Graph.out g (Graph.source g e)) -> reachable g (Graph.source g e) -> forall d,
  (dominates g d (Graph.source g e) /\ ~ strictly_dominates g d (Graph.target g e) <->
   dominates_b EV (dominator_tree p) d (Graph.source g e) = true /\
   (forall q, Map.get EV (Graph.target g e) (idom (dominator_tree p)) = Some q ->
      dominates_b EV (dominator_tree p) d q = false)).
(* Proof idea: the immediate dominator of the target dominates each reachable predecessor; its
   ancestors are exactly the strict dominators of the target. Apply dominator_tree_exact to the
   predecessor and parent. With no parent the runner reaches the root. Card: GRA-5. *)

(** With an exact tree, the computed frontiers are the dominance frontiers, and the iterated frontier is the least closed set. *)
Theorem dominance_frontier_exact : ready EV g p -> dominator_exact p = true -> forall d n,
  ((exists s, Map.get EV d (dominance_frontier p (dominator_tree p)) = Some s /\
              FinSet.mem EV n s = true) <-> in_df g d n).
(* Proof idea: dominance_chain identifies each runner walk with its frontier witnesses.
   Card: GRA-5. *)
Theorem iterated_frontier_exact : ready EV g p -> dominator_exact p = true ->
  (FinSet.mem EV n (iterated_frontier p (dominance_frontier p (dominator_tree p)) defs) = true <->
   in_idf g defs n).
(* Proof idea: worklist invariant: the seen set is closed under df and every member is derived by idf_step. Card: GRA-5. *)

(** Control dependence is the post-dominance frontier, edge by edge, for an exact post-dominator tree. *)
Theorem control_deps_exact : ready EV g p -> incl exits (Graph.nodes g) -> exits_reachable g exits ->
  dominator_exact (prepared_reverse p exits) = true -> In n (Graph.nodes g) ->
  In (Graph.source g e) (Graph.nodes g) ->
  ((exists l, Map.get EV n (control_deps p exits (post_dominator_tree p exits)) = Some l /\ In e l) <->
   control_dependent g exits n e).
(* Proof idea: dominance_chain on the reverse graph identifies the runner for each edge, and
   post_dominates_iff_reverse translates its witnesses to control dependence. Card: GRA-5. *)
End Gra5.
```

### GRA-7: direct iterated-frontier queries

```coq
Section Gra7.
Context {V E : Type} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g).
Variables (defs : list V) (live : V -> bool) (n : V).
Theorem direct_idf_exact : ready EV g p ->
  (FinSet.mem EV n (direct_idf p (dominator_tree p) defs) = true <-> in_idf g defs n).
Theorem direct_pruned_idf_exact : ready EV g p ->
  (FinSet.mem EV n (direct_pruned_idf p (dominator_tree p) defs live) = true <->
   in_pruned_idf g defs live n).
(* Proof idea: the DJ traversal discovers exactly the frontier of each processed definition;
   induction over worklist steps and derivations proves soundness and least-closure completeness.
   The pruning proof includes the live predicate on each derivation step. Card: GRA-7. *)
End Gra7.
```

### GRA-6a

```coq
Section Gra6a.
Context {V : Type} (EV : encoding V).
Variables (ig : interference V) (k : nat) (pre : Map.t V nat) (moves : list (V * V))
  (order : list V) (defs : list V) (src : option V) (live : FinSet.t V).

(** The observer step adds exactly the interferences of one point, makes every defined and live node a vertex, and keeps the graph symmetric and loop-free. *)
Theorem add_point_exact : FinSet.wf EV live -> forall u v,
  interferes EV (add_point EV defs src live ig) u v <->
  (interferes EV ig u v \/
   (In u defs /\ FinSet.mem EV v live = true /\ v <> u /\ Some v <> src) \/
   (In v defs /\ FinSet.mem EV u live = true /\ u <> v /\ Some u <> src)).
(* Proof idea: add_point is a fold of FinSet.add into both adjacency sets, over defs and FinSet.elements live; FinSet.elements_spec turns elements into membership. Card: GRA-6a. *)
Theorem add_point_vertices : FinSet.wf EV live -> forall v,
  FinSet.mem EV v (vertices (add_point EV defs src live ig)) = true <->
  (FinSet.mem EV v (vertices ig) = true \/ In v defs \/ FinSet.mem EV v live = true).
(* Proof idea: vertices only grow, by the defined nodes and the elements of live (FinSet.elements_spec). Card: GRA-6a. *)
Theorem add_point_wf : interference_wf EV ig -> FinSet.wf EV live ->
  interference_wf EV (add_point EV defs src live ig).
(* Proof idea: each added pair is added in both directions and skips equal ends; Map.wf_set and FinSet.wf_ops keep the stored sets well formed. Card: GRA-6a. *)

(** The checker decides properness. *)
Theorem check_colouring_correct : forall res, interference_wf EV ig -> Map.wf EV pre -> Map.wf EV (colours res) ->
  (check_colouring EV ig k pre res = true <-> proper_colouring EV ig k pre res).
(* Proof idea: unfold; each clause is one pass over the vertices and their neighbour sets, and Map.elements_spec on the well-formed maps. Card: GRA-6a. *)
(** Greedy colouring is proper for every order and move bias, and spills nothing when every degree is below k. *)
Theorem greedy_colour_proper : interference_wf EV ig -> Map.wf EV pre -> precolour_ok EV ig k pre ->
  (forall v, FinSet.mem EV v (vertices ig) = true -> In v order) ->
  proper_colouring EV ig k pre (greedy_colour EV ig k pre moves order).
(* Proof idea: invariant: the coloured part is proper; a vertex takes a colour absent from its coloured neighbours. Card: GRA-6a. *)
Theorem greedy_no_spill : interference_wf EV ig -> (forall v, (FinSet.size (neighbours EV ig v) < k)%nat) ->
  (forall v, FinSet.mem EV v (vertices ig) = true -> In v order) ->
  spilled (greedy_colour EV ig k Map.empty moves order) = [].
(* Proof idea: neighbours_wf makes FinSet.size the number of neighbours (FinSet.size_elements); fewer than k forbidden colours leave one free. Card: GRA-6a. *)
End Gra6a.
```

### GRA-6b

```coq
Section Gra6b.
Context {V : Type} (EV : encoding V).
Variables (ig : interference V) (k : nat) (pre : Map.t V nat) (moves : list (V * V)).

(** Chaitin-Briggs colouring is proper, and the checked wrapper is proper even if the producer is wrong. *)
Theorem briggs_colour_proper : interference_wf EV ig -> Map.wf EV pre -> precolour_ok EV ig k pre ->
  proper_colouring EV ig k pre (briggs_colour EV ig k pre moves).
(* Proof idea: select pops every pushed vertex once with the greedy step; simplify only removes vertices. Card: GRA-6b. *)
Theorem colour_checked_proper : interference_wf EV ig -> Map.wf EV pre -> precolour_ok EV ig k pre ->
  proper_colouring EV ig k pre (colour_checked EV ig k pre moves).
(* Proof idea: check_colouring_correct on the accepted branch (the producer's colour map is built from pre by Map.set, so it is well formed); the all-spilled branch is proper by precolour_ok. Card: GRA-6b. *)
(** Nothing spills when the graph simplifies completely; this is stated without precolouring. *)
Theorem briggs_no_spill : interference_wf EV ig -> degenerate EV ig k ->
  spilled (briggs_colour EV ig k Map.empty moves) = [].
(* Proof idea: a degenerate graph always has a vertex of degree < k to simplify, and at select time fewer than k of its neighbours are coloured. Card: GRA-6b. *)
End Gra6b.
```

## Algorithms and references

- **Depth-first search**, iterative with an explicit stack: Tarjan, "Depth-first search and linear
  graph algorithms", SIAM J. Comput. 1972. Reverse postorder and the edge classes are the standard
  forest classification. With several entries the roots form a forest, so an entry reached from an
  earlier one lies in that tree; `rpo_single_entry` is the single-entry statement, and dominance
  uses a virtual root above the roots.
- **Dominators:** Lengauer and Tarjan (1979) simple LT and Georgiadis (2005) Semi-NCA share
  DFS, semidominators and link/eval; each backend is directly proved exact. A fresh tagged virtual
  root handles multiple entries. `check_idom` remains an independent boundary checker.
- **Edge dominance:** an edge dominates a node `v` exactly when it is the only in-edge of `v` from
  a reachable node that `v` does not dominate; then it dominates what `v` dominates.
- **Strongly connected components:** Tarjan 1972, with an explicit stack and lowlinks, stated as the
  invariant I1 to I4; `scc_within` runs on a node list so that loop forests and weak orders recurse
  without filtering the whole graph. **DAG paths** by dynamic programming in the rpo of the
  reachable part; **forwarding chains** by memoised walking.
- **Loops:** Steensgaard, "Sequentializing program dependence graphs for irreducible programs"
  (1993) and Ramalingam, "On loops, dominators, and dominance frontiers" (TOPLAS 2002) for the
  recursive decomposition; Havlak (TOPLAS 1997) for irreducible loops. **Reducibility:** Hecht and
  Ullman (1972). **WTO:** Bourdoncle, "Efficient chaotic iteration strategies with widenings"
  (1993); the checker is his definition, so a wrong producer cannot cause an unsound schedule, and
  the all-heads order is the always-valid fallback.
- **Frontiers and control dependence:** Cytron, Ferrante, Rosen, Wegman and Zadeck (TOPLAS 1991)
  and the runner walk of Cooper, Harvey and Kennedy; Ferrante, Ottenstein and Warren (TOPLAS 1987).
  Both are specified for an exact tree only.
- **Colouring:** Chaitin et al. (1981); Briggs, Cooper and Torczon (TOPLAS 1994) for optimistic
  colouring; George and Appel (1996) for the move bias. Spill choice is a heuristic and not
  specified; properness and the no-spill guarantees are.

## Performance notes

- `prepare` is one pass over `Graph.nodes g` and their edges, with map costs of O(P) per
  operation; every later algorithm reads adjacency and predecessors by lookup in that index.
  Each adjacency list is traversed as required by the algorithm; do not repeatedly scan the full
  graph or unrelated lists. The `before`, `In` and `incl` forms appear in statements only.
  Prove a binary fuel bound for each traversal, including initialization and skipped roots.
- Each prepared index has an agreement lemma: `out_index` with `succ_agrees`, `in_index` with
  `pred_agrees`, `fuel` with `fuel_value`, `pre_num` and `post_num` with `ancestor_b_agrees`,
  `tin` and `tout` with `dom_tree_of_agrees`, `edge_dom_index` with `edge_dominates_iff`,
  `comp_of` with `scc_within_exact`.
- `dfs`, `rpo`, `scc`, `condensation`, `topological_sort`, `max_paths` and `resolve_all` take
  O(V + E) graph operations plus map, key, weight and output costs. Frontier and control-dependence
  runner walks cost O(V + E + visits), with up to O(VE) visits including repeated parallel edges.
- `check_idom` is O(V * (V + E)) graph operations:
  one blocked search per reachable node, over the same prepared index. `dominates_b` and
  `ancestor_b` queries are O(1) interval tests plus map lookups.
- `loop_forest_of` and `wto_of` are O((V + E) * d) for loop depth `d`, since each level is one
  `scc_within` call on a list; `natural_loop_nodes` is proportional to the loop and its incoming
  edges, because the search starts at one node and stops at the header. Materialized loop-node sets
  can themselves contain Theta(Vd) memberships. Map operations cost O(P), where P is the encoded
  key length, not necessarily O(log V); also count binary arithmetic, allocations and output.
- Colouring keeps a degree-bucket map (`Map.t nat (FinSet.t V)`) for simplify and forbidden colours
  as a set per vertex; finding a free colour is O(k).

## Open questions

1. **Edge equality.** `check_path` takes `eqE : E -> E -> bool` instead of an `encoding E`, so
   graphs with opaque edge types need no encoding; membership is a scan of one successor list,
   which is bounded by the out-degree of one node.
2. **Direct producers.** The selected dominator backend and `wto_of` are directly proved; boundary
   checkers remain useful for externally supplied candidates and differential examples.

## Cross-document contracts

Fixpoint uses `Graph.t`, `Graph.out`, `Graph.target`, `prepare`, `ready` and `wto_total`.
The dependency graph has duplicate-free outgoing edges. Views uses the total dominator tree
and its sound edge index; its soundness theorem requires duplicate-free outgoing edges.
Analyses uses `cdep`, `exits_reachable` and `max_paths` on the prepared reachable graph.

<!-- AUD-API-GR-SQ-BEGIN -->

# Graph and SSA source contracts

The definitions describe source work. Future theorem types are proof obligations.

## Galois.Graph.GraphAuditBase

Card: AUD-GR-MODELS

Source destination: `theories/Graph/GraphAuditBase.v`.

```rocq
From Galois.Collections Require Import CollectionsAuditCost.


From Stdlib Require Import List PArith Permutation.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsAuditCost.
From Galois.Graph Require Import GraphCore GraphPrepare.
Import List.ListNotations.

Inductive audit_graph_prepare_map_site : Type :=
  | AuditGraphOutSet
  | AuditGraphIncomingGet
  | AuditGraphIncomingSet.

Inductive audit_graph_prepare_call (V E : Type) : Type :=
  | AuditPrepareOutCall (vertex : V) (edges : list E)
  | AuditPrepareTargetCall (edge : E) (target : V)
  | AuditPrepareEncodeCall (site : audit_graph_prepare_map_site) (vertex : V) (code : positive).
Arguments AuditPrepareOutCall {V E} _ _.
Arguments AuditPrepareTargetCall {V E} _ _.
Arguments AuditPrepareEncodeCall {V E} _ _ _.

Definition audit_graph_prepare_calls {V E} (EV : encoding V) (g : Graph.t V E)
    : list (audit_graph_prepare_call V E) :=
  flat_map (fun v =>
    let outgoing := Graph.out g v in
    [AuditPrepareOutCall v outgoing; AuditPrepareOutCall v outgoing;
     AuditPrepareOutCall v outgoing; AuditPrepareEncodeCall AuditGraphOutSet v (encode EV v)] ++
    flat_map (fun e =>
      let target := Graph.target g e in
      [AuditPrepareTargetCall e target; AuditPrepareTargetCall e target;
       AuditPrepareEncodeCall AuditGraphIncomingGet target (encode EV target);
       AuditPrepareEncodeCall AuditGraphIncomingSet target (encode EV target)]) outgoing)
    (Graph.nodes g).

Definition audit_graph_prepare_callback_count {V E} (g : Graph.t V E) : nat :=
  4 * length (Graph.nodes g) +
  4 * fold_right (fun v n => length (Graph.out g v) + n) 0 (Graph.nodes g).

Inductive audit_graph_prepare_out_execution {V E} (EV : encoding V) (g : Graph.t V E)
    : list V -> Map.t V (list E) -> Map.t V (list E) ->
      list (audit_graph_prepare_call V E) -> Prop :=
  | AuditGraphOutNil m : audit_graph_prepare_out_execution EV g [] m m []
  | AuditGraphOutCons v rest initial middle events :
      audit_graph_prepare_out_execution EV g rest initial middle events ->
      audit_graph_prepare_out_execution EV g (v :: rest) initial
        (Map.set EV v (Graph.out g v) middle)
        (events ++ [AuditPrepareOutCall v (Graph.out g v);
          AuditPrepareEncodeCall AuditGraphOutSet v (encode EV v)]).

Inductive audit_graph_prepare_edges_execution {V E} (EV : encoding V) (g : Graph.t V E)
    : list E -> Map.t V (list E) -> Map.t V (list E) ->
      list (audit_graph_prepare_call V E) -> Prop :=
  | AuditGraphEdgesNil m : audit_graph_prepare_edges_execution EV g [] m m []
  | AuditGraphEdgesCons edge rest initial middle events :
      audit_graph_prepare_edges_execution EV g rest initial middle events ->
      audit_graph_prepare_edges_execution EV g (edge :: rest) initial (index_edge EV g edge middle)
        (events ++ [AuditPrepareTargetCall edge (Graph.target g edge);
          AuditPrepareTargetCall edge (Graph.target g edge);
          AuditPrepareEncodeCall AuditGraphIncomingGet (Graph.target g edge)
            (encode EV (Graph.target g edge));
          AuditPrepareEncodeCall AuditGraphIncomingSet (Graph.target g edge)
            (encode EV (Graph.target g edge))]).

Inductive audit_graph_prepare_in_execution {V E} (EV : encoding V) (g : Graph.t V E)
    : list V -> Map.t V (list E) -> Map.t V (list E) ->
      list (audit_graph_prepare_call V E) -> Prop :=
  | AuditGraphInNil m : audit_graph_prepare_in_execution EV g [] m m []
  | AuditGraphInCons v rest initial middle final tail_events edge_events :
      audit_graph_prepare_in_execution EV g rest initial middle tail_events ->
      audit_graph_prepare_edges_execution EV g (Graph.out g v) middle final edge_events ->
      audit_graph_prepare_in_execution EV g (v :: rest) initial final
        (tail_events ++ [AuditPrepareOutCall v (Graph.out g v)] ++ edge_events).

Inductive audit_graph_prepare_execution {V E} (EV : encoding V) (g : Graph.t V E)
    : prepared EV g -> list (audit_graph_prepare_call V E) -> Prop :=
  | AuditGraphPrepareRun out incoming out_events in_events :
      audit_graph_prepare_out_execution EV g (Graph.nodes g) Map.empty out out_events ->
      audit_graph_prepare_in_execution EV g (Graph.nodes g) Map.empty incoming in_events ->
      audit_graph_prepare_execution EV g
        (Prepared out incoming (Pos.of_succ_nat (2 * length (Graph.nodes g) + edge_count g + 1)))
        (out_events ++ in_events ++ map (fun v => AuditPrepareOutCall v (Graph.out g v))
          (rev (Graph.nodes g))).

Fixpoint audit_graph_prepare_out_counted {V E} (EV : encoding V) (g : Graph.t V E)
    (nodes : list V) (initial : Map.t V (list E))
    : Map.t V (list E) * list (audit_graph_prepare_call V E) :=
  match nodes with
  | [] => (initial, [])
  | v :: rest =>
      let '(middle, events) := audit_graph_prepare_out_counted EV g rest initial in
      let outgoing := Graph.out g v in
      let code := encode EV v in
      let next := Trie.set code (v, outgoing) middle in
      (next, events ++ [AuditPrepareOutCall v outgoing; AuditPrepareEncodeCall AuditGraphOutSet v
  code])
  end.

Fixpoint audit_graph_prepare_edges_counted {V E} (EV : encoding V) (g : Graph.t V E)
    (edges : list E) (initial : Map.t V (list E))
    : Map.t V (list E) * list (audit_graph_prepare_call V E) :=
  match edges with
  | [] => (initial, [])
  | edge :: rest =>
      let '(middle, events) := audit_graph_prepare_edges_counted EV g rest initial in
      let write_target := Graph.target g edge in
      let read_target := Graph.target g edge in
      let read_code := encode EV read_target in
      let found := Map.code_get read_code middle in
      let row := match found with Some xs => xs | None => [] end in
      let write_code := encode EV write_target in
      let next := Trie.set write_code (write_target, edge :: row) middle in
      (next, events ++ [AuditPrepareTargetCall edge write_target; AuditPrepareTargetCall edge
  read_target;
        AuditPrepareEncodeCall AuditGraphIncomingGet read_target read_code;
        AuditPrepareEncodeCall AuditGraphIncomingSet write_target write_code])
  end.

Fixpoint audit_graph_prepare_in_counted {V E} (EV : encoding V) (g : Graph.t V E)
    (nodes : list V) (initial : Map.t V (list E))
    : Map.t V (list E) * list (audit_graph_prepare_call V E) :=
  match nodes with
  | [] => (initial, [])
  | v :: rest =>
      let '(middle, tail_events) := audit_graph_prepare_in_counted EV g rest initial in
      let outgoing := Graph.out g v in
      let '(next, edge_events) := audit_graph_prepare_edges_counted EV g outgoing middle in
      (next, tail_events ++ [AuditPrepareOutCall v outgoing] ++ edge_events)
  end.

Fixpoint audit_graph_edge_count_counted {V E} (g : Graph.t V E) (nodes : list V)
    : nat * list (audit_graph_prepare_call V E) :=
  match nodes with
  | [] => (0, [])
  | v :: rest =>
      let '(later, events) := audit_graph_edge_count_counted g rest in
      let outgoing := Graph.out g v in
      (length outgoing + later, events ++ [AuditPrepareOutCall v outgoing])
  end.

Definition audit_graph_prepare_counted {V E} (EV : encoding V) (g : Graph.t V E)
    : prepared EV g * list (audit_graph_prepare_call V E) :=
  let '(outgoing, out_events) := audit_graph_prepare_out_counted EV g (Graph.nodes g) Map.empty in
  let '(incoming, in_events) := audit_graph_prepare_in_counted EV g (Graph.nodes g) Map.empty in
  let '(edges, edge_events) := audit_graph_edge_count_counted g (Graph.nodes g) in
  (Prepared outgoing incoming (Pos.of_succ_nat (2 * length (Graph.nodes g) + edges + 1)),
   out_events ++ in_events ++ edge_events).

Definition audit_graph_prepare_execution_exists_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E),
    exists result events, audit_graph_prepare_execution EV g result events /\
      result = prepare EV g.

Definition audit_graph_prepare_callbacks_statement
    (traced : forall {V E} (EV : encoding V) (g : Graph.t V E),
      prepared EV g * list (audit_graph_prepare_call V E)) : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E),
    let '(result, events) := traced EV g in
    audit_graph_prepare_execution EV g result events /\
    result = prepare EV g /\
    Permutation events (audit_graph_prepare_calls EV g) /\
    length events = audit_graph_prepare_callback_count g.

Definition audit_graph_prepare_map_model_event {V E} (event : audit_graph_prepare_call V E) : nat :=
  match event with
  | AuditPrepareEncodeCall AuditGraphIncomingGet _ code => audit_get_weight code
  | AuditPrepareEncodeCall _ _ code => audit_set_weight code
  | _ => 0
  end.

Definition audit_graph_prepare_map_model_work {V E} (events : list (audit_graph_prepare_call V E))
    : nat := fold_right (fun event n => audit_graph_prepare_map_model_event event + n) 0 events.

Definition audit_graph_prepare_map_model_expected {V E} (EV : encoding V) (g : Graph.t V E)
    : nat :=
  fold_right (fun v total =>
    audit_set_weight (encode EV v) +
    fold_right (fun edge subtotal =>
      audit_get_weight (encode EV (Graph.target g edge)) +
      audit_set_weight (encode EV (Graph.target g edge)) + subtotal)
      total (Graph.out g v)) 0 (Graph.nodes g).

Definition audit_graph_prepare_map_model_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) result events,
    audit_graph_prepare_execution EV g result events ->
    audit_graph_prepare_map_model_work events = audit_graph_prepare_map_model_expected EV g.

Definition audit_graph_prepare_emission_event {V E} (event : audit_graph_prepare_call V E) : nat :=
  match event with
  | AuditPrepareEncodeCall _ _ code => audit_encoding_weight (audit_key_bits_weight code)
  | _ => 0
  end.

Definition audit_graph_prepare_emission_work {V E} (events : list (audit_graph_prepare_call V E))
    : nat := fold_right (fun event n => audit_graph_prepare_emission_event event + n) 0 events.

Definition audit_graph_prepare_emission_expected {V E} (EV : encoding V) (g : Graph.t V E)
    : nat :=
  fold_right (fun v total =>
    audit_encoding_weight (audit_key_bits_weight (encode EV v)) +
    fold_right (fun edge subtotal =>
      2 * audit_encoding_weight (audit_key_bits_weight (encode EV (Graph.target g edge))) +
  subtotal)
      total (Graph.out g v)) 0 (Graph.nodes g).

Definition audit_graph_prepare_emission_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) result events,
    audit_graph_prepare_execution EV g result events ->
    audit_graph_prepare_emission_work events = audit_graph_prepare_emission_expected EV g.

Definition audit_graph_prepare_input_width {V E} (EV : encoding V) (g : Graph.t V E) : nat :=
  fold_right (fun v width => Nat.max (audit_key_bits_weight (encode EV v))
    (fold_right (fun edge more => Nat.max (audit_key_bits_weight (encode EV (Graph.target g edge)))
  more)
      width (Graph.out g v))) 0 (Graph.nodes g).

Definition audit_graph_prepare_input_budget {V E} (EV : encoding V) (g : Graph.t V E) : nat :=
  let n := length (Graph.nodes g) in
  let m := edge_count g in
  let events := 4 * n + 4 * m in
  let fuel_input := 2 * n + m + 1 in
  64 * S (events + fuel_input) * S (events + fuel_input) +
    events * (66 + 3 * audit_graph_prepare_input_width EV g) +
    audit_unary_conversion_weight fuel_input + fuel_input * Pos.size_nat (Pos.of_succ_nat
  fuel_input).

Definition audit_graph_prepare_model_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E),
    let '(result, events) := audit_graph_prepare_counted EV g in
    audit_graph_prepare_execution EV g result events /\
    result = prepare EV g /\
    length events = audit_graph_prepare_callback_count g /\
    audit_graph_prepare_map_model_work events + audit_graph_prepare_emission_work events <=
      audit_graph_prepare_input_budget EV g.






Inductive audit_graph_full_call (V E : Type) : Type :=
| AuditGraphFullCase (site : nat)
| AuditGraphFullCall (call : audit_graph_prepare_call V E)
| AuditGraphFullLength (edges : list E) (result : nat)
| AuditGraphFullNodesLength (nodes : list V) (result : nat)
| AuditGraphFullFuel (nodes edges : nat) (result : positive).
Arguments AuditGraphFullCase {V E} _.
Arguments AuditGraphFullCall {V E} _.
Arguments AuditGraphFullLength {V E} _ _.
Arguments AuditGraphFullNodesLength {V E} _ _.
Arguments AuditGraphFullFuel {V E} _ _ _.

Fixpoint audit_graph_full_out {V E} (EV : encoding V) (g : Graph.t V E)
    (nodes : list V) (initial : Map.t V (list E))
    : Map.t V (list E) * list (audit_graph_full_call V E) :=
  match nodes with
  | [] => (initial, [AuditGraphFullCase 0])
  | v :: rest =>
      let '(middle, events) := audit_graph_full_out EV g rest initial in
      let outgoing := Graph.out g v in let code := encode EV v in
      let next := Trie.set code (v, outgoing) middle in
      (next, AuditGraphFullCase 1 :: events ++
        [AuditGraphFullCall (AuditPrepareOutCall v outgoing);
         AuditGraphFullCall (AuditPrepareEncodeCall AuditGraphOutSet v code)])
  end.

Fixpoint audit_graph_full_edges {V E} (EV : encoding V) (g : Graph.t V E)
    (edges : list E) (initial : Map.t V (list E))
    : Map.t V (list E) * list (audit_graph_full_call V E) :=
  match edges with
  | [] => (initial, [AuditGraphFullCase 2])
  | edge :: rest =>
      let '(middle, events) := audit_graph_full_edges EV g rest initial in
      let write_target := Graph.target g edge in let read_target := Graph.target g edge in
      let read_code := encode EV read_target in let found := Map.code_get read_code middle in
      let row := match found with Some xs => xs | None => [] end in
      let write_code := encode EV write_target in
      let next := Trie.set write_code (write_target, edge :: row) middle in
      (next, AuditGraphFullCase 3 :: events ++
        [AuditGraphFullCall (AuditPrepareTargetCall edge write_target);
         AuditGraphFullCall (AuditPrepareTargetCall edge read_target);
         AuditGraphFullCall (AuditPrepareEncodeCall AuditGraphIncomingGet read_target read_code);
         AuditGraphFullCase (match found with Some _ => 4 | None => 5 end);
         AuditGraphFullCall (AuditPrepareEncodeCall AuditGraphIncomingSet write_target write_code)])
  end.

Fixpoint audit_graph_full_in {V E} (EV : encoding V) (g : Graph.t V E)
    (nodes : list V) (initial : Map.t V (list E))
    : Map.t V (list E) * list (audit_graph_full_call V E) :=
  match nodes with
  | [] => (initial, [AuditGraphFullCase 6])
  | v :: rest => let '(middle, tail_events) := audit_graph_full_in EV g rest initial in
      let outgoing := Graph.out g v in
      let '(next, edge_events) := audit_graph_full_edges EV g outgoing middle in
      (next, AuditGraphFullCase 7 :: tail_events ++
        [AuditGraphFullCall (AuditPrepareOutCall v outgoing)] ++ edge_events)
  end.

Fixpoint audit_graph_full_edge_count {V E} (g : Graph.t V E) (nodes : list V)
    : nat * list (audit_graph_full_call V E) :=
  match nodes with
  | [] => (0, [AuditGraphFullCase 8])
  | v :: rest => let '(later, events) := audit_graph_full_edge_count g rest in
      let outgoing := Graph.out g v in let len := length outgoing in
      (len + later, AuditGraphFullCase 9 :: events ++
        [AuditGraphFullCall (AuditPrepareOutCall v outgoing); AuditGraphFullLength outgoing len])
  end.

Definition audit_graph_prepare_full_counted {V E} (EV : encoding V) (g : Graph.t V E)
    : prepared EV g * list (audit_graph_full_call V E) :=
  let '(outgoing, out_events) := audit_graph_full_out EV g (Graph.nodes g) Map.empty in
  let '(incoming, in_events) := audit_graph_full_in EV g (Graph.nodes g) Map.empty in
  let nodes := length (Graph.nodes g) in
  let '(edges, edge_events) := audit_graph_full_edge_count g (Graph.nodes g) in
  let fuel := Pos.of_succ_nat (2 * nodes + edges + 1) in
  (Prepared outgoing incoming fuel, out_events ++ in_events ++
    [AuditGraphFullNodesLength (Graph.nodes g) nodes] ++ edge_events ++
    [AuditGraphFullFuel nodes edges fuel]).

Definition audit_graph_full_event_work {V E} (event : audit_graph_full_call V E) : nat :=
  64 + match event with
  | AuditGraphFullCall call => audit_graph_prepare_map_model_event call +
  audit_graph_prepare_emission_event call
  | AuditGraphFullLength edges _ => 2 * S (length edges)
  | AuditGraphFullNodesLength nodes _ => S (length nodes)
  | AuditGraphFullFuel nodes edges fuel =>
      let amount := 2 * nodes + edges + 1 in
      32 * S amount * S amount + audit_unary_conversion_weight amount +
        amount * audit_key_bits_weight fuel
  | AuditGraphFullCase _ => 0
  end.

Definition audit_graph_prepare_full_work {V E} (events : list (audit_graph_full_call V E)) : nat :=
  64 * S (length events) * S (length events) +
    fold_right (fun event total => audit_graph_full_event_work event + total) 0 events.

Definition audit_graph_prepare_full_event_bound {V E} (g : Graph.t V E) : nat :=
  8 + 12 * length (Graph.nodes g) + 8 * edge_count g.

Definition audit_graph_prepare_full_budget {V E} (EV : encoding V) (g : Graph.t V E) : nat :=
  let count := audit_graph_prepare_full_event_bound g in
  let amount := 2 * length (Graph.nodes g) + edge_count g + 1 in
  128 * S count * S count + count * (128 + 3 * audit_graph_prepare_input_width EV g) +
    64 * S amount * S amount + amount * audit_key_bits_weight (Pos.of_succ_nat amount).

Definition audit_graph_prepare_full_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E),
    let '(result, events) := audit_graph_prepare_full_counted EV g in
    result = prepare EV g /\
    length events <= audit_graph_prepare_full_event_bound g /\
    audit_graph_prepare_full_work events <= audit_graph_prepare_full_budget EV g.


Record audit_prepare_callback_model (V E B : Type) : Type := AuditPrepareCallbackModel {
  audit_prepare_out_model : V -> list E * list B;
  audit_prepare_target_model : E -> V * list B;
  audit_prepare_encode_model : V -> positive * list B
}.
Arguments audit_prepare_out_model {V E B} _ _.
Arguments audit_prepare_target_model {V E B} _ _.
Arguments audit_prepare_encode_model {V E B} _ _.

Definition audit_prepare_callbacks_erase {V E B} (EV : encoding V) (g : Graph.t V E)
    (cb : audit_prepare_callback_model V E B) : Prop :=
  (forall v, fst (audit_prepare_out_model cb v) = Graph.out g v) /\
  (forall e, fst (audit_prepare_target_model cb e) = Graph.target g e) /\
  (forall v, fst (audit_prepare_encode_model cb v) = encode EV v).

Definition audit_prepare_nested_event (V E B : Type) : Type := audit_graph_full_call V E * list B.

Fixpoint audit_prepare_nested_out {V E B} (g : Graph.t V E) (cb : audit_prepare_callback_model V E
  B)
    (nodes : list V) (initial : Map.t V (list E))
    : Map.t V (list E) * list (audit_prepare_nested_event V E B) :=
  match nodes with
  | [] => (initial, [(AuditGraphFullCase 0, [])])
  | v :: rest => let '(middle, events) := audit_prepare_nested_out g cb rest initial in
      let '(outgoing, out_body) := audit_prepare_out_model cb v in
      let '(code, encode_body) := audit_prepare_encode_model cb v in
      let next := Trie.set code (v, outgoing) middle in
      (next, (AuditGraphFullCase 1, []) :: events ++
        [(AuditGraphFullCall (AuditPrepareOutCall v outgoing), out_body);
         (AuditGraphFullCall (AuditPrepareEncodeCall AuditGraphOutSet v code), encode_body)])
  end.

Fixpoint audit_prepare_nested_edges {V E B} (g : Graph.t V E) (cb : audit_prepare_callback_model V E
  B)
    (edges : list E) (initial : Map.t V (list E))
    : Map.t V (list E) * list (audit_prepare_nested_event V E B) :=
  match edges with
  | [] => (initial, [(AuditGraphFullCase 2, [])])
  | edge :: rest => let '(middle, events) := audit_prepare_nested_edges g cb rest initial in
      let '(write_target, write_target_body) := audit_prepare_target_model cb edge in
      let '(read_target, read_target_body) := audit_prepare_target_model cb edge in
      let '(read_code, read_body) := audit_prepare_encode_model cb read_target in
      let found := Map.code_get read_code middle in
      let row := match found with Some xs => xs | None => [] end in
      let '(write_code, write_body) := audit_prepare_encode_model cb write_target in
      let next := Trie.set write_code (write_target, edge :: row) middle in
      (next, (AuditGraphFullCase 3, []) :: events ++
        [(AuditGraphFullCall (AuditPrepareTargetCall edge write_target), write_target_body);
         (AuditGraphFullCall (AuditPrepareTargetCall edge read_target), read_target_body);
         (AuditGraphFullCall (AuditPrepareEncodeCall AuditGraphIncomingGet read_target read_code),
  read_body);
         (AuditGraphFullCase (match found with Some _ => 4 | None => 5 end), []);
         (AuditGraphFullCall (AuditPrepareEncodeCall AuditGraphIncomingSet write_target write_code),
  write_body)])
  end.

Fixpoint audit_prepare_nested_in {V E B} (g : Graph.t V E) (cb : audit_prepare_callback_model V E B)
    (nodes : list V) (initial : Map.t V (list E))
    : Map.t V (list E) * list (audit_prepare_nested_event V E B) :=
  match nodes with
  | [] => (initial, [(AuditGraphFullCase 6, [])])
  | v :: rest => let '(middle, tail_events) := audit_prepare_nested_in g cb rest initial in
      let '(outgoing, body) := audit_prepare_out_model cb v in
      let '(next, edge_events) := audit_prepare_nested_edges g cb outgoing middle in
      (next, (AuditGraphFullCase 7, []) :: tail_events ++
        [(AuditGraphFullCall (AuditPrepareOutCall v outgoing), body)] ++ edge_events)
  end.

Fixpoint audit_prepare_nested_edge_count {V E B} (g : Graph.t V E)
    (cb : audit_prepare_callback_model V E B) (nodes : list V)
    : nat * list (audit_prepare_nested_event V E B) :=
  match nodes with
  | [] => (0, [(AuditGraphFullCase 8, [])])
  | v :: rest => let '(later, events) := audit_prepare_nested_edge_count g cb rest in
      let '(outgoing, body) := audit_prepare_out_model cb v in let len := length outgoing in
      (len + later, (AuditGraphFullCase 9, []) :: events ++
        [(AuditGraphFullCall (AuditPrepareOutCall v outgoing), body); (AuditGraphFullLength outgoing
  len, [])])
  end.

Definition audit_graph_prepare_nested_counted {V E B} (EV : encoding V) (g : Graph.t V E)
    (cb : audit_prepare_callback_model V E B)
    : prepared EV g * list (audit_prepare_nested_event V E B) :=
  let '(outgoing, out_events) := audit_prepare_nested_out g cb (Graph.nodes g) Map.empty in
  let '(incoming, in_events) := audit_prepare_nested_in g cb (Graph.nodes g) Map.empty in
  let nodes := length (Graph.nodes g) in
  let '(edges, edge_events) := audit_prepare_nested_edge_count g cb (Graph.nodes g) in
  let fuel := Pos.of_succ_nat (2 * nodes + edges + 1) in
  (Prepared outgoing incoming fuel, out_events ++ in_events ++
    [(AuditGraphFullNodesLength (Graph.nodes g) nodes, [])] ++ edge_events ++
    [(AuditGraphFullFuel nodes edges fuel, [])]).

Definition audit_prepare_nested_body_work {V E B} (weight : B -> nat)
    (events : list (audit_prepare_nested_event V E B)) : nat :=
  fold_right (fun event total => fold_right (fun item n => weight item + n) 0 (snd event) + total) 0
  events.

Definition audit_graph_prepare_nested_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (cb : audit_prepare_callback_model V E B),
    audit_prepare_callbacks_erase EV g cb ->
    let '(result, events) := audit_graph_prepare_nested_counted EV g cb in
    result = prepare EV g /\
    map fst events = snd (audit_graph_prepare_full_counted EV g) /\
    length events <= audit_graph_prepare_full_event_bound g /\
    audit_graph_prepare_full_work (map fst events) <= audit_graph_prepare_full_budget EV g.

Definition audit_graph_prepare_nested_total_work {V E B} (weight : B -> nat)
    (events : list (audit_prepare_nested_event V E B)) : nat :=
  audit_graph_prepare_full_work (map fst events) + audit_prepare_nested_body_work weight events.

From Stdlib Require Import List Bool PArith NArith.
Import List.ListNotations.

Inductive audit_comb_event (C : Type) : Type :=
| AuditCombCase (site : nat)
| AuditCombBody (event : C).
Arguments AuditCombCase {C} _.
Arguments AuditCombBody {C} _.

Definition audit_comb_call_count {C} (events : list (audit_comb_event C)) : nat :=
  fold_right (fun event n => match event with AuditCombCase 0 => S n | _ => n end) 0 events.

Fixpoint audit_pos_iter {A C} (step : A -> A * list C) (x : A) (fuel : positive)
    : A * list (audit_comb_event C) :=
  match fuel with
  | xH => let '(result, events) := step x in
      (result, AuditCombCase 0 :: map AuditCombBody events)
  | xO rest => let '(middle, first) := audit_pos_iter step x rest in
      let '(result, second) := audit_pos_iter step middle rest in
      (result, AuditCombCase 1 :: first ++ second)
  | xI rest => let '(middle, first) := audit_pos_iter step x rest in
      let '(last, second) := audit_pos_iter step middle rest in
      let '(result, events) := step last in
      (result, AuditCombCase 2 :: first ++ second ++ AuditCombCase 0 :: map AuditCombBody events)
  end.

Definition audit_n_iter {A C} (fuel : N) (step : A -> A * list C) (x : A)
    : A * list (audit_comb_event C) :=
  match fuel with
  | N0 => (x, [AuditCombCase 3])
  | Npos p => let '(result, events) := audit_pos_iter step x p in
      (result, AuditCombCase 4 :: events)
  end.

Fixpoint audit_fold_left {A S C} (step : S -> A -> S * list C) (xs : list A) (initial : S)
    : S * list (audit_comb_event C) :=
  match xs with
  | [] => (initial, [AuditCombCase 5])
  | a :: rest => let '(next, body) := step initial a in
      let '(result, events) := audit_fold_left step rest next in
      (result, AuditCombCase 6 :: map AuditCombBody body ++ events)
  end.

Fixpoint audit_fold_right {A S C} (step : A -> S -> S * list C) (xs : list A) (initial : S)
    : S * list (audit_comb_event C) :=
  match xs with
  | [] => (initial, [AuditCombCase 7])
  | a :: rest => let '(middle, events) := audit_fold_right step rest initial in
      let '(result, body) := step a middle in
      (result, AuditCombCase 8 :: events ++ map AuditCombBody body)
  end.

Fixpoint audit_map {A B C} (f : A -> B * list C) (xs : list A)
    : list B * list (audit_comb_event C) :=
  match xs with
  | [] => ([], [AuditCombCase 9])
  | a :: rest => let '(b, body) := f a in
      let '(later, events) := audit_map f rest in
      (b :: later, AuditCombCase 10 :: map AuditCombBody body ++ events)
  end.

Fixpoint audit_filter {A C} (f : A -> bool * list C) (xs : list A)
    : list A * list (audit_comb_event C) :=
  match xs with
  | [] => ([], [AuditCombCase 11])
  | a :: rest => let '(keep, body) := f a in
      let '(later, events) := audit_filter f rest in
      ((if keep then a :: later else later),
       AuditCombCase 12 :: map AuditCombBody body ++ AuditCombCase (if keep then 13 else 14) ::
  events)
  end.

Fixpoint audit_existsb_strict {A C} (f : A -> bool * list C) (xs : list A)
    : bool * list (audit_comb_event C) :=
  match xs with
  | [] => (false, [AuditCombCase 15])
  | a :: rest => let '(here, body) := f a in
      let '(later, events) := audit_existsb_strict f rest in
      (here || later, AuditCombCase 16 :: map AuditCombBody body ++ events)
  end.

Definition audit_pos_iter_statement : Prop :=
  forall A C (step : A -> A * list C) (f : A -> A) x fuel,
    (forall a, fst (step a) = f a) ->
    let '(result, events) := audit_pos_iter step x fuel in
    result = Pos.iter f x fuel /\ audit_comb_call_count events = Pos.to_nat fuel.

Definition audit_n_iter_statement : Prop :=
  forall A C (step : A -> A * list C) (f : A -> A) x fuel,
    (forall a, fst (step a) = f a) ->
    let '(result, events) := audit_n_iter fuel step x in
    result = N.iter fuel f x /\ audit_comb_call_count events = N.to_nat fuel.

Definition audit_fold_statement : Prop :=
  (forall A S C (step : S -> A -> S * list C) (f : S -> A -> S) xs initial,
    (forall s a, fst (step s a) = f s a) ->
    fst (audit_fold_left step xs initial) = fold_left f xs initial) /\
  (forall A S C (step : A -> S -> S * list C) (f : A -> S -> S) xs initial,
    (forall a s, fst (step a s) = f a s) ->
    fst (audit_fold_right step xs initial) = fold_right f initial xs).

Definition audit_list_map_filter_exists_statement : Prop :=
  (forall A B C (step : A -> B * list C) (f : A -> B) xs,
    (forall a, fst (step a) = f a) -> fst (audit_map step xs) = map f xs) /\
  (forall A C (step : A -> bool * list C) (f : A -> bool) xs,
    (forall a, fst (step a) = f a) -> fst (audit_filter step xs) = filter f xs) /\
  (forall A C (step : A -> bool * list C) (f : A -> bool) xs,
    (forall a, fst (step a) = f a) -> fst (audit_existsb_strict step xs) = existsb f xs).


(** Source work for the pinned naive [List.rev] and its append frames. *)
Fixpoint audit_graph_reverse_work (size : nat) : nat :=
  match size with
  | 0 => 1
  | S rest => 3 + rest + audit_graph_reverse_work rest
  end.

Inductive audit_graph_reverse_run {A} : list A -> list A -> nat -> Prop :=
| GraphReverseNil : audit_graph_reverse_run [] [] 1
| GraphReverseCons x xs reversed work :
    audit_graph_reverse_run xs reversed work ->
    audit_graph_reverse_run (x :: xs) (reversed ++ [x]) (3 + length reversed + work).

Definition audit_graph_reverse_run_statement : Prop :=
  forall A (xs : list A), exists result work,
    audit_graph_reverse_run xs result work /\ result = rev xs /\
    work = audit_graph_reverse_work (length xs) /\ work <= 4 * S (length xs) * S (length xs).

(** The selected source body uses the standard tail-recursive [rev_append]. *)
Definition audit_graph_reverse_fast_work (size : nat) : nat := 1 + 2 * size.

Fixpoint audit_graph_reverse_fast_counted {A} (xs acc : list A) : list A * nat :=
  match xs with
  | [] => (acc, 1)
  | x :: rest => let '(result, work) := audit_graph_reverse_fast_counted rest (x :: acc) in
      (result, 2 + work)
  end.

Inductive audit_graph_reverse_fast_run {A} : list A -> list A -> list A -> nat -> Prop :=
| GraphReverseFastNil acc : audit_graph_reverse_fast_run [] acc acc 1
| GraphReverseFastCons x xs acc result work :
    audit_graph_reverse_fast_run xs (x :: acc) result work ->
    audit_graph_reverse_fast_run (x :: xs) acc result (2 + work).

Definition audit_graph_reverse_fast_run_statement : Prop :=
  forall A (xs acc : list A), exists result work,
    audit_graph_reverse_fast_run xs acc result work /\ result = rev_append xs acc /\
    result = rev xs ++ acc /\ work = audit_graph_reverse_fast_work (length xs).

Definition audit_graph_reverse_fast_counted_statement : Prop :=
  forall A (xs acc : list A),
    let '(result, work) := audit_graph_reverse_fast_counted xs acc in
    audit_graph_reverse_fast_run xs acc result work /\ result = rev_append xs acc /\
    result = rev xs ++ acc /\ work = audit_graph_reverse_fast_work (length xs).

(** A reusable source/budget law only for genuinely external callback bodies. *)
Record audit_graph_external_callback_adapter {A R B} (call : A -> R * list B) (weight : B -> nat)
    (source : A -> R -> list B -> nat -> Prop) (budget : A -> nat) : Prop := {
  audit_graph_external_callback_source : forall arg result body,
    call arg = (result, body) ->
    source arg result body (fold_right (fun item n => weight item + n) 0 body) /\
    fold_right (fun item n => weight item + n) 0 body <= budget arg
}.

From Galois.Collections Require Import CollectionsAuditMap.
Inductive audit_prepare_source_event (V E B : Type) : Type :=
| PrepareSourceCase : nat -> audit_prepare_source_event V E B
| PrepareSourceOut : V -> list E -> list B -> audit_prepare_source_event V E B
| PrepareSourceTarget : E -> V -> list B -> audit_prepare_source_event V E B
| PrepareSourceMap : audit_map_event V (list E) B -> audit_prepare_source_event V E B
| PrepareSourceLength : nat -> audit_prepare_source_event V E B
| PrepareSourceFuel : nat -> nat -> positive -> audit_prepare_source_event V E B.
Arguments PrepareSourceCase {V E B} _.
Arguments PrepareSourceOut {V E B} _ _ _.
Arguments PrepareSourceTarget {V E B} _ _ _.
Arguments PrepareSourceMap {V E B} _.
Arguments PrepareSourceLength {V E B} _.
Arguments PrepareSourceFuel {V E B} _ _ _.

Fixpoint audit_prepare_source_out {V E B} (cb : audit_prepare_callback_model V E B)
    (nodes : list V) (initial : Map.t V (list E)) : Map.t V (list E) * list
  (audit_prepare_source_event V E B) :=
  match nodes with
  | [] => (initial, [PrepareSourceCase 0])
  | v :: rest => let '(middle, events) := audit_prepare_source_out cb rest initial in
      let '(outgoing, body) := audit_prepare_out_model cb v in
      let '(next, writes) := audit_map_set (audit_prepare_encode_model cb) v outgoing middle in
      (next, PrepareSourceCase 1 :: events ++ [PrepareSourceOut v outgoing body] ++ map
  PrepareSourceMap writes)
  end.

Fixpoint audit_prepare_source_edges {V E B} (cb : audit_prepare_callback_model V E B)
    (edges : list E) (initial : Map.t V (list E)) : Map.t V (list E) * list
  (audit_prepare_source_event V E B) :=
  match edges with
  | [] => (initial, [PrepareSourceCase 2])
  | edge :: rest => let '(middle, events) := audit_prepare_source_edges cb rest initial in
      let '(write_target, write_body) := audit_prepare_target_model cb edge in
      let '(read_target, read_body) := audit_prepare_target_model cb edge in
      let '(found, reads) := audit_map_get (audit_prepare_encode_model cb) read_target middle in
      let row := match found with Some xs => xs | None => [] end in
      let '(next, writes) := audit_map_set (audit_prepare_encode_model cb) write_target (edge ::
  row) middle in
      (next, PrepareSourceCase 3 :: events ++
        [PrepareSourceTarget edge write_target write_body; PrepareSourceTarget edge read_target
  read_body] ++
        map PrepareSourceMap reads ++ [PrepareSourceCase (match found with Some _ => 4 | None => 5
  end)] ++
        map PrepareSourceMap writes)
  end.

Fixpoint audit_prepare_source_in {V E B} (cb : audit_prepare_callback_model V E B)
    (nodes : list V) (initial : Map.t V (list E)) : Map.t V (list E) * list
  (audit_prepare_source_event V E B) :=
  match nodes with
  | [] => (initial, [PrepareSourceCase 6])
  | v :: rest => let '(middle, later) := audit_prepare_source_in cb rest initial in
      let '(outgoing, body) := audit_prepare_out_model cb v in
      let '(result, edges) := audit_prepare_source_edges cb outgoing middle in
      (result, PrepareSourceCase 7 :: later ++ [PrepareSourceOut v outgoing body] ++ edges)
  end.

Fixpoint audit_prepare_source_edge_count {V E B} (cb : audit_prepare_callback_model V E B)
    (nodes : list V) : nat * list (audit_prepare_source_event V E B) :=
  match nodes with
  | [] => (0, [PrepareSourceCase 8])
  | v :: rest => let '(later, events) := audit_prepare_source_edge_count cb rest in
      let '(outgoing, body) := audit_prepare_out_model cb v in
      (length outgoing + later, PrepareSourceCase 9 :: events ++
        [PrepareSourceOut v outgoing body; PrepareSourceLength (length outgoing)])
  end.

Definition audit_prepare_source_counted {V E B} (EV : encoding V) (g : Graph.t V E)
    (cb : audit_prepare_callback_model V E B) : prepared EV g * list (audit_prepare_source_event V E
  B) :=
  let '(outgoing, out_events) := audit_prepare_source_out cb (Graph.nodes g) Map.empty in
  let '(incoming, in_events) := audit_prepare_source_in cb (Graph.nodes g) Map.empty in
  let nodes := length (Graph.nodes g) in
  let '(edges, edge_events) := audit_prepare_source_edge_count cb (Graph.nodes g) in
  let fuel := Pos.of_succ_nat (2 * nodes + edges + 1) in
  (Prepared outgoing incoming fuel, out_events ++ in_events ++ [PrepareSourceLength nodes] ++
  edge_events ++
    [PrepareSourceFuel nodes edges fuel]).

Definition audit_prepare_source_event_work {V E B} (weight : B -> nat) (event :
  audit_prepare_source_event V E B) : nat :=
  let body := fun events => fold_right (fun item n => weight item + n) 0 events in
  64 + match event with
  | PrepareSourceOut _ _ events | PrepareSourceTarget _ _ events => body events
  | PrepareSourceMap item => audit_map_source_work body [item]
  | PrepareSourceLength n => 2 * S n
  | PrepareSourceFuel nodes edges fuel =>
      let amount := 2 * nodes + edges + 1 in
      32 * S amount * S amount + audit_unary_conversion_weight amount + amount * Pos.size_nat fuel
  | PrepareSourceCase _ => 0
  end.

Definition audit_prepare_source_body_event_work {V E B} (weight : B -> nat)
    (event : audit_prepare_source_event V E B) : nat :=
  match event with
  | PrepareSourceOut _ _ body | PrepareSourceTarget _ _ body |
    PrepareSourceMap (AuditMapGet _ _ _ _ body _) | PrepareSourceMap (AuditMapSet _ _ _ _ _ body _)
  |
    PrepareSourceMap (AuditMapRemove _ _ _ _ body _) => fold_right (fun item n => weight item + n) 0
  body
  | PrepareSourceCase _ | PrepareSourceLength _ | PrepareSourceFuel _ _ _ => 0
  end.

Definition audit_prepare_source_work {V E B} (weight : B -> nat) (events : list
  (audit_prepare_source_event V E B)) : nat :=
  fold_right (fun item n => audit_prepare_source_event_work weight item + n) 0 events.

Definition audit_prepare_source_body_work {V E B} (weight : B -> nat) (events : list
  (audit_prepare_source_event V E B)) : nat :=
  fold_right (fun item n => audit_prepare_source_body_event_work weight item + n) 0 events.

Definition audit_prepare_source_budget {V E} (EV : encoding V) (g : Graph.t V E) : nat :=
  let count := audit_graph_prepare_full_event_bound g in
  let width := audit_graph_prepare_input_width EV g in
  let amount := 2 * length (Graph.nodes g) + edge_count g + 1 in
  1024 * S count * S count + count * (512 + 64 * width) +
    64 * S amount * S amount + amount * Pos.size_nat (Pos.of_succ_nat amount).

Definition audit_prepare_source_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (cb : audit_prepare_callback_model V E B) (weight
  : B -> nat),
    audit_prepare_callbacks_erase EV g cb ->
    let '(result, events) := audit_prepare_source_counted EV g cb in
    result = prepare EV g /\ length events <= audit_graph_prepare_full_event_bound g /\
    audit_prepare_source_work weight events <= audit_prepare_source_budget EV g +
  audit_prepare_source_body_work weight events.

Definition audit_prepare_source_event_budget {V E B} (encode_budget out_budget : V -> nat)
    (target_budget : E -> nat) (event : audit_prepare_source_event V E B) : nat :=
  match event with
  | PrepareSourceOut v _ _ => out_budget v
  | PrepareSourceTarget e _ _ => target_budget e
  | PrepareSourceMap (AuditMapGet key _ _ _ _ _) | PrepareSourceMap (AuditMapSet key _ _ _ _ _ _) |
    PrepareSourceMap (AuditMapRemove key _ _ _ _ _) => encode_budget key
  | PrepareSourceCase _ | PrepareSourceLength _ | PrepareSourceFuel _ _ _ => 0
  end.

Definition audit_prepare_source_adapted_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (cb : audit_prepare_callback_model V E B) (weight
  : B -> nat)
    encode_source out_source target_source encode_budget out_budget target_budget,
    audit_prepare_callbacks_erase EV g cb ->
    audit_graph_external_callback_adapter (audit_prepare_encode_model cb) weight encode_source
  encode_budget ->
    audit_graph_external_callback_adapter (audit_prepare_out_model cb) weight out_source out_budget
  ->
    audit_graph_external_callback_adapter (audit_prepare_target_model cb) weight target_source
  target_budget ->
    let '(result, events) := audit_prepare_source_counted EV g cb in
    result = prepare EV g /\
    audit_prepare_source_work weight events <= audit_prepare_source_budget EV g +
      fold_right (fun event n => audit_prepare_source_event_budget encode_budget out_budget
  target_budget event + n) 0 events.

Definition audit_prepare_source_contract_statement : Prop :=
  audit_prepare_source_statement /\ audit_prepare_source_adapted_statement /\
  audit_map_get_source_work_bound_statement /\ audit_map_set_source_work_bound_statement.
```

## Galois.Graph.GraphAuditDfs

Card: AUD-GR-MODELS

Source destination: `theories/Graph/GraphAuditDfs.v`.

```rocq
From Galois.Collections Require Import CollectionsAuditCost CollectionsTrie.
From Galois.Graph Require Import GraphAuditBase.

From Stdlib Require Import List Bool PArith Arith ZArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditCost.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs.
Import List.ListNotations.

Inductive audit_dfs_call (V E : Type) : Type :=
  | AuditDfsCase (site : nat)
  | AuditDfsTarget (edge : E) (target : V)
  | AuditDfsMember (vertex : V) (set : FinSet.t V) (result : bool)
  | AuditDfsSuccessors (vertex : V) (index : Map.t V (list E)) (result : option (list E))
  | AuditDfsDiscover (vertex : V) (via : option E) (before after : DfsState.t V E)
  | AuditDfsFinish (vertex : V) (before after : DfsState.t V E).
Arguments AuditDfsCase {V E} _.
Arguments AuditDfsTarget {V E} _ _.
Arguments AuditDfsMember {V E} _ _ _.
Arguments AuditDfsSuccessors {V E} _ _ _.
Arguments AuditDfsDiscover {V E} _ _ _ _.
Arguments AuditDfsFinish {V E} _ _ _.

Definition audit_dfs_step_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (blocked : FinSet.t V) (work : dfs_stack V E * DfsState.t V E)
    : (dfs_stack V E * DfsState.t V E) * list (audit_dfs_call V E) :=
  let '(stack, st) := work in
  match stack with
  | [] => (([], st), [AuditDfsCase 0])
  | (v, []) :: rest =>
      let next := dfs_finish EV v st in
      ((rest, next), [AuditDfsCase 1; AuditDfsFinish v st next])
  | (v, e :: es) :: rest =>
      let target := Graph.target g e in
      let is_blocked := FinSet.mem EV target blocked in
      let is_seen := FinSet.mem EV target (DfsState.seen st) in
      if is_blocked || is_seen then
        (((v, es) :: rest, st), [AuditDfsTarget e target;
          AuditDfsMember target blocked is_blocked; AuditDfsMember target (DfsState.seen st)
  is_seen; AuditDfsCase 2])
      else
        let outgoing := Map.get EV target (out_index p) in
        let edges := match outgoing with Some xs => xs | None => [] end in
        let next := dfs_discover EV target (Some e) st in
        (((target, edges) :: (v, es) :: rest, next),
         [AuditDfsTarget e target; AuditDfsMember target blocked is_blocked;
          AuditDfsMember target (DfsState.seen st) is_seen; AuditDfsCase 3; AuditDfsSuccessors
  target (out_index p) outgoing;
          AuditDfsDiscover target (Some e) st next])
  end.

Fixpoint audit_dfs_run_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (blocked : FinSet.t V) (fuel : positive)
    (work : dfs_stack V E * DfsState.t V E)
    : (dfs_stack V E * DfsState.t V E) * list (audit_dfs_call V E) :=
  match fst work with
  | [] => (work, [AuditDfsCase 4])
  | _ :: _ => match fuel with
    | xH => let '(result, events) := audit_dfs_step_counted p blocked work in
        (result, AuditDfsCase 5 :: events)
    | xO rest => let '(middle, first) := audit_dfs_run_counted p blocked rest work in
        let '(result, second) := audit_dfs_run_counted p blocked rest middle in
        (result, AuditDfsCase 6 :: first ++ second)
    | xI rest => let '(middle, first) := audit_dfs_run_counted p blocked rest work in
        let '(last, second) := audit_dfs_run_counted p blocked rest middle in
        let '(result, step_events) := audit_dfs_step_counted p blocked last in
        (result, AuditDfsCase 7 :: first ++ second ++ step_events)
    end
  end.

Definition audit_dfs_root_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (blocked : FinSet.t V) (st : DfsState.t V E) (v : V)
    : DfsState.t V E * list (audit_dfs_call V E) :=
  let is_blocked := FinSet.mem EV v blocked in
  let is_seen := FinSet.mem EV v (DfsState.seen st) in
  if is_blocked || is_seen then
    (st, [AuditDfsMember v blocked is_blocked; AuditDfsMember v (DfsState.seen st) is_seen;
  AuditDfsCase 8])
  else
    let outgoing := Map.get EV v (out_index p) in
    let edges := match outgoing with Some xs => xs | None => [] end in
    let discovered := dfs_discover EV v None st in
    let '(result, events) := audit_dfs_run_counted p blocked (fuel p) ([(v, edges)], discovered) in
    (snd result, [AuditDfsMember v blocked is_blocked;
      AuditDfsMember v (DfsState.seen st) is_seen; AuditDfsCase 9; AuditDfsSuccessors v (out_index
  p) outgoing;
      AuditDfsDiscover v None st discovered] ++ events).

Fixpoint audit_dfs_roots_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (blocked : FinSet.t V) (roots : list V) (st : DfsState.t V E)
    : DfsState.t V E * list (audit_dfs_call V E) :=
  match roots with
  | [] => (st, [AuditDfsCase 10])
  | root :: rest =>
      let '(next, here) := audit_dfs_root_counted p blocked st root in
      let '(result, later) := audit_dfs_roots_counted p blocked rest next in
      (result, AuditDfsCase 11 :: here ++ later)
  end.

Definition audit_dfs_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (blocked : FinSet.t V) (roots : list V)
    : dfs_result V E * list (audit_dfs_call V E) :=
  let '(st, events) := audit_dfs_roots_counted p blocked roots dfs_initial in
  (DfsResult (rev (DfsState.pre st)) (rev (DfsState.post st)) (DfsState.parent st)
    (DfsState.pre_index st) (DfsState.post_index st) (DfsState.seen st), events).

Definition audit_dfs_model_event {V E} (EV : encoding V) (event : audit_dfs_call V E) : nat :=
  let read v := audit_get_weight (encode EV v) + audit_encoding_weight (audit_key_bits_weight
  (encode EV v)) in
  let write v := audit_set_weight (encode EV v) + audit_encoding_weight (audit_key_bits_weight
  (encode EV v)) in
  64 + match event with
  | AuditDfsMember v _ _ | AuditDfsSuccessors v _ _ => read v
  | AuditDfsDiscover v via st _ =>
      (match via with Some _ => 3 | None => 2 end) * write v +
      audit_binary_weight (Z.pos (DfsState.pre_clock st)) 1
  | AuditDfsFinish v st _ => write v + audit_binary_weight (Z.pos (DfsState.post_clock st)) 1
  | _ => 0 end.

Definition audit_dfs_model_work {V E} (EV : encoding V) (events : list (audit_dfs_call V E)) : nat
  :=
  256 * S (length events) * S (length events) +
    fold_right (fun event n => audit_dfs_model_event EV event + n) 0 events.

Definition audit_dfs_input_width {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (roots : list V) : nat :=
  let rows := Map.elements (out_index p) in
  let vertices := roots ++ Graph.nodes g ++ map fst rows ++
    flat_map (fun row => map (Graph.target g) (snd row)) rows in
  fold_right Nat.max 0 (map (fun v => audit_key_bits_weight (encode EV v)) vertices).

Definition audit_dfs_input_event_bound {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (roots : list V) : nat :=
  2 + length roots * (16 * S (Pos.to_nat (fuel p))).

Definition audit_dfs_input_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (roots : list V) : nat :=
  let events := audit_dfs_input_event_bound p roots in
  let clock_width := audit_key_bits_weight (Pos.of_succ_nat (2 + length roots * S (Pos.to_nat (fuel
  p)))) in
  let width := Nat.max (audit_dfs_input_width EV g p roots) clock_width in
  256 * S events * S events + events * (80 + 12 * width).

Definition audit_dfs_counted_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) blocked roots,
    let '(result, events) := audit_dfs_counted p blocked roots in
    result = dfs p blocked roots /\
    length events <= audit_dfs_input_event_bound p roots /\
    audit_dfs_model_work EV events <= audit_dfs_input_budget EV g p roots.


Inductive audit_dfs_detail (V E : Type) : Type :=
| AuditDfsParentSet (v : V) (e : E) (m : Map.t V E)
| AuditDfsNumSet (v : V) (number : positive) (m : Map.t V positive)
| AuditDfsSeenAdd (v : V) (s : FinSet.t V)
| AuditDfsClock (before after : positive).
Arguments AuditDfsParentSet {V E} _ _ _.
Arguments AuditDfsNumSet {V E} _ _ _.
Arguments AuditDfsSeenAdd {V E} _ _.
Arguments AuditDfsClock {V E} _ _.

Definition audit_dfs_discover_counted {V E} (EV : encoding V) (v : V) (via : option E)
    (st : DfsState.t V E) : DfsState.t V E * list (audit_dfs_detail V E) :=
  let '(parent, parent_events) := match via with
    | Some e => (Map.set EV v e (DfsState.parent st), [AuditDfsParentSet v e (DfsState.parent st)])
    | None => (DfsState.parent st, []) end in
  let index := Map.set EV v (DfsState.pre_clock st) (DfsState.pre_index st) in
  let seen := FinSet.add EV v (DfsState.seen st) in
  let clock := Pos.succ (DfsState.pre_clock st) in
  (DfsState.Make (v :: DfsState.pre st) (DfsState.post st) parent index
    (DfsState.post_index st) seen clock (DfsState.post_clock st),
   parent_events ++ [AuditDfsNumSet v (DfsState.pre_clock st) (DfsState.pre_index st);
     AuditDfsSeenAdd v (DfsState.seen st); AuditDfsClock (DfsState.pre_clock st) clock]).

Definition audit_dfs_finish_counted {V E} (EV : encoding V) (v : V) (st : DfsState.t V E)
    : DfsState.t V E * list (audit_dfs_detail V E) :=
  let index := Map.set EV v (DfsState.post_clock st) (DfsState.post_index st) in
  let clock := Pos.succ (DfsState.post_clock st) in
  (DfsState.Make (DfsState.pre st) (v :: DfsState.post st) (DfsState.parent st)
    (DfsState.pre_index st) index (DfsState.seen st) (DfsState.pre_clock st) clock,
   [AuditDfsNumSet v (DfsState.post_clock st) (DfsState.post_index st);
    AuditDfsClock (DfsState.post_clock st) clock]).

Definition audit_dfs_detail_work {V E} (EV : encoding V) (event : audit_dfs_detail V E) : nat :=
  64 + match event with
  | AuditDfsParentSet v _ _ | AuditDfsNumSet v _ _ | AuditDfsSeenAdd v _ =>
      audit_set_weight (encode EV v) + audit_encoding_weight (audit_key_bits_weight (encode EV v))
  | AuditDfsClock before _ => audit_binary_weight (Z.pos before) 1
  end.

Definition audit_dfs_helpers_statement : Prop :=
  (forall V E (EV : encoding V) v via (st : DfsState.t V E),
    let '(result, events) := audit_dfs_discover_counted EV v via st in
    result = dfs_discover EV v via st /\ length events <= 4) /\
  (forall V E (EV : encoding V) v (st : DfsState.t V E),
    let '(result, events) := audit_dfs_finish_counted EV v st in
    result = dfs_finish EV v st /\ length events = 2).

From Stdlib Require Import List Bool PArith Arith ZArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditCost.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs.
Import List.ListNotations.

Inductive audit_dfs_full_call (V E : Type) : Type :=
  | AuditDfsFullCase (site : nat)
  | AuditDfsFullTarget (edge : E) (target : V)
  | AuditDfsFullMember (vertex : V) (set : FinSet.t V) (result : bool)
  | AuditDfsFullSuccessors (vertex : V) (index : Map.t V (list E)) (result : option (list E))
  | AuditDfsFullDiscover (vertex : V) (via : option E) (before after : DfsState.t V E)
  | AuditDfsFullFinish (vertex : V) (before after : DfsState.t V E)
  | AuditDfsFullDetail (detail : audit_dfs_detail V E)
  | AuditDfsFullOutput (pre post : nat).
Arguments AuditDfsFullCase {V E} _.
Arguments AuditDfsFullTarget {V E} _ _.
Arguments AuditDfsFullMember {V E} _ _ _.
Arguments AuditDfsFullSuccessors {V E} _ _ _.
Arguments AuditDfsFullDiscover {V E} _ _ _ _.
Arguments AuditDfsFullFinish {V E} _ _ _.
Arguments AuditDfsFullDetail {V E} _.
Arguments AuditDfsFullOutput {V E} _ _.

Definition audit_dfs_full_step_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (blocked : FinSet.t V) (work : dfs_stack V E * DfsState.t V E)
    : (dfs_stack V E * DfsState.t V E) * list (audit_dfs_full_call V E) :=
  let '(stack, st) := work in
  match stack with
  | [] => (([], st), [AuditDfsFullCase 0])
  | (v, []) :: rest =>
      let '(next, detail) := audit_dfs_finish_counted EV v st in
      ((rest, next), AuditDfsFullCase 1 :: map AuditDfsFullDetail detail ++ [AuditDfsFullFinish v st
  next])
  | (v, e :: es) :: rest =>
      let target := Graph.target g e in
      let is_blocked := FinSet.mem EV target blocked in
      let is_seen := FinSet.mem EV target (DfsState.seen st) in
      if is_blocked || is_seen then
        (((v, es) :: rest, st), [AuditDfsFullTarget e target;
          AuditDfsFullMember target blocked is_blocked; AuditDfsFullMember target (DfsState.seen st)
  is_seen; AuditDfsFullCase 2])
      else
        let outgoing := Map.get EV target (out_index p) in
        let edges := match outgoing with Some xs => xs | None => [] end in
        let '(next, detail) := audit_dfs_discover_counted EV target (Some e) st in
        (((target, edges) :: (v, es) :: rest, next),
         [AuditDfsFullTarget e target; AuditDfsFullMember target blocked is_blocked;
          AuditDfsFullMember target (DfsState.seen st) is_seen; AuditDfsFullCase 3;
  AuditDfsFullSuccessors target (out_index p) outgoing] ++
          map AuditDfsFullDetail detail ++ [AuditDfsFullDiscover target (Some e) st next])
  end.

Fixpoint audit_dfs_full_run_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (blocked : FinSet.t V) (fuel : positive)
    (work : dfs_stack V E * DfsState.t V E)
    : (dfs_stack V E * DfsState.t V E) * list (audit_dfs_full_call V E) :=
  match fst work with
  | [] => (work, [AuditDfsFullCase 4])
  | _ :: _ => match fuel with
    | xH => let '(result, events) := audit_dfs_full_step_counted p blocked work in
        (result, AuditDfsFullCase 5 :: events)
    | xO rest => let '(middle, first) := audit_dfs_full_run_counted p blocked rest work in
        let '(result, second) := audit_dfs_full_run_counted p blocked rest middle in
        (result, AuditDfsFullCase 6 :: first ++ second)
    | xI rest => let '(middle, first) := audit_dfs_full_run_counted p blocked rest work in
        let '(last, second) := audit_dfs_full_run_counted p blocked rest middle in
        let '(result, step_events) := audit_dfs_full_step_counted p blocked last in
        (result, AuditDfsFullCase 7 :: first ++ second ++ step_events)
    end
  end.

Definition audit_dfs_full_root_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (blocked : FinSet.t V) (st : DfsState.t V E) (v : V)
    : DfsState.t V E * list (audit_dfs_full_call V E) :=
  let is_blocked := FinSet.mem EV v blocked in
  let is_seen := FinSet.mem EV v (DfsState.seen st) in
  if is_blocked || is_seen then
    (st, [AuditDfsFullMember v blocked is_blocked; AuditDfsFullMember v (DfsState.seen st) is_seen;
  AuditDfsFullCase 8])
  else
    let outgoing := Map.get EV v (out_index p) in
    let edges := match outgoing with Some xs => xs | None => [] end in
    let '(discovered, detail) := audit_dfs_discover_counted EV v None st in
    let '(result, events) := audit_dfs_full_run_counted p blocked (fuel p) ([(v, edges)],
  discovered) in
    (snd result, [AuditDfsFullMember v blocked is_blocked;
      AuditDfsFullMember v (DfsState.seen st) is_seen; AuditDfsFullCase 9; AuditDfsFullSuccessors v
  (out_index p) outgoing] ++
      map AuditDfsFullDetail detail ++ [AuditDfsFullDiscover v None st discovered] ++ events).

Fixpoint audit_dfs_full_roots_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (blocked : FinSet.t V) (roots : list V) (st : DfsState.t V E)
    : DfsState.t V E * list (audit_dfs_full_call V E) :=
  match roots with
  | [] => (st, [AuditDfsFullCase 10])
  | root :: rest =>
      let '(next, here) := audit_dfs_full_root_counted p blocked st root in
      let '(result, later) := audit_dfs_full_roots_counted p blocked rest next in
      (result, AuditDfsFullCase 11 :: here ++ later)
  end.

Definition audit_dfs_full_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (blocked : FinSet.t V) (roots : list V)
    : dfs_result V E * list (audit_dfs_full_call V E) :=
  let '(st, events) := audit_dfs_full_roots_counted p blocked roots dfs_initial in
  (DfsResult (rev (DfsState.pre st)) (rev (DfsState.post st)) (DfsState.parent st)
    (DfsState.pre_index st) (DfsState.post_index st) (DfsState.seen st),
    events ++ [AuditDfsFullOutput (length (DfsState.pre st)) (length (DfsState.post st))]).

Definition audit_dfs_full_model_event {V E} (EV : encoding V) (event : audit_dfs_full_call V E) :
  nat :=
  let read v := audit_get_weight (encode EV v) + audit_encoding_weight (audit_key_bits_weight
  (encode EV v)) in
  let write v := audit_set_weight (encode EV v) + audit_encoding_weight (audit_key_bits_weight
  (encode EV v)) in
  64 + match event with
  | AuditDfsFullMember v _ _ | AuditDfsFullSuccessors v _ _ => read v
  | AuditDfsFullDetail detail => audit_dfs_detail_work EV detail
  | AuditDfsFullOutput before after => before + after
  | _ => 0 end.

Definition audit_dfs_full_model_work {V E} (EV : encoding V) (events : list (audit_dfs_full_call V
  E)) : nat :=
  256 * S (length events) * S (length events) +
    fold_right (fun event n => audit_dfs_full_model_event EV event + n) 0 events.

Definition audit_dfs_full_input_width {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (roots : list V) : nat :=
  let rows := Map.elements (out_index p) in
  let vertices := roots ++ Graph.nodes g ++ map fst rows ++
    flat_map (fun row => map (Graph.target g) (snd row)) rows in
  fold_right Nat.max 0 (map (fun v => audit_key_bits_weight (encode EV v)) vertices).

Definition audit_dfs_full_input_event_bound {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (roots : list V) : nat :=
  3 + length roots * (40 * S (Pos.to_nat (fuel p))).

Definition audit_dfs_full_input_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (roots : list V) : nat :=
  let events := audit_dfs_full_input_event_bound p roots in
  let clock_width := audit_key_bits_weight (Pos.of_succ_nat (2 + length roots * S (Pos.to_nat (fuel
  p)))) in
  let width := Nat.max (audit_dfs_full_input_width EV g p roots) clock_width in
  512 * S events * S events + events * (140 + 12 * width).

Definition audit_dfs_full_counted_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) blocked roots,
    let '(result, events) := audit_dfs_full_counted p blocked roots in
    result = dfs p blocked roots /\
    length events <= audit_dfs_full_input_event_bound p roots /\
    audit_dfs_full_model_work EV events <= audit_dfs_full_input_budget EV g p roots.


Record audit_dfs_callback_model (V E B : Type) : Type := AuditDfsCallbackModel {
  audit_dfs_target_model : E -> V * list B;
  audit_dfs_encode_model : V -> positive * list B
}.
Arguments audit_dfs_target_model {V E B} _ _.
Arguments audit_dfs_encode_model {V E B} _ _.

Definition audit_dfs_callbacks_erase {V E B} (EV : encoding V) (g : Graph.t V E)
    (cb : audit_dfs_callback_model V E B) : Prop :=
  (forall e, fst (audit_dfs_target_model cb e) = Graph.target g e) /\
  (forall v, fst (audit_dfs_encode_model cb v) = encode EV v).

Definition audit_dfs_nested_event (V E B : Type) : Type := audit_dfs_full_call V E * list B.

Definition audit_dfs_nested_get {V A E B} (cb : audit_dfs_callback_model V E B)
    (v : V) (m : Map.t V A) : option A * list B :=
  let '(code, body) := audit_dfs_encode_model cb v in (Map.code_get code m, body).

Definition audit_dfs_nested_set {V A E B} (cb : audit_dfs_callback_model V E B)
    (v : V) (value : A) (m : Map.t V A) : Map.t V A * list B :=
  let '(code, body) := audit_dfs_encode_model cb v in (Trie.set code (v, value) m, body).

Definition audit_dfs_nested_discover {V E B} (cb : audit_dfs_callback_model V E B)
    (v : V) (via : option E) (st : DfsState.t V E)
    : DfsState.t V E * list (audit_dfs_nested_event V E B) :=
  let '(parent, parent_events) := match via with
    | Some e => let '(next, body) := audit_dfs_nested_set cb v e (DfsState.parent st) in
        (next, [(AuditDfsFullDetail (AuditDfsParentSet v e (DfsState.parent st)), body)])
    | None => (DfsState.parent st, []) end in
  let '(index, index_body) := audit_dfs_nested_set cb v (DfsState.pre_clock st) (DfsState.pre_index
  st) in
  let '(seen, seen_body) := audit_dfs_nested_set cb v tt (DfsState.seen st) in
  let clock := Pos.succ (DfsState.pre_clock st) in
  (DfsState.Make (v :: DfsState.pre st) (DfsState.post st) parent index
    (DfsState.post_index st) seen clock (DfsState.post_clock st),
   parent_events ++ [(AuditDfsFullDetail (AuditDfsNumSet v (DfsState.pre_clock st)
  (DfsState.pre_index st)), index_body);
     (AuditDfsFullDetail (AuditDfsSeenAdd v (DfsState.seen st)), seen_body);
     (AuditDfsFullDetail (AuditDfsClock (DfsState.pre_clock st) clock), [])]).

Definition audit_dfs_nested_finish {V E B} (cb : audit_dfs_callback_model V E B)
    (v : V) (st : DfsState.t V E) : DfsState.t V E * list (audit_dfs_nested_event V E B) :=
  let '(index, body) := audit_dfs_nested_set cb v (DfsState.post_clock st) (DfsState.post_index st)
  in
  let clock := Pos.succ (DfsState.post_clock st) in
  (DfsState.Make (DfsState.pre st) (v :: DfsState.post st) (DfsState.parent st)
    (DfsState.pre_index st) index (DfsState.seen st) (DfsState.pre_clock st) clock,
   [(AuditDfsFullDetail (AuditDfsNumSet v (DfsState.post_clock st) (DfsState.post_index st)), body);
    (AuditDfsFullDetail (AuditDfsClock (DfsState.post_clock st) clock), [])]).

Definition audit_dfs_nested_step {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (blocked : FinSet.t V)
    (work : dfs_stack V E * DfsState.t V E)
    : (dfs_stack V E * DfsState.t V E) * list (audit_dfs_nested_event V E B) :=
  let '(stack, st) := work in
  match stack with
  | [] => (([], st), [(AuditDfsFullCase 0, [])])
  | (v, []) :: rest => let '(next, detail) := audit_dfs_nested_finish cb v st in
      ((rest, next), (AuditDfsFullCase 1, []) :: detail ++ [(AuditDfsFullFinish v st next, [])])
  | (v, e :: es) :: rest =>
      let '(target, target_body) := audit_dfs_target_model cb e in
      let '(blocked_value, blocked_body) := audit_dfs_nested_get cb target blocked in
      let is_blocked := match blocked_value with Some _ => true | None => false end in
      let '(seen_value, seen_body) := audit_dfs_nested_get cb target (DfsState.seen st) in
      let is_seen := match seen_value with Some _ => true | None => false end in
      if is_blocked || is_seen then
        (((v, es) :: rest, st), [(AuditDfsFullTarget e target, target_body);
          (AuditDfsFullMember target blocked is_blocked, blocked_body);
          (AuditDfsFullMember target (DfsState.seen st) is_seen, seen_body); (AuditDfsFullCase 2,
  [])])
      else let '(outgoing, outgoing_body) := audit_dfs_nested_get cb target (out_index p) in
        let edges := match outgoing with Some xs => xs | None => [] end in
        let '(next, details) := audit_dfs_nested_discover cb target (Some e) st in
        (((target, edges) :: (v, es) :: rest, next),
          [(AuditDfsFullTarget e target, target_body); (AuditDfsFullMember target blocked
  is_blocked, blocked_body);
           (AuditDfsFullMember target (DfsState.seen st) is_seen, seen_body); (AuditDfsFullCase 3,
  []);
           (AuditDfsFullSuccessors target (out_index p) outgoing, outgoing_body)] ++ details ++
           [(AuditDfsFullDiscover target (Some e) st next, [])])
  end.

Fixpoint audit_dfs_nested_run {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (blocked : FinSet.t V)
    (fuel : positive) (work : dfs_stack V E * DfsState.t V E)
    : (dfs_stack V E * DfsState.t V E) * list (audit_dfs_nested_event V E B) :=
  match fst work with
  | [] => (work, [(AuditDfsFullCase 4, [])])
  | _ :: _ => match fuel with
    | xH => let '(result, events) := audit_dfs_nested_step p cb blocked work in
        (result, (AuditDfsFullCase 5, []) :: events)
    | xO rest => let '(middle, first) := audit_dfs_nested_run p cb blocked rest work in
        let '(result, second) := audit_dfs_nested_run p cb blocked rest middle in
        (result, (AuditDfsFullCase 6, []) :: first ++ second)
    | xI rest => let '(middle, first) := audit_dfs_nested_run p cb blocked rest work in
        let '(last, second) := audit_dfs_nested_run p cb blocked rest middle in
        let '(result, step_events) := audit_dfs_nested_step p cb blocked last in
        (result, (AuditDfsFullCase 7, []) :: first ++ second ++ step_events)
    end
  end.

Definition audit_dfs_nested_root {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (blocked : FinSet.t V)
    (st : DfsState.t V E) (v : V) : DfsState.t V E * list (audit_dfs_nested_event V E B) :=
  let '(blocked_value, blocked_body) := audit_dfs_nested_get cb v blocked in
  let is_blocked := match blocked_value with Some _ => true | None => false end in
  let '(seen_value, seen_body) := audit_dfs_nested_get cb v (DfsState.seen st) in
  let is_seen := match seen_value with Some _ => true | None => false end in
  if is_blocked || is_seen then
    (st, [(AuditDfsFullMember v blocked is_blocked, blocked_body);
      (AuditDfsFullMember v (DfsState.seen st) is_seen, seen_body); (AuditDfsFullCase 8, [])])
  else let '(outgoing, outgoing_body) := audit_dfs_nested_get cb v (out_index p) in
    let edges := match outgoing with Some xs => xs | None => [] end in
    let '(discovered, details) := audit_dfs_nested_discover cb v None st in
    let '(result, events) := audit_dfs_nested_run p cb blocked (fuel p) ([(v, edges)], discovered)
  in
    (snd result, [(AuditDfsFullMember v blocked is_blocked, blocked_body);
      (AuditDfsFullMember v (DfsState.seen st) is_seen, seen_body); (AuditDfsFullCase 9, []);
      (AuditDfsFullSuccessors v (out_index p) outgoing, outgoing_body)] ++ details ++
      [(AuditDfsFullDiscover v None st discovered, [])] ++ events).

Fixpoint audit_dfs_nested_roots {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (blocked : FinSet.t V)
    (roots : list V) (st : DfsState.t V E) : DfsState.t V E * list (audit_dfs_nested_event V E B) :=
  match roots with
  | [] => (st, [(AuditDfsFullCase 10, [])])
  | root :: rest => let '(next, here) := audit_dfs_nested_root p cb blocked st root in
      let '(result, later) := audit_dfs_nested_roots p cb blocked rest next in
      (result, (AuditDfsFullCase 11, []) :: here ++ later)
  end.

Definition audit_dfs_nested_counted {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (blocked : FinSet.t V) (roots : list
  V)
    : dfs_result V E * list (audit_dfs_nested_event V E B) :=
  let '(st, events) := audit_dfs_nested_roots p cb blocked roots dfs_initial in
  (DfsResult (rev (DfsState.pre st)) (rev (DfsState.post st)) (DfsState.parent st)
    (DfsState.pre_index st) (DfsState.post_index st) (DfsState.seen st),
   events ++ [(AuditDfsFullOutput (length (DfsState.pre st)) (length (DfsState.post st)), [])]).

Definition audit_dfs_nested_body_work {V E B} (weight : B -> nat)
    (events : list (audit_dfs_nested_event V E B)) : nat :=
  fold_right (fun event total => fold_right (fun item n => weight item + n) 0 (snd event) + total) 0
  events.

Definition audit_dfs_nested_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
      (cb : audit_dfs_callback_model V E B) blocked roots,
    audit_dfs_callbacks_erase EV g cb ->
    let '(result, events) := audit_dfs_nested_counted p cb blocked roots in
    result = dfs p blocked roots /\ map fst events = snd (audit_dfs_full_counted p blocked roots) /\
    length events <= audit_dfs_full_input_event_bound p roots /\
    audit_dfs_full_model_work EV (map fst events) <= audit_dfs_full_input_budget EV g p roots.

Definition audit_dfs_nested_total_work {V E B} (EV : encoding V) (weight : B -> nat)
    (events : list (audit_dfs_nested_event V E B)) : nat :=
  audit_dfs_full_model_work EV (map fst events) + audit_dfs_nested_body_work weight events.

Inductive audit_graph_callback_capture (V E B : Type) : Type :=
| AuditGraphTargetCapture : E -> V -> list B -> audit_graph_callback_capture V E B
| AuditGraphEncodeCapture : V -> positive -> list B -> audit_graph_callback_capture V E B.

Definition audit_graph_capture_callbacks {V E B} (cb : audit_dfs_callback_model V E B)
    : audit_dfs_callback_model V E (audit_graph_callback_capture V E B) :=
  AuditDfsCallbackModel V E (audit_graph_callback_capture V E B)
    (fun edge => let '(value, body) := audit_dfs_target_model cb edge in
      (value, [AuditGraphTargetCapture V E B edge value body]))
    (fun vertex => let '(code, body) := audit_dfs_encode_model cb vertex in
      (code, [AuditGraphEncodeCapture V E B vertex code body])).

Definition audit_graph_capture_callbacks_erases_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (cb : audit_dfs_callback_model V E B),
    audit_dfs_callbacks_erase EV g cb ->
    audit_dfs_callbacks_erase EV g (audit_graph_capture_callbacks cb).

Definition audit_graph_capture_work {V E B} (weight : B -> nat)
    (event : audit_graph_callback_capture V E B) : nat :=
  match event with
  | AuditGraphTargetCapture _ _ _ _ _ body
  | AuditGraphEncodeCapture _ _ _ _ _ body =>
      fold_right (fun item total => weight item + total) 0 body
  end.
From Galois.Collections Require Import CollectionsAuditTrie CollectionsAuditEncoding.
Definition audit_dfs_source_counted {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) blocked roots :=
  let '(st, events) := audit_dfs_nested_roots p (audit_graph_capture_callbacks cb) blocked roots
  dfs_initial in
  (DfsResult (rev_append (DfsState.pre st) []) (rev_append (DfsState.post st) []) (DfsState.parent
  st)
    (DfsState.pre_index st) (DfsState.post_index st) (DfsState.seen st),
   events ++ [(AuditDfsFullOutput (length (DfsState.pre st)) (length (DfsState.post st)), [])]).

Definition audit_dfs_source_code {V E B} (body : list (audit_graph_callback_capture V E B)) :
  positive :=
  match body with
  | [AuditGraphEncodeCapture _ _ _ _ code _] => code
  | _ => 1%positive
  end.

Definition audit_dfs_source_event_work {V E B} (weight : B -> nat)
    (item : audit_dfs_nested_event V E (audit_graph_callback_capture V E B)) : nat :=
  let '(event, body) := item in let code := audit_dfs_source_code body in
  let callback_work := fold_right (fun item n => audit_graph_capture_work weight item + n) 0 body in
  64 + callback_work + match event with
  | AuditDfsFullMember _ set _ => 5 + audit_trie_get_source_work code set
  | AuditDfsFullSuccessors _ input _ => 5 + audit_trie_get_source_work code input
  | AuditDfsFullDetail (AuditDfsParentSet v edge input) =>
      2 + audit_trie_update_source_work code (Some (v, edge)) input
  | AuditDfsFullDetail (AuditDfsNumSet v number input) =>
      2 + audit_trie_update_source_work code (Some (v, number)) input
  | AuditDfsFullDetail (AuditDfsSeenAdd v input) =>
      2 + audit_trie_update_source_work code (Some (v, tt)) input
  | AuditDfsFullDetail (AuditDfsClock before _) => 2 * Pos.size_nat before
  | AuditDfsFullOutput pre post => audit_graph_reverse_fast_work pre + audit_graph_reverse_fast_work
  post
  | _ => 0
  end.

Definition audit_dfs_source_body_work {V E B} (weight : B -> nat)
    (events : list (audit_dfs_nested_event V E (audit_graph_callback_capture V E B))) : nat :=
  fold_right (fun item n => fold_right (fun event k => audit_graph_capture_work weight event + k) 0
  (snd item) + n) 0 events.

Definition audit_dfs_source_work {V E B} (weight : B -> nat)
    (events : list (audit_dfs_nested_event V E (audit_graph_callback_capture V E B))) : nat :=
  fold_right (fun item n => audit_dfs_source_event_work weight item + n) 0 events.

Definition audit_dfs_source_event_wellformed {V E B}
    (item : audit_dfs_nested_event V E (audit_graph_callback_capture V E B)) : Prop :=
  let '(event, body) := item in
  match event with
  | AuditDfsFullMember v _ _ | AuditDfsFullSuccessors v _ _ =>
      exists code trace, body = [AuditGraphEncodeCapture V E B v code trace]
  | AuditDfsFullDetail (AuditDfsParentSet v _ _) | AuditDfsFullDetail (AuditDfsNumSet v _ _) |
    AuditDfsFullDetail (AuditDfsSeenAdd v _) =>
      exists code trace, body = [AuditGraphEncodeCapture V E B v code trace]
  | AuditDfsFullTarget e v => exists trace, body = [AuditGraphTargetCapture V E B e v trace]
  | _ => body = []
  end.

Definition audit_dfs_source_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (roots : list V) : nat :=
  let count := audit_dfs_full_input_event_bound p roots in
  let width := Nat.max (audit_dfs_full_input_width EV g p roots)
    (Pos.size_nat (Pos.of_succ_nat (S (length roots) * S (Pos.to_nat (fuel p))))) in
  1024 * S count * S count + count * (512 + 64 * width).

Definition audit_dfs_source_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (cb : audit_dfs_callback_model V E B) (weight : B -> nat) blocked roots,
    audit_dfs_callbacks_erase EV g cb ->
    let '(result, events) := audit_dfs_source_counted p cb blocked roots in
    result = dfs p blocked roots /\ Forall audit_dfs_source_event_wellformed events /\
    length events <= audit_dfs_full_input_event_bound p roots /\
    audit_dfs_source_work weight events <= audit_dfs_source_budget EV g p roots +
  audit_dfs_source_body_work weight events.

Definition audit_dfs_source_reverse_obligations : Prop :=
  audit_graph_reverse_run_statement /\ audit_graph_reverse_fast_run_statement /\
  audit_graph_reverse_fast_counted_statement.

Definition audit_dfs_source_successor_event {V E B}
    (item : audit_dfs_nested_event V E (audit_graph_callback_capture V E B)) : Prop :=
  match fst item with
  | AuditDfsFullDetail (AuditDfsClock before after) => fst (audit_positive_succ before) = after
  | _ => True
  end.

Definition audit_dfs_source_successor_correspondence_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (cb : audit_dfs_callback_model V E B) blocked roots,
    audit_dfs_callbacks_erase EV g cb ->
    Forall audit_dfs_source_successor_event (snd (audit_dfs_source_counted p cb blocked roots)).

Definition audit_dfs_source_successor_obligations : Prop :=
  audit_positive_succ_run_total_statement /\ audit_positive_succ_run_correct_statement /\
  audit_dfs_source_successor_correspondence_statement.

Definition audit_dfs_capture_budget {V E B} (encode_budget : V -> nat) (target_budget : E -> nat)
    (event : audit_graph_callback_capture V E B) : nat :=
  match event with
  | AuditGraphEncodeCapture _ _ _ vertex _ _ => encode_budget vertex
  | AuditGraphTargetCapture _ _ _ edge _ _ => target_budget edge
  end.

Definition audit_dfs_source_external_budget {V E B} (encode_budget : V -> nat) (target_budget : E ->
  nat)
    (events : list (audit_dfs_nested_event V E (audit_graph_callback_capture V E B))) : nat :=
  fold_right (fun item n => fold_right (fun event k => audit_dfs_capture_budget encode_budget
  target_budget event + k)
    0 (snd item) + n) 0 events.

Definition audit_dfs_source_adapted_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (cb : audit_dfs_callback_model V E B) (weight : B -> nat) blocked roots
    encode_source target_source encode_budget target_budget,
    audit_dfs_callbacks_erase EV g cb ->
    audit_graph_external_callback_adapter (audit_dfs_encode_model cb) weight encode_source
  encode_budget ->
    audit_graph_external_callback_adapter (audit_dfs_target_model cb) weight target_source
  target_budget ->
    let '(result, events) := audit_dfs_source_counted p cb blocked roots in
    result = dfs p blocked roots /\
    audit_dfs_source_work weight events <= audit_dfs_source_budget EV g p roots +
      audit_dfs_source_external_budget encode_budget target_budget events.

Definition audit_dfs_source_contract_statement : Prop :=
  audit_dfs_source_statement /\ audit_dfs_source_adapted_statement /\
  audit_dfs_source_reverse_obligations /\ audit_dfs_source_successor_obligations /\
  audit_trie_get_trace_adequate_statement /\ audit_trie_update_trace_adequate_statement /\
  audit_trie_get_source_work_bound_statement /\ audit_trie_update_source_work_bound_statement.
```

## Galois.Graph.GraphAuditVirtual

Card: AUD-GR-MODELS

Source destination: `theories/Graph/GraphAuditVirtual.v`.

```rocq
From Stdlib Require Import List Bool PArith ZArith.
From Galois.Collections Require Import CollectionsAuditCost CollectionsEncoding CollectionsMap
  CollectionsTrie CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphDominators.
Import List.ListNotations.
From Galois.Graph Require Import GraphAuditBase GraphAuditDfs.

From Galois.Graph Require Import GraphDominance GraphSemiDominators.

Inductive audit_virtual_call (V E : Type) : Type :=
| AuditVirtualCase (site : nat)
| AuditVirtualMem (v : V) (seen : FinSet.t V) (result : bool)
| AuditVirtualAdd (v : V) (seen : FinSet.t V)
| AuditVirtualOut (v : V) (edges : list E)
| AuditVirtualSource (e : E) (v : V)
| AuditVirtualTarget (e : E) (v : V)
| AuditVirtualEncode (v : V) (code : positive)
| AuditVirtualMap (size : nat).
Arguments AuditVirtualCase {V E} _.
Arguments AuditVirtualMem {V E} _ _ _.
Arguments AuditVirtualAdd {V E} _ _.
Arguments AuditVirtualOut {V E} _ _.
Arguments AuditVirtualSource {V E} _ _.
Arguments AuditVirtualTarget {V E} _ _.
Arguments AuditVirtualEncode {V E} _ _.
Arguments AuditVirtualMap {V E} _.

Fixpoint audit_virtual_entries_counted {V E} (EV : encoding V) (seen : FinSet.t V) (entries : list
  V)
    : list V * list (audit_virtual_call V E) :=
  match entries with
  | [] => ([], [AuditVirtualCase 0])
  | v :: rest => let found := FinSet.mem EV v seen in
    if found then let '(result, events) := audit_virtual_entries_counted EV seen rest in
      (result, AuditVirtualCase 1 :: AuditVirtualMem v seen found :: AuditVirtualCase 2 :: events)
    else let next := FinSet.add EV v seen in
      let '(result, events) := audit_virtual_entries_counted EV next rest in
      (v :: result, AuditVirtualCase 1 :: AuditVirtualMem v seen found :: AuditVirtualCase 3 ::
        AuditVirtualAdd v seen :: events)
  end.

Definition audit_virtual_out_counted {V E} (EV : encoding V) (g : Graph.t V E) (v : V + unit)
    : list (E + V) * list (audit_virtual_call V E) :=
  match v with
  | inl x => let edges := Graph.out g x in
      (map (@inl E V) edges, [AuditVirtualCase 4; AuditVirtualOut x edges; AuditVirtualMap (length
  edges)])
  | inr _ => let '(entries, events) := audit_virtual_entries_counted EV FinSet.empty (Graph.entries
  g) in
      (map (@inr E V) entries, AuditVirtualCase 5 :: events ++ [AuditVirtualMap (length entries)])
  end.

Definition audit_virtual_source_counted {V E} (g : Graph.t V E) (e : E + V)
    : (V + unit) * list (audit_virtual_call V E) :=
  match e with
  | inl original => let source := Graph.source g original in
      (inl source, [AuditVirtualCase 6; AuditVirtualSource original source])
  | inr _ => (inr tt, [AuditVirtualCase 7])
  end.

Definition audit_virtual_target_counted {V E} (g : Graph.t V E) (e : E + V)
    : (V + unit) * list (audit_virtual_call V E) :=
  match e with
  | inl original => let target := Graph.target g original in
      (inl target, [AuditVirtualCase 8; AuditVirtualTarget original target])
  | inr v => (inl v, [AuditVirtualCase 9])
  end.

Definition audit_virtual_encode_counted {V E} (EV : encoding V) (v : V + unit)
    : positive * list (audit_virtual_call V E) :=
  match v with
  | inl x => let code := encode EV x in (xO code, [AuditVirtualCase 10; AuditVirtualEncode x code])
  | inr _ => (xI xH, [AuditVirtualCase 11])
  end.

Definition audit_virtual_prepare_callbacks {V E} (EV : encoding V) (g : Graph.t V E)
    : audit_prepare_callback_model (V + unit) (E + V) (audit_virtual_call V E) :=
  AuditPrepareCallbackModel _ _ _ (audit_virtual_out_counted EV g)
    (audit_virtual_target_counted g) (audit_virtual_encode_counted EV).

Definition audit_virtual_dfs_callbacks {V E} (EV : encoding V) (g : Graph.t V E)
    : audit_dfs_callback_model (V + unit) (E + V) (audit_virtual_call V E) :=
  AuditDfsCallbackModel _ _ _ (audit_virtual_target_counted g) (audit_virtual_encode_counted EV).

Definition audit_virtual_callbacks_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E),
    audit_prepare_callbacks_erase (virtual_encoding EV) (virtual_graph EV g)
  (audit_virtual_prepare_callbacks EV g) /\
    audit_dfs_callbacks_erase (virtual_encoding EV) (virtual_graph EV g)
  (audit_virtual_dfs_callbacks EV g) /\
    (forall edge, fst (audit_virtual_source_counted g edge) = Graph.source (virtual_graph EV g)
  edge) /\
    (forall seen entries, fst (@audit_virtual_entries_counted V E EV seen entries) =
  virtual_entries_from EV seen entries).

Definition audit_virtual_search_with_prepared {V E} (EV : encoding V) (g : Graph.t V E) :=
  let '(p, prep_events) := audit_graph_prepare_nested_counted (virtual_encoding EV) (virtual_graph
  EV g)
    (audit_virtual_prepare_callbacks EV g) in
  let '(result, dfs_events) := audit_dfs_nested_counted p (audit_virtual_dfs_callbacks EV g)
  FinSet.empty [inr tt] in
  (p, (result, (prep_events, dfs_events))).

Definition audit_virtual_search_counted {V E} (EV : encoding V) (g : Graph.t V E) :=
  let '(_, (result, traces)) := audit_virtual_search_with_prepared EV g in (result, traces).

Definition audit_virtual_search_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g),
    fst (audit_virtual_search_counted EV g) = virtual_dfs p.

Definition audit_virtual_event_work {V E} (EV : encoding V) (event : audit_virtual_call V E) : nat
  :=
  64 + match event with
  | AuditVirtualMem v _ _ => audit_encoding_weight (audit_key_bits_weight (encode EV v)) +
  audit_get_weight (encode EV v)
  | AuditVirtualAdd v _ => audit_encoding_weight (audit_key_bits_weight (encode EV v)) +
  audit_set_weight (encode EV v)
  | AuditVirtualEncode _ code => audit_encoding_weight (audit_key_bits_weight code)
  | AuditVirtualMap size => S size
  | _ => 0 end.

Definition audit_virtual_entries_work {V E} (EV : encoding V) (events : list (audit_virtual_call V
  E)) : nat :=
  fold_right (fun event n => audit_virtual_event_work EV event + n) 0 events.

Definition audit_virtual_entries_width {V} (EV : encoding V) (entries : list V) : nat :=
  fold_right Nat.max 0 (map (fun v => audit_key_bits_weight (encode EV v)) entries).

Definition audit_virtual_entries_budget {V} (EV : encoding V) (entries : list V) : nat :=
  (1 + 4 * length entries) * (70 + 3 * audit_virtual_entries_width EV entries).

Definition audit_virtual_entries_statement : Prop :=
  forall V E (EV : encoding V) seen entries,
    let '(result, events) := @audit_virtual_entries_counted V E EV seen entries in
    result = virtual_entries_from EV seen entries /\ length events <= 1 + 4 * length entries /\
    audit_virtual_entries_work EV events <= audit_virtual_entries_budget EV entries.

Definition audit_virtual_search_work {V E} (EV : encoding V) (g : Graph.t V E) : nat :=
  let '(_, (prep_events, dfs_events)) := audit_virtual_search_counted EV g in
  audit_graph_prepare_nested_total_work (audit_virtual_event_work EV) prep_events +
  audit_dfs_nested_total_work (virtual_encoding EV) (audit_virtual_event_work EV) dfs_events.

Definition audit_virtual_search_budget {V E} (EV : encoding V) (g : Graph.t V E) : nat :=
  let vg := virtual_graph EV g in
  let encoding := virtual_encoding EV in
  let p := prepare encoding vg in
  let prep_count := audit_graph_prepare_full_event_bound vg in
  let dfs_count := audit_dfs_full_input_event_bound p [inr tt] in
  let width := Nat.max (audit_graph_prepare_input_width encoding vg)
    (audit_dfs_full_input_width encoding vg p [inr tt]) in
  let list_size := 1 + length (Graph.nodes g) + length (Graph.entries g) + edge_count g in
  let body_budget := 8 * S (length (Graph.entries g)) * (256 + 6 * width + list_size) in
  audit_graph_prepare_full_budget encoding vg + audit_dfs_full_input_budget encoding vg p [inr tt] +
    (prep_count + dfs_count) * body_budget.

Definition audit_virtual_search_bound_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E),
    audit_virtual_search_work EV g <= audit_virtual_search_budget EV g.


From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsTrie
  CollectionsAuditCost.
From Galois.Graph Require Import GraphDominance.
Import List.ListNotations.

Inductive audit_erase_call (V : Type) : Type :=
| AuditEraseCase (site : nat)
| AuditEraseElements (input : Map.t (V + unit) (V + unit)) (rows : list ((V + unit) * (V + unit)))
| AuditEraseSet (key value : V) (before : Map.t V V).
Arguments AuditEraseCase {V} _.
Arguments AuditEraseElements {V} _ _.
Arguments AuditEraseSet {V} _ _ _.

Fixpoint audit_erase_rows_counted {V} (EV : encoding V) (rows : list ((V + unit) * (V + unit)))
    : Map.t V V * list (audit_erase_call V) :=
  match rows with
  | [] => (Map.empty, [AuditEraseCase 0])
  | row :: rest => let '(middle, events) := audit_erase_rows_counted EV rest in
      match row with
      | (inl v, inl parent) => (Map.set EV v parent middle,
          AuditEraseCase 1 :: events ++ [AuditEraseCase 2; AuditEraseSet v parent middle])
      | _ => (middle, AuditEraseCase 1 :: events ++ [AuditEraseCase 3])
      end
  end.

Definition audit_erase_virtual_counted {V} (EV : encoding V) (m : Map.t (V + unit) (V + unit))
    : Map.t V V * list (audit_erase_call V) :=
  let rows := Map.elements m in let '(result, events) := audit_erase_rows_counted EV rows in
  (result, AuditEraseElements m rows :: events).

Fixpoint audit_erase_nodes_ne {A} (node : Trie.ne A) : nat :=
  match node with
  | Trie.N001 r => S (audit_erase_nodes_ne r)
  | Trie.N010 _ => 1
  | Trie.N011 _ r => S (audit_erase_nodes_ne r)
  | Trie.N100 l => S (audit_erase_nodes_ne l)
  | Trie.N101 l r => S (audit_erase_nodes_ne l + audit_erase_nodes_ne r)
  | Trie.N110 l _ => S (audit_erase_nodes_ne l)
  | Trie.N111 l _ r => S (audit_erase_nodes_ne l + audit_erase_nodes_ne r)
  end.

Definition audit_erase_nodes {A} (m : Trie.t A) : nat :=
  match m with Trie.Empty => 0 | Trie.Nodes node => audit_erase_nodes_ne node end.

Definition audit_erase_event_work {V} (EV : encoding V) (event : audit_erase_call V) : nat :=
  64 + match event with
  | AuditEraseElements input _ => 64 * Nat.pow (S (audit_erase_nodes input)) 3
  | AuditEraseSet key _ _ => audit_encoding_weight (audit_key_bits_weight (encode EV key)) +
  audit_set_weight (encode EV key)
  | AuditEraseCase _ => 0 end.

Definition audit_erase_virtual_work {V} (EV : encoding V) (events : list (audit_erase_call V)) : nat
  :=
  128 * S (length events) * S (length events) +
    fold_right (fun event total => audit_erase_event_work EV event + total) 0 events.

Definition audit_erase_width {V} (EV : encoding V) (m : Map.t (V + unit) (V + unit)) : nat :=
  fold_right (fun row n => match fst row with
    | inl v => Nat.max (audit_key_bits_weight (encode EV v)) n | inr _ => n end)
    0 (Map.elements m).

Definition audit_erase_event_bound {V} (m : Map.t (V + unit) (V + unit)) : nat :=
  2 + 3 * length (Map.elements m).

Definition audit_erase_virtual_budget {V} (EV : encoding V) (m : Map.t (V + unit) (V + unit)) : nat
  :=
  let count := audit_erase_event_bound m in
  256 * Nat.pow (S (audit_erase_nodes m)) 3 + 256 * S count * S count +
    count * (80 + 4 * audit_erase_width EV m).

Definition audit_erase_virtual_statement : Prop :=
  forall V (EV : encoding V) m,
    let '(result, events) := audit_erase_virtual_counted EV m in
    result = erase_virtual_parents EV m /\ length events <= audit_erase_event_bound m /\
    audit_erase_virtual_work EV events <= audit_erase_virtual_budget EV m.

From Galois.Collections Require Import CollectionsAuditElements CollectionsAuditMap.
Inductive audit_erase_nested_event (V B : Type) : Type :=
| EraseNestedCase : nat -> audit_erase_nested_event V B
| EraseNestedElements : audit_elements_event ((V + unit) * (V + unit)) -> audit_erase_nested_event V
  B
| EraseNestedSet : audit_map_event V V B -> audit_erase_nested_event V B.
Arguments EraseNestedCase {V B} _.
Arguments EraseNestedElements {V B} _.
Arguments EraseNestedSet {V B} _.

Fixpoint audit_erase_nested_rows {V B} (enc : V -> positive * list B)
    (rows : list ((V + unit) * (V + unit))) : Map.t V V * list (audit_erase_nested_event V B) :=
  match rows with
  | [] => (Map.empty, [EraseNestedCase 0])
  | row :: rest => let '(middle, events) := audit_erase_nested_rows enc rest in
      match row with
      | (inl v, inl parent) => let '(result, writes) := audit_map_set enc v parent middle in
          (result, [EraseNestedCase 1] ++ events ++ [EraseNestedCase 2] ++ map EraseNestedSet
  writes)
      | _ => (middle, [EraseNestedCase 1] ++ events ++ [EraseNestedCase 3])
      end
  end.

Definition audit_erase_virtual_nested {V B} (enc : V -> positive * list B)
    (m : Map.t (V + unit) (V + unit)) : Map.t V V * list (audit_erase_nested_event V B) :=
  let '(rows, elements) := audit_map_elements m in
  let '(result, events) := audit_erase_nested_rows enc rows in
  (result, map EraseNestedElements elements ++ events).

Definition audit_erase_nested_event_work {V B} (weight : B -> nat) (event : audit_erase_nested_event
  V B) : nat :=
  64 + match event with
  | EraseNestedElements item => audit_elements_frame_work item
  | EraseNestedSet item => audit_map_source_work (fun body => fold_right (fun x n => weight x + n) 0
  body) [item]
  | EraseNestedCase _ => 0
  end.

Definition audit_erase_nested_body_event_work {V B} (weight : B -> nat)
    (event : audit_erase_nested_event V B) : nat :=
  match event with
  | EraseNestedSet (AuditMapGet _ _ _ _ body _) | EraseNestedSet (AuditMapSet _ _ _ _ _ body _) |
    EraseNestedSet (AuditMapRemove _ _ _ _ body _) => fold_right (fun x n => weight x + n) 0 body
  | EraseNestedCase _ | EraseNestedElements _ => 0
  end.

Definition audit_erase_nested_work {V B} (weight : B -> nat) (events : list
  (audit_erase_nested_event V B)) : nat :=
  fold_right (fun item n => audit_erase_nested_event_work weight item + n) 0 events.

Definition audit_erase_nested_body_work {V B} (weight : B -> nat) (events : list
  (audit_erase_nested_event V B)) : nat :=
  fold_right (fun item n => audit_erase_nested_body_event_work weight item + n) 0 events.

Definition audit_erase_nested_width {V} (EV : encoding V) (m : Map.t (V + unit) (V + unit)) : nat :=
  fold_right (fun row n => match fst row with inl v => Nat.max (Pos.size_nat (encode EV v)) n | inr
  _ => n end)
    0 (Map.elements m).

Definition audit_erase_nested_budget {V} (EV : encoding V) (m : Map.t (V + unit) (V + unit)) : nat
  :=
  let n := S (audit_trie_nodes m) in
  1024 * n * n + 128 * audit_trie_output_bits m + 128 * n * S (audit_erase_nested_width EV m).

Definition audit_erase_nested_statement : Prop :=
  forall V B (EV : encoding V) (enc : V -> positive * list B) (weight : B -> nat) m,
    (forall v, fst (enc v) = encode EV v) ->
    let '(result, events) := audit_erase_virtual_nested enc m in
    result = erase_virtual_parents EV m /\
    audit_erase_nested_work weight events <= audit_erase_nested_budget EV m +
  audit_erase_nested_body_work weight events.
From Galois.Collections Require Import CollectionsAuditTrie CollectionsAuditFinSet.
Inductive audit_virtual_entries_full_event (V B : Type) : Type :=
| VirtualEntriesCase : nat -> audit_virtual_entries_full_event V B
| VirtualEntriesSet : audit_set_event V B -> audit_virtual_entries_full_event V B.
Arguments VirtualEntriesCase {V B} _.
Arguments VirtualEntriesSet {V B} _.

Fixpoint audit_virtual_entries_full_counted {V B}
    (enc : V -> positive * list B) (seen : FinSet.t V) (entries : list V)
    : list V * list (audit_virtual_entries_full_event V B) :=
  match entries with
  | [] => ([], [VirtualEntriesCase 0])
  | v :: rest =>
      let '(found, reads) := audit_finset_mem enc v seen in
      if found then
        let '(result, later) := audit_virtual_entries_full_counted enc seen rest in
        (result, [VirtualEntriesCase 1] ++ map VirtualEntriesSet reads ++
          [VirtualEntriesCase 2] ++ later)
      else
        let '(next, writes) := audit_finset_add enc v seen in
        let '(result, later) := audit_virtual_entries_full_counted enc next rest in
        (v :: result, [VirtualEntriesCase 1] ++ map VirtualEntriesSet reads ++
          [VirtualEntriesCase 3] ++ map VirtualEntriesSet writes ++ later)
  end.

Definition audit_virtual_entries_full_internal_event_work {V B}
    (event : audit_virtual_entries_full_event V B) : nat :=
  64 + match event with
  | VirtualEntriesSet (AuditSetMem _ code input _ _ _) =>
      5 + audit_trie_get_source_work code input
  | VirtualEntriesSet (AuditSetAdd key code input _ _ _) =>
      5 + audit_trie_update_source_work code (Some (key, tt)) input
  | VirtualEntriesSet (AuditSetRemove _ code input _ _ _) =>
      5 + audit_trie_update_source_work code None input
  | VirtualEntriesSet (AuditSetFold _ _) | VirtualEntriesCase _ => 0
  end.

Definition audit_virtual_entries_full_body_event_work {V B} (weight : B -> nat)
    (event : audit_virtual_entries_full_event V B) : nat :=
  match event with
  | VirtualEntriesSet (AuditSetMem _ _ _ _ body _)
  | VirtualEntriesSet (AuditSetAdd _ _ _ _ body _)
  | VirtualEntriesSet (AuditSetRemove _ _ _ _ body _) =>
      fold_right (fun item n => weight item + n) 0 body
  | VirtualEntriesSet (AuditSetFold _ _) | VirtualEntriesCase _ => 0
  end.

Definition audit_virtual_entries_full_internal_work {V B}
    (events : list (audit_virtual_entries_full_event V B)) : nat :=
  fold_right (fun item n => audit_virtual_entries_full_internal_event_work item + n) 0 events.

Definition audit_virtual_entries_full_body_work {V B} (weight : B -> nat)
    (events : list (audit_virtual_entries_full_event V B)) : nat :=
  fold_right (fun item n => audit_virtual_entries_full_body_event_work weight item + n) 0 events.

Definition audit_virtual_entries_full_width {V} (EV : encoding V) (entries : list V) : nat :=
  fold_right Nat.max 0 (map (fun v => Pos.size_nat (encode EV v)) entries).

Definition audit_virtual_entries_full_budget {V} (EV : encoding V) (entries : list V) : nat :=
  128 + length entries * (512 + 32 * audit_virtual_entries_full_width EV entries).

Definition audit_virtual_entries_full_statement : Prop :=
  forall V B (EV : encoding V) (enc : V -> positive * list B) seen entries,
    (forall v, fst (enc v) = encode EV v) ->
    let '(result, events) := audit_virtual_entries_full_counted enc seen entries in
    result = virtual_entries_from EV seen entries /\
    length events <= 1 + 4 * length entries /\
    audit_virtual_entries_full_internal_work events <= audit_virtual_entries_full_budget EV entries.

Definition audit_virtual_entries_full_total_statement : Prop :=
  forall V B (EV : encoding V) (enc : V -> positive * list B) (weight : B -> nat) seen entries,
    (forall v, fst (enc v) = encode EV v) ->
    let '(result, events) := audit_virtual_entries_full_counted enc seen entries in
    result = virtual_entries_from EV seen entries /\
    audit_virtual_entries_full_internal_work events + audit_virtual_entries_full_body_work weight
  events <=
      audit_virtual_entries_full_budget EV entries + audit_virtual_entries_full_body_work weight
  events.
Record audit_virtual_base_callbacks (V E B : Type) : Type := AuditVirtualBaseCallbacks {
  audit_virtual_base_out : V -> list E * list B;
  audit_virtual_base_target : E -> V * list B;
  audit_virtual_base_encode : V -> positive * list B
}.
Arguments audit_virtual_base_out {V E B} _ _.
Arguments audit_virtual_base_target {V E B} _ _.
Arguments audit_virtual_base_encode {V E B} _ _.

Inductive audit_virtual_full_call (V E B : Type) : Type :=
| VirtualFullCase : nat -> audit_virtual_full_call V E B
| VirtualFullOut : V -> list E -> list B -> audit_virtual_full_call V E B
| VirtualFullTarget : E -> V -> list B -> audit_virtual_full_call V E B
| VirtualFullSource : E -> V -> list B -> audit_virtual_full_call V E B
| VirtualFullEncode : V -> positive -> list B -> audit_virtual_full_call V E B
| VirtualFullEntry : audit_virtual_entries_full_event V B -> audit_virtual_full_call V E B
| VirtualFullMap : nat -> audit_virtual_full_call V E B.
Arguments VirtualFullCase {V E B} _.
Arguments VirtualFullOut {V E B} _ _ _.
Arguments VirtualFullTarget {V E B} _ _ _.
Arguments VirtualFullSource {V E B} _ _ _.
Arguments VirtualFullEncode {V E B} _ _ _.
Arguments VirtualFullEntry {V E B} _.
Arguments VirtualFullMap {V E B} _.

Definition audit_virtual_base_callbacks_erase {V E B} (EV : encoding V) (g : Graph.t V E)
    (cb : audit_virtual_base_callbacks V E B) : Prop :=
  (forall v, fst (audit_virtual_base_out cb v) = Graph.out g v) /\
  (forall e, fst (audit_virtual_base_target cb e) = Graph.target g e) /\
  (forall v, fst (audit_virtual_base_encode cb v) = encode EV v).

Definition audit_virtual_full_out {V E B} (g : Graph.t V E)
    (cb : audit_virtual_base_callbacks V E B) (v : V + unit)
    : list (E + V) * list (audit_virtual_full_call V E B) :=
  match v with
  | inl vertex => let '(edges, body) := audit_virtual_base_out cb vertex in
      (map (@inl E V) edges,
        [VirtualFullCase 0; VirtualFullOut vertex edges body; VirtualFullMap (length edges)])
  | inr _ =>
      let '(entries, events) := audit_virtual_entries_full_counted
        (audit_virtual_base_encode cb) FinSet.empty (Graph.entries g) in
      (map (@inr E V) entries,
        [VirtualFullCase 1] ++ map VirtualFullEntry events ++ [VirtualFullMap (length entries)])
  end.

Definition audit_virtual_full_target {V E B} (cb : audit_virtual_base_callbacks V E B)
    (edge : E + V) : (V + unit) * list (audit_virtual_full_call V E B) :=
  match edge with
  | inl original => let '(target, body) := audit_virtual_base_target cb original in
      (inl target, [VirtualFullCase 2; VirtualFullTarget original target body])
  | inr vertex => (inl vertex, [VirtualFullCase 3])
  end.

Definition audit_virtual_full_source {V E B} (source : E -> V * list B)
    (edge : E + V) : (V + unit) * list (audit_virtual_full_call V E B) :=
  match edge with
  | inl original => let '(vertex, body) := source original in
      (inl vertex, [VirtualFullCase 6; VirtualFullSource original vertex body])
  | inr _ => (inr tt, [VirtualFullCase 7])
  end.

Definition audit_virtual_full_source_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (source : E -> V * list B),
    (forall edge, fst (source edge) = Graph.source g edge) ->
    forall edge, fst (audit_virtual_full_source source edge) = Graph.source (virtual_graph EV g)
  edge.

Definition audit_virtual_full_encode {V E B} (cb : audit_virtual_base_callbacks V E B)
    (vertex : V + unit) : positive * list (audit_virtual_full_call V E B) :=
  match vertex with
  | inl original => let '(code, body) := audit_virtual_base_encode cb original in
      (xO code, [VirtualFullCase 4; VirtualFullEncode original code body])
  | inr _ => (xI xH, [VirtualFullCase 5])
  end.

Definition audit_virtual_full_prepare_callbacks {V E B} (g : Graph.t V E)
    (cb : audit_virtual_base_callbacks V E B)
    : audit_prepare_callback_model (V + unit) (E + V) (audit_virtual_full_call V E B) :=
  AuditPrepareCallbackModel _ _ _ (audit_virtual_full_out g cb)
    (audit_virtual_full_target cb) (audit_virtual_full_encode cb).

Definition audit_virtual_full_dfs_callbacks {V E B} (cb : audit_virtual_base_callbacks V E B)
    : audit_dfs_callback_model (V + unit) (E + V) (audit_virtual_full_call V E B) :=
  AuditDfsCallbackModel _ _ _ (audit_virtual_full_target cb) (audit_virtual_full_encode cb).

Definition audit_virtual_full_callbacks_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (cb : audit_virtual_base_callbacks V E B),
    audit_virtual_base_callbacks_erase EV g cb ->
    audit_prepare_callbacks_erase (virtual_encoding EV) (virtual_graph EV g)
      (audit_virtual_full_prepare_callbacks g cb) /\
    audit_dfs_callbacks_erase (virtual_encoding EV) (virtual_graph EV g)
      (audit_virtual_full_dfs_callbacks cb).

Definition audit_virtual_full_search_with_prepared {V E B} (EV : encoding V) (g : Graph.t V E)
    (cb : audit_virtual_base_callbacks V E B) :=
  let '(p, prepare_events) := audit_graph_prepare_nested_counted (virtual_encoding EV)
    (virtual_graph EV g) (audit_virtual_full_prepare_callbacks g cb) in
  let '(result, dfs_events) := audit_dfs_nested_counted p (audit_virtual_full_dfs_callbacks cb)
    FinSet.empty [inr tt] in
  (p, (result, (prepare_events, dfs_events))).

Definition audit_virtual_full_search_counted {V E B} (EV : encoding V) (g : Graph.t V E)
    (cb : audit_virtual_base_callbacks V E B) :=
  let '(_, (result, events)) := audit_virtual_full_search_with_prepared EV g cb in (result, events).

Definition audit_virtual_full_search_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (cb : audit_virtual_base_callbacks V E B)
    (p : prepared EV g), audit_virtual_base_callbacks_erase EV g cb ->
    fst (audit_virtual_full_search_counted EV g cb) = virtual_dfs p.

Definition audit_virtual_full_internal_event_work {V E B}
    (event : audit_virtual_full_call V E B) : nat :=
  64 + match event with
  | VirtualFullEntry inner => audit_virtual_entries_full_internal_event_work inner
  | VirtualFullMap size => S size
  | VirtualFullCase _ | VirtualFullOut _ _ _ | VirtualFullTarget _ _ _ | VirtualFullSource _ _ _ |
    VirtualFullEncode _ _ _ => 0
  end.

Definition audit_virtual_full_body_event_work {V E B} (weight : B -> nat)
    (event : audit_virtual_full_call V E B) : nat :=
  match event with
  | VirtualFullEntry inner => audit_virtual_entries_full_body_event_work weight inner
  | VirtualFullOut _ _ body | VirtualFullTarget _ _ body | VirtualFullSource _ _ body |
    VirtualFullEncode _ _ body =>
      fold_right (fun item n => weight item + n) 0 body
  | VirtualFullCase _ | VirtualFullMap _ => 0
  end.

Definition audit_virtual_full_events_body_work {V E B} (weight : B -> nat)
    (events : list (audit_virtual_full_call V E B)) : nat :=
  fold_right (fun item n => audit_virtual_full_body_event_work weight item + n) 0 events.

Definition audit_virtual_full_search_input_budget {V E} (EV : encoding V) (g : Graph.t V E) : nat :=
  let vg := virtual_graph EV g in
  let encoding := virtual_encoding EV in
  let p := prepare encoding vg in
  let prepare_count := audit_graph_prepare_full_event_bound vg in
  let dfs_count := audit_dfs_full_input_event_bound p [inr tt] in
  let width := Nat.max (audit_graph_prepare_input_width encoding vg)
    (audit_dfs_full_input_width encoding vg p [inr tt]) in
  let size := 1 + length (Graph.nodes g) + length (Graph.entries g) + edge_count g in
  let body_budget := 8 * S (length (Graph.entries g)) * (1024 + 128 * S width + size) in
  audit_graph_prepare_full_budget encoding vg + audit_dfs_full_input_budget encoding vg p [inr tt] +
    (prepare_count + dfs_count) * body_budget.

From Galois.Graph Require Import GraphAuditBase GraphAuditDfs.
Definition audit_virtual_source_search {V E B} (EV : encoding V) (g : Graph.t V E)
    (cb : audit_virtual_base_callbacks V E B) :=
  let '(p, prepare_events) := audit_prepare_source_counted (virtual_encoding EV) (virtual_graph EV
  g)
    (audit_virtual_full_prepare_callbacks g cb) in
  let '(result, dfs_events) := audit_dfs_source_counted p (audit_virtual_full_dfs_callbacks cb)
    FinSet.empty [inr tt] in
  (p, (result, (prepare_events, dfs_events))).

Definition audit_virtual_source_search_budget {V E} (EV : encoding V) (g : Graph.t V E) : nat :=
  let vg := virtual_graph EV g in let enc := virtual_encoding EV in let p := prepare enc vg in
  audit_prepare_source_budget enc vg + audit_dfs_source_budget enc vg p [inr tt] +
    audit_virtual_full_search_input_budget EV g.

Definition audit_virtual_source_search_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (cb : audit_virtual_base_callbacks V E B) (weight : B -> nat),
    audit_virtual_base_callbacks_erase EV g cb ->
    let '(vp, (result, (prepare_events, dfs_events))) := audit_virtual_source_search EV g cb in
    vp = virtual_prepared p /\ result = virtual_dfs p /\
    audit_prepare_source_work
      (fun item => audit_virtual_full_internal_event_work item + audit_virtual_full_body_event_work
  weight item)
      prepare_events +
    audit_dfs_source_work
      (fun item => audit_virtual_full_internal_event_work item + audit_virtual_full_body_event_work
  weight item)
      dfs_events <= audit_virtual_source_search_budget EV g +
    audit_prepare_source_body_work (audit_virtual_full_body_event_work weight) prepare_events +
    audit_dfs_source_body_work (audit_virtual_full_body_event_work weight) dfs_events.
```

## Galois.Graph.GraphAuditVirtualAdapter

Card: AUD-GR-MODELS

Source destination: `theories/Graph/GraphAuditVirtualAdapter.v`.

```rocq
(** * Virtual graph source adapters

    The virtual search prices each captured original callback at its actual input.
    For example, a virtual entry charges the encoder of the original entry vertex.
    Builds on: the virtual graph, preparation and DFS source models. *)
From Stdlib Require Import List.
From Galois.Collections Require Import CollectionsEncoding CollectionsAuditFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDominance GraphSemiDominators
  GraphAuditBase GraphAuditDfs GraphAuditVirtual.

(** Each virtual wrapper resolves to the supplied original callback it executes. *)
Definition audit_virtual_adapter_call_budget {V E B} (encode_budget out_budget : V -> nat)
    (target_budget : E -> nat) (event : audit_virtual_full_call V E B) : nat :=
  match event with
  | VirtualFullOut v _ _ => out_budget v
  | VirtualFullTarget e _ _ => target_budget e
  | VirtualFullEncode v _ _ => encode_budget v
  | VirtualFullEntry (VirtualEntriesSet (AuditSetAdd v _ _ _ _ _)) |
    VirtualFullEntry (VirtualEntriesSet (AuditSetMem v _ _ _ _ _)) |
    VirtualFullEntry (VirtualEntriesSet (AuditSetRemove v _ _ _ _ _)) => encode_budget v
  | _ => 0
  end.

(** One captured virtual search has the full original-input and per-call source bound. *)
Definition audit_virtual_source_search_adapted_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (cb : audit_virtual_base_callbacks V E B) (weight : B -> nat)
    encode_source out_source target_source encode_budget out_budget target_budget,
    audit_virtual_base_callbacks_erase EV g cb ->
    audit_graph_external_callback_adapter (audit_virtual_base_encode cb) weight encode_source
  encode_budget ->
    audit_graph_external_callback_adapter (audit_virtual_base_out cb) weight out_source out_budget
  ->
    audit_graph_external_callback_adapter (audit_virtual_base_target cb) weight target_source
  target_budget ->
    let '(vp, (result, (prepare_events, dfs_events))) := audit_virtual_source_search EV g cb in
    let budget := audit_virtual_adapter_call_budget encode_budget out_budget target_budget in
    vp = virtual_prepared p /\ result = virtual_dfs p /\
    audit_prepare_source_work
      (fun item => audit_virtual_full_internal_event_work item + audit_virtual_full_body_event_work
  weight item)
      prepare_events +
    audit_dfs_source_work
      (fun item => audit_virtual_full_internal_event_work item + audit_virtual_full_body_event_work
  weight item)
      dfs_events <= audit_virtual_source_search_budget EV g +
    audit_prepare_source_body_work budget prepare_events + audit_dfs_source_body_work budget
  dfs_events.
```

## Galois.Graph.GraphAuditScc

Card: AUD-GR-MODELS

Source destination: `theories/Graph/GraphAuditScc.v`.

```rocq
From Galois.Collections Require Import CollectionsAuditCost.
From Galois.Graph Require Import GraphAuditBase GraphAuditDfs.

From Stdlib Require Import List Bool PArith ZArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsTrie
  CollectionsFinSet CollectionsAuditCost.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphScc.
Import List.ListNotations.

Inductive audit_thelper_event (V E : Type) : Type :=
| THCase (site : nat)
| THGet (key : V) (m : Map.t V positive) (result : option positive)
| THGetEdges (key : V) (m : Map.t V (list E)) (result : option (list E))
| THSet (key : V) (value : positive) (m : Map.t V positive)
| THRemove (key : V) (m : Map.t V positive)
| THCompare (left right : V) (result : bool)
| THPosCompare (left right : positive) (result : bool)
| THMin (left right result : positive)
| THSucc (input result : positive)
| THTrieSet (key : positive) (members : list V) (m : Trie.t (list V)).
Arguments THCase {V E} _.
Arguments THGet {V E} _ _ _.
Arguments THGetEdges {V E} _ _ _.
Arguments THSet {V E} _ _ _.
Arguments THRemove {V E} _ _.
Arguments THCompare {V E} _ _ _.
Arguments THPosCompare {V E} _ _ _.
Arguments THMin {V E} _ _ _.
Arguments THSucc {V E} _ _.
Arguments THTrieSet {V E} _ _ _.

Definition audit_tarjan_discover_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (v : V) (st : tarjan_state V E)
    : tarjan_state V E * list (audit_thelper_event V E) :=
  let adjacent := Map.get EV v (out_index p) in
  let edges := match adjacent with Some xs => xs | None => [] end in
  let d := Map.set EV v (clock st) (disc st) in
  let l := Map.set EV v (clock st) (low st) in
  let next := Pos.succ (clock st) in
  (TarjanState (TarjanFrame v edges :: frames st) d l
    (v :: pending st) next (emitted st),
   [THGetEdges v (out_index p) adjacent; THSet v (clock st) (disc st);
    THSet v (clock st) (low st); THSucc (clock st) next]).

Definition audit_tarjan_lower_counted {V E} (EV : encoding V) (v : V) (n : positive)
    (st : tarjan_state V E) : tarjan_state V E * list (audit_thelper_event V E) :=
  let found := Map.get EV v (low st) in
  match found with
  | None => (st, [THGet v (low st) found; THCase 0])
  | Some old => let minimum := Pos.min old n in
      let next := TarjanState (frames st) (disc st) (Map.set EV v minimum (low st))
        (pending st) (clock st) (emitted st) in
      (next, [THGet v (low st) found; THCase 1; THMin old n minimum;
        THSet v minimum (low st)])
  end.

Fixpoint audit_tarjan_pop_counted {V E} (EV : encoding V) (root : V) (i : positive)
    (xs : list V) (links owners : Map.t V positive)
    : (list V * list V * Map.t V positive * Map.t V positive) * list (audit_thelper_event V E) :=
  match xs with
  | [] => (([], [], links, owners), [THCase 2])
  | v :: rest =>
      let links' := Map.remove EV v links in
      let owners' := Map.set EV v i owners in
      let equal := Pos.eqb (encode EV v) (encode EV root) in
      if equal then
        (([v], rest, links', owners'),
         [THCase 3; THRemove v links; THSet v i owners; THCompare v root equal; THCase 4])
      else
        let '(answer, later) := audit_tarjan_pop_counted EV root i rest links' owners' in
        let '(members, tail, links'', owners'') := answer in
        ((v :: members, tail, links'', owners''),
         [THCase 3; THRemove v links; THSet v i owners; THCompare v root equal; THCase 5] ++ later)
  end.

Definition audit_tarjan_emit_counted {V E} (EV : encoding V) (root : V) (st : tarjan_state V E)
    : tarjan_state V E * list (audit_thelper_event V E) :=
  let r := emitted st in
  let '(i, id_events) := match component_ids r with
    | [] => (1%positive, [THCase 6])
    | previous :: _ => let next := Pos.succ previous in (next, [THCase 7; THSucc previous next])
    end in
  let '(answer, pop_events) := audit_tarjan_pop_counted EV root i (pending st) (low st) (comp_of r)
  in
  let '(members, tail, links, owners) := answer in
  let component_map := Trie.set i members (component_at r) in
  (TarjanState (frames st) (disc st) links tail (clock st)
    (SccResult (members :: components r) (i :: component_ids r) component_map owners),
   id_events ++ pop_events ++ [THTrieSet i members (component_at r)]).

Definition audit_tarjan_close_counted {V E} (EV : encoding V) (v : V)
    (rest : list (tarjan_frame V E)) (st : tarjan_state V E)
    : tarjan_state V E * list (audit_thelper_event V E) :=
  let closed := TarjanState rest (disc st) (low st) (pending st) (clock st) (emitted st) in
  let lo := Map.get EV v (low st) in
  match lo with
  | None => (closed, [THGet v (low st) lo; THCase 8])
  | Some l => let di := Map.get EV v (disc st) in
    match di with
    | None => (closed, [THGet v (low st) lo; THGet v (disc st) di; THCase 9])
    | Some d => let eq := Pos.eqb l d in
      if eq then let '(next, events) := audit_tarjan_emit_counted EV v closed in
        (next, [THGet v (low st) lo; THGet v (disc st) di; THPosCompare l d eq; THCase 10] ++
  events)
      else match rest with
        | [] => (closed, [THGet v (low st) lo; THGet v (disc st) di; THPosCompare l d eq; THCase
  11])
        | parent :: _ => let '(next, events) := audit_tarjan_lower_counted EV (frame_node parent) l
  closed in
            (next, [THGet v (low st) lo; THGet v (disc st) di; THPosCompare l d eq; THCase 12] ++
  events)
        end
    end
  end.

Definition audit_thelper_event_work {V E} (EV : encoding V) (event : audit_thelper_event V E) : nat
  :=
  let enc v := audit_encoding_weight (audit_key_bits_weight (encode EV v)) in
  64 + match event with
  | THGet v _ _ | THGetEdges v _ _ => enc v + audit_get_weight (encode EV v)
  | THSet v _ _ => enc v + audit_set_weight (encode EV v)
  | THRemove v _ => enc v + audit_remove_weight (encode EV v)
  | THCompare a b _ => enc a + enc b + audit_binary_weight (Z.pos (encode EV a)) (Z.pos (encode EV
  b))
  | THPosCompare a b _ | THMin a b _ => audit_binary_weight (Z.pos a) (Z.pos b)
  | THSucc a _ => audit_binary_weight (Z.pos a) 1
  | THTrieSet key _ _ => audit_set_weight key
  | THCase _ => 0
  end.

Definition audit_thelper_work {V E} (EV : encoding V) (events : list (audit_thelper_event V E)) :
  nat :=
  fold_right (fun event total => audit_thelper_event_work EV event + total) 0 events.

Definition audit_tarjan_helpers_erasure_statement : Prop :=
  (forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) v st,
    fst (audit_tarjan_discover_counted p v st) = tarjan_discover p v st) /\
  (forall V E (EV : encoding V) v n (st : tarjan_state V E),
    fst (audit_tarjan_lower_counted EV v n st) = tarjan_lower EV v n st) /\
  (forall V E (EV : encoding V) root i xs links owners,
    fst (@audit_tarjan_pop_counted V E EV root i xs links owners) = tarjan_pop EV root i xs links
  owners) /\
  (forall V E (EV : encoding V) root (st : tarjan_state V E),
    fst (audit_tarjan_emit_counted EV root st) = tarjan_emit EV root st) /\
  (forall V E (EV : encoding V) v rest (st : tarjan_state V E),
    fst (audit_tarjan_close_counted EV v rest st) = tarjan_close EV v rest st).

Definition audit_tarjan_helpers_event_bound_statement : Prop :=
  (forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) v st,
    length (snd (audit_tarjan_discover_counted p v st)) = 4) /\
  (forall V E (EV : encoding V) v n (st : tarjan_state V E),
    length (snd (audit_tarjan_lower_counted EV v n st)) <= 4) /\
  (forall V E (EV : encoding V) root i xs links owners,
    length (snd (@audit_tarjan_pop_counted V E EV root i xs links owners)) <= 1 + 5 * length xs) /\
  (forall V E (EV : encoding V) root (st : tarjan_state V E),
    length (snd (audit_tarjan_emit_counted EV root st)) <= 4 + 5 * length (pending st)) /\
  (forall V E (EV : encoding V) v rest (st : tarjan_state V E),
    length (snd (audit_tarjan_close_counted EV v rest st)) <= 8 + 5 * length (pending st)).


From Galois.Graph Require Import GraphScc.

Inductive audit_tarjan_call (V E : Type) : Type :=
| AuditTarjanCase (site : nat)
| AuditTarjanTarget (edge : E) (target : V)
| AuditTarjanMember (v : V) (region : FinSet.t V) (result : bool)
| AuditTarjanGet (v : V) (map : Map.t V positive) (result : option positive)
| AuditTarjanDiscover (v : V) (before after : tarjan_state V E)
| AuditTarjanLower (v : V) (n : positive) (before after : tarjan_state V E)
| AuditTarjanClose (v : V) (rest : list (tarjan_frame V E)) (before after : tarjan_state V E)
| AuditTarjanHelper (event : audit_thelper_event V E)
| AuditTarjanSet (v : V) (before : FinSet.t V)
| AuditTarjanOutput (components identifiers : nat).
Arguments AuditTarjanCase {V E} _.
Arguments AuditTarjanTarget {V E} _ _.
Arguments AuditTarjanMember {V E} _ _ _.
Arguments AuditTarjanGet {V E} _ _ _.
Arguments AuditTarjanDiscover {V E} _ _ _.
Arguments AuditTarjanLower {V E} _ _ _ _.
Arguments AuditTarjanClose {V E} _ _ _ _.
Arguments AuditTarjanHelper {V E} _.
Arguments AuditTarjanSet {V E} _ _.
Arguments AuditTarjanOutput {V E} _ _.

Definition audit_tarjan_step_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (region : FinSet.t V) (st : tarjan_state V E)
    : tarjan_state V E * list (audit_tarjan_call V E) :=
  match frames st with
  | [] => (st, [AuditTarjanCase 0])
  | TarjanFrame v [] :: rest =>
      let '(next, detail) := audit_tarjan_close_counted EV v rest st in
      (next, AuditTarjanCase 1 :: map AuditTarjanHelper detail ++ [AuditTarjanClose v rest st next])
  | TarjanFrame v (edge :: edges) :: rest =>
      let advanced := TarjanState (TarjanFrame v edges :: rest) (disc st) (low st)
        (pending st) (clock st) (emitted st) in
      let target := Graph.target g edge in
      let inside := FinSet.mem EV target region in
      if inside then
        let found := Map.get EV target (disc st) in
        match found with
        | None => let '(next, detail) := audit_tarjan_discover_counted p target advanced in
            (next, [AuditTarjanTarget edge target; AuditTarjanMember target region inside;
              AuditTarjanCase 2; AuditTarjanGet target (disc st) found] ++
              map AuditTarjanHelper detail ++ [AuditTarjanDiscover target advanced next])
        | Some d => let on_stack := Map.get EV target (low st) in
            match on_stack with
            | None => (advanced, [AuditTarjanTarget edge target; AuditTarjanMember target region
  inside;
                AuditTarjanCase 2; AuditTarjanGet target (disc st) found;
                AuditTarjanGet target (low st) on_stack; AuditTarjanCase 3])
            | Some _ => let '(next, detail) := audit_tarjan_lower_counted EV v d advanced in
                (next, [AuditTarjanTarget edge target; AuditTarjanMember target region inside;
                  AuditTarjanCase 2; AuditTarjanGet target (disc st) found;
                  AuditTarjanGet target (low st) on_stack; AuditTarjanCase 4] ++
                  map AuditTarjanHelper detail ++ [AuditTarjanLower v d advanced next])
            end
        end
      else (advanced, [AuditTarjanTarget edge target; AuditTarjanMember target region inside;
        AuditTarjanCase 5])
  end.

Fixpoint audit_tarjan_run_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (region : FinSet.t V) (fuel : positive) (st : tarjan_state V E)
    : tarjan_state V E * list (audit_tarjan_call V E) :=
  match frames st with
  | [] => (st, [AuditTarjanCase 6])
  | _ :: _ => match fuel with
    | xH => let '(result, events) := audit_tarjan_step_counted p region st in
        (result, AuditTarjanCase 7 :: events)
    | xO rest => let '(middle, first) := audit_tarjan_run_counted p region rest st in
        let '(result, second) := audit_tarjan_run_counted p region rest middle in
        (result, AuditTarjanCase 8 :: first ++ second)
    | xI rest => let '(middle, first) := audit_tarjan_run_counted p region rest st in
        let '(last, second) := audit_tarjan_run_counted p region rest middle in
        let '(result, steps) := audit_tarjan_step_counted p region last in
        (result, AuditTarjanCase 9 :: first ++ second ++ steps)
    end
  end.

Definition audit_tarjan_root_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (region : FinSet.t V) (st : tarjan_state V E) (v : V)
    : tarjan_state V E * list (audit_tarjan_call V E) :=
  let found := Map.get EV v (disc st) in
  match found with
  | Some _ => (st, [AuditTarjanGet v (disc st) found; AuditTarjanCase 10])
  | None => let '(next, detail) := audit_tarjan_discover_counted p v st in
      let '(result, events) := audit_tarjan_run_counted p region (fuel p) next in
      (result, [AuditTarjanGet v (disc st) found; AuditTarjanCase 11] ++
        map AuditTarjanHelper detail ++ [AuditTarjanDiscover v st next] ++ events)
  end.

Fixpoint audit_tarjan_roots_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (region : FinSet.t V) (roots : list V) (st : tarjan_state V E)
    : tarjan_state V E * list (audit_tarjan_call V E) :=
  match roots with
  | [] => (st, [AuditTarjanCase 12])
  | root :: rest => let '(next, first) := audit_tarjan_root_counted p region st root in
      let '(result, later) := audit_tarjan_roots_counted p region rest next in
      (result, AuditTarjanCase 13 :: first ++ later)
  end.

Fixpoint audit_tarjan_region_counted {V E} (EV : encoding V) (region : list V) (set : FinSet.t V)
    : FinSet.t V * list (audit_tarjan_call V E) :=
  match region with
  | [] => (set, [AuditTarjanCase 14])
  | v :: rest => let next := FinSet.add EV v set in
      let '(result, events) := audit_tarjan_region_counted EV rest next in
      (result, AuditTarjanSet v set :: events)
  end.

Definition audit_scc_within_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (region : list V) : scc_result V * list (audit_tarjan_call V E) :=
  let '(keep, setup) := audit_tarjan_region_counted EV region FinSet.empty in
  let '(st, events) := audit_tarjan_roots_counted p keep region tarjan_initial in
  let r := emitted st in
  (tarjan_result st, setup ++ events ++ [AuditTarjanOutput (length (components r)) (length
  (component_ids r))]).

Definition audit_tarjan_event_work {V E} (EV : encoding V) (event : audit_tarjan_call V E) : nat :=
  64 + match event with
  | AuditTarjanMember v _ _ | AuditTarjanGet v _ _ =>
      audit_get_weight (encode EV v) + audit_encoding_weight (audit_key_bits_weight (encode EV v))
  | AuditTarjanSet v _ => audit_set_weight (encode EV v) + audit_encoding_weight
  (audit_key_bits_weight (encode EV v))
  | AuditTarjanHelper nested => audit_thelper_event_work EV nested
  | AuditTarjanOutput a b => a + b
  | _ => 0 end.

Definition audit_tarjan_model_work {V E} (EV : encoding V) (events : list (audit_tarjan_call V E)) :
  nat :=
  64 * S (length events) * S (length events) +
    fold_right (fun event n => audit_tarjan_event_work EV event + n) 0 events.

Definition audit_tarjan_input_event_bound {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (region : list V) : nat :=
  let steps := length region * S (Pos.to_nat (fuel p)) in
  (3 + length region * (12 + 12 * S (Pos.to_nat (fuel p)))) * (12 + 6 * S steps).

Definition audit_tarjan_input_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (region : list V) : nat :=
  let events := audit_tarjan_input_event_bound p region in
  let width := Nat.max (audit_dfs_input_width EV g p region)
    (audit_key_bits_weight (Pos.of_succ_nat (2 + length region * S (Pos.to_nat (fuel p))))) in
  128 * S events * S events + events * (140 + 12 * width).

Definition audit_scc_within_counted_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) region,
    let '(result, events) := audit_scc_within_counted p region in
    result = scc_within p region /\
    length events <= audit_tarjan_input_event_bound p region /\
    audit_tarjan_model_work EV events <= audit_tarjan_input_budget EV g p region.


Definition audit_tarjan_nested_event (V E B : Type) : Type := audit_tarjan_call V E * list B.

Definition audit_tarjan_nested_get {V E B A} (cb : audit_dfs_callback_model V E B) (v : V) (m :
  Map.t V A)
    : option A * list B := let '(code, body) := audit_dfs_encode_model cb v in (Map.code_get code m,
  body).

Definition audit_tarjan_nested_set {V E B A} (cb : audit_dfs_callback_model V E B) (v : V) (value :
  A) (m : Map.t V A)
    : Map.t V A * list B := let '(code, body) := audit_dfs_encode_model cb v in (Trie.set code (v,
  value) m, body).

Definition audit_tarjan_nested_remove {V E B A} (cb : audit_dfs_callback_model V E B) (v : V) (m :
  Map.t V A)
    : Map.t V A * list B := let '(code, body) := audit_dfs_encode_model cb v in (Trie.remove code m,
  body).

Definition audit_tarjan_nested_discover {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (v : V) (st : tarjan_state V E)
    : tarjan_state V E * list (audit_tarjan_nested_event V E B) :=
  let '(adjacent, out_body) := audit_tarjan_nested_get cb v (out_index p) in
  let edges := match adjacent with Some xs => xs | None => [] end in
  let '(d, d_body) := audit_tarjan_nested_set cb v (clock st) (disc st) in
  let '(l, l_body) := audit_tarjan_nested_set cb v (clock st) (low st) in
  let next := Pos.succ (clock st) in
  (TarjanState (TarjanFrame v edges :: frames st) d l (v :: pending st) next (emitted st),
   [(AuditTarjanHelper (THGetEdges v (out_index p) adjacent), out_body);
    (AuditTarjanHelper (THSet v (clock st) (disc st)), d_body);
    (AuditTarjanHelper (THSet v (clock st) (low st)), l_body);
    (AuditTarjanHelper (THSucc (clock st) next), [])]).

Definition audit_tarjan_nested_lower {V E B} (cb : audit_dfs_callback_model V E B)
    (v : V) (n : positive) (st : tarjan_state V E) : tarjan_state V E * list
  (audit_tarjan_nested_event V E B) :=
  let '(found, get_body) := audit_tarjan_nested_get cb v (low st) in
  match found with
  | None => (st, [(AuditTarjanHelper (THGet v (low st) found), get_body); (AuditTarjanHelper (THCase
  0), [])])
  | Some old => let minimum := Pos.min old n in
      let '(low_map, set_body) := audit_tarjan_nested_set cb v minimum (low st) in
      (TarjanState (frames st) (disc st) low_map (pending st) (clock st) (emitted st),
       [(AuditTarjanHelper (THGet v (low st) found), get_body); (AuditTarjanHelper (THCase 1), []);
        (AuditTarjanHelper (THMin old n minimum), []); (AuditTarjanHelper (THSet v minimum (low
  st)), set_body)])
  end.

Fixpoint audit_tarjan_nested_pop {V E B} (cb : audit_dfs_callback_model V E B) (root : V) (i :
  positive)
    (xs : list V) (links owners : Map.t V positive)
    : (list V * list V * Map.t V positive * Map.t V positive) * list (audit_tarjan_nested_event V E
  B) :=
  match xs with
  | [] => (([], [], links, owners), [(AuditTarjanHelper (THCase 2), [])])
  | v :: rest => let '(links', remove_body) := audit_tarjan_nested_remove cb v links in
      let '(owners', set_body) := audit_tarjan_nested_set cb v i owners in
      let '(v_code, v_body) := audit_dfs_encode_model cb v in
      let '(root_code, root_body) := audit_dfs_encode_model cb root in let equal := Pos.eqb v_code
  root_code in
      let head := [(AuditTarjanHelper (THCase 3), []); (AuditTarjanHelper (THRemove v links),
  remove_body);
        (AuditTarjanHelper (THSet v i owners), set_body); (AuditTarjanHelper (THCompare v root
  equal), v_body ++ root_body)] in
      if equal then (([v], rest, links', owners'), head ++ [(AuditTarjanHelper (THCase 4), [])])
      else let '(answer, later) := audit_tarjan_nested_pop cb root i rest links' owners' in
        let '(members, tail, links'', owners'') := answer in
        ((v :: members, tail, links'', owners''), head ++ [(AuditTarjanHelper (THCase 5), [])] ++
  later)
  end.

Definition audit_tarjan_nested_emit {V E B} (cb : audit_dfs_callback_model V E B) (root : V) (st :
  tarjan_state V E)
    : tarjan_state V E * list (audit_tarjan_nested_event V E B) :=
  let r := emitted st in
  let '(i, id_events) := match component_ids r with
    | [] => (1%positive, [(AuditTarjanHelper (THCase 6), [])])
    | previous :: _ => let next := Pos.succ previous in
        (next, [(AuditTarjanHelper (THCase 7), []); (AuditTarjanHelper (THSucc previous next), [])])
  end in
  let '(answer, pop_events) := audit_tarjan_nested_pop cb root i (pending st) (low st) (comp_of r)
  in
  let '(members, tail, links, owners) := answer in let component_map := Trie.set i members
  (component_at r) in
  (TarjanState (frames st) (disc st) links tail (clock st)
    (SccResult (members :: components r) (i :: component_ids r) component_map owners),
   id_events ++ pop_events ++ [(AuditTarjanHelper (THTrieSet i members (component_at r)), [])]).

Definition audit_tarjan_nested_close {V E B} (cb : audit_dfs_callback_model V E B) (v : V)
    (rest : list (tarjan_frame V E)) (st : tarjan_state V E)
    : tarjan_state V E * list (audit_tarjan_nested_event V E B) :=
  let closed := TarjanState rest (disc st) (low st) (pending st) (clock st) (emitted st) in
  let '(lo, lo_body) := audit_tarjan_nested_get cb v (low st) in
  match lo with
  | None => (closed, [(AuditTarjanHelper (THGet v (low st) lo), lo_body); (AuditTarjanHelper (THCase
  8), [])])
  | Some l => let '(di, di_body) := audit_tarjan_nested_get cb v (disc st) in
    let reads := [(AuditTarjanHelper (THGet v (low st) lo), lo_body);
      (AuditTarjanHelper (THGet v (disc st) di), di_body)] in
    match di with
    | None => (closed, reads ++ [(AuditTarjanHelper (THCase 9), [])])
    | Some d => let equal := Pos.eqb l d in
      if equal then let '(next, events) := audit_tarjan_nested_emit cb v closed in
        (next, reads ++ [(AuditTarjanHelper (THPosCompare l d equal), []); (AuditTarjanHelper
  (THCase 10), [])] ++ events)
      else match rest with
        | [] => (closed, reads ++ [(AuditTarjanHelper (THPosCompare l d equal), []);
  (AuditTarjanHelper (THCase 11), [])])
        | parent :: _ => let '(next, events) := audit_tarjan_nested_lower cb (frame_node parent) l
  closed in
            (next, reads ++ [(AuditTarjanHelper (THPosCompare l d equal), []); (AuditTarjanHelper
  (THCase 12), [])] ++ events)
        end
    end
  end.
Definition audit_tarjan_nested_step {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (region : FinSet.t V) (st :
  tarjan_state V E)
    : tarjan_state V E * list (audit_tarjan_nested_event V E B) :=
  match frames st with
  | [] => (st, [(AuditTarjanCase 0, [])])
  | TarjanFrame v [] :: rest => let '(next, detail) := audit_tarjan_nested_close cb v rest st in
      (next, (AuditTarjanCase 1, []) :: detail ++ [(AuditTarjanClose v rest st next, [])])
  | TarjanFrame v (edge :: edges) :: rest =>
      let advanced := TarjanState (TarjanFrame v edges :: rest) (disc st) (low st)
        (pending st) (clock st) (emitted st) in
      let '(target, target_body) := audit_dfs_target_model cb edge in
      let '(member, member_body) := audit_tarjan_nested_get cb target region in
      let inside := match member with Some _ => true | None => false end in
      if inside then let '(found, found_body) := audit_tarjan_nested_get cb target (disc st) in
        match found with
        | None => let '(next, detail) := audit_tarjan_nested_discover p cb target advanced in
            (next, [(AuditTarjanTarget edge target, target_body); (AuditTarjanMember target region
  inside, member_body);
              (AuditTarjanCase 2, []); (AuditTarjanGet target (disc st) found, found_body)] ++
  detail ++
              [(AuditTarjanDiscover target advanced next, [])])
        | Some d => let '(on_stack, low_body) := audit_tarjan_nested_get cb target (low st) in
          match on_stack with
          | None => (advanced, [(AuditTarjanTarget edge target, target_body); (AuditTarjanMember
  target region inside, member_body);
              (AuditTarjanCase 2, []); (AuditTarjanGet target (disc st) found, found_body);
              (AuditTarjanGet target (low st) on_stack, low_body); (AuditTarjanCase 3, [])])
          | Some _ => let '(next, detail) := audit_tarjan_nested_lower cb v d advanced in
              (next, [(AuditTarjanTarget edge target, target_body); (AuditTarjanMember target region
  inside, member_body);
                (AuditTarjanCase 2, []); (AuditTarjanGet target (disc st) found, found_body);
                (AuditTarjanGet target (low st) on_stack, low_body); (AuditTarjanCase 4, [])] ++
  detail ++
                [(AuditTarjanLower v d advanced next, [])])
          end
        end
      else (advanced, [(AuditTarjanTarget edge target, target_body); (AuditTarjanMember target
  region inside, member_body);
        (AuditTarjanCase 5, [])])
  end.

Fixpoint audit_tarjan_nested_run {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (region : FinSet.t V) (fuel :
  positive)
    (st : tarjan_state V E) : tarjan_state V E * list (audit_tarjan_nested_event V E B) :=
  match frames st with
  | [] => (st, [(AuditTarjanCase 6, [])])
  | _ :: _ => match fuel with
    | xH => let '(result, events) := audit_tarjan_nested_step p cb region st in
        (result, (AuditTarjanCase 7, []) :: events)
    | xO rest => let '(middle, first) := audit_tarjan_nested_run p cb region rest st in
        let '(result, second) := audit_tarjan_nested_run p cb region rest middle in
        (result, (AuditTarjanCase 8, []) :: first ++ second)
    | xI rest => let '(middle, first) := audit_tarjan_nested_run p cb region rest st in
        let '(last, second) := audit_tarjan_nested_run p cb region rest middle in
        let '(result, steps) := audit_tarjan_nested_step p cb region last in
        (result, (AuditTarjanCase 9, []) :: first ++ second ++ steps)
    end
  end.

Definition audit_tarjan_nested_root {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (region : FinSet.t V)
    (st : tarjan_state V E) (v : V) : tarjan_state V E * list (audit_tarjan_nested_event V E B) :=
  let '(found, body) := audit_tarjan_nested_get cb v (disc st) in
  match found with
  | Some _ => (st, [(AuditTarjanGet v (disc st) found, body); (AuditTarjanCase 10, [])])
  | None => let '(next, detail) := audit_tarjan_nested_discover p cb v st in
      let '(result, events) := audit_tarjan_nested_run p cb region (fuel p) next in
      (result, [(AuditTarjanGet v (disc st) found, body); (AuditTarjanCase 11, [])] ++
        detail ++ [(AuditTarjanDiscover v st next, [])] ++ events)
  end.

Fixpoint audit_tarjan_nested_roots {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (region : FinSet.t V)
    (roots : list V) (st : tarjan_state V E) : tarjan_state V E * list (audit_tarjan_nested_event V
  E B) :=
  match roots with
  | [] => (st, [(AuditTarjanCase 12, [])])
  | root :: rest => let '(next, here) := audit_tarjan_nested_root p cb region st root in
      let '(result, later) := audit_tarjan_nested_roots p cb region rest next in
      (result, (AuditTarjanCase 13, []) :: here ++ later)
  end.

Fixpoint audit_tarjan_nested_region {V E B} (cb : audit_dfs_callback_model V E B)
    (region : list V) (set : FinSet.t V) : FinSet.t V * list (audit_tarjan_nested_event V E B) :=
  match region with
  | [] => (set, [(AuditTarjanCase 14, [])])
  | v :: rest => let '(next, body) := audit_tarjan_nested_set cb v tt set in
      let '(result, events) := audit_tarjan_nested_region cb rest next in
      (result, (AuditTarjanSet v set, body) :: events)
  end.

Definition audit_scc_within_nested_counted {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (region : list V)
    : scc_result V * list (audit_tarjan_nested_event V E B) :=
  let '(keep, setup) := audit_tarjan_nested_region cb region FinSet.empty in
  let '(st, events) := audit_tarjan_nested_roots p cb keep region tarjan_initial in
  let r := emitted st in
  (tarjan_result st, setup ++ events ++ [(AuditTarjanOutput (length (components r)) (length
  (component_ids r)), [])]).

Definition audit_tarjan_nested_body_work {V E B} (weight : B -> nat)
    (events : list (audit_tarjan_nested_event V E B)) : nat :=
  fold_right (fun event total => fold_right (fun item n => weight item + n) 0 (snd event) + total) 0
  events.

Definition audit_tarjan_nested_total_work {V E B} (EV : encoding V) (weight : B -> nat)
    (events : list (audit_tarjan_nested_event V E B)) : nat :=
  audit_tarjan_model_work EV (map fst events) + audit_tarjan_nested_body_work weight events.

Definition audit_scc_within_nested_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
      (cb : audit_dfs_callback_model V E B) region,
    audit_dfs_callbacks_erase EV g cb ->
    let '(result, events) := audit_scc_within_nested_counted p cb region in
    result = scc_within p region /\ map fst events = snd (audit_scc_within_counted p region) /\
    length events <= audit_tarjan_input_event_bound p region /\
    audit_tarjan_model_work EV (map fst events) <= audit_tarjan_input_budget EV g p region.

Definition audit_scc_within_nested_total_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
      (cb : audit_dfs_callback_model V E B) (weight : B -> nat) region,
    audit_dfs_callbacks_erase EV g cb ->
    let '(_, events) := audit_scc_within_nested_counted p cb region in
    audit_tarjan_nested_total_work EV weight events <= audit_tarjan_input_budget EV g p region +
      audit_tarjan_nested_body_work weight events.

From Galois.Collections Require Import CollectionsAuditTrie CollectionsAuditPrimitive
  CollectionsAuditCompare CollectionsAuditEncoding.
Definition audit_scc_source_counted {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (region : list V) :=
  let captured := audit_graph_capture_callbacks cb in
  let '(keep, setup) := audit_tarjan_nested_region captured region FinSet.empty in
  let '(st, events) := audit_tarjan_nested_roots p captured keep region tarjan_initial in
  let r := emitted st in
  (SccResult (rev_append (components r) []) (rev_append (component_ids r) [])
    (component_at r) (comp_of r),
    setup ++ events ++ [(AuditTarjanOutput (length (components r)) (length (component_ids r)),
  [])]).

Definition audit_scc_source_codes {V E B} (body : list (audit_graph_callback_capture V E B)) :
  positive * positive :=
  match body with
  | [AuditGraphEncodeCapture _ _ _ _ first _; AuditGraphEncodeCapture _ _ _ _ second _] => (first,
  second)
  | _ => (1%positive, 1%positive)
  end.

Definition audit_scc_reverse_work := audit_graph_reverse_fast_work.
Definition audit_scc_reverse_run_statement : Prop :=
  audit_graph_reverse_run_statement /\ audit_graph_reverse_fast_run_statement /\
  audit_graph_reverse_fast_counted_statement.

Definition audit_scc_source_helper_work {V E B} (body : list (audit_graph_callback_capture V E B))
    (event : audit_thelper_event V E) : nat :=
  let code := audit_dfs_source_code body in
  match event with
  | THGet _ input _ => 5 + audit_trie_get_source_work code input
  | THGetEdges _ input _ => 5 + audit_trie_get_source_work code input
  | THSet key value input => 2 + audit_trie_update_source_work code (Some (key, value)) input
  | THRemove _ input => 2 + audit_trie_update_source_work code None input
  | THCompare _ _ _ => let '(a, b) := audit_scc_source_codes body in 4 + 2 * Nat.min (Pos.size_nat
  a) (Pos.size_nat b)
  | THPosCompare a b _ | THMin a b _ => 4 + 2 * Nat.min (Pos.size_nat a) (Pos.size_nat b)
  | THSucc a _ => 2 * Pos.size_nat a
  | THTrieSet key members input => 2 + audit_trie_update_source_work key (Some members) input
  | THCase _ => 0
  end.

Definition audit_scc_source_event_work {V E B} (weight : B -> nat)
    (item : audit_tarjan_nested_event V E (audit_graph_callback_capture V E B)) : nat :=
  let '(event, body) := item in let code := audit_dfs_source_code body in
  let callback := fold_right (fun item n => audit_graph_capture_work weight item + n) 0 body in
  64 + callback + match event with
  | AuditTarjanMember _ input _ => 5 + audit_trie_get_source_work code input
  | AuditTarjanGet _ input _ => 5 + audit_trie_get_source_work code input
  | AuditTarjanSet v input => 2 + audit_trie_update_source_work code (Some (v, tt)) input
  | AuditTarjanHelper helper => audit_scc_source_helper_work body helper
  | AuditTarjanOutput components identifiers =>
      audit_scc_reverse_work components + audit_scc_reverse_work identifiers
  | _ => 0
  end.

Definition audit_scc_source_event_wellformed {V E B}
    (item : audit_tarjan_nested_event V E (audit_graph_callback_capture V E B)) : Prop :=
  let '(event, body) := item in
  match event with
  | AuditTarjanMember v _ _ | AuditTarjanGet v _ _ | AuditTarjanSet v _ |
    AuditTarjanHelper (THGet v _ _) | AuditTarjanHelper (THGetEdges v _ _) |
    AuditTarjanHelper (THSet v _ _) | AuditTarjanHelper (THRemove v _) =>
      exists code trace, body = [AuditGraphEncodeCapture V E B v code trace]
  | AuditTarjanHelper (THCompare a b _) =>
      exists ac bc trace_a trace_b,
        body = [AuditGraphEncodeCapture V E B a ac trace_a; AuditGraphEncodeCapture V E B b bc
  trace_b]
  | AuditTarjanTarget edge vertex => exists trace, body = [AuditGraphTargetCapture V E B edge vertex
  trace]
  | _ => body = []
  end.

Definition audit_scc_source_work {V E B} (weight : B -> nat)
    (events : list (audit_tarjan_nested_event V E (audit_graph_callback_capture V E B))) : nat :=
  fold_right (fun event n => audit_scc_source_event_work weight event + n) 0 events.

Definition audit_scc_source_body_work {V E B} (weight : B -> nat)
    (events : list (audit_tarjan_nested_event V E (audit_graph_callback_capture V E B))) : nat :=
  fold_right (fun item n => fold_right (fun event k => audit_graph_capture_work weight event + k) 0
  (snd item) + n) 0 events.

Definition audit_scc_source_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (region : list V) : nat :=
  let count := audit_tarjan_input_event_bound p region in
  let width := Nat.max (audit_dfs_input_width EV g p region)
    (Pos.size_nat (Pos.of_succ_nat (2 + length region * S (Pos.to_nat (fuel p))))) in
  1024 * S count * S count + count * (512 + 64 * width).

Definition audit_scc_source_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (cb : audit_dfs_callback_model V E B) (weight : B -> nat) region,
    audit_dfs_callbacks_erase EV g cb ->
    let '(result, events) := audit_scc_source_counted p cb region in
    result = scc_within p region /\ Forall audit_scc_source_event_wellformed events /\
    length events <= audit_tarjan_input_event_bound p region /\
    audit_scc_source_work weight events <= audit_scc_source_budget EV g p region +
  audit_scc_source_body_work weight events.

Definition audit_scc_min_source_model (left right : positive) : positive * list
  audit_positive_compare_event :=
  let '(order, events) := audit_positive_compare left right in
  (match order with Gt => right | _ => left end, events).

Definition audit_scc_min_source_model_statement : Prop :=
  forall left right,
    let '(result, events) := audit_scc_min_source_model left right in
    result = Pos.min left right /\ 2 * length events <= 2 * Nat.min (Pos.size_nat left)
  (Pos.size_nat right).

Definition audit_scc_source_event_primitive {V E B}
    (item : audit_tarjan_nested_event V E (audit_graph_callback_capture V E B)) : Prop :=
  let '(event, body) := item in
  match event with
  | AuditTarjanHelper (THCompare _ _ result) =>
      let '(a, b) := audit_scc_source_codes body in fst (audit_positive_eqb a b) = result
  | AuditTarjanHelper (THPosCompare a b result) => fst (audit_positive_eqb a b) = result
  | AuditTarjanHelper (THMin a b result) => fst (audit_scc_min_source_model a b) = result
  | AuditTarjanHelper (THSucc input result) => fst (audit_positive_succ input) = result
  | _ => True
  end.

Definition audit_scc_source_primitive_correspondence_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (cb : audit_dfs_callback_model V E B) region,
    audit_dfs_callbacks_erase EV g cb ->
    Forall audit_scc_source_event_primitive (snd (audit_scc_source_counted p cb region)).

Definition audit_scc_source_library_obligations : Prop :=
  audit_trie_get_trace_adequate_statement /\ audit_trie_update_trace_adequate_statement /\
  audit_trie_get_source_work_bound_statement /\ audit_trie_update_source_work_bound_statement /\
  audit_positive_eqb_erases_statement /\ audit_positive_eqb_source_bound_statement /\
  audit_positive_compare_cont_statement /\ audit_positive_compare_statement /\
  audit_positive_succ_run_total_statement /\ audit_positive_succ_run_correct_statement /\
  audit_scc_min_source_model_statement /\ audit_scc_source_primitive_correspondence_statement /\
  audit_scc_reverse_run_statement.

Definition audit_scc_capture_budget {V E B} (encode_budget : V -> nat) (target_budget : E -> nat)
    (event : audit_graph_callback_capture V E B) : nat :=
  match event with
  | AuditGraphEncodeCapture _ _ _ vertex _ _ => encode_budget vertex
  | AuditGraphTargetCapture _ _ _ edge _ _ => target_budget edge
  end.

Definition audit_scc_source_external_budget {V E B} (encode_budget : V -> nat) (target_budget : E ->
  nat)
    (events : list (audit_tarjan_nested_event V E (audit_graph_callback_capture V E B))) : nat :=
  fold_right (fun item n => fold_right (fun event k => audit_scc_capture_budget encode_budget
  target_budget event + k)
    0 (snd item) + n) 0 events.

Definition audit_scc_source_adapted_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (cb : audit_dfs_callback_model V E B) (weight : B -> nat) region
    encode_source target_source encode_budget target_budget,
    audit_dfs_callbacks_erase EV g cb ->
    audit_graph_external_callback_adapter (audit_dfs_encode_model cb) weight encode_source
  encode_budget ->
    audit_graph_external_callback_adapter (audit_dfs_target_model cb) weight target_source
  target_budget ->
    let '(result, events) := audit_scc_source_counted p cb region in
    result = scc_within p region /\
    audit_scc_source_work weight events <= audit_scc_source_budget EV g p region +
      audit_scc_source_external_budget encode_budget target_budget events.

Definition audit_scc_source_contract_statement : Prop :=
  audit_scc_source_statement /\ audit_scc_source_library_obligations /\
  audit_scc_source_adapted_statement.
```

## Galois.Graph.GraphAuditWto

Card: AUD-GR-MODELS

Source destination: `theories/Graph/GraphAuditWto.v`.

```rocq
From Stdlib Require Import List Bool PArith ZArith.
From Galois.Collections Require Import CollectionsAuditCost CollectionsEncoding CollectionsMap
  CollectionsTrie CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphScc GraphWto.
Import List.ListNotations.
From Galois.Graph Require Import GraphAuditBase GraphAuditDfs GraphAuditScc.

From Galois.Graph Require Import GraphWto.

Inductive audit_wto_call (V E : Type) : Type :=
| AuditWtoCase (site : nat)
| AuditWtoDfs (event : audit_dfs_full_call V E)
| AuditWtoScc (event : audit_tarjan_call V E)
| AuditWtoRead (v : V) (m : Map.t V positive) (result : option positive)
| AuditWtoEdges (v : V) (m : Map.t V (list E)) (result : option (list E))
| AuditWtoWrite (v : V) (value : positive) (m : Map.t V positive)
| AuditWtoSucc (before after : positive)
| AuditWtoLe (a b : positive) (result : bool)
| AuditWtoEncode (v : V) (code : positive)
| AuditWtoTarget (e : E) (v : V)
| AuditWtoEqual (a b : positive) (result : bool)
| AuditWtoDepth (length : nat) (depth : positive)
| AuditWtoOutput (size : nat).
Arguments AuditWtoCase {V E} _.
Arguments AuditWtoDfs {V E} _.
Arguments AuditWtoScc {V E} _.
Arguments AuditWtoRead {V E} _ _ _.
Arguments AuditWtoEdges {V E} _ _ _.
Arguments AuditWtoWrite {V E} _ _ _.
Arguments AuditWtoSucc {V E} _ _.
Arguments AuditWtoLe {V E} _ _ _.
Arguments AuditWtoEncode {V E} _ _.
Arguments AuditWtoTarget {V E} _ _.
Arguments AuditWtoEqual {V E} _ _ _.
Arguments AuditWtoDepth {V E} _ _.
Arguments AuditWtoOutput {V E} _.

Fixpoint audit_wto_ranks_counted {V E} (EV : encoding V) (order : list V)
    (clock : positive) (m : Map.t V positive) : Map.t V positive * list (audit_wto_call V E) :=
  match order with
  | [] => (m, [AuditWtoCase 0])
  | v :: rest => let next_clock := Pos.succ clock in let next_map := Map.set EV v clock m in
      let '(result, events) := audit_wto_ranks_counted EV rest next_clock next_map in
      (result, AuditWtoCase 1 :: AuditWtoSucc clock next_clock :: AuditWtoWrite v clock m :: events)
  end.

Definition audit_wto_earlier_counted {V E} (EV : encoding V) (ranks : Map.t V positive) (u v : V)
    : V * list (audit_wto_call V E) :=
  let a := Map.get EV u ranks in let av := match a with Some n => n | None => 1%positive end in
  let b := Map.get EV v ranks in let bv := match b with Some n => n | None => 1%positive end in
  let choose := Pos.leb av bv in
  (if choose then u else v, [AuditWtoRead u ranks a; AuditWtoRead v ranks b; AuditWtoLe av bv
  choose]).

Fixpoint audit_wto_choose_counted {V E} (EV : encoding V) (ranks : Map.t V positive)
    (rest : list V) (header : V) : V * list (audit_wto_call V E) :=
  match rest with
  | [] => (header, [AuditWtoCase 2])
  | v :: tail => let '(next, here) := audit_wto_earlier_counted EV ranks header v in
      let '(result, later) := audit_wto_choose_counted EV ranks tail next in
      (result, AuditWtoCase 3 :: here ++ later)
  end.

Fixpoint audit_wto_remove_counted {V E} (EV : encoding V) (header : V) (vertices : list V)
    : list V * list (audit_wto_call V E) :=
  match vertices with
  | [] => ([], [AuditWtoCase 4])
  | v :: rest => let h := encode EV header in let k := encode EV v in let eq := Pos.eqb h k in
      let '(tail, later) := audit_wto_remove_counted EV header rest in
      (if eq then tail else v :: tail,
       AuditWtoCase 5 :: AuditWtoEncode header h :: AuditWtoEncode v k :: AuditWtoEqual h k eq ::
  later)
  end.

Fixpoint audit_wto_self_edges {V E} (EV : encoding V) (g : Graph.t V E) (v : V) (edges : list E)
    : bool * list (audit_wto_call V E) :=
  match edges with
  | [] => (false, [AuditWtoCase 6])
  | edge :: rest => let a := encode EV v in let target := Graph.target g edge in
      let b := encode EV target in let eq := Pos.eqb a b in
      let '(later, events) := audit_wto_self_edges EV g v rest in
      (eq || later, AuditWtoCase 7 :: AuditWtoEncode v a :: AuditWtoTarget edge target ::
        AuditWtoEncode target b :: AuditWtoEqual a b eq :: events)
  end.

Definition audit_wto_component_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (ranks : Map.t V positive) (recur : list V -> wto V * list (audit_wto_call V
  E))
    (component : list V) : wto V * list (audit_wto_call V E) :=
  match component with
  | [] => ([], [AuditWtoCase 8])
  | h :: rest => let '(header, choose_events) := audit_wto_choose_counted EV ranks rest h in
    match rest with
    | [] => let outgoing := Map.get EV h (out_index p) in
        let edges := match outgoing with Some xs => xs | None => [] end in
        let '(self, events) := audit_wto_self_edges EV g h edges in
        (if self then [WOpen h; WClose] else [WVertex h],
         AuditWtoCase 9 :: choose_events ++ AuditWtoCase 10 :: AuditWtoEdges h (out_index p)
  outgoing ::
           events ++ [AuditWtoOutput (if self then 2 else 1)])
    | _ :: _ => let '(smaller, remove_events) := audit_wto_remove_counted EV header component in
        let '(inside, events) := recur smaller in
        (WOpen header :: inside ++ [WClose], AuditWtoCase 9 :: choose_events ++ AuditWtoCase 11 ::
          remove_events ++ events ++ [AuditWtoOutput (2 + length inside)])
    end
  end.

Fixpoint audit_wto_components_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (ranks : Map.t V positive) (recur : list V -> wto V * list (audit_wto_call V
  E))
    (components : list (list V)) : wto V * list (audit_wto_call V E) :=
  match components with
  | [] => ([], [AuditWtoCase 12])
  | component :: rest => let '(first, here) := audit_wto_component_counted p ranks recur component
  in
      let '(later, events) := audit_wto_components_counted p ranks recur rest in
      (first ++ later, AuditWtoCase 13 :: here ++ events ++ [AuditWtoOutput (length first)])
  end.

Definition audit_wto_layer_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (ranks : Map.t V positive) (recur : list V -> wto V * list (audit_wto_call V
  E))
    (region : list V) : wto V * list (audit_wto_call V E) :=
  let '(sccs, scc_events) := audit_scc_within_counted p region in
  let '(result, events) := audit_wto_components_counted p ranks recur (rev (components sccs)) in
  (result, map AuditWtoScc scc_events ++ [AuditWtoOutput (length (components sccs))] ++ events).

Definition audit_wto_iter_event {V E} (event : audit_comb_event (audit_wto_call V E)) :
  audit_wto_call V E :=
  match event with AuditCombCase site => AuditWtoCase (20 + site) | AuditCombBody body => body end.

Definition audit_wto_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) : wto V * list (audit_wto_call V E) :=
  let '(search, dfs_events) := audit_dfs_full_counted p FinSet.empty (Graph.entries g) in
  let order := rpo search in
  let '(ranks, rank_events) := audit_wto_ranks_counted EV order 1%positive Map.empty in
  let depth := Pos.of_succ_nat (length order) in
  let base := fun _ : list V => (@nil (wto_token V), @nil (audit_wto_call V E)) in
  let step := fun recur => (audit_wto_layer_counted p ranks recur, @nil (audit_wto_call V E)) in
  let '(run, iter_events) := audit_pos_iter step base depth in
  let '(result, events) := run order in
  (result, map AuditWtoDfs dfs_events ++ [AuditWtoOutput (length (postorder search))] ++
    rank_events ++ [AuditWtoDepth (length order) depth] ++ map audit_wto_iter_event iter_events ++
  events ++ [AuditWtoOutput (length result)]).
Definition audit_wto_event_work {V E} (EV : encoding V) (event : audit_wto_call V E) : nat :=
  64 + match event with
  | AuditWtoDfs item => audit_dfs_full_model_event EV item
  | AuditWtoScc item => audit_tarjan_event_work EV item
  | AuditWtoRead v _ _ | AuditWtoEdges v _ _ =>
      audit_encoding_weight (audit_key_bits_weight (encode EV v)) + audit_get_weight (encode EV v)
  | AuditWtoWrite v _ _ =>
      audit_encoding_weight (audit_key_bits_weight (encode EV v)) + audit_set_weight (encode EV v)
  | AuditWtoSucc a _ => audit_binary_weight (Z.pos a) 1
  | AuditWtoLe a b _ | AuditWtoEqual a b _ => audit_binary_weight (Z.pos a) (Z.pos b)
  | AuditWtoEncode _ code => audit_encoding_weight (audit_key_bits_weight code)
  | AuditWtoOutput size => S size
  | AuditWtoDepth len depth => audit_unary_conversion_weight len + len * audit_key_bits_weight depth
  | _ => 0 end.

Definition audit_wto_model_work {V E} (EV : encoding V) (events : list (audit_wto_call V E)) : nat
  :=
  256 * S (length events) * S (length events) +
    fold_right (fun event total => audit_wto_event_work EV event + total) 0 events.

Definition audit_wto_input_order_bound {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) : nat := length (Graph.entries g) * S (Pos.to_nat (fuel p)).

Definition audit_wto_input_max_out {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) : nat :=
  fold_right (fun row n => Nat.max (length (snd row)) n) 0 (Map.elements (out_index p)).

Definition audit_wto_input_event_bound {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) : nat :=
  let n := audit_wto_input_order_bound p in
  let f := S (Pos.to_nat (fuel p)) in
  let m := audit_wto_input_max_out p in
  let scc_bound := (3 + n * (12 + 12 * f)) * (12 + 6 * S (n * f)) in
  1024 * Nat.pow (S n) (S n) * Nat.pow (S (scc_bound + n * (m + n) + f)) 3.

Definition audit_wto_input_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) : nat :=
  let n := audit_wto_input_order_bound p in
  let events := audit_wto_input_event_bound p in
  let width := Nat.max (audit_dfs_full_input_width EV g p (Graph.entries g))
    (audit_key_bits_weight (Pos.of_succ_nat (2 + n * S (Pos.to_nat (fuel p))))) in
  1024 * S events * S events + events * (512 + 24 * width).

Definition audit_wto_counted_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g),
    let '(result, events) := audit_wto_counted p in
    result = wto_of p /\
    length events <= audit_wto_input_event_bound p /\
    audit_wto_model_work EV events <= audit_wto_input_budget EV g p.

From Galois.Graph Require Import GraphWto.

Definition audit_wto_nested_event (V E B : Type) : Type := audit_wto_call V E * list B.

Fixpoint audit_wto_nested_ranks {V E B} (cb : audit_dfs_callback_model V E B) (order : list V)
    (clock : positive) (m : Map.t V positive) : Map.t V positive * list (audit_wto_nested_event V E
  B) :=
  match order with
  | [] => (m, [(AuditWtoCase 0, [])])
  | v :: rest => let next_clock := Pos.succ clock in
      let '(next_map, body) := audit_tarjan_nested_set cb v clock m in
      let '(result, events) := audit_wto_nested_ranks cb rest next_clock next_map in
      (result, (AuditWtoCase 1, []) :: (AuditWtoSucc clock next_clock, []) :: (AuditWtoWrite v clock
  m, body) :: events)
  end.

Definition audit_wto_nested_earlier {V E B} (cb : audit_dfs_callback_model V E B)
    (ranks : Map.t V positive) (u v : V) : V * list (audit_wto_nested_event V E B) :=
  let '(a, a_body) := audit_tarjan_nested_get cb u ranks in
  let av := match a with Some n => n | None => 1%positive end in
  let '(b, b_body) := audit_tarjan_nested_get cb v ranks in
  let bv := match b with Some n => n | None => 1%positive end in let choose := Pos.leb av bv in
  (if choose then u else v, [(AuditWtoRead u ranks a, a_body); (AuditWtoRead v ranks b, b_body);
  (AuditWtoLe av bv choose, [])]).

Fixpoint audit_wto_nested_choose {V E B} (cb : audit_dfs_callback_model V E B)
    (ranks : Map.t V positive) (rest : list V) (header : V) : V * list (audit_wto_nested_event V E
  B) :=
  match rest with
  | [] => (header, [(AuditWtoCase 2, [])])
  | v :: tail => let '(next, here) := audit_wto_nested_earlier cb ranks header v in
      let '(result, later) := audit_wto_nested_choose cb ranks tail next in
      (result, (AuditWtoCase 3, []) :: here ++ later)
  end.

Fixpoint audit_wto_nested_remove {V E B} (cb : audit_dfs_callback_model V E B) (header : V)
  (vertices : list V)
    : list V * list (audit_wto_nested_event V E B) :=
  match vertices with
  | [] => ([], [(AuditWtoCase 4, [])])
  | v :: rest => let '(h, h_body) := audit_dfs_encode_model cb header in
      let '(k, k_body) := audit_dfs_encode_model cb v in let equal := Pos.eqb h k in
      let '(tail, later) := audit_wto_nested_remove cb header rest in
      (if equal then tail else v :: tail, [(AuditWtoCase 5, []); (AuditWtoEncode header h, h_body);
        (AuditWtoEncode v k, k_body); (AuditWtoEqual h k equal, [])] ++ later)
  end.

Fixpoint audit_wto_nested_self_edges {V E B} (cb : audit_dfs_callback_model V E B)
    (v : V) (edges : list E) : bool * list (audit_wto_nested_event V E B) :=
  match edges with
  | [] => (false, [(AuditWtoCase 6, [])])
  | edge :: rest => let '(a, a_body) := audit_dfs_encode_model cb v in
      let '(target, target_body) := audit_dfs_target_model cb edge in
      let '(b, b_body) := audit_dfs_encode_model cb target in let equal := Pos.eqb a b in
      let '(later, events) := audit_wto_nested_self_edges cb v rest in
      (equal || later, [(AuditWtoCase 7, []); (AuditWtoEncode v a, a_body); (AuditWtoTarget edge
  target, target_body);
        (AuditWtoEncode target b, b_body); (AuditWtoEqual a b equal, [])] ++ events)
  end.

Definition audit_wto_nested_component {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (ranks : Map.t V positive)
    (recur : list V -> wto V * list (audit_wto_nested_event V E B)) (component : list V)
    : wto V * list (audit_wto_nested_event V E B) :=
  match component with
  | [] => ([], [(AuditWtoCase 8, [])])
  | h :: rest => let '(header, choose_events) := audit_wto_nested_choose cb ranks rest h in
    match rest with
    | [] => let '(outgoing, out_body) := audit_tarjan_nested_get cb h (out_index p) in
        let edges := match outgoing with Some xs => xs | None => [] end in
        let '(self, events) := audit_wto_nested_self_edges cb h edges in
        (if self then [WOpen h; WClose] else [WVertex h],
         (AuditWtoCase 9, []) :: choose_events ++ [(AuditWtoCase 10, []); (AuditWtoEdges h
  (out_index p) outgoing, out_body)] ++
           events ++ [(AuditWtoOutput (if self then 2 else 1), [])])
    | _ :: _ => let '(smaller, remove_events) := audit_wto_nested_remove cb header component in
        let '(inside, events) := recur smaller in
        (WOpen header :: inside ++ [WClose], (AuditWtoCase 9, []) :: choose_events ++ [(AuditWtoCase
  11, [])] ++
          remove_events ++ events ++ [(AuditWtoOutput (2 + length inside), [])])
    end
  end.

Fixpoint audit_wto_nested_components {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (ranks : Map.t V positive)
    (recur : list V -> wto V * list (audit_wto_nested_event V E B)) (components : list (list V))
    : wto V * list (audit_wto_nested_event V E B) :=
  match components with
  | [] => ([], [(AuditWtoCase 12, [])])
  | component :: rest => let '(first, here) := audit_wto_nested_component p cb ranks recur component
  in
      let '(later, events) := audit_wto_nested_components p cb ranks recur rest in
      (first ++ later, (AuditWtoCase 13, []) :: here ++ events ++ [(AuditWtoOutput (length first),
  [])])
  end.

Definition audit_wto_nested_layer {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (ranks : Map.t V positive)
    (recur : list V -> wto V * list (audit_wto_nested_event V E B)) (region : list V)
    : wto V * list (audit_wto_nested_event V E B) :=
  let '(sccs, scc_events) := audit_scc_within_nested_counted p cb region in
  let '(result, events) := audit_wto_nested_components p cb ranks recur (rev (components sccs)) in
  (result, map (fun item => (AuditWtoScc (fst item), snd item)) scc_events ++
    [(AuditWtoOutput (length (components sccs)), [])] ++ events).

Definition audit_wto_nested_counted {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B)
    : wto V * list (audit_wto_nested_event V E B) :=
  let '(search, dfs_events) := audit_dfs_nested_counted p cb FinSet.empty (Graph.entries g) in
  let order := rpo search in let '(ranks, rank_events) := audit_wto_nested_ranks cb order 1%positive
  Map.empty in
  let depth := Pos.of_succ_nat (length order) in
  let base := fun _ : list V => (@nil (wto_token V), @nil (audit_wto_nested_event V E B)) in
  let step := fun recur => (audit_wto_nested_layer p cb ranks recur, @nil (audit_wto_call V E)) in
  let '(run, iter_events) := audit_pos_iter step base depth in let '(result, events) := run order in
  (result, map (fun item => (AuditWtoDfs (fst item), snd item)) dfs_events ++
    [(AuditWtoOutput (length (postorder search)), [])] ++ rank_events ++ [(AuditWtoDepth (length
  order) depth, [])] ++
    map (fun e => (audit_wto_iter_event e, [])) iter_events ++ events ++ [(AuditWtoOutput (length
  result), [])]).

Definition audit_wto_nested_body_work {V E B} (weight : B -> nat) (events : list
  (audit_wto_nested_event V E B)) : nat :=
  fold_right (fun event total => fold_right (fun item n => weight item + n) 0 (snd event) + total) 0
  events.

Definition audit_wto_nested_total_work {V E B} (EV : encoding V) (weight : B -> nat)
    (events : list (audit_wto_nested_event V E B)) : nat :=
  audit_wto_model_work EV (map fst events) + audit_wto_nested_body_work weight events.

Definition audit_wto_nested_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
      (cb : audit_dfs_callback_model V E B) (weight : B -> nat),
    audit_dfs_callbacks_erase EV g cb ->
    let '(result, events) := audit_wto_nested_counted p cb in
    result = wto_of p /\ map fst events = snd (audit_wto_counted p) /\
    length events <= audit_wto_input_event_bound p /\
    audit_wto_nested_total_work EV weight events <= audit_wto_input_budget EV g p +
      audit_wto_nested_body_work weight events.

From Galois.Collections Require Import CollectionsAuditTrie CollectionsAuditPrimitive
  CollectionsAuditCompare CollectionsAuditEncoding.
Definition audit_wto_source_layer {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (ranks : Map.t V positive)
    (recur : list V -> wto V * list (audit_wto_nested_event V E (audit_graph_callback_capture V E
  B)))
    (region : list V) : wto V * list (audit_wto_nested_event V E (audit_graph_callback_capture V E
  B)) :=
  let '(sccs, scc_events) := audit_scc_source_counted p cb region in
  let '(result, events) := audit_wto_nested_components p (audit_graph_capture_callbacks cb) ranks
  recur
    (rev_append (components sccs) []) in
  (result, map (fun item => (AuditWtoScc (fst item), snd item)) scc_events ++
    [(AuditWtoOutput (length (components sccs)), [])] ++ events).

Definition audit_wto_source_counted {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B)
    : wto V * list (audit_wto_nested_event V E (audit_graph_callback_capture V E B)) :=
  let '(search, dfs_events) := audit_dfs_source_counted p cb FinSet.empty (Graph.entries g) in
  let order := rev_append (postorder search) [] in
  let captured := audit_graph_capture_callbacks cb in
  let '(ranks, rank_events) := audit_wto_nested_ranks captured order 1%positive Map.empty in
  let depth := Pos.of_succ_nat (length order) in
  let base := fun _ : list V => (@nil (wto_token V),
    @nil (audit_wto_nested_event V E (audit_graph_callback_capture V E B))) in
  let step := fun recur => (audit_wto_source_layer p cb ranks recur, @nil (audit_wto_call V E)) in
  let '(run, iter_events) := audit_pos_iter step base depth in let '(result, events) := run order in
  (result, map (fun item => (AuditWtoDfs (fst item), snd item)) dfs_events ++
    [(AuditWtoOutput (length (postorder search)), [])] ++ rank_events ++ [(AuditWtoDepth (length
  order) depth, [])] ++
    map (fun event => (audit_wto_iter_event event, [])) iter_events ++ events ++ [(AuditWtoOutput
  (length result), [])]).

Definition audit_wto_source_event_work {V E B} (weight : B -> nat)
    (item : audit_wto_nested_event V E (audit_graph_callback_capture V E B)) : nat :=
  let '(event, body) := item in let code := audit_dfs_source_code body in
  let callback := fold_right (fun event n => audit_graph_capture_work weight event + n) 0 body in
  match event with
  | AuditWtoDfs event => 64 + audit_dfs_source_event_work weight (event, body)
  | AuditWtoScc event => 64 + audit_scc_source_event_work weight (event, body)
  | AuditWtoRead _ input _ => 69 + callback + audit_trie_get_source_work code input
  | AuditWtoEdges _ input _ => 69 + callback + audit_trie_get_source_work code input
  | AuditWtoWrite v value input => 66 + callback + audit_trie_update_source_work code (Some (v,
  value)) input
  | AuditWtoSucc before _ => 64 + callback + 2 * Pos.size_nat before
  | AuditWtoLe a b _ | AuditWtoEqual a b _ => 68 + callback + 2 * Nat.min (Pos.size_nat a)
  (Pos.size_nat b)
  | AuditWtoDepth n depth => 64 + callback + audit_unary_conversion_weight n + 2 * S n * S
  (Pos.size_nat depth)
  | AuditWtoOutput n => 64 + callback + audit_graph_reverse_fast_work n + S n
  | AuditWtoCase _ | AuditWtoEncode _ _ | AuditWtoTarget _ _ => 64 + callback
  end.

Definition audit_wto_source_work {V E B} (weight : B -> nat)
    (events : list (audit_wto_nested_event V E (audit_graph_callback_capture V E B))) : nat :=
  fold_right (fun event n => audit_wto_source_event_work weight event + n) 0 events.

Definition audit_wto_source_body_work {V E B} (weight : B -> nat)
    (events : list (audit_wto_nested_event V E (audit_graph_callback_capture V E B))) : nat :=
  fold_right (fun item n => fold_right (fun event k => audit_graph_capture_work weight event + k) 0
  (snd item) + n) 0 events.

Definition audit_wto_source_budget {V E} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) :
  nat :=
  let count := audit_wto_input_event_bound p in
  let width := Nat.max (audit_dfs_full_input_width EV g p (Graph.entries g))
    (Pos.size_nat (Pos.of_succ_nat (2 + audit_wto_input_order_bound p * S (Pos.to_nat (fuel p)))))
  in
  4096 * Nat.pow (S count) 3 + count * (1024 + 128 * width).

Definition audit_wto_source_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (cb : audit_dfs_callback_model V E B) (weight : B -> nat),
    audit_dfs_callbacks_erase EV g cb ->
    let '(result, events) := audit_wto_source_counted p cb in
    result = wto_of p /\ length events <= audit_wto_input_event_bound p /\
    audit_wto_source_work weight events <= audit_wto_source_budget EV g p +
  audit_wto_source_body_work weight events.

Definition audit_wto_source_external_budget {V E B} (encode_budget : V -> nat) (target_budget : E ->
  nat)
    (events : list (audit_wto_nested_event V E (audit_graph_callback_capture V E B))) : nat :=
  fold_right (fun item n => fold_right (fun event k => audit_scc_capture_budget encode_budget
  target_budget event + k)
    0 (snd item) + n) 0 events.

Definition audit_wto_source_event_wellformed {V E B}
    (item : audit_wto_nested_event V E (audit_graph_callback_capture V E B)) : Prop :=
  let '(event, body) := item in
  match event with
  | AuditWtoDfs nested => audit_dfs_source_event_wellformed (nested, body)
  | AuditWtoScc nested => audit_scc_source_event_wellformed (nested, body)
  | AuditWtoRead v _ _ | AuditWtoEdges v _ _ | AuditWtoWrite v _ _ =>
      exists code trace, body = [AuditGraphEncodeCapture V E B v code trace]
  | AuditWtoEncode v code => exists trace, body = [AuditGraphEncodeCapture V E B v code trace]
  | AuditWtoTarget edge v => exists trace, body = [AuditGraphTargetCapture V E B edge v trace]
  | _ => body = []
  end.

Definition audit_wto_source_event_primitive {V E B}
    (item : audit_wto_nested_event V E (audit_graph_callback_capture V E B)) : Prop :=
  let '(event, body) := item in
  match event with
  | AuditWtoDfs nested => audit_dfs_source_successor_event (nested, body)
  | AuditWtoScc nested => audit_scc_source_event_primitive (nested, body)
  | AuditWtoSucc before after => fst (audit_positive_succ before) = after
  | AuditWtoLe a b result => fst (audit_positive_leb a b) = result
  | AuditWtoEqual a b result => fst (audit_positive_eqb a b) = result
  | AuditWtoDepth size depth => fst (audit_nat_encode size) = depth
  | _ => True
  end.

Definition audit_wto_source_event_correspondence_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (cb : audit_dfs_callback_model V E B), audit_dfs_callbacks_erase EV g cb ->
    let '(_, events) := audit_wto_source_counted p cb in
    Forall audit_wto_source_event_wellformed events /\ Forall audit_wto_source_event_primitive
  events.

Definition audit_wto_source_adapted_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (cb : audit_dfs_callback_model V E B) (weight : B -> nat) encode_source target_source
  encode_budget target_budget,
    audit_dfs_callbacks_erase EV g cb ->
    audit_graph_external_callback_adapter (audit_dfs_encode_model cb) weight encode_source
  encode_budget ->
    audit_graph_external_callback_adapter (audit_dfs_target_model cb) weight target_source
  target_budget ->
    let '(result, events) := audit_wto_source_counted p cb in
    result = wto_of p /\ audit_wto_source_work weight events <= audit_wto_source_budget EV g p +
      audit_wto_source_external_budget encode_budget target_budget events.

Definition audit_wto_source_contract_statement : Prop :=
  audit_wto_source_statement /\ audit_wto_source_adapted_statement /\
  audit_scc_source_contract_statement /\
  audit_dfs_source_contract_statement /\ audit_graph_reverse_fast_counted_statement /\
  audit_nat_encode_run_total_statement /\ audit_nat_encode_run_correct_statement /\
  audit_positive_order_statement /\ audit_wto_source_event_correspondence_statement.
```

## Galois.Graph.GraphAuditLoops

Card: AUD-GR-MODELS

Source destination: `theories/Graph/GraphAuditLoops.v`.

```rocq
(** * Loop forest source contracts

    The model records component searches, header removal and loop forest packing.
    For example, each cyclic component retains its actual SCC and child-map events.
    Builds on: graph DFS and SCC source models and collection source models. *)
From Stdlib Require Import List Bool PArith NArith ZArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet
  CollectionsAuditCost CollectionsAuditTrie CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditPrimitive CollectionsAuditCompare CollectionsAuditUnion
  CollectionsAuditMapTraverse CollectionsAuditEncoding.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphScc GraphLoops
  GraphAuditBase GraphAuditDfs GraphAuditScc GraphAuditWto.
Import List.ListNotations.
Inductive audit_loop_call (V E : Type) : Type :=
| AuditLoopCase (site : nat)
| AuditLoopDfs (event : audit_dfs_full_call V E)
| AuditLoopScc (event : audit_tarjan_call V E)
| AuditLoopRead (v : V) (m : Map.t V positive) (result : option positive)
| AuditLoopEdges (v : V) (m : Map.t V (list E)) (result : option (list E))
| AuditLoopEncode (v : V) (code : positive)
| AuditLoopTarget (e : E) (v : V)
| AuditLoopCompare (a b : positive) (result : bool)
| AuditLoopSet (v : V) (before : FinSet.t V)
| AuditLoopNodeWrite (v : V) (value : FinSet.t V) (before : Map.t V (FinSet.t V))
| AuditLoopParentWrite (v value : V) (before : Map.t V V)
| AuditLoopMap (head : V) (input : FinSet.t V) (result : Map.t V V)
| AuditLoopUnion (left right result : Map.t V V)
| AuditLoopOutput (size : nat)
| AuditLoopDepth (size : nat) (depth : N).
Arguments AuditLoopCase {V E} _.
Arguments AuditLoopDfs {V E} _.
Arguments AuditLoopScc {V E} _.
Arguments AuditLoopRead {V E} _ _ _.
Arguments AuditLoopEdges {V E} _ _ _.
Arguments AuditLoopEncode {V E} _ _.
Arguments AuditLoopTarget {V E} _ _.
Arguments AuditLoopCompare {V E} _ _ _.
Arguments AuditLoopSet {V E} _ _.
Arguments AuditLoopNodeWrite {V E} _ _ _.
Arguments AuditLoopParentWrite {V E} _ _ _.
Arguments AuditLoopMap {V E} _ _ _.
Arguments AuditLoopUnion {V E} _ _ _.
Arguments AuditLoopOutput {V E} _.
Arguments AuditLoopDepth {V E} _ _.

Fixpoint audit_loop_choose_counted {V E} (EV : encoding V) (numbers : Map.t V positive)
    (component : list V) : option V * list (audit_loop_call V E) :=
  match component with
  | [] => (None, [AuditLoopCase 0])
  | v :: rest => let '(chosen, events) := audit_loop_choose_counted EV numbers rest in
    match chosen with
    | None => (Some v, AuditLoopCase 1 :: events ++ [AuditLoopCase 2])
    | Some w => let a := Map.get EV w numbers in let av := match a with Some n => n | None =>
  1%positive end in
        let b := Map.get EV v numbers in let bv := match b with Some n => n | None => 1%positive end
  in
        let le := Pos.leb av bv in
        (Some (if le then v else w), AuditLoopCase 1 :: events ++
          [AuditLoopCase 3; AuditLoopRead w numbers a; AuditLoopRead v numbers b; AuditLoopCompare
  av bv le])
    end
  end.

Fixpoint audit_loop_without_counted {V E} (EV : encoding V) (header : V) (component : list V)
    : list V * list (audit_loop_call V E) :=
  match component with
  | [] => ([], [AuditLoopCase 4])
  | v :: rest => let a := encode EV v in let b := encode EV header in let eq := Pos.eqb a b in
      let '(tail, events) := audit_loop_without_counted EV header rest in
      (if eq then tail else v :: tail,
       AuditLoopCase 5 :: AuditLoopEncode v a :: AuditLoopEncode header b :: AuditLoopCompare a b eq
  :: events)
  end.

Fixpoint audit_loop_self_edges {V E} (EV : encoding V) (g : Graph.t V E) (v : V) (edges : list E)
    : bool * list (audit_loop_call V E) :=
  match edges with
  | [] => (false, [AuditLoopCase 6])
  | e :: rest => let target := Graph.target g e in let a := encode EV target in
      let b := encode EV v in let eq := Pos.eqb a b in
      let '(later, events) := audit_loop_self_edges EV g v rest in
      (eq || later, AuditLoopCase 7 :: AuditLoopTarget e target :: AuditLoopEncode target a ::
        AuditLoopEncode v b :: AuditLoopCompare a b eq :: events)
  end.

Definition audit_loop_cyclic_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (component : list V) : bool * list (audit_loop_call V E) :=
  match component with
  | [] => (false, [AuditLoopCase 8])
  | [v] => let found := Map.get EV v (out_index p) in
      let edges := match found with Some xs => xs | None => [] end in
      let '(result, events) := audit_loop_self_edges EV g v edges in
      (result, AuditLoopCase 9 :: AuditLoopEdges v (out_index p) found :: events)
  | _ :: _ :: _ => (true, [AuditLoopCase 10])
  end.

Definition audit_loop_block_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (numbers : Map.t V positive)
    (descend : option V -> list V -> list (loop_entry V) * list (audit_loop_call V E))
    (parent : option V) (region component : list V) : list (loop_entry V) * list (audit_loop_call V
  E) :=
  let '(cyclic, cyclic_events) := audit_loop_cyclic_counted p component in
  if cyclic then let '(chosen, choose_events) := audit_loop_choose_counted EV numbers component in
    match chosen with
    | None => ([], cyclic_events ++ AuditLoopCase 11 :: choose_events ++ [AuditLoopCase 12])
    | Some header => let '(smaller, remove_events) := audit_loop_without_counted EV header component
  in
        let '(children, child_events) := descend (Some header) smaller in
        (LoopEntry header component parent region :: children,
         cyclic_events ++ AuditLoopCase 11 :: choose_events ++ AuditLoopCase 13 ::
           remove_events ++ child_events ++ [AuditLoopOutput 1])
    end
  else ([], cyclic_events ++ [AuditLoopCase 14]).

Fixpoint audit_loop_blocks_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (numbers : Map.t V positive)
    (descend : option V -> list V -> list (loop_entry V) * list (audit_loop_call V E))
    (parent : option V) (region : list V) (components : list (list V))
    : list (loop_entry V) * list (audit_loop_call V E) :=
  match components with
  | [] => ([], [AuditLoopCase 15])
  | component :: rest => let '(first, here) := audit_loop_block_counted p numbers descend parent
  region component in
      let '(later, events) := audit_loop_blocks_counted p numbers descend parent region rest in
      (first ++ later, AuditLoopCase 16 :: here ++ events ++ [AuditLoopOutput (length first)])
  end.

Definition audit_loop_layer_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (numbers : Map.t V positive)
    (descend : option V -> list V -> list (loop_entry V) * list (audit_loop_call V E))
    (parent : option V) (region : list V) : list (loop_entry V) * list (audit_loop_call V E) :=
  let '(sccs, scc_events) := audit_scc_within_counted p region in
  let '(result, events) := audit_loop_blocks_counted p numbers descend parent region (components
  sccs) in
  (result, map AuditLoopScc scc_events ++ events).

Definition audit_loop_iter_event {V E} (event : audit_comb_event (audit_loop_call V E)) :
  audit_loop_call V E :=
  match event with AuditCombCase site => AuditLoopCase (20 + site) | AuditCombBody body => body end.

Definition audit_loop_entries_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) : list (loop_entry V) * list (audit_loop_call V E) :=
  let '(search, dfs_events) := audit_dfs_full_counted p FinSet.empty (Graph.entries g) in
  let depth := N.of_nat (length (preorder search)) in
  let base := fun (_ : option V) (_ : list V) => (@nil (loop_entry V), @nil (audit_loop_call V E))
  in
  let step := fun descend => (audit_loop_layer_counted p (post_num search) descend, @nil
  (audit_loop_call V E)) in
  let '(run, iter_events) := audit_n_iter depth step base in
  let '(result, events) := run None (preorder search) in
  (result, map AuditLoopDfs dfs_events ++ [AuditLoopDepth (length (preorder search)) depth] ++
    map audit_loop_iter_event iter_events ++ events).

Fixpoint audit_loop_set_counted {V E} (EV : encoding V) (vertices : list V) (set : FinSet.t V)
    : FinSet.t V * list (audit_loop_call V E) :=
  match vertices with
  | [] => (set, [AuditLoopCase 25])
  | v :: rest => let next := FinSet.add EV v set in
      let '(result, events) := audit_loop_set_counted EV rest next in
      (result, AuditLoopCase 26 :: AuditLoopSet v set :: events)
  end.

Fixpoint audit_loop_nodes_counted {V E} (EV : encoding V) (entries : list (loop_entry V))
    : Map.t V (FinSet.t V) * list (audit_loop_call V E) :=
  match entries with
  | [] => (Map.empty, [AuditLoopCase 27])
  | entry :: rest => let '(middle, later) := audit_loop_nodes_counted EV rest in
      let '(members, events) := audit_loop_set_counted EV (loop_members entry) FinSet.empty in
      let result := Map.set EV (loop_head entry) members middle in
      (result, AuditLoopCase 28 :: later ++ events ++ [AuditLoopNodeWrite (loop_head entry) members
  middle])
  end.

Fixpoint audit_loop_parents_counted {V E} (EV : encoding V) (entries : list (loop_entry V))
    : Map.t V V * list (audit_loop_call V E) :=
  match entries with
  | [] => (Map.empty, [AuditLoopCase 29])
  | entry :: rest => let '(middle, later) := audit_loop_parents_counted EV rest in
      match loop_enclosing entry with
      | None => (middle, AuditLoopCase 30 :: later ++ [AuditLoopCase 31])
      | Some parent => (Map.set EV (loop_head entry) parent middle,
          AuditLoopCase 30 :: later ++ [AuditLoopCase 32; AuditLoopParentWrite (loop_head entry)
  parent middle])
      end
  end.

Fixpoint audit_loop_owners_counted {V E} (EV : encoding V) (entries : list (loop_entry V))
    : Map.t V V * list (audit_loop_call V E) :=
  match entries with
  | [] => (Map.empty, [AuditLoopCase 33])
  | entry :: rest => let '(members, here) := audit_loop_set_counted EV (loop_members entry)
  FinSet.empty in
      let mapped := Map.map (fun _ => loop_head entry) members in
      let '(deeper, later) := audit_loop_owners_counted EV rest in
      let result := Map.union_with (fun _ deeper_value => deeper_value) mapped deeper in
      (result, AuditLoopCase 34 :: here ++ [AuditLoopMap (loop_head entry) members mapped] ++
        later ++ [AuditLoopUnion mapped deeper result])
  end.

Definition audit_loop_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) : loop_forest V * list (audit_loop_call V E) :=
  let '(entries, entry_events) := audit_loop_entries_counted p in
  let headers := map loop_head entries in
  let '(nodes, node_events) := audit_loop_nodes_counted EV entries in
  let '(parents, parent_events) := audit_loop_parents_counted EV entries in
  let '(owners, owner_events) := audit_loop_owners_counted EV entries in
  (LoopForest headers nodes parents owners, entry_events ++ [AuditLoopOutput (length headers)] ++
    node_events ++ parent_events ++ owner_events).

Fixpoint audit_loop_trie_nodes_ne {A} (node : Trie.ne A) : nat :=
  match node with
  | Trie.N001 r => S (audit_loop_trie_nodes_ne r)
  | Trie.N010 _ => 1
  | Trie.N011 _ r => S (audit_loop_trie_nodes_ne r)
  | Trie.N100 l => S (audit_loop_trie_nodes_ne l)
  | Trie.N101 l r => S (audit_loop_trie_nodes_ne l + audit_loop_trie_nodes_ne r)
  | Trie.N110 l _ => S (audit_loop_trie_nodes_ne l)
  | Trie.N111 l _ r => S (audit_loop_trie_nodes_ne l + audit_loop_trie_nodes_ne r)
  end.

Definition audit_loop_trie_nodes {A} (m : Trie.t A) : nat :=
  match m with Trie.Empty => 0 | Trie.Nodes node => audit_loop_trie_nodes_ne node end.

Definition audit_loop_event_work {V E} (EV : encoding V) (event : audit_loop_call V E) : nat :=
  64 + match event with
  | AuditLoopDfs item => audit_dfs_full_model_event EV item
  | AuditLoopScc item => audit_tarjan_event_work EV item
  | AuditLoopRead v _ _ | AuditLoopEdges v _ _ =>
      audit_encoding_weight (audit_key_bits_weight (encode EV v)) + audit_get_weight (encode EV v)
  | AuditLoopSet v _ | AuditLoopNodeWrite v _ _ | AuditLoopParentWrite v _ _ =>
      audit_encoding_weight (audit_key_bits_weight (encode EV v)) + audit_set_weight (encode EV v)
  | AuditLoopEncode _ code => audit_encoding_weight (audit_key_bits_weight code)
  | AuditLoopCompare a b _ => audit_binary_weight (Z.pos a) (Z.pos b)
  | AuditLoopMap _ input _ => 64 * S (audit_loop_trie_nodes input) * S (audit_loop_trie_nodes input)
  | AuditLoopUnion lhs rhs _ => let nodes := audit_loop_trie_nodes lhs + audit_loop_trie_nodes rhs
  in
      64 * S nodes * S nodes
  | AuditLoopOutput size => S size
  | AuditLoopDepth size depth => audit_unary_conversion_weight size + size * S (N.to_nat depth)
  | _ => 0 end.

Definition audit_loop_model_work {V E} (EV : encoding V) (events : list (audit_loop_call V E)) : nat
  :=
  512 * S (length events) * S (length events) +
    fold_right (fun event total => audit_loop_event_work EV event + total) 0 events.

Definition audit_loop_input_event_bound {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) : nat := 64 * S (audit_wto_input_event_bound p) * S
  (audit_wto_input_event_bound p).

Definition audit_loop_input_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) : nat :=
  let n := audit_wto_input_order_bound p in
  let events := audit_loop_input_event_bound p in
  let width := Nat.max (audit_dfs_full_input_width EV g p (Graph.entries g))
    (audit_key_bits_weight (Pos.of_succ_nat (2 + n * S (Pos.to_nat (fuel p))))) in
  4096 * Nat.pow (S events) 4 * Nat.pow (S width) 2.

Definition audit_loop_counted_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g),
    let '(result, events) := audit_loop_counted p in
    result = loop_forest_of p /\
    length events <= audit_loop_input_event_bound p /\
    audit_loop_model_work EV events <= audit_loop_input_budget EV g p.


Definition audit_loop_singleton_graph : Graph.t positive positive :=
  Graph.Make [1%positive] [1%positive] (fun _ => [1%positive]) (fun e => e) (fun e => e).

(** Events retain actual operands, callbacks and primitive traces. *)
Inductive audit_loop_steps_event (V E B : Type) : Type :=
  | LoopStepsCase : nat -> audit_loop_steps_event V E B
  | LoopStepsRank : audit_map_event V positive B -> audit_loop_steps_event V E B
  | LoopStepsEdges : audit_map_event V (list E) B -> audit_loop_steps_event V E B
  | LoopStepsTarget : E -> V -> list B -> audit_loop_steps_event V E B
  | LoopStepsEncode : V -> positive -> list B -> audit_loop_steps_event V E B
  | LoopStepsEq : positive -> positive -> bool -> list audit_positive_eqb_event ->
  audit_loop_steps_event V E B
  | LoopStepsLe : positive -> positive -> bool -> list audit_positive_compare_event ->
  audit_loop_steps_event V E B.
Arguments LoopStepsCase {V E B} _.
Arguments LoopStepsRank {V E B} _.
Arguments LoopStepsEdges {V E B} _.
Arguments LoopStepsTarget {V E B} _ _ _.
Arguments LoopStepsEncode {V E B} _ _ _.
Arguments LoopStepsEq {V E B} _ _ _ _.
Arguments LoopStepsLe {V E B} _ _ _ _.

(** Header selection compares actual ranks after recursively inspecting the suffix. *)
Fixpoint audit_loop_steps_choose {V E B} (enc : V -> positive * list B)
    (numbers : Map.t V positive) (vertices : list V) : option V * list (audit_loop_steps_event V E
  B) :=
  match vertices with
  | [] => (None, [LoopStepsCase 0])
  | v :: rest =>
      let '(chosen, later) := audit_loop_steps_choose enc numbers rest in
      match chosen with
      | None => (Some v, LoopStepsCase 1 :: later)
      | Some w =>
          let '(ra, ea) := audit_map_get enc w numbers in
          let '(rb, eb) := audit_map_get enc v numbers in
          let a := match ra with Some x => x | None => 1%positive end in
          let b := match rb with Some x => x | None => 1%positive end in
          let '(le, ec) := audit_positive_leb a b in
          (Some (if le then v else w), LoopStepsCase 2 :: later ++ map LoopStepsRank ea ++
            map LoopStepsRank eb ++ [LoopStepsLe a b le ec])
      end
  end.

(** Equality compares both actual encoder calls and the positive primitive trace. *)
Definition audit_loop_steps_equal {V E B} (enc : V -> positive * list B) (v h : V)
    : bool * list (audit_loop_steps_event V E B) :=
  let '(a, ea) := enc v in let '(b, eb) := enc h in
  let '(eq, events) := audit_positive_eqb a b in
  (eq, [LoopStepsEncode v a ea; LoopStepsEncode h b eb; LoopStepsEq a b eq events]).

(** Removing a header tests every component occurrence. *)
Fixpoint audit_loop_steps_without {V E B} (enc : V -> positive * list B) (h : V) (vertices : list V)
    : list V * list (audit_loop_steps_event V E B) :=
  match vertices with
  | [] => ([], [LoopStepsCase 3])
  | v :: rest =>
      let '(eq, here) := audit_loop_steps_equal enc v h in
      let '(later, events) := audit_loop_steps_without enc h rest in
      (if eq then later else v :: later, LoopStepsCase 4 :: here ++ events)
  end.

(** The strict edge scan retains calls after the first self edge. *)
Fixpoint audit_loop_steps_self {V E B} (enc : V -> positive * list B) (target : E -> V * list B)
    (v : V) (edges : list E) : bool * list (audit_loop_steps_event V E B) :=
  match edges with
  | [] => (false, [LoopStepsCase 5])
  | edge :: rest =>
      let '(dst, body) := target edge in
      let '(eq, here) := audit_loop_steps_equal enc dst v in
      let '(later, events) := audit_loop_steps_self enc target v rest in
      (eq || later, LoopStepsCase 6 :: LoopStepsTarget edge dst body :: here ++ events)
  end.

(** Empty, singleton and larger components follow their source branches. *)
Definition audit_loop_steps_cyclic {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (enc : V -> positive * list B) (target : E -> V * list B)
    (vertices : list V) : bool * list (audit_loop_steps_event V E B) :=
  match vertices with
  | [] => (false, [LoopStepsCase 7])
  | [v] =>
      let '(found, reads) := audit_map_get enc v (out_index p) in
      let edges := match found with Some xs => xs | None => [] end in
      let '(result, events) := audit_loop_steps_self enc target v edges in
      (result, LoopStepsCase 8 :: map LoopStepsEdges reads ++ events)
  | _ :: _ :: _ => (true, [LoopStepsCase 9])
  end.

(** These primitive source models erase to the actual loop operations. *)
Definition audit_loop_steps_erasure_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (enc : V -> positive * list B) (target : E -> V * list B),
    (forall v, fst (enc v) = encode EV v) ->
    (forall e, fst (target e) = Graph.target g e) ->
    (forall numbers vertices, fst (audit_loop_steps_choose (E := E) enc numbers vertices) =
      loop_choose EV numbers vertices) /\
    (forall h vertices, fst (audit_loop_steps_without (E := E) enc h vertices) = loop_without EV h
  vertices) /\
    (forall vertices, fst (audit_loop_steps_cyclic p enc target vertices) = loop_cyclic p vertices).

(** Work charges actual primitive operations and their attached callback bodies. *)
Definition audit_loop_steps_event_work {V E B} (weight : B -> nat) (event : audit_loop_steps_event V
  E B) : nat :=
  let body := fun xs => fold_right (fun x n => weight x + n) 0 xs in
  64 + match event with
  | LoopStepsCase _ => 0
  | LoopStepsRank call => audit_map_source_work body [call]
  | LoopStepsEdges call => audit_map_source_work body [call]
  | LoopStepsTarget _ _ xs | LoopStepsEncode _ _ xs => body xs
  | LoopStepsEq _ _ _ calls => audit_positive_eqb_source_work calls
  | LoopStepsLe _ _ _ calls => audit_positive_order_source_work calls
  end.

(** External charges are the bodies of the actual supplied callbacks. *)
Definition audit_loop_steps_event_external {V E B} (weight : B -> nat)
    (event : audit_loop_steps_event V E B) : nat :=
  match event with
  | LoopStepsTarget _ _ body | LoopStepsEncode _ _ body |
    LoopStepsRank (AuditMapGet _ _ _ _ body _) | LoopStepsRank (AuditMapSet _ _ _ _ _ body _) |
    LoopStepsRank (AuditMapRemove _ _ _ _ body _) | LoopStepsEdges (AuditMapGet _ _ _ _ body _) |
    LoopStepsEdges (AuditMapSet _ _ _ _ _ body _) | LoopStepsEdges (AuditMapRemove _ _ _ _ body _)
  =>
      fold_right (fun x n => weight x + n) 0 body
  | _ => 0
  end.

(** Sum work for this invocation's source events. *)
Definition audit_loop_steps_work {V E B} (weight : B -> nat) (events : list (audit_loop_steps_event
  V E B)) : nat :=
  fold_right (fun event n => audit_loop_steps_event_work weight event + n) 0 events.

(** Sum the actual external bodies of those same events. *)
Definition audit_loop_steps_external {V E B} (weight : B -> nat)
    (events : list (audit_loop_steps_event V E B)) : nat :=
  fold_right (fun event n => audit_loop_steps_event_external weight event + n) 0 events.

(** The shared bound measures all actual input lists, keys, ranks and successor targets. *)
Definition audit_loop_steps_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (numbers : Map.t V positive) (vertices : list V) (h : V) : nat :=
  let rank_rows := Map.elements numbers in
  let edge_rows := Map.elements (out_index p) in
  let edges := flat_map snd edge_rows in
  let keys := h :: vertices ++ map fst rank_rows ++ map fst edge_rows ++ map (Graph.target g) edges
  in
  let width := Nat.max (fold_right Nat.max 0 (map (fun v => Pos.size_nat (encode EV v)) keys))
    (fold_right Nat.max 0 (map (fun row => Pos.size_nat (snd row)) rank_rows)) in
  4096 * Nat.pow (S (length keys + length edges + length rank_rows + width)) 6.

(** Each helper's work is bounded by inputs and its actual external callback bodies. *)
Definition audit_loop_steps_bound_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) numbers vertices h
    (enc : V -> positive * list B) (target : E -> V * list B) (weight : B -> nat),
    (forall v, fst (enc v) = encode EV v) ->
    (forall e, fst (target e) = Graph.target g e) ->
    let budget := audit_loop_steps_budget EV g p numbers vertices h in
    let choose_events := snd (audit_loop_steps_choose (E := E) enc numbers vertices) in
    let without_events := snd (audit_loop_steps_without (E := E) enc h vertices) in
    let cyclic_events := snd (audit_loop_steps_cyclic p enc target vertices) in
    audit_loop_steps_work weight choose_events <= budget + audit_loop_steps_external weight
  choose_events /\
    audit_loop_steps_work weight without_events <= budget + audit_loop_steps_external weight
  without_events /\
    audit_loop_steps_work weight cyclic_events <= budget + audit_loop_steps_external weight
  cyclic_events.

(** Events preserve actual operands, results and the supplied encoding bodies. *)
Inductive audit_loop_pack_event (V B : Type) : Type :=
  | LoopPackCase : nat -> audit_loop_pack_event V B
  | LoopPackSet : audit_set_event V B -> audit_loop_pack_event V B
  | LoopPackNodes : audit_map_event V (FinSet.t V) B -> audit_loop_pack_event V B
  | LoopPackParent : audit_map_event V V B -> audit_loop_pack_event V B
  | LoopPackTransform : audit_map_transform_event V unit V unit -> audit_loop_pack_event V B
  | LoopPackUnion : audit_map_union_event V V unit -> audit_loop_pack_event V B.
Arguments LoopPackCase {V B} _.
Arguments LoopPackSet {V B} _.
Arguments LoopPackNodes {V B} _.
Arguments LoopPackParent {V B} _.
Arguments LoopPackTransform {V B} _.
Arguments LoopPackUnion {V B} _.

(** Node sets are built for each entry before inserting its header binding. *)
Fixpoint audit_loop_pack_nodes {V B} (enc : V -> positive * list B) (entries : list (loop_entry V))
    : Map.t V (FinSet.t V) * list (audit_loop_pack_event V B) :=
  match entries with
  | [] => (Map.empty, [LoopPackCase 0])
  | entry :: rest =>
      let '(index, later) := audit_loop_pack_nodes enc rest in
      let '(members, set_events) := audit_finset_of_list enc (loop_members entry) in
      let '(result, writes) := audit_map_set enc (loop_head entry) members index in
      (result, LoopPackCase 1 :: later ++ map LoopPackSet set_events ++ map LoopPackNodes writes)
  end.

(** Missing enclosing headers create no parent binding. *)
Fixpoint audit_loop_pack_parents {V B} (enc : V -> positive * list B) (entries : list (loop_entry
  V))
    : Map.t V V * list (audit_loop_pack_event V B) :=
  match entries with
  | [] => (Map.empty, [LoopPackCase 2])
  | entry :: rest =>
      let '(index, later) := audit_loop_pack_parents enc rest in
      match loop_enclosing entry with
      | None => (index, LoopPackCase 3 :: later)
      | Some parent =>
          let '(result, writes) := audit_map_set enc (loop_head entry) parent index in
          (result, LoopPackCase 4 :: later ++ map LoopPackParent writes)
      end
  end.

(** The actual transformation and union callbacks are fixed internal functions. *)
Fixpoint audit_loop_pack_owners {V B} (enc : V -> positive * list B) (entries : list (loop_entry V))
    : Map.t V V * list (audit_loop_pack_event V B) :=
  match entries with
  | [] => (Map.empty, [LoopPackCase 5])
  | entry :: rest =>
      let '(members, set_events) := audit_finset_of_list enc (loop_members entry) in
      let '(mapped, map_events) := audit_map_transform (fun _ : unit => (loop_head entry, []))
  members in
      let '(deeper, later) := audit_loop_pack_owners enc rest in
      let '(result, union_events) := audit_map_union (fun (_ x : V) => (x, [])) mapped deeper in
      (result, LoopPackCase 6 :: map LoopPackSet set_events ++ map LoopPackTransform map_events ++
        later ++ map LoopPackUnion union_events)
  end.

(** Pack the actual observations in source order. *)
Definition audit_loop_pack_source_counted {V B} (enc : V -> positive * list B)
    (entries : list (loop_entry V)) : loop_forest V * list (audit_loop_pack_event V B) :=
  let headers := map loop_head entries in
  let '(nodes, node_events) := audit_loop_pack_nodes enc entries in
  let '(parents, parent_events) := audit_loop_pack_parents enc entries in
  let '(owners, owner_events) := audit_loop_pack_owners enc entries in
  (LoopForest headers nodes parents owners,
    LoopPackCase 7 :: node_events ++ parent_events ++ owner_events).

(** Work charges each collection primitive and the actual supplied encoder bodies. *)
Definition audit_loop_pack_event_work {V B} (weight : B -> nat) (event : audit_loop_pack_event V B)
  : nat :=
  let body := fun xs => fold_right (fun x n => weight x + n) 0 xs in
  64 + match event with
  | LoopPackCase _ => 0
  | LoopPackSet call => audit_finset_source_work body [call]
  | LoopPackNodes call => audit_map_source_work body [call]
  | LoopPackParent call => audit_map_source_work body [call]
  | LoopPackTransform call => audit_map_transform_source_work (fun _ => 0) [call]
  | LoopPackUnion call => audit_map_union_source_work (fun _ => 0) [call]
  end.

(** Only actual encoder calls have external bodies in packing. *)
Definition audit_loop_pack_event_external {V B} (weight : B -> nat)
    (event : audit_loop_pack_event V B) : nat :=
  match event with
  | LoopPackSet (AuditSetAdd _ _ _ _ body _) | LoopPackSet (AuditSetMem _ _ _ _ body _) |
    LoopPackSet (AuditSetRemove _ _ _ _ body _) | LoopPackNodes (AuditMapGet _ _ _ _ body _) |
    LoopPackNodes (AuditMapSet _ _ _ _ _ body _) | LoopPackNodes (AuditMapRemove _ _ _ _ body _) |
    LoopPackParent (AuditMapGet _ _ _ _ body _) | LoopPackParent (AuditMapSet _ _ _ _ _ body _) |
    LoopPackParent (AuditMapRemove _ _ _ _ body _) => fold_right (fun x n => weight x + n) 0 body
  | _ => 0
  end.

(** Packing work sums this execution's events. *)
Definition audit_loop_pack_source_work {V B} (weight : B -> nat) (events : list
  (audit_loop_pack_event V B)) : nat :=
  fold_right (fun event n => audit_loop_pack_event_work weight event + n) 0 events.

(** External cost sums the bodies recorded by this execution. *)
Definition audit_loop_pack_source_external {V B} (weight : B -> nat)
    (events : list (audit_loop_pack_event V B)) : nat :=
  fold_right (fun event n => audit_loop_pack_event_external weight event + n) 0 events.

(** Input size measures headers, all members and their actual encoding widths. *)
Definition audit_loop_pack_input_scale {V} (EV : encoding V) (entries : list (loop_entry V)) : nat
  :=
  let vertices := map loop_head entries ++ flat_map loop_members entries ++
    flat_map (fun entry => match loop_enclosing entry with Some v => [v] | None => [] end) entries
  in
  S (length entries + length vertices + fold_right Nat.max 0
    (map (fun v => Pos.size_nat (encode EV v)) vertices)).

(** This bound depends only on the entries and supplied encoding. *)
Definition audit_loop_pack_source_budget {V} (EV : encoding V) (entries : list (loop_entry V)) : nat
  :=
  4096 * Nat.pow (audit_loop_pack_input_scale EV entries) 8.

(** The packed forest and source-work bound hold for arbitrary input entries. *)
Definition audit_loop_pack_source_statement : Prop :=
  forall V B (EV : encoding V) (enc : V -> positive * list B) (weight : B -> nat) entries,
    (forall v, fst (enc v) = encode EV v) ->
    let '(result, events) := audit_loop_pack_source_counted enc entries in
    result = loop_pack EV entries /\ audit_loop_pack_source_work weight events <=
      audit_loop_pack_source_budget EV entries + audit_loop_pack_source_external weight events.

(** Each event embeds a concrete source operation or a fixed local branch. *)
Inductive audit_loop_full_event (V E B : Type) : Type :=
  | LoopFullCase : nat -> audit_loop_full_event V E B
  | LoopFullOutput : nat -> audit_loop_full_event V E B
  | LoopFullDepth : nat -> N -> audit_loop_full_event V E B
  | LoopFullDfs : audit_dfs_nested_event V E (audit_graph_callback_capture V E B) ->
      audit_loop_full_event V E B
  | LoopFullScc : audit_tarjan_nested_event V E (audit_graph_callback_capture V E B) ->
      audit_loop_full_event V E B
  | LoopFullStep : audit_loop_steps_event V E B -> audit_loop_full_event V E B
  | LoopFullPack : audit_loop_pack_event V B -> audit_loop_full_event V E B.
Arguments LoopFullCase {V E B} _.
Arguments LoopFullOutput {V E B} _.
Arguments LoopFullDepth {V E B} _ _.
Arguments LoopFullDfs {V E B} _.
Arguments LoopFullScc {V E B} _.
Arguments LoopFullStep {V E B} _.
Arguments LoopFullPack {V E B} _.

(** A block records the actual cyclic test, choice, removal and descendant invocation. *)
Definition audit_loop_full_block {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (numbers : Map.t V positive)
    (descend : option V -> list V -> list (loop_entry V) * list (audit_loop_full_event V E B))
    (parent : option V) (region component : list V) : list (loop_entry V) * list
  (audit_loop_full_event V E B) :=
  let enc := audit_dfs_encode_model cb in
  let '(cyclic, cycle_events) := audit_loop_steps_cyclic p enc (audit_dfs_target_model cb) component
  in
  if cyclic then
    let '(chosen, choice_events) := audit_loop_steps_choose (E := E) enc numbers component in
    match chosen with
    | None => ([], map LoopFullStep cycle_events ++ [LoopFullCase 0] ++ map LoopFullStep
  choice_events)
    | Some h =>
        let '(smaller, remove_events) := audit_loop_steps_without (E := E) enc h component in
        let '(children, child_events) := descend (Some h) smaller in
        (LoopEntry h component parent region :: children,
          map LoopFullStep cycle_events ++ [LoopFullCase 1] ++ map LoopFullStep choice_events ++
          map LoopFullStep remove_events ++ child_events ++ [LoopFullOutput 1])
    end
  else ([], map LoopFullStep cycle_events ++ [LoopFullCase 2]).

(** The component fold preserves occurrence order and concatenation costs. *)
Fixpoint audit_loop_full_blocks {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (numbers : Map.t V positive)
    (descend : option V -> list V -> list (loop_entry V) * list (audit_loop_full_event V E B))
    (parent : option V) (region : list V) (components : list (list V))
    : list (loop_entry V) * list (audit_loop_full_event V E B) :=
  match components with
  | [] => ([], [LoopFullCase 3])
  | component :: rest =>
      let '(first, here) := audit_loop_full_block p cb numbers descend parent region component in
      let '(later, events) := audit_loop_full_blocks p cb numbers descend parent region rest in
      (first ++ later, LoopFullCase 4 :: here ++ events ++ [LoopFullOutput (length first)])
  end.

(** Each layer invokes the SCC source model on its actual region. *)
Definition audit_loop_full_layer {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (numbers : Map.t V positive)
    (descend : option V -> list V -> list (loop_entry V) * list (audit_loop_full_event V E B))
    (parent : option V) (region : list V) : list (loop_entry V) * list (audit_loop_full_event V E B)
  :=
  let '(sccs, calls) := audit_scc_source_counted p cb region in
  let '(result, events) := audit_loop_full_blocks p cb numbers descend parent region (components
  sccs) in
  (result, map LoopFullScc calls ++ events).

(** Binary iteration creates the same layer closures and uses the actual DFS output. *)
Definition audit_loop_full_entries {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B)
    : list (loop_entry V) * list (audit_loop_full_event V E B) :=
  let '(search, calls) := audit_dfs_source_counted p cb FinSet.empty (Graph.entries g) in
  let depth := N.of_nat (length (preorder search)) in
  let base := fun (_ : option V) (_ : list V) => (@nil (loop_entry V), @nil (audit_loop_full_event V
  E B)) in
  let step := fun recur => (audit_loop_full_layer p cb (post_num search) recur, @nil
  (audit_loop_full_event V E B)) in
  let '(run, iter_events) := audit_n_iter depth step base in
  let '(result, events) := run None (preorder search) in
  (result, map LoopFullDfs calls ++ [LoopFullDepth (length (preorder search)) depth] ++
    map (fun event => match event with
      | AuditCombCase site => LoopFullCase (10 + site)
      | AuditCombBody body => body
      end) iter_events ++ events).

(** The complete producer passes its actual entry list directly to packing. *)
Definition audit_loop_full_source_counted {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B)
    : loop_forest V * list (audit_loop_full_event V E B) :=
  let '(entries, calls) := audit_loop_full_entries p cb in
  let '(result, packing) := audit_loop_pack_source_counted (audit_dfs_encode_model cb) entries in
  (result, calls ++ [LoopFullOutput (length entries)] ++ map LoopFullPack packing).

(** The complete counted producer returns the exact source forest. *)
Definition audit_loop_full_source_erasure_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (cb : audit_dfs_callback_model V E B),
    audit_dfs_callbacks_erase EV g cb -> fst (audit_loop_full_source_counted p cb) = loop_forest_of
  p.

(** Work includes each nested body and source list concatenation. *)
Definition audit_loop_full_event_work {V E B} (weight : B -> nat) (event : audit_loop_full_event V E
  B) : nat :=
  64 + match event with
  | LoopFullCase _ => 0
  | LoopFullOutput n => S n
  | LoopFullDepth n _ => 16 * S n * S n
  | LoopFullDfs call => audit_dfs_source_event_work weight call
  | LoopFullScc call => audit_scc_source_event_work weight call
  | LoopFullStep call => audit_loop_steps_event_work weight call
  | LoopFullPack call => audit_loop_pack_event_work weight call
  end.

(** External charges use only captured bodies from this invocation. *)
Definition audit_loop_full_event_external {V E B} (weight : B -> nat)
    (event : audit_loop_full_event V E B) : nat :=
  match event with
  | LoopFullDfs call => audit_dfs_source_body_work weight [call]
  | LoopFullScc call => audit_scc_source_body_work weight [call]
  | LoopFullStep call => audit_loop_steps_event_external weight call
  | LoopFullPack call => audit_loop_pack_event_external weight call
  | _ => 0
  end.

(** The quadratic list allowance covers source trace composition and emitted prefixes. *)
Definition audit_loop_full_source_work {V E B} (weight : B -> nat)
    (events : list (audit_loop_full_event V E B)) : nat :=
  256 * S (length events) * S (length events) +
  fold_right (fun event n => audit_loop_full_event_work weight event + n) 0 events.

(** The same event list supplies the client body cost. *)
Definition audit_loop_full_source_external {V E B} (weight : B -> nat)
    (events : list (audit_loop_full_event V E B)) : nat :=
  fold_right (fun event n => audit_loop_full_event_external weight event + n) 0 events.

(** The original graph and prepared index determine the source-work bound. *)
Definition audit_loop_full_source_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) : nat :=
  let width := audit_dfs_full_input_width EV g p (Graph.entries g) in
  let count := audit_wto_input_event_bound p in
  let scale := S (count + width + Pos.to_nat (fuel p) + length (Graph.entries g) +
    audit_wto_input_max_out p) in
  1048576 * Nat.pow scale 8.

(** The whole producer returns the source forest with input-bounded source work. *)
Definition audit_loop_full_source_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (cb : audit_dfs_callback_model V E B) (weight : B -> nat),
    audit_dfs_callbacks_erase EV g cb ->
    let '(result, events) := audit_loop_full_source_counted p cb in
    result = loop_forest_of p /\ audit_loop_full_source_work weight events <=
      audit_loop_full_source_budget EV g p + audit_loop_full_source_external weight events.

(** Captured DFS and SCC calls retain their genuine client inputs. *)
Definition audit_loop_full_capture_budget {V E B} (encode_budget : V -> nat) (target_budget : E ->
  nat)
    (calls : list (audit_graph_callback_capture V E B)) : nat :=
  fold_right (fun call n => audit_scc_capture_budget encode_budget target_budget call + n) 0 calls.

(** Component and packing events expose only genuine external callback inputs. *)
Definition audit_loop_full_event_budget {V E B} (encode_budget : V -> nat) (target_budget : E ->
  nat)
    (event : audit_loop_full_event V E B) : nat :=
  match event with
  | LoopFullDfs (_, calls) | LoopFullScc (_, calls) =>
      audit_loop_full_capture_budget encode_budget target_budget calls
  | LoopFullStep (LoopStepsTarget e _ _) => target_budget e
  | LoopFullStep (LoopStepsEncode v _ _) => encode_budget v
  | LoopFullStep (LoopStepsRank (AuditMapGet v _ _ _ _ _)) |
    LoopFullStep (LoopStepsRank (AuditMapSet v _ _ _ _ _ _)) |
    LoopFullStep (LoopStepsRank (AuditMapRemove v _ _ _ _ _)) |
    LoopFullStep (LoopStepsEdges (AuditMapGet v _ _ _ _ _)) |
    LoopFullStep (LoopStepsEdges (AuditMapSet v _ _ _ _ _ _)) |
    LoopFullStep (LoopStepsEdges (AuditMapRemove v _ _ _ _ _)) |
    LoopFullPack (LoopPackSet (AuditSetAdd v _ _ _ _ _)) |
    LoopFullPack (LoopPackSet (AuditSetMem v _ _ _ _ _)) |
    LoopFullPack (LoopPackSet (AuditSetRemove v _ _ _ _ _)) |
    LoopFullPack (LoopPackNodes (AuditMapGet v _ _ _ _ _)) |
    LoopFullPack (LoopPackNodes (AuditMapSet v _ _ _ _ _ _)) |
    LoopFullPack (LoopPackNodes (AuditMapRemove v _ _ _ _ _)) |
    LoopFullPack (LoopPackParent (AuditMapGet v _ _ _ _ _)) |
    LoopFullPack (LoopPackParent (AuditMapSet v _ _ _ _ _ _)) |
    LoopFullPack (LoopPackParent (AuditMapRemove v _ _ _ _ _)) => encode_budget v
  | _ => 0
  end.

(** The full traversal has an input-derived bound and budgets for its actual client calls. *)
Definition audit_loop_full_source_adapted_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (cb : audit_dfs_callback_model V E B) (weight : B -> nat)
    encode_source target_source encode_budget target_budget,
    audit_dfs_callbacks_erase EV g cb ->
    audit_graph_external_callback_adapter (audit_dfs_encode_model cb) weight encode_source
  encode_budget ->
    audit_graph_external_callback_adapter (audit_dfs_target_model cb) weight target_source
  target_budget ->
    let '(result, events) := audit_loop_full_source_counted p cb in
    result = loop_forest_of p /\ audit_loop_full_source_work weight events <=
      audit_loop_full_source_budget EV g p +
      fold_right (fun event n => audit_loop_full_event_budget encode_budget target_budget event + n)
  0 events.

(** The full source contract joins erasure, recorded-body, adapted and SCC source obligations. *)
Definition audit_loop_full_source_contract_statement : Prop :=
  audit_loop_full_source_erasure_statement /\ audit_loop_full_source_statement /\
  audit_loop_full_source_adapted_statement /\ audit_scc_source_contract_statement /\
  audit_loop_steps_erasure_statement /\ audit_loop_steps_bound_statement /\
  audit_loop_pack_source_statement.
```

## Galois.Graph.GraphAuditSemiDominators

Card: AUD-GR-MODELS

Source destination: `theories/Graph/GraphAuditSemiDominators.v`.

```rocq
From Galois.Collections Require Import CollectionsAuditCost.
From Galois.Graph Require Import GraphAuditBase GraphAuditDfs GraphAuditVirtual.

From Stdlib Require Import List Bool PArith Arith ZArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsTrie
  CollectionsFinSet CollectionsAuditCost.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphSemiDominators GraphDominance.
Import List.ListNotations.

Inductive audit_semi_call (V : Type) : Type :=
| AuditSemiCase (site : nat)
| AuditSemiGet (v : V) (m : Map.t V V) (result : option V)
| AuditSemiRankGet (v : V) (m : Map.t V positive) (result : option positive)
| AuditSemiLess (a b : positive) (result : bool)
| AuditSemiLe (a b : positive) (result : bool)
| AuditSemiSet (v value : V) (m : Map.t V V).
Arguments AuditSemiCase {V} _.
Arguments AuditSemiGet {V} _ _ _.
Arguments AuditSemiRankGet {V} _ _ _.
Arguments AuditSemiLess {V} _ _ _.
Arguments AuditSemiLe {V} _ _ _.
Arguments AuditSemiSet {V} _ _ _.

Definition audit_semi_rank_counted {V E} (EV : encoding V) (r : dfs_result V E) (v : V)
    : positive * list (audit_semi_call V) :=
  let found := Map.get EV v (pre_num r) in
  (match found with Some p => p | None => 1%positive end, [AuditSemiRankGet v (pre_num r) found]).

Definition audit_semi_score_counted {V E} (EV : encoding V) (r : dfs_result V E)
    (semis : Map.t V V) (v : V) : positive * list (audit_semi_call V) :=
  let found := Map.get EV v semis in
  let value := match found with Some u => u | None => v end in
  let '(score, events) := audit_semi_rank_counted EV r value in
  (score, AuditSemiGet v semis found :: events).

Definition audit_semi_label_counted {V} (EV : encoding V) (st : SemiLinks.t V) (v : V)
    : V * list (audit_semi_call V) :=
  let found := Map.get EV v (SemiLinks.labels st) in
  (match found with Some u => u | None => v end, [AuditSemiGet v (SemiLinks.labels st) found]).

Inductive audit_semi_compress_run {V E} (EV : encoding V) (r : dfs_result V E)
    (semis : Map.t V V) (st : SemiLinks.t V) : V -> semi_query_result V -> list (audit_semi_call V)
  -> Prop :=
| AuditSemiCompressRoot v :
    Map.get EV v (SemiLinks.shortcut st) = None ->
    audit_semi_compress_run EV r semis st v (st, (v, None))
      [AuditSemiGet v (SemiLinks.shortcut st) None; AuditSemiCase 0]
| AuditSemiCompressStopped v a ra rv ea ev :
    Map.get EV v (SemiLinks.shortcut st) = Some a ->
    audit_semi_rank_counted EV r a = (ra, ea) -> audit_semi_rank_counted EV r v = (rv, ev) ->
    Pos.ltb ra rv = false ->
    audit_semi_compress_run EV r semis st v (st, (v, None))
      ([AuditSemiGet v (SemiLinks.shortcut st) (Some a)] ++ ea ++ ev ++
        [AuditSemiLess ra rv false; AuditSemiCase 1])
| AuditSemiCompressRecurNone v a ra rv ea ev st' root inner label label_events :
    Map.get EV v (SemiLinks.shortcut st) = Some a ->
    audit_semi_rank_counted EV r a = (ra, ea) -> audit_semi_rank_counted EV r v = (rv, ev) ->
    Pos.ltb ra rv = true -> audit_semi_compress_run EV r semis st a (st', (root, None)) inner ->
    audit_semi_label_counted EV st v = (label, label_events) ->
    audit_semi_compress_run EV r semis st v
      (semi_shortcut_set EV st' v root label, (root, Some label))
      ([AuditSemiGet v (SemiLinks.shortcut st) (Some a)] ++ ea ++ ev ++
        [AuditSemiLess ra rv true; AuditSemiCase 2] ++ inner ++ [AuditSemiCase 3] ++ label_events ++
        [AuditSemiSet v root (SemiLinks.shortcut st'); AuditSemiSet v label (SemiLinks.labels st')])
| AuditSemiCompressRecurSome v a ra rv ea ev st' root u inner label label_events sl su el eu choose
  :
    Map.get EV v (SemiLinks.shortcut st) = Some a ->
    audit_semi_rank_counted EV r a = (ra, ea) -> audit_semi_rank_counted EV r v = (rv, ev) ->
    Pos.ltb ra rv = true -> audit_semi_compress_run EV r semis st a (st', (root, Some u)) inner ->
    audit_semi_label_counted EV st v = (label, label_events) ->
    audit_semi_score_counted EV r semis label = (sl, el) ->
    audit_semi_score_counted EV r semis u = (su, eu) -> choose = Pos.leb sl su ->
    let best := if choose then label else u in
    audit_semi_compress_run EV r semis st v
      (semi_shortcut_set EV st' v root best, (root, Some best))
      ([AuditSemiGet v (SemiLinks.shortcut st) (Some a)] ++ ea ++ ev ++
        [AuditSemiLess ra rv true; AuditSemiCase 2] ++ inner ++ [AuditSemiCase 4] ++ label_events ++
        el ++ eu ++ [AuditSemiLe sl su choose; AuditSemiSet v root (SemiLinks.shortcut st');
          AuditSemiSet v best (SemiLinks.labels st')]).

Definition audit_semi_call_work {V} (EV : encoding V) (event : audit_semi_call V) : nat :=
  64 + match event with
  | AuditSemiGet v _ _ | AuditSemiRankGet v _ _ =>
      audit_encoding_weight (audit_key_bits_weight (encode EV v)) + audit_get_weight (encode EV v)
  | AuditSemiSet v _ _ => audit_encoding_weight (audit_key_bits_weight (encode EV v)) +
  audit_set_weight (encode EV v)
  | AuditSemiLess a b _ | AuditSemiLe a b _ => audit_binary_weight (Z.pos a) (Z.pos b)
  | AuditSemiCase _ => 0 end.

Definition audit_semi_compress_work {V} (EV : encoding V) (events : list (audit_semi_call V)) : nat
  :=
  64 * S (length events) * S (length events) +
    fold_right (fun event total => audit_semi_call_work EV event + total) 0 events.

Definition audit_semi_compress_width {V E} (EV : encoding V) (r : dfs_result V E)
    (semis : Map.t V V) (st : SemiLinks.t V) (v : V) : nat :=
  let pairs := Map.elements (SemiLinks.shortcut st) ++ Map.elements (SemiLinks.labels st) ++
  Map.elements semis in
  let vertices := v :: map fst pairs ++ map snd pairs ++ map fst (Map.elements (pre_num r)) in
  Nat.max (fold_right Nat.max 0 (map (fun x => audit_key_bits_weight (encode EV x)) vertices))
    (fold_right Nat.max 0 (map (fun pair => audit_key_bits_weight (snd pair)) (Map.elements (pre_num
  r)))).

Definition audit_semi_compress_event_bound {V E} (EV : encoding V) (r : dfs_result V E) (v : V) :
  nat :=
  20 * S (Pos.to_nat (semi_rank EV r v)).

Definition audit_semi_compress_budget {V E} (EV : encoding V) (r : dfs_result V E)
    (semis : Map.t V V) (st : SemiLinks.t V) (v : V) : nat :=
  let count := audit_semi_compress_event_bound EV r v in
  let width := audit_semi_compress_width EV r semis st v in
  128 * S count * S count + count * (80 + 6 * width).

Definition audit_semi_compress_statement : Prop :=
  forall V E (EV : encoding V) (r : dfs_result V E) semis st v,
    exists result events, audit_semi_compress_run EV r semis st v result events /\
      result = semi_compress EV (semi_rank EV r) (fun x => semi_rank EV r (semi_value EV semis x))
  st v /\
      length events <= audit_semi_compress_event_bound EV r v /\
      audit_semi_compress_work EV events <= audit_semi_compress_budget EV r semis st v.

Definition audit_semi_compress_unique_statement : Prop :=
  forall V E (EV : encoding V) (r : dfs_result V E) semis st v result1 events1 result2 events2,
    audit_semi_compress_run EV r semis st v result1 events1 ->
    audit_semi_compress_run EV r semis st v result2 events2 -> result1 = result2 /\ events1 =
  events2.


Inductive audit_semi_outer_call (V E : Type) : Type :=
| AuditSemiOuterCase (site : nat)
| AuditSemiOuterSource (edge : E) (source : V)
| AuditSemiOuterInner (event : audit_semi_call V)
| AuditSemiOuterTreeGet (v : V) (m : Map.t V E) (result : option E)
| AuditSemiOuterPredGet (v : V) (m : Map.t V (list E)) (result : option (list E))
| AuditSemiOuterResultSet (v value : V) (m : Map.t V V)
| AuditSemiOuterLink (v parent : V) (st : SemiLinks.t V)
| AuditSemiOuterOutput (size : nat).
Arguments AuditSemiOuterCase {V E} _.
Arguments AuditSemiOuterSource {V E} _ _.
Arguments AuditSemiOuterInner {V E} _.
Arguments AuditSemiOuterTreeGet {V E} _ _ _.
Arguments AuditSemiOuterPredGet {V E} _ _ _.
Arguments AuditSemiOuterResultSet {V E} _ _ _.
Arguments AuditSemiOuterLink {V E} _ _ _.
Arguments AuditSemiOuterOutput {V E} _.

Definition audit_semi_value_counted {V} (EV : encoding V) (semis : Map.t V V) (v : V)
    : V * list (audit_semi_call V) :=
  let found := Map.get EV v semis in
  (match found with Some u => u | None => v end, [AuditSemiGet v semis found]).

Inductive audit_semi_predecessor_run {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) (semis : Map.t V V) :
    SemiLinks.t V * V -> E -> SemiLinks.t V * V -> list (audit_semi_outer_call V E) -> Prop :=
| AuditSemiPredUnnumbered st best edge v :
    v = Graph.source g edge -> Map.get EV v (pre_num r) = None ->
    audit_semi_predecessor_run EV g r semis (st, best) edge (st, best)
      [AuditSemiOuterSource edge v; AuditSemiOuterInner (AuditSemiRankGet v (pre_num r) None);
  AuditSemiOuterCase 0]
| AuditSemiPredNumbered st best edge v number st' root part inner u value value_events
    best_rank selected_rank eb es choose :
    v = Graph.source g edge -> Map.get EV v (pre_num r) = Some number ->
    audit_semi_compress_run EV r semis st v (st', (root, part)) inner ->
    u = match part with Some chosen => chosen | None => v end ->
    audit_semi_value_counted EV semis u = (value, value_events) ->
    audit_semi_rank_counted EV r best = (best_rank, eb) ->
    audit_semi_rank_counted EV r value = (selected_rank, es) -> choose = Pos.leb best_rank
  selected_rank ->
    audit_semi_predecessor_run EV g r semis (st, best) edge
      (st', if choose then best else value)
      ([AuditSemiOuterSource edge v; AuditSemiOuterInner (AuditSemiRankGet v (pre_num r) (Some
  number)); AuditSemiOuterCase 1] ++
       map AuditSemiOuterInner inner ++ [AuditSemiOuterCase 2] ++ map AuditSemiOuterInner
  value_events ++
       map AuditSemiOuterInner eb ++ map AuditSemiOuterInner es ++ [AuditSemiOuterInner (AuditSemiLe
  best_rank selected_rank choose)]).

Inductive audit_semi_predecessors_run {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) (semis : Map.t V V) : list E -> SemiLinks.t V * V ->
    SemiLinks.t V * V -> list (audit_semi_outer_call V E) -> Prop :=
| AuditSemiPredsNil acc : audit_semi_predecessors_run EV g r semis [] acc acc [AuditSemiOuterCase 3]
| AuditSemiPredsCons edge rest initial middle result here later :
    audit_semi_predecessor_run EV g r semis initial edge middle here ->
    audit_semi_predecessors_run EV g r semis rest middle result later ->
    audit_semi_predecessors_run EV g r semis (edge :: rest) initial result
      (AuditSemiOuterCase 4 :: here ++ later).

Inductive audit_semi_settle_run {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (r : dfs_result V E) : SemiState.t V -> V -> SemiState.t V ->
    list (audit_semi_outer_call V E) -> Prop :=
| AuditSemiSettleRoot st w : Map.get EV w (tree_edge r) = None ->
    audit_semi_settle_run p r st w st [AuditSemiOuterTreeGet w (tree_edge r) None;
  AuditSemiOuterCase 5]
| AuditSemiSettleNode st w edge parent incoming edges links' best events :
    Map.get EV w (tree_edge r) = Some edge -> parent = Graph.source g edge ->
    incoming = Map.get EV w (in_index p) -> edges = match incoming with Some xs => xs | None => []
  end ->
    audit_semi_predecessors_run EV g r (SemiState.result st) edges (SemiState.links st, parent)
  (links', best) events ->
    audit_semi_settle_run p r st w
      (SemiState.Make (Map.set EV w best (SemiState.result st)) (semi_link EV links' w parent))
      ([AuditSemiOuterTreeGet w (tree_edge r) (Some edge); AuditSemiOuterCase 6;
        AuditSemiOuterSource edge parent; AuditSemiOuterPredGet w (in_index p) incoming] ++ events
  ++
       [AuditSemiOuterResultSet w best (SemiState.result st); AuditSemiOuterLink w parent links']).

Inductive audit_semi_settles_run {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (r : dfs_result V E) : list V -> SemiState.t V -> SemiState.t V ->
    list (audit_semi_outer_call V E) -> Prop :=
| AuditSemiSettlesNil st : audit_semi_settles_run p r [] st st [AuditSemiOuterCase 7]
| AuditSemiSettlesCons v rest initial middle result here later :
    audit_semi_settle_run p r initial v middle here -> audit_semi_settles_run p r rest middle result
  later ->
    audit_semi_settles_run p r (v :: rest) initial result (AuditSemiOuterCase 8 :: here ++ later).

Definition audit_semi_compute_run {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (r : dfs_result V E) (result : SemiState.t V)
    (events : list (audit_semi_outer_call V E)) : Prop :=
  exists inner, audit_semi_settles_run p r (rev (preorder r))
    (SemiState.Make Map.empty semi_links_empty) result inner /\
    events = AuditSemiOuterOutput (length (preorder r)) :: inner.

Definition audit_semi_outer_event_work {V E} (EV : encoding V) (event : audit_semi_outer_call V E) :
  nat :=
  64 + match event with
  | AuditSemiOuterInner item => audit_semi_call_work EV item
  | AuditSemiOuterTreeGet v _ _ | AuditSemiOuterPredGet v _ _ =>
      audit_encoding_weight (audit_key_bits_weight (encode EV v)) + audit_get_weight (encode EV v)
  | AuditSemiOuterResultSet v _ _ => audit_encoding_weight (audit_key_bits_weight (encode EV v)) +
  audit_set_weight (encode EV v)
  | AuditSemiOuterLink v _ _ => 3 * (audit_encoding_weight (audit_key_bits_weight (encode EV v)) +
  audit_set_weight (encode EV v))
  | AuditSemiOuterOutput size => S size
  | _ => 0 end.

Definition audit_semi_compute_work {V E} (EV : encoding V) (events : list (audit_semi_outer_call V
  E)) : nat :=
  256 * S (length events) * S (length events) +
    fold_right (fun event total => audit_semi_outer_event_work EV event + total) 0 events.

Definition audit_semi_compute_input_edges {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (r : dfs_result V E) : nat :=
  fold_right (fun v total => length (pred_edges p v) + total) 0 (preorder r).

Definition audit_semi_compute_rank_bound {V E} (r : dfs_result V E) : nat :=
  fold_right Nat.max 1 (map (fun row => Pos.to_nat (snd row)) (Map.elements (pre_num r))).

Definition audit_semi_compute_width {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (r : dfs_result V E) : nat :=
  let pred_edges_all := flat_map snd (Map.elements (in_index p)) in
  let tree_edges := map snd (Map.elements (tree_edge r)) in
  let vertices := preorder r ++ map fst (Map.elements (pre_num r)) ++
    map fst (Map.elements (tree_edge r)) ++ map fst (Map.elements (in_index p)) ++
    map (Graph.source g) (pred_edges_all ++ tree_edges) in
  Nat.max (fold_right Nat.max 0 (map (fun v => audit_key_bits_weight (encode EV v)) vertices))
    (fold_right Nat.max 0 (map (fun row => audit_key_bits_weight (snd row)) (Map.elements (pre_num
  r)))).

Definition audit_semi_compute_event_bound {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (r : dfs_result V E) : nat :=
  100 * S (length (preorder r)) * S (audit_semi_compute_input_edges p r) * S
  (audit_semi_compute_rank_bound r).

Definition audit_semi_compute_input_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (r : dfs_result V E) : nat :=
  let events := audit_semi_compute_event_bound p r in
  let width := audit_semi_compute_width EV g p r in
  512 * S events * S events + events * (512 + 16 * width).

Definition audit_semi_compute_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) (r : dfs_result V E),
    exists result events, audit_semi_compute_run p r result events /\ result = semi_compute p r /\
      length events <= audit_semi_compute_event_bound p r /\
      audit_semi_compute_work EV events <= audit_semi_compute_input_budget EV g p r.

Definition audit_semi_compute_unique_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) (r : dfs_result V E) a b ea eb,
    audit_semi_compute_run p r a ea -> audit_semi_compute_run p r b eb -> a = b /\ ea = eb.

From Galois.Collections Require Import CollectionsAuditMap CollectionsAuditCompare.
Inductive audit_semi_nested_event (V B : Type) : Type :=
| SemiNestedCase : nat -> audit_semi_nested_event V B
| SemiNestedVertexMap : audit_map_event V V B -> audit_semi_nested_event V B
| SemiNestedRankMap : audit_map_event V positive B -> audit_semi_nested_event V B
| SemiNestedCompare : positive -> positive -> bool -> list audit_positive_compare_event ->
    audit_semi_nested_event V B.
Arguments SemiNestedCase {V B} _.
Arguments SemiNestedVertexMap {V B} _.
Arguments SemiNestedRankMap {V B} _.
Arguments SemiNestedCompare {V B} _ _ _ _.

Definition audit_semi_nested_rank {V E B} (enc : V -> positive * list B)
    (r : dfs_result V E) (v : V) : positive * list (audit_semi_nested_event V B) :=
  let '(found, events) := audit_map_get enc v (pre_num r) in
  (match found with Some x => x | None => 1%positive end, map SemiNestedRankMap events).

Definition audit_semi_nested_score {V E B} (enc : V -> positive * list B)
    (r : dfs_result V E) (semis : Map.t V V) (v : V)
    : positive * list (audit_semi_nested_event V B) :=
  let '(found, events) := audit_map_get enc v semis in
  let next := match found with Some x => x | None => v end in
  let '(score, rank_events) := audit_semi_nested_rank enc r next in
  (score, map SemiNestedVertexMap events ++ rank_events).

Definition audit_semi_nested_label {V B} (enc : V -> positive * list B)
    (st : SemiLinks.t V) (v : V) : V * list (audit_semi_nested_event V B) :=
  let '(found, events) := audit_map_get enc v (SemiLinks.labels st) in
  (match found with Some x => x | None => v end, map SemiNestedVertexMap events).

Definition audit_semi_nested_shortcut_set {V B} (enc : V -> positive * list B)
    (st : SemiLinks.t V) (v root best : V) : SemiLinks.t V * list (audit_semi_nested_event V B) :=
  let '(shortcuts, first) := audit_map_set enc v root (SemiLinks.shortcut st) in
  let '(labels, second) := audit_map_set enc v best (SemiLinks.labels st) in
  (SemiLinks.Make (SemiLinks.original st) shortcuts labels,
    map SemiNestedVertexMap first ++ map SemiNestedVertexMap second).

Inductive audit_semi_nested_compress_run {V E B} (enc : V -> positive * list B)
    (r : dfs_result V E) (semis : Map.t V V) (st : SemiLinks.t V)
    : V -> semi_query_result V -> list (audit_semi_nested_event V B) -> Prop :=
| SemiNestedRoot v get_events :
    audit_map_get enc v (SemiLinks.shortcut st) = (None, get_events) ->
    audit_semi_nested_compress_run enc r semis st v (st, (v, None))
      (map SemiNestedVertexMap get_events ++ [SemiNestedCase 0])
| SemiNestedStopped v a get_events ra rv ea ev compare_events :
    audit_map_get enc v (SemiLinks.shortcut st) = (Some a, get_events) ->
    audit_semi_nested_rank enc r a = (ra, ea) -> audit_semi_nested_rank enc r v = (rv, ev) ->
    audit_positive_ltb ra rv = (false, compare_events) ->
    audit_semi_nested_compress_run enc r semis st v (st, (v, None))
      (map SemiNestedVertexMap get_events ++ ea ++ ev ++
        [SemiNestedCompare ra rv false compare_events; SemiNestedCase 1])
| SemiNestedRecurNone v a get_events ra rv ea ev compare_events st' root inner
    label label_events final set_events :
    audit_map_get enc v (SemiLinks.shortcut st) = (Some a, get_events) ->
    audit_semi_nested_rank enc r a = (ra, ea) -> audit_semi_nested_rank enc r v = (rv, ev) ->
    audit_positive_ltb ra rv = (true, compare_events) ->
    audit_semi_nested_compress_run enc r semis st a (st', (root, None)) inner ->
    audit_semi_nested_label enc st v = (label, label_events) ->
    audit_semi_nested_shortcut_set enc st' v root label = (final, set_events) ->
    audit_semi_nested_compress_run enc r semis st v (final, (root, Some label))
      (map SemiNestedVertexMap get_events ++ ea ++ ev ++
        [SemiNestedCompare ra rv true compare_events; SemiNestedCase 2] ++ inner ++
        [SemiNestedCase 3] ++ label_events ++ set_events)
| SemiNestedRecurSome v a get_events ra rv ea ev compare_events st' root u inner
    label label_events sl su el eu choose choose_events final set_events :
    audit_map_get enc v (SemiLinks.shortcut st) = (Some a, get_events) ->
    audit_semi_nested_rank enc r a = (ra, ea) -> audit_semi_nested_rank enc r v = (rv, ev) ->
    audit_positive_ltb ra rv = (true, compare_events) ->
    audit_semi_nested_compress_run enc r semis st a (st', (root, Some u)) inner ->
    audit_semi_nested_label enc st v = (label, label_events) ->
    audit_semi_nested_score enc r semis label = (sl, el) ->
    audit_semi_nested_score enc r semis u = (su, eu) ->
    audit_positive_leb sl su = (choose, choose_events) ->
    audit_semi_nested_shortcut_set enc st' v root (if choose then label else u) = (final,
  set_events) ->
    audit_semi_nested_compress_run enc r semis st v (final, (root, Some (if choose then label else
  u)))
      (map SemiNestedVertexMap get_events ++ ea ++ ev ++
        [SemiNestedCompare ra rv true compare_events; SemiNestedCase 2] ++ inner ++
        [SemiNestedCase 4] ++ label_events ++ el ++ eu ++
        [SemiNestedCompare sl su choose choose_events] ++ set_events).

Definition audit_semi_nested_compress_erasure_statement : Prop :=
  forall V E B (EV : encoding V) (enc : V -> positive * list B) (r : dfs_result V E) semis st v,
    (forall x, fst (enc x) = encode EV x) ->
    exists result events, audit_semi_nested_compress_run enc r semis st v result events /\
      result = semi_compress EV (semi_rank EV r) (fun x => semi_rank EV r (semi_value EV semis x))
  st v.

Definition audit_semi_nested_compress_unique_statement : Prop :=
  forall V E B enc (r : dfs_result V E) semis st v first first_events second second_events,
    audit_semi_nested_compress_run (B := B) enc r semis st v first first_events ->
    audit_semi_nested_compress_run enc r semis st v second second_events ->
    first = second /\ first_events = second_events.

Definition audit_semi_nested_event_work {V B} (weight : B -> nat)
    (event : audit_semi_nested_event V B) : nat :=
  let body := fun events => fold_right (fun item n => weight item + n) 0 events in
  64 + match event with
  | SemiNestedVertexMap map_event => audit_map_source_work body [map_event]
  | SemiNestedRankMap map_event => audit_map_source_work body [map_event]
  | SemiNestedCompare _ _ _ events => audit_positive_order_source_work events
  | SemiNestedCase _ => 0
  end.

Definition audit_semi_nested_body_event_work {V B} (weight : B -> nat)
    (event : audit_semi_nested_event V B) : nat :=
  match event with
  | SemiNestedVertexMap (AuditMapGet _ _ _ _ body _)
  | SemiNestedVertexMap (AuditMapSet _ _ _ _ _ body _)
  | SemiNestedVertexMap (AuditMapRemove _ _ _ _ body _)
  | SemiNestedRankMap (AuditMapGet _ _ _ _ body _)
  | SemiNestedRankMap (AuditMapSet _ _ _ _ _ body _)
  | SemiNestedRankMap (AuditMapRemove _ _ _ _ body _) =>
      fold_right (fun item n => weight item + n) 0 body
  | SemiNestedCase _ | SemiNestedCompare _ _ _ _ => 0
  end.

Definition audit_semi_nested_work {V B} (weight : B -> nat)
    (events : list (audit_semi_nested_event V B)) : nat :=
  fold_right (fun event n => audit_semi_nested_event_work weight event + n) 0 events.

Definition audit_semi_nested_body_work {V B} (weight : B -> nat)
    (events : list (audit_semi_nested_event V B)) : nat :=
  fold_right (fun event n => audit_semi_nested_body_event_work weight event + n) 0 events.

Definition audit_semi_nested_width {V E} (EV : encoding V) (r : dfs_result V E)
    (semis : Map.t V V) (st : SemiLinks.t V) (v : V) : nat :=
  let rows := Map.elements (SemiLinks.shortcut st) ++ Map.elements (SemiLinks.labels st) ++
    Map.elements semis in
  let vertices := v :: map fst rows ++ map snd rows ++ map fst (Map.elements (pre_num r)) in
  Nat.max (fold_right Nat.max 0 (map (fun x => Pos.size_nat (encode EV x)) vertices))
    (fold_right Nat.max 0 (map (fun row => Pos.size_nat (snd row)) (Map.elements (pre_num r)))).

Definition audit_semi_nested_input_budget {V E} (EV : encoding V) (r : dfs_result V E)
    (semis : Map.t V V) (st : SemiLinks.t V) (v : V) : nat :=
  let count := 20 * S (Pos.to_nat (semi_rank EV r v)) in
  128 * S count * S count + count * (256 + 32 * audit_semi_nested_width EV r semis st v).

Definition audit_semi_nested_compress_bound_statement : Prop :=
  forall V E B (EV : encoding V) (enc : V -> positive * list B) (weight : B -> nat)
    (r : dfs_result V E) semis st v result events,
    (forall x, fst (enc x) = encode EV x) ->
    audit_semi_nested_compress_run enc r semis st v result events ->
    length events <= 20 * S (Pos.to_nat (semi_rank EV r v)) /\
    audit_semi_nested_work weight events <=
      audit_semi_nested_input_budget EV r semis st v + audit_semi_nested_body_work weight events.
Inductive audit_semi_producer_nested_event (V E B : Type) : Type :=
| SemiProducerCase : nat -> audit_semi_producer_nested_event V E B
| SemiProducerSource : E -> V -> list B -> audit_semi_producer_nested_event V E B
| SemiProducerInner : audit_semi_nested_event V B -> audit_semi_producer_nested_event V E B
| SemiProducerTreeMap : audit_map_event V E B -> audit_semi_producer_nested_event V E B
| SemiProducerPredMap : audit_map_event V (list E) B -> audit_semi_producer_nested_event V E B
| SemiProducerOutput : nat -> audit_semi_producer_nested_event V E B.
Arguments SemiProducerCase {V E B} _.
Arguments SemiProducerSource {V E B} _ _ _.
Arguments SemiProducerInner {V E B} _.
Arguments SemiProducerTreeMap {V E B} _.
Arguments SemiProducerPredMap {V E B} _.
Arguments SemiProducerOutput {V E B} _.

Definition audit_semi_producer_link {V E B} (enc : V -> positive * list B)
    (st : SemiLinks.t V) (v parent : V)
    : SemiLinks.t V * list (audit_semi_producer_nested_event V E B) :=
  let '(original, a) := audit_map_set enc v parent (SemiLinks.original st) in
  let '(shortcut, b) := audit_map_set enc v parent (SemiLinks.shortcut st) in
  let '(labels, c) := audit_map_set enc v v (SemiLinks.labels st) in
  (SemiLinks.Make original shortcut labels,
    map (fun item => SemiProducerInner (SemiNestedVertexMap item)) (a ++ b ++ c)).

Inductive audit_semi_producer_pred_run {V E B} (enc : V -> positive * list B)
    (source : E -> V * list B) (r : dfs_result V E) (semis : Map.t V V) :
    SemiLinks.t V * V -> E -> SemiLinks.t V * V -> list (audit_semi_producer_nested_event V E B) ->
  Prop :=
| SemiProducerPredMissing st best edge vertex source_body rank_events :
    source edge = (vertex, source_body) -> audit_map_get enc vertex (pre_num r) = (None,
  rank_events) ->
    audit_semi_producer_pred_run enc source r semis (st, best) edge (st, best)
      ([SemiProducerSource edge vertex source_body] ++
       map (fun item => SemiProducerInner (SemiNestedRankMap item)) rank_events ++ [SemiProducerCase
  0])
| SemiProducerPredNumbered st best edge vertex source_body number rank_events st' root part inner
    u value value_events best_rank value_rank best_events value_rank_events choose compare_events :
    source edge = (vertex, source_body) -> audit_map_get enc vertex (pre_num r) = (Some number,
  rank_events) ->
    audit_semi_nested_compress_run enc r semis st vertex (st', (root, part)) inner ->
    u = match part with Some chosen => chosen | None => vertex end ->
    audit_map_get enc u semis = (value, value_events) ->
    audit_semi_nested_rank enc r best = (best_rank, best_events) ->
    audit_semi_nested_rank enc r (match value with Some x => x | None => u end) = (value_rank,
  value_rank_events) ->
    audit_positive_leb best_rank value_rank = (choose, compare_events) ->
    audit_semi_producer_pred_run enc source r semis (st, best) edge
      (st', if choose then best else match value with Some x => x | None => u end)
      ([SemiProducerSource edge vertex source_body] ++
       map (fun item => SemiProducerInner (SemiNestedRankMap item)) rank_events ++ [SemiProducerCase
  1] ++
       map SemiProducerInner inner ++ [SemiProducerCase 2] ++
       map (fun item => SemiProducerInner (SemiNestedVertexMap item)) value_events ++
       map SemiProducerInner best_events ++ map SemiProducerInner value_rank_events ++
       [SemiProducerInner (SemiNestedCompare best_rank value_rank choose compare_events)]).

Inductive audit_semi_producer_preds_run {V E B} (enc : V -> positive * list B)
    (source : E -> V * list B) (r : dfs_result V E) (semis : Map.t V V) :
    list E -> SemiLinks.t V * V -> SemiLinks.t V * V -> list (audit_semi_producer_nested_event V E
  B) -> Prop :=
| SemiProducerPredsNil acc : audit_semi_producer_preds_run enc source r semis [] acc acc
  [SemiProducerCase 3]
| SemiProducerPredsCons edge rest initial middle result here later :
    audit_semi_producer_pred_run enc source r semis initial edge middle here ->
    audit_semi_producer_preds_run enc source r semis rest middle result later ->
    audit_semi_producer_preds_run enc source r semis (edge :: rest) initial result
      (SemiProducerCase 4 :: here ++ later).

Inductive audit_semi_producer_settle_run {V E B} {EV : encoding V} {g : Graph.t V E}
    (enc : V -> positive * list B) (source : E -> V * list B) (p : prepared EV g) (r : dfs_result V
  E) :
    SemiState.t V -> V -> SemiState.t V -> list (audit_semi_producer_nested_event V E B) -> Prop :=
| SemiProducerSettleRoot st v tree_events : audit_map_get enc v (tree_edge r) = (None, tree_events)
  ->
    audit_semi_producer_settle_run enc source p r st v st
      (map SemiProducerTreeMap tree_events ++ [SemiProducerCase 5])
| SemiProducerSettleNode st v edge tree_events parent source_body incoming pred_events edges
    links' best pred_steps result_map result_events links'' link_events :
    audit_map_get enc v (tree_edge r) = (Some edge, tree_events) -> source edge = (parent,
  source_body) ->
    audit_map_get enc v (in_index p) = (incoming, pred_events) ->
    edges = match incoming with Some xs => xs | None => [] end ->
    audit_semi_producer_preds_run enc source r (SemiState.result st) edges
      (SemiState.links st, parent) (links', best) pred_steps ->
    audit_map_set enc v best (SemiState.result st) = (result_map, result_events) ->
    audit_semi_producer_link enc links' v parent = (links'', link_events) ->
    audit_semi_producer_settle_run enc source p r st v (SemiState.Make result_map links'')
      (map SemiProducerTreeMap tree_events ++ [SemiProducerCase 6; SemiProducerSource edge parent
  source_body] ++
       map SemiProducerPredMap pred_events ++ pred_steps ++
       map (fun item => SemiProducerInner (SemiNestedVertexMap item)) result_events ++ link_events).

Inductive audit_semi_producer_settles_run {V E B} {EV : encoding V} {g : Graph.t V E}
    (enc : V -> positive * list B) (source : E -> V * list B) (p : prepared EV g) (r : dfs_result V
  E) :
    list V -> SemiState.t V -> SemiState.t V -> list (audit_semi_producer_nested_event V E B) ->
  Prop :=
| SemiProducerSettlesNil st : audit_semi_producer_settles_run enc source p r [] st st
  [SemiProducerCase 7]
| SemiProducerSettlesCons v rest initial middle result here later :
    audit_semi_producer_settle_run enc source p r initial v middle here ->
    audit_semi_producer_settles_run enc source p r rest middle result later ->
    audit_semi_producer_settles_run enc source p r (v :: rest) initial result
      (SemiProducerCase 8 :: here ++ later).

Definition audit_semi_producer_nested_run {V E B} {EV : encoding V} {g : Graph.t V E}
    (enc : V -> positive * list B) (source : E -> V * list B) (p : prepared EV g) (r : dfs_result V
  E)
    (result : SemiState.t V) (events : list (audit_semi_producer_nested_event V E B)) : Prop :=
  exists inner, audit_semi_producer_settles_run enc source p r (rev (preorder r))
    (SemiState.Make Map.empty semi_links_empty) result inner /\
    events = SemiProducerOutput (length (preorder r)) :: inner.

Definition audit_semi_producer_nested_erasure_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) (r : dfs_result V E)
    (enc : V -> positive * list B) (source : E -> V * list B),
    (forall v, fst (enc v) = encode EV v) -> (forall e, fst (source e) = Graph.source g e) ->
    exists result events, audit_semi_producer_nested_run enc source p r result events /\
      result = semi_compute p r.

Definition audit_semi_producer_nested_unique_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) (r : dfs_result V E)
    (enc : V -> positive * list B) (source : E -> V * list B) a ea b eb,
    audit_semi_producer_nested_run enc source p r a ea -> audit_semi_producer_nested_run enc source
  p r b eb ->
    a = b /\ ea = eb.

Definition audit_semi_producer_nested_event_work {V E B} (weight : B -> nat)
    (event : audit_semi_producer_nested_event V E B) : nat :=
  let body := fun events => fold_right (fun item n => weight item + n) 0 events in
  64 + match event with
  | SemiProducerSource _ _ events => body events
  | SemiProducerInner item => audit_semi_nested_event_work weight item
  | SemiProducerTreeMap item => audit_map_source_work body [item]
  | SemiProducerPredMap item => audit_map_source_work body [item]
  | SemiProducerOutput size => S size
  | SemiProducerCase _ => 0
  end.

Definition audit_semi_producer_nested_body_event_work {V E B} (weight : B -> nat)
    (event : audit_semi_producer_nested_event V E B) : nat :=
  match event with
  | SemiProducerSource _ _ body => fold_right (fun item n => weight item + n) 0 body
  | SemiProducerInner item => audit_semi_nested_body_event_work weight item
  | SemiProducerTreeMap (AuditMapGet _ _ _ _ body _) |
    SemiProducerTreeMap (AuditMapSet _ _ _ _ _ body _) |
    SemiProducerTreeMap (AuditMapRemove _ _ _ _ body _) |
    SemiProducerPredMap (AuditMapGet _ _ _ _ body _) |
    SemiProducerPredMap (AuditMapSet _ _ _ _ _ body _) |
    SemiProducerPredMap (AuditMapRemove _ _ _ _ body _) =>
      fold_right (fun item n => weight item + n) 0 body
  | SemiProducerCase _ | SemiProducerOutput _ => 0
  end.

Definition audit_semi_producer_nested_work {V E B} (weight : B -> nat)
    (events : list (audit_semi_producer_nested_event V E B)) : nat :=
  fold_right (fun item n => audit_semi_producer_nested_event_work weight item + n) 0 events.

Definition audit_semi_producer_nested_body_work {V E B} (weight : B -> nat)
    (events : list (audit_semi_producer_nested_event V E B)) : nat :=
  fold_right (fun item n => audit_semi_producer_nested_body_event_work weight item + n) 0 events.

Definition audit_semi_producer_input_rank {V E} (r : dfs_result V E) : nat :=
  fold_right Nat.max 1 (map (fun row => Pos.to_nat (snd row)) (Map.elements (pre_num r))).

Definition audit_semi_producer_input_edges {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (r : dfs_result V E) : nat :=
  fold_right (fun v n => length (pred_edges p v) + n) 0 (preorder r).

Definition audit_semi_producer_input_width {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (r : dfs_result V E) : nat :=
  let edges := flat_map snd (Map.elements (in_index p)) ++ map snd (Map.elements (tree_edge r)) in
  let vertices := preorder r ++ map fst (Map.elements (pre_num r)) ++
    map fst (Map.elements (tree_edge r)) ++ map fst (Map.elements (in_index p)) ++ map (Graph.source
  g) edges in
  Nat.max (fold_right Nat.max 0 (map (fun v => Pos.size_nat (encode EV v)) vertices))
    (fold_right Nat.max 0 (map (fun row => Pos.size_nat (snd row)) (Map.elements (pre_num r)))).

Definition audit_semi_producer_event_bound {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (r : dfs_result V E) : nat :=
  100 * S (length (preorder r)) * S (audit_semi_producer_input_edges p r) *
    S (audit_semi_producer_input_rank r).

Definition audit_semi_producer_input_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (r : dfs_result V E) : nat :=
  let count := audit_semi_producer_event_bound p r in
  512 * S count * S count + count * (512 + 64 * audit_semi_producer_input_width EV g p r).

Definition audit_semi_producer_nested_bound_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) (r : dfs_result V E)
    (enc : V -> positive * list B) (source : E -> V * list B) (weight : B -> nat) result events,
    (forall v, fst (enc v) = encode EV v) -> (forall e, fst (source e) = Graph.source g e) ->
    audit_semi_producer_nested_run enc source p r result events ->
    length events <= audit_semi_producer_event_bound p r /\
    audit_semi_producer_nested_work weight events <=
      audit_semi_producer_input_budget EV g p r + audit_semi_producer_nested_body_work weight
  events.
From Galois.Graph Require Import GraphAuditVirtual.
Definition audit_virtual_semi_run {V E B} (EV : encoding V) (g : Graph.t V E)
    (cb : audit_virtual_base_callbacks V E B) (source : E -> V * list B)
    (result : SemiState.t (V + unit))
    (events : list (audit_semi_producer_nested_event (V + unit) (E + V) (audit_virtual_full_call V E
  B)))
    : Prop :=
  let '(p, (search, _)) := audit_virtual_full_search_with_prepared EV g cb in
  audit_semi_producer_nested_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
    p search result events.

Definition audit_virtual_semi_erasure_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (cb : audit_virtual_base_callbacks V E B) (source : E -> V * list B),
    audit_virtual_base_callbacks_erase EV g cb ->
    (forall edge, fst (source edge) = Graph.source g edge) ->
    exists result events, audit_virtual_semi_run EV g cb source result events /\
      result = semi_compute (virtual_prepared p) (virtual_dfs p).

Definition audit_virtual_semi_stage_work {V E B} (weight : B -> nat)
    (events : list (audit_semi_producer_nested_event (V + unit) (E + V) (audit_virtual_full_call V E
  B))) : nat :=
  audit_semi_producer_nested_work
    (fun event => audit_virtual_full_internal_event_work event + audit_virtual_full_body_event_work
  weight event)
    events.

Definition audit_virtual_semi_external_work {V E B} (weight : B -> nat)
    (events : list (audit_semi_producer_nested_event (V + unit) (E + V) (audit_virtual_full_call V E
  B))) : nat :=
  audit_semi_producer_nested_body_work (audit_virtual_full_body_event_work weight) events.

```

## Galois.Graph.GraphAuditLengauerTarjan

Card: AUD-GR-MODELS

Source destination: `theories/Graph/GraphAuditLengauerTarjan.v`.

```rocq
From Stdlib Require Import List Bool PArith ZArith.
From Galois.Collections Require Import CollectionsAuditCost CollectionsEncoding CollectionsMap
  CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphDominance GraphSemiDominators
  GraphAuditBase GraphAuditDfs GraphAuditVirtual.
Import List.ListNotations.
From Galois.Graph Require Import GraphAuditSemiDominators.

From Galois.Graph Require Import GraphLengauerTarjan.

Inductive audit_lt_call (V E : Type) : Type :=
| AuditLtCase (site : nat)
| AuditLtInner (event : audit_semi_call V)
| AuditLtBucketGet (v : V) (m : Map.t V (list V)) (result : option (list V))
| AuditLtBucketSet (v : V) (value : list V) (m : Map.t V (list V))
| AuditLtTreeGet (v : V) (m : Map.t V E) (result : option E)
| AuditLtSource (e : E) (v : V)
| AuditLtLink (v parent : V) (st : SemiLinks.t V)
| AuditLtEncode (v : V) (code : positive)
| AuditLtEq (a b : positive) (result : bool)
| AuditLtOutput (size : nat).
Arguments AuditLtCase {V E} _.
Arguments AuditLtInner {V E} _.
Arguments AuditLtBucketGet {V E} _ _ _.
Arguments AuditLtBucketSet {V E} _ _ _.
Arguments AuditLtTreeGet {V E} _ _ _.
Arguments AuditLtSource {V E} _ _.
Arguments AuditLtLink {V E} _ _ _.
Arguments AuditLtEncode {V E} _ _.
Arguments AuditLtEq {V E} _ _ _.
Arguments AuditLtOutput {V E} _.

Fixpoint audit_lt_buckets_counted {V E} (EV : encoding V) (semis : Map.t V V)
    (order : list V) (buckets : Map.t V (list V)) : Map.t V (list V) * list (audit_lt_call V E) :=
  match order with
  | [] => (buckets, [AuditLtCase 0])
  | v :: rest => let found := Map.get EV v semis in
    match found with
    | None => let '(result, events) := audit_lt_buckets_counted EV semis rest buckets in
        (result, AuditLtCase 1 :: AuditLtInner (AuditSemiGet v semis None) :: AuditLtCase 2 ::
  events)
    | Some s => let old := Map.get EV s buckets in
        let row := match old with Some xs => xs | None => [] end in
        let next := Map.set EV s (v :: row) buckets in
        let '(result, events) := audit_lt_buckets_counted EV semis rest next in
        (result, AuditLtCase 1 :: AuditLtInner (AuditSemiGet v semis (Some s)) :: AuditLtCase 3 ::
          AuditLtBucketGet s buckets old :: AuditLtBucketSet s (v :: row) buckets :: events)
    end
  end.

Inductive audit_lt_member_run {V E} (EV : encoding V) (r : dfs_result V E) (semis : Map.t V V)
    (s : V) : LtState.t V -> V -> LtState.t V -> list (audit_lt_call V E) -> Prop :=
| AuditLtMember st v links' root part inner u score score_events rank rank_events choose :
    audit_semi_compress_run EV r semis (LtState.links st) v (links', (root, part)) inner ->
    u = match part with Some best => best | None => v end ->
    audit_semi_score_counted EV r semis u = (score, score_events) ->
    audit_semi_rank_counted EV r s = (rank, rank_events) -> choose = Pos.ltb score rank ->
    let parent := if choose then u else s in
    audit_lt_member_run EV r semis s st v (LtState.Make links' (Map.set EV v parent (LtState.parents
  st)))
      (map AuditLtInner inner ++ [AuditLtCase 4] ++ map AuditLtInner score_events ++
       map AuditLtInner rank_events ++ [AuditLtInner (AuditSemiLess score rank choose);
         AuditLtInner (AuditSemiSet v parent (LtState.parents st))]).

Inductive audit_lt_members_run {V E} (EV : encoding V) (r : dfs_result V E) (semis : Map.t V V) (s :
  V) :
    list V -> LtState.t V -> LtState.t V -> list (audit_lt_call V E) -> Prop :=
| AuditLtMembersNil st : audit_lt_members_run EV r semis s [] st st [AuditLtCase 5]
| AuditLtMembersCons v rest initial middle result here later :
    audit_lt_member_run EV r semis s initial v middle here ->
    audit_lt_members_run EV r semis s rest middle result later ->
    audit_lt_members_run EV r semis s (v :: rest) initial result (AuditLtCase 6 :: here ++ later).

Inductive audit_lt_reverse_run {V E} (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E)
    (semis : Map.t V V) (buckets : Map.t V (list V)) : LtState.t V -> V -> LtState.t V -> list
  (audit_lt_call V E) -> Prop :=
| AuditLtReverseRoot st s bucket members settled events :
    bucket = Map.get EV s buckets -> members = match bucket with Some xs => xs | None => [] end ->
    audit_lt_members_run EV r semis s members st settled events -> Map.get EV s (tree_edge r) = None
  ->
    audit_lt_reverse_run EV g r semis buckets st s settled
      ([AuditLtBucketGet s buckets bucket] ++ events ++ [AuditLtTreeGet s (tree_edge r) None;
  AuditLtCase 7])
| AuditLtReverseNode st s bucket members settled events edge parent :
    bucket = Map.get EV s buckets -> members = match bucket with Some xs => xs | None => [] end ->
    audit_lt_members_run EV r semis s members st settled events -> Map.get EV s (tree_edge r) = Some
  edge ->
    parent = Graph.source g edge ->
    audit_lt_reverse_run EV g r semis buckets st s
      (LtState.Make (semi_link EV (LtState.links settled) s parent) (LtState.parents settled))
      ([AuditLtBucketGet s buckets bucket] ++ events ++
        [AuditLtTreeGet s (tree_edge r) (Some edge); AuditLtCase 8; AuditLtSource edge parent;
         AuditLtLink s parent (LtState.links settled)]).

Inductive audit_lt_reverse_fold_run {V E} (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E)
    (semis : Map.t V V) (buckets : Map.t V (list V)) : list V -> LtState.t V -> LtState.t V -> list
  (audit_lt_call V E) -> Prop :=
| AuditLtReverseNil st : audit_lt_reverse_fold_run EV g r semis buckets [] st st [AuditLtCase 9]
| AuditLtReverseCons v rest initial middle result here later :
    audit_lt_reverse_run EV g r semis buckets initial v middle here ->
    audit_lt_reverse_fold_run EV g r semis buckets rest middle result later ->
    audit_lt_reverse_fold_run EV g r semis buckets (v :: rest) initial result (AuditLtCase 10 ::
  here ++ later).

Definition audit_lt_correct_counted {V E} (EV : encoding V) (semis provisional corrected : Map.t V
  V)
    (v : V) : Map.t V V * list (audit_lt_call V E) :=
  let found := Map.get EV v provisional in
  match found with
  | None => (corrected, [AuditLtInner (AuditSemiGet v provisional found); AuditLtCase 11])
  | Some u => let a := encode EV u in let '(value, value_events) := audit_semi_value_counted EV
  semis v in
      let b := encode EV value in let equal := Pos.eqb a b in
      let '(parent, parent_events) := if equal then (u, []) else audit_semi_value_counted EV
  corrected u in
      (Map.set EV v parent corrected,
       [AuditLtInner (AuditSemiGet v provisional found); AuditLtCase 12; AuditLtEncode u a] ++
         map AuditLtInner value_events ++ [AuditLtEncode value b; AuditLtEq a b equal] ++
         map AuditLtInner parent_events ++ [AuditLtInner (AuditSemiSet v parent corrected)])
  end.

Fixpoint audit_lt_correct_fold {V E} (EV : encoding V) (semis provisional : Map.t V V)
    (vertices : list V) (corrected : Map.t V V) : Map.t V V * list (audit_lt_call V E) :=
  match vertices with
  | [] => (corrected, [AuditLtCase 13])
  | v :: rest => let '(middle, here) := audit_lt_correct_counted EV semis provisional corrected v in
      let '(result, later) := audit_lt_correct_fold EV semis provisional rest middle in
      (result, AuditLtCase 14 :: here ++ later)
  end.

Definition audit_lt_compute_run {V E} (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E)
    (semis : Map.t V V) (result : Map.t V V) (events : list (audit_lt_call V E)) : Prop :=
  let '(buckets, bucket_events) := audit_lt_buckets_counted EV semis (preorder r) Map.empty in
  exists settled reverse_events,
    audit_lt_reverse_fold_run EV g r semis buckets (rev (preorder r))
      (LtState.Make semi_links_empty Map.empty) settled reverse_events /\
    let '(output, correction_events) := audit_lt_correct_fold EV semis (LtState.parents settled)
  (preorder r) Map.empty in
    result = output /\ events = bucket_events ++ [AuditLtOutput (length (preorder r))] ++
  reverse_events ++ correction_events.

Definition audit_lt_event_work {V E} (EV : encoding V) (event : audit_lt_call V E) : nat :=
  64 + match event with
  | AuditLtInner item => audit_semi_call_work EV item
  | AuditLtBucketGet v _ _ | AuditLtTreeGet v _ _ =>
      audit_encoding_weight (audit_key_bits_weight (encode EV v)) + audit_get_weight (encode EV v)
  | AuditLtBucketSet v _ _ => audit_encoding_weight (audit_key_bits_weight (encode EV v)) +
  audit_set_weight (encode EV v)
  | AuditLtLink v _ _ => 3 * (audit_encoding_weight (audit_key_bits_weight (encode EV v)) +
  audit_set_weight (encode EV v))
  | AuditLtEncode _ code => audit_encoding_weight (audit_key_bits_weight code)
  | AuditLtEq a b _ => audit_binary_weight (Z.pos a) (Z.pos b)
  | AuditLtOutput size => S size
  | _ => 0 end.

Definition audit_lt_model_work {V E} (EV : encoding V) (events : list (audit_lt_call V E)) : nat :=
  256 * S (length events) * S (length events) +
    fold_right (fun event total => audit_lt_event_work EV event + total) 0 events.

Definition audit_lt_event_bound {V E} (r : dfs_result V E) : nat :=
  let n := S (length (preorder r)) in 200 * n * n * S (audit_semi_compute_rank_bound r).

Definition audit_lt_input_width {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) (semis : Map.t V V) : nat :=
  let rows := Map.elements semis in
  let vertices := preorder r ++ map fst rows ++ map snd rows ++ map fst (Map.elements (tree_edge r))
  ++
    map (Graph.source g) (map snd (Map.elements (tree_edge r))) ++ map fst (Map.elements (pre_num
  r)) in
  Nat.max (fold_right Nat.max 0 (map (fun v => audit_key_bits_weight (encode EV v)) vertices))
    (fold_right Nat.max 0 (map (fun row => audit_key_bits_weight (snd row)) (Map.elements (pre_num
  r)))).

Definition audit_lt_input_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) (semis : Map.t V V) : nat :=
  let count := audit_lt_event_bound r in let width := audit_lt_input_width EV g r semis in
  512 * S count * S count + count * (512 + 16 * width).

Definition audit_lt_compute_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E) semis,
    exists result events, audit_lt_compute_run EV g r semis result events /\ result = lt_compute EV
  g r semis /\
      length events <= audit_lt_event_bound r /\ audit_lt_model_work EV events <=
  audit_lt_input_budget EV g r semis.

Definition audit_lt_compute_unique_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E) semis a b ea eb,
    audit_lt_compute_run EV g r semis a ea -> audit_lt_compute_run EV g r semis b eb -> a = b /\ ea
  = eb.

From Galois.Collections Require Import CollectionsAuditMap CollectionsAuditPrimitive
  CollectionsAuditCompare.
From Galois.Graph Require Import GraphAuditVirtual GraphAuditSemiDominators.
Inductive audit_lt_nested_event (V E B : Type) : Type :=
| LtNestedCase : nat -> audit_lt_nested_event V E B
| LtNestedSemi : audit_semi_nested_event V B -> audit_lt_nested_event V E B
| LtNestedProducer : audit_semi_producer_nested_event V E B -> audit_lt_nested_event V E B
| LtNestedBucket : audit_map_event V (list V) B -> audit_lt_nested_event V E B
| LtNestedTree : audit_map_event V E B -> audit_lt_nested_event V E B
| LtNestedSource : E -> V -> list B -> audit_lt_nested_event V E B
| LtNestedEncode : V -> positive -> list B -> audit_lt_nested_event V E B
| LtNestedEqual : positive -> positive -> bool -> list audit_positive_eqb_event ->
  audit_lt_nested_event V E B
| LtNestedOutput : nat -> audit_lt_nested_event V E B.
Arguments LtNestedCase {V E B} _.
Arguments LtNestedSemi {V E B} _.
Arguments LtNestedProducer {V E B} _.
Arguments LtNestedBucket {V E B} _.
Arguments LtNestedTree {V E B} _.
Arguments LtNestedSource {V E B} _ _ _.
Arguments LtNestedEncode {V E B} _ _ _.
Arguments LtNestedEqual {V E B} _ _ _ _.
Arguments LtNestedOutput {V E B} _.

Fixpoint audit_lt_nested_buckets {V E B} (enc : V -> positive * list B) (semis : Map.t V V)
    (order : list V) (buckets : Map.t V (list V)) : Map.t V (list V) * list (audit_lt_nested_event V
  E B) :=
  match order with
  | [] => (buckets, [LtNestedCase 0])
  | v :: rest => let '(found, get_events) := audit_map_get enc v semis in
      match found with
      | None => let '(result, later) := audit_lt_nested_buckets enc semis rest buckets in
          (result, [LtNestedCase 1] ++ map (fun item => LtNestedSemi (SemiNestedVertexMap item))
  get_events ++
            [LtNestedCase 2] ++ later)
      | Some s => let '(old, bucket_events) := audit_map_get enc s buckets in
          let row := match old with Some xs => xs | None => [] end in
          let '(next, set_events) := audit_map_set enc s (v :: row) buckets in
          let '(result, later) := audit_lt_nested_buckets enc semis rest next in
          (result, [LtNestedCase 1] ++ map (fun item => LtNestedSemi (SemiNestedVertexMap item))
  get_events ++
            [LtNestedCase 3] ++ map LtNestedBucket bucket_events ++ map LtNestedBucket set_events ++
  later)
      end
  end.

Inductive audit_lt_nested_member_run {V E B} (enc : V -> positive * list B)
    (r : dfs_result V E) (semis : Map.t V V) (s : V) :
    LtState.t V -> V -> LtState.t V -> list (audit_lt_nested_event V E B) -> Prop :=
| LtNestedMember st v links root part inner u score score_events rank rank_events choose
  compare_events
    parents set_events :
    audit_semi_nested_compress_run enc r semis (LtState.links st) v (links, (root, part)) inner ->
    u = match part with Some best => best | None => v end ->
    audit_semi_nested_score enc r semis u = (score, score_events) ->
    audit_semi_nested_rank enc r s = (rank, rank_events) ->
    audit_positive_ltb score rank = (choose, compare_events) ->
    audit_map_set enc v (if choose then u else s) (LtState.parents st) = (parents, set_events) ->
    audit_lt_nested_member_run enc r semis s st v (LtState.Make links parents)
      (map LtNestedSemi inner ++ [LtNestedCase 4] ++ map LtNestedSemi score_events ++
       map LtNestedSemi rank_events ++ [LtNestedSemi (SemiNestedCompare score rank choose
  compare_events)] ++
       map (fun item => LtNestedSemi (SemiNestedVertexMap item)) set_events).

Inductive audit_lt_nested_members_run {V E B} (enc : V -> positive * list B)
    (r : dfs_result V E) (semis : Map.t V V) (s : V) :
    list V -> LtState.t V -> LtState.t V -> list (audit_lt_nested_event V E B) -> Prop :=
| LtNestedMembersNil st : audit_lt_nested_members_run enc r semis s [] st st [LtNestedCase 5]
| LtNestedMembersCons v rest initial middle result here later :
    audit_lt_nested_member_run enc r semis s initial v middle here ->
    audit_lt_nested_members_run enc r semis s rest middle result later ->
    audit_lt_nested_members_run enc r semis s (v :: rest) initial result (LtNestedCase 6 :: here ++
  later).

Inductive audit_lt_nested_reverse_run {V E B} (enc : V -> positive * list B)
    (source : E -> V * list B) (r : dfs_result V E) (semis : Map.t V V) (buckets : Map.t V (list V))
  :
    LtState.t V -> V -> LtState.t V -> list (audit_lt_nested_event V E B) -> Prop :=
| LtNestedReverseRoot st s bucket bucket_events members settled events tree_events :
    audit_map_get enc s buckets = (bucket, bucket_events) ->
    members = match bucket with Some xs => xs | None => [] end ->
    audit_lt_nested_members_run enc r semis s members st settled events ->
    audit_map_get enc s (tree_edge r) = (None, tree_events) ->
    audit_lt_nested_reverse_run enc source r semis buckets st s settled
      (map LtNestedBucket bucket_events ++ events ++ map LtNestedTree tree_events ++ [LtNestedCase
  7])
| LtNestedReverseNode st s bucket bucket_events members settled events edge tree_events parent
  source_body links link_events :
    audit_map_get enc s buckets = (bucket, bucket_events) ->
    members = match bucket with Some xs => xs | None => [] end ->
    audit_lt_nested_members_run enc r semis s members st settled events ->
    audit_map_get enc s (tree_edge r) = (Some edge, tree_events) -> source edge = (parent,
  source_body) ->
    audit_semi_producer_link enc (LtState.links settled) s parent = (links, link_events) ->
    audit_lt_nested_reverse_run enc source r semis buckets st s (LtState.Make links (LtState.parents
  settled))
      (map LtNestedBucket bucket_events ++ events ++ map LtNestedTree tree_events ++
        [LtNestedCase 8; LtNestedSource edge parent source_body] ++ map LtNestedProducer
  link_events).

Inductive audit_lt_nested_reverse_fold_run {V E B} (enc : V -> positive * list B)
    (source : E -> V * list B) (r : dfs_result V E) (semis : Map.t V V) (buckets : Map.t V (list V))
  :
    list V -> LtState.t V -> LtState.t V -> list (audit_lt_nested_event V E B) -> Prop :=
| LtNestedReverseNil st : audit_lt_nested_reverse_fold_run enc source r semis buckets [] st st
  [LtNestedCase 9]
| LtNestedReverseCons v rest initial middle result here later :
    audit_lt_nested_reverse_run enc source r semis buckets initial v middle here ->
    audit_lt_nested_reverse_fold_run enc source r semis buckets rest middle result later ->
    audit_lt_nested_reverse_fold_run enc source r semis buckets (v :: rest) initial result
      (LtNestedCase 10 :: here ++ later).

Definition audit_lt_nested_correct {V E B} (enc : V -> positive * list B)
    (semis provisional corrected : Map.t V V) (v : V) : Map.t V V * list (audit_lt_nested_event V E
  B) :=
  let '(found, first) := audit_map_get enc v provisional in
  match found with
  | None => (corrected, map (fun item => LtNestedSemi (SemiNestedVertexMap item)) first ++
  [LtNestedCase 11])
  | Some u => let '(a, a_body) := enc u in
      let '(value, value_events) := audit_map_get enc v semis in
      let value := match value with Some x => x | None => v end in
      let '(b, b_body) := enc value in let '(equal, equal_events) := audit_positive_eqb a b in
      let '(parent, parent_events) := if equal then (u, []) else
        let '(found_parent, events) := audit_map_get enc u corrected in
        (match found_parent with Some x => x | None => u end, events) in
      let '(result, set_events) := audit_map_set enc v parent corrected in
      (result, map (fun item => LtNestedSemi (SemiNestedVertexMap item)) first ++ [LtNestedCase 12;
  LtNestedEncode u a a_body] ++
       map (fun item => LtNestedSemi (SemiNestedVertexMap item)) value_events ++
       [LtNestedEncode value b b_body; LtNestedEqual a b equal equal_events] ++
       map (fun item => LtNestedSemi (SemiNestedVertexMap item)) parent_events ++
       map (fun item => LtNestedSemi (SemiNestedVertexMap item)) set_events)
  end.

Fixpoint audit_lt_nested_correct_fold {V E B} (enc : V -> positive * list B)
    (semis provisional : Map.t V V) (vertices : list V) (corrected : Map.t V V)
    : Map.t V V * list (audit_lt_nested_event V E B) :=
  match vertices with
  | [] => (corrected, [LtNestedCase 13])
  | v :: rest => let '(middle, here) := audit_lt_nested_correct enc semis provisional corrected v in
      let '(result, later) := audit_lt_nested_correct_fold enc semis provisional rest middle in
      (result, LtNestedCase 14 :: here ++ later)
  end.

Definition audit_lt_nested_run {V E B} (enc : V -> positive * list B) (source : E -> V * list B)
    (r : dfs_result V E) (semis : Map.t V V) (result : Map.t V V) (events : list
  (audit_lt_nested_event V E B)) : Prop :=
  let '(buckets, bucket_events) := audit_lt_nested_buckets enc semis (preorder r) Map.empty in
  exists settled reverse_events,
    audit_lt_nested_reverse_fold_run enc source r semis buckets (rev (preorder r))
      (LtState.Make semi_links_empty Map.empty) settled reverse_events /\
    let '(output, correction_events) := audit_lt_nested_correct_fold enc semis (LtState.parents
  settled) (preorder r) Map.empty in
    result = output /\ events = bucket_events ++ [LtNestedOutput (length (preorder r))] ++
  reverse_events ++ correction_events.

Definition audit_lt_nested_erasure_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E) semis
    (enc : V -> positive * list B) (source : E -> V * list B),
    (forall v, fst (enc v) = encode EV v) -> (forall e, fst (source e) = Graph.source g e) ->
    exists result events, audit_lt_nested_run enc source r semis result events /\ result =
  lt_compute EV g r semis.

Definition audit_lt_nested_unique_statement : Prop :=
  forall V E B (enc : V -> positive * list B) (source : E -> V * list B) r semis a ea b eb,
    audit_lt_nested_run enc source r semis a ea -> audit_lt_nested_run enc source r semis b eb -> a
  = b /\ ea = eb.

Definition audit_lt_nested_event_work {V E B} (weight : B -> nat) (event : audit_lt_nested_event V E
  B) : nat :=
  let body := fun events => fold_right (fun item n => weight item + n) 0 events in
  64 + match event with
  | LtNestedSemi item => audit_semi_nested_event_work weight item
  | LtNestedProducer item => audit_semi_producer_nested_event_work weight item
  | LtNestedBucket item => audit_map_source_work body [item]
  | LtNestedTree item => audit_map_source_work body [item]
  | LtNestedSource _ _ events | LtNestedEncode _ _ events => body events
  | LtNestedEqual _ _ _ events => audit_positive_eqb_source_work events
  | LtNestedOutput size => S size
  | LtNestedCase _ => 0
  end.

Definition audit_lt_nested_body_event_work {V E B} (weight : B -> nat)
    (event : audit_lt_nested_event V E B) : nat :=
  match event with
  | LtNestedSemi item => audit_semi_nested_body_event_work weight item
  | LtNestedProducer item => audit_semi_producer_nested_body_event_work weight item
  | LtNestedSource _ _ body | LtNestedEncode _ _ body |
    LtNestedBucket (AuditMapGet _ _ _ _ body _) | LtNestedBucket (AuditMapSet _ _ _ _ _ body _) |
    LtNestedBucket (AuditMapRemove _ _ _ _ body _) | LtNestedTree (AuditMapGet _ _ _ _ body _) |
    LtNestedTree (AuditMapSet _ _ _ _ _ body _) | LtNestedTree (AuditMapRemove _ _ _ _ body _) =>
      fold_right (fun item n => weight item + n) 0 body
  | LtNestedCase _ | LtNestedEqual _ _ _ _ | LtNestedOutput _ => 0
  end.

Definition audit_lt_nested_work {V E B} (weight : B -> nat) (events : list (audit_lt_nested_event V
  E B)) : nat :=
  fold_right (fun item n => audit_lt_nested_event_work weight item + n) 0 events.

Definition audit_lt_nested_body_work {V E B} (weight : B -> nat) (events : list
  (audit_lt_nested_event V E B)) : nat :=
  fold_right (fun item n => audit_lt_nested_body_event_work weight item + n) 0 events.

Definition audit_lt_nested_input_width {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) (semis : Map.t V V) : nat :=
  let rows := Map.elements semis in
  let vertices := preorder r ++ map fst rows ++ map snd rows ++ map fst (Map.elements (tree_edge r))
  ++
    map (Graph.source g) (map snd (Map.elements (tree_edge r))) ++ map fst (Map.elements (pre_num
  r)) in
  Nat.max (fold_right Nat.max 0 (map (fun v => Pos.size_nat (encode EV v)) vertices))
    (fold_right Nat.max 0 (map (fun row => Pos.size_nat (snd row)) (Map.elements (pre_num r)))).

Definition audit_lt_nested_input_event_bound {V E} (r : dfs_result V E) : nat :=
  let n := S (length (preorder r)) in 200 * n * n * S (audit_semi_producer_input_rank r).

Definition audit_lt_nested_input_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) (semis : Map.t V V) : nat :=
  let count := audit_lt_nested_input_event_bound r in
  512 * S count * S count + count * (512 + 64 * audit_lt_nested_input_width EV g r semis).

Definition audit_lt_nested_bound_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E) semis
    (enc : V -> positive * list B) (source : E -> V * list B) (weight : B -> nat) result events,
    (forall v, fst (enc v) = encode EV v) -> (forall e, fst (source e) = Graph.source g e) ->
    audit_lt_nested_run enc source r semis result events ->
    length events <= audit_lt_nested_input_event_bound r /\
    audit_lt_nested_work weight events <= audit_lt_nested_input_budget EV g r semis +
  audit_lt_nested_body_work weight events.
Definition audit_virtual_lt_run {V E B} (EV : encoding V) (g : Graph.t V E)
    (cb : audit_virtual_base_callbacks V E B) (source : E -> V * list B)
    (result : Map.t V V)
    (semi_events : list (audit_semi_producer_nested_event (V + unit) (E + V)
  (audit_virtual_full_call V E B)))
    (lt_events : list (audit_lt_nested_event (V + unit) (E + V) (audit_virtual_full_call V E B)))
    (erase_events : list (audit_erase_nested_event V B)) : Prop :=
  let '(vp, (search, _)) := audit_virtual_full_search_with_prepared EV g cb in
  exists semi_state virtual_parents,
    audit_semi_producer_nested_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
      vp search semi_state semi_events /\
    audit_lt_nested_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
      search (SemiState.result semi_state) virtual_parents lt_events /\
    audit_erase_virtual_nested (audit_virtual_base_encode cb) virtual_parents = (result,
  erase_events).

Definition audit_virtual_lt_erasure_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (cb : audit_virtual_base_callbacks V E B) (source : E -> V * list B),
    audit_virtual_base_callbacks_erase EV g cb ->
    (forall edge, fst (source edge) = Graph.source g edge) ->
    exists result semi_events lt_events erase_events,
      audit_virtual_lt_run EV g cb source result semi_events lt_events erase_events /\ result =
  simple_lt_idom p.

Definition audit_virtual_lt_stage_work {V E B} (weight : B -> nat)
    (events : list (audit_lt_nested_event (V + unit) (E + V) (audit_virtual_full_call V E B))) : nat
  :=
  audit_lt_nested_work
    (fun event => audit_virtual_full_internal_event_work event + audit_virtual_full_body_event_work
  weight event)
    events.

Definition audit_virtual_lt_external_work {V E B} (weight : B -> nat)
    (events : list (audit_lt_nested_event (V + unit) (E + V) (audit_virtual_full_call V E B))) : nat
  :=
  audit_lt_nested_body_work (audit_virtual_full_body_event_work weight) events.

From Galois.Graph Require Import GraphAuditVirtual GraphAuditSemiDominators.
Definition audit_virtual_lt_input_support {V E} (g : Graph.t V E) : list V :=
  let edges := flat_map (Graph.out g) (Graph.nodes g) in
  Graph.nodes g ++ Graph.entries g ++ map (Graph.source g) edges ++ map (Graph.target g) edges.

Definition audit_virtual_lt_input_width {V E} (EV : encoding V) (g : Graph.t V E) : nat :=
  fold_right Nat.max 0 (map (fun vertex => Pos.size_nat (encode EV vertex))
  (audit_virtual_lt_input_support g)).

Definition audit_virtual_lt_input_scale {V E} (EV : encoding V) (g : Graph.t V E) : nat :=
  4 + length (Graph.nodes g) + length (Graph.entries g) +
    length (flat_map (Graph.out g) (Graph.nodes g)) + audit_virtual_lt_input_width EV g.

Definition audit_virtual_lt_input_budget {V E} (EV : encoding V) (g : Graph.t V E) : nat :=
  1048576 * Nat.pow (audit_virtual_lt_input_scale EV g) 40.

```

## Galois.Graph.GraphAuditSemiNca

Card: AUD-GR-MODELS

Source destination: `theories/Graph/GraphAuditSemiNca.v`.

```rocq
(** * Semi-NCA source contracts

    Record each ancestor walk and its actual map and comparison bodies.
    For example, a missing parent stops the walk without consulting later ranks.
    Builds on: semidominator and graph source models. *)
From Stdlib Require Import List Bool PArith NArith ZArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet
  CollectionsAuditCost CollectionsAuditTrie CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements
  CollectionsAuditPrimitive CollectionsAuditCompare CollectionsAuditEncoding.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphSemiDominators GraphSemiNca
  GraphAuditBase GraphAuditDfs GraphAuditVirtual GraphAuditSemiDominators.
Import List.ListNotations.
Inductive audit_nca_walk_run {V E} (EV : encoding V) (r : dfs_result V E)
    (limit : positive) (parents : Map.t V V) : V -> V -> list (audit_semi_call V) -> Prop :=
| AuditNcaThreshold v rank events :
    audit_semi_rank_counted EV r v = (rank, events) -> Pos.leb rank limit = true ->
    audit_nca_walk_run EV r limit parents v v (events ++ [AuditSemiLe rank limit true; AuditSemiCase
  20])
| AuditNcaNoParent v rank events :
    audit_semi_rank_counted EV r v = (rank, events) -> Pos.leb rank limit = false ->
    Map.get EV v parents = None ->
    audit_nca_walk_run EV r limit parents v v
      (events ++ [AuditSemiLe rank limit false; AuditSemiCase 21; AuditSemiGet v parents None;
  AuditSemiCase 22])
| AuditNcaStop v rank events a ra rv ea ev :
    audit_semi_rank_counted EV r v = (rank, events) -> Pos.leb rank limit = false ->
    Map.get EV v parents = Some a -> audit_semi_rank_counted EV r a = (ra, ea) ->
    audit_semi_rank_counted EV r v = (rv, ev) -> Pos.ltb ra rv = false ->
    audit_nca_walk_run EV r limit parents v v
      (events ++ [AuditSemiLe rank limit false; AuditSemiCase 21; AuditSemiGet v parents (Some a)]
  ++
        ea ++ ev ++ [AuditSemiLess ra rv false; AuditSemiCase 23])
| AuditNcaRecur v rank events a ra rv ea ev result inner :
    audit_semi_rank_counted EV r v = (rank, events) -> Pos.leb rank limit = false ->
    Map.get EV v parents = Some a -> audit_semi_rank_counted EV r a = (ra, ea) ->
    audit_semi_rank_counted EV r v = (rv, ev) -> Pos.ltb ra rv = true ->
    audit_nca_walk_run EV r limit parents a result inner ->
    audit_nca_walk_run EV r limit parents v result
      (events ++ [AuditSemiLe rank limit false; AuditSemiCase 21; AuditSemiGet v parents (Some a)]
  ++
        ea ++ ev ++ [AuditSemiLess ra rv true; AuditSemiCase 24] ++ inner).

Definition audit_nca_walk_width {V E} (EV : encoding V) (r : dfs_result V E)
    (limit : positive) (parents : Map.t V V) (v : V) : nat :=
  let pairs := Map.elements parents in
  let vertices := v :: map fst pairs ++ map snd pairs ++ map fst (Map.elements (pre_num r)) in
  Nat.max (audit_key_bits_weight limit)
    (Nat.max (fold_right Nat.max 0 (map (fun x => audit_key_bits_weight (encode EV x)) vertices))
      (fold_right Nat.max 0 (map (fun row => audit_key_bits_weight (snd row)) (Map.elements (pre_num
  r))))).

Definition audit_nca_walk_event_bound {V E} (EV : encoding V) (r : dfs_result V E) (v : V) : nat :=
  12 * S (Pos.to_nat (semi_rank EV r v)).

Definition audit_nca_walk_budget {V E} (EV : encoding V) (r : dfs_result V E)
    (limit : positive) (parents : Map.t V V) (v : V) : nat :=
  let count := audit_nca_walk_event_bound EV r v in
  let width := audit_nca_walk_width EV r limit parents v in
  128 * S count * S count + count * (80 + 6 * width).

Definition audit_nca_walk_statement : Prop :=
  forall V E (EV : encoding V) (r : dfs_result V E) limit parents v,
    exists result events, audit_nca_walk_run EV r limit parents v result events /\
      result = nca_walk EV (semi_rank EV r) limit parents v /\
      length events <= audit_nca_walk_event_bound EV r v /\
      audit_semi_compress_work EV events <= audit_nca_walk_budget EV r limit parents v.

Definition audit_nca_walk_unique_statement : Prop :=
  forall V E (EV : encoding V) (r : dfs_result V E) limit parents v x y ex ey,
    audit_nca_walk_run EV r limit parents v x ex -> audit_nca_walk_run EV r limit parents v y ey ->
    x = y /\ ex = ey.


Inductive audit_nca_call (V E : Type) : Type :=
| AuditNcaCase (site : nat)
| AuditNcaTreeGet (v : V) (m : Map.t V E) (result : option E)
| AuditNcaSource (e : E) (v : V)
| AuditNcaInner (event : audit_semi_call V).
Arguments AuditNcaCase {V E} _.
Arguments AuditNcaTreeGet {V E} _ _ _.
Arguments AuditNcaSource {V E} _ _.
Arguments AuditNcaInner {V E} _.

Inductive audit_nca_step_run {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) (semis : Map.t V V) : Map.t V V -> V -> Map.t V V ->
    list (audit_nca_call V E) -> Prop :=
| AuditNcaStepRoot m v : Map.get EV v (tree_edge r) = None ->
    audit_nca_step_run EV g r semis m v m [AuditNcaTreeGet v (tree_edge r) None; AuditNcaCase 0]
| AuditNcaStepNode m v e value value_events limit limit_events source result walk_events :
    Map.get EV v (tree_edge r) = Some e -> audit_semi_value_counted EV semis v = (value,
  value_events) ->
    audit_semi_rank_counted EV r value = (limit, limit_events) -> source = Graph.source g e ->
    audit_nca_walk_run EV r limit m source result walk_events ->
    audit_nca_step_run EV g r semis m v (Map.set EV v result m)
      ([AuditNcaTreeGet v (tree_edge r) (Some e); AuditNcaCase 1] ++ map AuditNcaInner value_events
  ++
       map AuditNcaInner limit_events ++ [AuditNcaSource e source] ++ map AuditNcaInner walk_events
  ++
       [AuditNcaInner (AuditSemiSet v result m)]).

Inductive audit_nca_steps_run {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) (semis : Map.t V V) : list V -> Map.t V V -> Map.t V V ->
    list (audit_nca_call V E) -> Prop :=
| AuditNcaStepsNil m : audit_nca_steps_run EV g r semis [] m m [AuditNcaCase 2]
| AuditNcaStepsCons v rest initial middle result here later :
    audit_nca_step_run EV g r semis initial v middle here ->
    audit_nca_steps_run EV g r semis rest middle result later ->
    audit_nca_steps_run EV g r semis (v :: rest) initial result (AuditNcaCase 3 :: here ++ later).

Definition audit_nca_compute_run {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) (semis : Map.t V V) (result : Map.t V V) (events : list (audit_nca_call V
  E)) : Prop :=
  audit_nca_steps_run EV g r semis (preorder r) Map.empty result events.

Definition audit_nca_event_work {V E} (EV : encoding V) (event : audit_nca_call V E) : nat :=
  64 + match event with
  | AuditNcaTreeGet v _ _ => audit_encoding_weight (audit_key_bits_weight (encode EV v)) +
  audit_get_weight (encode EV v)
  | AuditNcaInner inner => audit_semi_call_work EV inner
  | _ => 0 end.

Definition audit_nca_compute_work {V E} (EV : encoding V) (events : list (audit_nca_call V E)) : nat
  :=
  256 * S (length events) * S (length events) +
    fold_right (fun event total => audit_nca_event_work EV event + total) 0 events.

Definition audit_nca_compute_event_bound {V E} (r : dfs_result V E) : nat :=
  64 * S (length (preorder r)) * S (audit_semi_compute_rank_bound r).

Definition audit_nca_compute_width {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) (semis : Map.t V V) : nat :=
  let rows := Map.elements semis in
  let vertices := preorder r ++ map fst rows ++ map snd rows ++ map fst (Map.elements (tree_edge r))
  ++
    map (Graph.source g) (map snd (Map.elements (tree_edge r))) ++ map fst (Map.elements (pre_num
  r)) in
  Nat.max (fold_right Nat.max 0 (map (fun v => audit_key_bits_weight (encode EV v)) vertices))
    (fold_right Nat.max 0 (map (fun row => audit_key_bits_weight (snd row)) (Map.elements (pre_num
  r)))).

Definition audit_nca_compute_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) (semis : Map.t V V) : nat :=
  let count := audit_nca_compute_event_bound r in
  let width := audit_nca_compute_width EV g r semis in
  512 * S count * S count + count * (256 + 12 * width).

Definition audit_nca_compute_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E) semis,
    exists result events, audit_nca_compute_run EV g r semis result events /\
      result = nca_compute EV g r semis /\ length events <= audit_nca_compute_event_bound r /\
      audit_nca_compute_work EV events <= audit_nca_compute_budget EV g r semis.

Definition audit_nca_compute_unique_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E) semis a b ea eb,
    audit_nca_compute_run EV g r semis a ea -> audit_nca_compute_run EV g r semis b eb -> a = b /\
  ea = eb.

Inductive audit_nca_source_event (V E B : Type) : Type :=
| NcaSourceCase : nat -> audit_nca_source_event V E B
| NcaSourceTree : audit_map_event V E B -> audit_nca_source_event V E B
| NcaSourceSource : E -> V -> list B -> audit_nca_source_event V E B
| NcaSourceInner : audit_semi_nested_event V B -> audit_nca_source_event V E B.
Arguments NcaSourceCase {V E B} _.
Arguments NcaSourceTree {V E B} _.
Arguments NcaSourceSource {V E B} _ _ _.
Arguments NcaSourceInner {V E B} _.

Inductive audit_nca_source_walk_run {V E B} (enc : V -> positive * list B) (r : dfs_result V E)
    (limit : positive) (parents : Map.t V V) : V -> V -> list (audit_semi_nested_event V B) -> Prop
  :=
| NcaSourceThreshold v rank events cmp :
    audit_semi_nested_rank enc r v = (rank, events) -> audit_positive_leb rank limit = (true, cmp)
  ->
    audit_nca_source_walk_run enc r limit parents v v (events ++ [SemiNestedCompare rank limit true
  cmp; SemiNestedCase 20])
| NcaSourceNoParent v rank events cmp reads :
    audit_semi_nested_rank enc r v = (rank, events) -> audit_positive_leb rank limit = (false, cmp)
  ->
    audit_map_get enc v parents = (None, reads) ->
    audit_nca_source_walk_run enc r limit parents v v
      (events ++ [SemiNestedCompare rank limit false cmp; SemiNestedCase 21] ++
        map SemiNestedVertexMap reads ++ [SemiNestedCase 22])
| NcaSourceStop v rank events cmp a reads ra rv ea ev cmp2 :
    audit_semi_nested_rank enc r v = (rank, events) -> audit_positive_leb rank limit = (false, cmp)
  ->
    audit_map_get enc v parents = (Some a, reads) -> audit_semi_nested_rank enc r a = (ra, ea) ->
    audit_semi_nested_rank enc r v = (rv, ev) -> audit_positive_ltb ra rv = (false, cmp2) ->
    audit_nca_source_walk_run enc r limit parents v v
      (events ++ [SemiNestedCompare rank limit false cmp; SemiNestedCase 21] ++ map
  SemiNestedVertexMap reads ++
        ea ++ ev ++ [SemiNestedCompare ra rv false cmp2; SemiNestedCase 23])
| NcaSourceRecur v rank events cmp a reads ra rv ea ev cmp2 result inner :
    audit_semi_nested_rank enc r v = (rank, events) -> audit_positive_leb rank limit = (false, cmp)
  ->
    audit_map_get enc v parents = (Some a, reads) -> audit_semi_nested_rank enc r a = (ra, ea) ->
    audit_semi_nested_rank enc r v = (rv, ev) -> audit_positive_ltb ra rv = (true, cmp2) ->
    audit_nca_source_walk_run enc r limit parents a result inner ->
    audit_nca_source_walk_run enc r limit parents v result
      (events ++ [SemiNestedCompare rank limit false cmp; SemiNestedCase 21] ++ map
  SemiNestedVertexMap reads ++
        ea ++ ev ++ [SemiNestedCompare ra rv true cmp2; SemiNestedCase 24] ++ inner).

Inductive audit_nca_source_step_run {V E B} (enc : V -> positive * list B) (source : E -> V * list
  B)
    (r : dfs_result V E) (semis : Map.t V V) : Map.t V V -> V -> Map.t V V -> list
  (audit_nca_source_event V E B) -> Prop :=
| NcaSourceRoot m v reads : audit_map_get enc v (tree_edge r) = (None, reads) ->
    audit_nca_source_step_run enc source r semis m v m (map NcaSourceTree reads ++ [NcaSourceCase
  0])
| NcaSourceNode m v edge reads value values limit ranks origin body result walk output writes :
    audit_map_get enc v (tree_edge r) = (Some edge, reads) ->
    audit_map_get enc v semis = (value, values) ->
    audit_semi_nested_rank enc r (match value with Some x => x | None => v end) = (limit, ranks) ->
    source edge = (origin, body) -> audit_nca_source_walk_run enc r limit m origin result walk ->
    audit_map_set enc v result m = (output, writes) ->
    audit_nca_source_step_run enc source r semis m v output
      (map NcaSourceTree reads ++ [NcaSourceCase 1] ++
       map (fun item => NcaSourceInner (SemiNestedVertexMap item)) values ++ map NcaSourceInner
  ranks ++
       [NcaSourceSource edge origin body] ++ map NcaSourceInner walk ++
       map (fun item => NcaSourceInner (SemiNestedVertexMap item)) writes).

Inductive audit_nca_source_steps_run {V E B} (enc : V -> positive * list B) (source : E -> V * list
  B)
    (r : dfs_result V E) (semis : Map.t V V) : list V -> Map.t V V -> Map.t V V -> list
  (audit_nca_source_event V E B) -> Prop :=
| NcaSourceStepsNil m : audit_nca_source_steps_run enc source r semis [] m m [NcaSourceCase 2]
| NcaSourceStepsCons v rest initial middle result here later :
    audit_nca_source_step_run enc source r semis initial v middle here ->
    audit_nca_source_steps_run enc source r semis rest middle result later ->
    audit_nca_source_steps_run enc source r semis (v :: rest) initial result (NcaSourceCase 3 ::
  here ++ later).

Definition audit_nca_source_run {V E B} (enc : V -> positive * list B) (source : E -> V * list B)
    (r : dfs_result V E) (semis : Map.t V V) (result : Map.t V V) (events : list
  (audit_nca_source_event V E B)) : Prop :=
  audit_nca_source_steps_run enc source r semis (preorder r) Map.empty result events.

Definition audit_nca_source_event_work {V E B} (weight : B -> nat) (event : audit_nca_source_event V
  E B) : nat :=
  64 + match event with
  | NcaSourceInner item => audit_semi_nested_event_work weight item
  | NcaSourceTree item => audit_map_source_work (fun es => fold_right (fun x n => weight x + n) 0
  es) [item]
  | NcaSourceSource _ _ es => fold_right (fun x n => weight x + n) 0 es
  | NcaSourceCase _ => 0
  end.

Definition audit_nca_source_event_body {V E B} (weight : B -> nat) (event : audit_nca_source_event V
  E B) : nat :=
  match event with
  | NcaSourceInner item => audit_semi_nested_body_event_work weight item
  | NcaSourceTree (AuditMapGet _ _ _ _ body _) | NcaSourceTree (AuditMapSet _ _ _ _ _ body _) |
    NcaSourceTree (AuditMapRemove _ _ _ _ body _) | NcaSourceSource _ _ body =>
      fold_right (fun x n => weight x + n) 0 body
  | NcaSourceCase _ => 0
  end.

Definition audit_nca_source_work {V E B} (weight : B -> nat) (events : list (audit_nca_source_event
  V E B)) : nat :=
  fold_right (fun item n => audit_nca_source_event_work weight item + n) 0 events.
Definition audit_nca_source_body_work {V E B} (weight : B -> nat) (events : list
  (audit_nca_source_event V E B)) : nat :=
  fold_right (fun item n => audit_nca_source_event_body weight item + n) 0 events.

Definition audit_nca_source_input_bound {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) (semis : Map.t V V) : nat :=
  let rows := Map.elements semis in
  let vertices := preorder r ++ map fst rows ++ map snd rows ++ map fst (Map.elements (tree_edge r))
  ++
    map (Graph.source g) (map snd (Map.elements (tree_edge r))) ++ map fst (Map.elements (pre_num
  r)) in
  let width := Nat.max (fold_right Nat.max 0 (map (fun v => Pos.size_nat (encode EV v)) vertices))
    (fold_right Nat.max 0 (map (fun row => Pos.size_nat (snd row)) (Map.elements (pre_num r)))) in
  let count := 64 * S (length (preorder r)) * S (audit_semi_producer_input_rank r) in
  512 * S count * S count + count * (512 + 64 * width).

Definition audit_nca_source_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E) semis
    (enc : V -> positive * list B) (source : E -> V * list B) (weight : B -> nat),
    (forall v, fst (enc v) = encode EV v) -> (forall e, fst (source e) = Graph.source g e) ->
    exists result events, audit_nca_source_run enc source r semis result events /\ result =
  nca_compute EV g r semis /\
      audit_nca_source_work weight events <= audit_nca_source_input_bound EV g r semis +
  audit_nca_source_body_work weight events.

Definition audit_nca_source_unique_statement : Prop :=
  forall V E B enc source (r : dfs_result V E) semis a ea b eb,
    audit_nca_source_run (B := B) enc source r semis a ea -> audit_nca_source_run enc source r semis
  b eb ->
    a = b /\ ea = eb.
```

## Galois.Graph.GraphAuditDominators

Card: AUD-GR-MODELS

Source destination: `theories/Graph/GraphAuditDominators.v`.

```rocq
From Stdlib Require Import List Bool PArith ZArith.
From Galois.Collections Require Import CollectionsAuditCost CollectionsEncoding CollectionsMap
  CollectionsTrie CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphDominance GraphDominators
  GraphSemiDominators GraphLengauerTarjan.
Import List.ListNotations.
From Galois.Graph Require Import GraphAuditBase GraphAuditDfs GraphAuditVirtual
  GraphAuditSemiDominators GraphAuditLengauerTarjan.

Record audit_lt_backend_trace (V E : Type) : Type := AuditLtBackendTrace {
  audit_lt_backend_prepare : list (audit_prepare_nested_event (V + unit) (E + V) (audit_virtual_call
  V E));
  audit_lt_backend_dfs : list (audit_dfs_nested_event (V + unit) (E + V) (audit_virtual_call V E));
  audit_lt_backend_semi : list (audit_semi_outer_call (V + unit) (E + V));
  audit_lt_backend_core : list (audit_lt_call (V + unit) (E + V));
  audit_lt_backend_erase : list (audit_erase_call V)
}.
Arguments AuditLtBackendTrace {V E} _ _ _ _ _.
Arguments audit_lt_backend_prepare {V E} _.
Arguments audit_lt_backend_dfs {V E} _.
Arguments audit_lt_backend_semi {V E} _.
Arguments audit_lt_backend_core {V E} _.
Arguments audit_lt_backend_erase {V E} _.

Definition audit_lt_backend_run {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (result : Map.t V V) (trace : audit_lt_backend_trace V E) : Prop :=
  let '(vp, (r, (prepare_events, dfs_events))) := audit_virtual_search_with_prepared EV g in
  exists state semi_events virtual_parents lt_events,
    audit_semi_compute_run vp r state semi_events /\
    audit_lt_compute_run (virtual_encoding EV) (virtual_graph EV g) r (SemiState.result state)
  virtual_parents lt_events /\
    let '(output, erase_events) := audit_erase_virtual_counted EV virtual_parents in
    result = output /\ trace = AuditLtBackendTrace prepare_events dfs_events semi_events lt_events
  erase_events.

Definition audit_lt_backend_selected_work {V E} (EV : encoding V) (trace : audit_lt_backend_trace V
  E) : nat :=
  audit_graph_prepare_nested_total_work (audit_virtual_event_work EV) (audit_lt_backend_prepare
  trace) +
  audit_dfs_nested_total_work (virtual_encoding EV) (audit_virtual_event_work EV)
  (audit_lt_backend_dfs trace) +
  audit_semi_compute_work (virtual_encoding EV) (audit_lt_backend_semi trace) +
  audit_lt_model_work (virtual_encoding EV) (audit_lt_backend_core trace) +
  audit_erase_virtual_work EV (audit_lt_backend_erase trace).

Definition audit_lt_backend_erasure_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g),
    exists result trace, audit_lt_backend_run p result trace /\ result = simple_lt_idom p.

Inductive audit_dom_body (V : Type) : Type :=
| AuditDomBodyRead (v : V) (m : Map.t V (list V)) (result : option (list V))
| AuditDomBodyTarget (v : V)
| AuditDomBodyEncode (v : V) (code : positive).
Arguments AuditDomBodyRead {V} _ _ _.
Arguments AuditDomBodyTarget {V} _.
Arguments AuditDomBodyEncode {V} _ _.

Inductive audit_dom_call (V E : Type) : Type :=
| AuditDomInitialDfs (event : audit_dfs_full_call V E)
| AuditDomCase (site : nat)
| AuditDomElements (input : Map.t V V) (rows : list (V * V))
| AuditDomChildRead (v : V) (m : Map.t V (list V)) (result : option (list V))
| AuditDomChildSet (v : V) (row : list V) (m : Map.t V (list V))
| AuditDomRootGet (v : V) (m : Map.t V V) (result : option V)
| AuditDomPrepare (event : audit_prepare_nested_event V V (audit_dom_body V))
| AuditDomDfs (event : audit_dfs_nested_event V V (audit_dom_body V))
| AuditDomOutput (size : nat).
Arguments AuditDomInitialDfs {V E} _.
Arguments AuditDomCase {V E} _.
Arguments AuditDomElements {V E} _ _.
Arguments AuditDomChildRead {V E} _ _ _.
Arguments AuditDomChildSet {V E} _ _ _.
Arguments AuditDomRootGet {V E} _ _ _.
Arguments AuditDomPrepare {V E} _.
Arguments AuditDomDfs {V E} _.
Arguments AuditDomOutput {V E} _.

Fixpoint audit_dom_children_counted {V E} (EV : encoding V) (bindings : list (V * V))
    : Map.t V (list V) * list (audit_dom_call V E) :=
  match bindings with
  | [] => (Map.empty, [AuditDomCase 0])
  | (v, u) :: rest => let '(children, events) := audit_dom_children_counted EV rest in
      let found := Map.get EV u children in
      let row := match found with Some xs => xs | None => [] end in
      (Map.set EV u (v :: row) children,
       AuditDomCase 1 :: events ++ [AuditDomChildRead u children found; AuditDomChildSet u (v ::
  row) children])
  end.

Fixpoint audit_dom_roots_counted {V E} (EV : encoding V) (m : Map.t V V) (live : list V)
    : list V * list (audit_dom_call V E) :=
  match live with
  | [] => ([], [AuditDomCase 2])
  | v :: rest => let found := Map.get EV v m in
      let '(later, events) := audit_dom_roots_counted EV m rest in
      (match found with None => v :: later | Some _ => later end,
       AuditDomCase 3 :: AuditDomRootGet v m found :: events)
  end.

Definition audit_dom_out_counted {V} (EV : encoding V) (children : Map.t V (list V)) (v : V)
    : list V * list (audit_dom_body V) :=
  let found := Map.get EV v children in
  (match found with Some xs => xs | None => [] end, [AuditDomBodyRead v children found]).

Definition audit_dom_target_counted {V} (v : V) : V * list (audit_dom_body V) :=
  (v, [AuditDomBodyTarget v]).

Definition audit_dom_encode_counted {V} (EV : encoding V) (v : V) : positive * list (audit_dom_body
  V) :=
  let code := encode EV v in (code, [AuditDomBodyEncode v code]).

Definition audit_dom_prepare_callbacks {V} (EV : encoding V) (children : Map.t V (list V))
    : audit_prepare_callback_model V V (audit_dom_body V) :=
  AuditPrepareCallbackModel _ _ _ (audit_dom_out_counted EV children)
    audit_dom_target_counted (audit_dom_encode_counted EV).

Definition audit_dom_dfs_callbacks {V} (EV : encoding V) : audit_dfs_callback_model V V
  (audit_dom_body V) :=
  AuditDfsCallbackModel _ _ _ audit_dom_target_counted (audit_dom_encode_counted EV).

Definition audit_dom_tree_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (parents : Map.t V V) : dom_tree V * list (audit_dom_call V E) :=
  let '(search, first_events) := audit_dfs_full_counted p FinSet.empty (Graph.entries g) in
  let live := preorder search in
  let rows := Map.elements parents in
  let '(children, child_events) := audit_dom_children_counted EV rows in
  let '(roots, root_events) := audit_dom_roots_counted EV parents live in
  let forest := Graph.Make roots live (fun v => index_edges EV children v)
    (fun v => match Map.get EV v parents with Some u => u | None => v end) (fun v => v) in
  let '(fp, prep_events) := audit_graph_prepare_nested_counted EV forest
  (audit_dom_prepare_callbacks EV children) in
  let '(result, dfs_events) := audit_dfs_nested_counted fp (audit_dom_dfs_callbacks EV) FinSet.empty
  roots in
  (DomTree parents (pre_num result) (post_num result),
   map AuditDomInitialDfs first_events ++ [AuditDomElements parents rows] ++ child_events ++
  root_events ++
     map AuditDomPrepare prep_events ++ map AuditDomDfs dfs_events ++ [AuditDomOutput (length
  live)]).

Definition audit_dom_body_work {V} (EV : encoding V) (event : audit_dom_body V) : nat :=
  64 + match event with
  | AuditDomBodyRead v _ _ => audit_encoding_weight (audit_key_bits_weight (encode EV v)) +
  audit_get_weight (encode EV v)
  | AuditDomBodyEncode _ code => audit_encoding_weight (audit_key_bits_weight code)
  | AuditDomBodyTarget _ => 0 end.

Definition audit_dom_event_work {V E} (EV : encoding V) (event : audit_dom_call V E) : nat :=
  64 + match event with
  | AuditDomInitialDfs item => audit_dfs_full_model_event EV item
  | AuditDomElements input _ => 64 * Nat.pow (S (audit_erase_nodes input)) 3
  | AuditDomChildRead v _ _ | AuditDomRootGet v _ _ =>
      audit_encoding_weight (audit_key_bits_weight (encode EV v)) + audit_get_weight (encode EV v)
  | AuditDomChildSet v _ _ => audit_encoding_weight (audit_key_bits_weight (encode EV v)) +
  audit_set_weight (encode EV v)
  | AuditDomPrepare (outer, body) => audit_graph_full_event_work outer +
      fold_right (fun item n => audit_dom_body_work EV item + n) 0 body
  | AuditDomDfs (outer, body) => audit_dfs_full_model_event EV outer +
      fold_right (fun item n => audit_dom_body_work EV item + n) 0 body
  | AuditDomOutput size => S size
  | AuditDomCase _ => 0 end.

Definition audit_dom_model_work {V E} (EV : encoding V) (events : list (audit_dom_call V E)) : nat
  :=
  1024 * S (length events) * S (length events) +
    fold_right (fun event total => audit_dom_event_work EV event + total) 0 events.

Definition audit_dom_input_scale {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (parents : Map.t V V) : nat :=
  1 + length (Graph.entries g) * S (Pos.to_nat (fuel p)) + audit_erase_nodes parents.

Definition audit_dom_input_event_bound {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (parents : Map.t V V) : nat :=
  1024 * Nat.pow (S (audit_dom_input_scale p parents)) 8.

Definition audit_dom_input_width {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (parents : Map.t V V) : nat :=
  let rows := Map.elements parents in
  Nat.max (audit_dfs_full_input_width EV g p (Graph.entries g))
    (fold_right Nat.max 0 (map (fun v => audit_key_bits_weight (encode EV v)) (map fst rows ++ map
  snd rows))).

Definition audit_dom_input_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (parents : Map.t V V) : nat :=
  let count := audit_dom_input_event_bound p parents in
  let width := Nat.max (audit_dom_input_width EV g p parents)
    (audit_key_bits_weight (Pos.of_succ_nat (S count))) in
  8192 * Nat.pow (S count) 3 * Nat.pow (S width) 2.

Definition audit_dom_tree_counted_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) parents,
    let '(result, events) := audit_dom_tree_counted p parents in
    result = dom_tree_of p parents /\ length events <= audit_dom_input_event_bound p parents /\
    audit_dom_model_work EV events <= audit_dom_input_budget EV g p parents.



From Galois.Collections Require Import CollectionsAuditMap CollectionsAuditElements.
Inductive audit_dom_source_body (V B : Type) : Type :=
| DomSourceBodyMap : audit_map_event V (list V) B -> audit_dom_source_body V B
| DomSourceBodyTarget : V -> audit_dom_source_body V B
| DomSourceBodyEncode : V -> positive -> list B -> audit_dom_source_body V B.
Arguments DomSourceBodyMap {V B} _.
Arguments DomSourceBodyTarget {V B} _.
Arguments DomSourceBodyEncode {V B} _ _ _.

Inductive audit_dom_source_event (V E B : Type) : Type :=
| DomSourceCase : nat -> audit_dom_source_event V E B
| DomSourceInitialDfs : audit_dfs_nested_event V E (audit_graph_callback_capture V E B) ->
  audit_dom_source_event V E B
| DomSourceElements : audit_elements_event (V * V) -> audit_dom_source_event V E B
| DomSourceChild : audit_map_event V (list V) B -> audit_dom_source_event V E B
| DomSourceParent : audit_map_event V V B -> audit_dom_source_event V E B
| DomSourcePrepare : audit_prepare_source_event V V (audit_dom_source_body V B) ->
  audit_dom_source_event V E B
| DomSourceDfs : audit_dfs_nested_event V V (audit_graph_callback_capture V V (audit_dom_source_body
  V B)) -> audit_dom_source_event V E B.
Arguments DomSourceCase {V E B} _.
Arguments DomSourceInitialDfs {V E B} _.
Arguments DomSourceElements {V E B} _.
Arguments DomSourceChild {V E B} _.
Arguments DomSourceParent {V E B} _.
Arguments DomSourcePrepare {V E B} _.
Arguments DomSourceDfs {V E B} _.

Fixpoint audit_dom_source_children {V E B} (enc : V -> positive * list B) (rows : list (V * V))
    : Map.t V (list V) * list (audit_dom_source_event V E B) :=
  match rows with
  | [] => (Map.empty, [DomSourceCase 0])
  | (v, u) :: rest => let '(children, events) := audit_dom_source_children enc rest in
      let '(found, reads) := audit_map_get enc u children in
      let row := match found with Some xs => xs | None => [] end in
      let '(next, writes) := audit_map_set enc u (v :: row) children in
      (next, DomSourceCase 1 :: events ++ map DomSourceChild reads ++ map DomSourceChild writes)
  end.

Fixpoint audit_dom_source_roots {V E B} (enc : V -> positive * list B) (parents : Map.t V V)
  (vertices : list V)
    : list V * list (audit_dom_source_event V E B) :=
  match vertices with
  | [] => ([], [DomSourceCase 2])
  | v :: rest => let '(found, reads) := audit_map_get enc v parents in
      let '(later, events) := audit_dom_source_roots enc parents rest in
      (match found with None => v :: later | Some _ => later end,
        DomSourceCase 3 :: map DomSourceParent reads ++ events)
  end.

Definition audit_dom_source_out {V B} (enc : V -> positive * list B) (children : Map.t V (list V))
  (v : V)
    : list V * list (audit_dom_source_body V B) :=
  let '(found, reads) := audit_map_get enc v children in
  (match found with Some xs => xs | None => [] end, map DomSourceBodyMap reads).

Definition audit_dom_source_target {V B} (v : V) : V * list (audit_dom_source_body V B) :=
  (v, [DomSourceBodyTarget v]).

Definition audit_dom_source_encode {V B} (enc : V -> positive * list B) (v : V)
    : positive * list (audit_dom_source_body V B) :=
  let '(code, body) := enc v in (code, [DomSourceBodyEncode v code body]).

Record audit_dom_source_receipt (V E B : Type) (EV : encoding V) : Type := AuditDomSourceReceipt {
  audit_dom_source_forest : Graph.t V V;
  audit_dom_source_index : prepared EV audit_dom_source_forest;
  audit_dom_source_result : dfs_result V V;
  audit_dom_source_events : list (audit_dom_source_event V E B)
}.
Arguments AuditDomSourceReceipt {V E B EV} _ _ _ _.
Arguments audit_dom_source_forest {V E B EV} _.
Arguments audit_dom_source_index {V E B EV} _.
Arguments audit_dom_source_result {V E B EV} _.
Arguments audit_dom_source_events {V E B EV} _.

Definition audit_dom_search_source_counted {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (parents : Map.t V V) (cb : audit_dfs_callback_model V E B)
    : audit_dom_source_receipt V E B EV :=
  let '(search, search_events) := audit_dfs_source_counted p cb FinSet.empty (Graph.entries g) in
  let vertices := preorder search in let '(rows, element_events) := audit_map_elements parents in
  let '(children, child_events) := audit_dom_source_children (audit_dfs_encode_model cb) rows in
  let '(roots, root_events) := audit_dom_source_roots (audit_dfs_encode_model cb) parents vertices
  in
  let forest := Graph.Make roots vertices (fun v => index_edges EV children v)
    (fun v => match Map.get EV v parents with Some u => u | None => v end) (fun v => v) in
  let prepare_cb := AuditPrepareCallbackModel V V (audit_dom_source_body V B)
    (audit_dom_source_out (audit_dfs_encode_model cb) children) audit_dom_source_target
    (audit_dom_source_encode (audit_dfs_encode_model cb)) in
  let dfs_cb := AuditDfsCallbackModel V V (audit_dom_source_body V B) audit_dom_source_target
    (audit_dom_source_encode (audit_dfs_encode_model cb)) in
  let '(fp, prepare_events) := audit_prepare_source_counted EV forest prepare_cb in
  let '(result, dfs_events) := audit_dfs_source_counted fp dfs_cb FinSet.empty roots in
  AuditDomSourceReceipt forest fp result
    (map DomSourceInitialDfs search_events ++ map DomSourceElements element_events ++ child_events
  ++ root_events ++
     map DomSourcePrepare prepare_events ++ map DomSourceDfs dfs_events).

Definition audit_dom_source_body_work {V B} (weight : B -> nat) (event : audit_dom_source_body V B)
  : nat :=
  64 + match event with
  | DomSourceBodyMap item => audit_map_source_work (fun es => fold_right (fun x n => weight x + n) 0
  es) [item]
  | DomSourceBodyEncode _ _ es => fold_right (fun x n => weight x + n) 0 es
  | DomSourceBodyTarget _ => 0
  end.

Definition audit_dom_source_body_external {V B} (weight : B -> nat) (event : audit_dom_source_body V
  B) : nat :=
  match event with
  | DomSourceBodyMap (AuditMapGet _ _ _ _ es _) | DomSourceBodyMap (AuditMapSet _ _ _ _ _ es _) |
    DomSourceBodyMap (AuditMapRemove _ _ _ _ es _) | DomSourceBodyEncode _ _ es =>
      fold_right (fun x n => weight x + n) 0 es
  | DomSourceBodyTarget _ => 0
  end.

Definition audit_dom_source_event_work {V E B} (weight : B -> nat) (event : audit_dom_source_event V
  E B) : nat :=
  let body := fun es => fold_right (fun x n => weight x + n) 0 es in
  64 + match event with
  | DomSourceInitialDfs item => audit_dfs_source_event_work weight item
  | DomSourceElements item => audit_elements_frame_work item
  | DomSourceChild item => audit_map_source_work body [item]
  | DomSourceParent item => audit_map_source_work body [item]
  | DomSourcePrepare item => audit_prepare_source_event_work (audit_dom_source_body_work weight)
  item
  | DomSourceDfs item => audit_dfs_source_event_work (audit_dom_source_body_work weight) item
  | DomSourceCase _ => 0
  end.

Definition audit_dom_source_event_external {V E B} (weight : B -> nat) (event :
  audit_dom_source_event V E B) : nat :=
  match event with
  | DomSourceInitialDfs item => audit_dfs_source_body_work weight [item]
  | DomSourceChild (AuditMapGet _ _ _ _ es _) | DomSourceChild (AuditMapSet _ _ _ _ _ es _) |
    DomSourceChild (AuditMapRemove _ _ _ _ es _) | DomSourceParent (AuditMapGet _ _ _ _ es _) |
    DomSourceParent (AuditMapSet _ _ _ _ _ es _) | DomSourceParent (AuditMapRemove _ _ _ _ es _) =>
      fold_right (fun x n => weight x + n) 0 es
  | DomSourcePrepare item => audit_prepare_source_body_work (audit_dom_source_body_external weight)
  [item]
  | DomSourceDfs item => audit_dfs_source_body_work (audit_dom_source_body_external weight) [item]
  | DomSourceCase _ | DomSourceElements _ => 0
  end.

Definition audit_dom_source_work {V E B} (weight : B -> nat) (events : list (audit_dom_source_event
  V E B)) : nat :=
  fold_right (fun item n => audit_dom_source_event_work weight item + n) 0 events.
Definition audit_dom_source_external_work {V E B} (weight : B -> nat) (events : list
  (audit_dom_source_event V E B)) : nat :=
  fold_right (fun item n => audit_dom_source_event_external weight item + n) 0 events.

Definition audit_dom_search_source_budget {V E B} (EV : encoding V) (g : Graph.t V E) (p : prepared
  EV g)
    (parents : Map.t V V) (receipt : audit_dom_source_receipt V E B EV) : nat :=
  let forest := audit_dom_source_forest receipt in let fp := audit_dom_source_index receipt in
  let size := S (audit_trie_nodes parents + length (Graph.nodes forest) + length (Graph.entries
  forest) +
    Pos.to_nat (fuel p) + Pos.to_nat (fuel fp)) in
  let width := audit_dfs_full_input_width EV g p (Graph.entries g) +
    audit_graph_prepare_input_width EV forest + audit_dfs_full_input_width EV forest fp
  (Graph.entries forest) +
    fold_right Nat.max 0 (map (fun row => Nat.max (Pos.size_nat (encode EV (fst row)))
      (Pos.size_nat (encode EV (snd row)))) (Map.elements parents)) in
  audit_dfs_source_budget EV g p (Graph.entries g) + audit_prepare_source_budget EV forest +
    audit_dfs_source_budget EV forest fp (Graph.entries forest) + 1048576 * Nat.pow size 8 * S width
  * S width.

Definition audit_dom_search_source_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) parents
    (cb : audit_dfs_callback_model V E B) (weight : B -> nat),
    audit_dfs_callbacks_erase EV g cb ->
    let receipt := audit_dom_search_source_counted p parents cb in
    audit_dom_source_result receipt = dom_search p parents /\
    audit_dom_source_work weight (audit_dom_source_events receipt) <= audit_dom_search_source_budget
  EV g p parents receipt +
      audit_dom_source_external_work weight (audit_dom_source_events receipt).
From Galois.Graph Require Import GraphAuditVirtual GraphAuditSemiDominators
  GraphAuditLengauerTarjan.
Definition audit_default_dom_single_run_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (cb : audit_virtual_base_callbacks V E B) (source : E -> V * list B) (weight : B -> nat),
    audit_virtual_base_callbacks_erase EV g cb -> (forall edge, fst (source edge) = Graph.source g
  edge) ->
    exists vp search prepare_events dfs_events semi_state semi_events virtual_parents lt_events
      parents erase_events receipt result,
      audit_virtual_source_search EV g cb = (vp, (search, (prepare_events, dfs_events))) /\
      audit_semi_producer_nested_run (audit_virtual_full_encode cb) (audit_virtual_full_source
  source)
        vp search semi_state semi_events /\
      audit_lt_nested_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
        search (SemiState.result semi_state) virtual_parents lt_events /\
      audit_erase_virtual_nested (audit_virtual_base_encode cb) virtual_parents = (parents,
  erase_events) /\
      receipt = audit_dom_search_source_counted p parents
        (AuditDfsCallbackModel V E B (audit_virtual_base_target cb) (audit_virtual_base_encode cb))
  /\
      result = DomTree parents (pre_num (audit_dom_source_result receipt)) (post_num
  (audit_dom_source_result receipt)) /\
      result = dominator_tree p /\
      audit_prepare_source_work
        (fun event => audit_virtual_full_internal_event_work event +
  audit_virtual_full_body_event_work weight event)
        prepare_events +
      audit_dfs_source_work
        (fun event => audit_virtual_full_internal_event_work event +
  audit_virtual_full_body_event_work weight event)
        dfs_events + audit_virtual_semi_stage_work weight semi_events + audit_virtual_lt_stage_work
  weight lt_events +
      audit_erase_nested_work weight erase_events + audit_dom_source_work weight
  (audit_dom_source_events receipt) <=
        audit_virtual_lt_input_budget EV g + audit_dom_search_source_budget EV g p parents receipt +
      audit_prepare_source_body_work (audit_virtual_full_body_event_work weight) prepare_events +
      audit_dfs_source_body_work (audit_virtual_full_body_event_work weight) dfs_events +
      audit_virtual_semi_external_work weight semi_events + audit_virtual_lt_external_work weight
  lt_events +
      audit_erase_nested_body_work weight erase_events + audit_dom_source_external_work weight
  (audit_dom_source_events receipt).
```

## Galois.Graph.GraphAuditDominatorsAdapter

Card: AUD-GR-MODELS

Source destination: `theories/Graph/GraphAuditDominatorsAdapter.v`.

```rocq
(** * Default dominator source adapters

    The default LT path charges the callbacks in one virtual-search receipt.
    For example, the forest search reuses the parent map produced by that same run.
    Builds on: virtual, LT and dominator source models. *)
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsAuditMap
  CollectionsAuditFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphDominance GraphSemiDominators
  GraphDominators
  GraphAuditBase GraphAuditDfs GraphAuditVirtual GraphAuditSemiDominators GraphAuditLengauerTarjan
  GraphAuditDominators.
Import List.ListNotations.

(** Virtual events identify the actual supplied operation and argument. *)
Definition audit_default_virtual_event_budget {V E B} (encode_budget out_budget : V -> nat)
    (target_budget source_budget : E -> nat) (event : audit_virtual_full_call V E B) : nat :=
  match event with
  | VirtualFullOut v _ _ => out_budget v
  | VirtualFullTarget e _ _ => target_budget e
  | VirtualFullSource e _ _ => source_budget e
  | VirtualFullEncode v _ _ => encode_budget v
  | VirtualFullEntry (VirtualEntriesSet (AuditSetAdd v _ _ _ _ _)) |
    VirtualFullEntry (VirtualEntriesSet (AuditSetMem v _ _ _ _ _)) |
    VirtualFullEntry (VirtualEntriesSet (AuditSetRemove v _ _ _ _ _)) => encode_budget v
  | _ => 0
  end.

Definition audit_default_erase_event_budget {V B} (encode_budget : V -> nat)
    (event : audit_erase_nested_event V B) : nat :=
  match event with
  | EraseNestedSet (AuditMapGet v _ _ _ _ _) | EraseNestedSet (AuditMapSet v _ _ _ _ _ _) |
    EraseNestedSet (AuditMapRemove v _ _ _ _ _) => encode_budget v
  | _ => 0
  end.

Definition audit_default_forest_body_budget {V B} (encode_budget : V -> nat)
    (event : audit_dom_source_body V B) : nat :=
  match event with
  | DomSourceBodyMap (AuditMapGet v _ _ _ _ _) | DomSourceBodyMap (AuditMapSet v _ _ _ _ _ _) |
    DomSourceBodyMap (AuditMapRemove v _ _ _ _ _) | DomSourceBodyEncode v _ _ => encode_budget v
  | DomSourceBodyTarget _ => 0
  end.

Definition audit_default_dom_event_budget {V E B} (encode_budget : V -> nat) (target_budget : E ->
  nat)
    (event : audit_dom_source_event V E B) : nat :=
  match event with
  | DomSourceInitialDfs (_, calls) => fold_right (fun call n => match call with
      | AuditGraphEncodeCapture _ _ _ v _ _ => encode_budget v + n
      | AuditGraphTargetCapture _ _ _ e _ _ => target_budget e + n end) 0 calls
  | DomSourceChild (AuditMapGet v _ _ _ _ _) | DomSourceChild (AuditMapSet v _ _ _ _ _ _) |
    DomSourceChild (AuditMapRemove v _ _ _ _ _) | DomSourceParent (AuditMapGet v _ _ _ _ _) |
    DomSourceParent (AuditMapSet v _ _ _ _ _ _) | DomSourceParent (AuditMapRemove v _ _ _ _ _) =>
  encode_budget v
  | DomSourcePrepare call => audit_prepare_source_body_work (audit_default_forest_body_budget
  encode_budget) [call]
  | DomSourceDfs call => audit_dfs_source_body_work (audit_default_forest_body_budget encode_budget)
  [call]
  | _ => 0
  end.

(** The original-input budget covers virtual LT and the finite forest producer. *)
Definition audit_default_dom_input_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) : nat :=
  let edges := flat_map (Graph.out g) (Graph.nodes g) in
  let vertices := Graph.nodes g ++ Graph.entries g ++ map (Graph.source g) edges ++ map
  (Graph.target g) edges in
  let width := fold_right Nat.max 0 (map (fun v => Pos.size_nat (encode EV v)) vertices) in
  let scale := S (4 + length vertices + length edges + width + Pos.to_nat (fuel p) +
    audit_dfs_full_input_width EV g p (Graph.entries g) + audit_dfs_source_budget EV g p
  (Graph.entries g)) in
  1048576 * Nat.pow scale 64.

(** The default producer binds one virtual receipt and budgets each actual callback. *)
Definition audit_default_dom_single_adapted_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (cb : audit_virtual_base_callbacks V E B) (source : E -> V * list B) (weight : B -> nat)
    encode_source out_source target_source source_source encode_budget out_budget target_budget
  source_budget,
    audit_virtual_base_callbacks_erase EV g cb -> (forall edge, fst (source edge) = Graph.source g
  edge) ->
    audit_graph_external_callback_adapter (audit_virtual_base_encode cb) weight encode_source
  encode_budget ->
    audit_graph_external_callback_adapter (audit_virtual_base_out cb) weight out_source out_budget
  ->
    audit_graph_external_callback_adapter (audit_virtual_base_target cb) weight target_source
  target_budget ->
    audit_graph_external_callback_adapter source weight source_source source_budget ->
    exists vp search prepare_events dfs_events semi_state semi_events virtual_parents lt_events
      parents erase_events receipt result,
      audit_virtual_source_search EV g cb = (vp, (search, (prepare_events, dfs_events))) /\
      audit_semi_producer_nested_run (audit_virtual_full_encode cb) (audit_virtual_full_source
  source)
        vp search semi_state semi_events /\
      audit_lt_nested_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
        search (SemiState.result semi_state) virtual_parents lt_events /\
      audit_erase_virtual_nested (audit_virtual_base_encode cb) virtual_parents = (parents,
  erase_events) /\
      receipt = audit_dom_search_source_counted p parents
        (AuditDfsCallbackModel V E B (audit_virtual_base_target cb) (audit_virtual_base_encode cb))
  /\
      result = DomTree parents (pre_num (audit_dom_source_result receipt))
        (post_num (audit_dom_source_result receipt)) /\ result = dominator_tree p /\
      let work := audit_prepare_source_work
        (fun event => audit_virtual_full_internal_event_work event +
  audit_virtual_full_body_event_work weight event)
        prepare_events + audit_dfs_source_work
        (fun event => audit_virtual_full_internal_event_work event +
  audit_virtual_full_body_event_work weight event)
        dfs_events + audit_virtual_semi_stage_work weight semi_events + audit_virtual_lt_stage_work
  weight lt_events +
        audit_erase_nested_work weight erase_events + audit_dom_source_work weight
  (audit_dom_source_events receipt) in
      let virtual_budget := audit_default_virtual_event_budget encode_budget out_budget
  target_budget source_budget in
      let external := audit_prepare_source_body_work virtual_budget prepare_events +
        audit_dfs_source_body_work virtual_budget dfs_events +
        audit_semi_producer_nested_body_work virtual_budget semi_events + audit_lt_nested_body_work
  virtual_budget lt_events +
        fold_right (fun e n => audit_default_erase_event_budget encode_budget e + n) 0 erase_events
  +
        fold_right (fun e n => audit_default_dom_event_budget encode_budget target_budget e + n) 0
          (audit_dom_source_events receipt) in
      work <= audit_default_dom_input_budget EV g p + external /\
      work <= audit_virtual_lt_input_budget EV g + audit_dom_search_source_budget EV g p parents
  receipt + external.
```

## Galois.Graph.GraphAuditDominatorSelect

Card: AUD-GR-MODELS

Source destination: `theories/Graph/GraphAuditDominatorSelect.v`.

```rocq
(** * Selectable dominator source contracts

    The selector records one virtual search, the chosen backend, checks and fallback.
    For example, a missing interval stops the checker before later map reads.
    Builds on: dominator, semidominator, Semi-NCA and collection source models. *)
From Stdlib Require Import List Bool PArith NArith ZArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet
  CollectionsAuditCost CollectionsAuditTrie CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements
  CollectionsAuditPrimitive CollectionsAuditCompare CollectionsAuditUnion
  CollectionsAuditMapTraverse
  CollectionsAuditEncoding.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphScc GraphDominance
  GraphDominators GraphSemiDominators
  GraphSemiNca GraphAuditBase GraphAuditDfs GraphAuditScc GraphAuditVirtual GraphAuditSemiDominators
  GraphAuditLengauerTarjan GraphAuditSemiNca GraphAuditDominators.
Import List.ListNotations.
Record audit_nca_backend_trace (V E : Type) : Type := AuditNcaBackendTrace {
  audit_nca_backend_prepare : list (audit_prepare_nested_event (V + unit) (E + V)
  (audit_virtual_call V E));
  audit_nca_backend_dfs : list (audit_dfs_nested_event (V + unit) (E + V) (audit_virtual_call V E));
  audit_nca_backend_semi : list (audit_semi_outer_call (V + unit) (E + V));
  audit_nca_backend_core : list (audit_nca_call (V + unit) (E + V));
  audit_nca_backend_erase : list (audit_erase_call V)
}.
Arguments AuditNcaBackendTrace {V E} _ _ _ _ _.
Arguments audit_nca_backend_prepare {V E} _.
Arguments audit_nca_backend_dfs {V E} _.
Arguments audit_nca_backend_semi {V E} _.
Arguments audit_nca_backend_core {V E} _.
Arguments audit_nca_backend_erase {V E} _.

Definition audit_nca_backend_run {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (result : Map.t V V) (trace : audit_nca_backend_trace V E) : Prop :=
  let '(vp, (r, (prepare_events, dfs_events))) := audit_virtual_search_with_prepared EV g in
  exists state semi_events virtual_parents nca_events,
    audit_semi_compute_run vp r state semi_events /\
    audit_nca_compute_run (virtual_encoding EV) (virtual_graph EV g) r (SemiState.result state)
  virtual_parents nca_events /\
    let '(output, erase_events) := audit_erase_virtual_counted EV virtual_parents in
    result = output /\ trace = AuditNcaBackendTrace prepare_events dfs_events semi_events nca_events
  erase_events.

Definition audit_nca_backend_selected_work {V E} (EV : encoding V) (trace : audit_nca_backend_trace
  V E) : nat :=
  audit_graph_prepare_nested_total_work (audit_virtual_event_work EV) (audit_nca_backend_prepare
  trace) +
  audit_dfs_nested_total_work (virtual_encoding EV) (audit_virtual_event_work EV)
  (audit_nca_backend_dfs trace) +
  audit_semi_compute_work (virtual_encoding EV) (audit_nca_backend_semi trace) +
  audit_nca_compute_work (virtual_encoding EV) (audit_nca_backend_core trace) +
  audit_erase_virtual_work EV (audit_nca_backend_erase trace).

Definition audit_nca_backend_erasure_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g),
    exists result trace, audit_nca_backend_run p result trace /\ result = semi_nca_idom p.

From Galois.Graph Require Import GraphDominators.

Inductive audit_dom_backend_trace (V E : Type) : Type :=
| AuditDomLtTrace (backend : audit_lt_backend_trace V E) (tree : list (audit_dom_call V E))
| AuditDomNcaTrace (backend : audit_nca_backend_trace V E) (tree : list (audit_dom_call V E)).
Arguments AuditDomLtTrace {V E} _ _.
Arguments AuditDomNcaTrace {V E} _ _.

Inductive audit_dom_tree_with_run {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) : dom_algorithm -> dom_tree V -> audit_dom_backend_trace V E -> Prop :=
| AuditDomWithLt parents backend tree tree_events :
    audit_lt_backend_run p parents backend -> audit_dom_tree_counted p parents = (tree, tree_events)
  ->
    audit_dom_tree_with_run p SimpleLT tree (AuditDomLtTrace backend tree_events)
| AuditDomWithNca parents backend tree tree_events :
    audit_nca_backend_run p parents backend -> audit_dom_tree_counted p parents = (tree,
  tree_events) ->
    audit_dom_tree_with_run p SemiNCA tree (AuditDomNcaTrace backend tree_events).

Definition audit_dom_tree_with_erasure_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) algorithm,
    exists result trace, audit_dom_tree_with_run p algorithm result trace /\
      result = dominator_tree_with p algorithm.

Definition audit_dom_tree_default_erasure_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g),
    exists result trace, audit_dom_tree_with_run p SimpleLT result trace /\ result = dominator_tree
  p.

(** A comparison retains both encoder calls and the positive equality trace. *)
Inductive audit_flat_source_event (V E B : Type) : Type :=
  | FlatSourceCase : nat -> audit_flat_source_event V E B
  | FlatSourceCompare : V -> V -> positive -> positive -> list B -> list B -> bool ->
      list audit_positive_eqb_event -> audit_flat_source_event V E B
  | FlatSourceDfs : audit_dfs_nested_event V E (audit_graph_callback_capture V E B) ->
      audit_flat_source_event V E B
  | FlatSourceMap : audit_map_event V V B -> audit_flat_source_event V E B.
Arguments FlatSourceCase {V E B} _.
Arguments FlatSourceCompare {V E B} _ _ _ _ _ _ _ _.
Arguments FlatSourceDfs {V E B} _.
Arguments FlatSourceMap {V E B} _.

(** The comparison evaluates both actual encoding calls before equality. *)
Definition audit_flat_source_compare {V E B} (enc : V -> positive * list B) (v s : V)
    : bool * list (audit_flat_source_event V E B) :=
  let '(a, ea) := enc v in
  let '(b, eb) := enc s in
  let '(same, trace) := audit_positive_eqb a b in
  (same, [FlatSourceCompare v s a b ea eb same trace]).

(** The strict entry scan evaluates every occurrence, including after a false result. *)
Fixpoint audit_flat_source_entries {V E B} (enc : V -> positive * list B)
    (s : V) (entries : list V) : bool * list (audit_flat_source_event V E B) :=
  match entries with
  | [] => (true, [FlatSourceCase 0])
  | v :: rest =>
      let '(same, here) := audit_flat_source_compare enc v s in
      let '(later, events) := audit_flat_source_entries enc s rest in
      (same && later, FlatSourceCase 1 :: here ++ events)
  end.

(** The forward fold retains the actual intermediate map at every node. *)
Fixpoint audit_flat_source_fold {V E B} (enc : V -> positive * list B) (s : V)
    (vertices : list V) (parents : Map.t V V) : Map.t V V * list (audit_flat_source_event V E B) :=
  match vertices with
  | [] => (parents, [FlatSourceCase 2])
  | v :: rest =>
      let '(same, compares) := audit_flat_source_compare enc v s in
      let '(next, writes) := if same then (parents, []) else audit_map_set enc v s parents in
      let '(result, events) := audit_flat_source_fold enc s rest next in
      (result, FlatSourceCase 3 :: compares ++ map FlatSourceMap writes ++ events)
  end.

(** The fallback follows the actual empty, rejected, and accepted entry branches. *)
Definition audit_flat_source_counted {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B)
    : Map.t V V * list (audit_flat_source_event V E B) :=
  match Graph.entries g with
  | [] => (Map.empty, [FlatSourceCase 4])
  | s :: rest =>
      let '(same, comparisons) := audit_flat_source_entries (audit_dfs_encode_model cb) s rest in
      if same then
        let '(search, search_events) := audit_dfs_source_counted p cb FinSet.empty (Graph.entries g)
  in
        let '(result, events) := audit_flat_source_fold (audit_dfs_encode_model cb) s
          (preorder search) Map.empty in
        (result, FlatSourceCase 5 :: comparisons ++ map FlatSourceDfs search_events ++ events)
      else (Map.empty, FlatSourceCase 6 :: comparisons)
  end.

(** Source work includes each primitive and its actual callback bodies. *)
Definition audit_flat_source_event_work {V E B} (weight : B -> nat)
    (event : audit_flat_source_event V E B) : nat :=
  64 + match event with
  | FlatSourceCase _ => 0
  | FlatSourceCompare _ _ _ _ ea eb _ calls =>
      fold_right (fun x n => weight x + n) 0 ea +
      fold_right (fun x n => weight x + n) 0 eb + audit_positive_eqb_source_work calls
  | FlatSourceDfs call => audit_dfs_source_event_work weight call
  | FlatSourceMap call => audit_map_source_work (fun es => fold_right (fun x n => weight x + n) 0
  es) [call]
  end.

(** External work counts only recorded client callback bodies. *)
Definition audit_flat_source_event_external {V E B} (weight : B -> nat)
    (event : audit_flat_source_event V E B) : nat :=
  match event with
  | FlatSourceCompare _ _ _ _ ea eb _ _ =>
      fold_right (fun x n => weight x + n) 0 ea + fold_right (fun x n => weight x + n) 0 eb
  | FlatSourceDfs call => audit_dfs_source_body_work weight [call]
  | FlatSourceMap (AuditMapGet _ _ _ _ es _) | FlatSourceMap (AuditMapSet _ _ _ _ _ es _) |
    FlatSourceMap (AuditMapRemove _ _ _ _ es _) => fold_right (fun x n => weight x + n) 0 es
  | FlatSourceCase _ => 0
  end.

(** Total work sums the events of this same fallback run. *)
Definition audit_flat_source_work {V E B} (weight : B -> nat)
    (events : list (audit_flat_source_event V E B)) : nat :=
  fold_right (fun event n => audit_flat_source_event_work weight event + n) 0 events.

(** External work sums the bodies attached to this same fallback run. *)
Definition audit_flat_source_external {V E B} (weight : B -> nat)
    (events : list (audit_flat_source_event V E B)) : nat :=
  fold_right (fun event n => audit_flat_source_event_external weight event + n) 0 events.

(** The budget depends on input dimensions and the already defined DFS budget. *)
Definition audit_flat_source_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) : nat :=
  let scale := S (length (Graph.entries g) + Pos.to_nat (fuel p) +
    audit_dfs_full_input_width EV g p (Graph.entries g) +
    audit_dfs_source_budget EV g p (Graph.entries g)) in
  4096 * Nat.pow scale 8.

(** The fallback returns the actual result with its complete source work bounded. *)
Definition audit_flat_source_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (cb : audit_dfs_callback_model V E B) (weight : B -> nat),
    audit_dfs_callbacks_erase EV g cb ->
    let '(result, events) := audit_flat_source_counted p cb in
    result = flat_idom p /\ audit_flat_source_work weight events <=
      audit_flat_source_budget EV g p + audit_flat_source_external weight events.

(** Events retain each concrete primitive call and each nested traversal. *)
Inductive audit_check_idom_event (V E B : Type) : Type :=
  | CheckIdomCase : nat -> audit_check_idom_event V E B
  | CheckIdomDfs : audit_dfs_nested_event V E (audit_graph_callback_capture V E B) ->
      audit_check_idom_event V E B
  | CheckIdomDom : audit_dom_source_event V E B -> audit_check_idom_event V E B
  | CheckIdomElements : audit_elements_event (V * V) -> audit_check_idom_event V E B
  | CheckIdomSet : audit_set_event V B -> audit_check_idom_event V E B
  | CheckIdomMap : audit_map_event V positive B -> audit_check_idom_event V E B
  | CheckIdomCompare : positive -> positive -> bool -> list audit_positive_compare_event ->
      audit_check_idom_event V E B.
Arguments CheckIdomCase {V E B} _.
Arguments CheckIdomDfs {V E B} _.
Arguments CheckIdomDom {V E B} _.
Arguments CheckIdomElements {V E B} _.
Arguments CheckIdomSet {V E B} _.
Arguments CheckIdomMap {V E B} _.
Arguments CheckIdomCompare {V E B} _ _ _ _.

(** Every binding evaluates all three set membership tests. *)
Fixpoint audit_check_idom_bindings {V E B} (enc : V -> positive * list B)
    (live numbered : FinSet.t V) (rows : list (V * V)) : bool * list (audit_check_idom_event V E B)
  :=
  match rows with
  | [] => (true, [CheckIdomCase 0])
  | (v, u) :: rest =>
      let '(a, ea) := audit_finset_mem enc v live in
      let '(b, eb) := audit_finset_mem enc u live in
      let '(c, ec) := audit_finset_mem enc v numbered in
      let '(later, events) := audit_check_idom_bindings enc live numbered rest in
      ((a && b && c) && later,
        CheckIdomCase 1 :: map CheckIdomSet ea ++ map CheckIdomSet eb ++
          map CheckIdomSet ec ++ events)
  end.

(** Interval lookups stop at the first missing value. *)
Definition audit_check_idom_dominates {V E B} (enc : V -> positive * list B)
    (t : dom_tree V) (d n : V) : bool * list (audit_check_idom_event V E B) :=
  let '(a, ea) := audit_map_get enc d (tin t) in
  match a with
  | None => (false, map CheckIdomMap ea ++ [CheckIdomCase 2])
  | Some aa =>
      let '(b, eb) := audit_map_get enc n (tin t) in
      match b with
      | None => (false, map CheckIdomMap ea ++ map CheckIdomMap eb ++ [CheckIdomCase 2])
      | Some bb =>
          let '(c, ec) := audit_map_get enc d (tout t) in
          match c with
          | None => (false, map CheckIdomMap ea ++ map CheckIdomMap eb ++ map CheckIdomMap ec ++
              [CheckIdomCase 2])
          | Some cc =>
              let '(e, ee) := audit_map_get enc n (tout t) in
              let reads := map CheckIdomMap ea ++ map CheckIdomMap eb ++
                map CheckIdomMap ec ++ map CheckIdomMap ee in
              match e with
              | None => (false, reads ++ [CheckIdomCase 2])
              | Some dd =>
                  let '(lhs, el) := audit_positive_leb aa bb in
                  let '(rhs, er) := audit_positive_leb dd cc in
                  (lhs && rhs, reads ++ [CheckIdomCompare aa bb lhs el; CheckIdomCompare dd cc rhs
  er])
              end
          end
      end
  end.

(** Every node checks blocked reachability and its interval comparison. *)
Fixpoint audit_check_idom_nodes {V E B} (enc : V -> positive * list B)
    (blocked : FinSet.t V) (t : dom_tree V) (d : V) (vertices : list V)
    : bool * list (audit_check_idom_event V E B) :=
  match vertices with
  | [] => (true, [CheckIdomCase 3])
  | n :: rest =>
      let '(seen, se) := audit_finset_mem enc n blocked in
      let '(dom, de) := audit_check_idom_dominates enc t d n in
      let '(later, events) := audit_check_idom_nodes enc blocked t d rest in
      (Bool.eqb (negb seen) dom && later, CheckIdomCase 4 :: map CheckIdomSet se ++ de ++ events)
  end.

(** Each candidate dominator performs its own blocked DFS and complete node scan. *)
Fixpoint audit_check_idom_candidates {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (t : dom_tree V)
    (all todo : list V) : bool * list (audit_check_idom_event V E B) :=
  match todo with
  | [] => (true, [CheckIdomCase 5])
  | d :: rest =>
      let '(blocked, add_events) := audit_finset_add (audit_dfs_encode_model cb) d FinSet.empty in
      let '(search, dfs_events) := audit_dfs_source_counted p cb blocked (Graph.entries g) in
      let '(ok, checks) := audit_check_idom_nodes (audit_dfs_encode_model cb) (visited search) t d
  all in
      let '(later, events) := audit_check_idom_candidates p cb t all rest in
      (ok && later, CheckIdomCase 6 :: map CheckIdomSet add_events ++
        map CheckIdomDfs dfs_events ++ checks ++ events)
  end.

(** This models the exact checker execution, including all intermediate search results. *)
Definition audit_check_idom_source_counted {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (parents : Map.t V V) (cb : audit_dfs_callback_model V E B)
    : bool * list (audit_check_idom_event V E B) :=
  let '(live, live_events) := audit_dfs_source_counted p cb FinSet.empty (Graph.entries g) in
  let receipt := audit_dom_search_source_counted p parents cb in
  let search := audit_dom_source_result receipt in
  let t := DomTree parents (pre_num search) (post_num search) in
  let '(rows, elements) := audit_map_elements parents in
  let '(binding_ok, bindings) := audit_check_idom_bindings (audit_dfs_encode_model cb)
    (visited live) (visited search) rows in
  let '(node_ok, nodes) := audit_check_idom_candidates p cb t (preorder live) (preorder live) in
  (binding_ok && node_ok, map CheckIdomDfs live_events ++
    map CheckIdomDom (audit_dom_source_events receipt) ++ map CheckIdomElements elements ++
    bindings ++ nodes).

(** Work charges nested source operations and the bodies attached to their actual calls. *)
Definition audit_check_idom_event_work {V E B} (weight : B -> nat)
    (event : audit_check_idom_event V E B) : nat :=
  let body := fun xs => fold_right (fun x n => weight x + n) 0 xs in
  64 + match event with
  | CheckIdomCase _ => 0
  | CheckIdomDfs call => audit_dfs_source_event_work weight call
  | CheckIdomDom call => audit_dom_source_event_work weight call
  | CheckIdomElements call => audit_elements_frame_work call
  | CheckIdomSet call => audit_finset_source_work body [call]
  | CheckIdomMap call => audit_map_source_work body [call]
  | CheckIdomCompare _ _ _ calls => audit_positive_order_source_work calls
  end.

(** The external charge retains only client bodies from this execution. *)
Definition audit_check_idom_event_external {V E B} (weight : B -> nat)
    (event : audit_check_idom_event V E B) : nat :=
  match event with
  | CheckIdomDfs call => audit_dfs_source_body_work weight [call]
  | CheckIdomDom call => audit_dom_source_event_external weight call
  | CheckIdomSet (AuditSetAdd _ _ _ _ body _) | CheckIdomSet (AuditSetMem _ _ _ _ body _) |
    CheckIdomSet (AuditSetRemove _ _ _ _ body _) | CheckIdomMap (AuditMapGet _ _ _ _ body _) |
    CheckIdomMap (AuditMapSet _ _ _ _ _ body _) | CheckIdomMap (AuditMapRemove _ _ _ _ body _) =>
      fold_right (fun x n => weight x + n) 0 body
  | CheckIdomCase _ | CheckIdomElements _ | CheckIdomSet (AuditSetFold _ _) |
    CheckIdomCompare _ _ _ _ => 0
  end.

(** The work measure sums the recorded source events. *)
Definition audit_check_idom_source_work {V E B} (weight : B -> nat)
    (events : list (audit_check_idom_event V E B)) : nat :=
  fold_right (fun event n => audit_check_idom_event_work weight event + n) 0 events.

(** The body measure sums the same run's client callback bodies. *)
Definition audit_check_idom_source_external {V E B} (weight : B -> nat)
    (events : list (audit_check_idom_event V E B)) : nat :=
  fold_right (fun event n => audit_check_idom_event_external weight event + n) 0 events.

(** The input scale includes parent keys, values, structure, prepared input and DFS budget. *)
Definition audit_check_idom_input_scale {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (parents : Map.t V V) : nat :=
  let rows := Map.elements parents in
  let width := fold_right Nat.max 0 (map (fun row =>
    Nat.max (Pos.size_nat (encode EV (fst row))) (Pos.size_nat (encode EV (snd row)))) rows) in
  S (length rows + width + audit_trie_nodes parents + Pos.to_nat (fuel p) +
    length (Graph.entries g) + audit_dfs_full_input_width EV g p (Graph.entries g) +
    audit_dfs_source_budget EV g p (Graph.entries g)).

(** The complete checker budget is derived from its input dimensions. *)
Definition audit_check_idom_source_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (parents : Map.t V V) : nat :=
  1048576 * Nat.pow (audit_check_idom_input_scale EV g p parents) 48.

(** The source model returns the checker result with bounded work. *)
Definition audit_check_idom_source_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) parents
    (cb : audit_dfs_callback_model V E B) (weight : B -> nat),
    audit_dfs_callbacks_erase EV g cb ->
    let '(result, events) := audit_check_idom_source_counted p parents cb in
    result = check_idom p parents /\ audit_check_idom_source_work weight events <=
      audit_check_idom_source_budget EV g p parents + audit_check_idom_source_external weight
  events.
Definition audit_virtual_nca_stage_work {V E B} (weight : B -> nat)
    (events : list (audit_nca_source_event (V + unit) (E + V)
      (audit_virtual_full_call V E B))) : nat :=
  audit_nca_source_work
    (fun event => audit_virtual_full_internal_event_work event +
      audit_virtual_full_body_event_work weight event) events.

(** External callback bodies are charged for the same recorded calls. *)
Definition audit_virtual_nca_external_work {V E B} (weight : B -> nat)
    (events : list (audit_nca_source_event (V + unit) (E + V)
      (audit_virtual_full_call V E B))) : nat :=
  audit_nca_source_body_work (audit_virtual_full_body_event_work weight) events.

Definition audit_virtual_nca_input_scale {V E} (EV : encoding V) (g : Graph.t V E) : nat :=
  let edges := flat_map (Graph.out g) (Graph.nodes g) in
  let vertices := Graph.nodes g ++ Graph.entries g ++ map (Graph.source g) edges ++
    map (Graph.target g) edges in
  4 + length (Graph.nodes g) + length (Graph.entries g) + length edges +
    fold_right Nat.max 0 (map (fun v => Pos.size_nat (encode EV v)) vertices).

(** The whole-producer budget depends only on the original graph and encoder. *)
Definition audit_virtual_nca_input_budget {V E} (EV : encoding V) (g : Graph.t V E) : nat :=
  1048576 * Nat.pow (audit_virtual_nca_input_scale EV g) 48.

Inductive audit_dom_select_trace (V E B : Type) : Type :=
  | DomSelectLt : list (audit_lt_nested_event (V + unit) (E + V)
      (audit_virtual_full_call V E B)) -> audit_dom_select_trace V E B
  | DomSelectNca : list (audit_nca_source_event (V + unit) (E + V)
      (audit_virtual_full_call V E B)) -> audit_dom_select_trace V E B.
Arguments DomSelectLt {V E B} _.
Arguments DomSelectNca {V E B} _.

Definition audit_dom_select_backend_work {V E B} (weight : B -> nat)
    (events : audit_dom_select_trace V E B) : nat :=
  match events with
  | DomSelectLt calls => audit_virtual_lt_stage_work weight calls
  | DomSelectNca calls => audit_virtual_nca_stage_work weight calls
  end.

(** External work charges the same chosen backend's client bodies. *)
Definition audit_dom_select_backend_external {V E B} (weight : B -> nat)
    (events : audit_dom_select_trace V E B) : nat :=
  match events with
  | DomSelectLt calls => audit_virtual_lt_external_work weight calls
  | DomSelectNca calls => audit_virtual_nca_external_work weight calls
  end.

Definition audit_dom_select_source_budget {V E B} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (parents : Map.t V V) (receipt : audit_dom_source_receipt V E B EV) : nat :=
  audit_virtual_lt_input_budget EV g + audit_virtual_nca_input_budget EV g +
  audit_dom_search_source_budget EV g p parents receipt.

(** The original-input budget includes the input graph and prepared traversal dimensions. *)
Definition audit_dom_select_input_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) : nat :=
  let scale := S (audit_virtual_nca_input_scale EV g + Pos.to_nat (fuel p) +
    audit_dfs_full_input_width EV g p (Graph.entries g) +
    audit_dfs_source_budget EV g p (Graph.entries g)) in
  1048576 * Nat.pow scale 64.

(** The chosen backend consumes the already captured search and semidominator results. *)
Definition audit_dom_select_single_backend {V E B} (EV : encoding V) (g : Graph.t V E)
    (cb : audit_virtual_base_callbacks V E B) (source : E -> V * list B)
    (search : dfs_result (V + unit) (E + V)) (semis : Map.t (V + unit) (V + unit))
    (choice : dom_algorithm) (trace : audit_dom_select_trace V E B)
    (parents : Map.t (V + unit) (V + unit)) : Prop :=
  match choice, trace with
  | SimpleLT, DomSelectLt events =>
      audit_lt_nested_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
        search semis parents events
  | SemiNCA, DomSelectNca events =>
      audit_nca_source_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
        search semis parents events
  | _, _ => False
  end.

(** Every bound component reads traces from the same one virtual-search invocation. *)
Definition audit_dom_select_single_run_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) choice
    (cb : audit_virtual_base_callbacks V E B) (source : E -> V * list B) (weight : B -> nat),
    audit_virtual_base_callbacks_erase EV g cb ->
    (forall edge, fst (source edge) = Graph.source g edge) ->
    exists vp search prepare_events dfs_events semi_state semi_events virtual_parents backend_events
      parents erase_events receipt result,
      audit_virtual_source_search EV g cb = (vp, (search, (prepare_events, dfs_events))) /\
      audit_semi_producer_nested_run (audit_virtual_full_encode cb) (audit_virtual_full_source
  source)
        vp search semi_state semi_events /\
      audit_dom_select_single_backend EV g cb source search (SemiState.result semi_state)
        choice backend_events virtual_parents /\
      audit_erase_virtual_nested (audit_virtual_base_encode cb) virtual_parents = (parents,
  erase_events) /\
      receipt = audit_dom_search_source_counted p parents
        (AuditDfsCallbackModel V E B (audit_virtual_base_target cb) (audit_virtual_base_encode cb))
  /\
      result = DomTree parents (pre_num (audit_dom_source_result receipt))
        (post_num (audit_dom_source_result receipt)) /\
      result = dominator_tree_with p choice /\
      let work := audit_prepare_source_work
        (fun event => audit_virtual_full_internal_event_work event +
  audit_virtual_full_body_event_work weight event)
        prepare_events +
        audit_dfs_source_work
          (fun event => audit_virtual_full_internal_event_work event +
  audit_virtual_full_body_event_work weight event)
          dfs_events + audit_virtual_semi_stage_work weight semi_events +
        audit_dom_select_backend_work weight backend_events + audit_erase_nested_work weight
  erase_events +
        audit_dom_source_work weight (audit_dom_source_events receipt) in
      let external := audit_prepare_source_body_work (audit_virtual_full_body_event_work weight)
  prepare_events +
        audit_dfs_source_body_work (audit_virtual_full_body_event_work weight) dfs_events +
        audit_virtual_semi_external_work weight semi_events + audit_dom_select_backend_external
  weight backend_events +
        audit_erase_nested_body_work weight erase_events +
        audit_dom_source_external_work weight (audit_dom_source_events receipt) in
      work <= audit_dom_select_source_budget EV g p parents receipt + external /\
      work <= audit_dom_select_input_budget EV g p + external.

(** The NCA backend itself shares one search receipt with all source-work charges. *)
Definition audit_virtual_nca_single_run_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (cb : audit_virtual_base_callbacks V E B) (source : E -> V * list B) (weight : B -> nat),
    audit_virtual_base_callbacks_erase EV g cb ->
    (forall edge, fst (source edge) = Graph.source g edge) ->
    exists vp search prepare_events dfs_events semi_state semi_events virtual_parents nca_events
      parents erase_events,
      audit_virtual_source_search EV g cb = (vp, (search, (prepare_events, dfs_events))) /\
      audit_semi_producer_nested_run (audit_virtual_full_encode cb) (audit_virtual_full_source
  source)
        vp search semi_state semi_events /\
      audit_nca_source_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
        search (SemiState.result semi_state) virtual_parents nca_events /\
      audit_erase_virtual_nested (audit_virtual_base_encode cb) virtual_parents = (parents,
  erase_events) /\
      parents = semi_nca_idom p /\
      audit_prepare_source_work
        (fun event => audit_virtual_full_internal_event_work event +
  audit_virtual_full_body_event_work weight event)
        prepare_events + audit_dfs_source_work
        (fun event => audit_virtual_full_internal_event_work event +
  audit_virtual_full_body_event_work weight event)
        dfs_events + audit_virtual_semi_stage_work weight semi_events + audit_virtual_nca_stage_work
  weight nca_events +
        audit_erase_nested_work weight erase_events <= audit_virtual_nca_input_budget EV g +
      audit_prepare_source_body_work (audit_virtual_full_body_event_work weight) prepare_events +
      audit_dfs_source_body_work (audit_virtual_full_body_event_work weight) dfs_events +
      audit_virtual_semi_external_work weight semi_events + audit_virtual_nca_external_work weight
  nca_events +
      audit_erase_nested_body_work weight erase_events.

(** A captured DFS call charges the genuine callback at its recorded input. *)
Definition audit_flat_check_capture_budget {V E B} (encode_budget : V -> nat) (target_budget : E ->
  nat)
    (calls : list (audit_graph_callback_capture V E B)) : nat :=
  fold_right (fun call n => audit_scc_capture_budget encode_budget target_budget call + n) 0 calls.

(** Every fallback event exposes its actual external callback inputs. *)
Definition audit_flat_source_event_budget {V E B} (encode_budget : V -> nat) (target_budget : E ->
  nat)
    (event : audit_flat_source_event V E B) : nat :=
  match event with
  | FlatSourceCase _ => 0
  | FlatSourceCompare v s _ _ _ _ _ _ => encode_budget v + encode_budget s
  | FlatSourceDfs (_, calls) => audit_flat_check_capture_budget encode_budget target_budget calls
  | FlatSourceMap (AuditMapGet v _ _ _ _ _) | FlatSourceMap (AuditMapSet v _ _ _ _ _ _) |
    FlatSourceMap (AuditMapRemove v _ _ _ _ _) => encode_budget v
  end.

(** The fallback has a bound in terms of actual callback budgets. *)
Definition audit_flat_source_adapted_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (cb : audit_dfs_callback_model V E B) (weight : B -> nat)
    encode_source target_source encode_budget target_budget,
    audit_dfs_callbacks_erase EV g cb ->
    audit_graph_external_callback_adapter (audit_dfs_encode_model cb) weight encode_source
  encode_budget ->
    audit_graph_external_callback_adapter (audit_dfs_target_model cb) weight target_source
  target_budget ->
    let '(result, events) := audit_flat_source_counted p cb in
    result = flat_idom p /\ audit_flat_source_work weight events <= audit_flat_source_budget EV g p
  +
      fold_right (fun event n => audit_flat_source_event_budget encode_budget target_budget event +
  n) 0 events.

(** The complete fallback contract includes its source and adapted work claims. *)
Definition audit_flat_source_contract_statement : Prop :=
  audit_flat_source_statement /\ audit_flat_source_adapted_statement.

(** The internal forest callback charges only its actual captured client encoder calls. *)
Definition audit_dom_source_body_budget {V B} (encode_budget : V -> nat)
    (event : audit_dom_source_body V B) : nat :=
  match event with
  | DomSourceBodyMap (AuditMapGet v _ _ _ _ _) | DomSourceBodyMap (AuditMapSet v _ _ _ _ _ _) |
    DomSourceBodyMap (AuditMapRemove v _ _ _ _ _) | DomSourceBodyEncode v _ _ => encode_budget v
  | DomSourceBodyTarget _ => 0
  end.

(** Forest search prices its nested calls by their original client inputs. *)
Definition audit_dom_source_event_budget {V E B} (encode_budget : V -> nat) (target_budget : E ->
  nat)
    (event : audit_dom_source_event V E B) : nat :=
  match event with
  | DomSourceInitialDfs (_, calls) => audit_flat_check_capture_budget encode_budget target_budget
  calls
  | DomSourceChild (AuditMapGet v _ _ _ _ _) | DomSourceChild (AuditMapSet v _ _ _ _ _ _) |
    DomSourceChild (AuditMapRemove v _ _ _ _ _) | DomSourceParent (AuditMapGet v _ _ _ _ _) |
    DomSourceParent (AuditMapSet v _ _ _ _ _ _) | DomSourceParent (AuditMapRemove v _ _ _ _ _) =>
  encode_budget v
  | DomSourcePrepare call => audit_prepare_source_body_work (audit_dom_source_body_budget
  encode_budget) [call]
  | DomSourceDfs call => audit_dfs_source_body_work (audit_dom_source_body_budget encode_budget)
  [call]
  | DomSourceCase _ | DomSourceElements _ => 0
  end.

(** Each checker event exposes the actual external encoder and target inputs. *)
Definition audit_check_idom_event_budget {V E B} (encode_budget : V -> nat) (target_budget : E ->
  nat)
    (event : audit_check_idom_event V E B) : nat :=
  match event with
  | CheckIdomDfs (_, calls) => audit_flat_check_capture_budget encode_budget target_budget calls
  | CheckIdomDom call => audit_dom_source_event_budget encode_budget target_budget call
  | CheckIdomSet (AuditSetAdd v _ _ _ _ _) | CheckIdomSet (AuditSetMem v _ _ _ _ _) |
    CheckIdomSet (AuditSetRemove v _ _ _ _ _) | CheckIdomMap (AuditMapGet v _ _ _ _ _) |
    CheckIdomMap (AuditMapSet v _ _ _ _ _ _) | CheckIdomMap (AuditMapRemove v _ _ _ _ _) =>
  encode_budget v
  | _ => 0
  end.

(** The checker has a bound in terms of actual callback budgets. *)
Definition audit_check_idom_source_adapted_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) parents
    (cb : audit_dfs_callback_model V E B) (weight : B -> nat)
    encode_source target_source encode_budget target_budget,
    audit_dfs_callbacks_erase EV g cb ->
    audit_graph_external_callback_adapter (audit_dfs_encode_model cb) weight encode_source
  encode_budget ->
    audit_graph_external_callback_adapter (audit_dfs_target_model cb) weight target_source
  target_budget ->
    let '(result, events) := audit_check_idom_source_counted p parents cb in
    result = check_idom p parents /\ audit_check_idom_source_work weight events <=
      audit_check_idom_source_budget EV g p parents +
      fold_right (fun event n => audit_check_idom_event_budget encode_budget target_budget event +
  n) 0 events.

(** The complete checker contract includes both recorded-body and adapted bounds. *)
Definition audit_check_idom_source_contract_statement : Prop :=
  audit_check_idom_source_statement /\ audit_check_idom_source_adapted_statement.

(** Every virtual event prices only genuine supplied callbacks at captured inputs. *)
Definition audit_virtual_call_budget {V E B} (encode_budget out_budget : V -> nat)
    (target_budget source_budget : E -> nat) (event : audit_virtual_full_call V E B) : nat :=
  match event with
  | VirtualFullOut v _ _ => out_budget v
  | VirtualFullTarget e _ _ => target_budget e
  | VirtualFullSource e _ _ => source_budget e
  | VirtualFullEncode v _ _ => encode_budget v
  | VirtualFullEntry (VirtualEntriesSet (AuditSetAdd v _ _ _ _ _)) |
    VirtualFullEntry (VirtualEntriesSet (AuditSetMem v _ _ _ _ _)) |
    VirtualFullEntry (VirtualEntriesSet (AuditSetRemove v _ _ _ _ _)) => encode_budget v
  | _ => 0
  end.

(** Erasure prices its recorded real-vertex encoder calls. *)
Definition audit_erase_nested_event_budget {V B} (encode_budget : V -> nat)
    (event : audit_erase_nested_event V B) : nat :=
  match event with
  | EraseNestedSet (AuditMapGet v _ _ _ _ _) | EraseNestedSet (AuditMapSet v _ _ _ _ _ _) |
    EraseNestedSet (AuditMapRemove v _ _ _ _ _) => encode_budget v
  | _ => 0
  end.

(** The selected backend budgets the captured events of the chosen actual branch. *)
Definition audit_dom_select_backend_budget {V E B} (budget : audit_virtual_full_call V E B -> nat)
    (trace : audit_dom_select_trace V E B) : nat :=
  match trace with
  | DomSelectLt events => audit_lt_nested_body_work budget events
  | DomSelectNca events => audit_nca_source_body_work budget events
  end.

(** An adapted selector binds one search receipt and prices every actual client call. *)
Definition audit_dom_select_single_adapted_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) choice
    (cb : audit_virtual_base_callbacks V E B) (source : E -> V * list B) (weight : B -> nat)
    encode_source out_source target_source source_source encode_budget out_budget target_budget
  source_budget,
    audit_virtual_base_callbacks_erase EV g cb ->
    (forall edge, fst (source edge) = Graph.source g edge) ->
    audit_graph_external_callback_adapter (audit_virtual_base_encode cb) weight encode_source
  encode_budget ->
    audit_graph_external_callback_adapter (audit_virtual_base_out cb) weight out_source out_budget
  ->
    audit_graph_external_callback_adapter (audit_virtual_base_target cb) weight target_source
  target_budget ->
    audit_graph_external_callback_adapter source weight source_source source_budget ->
    exists vp search prepare_events dfs_events semi_state semi_events virtual_parents backend_events
      parents erase_events receipt result,
      audit_virtual_source_search EV g cb = (vp, (search, (prepare_events, dfs_events))) /\
      audit_semi_producer_nested_run (audit_virtual_full_encode cb) (audit_virtual_full_source
  source)
        vp search semi_state semi_events /\
      audit_dom_select_single_backend EV g cb source search (SemiState.result semi_state)
        choice backend_events virtual_parents /\
      audit_erase_virtual_nested (audit_virtual_base_encode cb) virtual_parents = (parents,
  erase_events) /\
      receipt = audit_dom_search_source_counted p parents
        (AuditDfsCallbackModel V E B (audit_virtual_base_target cb) (audit_virtual_base_encode cb))
  /\
      result = DomTree parents (pre_num (audit_dom_source_result receipt))
        (post_num (audit_dom_source_result receipt)) /\
      result = dominator_tree_with p choice /\
      let work := audit_prepare_source_work
        (fun event => audit_virtual_full_internal_event_work event +
  audit_virtual_full_body_event_work weight event)
        prepare_events + audit_dfs_source_work
        (fun event => audit_virtual_full_internal_event_work event +
  audit_virtual_full_body_event_work weight event)
        dfs_events + audit_virtual_semi_stage_work weight semi_events +
        audit_dom_select_backend_work weight backend_events + audit_erase_nested_work weight
  erase_events +
        audit_dom_source_work weight (audit_dom_source_events receipt) in
      let budget := audit_virtual_call_budget encode_budget out_budget target_budget source_budget
  in
      let external := audit_prepare_source_body_work budget prepare_events +
  audit_dfs_source_body_work budget dfs_events +
        audit_semi_producer_nested_body_work budget semi_events + audit_dom_select_backend_budget
  budget backend_events +
        fold_right (fun event n => audit_erase_nested_event_budget encode_budget event + n) 0
  erase_events +
        fold_right (fun event n => audit_dom_source_event_budget encode_budget target_budget event +
  n) 0
          (audit_dom_source_events receipt) in
      work <= audit_dom_select_input_budget EV g p + external.

(** The selector contract includes recorded-body and per-call adapted source bounds. *)
Definition audit_dom_select_source_contract_statement : Prop :=
  audit_dom_select_single_run_statement /\ audit_dom_select_single_adapted_statement.

(** The NCA backend prices the same recorded virtual invocation at actual client inputs. *)
Definition audit_virtual_nca_single_adapted_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (cb : audit_virtual_base_callbacks V E B) (source : E -> V * list B) (weight : B -> nat)
    encode_source out_source target_source source_source encode_budget out_budget target_budget
  source_budget,
    audit_virtual_base_callbacks_erase EV g cb ->
    (forall edge, fst (source edge) = Graph.source g edge) ->
    audit_graph_external_callback_adapter (audit_virtual_base_encode cb) weight encode_source
  encode_budget ->
    audit_graph_external_callback_adapter (audit_virtual_base_out cb) weight out_source out_budget
  ->
    audit_graph_external_callback_adapter (audit_virtual_base_target cb) weight target_source
  target_budget ->
    audit_graph_external_callback_adapter source weight source_source source_budget ->
    exists vp search prepare_events dfs_events semi_state semi_events virtual_parents nca_events
      parents erase_events,
      audit_virtual_source_search EV g cb = (vp, (search, (prepare_events, dfs_events))) /\
      audit_semi_producer_nested_run (audit_virtual_full_encode cb) (audit_virtual_full_source
  source)
        vp search semi_state semi_events /\
      audit_nca_source_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
        search (SemiState.result semi_state) virtual_parents nca_events /\
      audit_erase_virtual_nested (audit_virtual_base_encode cb) virtual_parents = (parents,
  erase_events) /\
      parents = semi_nca_idom p /\
      let work := audit_prepare_source_work
        (fun event => audit_virtual_full_internal_event_work event +
  audit_virtual_full_body_event_work weight event)
        prepare_events + audit_dfs_source_work
        (fun event => audit_virtual_full_internal_event_work event +
  audit_virtual_full_body_event_work weight event)
        dfs_events + audit_virtual_semi_stage_work weight semi_events +
        audit_virtual_nca_stage_work weight nca_events + audit_erase_nested_work weight erase_events
  in
      let budget := audit_virtual_call_budget encode_budget out_budget target_budget source_budget
  in
      let external := audit_prepare_source_body_work budget prepare_events +
  audit_dfs_source_body_work budget dfs_events +
        audit_semi_producer_nested_body_work budget semi_events + audit_nca_source_body_work budget
  nca_events +
        fold_right (fun event n => audit_erase_nested_event_budget encode_budget event + n) 0
  erase_events in
      work <= audit_virtual_nca_input_budget EV g + external.

(** The NCA contract includes recorded-body and actual-call adapted source bounds. *)
Definition audit_virtual_nca_source_contract_statement : Prop :=
  audit_virtual_nca_single_run_statement /\ audit_virtual_nca_single_adapted_statement.

(** The fallback contract names its map and binary equality obligations. *)
Definition audit_flat_source_full_contract_statement : Prop :=
  audit_flat_source_contract_statement /\ audit_map_get_source_work_bound_statement /\
  audit_map_set_source_work_bound_statement /\ audit_positive_eqb_erases_statement /\
  audit_positive_eqb_source_bound_statement.

(** The checker contract names membership, map, comparison and forest-search obligations. *)
Definition audit_check_idom_source_full_contract_statement : Prop :=
  audit_check_idom_source_contract_statement /\ audit_map_get_source_work_bound_statement /\
  audit_finset_mem_erases_statement /\ audit_finset_add_erases_statement /\
  audit_positive_compare_cont_statement /\ audit_positive_order_statement /\
  audit_dom_search_source_statement.

(** The NCA source contract couples the forward pass and its virtual adapted invocation. *)
Definition audit_virtual_nca_source_full_contract_statement : Prop :=
  audit_nca_source_statement /\ audit_nca_source_unique_statement /\
  audit_virtual_nca_source_contract_statement /\ audit_map_get_source_work_bound_statement /\
  audit_map_set_source_work_bound_statement /\ audit_positive_compare_cont_statement /\
  audit_positive_order_statement.

(** The selectable producer includes both backend and forest-search source obligations. *)
Definition audit_dom_select_source_full_contract_statement : Prop :=
  audit_dom_select_source_contract_statement /\ audit_virtual_nca_source_full_contract_statement /\
  audit_lt_nested_erasure_statement /\ audit_lt_nested_unique_statement /\
  audit_lt_nested_bound_statement /\
  audit_dom_search_source_statement.
```

## Galois.Graph.GraphAuditFrontier

Card: AUD-GR-MODELS

Source destination: `theories/Graph/GraphAuditFrontier.v`.

```rocq
From Galois.Collections Require Import CollectionsAuditCost.
From Galois.Graph Require Import GraphAuditBase GraphAuditDfs GraphAuditVirtual
  GraphAuditDominators.

From Stdlib Require Import List Bool PArith ZArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditCost.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphDominators.

Import List.ListNotations.

Inductive audit_frontier_dom_call (N : Type) : Type :=
| AuditFrontierDomGet (n : N) (m : Map.t N positive) (r : option positive)
| AuditFrontierDomLe (a b : positive) (r : bool).
Arguments AuditFrontierDomGet {N} _ _ _.
Arguments AuditFrontierDomLe {N} _ _ _.

Definition audit_frontier_dom_counted {N} (EN : encoding N) (tree : dom_tree N) (d t : N)
    : bool * list (audit_frontier_dom_call N) :=
  let a := Map.get EN d (tin tree) in
  match a with
  | None => (false, [AuditFrontierDomGet d (tin tree) a])
  | Some av => let b := Map.get EN t (tin tree) in
    match b with
    | None => (false, [AuditFrontierDomGet d (tin tree) a; AuditFrontierDomGet t (tin tree) b])
    | Some bv => let c := Map.get EN d (tout tree) in
      match c with
      | None => (false, [AuditFrontierDomGet d (tin tree) a; AuditFrontierDomGet t (tin tree) b;
          AuditFrontierDomGet d (tout tree) c])
      | Some cv => let e := Map.get EN t (tout tree) in
        match e with
        | None => (false, [AuditFrontierDomGet d (tin tree) a; AuditFrontierDomGet t (tin tree) b;
            AuditFrontierDomGet d (tout tree) c; AuditFrontierDomGet t (tout tree) e])
        | Some ev => let first := Pos.leb av bv in let second := Pos.leb ev cv in
          (first && second, [AuditFrontierDomGet d (tin tree) a; AuditFrontierDomGet t (tin tree) b;
            AuditFrontierDomGet d (tout tree) c; AuditFrontierDomGet t (tout tree) e;
            AuditFrontierDomLe av bv first; AuditFrontierDomLe ev cv second])
        end
      end
    end
  end.

Definition audit_frontier_dom_event_work {N} (EN : encoding N) (event : audit_frontier_dom_call N) :
  nat :=
  64 + match event with
  | AuditFrontierDomGet n _ _ => audit_get_weight (encode EN n) + audit_encoding_weight
  (audit_key_bits_weight (encode EN n))
  | AuditFrontierDomLe a b _ => audit_binary_weight (Z.pos a) (Z.pos b)
  end.

Definition audit_frontier_dom_statement : Prop :=
  forall N (EN : encoding N) tree d t,
    let '(result, events) := audit_frontier_dom_counted EN tree d t in
    result = dominates_b EN tree d t /\ length events <= 6.

From Galois.Graph Require Import GraphFrontier.

Inductive audit_frontier_call (V E : Type) : Type :=
| AuditFrontierCase (site : nat)
| AuditFrontierDom (event : audit_frontier_dom_call V)
| AuditFrontierParent (v : V) (m : Map.t V V) (result : option V)
| AuditFrontierDfs (event : audit_dfs_full_call V E)
| AuditFrontierSource (e : E) (v : V)
| AuditFrontierTarget (e : E) (v : V)
| AuditFrontierPred (v : V) (m : Map.t V (list E)) (result : option (list E))
| AuditFrontierMem (v : V) (s : FinSet.t V) (result : bool)
| AuditFrontierGet (v : V) (m : Map.t V (FinSet.t V)) (result : option (FinSet.t V))
| AuditFrontierSetMember (v : V) (s : FinSet.t V)
| AuditFrontierSetRow (v : V) (row : FinSet.t V) (m : Map.t V (FinSet.t V))
| AuditFrontierOutput (size : nat).
Arguments AuditFrontierCase {V E} _.
Arguments AuditFrontierDom {V E} _.
Arguments AuditFrontierParent {V E} _ _ _.
Arguments AuditFrontierDfs {V E} _.
Arguments AuditFrontierSource {V E} _ _.
Arguments AuditFrontierTarget {V E} _ _.
Arguments AuditFrontierPred {V E} _ _ _.
Arguments AuditFrontierMem {V E} _ _ _.
Arguments AuditFrontierGet {V E} _ _ _.
Arguments AuditFrontierSetMember {V E} _ _.
Arguments AuditFrontierSetRow {V E} _ _ _.
Arguments AuditFrontierOutput {V E} _.

Definition audit_frontier_step_counted {V E} (EV : encoding V) (t : dom_tree V)
    (stop : option V) (state : option V * list V)
    : (option V * list V) * list (audit_frontier_call V E) :=
  let '(current, seen) := state in
  match current with
  | None => ((None, seen), [AuditFrontierCase 0])
  | Some v =>
      let '(blocked, detail) := match stop with
        | None => (false, [])
        | Some q => audit_frontier_dom_counted EV t v q end in
      if blocked then ((None, seen), AuditFrontierCase 1 :: map AuditFrontierDom detail ++
  [AuditFrontierCase 2])
      else let parent := Map.get EV v (idom t) in
        ((parent, v :: seen), AuditFrontierCase 1 :: map AuditFrontierDom detail ++
          [AuditFrontierCase 3; AuditFrontierParent v (idom t) parent])
  end.

Fixpoint audit_frontier_run_counted {V E} (EV : encoding V) (t : dom_tree V) (stop : option V)
    (fuel : positive) (state : option V * list V)
    : (option V * list V) * list (audit_frontier_call V E) :=
  match fst state with
  | None => (state, [AuditFrontierCase 4])
  | Some _ => match fuel with
    | xH => let '(result, events) := audit_frontier_step_counted EV t stop state in
        (result, AuditFrontierCase 5 :: events)
    | xO rest => let '(middle, first) := audit_frontier_run_counted EV t stop rest state in
        let '(result, second) := audit_frontier_run_counted EV t stop rest middle in
        (result, AuditFrontierCase 6 :: first ++ second)
    | xI rest => let '(middle, first) := audit_frontier_run_counted EV t stop rest state in
        let '(last, second) := audit_frontier_run_counted EV t stop rest middle in
        let '(result, events) := audit_frontier_step_counted EV t stop last in
        (result, AuditFrontierCase 7 :: first ++ second ++ events)
    end
  end.

Definition audit_frontier_runner_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (t : dom_tree V) (start : V) (stop : option V)
    : list V * list (audit_frontier_call V E) :=
  let '(result, events) := audit_frontier_run_counted EV t stop (fuel p) (Some start, []) in
  (snd result, events).

Definition audit_frontier_event_work {V E} (EV : encoding V) (event : audit_frontier_call V E) : nat
  :=
  64 + match event with
  | AuditFrontierDom item => audit_frontier_dom_event_work EV item
  | AuditFrontierDfs item => audit_dfs_full_model_event EV item
  | AuditFrontierParent v _ _ | AuditFrontierPred v _ _ | AuditFrontierMem v _ _ | AuditFrontierGet
  v _ _ =>
      audit_encoding_weight (audit_key_bits_weight (encode EV v)) + audit_get_weight (encode EV v)
  | AuditFrontierSetMember v _ | AuditFrontierSetRow v _ _ =>
      audit_encoding_weight (audit_key_bits_weight (encode EV v)) + audit_set_weight (encode EV v)
  | AuditFrontierOutput size => S size
  | _ => 0 end.

Definition audit_frontier_model_work {V E} (EV : encoding V) (events : list (audit_frontier_call V
  E)) : nat :=
  256 * S (length events) * S (length events) +
    fold_right (fun event total => audit_frontier_event_work EV event + total) 0 events.

Definition audit_frontier_runner_width {V} (EV : encoding V) (t : dom_tree V) (start : V) (stop :
  option V) : nat :=
  let parent_rows := Map.elements (idom t) in
  let vertices := start :: (match stop with Some v => [v] | None => [] end) ++
    map fst parent_rows ++ map snd parent_rows ++ map fst (Map.elements (tin t)) ++ map fst
  (Map.elements (tout t)) in
  let numbers := map snd (Map.elements (tin t)) ++ map snd (Map.elements (tout t)) in
  Nat.max (fold_right Nat.max 0 (map (fun v => audit_key_bits_weight (encode EV v)) vertices))
    (fold_right Nat.max 0 (map audit_key_bits_weight numbers)).

Definition audit_frontier_runner_event_bound (fuel : positive) : nat := 3 + 12 * S (Pos.to_nat
  fuel).

Definition audit_frontier_runner_budget {V} (EV : encoding V) (t : dom_tree V)
    (fuel : positive) (start : V) (stop : option V) : nat :=
  let count := audit_frontier_runner_event_bound fuel in let width := audit_frontier_runner_width EV
  t start stop in
  512 * S count * S count + count * (256 + 12 * width).

Definition audit_frontier_runner_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) (t : dom_tree V) start stop,
    let '(result, events) := audit_frontier_runner_counted p t start stop in
    result = frontier_runner p t start stop /\ length events <= audit_frontier_runner_event_bound
  (fuel p) /\
    audit_frontier_model_work EV events <= audit_frontier_runner_budget EV t (fuel p) start stop.


Fixpoint audit_frontier_collect_pred {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (nodes : list V) : list E * list (audit_frontier_call V E) :=
  match nodes with
  | [] => ([], [AuditFrontierCase 10])
  | v :: rest => let found := Map.get EV v (in_index p) in
      let row := match found with Some xs => xs | None => [] end in
      let '(later, events) := audit_frontier_collect_pred p rest in
      (row ++ later, AuditFrontierCase 11 :: AuditFrontierPred v (in_index p) found :: events ++
        [AuditFrontierOutput (length row)])
  end.

Fixpoint audit_frontier_live_filter {V E} (EV : encoding V) (g : Graph.t V E)
    (live : FinSet.t V) (edges : list E) : list E * list (audit_frontier_call V E) :=
  match edges with
  | [] => ([], [AuditFrontierCase 12])
  | e :: rest => let source := Graph.source g e in let keep := FinSet.mem EV source live in
      let '(later, events) := audit_frontier_live_filter EV g live rest in
      (if keep then e :: later else later, AuditFrontierCase 13 :: AuditFrontierSource e source ::
        AuditFrontierMem source live keep :: AuditFrontierCase (if keep then 14 else 15) :: events)
  end.

Fixpoint audit_frontier_targets {V E} (g : Graph.t V E) (e : E) (vertices : list V)
    : list (V * V) * list (audit_frontier_call V E) :=
  match vertices with
  | [] => ([], [AuditFrontierCase 16])
  | v :: rest => let target := Graph.target g e in let '(later, events) := audit_frontier_targets g
  e rest in
      ((v, target) :: later, AuditFrontierCase 17 :: AuditFrontierTarget e target :: events)
  end.

Fixpoint audit_frontier_edge_events {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (t : dom_tree V) (edges : list E)
    : list (V * V) * list (audit_frontier_call V E) :=
  match edges with
  | [] => ([], [AuditFrontierCase 18])
  | e :: rest => let source := Graph.source g e in let target := Graph.target g e in
      let stop := Map.get EV target (idom t) in
      let '(chain, walk_events) := audit_frontier_runner_counted p t source stop in
      let '(pairs, pair_events) := audit_frontier_targets g e chain in
      let '(later, events) := audit_frontier_edge_events p t rest in
      (pairs ++ later, AuditFrontierCase 19 :: AuditFrontierSource e source :: AuditFrontierTarget e
  target ::
        AuditFrontierParent target (idom t) stop :: walk_events ++ pair_events ++ events ++
        [AuditFrontierOutput (length pairs)])
  end.

Fixpoint audit_frontier_rows_counted {V E} (EV : encoding V) (pairs : list (V * V))
    (rows : Map.t V (FinSet.t V)) : Map.t V (FinSet.t V) * list (audit_frontier_call V E) :=
  match pairs with
  | [] => (rows, [AuditFrontierCase 20])
  | (d, n) :: rest => let found := Map.get EV d rows in
      let old := match found with Some s => s | None => FinSet.empty end in
      let row := FinSet.add EV n old in let next := Map.set EV d row rows in
      let '(result, events) := audit_frontier_rows_counted EV rest next in
      (result, AuditFrontierCase 21 :: AuditFrontierGet d rows found :: AuditFrontierSetMember n old
  ::
        AuditFrontierSetRow d row rows :: events)
  end.

Definition audit_frontier_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (t : dom_tree V) : Map.t V (FinSet.t V) * list (audit_frontier_call V E) :=
  let '(search, dfs_events) := audit_dfs_full_counted p FinSet.empty (Graph.entries g) in
  let '(incoming, pred_events) := audit_frontier_collect_pred p (Graph.nodes g) in
  let '(live_edges, filter_events) := audit_frontier_live_filter EV g (visited search) incoming in
  let '(pairs, pair_events) := audit_frontier_edge_events p t live_edges in
  let '(result, row_events) := audit_frontier_rows_counted EV pairs Map.empty in
  (result, map AuditFrontierDfs dfs_events ++ pred_events ++ filter_events ++ pair_events ++
  row_events).

Definition audit_frontier_input_edges {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) : list E := flat_map (pred_edges p) (Graph.nodes g).

Definition audit_frontier_input_width {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (t : dom_tree V) : nat :=
  let edges := audit_frontier_input_edges p in let parent_rows := Map.elements (idom t) in
  let vertices := Graph.nodes g ++ Graph.entries g ++ map (Graph.source g) edges ++ map
  (Graph.target g) edges ++
    map fst parent_rows ++ map snd parent_rows ++ map fst (Map.elements (tin t)) ++ map fst
  (Map.elements (tout t)) in
  let numbers := map snd (Map.elements (tin t)) ++ map snd (Map.elements (tout t)) in
  let callback_width := fold_right Nat.max 0 (map (fun v => audit_key_bits_weight (encode EV v))
  vertices) in
  Nat.max (audit_dfs_full_input_width EV g p (Graph.entries g))
    (Nat.max callback_width (Nat.max (fold_right Nat.max 0 (map audit_key_bits_weight numbers))
      (audit_key_bits_weight (Pos.of_succ_nat (2 + length (Graph.entries g) * S (Pos.to_nat (fuel
  p))))))).

Definition audit_frontier_input_event_bound {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) : nat :=
  let nodes := length (Graph.nodes g) in let edges := length (audit_frontier_input_edges p) in
  let f := S (Pos.to_nat (fuel p)) in
  100 * S (nodes + edges) * f * f + audit_dfs_full_input_event_bound p (Graph.entries g).

Definition audit_frontier_input_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (t : dom_tree V) : nat :=
  let count := audit_frontier_input_event_bound p in let width := audit_frontier_input_width EV g p
  t in
  1024 * S count * S count + count * (512 + 24 * width).

Definition audit_frontier_counted_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) t,
    let '(result, events) := audit_frontier_counted p t in
    result = dominance_frontier p t /\ length events <= audit_frontier_input_event_bound p /\
    audit_frontier_model_work EV events <= audit_frontier_input_budget EV g p t.


From Galois.Graph Require Import GraphFrontier.

Inductive audit_ifrontier_body (V : Type) : Type :=
| AuditIfCase (site : nat)
| AuditIfGet (v : V) (m : Map.t V (FinSet.t V)) (result : option (FinSet.t V))
| AuditIfElements (set : FinSet.t V) (result : list V)
| AuditIfMap (size : nat)
| AuditIfTarget (v : V)
| AuditIfEncode (v : V) (code : positive).
Arguments AuditIfCase {V} _.
Arguments AuditIfGet {V} _ _ _.
Arguments AuditIfElements {V} _ _.
Arguments AuditIfMap {V} _.
Arguments AuditIfTarget {V} _.
Arguments AuditIfEncode {V} _ _.

Definition audit_ifrontier_successors_counted {V} (EV : encoding V) (df : Map.t V (FinSet.t V)) (v :
  V)
    : list V * list (audit_ifrontier_body V) :=
  let found := Map.get EV v df in
  match found with
  | None => ([], [AuditIfGet v df found; AuditIfCase 0])
  | Some set => let values := FinSet.elements set in
      (values, [AuditIfGet v df found; AuditIfCase 1; AuditIfElements set values])
  end.

Fixpoint audit_ifrontier_entries_counted {V} (EV : encoding V) (df : Map.t V (FinSet.t V)) (defs :
  list V)
    : list V * list (audit_ifrontier_body V) :=
  match defs with
  | [] => ([], [AuditIfCase 2])
  | v :: rest => let '(first, here) := audit_ifrontier_successors_counted EV df v in
      let '(later, events) := audit_ifrontier_entries_counted EV df rest in
      (first ++ later, AuditIfCase 3 :: here ++ events ++ [AuditIfMap (length first)])
  end.

Definition audit_ifrontier_out_counted {V} (EV : encoding V) (df : Map.t V (FinSet.t V)) (v : V)
    : list (V * V) * list (audit_ifrontier_body V) :=
  let '(values, events) := audit_ifrontier_successors_counted EV df v in
  (map (fun n => (v, n)) values, events ++ [AuditIfMap (length values)]).

Definition audit_ifrontier_target_counted {V} (edge : V * V) : V * list (audit_ifrontier_body V) :=
  (snd edge, [AuditIfTarget (snd edge)]).

Definition audit_ifrontier_encode_counted {V} (EV : encoding V) (v : V) : positive * list
  (audit_ifrontier_body V) :=
  let code := encode EV v in (code, [AuditIfEncode v code]).

Definition audit_ifrontier_prepare_callbacks {V} (EV : encoding V) (df : Map.t V (FinSet.t V))
    : audit_prepare_callback_model V (V * V) (audit_ifrontier_body V) :=
  AuditPrepareCallbackModel _ _ _ (audit_ifrontier_out_counted EV df)
    audit_ifrontier_target_counted (audit_ifrontier_encode_counted EV).

Definition audit_ifrontier_dfs_callbacks {V} (EV : encoding V)
    : audit_dfs_callback_model V (V * V) (audit_ifrontier_body V) :=
  AuditDfsCallbackModel _ _ _ audit_ifrontier_target_counted (audit_ifrontier_encode_counted EV).

Definition audit_ifrontier_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (df : Map.t V (FinSet.t V)) (defs : list V) :=
  let '(entries, entry_events) := audit_ifrontier_entries_counted EV df defs in
  let fg := Graph.Make entries (Graph.nodes g)
    (fun v => map (fun n => (v, n)) (frontier_successors EV df v)) fst snd in
  let '(fp, prep_events) := audit_graph_prepare_nested_counted EV fg
  (audit_ifrontier_prepare_callbacks EV df) in
  let '(search, dfs_events) := audit_dfs_nested_counted fp (audit_ifrontier_dfs_callbacks EV)
  FinSet.empty entries in
  (visited search, (entry_events, (prep_events, dfs_events))).

Definition audit_ifrontier_body_work {V} (EV : encoding V) (event : audit_ifrontier_body V) : nat :=
  64 + match event with
  | AuditIfGet v _ _ => audit_encoding_weight (audit_key_bits_weight (encode EV v)) +
  audit_get_weight (encode EV v)
  | AuditIfElements set _ => 64 * Nat.pow (S (audit_erase_nodes set)) 3
  | AuditIfMap size => S size
  | AuditIfEncode _ code => audit_encoding_weight (audit_key_bits_weight code)
  | _ => 0 end.

Definition audit_ifrontier_work {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (df : Map.t V (FinSet.t V)) (defs : list V) : nat :=
  let '(_, (entry_events, (prep_events, dfs_events))) := audit_ifrontier_counted p df defs in
  fold_right (fun event n => audit_ifrontier_body_work EV event + n) 0 entry_events +
    audit_graph_prepare_nested_total_work (audit_ifrontier_body_work EV) prep_events +
    audit_dfs_nested_total_work EV (audit_ifrontier_body_work EV) dfs_events.

Definition audit_ifrontier_scale {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (df : Map.t V (FinSet.t V)) (defs : list V) : nat :=
  1 + length (Graph.nodes g) + length defs + audit_erase_nodes df +
    fold_right (fun row n => audit_erase_nodes (snd row) + n) 0 (Map.elements df).

Definition audit_ifrontier_width {V E} (EV : encoding V) (g : Graph.t V E)
    (df : Map.t V (FinSet.t V)) (defs : list V) : nat :=
  let rows := Map.elements df in
  let vertices := Graph.nodes g ++ defs ++ map fst rows ++ flat_map (fun row => FinSet.elements (snd
  row)) rows in
  fold_right Nat.max 0 (map (fun v => audit_key_bits_weight (encode EV v)) vertices).

Definition audit_ifrontier_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (df : Map.t V (FinSet.t V)) (defs : list V) : nat :=
  let scale := audit_ifrontier_scale p df defs in let width := audit_ifrontier_width EV g df defs in
  8192 * Nat.pow (S scale) 12 * Nat.pow (S width) 2.

Definition audit_ifrontier_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) df defs,
    fst (audit_ifrontier_counted p df defs) = iterated_frontier p df defs /\
    audit_ifrontier_work p df defs <= audit_ifrontier_budget EV g p df defs.

From Galois.Collections Require Import CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditCompare.
Record audit_frontier_source_callbacks (V E B : Type) : Type := AuditFrontierSourceCallbacks {
  audit_frontier_source_encode : V -> positive * list B;
  audit_frontier_source_source : E -> V * list B;
  audit_frontier_source_target : E -> V * list B
}.
Arguments audit_frontier_source_encode {V E B} _ _.
Arguments audit_frontier_source_source {V E B} _ _.
Arguments audit_frontier_source_target {V E B} _ _.

Inductive audit_frontier_source_event (V E B : Type) : Type :=
| FrontierSourceCase : nat -> audit_frontier_source_event V E B
| FrontierSourceDfs : audit_dfs_nested_event V E (audit_graph_callback_capture V E B) ->
  audit_frontier_source_event V E B
| FrontierSourceSource : E -> V -> list B -> audit_frontier_source_event V E B
| FrontierSourceTarget : E -> V -> list B -> audit_frontier_source_event V E B
| FrontierSourceParent : audit_map_event V V B -> audit_frontier_source_event V E B
| FrontierSourceRank : audit_map_event V positive B -> audit_frontier_source_event V E B
| FrontierSourcePred : audit_map_event V (list E) B -> audit_frontier_source_event V E B
| FrontierSourceRows : audit_map_event V (FinSet.t V) B -> audit_frontier_source_event V E B
| FrontierSourceSet : audit_set_event V B -> audit_frontier_source_event V E B
| FrontierSourceCompare : positive -> positive -> bool -> list audit_positive_compare_event ->
  audit_frontier_source_event V E B
| FrontierSourceOutput : nat -> audit_frontier_source_event V E B.
Arguments FrontierSourceCase {V E B} _.
Arguments FrontierSourceDfs {V E B} _.
Arguments FrontierSourceSource {V E B} _ _ _.
Arguments FrontierSourceTarget {V E B} _ _ _.
Arguments FrontierSourceParent {V E B} _.
Arguments FrontierSourceRank {V E B} _.
Arguments FrontierSourcePred {V E B} _.
Arguments FrontierSourceRows {V E B} _.
Arguments FrontierSourceSet {V E B} _.
Arguments FrontierSourceCompare {V E B} _ _ _ _.
Arguments FrontierSourceOutput {V E B} _.

Definition audit_frontier_source_dom {V E B} (enc : V -> positive * list B) (t : dom_tree V) (d n :
  V)
    : bool * list (audit_frontier_source_event V E B) :=
  let '(a, ea) := audit_map_get enc d (tin t) in
  match a with None => (false, map FrontierSourceRank ea) | Some av =>
    let '(b, eb) := audit_map_get enc n (tin t) in
    match b with None => (false, map FrontierSourceRank (ea ++ eb)) | Some bv =>
      let '(c, ec) := audit_map_get enc d (tout t) in
      match c with None => (false, map FrontierSourceRank (ea ++ eb ++ ec)) | Some cv =>
        let '(z, ez) := audit_map_get enc n (tout t) in
        match z with None => (false, map FrontierSourceRank (ea ++ eb ++ ec ++ ez)) | Some zv =>
          let '(first, ef) := audit_positive_leb av bv in let '(second, es) := audit_positive_leb zv
  cv in
          (first && second, map FrontierSourceRank (ea ++ eb ++ ec ++ ez) ++
            [FrontierSourceCompare av bv first ef; FrontierSourceCompare zv cv second es])
        end
      end
    end
  end.

Definition audit_frontier_source_step {V E B} (enc : V -> positive * list B) (t : dom_tree V)
    (stop : option V) (state : option V * list V) : (option V * list V) * list
  (audit_frontier_source_event V E B) :=
  let '(current, seen) := state in
  match current with
  | None => ((None, seen), [FrontierSourceCase 0])
  | Some v => let '(blocked, details) := match stop with
      | None => (false, []) | Some q => audit_frontier_source_dom enc t v q end in
      if blocked then ((None, seen), FrontierSourceCase 1 :: details ++ [FrontierSourceCase 2])
      else let '(parent, reads) := audit_map_get enc v (idom t) in
        ((parent, v :: seen), FrontierSourceCase 1 :: details ++ [FrontierSourceCase 3] ++ map
  FrontierSourceParent reads)
  end.

Fixpoint audit_frontier_source_walk {V E B} (enc : V -> positive * list B) (t : dom_tree V)
    (stop : option V) (fuel : positive) (state : option V * list V)
    : (option V * list V) * list (audit_frontier_source_event V E B) :=
  match fst state with
  | None => (state, [FrontierSourceCase 4])
  | Some _ => match fuel with
    | xH => let '(result, events) := audit_frontier_source_step enc t stop state in (result,
  FrontierSourceCase 5 :: events)
    | xO rest => let '(middle, first) := audit_frontier_source_walk enc t stop rest state in
        let '(result, second) := audit_frontier_source_walk enc t stop rest middle in (result,
  FrontierSourceCase 6 :: first ++ second)
    | xI rest => let '(middle, first) := audit_frontier_source_walk enc t stop rest state in
        let '(last, second) := audit_frontier_source_walk enc t stop rest middle in
        let '(result, events) := audit_frontier_source_step enc t stop last in (result,
  FrontierSourceCase 7 :: first ++ second ++ events)
    end
  end.

Fixpoint audit_frontier_source_incoming {V E B} {EV : encoding V} {g : Graph.t V E}
    (enc : V -> positive * list B) (p : prepared EV g) (nodes : list V)
    : list E * list (audit_frontier_source_event V E B) :=
  match nodes with
  | [] => ([], [FrontierSourceCase 10])
  | v :: rest => let '(found, reads) := audit_map_get enc v (in_index p) in
      let row := match found with Some xs => xs | None => [] end in
      let '(later, events) := audit_frontier_source_incoming enc p rest in
      (row ++ later, FrontierSourceCase 11 :: map FrontierSourcePred reads ++ events ++
  [FrontierSourceOutput (length row)])
  end.

Fixpoint audit_frontier_source_filter {V E B} (cb : audit_frontier_source_callbacks V E B)
    (live : FinSet.t V) (edges : list E) : list E * list (audit_frontier_source_event V E B) :=
  match edges with
  | [] => ([], [FrontierSourceCase 12])
  | edge :: rest => let '(vertex, body) := audit_frontier_source_source cb edge in
      let '(keep, reads) := audit_finset_mem (audit_frontier_source_encode cb) vertex live in
      let '(later, events) := audit_frontier_source_filter cb live rest in
      (if keep then edge :: later else later, [FrontierSourceCase 13; FrontierSourceSource edge
  vertex body] ++
        map FrontierSourceSet reads ++ [FrontierSourceCase (if keep then 14 else 15)] ++ events)
  end.

Fixpoint audit_frontier_source_targets {V E B} (cb : audit_frontier_source_callbacks V E B)
    (edge : E) (vertices : list V) : list (V * V) * list (audit_frontier_source_event V E B) :=
  match vertices with
  | [] => ([], [FrontierSourceCase 16])
  | v :: rest => let '(target, body) := audit_frontier_source_target cb edge in
      let '(later, events) := audit_frontier_source_targets cb edge rest in
      ((v, target) :: later, FrontierSourceCase 17 :: FrontierSourceTarget edge target body ::
  events)
  end.

Fixpoint audit_frontier_source_edges {V E B} {EV : encoding V} {g : Graph.t V E}
    (cb : audit_frontier_source_callbacks V E B) (p : prepared EV g) (t : dom_tree V) (edges : list
  E)
    : list (V * V) * list (audit_frontier_source_event V E B) :=
  match edges with
  | [] => ([], [FrontierSourceCase 18])
  | edge :: rest => let '(source, sb) := audit_frontier_source_source cb edge in
      let '(target, tb) := audit_frontier_source_target cb edge in
      let '(stop, reads) := audit_map_get (audit_frontier_source_encode cb) target (idom t) in
      let '(walk, we) := audit_frontier_source_walk (audit_frontier_source_encode cb) t stop (fuel
  p) (Some source, []) in
      let '(pairs, pe) := audit_frontier_source_targets cb edge (snd walk) in
      let '(later, events) := audit_frontier_source_edges cb p t rest in
      (pairs ++ later, [FrontierSourceCase 19; FrontierSourceSource edge source sb;
  FrontierSourceTarget edge target tb] ++
        map FrontierSourceParent reads ++ we ++ pe ++ events ++ [FrontierSourceOutput (length
  pairs)])
  end.

Fixpoint audit_frontier_source_rows {V E B} (enc : V -> positive * list B) (pairs : list (V * V))
    (rows : Map.t V (FinSet.t V)) : Map.t V (FinSet.t V) * list (audit_frontier_source_event V E B)
  :=
  match pairs with
  | [] => (rows, [FrontierSourceCase 20])
  | (d, n) :: rest => let '(found, reads) := audit_map_get enc d rows in
      let old := match found with Some s => s | None => FinSet.empty end in
      let '(row, adds) := audit_finset_add enc n old in let '(next, writes) := audit_map_set enc d
  row rows in
      let '(result, events) := audit_frontier_source_rows enc rest next in
      (result, FrontierSourceCase 21 :: map FrontierSourceRows reads ++ map FrontierSourceSet adds
  ++ map FrontierSourceRows writes ++ events)
  end.

Definition audit_frontier_source_counted {V E B} {EV : encoding V} {g : Graph.t V E}
    (cb : audit_frontier_source_callbacks V E B) (p : prepared EV g) (t : dom_tree V)
    : Map.t V (FinSet.t V) * list (audit_frontier_source_event V E B) :=
  let dfs_cb := AuditDfsCallbackModel V E B (audit_frontier_source_target cb)
  (audit_frontier_source_encode cb) in
  let '(search, dfs_events) := audit_dfs_source_counted p dfs_cb FinSet.empty (Graph.entries g) in
  let '(incoming, pred_events) := audit_frontier_source_incoming (audit_frontier_source_encode cb) p
  (Graph.nodes g) in
  let '(live, filter_events) := audit_frontier_source_filter cb (visited search) incoming in
  let '(pairs, pair_events) := audit_frontier_source_edges cb p t live in
  let '(result, row_events) := audit_frontier_source_rows (audit_frontier_source_encode cb) pairs
  Map.empty in
  (result, map FrontierSourceDfs dfs_events ++ pred_events ++ filter_events ++ pair_events ++
  row_events).

Definition audit_frontier_source_callbacks_erase {V E B} (EV : encoding V) (g : Graph.t V E)
    (cb : audit_frontier_source_callbacks V E B) : Prop :=
  (forall v, fst (audit_frontier_source_encode cb v) = encode EV v) /\
  (forall e, fst (audit_frontier_source_source cb e) = Graph.source g e) /\
  (forall e, fst (audit_frontier_source_target cb e) = Graph.target g e).

Definition audit_frontier_source_event_work {V E B} (weight : B -> nat)
    (event : audit_frontier_source_event V E B) : nat :=
  let body := fun events => fold_right (fun item n => weight item + n) 0 events in
  64 + match event with
  | FrontierSourceDfs item => audit_dfs_source_event_work weight item
  | FrontierSourceSource _ _ events | FrontierSourceTarget _ _ events => body events
  | FrontierSourceParent item => audit_map_source_work body [item]
  | FrontierSourceRank item => audit_map_source_work body [item]
  | FrontierSourcePred item => audit_map_source_work body [item]
  | FrontierSourceRows item => audit_map_source_work body [item]
  | FrontierSourceSet item => audit_finset_source_work body [item]
  | FrontierSourceCompare _ _ _ events => audit_positive_order_source_work events
  | FrontierSourceOutput n => S n
  | FrontierSourceCase _ => 0
  end.

Definition audit_frontier_source_body_event_work {V E B} (weight : B -> nat)
    (event : audit_frontier_source_event V E B) : nat :=
  match event with
  | FrontierSourceDfs item => audit_dfs_source_body_work weight [item]
  | FrontierSourceSource _ _ body | FrontierSourceTarget _ _ body |
    FrontierSourceParent (AuditMapGet _ _ _ _ body _) | FrontierSourceParent (AuditMapSet _ _ _ _ _
  body _) |
    FrontierSourceParent (AuditMapRemove _ _ _ _ body _) | FrontierSourceRank (AuditMapGet _ _ _ _
  body _) |
    FrontierSourceRank (AuditMapSet _ _ _ _ _ body _) | FrontierSourceRank (AuditMapRemove _ _ _ _
  body _) |
    FrontierSourcePred (AuditMapGet _ _ _ _ body _) | FrontierSourcePred (AuditMapSet _ _ _ _ _ body
  _) |
    FrontierSourcePred (AuditMapRemove _ _ _ _ body _) | FrontierSourceRows (AuditMapGet _ _ _ _
  body _) |
    FrontierSourceRows (AuditMapSet _ _ _ _ _ body _) | FrontierSourceRows (AuditMapRemove _ _ _ _
  body _) |
    FrontierSourceSet (AuditSetMem _ _ _ _ body _) | FrontierSourceSet (AuditSetAdd _ _ _ _ body _)
  |
    FrontierSourceSet (AuditSetRemove _ _ _ _ body _) => fold_right (fun item n => weight item + n)
  0 body
  | FrontierSourceSet (AuditSetFold _ _) | FrontierSourceCompare _ _ _ _ |
    FrontierSourceOutput _ | FrontierSourceCase _ => 0
  end.

Definition audit_frontier_source_work {V E B} (weight : B -> nat)
    (events : list (audit_frontier_source_event V E B)) : nat :=
  fold_right (fun item n => audit_frontier_source_event_work weight item + n) 0 events.

Definition audit_frontier_source_body_work {V E B} (weight : B -> nat)
    (events : list (audit_frontier_source_event V E B)) : nat :=
  fold_right (fun item n => audit_frontier_source_body_event_work weight item + n) 0 events.

Definition audit_frontier_source_input_edges {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) : list E := flat_map (pred_edges p) (Graph.nodes g).

Definition audit_frontier_source_input_width {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (t : dom_tree V) : nat :=
  let edges := audit_frontier_source_input_edges p in let parents := Map.elements (idom t) in
  let vertices := Graph.nodes g ++ Graph.entries g ++ map (Graph.source g) edges ++ map
  (Graph.target g) edges ++
    map fst parents ++ map snd parents ++ map fst (Map.elements (tin t)) ++ map fst (Map.elements
  (tout t)) in
  let numbers := map snd (Map.elements (tin t)) ++ map snd (Map.elements (tout t)) in
  Nat.max (audit_dfs_full_input_width EV g p (Graph.entries g))
    (Nat.max (fold_right Nat.max 0 (map (fun v => Pos.size_nat (encode EV v)) vertices))
      (Nat.max (fold_right Nat.max 0 (map Pos.size_nat numbers))
        (Pos.size_nat (Pos.of_succ_nat (2 + length (Graph.entries g) * S (Pos.to_nat (fuel p))))))).

Definition audit_frontier_source_input_event_bound {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) : nat :=
  let size := length (Graph.nodes g) + length (audit_frontier_source_input_edges p) in
  let f := S (Pos.to_nat (fuel p)) in
  1024 * S size * f * f + audit_dfs_full_input_event_bound p (Graph.entries g).

Definition audit_frontier_source_input_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (t : dom_tree V) : nat :=
  let count := audit_frontier_source_input_event_bound p in
  let width := audit_frontier_source_input_width EV g p t in
  1024 * S count * S count + count * (1024 + 128 * width).

Definition audit_frontier_source_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) (t : dom_tree V)
    (cb : audit_frontier_source_callbacks V E B) (weight : B -> nat),
    audit_frontier_source_callbacks_erase EV g cb ->
    let '(result, events) := audit_frontier_source_counted cb p t in
    result = dominance_frontier p t /\ length events <= audit_frontier_source_input_event_bound p /\
    audit_frontier_source_work weight events <=
      audit_frontier_source_input_budget EV g p t + audit_frontier_source_body_work weight events.
```

## Galois.Graph.GraphAuditFrontierAdapter

Card: AUD-GR-MODELS

Source destination: `theories/Graph/GraphAuditFrontierAdapter.v`.

```rocq
(** * Dominance-frontier source adapters

    Frontier work uses source, target and encoder budgets at each actual invocation.
    For example, a missing rank map entry still retains the encoder call that found it.
    Builds on: graph DFS and frontier source models. *)
From Stdlib Require Import List.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditMap CollectionsAuditFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDominators GraphFrontier GraphAuditBase
  GraphAuditDfs
  GraphAuditFrontier.

(** Each frontier event chooses the budget for its recorded client callback input. *)
Definition audit_frontier_adapter_event_budget {V E B} (encode_budget : V -> nat)
    (target_budget source_budget : E -> nat) (event : audit_frontier_source_event V E B) : nat :=
  match event with
  | FrontierSourceDfs (_, calls) => fold_right (fun call n => match call with
      | AuditGraphEncodeCapture _ _ _ v _ _ => encode_budget v + n
      | AuditGraphTargetCapture _ _ _ e _ _ => target_budget e + n end) 0 calls
  | FrontierSourceSource e _ _ => source_budget e
  | FrontierSourceTarget e _ _ => target_budget e
  | FrontierSourceParent (AuditMapGet v _ _ _ _ _) | FrontierSourceParent (AuditMapSet v _ _ _ _ _
  _) |
    FrontierSourceParent (AuditMapRemove v _ _ _ _ _) | FrontierSourceRank (AuditMapGet v _ _ _ _ _)
  |
    FrontierSourceRank (AuditMapSet v _ _ _ _ _ _) | FrontierSourceRank (AuditMapRemove v _ _ _ _ _)
  |
    FrontierSourcePred (AuditMapGet v _ _ _ _ _) | FrontierSourcePred (AuditMapSet v _ _ _ _ _ _) |
    FrontierSourcePred (AuditMapRemove v _ _ _ _ _) | FrontierSourceRows (AuditMapGet v _ _ _ _ _) |
    FrontierSourceRows (AuditMapSet v _ _ _ _ _ _) | FrontierSourceRows (AuditMapRemove v _ _ _ _ _)
  |
    FrontierSourceSet (AuditSetAdd v _ _ _ _ _) | FrontierSourceSet (AuditSetMem v _ _ _ _ _) |
    FrontierSourceSet (AuditSetRemove v _ _ _ _ _) => encode_budget v
  | _ => 0
  end.

(** The complete frontier producer applies each source law at the captured call. *)
Definition audit_frontier_source_adapted_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) (t : dom_tree V)
    (cb : audit_frontier_source_callbacks V E B) (weight : B -> nat)
    encode_source target_source source_source encode_budget target_budget source_budget,
    audit_frontier_source_callbacks_erase EV g cb ->
    audit_graph_external_callback_adapter (audit_frontier_source_encode cb) weight encode_source
  encode_budget ->
    audit_graph_external_callback_adapter (audit_frontier_source_target cb) weight target_source
  target_budget ->
    audit_graph_external_callback_adapter (audit_frontier_source_source cb) weight source_source
  source_budget ->
    let '(result, events) := audit_frontier_source_counted cb p t in
    result = dominance_frontier p t /\
    audit_frontier_source_work weight events <= audit_frontier_source_input_budget EV g p t +
      fold_right (fun event n => audit_frontier_adapter_event_budget encode_budget target_budget
  source_budget event + n)
        0 events.
```

## Galois.Graph.GraphAuditIdf

Card: AUD-GR-MODELS

Source destination: `theories/Graph/GraphAuditIdf.v`.

```rocq
(** * Direct IDF source contracts

    Record the actual forest preparation, priority queue, traversal and callback costs.
    For example, a pruned self-loop still records its live-predicate invocation.
    Builds on: graph audit components, collection source models and binary arithmetic. *)
From Stdlib Require Import List Bool PArith NArith ZArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsHeap
  CollectionsTrie CollectionsAuditCost CollectionsAuditQueue CollectionsAuditEncoding
  CollectionsAuditMap
  CollectionsAuditFinSet CollectionsAuditElements CollectionsAuditTrie CollectionsAuditPrimitive
  CollectionsAuditCompare CollectionsAuditPositiveSub CollectionsAuditNAdd.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphDominators GraphFrontier
  GraphIdf
  GraphAuditBase GraphAuditDfs GraphAuditDominators GraphAuditFrontier.
Import List.ListNotations.

(** A captured traversal callback is priced at its actual client input. *)
Definition audit_idf_capture_budget {V E B} (encode_budget : V -> nat) (target_budget : E -> nat)
    (event : audit_graph_callback_capture V E B) : nat :=
  match event with
  | AuditGraphEncodeCapture _ _ _ v _ _ => encode_budget v
  | AuditGraphTargetCapture _ _ _ e _ _ => target_budget e
  end.


Inductive audit_idf_collect_call (V E : Type) : Type :=
| AuditIdfCollectCase (site : nat)
| AuditIdfCollectTarget (e : E) (v : V)
| AuditIdfCollectParent (v : V) (m : Map.t V V) (result : option V)
| AuditIdfCollectDom (event : audit_frontier_dom_call V)
| AuditIdfCollectLive (v : V) (result : bool)
| AuditIdfCollectOut (v : V) (m : Map.t V (list E)) (result : option (list E))
| AuditIdfCollectSucc (before after : N).
Arguments AuditIdfCollectCase {V E} _.
Arguments AuditIdfCollectTarget {V E} _ _.
Arguments AuditIdfCollectParent {V E} _ _ _.
Arguments AuditIdfCollectDom {V E} _.
Arguments AuditIdfCollectLive {V E} _ _.
Arguments AuditIdfCollectOut {V E} _ _ _.
Arguments AuditIdfCollectSucc {V E} _ _.

Definition audit_idf_join_counted {V E} (EV : encoding V) (g : Graph.t V E) (t : dom_tree V)
    (live : V -> bool) (root : V) (edge : E) : bool * list (audit_idf_collect_call V E) :=
  let first := Graph.target g edge in let stop := Map.get EV first (idom t) in
  let '(blocked, dom_events) := match stop with
    | None => (false, []) | Some q => audit_frontier_dom_counted EV t root q end in
  let second := Graph.target g edge in let live_result := live second in
  (negb blocked && live_result, [AuditIdfCollectTarget edge first; AuditIdfCollectParent first (idom
  t) stop] ++
    map AuditIdfCollectDom dom_events ++ [AuditIdfCollectTarget edge second; AuditIdfCollectLive
  second live_result]).

Definition audit_idf_edge_counted {V E} (EV : encoding V) (g : Graph.t V E) (t : dom_tree V)
    (live : V -> bool) (root : V) (acc : list V * N) (edge : E)
    : (list V * N) * list (audit_idf_collect_call V E) :=
  let '(join, events) := audit_idf_join_counted EV g t live root edge in
  let '(values, target_events) := if join then let target := Graph.target g edge in
    (target :: fst acc, [AuditIdfCollectCase 0; AuditIdfCollectTarget edge target])
    else (fst acc, [AuditIdfCollectCase 1]) in
  let next := N.succ (snd acc) in
  ((values, next), events ++ target_events ++ [AuditIdfCollectSucc (snd acc) next]).

Fixpoint audit_idf_edges_counted {V E} (EV : encoding V) (g : Graph.t V E) (t : dom_tree V)
    (live : V -> bool) (root : V) (edges : list E) (acc : list V * N)
    : (list V * N) * list (audit_idf_collect_call V E) :=
  match edges with
  | [] => (acc, [AuditIdfCollectCase 2])
  | edge :: rest => let '(middle, here) := audit_idf_edge_counted EV g t live root acc edge in
      let '(result, later) := audit_idf_edges_counted EV g t live root rest middle in
      (result, AuditIdfCollectCase 3 :: here ++ later)
  end.

Fixpoint audit_idf_nodes_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (t : dom_tree V) (live : V -> bool) (root : V)
    (nodes : list V) (acc : list V * N) : (list V * N) * list (audit_idf_collect_call V E) :=
  match nodes with
  | [] => (acc, [AuditIdfCollectCase 4])
  | v :: rest => let found := Map.get EV v (out_index p) in
      let edges := match found with Some xs => xs | None => [] end in
      let '(middle, here) := audit_idf_edges_counted EV g t live root edges acc in
      let '(result, later) := audit_idf_nodes_counted p t live root rest middle in
      (result, AuditIdfCollectCase 5 :: AuditIdfCollectOut v (out_index p) found :: here ++ later)
  end.

Definition audit_idf_collect_event_work {V E} (EV : encoding V) (event : audit_idf_collect_call V E)
  : nat :=
  64 + match event with
  | AuditIdfCollectParent v _ _ | AuditIdfCollectOut v _ _ =>
      audit_encoding_weight (audit_key_bits_weight (encode EV v)) + audit_get_weight (encode EV v)
  | AuditIdfCollectDom inner => audit_frontier_dom_event_work EV inner
  | AuditIdfCollectSucc before _ => audit_binary_weight (Z.of_N before) 1
  | _ => 0 end.

Definition audit_idf_collect_work {V E} (EV : encoding V) (events : list (audit_idf_collect_call V
  E)) : nat :=
  256 * S (length events) * S (length events) +
    fold_right (fun event total => audit_idf_collect_event_work EV event + total) 0 events.

Definition audit_idf_collect_edges {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (nodes : list V) : list E := flat_map (succ_edges p) nodes.

Definition audit_idf_collect_event_bound {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (nodes : list V) : nat :=
  8 + 4 * length nodes + 32 * length (audit_idf_collect_edges p nodes).

Definition audit_idf_collect_width {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (t : dom_tree V) (root : V) (nodes : list V) (visits : N) : nat :=
  let edge_targets := map (Graph.target g) (audit_idf_collect_edges p nodes) in
  Nat.max (audit_frontier_runner_width EV t root None)
    (Nat.max (fold_right Nat.max 0 (map (fun v => audit_key_bits_weight (encode EV v)) (nodes ++
  edge_targets)))
      (audit_z_bits (Z.of_N (N.add visits (N.of_nat (length edge_targets)))))).

Definition audit_idf_collect_budget {V E} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (t : dom_tree V) (root : V) (nodes : list V) (visits : N) : nat :=
  let count := audit_idf_collect_event_bound p nodes in let width := audit_idf_collect_width EV g p
  t root nodes visits in
  512 * S count * S count + count * (256 + 12 * width).

Definition audit_idf_collect_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) (t : dom_tree V)
      live root nodes acc,
    let '(result, events) := audit_idf_nodes_counted p t live root nodes acc in
    result = fold_left (idf_collect_node p t live root) nodes acc /\
    length events <= audit_idf_collect_event_bound p nodes /\
    audit_idf_collect_work EV events <= audit_idf_collect_budget EV g p t root nodes (snd acc).


Inductive audit_idf_seed_call (V : Type) : Type :=
| AuditIdfSeedCase (site : nat)
| AuditIdfSeedGet (v : V) (m : Map.t V positive) (result : option positive)
| AuditIdfSeedSub (ceiling rank result : positive)
| AuditIdfSeedPush (priority : positive) (v : V) (before after : PQueue.t V) (events : list
  (queue_event V)).
Arguments AuditIdfSeedCase {V} _.
Arguments AuditIdfSeedGet {V} _ _ _.
Arguments AuditIdfSeedSub {V} _ _ _.
Arguments AuditIdfSeedPush {V} _ _ _ _ _.

Definition audit_idf_seed_counted {V} (EV : encoding V) (ceiling : positive)
    (levels : Map.t V positive) (queue : PQueue.t V) (v : V) : PQueue.t V * list
  (audit_idf_seed_call V) :=
  let found := Map.get EV v levels in
  match found with
  | None => (queue, [AuditIdfSeedGet v levels found; AuditIdfSeedCase 0])
  | Some _ => let priority_found := Map.get EV v levels in
      let priority := match priority_found with Some rank => Pos.sub ceiling rank | None => ceiling
  end in
      let '(next, events) := queue_push EV priority v queue in
      (next, [AuditIdfSeedGet v levels found; AuditIdfSeedCase 1; AuditIdfSeedGet v levels
  priority_found] ++
        (match priority_found with Some rank => [AuditIdfSeedSub ceiling rank priority] | None => []
  end) ++
        [AuditIdfSeedPush priority v queue next events])
  end.

Fixpoint audit_idf_seeds_counted {V} (EV : encoding V) (ceiling : positive) (levels : Map.t V
  positive)
    (defs : list V) (queue : PQueue.t V) : PQueue.t V * list (audit_idf_seed_call V) :=
  match defs with
  | [] => (queue, [AuditIdfSeedCase 2])
  | v :: rest => let '(next, here) := audit_idf_seed_counted EV ceiling levels queue v in
      let '(result, later) := audit_idf_seeds_counted EV ceiling levels rest next in
      (result, AuditIdfSeedCase 3 :: here ++ later)
  end.

Definition audit_idf_initial_counted {V} (EV : encoding V) (ceiling : positive)
    (levels : Map.t V positive) (defs : list V) : IdfState.t V * list (audit_idf_seed_call V) :=
  let '(queue, events) := audit_idf_seeds_counted EV ceiling levels defs PQueue.empty in
  (IdfState.Make queue FinSet.empty FinSet.empty FinSet.empty [] 0%N 0%N, events).

Definition audit_idf_seed_event_work {V} (EV : encoding V) (event : audit_idf_seed_call V) : nat :=
  64 + match event with
  | AuditIdfSeedGet v _ _ => audit_encoding_weight (audit_key_bits_weight (encode EV v)) +
  audit_get_weight (encode EV v)
  | AuditIdfSeedSub ceiling rank _ => audit_binary_weight (Z.pos ceiling) (Z.pos rank)
  | AuditIdfSeedPush _ _ _ _ events => queue_model_work EV events
  | AuditIdfSeedCase _ => 0 end.

Definition audit_idf_initial_work {V} (EV : encoding V) (events : list (audit_idf_seed_call V)) :
  nat :=
  256 * S (length events) * S (length events) +
    fold_right (fun event total => audit_idf_seed_event_work EV event + total) 0 events.

Definition audit_idf_initial_width {V} (EV : encoding V) (ceiling : positive)
    (levels : Map.t V positive) (defs : list V) : nat :=
  Nat.max (audit_key_bits_weight ceiling)
    (Nat.max (fold_right Nat.max 0 (map (fun v => audit_key_bits_weight (encode EV v)) defs))
      (fold_right Nat.max 0 (map (fun row => audit_key_bits_weight (snd row)) (Map.elements
  levels)))).

Definition audit_idf_initial_budget {V} (EV : encoding V) (ceiling : positive)
    (levels : Map.t V positive) (defs : list V) : nat :=
  let n := S (length defs) in let width := S (audit_idf_initial_width EV ceiling levels defs) in
  4096 * Nat.pow n 6 * Nat.pow width 2.

Definition audit_idf_initial_statement : Prop :=
  forall V (EV : encoding V) ceiling levels defs,
    let '(result, events) := audit_idf_initial_counted EV ceiling levels defs in
    result = idf_initial EV ceiling levels defs /\ length events <= 1 + 6 * length defs /\
    audit_idf_initial_work EV events <= audit_idf_initial_budget EV ceiling levels defs.


Inductive audit_idf_work_call (V E : Type) : Type :=
| IdfWorkCase : nat -> audit_idf_work_call V E
| IdfWorkIsEmpty : PQueue.t V -> bool -> audit_idf_work_call V E
| IdfWorkPop : PQueue.t V -> option (positive * V * PQueue.t V) ->
    list (queue_event V) -> audit_idf_work_call V E
| IdfWorkPush : positive -> V -> PQueue.t V -> PQueue.t V ->
    list (queue_event V) -> audit_idf_work_call V E
| IdfWorkGet : V -> Map.t V positive -> option positive -> audit_idf_work_call V E
| IdfWorkMem : V -> FinSet.t V -> bool -> audit_idf_work_call V E
| IdfWorkAdd : V -> FinSet.t V -> FinSet.t V -> audit_idf_work_call V E
| IdfWorkDfs : list (audit_dfs_full_call V V) -> audit_idf_work_call V E
| IdfWorkCollect : list (audit_idf_collect_call V E) -> audit_idf_work_call V E
| IdfWorkSub : positive -> positive -> positive -> audit_idf_work_call V E
| IdfWorkArithmetic : N -> N -> N -> audit_idf_work_call V E.
Arguments IdfWorkCase {V E} _.
Arguments IdfWorkIsEmpty {V E} _ _.
Arguments IdfWorkPop {V E} _ _ _.
Arguments IdfWorkPush {V E} _ _ _ _ _.
Arguments IdfWorkGet {V E} _ _ _.
Arguments IdfWorkMem {V E} _ _ _.
Arguments IdfWorkAdd {V E} _ _ _.
Arguments IdfWorkDfs {V E} _.
Arguments IdfWorkCollect {V E} _.
Arguments IdfWorkSub {V E} _ _ _.
Arguments IdfWorkArithmetic {V E} _ _ _.

Definition audit_idf_emit_counted {V E} (EV : encoding V) ceiling
    (levels : Map.t V positive) (st : IdfState.t V) (v : V)
    : IdfState.t V * list (audit_idf_work_call V E) :=
  let processed := FinSet.mem EV v (IdfState.processed st) in
  let '(pending, queue_events) := if processed then (IdfState.pending st, []) else
    let found := Map.get EV v levels in
    let '(priority, subevents) := match found with
      | Some rank => let priority := Pos.sub ceiling rank in
          (priority, [IdfWorkSub ceiling rank priority])
      | None => (ceiling, []) end in
    let '(queue, events) := queue_push EV priority v (IdfState.pending st) in
    (queue, [IdfWorkGet v levels found] ++ subevents ++
      [IdfWorkPush priority v (IdfState.pending st) queue events]) in
  let emitted := FinSet.add EV v (IdfState.emitted st) in
  let was_emitted := FinSet.mem EV v (IdfState.emitted st) in
  let count := if was_emitted then IdfState.output_count st else N.succ (IdfState.output_count st)
  in
  (IdfState.Make pending emitted (IdfState.scanned st) (IdfState.processed st)
    (IdfState.trace st) (IdfState.edge_visits st) count,
    [IdfWorkMem v (IdfState.processed st) processed] ++ queue_events ++
    [IdfWorkAdd v (IdfState.emitted st) emitted;
     IdfWorkMem v (IdfState.emitted st) was_emitted] ++
    if was_emitted then [] else [IdfWorkArithmetic (IdfState.output_count st) 1%N count]).

Fixpoint audit_idf_emit_list_counted {V E} (EV : encoding V) ceiling
    (levels : Map.t V positive) (values : list V) (st : IdfState.t V)
    : IdfState.t V * list (audit_idf_work_call V E) :=
  match values with
  | [] => (st, [IdfWorkCase 0])
  | v :: rest => let '(middle, here) := audit_idf_emit_counted EV ceiling levels st v in
      let '(result, later) := audit_idf_emit_list_counted EV ceiling levels rest middle in
      (result, IdfWorkCase 1 :: here ++ later)
  end.

Fixpoint audit_idf_scan_add_counted {V E} (EV : encoding V) (values : list V)
    (set : FinSet.t V) : FinSet.t V * list (audit_idf_work_call V E) :=
  match values with
  | [] => (set, [IdfWorkCase 2])
  | v :: rest => let next := FinSet.add EV v set in
      let '(result, events) := audit_idf_scan_add_counted EV rest next in
      (result, IdfWorkCase 3 :: IdfWorkAdd v set next :: events)
  end.

Definition audit_idf_work_step_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (t : dom_tree V) (forest : Graph.t V V)
    (tree_index : prepared EV forest) (levels : Map.t V positive) (live : V -> bool)
    (st : IdfState.t V) : IdfState.t V * list (audit_idf_work_call V E) :=
  let '(popped, pop_events) := queue_pop EV (IdfState.pending st) in
  match popped with
  | None => (st, [IdfWorkPop (IdfState.pending st) popped pop_events; IdfWorkCase 4])
  | Some (_, root, rest) =>
      let '(search, dfs_events) := audit_dfs_full_counted tree_index (IdfState.scanned st) [root] in
      let fresh := preorder search in
      let '(collected, collect_events) := audit_idf_nodes_counted p t live root fresh ([], 0%N) in
      let '(scanned, scan_events) := audit_idf_scan_add_counted EV fresh (IdfState.scanned st) in
      let processed := FinSet.add EV root (IdfState.processed st) in
      let visits := N.add (IdfState.edge_visits st) (snd collected) in
      let started := IdfState.Make rest (IdfState.emitted st) scanned processed
        (root :: IdfState.trace st) visits (IdfState.output_count st) in
      let '(result, emit_events) := audit_idf_emit_list_counted EV (fuel p) levels (fst collected)
  started in
      (result, [IdfWorkPop (IdfState.pending st) popped pop_events; IdfWorkCase 5;
        IdfWorkDfs dfs_events; IdfWorkCollect collect_events] ++ scan_events ++
        [IdfWorkAdd root (IdfState.processed st) processed;
         IdfWorkArithmetic (IdfState.edge_visits st) (snd collected) visits] ++ emit_events)
  end.

Fixpoint audit_idf_run_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (t : dom_tree V) (forest : Graph.t V V)
    (tree_index : prepared EV forest) (levels : Map.t V positive) (live : V -> bool)
    (k : positive) (st : IdfState.t V) : IdfState.t V * list (audit_idf_work_call V E) :=
  if PQueue.is_empty (IdfState.pending st) then
    (st, [IdfWorkIsEmpty (IdfState.pending st) true; IdfWorkCase 6]) else
    match k with
    | xH => let '(result, events) := audit_idf_work_step_counted p t forest tree_index levels live
  st in
        (result, IdfWorkIsEmpty (IdfState.pending st) false :: IdfWorkCase 7 :: events)
    | xO half => let '(middle, first) := audit_idf_run_counted p t forest tree_index levels live
  half st in
        let '(result, second) := audit_idf_run_counted p t forest tree_index levels live half middle
  in
        (result, IdfWorkIsEmpty (IdfState.pending st) false :: IdfWorkCase 8 :: first ++ second)
    | xI half => let '(middle, first) := audit_idf_run_counted p t forest tree_index levels live
  half st in
        let '(next, second) := audit_idf_run_counted p t forest tree_index levels live half middle
  in
        let '(result, last) := audit_idf_work_step_counted p t forest tree_index levels live next in
        (result, IdfWorkIsEmpty (IdfState.pending st) false :: IdfWorkCase 9 :: first ++ second ++
  last)
    end.

Definition audit_idf_work_step_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    t forest tree_index levels live st,
    fst (audit_idf_work_step_counted p t forest tree_index levels live st) =
      idf_work_step p t forest tree_index levels live st.

Definition audit_idf_run_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    t forest tree_index levels live k st,
    fst (audit_idf_run_counted p t forest tree_index levels live k st) =
      idf_run p t forest tree_index levels live k st.

Inductive audit_idf_producer_call (V E : Type) : Type :=
| IdfProducerDom : audit_dom_call V E -> audit_idf_producer_call V E
| IdfProducerPrepare : audit_prepare_nested_event V V (audit_dom_body V) ->
    audit_idf_producer_call V E
| IdfProducerDfs : audit_dfs_nested_event V V (audit_dom_body V) ->
    audit_idf_producer_call V E
| IdfProducerSeed : audit_idf_seed_call V -> audit_idf_producer_call V E
| IdfProducerWork : audit_idf_work_call V E -> audit_idf_producer_call V E
| IdfProducerLevelGet : V -> Map.t V V -> option V -> audit_idf_producer_call V E
| IdfProducerLevelRead : V -> Map.t V positive -> option positive -> audit_idf_producer_call V E
| IdfProducerLevelWrite : V -> positive -> Map.t V positive -> Map.t V positive ->
    audit_idf_producer_call V E
| IdfProducerCase : nat -> audit_idf_producer_call V E.
Arguments IdfProducerDom {V E} _.
Arguments IdfProducerPrepare {V E} _.
Arguments IdfProducerDfs {V E} _.
Arguments IdfProducerSeed {V E} _.
Arguments IdfProducerWork {V E} _.
Arguments IdfProducerLevelGet {V E} _ _ _.
Arguments IdfProducerLevelRead {V E} _ _ _.
Arguments IdfProducerLevelWrite {V E} _ _ _ _.
Arguments IdfProducerCase {V E} _.

Fixpoint audit_idf_levels_fold_counted {V E} (EV : encoding V) (parents : Map.t V V)
    (order : list V) (levels : Map.t V positive)
    : Map.t V positive * list (audit_idf_producer_call V E) :=
  match order with
  | [] => (levels, [IdfProducerCase 0])
  | v :: rest =>
      let found := Map.get EV v parents in
      let '(level, reads) := match found with
      | None => (xH, [])
      | Some parent => let prior := Map.get EV parent levels in
          (Pos.succ (match prior with Some x => x | None => xH end),
           [IdfProducerLevelRead parent levels prior]) end in
      let next := Map.set EV v level levels in
      let '(result, events) := audit_idf_levels_fold_counted EV parents rest next in
      (result, [IdfProducerCase 1; IdfProducerLevelGet v parents found] ++ reads ++
        [IdfProducerLevelWrite v level levels next] ++ events)
  end.

Definition audit_direct_pruned_idf_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (t : dom_tree V) (defs : list V) (live : V -> bool)
    : FinSet.t V * list (audit_idf_producer_call V E) :=
  let parents := idom t in
  let '(search, search_events) := audit_dfs_full_counted p FinSet.empty (Graph.entries g) in
  let vertices := preorder search in
  let rows := Map.elements parents in
  let '(children, child_events) := audit_dom_children_counted EV rows in
  let '(roots, root_events) := audit_dom_roots_counted EV parents vertices in
  let forest := Graph.Make roots vertices (fun v => index_edges EV children v)
    (fun v => match Map.get EV v parents with Some u => u | None => v end) (fun v => v) in
  let '(tree_index, prepare_events) :=
    audit_graph_prepare_nested_counted EV forest (audit_dom_prepare_callbacks EV children) in
  let '(level_search, level_dfs_events) :=
    audit_dfs_nested_counted tree_index (audit_dom_dfs_callbacks EV) FinSet.empty roots in
  let '(levels, level_events) := audit_idf_levels_fold_counted EV parents (rpo level_search)
  Map.empty in
  let '(initial, initial_events) := audit_idf_initial_counted EV (fuel p) levels defs in
  let '(result, run_events) := audit_idf_run_counted p t forest tree_index levels live
    (Pos.of_succ_nat (length (Graph.nodes g))) initial in
  (IdfState.emitted result,
    map (fun event => IdfProducerDom (AuditDomInitialDfs event)) search_events ++
    [IdfProducerDom (AuditDomElements parents rows)] ++
    map IdfProducerDom child_events ++ map IdfProducerDom root_events ++
    map IdfProducerPrepare prepare_events ++ map IdfProducerDfs level_dfs_events ++
    level_events ++ map IdfProducerSeed initial_events ++ map IdfProducerWork run_events).

Definition audit_direct_pruned_idf_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) t defs live,
    fst (audit_direct_pruned_idf_counted p t defs live) = direct_pruned_idf p t defs live.

Definition audit_direct_idf_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (t : dom_tree V) (defs : list V) :=
  audit_direct_pruned_idf_counted p t defs (fun _ => true).

Definition audit_direct_idf_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) t defs,
    fst (audit_direct_idf_counted p t defs) = direct_idf p t defs.
Definition audit_idf_dom_body_event_work {V} (EV : encoding V) (event : audit_dom_body V) : nat :=
  64 + match event with
  | AuditDomBodyRead v _ _ =>
      audit_encoding_weight (audit_key_bits_weight (encode EV v)) + audit_get_weight (encode EV v)
  | AuditDomBodyEncode _ code => audit_encoding_weight (audit_key_bits_weight code)
  | AuditDomBodyTarget _ => 0
  end.

Definition audit_idf_dom_event_work {V E} (EV : encoding V) (event : audit_dom_call V E) : nat :=
  64 + match event with
  | AuditDomInitialDfs item => audit_dfs_full_model_event EV item
  | AuditDomElements input _ => 64 * Nat.pow (S (Trie.size input)) 3
  | AuditDomChildRead v _ _ | AuditDomRootGet v _ _ =>
      audit_encoding_weight (audit_key_bits_weight (encode EV v)) + audit_get_weight (encode EV v)
  | AuditDomChildSet v _ _ =>
      audit_encoding_weight (audit_key_bits_weight (encode EV v)) + audit_set_weight (encode EV v)
  | AuditDomPrepare (outer, body) => audit_graph_full_event_work outer +
      fold_right (fun item n => audit_idf_dom_body_event_work EV item + n) 0 body
  | AuditDomDfs (outer, body) => audit_dfs_full_model_event EV outer +
      fold_right (fun item n => audit_idf_dom_body_event_work EV item + n) 0 body
  | AuditDomOutput size => S size
  | AuditDomCase _ => 0
  end.

Definition audit_idf_work_event_work {V E} (EV : encoding V) (event : audit_idf_work_call V E) : nat
  :=
  64 + match event with
  | IdfWorkPop _ _ events | IdfWorkPush _ _ _ _ events => queue_model_work EV events
  | IdfWorkGet v _ _ | IdfWorkMem v _ _ =>
      audit_encoding_weight (audit_key_bits_weight (encode EV v)) + audit_get_weight (encode EV v)
  | IdfWorkAdd v _ _ =>
      audit_encoding_weight (audit_key_bits_weight (encode EV v)) + audit_set_weight (encode EV v)
  | IdfWorkDfs events =>
      fold_right (fun item n => audit_dfs_full_model_event EV item + n) 0 events
  | IdfWorkCollect events =>
      fold_right (fun item n => audit_idf_collect_event_work EV item + n) 0 events
  | IdfWorkSub a b _ => audit_binary_weight (Z.pos a) (Z.pos b)
  | IdfWorkArithmetic a b _ => audit_binary_weight (Z.of_N a) (Z.of_N b)
  | IdfWorkCase _ | IdfWorkIsEmpty _ _ => 0
  end.

Definition audit_idf_producer_event_work {V E} (EV : encoding V)
    (event : audit_idf_producer_call V E) : nat :=
  64 + match event with
  | IdfProducerDom item => audit_idf_dom_event_work EV item
  | IdfProducerPrepare (outer, body) => audit_graph_full_event_work outer +
      fold_right (fun item n => audit_idf_dom_body_event_work EV item + n) 0 body
  | IdfProducerDfs (outer, body) => audit_dfs_full_model_event EV outer +
      fold_right (fun item n => audit_idf_dom_body_event_work EV item + n) 0 body
  | IdfProducerSeed item => audit_idf_seed_event_work EV item
  | IdfProducerWork item => audit_idf_work_event_work EV item
  | IdfProducerLevelGet v _ _ | IdfProducerLevelRead v _ _ =>
      audit_encoding_weight (audit_key_bits_weight (encode EV v)) + audit_get_weight (encode EV v)
  | IdfProducerLevelWrite v _ _ _ =>
      audit_encoding_weight (audit_key_bits_weight (encode EV v)) + audit_set_weight (encode EV v)
  | IdfProducerCase _ => 0
  end.

Definition audit_idf_selected_work {V E} (EV : encoding V)
    (events : list (audit_idf_producer_call V E)) : nat :=
  1024 * S (length events) * S (length events) +
    fold_right (fun item n => audit_idf_producer_event_work EV item + n) 0 events.

Definition audit_idf_input_support {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (t : dom_tree V) (defs : list V) : list V :=
  let rows := Map.elements (out_index p) in
  let parents := Map.elements (idom t) in
  defs ++ Graph.entries g ++ Graph.nodes g ++ map fst rows ++
    map (Graph.target g) (flat_map snd rows) ++ map fst parents ++ map snd parents ++
    map fst (Map.elements (tin t)) ++ map fst (Map.elements (tout t)).

Definition audit_idf_input_scale {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (t : dom_tree V) (defs : list V) : nat :=
  let rows := Map.elements (out_index p) in
  1 + length (audit_idf_input_support p t defs) + length (flat_map snd rows) +
    Trie.size (out_index p) + Trie.size (idom t) + Trie.size (tin t) + Trie.size (tout t) +
    Pos.to_nat (fuel p).

Definition audit_idf_input_width {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (t : dom_tree V) (defs : list V) : nat :=
  let numbers := fuel p :: map snd (Map.elements (tin t)) ++ map snd (Map.elements (tout t)) in
  Nat.max (fold_right Nat.max 0 (map (fun v => audit_key_bits_weight (encode EV v))
    (audit_idf_input_support p t defs)))
    (fold_right Nat.max 0 (map audit_key_bits_weight numbers)).

Definition audit_idf_selected_input_budget {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (t : dom_tree V) (defs : list V) : nat :=
  1048576 * Nat.pow (S (audit_idf_input_scale p t defs)) 24 *
    Nat.pow (S (audit_idf_input_width p t defs)) 4.

Definition audit_direct_pruned_idf_selected_bound_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) t defs live,
    let '(result, events) := audit_direct_pruned_idf_counted p t defs live in
    result = direct_pruned_idf p t defs live /\
    audit_idf_selected_work EV events <= audit_idf_selected_input_budget p t defs.

(** Events retain every callback input, result and body of this execution. *)
Inductive audit_idf_collect_source_event (V E B : Type) : Type :=
  | IdfCollectSourceCase : nat -> audit_idf_collect_source_event V E B
  | IdfCollectSourceTarget : E -> V -> list B -> audit_idf_collect_source_event V E B
  | IdfCollectSourceLive : V -> bool -> list B -> audit_idf_collect_source_event V E B
  | IdfCollectSourceParent : audit_map_event V V B -> audit_idf_collect_source_event V E B
  | IdfCollectSourceEdges : audit_map_event V (list E) B -> audit_idf_collect_source_event V E B
  | IdfCollectSourceDom : audit_frontier_source_event V E B -> audit_idf_collect_source_event V E B
  | IdfCollectSourceSucc : N -> N -> audit_idf_collect_source_event V E B.
Arguments IdfCollectSourceCase {V E B} _.
Arguments IdfCollectSourceTarget {V E B} _ _ _.
Arguments IdfCollectSourceLive {V E B} _ _ _.
Arguments IdfCollectSourceParent {V E B} _.
Arguments IdfCollectSourceEdges {V E B} _.
Arguments IdfCollectSourceDom {V E B} _.
Arguments IdfCollectSourceSucc {V E B} _ _.

(** The join tests dominance and liveness, retaining both actual target calls. *)
Definition audit_idf_collect_source_join {V E B} (enc : V -> positive * list B)
    (target : E -> V * list B) (live : V -> bool * list B) (t : dom_tree V) (root : V) (edge : E)
    : bool * list (audit_idf_collect_source_event V E B) :=
  let '(first, first_body) := target edge in
  let '(parent, parent_events) := audit_map_get enc first (idom t) in
  let '(blocked, dom_events) := match parent with
    | None => (false, [])
    | Some v => audit_frontier_source_dom enc t root v
    end in
  let '(second, second_body) := target edge in
  let '(is_live, live_body) := live second in
  (negb blocked && is_live, [IdfCollectSourceTarget edge first first_body] ++
    map IdfCollectSourceParent parent_events ++ map IdfCollectSourceDom dom_events ++
    [IdfCollectSourceTarget edge second second_body; IdfCollectSourceLive second is_live
  live_body]).

(** Every edge increments its binary counter; emitted targets call the source callback again. *)
Definition audit_idf_collect_source_edge {V E B} (enc : V -> positive * list B)
    (target : E -> V * list B) (live : V -> bool * list B) (t : dom_tree V) (root : V)
    (acc : list V * N) (edge : E) : (list V * N) * list (audit_idf_collect_source_event V E B) :=
  let '(emit, calls) := audit_idf_collect_source_join enc target live t root edge in
  let '(values, value_events) := if emit then
    let '(v, body) := target edge in (v :: fst acc, [IdfCollectSourceTarget edge v body])
    else (fst acc, []) in
  let count := N.succ (snd acc) in
  ((values, count), calls ++ value_events ++ [IdfCollectSourceSucc (snd acc) count]).

(** The edge fold preserves every occurrence and intermediate accumulator. *)
Fixpoint audit_idf_collect_source_edges {V E B} (enc : V -> positive * list B)
    (target : E -> V * list B) (live : V -> bool * list B) (t : dom_tree V) (root : V)
    (edges : list E) (acc : list V * N) : (list V * N) * list (audit_idf_collect_source_event V E B)
  :=
  match edges with
  | [] => (acc, [IdfCollectSourceCase 0])
  | edge :: rest =>
      let '(next, calls) := audit_idf_collect_source_edge enc target live t root acc edge in
      let '(result, events) := audit_idf_collect_source_edges enc target live t root rest next in
      (result, IdfCollectSourceCase 1 :: calls ++ events)
  end.

(** Node collection uses the actual prepared adjacency map for each scanned vertex. *)
Fixpoint audit_idf_collect_source_nodes {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (enc : V -> positive * list B) (target : E -> V * list B)
    (live : V -> bool * list B) (t : dom_tree V) (root : V) (vertices : list V) (acc : list V * N)
    : (list V * N) * list (audit_idf_collect_source_event V E B) :=
  match vertices with
  | [] => (acc, [IdfCollectSourceCase 2])
  | v :: rest =>
      let '(found, reads) := audit_map_get enc v (out_index p) in
      let edges := match found with Some xs => xs | None => [] end in
      let '(next, calls) := audit_idf_collect_source_edges enc target live t root edges acc in
      let '(result, events) := audit_idf_collect_source_nodes p enc target live t root rest next in
      (result, IdfCollectSourceCase 3 :: map IdfCollectSourceEdges reads ++ calls ++ events)
  end.

(** The actual source fold and its captured callbacks erase to node collection. *)
Definition audit_idf_collect_source_erasure_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (enc : V -> positive * list B) (target : E -> V * list B) (live : V -> bool * list B)
    (live_value : V -> bool) t root vertices acc,
    (forall v, fst (enc v) = encode EV v) ->
    (forall e, fst (target e) = Graph.target g e) ->
    (forall v, fst (live v) = live_value v) ->
    fst (audit_idf_collect_source_nodes p enc target live t root vertices acc) =
      fold_left (idf_collect_node p t live_value root) vertices acc.

(** Primitive work includes every recorded call and binary counter step. *)
Definition audit_idf_collect_source_event_work {V E B} (weight : B -> nat)
    (event : audit_idf_collect_source_event V E B) : nat :=
  let body := fun xs => fold_right (fun x n => weight x + n) 0 xs in
  64 + match event with
  | IdfCollectSourceCase _ => 0
  | IdfCollectSourceTarget _ _ xs | IdfCollectSourceLive _ _ xs => body xs
  | IdfCollectSourceParent call => audit_map_source_work body [call]
  | IdfCollectSourceEdges call => audit_map_source_work body [call]
  | IdfCollectSourceDom call => audit_frontier_source_event_work weight call
  | IdfCollectSourceSucc n _ => 4 + 2 * match n with N0 => 0 | Npos p => Pos.size_nat p end
  end.

(** Only bodies of actual supplied callbacks are external. *)
Definition audit_idf_collect_source_event_external {V E B} (weight : B -> nat)
    (event : audit_idf_collect_source_event V E B) : nat :=
  match event with
  | IdfCollectSourceTarget _ _ body | IdfCollectSourceLive _ _ body |
    IdfCollectSourceParent (AuditMapGet _ _ _ _ body _) |
    IdfCollectSourceParent (AuditMapSet _ _ _ _ _ body _) |
    IdfCollectSourceParent (AuditMapRemove _ _ _ _ body _) |
    IdfCollectSourceEdges (AuditMapGet _ _ _ _ body _) |
    IdfCollectSourceEdges (AuditMapSet _ _ _ _ _ body _) |
    IdfCollectSourceEdges (AuditMapRemove _ _ _ _ body _) =>
      fold_right (fun x n => weight x + n) 0 body
  | IdfCollectSourceDom call => audit_frontier_source_body_event_work weight call
  | _ => 0
  end.

(** Source work includes trace-list composition for this execution. *)
Definition audit_idf_collect_source_work {V E B} (weight : B -> nat)
    (events : list (audit_idf_collect_source_event V E B)) : nat :=
  256 * S (length events) * S (length events) +
    fold_right (fun event n => audit_idf_collect_source_event_work weight event + n) 0 events.

(** External work sums the captured callback bodies in the same events. *)
Definition audit_idf_collect_source_external {V E B} (weight : B -> nat)
    (events : list (audit_idf_collect_source_event V E B)) : nat :=
  fold_right (fun event n => audit_idf_collect_source_event_external weight event + n) 0 events.

(** The bound uses actual prepared edges, tree indexes, queried nodes and counter width. *)
Definition audit_idf_collect_source_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (t : dom_tree V) (root : V) (vertices : list V) (acc : list V * N) : nat :=
  let rows := Map.elements (out_index p) in
  let edges := flat_map snd rows in
  let parents := Map.elements (idom t) in
  let before := Map.elements (tin t) in
  let after := Map.elements (tout t) in
  let keys := root :: vertices ++ fst acc ++ map fst rows ++ map (Graph.target g) edges ++
    map fst parents ++ map snd parents ++ map fst before ++ map fst after in
  let width := fold_right Nat.max 0 (map (fun v => Pos.size_nat (encode EV v)) keys) in
  let ranks := fold_right Nat.max 0 (map (fun row => Pos.size_nat (snd row)) (before ++ after)) in
  let counter := match snd acc with N0 => 0 | Npos n => Pos.size_nat n end in
  4096 * Nat.pow (S (length keys + length edges + width + ranks + counter)) 6.

(** The same source fold has an input-derived bound plus actual callback bodies. *)
Definition audit_idf_collect_source_bound_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (enc : V -> positive * list B) (target : E -> V * list B) (live : V -> bool * list B)
    t root vertices acc (weight : B -> nat),
    (forall v, fst (enc v) = encode EV v) ->
    (forall e, fst (target e) = Graph.target g e) ->
    let events := snd (audit_idf_collect_source_nodes p enc target live t root vertices acc) in
    audit_idf_collect_source_work weight events <= audit_idf_collect_source_budget EV g p t root
  vertices acc +
      audit_idf_collect_source_external weight events.

(** Nested frontier events identify actual client callback inputs. *)
Definition audit_idf_frontier_event_budget {V E B} (encode_budget : V -> nat) (target_budget
  source_budget : E -> nat)
    (event : audit_frontier_source_event V E B) : nat :=
  match event with
  | FrontierSourceDfs (_, calls) =>
      fold_right (fun call n => audit_idf_capture_budget encode_budget target_budget call + n) 0
  calls
  | FrontierSourceSource e _ _ => source_budget e
  | FrontierSourceTarget e _ _ => target_budget e
  | FrontierSourceParent (AuditMapGet v _ _ _ _ _) | FrontierSourceParent (AuditMapSet v _ _ _ _ _
  _) |
    FrontierSourceParent (AuditMapRemove v _ _ _ _ _) | FrontierSourceRank (AuditMapGet v _ _ _ _ _)
  |
    FrontierSourceRank (AuditMapSet v _ _ _ _ _ _) | FrontierSourceRank (AuditMapRemove v _ _ _ _ _)
  |
    FrontierSourcePred (AuditMapGet v _ _ _ _ _) | FrontierSourcePred (AuditMapSet v _ _ _ _ _ _) |
    FrontierSourcePred (AuditMapRemove v _ _ _ _ _) | FrontierSourceRows (AuditMapGet v _ _ _ _ _) |
    FrontierSourceRows (AuditMapSet v _ _ _ _ _ _) | FrontierSourceRows (AuditMapRemove v _ _ _ _ _)
  |
    FrontierSourceSet (AuditSetAdd v _ _ _ _ _) | FrontierSourceSet (AuditSetMem v _ _ _ _ _) |
    FrontierSourceSet (AuditSetRemove v _ _ _ _ _) => encode_budget v
  | _ => 0
  end.

(** Each collector event prices the actual invocation, including repeated targets. *)
Definition audit_idf_collect_source_event_budget {V E B} (encode_budget live_budget : V -> nat)
    (target_budget : E -> nat) (event : audit_idf_collect_source_event V E B) : nat :=
  match event with
  | IdfCollectSourceTarget e _ _ => target_budget e
  | IdfCollectSourceLive v _ _ => live_budget v
  | IdfCollectSourceParent (AuditMapGet v _ _ _ _ _) | IdfCollectSourceParent (AuditMapSet v _ _ _ _
  _ _) |
    IdfCollectSourceParent (AuditMapRemove v _ _ _ _ _) | IdfCollectSourceEdges (AuditMapGet v _ _ _
  _ _) |
    IdfCollectSourceEdges (AuditMapSet v _ _ _ _ _ _) | IdfCollectSourceEdges (AuditMapRemove v _ _
  _ _ _) =>
      encode_budget v
  | IdfCollectSourceDom call => audit_idf_frontier_event_budget encode_budget target_budget (fun _
  => 0) call
  | _ => 0
  end.

(** The adapted collector bounds the same source fold by per-call input budgets. *)
Definition audit_idf_collect_source_adapted_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (enc : V -> positive * list B) (target : E -> V * list B) (live : V -> bool * list B)
    (live_value : V -> bool) t root vertices acc (weight : B -> nat)
    encode_source target_source live_source encode_budget target_budget live_budget,
    (forall v, fst (enc v) = encode EV v) ->
    (forall e, fst (target e) = Graph.target g e) ->
    (forall v, fst (live v) = live_value v) ->
    audit_graph_external_callback_adapter enc weight encode_source encode_budget ->
    audit_graph_external_callback_adapter target weight target_source target_budget ->
    audit_graph_external_callback_adapter live weight live_source live_budget ->
    let '(result, events) := audit_idf_collect_source_nodes p enc target live t root vertices acc in
    result = fold_left (idf_collect_node p t live_value root) vertices acc /\
    audit_idf_collect_source_work weight events <= audit_idf_collect_source_budget EV g p t root
  vertices acc +
      fold_right (fun event n => audit_idf_collect_source_event_budget encode_budget live_budget
  target_budget event + n)
        0 events.

(** This component contract does not claim the complete IDF worklist bound. *)
Definition audit_idf_collect_source_contract_statement : Prop :=
  audit_idf_collect_source_erasure_statement /\ audit_idf_collect_source_bound_statement /\
  audit_idf_collect_source_adapted_statement.

(** Events retain actual map, set, queue and arithmetic invocations. *)
Inductive audit_idf_queue_event (V B : Type) : Type :=
  | IdfQueueCase : nat -> audit_idf_queue_event V B
  | IdfQueueMap : audit_map_event V positive B -> audit_idf_queue_event V B
  | IdfQueueSet : audit_set_event V B -> audit_idf_queue_event V B
  | IdfQueuePush : audit_queue_nested_event V (positive * list B) -> audit_idf_queue_event V B
  | IdfQueueSub : audit_idf_sub_event -> audit_idf_queue_event V B
  | IdfQueueSucc : audit_nat_encoding_event -> audit_idf_queue_event V B.
Arguments IdfQueueCase {V B} _.
Arguments IdfQueueMap {V B} _.
Arguments IdfQueueSet {V B} _.
Arguments IdfQueuePush {V B} _.
Arguments IdfQueueSub {V B} _.
Arguments IdfQueueSucc {V B} _.

(** Priority reads the actual level and follows the binary subtraction path when present. *)
Definition audit_idf_queue_priority {V B} (enc : V -> positive * list B) (ceiling : positive)
    (levels : Map.t V positive) (v : V) : positive * list (audit_idf_queue_event V B) :=
  let '(found, reads) := audit_map_get enc v levels in
  match found with
  | None => (ceiling, map IdfQueueMap reads ++ [IdfQueueCase 0])
  | Some rank => let '(result, calls) := audit_idf_sub_counted ceiling rank in
      (result, map IdfQueueMap reads ++ [IdfQueueCase 1] ++ map IdfQueueSub calls)
  end.

(** Each seed performs the source's first lookup and, when present, its second priority lookup. *)
Definition audit_idf_queue_seed {V B} (enc : V -> positive * list B) (ceiling : positive)
    (levels : Map.t V positive) (q : PQueue.t V) (v : V) : PQueue.t V * list (audit_idf_queue_event
  V B) :=
  let '(found, reads) := audit_map_get enc v levels in
  match found with
  | None => (q, map IdfQueueMap reads ++ [IdfQueueCase 2])
  | Some _ =>
      let '(priority, calls) := audit_idf_queue_priority enc ceiling levels v in
      let '(result, queue_events) := audit_queue_recorded_push enc priority v q in
      (result, map IdfQueueMap reads ++ [IdfQueueCase 3] ++ calls ++ map IdfQueuePush queue_events)
  end.

(** Seed folding preserves duplicate definitions and every intermediate queue. *)
Fixpoint audit_idf_queue_seeds {V B} (enc : V -> positive * list B) (ceiling : positive)
    (levels : Map.t V positive) (defs : list V) (q : PQueue.t V) : PQueue.t V * list
  (audit_idf_queue_event V B) :=
  match defs with
  | [] => (q, [IdfQueueCase 4])
  | v :: rest => let '(next, calls) := audit_idf_queue_seed enc ceiling levels q v in
      let '(result, events) := audit_idf_queue_seeds enc ceiling levels rest next in
      (result, IdfQueueCase 5 :: calls ++ events)
  end.

(** Binary counter increment exposes the positive successor frames when present. *)
Definition audit_idf_queue_succ (value : N) : N * list audit_nat_encoding_event :=
  match value with
  | N0 => (1%N, [])
  | Npos p => let '(next, events) := audit_positive_succ p in (Npos next, events)
  end.

(** Emission records both set calls and pushes only when the vertex is not processed. *)
Definition audit_idf_queue_emit {V B} (enc : V -> positive * list B) (ceiling : positive)
    (levels : Map.t V positive) (st : IdfState.t V) (v : V) : IdfState.t V * list
  (audit_idf_queue_event V B) :=
  let '(processed, pe) := audit_finset_mem enc v (IdfState.processed st) in
  let '(pending, queue_events) := if processed then (IdfState.pending st, []) else
    let '(priority, calls) := audit_idf_queue_priority enc ceiling levels v in
    let '(q, events) := audit_queue_recorded_push enc priority v (IdfState.pending st) in
    (q, calls ++ map IdfQueuePush events) in
  let '(emitted, ee) := audit_finset_add enc v (IdfState.emitted st) in
  let '(was_emitted, we) := audit_finset_mem enc v (IdfState.emitted st) in
  let '(count, ce) := if was_emitted then (IdfState.output_count st, [])
    else audit_idf_queue_succ (IdfState.output_count st) in
  (IdfState.Make pending emitted (IdfState.scanned st) (IdfState.processed st)
    (IdfState.trace st) (IdfState.edge_visits st) count,
    map IdfQueueSet pe ++ queue_events ++ map IdfQueueSet ee ++ map IdfQueueSet we ++ map
  IdfQueueSucc ce).

(** These source operations return the exact queue states and emitted state. *)
Definition audit_idf_queue_source_erasure_statement : Prop :=
  forall V B (EV : encoding V) (enc : V -> positive * list B) ceiling levels defs q st v,
    (forall key, fst (enc key) = encode EV key) ->
    fst (audit_idf_queue_seeds enc ceiling levels defs q) = fold_left (idf_seed EV ceiling levels)
  defs q /\
    fst (audit_idf_queue_emit enc ceiling levels st v) = idf_emit EV ceiling levels st v.

(** Each queue event includes actual primitive source work and callback bodies. *)
Definition audit_idf_queue_event_work {V B} (weight : B -> nat) (event : audit_idf_queue_event V B)
  : nat :=
  let body := fun xs => fold_right (fun x n => weight x + n) 0 xs in
  64 + match event with
  | IdfQueueCase _ => 0
  | IdfQueueMap call => audit_map_source_work body [call]
  | IdfQueueSet call => audit_finset_source_work body [call]
  | IdfQueuePush call => audit_queue_recorded_full_source_work weight [call]
  | IdfQueueSub _ => 16
  | IdfQueueSucc _ => 4
  end.

(** A captured queue body contributes only its supplied encoder work. *)
Definition audit_idf_queue_push_external {V B} (weight : B -> nat)
    (event : audit_queue_nested_event V (positive * list B)) : nat :=
  let '(_, (_, calls)) := event in
  fold_right (fun call n => fold_right (fun x k => weight x + k) 0 (snd call) + n) 0 calls.

(** The external measure counts only bodies at actual encoder invocations. *)
Definition audit_idf_queue_event_external {V B} (weight : B -> nat) (event : audit_idf_queue_event V
  B) : nat :=
  match event with
  | IdfQueueMap (AuditMapGet _ _ _ _ body _) | IdfQueueMap (AuditMapSet _ _ _ _ _ body _) |
    IdfQueueMap (AuditMapRemove _ _ _ _ body _) | IdfQueueSet (AuditSetMem _ _ _ _ body _) |
    IdfQueueSet (AuditSetAdd _ _ _ _ body _) | IdfQueueSet (AuditSetRemove _ _ _ _ body _) =>
      fold_right (fun x n => weight x + n) 0 body
  | IdfQueuePush call => audit_idf_queue_push_external weight call
  | _ => 0
  end.

(** Trace composition charges all source events of this execution. *)
Definition audit_idf_queue_source_work {V B} (weight : B -> nat) (events : list
  (audit_idf_queue_event V B)) : nat :=
  256 * S (length events) * S (length events) +
    fold_right (fun event n => audit_idf_queue_event_work weight event + n) 0 events.

(** External cost sums the same execution's supplied callback bodies. *)
Definition audit_idf_queue_source_external {V B} (weight : B -> nat)
    (events : list (audit_idf_queue_event V B)) : nat :=
  fold_right (fun event n => audit_idf_queue_event_external weight event + n) 0 events.

(** The seed bound uses original queue structure, levels, key widths and definition occurrences. *)
Definition audit_idf_queue_seed_budget {V} (EV : encoding V) (ceiling : positive)
    (levels : Map.t V positive) (defs : list V) (q : PQueue.t V) : nat :=
  let rows := Map.elements levels in
  let width := fold_right Nat.max (Pos.size_nat ceiling)
    (map (fun row => Nat.max (Pos.size_nat (encode EV (fst row))) (Pos.size_nat (snd row))) rows) in
  let size := audit_queue_input_scale (PQueue.pending_count q) (PQueue.pending q) in
  let qwidth := audit_queue_input_width EV (PQueue.pending q) (PQueue.live q) defs [ceiling] in
  1048576 * Nat.pow (S (size + width + qwidth + length defs + length rows)) 12.

(** The emission bound adds actual counter width to the seed bound. *)
Definition audit_idf_queue_emit_budget {V} (EV : encoding V) (ceiling : positive)
    (levels : Map.t V positive) (st : IdfState.t V) (v : V) : nat :=
  let width := match IdfState.output_count st with N0 => 0 | Npos p => Pos.size_nat p end in
  audit_idf_queue_seed_budget EV ceiling levels [v] (IdfState.pending st) + 4096 * S width * S
  width.

(** Both operations have input-derived bounds plus bodies of their actual callback calls. *)
Definition audit_idf_queue_source_bound_statement : Prop :=
  forall V B (EV : encoding V) (enc : V -> positive * list B) ceiling levels defs q st v (weight : B
  -> nat),
    (forall key, fst (enc key) = encode EV key) ->
    let seed_events := snd (audit_idf_queue_seeds enc ceiling levels defs q) in
    let emit_events := snd (audit_idf_queue_emit enc ceiling levels st v) in
    audit_idf_queue_source_work weight seed_events <= audit_idf_queue_seed_budget EV ceiling levels
  defs q +
      audit_idf_queue_source_external weight seed_events /\
    audit_idf_queue_source_work weight emit_events <= audit_idf_queue_emit_budget EV ceiling levels
  st v +
      audit_idf_queue_source_external weight emit_events.

(** Queue callbacks expose the key from the same captured event. *)
Definition audit_idf_queue_push_budget {V B} (encode_budget : V -> nat)
    (call : audit_queue_nested_event V (positive * list B)) : nat :=
  match fst call with
  | QGet v _ | QSet v _ _ | QRemove v _ | QEncode v => encode_budget v
  | _ => 0
  end.

(** Every encoder budget is applied to the actual key of the recorded call. *)
Definition audit_idf_queue_event_budget {V B} (encode_budget : V -> nat) (event :
  audit_idf_queue_event V B) : nat :=
  match event with
  | IdfQueueMap (AuditMapGet v _ _ _ _ _) | IdfQueueMap (AuditMapSet v _ _ _ _ _ _) |
    IdfQueueMap (AuditMapRemove v _ _ _ _ _) | IdfQueueSet (AuditSetMem v _ _ _ _ _) |
    IdfQueueSet (AuditSetAdd v _ _ _ _ _) | IdfQueueSet (AuditSetRemove v _ _ _ _ _) =>
  encode_budget v
  | IdfQueuePush call => audit_idf_queue_push_budget encode_budget call
  | _ => 0
  end.

(** Seed and emission costs use source-and-budget laws for each actual encoder call. *)
Definition audit_idf_queue_source_adapted_statement : Prop :=
  forall V B (EV : encoding V) (enc : V -> positive * list B) ceiling levels defs q st v (weight : B
  -> nat)
    encode_source encode_budget,
    (forall key, fst (enc key) = encode EV key) ->
    audit_graph_external_callback_adapter enc weight encode_source encode_budget ->
    let seed_events := snd (audit_idf_queue_seeds enc ceiling levels defs q) in
    let emit_events := snd (audit_idf_queue_emit enc ceiling levels st v) in
    audit_idf_queue_source_work weight seed_events <= audit_idf_queue_seed_budget EV ceiling levels
  defs q +
      fold_right (fun event n => audit_idf_queue_event_budget encode_budget event + n) 0 seed_events
  /\
    audit_idf_queue_source_work weight emit_events <= audit_idf_queue_emit_budget EV ceiling levels
  st v +
      fold_right (fun event n => audit_idf_queue_event_budget encode_budget event + n) 0
  emit_events.

(** The component contract includes all fixed primitive and queue source obligations. *)
Definition audit_idf_queue_source_contract_statement : Prop :=
  audit_idf_queue_source_erasure_statement /\ audit_idf_queue_source_bound_statement /\
  audit_idf_queue_source_adapted_statement /\ audit_idf_sub_source_statement /\
  audit_queue_full_source_contract_statement.

(** Events retain actual forest setup, DFS and level-index primitive calls. *)
Inductive audit_idf_prepare_event (V E B : Type) : Type :=
  | IdfPrepareDom : audit_dom_source_event V E B -> audit_idf_prepare_event V E B
  | IdfPrepareDfs : audit_dfs_nested_event V V (audit_graph_callback_capture V V
  (audit_dom_source_body V B)) ->
      audit_idf_prepare_event V E B
  | IdfPrepareParent : audit_map_event V V B -> audit_idf_prepare_event V E B
  | IdfPrepareLevel : audit_map_event V positive B -> audit_idf_prepare_event V E B
  | IdfPrepareSucc : audit_nat_encoding_event -> audit_idf_prepare_event V E B
  | IdfPrepareOutput : nat -> audit_idf_prepare_event V E B
  | IdfPrepareCase : nat -> audit_idf_prepare_event V E B.
Arguments IdfPrepareDom {V E B} _.
Arguments IdfPrepareDfs {V E B} _.
Arguments IdfPrepareParent {V E B} _.
Arguments IdfPrepareLevel {V E B} _.
Arguments IdfPrepareSucc {V E B} _.
Arguments IdfPrepareOutput {V E B} _.
Arguments IdfPrepareCase {V E B} _.

(** A numbered vertex reads its actual parent and parent's previously computed level. *)
Definition audit_idf_prepare_level_step {V E B} (enc : V -> positive * list B) (parents : Map.t V V)
    (levels : Map.t V positive) (v : V) : Map.t V positive * list (audit_idf_prepare_event V E B) :=
  let '(parent, pe) := audit_map_get enc v parents in
  let '(level, calls) := match parent with
    | None => (1%positive, [IdfPrepareCase 0])
    | Some u => let '(found, reads) := audit_map_get enc u levels in
        let before := match found with None => 1%positive | Some x => x end in
        let '(next, succ) := audit_positive_succ before in
        (next, IdfPrepareCase 1 :: map IdfPrepareLevel reads ++ map IdfPrepareSucc succ)
    end in
  let '(result, writes) := audit_map_set enc v level levels in
  (result, map IdfPrepareParent pe ++ calls ++ map IdfPrepareLevel writes).

(** The forward level fold preserves actual intermediate maps and ordered occurrences. *)
Fixpoint audit_idf_prepare_levels {V E B} (enc : V -> positive * list B) (parents : Map.t V V)
    (vertices : list V) (levels : Map.t V positive) : Map.t V positive * list
  (audit_idf_prepare_event V E B) :=
  match vertices with
  | [] => (levels, [IdfPrepareCase 2])
  | v :: rest =>
      let '(next, here) := audit_idf_prepare_level_step enc parents levels v in
      let '(result, later) := audit_idf_prepare_levels enc parents rest next in
      (result, IdfPrepareCase 3 :: here ++ later)
  end.

(** The prepared forest and levels are coupled in one dependent receipt. *)
Record audit_idf_prepare_receipt (V E B : Type) (EV : encoding V) : Type := IdfPrepareReceipt {
  audit_idf_prepare_forest : Graph.t V V;
  audit_idf_prepare_index : prepared EV audit_idf_prepare_forest;
  audit_idf_prepare_values : Map.t V positive;
  audit_idf_prepare_events : list (audit_idf_prepare_event V E B)
}.
Arguments IdfPrepareReceipt {V E B EV} _ _ _ _.
Arguments audit_idf_prepare_forest {V E B EV} _.
Arguments audit_idf_prepare_index {V E B EV} _.
Arguments audit_idf_prepare_values {V E B EV} _.
Arguments audit_idf_prepare_events {V E B EV} _.

(** Forest preparation builds the original child index and reuses it for level numbering. *)
Definition audit_idf_prepare_source_counted {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (t : dom_tree V) (cb : audit_dfs_callback_model V E B)
    : audit_idf_prepare_receipt V E B EV :=
  let parents := idom t in
  let '(live, live_events) := audit_dfs_source_counted p cb FinSet.empty (Graph.entries g) in
  let vertices := preorder live in
  let '(rows, elements) := audit_map_elements parents in
  let '(children, child_events) := audit_dom_source_children (audit_dfs_encode_model cb) rows in
  let '(roots, root_events) := audit_dom_source_roots (audit_dfs_encode_model cb) parents vertices
  in
  let forest := Graph.Make roots vertices (fun v => index_edges EV children v)
    (fun v => match Map.get EV v parents with Some u => u | None => v end) (fun v => v) in
  let prepare_cb := AuditPrepareCallbackModel V V (audit_dom_source_body V B)
    (audit_dom_source_out (audit_dfs_encode_model cb) children) audit_dom_source_target
    (audit_dom_source_encode (audit_dfs_encode_model cb)) in
  let dfs_cb := AuditDfsCallbackModel V V (audit_dom_source_body V B) audit_dom_source_target
    (audit_dom_source_encode (audit_dfs_encode_model cb)) in
  let '(index, prepare_events) := audit_prepare_source_counted EV forest prepare_cb in
  let '(search, search_events) := audit_dfs_source_counted index dfs_cb FinSet.empty roots in
  let order := rev_append (postorder search) [] in
  let '(levels, level_events) := audit_idf_prepare_levels (E := E) (audit_dfs_encode_model cb)
    parents order Map.empty in
  IdfPrepareReceipt forest index levels
    (map (fun x => IdfPrepareDom (DomSourceInitialDfs x)) live_events ++
     map (fun x => IdfPrepareDom (DomSourceElements x)) elements ++ map IdfPrepareDom child_events
  ++
     map IdfPrepareDom root_events ++ map (fun x => IdfPrepareDom (DomSourcePrepare x))
  prepare_events ++
     map IdfPrepareDfs search_events ++ [IdfPrepareOutput (length (postorder search))] ++
  level_events).

(** The forest and computed levels agree with the exact direct-IDF preparation. *)
Definition audit_idf_prepare_source_erasure_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) (t : dom_tree V)
    (cb : audit_dfs_callback_model V E B),
    audit_dfs_callbacks_erase EV g cb ->
    let receipt := audit_idf_prepare_source_counted p t cb in
    audit_idf_prepare_forest receipt = dom_forest p (idom t) /\
    audit_idf_prepare_values receipt =
      idf_levels EV (idom t) (dom_forest p (idom t)) (prepare EV (dom_forest p (idom t))).

(** The actual forest-index receipt agrees after transporting along the forest equality. *)
Definition audit_idf_prepare_index_erasure_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) (t : dom_tree V)
    (cb : audit_dfs_callback_model V E B),
    audit_dfs_callbacks_erase EV g cb ->
    let receipt := audit_idf_prepare_source_counted p t cb in
    exists Hforest : audit_idf_prepare_forest receipt = dom_forest p (idom t),
      eq_rect _ (prepared EV) (audit_idf_prepare_index receipt) _ Hforest =
        prepare EV (dom_forest p (idom t)).

(** Work prices the actual setup, DFS, map and successor source calls. *)
Definition audit_idf_prepare_event_work {V E B} (weight : B -> nat) (event : audit_idf_prepare_event
  V E B) : nat :=
  let body := fun xs => fold_right (fun x n => weight x + n) 0 xs in
  64 + match event with
  | IdfPrepareDom call => audit_dom_source_event_work weight call
  | IdfPrepareDfs call => audit_dfs_source_event_work (audit_dom_source_body_work weight) call
  | IdfPrepareParent call => audit_map_source_work body [call]
  | IdfPrepareLevel call => audit_map_source_work body [call]
  | IdfPrepareSucc _ => 4
  | IdfPrepareOutput n => audit_graph_reverse_fast_work n
  | IdfPrepareCase _ => 0
  end.

(** External bodies are drawn only from actual encoder and target calls. *)
Definition audit_idf_prepare_event_external {V E B} (weight : B -> nat)
    (event : audit_idf_prepare_event V E B) : nat :=
  match event with
  | IdfPrepareDom call => audit_dom_source_event_external weight call
  | IdfPrepareDfs call => audit_dfs_source_body_work (audit_dom_source_body_external weight) [call]
  | IdfPrepareParent (AuditMapGet _ _ _ _ body _) | IdfPrepareParent (AuditMapSet _ _ _ _ _ body _)
  |
    IdfPrepareParent (AuditMapRemove _ _ _ _ body _) | IdfPrepareLevel (AuditMapGet _ _ _ _ body _)
  |
    IdfPrepareLevel (AuditMapSet _ _ _ _ _ body _) | IdfPrepareLevel (AuditMapRemove _ _ _ _ body _)
  =>
      fold_right (fun x n => weight x + n) 0 body
  | _ => 0
  end.

(** Source work includes trace and output-list composition. *)
Definition audit_idf_prepare_source_work {V E B} (weight : B -> nat) (events : list
  (audit_idf_prepare_event V E B)) : nat :=
  256 * S (length events) * S (length events) +
    fold_right (fun event n => audit_idf_prepare_event_work weight event + n) 0 events.

(** Sum the actual external callback bodies in the same receipt. *)
Definition audit_idf_prepare_source_external {V E B} (weight : B -> nat)
    (events : list (audit_idf_prepare_event V E B)) : nat :=
  fold_right (fun event n => audit_idf_prepare_event_external weight event + n) 0 events.

(** The bound uses only graph, prepared-index and supplied parent-map dimensions. *)
Definition audit_idf_prepare_source_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (t : dom_tree V) : nat :=
  let rows := Map.elements (idom t) in
  let width := fold_right Nat.max 0 (map (fun row =>
    Nat.max (Pos.size_nat (encode EV (fst row))) (Pos.size_nat (encode EV (snd row)))) rows) in
  let scale := S (length rows + width + Pos.to_nat (fuel p) +
    audit_dfs_full_input_width EV g p (Graph.entries g) +
    audit_dfs_source_budget EV g p (Graph.entries g)) in
  1048576 * Nat.pow scale 48.

(** The actual preparation receipt has bounded work and coupled output erasure. *)
Definition audit_idf_prepare_source_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) (t : dom_tree V)
    (cb : audit_dfs_callback_model V E B) (weight : B -> nat),
    audit_dfs_callbacks_erase EV g cb ->
    let receipt := audit_idf_prepare_source_counted p t cb in
    audit_idf_prepare_forest receipt = dom_forest p (idom t) /\
    audit_idf_prepare_values receipt =
      idf_levels EV (idom t) (dom_forest p (idom t)) (prepare EV (dom_forest p (idom t))) /\
    audit_idf_prepare_source_work weight (audit_idf_prepare_events receipt) <=
      audit_idf_prepare_source_budget EV g p t +
      audit_idf_prepare_source_external weight (audit_idf_prepare_events receipt).

(** An internal forest callback prices its captured original encoder input. *)
Definition audit_idf_prepare_body_budget {V B} (encode_budget : V -> nat) (event :
  audit_dom_source_body V B) : nat :=
  match event with
  | DomSourceBodyMap (AuditMapGet v _ _ _ _ _) | DomSourceBodyMap (AuditMapSet v _ _ _ _ _ _) |
    DomSourceBodyMap (AuditMapRemove v _ _ _ _ _) | DomSourceBodyEncode v _ _ => encode_budget v
  | DomSourceBodyTarget _ => 0
  end.

(** The forest setup event prices only actual captured client callbacks. *)
Definition audit_idf_prepare_dom_budget {V E B} (encode_budget : V -> nat) (target_budget : E ->
  nat)
    (event : audit_dom_source_event V E B) : nat :=
  match event with
  | DomSourceInitialDfs (_, calls) =>
      fold_right (fun call n => audit_idf_capture_budget encode_budget target_budget call + n) 0
  calls
  | DomSourceChild (AuditMapGet v _ _ _ _ _) | DomSourceChild (AuditMapSet v _ _ _ _ _ _) |
    DomSourceChild (AuditMapRemove v _ _ _ _ _) | DomSourceParent (AuditMapGet v _ _ _ _ _) |
    DomSourceParent (AuditMapSet v _ _ _ _ _ _) | DomSourceParent (AuditMapRemove v _ _ _ _ _) =>
  encode_budget v
  | DomSourcePrepare call => audit_prepare_source_body_work (audit_idf_prepare_body_budget
  encode_budget) [call]
  | DomSourceDfs call => audit_dfs_source_body_work (audit_idf_prepare_body_budget encode_budget)
  [call]
  | _ => 0
  end.

(** Every preparation event prices the original client input of its captured call. *)
Definition audit_idf_prepare_event_budget {V E B} (encode_budget : V -> nat) (target_budget : E ->
  nat)
    (event : audit_idf_prepare_event V E B) : nat :=
  match event with
  | IdfPrepareDom call => audit_idf_prepare_dom_budget encode_budget target_budget call
  | IdfPrepareDfs call => audit_dfs_source_body_work (audit_idf_prepare_body_budget encode_budget)
  [call]
  | IdfPrepareParent (AuditMapGet v _ _ _ _ _) | IdfPrepareParent (AuditMapSet v _ _ _ _ _ _) |
    IdfPrepareParent (AuditMapRemove v _ _ _ _ _) | IdfPrepareLevel (AuditMapGet v _ _ _ _ _) |
    IdfPrepareLevel (AuditMapSet v _ _ _ _ _ _) | IdfPrepareLevel (AuditMapRemove v _ _ _ _ _) =>
  encode_budget v
  | _ => 0
  end.

(** The adapted bound uses the same actual preparation receipt and per-call client budgets. *)
Definition audit_idf_prepare_source_adapted_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) (t : dom_tree V)
    (cb : audit_dfs_callback_model V E B) (weight : B -> nat)
    encode_source target_source encode_budget target_budget,
    audit_dfs_callbacks_erase EV g cb ->
    audit_graph_external_callback_adapter (audit_dfs_encode_model cb) weight encode_source
  encode_budget ->
    audit_graph_external_callback_adapter (audit_dfs_target_model cb) weight target_source
  target_budget ->
    let receipt := audit_idf_prepare_source_counted p t cb in
    audit_idf_prepare_source_work weight (audit_idf_prepare_events receipt) <=
      audit_idf_prepare_source_budget EV g p t +
      fold_right (fun event n => audit_idf_prepare_event_budget encode_budget target_budget event +
  n) 0
        (audit_idf_prepare_events receipt).

(** This component contract includes the dependent index and level agreements. *)
Definition audit_idf_prepare_source_contract_statement : Prop :=
  audit_idf_prepare_source_erasure_statement /\ audit_idf_prepare_index_erasure_statement /\
  audit_idf_prepare_source_statement /\ audit_idf_prepare_source_adapted_statement.

(** Events carry the exact nested source operations and actual intermediate states. *)
Inductive audit_idf_full_event (V E B : Type) : Type :=
  | IdfFullCase : nat -> audit_idf_full_event V E B
  | IdfFullPrepare : audit_idf_prepare_event V E B -> audit_idf_full_event V E B
  | IdfFullQueue : audit_idf_queue_event V B -> audit_idf_full_event V E B
  | IdfFullPop : audit_queue_nested_event V (positive * list B) -> audit_idf_full_event V E B
  | IdfFullDfs : audit_dfs_nested_event V V (audit_graph_callback_capture V V (audit_dom_source_body
  V B)) ->
      audit_idf_full_event V E B
  | IdfFullCollect : audit_idf_collect_source_event V E B -> audit_idf_full_event V E B
  | IdfFullSet : audit_set_event V B -> audit_idf_full_event V E B
  | IdfFullAdd : audit_idf_nadd_event -> audit_idf_full_event V E B
  | IdfFullEmpty : PQueue.t V -> bool -> audit_idf_full_event V E B
  | IdfFullFuel : nat -> positive -> audit_idf_full_event V E B.
Arguments IdfFullCase {V E B} _.
Arguments IdfFullPrepare {V E B} _.
Arguments IdfFullQueue {V E B} _.
Arguments IdfFullPop {V E B} _.
Arguments IdfFullDfs {V E B} _.
Arguments IdfFullCollect {V E B} _.
Arguments IdfFullSet {V E B} _.
Arguments IdfFullAdd {V E B} _.
Arguments IdfFullEmpty {V E B} _ _.
Arguments IdfFullFuel {V E B} _ _.

(** Set insertion processes every freshly reached vertex in order. *)
Fixpoint audit_idf_full_scan {V E B} (enc : V -> positive * list B) (vertices : list V) (set :
  FinSet.t V)
    : FinSet.t V * list (audit_idf_full_event V E B) :=
  match vertices with
  | [] => (set, [IdfFullCase 0])
  | v :: rest =>
      let '(next, calls) := audit_finset_add enc v set in
      let '(result, events) := audit_idf_full_scan enc rest next in
      (result, IdfFullCase 1 :: map IdfFullSet calls ++ events)
  end.

(** Emission folds the actual priority, set and queue source operation over all collected
    targets. *)
Fixpoint audit_idf_full_emit {V E B} (enc : V -> positive * list B) (ceiling : positive)
    (levels : Map.t V positive) (vertices : list V) (state : IdfState.t V)
    : IdfState.t V * list (audit_idf_full_event V E B) :=
  match vertices with
  | [] => (state, [IdfFullCase 2])
  | v :: rest =>
      let '(next, calls) := audit_idf_queue_emit enc ceiling levels state v in
      let '(result, events) := audit_idf_full_emit enc ceiling levels rest next in
      (result, IdfFullCase 3 :: map IdfFullQueue calls ++ events)
  end.

(** A pop executes the actual fresh-subtree DFS, collection, scans and emissions. *)
Definition audit_idf_full_step {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (t : dom_tree V) (forest : Graph.t V V) (index : prepared EV forest)
    (levels : Map.t V positive) (enc : V -> positive * list B) (target : E -> V * list B)
    (live : V -> bool * list B) (state : IdfState.t V) : IdfState.t V * list (audit_idf_full_event V
  E B) :=
  let '(popped, pop_calls) := audit_queue_recorded_pop enc (IdfState.pending state) in
  match popped with
  | None => (state, map IdfFullPop pop_calls ++ [IdfFullCase 4])
  | Some (_, root, rest) =>
      let dfs_cb := AuditDfsCallbackModel V V (audit_dom_source_body V B) audit_dom_source_target
        (audit_dom_source_encode enc) in
      let '(search, dfs_calls) := audit_dfs_source_counted index dfs_cb (IdfState.scanned state)
  [root] in
      let fresh := preorder search in
      let '(collected, collect_calls) := audit_idf_collect_source_nodes p enc target live t root
  fresh ([], 0%N) in
      let '(scanned, scan_calls) := audit_idf_full_scan enc fresh (IdfState.scanned state) in
      let '(processed, process_calls) := audit_finset_add enc root (IdfState.processed state) in
      let '(visits, add_calls) := audit_idf_nadd_counted (IdfState.edge_visits state) (snd
  collected) in
      let started := IdfState.Make rest (IdfState.emitted state) scanned processed
        (root :: IdfState.trace state) visits (IdfState.output_count state) in
      let '(result, emit_calls) := audit_idf_full_emit enc (fuel p) levels (fst collected) started
  in
      (result, map IdfFullPop pop_calls ++ [IdfFullCase 5] ++ map IdfFullDfs dfs_calls ++
        map IdfFullCollect collect_calls ++ scan_calls ++ map IdfFullSet process_calls ++
        map IdfFullAdd add_calls ++ emit_calls)
  end.

(** Binary iteration tests the actual queue before each recursive call. *)
Fixpoint audit_idf_full_run {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (t : dom_tree V) (forest : Graph.t V V) (index : prepared EV forest)
    (levels : Map.t V positive) (enc : V -> positive * list B) (target : E -> V * list B)
    (live : V -> bool * list B) (fuel : positive) (state : IdfState.t V)
    : IdfState.t V * list (audit_idf_full_event V E B) :=
  let empty := PQueue.is_empty (IdfState.pending state) in
  if empty then (state, [IdfFullEmpty (IdfState.pending state) true; IdfFullCase 6]) else
    match fuel with
    | xH => let '(result, events) := audit_idf_full_step p t forest index levels enc target live
  state in
        (result, IdfFullEmpty (IdfState.pending state) false :: IdfFullCase 7 :: events)
    | xO half =>
        let '(middle, first) := audit_idf_full_run p t forest index levels enc target live half
  state in
        let '(result, later) := audit_idf_full_run p t forest index levels enc target live half
  middle in
        (result, IdfFullEmpty (IdfState.pending state) false :: IdfFullCase 8 :: first ++ later)
    | xI half =>
        let '(middle, first) := audit_idf_full_run p t forest index levels enc target live half
  state in
        let '(last, later) := audit_idf_full_run p t forest index levels enc target live half middle
  in
        let '(result, calls) := audit_idf_full_step p t forest index levels enc target live last in
        (result, IdfFullEmpty (IdfState.pending state) false :: IdfFullCase 9 :: first ++ later ++
  calls)
    end.

(** The whole direct producer shares one preparation receipt with its actual worklist run. *)
Definition audit_idf_full_source_counted {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (t : dom_tree V) (defs : list V) (cb : audit_dfs_callback_model V E B)
    (live : V -> bool * list B) : FinSet.t V * list (audit_idf_full_event V E B) :=
  let receipt := audit_idf_prepare_source_counted p t cb in
  let forest := audit_idf_prepare_forest receipt in let index := audit_idf_prepare_index receipt in
  let levels := audit_idf_prepare_values receipt in let enc := audit_dfs_encode_model cb in
  let '(pending, seed_calls) := audit_idf_queue_seeds enc (fuel p) levels defs PQueue.empty in
  let initial := IdfState.Make pending FinSet.empty FinSet.empty FinSet.empty [] 0%N 0%N in
  let run_fuel := Pos.of_succ_nat (length (Graph.nodes g)) in
  let '(result, run_calls) := audit_idf_full_run p t forest index levels enc (audit_dfs_target_model
  cb)
    live run_fuel initial in
  (IdfState.emitted result, map IdfFullPrepare (audit_idf_prepare_events receipt) ++ map
  IdfFullQueue seed_calls ++
    [IdfFullFuel (length (Graph.nodes g)) run_fuel] ++ run_calls).

(** The actual same-run producer erases to the direct pruned IDF result. *)
Definition audit_idf_full_source_erasure_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) (t : dom_tree V) defs
    (cb : audit_dfs_callback_model V E B) (live : V -> bool * list B) (live_value : V -> bool),
    audit_dfs_callbacks_erase EV g cb -> (forall v, fst (live v) = live_value v) ->
    fst (audit_idf_full_source_counted p t defs cb live) = direct_pruned_idf p t defs live_value.

(** Source work prices every concrete nested primitive and captured callback body. *)
Definition audit_idf_full_event_work {V E B} (weight : B -> nat) (event : audit_idf_full_event V E
  B) : nat :=
  let body := fun xs => fold_right (fun x n => weight x + n) 0 xs in
  64 + match event with
  | IdfFullPrepare call => audit_idf_prepare_event_work weight call
  | IdfFullQueue call => audit_idf_queue_event_work weight call
  | IdfFullPop call => audit_queue_recorded_full_source_work weight [call]
  | IdfFullDfs call => audit_dfs_source_event_work (audit_dom_source_body_work weight) call
  | IdfFullCollect call => audit_idf_collect_source_event_work weight call
  | IdfFullSet call => audit_finset_source_work body [call]
  | IdfFullAdd _ => 16
  | IdfFullFuel n _ => 64 * S n * S n
  | IdfFullEmpty _ _ | IdfFullCase _ => 0
  end.

(** External work contains only actual supplied encoder, target and live callback bodies. *)
Definition audit_idf_full_event_external {V E B} (weight : B -> nat)
    (event : audit_idf_full_event V E B) : nat :=
  match event with
  | IdfFullPrepare call => audit_idf_prepare_event_external weight call
  | IdfFullQueue call => audit_idf_queue_event_external weight call
  | IdfFullPop call => audit_idf_queue_push_external weight call
  | IdfFullDfs call => audit_dfs_source_body_work (audit_dom_source_body_external weight) [call]
  | IdfFullCollect call => audit_idf_collect_source_event_external weight call
  | IdfFullSet (AuditSetMem _ _ _ _ body _) | IdfFullSet (AuditSetAdd _ _ _ _ body _) |
    IdfFullSet (AuditSetRemove _ _ _ _ body _) => fold_right (fun x n => weight x + n) 0 body
  | _ => 0
  end.

(** Whole-source work charges nested frames and source trace-list concatenation. *)
Definition audit_idf_full_source_work {V E B} (weight : B -> nat) (events : list
  (audit_idf_full_event V E B)) : nat :=
  256 * Nat.pow (S (length events)) 3 +
    fold_right (fun event n => audit_idf_full_event_work weight event + n) 0 events.

(** The callback charge sums bodies from the same source run. *)
Definition audit_idf_full_source_external {V E B} (weight : B -> nat)
    (events : list (audit_idf_full_event V E B)) : nat :=
  fold_right (fun event n => audit_idf_full_event_external weight event + n) 0 events.

(** The scale uses only original graph, prepared index, tree and definition inputs. *)
Definition audit_idf_full_input_scale {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (t : dom_tree V) (defs : list V) : nat :=
  let out_rows := Map.elements (out_index p) in
  let edges := flat_map snd out_rows in
  let parents := Map.elements (idom t) in
  let tins := Map.elements (tin t) in let touts := Map.elements (tout t) in
  let vertices := defs ++ Graph.nodes g ++ Graph.entries g ++ map fst out_rows ++
    map (Graph.target g) edges ++ map fst parents ++ map snd parents ++ map fst tins ++ map fst
  touts in
  let vertex_width := fold_right Nat.max 0 (map (fun v => Pos.size_nat (encode EV v)) vertices) in
  let rank_width := fold_right Nat.max 0 (map (fun row => Pos.size_nat (snd row)) (tins ++ touts))
  in
  S (length vertices + length edges + length parents + vertex_width + rank_width +
    Pos.to_nat (fuel p) + audit_idf_prepare_source_budget EV g p t).

(** The complete bound does not depend on returned work or callback events. *)
Definition audit_idf_full_input_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (t : dom_tree V) (defs : list V) : nat :=
  1048576 * Nat.pow (audit_idf_full_input_scale EV g p t defs) 128.

(** The pruned producer has the exact result and an original-input source-work bound. *)
Definition audit_idf_full_source_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) (t : dom_tree V) defs
    (cb : audit_dfs_callback_model V E B) (live : V -> bool * list B) (live_value : V -> bool)
  (weight : B -> nat),
    audit_dfs_callbacks_erase EV g cb -> (forall v, fst (live v) = live_value v) ->
    let '(result, events) := audit_idf_full_source_counted p t defs cb live in
    result = direct_pruned_idf p t defs live_value /\ audit_idf_full_source_work weight events <=
      audit_idf_full_input_budget EV g p t defs + audit_idf_full_source_external weight events.

(** The unpruned producer fixes its internal live predicate and has the same bound. *)
Definition audit_idf_full_unpruned_source_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) (t : dom_tree V) defs
    (cb : audit_dfs_callback_model V E B) (weight : B -> nat),
    audit_dfs_callbacks_erase EV g cb ->
    let '(result, events) := audit_idf_full_source_counted p t defs cb (fun _ => (true, [])) in
    result = direct_idf p t defs /\ audit_idf_full_source_work weight events <=
      audit_idf_full_input_budget EV g p t defs + audit_idf_full_source_external weight events.

(** Each event prices its actual client input, including nested forest callbacks. *)
Definition audit_idf_full_event_budget {V E B} (encode_budget live_budget : V -> nat) (target_budget
  : E -> nat)
    (event : audit_idf_full_event V E B) : nat :=
  match event with
  | IdfFullPrepare call => audit_idf_prepare_event_budget encode_budget target_budget call
  | IdfFullQueue call => audit_idf_queue_event_budget encode_budget call
  | IdfFullPop call => audit_idf_queue_push_budget encode_budget call
  | IdfFullDfs call => audit_dfs_source_body_work (audit_idf_prepare_body_budget encode_budget)
  [call]
  | IdfFullCollect call => audit_idf_collect_source_event_budget encode_budget live_budget
  target_budget call
  | IdfFullSet (AuditSetMem v _ _ _ _ _) | IdfFullSet (AuditSetAdd v _ _ _ _ _) |
    IdfFullSet (AuditSetRemove v _ _ _ _ _) => encode_budget v
  | _ => 0
  end.

(** The pruned source bound applies each law to actual recorded callback invocations. *)
Definition audit_idf_full_source_adapted_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) (t : dom_tree V) defs
    (cb : audit_dfs_callback_model V E B) (live : V -> bool * list B) (live_value : V -> bool)
  (weight : B -> nat)
    encode_source target_source live_source encode_budget target_budget live_budget,
    audit_dfs_callbacks_erase EV g cb -> (forall v, fst (live v) = live_value v) ->
    audit_graph_external_callback_adapter (audit_dfs_encode_model cb) weight encode_source
  encode_budget ->
    audit_graph_external_callback_adapter (audit_dfs_target_model cb) weight target_source
  target_budget ->
    audit_graph_external_callback_adapter live weight live_source live_budget ->
    let '(result, events) := audit_idf_full_source_counted p t defs cb live in
    result = direct_pruned_idf p t defs live_value /\ audit_idf_full_source_work weight events <=
      audit_idf_full_input_budget EV g p t defs +
      fold_right (fun event n => audit_idf_full_event_budget encode_budget live_budget target_budget
  event + n) 0 events.

(** The unpruned source bound has no external live-predicate assumption or charge. *)
Definition audit_idf_full_unpruned_adapted_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) (t : dom_tree V) defs
    (cb : audit_dfs_callback_model V E B) (weight : B -> nat) encode_source target_source
  encode_budget target_budget,
    audit_dfs_callbacks_erase EV g cb ->
    audit_graph_external_callback_adapter (audit_dfs_encode_model cb) weight encode_source
  encode_budget ->
    audit_graph_external_callback_adapter (audit_dfs_target_model cb) weight target_source
  target_budget ->
    let '(result, events) := audit_idf_full_source_counted p t defs cb (fun _ => (true, [])) in
    result = direct_idf p t defs /\ audit_idf_full_source_work weight events <=
      audit_idf_full_input_budget EV g p t defs +
      fold_right (fun event n => audit_idf_full_event_budget encode_budget (fun _ => 0)
  target_budget event + n) 0 events.

(** The complete direct-IDF source contract includes each actual producer and primitive boundary. *)
Definition audit_idf_full_source_contract_statement : Prop :=
  audit_idf_full_source_erasure_statement /\ audit_idf_full_source_statement /\
  audit_idf_full_unpruned_source_statement /\ audit_idf_full_source_adapted_statement /\
  audit_idf_full_unpruned_adapted_statement /\ audit_idf_prepare_source_contract_statement /\
  audit_idf_queue_source_contract_statement /\ audit_idf_collect_source_contract_statement /\
  audit_idf_nadd_source_statement /\ audit_idf_sub_source_statement /\
  audit_queue_full_source_contract_statement.
```

## Galois.Graph.GraphAuditCost

Card: AUD-GR-MODELS

Source destination: `theories/Graph/GraphAuditCost.v`.

```rocq
(** * Graph source-cost facade

    The facade exposes the complete leaf source contracts without adding bridge dependencies.
    For example, the default dominator contract does not wait for the Semi-NCA selector proof.
    Builds on: graph audit leaf models and their source adapters. *)
From Galois.Graph Require Export GraphAuditBase GraphAuditDfs GraphAuditVirtual
  GraphAuditVirtualAdapter
  GraphAuditScc GraphAuditWto GraphAuditLoops GraphAuditSemiDominators GraphAuditLengauerTarjan
  GraphAuditSemiNca GraphAuditDominators GraphAuditDominatorsAdapter GraphAuditDominatorSelect
  GraphAuditFrontier GraphAuditFrontierAdapter GraphAuditIdf.

(** The family contract names the actual source and adapted boundary for every graph producer. *)
Definition graph_audit_source_contract_statement : Prop :=
  audit_prepare_source_contract_statement /\ audit_dfs_source_contract_statement /\
  audit_virtual_full_source_statement /\ audit_virtual_full_callbacks_statement /\
  audit_virtual_entries_full_statement /\ audit_erase_nested_statement /\
  audit_virtual_source_search_adapted_statement /\ audit_scc_source_contract_statement /\
  audit_wto_source_contract_statement /\ audit_loop_full_source_contract_statement /\
  audit_semi_producer_nested_erasure_statement /\ audit_semi_producer_nested_unique_statement /\
  audit_semi_producer_nested_bound_statement /\ audit_lt_nested_erasure_statement /\
  audit_lt_nested_unique_statement /\ audit_lt_nested_bound_statement /\
  audit_default_dom_single_adapted_statement /\ audit_virtual_nca_source_full_contract_statement /\
  audit_flat_source_full_contract_statement /\ audit_check_idom_source_full_contract_statement /\
  audit_dom_select_source_full_contract_statement /\ audit_frontier_source_adapted_statement /\
  audit_idf_full_source_contract_statement.
```

### Future proofs in `GraphAuditBaseAdequacy`

Card: AUD-GR-BASE

Source destination: `theories/Graph/GraphAuditBaseAdequacy.v`.

```rocq
From Galois.Graph Require Import GraphAuditBase.

Theorem audit_graph_prepare_execution_exists_holds :
  GraphAuditBase.audit_graph_prepare_execution_exists_statement.
Theorem audit_graph_prepare_map_model_holds :
  GraphAuditBase.audit_graph_prepare_map_model_statement.
Theorem audit_graph_prepare_emission_holds :
  GraphAuditBase.audit_graph_prepare_emission_statement.
Theorem audit_graph_prepare_model_holds :
  GraphAuditBase.audit_graph_prepare_model_statement.
Theorem audit_graph_prepare_full_correct :
  GraphAuditBase.audit_graph_prepare_full_statement.
Theorem audit_graph_prepare_nested_correct :
  GraphAuditBase.audit_graph_prepare_nested_statement.
Theorem audit_pos_iter_holds :
  GraphAuditBase.audit_pos_iter_statement.
Theorem audit_n_iter_holds :
  GraphAuditBase.audit_n_iter_statement.
Theorem audit_fold_holds :
  GraphAuditBase.audit_fold_statement.
Theorem audit_list_map_filter_exists_holds :
  GraphAuditBase.audit_list_map_filter_exists_statement.
Theorem audit_graph_reverse_run_holds :
  GraphAuditBase.audit_graph_reverse_run_statement.
Theorem audit_graph_reverse_fast_run_holds :
  GraphAuditBase.audit_graph_reverse_fast_run_statement.
Theorem audit_graph_reverse_fast_counted_holds :
  GraphAuditBase.audit_graph_reverse_fast_counted_statement.
Theorem audit_prepare_source_correct :
  GraphAuditBase.audit_prepare_source_statement.
Theorem audit_prepare_source_adapted_holds :
  GraphAuditBase.audit_prepare_source_adapted_statement.
Theorem audit_prepare_source_contract_holds :
  GraphAuditBase.audit_prepare_source_contract_statement.
```

### Future proofs in `GraphAuditCostAdequacy`

Card: AUD-GR

Source destination: `theories/Graph/GraphAuditCostAdequacy.v`.

```rocq
From Galois.Graph Require Import GraphAuditCost.

Theorem graph_audit_source_contract_holds :
  GraphAuditCost.graph_audit_source_contract_statement.
```

### Future proofs in `GraphAuditDfsAdequacy`

Card: AUD-GR-DFS

Source destination: `theories/Graph/GraphAuditDfsAdequacy.v`.

```rocq
From Galois.Graph Require Import GraphAuditDfs.

Theorem audit_dfs_counted_correct :
  GraphAuditDfs.audit_dfs_counted_statement.
Theorem audit_dfs_helpers_correct :
  GraphAuditDfs.audit_dfs_helpers_statement.
Theorem audit_dfs_full_counted_correct :
  GraphAuditDfs.audit_dfs_full_counted_statement.
Theorem audit_dfs_nested_correct :
  GraphAuditDfs.audit_dfs_nested_statement.
Theorem audit_graph_capture_callbacks_erases_holds :
  GraphAuditDfs.audit_graph_capture_callbacks_erases_statement.
Theorem audit_dfs_source_correct :
  GraphAuditDfs.audit_dfs_source_statement.
Theorem audit_dfs_source_successor_correspondence_holds :
  GraphAuditDfs.audit_dfs_source_successor_correspondence_statement.
Theorem audit_dfs_source_adapted_holds :
  GraphAuditDfs.audit_dfs_source_adapted_statement.
Theorem audit_dfs_source_contract_holds :
  GraphAuditDfs.audit_dfs_source_contract_statement.
```

### Future proofs in `GraphAuditDominatorSelectAdequacy`

Card: AUD-GR-DOM-SELECT

Source destination: `theories/Graph/GraphAuditDominatorSelectAdequacy.v`.

```rocq
From Galois.Graph Require Import GraphAuditDominatorSelect.

Theorem audit_nca_backend_erasure :
  GraphAuditDominatorSelect.audit_nca_backend_erasure_statement.
Theorem audit_dom_tree_with_erasure :
  GraphAuditDominatorSelect.audit_dom_tree_with_erasure_statement.
Theorem audit_dom_tree_default_erasure_holds :
  GraphAuditDominatorSelect.audit_dom_tree_default_erasure_statement.
Theorem audit_flat_source_holds :
  GraphAuditDominatorSelect.audit_flat_source_statement.
Theorem audit_check_idom_source_holds :
  GraphAuditDominatorSelect.audit_check_idom_source_statement.
Theorem audit_dom_select_single_run_holds :
  GraphAuditDominatorSelect.audit_dom_select_single_run_statement.
Theorem audit_virtual_nca_single_run_holds :
  GraphAuditDominatorSelect.audit_virtual_nca_single_run_statement.
Theorem audit_flat_source_adapted_holds :
  GraphAuditDominatorSelect.audit_flat_source_adapted_statement.
Theorem audit_flat_source_contract_holds :
  GraphAuditDominatorSelect.audit_flat_source_contract_statement.
Theorem audit_check_idom_source_adapted_holds :
  GraphAuditDominatorSelect.audit_check_idom_source_adapted_statement.
Theorem audit_check_idom_source_contract_holds :
  GraphAuditDominatorSelect.audit_check_idom_source_contract_statement.
Theorem audit_dom_select_single_adapted_holds :
  GraphAuditDominatorSelect.audit_dom_select_single_adapted_statement.
Theorem audit_dom_select_source_contract_holds :
  GraphAuditDominatorSelect.audit_dom_select_source_contract_statement.
Theorem audit_virtual_nca_single_adapted_holds :
  GraphAuditDominatorSelect.audit_virtual_nca_single_adapted_statement.
Theorem audit_virtual_nca_source_contract_holds :
  GraphAuditDominatorSelect.audit_virtual_nca_source_contract_statement.
Theorem audit_flat_source_full_contract_holds :
  GraphAuditDominatorSelect.audit_flat_source_full_contract_statement.
Theorem audit_check_idom_source_full_contract_holds :
  GraphAuditDominatorSelect.audit_check_idom_source_full_contract_statement.
Theorem audit_virtual_nca_source_full_contract_holds :
  GraphAuditDominatorSelect.audit_virtual_nca_source_full_contract_statement.
Theorem audit_dom_select_source_full_contract_holds :
  GraphAuditDominatorSelect.audit_dom_select_source_full_contract_statement.
```

### Future proofs in `GraphAuditDominatorsAdequacy`

Card: AUD-GR-DOM

Source destination: `theories/Graph/GraphAuditDominatorsAdequacy.v`.

```rocq
From Galois.Graph Require Import GraphAuditDominators.

Theorem audit_lt_backend_erasure :
  GraphAuditDominators.audit_lt_backend_erasure_statement.
Theorem audit_dom_tree_counted_correct :
  GraphAuditDominators.audit_dom_tree_counted_statement.
Theorem audit_dom_search_source_correct :
  GraphAuditDominators.audit_dom_search_source_statement.
Theorem audit_default_dom_single_run_holds :
  GraphAuditDominators.audit_default_dom_single_run_statement.
```

### Future proofs in `GraphAuditDominatorsAdapterAdequacy`

Card: AUD-GR-DOM

Source destination: `theories/Graph/GraphAuditDominatorsAdapterAdequacy.v`.

```rocq
From Galois.Graph Require Import GraphAuditDominatorsAdapter.

Theorem audit_default_dom_single_adapted_holds :
  GraphAuditDominatorsAdapter.audit_default_dom_single_adapted_statement.
```

### Future proofs in `GraphAuditFrontierAdequacy`

Card: AUD-GR-DF

Source destination: `theories/Graph/GraphAuditFrontierAdequacy.v`.

```rocq
From Galois.Graph Require Import GraphAuditFrontier.

Theorem audit_frontier_dom_correct :
  GraphAuditFrontier.audit_frontier_dom_statement.
Theorem audit_frontier_runner_correct :
  GraphAuditFrontier.audit_frontier_runner_statement.
Theorem audit_frontier_counted_correct :
  GraphAuditFrontier.audit_frontier_counted_statement.
Theorem audit_ifrontier_correct :
  GraphAuditFrontier.audit_ifrontier_statement.
Theorem audit_frontier_source_correct :
  GraphAuditFrontier.audit_frontier_source_statement.
```

### Future proofs in `GraphAuditFrontierAdapterAdequacy`

Card: AUD-GR-DF

Source destination: `theories/Graph/GraphAuditFrontierAdapterAdequacy.v`.

```rocq
From Galois.Graph Require Import GraphAuditFrontierAdapter.

Theorem audit_frontier_source_adapted_holds :
  GraphAuditFrontierAdapter.audit_frontier_source_adapted_statement.
```

### Future proofs in `GraphAuditIdfAdequacy`

Card: AUD-GR-IDF

Source destination: `theories/Graph/GraphAuditIdfAdequacy.v`.

```rocq
From Galois.Graph Require Import GraphAuditIdf.

Theorem audit_idf_collect_correct :
  GraphAuditIdf.audit_idf_collect_statement.
Theorem audit_idf_initial_correct :
  GraphAuditIdf.audit_idf_initial_statement.
Theorem audit_idf_work_step_correct :
  GraphAuditIdf.audit_idf_work_step_statement.
Theorem audit_idf_run_correct :
  GraphAuditIdf.audit_idf_run_statement.
Theorem audit_direct_pruned_idf_correct :
  GraphAuditIdf.audit_direct_pruned_idf_statement.
Theorem audit_direct_idf_correct :
  GraphAuditIdf.audit_direct_idf_statement.
Theorem audit_direct_pruned_idf_selected_bound :
  GraphAuditIdf.audit_direct_pruned_idf_selected_bound_statement.
Theorem audit_idf_collect_source_erasure_holds :
  GraphAuditIdf.audit_idf_collect_source_erasure_statement.
Theorem audit_idf_collect_source_bound_holds :
  GraphAuditIdf.audit_idf_collect_source_bound_statement.
Theorem audit_idf_collect_source_adapted_holds :
  GraphAuditIdf.audit_idf_collect_source_adapted_statement.
Theorem audit_idf_collect_source_contract_holds :
  GraphAuditIdf.audit_idf_collect_source_contract_statement.
Theorem audit_idf_queue_source_erasure_holds :
  GraphAuditIdf.audit_idf_queue_source_erasure_statement.
Theorem audit_idf_queue_source_bound_holds :
  GraphAuditIdf.audit_idf_queue_source_bound_statement.
Theorem audit_idf_queue_source_adapted_holds :
  GraphAuditIdf.audit_idf_queue_source_adapted_statement.
Theorem audit_idf_queue_source_contract_holds :
  GraphAuditIdf.audit_idf_queue_source_contract_statement.
Theorem audit_idf_prepare_source_erasure_holds :
  GraphAuditIdf.audit_idf_prepare_source_erasure_statement.
Theorem audit_idf_prepare_index_erasure_holds :
  GraphAuditIdf.audit_idf_prepare_index_erasure_statement.
Theorem audit_idf_prepare_source_holds :
  GraphAuditIdf.audit_idf_prepare_source_statement.
Theorem audit_idf_prepare_source_adapted_holds :
  GraphAuditIdf.audit_idf_prepare_source_adapted_statement.
Theorem audit_idf_prepare_source_contract_holds :
  GraphAuditIdf.audit_idf_prepare_source_contract_statement.
Theorem audit_idf_full_source_erasure_holds :
  GraphAuditIdf.audit_idf_full_source_erasure_statement.
Theorem audit_idf_full_source_holds :
  GraphAuditIdf.audit_idf_full_source_statement.
Theorem audit_idf_full_unpruned_source_holds :
  GraphAuditIdf.audit_idf_full_unpruned_source_statement.
Theorem audit_idf_full_source_adapted_holds :
  GraphAuditIdf.audit_idf_full_source_adapted_statement.
Theorem audit_idf_full_unpruned_adapted_holds :
  GraphAuditIdf.audit_idf_full_unpruned_adapted_statement.
Theorem audit_idf_full_source_contract_holds :
  GraphAuditIdf.audit_idf_full_source_contract_statement.
```

### Future proofs in `GraphAuditLengauerTarjanAdequacy`

Card: AUD-GR-LT

Source destination: `theories/Graph/GraphAuditLengauerTarjanAdequacy.v`.

```rocq
From Galois.Graph Require Import GraphAuditLengauerTarjan.

Theorem audit_lt_compute_correct :
  GraphAuditLengauerTarjan.audit_lt_compute_statement.
Theorem audit_lt_compute_unique :
  GraphAuditLengauerTarjan.audit_lt_compute_unique_statement.
Theorem audit_lt_nested_erasure :
  GraphAuditLengauerTarjan.audit_lt_nested_erasure_statement.
Theorem audit_lt_nested_unique :
  GraphAuditLengauerTarjan.audit_lt_nested_unique_statement.
Theorem audit_lt_nested_bound :
  GraphAuditLengauerTarjan.audit_lt_nested_bound_statement.
Theorem audit_virtual_lt_erasure :
  GraphAuditLengauerTarjan.audit_virtual_lt_erasure_statement.
```

### Future proofs in `GraphAuditLoopsAdequacy`

Card: AUD-GR-LOOP

Source destination: `theories/Graph/GraphAuditLoopsAdequacy.v`.

```rocq
From Galois.Graph Require Import GraphAuditLoops.

Theorem audit_loop_counted_correct :
  GraphAuditLoops.audit_loop_counted_statement.
Theorem audit_loop_steps_erasure_holds :
  GraphAuditLoops.audit_loop_steps_erasure_statement.
Theorem audit_loop_steps_bound_holds :
  GraphAuditLoops.audit_loop_steps_bound_statement.
Theorem audit_loop_pack_source_holds :
  GraphAuditLoops.audit_loop_pack_source_statement.
Theorem audit_loop_full_source_erasure_holds :
  GraphAuditLoops.audit_loop_full_source_erasure_statement.
Theorem audit_loop_full_source_holds :
  GraphAuditLoops.audit_loop_full_source_statement.
Theorem audit_loop_full_source_adapted_holds :
  GraphAuditLoops.audit_loop_full_source_adapted_statement.
Theorem audit_loop_full_source_contract_holds :
  GraphAuditLoops.audit_loop_full_source_contract_statement.
```

### Future proofs in `GraphAuditSccAdequacy`

Card: AUD-GR-SCC

Source destination: `theories/Graph/GraphAuditSccAdequacy.v`.

```rocq
From Galois.Graph Require Import GraphAuditScc.

Theorem audit_tarjan_helpers_erasure :
  GraphAuditScc.audit_tarjan_helpers_erasure_statement.
Theorem audit_tarjan_helpers_event_bound :
  GraphAuditScc.audit_tarjan_helpers_event_bound_statement.
Theorem audit_scc_within_counted_correct :
  GraphAuditScc.audit_scc_within_counted_statement.
Theorem audit_scc_within_nested_holds :
  GraphAuditScc.audit_scc_within_nested_statement.
Theorem audit_scc_within_nested_total_holds :
  GraphAuditScc.audit_scc_within_nested_total_statement.
Theorem audit_scc_reverse_run_holds :
  GraphAuditScc.audit_scc_reverse_run_statement.
Theorem audit_scc_source_correct :
  GraphAuditScc.audit_scc_source_statement.
Theorem audit_scc_min_source_model_holds :
  GraphAuditScc.audit_scc_min_source_model_statement.
Theorem audit_scc_source_primitive_correspondence_holds :
  GraphAuditScc.audit_scc_source_primitive_correspondence_statement.
Theorem audit_scc_source_primitives_correct :
  GraphAuditScc.audit_scc_source_library_obligations.
Theorem audit_scc_source_adapted_correct :
  GraphAuditScc.audit_scc_source_adapted_statement.
Theorem audit_scc_source_contract_correct :
  GraphAuditScc.audit_scc_source_contract_statement.
```

### Future proofs in `GraphAuditSemiDominatorsAdequacy`

Card: AUD-GR-SEMI

Source destination: `theories/Graph/GraphAuditSemiDominatorsAdequacy.v`.

```rocq
From Galois.Graph Require Import GraphAuditSemiDominators.

Theorem audit_semi_compress_correct :
  GraphAuditSemiDominators.audit_semi_compress_statement.
Theorem audit_semi_compress_unique :
  GraphAuditSemiDominators.audit_semi_compress_unique_statement.
Theorem audit_semi_compute_correct :
  GraphAuditSemiDominators.audit_semi_compute_statement.
Theorem audit_semi_compute_unique :
  GraphAuditSemiDominators.audit_semi_compute_unique_statement.
Theorem audit_semi_nested_compress_erasure :
  GraphAuditSemiDominators.audit_semi_nested_compress_erasure_statement.
Theorem audit_semi_nested_compress_unique :
  GraphAuditSemiDominators.audit_semi_nested_compress_unique_statement.
Theorem audit_semi_nested_compress_bound :
  GraphAuditSemiDominators.audit_semi_nested_compress_bound_statement.
Theorem audit_semi_producer_nested_erasure :
  GraphAuditSemiDominators.audit_semi_producer_nested_erasure_statement.
Theorem audit_semi_producer_nested_unique :
  GraphAuditSemiDominators.audit_semi_producer_nested_unique_statement.
Theorem audit_semi_producer_nested_bound :
  GraphAuditSemiDominators.audit_semi_producer_nested_bound_statement.
Theorem audit_virtual_semi_erasure_holds :
  GraphAuditSemiDominators.audit_virtual_semi_erasure_statement.
```

### Future proofs in `GraphAuditSemiNcaAdequacy`

Card: AUD-GR-SNCA

Source destination: `theories/Graph/GraphAuditSemiNcaAdequacy.v`.

```rocq
From Galois.Graph Require Import GraphAuditSemiNca.

Theorem audit_nca_walk_correct :
  GraphAuditSemiNca.audit_nca_walk_statement.
Theorem audit_nca_walk_unique :
  GraphAuditSemiNca.audit_nca_walk_unique_statement.
Theorem audit_nca_compute_correct :
  GraphAuditSemiNca.audit_nca_compute_statement.
Theorem audit_nca_compute_unique :
  GraphAuditSemiNca.audit_nca_compute_unique_statement.
Theorem audit_nca_source_holds :
  GraphAuditSemiNca.audit_nca_source_statement.
Theorem audit_nca_source_unique_holds :
  GraphAuditSemiNca.audit_nca_source_unique_statement.
```

### Future proofs in `GraphAuditVirtualAdequacy`

Card: AUD-GR-VIRTUAL

Source destination: `theories/Graph/GraphAuditVirtualAdequacy.v`.

```rocq
From Galois.Graph Require Import GraphAuditVirtual.

Theorem audit_virtual_callbacks_correct :
  GraphAuditVirtual.audit_virtual_callbacks_statement.
Theorem audit_virtual_search_correct :
  GraphAuditVirtual.audit_virtual_search_statement.
Theorem audit_virtual_entries_correct :
  GraphAuditVirtual.audit_virtual_entries_statement.
Theorem audit_virtual_search_bound :
  GraphAuditVirtual.audit_virtual_search_bound_statement.
Theorem audit_erase_virtual_correct :
  GraphAuditVirtual.audit_erase_virtual_statement.
Theorem audit_erase_nested_correct :
  GraphAuditVirtual.audit_erase_nested_statement.
Theorem audit_virtual_entries_full_correct :
  GraphAuditVirtual.audit_virtual_entries_full_statement.
Theorem audit_virtual_entries_full_total_holds :
  GraphAuditVirtual.audit_virtual_entries_full_total_statement.
Theorem audit_virtual_full_source_correct :
  GraphAuditVirtual.audit_virtual_full_source_statement.
Theorem audit_virtual_full_callbacks_correct :
  GraphAuditVirtual.audit_virtual_full_callbacks_statement.
Theorem audit_virtual_full_search_correct :
  GraphAuditVirtual.audit_virtual_full_search_statement.
Theorem audit_virtual_source_search_holds :
  GraphAuditVirtual.audit_virtual_source_search_statement.
```

### Future proofs in `GraphAuditVirtualAdapterAdequacy`

Card: AUD-GR-VIRTUAL

Source destination: `theories/Graph/GraphAuditVirtualAdapterAdequacy.v`.

```rocq
From Galois.Graph Require Import GraphAuditVirtualAdapter.

Theorem audit_virtual_source_search_adapted_holds :
  GraphAuditVirtualAdapter.audit_virtual_source_search_adapted_statement.
```

### Future proofs in `GraphAuditWtoAdequacy`

Card: AUD-GR-WTO

Source destination: `theories/Graph/GraphAuditWtoAdequacy.v`.

```rocq
From Galois.Graph Require Import GraphAuditWto.

Theorem audit_wto_counted_correct :
  GraphAuditWto.audit_wto_counted_statement.
Theorem audit_wto_nested_holds :
  GraphAuditWto.audit_wto_nested_statement.
Theorem audit_wto_source_holds :
  GraphAuditWto.audit_wto_source_statement.
Theorem audit_wto_source_event_correspondence_holds :
  GraphAuditWto.audit_wto_source_event_correspondence_statement.
Theorem audit_wto_source_adapted_holds :
  GraphAuditWto.audit_wto_source_adapted_statement.
Theorem audit_wto_source_contract_holds :
  GraphAuditWto.audit_wto_source_contract_statement.
```

<!-- AUD-API-GR-SQ-END -->

The fast reverse source models depend on three same-value refinements owned by AUD-GR-MODELS:
`GraphDfs.v` uses `rev_append xs []` for the `dfs` pre/post results and `rpo`;
`GraphScc.v` uses it for `tarjan_result` components and component IDs; and `GraphWto.v`
uses it for the `wto_unfold` reversal of `components (scc_within p region)`. The existing
public results and theorems retain their meanings. The audit adequacy statements above cover
fast and legacy reverse models separately.

### Fast reverse source refinements

Card: AUD-GR-MODELS

Source destinations: `theories/Graph/GraphDfs.v`, `theories/Graph/GraphScc.v` and
`theories/Graph/GraphWto.v`.
