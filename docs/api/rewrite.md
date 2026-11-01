# Galois.Rewrite

`Galois.Rewrite` is a standalone, directly verified equality-saturation library. Its theory
depends on Rocq Stdlib and `Galois.Collections` only. Clients supply signatures, interpretations,
rules, their proofs, fact validity and costs. Equality compares the entire `option` result: two
undefined evaluations are equal. No statement here implies that a partial operation is defined.
The ANA-6 compatibility surface and external explanation checker remain available in Analyses.

The public contract is organized by implementation card. Definitions written with an omitted
body specify an executable function; the accompanying equations and theorem statements fix its
meaning. A theorem is a proof obligation, not evidence of a proof. All core theorems are closed
under the global context. Dictionaries are parameterized records, without carrier `Type` fields.
At commit `3281819`, REW-1 through REW-7 and ANA-6 have landed. Their reports and independent
reviews record checked claims and finite examples under the stated premises.

## Files

| Card | Files |
|---|---|
| REW-1 | `RewriteSyntax.v`, `RewriteRules.v`, `RewriteEquality.v`, `dune` |
| REW-2 | `RewriteEgraph.v`, `RewriteIndex.v`, `RewriteRebuild.v` |
| REW-3 | `RewriteMatch.v` |
| REW-4 | `RewriteAnalysis.v` |
| REW-5 | `RewriteRun.v` |
| REW-6 | `RewriteExtract.v` |
| REW-7 | Analyses Order, SSA and word clients, specified in `analyses.md` |

## REW-1: syntax, rules and equality

Every application records its result sort and the list of its argument sorts. A signature checks
that full shape, permitting fixed or variadic operators. Free variables and pattern holes are
distinct. Holes are first-order: this contract has no binders or alpha-equivalence.

```coq
Inductive rw_term (K Sort V : Type) : Type :=
| RWVar (s : Sort) (v : V)
| RWApp (s : Sort) (op : K) (args : list (rw_term K Sort V)).
Inductive rw_pattern (K Sort V H : Type) : Type :=
| RWHole (s : Sort) (h : H)
| RWPVar (s : Sort) (v : V)
| RWPApp (s : Sort) (op : K) (args : list (rw_pattern K Sort V H)).

Definition rw_sort {K Sort V} (t : rw_term K Sort V) : Sort :=
  match t with RWVar s _ => s | RWApp s _ _ => s end.
Definition rwp_sort {K Sort V H} (p : rw_pattern K Sort V H) : Sort :=
  match p with RWHole s _ => s | RWPVar s _ => s | RWPApp s _ _ => s end.

Record rw_signature (K Sort V : Type) : Type := RwSignature {
  rw_var_sort : V -> option Sort;
  rw_operator_shape : K -> list Sort -> Sort -> bool
}.
Inductive rw_typed {K Sort V} (sig : rw_signature K Sort V) : rw_term K Sort V -> Prop :=
| rw_typed_var : forall s v, rw_var_sort sig v = Some s -> rw_typed sig (RWVar s v)
| rw_typed_app : forall s op args, Forall (rw_typed sig) args ->
    rw_operator_shape sig op (map rw_sort args) s = true ->
    rw_typed sig (RWApp s op args).
Inductive rwp_typed {K Sort V H} (sig : rw_signature K Sort V) (hs : H -> option Sort) :
    rw_pattern K Sort V H -> Prop :=
| rwp_typed_hole : forall s h, hs h = Some s -> rwp_typed sig hs (RWHole s h)
| rwp_typed_var : forall s v, rw_var_sort sig v = Some s -> rwp_typed sig hs (RWPVar s v)
| rwp_typed_app : forall s op args, Forall (rwp_typed sig hs) args ->
    rw_operator_shape sig op (map rwp_sort args) s = true ->
    rwp_typed sig hs (RWPApp s op args).

Definition rw_substitution (K Sort V H : Type) := H -> option (rw_term K Sort V).
Definition rw_sub_typed {K Sort V H} (sig : rw_signature K Sort V) (hs : H -> option Sort)
    (sub : rw_substitution K Sort V H) : Prop :=
  forall h s, hs h = Some s -> exists t, sub h = Some t /\ rw_sort t = s /\ rw_typed sig t.
Definition rw_instantiate {K Sort V H} (sub : rw_substitution K Sort V H)
    (p : rw_pattern K Sort V H) : option (rw_term K Sort V).
(* Holes use sub; variables are unchanged; an application succeeds exactly when all children do. *)

Record rw_semantics (K Sort V C : Type) : Type := RwSemantics {
  rw_var_value : V -> option C;
  rw_eval_op : K -> list C -> option C
}.
Definition rw_denote {K Sort V C} (sem : rw_semantics K Sort V C)
    (t : rw_term K Sort V) : option C.
(* Variable lookup; strict left-to-right traversal of children followed by rw_eval_op. *)
Definition rw_equiv {K Sort V C} (admissible : rw_semantics K Sort V C -> Prop)
    (t u : rw_term K Sort V) : Prop :=
  forall sem, admissible sem -> rw_denote sem t = rw_denote sem u.

Theorem rw_instantiate_typed {K Sort V H} (sig : rw_signature K Sort V)
    (hs : H -> option Sort) (sub : rw_substitution K Sort V H) (p : rw_pattern K Sort V H) :
  rwp_typed sig hs p -> rw_sub_typed sig hs sub ->
  exists t, rw_instantiate sub p = Some t /\ rw_typed sig t /\ rw_sort t = rwp_sort p.

Record rw_rule (K Sort V H : Type) : Type := RwRule {
  rw_holes : list H;
  rw_hole_sort : H -> option Sort;
  rw_lhs : rw_pattern K Sort V H;
  rw_rhs : rw_pattern K Sort V H;
  rw_condition : rw_substitution K Sort V H -> bool
}.
Definition rw_rule_wf {K Sort V H} (sig : rw_signature K Sort V)
    (r : rw_rule K Sort V H) : Prop :=
  NoDup (rw_holes r) /\
  (forall h, In h (rw_holes r) <-> exists s, rw_hole_sort r h = Some s) /\
  rwp_typed sig (rw_hole_sort r) (rw_lhs r) /\
  rwp_typed sig (rw_hole_sort r) (rw_rhs r) /\ rwp_sort (rw_lhs r) = rwp_sort (rw_rhs r).
Definition rw_rule_sound {K Sort V H C} (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (r : rw_rule K Sort V H) : Prop :=
  forall sub l r', rw_sub_typed sig (rw_hole_sort r) sub -> rw_condition r sub = true ->
    rw_instantiate sub (rw_lhs r) = Some l -> rw_instantiate sub (rw_rhs r) = Some r' ->
    rw_equiv admissible l r'.

Inductive rw_equal {K Sort V H C} (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H)) :
    rw_term K Sort V -> rw_term K Sort V -> Prop :=
| rw_eq_refl : forall t, rw_equal sig admissible rules t t
| rw_eq_sym : forall t u, rw_equal sig admissible rules t u -> rw_equal sig admissible rules u t
| rw_eq_trans : forall t u v, rw_equal sig admissible rules t u ->
    rw_equal sig admissible rules u v -> rw_equal sig admissible rules t v
| rw_eq_app : forall s op ts us, Forall2 (rw_equal sig admissible rules) ts us ->
    rw_equal sig admissible rules (RWApp s op ts) (RWApp s op us)
| rw_eq_rule : forall r sub l u, In r rules -> rw_sub_typed sig (rw_hole_sort r) sub ->
    rw_condition r sub = true -> rw_instantiate sub (rw_lhs r) = Some l ->
    rw_instantiate sub (rw_rhs r) = Some u -> rw_equal sig admissible rules l u.

Theorem rw_equal_sound {K Sort V H C} (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H)) :
  Forall (rw_rule_sound sig admissible) rules ->
  forall t u, rw_equal sig admissible rules t u -> rw_equiv admissible t u.
Theorem rw_equal_typed {K Sort V H C} (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H)) :
  Forall (rw_rule_wf sig) rules ->
  forall t u, rw_typed sig t -> rw_equal sig admissible rules t u ->
    rw_typed sig u /\ rw_sort t = rw_sort u.
```

## REW-2: represented terms and graph operations

Class identifiers and node identifiers are positive keys. Operations build prepared indexes once
per graph phase and update them as needed, rather than scanning the node list at each use. The
following abstract observers define the public representation relation. A child points to a class,
and a finite
derivation of `rw_represents` unfolds one graph node per term node; the graph itself may contain
cycles. `rw_roots` and `rw_nodes_in` enumerate exactly the allocated canonical roots and nodes.
The graph's sort is fixed at allocation and a merge of different sorts is rejected.

```coq
Definition rw_id := positive.
Inductive rw_node (K Sort V : Type) : Type :=
| RWNVar (s : Sort) (v : V)
| RWNApp (s : Sort) (op : K) (children : list rw_id).
Definition rw_node_sort {K Sort V} (n : rw_node K Sort V) : Sort :=
  match n with RWNVar s _ => s | RWNApp s _ _ => s end.

Record rw_graph (K Sort V : Type) : Type := RwGraph {
  rw_roots : list rw_id;
  rw_nodes_in : list rw_id;
  rw_class_roots : Map.t rw_id rw_id;
  rw_sorts : Map.t rw_id Sort;
  rw_nodes : Map.t rw_id (rw_id * rw_node K Sort V)
}.
Definition rw_find {K Sort V} (g : rw_graph K Sort V) (c : rw_id) : option rw_id :=
  Map.get positive_encoding c (rw_class_roots g).
Definition rw_class_sort {K Sort V} (g : rw_graph K Sort V) (c : rw_id) : option Sort :=
  Map.get positive_encoding c (rw_sorts g).
Definition rw_node_at {K Sort V} (g : rw_graph K Sort V) (n : rw_id) :
    option (rw_id * rw_node K Sort V) := Map.get positive_encoding n (rw_nodes g).
Inductive rw_represents {K Sort V} (g : rw_graph K Sort V) : rw_id -> rw_term K Sort V -> Prop :=
| rw_repr_var : forall c n owner root s v,
    rw_node_at g n = Some (owner, RWNVar s v) -> rw_find g owner = Some root ->
    rw_find g c = Some root -> rw_represents g c (RWVar s v)
| rw_repr_app : forall c n owner root s op ids ts,
    rw_node_at g n = Some (owner, RWNApp s op ids) -> rw_find g owner = Some root ->
    rw_find g c = Some root -> Forall2 (rw_represents g) ids ts ->
    rw_represents g c (RWApp s op ts).

Definition rw_graph_wf {K Sort V} (sig : rw_signature K Sort V)
    (g : rw_graph K Sort V) : Prop :=
  NoDup (rw_roots g) /\ NoDup (rw_nodes_in g) /\
  Map.wf positive_encoding (rw_class_roots g) /\ Map.wf positive_encoding (rw_sorts g) /\
  Map.wf positive_encoding (rw_nodes g) /\
  (forall c root, rw_find g c = Some root ->
    In root (rw_roots g) /\ rw_find g root = Some root /\
    exists s, rw_class_sort g c = Some s /\ rw_class_sort g root = Some s) /\
  (forall root, In root (rw_roots g) -> rw_find g root = Some root) /\
  (forall c, (exists s, rw_class_sort g c = Some s) <->
    (exists root, rw_find g c = Some root)) /\
  (forall n, In n (rw_nodes_in g) <-> exists c node, rw_node_at g n = Some (c, node)) /\
  (forall n c node, rw_node_at g n = Some (c, node) ->
    rw_class_sort g c = Some (rw_node_sort node)) /\
  (forall n c s v, rw_node_at g n = Some (c, RWNVar s v) ->
    rw_var_sort sig v = Some s) /\
  (forall n c s op ids, rw_node_at g n = Some (c, RWNApp s op ids) ->
    exists sorts, Forall2 (fun id ty => rw_class_sort g id = Some ty) ids sorts /\
      rw_operator_shape sig op sorts s = true) /\
  (forall c t, rw_represents g c t -> rw_typed sig t).

Definition rw_graph_sound {K Sort V H C} (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H))
    (g : rw_graph K Sort V) : Prop :=
  forall c t u, rw_represents g c t -> rw_represents g c u -> rw_equal sig admissible rules t u.
Definition rw_extends {K Sort V} (g g' : rw_graph K Sort V) : Prop :=
  forall c t, rw_represents g c t -> rw_represents g' c t.
Definition rw_clean {K Sort V} (g : rw_graph K Sort V) : Prop :=
  forall a b t, rw_represents g a t -> rw_represents g b t -> rw_find g a = rw_find g b.
Definition rw_productive {K Sort V} (g : rw_graph K Sort V) : Prop :=
  forall c root, rw_find g c = Some root -> exists t, rw_represents g c t.
Definition rw_joinable {K Sort V H C} (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H))
    (g : rw_graph K Sort V) (a b : rw_id) : Prop :=
  (exists t, rw_represents g a t) /\ (exists u, rw_represents g b u) /\
  forall t u, rw_represents g a t -> rw_represents g b u -> rw_equal sig admissible rules t u.

Record rw_index (K : Type) : Type := RwIndex {
  rw_index_ops : Map.t K (list rw_id);
  rw_index_parents : Map.t rw_id (list rw_id);
  rw_index_root_parents : Map.t rw_id (list rw_id)
}.
Definition rw_lookup_list {K} (E : encoding K) (k : K) (m : Map.t K (list rw_id)) : list rw_id :=
  match Map.get E k m with Some ids => ids | None => [] end.
Definition rw_index_agrees {K Sort V} (EK : encoding K) (g : rw_graph K Sort V)
    (ix : rw_index K) : Prop :=
  Map.wf EK (rw_index_ops ix) /\ Map.wf positive_encoding (rw_index_parents ix) /\
  Map.wf positive_encoding (rw_index_root_parents ix) /\
  (forall op, NoDup (rw_lookup_list EK op (rw_index_ops ix))) /\
  (forall child, NoDup (rw_lookup_list positive_encoding child (rw_index_parents ix))) /\
  (forall root, NoDup (rw_lookup_list positive_encoding root (rw_index_root_parents ix))) /\
  (forall op n, In n (rw_lookup_list EK op (rw_index_ops ix)) <->
    exists c s ids, rw_node_at g n = Some (c, RWNApp s op ids)) /\
  (forall child n, In n (rw_lookup_list positive_encoding child (rw_index_parents ix)) <->
    exists c s op ids, rw_node_at g n = Some (c, RWNApp s op ids) /\ In child ids) /\
  (forall root n, In n (rw_lookup_list positive_encoding root (rw_index_root_parents ix)) <->
    exists c s op ids child, rw_node_at g n = Some (c, RWNApp s op ids) /\ In child ids /\
      rw_find g child = Some root).
Definition rw_build_index {K Sort V} (EK : encoding K) (g : rw_graph K Sort V) : rw_index K.
Theorem rw_build_index_agrees {K Sort V} (EK : encoding K) (sig : rw_signature K Sort V)
    (g : rw_graph K Sort V) : rw_graph_wf sig g -> rw_index_agrees EK g (rw_build_index EK g).
Definition rw_parent_nodes {K Sort V} (g : rw_graph K Sort V) (ix : rw_index K) (c : rw_id) :
    list rw_id :=
  match rw_find g c with
  | Some root => rw_lookup_list positive_encoding root (rw_index_root_parents ix)
  | None => []
  end.
Theorem rw_parent_nodes_agree {K Sort V} (EK : encoding K) (g : rw_graph K Sort V)
    (ix : rw_index K) (c n : rw_id) :
  rw_index_agrees EK g ix ->
  (In n (rw_parent_nodes g ix c) <-> exists root owner s op ids child,
    rw_find g c = Some root /\ rw_find g child = Some root /\
    rw_node_at g n = Some (owner, RWNApp s op ids) /\ In child ids).

Definition rw_empty {K Sort V} : rw_graph K Sort V.
Definition rw_add {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (g : rw_graph K Sort V) (t : rw_term K Sort V) : rw_graph K Sort V * rw_id.
Definition rw_union {K Sort V} (ES : encoding Sort) (g : rw_graph K Sort V)
    (a b : rw_id) : option (rw_graph K Sort V).
Definition rw_index_after_union {K Sort V} (g g' : rw_graph K Sort V) (ix : rw_index K)
    (a b : rw_id) : rw_index K.
Definition rw_index_after_node_change {K Sort V} (EK : encoding K) (g g' : rw_graph K Sort V)
    (ix : rw_index K) (n : rw_id) : rw_index K.
Definition rw_rebuild {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (g : rw_graph K Sort V) : rw_graph K Sort V.
```

`rw_add` interns every node of the finite term, allocates missing classes, and returns its class.
`rw_union` returns `None` for an unallocated identifier or different class sorts; otherwise it
merges exactly the requested classes. `rw_rebuild` canonicalizes
children and repeatedly merges congruent parents until clean. It may add equalities but no new
term node; it terminates on every finite well-formed graph. Existing class identifiers remain
valid. Neither operation silently authorizes an arbitrary semantic equality: preservation requires
the explicit `rw_joinable` premise for union.

The root-parent index aggregates parents of every alias in each canonical class. After a union,
`rw_index_after_union` combines the two old root buckets into the new root bucket and removes the
obsolete bucket, without scanning nodes. After a node is canonicalized, `rw_index_after_node_change`
updates the raw, root-parent and operator buckets using only that node's old and new children.
Both updates deduplicate node identifiers; node changes account for repeated child IDs and distinct
child aliases resolving to the same root before removing or reinserting the parent.
Rebuild initializes the index once and maintains these invariants after every such change; this
includes parents that still contain a noncanonical child alias.
Rebuild keeps dirty congruence obligations in a local indexed pair worklist, not a public graph
field. A finite binary credit bounds the iteration; the prepared pair universe can be quadratic
within an operator bucket. This observation is not a complexity theorem or measurement.

```coq
Theorem rw_empty_wf {K Sort V} (sig : rw_signature K Sort V) : rw_graph_wf sig rw_empty.
Theorem rw_empty_sound {K Sort V H C} (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H)) :
  rw_graph_sound sig admissible rules rw_empty.
Theorem rw_empty_productive {K Sort V} : rw_productive (@rw_empty K Sort V).
Theorem rw_add_correct {K Sort V H C} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (sig : rw_signature K Sort V) (admissible : rw_semantics K Sort V C -> Prop)
    (rules : list (rw_rule K Sort V H)) (g : rw_graph K Sort V) (t : rw_term K Sort V) :
  rw_graph_wf sig g -> rw_graph_sound sig admissible rules g -> rw_productive g -> rw_typed sig t ->
  let '(g', c) := rw_add EK ES EV g t in
  rw_graph_wf sig g' /\ rw_graph_sound sig admissible rules g' /\ rw_productive g' /\
  rw_extends g g' /\
  rw_represents g' c t.
Theorem rw_union_correct {K Sort V H C} (ES : encoding Sort) (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H))
    (g g' : rw_graph K Sort V) (a b : rw_id) :
  rw_graph_wf sig g -> rw_graph_sound sig admissible rules g -> rw_productive g ->
  rw_joinable sig admissible rules g a b -> rw_union ES g a b = Some g' ->
  rw_graph_wf sig g' /\ rw_graph_sound sig admissible rules g' /\ rw_productive g' /\
  rw_extends g g' /\
  rw_find g' a = rw_find g' b.
Theorem rw_union_structure {K Sort V} (ES : encoding Sort) (sig : rw_signature K Sort V)
    (g g' : rw_graph K Sort V) (a b ra rb : rw_id) :
  rw_graph_wf sig g -> rw_find g a = Some ra -> rw_find g b = Some rb ->
  rw_union ES g a b = Some g' ->
  (forall n, rw_node_at g' n = rw_node_at g n) /\
  (forall x, (exists root, rw_find g x = Some root) <->
             (exists root, rw_find g' x = Some root)) /\
  (forall x y rx ry, rw_find g x = Some rx -> rw_find g y = Some ry ->
    (rw_find g' x = rw_find g' y <->
      rx = ry \/ (rx = ra /\ ry = rb) \/ (rx = rb /\ ry = ra))).
Theorem rw_index_after_union_agrees {K Sort V} (EK : encoding K) (ES : encoding Sort)
    (sig : rw_signature K Sort V) (g g' : rw_graph K Sort V) (ix : rw_index K) (a b : rw_id) :
  rw_graph_wf sig g -> rw_index_agrees EK g ix -> rw_union ES g a b = Some g' ->
  rw_index_agrees EK g' (rw_index_after_union g g' ix a b).
Theorem rw_index_after_node_change_agrees {K Sort V} (EK : encoding K)
    (sig : rw_signature K Sort V) (g g' : rw_graph K Sort V) (ix : rw_index K) (n : rw_id) :
  rw_graph_wf sig g -> rw_graph_wf sig g' -> rw_index_agrees EK g ix ->
  (forall c, rw_find g' c = rw_find g c) ->
  (forall m, m <> n -> rw_node_at g' m = rw_node_at g m) ->
  rw_index_agrees EK g' (rw_index_after_node_change EK g g' ix n).
Theorem rw_rebuild_correct {K Sort V H C} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H))
    (g : rw_graph K Sort V) :
  rw_graph_wf sig g -> rw_graph_sound sig admissible rules g -> rw_productive g ->
  rw_graph_wf sig (rw_rebuild EK ES EV g) /\
  rw_graph_sound sig admissible rules (rw_rebuild EK ES EV g) /\
  rw_productive (rw_rebuild EK ES EV g) /\
  rw_clean (rw_rebuild EK ES EV g) /\
  rw_extends g (rw_rebuild EK ES EV g).
```

## REW-3: indexed single-pattern matching

The matcher returns finite maps from holes to classes. Repeated occurrences must resolve to the
same canonical class. It is complete for one finite first-order pattern, including graph cycles;
it does not promise multipattern joins. The caller supplies a concrete term witness for each
hole before testing a term-dependent rule condition. The matcher builds and uses operator and
parent indexes; it does not rescan all nodes for each recursive match.

```coq
Definition rwp_holes {K Sort V H} (p : rw_pattern K Sort V H) : list H.
(* Traverse the pattern left to right, collecting each hole occurrence, including repetitions. *)
Definition rw_assignment (H : Type) := Map.t H rw_id.
Definition rw_covers {K Sort V H} (EH : encoding H) (g : rw_graph K Sort V)
    (p : rw_pattern K Sort V H) (a : rw_assignment H)
    (sub : rw_substitution K Sort V H) : Prop :=
  forall h, In h (rwp_holes p) ->
    exists c t, Map.get EH h a = Some c /\ sub h = Some t /\ rw_represents g c t.
Definition rw_match {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (g : rw_graph K Sort V) (root : rw_id) (p : rw_pattern K Sort V H) :
    list (rw_assignment H).

Theorem rw_match_sound {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) (g : rw_graph K Sort V)
    (root : rw_id) (p : rw_pattern K Sort V H) (a : rw_assignment H)
    (sub : rw_substitution K Sort V H) (t : rw_term K Sort V) :
  rw_graph_wf sig g -> In a (rw_match EK ES EV EH g root p) -> rw_covers EH g p a sub ->
  rw_instantiate sub p = Some t -> rw_represents g root t.
Theorem rw_match_complete {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (sig : rw_signature K Sort V) (g : rw_graph K Sort V)
    (root : rw_id) (p : rw_pattern K Sort V H) (sub : rw_substitution K Sort V H)
    (t : rw_term K Sort V) :
  rw_graph_wf sig g -> rw_clean g ->
  rwp_typed sig (fun h => option_map rw_sort (sub h)) p ->
  rw_instantiate sub p = Some t -> rw_represents g root t ->
  exists a, In a (rw_match EK ES EV EH g root p) /\ rw_covers EH g p a sub.
```

## REW-4: validated class analyses

An analysis fact describes all outcomes, including `None`, of all finite terms represented by
the class in every admissible environment. The client chooses this interpretation and proves
its transfer and combination laws. A nonzero guard that needs successful evaluation must require
the fact to exclude both zero and `None`. Facts with contextual validity may be used only with
that context in `admissible`; they must not be promoted to a larger environment set.

```coq
Record rw_analysis (K Sort V C F : Type) : Type := RwAnalysis {
  rw_fact_holds : F -> option C -> Prop;
  rw_fact_unknown : F;
  rw_fact_combine : F -> F -> F;
  rw_fact_transfer : rw_graph K Sort V -> (rw_id -> F) -> rw_id -> F
}.
Definition rw_fact_valid {K Sort V C F} (admissible : rw_semantics K Sort V C -> Prop)
    (an : rw_analysis K Sort V C F) (g : rw_graph K Sort V) (c : rw_id) (f : F) : Prop :=
  forall t sem, rw_represents g c t -> admissible sem -> rw_fact_holds an f (rw_denote sem t).
Definition rw_facts_valid {K Sort V C F} (admissible : rw_semantics K Sort V C -> Prop)
    (an : rw_analysis K Sort V C F) (g : rw_graph K Sort V) (facts : rw_id -> F) : Prop :=
  forall c, rw_fact_valid admissible an g c (facts c).
Record rw_analysis_laws {K Sort V C F} (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (an : rw_analysis K Sort V C F) : Prop := {
  rw_unknown_valid : forall result, rw_fact_holds an (rw_fact_unknown an) result;
  rw_combine_valid : forall f h result, rw_fact_holds an f result ->
    rw_fact_holds an h result -> rw_fact_holds an (rw_fact_combine an f h) result;
  rw_transfer_valid : forall g facts c, rw_graph_wf sig g -> rw_facts_valid admissible an g facts ->
    rw_fact_valid admissible an g c (rw_fact_transfer an g facts c)
}.
Definition rw_analyse_step {K Sort V C F} (an : rw_analysis K Sort V C F)
    (g : rw_graph K Sort V) (facts : rw_id -> F) (c : rw_id) : rw_id -> F.
(* At c, combine its old fact with the transfer result; elsewhere retain the old fact. *)
Theorem rw_analyse_step_valid {K Sort V C F} (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (an : rw_analysis K Sort V C F)
    (g : rw_graph K Sort V) (facts : rw_id -> F) (c : rw_id) :
  rw_analysis_laws sig admissible an -> rw_graph_wf sig g -> rw_facts_valid admissible an g facts ->
  rw_facts_valid admissible an g (rw_analyse_step an g facts c).
```

After any graph extension or union, a client must re-establish `rw_facts_valid` before reading
facts; unknown facts are always valid. Analysis-triggered merges go through the same `rw_union`
and `rw_joinable` proof obligation as ordinary rewrites. No convergence or least-fact result is
claimed by this single step.

## REW-5: bounded execution

An attempt names a rule, a root and a finite map of hole witnesses. A schedule is supplied by the
consumer and can use externally maintained, valid analysis facts when choosing attempts. The
runner checks typing, representation and the rule's Boolean condition before applying an attempt.
It adds the right-hand term, unions its class with the matched root, and rebuilds. Failed attempts
consume fuel and leave the graph unchanged. All fuel is binary `N`. A scheduler returning `None`
means it stopped; it does not establish a fixed point or fairness.

```coq
Record rw_attempt (K Sort V H : Type) : Type := RwAttempt {
  rw_attempt_rule : nat;
  rw_attempt_root : rw_id;
  rw_attempt_sub : Map.t H (rw_term K Sort V)
}.
Definition rw_attempt_substitution {K Sort V H} (EH : encoding H) (a : rw_attempt K Sort V H) :
    rw_substitution K Sort V H := fun h => Map.get EH h (rw_attempt_sub a).
Definition rw_check_sub {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) (r : rw_rule K Sort V H)
    (sub : rw_substitution K Sort V H) : bool.
(* For every listed hole: a binding exists, has the declared sort, and is recursively typed. *)
Theorem rw_check_sub_sound {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (sig : rw_signature K Sort V)
    (r : rw_rule K Sort V H) (sub : rw_substitution K Sort V H) :
  rw_rule_wf sig r -> rw_check_sub EK ES EV EH sig r sub = true ->
  rw_sub_typed sig (rw_hole_sort r) sub.
Theorem rw_check_sub_complete {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (sig : rw_signature K Sort V)
    (r : rw_rule K Sort V H) (sub : rw_substitution K Sort V H) :
  rw_rule_wf sig r -> rw_sub_typed sig (rw_hole_sort r) sub ->
  rw_check_sub EK ES EV EH sig r sub = true.
Definition rw_rep_test {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (g : rw_graph K Sort V) (c : rw_id) (t : rw_term K Sort V) : bool.
Theorem rw_rep_test_spec {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (sig : rw_signature K Sort V) (g : rw_graph K Sort V) (c : rw_id) (t : rw_term K Sort V) :
  rw_graph_wf sig g -> (rw_rep_test EK ES EV g c t = true <-> rw_represents g c t).
Definition rw_apply {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) (rules : list (rw_rule K Sort V H))
    (g : rw_graph K Sort V) (a : rw_attempt K Sort V H) : option (rw_graph K Sort V).
(* Reject an absent rule, invalid substitution, false condition, failed instantiation, absent lhs,
   or failed union. Otherwise add the rhs, union it with the root and rebuild. *)
Theorem rw_apply_correct {K Sort V H C} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H))
    (g g' : rw_graph K Sort V) (a : rw_attempt K Sort V H) :
  Forall (rw_rule_wf sig) rules -> Forall (rw_rule_sound sig admissible) rules ->
  rw_graph_wf sig g -> rw_graph_sound sig admissible rules g -> rw_productive g ->
  rw_apply EK ES EV EH sig rules g a = Some g' ->
  rw_graph_wf sig g' /\ rw_graph_sound sig admissible rules g' /\ rw_productive g' /\
  rw_clean g' /\ rw_extends g g'.

Inductive rw_stop : Type := RWStopped | RWFuelExhausted.
Record rw_run_result (K Sort V : Type) : Type := RwRunResult {
  rw_run_graph : rw_graph K Sort V;
  rw_run_stop : rw_stop
}.
Definition rw_strategy (K Sort V H : Type) := rw_graph K Sort V -> option (rw_attempt K Sort V H).
Definition rw_run {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) (rules : list (rw_rule K Sort V H))
    (strategy : rw_strategy K Sort V H) (fuel : N) (g : rw_graph K Sort V) :
    rw_run_result K Sort V.
(* Zero fuel returns RWFuelExhausted; otherwise ask the strategy. None returns RWStopped.
   Some attempt applies it if accepted and continues with fuel minus one. *)
Theorem rw_run_correct {K Sort V H C} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H))
    (strategy : rw_strategy K Sort V H) (fuel : N) (g : rw_graph K Sort V) :
  Forall (rw_rule_wf sig) rules -> Forall (rw_rule_sound sig admissible) rules ->
  rw_graph_wf sig g -> rw_graph_sound sig admissible rules g -> rw_productive g ->
  let g' := rw_run_graph (rw_run EK ES EV EH sig rules strategy fuel g) in
  rw_graph_wf sig g' /\ rw_graph_sound sig admissible rules g' /\ rw_productive g' /\
  rw_extends g g'.
```

## REW-6: exact finite tree extraction

The objective is the sum of nonnegative natural weights over the materialized tree, counting
repeated subtrees each time. Variable and operator weights are separate. The result is exact
among all finite represented terms, including in cyclic class graphs. It does not optimize shared
DAG size, register pressure or a cross-root objective. Materializing the output can take space
exponential in the compact graph; count output size separately. Costs are mathematical naturals.

```coq
Definition rw_tree_cost {K Sort V} (var_cost : V -> nat) (op_cost : K -> nat)
    (t : rw_term K Sort V) : nat.
(* Variables cost var_cost v; applications cost op_cost op plus the sum of child tree costs. *)
Definition rw_extract_tree {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (var_cost : V -> nat) (op_cost : K -> nat) (g : rw_graph K Sort V) (c : rw_id) :
    option (rw_term K Sort V).
Theorem rw_extract_tree_some {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (sig : rw_signature K Sort V) (var_cost : V -> nat) (op_cost : K -> nat)
    (g : rw_graph K Sort V) (c : rw_id) (t : rw_term K Sort V) :
  rw_graph_wf sig g -> rw_extract_tree EK ES EV var_cost op_cost g c = Some t ->
  rw_represents g c t /\
  forall u, rw_represents g c u -> rw_tree_cost var_cost op_cost t <= rw_tree_cost var_cost op_cost u.
Theorem rw_extract_tree_none {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (sig : rw_signature K Sort V) (var_cost : V -> nat) (op_cost : K -> nat)
    (g : rw_graph K Sort V) (c : rw_id) :
  rw_graph_wf sig g -> (rw_extract_tree EK ES EV var_cost op_cost g c = None <->
    (forall t, ~ rw_represents g c t)).
Theorem rw_extract_tree_equiv {K Sort V H C} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H))
    (var_cost : V -> nat) (op_cost : K -> nat) (g : rw_graph K Sort V)
    (c : rw_id) (input output : rw_term K Sort V) :
  Forall (rw_rule_sound sig admissible) rules -> rw_graph_wf sig g ->
  rw_graph_sound sig admissible rules g -> rw_represents g c input ->
  rw_extract_tree EK ES EV var_cost op_cost g c = Some output ->
  rw_equiv admissible input output /\
  rw_tree_cost var_cost op_cost output <= rw_tree_cost var_cost op_cost input.
```

The extractor considers finite-height witnesses and retains a cheapest candidate per class per
round. Removing a repeated class on a witness path cannot increase additive natural cost; thus an
optimal witness exists within the number of canonical classes whenever any witness exists.
Equal-cost choices break ties by smaller tree size and then structural order, so a zero-cost cycle
does not create a cyclic output. No productivity premise is needed for extraction: a class with
no finite witness returns `None`.
<!-- AUD-API-RW-BEGIN -->

# Rewrite source contracts

Definitions specify source work; future theorem types are proof obligations.

## Galois.Rewrite.RewriteAuditQueueReference

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditQueueReference.v`.

```rocq
(** * RewriteAuditQueueReference

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
Import List.ListNotations.

Record rw_pending_queue : Type := RwPendingQueue {
  rw_pending_sequence : list rw_pair;
  rw_pending_members : FinSet.t rw_pair
}.


Definition rw_pending_pair_encoding : encoding rw_pair :=
  pair_encoding positive_encoding positive_encoding.


Definition rw_pending_pair_key_bits (p : rw_pair) : nat :=
  Pos.size_nat (encode rw_pending_pair_encoding p).


(** This statement fixes the pending pair key bits exact contract. *)
Definition rw_pending_pair_key_bits_exact_contract : Prop := forall n m,
  rw_pending_pair_key_bits (n, m) = S (2 * Pos.size_nat n + 2 * Pos.size_nat m).


Definition rw_pending_valid (q : rw_pending_queue) : Prop :=
  NoDup (rw_pending_sequence q) /\
  FinSet.wf rw_pending_pair_encoding (rw_pending_members q) /\
  forall p, FinSet.mem rw_pending_pair_encoding p (rw_pending_members q) = true <->
    In p (rw_pending_sequence q).


Definition rw_pending_empty : rw_pending_queue := RwPendingQueue nil FinSet.empty.

Definition rw_pending_insert (p : rw_pair) (q : rw_pending_queue) : rw_pending_queue :=
  if FinSet.mem rw_pending_pair_encoding p (rw_pending_members q) then q
  else RwPendingQueue (p :: rw_pending_sequence q)
    (FinSet.add rw_pending_pair_encoding p (rw_pending_members q)).

Definition rw_pending_prepend (ps : list rw_pair) (q : rw_pending_queue) : rw_pending_queue :=
  fold_right rw_pending_insert q ps.

Definition rw_pending_pop (q : rw_pending_queue) : option (rw_pair * rw_pending_queue) :=
  match rw_pending_sequence q with
  | nil => None
  | p :: ps => Some (p, RwPendingQueue ps
      (FinSet.remove rw_pending_pair_encoding p (rw_pending_members q)))
  end.

Definition rw_pending_initial {K Sort V} (EK : encoding K)
    (EN : encoding (rw_node K Sort V)) (base : rw_graph K Sort V) (ix : rw_index K)
    (vars : Map.t positive (list rw_id)) : rw_pending_queue :=
  fold_right (fun n q => fold_right (fun m acc => rw_pending_insert (n,m) acc) q
    (rw_partners EK EN base ix vars n)) rw_pending_empty (rw_nodes_in base).

Definition rw_pending_initial_with_count {K Sort V} (EK : encoding K)
    (EN : encoding (rw_node K Sort V)) (base : rw_graph K Sort V) (ix : rw_index K)
    (vars : Map.t positive (list rw_id)) : rw_pending_queue * nat :=
  fold_right (fun n state =>
    fold_right (fun m acc =>
      let '(q, count) := acc in (rw_pending_insert (n, m) q, S count))
      state (rw_partners EK EN base ix vars n))
    (rw_pending_empty, 0) (rw_nodes_in base).


Record rw_queue_state (K Sort V : Type) : Type := RwQueueState {
  rw_queue_graph : rw_graph K Sort V;
  rw_queue_index : rw_index K;
  rw_queue_pending : rw_pending_queue
}.
Arguments RwQueueState {K Sort V}.
Arguments rw_queue_graph {K Sort V}.
Arguments rw_queue_index {K Sort V}.
Arguments rw_queue_pending {K Sort V}.


Definition rw_queue_project {K Sort V} (state : rw_queue_state K Sort V) :
    rw_rebuild_state K Sort V :=
  RwRebuildState (rw_queue_graph state) (rw_queue_index state)
    (rw_pending_sequence (rw_queue_pending state)).


Definition rw_queue_step {K Sort V} (EK : encoding K) (ES : encoding Sort)
    (EN : encoding (rw_node K Sort V)) (base : rw_graph K Sort V)
    (baseix : rw_index K) (vars : Map.t positive (list rw_id))
    (state : rw_queue_state K Sort V) : rw_queue_state K Sort V :=
  let g := rw_queue_graph state in
  let ix := rw_queue_index state in
  match rw_pending_pop (rw_queue_pending state) with
  | None => state
  | Some ((n, m), rest) =>
    let dropped := RwQueueState g ix rest in
    match rw_node_at g n, rw_node_at g m with
    | Some (a, node), Some (b, other) =>
      match rw_find g a, rw_find g b with
      | Some ra, Some rb =>
        if Pos.eq_dec (encode EN (rw_canonical_node g node))
             (encode EN (rw_canonical_node g other)) then
          if Pos.eq_dec ra rb then dropped
          else match rw_union ES g a b with
          | Some g' =>
            RwQueueState g' (rw_index_after_union g g' ix a b)
              (rw_pending_prepend
                (flat_map (rw_pairs_for EK EN base baseix vars)
                  (rw_parent_nodes g ix a ++ rw_parent_nodes g ix b)) rest)
          | None => dropped
          end
        else dropped
      | _, _ => dropped
      end
    | _, _ => dropped
    end
  end.


Definition rw_pending_rebuild {K Sort V} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (g : rw_graph K Sort V) : rw_graph K Sort V :=
  let EN := rw_node_encoding EK ES EV in
  let ix := rw_build_index EK g in
  let vars := rw_build_table positive_encoding g (RewriteRebuild.rw_variable_keys EN) in
  let '(pending, pair_count) := rw_pending_initial_with_count EK EN g ix vars in
  let initial := RwQueueState g ix pending in
  let fuel := length (rw_roots g) * S pair_count + length (rw_pending_sequence pending) in
  let done := fun state => rw_rebuild_done (rw_queue_project state) in
  let final := rw_repeat done (rw_queue_step EK ES EN g ix vars) (Pos.of_succ_nat fuel) initial in
  fst (rw_canonicalize_all EK (rw_nodes_in (rw_queue_graph final))
    (rw_queue_graph final) (rw_queue_index final)).


(** This statement fixes the pending initial with count correct contract. *)
Definition rw_pending_initial_with_count_correct_contract : Prop :=
  forall K Sort V (EK : encoding K) (EN : encoding (rw_node K Sort V))
    (base : rw_graph K Sort V) (ix : rw_index K) (vars : Map.t positive (list rw_id)),
    rw_pending_initial_with_count EK EN base ix vars =
      (rw_pending_initial EK EN base ix vars, length (rw_pair_universe EK EN base ix vars)).


(** This statement fixes the queue step agrees contract. *)
Definition rw_queue_step_agrees_contract : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EN : encoding (rw_node K Sort V))
    base baseix vars (state : rw_queue_state K Sort V),
    rw_pending_valid (rw_queue_pending state) ->
    rw_pending_valid (rw_queue_pending (rw_queue_step EK ES EN base baseix vars state)) /\
    rw_queue_project (rw_queue_step EK ES EN base baseix vars state) =
      rw_rebuild_step EK ES EN base baseix vars (rw_queue_project state).


(** This statement fixes the pending empty valid contract. *)
Definition rw_pending_empty_valid_contract : Prop :=
  rw_pending_valid rw_pending_empty /\ rw_pending_sequence rw_pending_empty = nil.


(** This statement fixes the pending insert order contract. *)
Definition rw_pending_insert_order_contract : Prop := forall q p, rw_pending_valid q ->
  rw_pending_sequence (rw_pending_insert p q) =
    if in_dec rw_pair_dec p (rw_pending_sequence q)
    then rw_pending_sequence q else p :: rw_pending_sequence q.


(** This statement fixes the pending membership contract. *)
Definition rw_pending_membership_contract : Prop := forall q p x,
  rw_pending_valid q ->
  rw_pending_valid (rw_pending_insert p q) /\
  (In x (rw_pending_sequence (rw_pending_insert p q)) <->
    x = p \/ In x (rw_pending_sequence q)).


(** This statement fixes the pending pop agrees contract. *)
Definition rw_pending_pop_agrees_contract : Prop := forall q, rw_pending_valid q ->
  match rw_pending_sequence q, rw_pending_pop q with
  | nil, None => True
  | p :: rest, Some (p', q') =>
    p' = p /\ rw_pending_valid q' /\ rw_pending_sequence q' = rest
  | _, _ => False
  end.


(** This statement fixes the pending prepend agrees contract. *)
Definition rw_pending_prepend_agrees_contract : Prop := forall ps q, rw_pending_valid q ->
  rw_pending_valid (rw_pending_prepend ps q) /\
  rw_pending_sequence (rw_pending_prepend ps q) =
    nodup rw_pair_dec (ps ++ rw_pending_sequence q).


(** This statement fixes the pair universe refines contract. *)
Definition rw_pair_universe_refines_contract : Prop :=
  forall K Sort V (EK : encoding K) (EN : encoding (rw_node K Sort V))
    (base : rw_graph K Sort V) (ix : rw_index K)
    (vars : Map.t positive (list rw_id)),
    let q := rw_pending_initial EK EN base ix vars in
    rw_pending_valid q /\
    rw_pending_sequence q = nodup rw_pair_dec (rw_pair_universe EK EN base ix vars).


(** This statement fixes the pending rebuild agrees contract. *)
Definition rw_pending_rebuild_agrees_contract : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (g : rw_graph K Sort V),
    rw_pending_rebuild EK ES EV g = rw_rebuild EK ES EV g.


Record rw_pending_charge := RwPendingCharge {
  rw_pending_probes : nat;
  rw_pending_updates : nat;
  rw_pending_key_steps : nat
}.

Definition rw_pending_charge_insert (p : rw_pair) (state : rw_pending_queue * rw_pending_charge) :
    rw_pending_queue * rw_pending_charge :=
  let '(q, charge) := state in
  let bits := rw_pending_pair_key_bits p in
  if FinSet.mem rw_pending_pair_encoding p (rw_pending_members q) then
    (q, RwPendingCharge (S (rw_pending_probes charge)) (rw_pending_updates charge)
      (bits + rw_pending_key_steps charge))
  else
    (RwPendingQueue (p :: rw_pending_sequence q)
      (FinSet.add rw_pending_pair_encoding p (rw_pending_members q)),
      RwPendingCharge (S (rw_pending_probes charge)) (S (rw_pending_updates charge))
        (2 * bits + rw_pending_key_steps charge)).

Definition rw_pending_initial_counted {K Sort V} (EK : encoding K)
    (EN : encoding (rw_node K Sort V)) (base : rw_graph K Sort V) (ix : rw_index K)
    (vars : Map.t positive (list rw_id)) : rw_pending_queue * rw_pending_charge :=
  fold_right (fun n st => fold_right (fun m acc => rw_pending_charge_insert (n,m) acc) st
    (rw_partners EK EN base ix vars n)) (rw_pending_empty, RwPendingCharge 0 0 0)
    (rw_nodes_in base).

Definition rw_pending_key_budget (pairs : list rw_pair) : nat :=
  fold_right (fun p n => 2 * rw_pending_pair_key_bits p + n) 0 pairs.

(** This statement fixes the pending initial counted correct contract. *)
Definition rw_pending_initial_counted_correct_contract : Prop :=
  forall K Sort V (EK : encoding K) (EN : encoding (rw_node K Sort V))
    (base : rw_graph K Sort V) (ix : rw_index K) (vars : Map.t positive (list rw_id)),
    let '(pending, charge) := rw_pending_initial_counted EK EN base ix vars in
    pending = rw_pending_initial EK EN base ix vars /\
    rw_pending_probes charge = length (rw_pair_universe EK EN base ix vars) /\
    rw_pending_updates charge <= length (rw_pair_universe EK EN base ix vars) /\
    rw_pending_key_steps charge <= rw_pending_key_budget (rw_pair_universe EK EN base ix vars).


Inductive rw_queue_insert_call : Type :=
  | RWQueuePairCode : rw_pair -> positive -> rw_queue_insert_call
  | RWQueueGet : rw_pair -> FinSet.t rw_pair -> option unit -> rw_queue_insert_call
  | RWQueueSet : rw_pair -> FinSet.t rw_pair -> FinSet.t rw_pair -> rw_queue_insert_call
  | RWQueueRemove : rw_pair -> FinSet.t rw_pair -> FinSet.t rw_pair -> rw_queue_insert_call.


Definition rw_queue_insert_event_cost (event : audit_event rw_queue_insert_call) : nat :=
  match event with
  | AuditCall (RWQueuePairCode _ code) => audit_encoding_weight (Pos.size_nat code)
  | AuditCall (RWQueueGet p _ _) =>
    audit_get_weight (encode rw_pending_pair_encoding p)
  | AuditCall (RWQueueSet p _ _) =>
    audit_set_weight (encode rw_pending_pair_encoding p)
  | AuditCall (RWQueueRemove p _ _) =>
    audit_remove_weight (encode rw_pending_pair_encoding p)
  | _ => 1
  end.


Definition rw_queue_insert_model_cost (trace : audit_trace rw_queue_insert_call) : nat :=
  fold_right (fun event total => rw_queue_insert_event_cost event + total) 0 trace.


Definition rw_queue_insert_atomic (p : rw_pair) (q : rw_pending_queue) :
    rw_pending_queue * audit_trace rw_queue_insert_call :=
  let code := encode rw_pending_pair_encoding p in
  let members := rw_pending_members q in
  let found := Map.code_get code members in
  match found with
  | Some _ =>
    (q, [AuditCase 0 []; AuditCall (RWQueuePairCode p code);
      AuditCall (RWQueueGet p members found); AuditCase 1 []])
  | None =>
    let code' := encode rw_pending_pair_encoding p in
    let updated := Trie.set code' (p, tt) members in
    (RwPendingQueue (p :: rw_pending_sequence q) updated,
      [AuditCase 0 []; AuditCall (RWQueuePairCode p code);
       AuditCall (RWQueueGet p members found); AuditCase 2 [];
       AuditCall (RWQueuePairCode p code'); AuditCall (RWQueueSet p members updated);
       AuditConstruct 3 []; AuditConstruct 4 []])
  end.


Record rw_queue_encoder_adapter (A : Type) : Type := RwQueueEncoderAdapter {
  rw_queue_encoder_run : A -> positive * nat
}.
Arguments RwQueueEncoderAdapter {A}.
Arguments rw_queue_encoder_run {A}.


Record rw_queue_encoder_adapter_laws {A} (E : encoding A)
    (external_execution : A -> positive -> nat -> Prop)
    (adapter : rw_queue_encoder_adapter A) : Prop := {
  rw_queue_encoder_agrees : forall input,
    fst (rw_queue_encoder_run adapter input) = encode E input;
  rw_queue_encoder_adequate : forall input,
    let '(result, work) := rw_queue_encoder_run adapter input in
    external_execution input result work
}.


Definition rw_queue_pop_atomic (q : rw_pending_queue) :
    option (rw_pair * rw_pending_queue) * audit_trace rw_queue_insert_call :=
  match rw_pending_sequence q with
  | nil => (None, [AuditCase 20 []; AuditConstruct 22 []])
  | p :: rest =>
    let code := encode rw_pending_pair_encoding p in
    let updated := Trie.remove code (rw_pending_members q) in
    (Some (p, RwPendingQueue rest updated),
      [AuditCase 21 []; AuditCall (RWQueuePairCode p code);
       AuditCall (RWQueueRemove p (rw_pending_members q) updated);
       AuditConstruct 23 []; AuditConstruct 24 []; AuditConstruct 25 []])
  end.


Fixpoint rw_queue_prepend_atomic (pairs : list rw_pair) (q : rw_pending_queue) :
    rw_pending_queue * audit_trace rw_queue_insert_call :=
  match pairs with
  | nil => (q, [AuditCase 10 []])
  | p :: rest =>
    let '(after_rest, rest_trace) := rw_queue_prepend_atomic rest q in
    let '(out, insert_trace) := rw_queue_insert_atomic p after_rest in
    (out, AuditCase 11 [] :: rest_trace ++ insert_trace)
  end.


Fixpoint rw_queue_append_atomic {A} (first second : list A) : list A * audit_trace unit :=
  match first with
  | nil => (second, [AuditCase 195 []])
  | item :: rest =>
    let '(tail, trace) := rw_queue_append_atomic rest second in
    (item :: tail, [AuditCase 196 []] ++ trace ++ [AuditConstruct 197 []])
  end.


Fixpoint rw_fuel_length {A} (xs : list A) : nat * audit_trace unit :=
  match xs with
  | nil => (0, [AuditCase 410 []; AuditConstruct 411 []])
  | _ :: rest => let '(n, trace) := rw_fuel_length rest in
      (S n, [AuditCase 412 []; AuditArithmetic 440 []] ++ trace ++ [AuditConstruct 413 []])
  end.


Fixpoint rw_fuel_add (n m : nat) : nat * audit_trace unit :=
  match n with
  | 0 => (m, [AuditCase 414 []])
  | S n' => let '(out, trace) := rw_fuel_add n' m in
      (S out, [AuditCase 415 []; AuditArithmetic 441 []] ++ trace ++ [AuditConstruct 416 []])
  end.


Fixpoint rw_fuel_mul (n m : nat) : nat * audit_trace unit :=
  match n with
  | 0 => (0, [AuditCase 417 []; AuditConstruct 418 []])
  | S n' =>
    let '(tail, tail_trace) := rw_fuel_mul n' m in
    let '(out, add_trace) := rw_fuel_add m tail in
    (out, [AuditCase 419 []; AuditArithmetic 442 []] ++ tail_trace ++
      [AuditArithmetic 443 []] ++ add_trace)
  end.


Fixpoint rw_fuel_pos_succ (p : positive) : positive * audit_trace unit :=
  match p with
  | xH => (xO xH, [AuditCase 420 []; AuditConstruct 421 []])
  | xO rest => (xI rest, [AuditCase 422 []; AuditConstruct 423 []])
  | xI rest => let '(out, trace) := rw_fuel_pos_succ rest in
      (xO out, [AuditCase 424 []; AuditArithmetic 444 []] ++ trace ++ [AuditConstruct 425 []])
  end.


Fixpoint rw_fuel_to_positive (n : nat) : positive * audit_trace unit :=
  match n with
  | 0 => (xH, [AuditCase 426 []; AuditConstruct 427 []])
  | S rest => let '(p, tail_trace) := rw_fuel_to_positive rest in
      let '(out, succ_trace) := rw_fuel_pos_succ p in
      (out, [AuditCase 428 []; AuditArithmetic 445 []] ++ tail_trace ++
        [AuditArithmetic 446 []] ++ succ_trace)
  end.


Definition rw_rebuild_fuel_atomic {K Sort V} (g : rw_graph K Sort V) (pair_count : nat)
    (queue : rw_pending_queue) : positive * audit_trace unit :=
  let roots := rw_roots g in
  let '(root_count, root_trace) := rw_fuel_length roots in
  let width := S pair_count in
  let '(product, mul_trace) := rw_fuel_mul root_count width in
  let pending := rw_pending_sequence queue in
  let '(pending_count, pending_trace) := rw_fuel_length pending in
  let '(total, add_trace) := rw_fuel_add product pending_count in
  let '(fuel, conversion_trace) := rw_fuel_to_positive total in
  (fuel, [AuditCase 430 []; AuditArithmetic 447 []] ++ root_trace ++
    [AuditConstruct 429 []; AuditArithmetic 448 []] ++ mul_trace ++
    [AuditCase 431 []; AuditArithmetic 449 []] ++ pending_trace ++
    [AuditArithmetic 450 []] ++ add_trace ++ [AuditArithmetic 451 []] ++ conversion_trace).


Definition rw_rebuild_fuel_work (roots pair_count pending : nat) : nat :=
  let product := roots * S pair_count in
  let total := product + pending in
  30 + 3 * roots + 3 * pending + roots * (4 + 3 * S pair_count) +
    3 * product + (S total) * (5 + 3 * Pos.size_nat (Pos.of_succ_nat total)).


Definition rw_node_encode_atomic {K Sort V KE SE VE}
    (op : K -> positive * list KE) (sort : Sort -> positive * list SE)
    (value : V -> positive * list VE) (node : rw_node K Sort V) :=
  audit_sum_encode (audit_pair_encode sort value)
    (audit_pair_encode sort (audit_pair_encode op
      (audit_list_encode audit_positive_encode))) (rw_node_key node).


Definition rw_node_encode_trace_cost {K Sort V KE SE VE}
    (op_work : list KE -> nat) (sort_work : list SE -> nat) (value_work : list VE -> nat)
    (trace : list (audit_sum_event (Sort * V) (Sort * (K * list rw_id))
      (audit_pair_event Sort V SE VE)
      (audit_pair_event Sort (K * list rw_id) SE
        (audit_pair_event K (list rw_id) KE
          (audit_list_event rw_id (audit_basic_encoding_event positive)))))) : nat :=
  audit_sum_events_work (audit_pair_events_work sort_work value_work)
    (audit_pair_events_work sort_work
      (audit_pair_events_work op_work
        (audit_list_events_work (@length (audit_basic_encoding_event positive))))) trace.


Definition rw_external_encoding_events {A} (adapter : rw_queue_encoder_adapter A) (x : A) :
    positive * list nat :=
  let '(code, work) := rw_queue_encoder_run adapter x in (code, [work]).


Definition rw_external_events_work (events : list nat) : nat := fold_right Nat.add 0 events.


Definition rw_queue_insert_trie_work (event : audit_event rw_queue_insert_call) : nat :=
  match event with
  | AuditCall (RWQueueGet p before _) =>
      audit_trie_get_source_work (encode rw_pending_pair_encoding p) before
  | AuditCall (RWQueueSet p before _) =>
      audit_trie_update_source_work (encode rw_pending_pair_encoding p) (Some (p, tt)) before
  | AuditCall (RWQueueRemove p before _) =>
      audit_trie_update_source_work (encode rw_pending_pair_encoding p) None before
  | _ => 0
  end.


Definition rw_queue_insert_trie_trace_work (trace : audit_trace rw_queue_insert_call) : nat :=
  fold_right (fun event total => rw_queue_insert_trie_work event + total) 0 trace.


Definition rw_queue_insert_expanded_work (trace : audit_trace rw_queue_insert_call) : nat :=
  rw_queue_insert_model_cost trace + rw_queue_insert_trie_trace_work trace.


Definition rw_queue_prepend_expanded_budget (pairs : list rw_pair) : nat :=
  S (length pairs) + fold_right (fun p total => 8 + 26 * rw_pending_pair_key_bits p + total) 0
    pairs.
```

## Galois.Rewrite.RewriteAuditQueuePositive

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditQueuePositive.v`.

```rocq
(** * RewriteAuditQueuePositive

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
Import List.ListNotations.

Inductive rw_rq_decision_frame : Type :=
  | RQDecBuildCase : positive -> rw_rq_decision_frame
  | RQDecBuildRecursive : positive -> rw_rq_decision_frame
  | RQDecClosure : positive -> rw_rq_decision_frame
  | RQDecApply : positive -> positive -> rw_rq_decision_frame
  | RQDecInspect : positive -> rw_rq_decision_frame
  | RQDecReturn : bool -> rw_rq_decision_frame.


Fixpoint rw_rq_decision_build (first : positive) :
    (positive -> bool * list rw_rq_decision_frame) * list rw_rq_decision_frame :=
  match first with
  | xH =>
    ((fun second =>
      let answer := match second with xH => true | _ => false end in
      (answer, [RQDecInspect second; RQDecReturn answer])),
      [RQDecBuildCase first; RQDecClosure first])
  | xI rest =>
    let '(child, build_trace) := rw_rq_decision_build rest in
    ((fun second =>
      match second with
      | xI tail =>
        let '(answer, call_trace) := child tail in
        (answer, [RQDecInspect second; RQDecApply rest tail] ++ call_trace ++
          [RQDecReturn answer])
      | _ => (false, [RQDecInspect second; RQDecReturn false])
      end),
      [RQDecBuildCase first; RQDecBuildRecursive rest] ++ build_trace ++
        [RQDecClosure first])
  | xO rest =>
    let '(child, build_trace) := rw_rq_decision_build rest in
    ((fun second =>
      match second with
      | xO tail =>
        let '(answer, call_trace) := child tail in
        (answer, [RQDecInspect second; RQDecApply rest tail] ++ call_trace ++
          [RQDecReturn answer])
      | _ => (false, [RQDecInspect second; RQDecReturn false])
      end),
      [RQDecBuildCase first; RQDecBuildRecursive rest] ++ build_trace ++
        [RQDecClosure first])
  end.


Definition rw_rq_decision_atomic (first second : positive) :
    bool * list rw_rq_decision_frame :=
  let '(compare, build_trace) := rw_rq_decision_build first in
  let '(answer, call_trace) := compare second in
  (answer, build_trace ++ RQDecApply first second :: call_trace).

(** The computational sumbool tag agrees with the actual transparent Stdlib decider. *)

(** This statement fixes the rq decision source erases statement contract. *)
Definition rw_rq_decision_source_erases_statement : Prop :=
  forall first second,
  fst (rw_rq_decision_atomic first second) =
    if Pos.eq_dec first second then true else false.

(** Construction traverses all first-operand bits even on an immediate second mismatch. *)

(** This statement fixes the rq decision build count statement contract. *)
Definition rw_rq_decision_build_count_statement : Prop :=
  forall first,
  length (snd (rw_rq_decision_build first)) = 3 * Pos.size_nat first - 1.

(** Both comparator construction and actual application fit a two-operand bit ceiling. *)

(** This statement fixes the rq decision source bound statement contract. *)
Definition rw_rq_decision_source_bound_statement : Prop :=
  forall first second,
  64 * length (snd (rw_rq_decision_atomic first second)) <=
    1024 + 512 * (Pos.size_nat first + Pos.size_nat second).

(** A mismatched low bit still pays for all three first-operand closure frames. *)
```

## Galois.Rewrite.RewriteAuditQueueKernel

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditQueueKernel.v`.

```rocq
(** * RewriteAuditQueueKernel

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditQueuePositive RewriteAuditQueueReference.
Import List.ListNotations.

Definition rw_rq_node_event (K Sort V : Type) :=
  audit_sum_event (Sort * V) (Sort * (K * list rw_id))
    (audit_pair_event Sort V nat nat)
    (audit_pair_event Sort (K * list rw_id) nat
      (audit_pair_event K (list rw_id) nat
        (audit_list_event rw_id (audit_basic_encoding_event positive)))).


Inductive rw_rq_receipt (K Sort V : Type) : Type :=
  | RQSourceBlock : nat -> rw_rq_receipt K Sort V
  | RQSourceGet : forall A, positive -> Trie.t A -> option A ->
      audit_trace (audit_trie_call A) -> rw_rq_receipt K Sort V
  | RQSourceUpdate : forall A, positive -> option A -> Trie.t A -> Trie.t A ->
      audit_trace (audit_trie_call A) -> rw_rq_receipt K Sort V
  | RQSourceOperator : K -> positive -> nat -> rw_rq_receipt K Sort V
  | RQSourceSort : Sort -> positive -> nat -> rw_rq_receipt K Sort V
  | RQSourceVariable : V -> positive -> nat -> rw_rq_receipt K Sort V
  | RQSourcePair : rw_pair -> positive ->
      list (audit_pair_event positive positive (audit_basic_encoding_event positive)
        (audit_basic_encoding_event positive)) -> rw_rq_receipt K Sort V
  | RQSourceNode : rw_node K Sort V -> positive -> list (rw_rq_node_event K Sort V) ->
      rw_rq_receipt K Sort V
  | RQSourceDecision : positive -> positive -> bool -> list rw_rq_decision_frame ->
      rw_rq_receipt K Sort V
  | RQSourceCollapse : rw_id -> rw_id -> Map.t rw_id rw_id -> Map.t rw_id rw_id ->
      list (audit_map_transform_event rw_id rw_id rw_id rw_rq_decision_frame) ->
      rw_rq_receipt K Sort V
  | RQSourceFuel : rw_graph K Sort V -> nat -> rw_pending_queue -> positive ->
      audit_trace unit -> rw_rq_receipt K Sort V.
Arguments RQSourceBlock {K Sort V}.
Arguments RQSourceGet {K Sort V A}.
Arguments RQSourceUpdate {K Sort V A}.
Arguments RQSourceOperator {K Sort V}.
Arguments RQSourceSort {K Sort V}.
Arguments RQSourceVariable {K Sort V}.
Arguments RQSourcePair {K Sort V}.
Arguments RQSourceNode {K Sort V}.
Arguments RQSourceDecision {K Sort V}.
Arguments RQSourceCollapse {K Sort V}.
Arguments RQSourceFuel {K Sort V}.


Definition rw_rq_receipt_work {K Sort V} (receipt : rw_rq_receipt K Sort V) : nat :=
  match receipt with
  | RQSourceBlock _ => 64
  | RQSourceGet _ _ _ trace => 64 + audit_trie_get_trace_source_work trace
  | RQSourceUpdate _ _ _ _ trace => 64 + audit_trie_update_trace_source_work trace
  | RQSourceOperator _ _ body => 64 + body
  | RQSourceSort _ _ body => 64 + body
  | RQSourceVariable _ _ body => 64 + body
  | RQSourcePair _ _ trace => 64 +
      audit_pair_events_work audit_basic_encoding_work audit_basic_encoding_work trace
  | RQSourceNode _ _ trace => 64 +
      rw_node_encode_trace_cost rw_external_events_work rw_external_events_work
        rw_external_events_work trace
  | RQSourceDecision _ _ _ trace => 64 + 64 * length trace
  | RQSourceCollapse _ _ _ _ trace => 64 +
      audit_map_transform_source_work (fun bits => 64 * length bits) trace
  | RQSourceFuel _ _ _ _ trace => 64 + 64 * audit_work trace
  end.


Definition rw_rq_receipts_work {K Sort V} (receipts : list (rw_rq_receipt K Sort V)) : nat :=
  fold_right (fun receipt total => rw_rq_receipt_work receipt + total) 0 receipts.


Record rw_rq_source (K Sort V A : Type) := RwRqSource {
  rw_rq_value : A;
  rw_rq_receipts : list (rw_rq_receipt K Sort V)
}.
Arguments RwRqSource {K Sort V A}.
Arguments rw_rq_value {K Sort V A}.
Arguments rw_rq_receipts {K Sort V A}.


Definition rw_rq_return {K Sort V A} (site : nat) (value : A) : rw_rq_source K Sort V A :=
  RwRqSource value [RQSourceBlock site].


Definition rw_rq_bind {K Sort V A B} (site : nat) (first : rw_rq_source K Sort V A)
    (next : A -> rw_rq_source K Sort V B) : rw_rq_source K Sort V B :=
  let later := next (rw_rq_value first) in
  RwRqSource (rw_rq_value later)
    (rw_rq_receipts first ++ RQSourceBlock site :: rw_rq_receipts later).


Definition rw_rq_code_get {K Sort V A} (code : positive) (before : Trie.t A) :
    rw_rq_source K Sort V (option A) :=
  let '(out, trace) := audit_trie_get code before in
  RwRqSource out [RQSourceGet code before out trace].


Definition rw_rq_map_code_get {K Sort V A B} (code : positive) (before : Map.t A B) :
    rw_rq_source K Sort V (option B) :=
  rw_rq_bind 1000 (rw_rq_code_get code before)
    (fun stored => rw_rq_return 1001 (option_map snd stored)).


Definition rw_rq_code_set {K Sort V A} (code : positive) (value : A) (before : Trie.t A) :
    rw_rq_source K Sort V (Trie.t A) :=
  let '(out, trace) := audit_trie_set code value before in
  RwRqSource out [RQSourceUpdate code (Some value) before out trace].


Definition rw_rq_code_remove {K Sort V A} (code : positive) (before : Trie.t A) :
    rw_rq_source K Sort V (Trie.t A) :=
  let '(out, trace) := audit_trie_remove code before in
  RwRqSource out [RQSourceUpdate code None before out trace].


Definition rw_rq_operator_encode {K Sort V} (adapter : rw_queue_encoder_adapter K) (x : K) :
    rw_rq_source K Sort V positive :=
  let '(code, body) := rw_queue_encoder_run adapter x in
  RwRqSource code [RQSourceOperator x code body].


Definition rw_rq_sort_encode {K Sort V} (adapter : rw_queue_encoder_adapter Sort) (x : Sort) :
    rw_rq_source K Sort V positive :=
  let '(code, body) := rw_queue_encoder_run adapter x in
  RwRqSource code [RQSourceSort x code body].


Definition rw_rq_variable_encode {K Sort V} (adapter : rw_queue_encoder_adapter V) (x : V) :
    rw_rq_source K Sort V positive :=
  let '(code, body) := rw_queue_encoder_run adapter x in
  RwRqSource code [RQSourceVariable x code body].


Definition rw_rq_pair_encode {K Sort V} (pair_value : rw_pair) :
    rw_rq_source K Sort V positive :=
  let '(code, trace) := audit_pair_encode audit_positive_encode audit_positive_encode pair_value in
  RwRqSource code [RQSourcePair pair_value code trace].


Definition rw_rq_node_encode {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (node : rw_node K Sort V) : rw_rq_source K Sort V positive :=
  let '(code, trace) := rw_node_encode_atomic (rw_external_encoding_events op)
    (rw_external_encoding_events sort) (rw_external_encoding_events value) node in
  RwRqSource code [RQSourceNode node code trace].


Definition rw_rq_decision {K Sort V} (a b : positive) : rw_rq_source K Sort V bool :=
  let '(answer, trace) := rw_rq_decision_atomic a b in
  RwRqSource answer [RQSourceDecision a b answer trace].


Definition rw_rq_collapse_source_child (from into root : rw_id) :
    rw_id * list rw_rq_decision_frame :=
  let '(same, trace) := rw_rq_decision_atomic root from in
  ((if same then into else root), trace).


Definition rw_rq_collapse_source {K Sort V} (from into : rw_id)
    (before : Map.t rw_id rw_id) : rw_rq_source K Sort V (Map.t rw_id rw_id) :=
  let '(out, trace) := audit_map_transform (rw_rq_collapse_source_child from into) before in
  RwRqSource out [RQSourceCollapse from into before out trace].


Fixpoint rw_rq_source_append {K Sort V A} (xs ys : list A) : rw_rq_source K Sort V (list A) :=
  match xs with
  | nil => rw_rq_return 1002 ys
  | x :: rest => rw_rq_bind 1003 (rw_rq_source_append rest ys)
      (fun tail => rw_rq_return 1004 (x :: tail))
  end.


Fixpoint rw_rq_source_fold_right {K Sort V A B}
    (f : A -> B -> rw_rq_source K Sort V B) (xs : list A) (initial : B) : rw_rq_source K Sort V B :=
  match xs with
  | nil => rw_rq_return 1005 initial
  | x :: rest => rw_rq_bind 1006 (rw_rq_source_fold_right f rest initial) (f x)
  end.


Fixpoint rw_rq_source_map {K Sort V A B} (f : A -> rw_rq_source K Sort V B) (xs : list A) :
    rw_rq_source K Sort V (list B) :=
  match xs with
  | nil => rw_rq_return 1007 nil
  | x :: rest => rw_rq_bind 1008 (f x) (fun head =>
      rw_rq_bind 1009 (rw_rq_source_map f rest) (fun tail => rw_rq_return 1010 (head :: tail)))
  end.


Fixpoint rw_rq_source_flat_map {K Sort V A B} (f : A -> rw_rq_source K Sort V (list B))
    (xs : list A) : rw_rq_source K Sort V (list B) :=
  match xs with
  | nil => rw_rq_return 1011 nil
  | x :: rest => rw_rq_bind 1012 (f x) (fun head =>
      rw_rq_bind 1013 (rw_rq_source_flat_map f rest) (fun tail => rw_rq_source_append head tail))
  end.

(** Receipt cost is computed without calling a client encoder or recovering an old map. *)

(** This statement fixes the rq get receipt statement contract. *)
Definition rw_rq_get_receipt_statement : Prop :=
  forall K Sort V A code (before : Trie.t A),
  let run := @rw_rq_code_get K Sort V A code before in
  rw_rq_value run = Trie.get code before /\
  exists trace, rw_rq_receipts run = [RQSourceGet code before (rw_rq_value run) trace] /\
    audit_trie_get code before = (rw_rq_value run, trace).


Fixpoint rw_rq_pair_external {A B EA EB} (first : list EA -> nat) (second : list EB -> nat)
    (trace : list (audit_pair_event A B EA EB)) : nat :=
  match trace with
  | nil => 0
  | AuditPairFirst _ _ child :: rest => first child + rw_rq_pair_external first second rest
  | AuditPairSecond _ _ child :: rest => second child + rw_rq_pair_external first second rest
  | AuditPairFrame _ :: rest => rw_rq_pair_external first second rest
  end.


Definition rw_rq_node_external {K Sort V} (trace : list (rw_rq_node_event K Sort V)) : nat :=
  fold_right (fun event total =>
    match event with
    | AuditSumLeft _ _ child =>
      rw_rq_pair_external rw_external_events_work rw_external_events_work child + total
    | AuditSumRight _ _ child =>
      rw_rq_pair_external rw_external_events_work
        (rw_rq_pair_external rw_external_events_work (fun _ => 0)) child + total
    end) 0 trace.


Definition rw_rq_receipt_budget {K Sort V} (receipt : rw_rq_receipt K Sort V) : nat :=
  match receipt with
  | RQSourceBlock _ => 128
  | RQSourceGet code _ _ _ => 256 + 512 * Pos.size_nat code
  | RQSourceUpdate code _ _ _ _ => 256 + 512 * Pos.size_nat code
  | RQSourceOperator _ _ body => 256 + body
  | RQSourceSort _ _ body => 256 + body
  | RQSourceVariable _ _ body => 256 + body
  | RQSourcePair pair_value _ _ =>
    1024 + 1024 * (Pos.size_nat (fst pair_value) + Pos.size_nat (snd pair_value))
  | RQSourceNode _ code trace =>
    2048 + 2048 * Pos.size_nat code + rw_rq_node_external trace
  | RQSourceDecision a b _ _ => 1024 + 512 * (Pos.size_nat a + Pos.size_nat b)
  | RQSourceCollapse from _ before _ trace =>
    1024 + 1024 * audit_trie_nodes before +
      fold_right (fun event total =>
        match event with
        | AuditMapTransformCall _ input _ _ =>
          1024 + 512 * (Pos.size_nat input + Pos.size_nat from) + total
        | _ => total
        end) 0 trace
  | RQSourceFuel graph count queue _ _ =>
    256 + 256 * rw_rebuild_fuel_work (length (rw_roots graph)) count
      (length (rw_pending_sequence queue))
  end.


Definition rw_rq_receipts_budget {K Sort V} (receipts : list (rw_rq_receipt K Sort V)) : nat :=
  fold_right (fun receipt total => rw_rq_receipt_budget receipt + total) 0 receipts.


Inductive rw_rq_receipt_valid {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V) :
    rw_rq_receipt K Sort V -> Prop :=
  | RQValidBlock : forall site, rw_rq_receipt_valid op sort value (RQSourceBlock site)
  | RQValidGet : forall A code (before : Trie.t A) out trace,
      audit_trie_get code before = (out, trace) ->
      rw_rq_receipt_valid op sort value (RQSourceGet code before out trace)
  | RQValidUpdate : forall A code item (before after : Trie.t A) trace,
      audit_trie_update code item before = (after, trace) ->
      rw_rq_receipt_valid op sort value (RQSourceUpdate code item before after trace)
  | RQValidOperator : forall input code body,
      rw_queue_encoder_run op input = (code, body) ->
      rw_rq_receipt_valid op sort value (RQSourceOperator input code body)
  | RQValidSort : forall input code body,
      rw_queue_encoder_run sort input = (code, body) ->
      rw_rq_receipt_valid op sort value (RQSourceSort input code body)
  | RQValidVariable : forall input code body,
      rw_queue_encoder_run value input = (code, body) ->
      rw_rq_receipt_valid op sort value (RQSourceVariable input code body)
  | RQValidPair : forall input code trace,
      audit_pair_encode audit_positive_encode audit_positive_encode input = (code, trace) ->
      rw_rq_receipt_valid op sort value (RQSourcePair input code trace)
  | RQValidNode : forall input code trace,
      rw_node_encode_atomic (rw_external_encoding_events op) (rw_external_encoding_events sort)
        (rw_external_encoding_events value) input = (code, trace) ->
      rw_rq_receipt_valid op sort value (RQSourceNode input code trace)
  | RQValidDecision : forall a b answer trace,
      rw_rq_decision_atomic a b = (answer, trace) ->
      rw_rq_receipt_valid op sort value (RQSourceDecision a b answer trace)
  | RQValidCollapse : forall from into before after trace,
      audit_map_transform (rw_rq_collapse_source_child from into) before = (after, trace) ->
      rw_rq_receipt_valid op sort value (RQSourceCollapse from into before after trace)
  | RQValidFuel : forall graph count queue fuel trace,
      rw_rebuild_fuel_atomic graph count queue = (fuel, trace) ->
      rw_rq_receipt_valid op sort value (RQSourceFuel graph count queue fuel trace).

(** Every recorded primitive obeys a ceiling computed from its own original operands. *)

(** This statement fixes the rq receipt bound statement contract. *)
Definition rw_rq_receipt_bound_statement : Prop :=
  forall K Sort V (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) receipt,
  rw_rq_receipt_valid op sort value receipt ->
  rw_rq_receipt_work receipt <= rw_rq_receipt_budget receipt.

(** Actual source receipt streams compose primitive ceilings without a whole-bound premise. *)

(** This statement fixes the rq receipts bound statement contract. *)
Definition rw_rq_receipts_bound_statement : Prop :=
  forall K Sort V (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) receipts,
  Forall (rw_rq_receipt_valid op sort value) receipts ->
  rw_rq_receipts_work receipts <= rw_rq_receipts_budget receipts.
```

## Galois.Rewrite.RewriteAuditQueueCollections

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditQueueCollections.v`.

```rocq
(** * RewriteAuditQueueCollections

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditQueueKernel RewriteAuditQueueReference.
Import List.ListNotations.

Local Notation "'rqlet' x ':=' e 'in' c" :=
  (rw_rq_bind 1020 e (fun x => c))
  (at level 10, x ident, e at level 100, c at level 200).

Definition rw_rq_insert_source {K Sort V} (p : rw_pair) (queue : rw_pending_queue) :
    rw_rq_source K Sort V rw_pending_queue :=
  rqlet code := rw_rq_pair_encode p in
  rqlet found := rw_rq_map_code_get code (rw_pending_members queue) in
  match found with
  | Some _ => rw_rq_return 1021 queue
  | None =>
    rqlet write_code := rw_rq_pair_encode p in
    rqlet members := rw_rq_code_set write_code (p, tt) (rw_pending_members queue) in
    rw_rq_return 1022 (RwPendingQueue (p :: rw_pending_sequence queue) members)
  end.


Definition rw_rq_prepend_source {K Sort V} (pairs : list rw_pair) (queue : rw_pending_queue) :
    rw_rq_source K Sort V rw_pending_queue :=
  rw_rq_source_fold_right rw_rq_insert_source pairs queue.


Definition rw_rq_pop_source {K Sort V} (queue : rw_pending_queue) :
    rw_rq_source K Sort V (option (rw_pair * rw_pending_queue)) :=
  match rw_pending_sequence queue with
  | nil => rw_rq_return 1023 None
  | p :: rest =>
    rqlet code := rw_rq_pair_encode p in
    rqlet members := rw_rq_code_remove code (rw_pending_members queue) in
    rw_rq_return 1024 (Some (p, RwPendingQueue rest members))
  end.


Fixpoint rw_rq_id_member_source {K Sort V} (target : rw_id) (ids : list rw_id) :
    rw_rq_source K Sort V bool :=
  match ids with
  | nil => rw_rq_return 1025 false
  | id :: rest =>
    rqlet tail := rw_rq_id_member_source target rest in
    rqlet same := rw_rq_decision id target in
    rw_rq_return 1026 (same || tail)
  end.


Fixpoint rw_rq_id_nodup_source {K Sort V} (ids : list rw_id) :
    rw_rq_source K Sort V (list rw_id) :=
  match ids with
  | nil => rw_rq_return 1027 nil
  | id :: rest =>
    rqlet present := rw_rq_id_member_source id rest in
    rqlet tail := rw_rq_id_nodup_source rest in
    rw_rq_return 1028 (if present then tail else id :: tail)
  end.


Fixpoint rw_rq_remove_ids_source {K Sort V} (target : rw_id) (ids : list rw_id) :
    rw_rq_source K Sort V (list rw_id) :=
  match ids with
  | nil => rw_rq_return 1029 nil
  | id :: rest =>
    rqlet same := rw_rq_decision target id in
    rqlet tail := rw_rq_remove_ids_source target rest in
    rw_rq_return 1030 (if same then tail else id :: tail)
  end.


Definition rw_rq_bucket_add_source {K Sort V A}
    (encoder : A -> rw_rq_source K Sort V positive) (key : A) (id : rw_id)
    (table : Map.t A (list rw_id)) : rw_rq_source K Sort V (Map.t A (list rw_id)) :=
  rqlet code := encoder key in
  rqlet found := rw_rq_map_code_get code table in
  let ids := match found with Some xs => xs | None => nil end in
  rqlet unique := rw_rq_id_nodup_source (id :: ids) in
  rqlet write_code := encoder key in
  rw_rq_code_set write_code (key, unique) table.


Definition rw_rq_bucket_remove_source {K Sort V A}
    (encoder : A -> rw_rq_source K Sort V positive) (key : A) (id : rw_id)
    (table : Map.t A (list rw_id)) : rw_rq_source K Sort V (Map.t A (list rw_id)) :=
  rqlet code := encoder key in
  rqlet found := rw_rq_map_code_get code table in
  let ids := match found with Some xs => xs | None => nil end in
  rqlet retained := rw_rq_remove_ids_source id ids in
  rqlet write_code := encoder key in
  rw_rq_code_set write_code (key, retained) table.


Definition rw_rq_table_add_source {K Sort V A}
    (encoder : A -> rw_rq_source K Sort V positive) (keys : list A) (id : rw_id)
    (table : Map.t A (list rw_id)) : rw_rq_source K Sort V (Map.t A (list rw_id)) :=
  rw_rq_source_fold_right (fun key acc => rw_rq_bucket_add_source encoder key id acc) keys table.


Definition rw_rq_table_remove_source {K Sort V A}
    (encoder : A -> rw_rq_source K Sort V positive) (keys : list A) (id : rw_id)
    (table : Map.t A (list rw_id)) : rw_rq_source K Sort V (Map.t A (list rw_id)) :=
  rw_rq_source_fold_right (fun key acc => rw_rq_bucket_remove_source encoder key id acc) keys table.


Definition rw_rq_positive_encode {K Sort V} (id : positive) : rw_rq_source K Sort V positive :=
  rw_rq_return 1031 id.


Definition rw_rq_find_source {K Sort V} (g : rw_graph K Sort V) (id : rw_id) :
    rw_rq_source K Sort V (option rw_id) :=
  rqlet code := rw_rq_positive_encode id in
  rw_rq_map_code_get code (rw_class_roots g).


Definition rw_rq_node_source {K Sort V} (g : rw_graph K Sort V) (id : rw_id) :
    rw_rq_source K Sort V (option (rw_id * rw_node K Sort V)) :=
  rqlet code := rw_rq_positive_encode id in
  rw_rq_map_code_get code (rw_nodes g).


Definition rw_rq_sort_source {K Sort V} (g : rw_graph K Sort V) (id : rw_id) :
    rw_rq_source K Sort V (option Sort) :=
  rqlet code := rw_rq_positive_encode id in
  rw_rq_map_code_get code (rw_sorts g).


Definition rw_rq_canon_node_source {K Sort V} (g : rw_graph K Sort V)
    (node : rw_node K Sort V) : rw_rq_source K Sort V (rw_node K Sort V) :=
  match node with
  | RWNVar s v => rw_rq_return 1032 (RWNVar s v)
  | RWNApp s k ids =>
    rqlet canonical := rw_rq_source_map (fun id =>
      rqlet found := rw_rq_find_source g id in
      rw_rq_return 1033 (match found with Some r => r | None => id end)) ids in
    rw_rq_return 1034 (RWNApp s k canonical)
  end.


Fixpoint rw_rq_root_filter_source {K Sort V} (a b : rw_id) (roots : list rw_id) :
    rw_rq_source K Sort V (list rw_id) :=
  match roots with
  | nil => rw_rq_return 1035 nil
  | root :: rest =>
    rqlet first := rw_rq_decision root a in
    rqlet second := rw_rq_decision root b in
    rqlet tail := rw_rq_root_filter_source a b rest in
    rw_rq_return 1036 (if first || second then tail else root :: tail)
  end.


Definition rw_rq_merge_source {K Sort V} (g : rw_graph K Sort V) (a b : rw_id) :
    rw_rq_source K Sort V (rw_graph K Sort V) :=
  rqlet roots := rw_rq_root_filter_source a b (rw_roots g) in
  rqlet classes := rw_rq_collapse_source b a (rw_class_roots g) in
  rw_rq_return 1037 (RwGraph (a :: roots) (rw_nodes_in g) classes (rw_sorts g) (rw_nodes g)).


Definition rw_rq_union_source {K Sort V} (sort : rw_queue_encoder_adapter Sort)
    (g : rw_graph K Sort V) (a b : rw_id) : rw_rq_source K Sort V (option (rw_graph K Sort V)) :=
  rqlet first := rw_rq_find_source g a in
  match first with
  | None => rw_rq_return 1038 None
  | Some ra =>
    rqlet second := rw_rq_find_source g b in
    match second with
    | None => rw_rq_return 1039 None
    | Some rb =>
      rqlet first_sort := rw_rq_sort_source g a in
      match first_sort with
      | None => rw_rq_return 1040 None
      | Some sa =>
        rqlet second_sort := rw_rq_sort_source g b in
        match second_sort with
        | None => rw_rq_return 1041 None
        | Some sb =>
          rqlet ca := rw_rq_sort_encode sort sa in
          rqlet cb := rw_rq_sort_encode sort sb in
          rqlet same := rw_rq_decision ca cb in
          if same then rqlet out := rw_rq_merge_source g ra rb in rw_rq_return 1042 (Some out)
          else rw_rq_return 1043 None
        end
      end
    end
  end.
```

## Galois.Rewrite.RewriteAuditQueueIndex

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditQueueIndex.v`.

```rocq
(** * RewriteAuditQueueIndex

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditQueueCollections RewriteAuditQueueKernel
  RewriteAuditQueueReference.
Import List.ListNotations.

Local Notation "'rqlet' x ':=' e 'in' c" :=
  (rw_rq_bind 1020 e (fun x => c))
  (at level 10, x ident, e at level 100, c at level 200).

Definition rw_rq_operator_keys_source {K Sort V} (node : rw_node K Sort V) :
    rw_rq_source K Sort V (list K) :=
  match node with
  | RWNVar _ _ => rw_rq_return 1044 nil
  | RWNApp _ op _ => rw_rq_return 1045 [op]
  end.


Definition rw_rq_child_keys_source {K Sort V} (node : rw_node K Sort V) :
    rw_rq_source K Sort V (list rw_id) :=
  match node with
  | RWNVar _ _ => rw_rq_return 1046 nil
  | RWNApp _ _ children => rw_rq_return 1047 children
  end.


Definition rw_rq_root_keys_source {K Sort V} (g : rw_graph K Sort V)
    (node : rw_node K Sort V) : rw_rq_source K Sort V (list rw_id) :=
  rqlet children := rw_rq_child_keys_source node in
  rw_rq_source_flat_map (fun child =>
    rqlet found := rw_rq_find_source g child in
    rw_rq_return 1048 (match found with None => nil | Some root => [root] end)) children.


Definition rw_rq_variable_keys_source {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (node : rw_node K Sort V) : rw_rq_source K Sort V (list rw_id) :=
  match node with
  | RWNVar s v =>
    rqlet code := rw_rq_node_encode op sort value (RWNVar s v) in
    rw_rq_return 1049 [code]
  | RWNApp _ _ _ => rw_rq_return 1050 nil
  end.


Definition rw_rq_build_table_source {K Sort V A}
    (encoder : A -> rw_rq_source K Sort V positive)
    (keys : rw_node K Sort V -> rw_rq_source K Sort V (list A))
    (g : rw_graph K Sort V) (ids : list rw_id) :
    rw_rq_source K Sort V (Map.t A (list rw_id)) :=
  rw_rq_source_fold_right (fun id table =>
    rqlet found := rw_rq_node_source g id in
    match found with
    | None => rw_rq_return 1051 table
    | Some (_, node) =>
      rqlet actual_keys := keys node in
      rw_rq_table_add_source encoder actual_keys id table
    end) ids Map.empty.


Definition rw_rq_prepare_source {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (g : rw_graph K Sort V) : rw_rq_source K Sort V (rw_index K * Map.t rw_id (list rw_id)) :=
  rqlet ops := rw_rq_build_table_source (rw_rq_operator_encode op)
    rw_rq_operator_keys_source g (rw_nodes_in g) in
  rqlet children := rw_rq_build_table_source rw_rq_positive_encode
    rw_rq_child_keys_source g (rw_nodes_in g) in
  rqlet roots := rw_rq_build_table_source rw_rq_positive_encode
    (rw_rq_root_keys_source g) g (rw_nodes_in g) in
  rqlet variables := rw_rq_build_table_source rw_rq_positive_encode
    (rw_rq_variable_keys_source op sort value) g (rw_nodes_in g) in
  rw_rq_return 1052 (RwIndex ops children roots, variables).


Definition rw_rq_partners_source {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (base : rw_graph K Sort V) (ix : rw_index K) (vars : Map.t rw_id (list rw_id))
    (id : rw_id) : rw_rq_source K Sort V (list rw_id) :=
  rqlet found := rw_rq_node_source base id in
  match found with
  | None => rw_rq_return 1053 nil
  | Some (_, RWNVar s v) =>
    rqlet key := rw_rq_node_encode op sort value (RWNVar s v) in
    rqlet code := rw_rq_positive_encode key in
    rqlet bucket := rw_rq_map_code_get code vars in
    rw_rq_return 1054 (match bucket with None => nil | Some ids => ids end)
  | Some (_, RWNApp _ k _) =>
    rqlet code := rw_rq_operator_encode op k in
    rqlet bucket := rw_rq_map_code_get code (rw_index_ops ix) in
    rw_rq_return 1055 (match bucket with None => nil | Some ids => ids end)
  end.


Definition rw_rq_initial_source {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (base : rw_graph K Sort V) (ix : rw_index K) (vars : Map.t rw_id (list rw_id)) :
    rw_rq_source K Sort V (rw_pending_queue * nat) :=
  rw_rq_source_fold_right (fun id state =>
    rqlet partners := rw_rq_partners_source op sort value base ix vars id in
    rw_rq_source_fold_right (fun other current =>
      let '(queue, count) := current in
      rqlet next := rw_rq_insert_source (id, other) queue in
      rw_rq_return 1056 (next, S count)) partners state)
    (rw_nodes_in base) (rw_pending_empty, 0).


Definition rw_rq_parent_source {K Sort V} (g : rw_graph K Sort V) (ix : rw_index K)
    (id : rw_id) : rw_rq_source K Sort V (list rw_id) :=
  rqlet found := rw_rq_find_source g id in
  match found with
  | None => rw_rq_return 1057 nil
  | Some root =>
    rqlet code := rw_rq_positive_encode root in
    rqlet found_bucket := rw_rq_map_code_get code (rw_index_root_parents ix) in
    rw_rq_return 1058 (match found_bucket with None => nil | Some ids => ids end)
  end.


Definition rw_rq_index_update_source {K Sort V} (g g' : rw_graph K Sort V)
    (ix : rw_index K) (a b : rw_id) : rw_rq_source K Sort V (rw_index K) :=
  rqlet first := rw_rq_find_source g a in
  match first with
  | None => rw_rq_return 1059 ix
  | Some ra =>
    rqlet second := rw_rq_find_source g b in
    match second with
    | None => rw_rq_return 1060 ix
    | Some rb =>
      rqlet new_root := rw_rq_find_source g' a in
      match new_root with
      | None => rw_rq_return 1061 ix
      | Some root =>
        let before := rw_index_root_parents ix in
        rqlet first_bucket := rw_rq_map_code_get ra before in
        rqlet second_bucket := rw_rq_map_code_get rb before in
        let xs := match first_bucket with None => nil | Some ids => ids end in
        let ys := match second_bucket with None => nil | Some ids => ids end in
        rqlet joined := rw_rq_source_append xs ys in
        rqlet unique := rw_rq_id_nodup_source joined in
        rqlet removed_a := rw_rq_code_remove ra before in
        rqlet without := rw_rq_code_remove rb removed_a in
        rqlet updated := rw_rq_code_set root (root, unique) without in
        rw_rq_return 1062 (RwIndex (rw_index_ops ix) (rw_index_parents ix) updated)
      end
    end
  end.


Definition rw_rq_change_keys_source {K Sort V A}
    (g : rw_graph K Sort V)
    (keys : rw_node K Sort V -> rw_rq_source K Sort V (list A)) (id : rw_id) :
    rw_rq_source K Sort V (list A) :=
  rqlet found := rw_rq_node_source g id in
  match found with
  | None => rw_rq_return 1063 nil
  | Some (_, node) => keys node
  end.


Definition rw_rq_change_table_source {K Sort V A}
    (encoder : A -> rw_rq_source K Sort V positive) (g g' : rw_graph K Sort V)
    (old_keys new_keys : rw_node K Sort V -> rw_rq_source K Sort V (list A))
    (table : Map.t A (list rw_id)) (id : rw_id) : rw_rq_source K Sort V (Map.t A (list rw_id)) :=
  rqlet new := rw_rq_change_keys_source g' new_keys id in
  rqlet old := rw_rq_change_keys_source g old_keys id in
  rqlet removed := rw_rq_table_remove_source encoder old id table in
  rw_rq_table_add_source encoder new id removed.


Definition rw_rq_change_index_source {K Sort V} (op : rw_queue_encoder_adapter K)
    (g g' : rw_graph K Sort V) (ix : rw_index K) (id : rw_id) :
    rw_rq_source K Sort V (rw_index K) :=
  rqlet ops := rw_rq_change_table_source (rw_rq_operator_encode op) g g'
    rw_rq_operator_keys_source rw_rq_operator_keys_source (rw_index_ops ix) id in
  rqlet children := rw_rq_change_table_source rw_rq_positive_encode g g'
    rw_rq_child_keys_source rw_rq_child_keys_source (rw_index_parents ix) id in
  rqlet roots := rw_rq_change_table_source rw_rq_positive_encode g g'
    (rw_rq_root_keys_source g) (rw_rq_root_keys_source g') (rw_index_root_parents ix) id in
  rw_rq_return 1064 (RwIndex ops children roots).


Definition rw_rq_final_one_source {K Sort V} (op : rw_queue_encoder_adapter K)
    (g : rw_graph K Sort V) (ix : rw_index K) (id : rw_id) :
    rw_rq_source K Sort V (rw_graph K Sort V * rw_index K) :=
  rqlet found := rw_rq_node_source g id in
  match found with
  | None => rw_rq_return 1065 (g, ix)
  | Some (owner, node) =>
    rqlet canonical := rw_rq_canon_node_source g node in
    rqlet nodes := rw_rq_code_set id (id, (owner, canonical)) (rw_nodes g) in
    let next := RwGraph (rw_roots g) (rw_nodes_in g) (rw_class_roots g) (rw_sorts g) nodes in
    rqlet next_index := rw_rq_change_index_source op g next ix id in
    rw_rq_return 1066 (next, next_index)
  end.


Fixpoint rw_rq_final_all_source {K Sort V} (op : rw_queue_encoder_adapter K)
    (ids : list rw_id) (g : rw_graph K Sort V) (ix : rw_index K) :
    rw_rq_source K Sort V (rw_graph K Sort V * rw_index K) :=
  match ids with
  | nil => rw_rq_return 1067 (g, ix)
  | id :: rest =>
    rqlet next := rw_rq_final_one_source op g ix id in
    let '(graph, index) := next in rw_rq_final_all_source op rest graph index
  end.
```

## Galois.Rewrite.RewriteAuditQueueRebuild

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditQueueRebuild.v`.

```rocq
(** * RewriteAuditQueueRebuild

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditQueueCollections RewriteAuditQueueIndex
  RewriteAuditQueueKernel RewriteAuditQueueReference.
Import List.ListNotations.

Local Notation "'rqlet' x ':=' e 'in' c" :=
  (rw_rq_bind 1020 e (fun x => c))
  (at level 10, x ident, e at level 100, c at level 200).

Definition rw_rq_enqueue_source {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (base : rw_graph K Sort V) (baseix : rw_index K) (vars : Map.t rw_id (list rw_id))
    (g : rw_graph K Sort V) (ix : rw_index K) (a b : rw_id) (queue : rw_pending_queue) :
    rw_rq_source K Sort V rw_pending_queue :=
  rqlet first := rw_rq_parent_source g ix a in
  rqlet second := rw_rq_parent_source g ix b in
  rqlet parents := rw_rq_source_append first second in
  rqlet pairs := rw_rq_source_flat_map (fun id =>
    rqlet partners := rw_rq_partners_source op sort value base baseix vars id in
    rw_rq_source_map (fun other => rw_rq_return 1068 (id, other)) partners) parents in
  rw_rq_prepend_source pairs queue.


Definition rw_rq_step_source {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (base : rw_graph K Sort V) (baseix : rw_index K) (vars : Map.t rw_id (list rw_id))
    (state : rw_queue_state K Sort V) : rw_rq_source K Sort V (rw_queue_state K Sort V) :=
  let g := rw_queue_graph state in
  let ix := rw_queue_index state in
  rqlet popped := rw_rq_pop_source (rw_queue_pending state) in
  match popped with
  | None => rw_rq_return 1069 state
  | Some ((n, m), rest) =>
    let dropped := RwQueueState g ix rest in
    rqlet first := rw_rq_node_source g n in
    match first with
    | None => rw_rq_return 1070 dropped
    | Some (a, node) =>
      rqlet second := rw_rq_node_source g m in
      match second with
      | None => rw_rq_return 1071 dropped
      | Some (b, other) =>
        rqlet first_root := rw_rq_find_source g a in
        match first_root with
        | None => rw_rq_return 1072 dropped
        | Some ra =>
          rqlet second_root := rw_rq_find_source g b in
          match second_root with
          | None => rw_rq_return 1073 dropped
          | Some rb =>
            rqlet canonical_a := rw_rq_canon_node_source g node in
            rqlet code_a := rw_rq_node_encode op sort value canonical_a in
            rqlet canonical_b := rw_rq_canon_node_source g other in
            rqlet code_b := rw_rq_node_encode op sort value canonical_b in
            rqlet same_code := rw_rq_decision code_a code_b in
            if same_code then
              rqlet same_root := rw_rq_decision ra rb in
              if same_root then rw_rq_return 1074 dropped
              else
                rqlet united := rw_rq_union_source sort g a b in
                match united with
                | None => rw_rq_return 1075 dropped
                | Some next_graph =>
                  rqlet next_index := rw_rq_index_update_source g next_graph ix a b in
                  rqlet next_queue := rw_rq_enqueue_source op sort value base baseix vars
                    g ix a b rest in
                  rw_rq_return 1076 (RwQueueState next_graph next_index next_queue)
                end
            else rw_rq_return 1077 dropped
          end
        end
      end
    end
  end.


Fixpoint rw_rq_repeat_source {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (base : rw_graph K Sort V) (ix : rw_index K) (vars : Map.t rw_id (list rw_id))
    (fuel : positive) (state : rw_queue_state K Sort V) :
    rw_rq_source K Sort V (rw_queue_state K Sort V) :=
  match rw_pending_sequence (rw_queue_pending state) with
  | nil => rw_rq_return 1078 state
  | _ :: _ =>
    match fuel with
    | xH => rw_rq_step_source op sort value base ix vars state
    | xO rest =>
      rqlet middle := rw_rq_repeat_source op sort value base ix vars rest state in
      rw_rq_repeat_source op sort value base ix vars rest middle
    | xI rest =>
      rqlet first := rw_rq_step_source op sort value base ix vars state in
      rqlet middle := rw_rq_repeat_source op sort value base ix vars rest first in
      rw_rq_repeat_source op sort value base ix vars rest middle
    end
  end.


Definition rw_rq_fuel_source {K Sort V} (g : rw_graph K Sort V) (count : nat)
    (queue : rw_pending_queue) : rw_rq_source K Sort V positive :=
  let '(fuel, trace) := rw_rebuild_fuel_atomic g count queue in
  RwRqSource fuel [RQSourceFuel g count queue fuel trace].


Definition rw_rq_rebuild_source {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (g : rw_graph K Sort V) : rw_rq_source K Sort V (rw_graph K Sort V) :=
  rqlet prepared := rw_rq_prepare_source op sort value g in
  let '(ix, vars) := prepared in
  rqlet initial_queue := rw_rq_initial_source op sort value g ix vars in
  let '(queue, count) := initial_queue in
  rqlet fuel := rw_rq_fuel_source g count queue in
  rqlet final := rw_rq_repeat_source op sort value g ix vars fuel (RwQueueState g ix queue) in
  rqlet canonical := rw_rq_final_all_source op (rw_nodes_in (rw_queue_graph final))
    (rw_queue_graph final) (rw_queue_index final) in
  rw_rq_return 1079 (fst canonical).


Inductive rw_rq_rebuild_source_run {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (g : rw_graph K Sort V) : rw_graph K Sort V -> list (rw_rq_receipt K Sort V) -> Prop :=
  | RQRebuildSourceRun : forall output receipts,
      rw_rq_rebuild_source op sort value g = RwRqSource output receipts ->
      rw_rq_rebuild_source_run op sort value g output receipts.

(** The actual full source execution erases to the existing ordered rebuild on the same input. *)

(** This statement fixes the rq rebuild source erases statement contract. *)
Definition rw_rq_rebuild_source_erases_statement : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) g output receipts,
  (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
  (forall ty, fst (rw_queue_encoder_run sort ty) = encode ES ty) ->
  (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
  rw_rq_rebuild_source_run op sort value g output receipts ->
  output = rw_pending_rebuild EK ES EV g /\ output = rw_rebuild EK ES EV g.

(** Every primitive receipt belongs to its actual original invocation in the complete run. *)

(** This statement fixes the rq rebuild source valid statement contract. *)
Definition rw_rq_rebuild_source_valid_statement : Prop :=
  forall K Sort V (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) g output receipts,
  rw_rq_rebuild_source_run op sort value g output receipts ->
  Forall (rw_rq_receipt_valid op sort value) receipts.

(** The complete source run composes ceilings for its own actual input and intermediate states. *)

(** This statement fixes the rq rebuild source bound statement contract. *)
Definition rw_rq_rebuild_source_bound_statement : Prop :=
  forall K Sort V (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) g output receipts,
  rw_rq_rebuild_source_run op sort value g output receipts ->
  rw_rq_receipts_work receipts <= rw_rq_receipts_budget receipts.

(** Ordered deduplication is linear in offered pairs plus their actual encoded bit lengths. *)

(** This statement fixes the rq prepend source linear statement contract. *)
Definition rw_rq_prepend_source_linear_statement : Prop :=
  forall K Sort V pairs queue,
  let source := @rw_rq_prepend_source K Sort V pairs queue in
  rw_rq_value source = rw_pending_prepend pairs queue /\
  rw_rq_receipts_work (rw_rq_receipts source) <=
    4096 * S (length pairs) +
      4096 * fold_right (fun p n => rw_pending_pair_key_bits p + n) 0 pairs.

(** A nonempty whole-source run retains real read/write/encoding receipts and the exact graph. *)
```

## Galois.Rewrite.RewriteAuditQueueContracts

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditQueueContracts.v`.

```rocq
(** * RewriteAuditQueueContracts

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditQueueKernel RewriteAuditQueueRebuild
  RewriteAuditQueueReference.
Import List.ListNotations.

Definition rw_rq_external_body {A} (execution : A -> positive -> nat -> Prop)
    (input : A) (code : positive) (events : list nat) : Prop :=
  exists body, events = [body] /\ execution input code body.


Definition rw_rq_variable_pair_external {Sort V}
    (sort_execution : Sort -> positive -> nat -> Prop)
    (value_execution : V -> positive -> nat -> Prop)
    (trace : list (audit_pair_event Sort V nat nat)) : Prop :=
  Forall (fun event => match event with
    | AuditPairFirst input code events => rw_rq_external_body sort_execution input code events
    | AuditPairSecond input code events => rw_rq_external_body value_execution input code events
    | AuditPairFrame _ => True
    end) trace.


Definition rw_rq_operator_pair_external {K}
    (op_execution : K -> positive -> nat -> Prop)
    (trace : list (audit_pair_event K (list rw_id) nat
      (audit_list_event rw_id (audit_basic_encoding_event positive)))) : Prop :=
  Forall (fun event => match event with
    | AuditPairFirst input code events => rw_rq_external_body op_execution input code events
    | _ => True
    end) trace.


Definition rw_rq_application_pair_external {K Sort}
    (op_execution : K -> positive -> nat -> Prop)
    (sort_execution : Sort -> positive -> nat -> Prop)
    (trace : list (audit_pair_event Sort (K * list rw_id) nat
      (audit_pair_event K (list rw_id) nat
        (audit_list_event rw_id (audit_basic_encoding_event positive))))) : Prop :=
  Forall (fun event => match event with
    | AuditPairFirst input code events => rw_rq_external_body sort_execution input code events
    | AuditPairSecond _ _ events => rw_rq_operator_pair_external op_execution events
    | AuditPairFrame _ => True
    end) trace.


Definition rw_rq_node_external_execution {K Sort V}
    (op_execution : K -> positive -> nat -> Prop)
    (sort_execution : Sort -> positive -> nat -> Prop)
    (value_execution : V -> positive -> nat -> Prop)
    (trace : list (rw_rq_node_event K Sort V)) : Prop :=
  Forall (fun event => match event with
    | AuditSumLeft _ _ events =>
      rw_rq_variable_pair_external sort_execution value_execution events
    | AuditSumRight _ _ events =>
      rw_rq_application_pair_external op_execution sort_execution events
    end) trace.


Definition rw_rq_receipt_external_execution {K Sort V}
    (op_execution : K -> positive -> nat -> Prop)
    (sort_execution : Sort -> positive -> nat -> Prop)
    (value_execution : V -> positive -> nat -> Prop) (receipt : rw_rq_receipt K Sort V) : Prop :=
  match receipt with
  | RQSourceOperator input code body => op_execution input code body
  | RQSourceSort input code body => sort_execution input code body
  | RQSourceVariable input code body => value_execution input code body
  | RQSourceNode _ _ events =>
    rw_rq_node_external_execution op_execution sort_execution value_execution events
  | _ => True
  end.

(** Every client encoder call in the source run retains its original execution witness. *)

(** This statement fixes the rq rebuild source external statement contract. *)
Definition rw_rq_rebuild_source_external_statement : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V)
    (op_execution : K -> positive -> nat -> Prop)
    (sort_execution : Sort -> positive -> nat -> Prop)
    (value_execution : V -> positive -> nat -> Prop) g output receipts,
  rw_queue_encoder_adapter_laws EK op_execution op ->
  rw_queue_encoder_adapter_laws ES sort_execution sort ->
  rw_queue_encoder_adapter_laws EV value_execution value ->
  rw_rq_rebuild_source_run op sort value g output receipts ->
  Forall (rw_rq_receipt_external_execution op_execution sort_execution value_execution) receipts.

(** The full original-invocation source relation, external calls and composed budget agree. *)

(** This statement fixes the rq rebuild source complete contract statement contract. *)
Definition rw_rq_rebuild_source_complete_contract_statement : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V)
    (op_execution : K -> positive -> nat -> Prop)
    (sort_execution : Sort -> positive -> nat -> Prop)
    (value_execution : V -> positive -> nat -> Prop) g,
  rw_queue_encoder_adapter_laws EK op_execution op ->
  rw_queue_encoder_adapter_laws ES sort_execution sort ->
  rw_queue_encoder_adapter_laws EV value_execution value ->
  let run := rw_rq_rebuild_source op sort value g in
  rw_rq_rebuild_source_run op sort value g (rw_rq_value run) (rw_rq_receipts run) /\
  rw_rq_value run = rw_pending_rebuild EK ES EV g /\
  rw_rq_value run = rw_rebuild EK ES EV g /\
  Forall (rw_rq_receipt_valid op sort value) (rw_rq_receipts run) /\
  Forall (rw_rq_receipt_external_execution op_execution sort_execution value_execution)
    (rw_rq_receipts run) /\
  rw_rq_receipts_work (rw_rq_receipts run) <= rw_rq_receipts_budget (rw_rq_receipts run).


Definition rw_rq_input_structure {K Sort V} (g : rw_graph K Sort V) : nat :=
  S (length (rw_roots g) + length (rw_nodes_in g) +
    audit_trie_nodes (rw_class_roots g) + audit_trie_nodes (rw_sorts g) +
    audit_trie_nodes (rw_nodes g) +
    fold_right (fun id total =>
      match rw_node_at g id with
      | Some (_, RWNApp _ _ children) => length children + total
      | _ => total
      end) 0 (rw_nodes_in g)).


Definition rw_rq_receipt_foreign_work {K Sort V} (receipt : rw_rq_receipt K Sort V) : nat :=
  match receipt with
  | RQSourceOperator _ _ body => body
  | RQSourceSort _ _ body => body
  | RQSourceVariable _ _ body => body
  | RQSourceNode _ _ events => rw_rq_node_external events
  | _ => 0
  end.


Definition rw_rq_receipt_dimension {K Sort V} (receipt : rw_rq_receipt K Sort V) : nat :=
  match receipt with
  | RQSourceGet code before _ _ => S (Pos.size_nat code + audit_trie_nodes before)
  | RQSourceUpdate code _ before after _ =>
    S (Pos.size_nat code + audit_trie_nodes before + audit_trie_nodes after)
  | RQSourceOperator _ code _ => S (Pos.size_nat code)
  | RQSourceSort _ code _ => S (Pos.size_nat code)
  | RQSourceVariable _ code _ => S (Pos.size_nat code)
  | RQSourcePair pair_value code _ =>
    S (Pos.size_nat (fst pair_value) + Pos.size_nat (snd pair_value) + Pos.size_nat code)
  | RQSourceNode _ code _ => S (Pos.size_nat code)
  | RQSourceDecision a b _ _ => S (Pos.size_nat a + Pos.size_nat b)
  | RQSourceCollapse from into before after _ =>
    S (Pos.size_nat from + Pos.size_nat into + audit_trie_nodes before + audit_trie_nodes after +
      fold_right (fun entry largest => Nat.max (Pos.size_nat (snd entry)) largest)
        0 (Map.elements before))
  | RQSourceFuel graph count queue fuel _ =>
    S (length (rw_roots graph) + count + length (rw_pending_sequence queue) + Pos.size_nat fuel)
  | RQSourceBlock _ => 1
  end.


Definition rw_rq_run_dimension {K Sort V} (receipts : list (rw_rq_receipt K Sort V)) : nat :=
  fold_right (fun receipt largest => Nat.max (rw_rq_receipt_dimension receipt) largest) 1 receipts.


Definition rw_rq_run_foreign_work {K Sort V} (receipts : list (rw_rq_receipt K Sort V)) : N :=
  fold_right (fun receipt total => (N.of_nat (rw_rq_receipt_foreign_work receipt) + total)%N)
    0%N receipts.


Definition rw_rq_whole_input_budget {K Sort V} (g : rw_graph K Sort V)
    (receipts : list (rw_rq_receipt K Sort V)) : N :=
  (rw_rq_run_foreign_work receipts +
    65536 * N.pow (N.of_nat (rw_rq_input_structure g)) 14 *
      N.pow (N.of_nat (rw_rq_run_dimension receipts)) 4)%N.

(** Source control and primitive-call occurrences have an input-only polynomial ceiling. *)

(** This statement fixes the rq source call count statement contract. *)
Definition rw_rq_source_call_count_statement : Prop :=
  forall K Sort V (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) g output receipts,
  rw_rq_rebuild_source_run op sort value g output receipts ->
  (N.of_nat (length receipts) <=
    65536 * N.pow (N.of_nat (rw_rq_input_structure g)) 10)%N.

(** Whole-source work is bounded independently of the number of returned receipts. *)

(** This statement fixes the rq rebuild input bound statement contract. *)
Definition rw_rq_rebuild_input_bound_statement : Prop :=
  forall K Sort V (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) g output receipts,
  rw_rq_rebuild_source_run op sort value g output receipts ->
  (N.of_nat (rw_rq_receipts_work receipts) <= rw_rq_whole_input_budget g receipts)%N.
```

## Galois.Rewrite.RewriteAuditIndexReference

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditIndexReference.v`.

```rocq
(** * RewriteAuditIndexReference

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditQueueReference.
Import List.ListNotations.

Record rw_phase_view (K Sort V : Type) := RwPhaseView {
  rw_view_find : rw_id -> option rw_id;
  rw_view_sort : rw_id -> option Sort;
  rw_view_node : rw_id -> option (rw_id * rw_node K Sort V);
  rw_view_operator_nodes : K -> list rw_id;
  rw_view_variable_nodes : V -> list rw_id;
  rw_view_parent_nodes : rw_id -> list rw_id;
  rw_view_roots : unit -> list rw_id;
  rw_view_nodes : unit -> list rw_id
}.
Arguments RwPhaseView {K Sort V}.
Arguments rw_view_find {K Sort V}.
Arguments rw_view_sort {K Sort V}.
Arguments rw_view_node {K Sort V}.
Arguments rw_view_operator_nodes {K Sort V}.
Arguments rw_view_variable_nodes {K Sort V}.
Arguments rw_view_parent_nodes {K Sort V}.
Arguments rw_view_roots {K Sort V}.
Arguments rw_view_nodes {K Sort V}.

Record rw_snapshot_view (K Sort V : Type) := RwSnapshotView {
  rw_snapshot_base : rw_phase_view K Sort V;
  rw_snapshot_graph : unit -> rw_graph K Sort V
}.
Arguments RwSnapshotView {K Sort V}.
Arguments rw_snapshot_base {K Sort V}.
Arguments rw_snapshot_graph {K Sort V}.

Definition rw_view_agrees {K Sort V} (g : rw_graph K Sort V) (v : rw_phase_view K Sort V) : Prop :=
  (forall c, rw_view_find v c = rw_find g c) /\
  (forall c, rw_view_sort v c = rw_class_sort g c) /\
  (forall n, rw_view_node v n = rw_node_at g n) /\
  (forall op, NoDup (rw_view_operator_nodes v op)) /\
  (forall value, NoDup (rw_view_variable_nodes v value)) /\
  (forall c, NoDup (rw_view_parent_nodes v c)) /\
  (forall op n, In n (rw_view_operator_nodes v op) <->
    exists owner sort children, rw_node_at g n = Some (owner, RWNApp sort op children)) /\
  (forall value n, In n (rw_view_variable_nodes v value) <->
    exists owner sort, rw_node_at g n = Some (owner, RWNVar sort value)) /\
  (forall c n, In n (rw_view_parent_nodes v c) <->
    exists root owner sort op children child,
      rw_find g c = Some root /\ rw_find g child = Some root /\
      rw_node_at g n = Some (owner, RWNApp sort op children) /\ In child children) /\
  rw_view_roots v tt = rw_roots g /\ rw_view_nodes v tt = rw_nodes_in g.

Definition rw_phase_ordered {K Sort V} (v : rw_phase_view K Sort V) : Prop :=
  (forall op, rw_view_operator_nodes v op =
    FinSet.elements (FinSet.of_list positive_encoding (rw_view_operator_nodes v op))) /\
  (forall value, rw_view_variable_nodes v value =
    FinSet.elements (FinSet.of_list positive_encoding (rw_view_variable_nodes v value))) /\
  forall id, rw_view_parent_nodes v id =
    FinSet.elements (FinSet.of_list positive_encoding (rw_view_parent_nodes v id)).

Definition rw_snapshot_agrees {K Sort V} (g : rw_graph K Sort V)
    (v : rw_snapshot_view K Sort V) : Prop :=
  rw_view_agrees g (rw_snapshot_base v) /\ rw_phase_ordered (rw_snapshot_base v) /\
  rw_snapshot_graph v tt = g.

Definition rw_snapshot_extract {K Sort V} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (vc : V -> nat) (oc : K -> nat)
    (view : rw_snapshot_view K Sort V) (root : rw_id) : option (rw_term K Sort V) :=
  rw_extract_tree EK ES EV vc oc (rw_snapshot_graph view tt) root.

(** This statement fixes the snapshot extract agrees contract. *)
Definition rw_snapshot_extract_agrees_contract : Prop := forall K Sort V (EK : encoding K) (ES :
    encoding Sort)
    (EV : encoding V) vc oc (g : rw_graph K Sort V) view root,
  rw_snapshot_agrees g view ->
  rw_snapshot_extract EK ES EV vc oc view root = rw_extract_tree EK ES EV vc oc g root.


Inductive rw_index_event : Type :=
  | RWIndexDirty : rw_id -> rw_index_event
  | RWIndexSkipped : rw_pair -> rw_index_event
  | RWIndexCongruence : rw_pair -> rw_id -> rw_id -> rw_id -> rw_index_event.

Inductive rw_run_event (K Sort V H : Type) : Type :=
  | RWRunRejected : rw_attempt K Sort V H -> rw_run_event K Sort V H
  | RWRunAccepted : rw_attempt K Sort V H -> list rw_index_event -> rw_run_event K Sort V H.
Arguments RWRunRejected {K Sort V H}.
Arguments RWRunAccepted {K Sort V H}.


Record rw_index_state (K Sort V : Type) := RWIndexState {
  rw_index_base : rw_graph K Sort V;
  rw_index_forest : UnionFind.t rw_id;
  rw_index_parent_buckets : Map.t rw_id (FinSet.t rw_id);
  rw_index_signatures : Map.t (rw_node K Sort V) (FinSet.t rw_id);
  rw_index_node_keys : Map.t rw_id (rw_node K Sort V);
  rw_index_dirty_order : list rw_id;
  rw_index_dirty_set : FinSet.t rw_id;
  rw_index_pending : rw_pending_queue;
  rw_index_operators : Map.t K (FinSet.t rw_id);
  rw_index_variables : Map.t V (FinSet.t rw_id);
  rw_index_fresh : positive
}.
Arguments RWIndexState {K Sort V}.
Arguments rw_index_base {K Sort V}.
Arguments rw_index_forest {K Sort V}.
Arguments rw_index_parent_buckets {K Sort V}.
Arguments rw_index_signatures {K Sort V}.
Arguments rw_index_node_keys {K Sort V}.
Arguments rw_index_dirty_order {K Sort V}.
Arguments rw_index_dirty_set {K Sort V}.
Arguments rw_index_pending {K Sort V}.
Arguments rw_index_operators {K Sort V}.
Arguments rw_index_variables {K Sort V}.
Arguments rw_index_fresh {K Sort V}.

Definition rw_index_find {K Sort V} (state : rw_index_state K Sort V) (id : rw_id) : option rw_id :=
  match rw_find (rw_index_base state) id with
  | None => None
  | Some root => Some (fst (UnionFind.find positive_encoding root (rw_index_forest state)))
  end.

Definition rw_index_graph {K Sort V} (state : rw_index_state K Sort V) : rw_graph K Sort V :=
  let base := rw_index_base state in
  let root r := fst (UnionFind.find positive_encoding r (rw_index_forest state)) in
  RwGraph (filter (fun r => Pos.eqb (root r) r) (rw_roots base)) (rw_nodes_in base)
    (Map.map root (rw_class_roots base)) (rw_sorts base) (rw_nodes base).

Definition rw_index_bucket {A} (E : encoding A) (key : A)
    (table : Map.t A (FinSet.t rw_id)) : FinSet.t rw_id :=
  match Map.get E key table with Some bucket => bucket | None => FinSet.empty end.

Definition rw_index_view {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (state : rw_index_state K Sort V) : rw_snapshot_view K Sort V :=
  RwSnapshotView (RwPhaseView (rw_index_find state) (rw_class_sort (rw_index_base state))
    (rw_node_at (rw_index_base state))
    (fun op => FinSet.elements (rw_index_bucket EK op (rw_index_operators state)))
    (fun value => FinSet.elements (rw_index_bucket EV value (rw_index_variables state)))
    (fun id => match rw_index_find state id with
      | None => nil
      | Some root => FinSet.elements (rw_index_bucket positive_encoding root
    (rw_index_parent_buckets state))
      end)
    (fun _ => rw_roots (rw_index_graph state)) (fun _ => rw_nodes_in (rw_index_base state)))
    (fun _ => rw_index_graph state).

Definition rw_index_canonical_node {K Sort V} (state : rw_index_state K Sort V)
    (node : rw_node K Sort V) : rw_node K Sort V :=
  let canon id := match rw_index_find state id with Some root => root | None => id end in
  match node with RWNVar sort v => RWNVar sort v | RWNApp sort op ids => RWNApp sort op (map
    canon ids) end.

Definition rw_index_phase_clean {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding
    V) (state : rw_index_state K Sort V) : Prop :=
  rw_index_dirty_order state = nil /\ rw_pending_sequence (rw_index_pending state) = nil.

Definition rw_index_valid {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (sig : rw_signature K Sort V) (state : rw_index_state K Sort V) : Prop :=
  let graph := rw_index_graph state in let base := rw_index_base state in
  let EN := rw_node_encoding EK ES EV in
  rw_graph_wf sig graph /\ rw_snapshot_agrees graph (rw_index_view EK ES EV state) /\
  UnionFind.wf positive_encoding (rw_index_forest state) /\
  (forall c, In c (UnionFind.keys positive_encoding (rw_index_forest state)) -> rw_find base c =
    Some c) /\
  Map.wf EK (rw_index_operators state) /\ Map.wf EV (rw_index_variables state) /\
  Map.wf positive_encoding (rw_index_parent_buckets state) /\ Map.wf EN (rw_index_signatures
    state) /\
  Map.wf positive_encoding (rw_index_node_keys state) /\
  (forall op, FinSet.wf positive_encoding (rw_index_bucket EK op (rw_index_operators state))) /\
  (forall value, FinSet.wf positive_encoding (rw_index_bucket EV value (rw_index_variables
    state))) /\
  (forall root, FinSet.wf positive_encoding (rw_index_bucket positive_encoding root
    (rw_index_parent_buckets state))) /\
  (forall key, FinSet.wf positive_encoding (rw_index_bucket EN key (rw_index_signatures state))) /\
  NoDup (rw_index_dirty_order state) /\ FinSet.wf positive_encoding (rw_index_dirty_set state) /\
  (forall n, FinSet.mem positive_encoding n (rw_index_dirty_set state) = true <-> In n
    (rw_index_dirty_order state)) /\
  (forall n, In n (rw_index_dirty_order state) -> exists owner node, rw_node_at base n = Some
    (owner,node)) /\
  (forall n owner node, rw_node_at base n = Some (owner,node) -> ~ In n (rw_index_dirty_order
    state) ->
    Map.get positive_encoding n (rw_index_node_keys state) = Some (rw_index_canonical_node state
    node)) /\
  (forall n key, Map.get positive_encoding n (rw_index_node_keys state) = Some key <->
    FinSet.mem positive_encoding n (rw_index_bucket EN key (rw_index_signatures state)) = true) /\
  (forall n key, Map.get positive_encoding n (rw_index_node_keys state) = Some key ->
    exists owner node, rw_node_at base n = Some (owner,node)) /\
  (forall n m owner other_owner node other root other_root,
    rw_node_at base n = Some (owner,node) -> rw_node_at base m = Some (other_owner,other) ->
    ~ In n (rw_index_dirty_order state) -> ~ In m (rw_index_dirty_order state) ->
    rw_index_canonical_node state node = rw_index_canonical_node state other ->
    rw_index_find state owner = Some root -> rw_index_find state other_owner = Some other_root ->
    root <> other_root -> In (n,m) (rw_pending_sequence (rw_index_pending state)) \/
      In (m,n) (rw_pending_sequence (rw_index_pending state))) /\
  rw_pending_valid (rw_index_pending state) /\
  (forall p, In p (rw_pending_sequence (rw_index_pending state)) ->
    (exists owner node, rw_node_at base (fst p) = Some (owner,node)) /\
    (exists owner node, rw_node_at base (snd p) = Some (owner,node))) /\
  (forall c root, rw_find graph c = Some root -> (c < rw_index_fresh state)%positive) /\
  (forall n owner node, rw_node_at graph n = Some (owner,node) -> (n < rw_index_fresh
    state)%positive) /\
  (rw_index_phase_clean EK ES EV state -> rw_clean graph).
```

## Galois.Rewrite.RewriteAuditIndexBuild

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditIndexBuild.v`.

```rocq
(** * RewriteAuditIndexBuild

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexReference.
Import List.ListNotations.

Record rw_ri_build_acc (K V : Type) := RwRiBuildAcc {
  rw_ri_build_ops : Map.t K (FinSet.t rw_id);
  rw_ri_build_vars : Map.t V (FinSet.t rw_id);
  rw_ri_build_parents : Map.t rw_id (FinSet.t rw_id)
}.
Arguments RwRiBuildAcc {K V}.
Arguments rw_ri_build_ops {K V}.
Arguments rw_ri_build_vars {K V}.
Arguments rw_ri_build_parents {K V}.


Definition rw_ri_bucket_add {A} (E : encoding A) (key : A) (id : rw_id)
    (table : Map.t A (FinSet.t rw_id)) : Map.t A (FinSet.t rw_id) :=
  Map.set E key (FinSet.add positive_encoding id (rw_index_bucket E key table)) table.


Fixpoint rw_ri_build_parent_nodes_value {K Sort V} (g : rw_graph K Sort V) (id : rw_id)
    (children : list rw_id) (table : Map.t rw_id (FinSet.t rw_id)) : Map.t rw_id (FinSet.t rw_id) :=
  match children with
  | nil => table
  | child :: rest =>
    match rw_find g child with
    | None => rw_ri_build_parent_nodes_value g id rest table
    | Some root => rw_ri_build_parent_nodes_value g id rest (rw_ri_bucket_add positive_encoding
    root id table)
    end
  end.


Fixpoint rw_ri_build_nodes_value {K Sort V} (EK : encoding K) (EV : encoding V)
    (g : rw_graph K Sort V) (ids : list rw_id) (acc : rw_ri_build_acc K V) : rw_ri_build_acc K V :=
  match ids with
  | nil => acc
  | id :: rest =>
    match rw_node_at g id with
    | None => rw_ri_build_nodes_value EK EV g rest acc
    | Some (_, RWNVar _ v) =>
      rw_ri_build_nodes_value EK EV g rest
        (RwRiBuildAcc (rw_ri_build_ops acc) (rw_ri_bucket_add EV v id (rw_ri_build_vars acc))
          (rw_ri_build_parents acc))
    | Some (_, RWNApp _ op children) =>
      let ops := rw_ri_bucket_add EK op id (rw_ri_build_ops acc) in
      let parents := rw_ri_build_parent_nodes_value g id children (rw_ri_build_parents acc) in
      rw_ri_build_nodes_value EK EV g rest (RwRiBuildAcc ops (rw_ri_build_vars acc) parents)
    end
  end.
```

## Galois.Rewrite.RewriteAuditIndexPrepareReference

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditIndexPrepareReference.v`.

```rocq
(** * RewriteAuditIndexPrepareReference

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexBuild RewriteAuditIndexReference
  RewriteAuditQueueReference.
Import List.ListNotations.

Inductive rw_ri_fresh_call (K Sort V : Type) : Type :=
  | RIFreshRoots : Map.t rw_id rw_id -> list (rw_id * rw_id) ->
      list (audit_elements_event (rw_id * rw_id)) -> rw_ri_fresh_call K Sort V
  | RIFreshNodes : Map.t rw_id (rw_id * rw_node K Sort V) ->
      list (rw_id * (rw_id * rw_node K Sort V)) ->
      list (audit_elements_event (rw_id * (rw_id * rw_node K Sort V))) -> rw_ri_fresh_call K Sort V
  | RIFreshMax : positive -> positive -> positive -> rw_ri_fresh_call K Sort V
  | RIFreshSucc : positive -> positive -> list audit_nat_encoding_event -> rw_ri_fresh_call K
    Sort V.
Arguments RIFreshRoots {K Sort V}.
Arguments RIFreshNodes {K Sort V}.
Arguments RIFreshMax {K Sort V}.
Arguments RIFreshSucc {K Sort V}.


Definition rw_ri_fresh_event_cost {K Sort V} (event : audit_event (rw_ri_fresh_call K Sort V)) :
    nat :=
  match event with
  | AuditCall (RIFreshRoots _ _ trace) => 1 + audit_elements_work trace
  | AuditCall (RIFreshNodes _ _ trace) => 1 + audit_elements_work trace
  | AuditCall (RIFreshMax key current _) => 4 + Pos.size_nat key + Pos.size_nat current
  | AuditCall (RIFreshSucc _ _ trace) => 1 + audit_nat_events_work trace
  | _ => 1
  end.

Definition rw_ri_fresh_trace_cost {K Sort V} (trace : audit_trace (rw_ri_fresh_call K Sort V)) :
    nat :=
  fold_right (fun event total => rw_ri_fresh_event_cost event + total) 0 trace.


Fixpoint rw_ri_max_entries_atomic {A K Sort V} (entries : list (positive * A)) (current :
    positive) :
    positive * audit_trace (rw_ri_fresh_call K Sort V) :=
  match entries with
  | nil => (current, [AuditCase 810 []])
  | (key, _) :: rest =>
    let next := Pos.max key current in
    let '(out, trace) := rw_ri_max_entries_atomic rest next in
    (out, [AuditCase 811 []; AuditCall (RIFreshMax key current next)] ++ trace)
  end.


Definition rw_ri_fresh_atomic {K Sort V} (g : rw_graph K Sort V) :
    positive * audit_trace (rw_ri_fresh_call K Sort V) :=
  let roots_map := rw_class_roots g in
  let '(roots, root_trace) := audit_map_elements roots_map in
  let nodes_map := rw_nodes g in
  let '(nodes, node_trace) := audit_map_elements nodes_map in
  let '(root_max, root_max_trace) := rw_ri_max_entries_atomic roots 1%positive in
  let '(all_max, node_max_trace) := rw_ri_max_entries_atomic nodes root_max in
  let '(fresh, succ_trace) := audit_positive_succ all_max in
  (fresh, [AuditCase 812 []; AuditCall (RIFreshRoots roots_map roots root_trace);
    AuditCase 813 []; AuditCall (RIFreshNodes nodes_map nodes node_trace)] ++
    root_max_trace ++ node_max_trace ++ [AuditCall (RIFreshSucc all_max fresh succ_trace)]).


Definition rw_ri_fresh_value {K Sort V} (g : rw_graph K Sort V) : positive :=
  let roots := Map.elements (rw_class_roots g) in
  let nodes := Map.elements (rw_nodes g) in
  let root_max := fold_left (fun acc entry => Pos.max (fst entry) acc) roots 1%positive in
  let all_max := fold_left (fun acc entry => Pos.max (fst entry) acc) nodes root_max in
  Pos.succ all_max.


Definition rw_index_build {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (g : rw_graph K Sort V) : rw_index_state K Sort V :=
  let empty := RwRiBuildAcc Map.empty Map.empty Map.empty in
  let buckets := rw_ri_build_nodes_value EK EV g (rw_nodes_in g) empty in
  let dirty := FinSet.of_list positive_encoding (rw_nodes_in g) in
  let fresh := rw_ri_fresh_value g in
  RWIndexState g UnionFind.make (rw_ri_build_parents buckets) Map.empty Map.empty
    (rw_nodes_in g) dirty rw_pending_empty (rw_ri_build_ops buckets) (rw_ri_build_vars buckets)
    fresh.
```

## Galois.Rewrite.RewriteAuditIndexTickReference

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditIndexTickReference.v`.

```rocq
(** * RewriteAuditIndexTickReference

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexBuild RewriteAuditIndexReference
  RewriteAuditQueueReference.
Import List.ListNotations.

Definition rw_ri_state_update {K Sort V} (s : rw_index_state K Sort V)
    (forest : UnionFind.t rw_id) (parents : Map.t rw_id (FinSet.t rw_id))
    (signatures : Map.t (rw_node K Sort V) (FinSet.t rw_id))
    (keys : Map.t rw_id (rw_node K Sort V)) (dirty_order : list rw_id)
    (dirty_set : FinSet.t rw_id) (pending : rw_pending_queue) : rw_index_state K Sort V :=
  RWIndexState (rw_index_base s) forest parents signatures keys dirty_order dirty_set pending
    (rw_index_operators s) (rw_index_variables s) (rw_index_fresh s).


Definition rw_ri_bucket_remove {A} (E : encoding A) (key : A) (id : rw_id)
    (table : Map.t A (FinSet.t rw_id)) : Map.t A (FinSet.t rw_id) :=
  match Map.get E key table with
  | None => table
  | Some bucket =>
    let updated := FinSet.remove positive_encoding id bucket in
    if FinSet.is_empty updated then Map.remove E key table else Map.set E key updated table
  end.


Fixpoint rw_ri_mark_dirty (ids : list rw_id) (order : list rw_id) (members : FinSet.t rw_id) :
    list rw_id * FinSet.t rw_id :=
  match ids with
  | nil => (order, members)
  | id :: rest =>
    if FinSet.mem positive_encoding id members then rw_ri_mark_dirty rest order members
    else rw_ri_mark_dirty rest (id :: order) (FinSet.add positive_encoding id members)
  end.


Definition rw_ri_dirty_tick {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (s : rw_index_state K Sort V) (id : rw_id) (rest : list rw_id) : rw_index_state K Sort V :=
  let EN := rw_node_encoding EK ES EV in
  let dirty := FinSet.remove positive_encoding id (rw_index_dirty_set s) in
  match rw_node_at (rw_index_base s) id with
  | None => rw_ri_state_update s (rw_index_forest s) (rw_index_parent_buckets s)
      (rw_index_signatures s) (rw_index_node_keys s) rest dirty (rw_index_pending s)
  | Some (_, node) =>
    let signatures := match Map.get positive_encoding id (rw_index_node_keys s) with
      | None => rw_index_signatures s
      | Some old => rw_ri_bucket_remove EN old id (rw_index_signatures s) end in
    let canonical := rw_index_canonical_node s node in
    let peers := FinSet.elements (rw_index_bucket EN canonical signatures) in
    let pending := rw_pending_prepend (map (fun other => (id, other)) peers) (rw_index_pending s) in
    let signatures' := rw_ri_bucket_add EN canonical id signatures in
    let keys' := Map.set positive_encoding id canonical (rw_index_node_keys s) in
    rw_ri_state_update s (rw_index_forest s) (rw_index_parent_buckets s)
      signatures' keys' rest dirty pending
  end.


Definition rw_ri_pair_tick {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (s : rw_index_state K Sort V) (pair : rw_pair) (remaining : rw_pending_queue) :
    rw_index_state K Sort V * rw_index_event :=
  let '(n, m) := pair in
  let dropped := rw_ri_state_update s (rw_index_forest s) (rw_index_parent_buckets s)
    (rw_index_signatures s) (rw_index_node_keys s) (rw_index_dirty_order s) (rw_index_dirty_set
    s) remaining in
  let base := rw_index_base s in
  let EN := rw_node_encoding EK ES EV in
  match rw_node_at base n, rw_node_at base m with
  | Some (a, node), Some (b, other) =>
    match rw_index_find s a, rw_index_find s b with
    | Some ra, Some rb =>
      if Pos.eq_dec (encode EN (rw_index_canonical_node s node))
          (encode EN (rw_index_canonical_node s other)) then
        if Pos.eq_dec ra rb then (dropped, RWIndexSkipped pair)
        else match rw_class_sort base a, rw_class_sort base b with
        | Some sa, Some sb =>
          if Pos.eq_dec (encode ES sa) (encode ES sb) then
            let forest := UnionFind.union positive_encoding ra rb (rw_index_forest s) in
            let root := fst (UnionFind.find positive_encoding ra forest) in
            let parent_table := rw_index_parent_buckets s in
            let left_parents := rw_index_bucket positive_encoding ra parent_table in
            let right_parents := rw_index_bucket positive_encoding rb parent_table in
            let merged := FinSet.union positive_encoding left_parents right_parents in
            let without := Map.remove positive_encoding rb (Map.remove positive_encoding ra
    parent_table) in
            let parents := if FinSet.is_empty merged then without else Map.set positive_encoding
    root merged without in
            let '(order, dirty) := rw_ri_mark_dirty (FinSet.elements merged)
              (rw_index_dirty_order s) (rw_index_dirty_set s) in
            (rw_ri_state_update s forest parents (rw_index_signatures s) (rw_index_node_keys s)
              order dirty remaining, RWIndexCongruence pair ra rb root)
          else (dropped, RWIndexSkipped pair)
        | _, _ => (dropped, RWIndexSkipped pair)
        end
      else (dropped, RWIndexSkipped pair)
    | _, _ => (dropped, RWIndexSkipped pair)
    end
  | _, _ => (dropped, RWIndexSkipped pair)
  end.


Definition rw_index_tick {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (s : rw_index_state K Sort V) : option (rw_index_state K Sort V * rw_index_event) :=
  match rw_index_dirty_order s with
  | id :: rest => Some (rw_ri_dirty_tick EK ES EV s id rest, RWIndexDirty id)
  | nil => match rw_pending_pop (rw_index_pending s) with
    | None => None
    | Some (pending_pair, remaining) => Some (rw_ri_pair_tick EK ES EV s pending_pair remaining)
    end
  end.


Definition rw_ri_rebuild_done {K Sort V} (state : rw_index_state K Sort V * list rw_index_event)
    : bool :=
  match rw_index_dirty_order (fst state), rw_pending_sequence (rw_index_pending (fst state)) with
  | nil, nil => true
  | _, _ => false
  end.


Definition rw_ri_rebuild_step {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (state : rw_index_state K Sort V * list rw_index_event) : rw_index_state K Sort V * list
    rw_index_event :=
  match rw_index_tick EK ES EV (fst state) with
  | None => state
  | Some (next, event) => (next, event :: snd state)
  end.


Definition rw_ri_rebuild_fuel {K Sort V} (s : rw_index_state K Sort V) : positive :=
  let nodes := length (rw_nodes_in (rw_index_base s)) in
  let roots := length (rw_roots (rw_index_graph s)) in
  let pending := length (rw_pending_sequence (rw_index_pending s)) in
  Pos.of_succ_nat (pending + (S roots) * (S nodes) * (S nodes) + length (rw_index_dirty_order s)).


Definition rw_index_rebuild {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (s : rw_index_state K Sort V) : rw_index_state K Sort V * list rw_index_event :=
  let '(out, reversed) := rw_repeat rw_ri_rebuild_done (rw_ri_rebuild_step EK ES EV)
    (rw_ri_rebuild_fuel s) (s, nil) in
  (out, rev reversed).
```

## Galois.Rewrite.RewriteAuditIndexFind

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditIndexFind.v`.

```rocq
(** * RewriteAuditIndexFind

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexReference.
Import List.ListNotations.

Inductive rw_ri_find_call : Type :=
  | RIFindBase : rw_id -> Map.t rw_id rw_id -> option rw_id ->
      audit_trace (audit_trie_call (rw_id * rw_id)) -> rw_ri_find_call
  | RIFindForest : rw_id -> UnionFind.t rw_id -> (rw_id * UnionFind.t rw_id) ->
      list (audit_uf_event rw_id (audit_basic_encoding_event positive)) -> rw_ri_find_call.


Definition rw_ri_find_event_cost (event : audit_event rw_ri_find_call) : nat :=
  match event with
  | AuditCall (RIFindBase _ _ _ trace) => 2 + audit_trie_get_trace_source_work trace
  | AuditCall (RIFindForest _ _ _ trace) => 1 + audit_uf_source_work audit_basic_encoding_work trace
  | _ => 1
  end.

Definition rw_ri_find_trace_cost (trace : audit_trace rw_ri_find_call) : nat :=
  fold_right (fun event total => rw_ri_find_event_cost event + total) 0 trace.


Definition rw_ri_find_atomic {K Sort V} (state : rw_index_state K Sort V) (id : rw_id) :
    option rw_id * audit_trace rw_ri_find_call :=
  let parents := rw_class_roots (rw_index_base state) in
  let '(base_root, base_trace) := audit_map_code_get id parents in
  match base_root with
  | None => (None, [AuditCase 820 []; AuditCall (RIFindBase id parents None base_trace);
      AuditCase 821 []; AuditConstruct 822 []])
  | Some root =>
    let forest := rw_index_forest state in
    let '(found, find_trace) := audit_uf_find audit_positive_encode root forest in
    (Some (fst found), [AuditCase 820 []; AuditCall (RIFindBase id parents (Some root) base_trace);
      AuditCase 823 []; AuditCall (RIFindForest root forest found find_trace); AuditConstruct 824
    []])
  end.


Fixpoint rw_ri_find_fuel_budget (fuel : nat) (id : rw_id) (forest : UnionFind.t rw_id) : nat :=
  match fuel with
  | 0 => 16
  | S rest => 64 + 32 * Pos.size_nat id +
    match Map.get positive_encoding id (UnionFind.parents forest) with
    | None => 0
    | Some next => rw_ri_find_fuel_budget rest next forest
    end
  end.


Definition rw_ri_find_budget {K Sort V} (state : rw_index_state K Sort V) (id : rw_id) : nat :=
  10 + 5 * Pos.size_nat id +
  match rw_find (rw_index_base state) id with
  | None => 0
  | Some root => rw_ri_find_fuel_budget (S (UnionFind.max_rank (rw_index_forest state)))
      root (rw_index_forest state)
  end.


Inductive rw_ri_canon_call : Type :=
  | RICanonFind : rw_id -> option rw_id -> audit_trace rw_ri_find_call -> rw_ri_canon_call.


Definition rw_ri_canon_event_cost (event : audit_event rw_ri_canon_call) : nat :=
  match event with AuditCall (RICanonFind _ _ trace) => 1 + rw_ri_find_trace_cost trace | _ => 1
    end.

Definition rw_ri_canon_trace_cost (trace : audit_trace rw_ri_canon_call) : nat :=
  fold_right (fun event total => rw_ri_canon_event_cost event + total) 0 trace.


Fixpoint rw_ri_canon_children {K Sort V} (state : rw_index_state K Sort V) (ids : list rw_id) :
    list rw_id * audit_trace rw_ri_canon_call :=
  match ids with
  | nil => (nil, [AuditCase 825 []; AuditConstruct 826 []])
  | id :: rest =>
    let '(found, find_trace) := rw_ri_find_atomic state id in
    let current := match found with Some root => root | None => id end in
    let '(tail, trace) := rw_ri_canon_children state rest in
    (current :: tail, [AuditCase 827 []; AuditCall (RICanonFind id found find_trace);
      AuditCase 828 []] ++ trace ++ [AuditConstruct 829 []])
  end.


Definition rw_ri_canon_atomic {K Sort V} (state : rw_index_state K Sort V) (node : rw_node K Sort
    V) :
    rw_node K Sort V * audit_trace rw_ri_canon_call :=
  match node with
  | RWNVar s v => (RWNVar s v, [AuditCase 830 []; AuditConstruct 831 []])
  | RWNApp s op children =>
    let '(ids, trace) := rw_ri_canon_children state children in
    (RWNApp s op ids, [AuditCase 832 []] ++ trace ++ [AuditConstruct 833 []])
  end.


Fixpoint rw_ri_canon_children_budget {K Sort V} (state : rw_index_state K Sort V) (ids : list
    rw_id) : nat :=
  match ids with nil => 2 | id :: rest => 4 + rw_ri_find_budget state id +
    rw_ri_canon_children_budget state rest end.

Definition rw_ri_canon_budget {K Sort V} (state : rw_index_state K Sort V) (node : rw_node K Sort
    V) : nat :=
  match node with RWNVar _ _ => 2 | RWNApp _ _ ids => 2 + rw_ri_canon_children_budget state ids end.


(** This statement fixes the ri find erases contract. *)
Definition rw_ri_find_erases_contract : Prop := forall K Sort V (state : rw_index_state K Sort V)
    id,
  fst (rw_ri_find_atomic state id) = rw_index_find state id.

(** This statement fixes the ri find bound contract. *)
Definition rw_ri_find_bound_contract : Prop := forall K Sort V (state : rw_index_state K Sort V) id,
  rw_ri_find_trace_cost (snd (rw_ri_find_atomic state id)) <= rw_ri_find_budget state id.

(** This statement fixes the ri canon erases contract. *)
Definition rw_ri_canon_erases_contract : Prop := forall K Sort V (state : rw_index_state K Sort
    V) node,
  fst (rw_ri_canon_atomic state node) = rw_index_canonical_node state node.

(** This statement fixes the ri canon bound contract. *)
Definition rw_ri_canon_bound_contract : Prop := forall K Sort V (state : rw_index_state K Sort V)
    node,
  rw_ri_canon_trace_cost (snd (rw_ri_canon_atomic state node)) <= rw_ri_canon_budget state node.
```

## Galois.Rewrite.RewriteAuditIndexBucket

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditIndexBucket.v`.

```rocq
(** * RewriteAuditIndexBucket

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexBuild RewriteAuditIndexTickReference.
Import List.ListNotations.

Inductive rw_ri_bucket_call (A CE : Type) : Type :=
  | RIBucketRead : list (audit_map_event A (FinSet.t rw_id) CE) -> rw_ri_bucket_call A CE
  | RIBucketMember : list (audit_set_event rw_id (audit_basic_encoding_event positive)) ->
    rw_ri_bucket_call A CE
  | RIBucketWrite : list (audit_map_event A (FinSet.t rw_id) CE) -> rw_ri_bucket_call A CE.
Arguments RIBucketRead {A CE}.
Arguments RIBucketMember {A CE}.
Arguments RIBucketWrite {A CE}.


Definition rw_ri_bucket_event_cost {A CE} (enc_work : list CE -> nat)
    (event : audit_event (rw_ri_bucket_call A CE)) : nat :=
  match event with
  | AuditCall (RIBucketRead trace) => 1 + audit_map_source_work enc_work trace
  | AuditCall (RIBucketMember trace) => 1 + audit_finset_source_work audit_basic_encoding_work trace
  | AuditCall (RIBucketWrite trace) => 1 + audit_map_source_work enc_work trace
  | _ => 1
  end.

Definition rw_ri_bucket_trace_cost {A CE} (enc_work : list CE -> nat)
    (trace : audit_trace (rw_ri_bucket_call A CE)) : nat :=
  fold_right (fun event total => rw_ri_bucket_event_cost enc_work event + total) 0 trace.


Definition rw_ri_bucket_add_atomic {A CE} (enc : A -> positive * list CE) (key : A) (id : rw_id)
    (table : Map.t A (FinSet.t rw_id)) : Map.t A (FinSet.t rw_id) * audit_trace
    (rw_ri_bucket_call A CE) :=
  let '(found, read_trace) := audit_map_get enc key table in
  let bucket := match found with Some stored => stored | None => FinSet.empty end in
  let '(updated, member_trace) := audit_finset_add audit_positive_encode id bucket in
  let '(out, write_trace) := audit_map_set enc key updated table in
  (out, [AuditCall (RIBucketRead read_trace); AuditCase 834 [];
    AuditCall (RIBucketMember member_trace); AuditCall (RIBucketWrite write_trace)]).


Definition rw_ri_bucket_remove_atomic {A CE} (enc : A -> positive * list CE) (key : A) (id : rw_id)
    (table : Map.t A (FinSet.t rw_id)) : Map.t A (FinSet.t rw_id) * audit_trace
    (rw_ri_bucket_call A CE) :=
  let '(found, read_trace) := audit_map_get enc key table in
  match found with
  | None => (table, [AuditCall (RIBucketRead read_trace); AuditCase 835 []])
  | Some bucket =>
    let '(updated, member_trace) := audit_finset_remove audit_positive_encode id bucket in
    if FinSet.is_empty updated then
      let '(out, write_trace) := audit_map_remove enc key table in
      (out, [AuditCall (RIBucketRead read_trace); AuditCase 836 [];
        AuditCall (RIBucketMember member_trace); AuditCase 837 []; AuditCall (RIBucketWrite
    write_trace)])
    else
      let '(out, write_trace) := audit_map_set enc key updated table in
      (out, [AuditCall (RIBucketRead read_trace); AuditCase 836 [];
        AuditCall (RIBucketMember member_trace); AuditCase 838 []; AuditCall (RIBucketWrite
    write_trace)])
  end.


Definition rw_ri_bucket_atomic_budget {A CE} (enc : A -> positive * list CE)
    (enc_work : list CE -> nat) (key : A) (id : rw_id) : nat :=
  let '(code, trace) := enc key in
  50 + 2 * enc_work trace + 32 * Pos.size_nat code + 16 * Pos.size_nat id.


(** This statement fixes the ri bucket add erases contract. *)
Definition rw_ri_bucket_add_erases_contract : Prop := forall A CE (E : encoding A) (enc : A ->
    positive * list CE) key id table,
  fst (enc key) = encode E key -> fst (rw_ri_bucket_add_atomic enc key id table) =
    rw_ri_bucket_add E key id table.

(** This statement fixes the ri bucket remove erases contract. *)
Definition rw_ri_bucket_remove_erases_contract : Prop := forall A CE (E : encoding A) (enc : A ->
    positive * list CE) key id table,
  fst (enc key) = encode E key -> fst (rw_ri_bucket_remove_atomic enc key id table) =
    rw_ri_bucket_remove E key id table.

(** This statement fixes the ri bucket add bound contract. *)
Definition rw_ri_bucket_add_bound_contract : Prop := forall A CE (enc : A -> positive * list CE)
    enc_work key id table,
  rw_ri_bucket_trace_cost enc_work (snd (rw_ri_bucket_add_atomic enc key id table)) <=
    rw_ri_bucket_atomic_budget enc enc_work key id.

(** This statement fixes the ri bucket remove bound contract. *)
Definition rw_ri_bucket_remove_bound_contract : Prop := forall A CE (enc : A -> positive * list
    CE) enc_work key id table,
  rw_ri_bucket_trace_cost enc_work (snd (rw_ri_bucket_remove_atomic enc key id table)) <=
    rw_ri_bucket_atomic_budget enc enc_work key id.
```

## Galois.Rewrite.RewriteAuditIndexDirty

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditIndexDirty.v`.

```rocq
(** * RewriteAuditIndexDirty

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexBucket RewriteAuditIndexFind
  RewriteAuditIndexReference RewriteAuditIndexTickReference RewriteAuditQueueReference.
Import List.ListNotations.

Definition rw_ri_node_event (K Sort V : Type) :=
  audit_sum_event (Sort * V) (Sort * (K * list rw_id))
    (audit_pair_event Sort V nat nat)
    (audit_pair_event Sort (K * list rw_id) nat
      (audit_pair_event K (list rw_id) nat (audit_list_event rw_id (audit_basic_encoding_event
    positive)))).


Definition rw_ri_node_encoder {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (node : rw_node K Sort V) : positive * list (rw_ri_node_event K Sort V) :=
  rw_node_encode_atomic (rw_external_encoding_events op) (rw_external_encoding_events sort)
    (rw_external_encoding_events value) node.


Definition rw_ri_node_encoding_work {K Sort V} (trace : list (rw_ri_node_event K Sort V)) : nat :=
  rw_node_encode_trace_cost rw_external_events_work rw_external_events_work
    rw_external_events_work trace.


Inductive rw_ri_dirty_call (K Sort V : Type) : Type :=
  | RIDirtySet : list (audit_set_event rw_id (audit_basic_encoding_event positive)) ->
    rw_ri_dirty_call K Sort V
  | RIDirtyNode : list (audit_map_event rw_id (rw_id * rw_node K Sort V)
    (audit_basic_encoding_event positive)) ->
      rw_ri_dirty_call K Sort V
  | RIDirtyOldKey : list (audit_map_event rw_id (rw_node K Sort V) (audit_basic_encoding_event
    positive)) ->
      rw_ri_dirty_call K Sort V
  | RIDirtyBucket : list (audit_event (rw_ri_bucket_call (rw_node K Sort V) (rw_ri_node_event K
    Sort V))) ->
      rw_ri_dirty_call K Sort V
  | RIDirtyCanon : rw_node K Sort V -> rw_node K Sort V -> audit_trace rw_ri_canon_call ->
    rw_ri_dirty_call K Sort V
  | RIDirtySignature : list (audit_map_event (rw_node K Sort V) (FinSet.t rw_id)
    (rw_ri_node_event K Sort V)) ->
      rw_ri_dirty_call K Sort V
  | RIDirtyPeers : list (audit_set_elements_event rw_id) -> rw_ri_dirty_call K Sort V
  | RIDirtyPairs : list rw_id -> list rw_pair -> audit_trace unit -> rw_ri_dirty_call K Sort V
  | RIDirtyPending : rw_pending_queue -> audit_trace rw_queue_insert_call -> rw_ri_dirty_call K
    Sort V
  | RIDirtyKeySet : list (audit_map_event rw_id (rw_node K Sort V) (audit_basic_encoding_event
    positive)) ->
      rw_ri_dirty_call K Sort V.
Arguments RIDirtySet {K Sort V}.
Arguments RIDirtyNode {K Sort V}.
Arguments RIDirtyOldKey {K Sort V}.
Arguments RIDirtyBucket {K Sort V}.
Arguments RIDirtyCanon {K Sort V}.
Arguments RIDirtySignature {K Sort V}.
Arguments RIDirtyPeers {K Sort V}.
Arguments RIDirtyPairs {K Sort V}.
Arguments RIDirtyPending {K Sort V}.
Arguments RIDirtyKeySet {K Sort V}.


Definition rw_ri_dirty_event_cost {K Sort V} (event : audit_event (rw_ri_dirty_call K Sort V)) :
    nat :=
  match event with
  | AuditCall (RIDirtySet trace) => 1 + audit_finset_source_work audit_basic_encoding_work trace
  | AuditCall (RIDirtyNode trace) => 1 + audit_map_source_work audit_basic_encoding_work trace
  | AuditCall (RIDirtyOldKey trace) => 1 + audit_map_source_work audit_basic_encoding_work trace
  | AuditCall (RIDirtyBucket trace) => 1 + rw_ri_bucket_trace_cost rw_ri_node_encoding_work trace
  | AuditCall (RIDirtyCanon _ _ trace) => 1 + rw_ri_canon_trace_cost trace
  | AuditCall (RIDirtySignature trace) => 1 + audit_map_source_work rw_ri_node_encoding_work trace
  | AuditCall (RIDirtyPeers trace) => 1 + audit_set_elements_work trace
  | AuditCall (RIDirtyPairs _ _ trace) => 1 + audit_work trace
  | AuditCall (RIDirtyPending _ trace) => 1 + rw_queue_insert_expanded_work trace
  | AuditCall (RIDirtyKeySet trace) => 1 + audit_map_source_work audit_basic_encoding_work trace
  | _ => 1
  end.

Definition rw_ri_dirty_trace_cost {K Sort V} (trace : audit_trace (rw_ri_dirty_call K Sort V)) :
    nat :=
  fold_right (fun event total => rw_ri_dirty_event_cost event + total) 0 trace.


Fixpoint rw_ri_peer_pairs_atomic (id : rw_id) (peers : list rw_id) : list rw_pair * audit_trace
    unit :=
  match peers with
  | nil => (nil, [AuditCase 840 []; AuditConstruct 841 []])
  | peer :: rest =>
    let pair_value := (id, peer) in
    let '(tail, trace) := rw_ri_peer_pairs_atomic id rest in
    (pair_value :: tail, [AuditCase 842 []; AuditConstruct 843 []] ++ trace ++ [AuditConstruct
    844 []])
  end.


Definition rw_ri_dirty_tick_atomic {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (s : rw_index_state K Sort V) (id : rw_id) (rest : list rw_id) :
    rw_index_state K Sort V * audit_trace (rw_ri_dirty_call K Sort V) :=
  let node_enc := rw_ri_node_encoder op sort value in
  let '(dirty, dirty_trace) := audit_finset_remove audit_positive_encode id (rw_index_dirty_set
    s) in
  let '(found, node_trace) := audit_map_get audit_positive_encode id (rw_nodes (rw_index_base s)) in
  let prefix := [AuditCall (RIDirtySet dirty_trace); AuditCall (RIDirtyNode node_trace)] in
  match found with
  | None =>
    (rw_ri_state_update s (rw_index_forest s) (rw_index_parent_buckets s)
      (rw_index_signatures s) (rw_index_node_keys s) rest dirty (rw_index_pending s),
      prefix ++ [AuditCase 845 []; AuditConstruct 846 []])
  | Some (_, node) =>
    let '(old, old_trace) := audit_map_get audit_positive_encode id (rw_index_node_keys s) in
    let '(signatures, remove_events) := match old with
      | None => (rw_index_signatures s, [AuditCase 849 []])
      | Some key => let '(out, trace) := rw_ri_bucket_remove_atomic node_enc key id
    (rw_index_signatures s) in
        (out, [AuditCase 850 []; AuditCall (RIDirtyBucket trace)])
      end in
    let '(canonical, canon_trace) := rw_ri_canon_atomic s node in
    let '(found_peers, sig_trace) := audit_map_get node_enc canonical signatures in
    let bucket := match found_peers with Some b => b | None => FinSet.empty end in
    let '(peers, peers_trace) := audit_finset_elements bucket in
    let '(pairs, pairs_trace) := rw_ri_peer_pairs_atomic id peers in
    let '(pending, pending_trace) := rw_queue_prepend_atomic pairs (rw_index_pending s) in
    let '(signatures', add_trace) := rw_ri_bucket_add_atomic node_enc canonical id signatures in
    let '(keys', key_trace) := audit_map_set audit_positive_encode id canonical
    (rw_index_node_keys s) in
    (rw_ri_state_update s (rw_index_forest s) (rw_index_parent_buckets s) signatures' keys' rest
    dirty pending,
      prefix ++ [AuditCase 847 []; AuditCall (RIDirtyOldKey old_trace)] ++ remove_events ++
      [
        AuditCall (RIDirtyCanon node canonical canon_trace); AuditCall (RIDirtySignature sig_trace);
        AuditCall (RIDirtyPeers peers_trace); AuditCall (RIDirtyPairs peers pairs pairs_trace);
        AuditCall (RIDirtyPending pending pending_trace); AuditCall (RIDirtyBucket add_trace);
        AuditCall (RIDirtyKeySet key_trace); AuditConstruct 848 []])
  end.


Definition rw_ri_dirty_tick_budget {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV :
    encoding V)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (s : rw_index_state K Sort V) (id : rw_id) : nat :=
  let EN := rw_node_encoding EK ES EV in
  let node_enc := rw_ri_node_encoder op sort value in
  100 + 64 * Pos.size_nat id +
  match rw_node_at (rw_index_base s) id with
  | None => 0
  | Some (_, node) =>
    let old := Map.get positive_encoding id (rw_index_node_keys s) in
    let signatures := match old with
      | None => rw_index_signatures s
      | Some key => rw_ri_bucket_remove EN key id (rw_index_signatures s) end in
    let canonical := rw_index_canonical_node s node in
    let peers_bucket := rw_index_bucket EN canonical signatures in
    let peers := FinSet.elements peers_bucket in
    let pairs := map (fun other => (id, other)) peers in
    (match old with None => 0 | Some key =>
      rw_ri_bucket_atomic_budget node_enc rw_ri_node_encoding_work key id end) +
    rw_ri_canon_budget s node +
    2 * rw_ri_bucket_atomic_budget node_enc rw_ri_node_encoding_work canonical id +
    19 * audit_trie_nodes peers_bucket + audit_trie_output_bits peers_bucket + 6 +
    2 + 3 * length peers + rw_queue_prepend_expanded_budget pairs
  end.


(** This statement fixes the ri dirty client statement contract. *)
Definition rw_ri_dirty_client_statement : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (op_execution : K -> positive -> nat -> Prop)
    (sort_execution : Sort -> positive -> nat -> Prop) (value_execution : V -> positive -> nat ->
    Prop)
    (s : rw_index_state K Sort V) id rest,
  rw_queue_encoder_adapter_laws EK op_execution op ->
  rw_queue_encoder_adapter_laws ES sort_execution sort ->
  rw_queue_encoder_adapter_laws EV value_execution value ->
  let '(out, trace) := rw_ri_dirty_tick_atomic op sort value s id rest in
  out = rw_ri_dirty_tick EK ES EV s id rest /\
  rw_ri_dirty_trace_cost trace <= rw_ri_dirty_tick_budget EK ES EV op sort value s id.

(** This statement fixes the ri dirty client contract. *)
Definition rw_ri_dirty_client_contract : Prop := rw_ri_dirty_client_statement.
```

## Galois.Rewrite.RewriteAuditIndexMark

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditIndexMark.v`.

```rocq
(** * RewriteAuditIndexMark

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexTickReference.
Import List.ListNotations.

Inductive rw_ri_mark_call : Type :=
  | RIMarkMem : rw_id -> bool -> list (audit_set_event rw_id (audit_basic_encoding_event
    positive)) -> rw_ri_mark_call
  | RIMarkAdd : rw_id -> FinSet.t rw_id ->
      list (audit_set_event rw_id (audit_basic_encoding_event positive)) -> rw_ri_mark_call.


Definition rw_ri_mark_event_cost (event : audit_event rw_ri_mark_call) : nat :=
  match event with
  | AuditCall (RIMarkMem _ _ trace) => 1 + audit_finset_source_work audit_basic_encoding_work trace
  | AuditCall (RIMarkAdd _ _ trace) => 1 + audit_finset_source_work audit_basic_encoding_work trace
  | _ => 1
  end.

Definition rw_ri_mark_trace_cost (trace : audit_trace rw_ri_mark_call) : nat :=
  fold_right (fun event total => rw_ri_mark_event_cost event + total) 0 trace.


Fixpoint rw_ri_mark_dirty_atomic (ids : list rw_id) (order : list rw_id) (members : FinSet.t
    rw_id) :
    (list rw_id * FinSet.t rw_id) * audit_trace rw_ri_mark_call :=
  match ids with
  | nil => ((order, members), [AuditCase 860 []; AuditConstruct 861 []])
  | id :: rest =>
    let '(present, mem_trace) := audit_finset_mem audit_positive_encode id members in
    if present then
      let '(out, trace) := rw_ri_mark_dirty_atomic rest order members in
      (out, [AuditCase 862 []; AuditCall (RIMarkMem id present mem_trace); AuditCase 863 []] ++
    trace)
    else
      let '(updated, add_trace) := audit_finset_add audit_positive_encode id members in
      let '(out, trace) := rw_ri_mark_dirty_atomic rest (id :: order) updated in
      (out, [AuditCase 862 []; AuditCall (RIMarkMem id present mem_trace); AuditCase 864 [];
        AuditCall (RIMarkAdd id updated add_trace); AuditConstruct 865 []] ++ trace)
  end.


Fixpoint rw_ri_mark_budget (ids : list rw_id) : nat :=
  match ids with nil => 2 | id :: rest => 24 + 24 * Pos.size_nat id + rw_ri_mark_budget rest end.


(** This statement fixes the ri mark erases contract. *)
Definition rw_ri_mark_erases_contract : Prop := forall ids order members,
  fst (rw_ri_mark_dirty_atomic ids order members) = rw_ri_mark_dirty ids order members.

(** This statement fixes the ri mark bound contract. *)
Definition rw_ri_mark_bound_contract : Prop := forall ids order members,
  rw_ri_mark_trace_cost (snd (rw_ri_mark_dirty_atomic ids order members)) <= rw_ri_mark_budget ids.
```

## Galois.Rewrite.RewriteAuditIndexCompare

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditIndexCompare.v`.

```rocq
(** * RewriteAuditIndexCompare

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditQueuePositive.
Import List.ListNotations.

Inductive rw_ri_positive_call : Type :=
  | RIPositiveDecision : positive -> positive -> bool -> rw_ri_positive_call
  | RIPositiveFrame : rw_rq_decision_frame -> rw_ri_positive_call.


Definition rw_ri_positive_dec_atomic (a b : positive) : bool * audit_trace rw_ri_positive_call :=
  let '(answer, frames) := rw_rq_decision_atomic a b in
  (answer, AuditCall (RIPositiveDecision a b answer) ::
    map (fun frame => AuditCall (RIPositiveFrame frame)) frames).


Definition rw_ri_positive_dec_budget (a : positive) : nat := 8 * Pos.size_nat a.

(** This statement fixes the ri positive dec erases contract. *)
Definition rw_ri_positive_dec_erases_contract : Prop := forall a b,
  fst (rw_ri_positive_dec_atomic a b) = if Pos.eq_dec a b then true else false.

(** This statement fixes the ri positive dec bound contract. *)
Definition rw_ri_positive_dec_bound_contract : Prop := forall a b,
  audit_work (snd (rw_ri_positive_dec_atomic a b)) <= rw_ri_positive_dec_budget a.
```

## Galois.Rewrite.RewriteAuditIndexPair

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditIndexPair.v`.

```rocq
(** * RewriteAuditIndexPair

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexCompare RewriteAuditIndexDirty
  RewriteAuditIndexFind RewriteAuditIndexMark RewriteAuditIndexReference
  RewriteAuditIndexTickReference RewriteAuditQueueReference.
Import List.ListNotations.

Inductive rw_ri_pair_call (K Sort V : Type) : Type :=
  | RIPairNode : list (audit_map_event rw_id (rw_id * rw_node K Sort V)
    (audit_basic_encoding_event positive)) ->
      rw_ri_pair_call K Sort V
  | RIPairFind : rw_id -> option rw_id -> audit_trace rw_ri_find_call -> rw_ri_pair_call K Sort V
  | RIPairCanon : rw_node K Sort V -> rw_node K Sort V -> audit_trace rw_ri_canon_call ->
    rw_ri_pair_call K Sort V
  | RIPairNodeCode : rw_node K Sort V -> positive -> list (rw_ri_node_event K Sort V) ->
    rw_ri_pair_call K Sort V
  | RIPairDecision : positive -> positive -> bool -> audit_trace rw_ri_positive_call ->
    rw_ri_pair_call K Sort V
  | RIPairSort : list (audit_map_event rw_id Sort (audit_basic_encoding_event positive)) ->
    rw_ri_pair_call K Sort V
  | RIPairSortCode : Sort -> positive -> list nat -> rw_ri_pair_call K Sort V
  | RIPairUnion : list (audit_uf_event rw_id (audit_basic_encoding_event positive)) ->
    rw_ri_pair_call K Sort V
  | RIPairForestFind : list (audit_uf_event rw_id (audit_basic_encoding_event positive)) ->
    rw_ri_pair_call K Sort V
  | RIPairParentMap : list (audit_map_event rw_id (FinSet.t rw_id) (audit_basic_encoding_event
    positive)) ->
      rw_ri_pair_call K Sort V
  | RIPairSetUnion : list (audit_union_event rw_id) -> rw_ri_pair_call K Sort V
  | RIPairParentElements : list (audit_set_elements_event rw_id) -> rw_ri_pair_call K Sort V
  | RIPairMark : audit_trace rw_ri_mark_call -> rw_ri_pair_call K Sort V.
Arguments RIPairNode {K Sort V}.
Arguments RIPairFind {K Sort V}.
Arguments RIPairCanon {K Sort V}.
Arguments RIPairNodeCode {K Sort V}.
Arguments RIPairDecision {K Sort V}.
Arguments RIPairSort {K Sort V}.
Arguments RIPairSortCode {K Sort V}.
Arguments RIPairUnion {K Sort V}.
Arguments RIPairForestFind {K Sort V}.
Arguments RIPairParentMap {K Sort V}.
Arguments RIPairSetUnion {K Sort V}.
Arguments RIPairParentElements {K Sort V}.
Arguments RIPairMark {K Sort V}.


Definition rw_ri_pair_event_cost {K Sort V} (event : audit_event (rw_ri_pair_call K Sort V)) :
    nat :=
  match event with
  | AuditCall (RIPairNode trace) => 1 + audit_map_source_work audit_basic_encoding_work trace
  | AuditCall (RIPairFind _ _ trace) => 1 + rw_ri_find_trace_cost trace
  | AuditCall (RIPairCanon _ _ trace) => 1 + rw_ri_canon_trace_cost trace
  | AuditCall (RIPairNodeCode _ _ trace) => 1 + rw_ri_node_encoding_work trace
  | AuditCall (RIPairDecision _ _ _ trace) => 64 + 64 * audit_work trace
  | AuditCall (RIPairSort trace) => 1 + audit_map_source_work audit_basic_encoding_work trace
  | AuditCall (RIPairSortCode _ _ trace) => 1 + rw_external_events_work trace
  | AuditCall (RIPairUnion trace) => 1 + audit_uf_source_work audit_basic_encoding_work trace
  | AuditCall (RIPairForestFind trace) => 1 + audit_uf_source_work audit_basic_encoding_work trace
  | AuditCall (RIPairParentMap trace) => 1 + audit_map_source_work audit_basic_encoding_work trace
  | AuditCall (RIPairSetUnion trace) => 1 + audit_finset_union_source_work trace
  | AuditCall (RIPairParentElements trace) => 1 + audit_set_elements_work trace
  | AuditCall (RIPairMark trace) => 1 + rw_ri_mark_trace_cost trace
  | _ => 1
  end.

Definition rw_ri_pair_trace_cost {K Sort V} (trace : audit_trace (rw_ri_pair_call K Sort V)) :
    nat :=
  fold_right (fun event total => rw_ri_pair_event_cost event + total) 0 trace.


Definition rw_ri_pair_skip {K Sort V} (dropped : rw_index_state K Sort V) (p : rw_pair)
    (prefix : audit_trace (rw_ri_pair_call K Sort V)) :
    (rw_index_state K Sort V * rw_index_event) * audit_trace (rw_ri_pair_call K Sort V) :=
  ((dropped, RWIndexSkipped p), prefix ++ [AuditCase 890 []; AuditConstruct 891 [];
    AuditConstruct 892 []]).


Definition rw_ri_pair_merge_atomic {K Sort V} (s dropped : rw_index_state K Sort V)
    (p : rw_pair) (remaining : rw_pending_queue) (ra rb : rw_id)
    (prefix : audit_trace (rw_ri_pair_call K Sort V)) :
    (rw_index_state K Sort V * rw_index_event) * audit_trace (rw_ri_pair_call K Sort V) :=
  let '(forest, union_trace) := audit_uf_union audit_positive_encode ra rb (rw_index_forest s) in
  let '(found_root, root_trace) := audit_uf_find audit_positive_encode ra forest in
  let root := fst found_root in
  let parent_table := rw_index_parent_buckets s in
  let '(left_found, left_trace) := audit_map_get audit_positive_encode ra parent_table in
  let '(right_found, right_trace) := audit_map_get audit_positive_encode rb parent_table in
  let left_bucket := match left_found with Some b => b | None => FinSet.empty end in
  let right_bucket := match right_found with Some b => b | None => FinSet.empty end in
  let '(merged, union_set_trace) := audit_finset_union left_bucket right_bucket in
  let '(removed_a, remove_a_trace) := audit_map_remove audit_positive_encode ra parent_table in
  let '(without, remove_b_trace) := audit_map_remove audit_positive_encode rb removed_a in
  let '(parents, write_events) :=
    if FinSet.is_empty merged then (without, [AuditCase 893 []])
    else let '(updated, write_trace) := audit_map_set audit_positive_encode root merged without in
      (updated, [AuditCase 894 []; AuditCall (RIPairParentMap write_trace)]) in
  let '(ids, elements_trace) := audit_finset_elements merged in
  let '((order, dirty), mark_trace) := rw_ri_mark_dirty_atomic ids (rw_index_dirty_order s)
    (rw_index_dirty_set s) in
  let next := rw_ri_state_update s forest parents (rw_index_signatures s) (rw_index_node_keys s)
    order dirty remaining in
  ((next, RWIndexCongruence p ra rb root), prefix ++
    [AuditCall (RIPairUnion union_trace); AuditCall (RIPairForestFind root_trace);
     AuditCall (RIPairParentMap left_trace); AuditCall (RIPairParentMap right_trace);
     AuditCall (RIPairSetUnion union_set_trace); AuditCall (RIPairParentMap remove_a_trace);
     AuditCall (RIPairParentMap remove_b_trace)] ++ write_events ++
    [AuditCall (RIPairParentElements elements_trace); AuditCall (RIPairMark mark_trace);
     AuditConstruct 895 []; AuditConstruct 896 []; AuditConstruct 897 []]).


Definition rw_ri_pair_atomic {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (s : rw_index_state K Sort V) (p : rw_pair) (remaining : rw_pending_queue) :
    (rw_index_state K Sort V * rw_index_event) * audit_trace (rw_ri_pair_call K Sort V) :=
  let '(n, m) := p in
  let dropped := rw_ri_state_update s (rw_index_forest s) (rw_index_parent_buckets s)
    (rw_index_signatures s) (rw_index_node_keys s) (rw_index_dirty_order s) (rw_index_dirty_set
    s) remaining in
  let base := rw_index_base s in
  let node_enc := rw_ri_node_encoder op sort value in
  let '(first, first_trace) := audit_map_get audit_positive_encode n (rw_nodes base) in
  let prefix := [AuditConstruct 898 []; AuditCall (RIPairNode first_trace)] in
  match first with
  | None => rw_ri_pair_skip dropped p (prefix ++ [AuditCase 899 []])
  | Some (a, node) =>
    let '(second, second_trace) := audit_map_get audit_positive_encode m (rw_nodes base) in
    let prefix := prefix ++ [AuditCase 900 []; AuditCall (RIPairNode second_trace)] in
    match second with
    | None => rw_ri_pair_skip dropped p (prefix ++ [AuditCase 901 []])
    | Some (b, other) =>
      let '(first_root, first_root_trace) := rw_ri_find_atomic s a in
      let prefix := prefix ++ [AuditCase 902 []; AuditCall (RIPairFind a first_root
    first_root_trace)] in
      match first_root with
      | None => rw_ri_pair_skip dropped p (prefix ++ [AuditCase 903 []])
      | Some ra =>
        let '(second_root, second_root_trace) := rw_ri_find_atomic s b in
        let prefix := prefix ++ [AuditCase 904 []; AuditCall (RIPairFind b second_root
    second_root_trace)] in
        match second_root with
        | None => rw_ri_pair_skip dropped p (prefix ++ [AuditCase 905 []])
        | Some rb =>
          let '(ca, ca_trace) := rw_ri_canon_atomic s node in
          let '(code_a, code_a_trace) := node_enc ca in
          let '(cb, cb_trace) := rw_ri_canon_atomic s other in
          let '(code_b, code_b_trace) := node_enc cb in
          let '(same_code, code_compare_trace) := rw_ri_positive_dec_atomic code_a code_b in
          let prefix := prefix ++ [AuditCase 906 []; AuditCall (RIPairCanon node ca ca_trace);
            AuditCall (RIPairNodeCode ca code_a code_a_trace); AuditCall (RIPairCanon other cb
    cb_trace);
            AuditCall (RIPairNodeCode cb code_b code_b_trace);
            AuditCall (RIPairDecision code_a code_b same_code code_compare_trace)] in
          if same_code then
            let '(same_root, root_compare_trace) := rw_ri_positive_dec_atomic ra rb in
            let prefix := prefix ++ [AuditCase 907 []; AuditCall (RIPairDecision ra rb same_root
    root_compare_trace)] in
            if same_root then rw_ri_pair_skip dropped p (prefix ++ [AuditCase 908 []])
            else
              let '(first_sort, first_sort_trace) := audit_map_get audit_positive_encode a
    (rw_sorts base) in
              let prefix := prefix ++ [AuditCase 909 []; AuditCall (RIPairSort first_sort_trace)] in
              match first_sort with
              | None => rw_ri_pair_skip dropped p (prefix ++ [AuditCase 910 []])
              | Some sa =>
                let '(second_sort, second_sort_trace) := audit_map_get audit_positive_encode b
    (rw_sorts base) in
                let prefix := prefix ++ [AuditCase 911 []; AuditCall (RIPairSort
    second_sort_trace)] in
                match second_sort with
                | None => rw_ri_pair_skip dropped p (prefix ++ [AuditCase 912 []])
                | Some sb =>
                  let '(code_sa, sa_trace) := rw_external_encoding_events sort sa in
                  let '(code_sb, sb_trace) := rw_external_encoding_events sort sb in
                  let '(same_sort, sort_compare_trace) := rw_ri_positive_dec_atomic code_sa
    code_sb in
                  let prefix := prefix ++ [AuditCase 913 []; AuditCall (RIPairSortCode sa code_sa
    sa_trace);
                    AuditCall (RIPairSortCode sb code_sb sb_trace);
                    AuditCall (RIPairDecision code_sa code_sb same_sort sort_compare_trace)] in
                  if same_sort then rw_ri_pair_merge_atomic s dropped p remaining ra rb (prefix
    ++ [AuditCase 914 []])
                  else rw_ri_pair_skip dropped p (prefix ++ [AuditCase 915 []])
                end
              end
          else rw_ri_pair_skip dropped p (prefix ++ [AuditCase 916 []])
        end
      end
    end
  end.
```

## Galois.Rewrite.RewriteAuditIndexRebuild

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditIndexRebuild.v`.

```rocq
(** * RewriteAuditIndexRebuild

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexDirty RewriteAuditIndexPair
  RewriteAuditIndexReference RewriteAuditIndexTickReference RewriteAuditQueueReference.
Import List.ListNotations.

Inductive rw_ri_tick_call (K Sort V : Type) : Type :=
  | RITickDirty : audit_trace
    (rw_ri_dirty_call K Sort V) -> rw_ri_tick_call K Sort V
  | RITickPop : audit_trace
    rw_queue_insert_call -> rw_ri_tick_call K Sort V
  | RITickPair : audit_trace
    (rw_ri_pair_call K Sort V) -> rw_ri_tick_call K Sort V.
Arguments RITickDirty {K Sort
    V}.
Arguments RITickPop {K Sort V}.
Arguments RITickPair {K Sort V}.


Definition rw_ri_tick_event_cost {K Sort V}
    (event : audit_event (rw_ri_tick_call K Sort V)) : nat
    :=
  match event with
  | AuditCall (RITickDirty trace) => 64 + rw_ri_dirty_trace_cost
    trace
  | AuditCall (RITickPop trace) => 64 + rw_queue_insert_expanded_work trace
  |
    AuditCall (RITickPair trace) => 64 + rw_ri_pair_trace_cost trace
  | _ => 64

    end.


Definition rw_ri_tick_trace_cost {K Sort V}
    (trace : audit_trace (rw_ri_tick_call
    K Sort V)) : nat :=
  fold_right (fun event total => rw_ri_tick_event_cost event + total) 0
    trace.


Definition rw_ri_tick_atomic {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort
    : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (s :
    rw_index_state K Sort V) :
    option (rw_index_state K Sort V * rw_index_event) *

    audit_trace (rw_ri_tick_call K Sort V) :=
  match rw_index_dirty_order s with
  | id :: rest
    =>
    let '(next, trace) := rw_ri_dirty_tick_atomic op sort value s id rest in
    (Some
    (next, RWIndexDirty id),
      [AuditCase 930 []; AuditCall (RITickDirty trace);
    AuditConstruct 931 []])
  | nil =>
    let '(popped, trace) := rw_queue_pop_atomic
    (rw_index_pending s) in
    match popped with
    | None => (None, [AuditCase 932 [];
    AuditCall (RITickPop trace);
        AuditCase 933 []; AuditConstruct 934 []])
    | Some
    (pair_value, remaining) =>
      let '(next, pair_trace) := rw_ri_pair_atomic op sort value
    s pair_value remaining in
      (Some next, [AuditCase 932 []; AuditCall (RITickPop trace);

           AuditCase 935 []; AuditCall (RITickPair pair_trace); AuditConstruct 936 []])
    end

     end.

(** The tick mirror returns the actual deterministic tick on the same state.
    *)

(** This statement fixes the ri tick erases statement contract. *)
Definition rw_ri_tick_erases_statement : Prop :=
  forall K Sort V (EK : encoding K) (ES
    : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort :
    rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) s,
  (forall k, fst
    (rw_queue_encoder_run op k) = encode EK k) ->
  (forall ty, fst (rw_queue_encoder_run sort
    ty) = encode ES ty) ->
  (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->

    fst (rw_ri_tick_atomic op sort value s) = rw_index_tick EK ES EV s.


Inductive rw_ri_repeat_call (K Sort V : Type) : Type :=
  | RIRepeatTick : rw_index_state K Sort V ->

         option (rw_index_state K Sort V * rw_index_event) ->
      audit_trace (rw_ri_tick_call
    K Sort V) -> rw_ri_repeat_call K Sort V.
Arguments RIRepeatTick {K Sort V}.


Definition rw_ri_repeat_event_cost {K Sort V}
    (event : audit_event (rw_ri_repeat_call K Sort V)) :
    nat :=
  match event with
  | AuditCall (RIRepeatTick _ _ trace) => 64 +
    rw_ri_tick_trace_cost trace
  | _ => 64
  end.


Definition rw_ri_repeat_trace_cost {K Sort
    V}
    (trace : audit_trace (rw_ri_repeat_call K Sort V)) : nat :=
  fold_right (fun event
    total => rw_ri_repeat_event_cost event + total) 0 trace.


Definition rw_ri_repeat_once {K
    Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value
    : rw_queue_encoder_adapter V)
    (state : rw_index_state K Sort V * list rw_index_event) :

       (rw_index_state K Sort V * list rw_index_event) *
      audit_trace (rw_ri_repeat_call K
    Sort V) :=
  let '(answer, trace) := rw_ri_tick_atomic op sort value (fst state) in
  match
    answer with
  | None => (state, [AuditCall (RIRepeatTick (fst state) answer trace);
    AuditCase 937 []])
  | Some (next, event) => ((next, event :: snd state),
      [AuditCall
    (RIRepeatTick (fst state) answer trace); AuditCase 938 [];
       AuditConstruct 939 [];
    AuditConstruct 940 []])
  end.


Fixpoint rw_ri_repeat_atomic {K Sort V} (op :
    rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value :
    rw_queue_encoder_adapter V)
    (fuel : positive) (state : rw_index_state K Sort V * list
    rw_index_event) :
    (rw_index_state K Sort V * list rw_index_event) *
      audit_trace
    (rw_ri_repeat_call K Sort V) :=
  if rw_ri_rebuild_done state then (state, [AuditCase 941
    []; AuditCase 942 []])
  else match fuel with
  | xH => let '(out, trace) :=
    rw_ri_repeat_once op sort value state in
      (out, [AuditCase 941 []; AuditCase 943 []] ++
    trace)
  | xO rest =>
    let '(middle, first_trace) := rw_ri_repeat_atomic op sort value
    rest state in
    let '(out, second_trace) := rw_ri_repeat_atomic op sort value rest middle
    in
    (out, [AuditCase 941 []; AuditCase 944 []] ++ first_trace ++ second_trace)
  | xI
    rest =>
    let '(middle, first_trace) := rw_ri_repeat_once op sort value state in
    let
    '(later, second_trace) := rw_ri_repeat_atomic op sort value rest middle in
    let '(out,
    last_trace) := rw_ri_repeat_atomic op sort value rest later in
    (out, [AuditCase 941 [];
    AuditCase 945 []] ++ first_trace ++ second_trace ++ last_trace)
  end.

(** The binary
    source observer preserves the actual repeat schedule and reversed events. *)

(** This statement fixes the ri repeat erases statement contract. *)
Definition rw_ri_repeat_erases_statement : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding
    Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort :
    rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) fuel state,

    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
  (forall ty, fst
    (rw_queue_encoder_run sort ty) = encode ES ty) ->
  (forall v, fst (rw_queue_encoder_run
    value v) = encode EV v) ->
  fst (rw_ri_repeat_atomic op sort value fuel state) =

    rw_repeat rw_ri_rebuild_done (rw_ri_rebuild_step EK ES EV) fuel state.


Fixpoint rw_ri_reverse_onto {A} (xs acc : list A) : list A * nat :=
  match xs with
  | nil => (acc,
    64)
  | x :: rest => let '(out, work) := rw_ri_reverse_onto rest (x :: acc) in
      (out,
    128 + work)
  end.

(** Every actual tick is counted once; no successful merge is dropped
    from the observation. *)

Definition rw_ri_repeat_tick_count {K Sort V}
    (trace :
    audit_trace (rw_ri_repeat_call K Sort V)) : nat :=
  fold_right (fun event count =>

    match event with AuditCall _ => S count | _ => count end) 0 trace.

(** The repeat consumes
    at most its binary fuel in actual tick calls. *)

(** This statement fixes the ri repeat tick bound statement contract. *)
Definition rw_ri_repeat_tick_bound_statement : Prop :=
  forall K Sort V (op : rw_queue_encoder_adapter
    K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V) fuel
    state,
  rw_ri_repeat_tick_count (snd (rw_ri_repeat_atomic op sort value fuel state)) <=

    Pos.to_nat fuel.



Definition rw_ri_forest_root_atomic (forest : UnionFind.t rw_id) (id : rw_id) :
    rw_id * list
    (audit_uf_event rw_id (audit_basic_encoding_event positive)) :=
  let '(found, trace) :=
    audit_uf_find audit_positive_encode id forest in (fst found, trace).


Fixpoint rw_ri_roots_atomic (forest : UnionFind.t rw_id) (roots : list rw_id) :
    list rw_id * nat
    :=
  match roots with
  | nil => (nil, 64)
  | r :: rest =>
    let '(root, trace) :=
    rw_ri_forest_root_atomic forest r in
    let '(same, compare_trace) := audit_positive_eqb
    root r in
    let '(tail, tail_work) := rw_ri_roots_atomic forest rest in
    ((if same then
    r :: tail else tail), 64 +
      audit_uf_source_work audit_basic_encoding_work trace +

     audit_positive_eqb_source_work compare_trace + tail_work)
  end.


Definition rw_ri_graph_atomic {K Sort V} (state : rw_index_state K Sort V) :
    rw_graph K Sort V *
    nat :=
  let base := rw_index_base state in
  let forest := rw_index_forest state in
  let
    '(roots, root_work) := rw_ri_roots_atomic forest (rw_roots base) in
  let '(aliases, trace)
    :=
    audit_map_transform (rw_ri_forest_root_atomic forest) (rw_class_roots base) in

    (RwGraph roots (rw_nodes_in base) aliases (rw_sorts base) (rw_nodes base),
    64 +
    root_work +
      audit_map_transform_source_work (audit_uf_source_work
    audit_basic_encoding_work) trace).


Definition rw_ri_rebuild_fuel_atomic {K Sort V} (s :
    rw_index_state K Sort V) :
    positive * nat :=
  let '(nodes, nt) := rw_fuel_length
    (rw_nodes_in (rw_index_base s)) in
  let '(graph, gw) := rw_ri_graph_atomic s in
  let
    '(roots, rt) := rw_fuel_length (rw_roots graph) in
  let '(pending, pt) := rw_fuel_length
    (rw_pending_sequence (rw_index_pending s)) in
  let '(first, mt) := rw_fuel_mul (S roots) (S
    nodes) in
  let '(square, st) := rw_fuel_mul first (S nodes) in
  let '(prefix, add_trace)
    := rw_fuel_add pending square in
  let '(dirty, dt) := rw_fuel_length (rw_index_dirty_order
    s) in
  let '(total, total_trace) := rw_fuel_add prefix dirty in
  let '(fuel, ft) :=
    rw_fuel_to_positive total in
  (fuel, 64 + audit_work nt + gw + audit_work rt + audit_work
    pt +
    audit_work mt + audit_work st + audit_work add_trace + audit_work dt +

    audit_work total_trace + audit_work ft).


Definition rw_ri_rebuild_atomic {K Sort V} (op :
    rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value :
    rw_queue_encoder_adapter V)
    (s : rw_index_state K Sort V) :
    (rw_index_state K Sort V
    * list rw_index_event) * nat :=
  let '(fuel, fuel_work) := rw_ri_rebuild_fuel_atomic s in

    let '((out, reversed), trace) := rw_ri_repeat_atomic op sort value fuel (s, nil) in
  let
    '(events, reverse_work) := rw_ri_reverse_onto reversed nil in
  ((out, events), 64 +
    fuel_work + rw_ri_repeat_trace_cost trace + reverse_work).

(** The graph observer pays for
    actual materialization and preserves every exposed map. *)

(** This statement fixes the ri graph erases statement contract. *)
Definition rw_ri_graph_erases_statement : Prop :=
  forall K Sort V (s : rw_index_state K Sort V),

    fst (rw_ri_graph_atomic s) = rw_index_graph s.

(** Fuel setup evaluates the exact public
    arithmetic and graph observer. *)

(** This statement fixes the ri rebuild fuel erases statement contract. *)
Definition rw_ri_rebuild_fuel_erases_statement : Prop :=

    forall K Sort V (s : rw_index_state K Sort V),
  fst (rw_ri_rebuild_fuel_atomic s) =
    rw_ri_rebuild_fuel s.

(** The complete rebuild returns the same state and chronological
    event list. *)

(** This statement fixes the ri rebuild erases statement contract. *)
Definition rw_ri_rebuild_erases_statement : Prop :=
  forall K Sort V (EK :
    encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) s,
  (forall
    k, fst (rw_queue_encoder_run op k) = encode EK k) ->
  (forall ty, fst (rw_queue_encoder_run
    sort ty) = encode ES ty) ->
  (forall v, fst (rw_queue_encoder_run value v) = encode EV v)
    ->
  fst (rw_ri_rebuild_atomic op sort value s) = rw_index_rebuild EK ES EV s.

(** The same
    actual pair tick determines the complete source-cost trace and result. *)

(** This statement fixes the ri pair erases statement contract. *)
Definition rw_ri_pair_erases_statement : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding
    Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort :
    rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) s pair_value
    remaining,
  (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
  (forall ty, fst
    (rw_queue_encoder_run sort ty) = encode ES ty) ->
  (forall v, fst (rw_queue_encoder_run
    value v) = encode EV v) ->
  fst (rw_ri_pair_atomic op sort value s pair_value remaining) =

       rw_ri_pair_tick EK ES EV s pair_value remaining.

(** A nonempty complete rebuild merges
    duplicate variables and exhausts both worklists. *)

Definition rw_ri_pair_node_read_count {K Sort V}
    (trace : audit_trace (rw_ri_pair_call K
    Sort V)) : nat :=
  fold_right (fun event total =>
    match event with AuditCall
    (RIPairNode _) => S total | _ => total end) 0 trace.

(** A missing first multi-match
    scrutinee skips the second node read. *)
```

## Galois.Rewrite.RewriteAuditIndexPrepare

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditIndexPrepare.v`.

```rocq
(** * RewriteAuditIndexPrepare

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexBucket RewriteAuditIndexBuild
  RewriteAuditIndexPrepareReference RewriteAuditIndexReference RewriteAuditQueueContracts
  RewriteAuditQueueReference.
Import List.ListNotations.

Inductive rw_ri_prepare_receipt (K Sort V : Type) : Type :=
  | RIPrepareBlock : rw_ri_prepare_receipt K Sort V
  | RIPrepareNodeRead : list (audit_map_event rw_id (rw_id * rw_node K Sort V)
      (audit_basic_encoding_event positive)) -> rw_ri_prepare_receipt K Sort V
  | RIPrepareRootRead : list (audit_map_event rw_id rw_id
      (audit_basic_encoding_event positive)) -> rw_ri_prepare_receipt K Sort V
  | RIPrepareOperatorOnce : audit_trace (rw_ri_bucket_call K nat) ->
      rw_ri_prepare_receipt K Sort V
  | RIPrepareVariableOnce : audit_trace (rw_ri_bucket_call V nat) ->
      rw_ri_prepare_receipt K Sort V
  | RIPrepareParentOnce : audit_trace
      (rw_ri_bucket_call rw_id (audit_basic_encoding_event positive)) ->
      rw_ri_prepare_receipt K Sort V
  | RIPrepareDirtyOnce : list (audit_set_event rw_id (audit_basic_encoding_event positive)) ->
      rw_ri_prepare_receipt K Sort V
  | RIPrepareFreshOnce : audit_trace (rw_ri_fresh_call K Sort V) ->
      rw_ri_prepare_receipt K Sort V.
Arguments RIPrepareBlock {K Sort V}.
Arguments RIPrepareNodeRead {K Sort V}.
Arguments RIPrepareRootRead {K Sort V}.
Arguments RIPrepareOperatorOnce {K Sort V}.
Arguments RIPrepareVariableOnce {K Sort V}.
Arguments RIPrepareParentOnce {K Sort V}.
Arguments RIPrepareDirtyOnce {K Sort V}.
Arguments RIPrepareFreshOnce {K Sort V}.


Definition rw_ri_prepare_receipt_work {K Sort V}
    (receipt : rw_ri_prepare_receipt K Sort V) : nat :=
  match receipt with
  | RIPrepareBlock => 64
  | RIPrepareNodeRead trace => 64 + audit_map_source_work audit_basic_encoding_work trace
  | RIPrepareRootRead trace => 64 + audit_map_source_work audit_basic_encoding_work trace
  | RIPrepareOperatorOnce trace => 64 + rw_ri_bucket_trace_cost rw_external_events_work trace
  | RIPrepareVariableOnce trace => 64 + rw_ri_bucket_trace_cost rw_external_events_work trace
  | RIPrepareParentOnce trace => 64 + rw_ri_bucket_trace_cost audit_basic_encoding_work trace
  | RIPrepareDirtyOnce trace => 64 + audit_finset_source_work audit_basic_encoding_work trace
  | RIPrepareFreshOnce trace => 64 + rw_ri_fresh_trace_cost trace
  end.


Definition rw_ri_prepare_once_work {K Sort V}
    (receipts : list (rw_ri_prepare_receipt K Sort V)) : nat :=
  fold_right (fun receipt total => rw_ri_prepare_receipt_work receipt + total) 0 receipts.


Fixpoint rw_ri_prepare_parents_once {K Sort V} (g : rw_graph K Sort V) (id : rw_id)
    (children : list rw_id) (table : Map.t rw_id (FinSet.t rw_id)) :
    Map.t rw_id (FinSet.t rw_id) * list (rw_ri_prepare_receipt K Sort V) :=
  match children with
  | nil => (table, [RIPrepareBlock])
  | child :: rest =>
    let '(found, lookup) := audit_map_get audit_positive_encode child (rw_class_roots g) in
    match found with
    | None =>
      let '(out, later) := rw_ri_prepare_parents_once g id rest table in
      (out, RIPrepareRootRead lookup :: RIPrepareBlock :: later)
    | Some root =>
      let '(updated, bucket) := rw_ri_bucket_add_atomic audit_positive_encode root id table in
      let '(out, later) := rw_ri_prepare_parents_once g id rest updated in
      (out, RIPrepareRootRead lookup :: RIPrepareParentOnce bucket :: later)
    end
  end.


Fixpoint rw_ri_prepare_nodes_once {K Sort V} (op : rw_queue_encoder_adapter K)
    (value : rw_queue_encoder_adapter V) (g : rw_graph K Sort V) (ids : list rw_id)
    (acc : rw_ri_build_acc K V) : rw_ri_build_acc K V * list (rw_ri_prepare_receipt K Sort V) :=
  match ids with
  | nil => (acc, [RIPrepareBlock])
  | id :: rest =>
    let '(found, lookup) := audit_map_get audit_positive_encode id (rw_nodes g) in
    match found with
    | None =>
      let '(out, later) := rw_ri_prepare_nodes_once op value g rest acc in
      (out, RIPrepareNodeRead lookup :: RIPrepareBlock :: later)
    | Some (_, RWNVar _ v) =>
      let '(updated, bucket) := rw_ri_bucket_add_atomic (rw_external_encoding_events value)
        v id (rw_ri_build_vars acc) in
      let next := RwRiBuildAcc (rw_ri_build_ops acc) updated (rw_ri_build_parents acc) in
      let '(out, later) := rw_ri_prepare_nodes_once op value g rest next in
      (out, RIPrepareNodeRead lookup :: RIPrepareVariableOnce bucket :: later)
    | Some (_, RWNApp _ k children) =>
      let '(updated, bucket) := rw_ri_bucket_add_atomic (rw_external_encoding_events op)
        k id (rw_ri_build_ops acc) in
      let '(parents, parent_receipts) :=
        rw_ri_prepare_parents_once g id children (rw_ri_build_parents acc) in
      let next := RwRiBuildAcc updated (rw_ri_build_vars acc) parents in
      let '(out, later) := rw_ri_prepare_nodes_once op value g rest next in
      (out, RIPrepareNodeRead lookup :: RIPrepareOperatorOnce bucket ::
        parent_receipts ++ later)
    end
  end.


Definition rw_ri_prepare_once {K Sort V} (op : rw_queue_encoder_adapter K)
    (value : rw_queue_encoder_adapter V) (g : rw_graph K Sort V) :
    rw_index_state K Sort V * list (rw_ri_prepare_receipt K Sort V) :=
  let empty := RwRiBuildAcc Map.empty Map.empty Map.empty in
  let '(buckets, bucket_receipts) :=
    rw_ri_prepare_nodes_once op value g (rw_nodes_in g) empty in
  let '(dirty, dirty_trace) := audit_finset_of_list audit_positive_encode (rw_nodes_in g) in
  let '(fresh, fresh_trace) := rw_ri_fresh_atomic g in
  (RWIndexState g UnionFind.make (rw_ri_build_parents buckets) Map.empty Map.empty
    (rw_nodes_in g) dirty rw_pending_empty (rw_ri_build_ops buckets)
    (rw_ri_build_vars buckets) fresh,
    RIPrepareBlock :: bucket_receipts ++
      [RIPrepareDirtyOnce dirty_trace; RIPrepareFreshOnce fresh_trace; RIPrepareBlock]).

(** The one-invocation preparation mirror computes the separate plain index producer. *)

(** This statement fixes the ri prepare once erases statement contract. *)
Definition rw_ri_prepare_once_erases_statement : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (value : rw_queue_encoder_adapter V) graph,
  (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
  (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
  fst (rw_ri_prepare_once op value graph) = rw_index_build EK ES EV graph.

(** Preparation emits only linearly many top-level receipts in the stored input structure. *)

(** This statement fixes the ri prepare once receipts statement contract. *)
Definition rw_ri_prepare_once_receipts_statement : Prop :=
  forall K Sort V (op : rw_queue_encoder_adapter K) (value : rw_queue_encoder_adapter V)
    (graph : rw_graph K Sort V),
  length (snd (rw_ri_prepare_once op value graph)) <= 16 * rw_rq_input_structure graph.
```

## Galois.Rewrite.RewriteAuditIndexMembership

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditIndexMembership.v`.

```rocq
(** * RewriteAuditIndexMembership

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexCompare RewriteAuditIndexFind
  RewriteAuditIndexReference RewriteAuditQueueReference.
Import List.ListNotations.

Definition rw_ri_encoded_equal {A} (adapter : rw_queue_encoder_adapter A) (a b : A) :
    bool *
    nat :=
  let '(p, pw) := rw_queue_encoder_run adapter a in
  let '(q, qw) :=
    rw_queue_encoder_run adapter b in
  let '(answer, trace) := rw_ri_positive_dec_atomic p q
    in
  (answer, 64 + pw + qw + 64 * audit_work trace).


Definition rw_ri_same_class_atomic {K Sort
    V} (state : rw_index_state K Sort V)
    (a b : rw_id) : bool * nat :=
  let '(first, ft) :=
    rw_ri_find_atomic state a in
  match first with
  | None => (false, 64 +
    rw_ri_find_trace_cost ft)
  | Some x =>
    let '(second, st) := rw_ri_find_atomic state b
    in
    match second with
    | None => (false, 64 + rw_ri_find_trace_cost ft +
    rw_ri_find_trace_cost st)
    | Some y => let '(answer, trace) := audit_positive_eqb x y in

           (answer, 64 + rw_ri_find_trace_cost ft + rw_ri_find_trace_cost st +

    audit_positive_eqb_source_work trace)
    end
  end.


Definition rw_ri_bucket_ids {A E}
    (encoder : A -> positive * list E)
    (encoder_work : list E -> nat) (key : A) (table :
    Map.t A (FinSet.t rw_id)) :
    list rw_id * nat :=
  let '(found, trace) := audit_map_get
    encoder key table in
  let bucket := match found with Some b => b | None => FinSet.empty end
    in
  let '(ids, et) := audit_finset_elements bucket in
  (ids, 64 + audit_map_source_work
    encoder_work trace + audit_set_elements_work et).


Fixpoint rw_ri_member_atomic {K Sort V}
    (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value :
    rw_queue_encoder_adapter V)
    (state : rw_index_state K Sort V) (term : rw_term K Sort V)
    (root : rw_id) : bool * nat :=
  match term with
  | RWVar ty v =>
    let '(candidates,
    bucket_work) := rw_ri_bucket_ids (rw_external_encoding_events value)

    rw_external_events_work v (rw_index_variables state) in
    let fix visit (ids : list rw_id)
    : bool * nat :=
      match ids with
      | nil => (false, 64)
      | id :: rest =>

     let '(found, node_trace) := audit_map_get audit_positive_encode id
          (rw_nodes
    (rw_index_base state)) in
        let '(head, head_work) := match found with
          |
    Some (owner, RWNVar ty' v') =>
            let '(same_sort, sw) := rw_ri_encoded_equal sort
    ty ty' in
            if same_sort then
              let '(same_value, vw) :=
    rw_ri_encoded_equal value v v' in
              if same_value then
                let
    '(same_class, cw) := rw_ri_same_class_atomic state root owner in

    (same_class, 64 + sw + vw + cw)
              else (false, 64 + sw + vw)
            else
    (false, 64 + sw)
          | _ => (false, 64)
          end in
        let '(tail,
    tail_work) := visit rest in
        (head || tail, 64 + audit_map_source_work
    audit_basic_encoding_work node_trace +
          head_work + tail_work)
      end in
    let
    '(answer, work) := visit candidates in (answer, 64 + bucket_work + work)
  | RWApp ty k
    children =>
    let '(candidates, bucket_work) := rw_ri_bucket_ids
    (rw_external_encoding_events op)
      rw_external_events_work k (rw_index_operators state)
    in
    let fix visit (ids : list rw_id) : bool * nat :=
      match ids with
      | nil =>
    (false, 64)
      | id :: rest =>
        let '(found, node_trace) := audit_map_get
    audit_positive_encode id
          (rw_nodes (rw_index_base state)) in
        let '(head,
    head_work) := match found with
          | Some (owner, RWNApp ty' k' child_ids) =>

       let '(same_sort, sw) := rw_ri_encoded_equal sort ty ty' in
            if same_sort then

                 let '(same_op, ow) := rw_ri_encoded_equal op k k' in
              if same_op
    then
                let '(same_class, cw) := rw_ri_same_class_atomic state root owner in

                 let fix pairs (terms : list (rw_term K Sort V)) (classes : list rw_id) :

                 bool * nat :=
                  match terms, classes with
                  |
    nil, nil => (true, 64)
                  | t :: ts, c :: cs =>
                    let
    '(head, hw) := rw_ri_member_atomic op sort value state t c in
                    let
    '(tail, tw) := pairs ts cs in (head && tail, 64 + hw + tw)
                  | _, _ =>
    (false, 64)
                  end in
                let '(same_children, child_work) :=
    pairs children child_ids in
                (same_class && same_children, 64 + sw + ow + cw
    + child_work)
              else (false, 64 + sw + ow)
            else (false, 64 + sw)

          | _ => (false, 64)
          end in
        let '(tail, tail_work) := visit rest in

         (head || tail, 64 + audit_map_source_work audit_basic_encoding_work node_trace +

       head_work + tail_work)
      end in
    let '(answer, work) := visit candidates in
    (answer, 64 + bucket_work + work)
  end.

(** Prepared indexed membership recognizes exactly
    finite represented terms. *)

(** This statement fixes the ri member spec statement contract. *)
Definition rw_ri_member_spec_statement : Prop :=
  forall K
    Sort V (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op :
    rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value :
    rw_queue_encoder_adapter V) (sig : rw_signature K Sort V) state term root,
  (forall k, fst
    (rw_queue_encoder_run op k) = encode EK k) ->
  (forall ty, fst (rw_queue_encoder_run sort
    ty) = encode ES ty) ->
  (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->

    rw_index_valid EK ES EV sig state ->
  (fst (rw_ri_member_atomic op sort value state term
    root) = true <->
    rw_represents (rw_index_graph state) root term).
```

## Galois.Rewrite.RewriteAuditIndexMatchReference

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditIndexMatchReference.v`.

```rocq
(** * RewriteAuditIndexMatchReference

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexReference.
Import List.ListNotations.

Definition rw_view_match_candidates {K Sort V H} (EH : encoding H)
    (view : rw_phase_view K Sort V) (op : K) (ps : list (rw_pattern K Sort V H))
    (a : rw_assignment H) : list rw_id :=
  match ps with
  | RWHole _ h :: _ =>
    match Map.get EH h a with
    | Some c => rw_view_parent_nodes view c
    | None => rw_view_operator_nodes view op
    end
  | _ => rw_view_operator_nodes view op
  end.

Definition rw_view_same_class {K Sort V} (view : rw_phase_view K Sort V) (a b : rw_id) : bool :=
  match rw_view_find view a, rw_view_find view b with
  | Some ra, Some rb => Pos.eqb ra rb
  | _, _ => false
  end.

Fixpoint rw_view_match_on {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (view : rw_phase_view K Sort V) (p : rw_pattern K Sort V H)
    (root : rw_id) (a : rw_assignment H) {struct p} : list (rw_assignment H) :=
  match p with
  | RWHole s h =>
    match rw_view_find view root, rw_view_sort view root with
    | Some canonical, Some ty => if rw_key_eq_dec ES s ty then rw_bind EH h canonical a else []
    | _, _ => []
    end
  | RWPVar s v =>
    flat_map (fun n =>
      match rw_view_node view n with
      | Some (owner, RWNVar ty w) =>
        if rw_key_eq_dec ES s ty then if rw_key_eq_dec EV v w then
          if rw_view_same_class view root owner then [a] else [] else [] else []
      | _ => []
      end) (rw_view_variable_nodes view v)
  | RWPApp s op ps =>
    flat_map (fun n =>
      match rw_view_node view n with
      | Some (owner, RWNApp ty other ids) =>
        if rw_key_eq_dec ES s ty then if rw_key_eq_dec EK op other then
          if rw_view_same_class view root owner then
            rw_match_children (map (rw_view_match_on EK ES EV EH view) ps) ids a
          else [] else [] else []
      | _ => []
      end) (rw_view_match_candidates EH view op ps a)
  end.

Definition rw_view_match {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (view : rw_phase_view K Sort V) (root : rw_id)
    (pattern : rw_pattern K Sort V H) : list (rw_assignment H) :=
  rw_distinct_assignments EH (rw_view_match_on EK ES EV EH view pattern root Map.empty).


(** This statement fixes the view match sound contract. *)
Definition rw_view_match_sound_contract : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) (g : rw_graph K Sort V)
    view root (pattern : rw_pattern K Sort V H) assignment sub term,
    rw_graph_wf sig g -> rw_view_agrees g view ->
    In assignment (rw_view_match EK ES EV EH view root pattern) ->
    rw_covers EH g pattern assignment sub -> rw_instantiate sub pattern = Some term ->
    rw_represents g root term.

(** This statement fixes the view match complete contract. *)
Definition rw_view_match_complete_contract : Prop :=
 forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
  (EH : encoding H) (sig : rw_signature K Sort V) (g : rw_graph K Sort V)
  view root (pattern : rw_pattern K Sort V H) sub term,
  rw_graph_wf sig g -> rw_view_agrees g view -> rw_clean g ->
  rwp_typed sig (fun h => option_map rw_sort (sub h)) pattern ->
  rw_instantiate sub pattern = Some term -> rw_represents g root term ->
  exists assignment,
    In assignment (rw_view_match EK ES EV EH view root pattern) /\
    rw_covers EH g pattern assignment sub.

(** This statement fixes the view match assignment contract. *)
Definition rw_view_match_assignment_contract : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) (g : rw_graph K Sort V)
    view root (pattern : rw_pattern K Sort V H) assignment,
    rw_graph_wf sig g -> rw_view_agrees g view ->
    In assignment (rw_view_match EK ES EV EH view root pattern) ->
    Map.wf EH assignment /\
    (forall h, (exists c, Map.get EH h assignment = Some c) <-> In h (rwp_holes pattern)) /\
    forall h c, Map.get EH h assignment = Some c -> rw_find g c = Some c.

(** This statement fixes the view match nodup contract. *)
Definition rw_view_match_nodup_contract : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (view : rw_phase_view K Sort V) root (pattern : rw_pattern K Sort V H),
    NoDup (rw_view_match EK ES EV EH view root pattern).
```

## Galois.Rewrite.RewriteAuditIndexMatch

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditIndexMatch.v`.

```rocq
(** * RewriteAuditIndexMatch

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexCompare RewriteAuditIndexFind
  RewriteAuditIndexMatchReference RewriteAuditIndexMembership RewriteAuditIndexReference
  RewriteAuditQueueReference.
Import List.ListNotations.

Fixpoint rw_ri_match_append {A} (xs ys : list A) : list A * nat :=
  match xs with
  | nil => (ys, 64)
  | x :: rest =>
    let '(tail, work) := rw_ri_match_append rest ys in
    (x :: tail, 64 + work)
  end.


Definition rw_ri_bind_atomic {H} (hole : rw_queue_encoder_adapter H) (h : H) (root : rw_id)
    (assignment : rw_assignment H) : list (rw_assignment H) * nat :=
  let '(found, lookup) := audit_map_get (rw_external_encoding_events hole) h assignment in
  match found with
  | Some old =>
    let '(same, trace) := rw_ri_positive_dec_atomic old root in
    ((if same then [assignment] else nil),
      64 + audit_map_source_work rw_external_events_work lookup + 64 * audit_work trace)
  | None =>
    let '(updated, trace) := audit_map_set (rw_external_encoding_events hole) h root assignment in
    ([updated], 64 + audit_map_source_work rw_external_events_work lookup +
      audit_map_source_work rw_external_events_work trace)
  end.


Fixpoint rw_ri_match_flat_map {A B} (body : A -> list B * nat) (xs : list A) : list B * nat :=
  match xs with
  | nil => (nil, 64)
  | x :: rest =>
    let '(head, hw) := body x in
    let '(tail, tw) := rw_ri_match_flat_map body rest in
    let '(out, aw) := rw_ri_match_append head tail in
    (out, 64 + hw + tw + aw)
  end.


Fixpoint rw_ri_match_children_atomic {H}
    (functions : list (rw_id -> rw_assignment H -> list (rw_assignment H) * nat))
    (ids : list rw_id) (assignment : rw_assignment H) : list (rw_assignment H) * nat :=
  match functions, ids with
  | nil, nil => ([assignment], 64)
  | f :: rest, id :: children =>
    let '(heads, hw) := f id assignment in
    let '(out, tw) := rw_ri_match_flat_map
      (rw_ri_match_children_atomic rest children) heads in
    (out, 64 + hw + tw)
  | _, _ => (nil, 64)
  end.


Definition rw_ri_match_candidates_atomic {K Sort V H} (op : rw_queue_encoder_adapter K)
    (hole : rw_queue_encoder_adapter H) (state : rw_index_state K Sort V) (key : K)
    (patterns : list (rw_pattern K Sort V H)) (assignment : rw_assignment H) :
    list rw_id * nat :=
  match patterns with
  | RWHole _ h :: _ =>
    let '(found, lookup) := audit_map_get (rw_external_encoding_events hole) h assignment in
    let prefix := 64 + audit_map_source_work rw_external_events_work lookup in
    match found with
    | None =>
      let '(out, work) := rw_ri_bucket_ids (rw_external_encoding_events op)
        rw_external_events_work key (rw_index_operators state) in
      (out, prefix + work)
    | Some id =>
      let '(root, trace) := rw_ri_find_atomic state id in
      match root with
      | None => (nil, prefix + rw_ri_find_trace_cost trace)
      | Some root =>
        let '(out, work) := rw_ri_bucket_ids audit_positive_encode audit_basic_encoding_work
          root (rw_index_parent_buckets state) in
        (out, prefix + rw_ri_find_trace_cost trace + work)
      end
    end
  | _ => rw_ri_bucket_ids (rw_external_encoding_events op)
      rw_external_events_work key (rw_index_operators state)
  end.


Fixpoint rw_ri_match_on_atomic {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (hole : rw_queue_encoder_adapter H) (state : rw_index_state K Sort V)
    (pattern : rw_pattern K Sort V H) (root : rw_id) (assignment : rw_assignment H)
    {struct pattern} : list (rw_assignment H) * nat :=
  match pattern with
  | RWHole ty h =>
    let '(found, trace) := rw_ri_find_atomic state root in
    match found with
    | None => (nil, 64 + rw_ri_find_trace_cost trace)
    | Some canonical =>
      let '(declared, lookup) := audit_map_get audit_positive_encode root
        (rw_sorts (rw_index_base state)) in
      let prefix := 64 + rw_ri_find_trace_cost trace +
        audit_map_source_work audit_basic_encoding_work lookup in
      match declared with
      | None => (nil, prefix)
      | Some declared =>
        let '(same, work) := rw_ri_encoded_equal sort ty declared in
        if same then
          let '(out, binding_work) := rw_ri_bind_atomic hole h canonical assignment in
          (out, prefix + work + binding_work)
        else (nil, prefix + work)
      end
    end
  | RWPVar ty v =>
    let '(candidates, bucket_work) := rw_ri_bucket_ids (rw_external_encoding_events value)
      rw_external_events_work v (rw_index_variables state) in
    let '(out, work) := rw_ri_match_flat_map (fun id =>
      let '(found, trace) := audit_map_get audit_positive_encode id
        (rw_nodes (rw_index_base state)) in
      let prefix := 64 + audit_map_source_work audit_basic_encoding_work trace in
      match found with
      | Some (owner, RWNVar declared w) =>
        let '(same_sort, sw) := rw_ri_encoded_equal sort ty declared in
        if same_sort then
          let '(same_value, vw) := rw_ri_encoded_equal value v w in
          if same_value then
            let '(same_class, cw) := rw_ri_same_class_atomic state root owner in
            ((if same_class then [assignment] else nil), prefix + sw + vw + cw)
          else (nil, prefix + sw + vw)
        else (nil, prefix + sw)
      | _ => (nil, prefix)
      end) candidates in
    (out, 64 + bucket_work + work)
  | RWPApp ty key patterns =>
    let '(candidates, bucket_work) :=
      rw_ri_match_candidates_atomic op hole state key patterns assignment in
    let '(out, work) := rw_ri_match_flat_map (fun id =>
      let '(found, trace) := audit_map_get audit_positive_encode id
        (rw_nodes (rw_index_base state)) in
      let prefix := 64 + audit_map_source_work audit_basic_encoding_work trace in
      match found with
      | Some (owner, RWNApp declared other children) =>
        let '(same_sort, sw) := rw_ri_encoded_equal sort ty declared in
        if same_sort then
          let '(same_op, ow) := rw_ri_encoded_equal op key other in
          if same_op then
            let '(same_class, cw) := rw_ri_same_class_atomic state root owner in
            if same_class then
              let functions := map (rw_ri_match_on_atomic op sort value hole state) patterns in
              let '(out, mw) := rw_ri_match_children_atomic functions children assignment in
              (out, prefix + sw + ow + cw + 64 * S (length patterns) + mw)
            else (nil, prefix + sw + ow + cw)
          else (nil, prefix + sw + ow)
        else (nil, prefix + sw)
      | _ => (nil, prefix)
      end) candidates in
    (out, 64 + bucket_work + work)
  end.


Definition rw_ri_assignment_encode {H} (hole : rw_queue_encoder_adapter H)
    (entries : list (H * rw_id)) :=
  audit_list_encode (audit_pair_encode (rw_external_encoding_events hole) audit_positive_encode)
    entries.


Definition rw_ri_assignment_encode_work {H}
    (events : list (audit_list_event (H * rw_id)
      (audit_pair_event H rw_id nat (audit_basic_encoding_event positive)))) : nat :=
  audit_list_events_work
    (audit_pair_events_work rw_external_events_work audit_basic_encoding_work) events.


Fixpoint rw_ri_assignment_table_atomic {H} (hole : rw_queue_encoder_adapter H)
    (results : list (rw_assignment H)) :
    Map.t (list (H * rw_id)) (rw_assignment H) * nat :=
  match results with
  | nil => (Map.empty, 64)
  | assignment :: rest =>
    let '(table, tail_work) := rw_ri_assignment_table_atomic hole rest in
    let '(entries, enumeration) := audit_map_elements assignment in
    let '(out, insertion) := audit_map_set (rw_ri_assignment_encode hole) entries assignment
    table in
    (out, 64 + tail_work + audit_elements_work enumeration +
      audit_map_source_work rw_ri_assignment_encode_work insertion)
  end.


Definition rw_ri_distinct_assignments_atomic {H} (hole : rw_queue_encoder_adapter H)
    (results : list (rw_assignment H)) : list (rw_assignment H) * nat :=
  let '(table, table_work) := rw_ri_assignment_table_atomic hole results in
  let '(entries, enumeration) := audit_map_elements table in
  (map snd entries, 64 + table_work + audit_elements_work enumeration + 64 * S (length entries)).


Definition rw_ri_match_atomic {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (hole : rw_queue_encoder_adapter H) (state : rw_index_state K Sort V)
    (root : rw_id) (pattern : rw_pattern K Sort V H) : list (rw_assignment H) * nat :=
  let '(raw, match_work) := rw_ri_match_on_atomic op sort value hole state pattern root Map.empty in
  let '(out, distinct_work) := rw_ri_distinct_assignments_atomic hole raw in
  (out, 64 + match_work + distinct_work).

(** Matching preserves the plain matcher, including canonical duplicate-removal order. *)

(** This statement fixes the ri match erases statement contract. *)
Definition rw_ri_match_erases_statement : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H) state root pattern,
  (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
  (forall s, fst (rw_queue_encoder_run sort s) = encode ES s) ->
  (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
  (forall h, fst (rw_queue_encoder_run hole h) = encode EH h) ->
  fst (rw_ri_match_atomic op sort value hole state root pattern) =
    rw_view_match EK ES EV EH (rw_snapshot_base (rw_index_view EK ES EV state)) root pattern.
```

## Galois.Rewrite.RewriteAuditSharedReference

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditSharedReference.v`.

```rocq
(** * RewriteAuditSharedReference

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
Import List.ListNotations.

Inductive rw_shared_node (K Sort V : Type) : Type :=
  | RWSharedVar : Sort -> V -> rw_shared_node K Sort V
  | RWSharedApp : Sort -> K -> list positive -> rw_shared_node K Sort V.

Record rw_shared_tree (K Sort V : Type) := RwSharedTree {
  rw_shared_root : positive;
  rw_shared_nodes : Map.t positive (rw_shared_node K Sort V)
}.

Definition rw_shared_wf {K Sort V} (dag : rw_shared_tree K Sort V) : Prop :=
  Map.wf positive_encoding (rw_shared_nodes K Sort V dag) /\
  (exists node, Map.get positive_encoding (rw_shared_root K Sort V dag)
    (rw_shared_nodes K Sort V dag) = Some node) /\
  exists rank : positive -> nat,
    forall id s op children,
      Map.get positive_encoding id (rw_shared_nodes K Sort V dag) =
        Some (RWSharedApp K Sort V s op children) ->
      forall child, In child children ->
        (exists node, Map.get positive_encoding child (rw_shared_nodes K Sort V dag) = Some node) /\
        rank child < rank id.



Inductive rw_shared_validation_call (K Sort V : Type) : Type :=
  | RWSharedEnumerate : Trie.t (positive * rw_shared_node K Sort V) ->
      list (positive * (positive * rw_shared_node K Sort V)) ->
      list (audit_elements_event (positive * rw_shared_node K Sort V)) ->
    rw_shared_validation_call K Sort V
  | RWSharedKeyCheck : positive -> positive -> bool -> rw_shared_validation_call K Sort V
  | RWSharedRootRead : positive -> Trie.t (positive * rw_shared_node K Sort V) ->
      option (rw_shared_node K Sort V) -> rw_shared_validation_call K Sort V
  | RWSharedLength : nat -> audit_trace unit -> rw_shared_validation_call K Sort V
  | RWSharedReadyRead : positive -> FinSet.t positive -> option unit -> rw_shared_validation_call
    K Sort V
  | RWSharedReadyAdd : positive -> FinSet.t positive -> FinSet.t positive ->
    rw_shared_validation_call K Sort V.
Arguments RWSharedEnumerate {K Sort V}.
Arguments RWSharedKeyCheck {K Sort V}.
Arguments RWSharedRootRead {K Sort V}.
Arguments RWSharedLength {K Sort V}.
Arguments RWSharedReadyRead {K Sort V}.
Arguments RWSharedReadyAdd {K Sort V}.


Definition rw_shared_validation_event_cost {K Sort V}
    (event : audit_event (rw_shared_validation_call K Sort V)) : nat :=
  match event with
  | AuditCall (RWSharedEnumerate _ _ events) => 1 + audit_elements_work events
  | AuditCall (RWSharedKeyCheck p q _) =>
      1 + audit_positive_eqb_source_work (snd (audit_positive_eqb p q))
  | AuditCall (RWSharedRootRead id input _) => 2 + audit_trie_get_source_work id input
  | AuditCall (RWSharedLength _ trace) => 1 + audit_work trace
  | AuditCall (RWSharedReadyRead id input _) => 2 + audit_trie_get_source_work id input
  | AuditCall (RWSharedReadyAdd id input _) => 2 + audit_trie_update_source_work id (Some (id,
    tt)) input
  | _ => 1
  end.


Definition rw_shared_validation_trace_cost {K Sort V}
    (trace : audit_trace (rw_shared_validation_call K Sort V)) : nat :=
  fold_right (fun event total => rw_shared_validation_event_cost event + total) 0 trace.


Fixpoint rw_shared_length_atomic {A} (xs : list A) : nat * audit_trace unit :=
  match xs with
  | nil => (0, [AuditCase 751 []; AuditConstruct 752 []])
  | _ :: rest => let '(n, trace) := rw_shared_length_atomic rest in
    (S n, [AuditCase 753 []; AuditArithmetic 754 []] ++ trace ++ [AuditConstruct 755 []])
  end.


Fixpoint rw_shared_children_ready {K Sort V} (children : list positive) (ready : FinSet.t
    positive) :
    bool * audit_trace (rw_shared_validation_call K Sort V) :=
  match children with
  | nil => (true, [AuditCase 720 []; AuditConstruct 721 []])
  | child :: rest =>
    let found := Map.code_get child ready in
    let present := match found with Some _ => true | None => false end in
    let '(tail, trace) := rw_shared_children_ready rest ready in
    let '(answer, bool_trace) := if present then (tail, [AuditCase 724 []])
      else (false, [AuditCase 724 []; AuditConstruct 745 []]) in
    (answer, [AuditCase 722 []; AuditCall (RWSharedReadyRead child ready found); AuditCase 723
    []] ++
      trace ++ bool_trace)
  end.


Fixpoint rw_shared_validation_pass {K Sort V}
    (entries : list (positive * (positive * rw_shared_node K Sort V))) (ready : FinSet.t positive) :
    FinSet.t positive * audit_trace (rw_shared_validation_call K Sort V) :=
  match entries with
  | nil => (ready, [AuditCase 725 []])
  | (_, (id, node)) :: rest =>
    let '(is_ready, child_trace) := match node with
      | RWSharedVar _ _ _ _ _ => (true, [AuditCase 726 []; AuditConstruct 727 []])
      | RWSharedApp _ _ _ _ _ children =>
        let '(out, trace) := rw_shared_children_ready children ready in (out, AuditCase 746 [] ::
    trace)
      end in
    if is_ready then
      let updated := Trie.set id (id, tt) ready in
      let '(out, tail_trace) := rw_shared_validation_pass rest updated in
      (out, [AuditCase 728 []] ++ child_trace ++ [AuditCase 729 [];
        AuditCall (RWSharedReadyAdd id ready updated)] ++ tail_trace)
    else
      let '(out, tail_trace) := rw_shared_validation_pass rest ready in
      (out, [AuditCase 728 []] ++ child_trace ++ [AuditCase 730 []] ++ tail_trace)
  end.


Fixpoint rw_shared_validation_rounds {K Sort V} (fuel : nat)
    (entries : list (positive * (positive * rw_shared_node K Sort V))) (ready : FinSet.t positive) :
    FinSet.t positive * audit_trace (rw_shared_validation_call K Sort V) :=
  match fuel with
  | 0 => (ready, [AuditCase 731 []])
  | S rest => let '(next, pass_trace) := rw_shared_validation_pass entries ready in
    let '(out, tail_trace) := rw_shared_validation_rounds rest entries next in
    (out, [AuditCase 732 []] ++ pass_trace ++ tail_trace)
  end.


Fixpoint rw_shared_validation_keys {K Sort V}
    (entries : list (positive * (positive * rw_shared_node K Sort V))) :
    bool * audit_trace (rw_shared_validation_call K Sort V) :=
  match entries with
  | nil => (true, [AuditCase 733 []; AuditConstruct 734 []])
  | (position, (id, _)) :: rest =>
    let same := Pos.eqb position id in
    let '(tail, trace) := rw_shared_validation_keys rest in
    let '(answer, bool_trace) := if same then (tail, [AuditCase 736 []])
      else (false, [AuditCase 736 []; AuditConstruct 747 []]) in
    (answer, [AuditCase 735 []; AuditCall (RWSharedKeyCheck position id same)] ++ trace ++
    bool_trace)
  end.


Fixpoint rw_shared_validation_all_ready {K Sort V}
    (entries : list (positive * (positive * rw_shared_node K Sort V))) (ready : FinSet.t positive) :
    bool * audit_trace (rw_shared_validation_call K Sort V) :=
  match entries with
  | nil => (true, [AuditCase 737 []; AuditConstruct 738 []])
  | (_, (id, _)) :: rest =>
    let found := Map.code_get id ready in
    let present := match found with Some _ => true | None => false end in
    let '(tail, trace) := rw_shared_validation_all_ready rest ready in
    let '(answer, bool_trace) := if present then (tail, [AuditCase 741 []])
      else (false, [AuditCase 741 []; AuditConstruct 748 []]) in
    (answer, [AuditCase 739 []; AuditCall (RWSharedReadyRead id ready found); AuditCase 740 []] ++
      trace ++ bool_trace)
  end.


Definition rw_shared_validate_atomic {K Sort V} (dag : rw_shared_tree K Sort V) :
    bool * audit_trace (rw_shared_validation_call K Sort V) :=
  let nodes := rw_shared_nodes K Sort V dag in
  let '(entries, enum_trace) := audit_trie_elements nodes in
  let root := rw_shared_root K Sort V dag in
  let root_found := Map.code_get root nodes in
  let root_ok := match root_found with Some _ => true | None => false end in
  let '(keys_ok, key_trace) := rw_shared_validation_keys entries in
  let '(count, length_trace) := rw_shared_length_atomic entries in
  let '(ready, round_trace) := rw_shared_validation_rounds count entries FinSet.empty in
  let '(all_ok, all_trace) := rw_shared_validation_all_ready entries ready in
  let '(both, first_bool_trace) := if root_ok then (keys_ok, [AuditCase 743 []])
    else (false, [AuditCase 743 []; AuditConstruct 749 []]) in
  let '(answer, second_bool_trace) := if both then (all_ok, [AuditCase 744 []])
    else (false, [AuditCase 744 []; AuditConstruct 750 []]) in
  (answer,
    [AuditCall (RWSharedEnumerate nodes entries enum_trace); AuditCall (RWSharedRootRead root
    nodes root_found);
     AuditCase 742 []] ++ key_trace ++ [AuditCall (RWSharedLength count length_trace)] ++
     round_trace ++ all_trace ++ first_bool_trace ++ second_bool_trace).


Fixpoint rw_shared_children_ready_value (children : list positive) (ready : FinSet.t positive) :
    bool :=
  match children with
  | nil => true
  | child :: rest =>
    let present := match Map.code_get child ready with Some _ => true | None => false end in
    present && rw_shared_children_ready_value rest ready
  end.


Fixpoint rw_shared_validation_pass_value {K Sort V}
    (entries : list (positive * (positive * rw_shared_node K Sort V))) (ready : FinSet.t positive) :
    FinSet.t positive :=
  match entries with
  | nil => ready
  | (_, (id, node)) :: rest =>
    let is_ready := match node with
      | RWSharedVar _ _ _ _ _ => true
      | RWSharedApp _ _ _ _ _ children => rw_shared_children_ready_value children ready
      end in
    rw_shared_validation_pass_value rest (if is_ready then Trie.set id (id, tt) ready else ready)
  end.


Fixpoint rw_shared_validation_rounds_value {K Sort V} (fuel : nat)
    (entries : list (positive * (positive * rw_shared_node K Sort V))) (ready : FinSet.t positive) :
    FinSet.t positive :=
  match fuel with
  | 0 => ready
  | S rest => rw_shared_validation_rounds_value rest entries (rw_shared_validation_pass_value
    entries ready)
  end.


Fixpoint rw_shared_validation_keys_value {K Sort V}
    (entries : list (positive * (positive * rw_shared_node K Sort V))) : bool :=
  match entries with nil => true | (position, (id, _)) :: rest =>
    Pos.eqb position id && rw_shared_validation_keys_value rest end.


Fixpoint rw_shared_validation_all_ready_value {K Sort V}
    (entries : list (positive * (positive * rw_shared_node K Sort V))) (ready : FinSet.t
    positive) : bool :=
  match entries with
  | nil => true
  | (_, (id, _)) :: rest =>
    let present := match Map.code_get id ready with Some _ => true | None => false end in
    present && rw_shared_validation_all_ready_value rest ready
  end.


Definition rw_shared_validate {K Sort V} (dag : rw_shared_tree K Sort V) : bool :=
  let nodes := rw_shared_nodes K Sort V dag in
  let entries := Trie.elements nodes in
  let root_ok := match Map.code_get (rw_shared_root K Sort V dag) nodes with Some _ => true |
    None => false end in
  let keys_ok := rw_shared_validation_keys_value entries in
  let ready := rw_shared_validation_rounds_value (length entries) entries FinSet.empty in
  let all_ok := rw_shared_validation_all_ready_value entries ready in
  root_ok && keys_ok && all_ok.


Fixpoint rw_shared_children_bits (children : list positive) : nat :=
  match children with nil => 0 | id :: rest => S (Pos.size_nat id) + rw_shared_children_bits rest
    end.


(** This statement fixes the shared validate spec contract. *)
Definition rw_shared_validate_spec_contract : Prop := forall K Sort V (dag : rw_shared_tree K
    Sort V),
  rw_shared_validate dag = true <-> rw_shared_wf dag.

(** This statement fixes the shared validate atomic erases contract. *)
Definition rw_shared_validate_atomic_erases_contract : Prop := forall K Sort V (dag :
    rw_shared_tree K Sort V),
  fst (rw_shared_validate_atomic dag) = rw_shared_validate dag.

Inductive rw_shared_unfold_call (K Sort V : Type) : Type :=
  | RWUnfoldValidate : bool -> audit_trace (rw_shared_validation_call K Sort V) ->
    rw_shared_unfold_call K Sort V
  | RWUnfoldEnumerate : Trie.t (positive * rw_shared_node K Sort V) ->
      list (positive * (positive * rw_shared_node K Sort V)) ->
      list (audit_elements_event (positive * rw_shared_node K Sort V)) -> rw_shared_unfold_call K
    Sort V
  | RWUnfoldLength : nat -> audit_trace unit -> rw_shared_unfold_call K Sort V
  | RWUnfoldRead : positive -> Trie.t (positive * rw_shared_node K Sort V) ->
      option (rw_shared_node K Sort V) -> rw_shared_unfold_call K Sort V.
Arguments RWUnfoldValidate {K Sort V}.
Arguments RWUnfoldEnumerate {K Sort V}.
Arguments RWUnfoldLength {K Sort V}.
Arguments RWUnfoldRead {K Sort V}.


Definition rw_shared_unfold_event_cost {K Sort V} (event : audit_event (rw_shared_unfold_call K
    Sort V)) : nat :=
  match event with
  | AuditCall (RWUnfoldValidate _ trace) => 1 + rw_shared_validation_trace_cost trace
  | AuditCall (RWUnfoldEnumerate _ _ trace) => 1 + audit_elements_work trace
  | AuditCall (RWUnfoldLength _ trace) => 1 + audit_work trace
  | AuditCall (RWUnfoldRead id nodes _) => 2 + audit_trie_get_source_work id nodes
  | _ => 1
  end.

Definition rw_shared_unfold_trace_cost {K Sort V} (trace : audit_trace (rw_shared_unfold_call K
    Sort V)) : nat :=
  fold_right (fun event total => rw_shared_unfold_event_cost event + total) 0 trace.


Fixpoint rw_shared_unfold_fuel_atomic {K Sort V} (fuel : nat) (dag : rw_shared_tree K Sort V)
    (id : positive) : option (rw_term K Sort V) * audit_trace (rw_shared_unfold_call K Sort V) :=
  match fuel with
  | 0 => (None, [AuditCase 760 []; AuditConstruct 761 []])
  | S rest =>
    let nodes := rw_shared_nodes K Sort V dag in
    let found := Map.code_get id nodes in
    match found with
    | None => (None, [AuditCase 762 []; AuditCall (RWUnfoldRead id nodes None);
        AuditCase 763 []; AuditConstruct 764 []])
    | Some (RWSharedVar _ _ _ sort value) =>
      (Some (RWVar sort value), [AuditCase 762 []; AuditCall (RWUnfoldRead id nodes found);
        AuditCase 765 []; AuditConstruct 766 []; AuditConstruct 767 []])
    | Some (RWSharedApp _ _ _ sort op children) =>
      let fix visit (ids : list positive) :
          option (list (rw_term K Sort V)) * audit_trace (rw_shared_unfold_call K Sort V) :=
        match ids with
        | nil => (Some nil, [AuditCase 768 []; AuditConstruct 769 []; AuditConstruct 770 []])
        | child :: tail =>
          let '(head, ht) := rw_shared_unfold_fuel_atomic rest dag child in
          match head with
          | None => (None, [AuditCase 771 []] ++ ht ++ [AuditCase 772 []; AuditConstruct 773 []])
          | Some head_tree =>
            let '(others, ot) := visit tail in
            match others with
            | None => (None, [AuditCase 771 []] ++ ht ++ [AuditCase 774 []] ++ ot ++
                [AuditCase 775 []; AuditConstruct 776 []])
            | Some tail_trees => (Some (head_tree :: tail_trees), [AuditCase 771 []] ++ ht ++
                [AuditCase 774 []] ++ ot ++ [AuditCase 777 []; AuditConstruct 778 [];
    AuditConstruct 779 []])
            end
          end
        end in
      let '(out, trace) := visit children in
      match out with
      | None => (None, [AuditCase 762 []; AuditCall (RWUnfoldRead id nodes found); AuditCase 780
    []] ++
          trace ++ [AuditCase 781 []; AuditConstruct 782 []])
      | Some trees => (Some (RWApp sort op trees),
          [AuditCase 762 []; AuditCall (RWUnfoldRead id nodes found); AuditCase 780 []] ++ trace ++
          [AuditCase 783 []; AuditConstruct 784 []; AuditConstruct 785 []])
      end
    end
  end.


Definition rw_shared_unfold_atomic {K Sort V} (dag : rw_shared_tree K Sort V) :
    option (rw_term K Sort V) * audit_trace (rw_shared_unfold_call K Sort V) :=
  let '(valid, valid_trace) := rw_shared_validate_atomic dag in
  if valid then
    let nodes := rw_shared_nodes K Sort V dag in
    let '(entries, enum_trace) := audit_trie_elements nodes in
    let '(count, length_trace) := rw_shared_length_atomic entries in
    let '(out, trace) := rw_shared_unfold_fuel_atomic (S count) dag (rw_shared_root K Sort V dag) in
    (out, [AuditCall (RWUnfoldValidate valid valid_trace); AuditCase 786 [];
      AuditCall (RWUnfoldEnumerate nodes entries enum_trace); AuditCall (RWUnfoldLength count
    length_trace);
      AuditConstruct 787 []] ++ trace)
  else (None, [AuditCall (RWUnfoldValidate valid valid_trace); AuditCase 788 []; AuditConstruct
    789 []]).


Fixpoint rw_shared_unfold_fuel_value {K Sort V} (fuel : nat) (dag : rw_shared_tree K Sort V)
    (id : positive) : option (rw_term K Sort V) :=
  match fuel with
  | 0 => None
  | S rest =>
    match Map.code_get id (rw_shared_nodes K Sort V dag) with
    | None => None
    | Some (RWSharedVar _ _ _ sort value) => Some (RWVar sort value)
    | Some (RWSharedApp _ _ _ sort op children) =>
      let fix visit (ids : list positive) : option (list (rw_term K Sort V)) :=
        match ids with
        | nil => Some nil
        | child :: tail => match rw_shared_unfold_fuel_value rest dag child with
          | None => None
          | Some head => match visit tail with
            | None => None
            | Some tails => Some (head :: tails)
            end
          end
        end in
      match visit children with None => None | Some trees => Some (RWApp sort op trees) end
    end
  end.


Definition rw_shared_unfold {K Sort V} (dag : rw_shared_tree K Sort V) : option (rw_term K Sort
    V) :=
  if rw_shared_validate dag then
    let nodes := rw_shared_nodes K Sort V dag in
    let count := length (Trie.elements nodes) in
    rw_shared_unfold_fuel_value (S count) dag (rw_shared_root K Sort V dag)
  else None.


(** This statement fixes the shared unfold total statement contract. *)
Definition rw_shared_unfold_total_statement : Prop :=
  forall K Sort V (dag : rw_shared_tree K Sort V), rw_shared_wf dag -> exists tree,
    rw_shared_unfold dag = Some tree.

(** This statement fixes the shared unfold valid statement contract. *)
Definition rw_shared_unfold_valid_statement : Prop :=
  forall K Sort V (dag : rw_shared_tree K Sort V) tree, rw_shared_unfold dag = Some tree ->
    rw_shared_wf dag.

(** This statement fixes the shared unfold erases statement contract. *)
Definition rw_shared_unfold_erases_statement : Prop :=
  forall K Sort V (dag : rw_shared_tree K Sort V),
    fst (rw_shared_unfold_atomic dag) = rw_shared_unfold dag.

(** This statement fixes the shared unfold total contract. *)
Definition rw_shared_unfold_total_contract : Prop := rw_shared_unfold_total_statement.

(** This statement fixes the shared unfold valid contract. *)
Definition rw_shared_unfold_valid_contract : Prop := rw_shared_unfold_valid_statement.

(** This statement fixes the shared unfold atomic erases contract. *)
Definition rw_shared_unfold_atomic_erases_contract : Prop := rw_shared_unfold_erases_statement.
```

## Galois.Rewrite.RewriteAuditSharedCompare

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditSharedCompare.v`.

```rocq
(** * RewriteAuditSharedCompare

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditQueueReference RewriteAuditSharedReference.
Import List.ListNotations.

Definition rw_rd_memo := Map.t (positive * positive) comparison.


Definition rw_rd_pair_encode
    := audit_pair_encode audit_positive_encode audit_positive_encode.


Definition rw_rd_pair_encoding_work
    (trace : list (audit_pair_event positive positive

    (audit_basic_encoding_event positive) (audit_basic_encoding_event positive))) : nat :=

    audit_pair_events_work audit_basic_encoding_work audit_basic_encoding_work
    trace.


Definition rw_rd_memo_get (p q : positive) (memo : rw_rd_memo) : option comparison *
    nat :=
  let '(answer, trace) := audit_map_get rw_rd_pair_encode (p, q) memo in
  (answer,
    64 + audit_map_source_work rw_rd_pair_encoding_work trace).


Definition rw_rd_memo_set (p q
    : positive) (answer : comparison) (memo : rw_rd_memo) :
    rw_rd_memo * nat :=
  let '(out,
    trace) := audit_map_set rw_rd_pair_encode (p, q) answer memo in
  (out, 64 +
    audit_map_source_work rw_rd_pair_encoding_work trace).


Definition rw_rd_node_get {K Sort V}
    (nodes : Map.t positive (rw_shared_node K Sort V))
    (id : positive) : option
    (rw_shared_node K Sort V) * nat :=
  let '(out, trace) := audit_map_get
    audit_positive_encode id nodes in
  (out, 64 + audit_map_source_work
    audit_basic_encoding_work trace).


Fixpoint rw_rd_positive_compare_cont (otherwise :
    comparison) (p q : positive) :
    comparison * nat :=
  match p, q with
  | xH, xH =>
    (otherwise, 64)
  | xH, xO _ => (Lt, 64)
  | xH, xI _ => (Lt, 64)
  | xO _, xH => (Gt, 64)

    | xI _, xH => (Gt, 64)
  | xO a, xO b => let '(answer, work) := rw_rd_positive_compare_cont
    otherwise a b in
      (answer, 64 + work)
  | xI a, xI b => let '(answer, work) :=
    rw_rd_positive_compare_cont otherwise a b in
      (answer, 64 + work)
  | xO a, xI b => let
    '(answer, work) := rw_rd_positive_compare_cont Lt a b in
      (answer, 64 + work)
  | xI a,
    xO b => let '(answer, work) := rw_rd_positive_compare_cont Gt a b in
      (answer, 64 +
    work)
  end.


Fixpoint rw_rd_headers_compare (xs ys : list positive) : comparison * nat :=

    match xs, ys with
  | nil, nil => (Eq, 64)
  | nil, _ :: _ => (Lt, 64)
  | _ :: _, nil =>
    (Gt, 64)
  | x :: rest, y :: tail =>
    let '(head, head_work) :=
    rw_rd_positive_compare_cont Eq x y in
    match head with
    | Eq => let '(answer,
    tail_work) := rw_rd_headers_compare rest tail in
        (answer, 64 + head_work +
    tail_work)
    | _ => (head, 64 + head_work)
    end
  end.


Definition rw_rd_children {K
    Sort V} (node : rw_shared_node K Sort V) : list positive :=
  match node with
  |
    RWSharedVar _ _ _ _ _ => nil
  | RWSharedApp _ _ _ _ _ children => children

    end.


Definition rw_rd_header {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort :
    rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (node :
    rw_shared_node K Sort V) : list positive * nat :=
  match node with
  | RWSharedVar _ _ _ ty
    v =>
    let '(s, sw) := rw_queue_encoder_run sort ty in
    let '(x, xw) :=
    rw_queue_encoder_run value v in
    ([1%positive; s; x; 1%positive], 64 + sw + xw)
  |
    RWSharedApp _ _ _ ty k children =>
    let '(s, sw) := rw_queue_encoder_run sort ty in

    let '(x, xw) := rw_queue_encoder_run op k in
    let '(arity, length_trace) :=
    rw_fuel_length children in
    let '(code, code_trace) := audit_nat_encode arity in

    ([2%positive; s; x; code],
      64 + sw + xw + audit_work length_trace +
    audit_nat_events_work code_trace)
  end.


Inductive rw_rd_compare_run {K Sort V} (op :
    rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value :
    rw_queue_encoder_adapter V)
    (left right : Map.t positive (rw_shared_node K Sort V)) :

     positive -> positive -> rw_rd_memo -> comparison -> rw_rd_memo -> nat -> Prop :=
  |
    RDRootCached : forall p q memo answer read_work,
      rw_rd_memo_get p q memo = (Some
    answer, read_work) ->
      rw_rd_compare_run op sort value left right p q memo answer memo
    (64 + read_work)
  | RDRootDifferent : forall p q memo a b header_a header_b answer

    read_work left_work right_work a_work b_work comparison_work memo' write_work,

    rw_rd_memo_get p q memo = (None, read_work) ->
      rw_rd_node_get left p = (Some a,
    left_work) ->
      rw_rd_node_get right q = (Some b, right_work) ->
      rw_rd_header op
    sort value a = (header_a, a_work) ->
      rw_rd_header op sort value b = (header_b, b_work)
    ->
      rw_rd_headers_compare header_a header_b = (answer, comparison_work) ->
      answer
    <> Eq ->
      rw_rd_memo_set p q answer memo = (memo', write_work) ->

    rw_rd_compare_run op sort value left right p q memo answer memo'
        (64 + read_work +
    left_work + right_work + a_work + b_work +
          comparison_work + write_work)
  |
    RDRootChildren : forall p q memo a b header_a header_b answer
      read_work left_work
    right_work a_work b_work comparison_work child_work
      child_memo memo' write_work,

    rw_rd_memo_get p q memo = (None, read_work) ->
      rw_rd_node_get left p = (Some a,
    left_work) ->
      rw_rd_node_get right q = (Some b, right_work) ->
      rw_rd_header op
    sort value a = (header_a, a_work) ->
      rw_rd_header op sort value b = (header_b, b_work)
    ->
      rw_rd_headers_compare header_a header_b = (Eq, comparison_work) ->

    rw_rd_compare_children_run op sort value left right
        (rw_rd_children a)
    (rw_rd_children b) memo answer child_memo child_work ->
      rw_rd_memo_set p q answer
    child_memo = (memo', write_work) ->
      rw_rd_compare_run op sort value left right p q
    memo answer memo'
        (64 + read_work + left_work + right_work + a_work + b_work +

        comparison_work + child_work + write_work)
with rw_rd_compare_children_run {K Sort V}
    (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value :
    rw_queue_encoder_adapter V)
    (left right : Map.t positive (rw_shared_node K Sort V)) :

     list positive -> list positive -> rw_rd_memo -> comparison -> rw_rd_memo -> nat -> Prop :=

     | RDChildrenEmpty : forall memo,
      rw_rd_compare_children_run op sort value left right
    nil nil memo Eq memo 64
  | RDChildrenLeftEmpty : forall y ys memo,

    rw_rd_compare_children_run op sort value left right nil (y :: ys) memo Lt memo 64
  |
    RDChildrenRightEmpty : forall x xs memo,
      rw_rd_compare_children_run op sort value left
    right (x :: xs) nil memo Gt memo 64
  | RDChildrenDifferent : forall x xs y ys memo answer
    next child_work,
      rw_rd_compare_run op sort value left right x y memo answer next
    child_work ->
      answer <> Eq ->
      rw_rd_compare_children_run op sort value left
    right
        (x :: xs) (y :: ys) memo answer next (64 + child_work)
  | RDChildrenEqual :
    forall x xs y ys memo middle final answer child_work tail_work,
      rw_rd_compare_run op
    sort value left right x y memo Eq middle child_work ->
      rw_rd_compare_children_run op
    sort value left right xs ys middle answer final tail_work ->

    rw_rd_compare_children_run op sort value left right
        (x :: xs) (y :: ys) memo answer
    final (64 + child_work + tail_work).


Inductive rw_shared_compare_run {K Sort V} (op :
    rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value :
    rw_queue_encoder_adapter V)
    (left right : rw_shared_tree K Sort V) : option bool -> nat
    -> Prop :=
  | RDCompareInvalid : forall lvalid rvalid lt rt,

    rw_shared_validate_atomic left = (lvalid, lt) ->
      rw_shared_validate_atomic right =
    (rvalid, rt) ->
      lvalid && rvalid = false ->
      rw_shared_compare_run op sort value
    left right None
        (64 + rw_shared_validation_trace_cost lt +
    rw_shared_validation_trace_cost rt)
  | RDCompareValid : forall lt rt memo answer work,

     rw_shared_validate_atomic left = (true, lt) ->
      rw_shared_validate_atomic right =
    (true, rt) ->
      rw_rd_compare_run op sort value (rw_shared_nodes K Sort V left)

    (rw_shared_nodes K Sort V right) (rw_shared_root K Sort V left)
        (rw_shared_root K
    Sort V right) Map.empty answer memo work ->
      rw_shared_compare_run op sort value left
    right
        (Some (match answer with Gt => false | _ => true end))
        (64 +
    rw_shared_validation_trace_cost lt + rw_shared_validation_trace_cost rt + work).

(** Every
    pair of stored graphs has exactly one result and charged source execution. *)

(** This statement fixes the rd compare total statement contract. *)
Definition rw_rd_compare_total_statement : Prop :=
  forall K Sort V (op : rw_queue_encoder_adapter K)

       (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V) left right,

    exists answer work, rw_shared_compare_run op sort value left right answer work.

(** Fixed
    operational runs agree on result and cost, including malformed-input rejection.
    *)

(** This statement fixes the rd compare unique statement contract. *)
Definition rw_rd_compare_unique_statement : Prop :=
  forall K Sort V (op :
    rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value :
    rw_queue_encoder_adapter V)
    left right first second first_work second_work,

    rw_shared_compare_run op sort value left right first first_work ->
  rw_shared_compare_run
    op sort value left right second second_work ->
  first = second /\ first_work = second_work.
```

## Galois.Rewrite.RewriteAuditSharedExtract

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditSharedExtract.v`.

```rocq
(** * RewriteAuditSharedExtract

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditQueueReference RewriteAuditSharedCompare
  RewriteAuditSharedReference.
Import List.ListNotations.

Fixpoint rw_rd_positive_add (a b : positive) : positive * nat :=
  match a, b with
  | xH, xH =>
    (xO xH, 64)
  | xH, xO y => (xI y, 64)
  | xH, xI y => let '(s, w) := rw_fuel_pos_succ y in
    (xO s, 64 + audit_work w)
  | xO x, xH => (xI x, 64)
  | xI x, xH => let '(s, w) :=
    rw_fuel_pos_succ x in (xO s, 64 + audit_work w)
  | xO x, xO y => let '(s, w) :=
    rw_rd_positive_add x y in (xO s, 64 + w)
  | xO x, xI y => let '(s, w) := rw_rd_positive_add
    x y in (xI s, 64 + w)
  | xI x, xO y => let '(s, w) := rw_rd_positive_add x y in (xI s, 64 +
    w)
  | xI x, xI y => let '(s, w) := rw_rd_positive_add x y in
      let '(t, tw) :=
    rw_fuel_pos_succ s in (xO t, 64 + w + audit_work tw)
  end.


Definition rw_rd_N_add (a b :
    N) : N * nat :=
  match a, b with
  | N0, _ => (b, 64)
  | _, N0 => (a, 64)
  | Npos x, Npos
    y => let '(s, w) := rw_rd_positive_add x y in (Npos s, 64 + w)
  end.


Definition rw_rd_N_compare (a b : N) : comparison * nat :=
  match a, b with
  | N0, N0 => (Eq, 64)
  |
    N0, _ => (Lt, 64)
  | _, N0 => (Gt, 64)
  | Npos x, Npos y => rw_rd_positive_compare_cont Eq
    x y
  end.


Fixpoint rw_rd_nat_to_N (n : nat) : N * nat :=
  match n with
  | 0 => (0%N,
    64)
  | S rest => let '(x, w) := rw_rd_nat_to_N rest in
      let '(out, aw) := rw_rd_N_add
    1%N x in (out, 64 + w + aw)
  end.


Record rw_rd_candidate := RwRdCandidate {

    rw_rd_pointer : positive;
  rw_rd_cost : N;
  rw_rd_size : N
}.


Record rw_rd_store (K Sort
    V : Type) := RwRdStore {
  rw_rd_nodes : Map.t positive (rw_shared_node K Sort V);

    rw_rd_next : positive
}.
Arguments RwRdStore {K Sort V}.
Arguments rw_rd_nodes {K Sort
    V}.
Arguments rw_rd_next {K Sort V}.


Definition rw_rd_table := Map.t rw_id
    rw_rd_candidate.


Definition rw_rd_candidate_get {K Sort V} (g : rw_graph K Sort V)

    (table : rw_rd_table) (id : rw_id) : option rw_rd_candidate * nat :=
  let '(root, rt) :=
    audit_map_get audit_positive_encode id (rw_class_roots g) in
  match root with
  | None =>
    (None, 64 + audit_map_source_work audit_basic_encoding_work rt)
  | Some r => let '(answer,
    add_trace) := audit_map_get audit_positive_encode r table in
      (answer, 64 +
    audit_map_source_work audit_basic_encoding_work rt +
        audit_map_source_work
    audit_basic_encoding_work add_trace)
  end.


Fixpoint rw_rd_gather {K Sort V} (g : rw_graph
    K Sort V) (table : rw_rd_table)
    (ids : list rw_id) : option (list positive * N * N) *
    nat :=
  match ids with
  | nil => (Some (nil, 0%N, 0%N), 64)
  | id :: rest =>
    let
    '(head, hw) := rw_rd_candidate_get g table id in
    let '(tail, tw) := rw_rd_gather g table
    rest in
    match head, tail with
    | Some c, Some (pointers, cost, size) =>
      let
    '(cost', cw) := rw_rd_N_add (rw_rd_cost c) cost in
      let '(size', sw) := rw_rd_N_add
    (rw_rd_size c) size in
      (Some (rw_rd_pointer c :: pointers, cost', size'), 64 + hw + tw
    + cw + sw)
    | _, _ => (None, 64 + hw + tw)
    end
  end.


Definition rw_rd_allocate {K
    Sort V} (node : rw_shared_node K Sort V)
    (cost size : N) (store : rw_rd_store K Sort V)
    :
    (rw_rd_candidate * rw_rd_store K Sort V) * nat :=
  let id := rw_rd_next store in

    let '(nodes, nt) := audit_map_set audit_positive_encode id node (rw_rd_nodes store) in
  let
    '(fresh, ft) := rw_fuel_pos_succ id in
  ((RwRdCandidate id cost size, RwRdStore nodes
    fresh),
    64 + audit_map_source_work audit_basic_encoding_work nt + audit_work
    ft).


Definition rw_rd_production {K Sort V} (vc : V -> nat * nat) (oc : K -> nat * nat)

    (g : rw_graph K Sort V) (old : rw_rd_table) (node : rw_node K Sort V)
    (store :
    rw_rd_store K Sort V) :
    (option rw_rd_candidate * rw_rd_store K Sort V) * nat :=
  match
    node with
  | RWNVar ty v =>
    let '(cost, callback_work) := vc v in
    let '(binary,
    conversion_work) := rw_rd_nat_to_N cost in
    let '((candidate, next), allocation_work) :=

         rw_rd_allocate (RWSharedVar K Sort V ty v) binary 1%N store in
    ((Some candidate,
    next), 64 + callback_work + conversion_work + allocation_work)
  | RWNApp ty op children =>

       let '(args, gather_work) := rw_rd_gather g old children in
    match args with
    | None
    => ((None, store), 64 + gather_work)
    | Some (pointers, child_cost, child_size) =>

    let '(cost, callback_work) := oc op in
      let '(binary, conversion_work) :=
    rw_rd_nat_to_N cost in
      let '(total, addition_work) := rw_rd_N_add binary child_cost
    in
      let '(size, size_work) := rw_rd_N_add 1%N child_size in
      let '((candidate,
    next), allocation_work) :=
        rw_rd_allocate (RWSharedApp K Sort V ty op pointers)
    total size store in
      ((Some candidate, next), 64 + gather_work + callback_work +
    conversion_work +
        addition_work + size_work + allocation_work)
    end

    end.


Inductive rw_rd_choose_run {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort :
    rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (store : rw_rd_store
    K Sort V) (old fresh : rw_rd_candidate) :
    rw_rd_candidate -> nat -> Prop :=
  |
    RDChooseCost : forall answer work,
      rw_rd_N_compare (rw_rd_cost old) (rw_rd_cost fresh)
    = (answer, work) ->
      answer <> Eq ->
      rw_rd_choose_run op sort value store old
    fresh
        (match answer with Lt => old | _ => fresh end) (64 + work)
  | RDChooseSize :
    forall cost_work answer work,
      rw_rd_N_compare (rw_rd_cost old) (rw_rd_cost fresh) =
    (Eq, cost_work) ->
      rw_rd_N_compare (rw_rd_size old) (rw_rd_size fresh) = (answer,
    work) ->
      answer <> Eq ->
      rw_rd_choose_run op sort value store old fresh

    (match answer with Lt => old | _ => fresh end) (64 + cost_work + work)
  | RDChooseCode :
    forall cost_work size_work answer work,
      rw_rd_N_compare (rw_rd_cost old) (rw_rd_cost
    fresh) = (Eq, cost_work) ->
      rw_rd_N_compare (rw_rd_size old) (rw_rd_size fresh) = (Eq,
    size_work) ->
      rw_shared_compare_run op sort value
        (RwSharedTree K Sort V
    (rw_rd_pointer old) (rw_rd_nodes store))
        (RwSharedTree K Sort V (rw_rd_pointer
    fresh) (rw_rd_nodes store))
        (Some answer) work ->
      rw_rd_choose_run op sort
    value store old fresh
        (if answer then old else fresh) (64 + cost_work + size_work +
    work).


Inductive rw_rd_insert_run {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort :
    rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (store : rw_rd_store
    K Sort V) (root : rw_id) (fresh : rw_rd_candidate)
    (table : rw_rd_table) : rw_rd_table
    -> nat -> Prop :=
  | RDInsertAbsent : forall rt out wt,
      audit_map_get
    audit_positive_encode root table = (None, rt) ->
      audit_map_set audit_positive_encode
    root fresh table = (out, wt) ->
      rw_rd_insert_run op sort value store root fresh table
    out
        (64 + audit_map_source_work audit_basic_encoding_work rt +

    audit_map_source_work audit_basic_encoding_work wt)
  | RDInsertPresent : forall rt old
    chosen choose_work out wt,
      audit_map_get audit_positive_encode root table = (Some old,
    rt) ->
      rw_rd_choose_run op sort value store old fresh chosen choose_work ->

    audit_map_set audit_positive_encode root chosen table = (out, wt) ->
      rw_rd_insert_run
    op sort value store root fresh table out
        (64 + audit_map_source_work
    audit_basic_encoding_work rt + choose_work +
          audit_map_source_work
    audit_basic_encoding_work wt).


Inductive rw_rd_round_run {K Sort V} (op :
    rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value :
    rw_queue_encoder_adapter V)
    (vc : V -> nat * nat) (oc : K -> nat * nat) (g : rw_graph K
    Sort V)
    (old : rw_rd_table) : list (rw_id * (rw_id * rw_node K Sort V)) ->

    rw_rd_table -> rw_rd_store K Sort V -> rw_rd_table -> rw_rd_store K Sort V -> nat -> Prop
    :=
  | RDRoundNil : forall table store,
      rw_rd_round_run op sort value vc oc g old nil
    table store table store 64
  | RDRoundSkip : forall id owner node rest table store root rt
    produced next pw out final tw,
      audit_map_get audit_positive_encode owner
    (rw_class_roots g) = (root, rt) ->
      rw_rd_production vc oc g old node store =
    ((produced, next), pw) ->
      (root = None \/ produced = None) ->
      rw_rd_round_run op
    sort value vc oc g old rest table next out final tw ->
      rw_rd_round_run op sort value
    vc oc g old ((id, (owner, node)) :: rest)
        table store out final
        (64 +
    audit_map_source_work audit_basic_encoding_work rt + pw + tw)
  | RDRoundInsert : forall id
    owner node rest table store root rt fresh next pw
      inserted iw out final tw,

    audit_map_get audit_positive_encode owner (rw_class_roots g) = (Some root, rt) ->

    rw_rd_production vc oc g old node store = ((Some fresh, next), pw) ->
      rw_rd_insert_run
    op sort value next root fresh table inserted iw ->
      rw_rd_round_run op sort value vc oc
    g old rest inserted next out final tw ->
      rw_rd_round_run op sort value vc oc g old
    ((id, (owner, node)) :: rest)
        table store out final
        (64 +
    audit_map_source_work audit_basic_encoding_work rt + pw + iw + tw).


Inductive rw_rd_rounds_run {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort :
    rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (vc : V -> nat *
    nat) (oc : K -> nat * nat) (g : rw_graph K Sort V)
    (entries : list (rw_id * (rw_id *
    rw_node K Sort V))) :
    positive -> rw_rd_table -> rw_rd_store K Sort V ->
    rw_rd_table
    -> rw_rd_store K Sort V -> nat -> Prop :=
  | RDRoundsOne : forall table store out final
    work,
      rw_rd_round_run op sort value vc oc g table entries table store out final work
    ->
      rw_rd_rounds_run op sort value vc oc g entries xH table store out final (64 +
    work)
  | RDRoundsEven : forall p table store middle ms out final first second,

    rw_rd_rounds_run op sort value vc oc g entries p table store middle ms first ->

    rw_rd_rounds_run op sort value vc oc g entries p middle ms out final second ->

    rw_rd_rounds_run op sort value vc oc g entries (xO p)
        table store out final (64 +
    first + second)
  | RDRoundsOdd : forall p table store next ns middle ms out final one first
    second,
      rw_rd_round_run op sort value vc oc g table entries table store next ns one
    ->
      rw_rd_rounds_run op sort value vc oc g entries p next ns middle ms first ->

    rw_rd_rounds_run op sort value vc oc g entries p middle ms out final second ->

    rw_rd_rounds_run op sort value vc oc g entries (xI p)
        table store out final (64 +
    one + first + second).



Inductive rw_shared_extract_run {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort :
    rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (vc : V -> nat *
    nat) (oc : K -> nat * nat) (g : rw_graph K Sort V) (root : rw_id) :
    option
    (rw_shared_tree K Sort V) -> nat -> Prop :=
  | RDExtractEmpty : forall lt,

    rw_fuel_length (rw_roots g) = (0, lt) ->
      rw_shared_extract_run op sort value vc oc g
    root None (64 + audit_work lt)
  | RDExtractMissing : forall n lt fuel ft entries et table
    store rounds_work lookup_work,
      rw_fuel_length (rw_roots g) = (S n, lt) ->

    rw_fuel_to_positive n = (fuel, ft) ->
      audit_map_elements (rw_nodes g) = (entries, et)
    ->
      rw_rd_rounds_run op sort value vc oc g entries fuel Map.empty
        (RwRdStore
    Map.empty 1%positive) table store rounds_work ->
      rw_rd_candidate_get g table root =
    (None, lookup_work) ->
      rw_shared_extract_run op sort value vc oc g root None

    (64 + audit_work lt + audit_work ft + audit_elements_work et +
          rounds_work +
    lookup_work)
  | RDExtractFound : forall n lt fuel ft entries et table store rounds_work
    candidate lookup_work,
      rw_fuel_length (rw_roots g) = (S n, lt) ->

    rw_fuel_to_positive n = (fuel, ft) ->
      audit_map_elements (rw_nodes g) = (entries, et)
    ->
      rw_rd_rounds_run op sort value vc oc g entries fuel Map.empty
        (RwRdStore
    Map.empty 1%positive) table store rounds_work ->
      rw_rd_candidate_get g table root =
    (Some candidate, lookup_work) ->
      rw_shared_extract_run op sort value vc oc g root

       (Some (RwSharedTree K Sort V (rw_rd_pointer candidate) (rw_rd_nodes store)))
        (64
    + audit_work lt + audit_work ft + audit_elements_work et +
          rounds_work +
    lookup_work).


Definition rw_rd_node_input_weight {K Sort V} (op : rw_queue_encoder_adapter
    K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (node
    : rw_shared_node K Sort V) : nat :=
  let '(header, work) := rw_rd_header op sort value node
    in
  S (work + fold_right (fun p n => Pos.size_nat p + n) 0 header +

    rw_shared_children_bits (rw_rd_children node)).


Definition rw_rd_graph_input_weight {K Sort
    V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value :
    rw_queue_encoder_adapter V)
    (dag : rw_shared_tree K Sort V) : nat :=
  let entries :=
    Map.elements (rw_shared_nodes K Sort V dag) in
  S (Pos.size_nat (rw_shared_root K Sort V
    dag) +
    fold_right (fun entry n => Pos.size_nat (fst entry) +

    rw_rd_node_input_weight op sort value (snd entry) + n) 0 entries +
    audit_trie_nodes
    (rw_shared_nodes K Sort V dag)).


Definition rw_rd_compare_budget {K Sort V} (op :
    rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value :
    rw_queue_encoder_adapter V)
    (left right : rw_shared_tree K Sort V) : nat :=
  Nat.pow
    (1024 * S (rw_rd_graph_input_weight op sort value left +
    rw_rd_graph_input_weight op
    sort value right)) 8.

(** Every completed comparator run is bounded by the stored inputs
    and actual encoder bodies. *)

(** This statement fixes the rd compare bound statement contract. *)
Definition rw_rd_compare_bound_statement : Prop :=
  forall K
    Sort V (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value :
    rw_queue_encoder_adapter V)
    left right answer work,
  rw_shared_compare_run op sort
    value left right answer work ->
  work <= rw_rd_compare_budget op sort value left
    right.

(** Extraction returns exactly the existing selected tree after separately charged
    unfolding. *)

(** This statement fixes the rd extract agrees statement contract. *)
Definition rw_rd_extract_agrees_statement : Prop :=
  forall K Sort V (EK :
    encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (vc : V ->
    nat * nat) (oc : K -> nat * nat)
    (sig : rw_signature K Sort V) g root answer work,

    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
  (forall ty, fst
    (rw_queue_encoder_run sort ty) = encode ES ty) ->
  (forall v, fst (rw_queue_encoder_run
    value v) = encode EV v) ->
  rw_graph_wf sig g ->
  rw_shared_extract_run op sort value vc
    oc g root answer work ->
  match answer, rw_extract_tree EK ES EV (fun v => fst (vc v))

     (fun k => fst (oc k)) g root with
  | None, None => True
  | Some dag, Some tree =>
    rw_shared_wf dag /\ rw_shared_unfold dag = Some tree
  | _, _ => False
  end.

(** The fully
    fixed extraction relation has a result for every finite graph. *)

(** This statement fixes the rd extract total statement contract. *)
Definition rw_rd_extract_total_statement : Prop :=
  forall K Sort V (op : rw_queue_encoder_adapter K)

       (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (vc : V
    -> nat * nat) (oc : K -> nat * nat) g root,
  exists answer work, rw_shared_extract_run op
    sort value vc oc g root answer work.

(** The relational source equations determine both the
    selected shared result and its work. *)

(** This statement fixes the rd extract unique statement contract. *)
Definition rw_rd_extract_unique_statement : Prop :=

     forall K Sort V (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter
    Sort) (value : rw_queue_encoder_adapter V)
    (vc : V -> nat * nat) (oc : K -> nat * nat) g
    root first second fw sw,
  rw_shared_extract_run op sort value vc oc g root first fw ->

    rw_shared_extract_run op sort value vc oc g root second sw -> first = second /\ fw = sw.
```

## Galois.Rewrite.RewriteAuditSharedObservers

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditSharedObservers.v`.

```rocq
(** * RewriteAuditSharedObservers

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditQueueReference RewriteAuditSharedExtract
  RewriteAuditSharedReference.
Import List.ListNotations.

Fixpoint rw_rd_shared_gather (table : rw_rd_table) (ids : list positive) :
    option (N * N) *
    nat :=
  match ids with
  | nil => (Some (0%N, 0%N), 64)
  | id :: rest =>
    let '(head,
    ht) := audit_map_get audit_positive_encode id table in
    let '(tail, tw) :=
    rw_rd_shared_gather table rest in
    let hw := audit_map_source_work
    audit_basic_encoding_work ht in
    match head, tail with
    | Some c, Some (cost, size)
    =>
      let '(cost', cw) := rw_rd_N_add (rw_rd_cost c) cost in
      let '(size', sw) :=
    rw_rd_N_add (rw_rd_size c) size in
      (Some (cost', size'), 64 + hw + tw + cw + sw)
    |
    _, _ => (None, 64 + hw + tw)
    end
  end.


Definition rw_rd_scalar_node {K Sort V} (vc : V
    -> nat * nat) (oc : K -> nat * nat)
    (table : rw_rd_table) (id : positive) (node :
    rw_shared_node K Sort V) :
    option rw_rd_candidate * nat :=
  match node with
  |
    RWSharedVar _ _ _ _ v =>
    let '(cost, callback_work) := vc v in
    let '(binary,
    conversion_work) := rw_rd_nat_to_N cost in
    (Some (RwRdCandidate id binary 1%N), 64 +
    callback_work + conversion_work)
  | RWSharedApp _ _ _ _ op children =>
    let '(args,
    gather_work) := rw_rd_shared_gather table children in
    match args with
    | None =>
    (None, 64 + gather_work)
    | Some (child_cost, child_size) =>
      let '(cost,
    callback_work) := oc op in
      let '(binary, conversion_work) := rw_rd_nat_to_N cost in

       let '(total, addition_work) := rw_rd_N_add binary child_cost in
      let '(size,
    size_work) := rw_rd_N_add 1%N child_size in
      (Some (RwRdCandidate id total size), 64 +
    gather_work + callback_work +
        conversion_work + addition_work + size_work)
    end

    end.


Fixpoint rw_rd_scalar_pass {K Sort V} (vc : V -> nat * nat) (oc : K -> nat * nat)

    (old : rw_rd_table) (entries : list (positive * rw_shared_node K Sort V))
    (acc :
    rw_rd_table) : rw_rd_table * nat :=
  match entries with
  | nil => (acc, 64)
  | (id, node)
    :: rest =>
    let '(candidate, nw) := rw_rd_scalar_node vc oc old id node in
    match
    candidate with
    | None => let '(out, tw) := rw_rd_scalar_pass vc oc old rest acc in

      (out, 64 + nw + tw)
    | Some c =>
      let '(next, wt) := audit_map_set
    audit_positive_encode id c acc in
      let '(out, tw) := rw_rd_scalar_pass vc oc old rest
    next in
      (out, 64 + nw + audit_map_source_work audit_basic_encoding_work wt + tw)

    end
  end.


Fixpoint rw_rd_scalar_rounds {K Sort V} (vc : V -> nat * nat) (oc : K -> nat *
    nat)
    (entries : list (positive * rw_shared_node K Sort V)) (rounds : positive)

    (table : rw_rd_table) : rw_rd_table * nat :=
  match rounds with
  | xH => let '(out, work)
    := rw_rd_scalar_pass vc oc table entries table in
      (out, 64 + work)
  | xO p => let
    '(middle, mw) := rw_rd_scalar_rounds vc oc entries p table in
      let '(out, tw) :=
    rw_rd_scalar_rounds vc oc entries p middle in
      (out, 64 + mw + tw)
  | xI p => let
    '(first, fw) := rw_rd_scalar_pass vc oc table entries table in
      let '(middle, mw) :=
    rw_rd_scalar_rounds vc oc entries p first in
      let '(out, tw) := rw_rd_scalar_rounds vc
    oc entries p middle in
      (out, 64 + fw + mw + tw)
  end.


Definition rw_rd_scalar_observe {K Sort V} (vc : V -> nat * nat) (oc : K -> nat * nat)
    (dag :
    rw_shared_tree K Sort V) : option (N * N) * nat :=
  let '(valid, vt) :=
    rw_shared_validate_atomic dag in
  let vw := rw_shared_validation_trace_cost vt in
  if
    valid then
    let '(entries, et) := audit_map_elements (rw_shared_nodes K Sort V dag) in

     let '(count, lt) := rw_fuel_length entries in
    let setup := 64 + vw +
    audit_elements_work et + audit_work lt in
    match count with
    | 0 => (None, setup)

    | S rest =>
      let '(fuel, ft) := rw_fuel_to_positive rest in
      let '(table, tw) :=
    rw_rd_scalar_rounds vc oc entries fuel Map.empty in
      let '(found, rt) := audit_map_get
    audit_positive_encode (rw_shared_root K Sort V dag) table in
      (option_map (fun c =>
    (rw_rd_cost c, rw_rd_size c)) found,
        setup + audit_work ft + tw +
    audit_map_source_work audit_basic_encoding_work rt)
    end
  else (None, 64 +
    vw).


Fixpoint rw_rd_positive_to_nat (p : positive) : nat * nat :=
  match p with
  | xH =>
    (1, 64)
  | xO rest => let '(n, nw) := rw_rd_positive_to_nat rest in
      let '(out,
    add_trace) := rw_fuel_add n n in (out, 64 + nw + audit_work add_trace)
  | xI rest => let
    '(n, nw) := rw_rd_positive_to_nat rest in
      let '(out, add_trace) := rw_fuel_add n n in
    (S out, 64 + nw + audit_work add_trace)
  end.


Definition rw_rd_N_to_nat (n : N) : nat *
    nat :=
  match n with N0 => (0, 64) | Npos p => rw_rd_positive_to_nat p end.


Definition rw_shared_tree_cost_binary_atomic {K Sort V} (vc : V -> nat * nat)
    (oc : K -> nat * nat)
    (dag : rw_shared_tree K Sort V) : option N * nat :=
  let '(out, work) :=
    rw_rd_scalar_observe vc oc dag in
  (option_map fst out, 64 + work).


Definition rw_shared_tree_size_binary_atomic {K Sort V} (dag : rw_shared_tree K Sort V) :
    option N
    * nat :=
  let '(out, work) := rw_rd_scalar_observe (fun _ => (0, 64)) (fun _ => (0, 64))
    dag in
  (option_map snd out, 64 + work).


Definition rw_shared_tree_cost_atomic {K Sort V}
    (vc : V -> nat * nat)
    (oc : K -> nat * nat) (dag : rw_shared_tree K Sort V) : option nat
    * nat :=
  let '(out, work) := rw_shared_tree_cost_binary_atomic vc oc dag in
  match out
    with
  | None => (None, 64 + work)
  | Some n => let '(result, conversion_work) :=
    rw_rd_N_to_nat n in
      (Some result, 64 + work + conversion_work)
  end.

(** The scalar
    observer measures the same unfolded tree, with every repeated occurrence. *)

(** This statement fixes the rd scalar agrees statement contract. *)
Definition rw_rd_scalar_agrees_statement : Prop :=
  forall K Sort V (vc : V -> nat * nat) (oc : K ->
    nat * nat)
    (dag : rw_shared_tree K Sort V) tree,
  rw_shared_unfold dag = Some tree ->

    fst (rw_rd_scalar_observe vc oc dag) =
    Some (N.of_nat (rw_tree_cost (fun v => fst (vc
    v)) (fun k => fst (oc k)) tree),
      N.of_nat (rw_tree_size tree)).

(** Invalid DAGs are
    rejected by all observers before their client cost callbacks run. *)

(** This statement fixes the rd scalar reject statement contract. *)
Definition rw_rd_scalar_reject_statement : Prop :=
  forall K Sort V (vc : V -> nat * nat) (oc : K ->
    nat * nat)
    (dag : rw_shared_tree K Sort V),
  rw_shared_validate dag = false -> fst
    (rw_rd_scalar_observe vc oc dag) = None.
```

## Galois.Rewrite.RewriteAuditSharedBoundsContracts

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditSharedBoundsContracts.v`.

```rocq
(** * RewriteAuditSharedBoundsContracts

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditQueueReference RewriteAuditSharedExtract
  RewriteAuditSharedObservers RewriteAuditSharedReference.
Import List.ListNotations.

Definition rw_rd_source_node {K Sort V} (node : rw_node K Sort V) : rw_shared_node K Sort V :=

    match node with
  | RWNVar s v => RWSharedVar K Sort V s v
  | RWNApp s k ids => RWSharedApp
    K Sort V s k ids
  end.


Definition rw_rd_callback_weight {K Sort V} (vc : V -> nat * nat)
    (oc : K -> nat * nat)
    (node : rw_node K Sort V) : nat :=
  match node with
  | RWNVar _
    v => let '(cost, work) := vc v in S (cost + work)
  | RWNApp _ k _ => let '(cost, work) :=
    oc k in S (cost + work)
  end.


Definition rw_rd_extract_input_weight {K Sort V} (op :
    rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value :
    rw_queue_encoder_adapter V)
    (vc : V -> nat * nat) (oc : K -> nat * nat) (g : rw_graph K
    Sort V) (root : rw_id) : nat :=
  S (Pos.size_nat root + length (rw_roots g) +

    audit_trie_nodes (rw_nodes g) + audit_trie_nodes (rw_class_roots g) +
    fold_right (fun
    entry n => Pos.size_nat (fst entry) + Pos.size_nat (fst (snd entry)) +

    rw_rd_node_input_weight op sort value (rw_rd_source_node (snd (snd entry))) +

    rw_rd_callback_weight vc oc (snd (snd entry)) + n) 0 (Map.elements (rw_nodes g)) +

    fold_right (fun entry n => Pos.size_nat (fst entry) + Pos.size_nat (snd entry) + n)
      0
    (Map.elements (rw_class_roots g))).


Definition rw_rd_extract_budget {K Sort V} (op :
    rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value :
    rw_queue_encoder_adapter V)
    (vc : V -> nat * nat) (oc : K -> nat * nat) (g : rw_graph K
    Sort V) (root : rw_id) : nat :=
  Nat.pow (1024 * rw_rd_extract_input_weight op sort value
    vc oc g root) 20.

(** Every extraction source run obeys a finite input-only ceiling.
    *)

(** This statement fixes the rd extract bound statement contract. *)
Definition rw_rd_extract_bound_statement : Prop :=
  forall K Sort V (op :
    rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value :
    rw_queue_encoder_adapter V)
    (vc : V -> nat * nat) (oc : K -> nat * nat) g root answer
    work,
  rw_shared_extract_run op sort value vc oc g root answer work ->
  work <=
    rw_rd_extract_budget op sort value vc oc g root.

(** Backpointer allocation is bounded by
    the number of actual production visits. *)

(** This statement fixes the rd extract storage statement contract. *)
Definition rw_rd_extract_storage_statement : Prop
    :=
  forall K Sort V (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter
    Sort) (value : rw_queue_encoder_adapter V)
    (vc : V -> nat * nat) (oc : K -> nat * nat) g
    root dag work,
  rw_shared_extract_run op sort value vc oc g root (Some dag) work ->

    Map.size (rw_shared_nodes K Sort V dag) <= length (rw_roots g) * Map.size (rw_nodes
    g).


Definition rw_rd_scalar_input_weight {K Sort V} (vc : V -> nat * nat) (oc : K -> nat *
    nat)
    (dag : rw_shared_tree K Sort V) : nat :=
  S (audit_trie_nodes (rw_shared_nodes K
    Sort V dag) +
    Pos.size_nat (rw_shared_root K Sort V dag) +
    fold_right (fun entry n
    => Pos.size_nat (fst entry) +
      match snd entry with
      | RWSharedVar _ _ _ _ v =>
    let '(cost, work) := vc v in S (cost + work + n)
      | RWSharedApp _ _ _ _ k ids => let
    '(cost, work) := oc k in
          S (cost + work + rw_shared_children_bits ids + n)

    end) 0 (Map.elements (rw_shared_nodes K Sort V dag))).


Definition rw_rd_scalar_budget {K
    Sort V} (vc : V -> nat * nat) (oc : K -> nat * nat)
    (dag : rw_shared_tree K Sort V) :
    nat :=
  Nat.pow (1024 * rw_rd_scalar_input_weight vc oc dag) 8.

(** Binary scalar work
    depends on stored input and binary payload work, not unfolded size. *)

(** This statement fixes the rd scalar bound statement contract. *)
Definition rw_rd_scalar_bound_statement : Prop :=
  forall K Sort V (vc : V -> nat * nat) (oc : K ->
    nat * nat)
    (dag : rw_shared_tree K Sort V),
  snd (rw_rd_scalar_observe vc oc dag) <=
    rw_rd_scalar_budget vc oc dag.

(** The unary observer separately pays for constructing its
    unary result. *)

(** This statement fixes the rd unary cost bound statement contract. *)
Definition rw_rd_unary_cost_bound_statement : Prop :=
  forall K Sort V (vc
    : V -> nat * nat) (oc : K -> nat * nat)
    (dag : rw_shared_tree K Sort V),
  snd
    (rw_shared_tree_cost_atomic vc oc dag) <=
    128 + rw_rd_scalar_budget vc oc dag +

    match fst (rw_shared_tree_cost_binary_atomic vc oc dag) with
    | None => 0
    | Some cost
    => snd (rw_rd_N_to_nat cost)
    end.

(** A nonempty source run constructs a real variable
    backpointer with a matching unfold. *)
```

## Galois.Rewrite.RewriteAuditProofCarrier

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditProofCarrier.v`.

```rocq
(** * RewriteAuditProofCarrier

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
Import List.ListNotations.

Inductive rw_evidence_reason (K Sort V H : Type) : Type :=
  | RWEvidenceRefl : rw_evidence_reason K Sort V H
  | RWEvidenceRule : nat -> Map.t H (rw_term K Sort V) -> rw_evidence_reason K Sort V H
  | RWEvidenceSym : positive -> rw_evidence_reason K Sort V H
  | RWEvidenceTrans : positive -> positive -> rw_evidence_reason K Sort V H
  | RWEvidenceCongruence : list positive -> rw_evidence_reason K Sort V H.

Arguments RWEvidenceRefl {K Sort V H}.
Arguments RWEvidenceRule {K Sort V H}.
Arguments RWEvidenceSym {K Sort V H}.
Arguments RWEvidenceTrans {K Sort V H}.
Arguments RWEvidenceCongruence {K Sort V H}.


Record rw_evidence_node (K Sort V H : Type) : Type := RWEvidenceNode {
  rw_evidence_left : rw_term K Sort V;
  rw_evidence_right : rw_term K Sort V;
  rw_evidence_reason_of : rw_evidence_reason K Sort V H;
  rw_evidence_time : nat * nat
}.

Arguments RWEvidenceNode {K Sort V H}.
Arguments rw_evidence_left {K Sort V H}.
Arguments rw_evidence_right {K Sort V H}.
Arguments rw_evidence_reason_of {K Sort V H}.
Arguments rw_evidence_time {K Sort V H}.


Record rw_provenance (K Sort V H : Type) : Type := RWProvenance {
  rw_provenance_ids : list positive;
  rw_provenance_nodes : Map.t positive (rw_evidence_node K Sort V H)
}.

Arguments RWProvenance {K Sort V H}.
Arguments rw_provenance_ids {K Sort V H}.
Arguments rw_provenance_nodes {K Sort V H}.


Definition rw_reason_references {K Sort V H} (r : rw_evidence_reason K Sort V H) :
    list positive :=
  match r with
  | RWEvidenceRefl => []
  | RWEvidenceRule _ _ => []
  | RWEvidenceSym child => [child]
  | RWEvidenceTrans first second => [first; second]
  | RWEvidenceCongruence children => children
  end.


Definition rw_evidence_time_le (first second : nat * nat) : Prop :=
  fst first < fst second \/ fst first = fst second /\ snd first <= snd second.


Definition rw_evidence_time_lt (first second : nat * nat) : Prop :=
  fst first < fst second \/ fst first = fst second /\ snd first < snd second.


Definition rw_evidence_reason_valid {K Sort V H}
    (EH : encoding H) (sig : rw_signature K Sort V)
    (rules : list (rw_rule K Sort V H)) (p : rw_provenance K Sort V H)
    (node : rw_evidence_node K Sort V H) : Prop :=
  let left := rw_evidence_left node in
  let right := rw_evidence_right node in
  let lookup id := Map.get positive_encoding id (rw_provenance_nodes p) in
  match rw_evidence_reason_of node with
  | RWEvidenceRefl => left = right
  | RWEvidenceRule index bindings =>
    exists r,
      nth_error rules index = Some r /\
      let sub := fun h => Map.get EH h bindings in
      rw_sub_typed sig (rw_hole_sort r) sub /\ rw_condition r sub = true /\
      rw_instantiate sub (rw_lhs r) = Some left /\
      rw_instantiate sub (rw_rhs r) = Some right
  | RWEvidenceSym child =>
    exists n, lookup child = Some n /\
      rw_evidence_left n = right /\ rw_evidence_right n = left
  | RWEvidenceTrans first second =>
    exists n m,
      lookup first = Some n /\ lookup second = Some m /\
      rw_evidence_left n = left /\ rw_evidence_right n = rw_evidence_left m /\
      rw_evidence_right m = right
  | RWEvidenceCongruence children =>
    exists sort op ls rs,
      left = RWApp sort op ls /\ right = RWApp sort op rs /\ length ls = length rs /\
      Forall2 (fun id pair => exists n, lookup id = Some n /\
        rw_evidence_left n = fst pair /\ rw_evidence_right n = snd pair)
        children (combine ls rs)
  end.


Definition rw_provenance_valid {K Sort V H}
    (EH : encoding H) (sig : rw_signature K Sort V)
    (rules : list (rw_rule K Sort V H)) (p : rw_provenance K Sort V H) : Prop :=
  NoDup (rw_provenance_ids p) /\
  Map.wf positive_encoding (rw_provenance_nodes p) /\
  (forall id, In id (rw_provenance_ids p) <->
    exists node, Map.get positive_encoding id (rw_provenance_nodes p) = Some node) /\
  forall id node, Map.get positive_encoding id (rw_provenance_nodes p) = Some node ->
    rw_evidence_reason_valid EH sig rules p node /\
    Forall (fun child => (child < id)%positive /\
      exists n, Map.get positive_encoding child (rw_provenance_nodes p) = Some n /\
        rw_evidence_time_le (rw_evidence_time n) (rw_evidence_time node))
      (rw_reason_references (rw_evidence_reason_of node)).


(** This statement fixes the provenance sound contract. *)
Definition rw_provenance_sound_contract : Prop :=
  forall K Sort V H C (EH : encoding H) (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H))
    (p : rw_provenance K Sort V H),
    rw_provenance_valid EH sig rules p ->
    forall id node, Map.get positive_encoding id (rw_provenance_nodes p) = Some node ->
      rw_equal sig admissible rules (rw_evidence_left node) (rw_evidence_right node).
```

## Galois.Rewrite.RewriteAuditProofClosure

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditProofClosure.v`.

```rocq
(** * RewriteAuditProofClosure

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditProofCarrier RewriteAuditQueueReference
  RewriteAuditSharedCompare.
Import List.ListNotations.

Fixpoint rw_rp_append {A} (xs ys : list A) : list A * nat :=
  match xs with
  | nil => (ys,
    64)
  | x :: rest => let '(tail, work) := rw_rp_append rest ys in
      (x :: tail, 128 +
    work)
  end.


Fixpoint rw_rp_term_tokens {K Sort V} (op : rw_queue_encoder_adapter K)

    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (term :
    rw_term K Sort V) : list positive * nat :=
  match term with
  | RWVar ty v =>
    let '(s,
    sw) := rw_queue_encoder_run sort ty in
    let '(x, xw) := rw_queue_encoder_run value v in

      ([1%positive; s; x; 1%positive], 64 + sw + xw)
  | RWApp ty k children =>
    let '(s, sw)
    := rw_queue_encoder_run sort ty in
    let '(x, xw) := rw_queue_encoder_run op k in
    let
    '(arity, lt) := rw_fuel_length children in
    let '(arity_code, et) := audit_nat_encode
    arity in
    let fix visit (ts : list (rw_term K Sort V)) : list positive * nat :=

    match ts with
      | nil => (nil, 64)
      | t :: rest =>
        let '(head, hw) :=
    rw_rp_term_tokens op sort value t in
        let '(tail, tw) := visit rest in
        let
    '(out, aw) := rw_rp_append head tail in (out, 64 + hw + tw + aw)
      end in
    let
    '(tokens, work) := visit children in
    (2%positive :: s :: x :: arity_code :: tokens,

     64 + sw + xw + audit_work lt + audit_nat_events_work et + work)
  end.


Definition rw_rp_term_key {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort :
    rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (term : rw_term K
    Sort V) : positive * nat :=
  let '(tokens, work) := rw_rp_term_tokens op sort value term
    in
  let '(code, trace) := audit_list_encode audit_positive_encode tokens in
  (code, 64 +
    work + audit_list_events_work audit_basic_encoding_work trace).


Fixpoint rw_rp_fresh_loop
    (ids : list positive) (largest : positive) : positive * nat :=
  match ids with
  | nil =>
    let '(fresh, trace) := rw_fuel_pos_succ largest in
      (fresh, 64 + audit_work trace)
  |
    id :: rest =>
    let '(order, comparison_work) := rw_rd_positive_compare_cont Eq id largest
    in
    let next := match order with Gt => id | _ => largest end in
    let '(fresh,
    tail_work) := rw_rp_fresh_loop rest next in
    (fresh, 64 + comparison_work + tail_work)

    end.


Definition rw_rp_proof_index := Map.t (positive * positive) positive.


Definition rw_rp_proof_get (lhs rhs : positive) (index : rw_rp_proof_index) :
    option positive * nat
    :=
  let '(answer, trace) := audit_map_get rw_rd_pair_encode (lhs, rhs) index in
  (answer,
    64 + audit_map_source_work rw_rd_pair_encoding_work trace).


Definition rw_rp_proof_put (lhs
    rhs id : positive) (index : rw_rp_proof_index) :
    rw_rp_proof_index * nat :=
  let
    '(answer, trace) := audit_map_set rw_rd_pair_encode (lhs, rhs) id index in
  (answer, 64 +
    audit_map_source_work rw_rd_pair_encoding_work trace).


Record rw_rp_connection_state (K
    Sort V H : Type) := RwRpConnectionState {
  rw_rp_proof : rw_provenance K Sort V H;

    rw_rp_index : rw_rp_proof_index
}.
Arguments RwRpConnectionState {K Sort V H}.
Arguments
    rw_rp_proof {K Sort V H}.
Arguments rw_rp_index {K Sort V H}.


Definition rw_rp_add_evidence
    {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V)
    (stamp : nat * nat) (lhs rhs : rw_term K Sort V)

     (reason : rw_evidence_reason K Sort V H) (state : rw_rp_connection_state K Sort V H) :

    (positive * rw_rp_connection_state K Sort V H) * nat :=
  let proof := rw_rp_proof state in

     let '(id, fresh_work) := rw_rp_fresh_loop (rw_provenance_ids proof) 1%positive in
  let
    node := RWEvidenceNode lhs rhs reason stamp in
  let '(nodes, nt) := audit_map_set
    audit_positive_encode id node (rw_provenance_nodes proof) in
  let '(lk, lw) :=
    rw_rp_term_key op sort value lhs in
  let '(rk, rw) := rw_rp_term_key op sort value rhs in

    let '(index, iw) := rw_rp_proof_put lk rk id (rw_rp_index state) in
  ((id,
    RwRpConnectionState (RWProvenance (id :: rw_provenance_ids proof) nodes) index),
    64 +
    fresh_work + audit_map_source_work audit_basic_encoding_work nt + lw + rw + iw).


Fixpoint rw_rp_index_existing {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort :
    rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (ids : list
    positive) (proof : rw_provenance K Sort V H) (index : rw_rp_proof_index) :

    rw_rp_proof_index * nat :=
  match ids with
  | nil => (index, 64)
  | id :: rest =>
    let
    '(found, nt) := audit_map_get audit_positive_encode id (rw_provenance_nodes proof) in

    let nw := audit_map_source_work audit_basic_encoding_work nt in
    match found with
    |
    None => let '(out, tw) := rw_rp_index_existing op sort value rest proof index in

    (out, 64 + nw + tw)
    | Some node =>
      let '(lk, lw) := rw_rp_term_key op sort value
    (rw_evidence_left node) in
      let '(rk, rw) := rw_rp_term_key op sort value
    (rw_evidence_right node) in
      let '(next, iw) := rw_rp_proof_put lk rk id index in

    let '(out, tw) := rw_rp_index_existing op sort value rest proof next in
      (out, 64 + nw
    + lw + rw + iw + tw)
    end
  end.


Definition rw_rp_try_symmetry {K Sort V H} (op :
    rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value :
    rw_queue_encoder_adapter V)
    (stamp : nat * nat) (lhs rhs : rw_term K Sort V)
    (state
    : rw_rp_connection_state K Sort V H) :
    (option positive * rw_rp_connection_state K Sort
    V H) * nat :=
  let '(lk, lw) := rw_rp_term_key op sort value lhs in
  let '(rk, rw) :=
    rw_rp_term_key op sort value rhs in
  let '(reverse, lookup_work) := rw_rp_proof_get rk lk
    (rw_rp_index state) in
  match reverse with
  | None => ((None, state), 64 + lw + rw +
    lookup_work)
  | Some id =>
    let '((new, next), work) := rw_rp_add_evidence op sort value
    stamp lhs rhs
      (RWEvidenceSym id) state in
    ((Some new, next), 64 + lw + rw +
    lookup_work + work)
  end.


Fixpoint rw_rp_try_transitivity {K Sort V H} (op :
    rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value :
    rw_queue_encoder_adapter V)
    (stamp : nat * nat) (lhs rhs : rw_term K Sort V)

    (middles : list (rw_term K Sort V)) (state : rw_rp_connection_state K Sort V H) :

    (option positive * rw_rp_connection_state K Sort V H) * nat :=
  match middles with
  | nil
    => ((None, state), 64)
  | middle :: rest =>
    let '(lk, lw) := rw_rp_term_key op sort
    value lhs in
    let '(mk, mw) := rw_rp_term_key op sort value middle in
    let '(rk, rw)
    := rw_rp_term_key op sort value rhs in
    let '(first, fw) := rw_rp_proof_get lk mk
    (rw_rp_index state) in
    match first with
    | None => let '(answer, work) :=
    rw_rp_try_transitivity op sort value stamp
        lhs rhs rest state in (answer, 64 + lw +
    mw + rw + fw + work)
    | Some a =>
      let '(second, sw) := rw_rp_proof_get mk rk
    (rw_rp_index state) in
      match second with
      | None => let '(answer, work) :=
    rw_rp_try_transitivity op sort value stamp
          lhs rhs rest state in (answer, 64 + lw
    + mw + rw + fw + sw + work)
      | Some b =>
        let '((id, next), work) :=
    rw_rp_add_evidence op sort value stamp lhs rhs
          (RWEvidenceTrans a b) state in

       ((Some id, next), 64 + lw + mw + rw + fw + sw + work)
      end
    end
  end.

(** The
    generic sorted-term key has exactly the promised preorder-list encoding. *)

(** This statement fixes the rp term key agrees statement contract. *)
Definition rw_rp_term_key_agrees_statement : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding
    Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort :
    rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) term,
  (forall k,
    fst (rw_queue_encoder_run op k) = encode EK k) ->
  (forall ty, fst (rw_queue_encoder_run
    sort ty) = encode ES ty) ->
  (forall v, fst (rw_queue_encoder_run value v) = encode EV v)
    ->
  fst (rw_rp_term_key op sort value term) =
    encode (list_encoding positive_encoding)
    (rw_tree_code EK ES EV term).



Fixpoint rw_rp_children_evidence {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort :
    rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (lhs rhs : list
    (rw_term K Sort V)) (state : rw_rp_connection_state K Sort V H) :
    option (list positive)
    * nat :=
  match lhs, rhs with
  | nil, nil => (Some nil, 64)
  | a :: xs, b :: ys =>

    let '(lk, lw) := rw_rp_term_key op sort value a in
    let '(rk, rw) := rw_rp_term_key op
    sort value b in
    let '(found, fw) := rw_rp_proof_get lk rk (rw_rp_index state) in

    match found with
    | None => (None, 64 + lw + rw + fw)
    | Some id =>
      let '(tail,
    tw) := rw_rp_children_evidence op sort value xs ys state in
      (option_map (fun ids => id
    :: ids) tail, 64 + lw + rw + fw + tw)
    end
  | _, _ => (None, 64)
  end.


Definition rw_rp_try_congruence {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort :
    rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (stamp : nat * nat)
    (lhs rhs : rw_term K Sort V)
    (state : rw_rp_connection_state K Sort V H) :
    (option
    positive * rw_rp_connection_state K Sort V H) * nat :=
  match lhs, rhs with
  | RWApp s k
    xs, RWApp t l ys =>
    let '(sc, sw) := rw_queue_encoder_run sort s in
    let '(tc, tw) :=
    rw_queue_encoder_run sort t in
    let '(same_sort, st) := audit_positive_eqb sc tc in

    if same_sort then
      let '(kc, kw) := rw_queue_encoder_run op k in
      let '(lc, lw) :=
    rw_queue_encoder_run op l in
      let '(same_op, kt) := audit_positive_eqb kc lc in

    if same_op then
        let '(children, cw) := rw_rp_children_evidence op sort value xs ys
    state in
        match children with
        | None => ((None, state), 64 + sw + tw +
    audit_positive_eqb_source_work st +
            kw + lw + audit_positive_eqb_source_work kt
    + cw)
        | Some ids =>
          let '((id, next), work) := rw_rp_add_evidence op sort
    value stamp lhs rhs
            (RWEvidenceCongruence ids) state in
          ((Some id,
    next), 64 + sw + tw + audit_positive_eqb_source_work st +
            kw + lw +
    audit_positive_eqb_source_work kt + cw + work)
        end
      else ((None, state), 64 +
    sw + tw + audit_positive_eqb_source_work st +
        kw + lw +
    audit_positive_eqb_source_work kt)
    else ((None, state), 64 + sw + tw +
    audit_positive_eqb_source_work st)
  | _, _ => ((None, state), 64)
  end.


Definition rw_rp_close_pair {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort :
    rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (stamp : nat * nat)
    (terms : list (rw_term K Sort V))
    (lhs rhs : rw_term K Sort V) (state :
    rw_rp_connection_state K Sort V H) :
    rw_rp_connection_state K Sort V H * nat :=
  let
    '(lk, lw) := rw_rp_term_key op sort value lhs in
  let '(rk, rw) := rw_rp_term_key op sort
    value rhs in
  let '(present, pw) := rw_rp_proof_get lk rk (rw_rp_index state) in
  match
    present with
  | Some _ => (state, 64 + lw + rw + pw)
  | None =>
    let '(same, st) :=
    audit_positive_eqb lk rk in
    let prefix := 64 + lw + rw + pw +
    audit_positive_eqb_source_work st in
    if same then
      let '((_, next), work) :=
    rw_rp_add_evidence op sort value stamp lhs rhs
        RWEvidenceRefl state in (next, prefix
    + work)
    else
      let '((symmetric, first), fw) :=
        rw_rp_try_symmetry op sort
    value stamp lhs rhs state in
      match symmetric with
      | Some _ => (first, prefix +
    fw)
      | None =>
        let '((transitive, second), sw) :=

    rw_rp_try_transitivity op sort value stamp lhs rhs terms first in
        match transitive
    with
        | Some _ => (second, prefix + fw + sw)
        | None => let '((_, final), cw)
    :=
            rw_rp_try_congruence op sort value stamp lhs rhs second in

    (final, prefix + fw + sw + cw)
        end
      end
  end.


Fixpoint rw_rp_close_row {K
    Sort V H} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V)
    (stamp : nat * nat) (terms : list (rw_term K Sort
    V))
    (lhs : rw_term K Sort V) (rights : list (rw_term K Sort V))
    (state :
    rw_rp_connection_state K Sort V H) : rw_rp_connection_state K Sort V H * nat :=
  match
    rights with
  | nil => (state, 64)
  | rhs :: rest =>
    let '(next, nw) :=
    rw_rp_close_pair op sort value stamp terms lhs rhs state in
    let '(out, tw) :=
    rw_rp_close_row op sort value stamp terms lhs rest next in
    (out, 64 + nw + tw)

    end.


Fixpoint rw_rp_close_pass {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort :
    rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (stamp : nat * nat)
    (terms lefts : list (rw_term K Sort V))
    (state : rw_rp_connection_state K Sort V H) :
    rw_rp_connection_state K Sort V H * nat :=
  match lefts with
  | nil => (state, 64)
  | lhs
    :: rest =>
    let '(next, nw) := rw_rp_close_row op sort value stamp terms lhs terms state
    in
    let '(out, tw) := rw_rp_close_pass op sort value stamp terms rest next in
    (out,
    64 + nw + tw)
  end.


Fixpoint rw_rp_close_rounds {K Sort V H} (op :
    rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value :
    rw_queue_encoder_adapter V)
    (stamp : nat * nat) (terms : list (rw_term K Sort V)) (fuel
    : positive)
    (state : rw_rp_connection_state K Sort V H) : rw_rp_connection_state K Sort
    V H * nat :=
  match fuel with
  | xH => let '(out, work) := rw_rp_close_pass op sort value
    stamp terms terms state in
      (out, 64 + work)
  | xO rest => let '(middle, mw) :=
    rw_rp_close_rounds op sort value stamp terms rest state in
      let '(out, tw) :=
    rw_rp_close_rounds op sort value stamp terms rest middle in
      (out, 64 + mw + tw)
  | xI
    rest => let '(first, fw) := rw_rp_close_pass op sort value stamp terms terms state in

    let '(middle, mw) := rw_rp_close_rounds op sort value stamp terms rest first in
      let
    '(out, tw) := rw_rp_close_rounds op sort value stamp terms rest middle in
      (out, 64 +
    fw + mw + tw)
  end.


Fixpoint rw_rp_subterms {K Sort V} (term : rw_term K Sort V) : list
    (rw_term K Sort V) * nat :=
  match term with
  | RWVar _ _ => ([term], 64)
  | RWApp _ _
    children =>
    let fix visit (ts : list (rw_term K Sort V)) : list (rw_term K Sort V) * nat
    :=
      match ts with
      | nil => (nil, 64)
      | t :: rest => let '(head, hw) :=
    rw_rp_subterms t in
          let '(tail, tw) := visit rest in
          let '(out, aw) :=
    rw_rp_append head tail in (out, 64 + hw + tw + aw)
      end in
    let '(others, work) :=
    visit children in (term :: others, 64 + work)
  end.


Fixpoint rw_rp_nat_compare (a b : nat)
    : comparison * nat :=
  match a, b with
  | 0, 0 => (Eq, 64)
  | 0, S _ => (Lt, 64)
  | S _,
    0 => (Gt, 64)
  | S x, S y => let '(answer, work) := rw_rp_nat_compare x y in (answer, 64 +
    work)
  end.


Fixpoint rw_rp_evidence_terms {K Sort V H}
    (entries : list (positive *
    rw_evidence_node K Sort V H)) (largest_group : nat) :
    (list (rw_term K Sort V) * nat) *
    nat :=
  match entries with
  | nil => ((nil, largest_group), 64)
  | (_, node) :: rest =>

      let group := fst (rw_evidence_time node) in
    let '(order, cw) := rw_rp_nat_compare
    group largest_group in
    let next := match order with Gt => group | _ => largest_group end
    in
    let '(lhs, lw) := rw_rp_subterms (rw_evidence_left node) in
    let '(rhs, rw) :=
    rw_rp_subterms (rw_evidence_right node) in
    let '((tail, maximum), tw) :=
    rw_rp_evidence_terms rest next in
    let '(both, bw) := rw_rp_append lhs rhs in
    let
    '(out, aw) := rw_rp_append both tail in
    ((out, maximum), 64 + cw + lw + rw + tw + bw +
    aw)
  end.


Definition rw_rp_connect_atomic {K Sort V H} (op : rw_queue_encoder_adapter K)

      (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (proof :
    rw_provenance K Sort V H) (lhs rhs : rw_term K Sort V) :
    option (rw_provenance K Sort V
    H * positive) * nat :=
  let '(entries, et) := audit_map_elements (rw_provenance_nodes
    proof) in
  let '((known, largest), kw) := rw_rp_evidence_terms entries 0 in
  let '(lefts,
    lw) := rw_rp_subterms lhs in
  let '(rights, rw) := rw_rp_subterms rhs in
  let '(both, bw)
    := rw_rp_append lefts rights in
  let '(terms, aw) := rw_rp_append both known in
  let
    '(index, iw) := rw_rp_index_existing op sort value (rw_provenance_ids proof) proof Map.empty
    in
  let '(count, lt) := rw_fuel_length terms in
  let '(square, mt) := rw_fuel_mul count
    count in
  let '(fuel, ft) := rw_fuel_to_positive square in
  let '(final, work) :=
    rw_rp_close_rounds op sort value (S largest, 0) terms fuel
    (RwRpConnectionState proof
    index) in
  let '(lk, lkw) := rw_rp_term_key op sort value lhs in
  let '(rk, rkw) :=
    rw_rp_term_key op sort value rhs in
  let '(answer, qw) := rw_rp_proof_get lk rk
    (rw_rp_index final) in
  (option_map (fun id => (rw_rp_proof final, id)) answer,
    64 +
    audit_elements_work et + kw + lw + rw + bw + aw + iw +
      audit_work lt + audit_work mt +
    audit_work ft + work + lkw + rkw + qw).



Inductive rw_rp_generated {K Sort V H} (proof : rw_provenance K Sort V H) :
    rw_term K Sort V
    -> rw_term K Sort V -> Prop :=
  | RPGeneratedLeaf : forall id node,
      Map.get
    positive_encoding id (rw_provenance_nodes proof) = Some node ->
      rw_rp_generated proof
    (rw_evidence_left node) (rw_evidence_right node)
  | RPGeneratedRefl : forall t,
    rw_rp_generated proof t t
  | RPGeneratedSym : forall t u, rw_rp_generated proof t u ->
    rw_rp_generated proof u t
  | RPGeneratedTrans : forall t u v,
      rw_rp_generated proof t
    u -> rw_rp_generated proof u v -> rw_rp_generated proof t v
  | RPGeneratedCongruence :
    forall s k xs ys,
      Forall2 (rw_rp_generated proof) xs ys ->
      rw_rp_generated proof
    (RWApp s k xs) (RWApp s k ys).

(** The fixed finite closure succeeds for precisely the
    ground equalities it generates. *)

(** This statement fixes the rp connect complete statement contract. *)
Definition rw_rp_connect_complete_statement : Prop :=

    forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op :
    rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value :
    rw_queue_encoder_adapter V) (proof : rw_provenance K Sort V H) lhs rhs,
  (forall k, fst
    (rw_queue_encoder_run op k) = encode EK k) ->
  (forall ty, fst (rw_queue_encoder_run sort
    ty) = encode ES ty) ->
  (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->

    Map.wf positive_encoding (rw_provenance_nodes proof) ->
  (forall id, In id
    (rw_provenance_ids proof) <->
    exists node, Map.get positive_encoding id
    (rw_provenance_nodes proof) = Some node) ->
  rw_rp_generated proof lhs rhs ->
  exists
    extended id, fst (rw_rp_connect_atomic op sort value proof lhs rhs) = Some (extended,
    id).

(** Successful connection extends the actual provenance with an equality of the
    requested ends. *)

(** This statement fixes the rp connect sound statement contract. *)
Definition rw_rp_connect_sound_statement : Prop :=
  forall K Sort V H
    (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (op :
    rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value :
    rw_queue_encoder_adapter V) (sig : rw_signature K Sort V) rules proof
    lhs rhs extended
    id,
  (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
  (forall ty, fst
    (rw_queue_encoder_run sort ty) = encode ES ty) ->
  (forall v, fst (rw_queue_encoder_run
    value v) = encode EV v) ->
  rw_provenance_valid EH sig rules proof ->
  fst
    (rw_rp_connect_atomic op sort value proof lhs rhs) = Some (extended, id) ->

    rw_provenance_valid EH sig rules extended /\
  (forall key node, Map.get positive_encoding
    key (rw_provenance_nodes proof) = Some node ->
    Map.get positive_encoding key
    (rw_provenance_nodes extended) = Some node) /\
  exists node, Map.get positive_encoding id
    (rw_provenance_nodes extended) = Some node /\
    rw_evidence_left node = lhs /\
    rw_evidence_right node = rhs.
```

## Galois.Rewrite.RewriteAuditProofTick

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditProofTick.v`.

```rocq
(** * RewriteAuditProofTick

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexRebuild RewriteAuditIndexReference
  RewriteAuditProofCarrier RewriteAuditProofClosure RewriteAuditQueueReference
  RewriteAuditSharedReference.
Import List.ListNotations.

Record rw_class_witness_store (K Sort V : Type) := RWClassWitnessStore {

    rw_class_witness_nodes : Map.t positive (rw_shared_node K Sort V);
  rw_class_witness_roots
    : Map.t rw_id positive
}.
Arguments RWClassWitnessStore {K Sort V}.
Arguments
    rw_class_witness_nodes {K Sort V}.
Arguments rw_class_witness_roots {K Sort V}.


Record rw_tracked_state (K Sort V H : Type) := RWTrackedState {
  rw_tracked_machine :
    rw_index_state K Sort V;
  rw_tracked_provenance : rw_provenance K Sort V H;

    rw_tracked_witnesses : rw_class_witness_store K Sort V;
  rw_tracked_event_nodes : Map.t
    (nat * nat) positive
}.
Arguments RWTrackedState {K Sort V H}.
Arguments rw_tracked_machine
    {K Sort V H}.
Arguments rw_tracked_provenance {K Sort V H}.
Arguments rw_tracked_witnesses
    {K Sort V H}.
Arguments rw_tracked_event_nodes {K Sort V H}.


Definition rw_rp_stamp_encode
    := audit_pair_encode audit_nat_encode audit_nat_encode.


Definition rw_rp_stamp_work

    (trace : list (audit_pair_event nat nat audit_nat_encoding_event audit_nat_encoding_event))
    : nat :=
  audit_pair_events_work audit_nat_events_work audit_nat_events_work
    trace.


Definition rw_rp_stamp_put (stamp : nat * nat) (id : positive)
    (table : Map.t
    (nat * nat) positive) : Map.t (nat * nat) positive * nat :=
  let '(out, trace) :=
    audit_map_set rw_rp_stamp_encode stamp id table in
  (out, 64 + audit_map_source_work
    rw_rp_stamp_work trace).


Definition rw_rp_witness_merge {K Sort V} (a b root pointer :
    positive)
    (store : rw_class_witness_store K Sort V) : rw_class_witness_store K Sort V *
    nat :=
  let '(first, ft) := audit_map_remove audit_positive_encode a
    (rw_class_witness_roots store) in
  let '(second, st) := audit_map_remove
    audit_positive_encode b first in
  let '(roots, rt) := audit_map_set audit_positive_encode
    root pointer second in
  (RWClassWitnessStore (rw_class_witness_nodes store) roots,
    64 +
    audit_map_source_work audit_basic_encoding_work ft +
      audit_map_source_work
    audit_basic_encoding_work st +
      audit_map_source_work audit_basic_encoding_work
    rt).


Definition rw_rp_witness_read {K Sort V} (id : rw_id)
    (store :
    rw_class_witness_store K Sort V) :
    option (positive * rw_term K Sort V) * nat :=
  let
    '(pointer, trace) := audit_map_get audit_positive_encode id (rw_class_witness_roots store)
    in
  let read_work := audit_map_source_work audit_basic_encoding_work trace in
  match
    pointer with
  | None => (None, 64 + read_work)
  | Some p =>
    let '(tree, unfold_trace)
    := rw_shared_unfold_atomic
      (RwSharedTree K Sort V p (rw_class_witness_nodes store))
    in
    (option_map (fun t => (p, t)) tree,
      64 + read_work +
    rw_shared_unfold_trace_cost unfold_trace)
  end.


Definition rw_rp_restate {K Sort V H} (old
    : rw_tracked_state K Sort V H)
    (machine : rw_index_state K Sort V) (proof :
    rw_provenance K Sort V H)
    (witnesses : rw_class_witness_store K Sort V) (events : Map.t
    (nat * nat) positive) :
    rw_tracked_state K Sort V H := RWTrackedState machine proof
    witnesses events.



Definition rw_rp_connect_at_atomic {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort :
    rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (stamp : nat * nat)
    (proof : rw_provenance K Sort V H) (lhs rhs : rw_term K Sort V) :
    option (rw_provenance
    K Sort V H * positive) * nat :=
  let '(entries, et) := audit_map_elements
    (rw_provenance_nodes proof) in
  let '((known, largest), kw) := rw_rp_evidence_terms entries
    0 in
  let '(lefts, lw) := rw_rp_subterms lhs in
  let '(rights, rw) := rw_rp_subterms rhs
    in
  let '(both, bw) := rw_rp_append lefts rights in
  let '(terms, aw) := rw_rp_append both
    known in
  let '(index, iw) := rw_rp_index_existing op sort value (rw_provenance_ids proof)
    proof Map.empty in
  let '(count, lt) := rw_fuel_length terms in
  let '(square, mt) :=
    rw_fuel_mul count count in
  let '(fuel, ft) := rw_fuel_to_positive square in
  let '(final,
    work) := rw_rp_close_rounds op sort value stamp terms fuel
    (RwRpConnectionState proof
    index) in
  let '(lk, lkw) := rw_rp_term_key op sort value lhs in
  let '(rk, rkw) :=
    rw_rp_term_key op sort value rhs in
  let '(answer, qw) := rw_rp_proof_get lk rk
    (rw_rp_index final) in
  (option_map (fun id => (rw_rp_proof final, id)) answer,
    64 +
    audit_elements_work et + kw + lw + rw + bw + aw + iw +
      audit_work lt + audit_work mt +
    audit_work ft + work + lkw + rkw + qw).



Definition rw_rp_record_connection {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort :
    rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (stamp : nat * nat)
    (lhs rhs : rw_term K Sort V)
    (proof : rw_provenance K Sort V H) :
    option
    (rw_provenance K Sort V H * positive) * nat :=
  let '(connection, connection_work) :=

    rw_rp_connect_at_atomic op sort value stamp proof lhs rhs in
  match connection with
  |
    None => (None, 64 + connection_work)
  | Some (extended, id) =>
    let '(index, iw) :=
    rw_rp_index_existing op sort value (rw_provenance_ids extended)
      extended Map.empty in

       let state := RwRpConnectionState extended index in
    let '((refl, with_refl), rw) :=
    rw_rp_add_evidence op sort value stamp rhs rhs
      RWEvidenceRefl state in
    let
    '((event_id, final), fw) := rw_rp_add_evidence op sort value stamp lhs rhs

    (RWEvidenceTrans id refl) with_refl in
    (Some (rw_rp_proof final, event_id), 64 +
    connection_work + iw + rw + fw)
  end.


Definition rw_rp_tick_atomic {K Sort V H} (op :
    rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value :
    rw_queue_encoder_adapter V)
    (stamp : nat * nat) (state : rw_tracked_state K Sort V H) :

       option (rw_tracked_state K Sort V H * rw_index_event) * nat :=
  let '(stepped, trace) :=
    rw_ri_tick_atomic op sort value (rw_tracked_machine state) in
  let step_work :=
    rw_ri_tick_trace_cost trace in
  match stepped with
  | None => (None, 64 + step_work)
  |
    Some (next, event) =>
    match event with
    | RWIndexCongruence pair_value a b root =>

       let store := rw_tracked_witnesses state in
      let '(lhs, lw) := rw_rp_witness_read a
    store in
      match lhs with
      | None => (None, 64 + step_work + lw)
      | Some
    (left_pointer, left_term) =>
        let '(rhs, rw) := rw_rp_witness_read b store in

    match rhs with
        | None => (None, 64 + step_work + lw + rw)
        | Some (_,
    right_term) =>
          let '(recorded, record_work) := rw_rp_record_connection op sort
    value stamp
            left_term right_term (rw_tracked_provenance state) in

    match recorded with
          | None => (None, 64 + step_work + lw + rw + record_work)

        | Some (proof, id) =>
            let '(witnesses, witness_work) := rw_rp_witness_merge
    a b root left_pointer store in
            let '(events, event_work) := rw_rp_stamp_put
    stamp id (rw_tracked_event_nodes state) in
            (Some (RWTrackedState next proof
    witnesses events, event),
              64 + step_work + lw + rw + record_work +
    witness_work + event_work)
          end
        end
      end
    | _ => (Some
    (RWTrackedState next (rw_tracked_provenance state)
        (rw_tracked_witnesses state)
    (rw_tracked_event_nodes state), event), 64 + step_work)
    end
  end.

(** Every captured
    merge stores a proof with the actual pre-state witness endpoints and stamp. *)

(** This statement fixes the rp tick captures statement contract. *)
Definition rw_rp_tick_captures_statement : Prop :=
  forall K Sort V H (op : rw_queue_encoder_adapter
    K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    stamp
    (state next : rw_tracked_state K Sort V H) pair_value a b root work,
  rw_rp_tick_atomic op
    sort value stamp state =
    (Some (next, RWIndexCongruence pair_value a b root), work) ->

    exists left_pointer lhs right_pointer rhs id node,
    fst (rw_rp_witness_read a
    (rw_tracked_witnesses state)) = Some (left_pointer, lhs) /\
    fst (rw_rp_witness_read b
    (rw_tracked_witnesses state)) = Some (right_pointer, rhs) /\
    Map.get (pair_encoding
    nat_encoding nat_encoding) stamp (rw_tracked_event_nodes next) =
      Some id /\

    Map.get positive_encoding id (rw_provenance_nodes (rw_tracked_provenance next)) = Some node
    /\
    rw_evidence_left node = lhs /\ rw_evidence_right node = rhs /\ rw_evidence_time node
    = stamp.
```

## Galois.Rewrite.RewriteAuditProofSeed

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditProofSeed.v`.

```rocq
(** * RewriteAuditProofSeed

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexPrepare RewriteAuditIndexReference
  RewriteAuditProofCarrier RewriteAuditProofTick RewriteAuditQueueReference
  RewriteAuditSharedReference.
Import List.ListNotations.

Record rw_rp_seed_acc (K Sort V : Type) := RwRpSeedAcc {
  rw_rp_seed_graph : rw_graph K Sort
    V;
  rw_rp_seed_witnesses : rw_class_witness_store K Sort V;
  rw_rp_seed_next : positive;

    rw_rp_seed_witness_next : positive
}.
Arguments RwRpSeedAcc {K Sort V}.
Arguments
    rw_rp_seed_graph {K Sort V}.
Arguments rw_rp_seed_witnesses {K Sort V}.
Arguments
    rw_rp_seed_next {K Sort V}.
Arguments rw_rp_seed_witness_next {K Sort V}.


Definition rw_rp_seed_empty {K Sort V} : rw_rp_seed_acc K Sort V :=
  RwRpSeedAcc (RwGraph nil nil
    Map.empty Map.empty Map.empty)
    (RWClassWitnessStore Map.empty Map.empty) 1%positive
    1%positive.


Definition rw_rp_seed_node {K Sort V} (node : rw_node K Sort V)
    (shared :
    rw_shared_node K Sort V) (acc : rw_rp_seed_acc K Sort V) :
    ((rw_id * positive) *
    rw_rp_seed_acc K Sort V) * nat :=
  let id := rw_rp_seed_next acc in
  let pointer :=
    rw_rp_seed_witness_next acc in
  let graph := rw_rp_seed_graph acc in
  let store :=
    rw_rp_seed_witnesses acc in
  let '(aliases, alias_trace) := audit_map_set
    audit_positive_encode id id (rw_class_roots graph) in
  let '(sorts, sort_trace) :=
    audit_map_set audit_positive_encode id (rw_node_sort node) (rw_sorts graph) in
  let
    '(nodes, node_trace) := audit_map_set audit_positive_encode id (id, node) (rw_nodes graph)
    in
  let '(shared_nodes, shared_trace) := audit_map_set audit_positive_encode pointer
    shared
    (rw_class_witness_nodes store) in
  let '(witness_roots, root_trace) :=
    audit_map_set audit_positive_encode id pointer
    (rw_class_witness_roots store) in
  let
    '(fresh, fresh_trace) := rw_fuel_pos_succ id in
  let '(witness_fresh, witness_fresh_trace)
    := rw_fuel_pos_succ pointer in
  (((id, pointer), RwRpSeedAcc
    (RwGraph (id :: rw_roots
    graph) (id :: rw_nodes_in graph) aliases sorts nodes)
    (RWClassWitnessStore shared_nodes
    witness_roots) fresh witness_fresh),
    64 + audit_map_source_work
    audit_basic_encoding_work alias_trace +
      audit_map_source_work
    audit_basic_encoding_work sort_trace +
      audit_map_source_work audit_basic_encoding_work
    node_trace +
      audit_map_source_work audit_basic_encoding_work shared_trace +

    audit_map_source_work audit_basic_encoding_work root_trace + audit_work fresh_trace +

    audit_work witness_fresh_trace).


Fixpoint rw_rp_seed_term {K Sort V} (term : rw_term K Sort
    V) (acc : rw_rp_seed_acc K Sort V) :
    ((rw_id * positive) * rw_rp_seed_acc K Sort V) *
    nat :=
  match term with
  | RWVar ty v =>
    let '(out, work) := rw_rp_seed_node (RWNVar
    ty v) (RWSharedVar K Sort V ty v) acc in
    (out, 64 + work)
  | RWApp ty op children =>

     let fix visit (ts : list (rw_term K Sort V)) (state : rw_rp_seed_acc K Sort V) :

    (list rw_id * list positive * rw_rp_seed_acc K Sort V) * nat :=
      match ts with
      |
    nil => ((nil, nil, state), 64)
      | t :: rest =>
        let '(((head, pointer), next),
    hw) := rw_rp_seed_term t state in
        let '((tail, pointers, final), tw) := visit rest
    next in
        ((head :: tail, pointer :: pointers, final), 64 + hw + tw)
      end in

    let '((ids, pointers, next), child_work) := visit children acc in
    let '(out, work) :=
    rw_rp_seed_node (RWNApp ty op ids)
      (RWSharedApp K Sort V ty op pointers) next in

    (out, 64 + child_work + work)
  end.


Definition rw_rp_seed_atomic {K Sort V H} (EK :
    encoding K) (ES : encoding Sort)
    (EV : encoding V) (op : rw_queue_encoder_adapter K)
    (value : rw_queue_encoder_adapter V)
    (term : rw_term K Sort V) : (rw_id *
    rw_tracked_state K Sort V H) * nat :=
  let '(((root, _), acc), seed_work) :=
    rw_rp_seed_term term rw_rp_seed_empty in
  let '(machine, trace) := rw_ri_prepare_once op value (rw_rp_seed_graph acc) in
  ((root, RWTrackedState machine (RWProvenance nil
    Map.empty)
    (rw_rp_seed_witnesses acc) Map.empty),
    64 + seed_work +
    rw_ri_prepare_once_work trace).

(** Seeding creates a represented source
    term and finite acyclic witnesses for every class. *)

(** This statement fixes the rp seed represents statement contract. *)
Definition rw_rp_seed_represents_statement : Prop :=
  forall K Sort V H (EK : encoding K) (ES :
    encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (value :
    rw_queue_encoder_adapter V)
    (sig : rw_signature K Sort V) term root (state :
    rw_tracked_state K Sort V H) work,
  rw_typed sig term ->
  rw_rp_seed_atomic EK ES EV op
    value term = ((root, state), work) ->
  rw_graph_wf sig (rw_index_graph (rw_tracked_machine
    state)) /\
  rw_represents (rw_index_graph (rw_tracked_machine state)) root term /\
  forall
    c pointer,
    Map.get positive_encoding c (rw_class_witness_roots (rw_tracked_witnesses
    state)) =
      Some pointer ->
    exists tree, rw_shared_unfold (RwSharedTree K Sort V
    pointer
      (rw_class_witness_nodes (rw_tracked_witnesses state))) = Some tree /\

    rw_represents (rw_index_graph (rw_tracked_machine state)) c tree.

(** The empty-rule seed
    consumer retains and unfolds a nontrivial application. *)
```

## Galois.Rewrite.RewriteAuditProofRebuild

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditProofRebuild.v`.

```rocq
(** * RewriteAuditProofRebuild

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexRebuild RewriteAuditIndexReference
  RewriteAuditIndexTickReference RewriteAuditProofCarrier RewriteAuditProofClosure
  RewriteAuditProofTick RewriteAuditQueueReference RewriteAuditSharedReference.
Import List.ListNotations.

Definition rw_rp_rebuild_done {K Sort V H}
    (state : rw_tracked_state K Sort V H * nat * list
    rw_index_event) : bool :=
  let '(tracked, _, _) := state in
  match rw_index_dirty_order
    (rw_tracked_machine tracked),
      rw_pending_sequence (rw_index_pending
    (rw_tracked_machine tracked)) with
  | nil, nil => true
  | _, _ => false
  end.


Definition rw_rp_rebuild_once {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort :
    rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (group : nat) (state
    : rw_tracked_state K Sort V H * nat * list rw_index_event) :
    (rw_tracked_state K Sort V
    H * nat * list rw_index_event) * nat :=
  let '(tracked, position, events) := state in
  let
    '(next, work) := rw_rp_tick_atomic op sort value (group, S position) tracked in
  match next
    with
  | None => (state, 64 + work)
  | Some (final, event) => ((final, S position, event ::
    events), 64 + work)
  end.


Fixpoint rw_rp_rebuild_repeat {K Sort V H} (op :
    rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value :
    rw_queue_encoder_adapter V)
    (group : nat) (fuel : positive)
    (state :
    rw_tracked_state K Sort V H * nat * list rw_index_event) :
    (rw_tracked_state K Sort V H
    * nat * list rw_index_event) * nat :=
  if rw_rp_rebuild_done state then (state, 64)
  else
    match fuel with
  | xH => let '(out, work) := rw_rp_rebuild_once op sort value group state
    in
      (out, 64 + work)
  | xO rest =>
    let '(middle, mw) := rw_rp_rebuild_repeat op
    sort value group rest state in
    let '(out, tw) := rw_rp_rebuild_repeat op sort value
    group rest middle in
    (out, 64 + mw + tw)
  | xI rest =>
    let '(first, fw) :=
    rw_rp_rebuild_once op sort value group state in
    let '(middle, mw) :=
    rw_rp_rebuild_repeat op sort value group rest first in
    let '(out, tw) :=
    rw_rp_rebuild_repeat op sort value group rest middle in
    (out, 64 + fw + mw + tw)

    end.


Definition rw_rp_rebuild_atomic {K Sort V H} (op : rw_queue_encoder_adapter K)

    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (group :
    nat) (state : rw_tracked_state K Sort V H) :
    (rw_tracked_state K Sort V H * list
    rw_index_event) * nat :=
  let '(fuel, fw) := rw_ri_rebuild_fuel_atomic (rw_tracked_machine
    state) in
  let '((final, _, reversed), work) :=
    rw_rp_rebuild_repeat op sort value
    group fuel (state, 0, nil) in
  let '(events, rw) := rw_ri_reverse_onto reversed nil in

    ((final, events), 64 + fw + work + rw).


Definition rw_rp_phase_connected {K Sort V H} (EK :
    encoding K) (ES : encoding Sort)
    (EV : encoding V) (state : rw_tracked_state K Sort V H)
    : Prop :=
  let graph := rw_index_graph (rw_tracked_machine state) in
  let proof :=
    rw_tracked_provenance state in
  let witnesses := rw_tracked_witnesses state in
  Map.wf
    positive_encoding (rw_provenance_nodes proof) /\
  (forall id, In id (rw_provenance_ids
    proof) <->
    exists node, Map.get positive_encoding id (rw_provenance_nodes proof) = Some
    node) /\
  (exists sig, rw_graph_wf sig graph) /\
  (forall c root, rw_find graph c = Some
    root ->
    exists pointer tree,
      Map.get positive_encoding root
    (rw_class_witness_roots witnesses) = Some pointer /\
      rw_shared_unfold (RwSharedTree K
    Sort V pointer (rw_class_witness_nodes witnesses)) =
        Some tree /\ rw_represents
    graph root tree) /\
  (forall root pointer tree,
    Map.get positive_encoding root
    (rw_class_witness_roots witnesses) = Some pointer ->
    rw_shared_unfold (RwSharedTree K
    Sort V pointer (rw_class_witness_nodes witnesses)) =
      Some tree -> rw_represents graph
    root tree) /\
  forall c lhs rhs, rw_represents graph c lhs -> rw_represents graph c rhs ->

       rw_rp_generated proof lhs rhs.

(** Every produced tracked rebuild event has a same-input
    indexed tick execution. *)

(** This statement fixes the rp rebuild projects statement contract. *)
Definition rw_rp_rebuild_projects_statement : Prop :=
  forall K
    Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op :
    rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value :
    rw_queue_encoder_adapter V) group (state : rw_tracked_state K Sort V H)
    final events
    work,
  (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
  (forall ty, fst
    (rw_queue_encoder_run sort ty) = encode ES ty) ->
  (forall v, fst (rw_queue_encoder_run
    value v) = encode EV v) ->
  rw_rp_rebuild_atomic op sort value group state = ((final,
    events), work) ->
  rw_rp_phase_connected EK ES EV state ->
  rw_index_rebuild EK ES EV
    (rw_tracked_machine state) =
    (rw_tracked_machine final, events).
```

## Galois.Rewrite.RewriteAuditIndexRules

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditIndexRules.v`.

```rocq
(** * RewriteAuditIndexRules

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexMembership RewriteAuditQueueReference.
Import List.ListNotations.

Inductive rw_rp_guard_program (K Sort V H : Type) : Type :=
  | RPGuardReturn : bool -> nat -> rw_rp_guard_program K Sort V H
  | RPGuardLookup : nat -> H ->
      (option (rw_term K Sort V) -> rw_rp_guard_program K Sort V H) ->
      rw_rp_guard_program K Sort V H.
Arguments RPGuardReturn {K Sort V H}.
Arguments RPGuardLookup {K Sort V H}.


Fixpoint rw_rp_guard_plain {K Sort V H} (sub : rw_substitution K Sort V H)
    (program : rw_rp_guard_program K Sort V H) : bool :=
  match program with
  | RPGuardReturn answer _ => answer
  | RPGuardLookup _ h next => rw_rp_guard_plain sub (next (sub h))
  end.


Fixpoint rw_rp_guard_execute {K Sort V H} (hole : rw_queue_encoder_adapter H)
    (bindings : Map.t H (rw_term K Sort V))
    (program : rw_rp_guard_program K Sort V H) :
    bool * nat * list (audit_map_event H (rw_term K Sort V) nat) :=
  match program with
  | RPGuardReturn answer body => (answer, 64 + body, nil)
  | RPGuardLookup body h next =>
    let '(binding, receipt) := audit_map_get (rw_external_encoding_events hole) h bindings in
    let '(answer, later_work, later) := rw_rp_guard_execute hole bindings (next binding) in
    (answer, 64 + body + audit_map_source_work rw_external_events_work receipt + later_work,
      receipt ++ later)
  end.



Record rw_rp_rule_callbacks (K Sort V H : Type) := RwRpRuleCallbacks {
  rw_rp_var_sort : V ->
    option Sort * nat;
  rw_rp_operator_shape : K -> list Sort -> Sort -> bool * nat;

    rw_rp_hole_sort : rw_rule K Sort V H -> H -> option Sort * nat;
  rw_rp_guard : rw_rule K Sort V H -> rw_rp_guard_program K Sort V H
}.
Arguments rw_rp_var_sort {K Sort V H}.
Arguments rw_rp_operator_shape {K Sort V
    H}.
Arguments rw_rp_hole_sort {K Sort V H}.
Arguments rw_rp_guard {K Sort V H}.


Fixpoint rw_rp_term_sorts {K Sort V} (terms : list (rw_term K Sort V)) : list Sort * nat :=
  match
    terms with
  | nil => (nil, 64)
  | t :: rest => let '(tail, work) := rw_rp_term_sorts rest
    in
      (rw_sort t :: tail, 128 + work)
  end.


Fixpoint rw_rp_type_atomic {K Sort V H}
    (sort : rw_queue_encoder_adapter Sort)
    (callbacks : rw_rp_rule_callbacks K Sort V H)
    (term : rw_term K Sort V) : bool * nat :=
  match term with
  | RWVar ty v =>
    let
    '(declared, callback_work) := rw_rp_var_sort callbacks v in
    match declared with
    |
    None => (false, 64 + callback_work)
    | Some s => let '(answer, work) :=
    rw_ri_encoded_equal sort ty s in
        (answer, 64 + callback_work + work)
    end
  |
    RWApp ty op children =>
    let fix visit (terms : list (rw_term K Sort V)) : bool * nat :=

         match terms with
      | nil => (true, 64)
      | t :: rest => let '(head, hw) :=
    rw_rp_type_atomic sort callbacks t in
          let '(tail, tw) := visit rest in (head &&
    tail, 64 + hw + tw)
      end in
    let '(typed, type_work) := visit children in
    let
    '(sorts, sort_work) := rw_rp_term_sorts children in
    let '(shape, callback_work) :=
    rw_rp_operator_shape callbacks op sorts ty in
    (typed && shape, 64 + type_work +
    sort_work + callback_work)
  end.


Fixpoint rw_rp_sub_check_atomic {K Sort V H} (sort :
    rw_queue_encoder_adapter Sort)
    (hole : rw_queue_encoder_adapter H) (callbacks :
    rw_rp_rule_callbacks K Sort V H)
    (rule : rw_rule K Sort V H) (holes : list H) (bindings
    : Map.t H (rw_term K Sort V)) :
    bool * nat :=
  match holes with
  | nil => (true, 64)

    | h :: rest =>
    let '(declared, callback_work) := rw_rp_hole_sort callbacks rule h in

    let '(head, head_work) := match declared with
      | None => (false, 64 + callback_work)

       | Some ty =>
        let '(binding, trace) := audit_map_get (rw_external_encoding_events
    hole) h bindings in
        let lookup_work := audit_map_source_work rw_external_events_work
    trace in
        match binding with
        | None => (false, 64 + callback_work +
    lookup_work)
        | Some term =>
          let '(same_sort, comparison_work) :=
    rw_ri_encoded_equal sort (rw_sort term) ty in
          if same_sort then
            let
    '(typed, type_work) := rw_rp_type_atomic sort callbacks term in
            (typed, 64 +
    callback_work + lookup_work + comparison_work + type_work)
          else (false, 64 +
    callback_work + lookup_work + comparison_work)
        end
      end in
    let '(tail,
    tail_work) := rw_rp_sub_check_atomic sort hole callbacks rule rest bindings in
    (head &&
    tail, 64 + head_work + tail_work)
  end.


Definition rw_rp_guard_atomic {K Sort V H} (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) (rule : rw_rule K Sort V H)
    (bindings : Map.t H (rw_term K Sort V)) : bool * nat :=
  let '(answer, work, _) := rw_rp_guard_execute hole bindings (rw_rp_guard callbacks rule) in
  (answer, 64 + work).


Fixpoint rw_rp_instantiate_atomic {K Sort V H} (hole : rw_queue_encoder_adapter H)
    (bindings :
    Map.t H (rw_term K Sort V)) (pattern : rw_pattern K Sort V H) :
    option (rw_term K Sort
    V) * nat :=
  match pattern with
  | RWHole _ h =>
    let '(out, trace) := audit_map_get
    (rw_external_encoding_events hole) h bindings in
    (out, 64 + audit_map_source_work
    rw_external_events_work trace)
  | RWPVar ty v => (Some (RWVar ty v), 64)
  | RWPApp ty op
    children =>
    let fix visit (ps : list (rw_pattern K Sort V H)) : option (list (rw_term K
    Sort V)) * nat :=
      match ps with
      | nil => (Some nil, 64)
      | p :: rest =>

        let '(head, hw) := rw_rp_instantiate_atomic hole bindings p in
        match head with

          | None => (None, 64 + hw)
        | Some term => let '(tail, tw) := visit rest in

           (option_map (fun ts => term :: ts) tail, 64 + hw + tw)
        end
      end in

    let '(args, work) := visit children in (option_map (RWApp ty op) args, 64 + work)

    end.


Fixpoint rw_rp_rule_lookup {K Sort V H} (rules : list (rw_rule K Sort V H)) (position
    : nat) :
    option (rw_rule K Sort V H) * nat :=
  match rules with
  | nil => (None, 64)

    | rule :: rest =>
    match position with
    | 0 => (Some rule, 64)
    | S p => let '(out,
    work) := rw_rp_rule_lookup rest p in (out, 64 + work)
    end
  end.


Fixpoint rw_rp_rule_table_atomic {K Sort V H} (rules : list (rw_rule K Sort V H))
    (index : nat) : Map.t nat (rw_rule K Sort V H) * nat :=
  match rules with
  | nil => (Map.empty, 64)
  | rule :: rest =>
    let '(table, tail_work) := rw_rp_rule_table_atomic rest (S index) in
    let '(out, trace) := audit_map_set audit_nat_encode index rule table in
    (out, 64 + tail_work + audit_map_source_work audit_nat_events_work trace)
  end.


Definition rw_rp_rule_body_gate_atomic {K Sort V H} (sort : rw_queue_encoder_adapter Sort)
    (hole : rw_queue_encoder_adapter H) (callbacks : rw_rp_rule_callbacks K Sort V H)
    (rule : rw_rule K Sort V H) (attempt : rw_attempt K Sort V H) :
    option (rw_term K Sort V * rw_term K Sort V) * nat :=
  let bindings := rw_attempt_sub attempt in
  let '(typed, type_work) :=
    rw_rp_sub_check_atomic sort hole callbacks rule (rw_holes rule) bindings in
  let '(guard, guard_work) := rw_rp_guard_atomic hole callbacks rule bindings in
  let prefix := 64 + type_work + guard_work in
  if typed && guard then
    let '(lhs, lw) := rw_rp_instantiate_atomic hole bindings (rw_lhs rule) in
    match lhs with
    | None => (None, prefix + lw)
    | Some left_term =>
      let '(rhs, rw) := rw_rp_instantiate_atomic hole bindings (rw_rhs rule) in
      (option_map (fun right_term => (left_term, right_term)) rhs, prefix + lw + rw)
    end
  else (None, prefix).


Definition rw_rp_rule_gate_prepared_atomic {K Sort V H} (sort : rw_queue_encoder_adapter Sort)
    (hole : rw_queue_encoder_adapter H) (callbacks : rw_rp_rule_callbacks K Sort V H)
    (table : Map.t nat (rw_rule K Sort V H)) (attempt : rw_attempt K Sort V H) :
    option (rw_term K Sort V * rw_term K Sort V) * nat :=
  let '(found, lookup) := audit_map_get audit_nat_encode (rw_attempt_rule attempt) table in
  let prefix := 64 + audit_map_source_work audit_nat_events_work lookup in
  match found with
  | None => (None, prefix)
  | Some rule =>
    let '(out, work) := rw_rp_rule_body_gate_atomic sort hole callbacks rule attempt in
    (out, prefix + work)
  end.


Definition rw_rp_rule_gate_atomic {K Sort V H} (sort : rw_queue_encoder_adapter Sort)
    (hole : rw_queue_encoder_adapter H) (callbacks : rw_rp_rule_callbacks K Sort V H)
    (rules : list (rw_rule K Sort V H)) (attempt : rw_attempt K Sort V H) :
    option (rw_term K Sort V * rw_term K Sort V) * nat :=
  let '(table, preparation_work) := rw_rp_rule_table_atomic rules 0 in
  let '(out, work) := rw_rp_rule_gate_prepared_atomic sort hole callbacks table attempt in
  (out, 64 + preparation_work + work).

(** The prepared natural-key table preserves every rule position, including absent indices. *)

(** This statement fixes the rp rule table erases statement contract. *)
Definition rw_rp_rule_table_erases_statement : Prop :=
  forall K Sort V H (rules : list (rw_rule K Sort V H)) index,
  Map.get nat_encoding index (fst (rw_rp_rule_table_atomic rules 0)) = nth_error rules index.

(** Instantiation follows the exact library substitution lookup and failure order.
    *)

(** This statement fixes the rp instantiate erases statement contract. *)
Definition rw_rp_instantiate_erases_statement : Prop :=
  forall K Sort V H (EH :
    encoding H) (hole : rw_queue_encoder_adapter H) bindings pattern,
  (forall h, fst
    (rw_queue_encoder_run hole h) = encode EH h) ->
  @fst (option (rw_term K Sort V)) nat
    (rw_rp_instantiate_atomic hole bindings pattern) =
    rw_instantiate (fun h => Map.get EH h
    bindings) pattern.

(** The same finite guard program agrees with the actual guard for every substitution. *)

Definition rw_rp_guard_adapter_laws {K Sort V H}
    (callbacks : rw_rp_rule_callbacks K Sort V H) : Prop :=
  forall rule sub,
    rw_rp_guard_plain sub (rw_rp_guard callbacks rule) = rw_condition rule sub.
```

## Galois.Rewrite.RewriteAuditProofApply

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditProofApply.v`.

```rocq
(** * RewriteAuditProofApply

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexFind RewriteAuditIndexMembership
  RewriteAuditIndexPair RewriteAuditIndexPrepare RewriteAuditIndexPrepareReference
  RewriteAuditIndexRebuild RewriteAuditIndexReference RewriteAuditIndexRules
  RewriteAuditProofCarrier RewriteAuditProofClosure RewriteAuditProofRebuild
  RewriteAuditProofSeed RewriteAuditProofTick RewriteAuditQueueReference
  RewriteAuditSharedReference.
Import List.ListNotations.

Definition rw_rp_accept_atomic {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV :
    encoding V) (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)

    (value : rw_queue_encoder_adapter V) (stamp : nat * nat)
    (state : rw_tracked_state K
    Sort V H) (attempt : rw_attempt K Sort V H)
    (lhs rhs : rw_term K Sort V) : option
    (rw_tracked_state K Sort V H) * nat :=
  let '(graph, graph_work) := rw_ri_graph_atomic
    (rw_tracked_machine state) in
  let '(witness_entries, witness_enum) :=

    audit_map_elements (rw_class_witness_nodes (rw_tracked_witnesses state)) in
  let '(largest,
    max_trace) :=
    @rw_ri_max_entries_atomic (rw_shared_node K Sort V) K Sort V
    witness_entries
      (rw_index_fresh (rw_tracked_machine state)) in
  let '(fresh,
    fresh_trace) := rw_fuel_pos_succ largest in
  let fresh_work := audit_elements_work
    witness_enum +
    rw_ri_fresh_trace_cost max_trace + audit_work fresh_trace in
  let acc :=
    RwRpSeedAcc graph (rw_tracked_witnesses state)
    (rw_index_fresh (rw_tracked_machine
    state)) fresh in
  let '(((rhs_root, _), grown), growth_work) := rw_rp_seed_term rhs acc in

     let '(prepared, prepare_trace) := rw_ri_prepare_once op value (rw_rp_seed_graph grown)
    in
  let prepare_work := rw_ri_prepare_once_work prepare_trace
    in
  let '(first, ft) := rw_ri_find_atomic prepared (rw_attempt_root attempt) in
  let
    prefix := 64 + graph_work + fresh_work + growth_work + prepare_work +

    rw_ri_find_trace_cost ft in
  match first with
  | None => (None, prefix)
  | Some a =>

    let '(second, st) := rw_ri_find_atomic prepared rhs_root in
    let prefix := prefix +
    rw_ri_find_trace_cost st in
    match second with
    | None => (None, prefix)
    | Some b
    =>
      let '(left_sort, lt) := audit_map_get audit_positive_encode a
        (rw_sorts
    (rw_index_base prepared)) in
      let prefix := prefix + audit_map_source_work
    audit_basic_encoding_work lt in
      match left_sort with
      | None => (None, prefix)

       | Some sa =>
        let '(right_sort, rt) := audit_map_get audit_positive_encode b

        (rw_sorts (rw_index_base prepared)) in
        let prefix := prefix +
    audit_map_source_work audit_basic_encoding_work rt in
        match right_sort with

    | None => (None, prefix)
        | Some sb =>
          let '(same_sort, sort_work) :=
    rw_ri_encoded_equal sort sa sb in
          let prefix := prefix + sort_work in
          if
    same_sort then
            let old_witnesses := rw_rp_seed_witnesses grown in

    let '(pointer, pt) := audit_map_get audit_positive_encode a

    (rw_class_witness_roots old_witnesses) in
            let prefix := prefix +
    audit_map_source_work audit_basic_encoding_work pt in
            match pointer with

        | None => (None, prefix)
            | Some p =>
              let '((machine,
    merge_event), merge_trace) := rw_ri_pair_merge_atomic
                prepared prepared (a,
    b) (rw_index_pending prepared) a b nil in
              let root := match merge_event with

                  | RWIndexCongruence _ _ _ r => r
                | _ => a
                end
    in
              let '(witnesses, witness_work) := rw_rp_witness_merge a b root p
    old_witnesses in
              let proof := rw_tracked_provenance state in
              let
    '(index, iw) := rw_rp_index_existing op sort value
                (rw_provenance_ids proof)
    proof Map.empty in
              let '((id, extended), evidence_work) := rw_rp_add_evidence
    op sort value stamp lhs rhs
                (RWEvidenceRule (rw_attempt_rule attempt)
    (rw_attempt_sub attempt))
                (RwRpConnectionState proof index) in

    let '(events, event_work) := rw_rp_stamp_put stamp id (rw_tracked_event_nodes state) in

             (Some (RWTrackedState machine (rw_rp_proof extended) witnesses events),

        prefix + rw_ri_pair_trace_cost merge_trace + witness_work + iw +

    evidence_work + event_work)
            end
          else (None, prefix)
        end

    end
    end
  end.


Definition rw_rp_rule_step_prepared_atomic {K Sort V H} (EK : encoding K) (ES :
    encoding Sort)
    (EV : encoding V) (op : rw_queue_encoder_adapter K) (sort :
    rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole :
    rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) (table : Map.t nat (rw_rule K Sort V H))
    (position : nat) (state : rw_tracked_state K Sort V H) (attempt :
    rw_attempt K Sort V H) :
    option (rw_tracked_state K Sort V H) * nat :=
  let '(gate,
    gate_work) := rw_rp_rule_gate_prepared_atomic sort hole callbacks table attempt in
  match gate with

     | None => (None, 64 + gate_work)
  | Some (lhs, rhs) =>
    let '(represented, member_work)
    := rw_ri_member_atomic op sort value
      (rw_tracked_machine state) lhs (rw_attempt_root
    attempt) in
    if represented then
      let '(accepted, work) := rw_rp_accept_atomic EK ES
    EV op sort value (S position, 0)
        state attempt lhs rhs in (accepted, 64 + gate_work
    + member_work + work)
    else (None, 64 + gate_work + member_work)
  end.



Definition rw_rp_rule_step_atomic {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) (rules : list (rw_rule K Sort V H))
    (position : nat) (state : rw_tracked_state K Sort V H) (attempt : rw_attempt K Sort V H) :
    option (rw_tracked_state K Sort V H) * nat :=
  let '(table, preparation_work) := rw_rp_rule_table_atomic rules 0 in
  let '(out, work) := rw_rp_rule_step_prepared_atomic EK ES EV op sort value hole callbacks
    table position state attempt in
  (out, 64 + preparation_work + work).


Definition rw_rp_apply_prepared_atomic {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value :
    rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks :
    rw_rp_rule_callbacks K Sort V H) (table : Map.t nat (rw_rule K Sort V H))
    (position : nat)
    (state : rw_tracked_state K Sort V H) (attempt : rw_attempt K Sort V H) :
    option
    (rw_tracked_state K Sort V H * list rw_index_event) * nat :=
  let '(stepped, step_work) :=
    rw_rp_rule_step_prepared_atomic EK ES EV op sort value hole callbacks
    table position state
    attempt in
  match stepped with
  | None => (None, 64 + step_work)
  | Some next =>
    let
    '(out, work) := rw_rp_rebuild_atomic op sort value (S position) next in
    (Some out, 64 +
    step_work + work)
  end.



Definition rw_rp_apply_atomic {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) (rules : list (rw_rule K Sort V H))
    (position : nat) (state : rw_tracked_state K Sort V H) (attempt : rw_attempt K Sort V H) :
    option (rw_tracked_state K Sort V H * list rw_index_event) * nat :=
  let '(table, preparation_work) := rw_rp_rule_table_atomic rules 0 in
  let '(out, work) := rw_rp_apply_prepared_atomic EK ES EV op sort value hole callbacks
    table position state attempt in
  (out, 64 + preparation_work + work).
```

## Galois.Rewrite.RewriteAuditIndexPrograms

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditIndexPrograms.v`.

```rocq
(** * RewriteAuditIndexPrograms

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexFind RewriteAuditIndexRebuild
  RewriteAuditIndexReference RewriteAuditQueueReference.
Import List.ListNotations.

Inductive rw_rp_query (K Sort V : Type) : Type :=
  | RPQueryFind : rw_id -> option rw_id ->
    rw_rp_query K Sort V
  | RPQuerySort : rw_id -> option Sort -> rw_rp_query K Sort V
  |
    RPQueryNode : rw_id -> option (rw_id * rw_node K Sort V) -> rw_rp_query K Sort V
  |
    RPQueryOperator : K -> list rw_id -> rw_rp_query K Sort V
  | RPQueryVariable : V -> list
    rw_id -> rw_rp_query K Sort V
  | RPQueryParents : rw_id -> list rw_id -> rw_rp_query K Sort
    V
  | RPQueryRoots : list rw_id -> rw_rp_query K Sort V
  | RPQueryNodes : list rw_id ->
    rw_rp_query K Sort V
  | RPQueryGraph : rw_graph K Sort V -> rw_rp_query K Sort V.
Arguments
    RPQueryFind {K Sort V}.
Arguments RPQuerySort {K Sort V}.
Arguments RPQueryNode {K Sort
    V}.
Arguments RPQueryOperator {K Sort V}.
Arguments RPQueryVariable {K Sort V}.
Arguments
    RPQueryParents {K Sort V}.
Arguments RPQueryRoots {K Sort V}.
Arguments RPQueryNodes {K Sort
    V}.
Arguments RPQueryGraph {K Sort V}.


Inductive rw_rp_view_request (K Sort V : Type) : Type -> Type :=
  | RPRequestFind : rw_id -> rw_rp_view_request K Sort V (option rw_id)
  | RPRequestSort : rw_id -> rw_rp_view_request K Sort V (option Sort)
  | RPRequestNode : rw_id -> rw_rp_view_request K Sort V (option (rw_id * rw_node K Sort V))
  | RPRequestOperator : K -> rw_rp_view_request K Sort V (list rw_id)
  | RPRequestVariable : V -> rw_rp_view_request K Sort V (list rw_id)
  | RPRequestParents : rw_id -> rw_rp_view_request K Sort V (list rw_id)
  | RPRequestRoots : rw_rp_view_request K Sort V (list rw_id)
  | RPRequestNodes : rw_rp_view_request K Sort V (list rw_id)
  | RPRequestGraph : rw_rp_view_request K Sort V (rw_graph K Sort V).
Arguments RPRequestFind {K Sort V}.
Arguments RPRequestSort {K Sort V}.
Arguments RPRequestNode {K Sort V}.
Arguments RPRequestOperator {K Sort V}.
Arguments RPRequestVariable {K Sort V}.
Arguments RPRequestParents {K Sort V}.
Arguments RPRequestRoots {K Sort V}.
Arguments RPRequestNodes {K Sort V}.
Arguments RPRequestGraph {K Sort V}.


Inductive rw_rp_view_program (K Sort V A : Type) : Type :=
  | RPViewReturn : A -> nat -> rw_rp_view_program K Sort V A
  | RPViewAsk : forall R, nat -> rw_rp_view_request K Sort V R ->
      (R -> rw_rp_view_program K Sort V A) -> rw_rp_view_program K Sort V A.
Arguments RPViewReturn {K Sort V A}.
Arguments RPViewAsk {K Sort V A R}.


Inductive rw_rp_provider_trace (K Sort V : Type) : Type :=
  | RPProviderFind : audit_trace rw_ri_find_call -> rw_rp_provider_trace K Sort V
  | RPProviderPositive : forall A, list (audit_map_event rw_id A
      (audit_basic_encoding_event positive)) -> rw_rp_provider_trace K Sort V
  | RPProviderOperator : list (audit_map_event K (FinSet.t rw_id) nat) ->
      rw_rp_provider_trace K Sort V
  | RPProviderVariable : list (audit_map_event V (FinSet.t rw_id) nat) ->
      rw_rp_provider_trace K Sort V
  | RPProviderElements : FinSet.t rw_id -> list rw_id ->
      list (audit_set_elements_event rw_id) -> rw_rp_provider_trace K Sort V
  | RPProviderGraph : rw_index_state K Sort V -> rw_graph K Sort V -> nat ->
      rw_rp_provider_trace K Sort V.
Arguments RPProviderFind {K Sort V}.
Arguments RPProviderPositive {K Sort V A}.
Arguments RPProviderOperator {K Sort V}.
Arguments RPProviderVariable {K Sort V}.
Arguments RPProviderElements {K Sort V}.
Arguments RPProviderGraph {K Sort V}.


Definition rw_rp_provider_trace_work {K Sort V}
    (trace : rw_rp_provider_trace K Sort V) : nat :=
  match trace with
  | RPProviderFind events => rw_ri_find_trace_cost events
  | RPProviderPositive events => audit_map_source_work audit_basic_encoding_work events
  | RPProviderOperator events => audit_map_source_work rw_external_events_work events
  | RPProviderVariable events => audit_map_source_work rw_external_events_work events
  | RPProviderElements _ _ events => audit_set_elements_work events
  | RPProviderGraph _ _ work => work
  end.


Record rw_rp_query_receipt (K Sort V : Type) := RwRpQueryReceipt {
  rw_rp_query_observation : rw_rp_query K Sort V;
  rw_rp_query_sources : list (rw_rp_provider_trace K Sort V)
}.
Arguments RwRpQueryReceipt {K Sort V}.
Arguments rw_rp_query_observation {K Sort V}.
Arguments rw_rp_query_sources {K Sort V}.


Definition rw_rp_query_receipt_work {K Sort V}
    (receipt : rw_rp_query_receipt K Sort V) : nat :=
  fold_right (fun trace total => rw_rp_provider_trace_work trace + total) 64
    (rw_rp_query_sources receipt).


Definition rw_rp_view_plain_request {K Sort V R} (view : rw_snapshot_view K Sort V)
    (request : rw_rp_view_request K Sort V R) : R :=
  let base := rw_snapshot_base view in
  match request with
  | RPRequestFind id => rw_view_find base id
  | RPRequestSort id => rw_view_sort base id
  | RPRequestNode id => rw_view_node base id
  | RPRequestOperator key => rw_view_operator_nodes base key
  | RPRequestVariable key => rw_view_variable_nodes base key
  | RPRequestParents id => rw_view_parent_nodes base id
  | RPRequestRoots => rw_view_roots base tt
  | RPRequestNodes => rw_view_nodes base tt
  | RPRequestGraph => rw_snapshot_graph view tt
  end.


Fixpoint rw_rp_view_plain {K Sort V A} (view : rw_snapshot_view K Sort V)
    (program : rw_rp_view_program K Sort V A) : A :=
  match program with
  | RPViewReturn answer _ => answer
  | RPViewAsk _ request next =>
    rw_rp_view_plain view (next (rw_rp_view_plain_request view request))
  end.


Definition rw_rp_view_execute_request {K Sort V R} (op : rw_queue_encoder_adapter K)
    (value : rw_queue_encoder_adapter V) (state : rw_index_state K Sort V)
    (request : rw_rp_view_request K Sort V R) : R * rw_rp_query_receipt K Sort V :=
  match request with
  | RPRequestFind id =>
    let '(answer, trace) := rw_ri_find_atomic state id in
    (answer, RwRpQueryReceipt (RPQueryFind id answer) [RPProviderFind trace])
  | RPRequestSort id =>
    let '(answer, trace) := audit_map_get audit_positive_encode id
      (rw_sorts (rw_index_base state)) in
    (answer, RwRpQueryReceipt (RPQuerySort id answer) [RPProviderPositive trace])
  | RPRequestNode id =>
    let '(answer, trace) := audit_map_get audit_positive_encode id
      (rw_nodes (rw_index_base state)) in
    (answer, RwRpQueryReceipt (RPQueryNode id answer) [RPProviderPositive trace])
  | RPRequestOperator key =>
    let '(found, trace) := audit_map_get (rw_external_encoding_events op) key
      (rw_index_operators state) in
    let bucket := match found with Some stored => stored | None => FinSet.empty end in
    let '(answer, elements) := audit_finset_elements bucket in
    (answer, RwRpQueryReceipt (RPQueryOperator key answer)
      [RPProviderOperator trace; RPProviderElements bucket answer elements])
  | RPRequestVariable key =>
    let '(found, trace) := audit_map_get (rw_external_encoding_events value) key
      (rw_index_variables state) in
    let bucket := match found with Some stored => stored | None => FinSet.empty end in
    let '(answer, elements) := audit_finset_elements bucket in
    (answer, RwRpQueryReceipt (RPQueryVariable key answer)
      [RPProviderVariable trace; RPProviderElements bucket answer elements])
  | RPRequestParents id =>
    let '(found, trace) := rw_ri_find_atomic state id in
    match found with
    | None => (nil, RwRpQueryReceipt (RPQueryParents id nil) [RPProviderFind trace])
    | Some root =>
      let '(stored, lookup) := audit_map_get audit_positive_encode root
        (rw_index_parent_buckets state) in
      let bucket := match stored with Some stored => stored | None => FinSet.empty end in
      let '(answer, elements) := audit_finset_elements bucket in
      (answer, RwRpQueryReceipt (RPQueryParents id answer)
        [RPProviderFind trace; RPProviderPositive lookup;
         RPProviderElements bucket answer elements])
    end
  | RPRequestRoots =>
    let '(graph, work) := rw_ri_graph_atomic state in
    (rw_roots graph, RwRpQueryReceipt (RPQueryRoots (rw_roots graph))
      [RPProviderGraph state graph work])
  | RPRequestNodes =>
    let answer := rw_nodes_in (rw_index_base state) in
    (answer, RwRpQueryReceipt (RPQueryNodes answer) nil)
  | RPRequestGraph =>
    let '(graph, work) := rw_ri_graph_atomic state in
    (graph, RwRpQueryReceipt (RPQueryGraph graph) [RPProviderGraph state graph work])
  end.


Fixpoint rw_rp_view_execute {K Sort V A} (op : rw_queue_encoder_adapter K)
    (value : rw_queue_encoder_adapter V) (state : rw_index_state K Sort V)
    (program : rw_rp_view_program K Sort V A) :
    A * nat * list (rw_rp_query_receipt K Sort V) :=
  match program with
  | RPViewReturn answer body => (answer, 64 + body, nil)
  | RPViewAsk body request next =>
    let '(answer, receipt) := rw_rp_view_execute_request op value state request in
    let '(out, later_work, later) := rw_rp_view_execute op value state (next answer) in
    (out, 64 + body + rw_rp_query_receipt_work receipt + later_work, receipt :: later)
  end.


Record rw_rp_strategy_adapter (K Sort V H : Type) := RwRpStrategyAdapter {
  rw_rp_strategy_program : rw_rp_view_program K Sort V (option (rw_attempt K Sort V H))
}.
Arguments rw_rp_strategy_program {K Sort V H}.


Definition rw_rp_strategy_run {K Sort V H} (op : rw_queue_encoder_adapter K)
    (value : rw_queue_encoder_adapter V) (adapter : rw_rp_strategy_adapter K Sort V H)
    (state : rw_index_state K Sort V) :=
  rw_rp_view_execute op value state (rw_rp_strategy_program adapter).
```

## Galois.Rewrite.RewriteAuditProofRun

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditProofRun.v`.

```rocq
(** * RewriteAuditProofRun

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexPrograms RewriteAuditIndexReference
  RewriteAuditIndexRules RewriteAuditProofApply RewriteAuditProofRebuild RewriteAuditProofSeed
  RewriteAuditProofTick RewriteAuditQueueReference.
Import List.ListNotations.

Record rw_rp_run_state (K Sort V H : Type) := RwRpRunState {
  rw_rp_current : rw_tracked_state K
    Sort V H;
  rw_rp_stopped : bool;
  rw_rp_position : nat;
  rw_rp_events : list
    (rw_run_event K Sort V H)
}.
Arguments RwRpRunState {K Sort V H}.
Arguments rw_rp_current {K
    Sort V H}.
Arguments rw_rp_stopped {K Sort V H}.
Arguments rw_rp_position {K Sort V
    H}.
Arguments rw_rp_events {K Sort V H}.


Definition rw_rp_run_once {K Sort V H} (EK :
    encoding K) (ES : encoding Sort)
    (EV : encoding V) (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole :
    rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) (table : Map.t nat (rw_rule K Sort V H))
    (strategy : rw_rp_strategy_adapter K Sort V H) (state :
    rw_rp_run_state K Sort V H) :
    rw_rp_run_state K Sort V H * nat :=
  if rw_rp_stopped
    state then (state, 64)
  else
    let tracked := rw_rp_current state in
    let '(offer, body_work, receipts) :=
      rw_rp_strategy_run op value strategy (rw_tracked_machine tracked) in
    let prefix := 64 + body_work in
    match offer with
    | None => (RwRpRunState tracked true (rw_rp_position state)
    (rw_rp_events state), prefix)
    | Some attempt =>
      let '(applied, work) :=
    rw_rp_apply_prepared_atomic EK ES EV op sort value hole callbacks table
        (rw_rp_position
    state) tracked attempt in
      match applied with
      | None => (RwRpRunState tracked
    false (S (rw_rp_position state))
          (RWRunRejected attempt :: rw_rp_events state),
    prefix + work)
      | Some (next, events) => (RwRpRunState next false (S (rw_rp_position
    state))
          (RWRunAccepted attempt events :: rw_rp_events state), prefix + work)

    end
    end.


Fixpoint rw_rp_run_repeat {K Sort V H} (EK : encoding K) (ES : encoding Sort)

       (EV : encoding V) (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter
    Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)

    (callbacks : rw_rp_rule_callbacks K Sort V H) (table : Map.t nat (rw_rule K Sort V H))

    (strategy : rw_rp_strategy_adapter K Sort V H) (fuel : positive)
    (state :
    rw_rp_run_state K Sort V H) : rw_rp_run_state K Sort V H * nat :=
  if rw_rp_stopped state
    then (state, 64)
  else match fuel with
  | xH => let '(out, work) := rw_rp_run_once EK ES
    EV op sort value hole callbacks table strategy state in
      (out, 64 + work)
  | xO rest
    => let '(middle, mw) :=
      rw_rp_run_repeat EK ES EV op sort value hole callbacks table
    strategy rest state in
      let '(out, tw) := rw_rp_run_repeat EK ES EV op sort value hole
    callbacks table strategy rest middle in
      (out, 64 + mw + tw)
  | xI rest => let
    '(first, fw) :=
      rw_rp_run_once EK ES EV op sort value hole callbacks table strategy
    state in
      let '(middle, mw) := rw_rp_run_repeat EK ES EV op sort value hole callbacks
    table strategy rest first in
      let '(out, tw) := rw_rp_run_repeat EK ES EV op sort value
    hole callbacks table strategy rest middle in
      (out, 64 + fw + mw + tw)
  end.


Record rw_tracked_output (K Sort V H : Type) := RwTrackedOutput {
  rw_tracked_final :
    rw_tracked_state K Sort V H;
  rw_tracked_stop : rw_stop;
  rw_tracked_initial : list
    rw_index_event;
  rw_tracked_events : list (rw_run_event K Sort V H)
}.
Arguments
    RwTrackedOutput {K Sort V H}.
Arguments rw_tracked_final {K Sort V H}.
Arguments
    rw_tracked_stop {K Sort V H}.
Arguments rw_tracked_initial {K Sort V H}.
Arguments
    rw_tracked_events {K Sort V H}.


Definition rw_rp_run_atomic {K Sort V H} (EK : encoding K)
    (ES : encoding Sort)
    (EV : encoding V) (op : rw_queue_encoder_adapter K) (sort :
    rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole :
    rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) (rules : list
    (rw_rule K Sort V H))
    (strategy : rw_rp_strategy_adapter K Sort V H) (fuel : N) (seed :
    rw_term K Sort V) :
    (rw_id * rw_tracked_output K Sort V H) * nat :=
  let '((root,
    initial), seed_work) := rw_rp_seed_atomic EK ES EV op value seed in
  match fuel with
  | N0
    => ((root, RwTrackedOutput initial RWFuelExhausted nil nil), 64 + seed_work)
  | Npos p =>
    let '(table, rule_preparation_work) := rw_rp_rule_table_atomic rules 0 in

      let '((ready, initial_events), initial_work) := rw_rp_rebuild_atomic op sort value 0
    initial in
    let '(final, run_work) := rw_rp_run_repeat EK ES EV op sort value hole
    callbacks table strategy p
      (RwRpRunState ready false 0 nil) in
    ((root,
    RwTrackedOutput (rw_rp_current final)
      (if rw_rp_stopped final then RWStopped else
    RWFuelExhausted)
      initial_events (rw_rp_events final)), 64 + seed_work + initial_work +
    run_work + rule_preparation_work)
  end.
```

## Galois.Rewrite.RewriteAuditIndexProgramLaws

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditIndexProgramLaws.v`.

```rocq
(** * RewriteAuditIndexProgramLaws

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexPrograms RewriteAuditIndexReference
  RewriteAuditIndexRules.
Import List.ListNotations.

Definition rw_rp_callbacks_agree {K Sort V H} (EH : encoding H)
    (sig : rw_signature K Sort
    V) (callbacks : rw_rp_rule_callbacks K Sort V H) (rules : list (rw_rule K Sort V H)) : Prop :=
  (forall v, fst (rw_rp_var_sort
    callbacks v) = rw_var_sort sig v) /\
  (forall k args result, fst (rw_rp_operator_shape
    callbacks k args result) =
    rw_operator_shape sig k args result) /\
  (forall rule h, In rule rules -> fst
    (rw_rp_hole_sort callbacks rule h) = rw_hole_sort rule h) /\
  forall rule sub, In rule rules ->
    rw_rp_guard_plain sub (rw_rp_guard callbacks rule) = rw_condition rule sub.


Definition rw_rp_query_agrees {K Sort V} (EK : encoding
    K) (EV : encoding V)
    (state : rw_index_state K Sort V) (query : rw_rp_query K Sort V) :
    Prop :=
  match query with
  | RPQueryFind id answer => answer = rw_index_find state id
  |
    RPQuerySort id answer => answer = rw_class_sort (rw_index_base state) id
  | RPQueryNode id
    answer => answer = rw_node_at (rw_index_base state) id
  | RPQueryOperator k answer =>

    answer = FinSet.elements (rw_index_bucket EK k (rw_index_operators state))
  |
    RPQueryVariable v answer =>
    answer = FinSet.elements (rw_index_bucket EV v
    (rw_index_variables state))
  | RPQueryParents id answer => answer =
    match rw_index_find
    state id with
    | None => nil
    | Some r => FinSet.elements (rw_index_bucket
    positive_encoding r (rw_index_parent_buckets state))
    end
  | RPQueryRoots answer =>
    answer = rw_roots (rw_index_graph state)
  | RPQueryNodes answer => answer = rw_nodes_in
    (rw_index_base state)
  | RPQueryGraph answer => answer = rw_index_graph state

    end.


Definition rw_rp_strategy_adapter_laws {K Sort V H} (EK : encoding K) (ES : encoding
    Sort)
    (EV : encoding V) (adapter : rw_rp_strategy_adapter K Sort V H)
    (strategy :
    rw_snapshot_view K Sort V -> option (rw_attempt K Sort V H))
    (execution : rw_snapshot_view K Sort V ->
      rw_rp_view_program K Sort V (option (rw_attempt K Sort V H)) -> Prop) : Prop :=
  forall state,
    let view := rw_index_view EK ES EV state in
    rw_rp_view_plain view (rw_rp_strategy_program adapter) = strategy view /\
    execution view (rw_rp_strategy_program adapter).
```

## Galois.Rewrite.RewriteAuditProofPublic

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditProofPublic.v`.

```rocq
(** * RewriteAuditProofPublic

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexRules RewriteAuditProofRun
  RewriteAuditProofSeed RewriteAuditQueueReference.
Import List.ListNotations.

(** This statement fixes the rp run callback bound statement contract. *)
Definition rw_rp_run_callback_bound_statement : Prop :=
  forall
    K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op :
    rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value :
    rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks :
    rw_rp_rule_callbacks K Sort V H) rules adapter fuel seed,
  let '((_, output), _) :=
    rw_rp_run_atomic EK ES EV op sort value hole callbacks rules adapter fuel seed in

    (N.of_nat (length (rw_tracked_events output)) +
    match rw_tracked_stop output with
    RWStopped => 1%N | RWFuelExhausted => 0%N end <= fuel)%N.

(** Zero fuel pays seed and index
    preparation but makes no strategy invocation or rebuild. *)

(** This statement fixes the rp run zero statement contract. *)
Definition rw_rp_run_zero_statement : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding
    Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort :
    rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole :
    rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) rules adapter
    seed,
  let '((root, state), seed_work) := @rw_rp_seed_atomic K Sort V H EK ES EV op value
    seed in
  rw_rp_run_atomic EK ES EV op sort value hole callbacks rules adapter 0%N seed =

     ((root, RwTrackedOutput state RWFuelExhausted nil nil), 64 + seed_work).
```

## Galois.Rewrite.RewriteAuditIndexRun

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditIndexRun.v`.

```rocq
(** * RewriteAuditIndexRun

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexFind RewriteAuditIndexMembership
  RewriteAuditIndexPair RewriteAuditIndexPrepare RewriteAuditIndexProgramLaws
  RewriteAuditIndexPrograms RewriteAuditIndexRebuild RewriteAuditIndexReference
  RewriteAuditIndexRules RewriteAuditQueueReference.
Import List.ListNotations.

Definition rw_ri_grow_node {K Sort V} (node : rw_node K Sort V)
    (state : rw_graph K Sort V * positive) : (rw_id * (rw_graph K Sort V * positive)) * nat :=
  let '(graph, id) := state in
  let '(aliases, alias_trace) := audit_map_set audit_positive_encode id id (rw_class_roots graph) in
  let '(sorts, st) := audit_map_set audit_positive_encode id (rw_node_sort node) (rw_sorts graph) in
  let '(nodes, nt) := audit_map_set audit_positive_encode id (id, node) (rw_nodes graph) in
  let '(fresh, ft) := rw_fuel_pos_succ id in
  ((id, (RwGraph (id :: rw_roots graph) (id :: rw_nodes_in graph) aliases sorts nodes, fresh)),
    64 + audit_map_source_work audit_basic_encoding_work alias_trace +
      audit_map_source_work audit_basic_encoding_work st +
      audit_map_source_work audit_basic_encoding_work nt + audit_work ft).


Fixpoint rw_ri_grow_term {K Sort V} (term : rw_term K Sort V)
    (state : rw_graph K Sort V * positive) : (rw_id * (rw_graph K Sort V * positive)) * nat :=
  match term with
  | RWVar ty v =>
    let '(out, work) := rw_ri_grow_node (RWNVar ty v) state in (out, 64 + work)
  | RWApp ty op terms =>
    let fix visit (terms : list (rw_term K Sort V)) (state : rw_graph K Sort V * positive) :
        (list rw_id * (rw_graph K Sort V * positive)) * nat :=
      match terms with
      | nil => ((nil, state), 64)
      | term :: rest =>
        let '((id, next), hw) := rw_ri_grow_term term state in
        let '((ids, final), tw) := visit rest next in
        ((id :: ids, final), 64 + hw + tw)
      end in
    let '((ids, next), children_work) := visit terms state in
    let '(out, work) := rw_ri_grow_node (RWNApp ty op ids) next in
    (out, 64 + children_work + work)
  end.


Definition rw_ri_accept_atomic {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (state : rw_index_state K Sort V) (attempt : rw_attempt K Sort V H)
    (rhs : rw_term K Sort V) : option (rw_index_state K Sort V) * nat :=
  let '(graph, graph_work) := rw_ri_graph_atomic state in
  let '((rhs_root, (grown, _)), growth_work) :=
    rw_ri_grow_term rhs (graph, rw_index_fresh state) in
  let '(prepared, prepare_trace) := rw_ri_prepare_once op value grown in
  let '(first, ft) := rw_ri_find_atomic prepared (rw_attempt_root attempt) in
  let prefix := 64 + graph_work + growth_work + rw_ri_prepare_once_work prepare_trace +
    rw_ri_find_trace_cost ft in
  match first with
  | None => (None, prefix)
  | Some a =>
    let '(second, st) := rw_ri_find_atomic prepared rhs_root in
    let prefix := prefix + rw_ri_find_trace_cost st in
    match second with
    | None => (None, prefix)
    | Some b =>
      let '(left_sort, lt) := audit_map_get audit_positive_encode a (rw_sorts grown) in
      let prefix := prefix + audit_map_source_work audit_basic_encoding_work lt in
      match left_sort with
      | None => (None, prefix)
      | Some sa =>
        let '(right_sort, rt) := audit_map_get audit_positive_encode b (rw_sorts grown) in
        let prefix := prefix + audit_map_source_work audit_basic_encoding_work rt in
        match right_sort with
        | None => (None, prefix)
        | Some sb =>
          let '(same_sort, comparison_work) := rw_ri_encoded_equal sort sa sb in
          if same_sort then
            let '((machine, _), trace) := rw_ri_pair_merge_atomic prepared prepared
              (rw_attempt_root attempt, rhs_root) (rw_index_pending prepared) a b nil in
            (Some machine, prefix + comparison_work + rw_ri_pair_trace_cost trace)
          else (None, prefix + comparison_work)
        end
      end
    end
  end.


Definition rw_ri_rule_step_prepared_atomic {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (hole : rw_queue_encoder_adapter H) (callbacks : rw_rp_rule_callbacks K Sort V H)
    (table : Map.t nat (rw_rule K Sort V H)) (state : rw_index_state K Sort V)
    (attempt : rw_attempt K Sort V H) : option (rw_index_state K Sort V) * nat :=
  let '(gate, gate_work) := rw_rp_rule_gate_prepared_atomic sort hole callbacks table attempt in
  match gate with
  | None => (None, 64 + gate_work)
  | Some (lhs, rhs) =>
    let '(represented, member_work) :=
      rw_ri_member_atomic op sort value state lhs (rw_attempt_root attempt) in
    if represented then
      let '(out, work) := rw_ri_accept_atomic op sort value state attempt rhs in
      (out, 64 + gate_work + member_work + work)
    else (None, 64 + gate_work + member_work)
  end.



Definition rw_ri_rule_step_atomic {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (hole : rw_queue_encoder_adapter H) (callbacks : rw_rp_rule_callbacks K Sort V H)
    (rules : list (rw_rule K Sort V H)) (state : rw_index_state K Sort V)
    (attempt : rw_attempt K Sort V H) : option (rw_index_state K Sort V) * nat :=
  let '(table, preparation_work) := rw_rp_rule_table_atomic rules 0 in
  let '(out, work) := rw_ri_rule_step_prepared_atomic op sort value hole callbacks table state
    attempt in
  (out, 64 + preparation_work + work).


Definition rw_ri_apply_prepared_atomic {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (hole : rw_queue_encoder_adapter H) (callbacks : rw_rp_rule_callbacks K Sort V H)
    (table : Map.t nat (rw_rule K Sort V H)) (state : rw_index_state K Sort V)
    (attempt : rw_attempt K Sort V H) :
    option (rw_index_state K Sort V * list rw_index_event) * nat :=
  let '(applied, work) := rw_ri_rule_step_prepared_atomic op sort value hole callbacks table
    state attempt in
  match applied with
  | None => (None, 64 + work)
  | Some next =>
    let '(out, rebuild_work) := rw_ri_rebuild_atomic op sort value next in
    (Some out, 64 + work + rebuild_work)
  end.



Definition rw_ri_apply_atomic {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (hole : rw_queue_encoder_adapter H) (callbacks : rw_rp_rule_callbacks K Sort V H)
    (rules : list (rw_rule K Sort V H)) (state : rw_index_state K Sort V)
    (attempt : rw_attempt K Sort V H) :
    option (rw_index_state K Sort V * list rw_index_event) * nat :=
  let '(table, preparation_work) := rw_rp_rule_table_atomic rules 0 in
  let '(out, work) := rw_ri_apply_prepared_atomic op sort value hole callbacks table state
    attempt in
  (out, 64 + preparation_work + work).


Record rw_ri_runner (K Sort V H : Type) := RwRiRunner {
  rw_ri_runner_state : rw_index_state K Sort V;
  rw_ri_runner_stopped : bool;
  rw_ri_runner_events : list (rw_run_event K Sort V H)
}.
Arguments RwRiRunner {K Sort V H}.
Arguments rw_ri_runner_state {K Sort V H}.
Arguments rw_ri_runner_stopped {K Sort V H}.
Arguments rw_ri_runner_events {K Sort V H}.


Definition rw_ri_run_once {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (hole : rw_queue_encoder_adapter H) (callbacks : rw_rp_rule_callbacks K Sort V H)
    (table : Map.t nat (rw_rule K Sort V H)) (strategy : rw_rp_strategy_adapter K Sort V H)
    (run : rw_ri_runner K Sort V H) : rw_ri_runner K Sort V H * nat :=
  if rw_ri_runner_stopped run then (run, 64)
  else
    let state := rw_ri_runner_state run in
    let '(offer, callback_work, _) := rw_rp_strategy_run op value strategy state in
    match offer with
    | None => (RwRiRunner state true (rw_ri_runner_events run), 64 + callback_work)
    | Some attempt =>
      let '(applied, work) := rw_ri_apply_prepared_atomic op sort value hole callbacks table
    state attempt in
      match applied with
      | None => (RwRiRunner state false (RWRunRejected attempt :: rw_ri_runner_events run),
          64 + callback_work + work)
      | Some (next, events) =>
        (RwRiRunner next false (RWRunAccepted attempt events :: rw_ri_runner_events run),
          64 + callback_work + work)
      end
    end.


Fixpoint rw_ri_run_repeat {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (hole : rw_queue_encoder_adapter H) (callbacks : rw_rp_rule_callbacks K Sort V H)
    (table : Map.t nat (rw_rule K Sort V H)) (strategy : rw_rp_strategy_adapter K Sort V H)
    (fuel : positive) (run : rw_ri_runner K Sort V H) : rw_ri_runner K Sort V H * nat :=
  if rw_ri_runner_stopped run then (run, 64)
  else match fuel with
  | xH =>
    let '(out, work) := rw_ri_run_once op sort value hole callbacks table strategy run in
    (out, 64 + work)
  | xO rest =>
    let '(middle, mw) := rw_ri_run_repeat op sort value hole callbacks table strategy rest run in
    let '(out, tw) := rw_ri_run_repeat op sort value hole callbacks table strategy rest middle in
    (out, 64 + mw + tw)
  | xI rest =>
    let '(first, fw) := rw_ri_run_once op sort value hole callbacks table strategy run in
    let '(middle, mw) := rw_ri_run_repeat op sort value hole callbacks table strategy rest first in
    let '(out, tw) := rw_ri_run_repeat op sort value hole callbacks table strategy rest middle in
    (out, 64 + fw + mw + tw)
  end.


Definition rw_ri_run_atomic {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (hole : rw_queue_encoder_adapter H) (callbacks : rw_rp_rule_callbacks K Sort V H)
    (rules : list (rw_rule K Sort V H)) (strategy : rw_rp_strategy_adapter K Sort V H)
    (fuel : N) (graph : rw_graph K Sort V) :
    (rw_run_result K Sort V * list rw_index_event * list (rw_run_event K Sort V H)) * nat :=
  match fuel with
  | N0 => ((RwRunResult graph RWFuelExhausted, nil, nil), 64)
  | Npos fuel =>
    let '(table, rule_preparation_work) := rw_rp_rule_table_atomic rules 0 in
    let '(prepared, prepare_trace) := rw_ri_prepare_once op value graph in
    let '((ready, initial_events), initial_work) := rw_ri_rebuild_atomic op sort value prepared in
    let '(final, run_work) := rw_ri_run_repeat op sort value hole callbacks table strategy fuel
      (RwRiRunner ready false nil) in
    let '(result_graph, graph_work) := rw_ri_graph_atomic (rw_ri_runner_state final) in
    ((RwRunResult result_graph
      (if rw_ri_runner_stopped final then RWStopped else RWFuelExhausted),
      initial_events, rw_ri_runner_events final),
      64 + rw_ri_prepare_once_work prepare_trace + initial_work + run_work + graph_work +
    rule_preparation_work)
  end.

(** Zero graph-only fuel performs no preparation or external callback. *)

(** This statement fixes the ri run zero source statement contract. *)
Definition rw_ri_run_zero_source_statement : Prop :=
  forall K Sort V H (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) rules strategy graph,
  rw_ri_run_atomic op sort value hole callbacks rules strategy 0%N graph =
    ((RwRunResult graph RWFuelExhausted, nil, nil), 64).


(** This statement fixes the ri run semantic statement contract. *)
Definition rw_ri_run_semantic_statement : Prop :=
  forall K Sort V H C (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) rules adapter fuel graph,
  (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
  (forall s, fst (rw_queue_encoder_run sort s) = encode ES s) ->
  (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
  (forall h, fst (rw_queue_encoder_run hole h) = encode EH h) ->
  rw_rp_callbacks_agree EH sig callbacks rules ->
  Forall (rw_rule_wf sig) rules -> Forall (rw_rule_sound sig admissible) rules ->
  rw_graph_wf sig graph -> rw_graph_sound sig admissible rules graph -> rw_productive graph ->
  let '((result, _, _), _) :=
    rw_ri_run_atomic op sort value hole callbacks rules adapter fuel graph in
  rw_graph_wf sig (rw_run_graph result) /\
  rw_graph_sound sig admissible rules (rw_run_graph result) /\
  rw_productive (rw_run_graph result) /\ rw_extends graph (rw_run_graph result) /\
  (fuel <> 0%N -> rw_clean (rw_run_graph result)).
```

## Galois.Rewrite.RewriteAuditIndexPublic

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditIndexPublic.v`.

```rocq
(** * RewriteAuditIndexPublic

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexPrepareReference RewriteAuditIndexReference
  RewriteAuditIndexTickReference.
Import List.ListNotations.

Inductive rw_index_clean_trace {K Sort V H T}
    (graph : T -> rw_graph K Sort V) (view : T -> rw_snapshot_view K Sort V)
    (apply : T -> rw_attempt K Sort V H -> option (T * list rw_index_event))
    (strategy : rw_snapshot_view K Sort V -> option (rw_attempt K Sort V H)) :
    T -> list (rw_run_event K Sort V H) -> T -> Prop :=
  | RWIndexCleanTraceNil : forall state,
      rw_snapshot_agrees (graph state) (view state) -> rw_clean (graph state) ->
      rw_index_clean_trace graph view apply strategy state nil state
  | RWIndexCleanTraceReject : forall state final attempt events,
      rw_snapshot_agrees (graph state) (view state) -> rw_clean (graph state) ->
      strategy (view state) = Some attempt -> apply state attempt = None ->
      rw_index_clean_trace graph view apply strategy state events final ->
      rw_index_clean_trace graph view apply strategy state (RWRunRejected attempt :: events) final
  | RWIndexCleanTraceAccept : forall state next final attempt merges events,
      rw_snapshot_agrees (graph state) (view state) -> rw_clean (graph state) ->
      strategy (view state) = Some attempt -> apply state attempt = Some (next, merges) ->
      rw_index_clean_trace graph view apply strategy next events final ->
rw_index_clean_trace graph view apply strategy state (RWRunAccepted attempt merges ::
    events) final.


Definition rw_index_result {K Sort V} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (g : rw_graph K Sort V) : rw_graph K Sort V :=
  rw_index_graph (fst (rw_index_rebuild EK ES EV (rw_index_build EK ES EV g))).


(** This statement fixes the index clean contract. *)
Definition rw_index_clean_contract : Prop :=
  forall K Sort V H C (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (sig : rw_signature K Sort V) (admissible : rw_semantics K Sort V C -> Prop)
    (rules : list (rw_rule K Sort V H)) (g : rw_graph K Sort V),
    rw_graph_wf sig g -> rw_graph_sound sig admissible rules g -> rw_productive g ->
    rw_index_phase_clean EK ES EV
      (fst (rw_index_rebuild EK ES EV (rw_index_build EK ES EV g))) /\
    rw_graph_wf sig (rw_index_result EK ES EV g) /\
    rw_clean (rw_index_result EK ES EV g) /\ rw_productive (rw_index_result EK ES EV g).


(** This statement fixes the index sound contract. *)
Definition rw_index_sound_contract : Prop :=
  forall K Sort V H C (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (sig : rw_signature K Sort V) (admissible : rw_semantics K Sort V C -> Prop)
    (rules : list (rw_rule K Sort V H)) (g : rw_graph K Sort V),
    rw_graph_wf sig g -> rw_graph_sound sig admissible rules g -> rw_productive g ->
    rw_graph_sound sig admissible rules (rw_index_result EK ES EV g).


(** This statement fixes the index witness contract. *)
Definition rw_index_witness_contract : Prop :=
  forall K Sort V H C (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (sig : rw_signature K Sort V) (admissible : rw_semantics K Sort V C -> Prop)
    (rules : list (rw_rule K Sort V H)) (g : rw_graph K Sort V),
    rw_graph_wf sig g -> rw_graph_sound sig admissible rules g -> rw_productive g ->
    forall c t, rw_represents g c t -> rw_represents (rw_index_result EK ES EV g) c t.


Definition index_nonempty_buckets {K Sort V} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (state : rw_index_state K Sort V) : Prop :=
  (forall key bucket, Map.get EK key (rw_index_operators state) = Some bucket ->
    exists node, FinSet.mem positive_encoding node bucket = true) /\
  (forall key bucket, Map.get EV key (rw_index_variables state) = Some bucket ->
    exists node, FinSet.mem positive_encoding node bucket = true) /\
  (forall key bucket, Map.get (rw_node_encoding EK ES EV) key
      (rw_index_signatures state) = Some bucket ->
    exists node, FinSet.mem positive_encoding node bucket = true).


Definition index_parent_support {K Sort V} (state : rw_index_state K Sort V) : Prop :=
  forall root bucket,
    Map.get positive_encoding root (rw_index_parent_buckets state) = Some bucket ->
    In root (rw_roots (rw_index_base state)).


Definition index_supported_valid {K Sort V} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (sig : rw_signature K Sort V) (state : rw_index_state K Sort V) : Prop :=
  rw_index_valid EK ES EV sig state /\ index_nonempty_buckets EK ES EV state /\
  index_parent_support state.


(** This statement fixes the index support cardinality type contract. *)
Definition index_support_cardinality_type : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
      (sig : rw_signature K Sort V) (state : rw_index_state K Sort V),
    index_supported_valid EK ES EV sig state ->
    Map.size (rw_index_operators state) <= length (rw_nodes_in (rw_index_base state)) /\
    Map.size (rw_index_variables state) <= length (rw_nodes_in (rw_index_base state)) /\
    Map.size (rw_index_signatures state) <= length (rw_nodes_in (rw_index_base state)) /\
    Map.size (rw_index_parent_buckets state) <= length (rw_roots (rw_index_base state)).


(** This statement fixes the index supported cardinality contract. *)
Definition index_supported_cardinality_contract : Prop := index_support_cardinality_type.


Definition bucket_member_count {K} (table : Map.t K (FinSet.t positive)) : nat :=
  fold_right (fun entry total => FinSet.size (snd entry) + total) 0 (Map.elements table).


Definition bucket_node_support {K} (E : encoding K) (nodes : list positive)
    (table : Map.t K (FinSet.t positive)) : Prop :=
  forall key bucket, Map.get E key table = Some bucket ->
    FinSet.wf positive_encoding bucket /\
    forall node, FinSet.mem positive_encoding node bucket = true -> In node nodes.


Definition index_bucket_node_support {K Sort V} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (state : rw_index_state K Sort V) : Prop :=
  let nodes := rw_nodes_in (rw_index_base state) in
  bucket_node_support EK nodes (rw_index_operators state) /\
  bucket_node_support EV nodes (rw_index_variables state) /\
  bucket_node_support (rw_node_encoding EK ES EV) nodes (rw_index_signatures state) /\
  bucket_node_support positive_encoding nodes (rw_index_parent_buckets state).

(** Under the stronger support, memberships are bounded by graph-list products. *)

(** This statement fixes the index member node bound contract. *)
Definition index_member_node_bound_contract : Prop := forall K Sort V (EK : encoding K) (ES :
    encoding Sort)
    (EV : encoding V) (sig : rw_signature K Sort V) (state : rw_index_state K Sort V),
  index_supported_valid EK ES EV sig state -> index_bucket_node_support EK ES EV state ->
  let nodes := length (rw_nodes_in (rw_index_base state)) in
  let roots := length (rw_roots (rw_index_base state)) in
  bucket_member_count (rw_index_operators state) <= nodes * nodes /\
  bucket_member_count (rw_index_variables state) <= nodes * nodes /\
  bucket_member_count (rw_index_signatures state) <= nodes * nodes /\
  bucket_member_count (rw_index_parent_buckets state) <= roots * nodes.


(** This statement fixes the index build supported contract. *)
Definition rw_index_build_supported_contract : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (sig : rw_signature K Sort V) (g : rw_graph K Sort V),
    rw_graph_wf sig g ->
    let state := rw_index_build EK ES EV g in
    rw_index_graph state = g /\ index_supported_valid EK ES EV sig state /\
    index_bucket_node_support EK ES EV state.


(** This statement fixes the index tick supported contract. *)
Definition rw_index_tick_supported_contract : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (sig : rw_signature K Sort V) (state next : rw_index_state K Sort V) event,
    index_supported_valid EK ES EV sig state -> index_bucket_node_support EK ES EV state ->
    rw_index_tick EK ES EV state = Some (next, event) ->
    index_supported_valid EK ES EV sig next /\ index_bucket_node_support EK ES EV next.
```

## Galois.Rewrite.RewriteAuditProofFacts

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditProofFacts.v`.

```rocq
(** * RewriteAuditProofFacts

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexPrograms RewriteAuditIndexReference
  RewriteAuditIndexRules RewriteAuditProofApply RewriteAuditProofRebuild RewriteAuditProofRun
  RewriteAuditProofTick RewriteAuditQueueReference.
Import List.ListNotations.

Inductive rw_rp_fact_program (K Sort V H F : Type) : Type :=
  | RPFactReturn : option (rw_attempt K Sort V H) -> nat -> rw_rp_fact_program K Sort V H F
  | RPFactView : forall R, nat -> rw_rp_view_request K Sort V R ->
      (R -> rw_rp_fact_program K Sort V H F) -> rw_rp_fact_program K Sort V H F
  | RPFactLookup : nat -> rw_id ->
      (F -> rw_rp_fact_program K Sort V H F) -> rw_rp_fact_program K Sort V H F.
Arguments RPFactReturn {K Sort V H F}.
Arguments RPFactView {K Sort V H F R}.
Arguments RPFactLookup {K Sort V H F}.


Inductive rw_rp_fact_receipt (K Sort V F : Type) : Type :=
  | RPFactSnapshot : rw_rp_query_receipt K Sort V -> rw_rp_fact_receipt K Sort V F
  | RPFactRead : list (audit_map_event rw_id F (audit_basic_encoding_event positive)) ->
      rw_rp_fact_receipt K Sort V F.
Arguments RPFactSnapshot {K Sort V F}.
Arguments RPFactRead {K Sort V F}.


Record rw_rp_fact_strategy_adapter (K Sort V H F : Type) := RwRpFactStrategyAdapter {
  rw_rp_fact_strategy_program : rw_rp_fact_program K Sort V H F
}.
Arguments rw_rp_fact_strategy_program {K Sort V H F}.


Fixpoint rw_rp_fact_execute {K Sort V H F} (op : rw_queue_encoder_adapter K)
    (value : rw_queue_encoder_adapter V) (state : rw_index_state K Sort V)
    (unknown : F) (facts : Map.t rw_id F) (program : rw_rp_fact_program K Sort V H F) :
    option (rw_attempt K Sort V H) * nat * list (rw_rp_fact_receipt K Sort V F) :=
  match program with
  | RPFactReturn offer body => (offer, 64 + body, nil)
  | RPFactView body request next =>
    let '(answer, receipt) := rw_rp_view_execute_request op value state request in
    let '(offer, later_work, later) := rw_rp_fact_execute op value state unknown facts (next
    answer) in
    (offer, 64 + body + rw_rp_query_receipt_work receipt + later_work,
      RPFactSnapshot receipt :: later)
  | RPFactLookup body id next =>
    let '(answer, trace) := audit_map_get audit_positive_encode id facts in
    let observed := match answer with Some fact => fact | None => unknown end in
    let '(offer, later_work, later) := rw_rp_fact_execute op value state unknown facts (next
    observed) in
    (offer, 64 + body + audit_map_source_work audit_basic_encoding_work trace + later_work,
      RPFactRead trace :: later)
  end.


Definition rw_rp_fact_strategy_run {K Sort V H F} (op : rw_queue_encoder_adapter K)
    (value : rw_queue_encoder_adapter V) (adapter : rw_rp_fact_strategy_adapter K Sort V H F)
    (state : rw_index_state K Sort V) (unknown : F) (facts : Map.t rw_id F) :=
  rw_rp_fact_execute op value state unknown facts (rw_rp_fact_strategy_program adapter).


Definition rw_rp_fact_run_once {K Sort V H F} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding
    V) (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value :
    rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks :
    rw_rp_rule_callbacks K Sort V H) (table : Map.t nat (rw_rule K Sort V H)) (unknown : F)
    (strategy :
    rw_rp_fact_strategy_adapter K Sort V H F)
    (state : rw_rp_run_state K Sort V H * Map.t
    rw_id F) :
    (rw_rp_run_state K Sort V H * Map.t rw_id F) * nat :=
  let '(run, facts) :=
    state in
  if rw_rp_stopped run then (state, 64)
  else
    let tracked := rw_rp_current run
    in
    let '(offer, body_work, receipts) := rw_rp_fact_strategy_run op value strategy
      (rw_tracked_machine tracked) unknown facts in
    let prefix := 64 + body_work in

    match offer with
    | None => ((RwRpRunState tracked true (rw_rp_position run)
    (rw_rp_events run), facts), prefix)
    | Some attempt =>
      let '(applied, work) :=
    rw_rp_apply_prepared_atomic EK ES EV op sort value hole callbacks table
        (rw_rp_position run)
    tracked attempt in
      match applied with
      | None => ((RwRpRunState tracked false (S
    (rw_rp_position run))
          (RWRunRejected attempt :: rw_rp_events run), facts), prefix
    + work)
      | Some (next, events) => ((RwRpRunState next false (S (rw_rp_position run))

           (RWRunAccepted attempt events :: rw_rp_events run), Map.empty), prefix + work + 64)

        end
    end.


Fixpoint rw_rp_fact_run_repeat {K Sort V H F} (EK : encoding K) (ES :
    encoding Sort)
    (EV : encoding V) (op : rw_queue_encoder_adapter K) (sort :
    rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole :
    rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) (table : Map.t nat (rw_rule K Sort V H))
    (unknown : F)
    (strategy : rw_rp_fact_strategy_adapter K Sort V H F) (fuel :
    positive)
    (state : rw_rp_run_state K Sort V H * Map.t rw_id F) :
    (rw_rp_run_state K
    Sort V H * Map.t rw_id F) * nat :=
  if rw_rp_stopped (fst state) then (state, 64)
  else
    match fuel with
  | xH => let '(out, work) := rw_rp_fact_run_once EK ES EV op sort value
    hole callbacks table unknown strategy state in
      (out, 64 + work)
  | xO rest => let '(middle,
    mw) :=
      rw_rp_fact_run_repeat EK ES EV op sort value hole callbacks table unknown strategy rest
    state in
      let '(out, tw) := rw_rp_fact_run_repeat EK ES EV op sort value hole callbacks table unknown
    strategy rest middle in
      (out, 64 + mw + tw)
  | xI rest => let '(first, fw) :=

        rw_rp_fact_run_once EK ES EV op sort value hole callbacks table unknown strategy state in

    let '(middle, mw) := rw_rp_fact_run_repeat EK ES EV op sort value hole callbacks table
    unknown strategy rest first in
      let '(out, tw) := rw_rp_fact_run_repeat EK ES EV op sort value
    hole callbacks table unknown strategy rest middle in
      (out, 64 + fw + mw + tw)

    end.


Definition rw_rp_fact_run_atomic {K Sort V H F} (EK : encoding K) (ES : encoding
    Sort)
    (EV : encoding V) (op : rw_queue_encoder_adapter K) (sort :
    rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole :
    rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) (rules : list
    (rw_rule K Sort V H)) (unknown : F)
    (strategy : rw_rp_fact_strategy_adapter K Sort V H F) (fuel : N)

      (input : rw_tracked_state K Sort V H * Map.t rw_id F) :
    (rw_tracked_output K Sort V H
    * Map.t rw_id F) * nat :=
  let '(initial, facts) := input in
  match fuel with
  | N0 =>
    ((RwTrackedOutput initial RWFuelExhausted nil nil, facts), 64)
  | Npos p =>
    let '(table, rule_preparation_work) := rw_rp_rule_table_atomic rules 0 in
    let
    '((ready, initial_events), initial_work) := rw_rp_rebuild_atomic op sort value 0 initial in

       let '((final, retained), run_work) :=
      rw_rp_fact_run_repeat EK ES EV op sort value
    hole callbacks table unknown strategy p
        (RwRpRunState ready false 0 nil, Map.empty) in

    ((RwTrackedOutput (rw_rp_current final)
      (if rw_rp_stopped final then RWStopped else
    RWFuelExhausted)
      initial_events (rw_rp_events final), retained), 128 + initial_work +
    run_work + rule_preparation_work)
  end.

(** A positive-budget callback can never observe facts retained across the
    initial rebuild. *)

(** This statement fixes the rp fact initial invalidation statement contract. *)
Definition rw_rp_fact_initial_invalidation_statement : Prop :=
  forall
    K Sort V H F (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op :
    rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value :
    rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks :
    rw_rp_rule_callbacks K Sort V H) rules (unknown : F)
    (adapter : rw_rp_fact_strategy_adapter K Sort V H
    F) p initial first second,
  rw_rp_fact_run_atomic EK ES EV op sort value hole callbacks
    rules unknown adapter (Npos p)
    (initial, first) =
  rw_rp_fact_run_atomic EK ES EV op sort value
    hole callbacks rules unknown adapter (Npos p)
    (initial, second).
```

## Galois.Rewrite.RewriteAuditProofRepresentation

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditProofRepresentation.v`.

```rocq
(** * RewriteAuditProofRepresentation

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexMembership RewriteAuditIndexReference
  RewriteAuditQueueReference.
Import List.ListNotations.

Record rw_repr_node (K Sort V : Type) := RWReprNode {
  rw_repr_class : rw_id;
  rw_repr_graph_node : rw_id;
  rw_repr_term : rw_term K Sort V;
  rw_repr_children : list positive
}.
Arguments RWReprNode {K Sort V}.
Arguments rw_repr_class {K Sort V}.
Arguments rw_repr_graph_node {K Sort V}.
Arguments rw_repr_term {K Sort V}.
Arguments rw_repr_children {K Sort V}.


Record rw_repr_witness (K Sort V : Type) := RWReprWitness {
  rw_repr_root : positive;
  rw_repr_ids : list positive;
  rw_repr_nodes : Map.t positive (rw_repr_node K Sort V)
}.
Arguments RWReprWitness {K Sort V}.
Arguments rw_repr_root {K Sort V}.
Arguments rw_repr_ids {K Sort V}.
Arguments rw_repr_nodes {K Sort V}.


Definition rw_repr_node_valid {K Sort V} (g : rw_graph K Sort V)
    (w : rw_repr_witness K Sort V) (id : positive) (n : rw_repr_node K Sort V) : Prop :=
  exists owner root graph_node,
    rw_node_at g (rw_repr_graph_node n) = Some (owner, graph_node) /\
    rw_find g owner = Some root /\ rw_find g (rw_repr_class n) = Some root /\
    match graph_node, rw_repr_term n with
    | RWNVar s v, RWVar s' v' => s = s' /\ v = v' /\ rw_repr_children n = nil
    | RWNApp s op ids, RWApp s' op' terms =>
      s = s' /\ op = op' /\ length ids = length terms /\
      Forall2 (fun child pair => (child < id)%positive /\
        exists m, Map.get positive_encoding child (rw_repr_nodes w) = Some m /\
          rw_repr_class m = fst pair /\ rw_repr_term m = snd pair)
        (rw_repr_children n) (combine ids terms)
    | _, _ => False
    end.


Definition rw_repr_witness_valid {K Sort V} (g : rw_graph K Sort V)
    (c : rw_id) (t : rw_term K Sort V) (w : rw_repr_witness K Sort V) : Prop :=
  NoDup (rw_repr_ids w) /\ Map.wf positive_encoding (rw_repr_nodes w) /\
  (forall id, In id (rw_repr_ids w) <->
    exists n, Map.get positive_encoding id (rw_repr_nodes w) = Some n) /\
  (exists n, Map.get positive_encoding (rw_repr_root w) (rw_repr_nodes w) = Some n /\
    rw_repr_class n = c /\ rw_repr_term n = t) /\
  forall id n, Map.get positive_encoding id (rw_repr_nodes w) = Some n ->
    rw_repr_node_valid g w id n.


Record rw_rp_repr_acc (K Sort V : Type) := RwRpReprAcc {
  rw_rp_repr_ids : list positive;
  rw_rp_repr_nodes : Map.t positive (rw_repr_node K Sort V);
  rw_rp_repr_next : positive
}.
Arguments RwRpReprAcc {K Sort V}.
Arguments rw_rp_repr_ids {K Sort V}.
Arguments rw_rp_repr_nodes {K Sort V}.
Arguments rw_rp_repr_next {K Sort V}.


Definition rw_rp_repr_emit {K Sort V} (node : rw_repr_node K Sort V)
    (acc : rw_rp_repr_acc K Sort V) : (positive * rw_rp_repr_acc K Sort V) * nat :=
  let id := rw_rp_repr_next acc in
  let '(nodes, trace) := audit_map_set audit_positive_encode id node (rw_rp_repr_nodes acc) in
  let '(fresh, successor_trace) := rw_fuel_pos_succ id in
  ((id, RwRpReprAcc (id :: rw_rp_repr_ids acc) nodes fresh),
    64 + audit_map_source_work audit_basic_encoding_work trace + audit_work successor_trace).


Fixpoint rw_rp_repr_term_atomic {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (state : rw_index_state K Sort V) (term : rw_term K Sort V) (root : rw_id)
    (acc : rw_rp_repr_acc K Sort V) {struct term} :
    option (positive * rw_rp_repr_acc K Sort V) * nat :=
  let key_match := fun owner ty other_ty =>
    let '(same_sort, sw) := rw_ri_encoded_equal sort ty other_ty in
    if same_sort then
      let '(same_class, cw) := rw_ri_same_class_atomic state root owner in
      (same_class, 64 + sw + cw)
    else (false, 64 + sw) in
  match term with
  | RWVar ty v =>
    let '(candidates, bw) := rw_ri_bucket_ids (rw_external_encoding_events value)
      rw_external_events_work v (rw_index_variables state) in
    let fix visit (ids : list rw_id) : option (positive * rw_rp_repr_acc K Sort V) * nat :=
      match ids with
      | nil => (None, 64)
      | id :: rest =>
        let '(found, trace) := audit_map_get audit_positive_encode id
          (rw_nodes (rw_index_base state)) in
        let prefix := 64 + audit_map_source_work audit_basic_encoding_work trace in
        let '(candidate, candidate_work) :=
          match found with
          | Some (owner, RWNVar declared other) =>
            let '(same, kw) := key_match owner ty declared in
            if same then
              let '(same_value, vw) := rw_ri_encoded_equal value v other in
              if same_value then
                let '(out, ew) := rw_rp_repr_emit (RWReprNode root id term nil) acc in
                (Some out, kw + vw + ew)
              else (None, kw + vw)
            else (None, kw)
          | _ => (None, 64)
          end in
        match candidate with
        | Some out => (Some out, prefix + candidate_work)
        | None => let '(out, later_work) := visit rest in
            (out, prefix + candidate_work + later_work)
        end
      end in
    let '(out, work) := visit candidates in (out, 64 + bw + work)
  | RWApp ty key terms =>
    let '(candidates, bw) := rw_ri_bucket_ids (rw_external_encoding_events op)
      rw_external_events_work key (rw_index_operators state) in
    let fix visit (ids : list rw_id) : option (positive * rw_rp_repr_acc K Sort V) * nat :=
      match ids with
      | nil => (None, 64)
      | id :: rest =>
        let '(found, trace) := audit_map_get audit_positive_encode id
          (rw_nodes (rw_index_base state)) in
        let prefix := 64 + audit_map_source_work audit_basic_encoding_work trace in
        let '(candidate, candidate_work) :=
          match found with
          | Some (owner, RWNApp declared other children) =>
            let '(same, kw) := key_match owner ty declared in
            if same then
              let '(same_op, ow) := rw_ri_encoded_equal op key other in
              if same_op then
                let fix descend (ts : list (rw_term K Sort V)) (cs : list rw_id)
                    (acc : rw_rp_repr_acc K Sort V) :
                    option (list positive * rw_rp_repr_acc K Sort V) * nat :=
                  match ts, cs with
                  | nil, nil => (Some (nil, acc), 64)
                  | t :: ts, c :: cs =>
                    let '(head, hw) := rw_rp_repr_term_atomic op sort value state t c acc in
                    match head with
                    | None => (None, 64 + hw)
                    | Some (pointer, next) =>
                      let '(tail, tw) := descend ts cs next in
                      (option_map (fun pair => (pointer :: fst pair, snd pair)) tail,
                        64 + hw + tw)
                    end
                  | _, _ => (None, 64)
                  end in
                let '(children, cw) := descend terms children acc in
                match children with
                | None => (None, kw + ow + cw)
                | Some (pointers, next) =>
                  let '(out, ew) := rw_rp_repr_emit (RWReprNode root id term pointers) next in
                  (Some out, kw + ow + cw + ew)
                end
              else (None, kw + ow)
            else (None, kw)
          | _ => (None, 64)
          end in
        match candidate with
        | Some out => (Some out, prefix + candidate_work)
        | None => let '(out, later_work) := visit rest in
            (out, prefix + candidate_work + later_work)
        end
      end in
    let '(out, work) := visit candidates in (out, 64 + bw + work)
  end.


Definition rw_rp_repr_find_atomic {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (state : rw_index_state K Sort V) (root : rw_id) (term : rw_term K Sort V) :
    option (rw_repr_witness K Sort V) * nat :=
  let '(found, work) := rw_rp_repr_term_atomic op sort value state term root
    (RwRpReprAcc nil Map.empty 1%positive) in
  (option_map (fun pair =>
    RWReprWitness (fst pair) (rw_rp_repr_ids (snd pair)) (rw_rp_repr_nodes (snd pair))) found,
    64 + work).

(** The computational finder returns exactly a valid witness or proves absence on valid phases. *)

(** This statement fixes the rp repr find spec statement contract. *)
Definition rw_rp_repr_find_spec_statement : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (sig : rw_signature K Sort V) state root term,
  (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
  (forall s, fst (rw_queue_encoder_run sort s) = encode ES s) ->
  (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
  rw_graph_wf sig (rw_index_graph state) ->
  rw_snapshot_agrees (rw_index_graph state) (rw_index_view EK ES EV state) ->
  match fst (rw_rp_repr_find_atomic op sort value state root term) with
  | Some witness => rw_repr_witness_valid (rw_index_graph state) root term witness
  | None => ~ rw_represents (rw_index_graph state) root term
  end.
```

## Galois.Rewrite.RewriteAuditProofSelected

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditProofSelected.v`.

```rocq
(** * RewriteAuditProofSelected

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexMembership RewriteAuditIndexProgramLaws
  RewriteAuditIndexReference RewriteAuditIndexRules RewriteAuditProofCarrier
  RewriteAuditProofClosure RewriteAuditProofRebuild RewriteAuditProofRun RewriteAuditProofTick
  RewriteAuditQueueReference.
Import List.ListNotations.

Definition rw_rp_selected_atomic {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (state : rw_tracked_state K Sort V H) (root : rw_id)
    (seed tree : rw_term K Sort V) : option (rw_provenance K Sort V H * positive) * nat :=
  let machine := rw_tracked_machine state in
  let '(source_member, source_work) := rw_ri_member_atomic op sort value machine seed root in
  let '(tree_member, tree_work) := rw_ri_member_atomic op sort value machine tree root in
  if source_member && tree_member then
    let '(out, connection_work) :=
      rw_rp_connect_atomic op sort value (rw_tracked_provenance state) seed tree in
    (out, 64 + source_work + tree_work + connection_work)
  else (None, 64 + source_work + tree_work).


(** This statement fixes the rp run semantic statement contract. *)
Definition rw_rp_run_semantic_statement : Prop :=
  forall K Sort V H C (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) rules adapter fuel seed,
  (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
  (forall s, fst (rw_queue_encoder_run sort s) = encode ES s) ->
  (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
  (forall h, fst (rw_queue_encoder_run hole h) = encode EH h) ->
  rw_rp_callbacks_agree EH sig callbacks rules ->
  Forall (rw_rule_wf sig) rules -> Forall (rw_rule_sound sig admissible) rules ->
  rw_typed sig seed ->
  let '((root, output), _) :=
    rw_rp_run_atomic EK ES EV op sort value hole callbacks rules adapter fuel seed in
  let state := rw_tracked_final output in
  let graph := rw_index_graph (rw_tracked_machine state) in
  rw_graph_wf sig graph /\ rw_graph_sound sig admissible rules graph /\
  rw_productive graph /\ rw_represents graph root seed /\
  (fuel <> 0%N -> rw_clean graph) /\
  rw_rp_phase_connected EK ES EV state /\
  rw_provenance_valid EH sig rules (rw_tracked_provenance state).

(** Every represented selected endpoint has a finite explanation from the actual phase
    provenance. *)

(** This statement fixes the rp selected complete statement contract. *)
Definition rw_rp_selected_complete_statement : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (state : rw_tracked_state K Sort V H)
    (sig : rw_signature K Sort V) rules root seed tree,
  (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
  (forall s, fst (rw_queue_encoder_run sort s) = encode ES s) ->
  (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
  rw_graph_wf sig (rw_index_graph (rw_tracked_machine state)) ->
  rw_rp_phase_connected EK ES EV state ->
  rw_provenance_valid EH sig rules (rw_tracked_provenance state) ->
  rw_represents (rw_index_graph (rw_tracked_machine state)) root seed ->
  rw_represents (rw_index_graph (rw_tracked_machine state)) root tree ->
  exists proof id node,
    fst (rw_rp_selected_atomic op sort value state root seed tree) = Some (proof, id) /\
    rw_provenance_valid EH sig rules proof /\
    Map.get positive_encoding id (rw_provenance_nodes proof) = Some node /\
    rw_evidence_left node = seed /\ rw_evidence_right node = tree.
```

## Galois.Rewrite.RewriteAuditProofSemantic

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditProofSemantic.v`.

```rocq
(** * RewriteAuditProofSemantic

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexReference RewriteAuditProofCarrier
  RewriteAuditProofRepresentation RewriteAuditProofTick RewriteAuditSharedReference.
Import List.ListNotations.

Definition rw_tracked_graph {K Sort V H} (state : rw_tracked_state K Sort V H) :=
  rw_index_graph (rw_tracked_machine state).


Definition rw_class_witnesses_valid {K Sort V} (g : rw_graph K Sort V)
    (store : rw_class_witness_store K Sort V) : Prop :=
  Map.wf positive_encoding (rw_class_witness_nodes store) /\
  Map.wf positive_encoding (rw_class_witness_roots store) /\
  (forall root pointer,
    Map.get positive_encoding root (rw_class_witness_roots store) = Some pointer ->
    rw_find g root = Some root) /\
  forall c root, rw_find g c = Some root ->
    exists pointer term,
      Map.get positive_encoding root (rw_class_witness_roots store) = Some pointer /\
      let dag := RwSharedTree K Sort V pointer (rw_class_witness_nodes store) in
      rw_shared_wf dag /\ rw_shared_unfold dag = Some term /\ rw_represents g root term.



Definition rw_provenance_extends {K Sort V H} (old new : rw_provenance K Sort V H) : Prop :=
  forall id node, Map.get positive_encoding id (rw_provenance_nodes old) = Some node ->
    Map.get positive_encoding id (rw_provenance_nodes new) = Some node.

Definition rw_provenance_rule_stable {K Sort V H} (old new : rw_provenance K Sort V H) : Prop :=
  forall id node index bindings,
    Map.get positive_encoding id (rw_provenance_nodes new) = Some node ->
    rw_evidence_reason_of node = RWEvidenceRule index bindings ->
    Map.get positive_encoding id (rw_provenance_nodes old) = Some node.


Definition rw_class_connected {K Sort V H} (EH : encoding H) (sig : rw_signature K Sort V)
    (rules : list (rw_rule K Sort V H))
    (unfold_tree : rw_shared_tree K Sort V -> option (rw_term K Sort V))
    (connect : rw_graph K Sort V -> rw_provenance K Sort V H -> rw_id ->
      rw_term K Sort V -> rw_term K Sort V -> rw_repr_witness K Sort V ->
      option (rw_provenance K Sort V H * positive))
    (graph : rw_graph K Sort V) (store : rw_class_witness_store K Sort V)
    (proof : rw_provenance K Sort V H) : Prop :=
  forall current,
    rw_provenance_valid EH sig rules current -> rw_provenance_extends proof current ->
  forall c root pointer base term witness,
    rw_find graph c = Some root ->
    Map.get positive_encoding root (rw_class_witness_roots store) = Some pointer ->
    unfold_tree (RwSharedTree K Sort V pointer (rw_class_witness_nodes store)) = Some base ->
    rw_repr_witness_valid graph c term witness ->
    exists extended id node,
      connect graph current c base term witness = Some (extended, id) /\
      rw_provenance_extends current extended /\ rw_provenance_rule_stable current extended /\
      rw_provenance_valid EH sig rules extended /\
      Map.get positive_encoding id (rw_provenance_nodes extended) = Some node /\
      rw_evidence_left node = base /\ rw_evidence_right node = term.


Definition rw_tracked_event_index_valid {K Sort V H}
      (state : rw_tracked_state K Sort V H) (initial : list rw_index_event)
      (events : list (rw_run_event K Sort V H)) : Prop :=
    let index := rw_tracked_event_nodes state in
    let proof := rw_tracked_provenance state in
    let E := pair_encoding nat_encoding nat_encoding in
    Map.wf E index /\
    (forall position item a b root,
      nth_error initial position = Some (RWIndexCongruence item a b root) ->
      exists id node, Map.get E (0, S position) index = Some id /\
        Map.get positive_encoding id (rw_provenance_nodes proof) = Some node /\
        rw_evidence_time node = (0, S position)) /\
    (forall position attempt rebuild_events,
      nth_error (rev events) position = Some (RWRunAccepted attempt rebuild_events) ->
      exists id node, Map.get E (S position, 0) index = Some id /\
        Map.get positive_encoding id (rw_provenance_nodes proof) = Some node /\
        rw_evidence_time node = (S position, 0) /\
rw_evidence_reason_of node = RWEvidenceRule (rw_attempt_rule attempt) (rw_attempt_sub
    attempt)) /\
    forall position attempt rebuild_events subposition item a b root,
      nth_error (rev events) position = Some (RWRunAccepted attempt rebuild_events) ->
      nth_error rebuild_events subposition = Some (RWIndexCongruence item a b root) ->
      exists id node, Map.get E (S position, S subposition) index = Some id /\
        Map.get positive_encoding id (rw_provenance_nodes proof) = Some node /\
        rw_evidence_time node = (S position, S subposition).

Definition rw_tracked_rule_nodes_covered {K Sort V H}
      (state : rw_tracked_state K Sort V H) (events : list (rw_run_event K Sort V H)) : Prop :=
    let index := rw_tracked_event_nodes state in
    let proof := rw_tracked_provenance state in
    forall id node rule_index bindings,
      Map.get positive_encoding id (rw_provenance_nodes proof) = Some node ->
      rw_evidence_reason_of node = RWEvidenceRule rule_index bindings ->
      exists position attempt rebuild_events,
        nth_error (rev events) position = Some (RWRunAccepted attempt rebuild_events) /\
        Map.get (pair_encoding nat_encoding nat_encoding) (S position, 0) index = Some id /\
        rw_attempt_rule attempt = rule_index /\ rw_attempt_sub attempt = bindings.



Definition rw_tracked_stamp_fresh {K Sort V H} (stamp : nat * nat)
    (state : rw_tracked_state K Sort V H) : Prop :=
  Map.get (pair_encoding nat_encoding nat_encoding) stamp (rw_tracked_event_nodes state) = None /\
forall id node, Map.get positive_encoding id (rw_provenance_nodes (rw_tracked_provenance
    state)) = Some node ->
    rw_evidence_time_lt (rw_evidence_time node) stamp.

Inductive rw_tracked_rebuild_trace {T} (tick : (nat * nat) -> T -> option (T * rw_index_event))
    (group : nat) : nat -> T -> list rw_index_event -> T -> Prop :=
  | RWTrackedRebuildDone : forall position state,
tick (group, S position) state = None -> rw_tracked_rebuild_trace tick group position
    state nil state
  | RWTrackedRebuildStep : forall position state next final event events,
      tick (group, S position) state = Some (next,event) ->
      rw_tracked_rebuild_trace tick group (S position) next events final ->
      rw_tracked_rebuild_trace tick group position state (event :: events) final.

Definition rw_facts_invalidate {F} (_ : Map.t rw_id F) : Map.t rw_id F := Map.empty.


Definition rw_fact_store_valid {K Sort V C F}
    (admissible : rw_semantics K Sort V C -> Prop) (an : rw_analysis K Sort V C F)
    (g : rw_graph K Sort V) (facts : Map.t rw_id F) : Prop :=
  Map.wf positive_encoding facts /\
  forall id f, Map.get positive_encoding id facts = Some f ->
    rw_fact_valid admissible an g id f.


(** This statement fixes the facts invalidate sound contract. *)
Definition rw_facts_invalidate_sound_contract : Prop :=
  forall K Sort V C F (admissible : rw_semantics K Sort V C -> Prop)
    (an : rw_analysis K Sort V C F) (old new : rw_graph K Sort V) facts,
    rw_fact_store_valid admissible an old facts ->
    rw_fact_store_valid admissible an new (rw_facts_invalidate facts) /\
    forall id, Map.get positive_encoding id (rw_facts_invalidate facts) = None.


Definition rw_fact_store_total {K Sort V C F} (an : rw_analysis K Sort V C F)
    (facts : Map.t rw_id F) (id : rw_id) : F :=
  match Map.get positive_encoding id facts with
  | Some fact => fact
  | None => rw_fact_unknown an
  end.


(** This statement fixes the fact store total valid contract. *)
Definition rw_fact_store_total_valid_contract : Prop := forall K Sort V C F (sig : rw_signature K
    Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (an : rw_analysis K Sort V C F)
    (g : rw_graph K Sort V) facts,
  rw_analysis_laws sig admissible an -> rw_fact_store_valid admissible an g facts ->
  rw_facts_valid admissible an g (rw_fact_store_total an facts).


(** This statement fixes the fact store total after invalidate contract. *)
Definition rw_fact_store_total_after_invalidate_contract : Prop := forall K Sort V C F
    (an : rw_analysis K Sort V C F) facts id,
  rw_fact_store_total an (rw_facts_invalidate facts) id = rw_fact_unknown an.



Record rw_fact_view (K Sort V F : Type) := RWFactView {
  rw_fact_snapshot : rw_snapshot_view K Sort V;
  rw_fact_lookup : rw_id -> F
}.
Arguments RWFactView {K Sort V F}.
Arguments rw_fact_snapshot {K Sort V F}.
Arguments rw_fact_lookup {K Sort V F}.

Definition rw_fact_observe {K Sort V H C F} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (an : rw_analysis K Sort V C F)
    (state : rw_tracked_state K Sort V H) (facts : Map.t rw_id F) : rw_fact_view K Sort V F :=
  RWFactView (rw_index_view EK ES EV (rw_tracked_machine state)) (rw_fact_store_total an facts).

(** This statement fixes the fact observe valid contract. *)
Definition rw_fact_observe_valid_contract : Prop :=
  forall K Sort V H C F (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (sig : rw_signature K Sort V) (admissible : rw_semantics K Sort V C -> Prop)
    (an : rw_analysis K Sort V C F) (state : rw_tracked_state K Sort V H) facts,
    rw_analysis_laws sig admissible an ->
rw_snapshot_agrees (rw_tracked_graph state) (rw_index_view EK ES EV (rw_tracked_machine
    state)) ->
    rw_fact_store_valid admissible an (rw_tracked_graph state) facts ->
    let observed := rw_fact_observe EK ES EV an state facts in
    rw_snapshot_agrees (rw_tracked_graph state) (rw_fact_snapshot observed) /\
    rw_facts_valid admissible an (rw_tracked_graph state) (rw_fact_lookup observed).
```

## Galois.Rewrite.RewriteAuditProofRealizations

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditProofRealizations.v`.

```rocq
(** * RewriteAuditProofRealizations

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexReference RewriteAuditIndexRules
  RewriteAuditProofApply RewriteAuditProofTick RewriteAuditQueueReference.
Import List.ListNotations.

Definition rw_rp_factful_apply_atomic {K Sort V H F} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) rules position
    (input : rw_tracked_state K Sort V H * Map.t rw_id F) attempt :
    option ((rw_tracked_state K Sort V H * Map.t rw_id F) * list rw_index_event) * nat :=
  let '(state, _) := input in
  let '(applied, work) := rw_rp_apply_atomic EK ES EV op sort value hole callbacks
    rules position state attempt in
  (option_map (fun pair => ((fst pair, Map.empty), snd pair)) applied, 128 + work).

(** A successful public factful apply exposes only the newly invalidated map. *)
```

## Galois.Rewrite.RewriteAuditProofFactPublic

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditProofFactPublic.v`.

```rocq
(** * RewriteAuditProofFactPublic

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexPrograms RewriteAuditIndexReference
  RewriteAuditIndexRules RewriteAuditProofFacts RewriteAuditProofRun RewriteAuditProofSemantic
  RewriteAuditProofTick RewriteAuditQueueReference.
Import List.ListNotations.

Fixpoint rw_rp_fact_plain {K Sort V H F} (view : rw_snapshot_view K Sort V)
    (lookup : rw_id -> F) (program : rw_rp_fact_program K Sort V H F) :
    option (rw_attempt K Sort V H) :=
  match program with
  | RPFactReturn offer _ => offer
  | RPFactView _ request next =>
    rw_rp_fact_plain view lookup (next (rw_rp_view_plain_request view request))
  | RPFactLookup _ id next => rw_rp_fact_plain view lookup (next (lookup id))
  end.


Definition rw_rp_fact_strategy_agrees {K Sort V H C F} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (an : rw_analysis K Sort V C F)
    (adapter : rw_rp_fact_strategy_adapter K Sort V H F)
    (strategy : rw_fact_view K Sort V F -> option (rw_attempt K Sort V H)) : Prop :=
  forall (state : rw_tracked_state K Sort V H) facts,
    let view := rw_fact_observe EK ES EV an state facts in
    rw_rp_fact_plain (rw_fact_snapshot view) (rw_fact_lookup view)
      (rw_rp_fact_strategy_program adapter) = strategy view.

(** Fact-run source realization includes the unknown fallback and exact invalidation boundary. *)

(** This statement fixes the rp fact run valid statement contract. *)
Definition rw_rp_fact_run_valid_statement : Prop :=
  forall K Sort V H C F (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) rules (an : rw_analysis K Sort V C F)
    (admissible : rw_semantics K Sort V C -> Prop) adapter fuel state facts,
  rw_fact_store_valid admissible an (rw_tracked_graph state) facts ->
  let '((output, retained), _) := rw_rp_fact_run_atomic EK ES EV op sort value hole callbacks
    rules (rw_fact_unknown an) adapter fuel (state, facts) in
  rw_fact_store_valid admissible an (rw_tracked_graph (rw_tracked_final output)) retained.

(** Fact-query programs preserve the same callback count, including stopping and rejected calls. *)

(** This statement fixes the rp fact callback bound statement contract. *)
Definition rw_rp_fact_callback_bound_statement : Prop :=
  forall K Sort V H F (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) rules (unknown : F) adapter fuel input,
  let '((output, _), _) := rw_rp_fact_run_atomic EK ES EV op sort value hole callbacks
    rules unknown adapter fuel input in
  (N.of_nat (length (rw_tracked_events output)) +
    match rw_tracked_stop output with RWStopped => 1%N | RWFuelExhausted => 0%N end <= fuel)%N.
```

## Galois.Rewrite.RewriteAuditIndexDimensions

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditIndexDimensions.v`.

```rocq
(** * RewriteAuditIndexDimensions

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexReference RewriteAuditQueueReference.
Import List.ListNotations.

Fixpoint rw_whole_term_dimension {K Sort V} (term : rw_term K Sort V) : nat :=
  match term with
  | RWVar _ _ => 1
  | RWApp _ _ children =>
    S ((fix visit (terms : list (rw_term K Sort V)) : nat :=
      match terms with
      | nil => 1
      | t :: rest => S (rw_whole_term_dimension t + visit rest)
      end) children)
  end.


Fixpoint rw_whole_pattern_dimension {K Sort V H} (pattern : rw_pattern K Sort V H) : nat :=
  match pattern with
  | RWHole _ _ => 1
  | RWPVar _ _ => 1
  | RWPApp _ _ children =>
    S ((fix visit (patterns : list (rw_pattern K Sort V H)) : nat :=
      match patterns with
      | nil => 1
      | p :: rest => S (rw_whole_pattern_dimension p + visit rest)
      end) children)
  end.


Definition rw_whole_ids_dimension (ids : list positive) : nat :=
  fold_right (fun id total => S (Pos.size_nat id + total)) 1 ids.


Definition rw_whole_map_dimension {K V} (key_dimension : K -> nat)
    (value_dimension : V -> nat) (table : Map.t K V) : nat :=
  S (audit_trie_nodes table + fold_right (fun entry total =>
    S (key_dimension (fst entry) + value_dimension (snd entry) + total)) 1 (Map.elements table)).


Definition rw_whole_set_dimension (set : FinSet.t rw_id) : nat :=
  rw_whole_map_dimension Pos.size_nat (fun _ => 1) set.


Definition rw_whole_node_dimension {K Sort V} (node : rw_node K Sort V) : nat :=
  match node with
  | RWNVar _ _ => 1
  | RWNApp _ _ children => S (rw_whole_ids_dimension children)
  end.


Definition rw_whole_graph_dimension {K Sort V} (graph : rw_graph K Sort V) : nat :=
  S (rw_whole_ids_dimension (rw_roots graph) + rw_whole_ids_dimension (rw_nodes_in graph) +
    rw_whole_map_dimension Pos.size_nat Pos.size_nat (rw_class_roots graph) +
    rw_whole_map_dimension Pos.size_nat (fun _ => 1) (rw_sorts graph) +
    rw_whole_map_dimension Pos.size_nat
      (fun entry => Pos.size_nat (fst entry) + rw_whole_node_dimension (snd entry))
      (rw_nodes graph)).


Definition rw_whole_forest_dimension (forest : UnionFind.t rw_id) : nat :=
  S (UnionFind.max_rank forest +
    rw_whole_map_dimension Pos.size_nat Pos.size_nat (UnionFind.parents forest) +
    rw_whole_map_dimension Pos.size_nat (fun rank => S rank) (UnionFind.ranks forest)).


Definition rw_whole_index_dimension {K Sort V} (state : rw_index_state K Sort V) : nat :=
  S (rw_whole_graph_dimension (rw_index_base state) +
    rw_whole_forest_dimension (rw_index_forest state) +
    rw_whole_map_dimension Pos.size_nat rw_whole_set_dimension (rw_index_parent_buckets state) +
    rw_whole_map_dimension rw_whole_node_dimension rw_whole_set_dimension
      (rw_index_signatures state) +
    rw_whole_map_dimension Pos.size_nat rw_whole_node_dimension (rw_index_node_keys state) +
    rw_whole_ids_dimension (rw_index_dirty_order state) +
    rw_whole_set_dimension (rw_index_dirty_set state) +
    fold_right (fun pair total => S (Pos.size_nat (fst pair) + Pos.size_nat (snd pair) + total))
      1 (rw_pending_sequence (rw_index_pending state)) +
    rw_whole_map_dimension
      (fun pair => Pos.size_nat (fst pair) + Pos.size_nat (snd pair)) (fun _ => 1)
      (rw_pending_members (rw_index_pending state)) +
    rw_whole_map_dimension (fun _ => 1) rw_whole_set_dimension (rw_index_operators state) +
    rw_whole_map_dimension (fun _ => 1) rw_whole_set_dimension (rw_index_variables state) +
    Pos.size_nat (rw_index_fresh state)).


Definition rw_whole_bindings_dimension {K Sort V H}
    (bindings : Map.t H (rw_term K Sort V)) : nat :=
  rw_whole_map_dimension (fun _ => 1) rw_whole_term_dimension bindings.


Definition rw_whole_attempt_dimension {K Sort V H} (attempt : rw_attempt K Sort V H) : nat :=
  S (rw_attempt_rule attempt + Pos.size_nat (rw_attempt_root attempt) +
    rw_whole_bindings_dimension (rw_attempt_sub attempt)).


Definition rw_whole_rules_dimension {K Sort V H} (rules : list (rw_rule K Sort V H)) : nat :=
  fold_right (fun rule total => S (length (rw_holes rule) +
    rw_whole_pattern_dimension (rw_lhs rule) + rw_whole_pattern_dimension (rw_rhs rule) + total))
    1 rules.
```

## Galois.Rewrite.RewriteAuditProofDimensions

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditProofDimensions.v`.

```rocq
(** * RewriteAuditProofDimensions

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexDimensions RewriteAuditProofCarrier.
Import List.ListNotations.

Definition rw_whole_reason_dimension {K Sort V H} (reason : rw_evidence_reason K Sort V H) :
    nat :=
  match reason with
  | RWEvidenceRefl => 1
  | RWEvidenceRule index bindings => S (index + rw_whole_bindings_dimension bindings)
  | RWEvidenceSym child => S (Pos.size_nat child)
  | RWEvidenceTrans first second => S (Pos.size_nat first + Pos.size_nat second)
  | RWEvidenceCongruence children => S (rw_whole_ids_dimension children)
  end.


Definition rw_whole_provenance_dimension {K Sort V H} (proof : rw_provenance K Sort V H) :
    nat :=
  S (rw_whole_ids_dimension (rw_provenance_ids proof) +
    rw_whole_map_dimension Pos.size_nat (fun node =>
      rw_whole_term_dimension (rw_evidence_left node) +
      rw_whole_term_dimension (rw_evidence_right node) +
      rw_whole_reason_dimension (rw_evidence_reason_of node) +
      fst (rw_evidence_time node) + snd (rw_evidence_time node)) (rw_provenance_nodes proof)).
```

## Galois.Rewrite.RewriteAuditIndexDimensions2

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditIndexDimensions2.v`.

```rocq
(** * RewriteAuditIndexDimensions2

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexDimensions RewriteAuditSharedReference.
Import List.ListNotations.

Definition rw_whole_shared_node_dimension {K Sort V} (node : rw_shared_node K Sort V) : nat :=
  match node with
  | RWSharedVar _ _ _ _ _ => 1
  | RWSharedApp _ _ _ _ _ children => S (rw_whole_ids_dimension children)
  end.
```

## Galois.Rewrite.RewriteAuditProofDimensions2

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditProofDimensions2.v`.

```rocq
(** * RewriteAuditProofDimensions2

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexDimensions RewriteAuditIndexDimensions2
  RewriteAuditProofDimensions RewriteAuditProofTick RewriteAuditSharedReference.
Import List.ListNotations.

Definition rw_whole_witness_dimension {K Sort V} (store : rw_class_witness_store K Sort V) :
    nat :=
  let nodes := rw_class_witness_nodes store in
  S (rw_whole_map_dimension Pos.size_nat rw_whole_shared_node_dimension nodes +
    rw_whole_map_dimension Pos.size_nat Pos.size_nat (rw_class_witness_roots store) +
    fold_right (fun entry total =>
      match rw_shared_unfold (RwSharedTree K Sort V (fst entry) nodes) with
      | None => S total
      | Some term => S (rw_whole_term_dimension term + total)
      end) 1 (Map.elements nodes)).


Definition rw_whole_tracked_dimension {K Sort V H} (state : rw_tracked_state K Sort V H) :
    nat :=
  S (rw_whole_index_dimension (rw_tracked_machine state) +
    rw_whole_provenance_dimension (rw_tracked_provenance state) +
    rw_whole_witness_dimension (rw_tracked_witnesses state) +
    rw_whole_map_dimension (fun stamp => S (fst stamp + snd stamp)) Pos.size_nat
      (rw_tracked_event_nodes state)).
```

## Galois.Rewrite.RewriteAuditIndexDimensions3

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditIndexDimensions3.v`.

```rocq
(** * RewriteAuditIndexDimensions3

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexDimensions RewriteAuditIndexReference.
Import List.ListNotations.

Definition rw_whole_event_attempt_dimension {K Sort V H}
    (events : list (rw_run_event K Sort V H)) : nat :=
  fold_right (fun event largest => Nat.max largest
    (match event with
    | RWRunRejected attempt => rw_whole_attempt_dimension attempt
    | RWRunAccepted attempt _ => rw_whole_attempt_dimension attempt
    end)) 1 events.
```

## Galois.Rewrite.RewriteAuditProofDimensions3

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditProofDimensions3.v`.

```rocq
(** * RewriteAuditProofDimensions3

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexDimensions RewriteAuditIndexDimensions3
  RewriteAuditProofDimensions2 RewriteAuditProofRun.
Import List.ListNotations.

Definition rw_rp_whole_operand_dimension {K Sort V H} (rules : list (rw_rule K Sort V H))
    (seed : rw_term K Sort V) (output : rw_tracked_output K Sort V H) : nat :=
  S (rw_whole_term_dimension seed + rw_whole_rules_dimension rules +
    rw_whole_tracked_dimension (rw_tracked_final output) +
    rw_whole_event_attempt_dimension (rw_tracked_events output)).
```

## Galois.Rewrite.RewriteAuditIndexDimensions4

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditIndexDimensions4.v`.

```rocq
(** * RewriteAuditIndexDimensions4

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
Import List.ListNotations.

Definition rw_whole_source_ceiling (fuel : N) (dimension code_width body_control : nat) : N :=
  (4294967296 * (1 + fuel) * (1 + N.of_nat body_control) *
    N.pow (N.of_nat (S (dimension + code_width)))
      (128 + 16 * N.pow (N.of_nat dimension) 4))%N.
```

## Galois.Rewrite.RewriteAuditIndexExternal

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditIndexExternal.v`.

```rocq
(** * RewriteAuditIndexExternal

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexDimensions RewriteAuditIndexPrograms
  RewriteAuditIndexReference RewriteAuditIndexRules RewriteAuditQueueReference.
Import List.ListNotations.

Definition rw_whole_encoder_fits {A} (adapter : rw_queue_encoder_adapter A)
    (width body : nat) (input : A) : Prop :=
  let '(code, work) := rw_queue_encoder_run adapter input in
  Pos.size_nat code <= width /\ work <= body.


Fixpoint rw_whole_term_atoms {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (width body : nat) (term : rw_term K Sort V) : Prop :=
  match term with
  | RWVar ty v => rw_whole_encoder_fits sort width body ty /\
      rw_whole_encoder_fits value width body v
  | RWApp ty k children =>
    rw_whole_encoder_fits sort width body ty /\ rw_whole_encoder_fits op width body k /\
    (fix visit (terms : list (rw_term K Sort V)) : Prop :=
      match terms with
      | nil => True
      | t :: rest => rw_whole_term_atoms op sort value width body t /\ visit rest
      end) children
  end.


Fixpoint rw_whole_pattern_atoms {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (hole : rw_queue_encoder_adapter H) (width body : nat)
    (pattern : rw_pattern K Sort V H) : Prop :=
  match pattern with
  | RWHole ty h => rw_whole_encoder_fits sort width body ty /\
      rw_whole_encoder_fits hole width body h
  | RWPVar ty v => rw_whole_encoder_fits sort width body ty /\
      rw_whole_encoder_fits value width body v
  | RWPApp ty k children =>
    rw_whole_encoder_fits sort width body ty /\ rw_whole_encoder_fits op width body k /\
    (fix visit (patterns : list (rw_pattern K Sort V H)) : Prop :=
      match patterns with
      | nil => True
      | p :: rest => rw_whole_pattern_atoms op sort value hole width body p /\ visit rest
      end) children
  end.


Definition rw_whole_node_atoms {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (width body : nat) (node : rw_node K Sort V) : Prop :=
  match node with
  | RWNVar ty v => rw_whole_encoder_fits sort width body ty /\
      rw_whole_encoder_fits value width body v
  | RWNApp ty k _ => rw_whole_encoder_fits sort width body ty /\
      rw_whole_encoder_fits op width body k
  end.


Definition rw_whole_graph_atoms {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (width body : nat) (graph : rw_graph K Sort V) : Prop :=
  Forall (fun entry => rw_whole_encoder_fits sort width body (snd entry))
    (Map.elements (rw_sorts graph)) /\
  Forall (fun entry => rw_whole_node_atoms op sort value width body (snd (snd entry)))
    (Map.elements (rw_nodes graph)).


Definition rw_whole_index_atoms {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (width body : nat) (state : rw_index_state K Sort V) : Prop :=
  rw_whole_graph_atoms op sort value width body (rw_index_base state) /\
  Forall (fun entry => rw_whole_encoder_fits op width body (fst entry))
    (Map.elements (rw_index_operators state)) /\
  Forall (fun entry => rw_whole_encoder_fits value width body (fst entry))
    (Map.elements (rw_index_variables state)) /\
  Forall (fun entry => rw_whole_node_atoms op sort value width body (fst entry))
    (Map.elements (rw_index_signatures state)) /\
  Forall (fun entry => rw_whole_node_atoms op sort value width body (snd entry))
    (Map.elements (rw_index_node_keys state)).


Fixpoint rw_whole_term_callbacks {K Sort V H} (sort : rw_queue_encoder_adapter Sort)
    (callbacks : rw_rp_rule_callbacks K Sort V H) (width body : nat)
    (term : rw_term K Sort V) : Prop :=
  match term with
  | RWVar _ v =>
    let '(declared, work) := rw_rp_var_sort callbacks v in
    work <= body /\
    match declared with None => True | Some ty => rw_whole_encoder_fits sort width body ty end
  | RWApp ty k children =>
    snd (rw_rp_operator_shape callbacks k (map rw_sort children) ty) <= body /\
    (fix visit (terms : list (rw_term K Sort V)) : Prop :=
      match terms with
      | nil => True
      | t :: rest => rw_whole_term_callbacks sort callbacks width body t /\ visit rest
      end) children
  end.


Fixpoint rw_whole_guard_control {K Sort V H} (sub : rw_substitution K Sort V H)
    (program : rw_rp_guard_program K Sort V H) : nat :=
  match program with
  | RPGuardReturn _ body => 64 + body
  | RPGuardLookup body h next => 64 + body + rw_whole_guard_control sub (next (sub h))
  end.


Fixpoint rw_whole_guard_queries {K Sort V H} (hole : rw_queue_encoder_adapter H)
    (width body : nat) (sub : rw_substitution K Sort V H)
    (program : rw_rp_guard_program K Sort V H) : Prop :=
  match program with
  | RPGuardReturn _ _ => True
  | RPGuardLookup _ h next => rw_whole_encoder_fits hole width body h /\
      rw_whole_guard_queries hole width body sub (next (sub h))
  end.


Definition rw_whole_rules_external {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (hole : rw_queue_encoder_adapter H) (callbacks : rw_rp_rule_callbacks K Sort V H)
    (width body : nat) (rules : list (rw_rule K Sort V H)) : Prop :=
  Forall (fun rule =>
    rw_whole_pattern_atoms op sort value hole width body (rw_lhs rule) /\
    rw_whole_pattern_atoms op sort value hole width body (rw_rhs rule) /\
    Forall (fun h => rw_whole_encoder_fits hole width body h /\
      let '(declared, work) := rw_rp_hole_sort callbacks rule h in
      work <= body /\
      match declared with None => True | Some ty => rw_whole_encoder_fits sort width body ty end)
      (rw_holes rule)) rules.


Definition rw_whole_attempt_external {K Sort V H} (EH : encoding H)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) (width body : nat)
    (rules : list (rw_rule K Sort V H)) (attempt : rw_attempt K Sort V H) : Prop :=
  Forall (fun entry => rw_whole_encoder_fits hole width body (fst entry) /\
    rw_whole_term_atoms op sort value width body (snd entry) /\
    rw_whole_term_callbacks sort callbacks width body (snd entry))
    (Map.elements (rw_attempt_sub attempt)) /\
  match nth_error rules (rw_attempt_rule attempt) with
  | None => True
  | Some rule =>
    let sub := fun h => Map.get EH h (rw_attempt_sub attempt) in
    rw_whole_guard_control sub (rw_rp_guard callbacks rule) <= body /\
    rw_whole_guard_queries hole width body sub (rw_rp_guard callbacks rule)
  end.


Definition rw_whole_request_external {K Sort V R} (op : rw_queue_encoder_adapter K)
    (value : rw_queue_encoder_adapter V) (width body : nat)
    (request : rw_rp_view_request K Sort V R) : Prop :=
  match request with
  | RPRequestFind id => Pos.size_nat id <= width
  | RPRequestSort id => Pos.size_nat id <= width
  | RPRequestNode id => Pos.size_nat id <= width
  | RPRequestOperator key => rw_whole_encoder_fits op width body key
  | RPRequestVariable key => rw_whole_encoder_fits value width body key
  | RPRequestParents id => Pos.size_nat id <= width
  | RPRequestRoots => True
  | RPRequestNodes => True
  | RPRequestGraph => True
  end.


Fixpoint rw_whole_view_control {K Sort V A} (view : rw_snapshot_view K Sort V)
    (program : rw_rp_view_program K Sort V A) : nat :=
  match program with
  | RPViewReturn _ body => 64 + body
  | RPViewAsk body request next =>
    64 + body + rw_whole_view_control view (next (rw_rp_view_plain_request view request))
  end.


Fixpoint rw_whole_view_queries {K Sort V A} (op : rw_queue_encoder_adapter K)
    (value : rw_queue_encoder_adapter V) (width body : nat) (view : rw_snapshot_view K Sort V)
    (program : rw_rp_view_program K Sort V A) : Prop :=
  match program with
  | RPViewReturn _ _ => True
  | RPViewAsk _ request next => rw_whole_request_external op value width body request /\
      rw_whole_view_queries op value width body view
        (next (rw_rp_view_plain_request view request))
  end.


Definition rw_whole_strategy_external {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (dimension width body : nat)
    (adapter : rw_rp_strategy_adapter K Sort V H) : Prop :=
  forall state,
    rw_whole_index_dimension state <= Nat.pow (S (dimension + width)) 8 ->
    rw_whole_index_atoms op sort value width body state ->
    let view := rw_index_view EK ES EV state in
    rw_whole_view_control view (rw_rp_strategy_program adapter) <= body /\
    rw_whole_view_queries op value width body view (rw_rp_strategy_program adapter).
```

## Galois.Rewrite.RewriteAuditIndexEventEnvelope

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditIndexEventEnvelope.v`.

```rocq
(** * RewriteAuditIndexEventEnvelope

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexExternal RewriteAuditIndexReference
  RewriteAuditIndexRules RewriteAuditQueueReference.
Import List.ListNotations.

Definition rw_whole_event_external {K Sort V H} (EH : encoding H)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) (width body : nat)
    (rules : list (rw_rule K Sort V H)) (event : rw_run_event K Sort V H) : Prop :=
  match event with
  | RWRunRejected attempt =>
    rw_whole_attempt_external EH op sort value hole callbacks width body rules attempt
  | RWRunAccepted attempt _ =>
    rw_whole_attempt_external EH op sort value hole callbacks width body rules attempt
  end.
```

## Galois.Rewrite.RewriteAuditProofWholeContracts

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditProofWholeContracts.v`.

```rocq
(** * RewriteAuditProofWholeContracts

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexDimensions4 RewriteAuditIndexEventEnvelope
  RewriteAuditIndexExternal RewriteAuditIndexProgramLaws RewriteAuditIndexPrograms
  RewriteAuditIndexRules RewriteAuditProofCarrier RewriteAuditProofDimensions3
  RewriteAuditProofRun RewriteAuditProofTick RewriteAuditQueueReference RewriteAuditSharedReference.
Import List.ListNotations.

Definition rw_whole_provenance_atoms {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (width body : nat) (proof : rw_provenance K Sort V H) : Prop :=
  Forall (fun entry => rw_whole_term_atoms op sort value width body
      (rw_evidence_left (snd entry)) /\
    rw_whole_term_atoms op sort value width body (rw_evidence_right (snd entry)))
    (Map.elements (rw_provenance_nodes proof)).


Definition rw_whole_witness_atoms {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (width body : nat) (store : rw_class_witness_store K Sort V) : Prop :=
  Forall (fun entry =>
    match snd entry with
    | RWSharedVar _ _ _ ty v => rw_whole_encoder_fits sort width body ty /\
        rw_whole_encoder_fits value width body v
    | RWSharedApp _ _ _ ty k _ => rw_whole_encoder_fits sort width body ty /\
        rw_whole_encoder_fits op width body k
    end) (Map.elements (rw_class_witness_nodes store)).


Record rw_rp_whole_invocation {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (hole : rw_queue_encoder_adapter H) (callbacks : rw_rp_rule_callbacks K Sort V H)
    (rules : list (rw_rule K Sort V H)) (adapter : rw_rp_strategy_adapter K Sort V H)
    (seed : rw_term K Sort V) (output : rw_tracked_output K Sort V H)
    (width body : nat) : Prop := RwRpWholeInvocation {
  rw_rp_whole_seed_atoms : rw_whole_term_atoms op sort value width body seed;
  rw_rp_whole_rules_external : rw_whole_rules_external op sort value hole callbacks
    width body rules;
  rw_rp_whole_event_external : Forall
    (rw_whole_event_external EH op sort value hole callbacks width body rules)
    (rw_tracked_events output);
  rw_rp_whole_index_atoms : rw_whole_index_atoms op sort value width body
    (rw_tracked_machine (rw_tracked_final output));
  rw_rp_whole_proof_atoms : rw_whole_provenance_atoms op sort value width body
    (rw_tracked_provenance (rw_tracked_final output));
  rw_rp_whole_witness_atoms : rw_whole_witness_atoms op sort value width body
    (rw_tracked_witnesses (rw_tracked_final output));
  rw_rp_whole_strategy_external : rw_whole_strategy_external EK ES EV op sort value
    (rw_rp_whole_operand_dimension rules seed output) width body adapter
}.

(** Whole tracked source work has a closed fuel/operand/body ceiling independent of audit logs. *)

(** This statement fixes the rp whole bound statement contract. *)
Definition rw_rp_whole_bound_statement : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) (sig : rw_signature K Sort V)
    rules adapter fuel seed width body,
  (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
  (forall s, fst (rw_queue_encoder_run sort s) = encode ES s) ->
  (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
  (forall h, fst (rw_queue_encoder_run hole h) = encode EH h) ->
  rw_rp_callbacks_agree EH sig callbacks rules -> Forall (rw_rule_wf sig) rules ->
  rw_typed sig seed ->
  let '((_, output), work) :=
    rw_rp_run_atomic EK ES EV op sort value hole callbacks rules adapter fuel seed in
  rw_rp_whole_invocation EK ES EV EH op sort value hole callbacks rules adapter seed output
    width body ->
  (N.of_nat work <= rw_whole_source_ceiling fuel
    (rw_rp_whole_operand_dimension rules seed output) width body)%N.
```

## Galois.Rewrite.RewriteAuditIndexWholeContracts

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditIndexWholeContracts.v`.

```rocq
(** * RewriteAuditIndexWholeContracts

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexDimensions RewriteAuditIndexDimensions3
  RewriteAuditIndexDimensions4 RewriteAuditIndexEventEnvelope RewriteAuditIndexExternal
  RewriteAuditIndexMatch RewriteAuditIndexProgramLaws RewriteAuditIndexPrograms
  RewriteAuditIndexReference RewriteAuditIndexRules RewriteAuditIndexRun RewriteAuditQueueReference.
Import List.ListNotations.

Definition rw_ri_whole_operand_dimension {K Sort V H} (rules : list (rw_rule K Sort V H))
    (input : rw_graph K Sort V) (result : rw_run_result K Sort V)
    (events : list (rw_run_event K Sort V H)) : nat :=
  S (rw_whole_graph_dimension input + rw_whole_graph_dimension (rw_run_graph result) +
    rw_whole_rules_dimension rules + rw_whole_event_attempt_dimension events).


Record rw_ri_whole_invocation {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (hole : rw_queue_encoder_adapter H) (callbacks : rw_rp_rule_callbacks K Sort V H)
    (rules : list (rw_rule K Sort V H)) (adapter : rw_rp_strategy_adapter K Sort V H)
    (input : rw_graph K Sort V) (result : rw_run_result K Sort V)
    (events : list (rw_run_event K Sort V H)) (width body : nat) : Prop := RwRiWholeInvocation {
  rw_ri_whole_input_atoms : rw_whole_graph_atoms op sort value width body input;
  rw_ri_whole_output_atoms : rw_whole_graph_atoms op sort value width body (rw_run_graph result);
  rw_ri_whole_rules_external : rw_whole_rules_external op sort value hole callbacks
    width body rules;
  rw_ri_whole_event_external : Forall
    (rw_whole_event_external EH op sort value hole callbacks width body rules) events;
  rw_ri_whole_strategy_external : rw_whole_strategy_external EK ES EV op sort value
    (rw_ri_whole_operand_dimension rules input result events) width body adapter
}.

(** Graph-only source work includes all accepted/rejected attempts, rebuilds and final output. *)

(** This statement fixes the ri whole bound statement contract. *)
Definition rw_ri_whole_bound_statement : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) (sig : rw_signature K Sort V)
    rules adapter fuel graph width body,
  (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
  (forall s, fst (rw_queue_encoder_run sort s) = encode ES s) ->
  (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
  (forall h, fst (rw_queue_encoder_run hole h) = encode EH h) ->
  rw_rp_callbacks_agree EH sig callbacks rules -> Forall (rw_rule_wf sig) rules ->
  rw_graph_wf sig graph ->
  let '((result, _, events), work) :=
    rw_ri_run_atomic op sort value hole callbacks rules adapter fuel graph in
  rw_ri_whole_invocation EK ES EV EH op sort value hole callbacks rules adapter graph result events
    width body ->
  (N.of_nat work <= rw_whole_source_ceiling fuel
    (rw_ri_whole_operand_dimension rules graph result events) width body)%N.

(** The matcher has an input-only finite-pattern bound, including canonical assignment storage. *)

(** This statement fixes the ri match bound statement contract. *)
Definition rw_ri_match_bound_statement : Prop :=
  forall K Sort V H (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    state root (pattern : rw_pattern K Sort V H) width body,
  rw_whole_index_atoms op sort value width body state ->
  rw_whole_pattern_atoms op sort value hole width body pattern ->
  let dimension := S (rw_whole_index_dimension state + Pos.size_nat root +
    rw_whole_pattern_dimension pattern + width) in
  (N.of_nat (snd (rw_ri_match_atomic op sort value hole state root pattern)) <=
    4294967296 * (1 + N.of_nat body) *
      N.pow (N.of_nat dimension) (32 + 16 * N.of_nat (rw_whole_pattern_dimension pattern)))%N.

(** Selected output charges both finite-term membership traversals and the actual closure kernel. *)
```

## Galois.Rewrite.RewriteAuditProofSelectedContracts

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditProofSelectedContracts.v`.

```rocq
(** * RewriteAuditProofSelectedContracts

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexDimensions RewriteAuditIndexExternal
  RewriteAuditIndexReference RewriteAuditProofDimensions2 RewriteAuditProofRepresentation
  RewriteAuditProofSelected RewriteAuditProofTick RewriteAuditProofWholeContracts
  RewriteAuditQueueReference.
Import List.ListNotations.

(** This statement fixes the rp selected bound statement contract. *)
Definition rw_rp_selected_bound_statement : Prop :=
  forall K Sort V H (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (state : rw_tracked_state K Sort V H)
    root seed tree width body,
  rw_whole_index_atoms op sort value width body (rw_tracked_machine state) ->
  rw_whole_provenance_atoms op sort value width body (rw_tracked_provenance state) ->
  rw_whole_term_atoms op sort value width body seed ->
  rw_whole_term_atoms op sort value width body tree ->
  let dimension := S (rw_whole_tracked_dimension state + Pos.size_nat root +
    rw_whole_term_dimension seed + rw_whole_term_dimension tree + width) in
  (N.of_nat (snd (rw_rp_selected_atomic op sort value state root seed tree)) <=
    4294967296 * (1 + N.of_nat body) * N.pow (N.of_nat dimension)
      (128 + 16 * N.of_nat (rw_whole_term_dimension seed + rw_whole_term_dimension tree)))%N.

(** Representation search pays for failed candidates and construction of the actual witness. *)

(** This statement fixes the rp repr find bound statement contract. *)
Definition rw_rp_repr_find_bound_statement : Prop :=
  forall K Sort V (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (state : rw_index_state K Sort V)
    root term width body,
  rw_whole_index_atoms op sort value width body state ->
  rw_whole_term_atoms op sort value width body term ->
  let dimension := S (rw_whole_index_dimension state + Pos.size_nat root +
    rw_whole_term_dimension term + width) in
  (N.of_nat (snd (rw_rp_repr_find_atomic op sort value state root term)) <=
    4294967296 * (1 + N.of_nat body) * N.pow (N.of_nat dimension)
      (64 + 16 * N.of_nat (rw_whole_term_dimension term)))%N.

(** Initial graph preparation has a stored-input bound with actual component encoder bodies. *)
```

## Galois.Rewrite.RewriteAuditIndexPreparationContracts

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditIndexPreparationContracts.v`.

```rocq
(** * RewriteAuditIndexPreparationContracts

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexDimensions RewriteAuditIndexExternal
  RewriteAuditIndexPrepare RewriteAuditQueueReference.
Import List.ListNotations.

(** This statement fixes the ri prepare once bound statement contract. *)
Definition rw_ri_prepare_once_bound_statement : Prop :=
  forall K Sort V (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (graph : rw_graph K Sort V) width body,
  rw_whole_graph_atoms op sort value width body graph ->
  (N.of_nat (rw_ri_prepare_once_work (snd (rw_ri_prepare_once op value graph))) <=
    65536 * (1 + N.of_nat body) *
      N.pow (N.of_nat (S (rw_whole_graph_dimension graph + width))) 16)%N.

(** Once-built rule tables include the fixed unary-natural encoder on every actual numeric index. *)
```

## Galois.Rewrite.RewriteAuditIndexRuleTableContracts

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditIndexRuleTableContracts.v`.

```rocq
(** * RewriteAuditIndexRuleTableContracts

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexRules.
Import List.ListNotations.

(** This statement fixes the rp rule table bound statement contract. *)
Definition rw_rp_rule_table_bound_statement : Prop :=
  forall K Sort V H (rules : list (rw_rule K Sort V H)) start,
  (N.of_nat (snd (rw_rp_rule_table_atomic rules start)) <=
    65536 * N.pow (N.of_nat (S (start + length rules))) 16)%N.
```

## Galois.Rewrite.RewriteAuditProofFactWholeContracts

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditProofFactWholeContracts.v`.

```rocq
(** * RewriteAuditProofFactWholeContracts

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexDimensions RewriteAuditIndexDimensions3
  RewriteAuditIndexDimensions4 RewriteAuditIndexEventEnvelope RewriteAuditIndexExternal
  RewriteAuditIndexProgramLaws RewriteAuditIndexPrograms RewriteAuditIndexReference
  RewriteAuditIndexRules RewriteAuditProofDimensions2 RewriteAuditProofFacts
  RewriteAuditProofRun RewriteAuditProofTick RewriteAuditProofWholeContracts
  RewriteAuditQueueReference.
Import List.ListNotations.

Fixpoint rw_whole_fact_control {K Sort V H F} (view : rw_snapshot_view K Sort V)
    (unknown : F) (program : rw_rp_fact_program K Sort V H F) : nat :=
  match program with
  | RPFactReturn _ body => 64 + body
  | RPFactView body request next =>
    64 + body + rw_whole_fact_control view unknown
      (next (rw_rp_view_plain_request view request))
  | RPFactLookup body _ next => 64 + body + rw_whole_fact_control view unknown (next unknown)
  end.


Fixpoint rw_whole_fact_queries {K Sort V H F} (op : rw_queue_encoder_adapter K)
    (value : rw_queue_encoder_adapter V) (width body : nat) (view : rw_snapshot_view K Sort V)
    (unknown : F) (program : rw_rp_fact_program K Sort V H F) : Prop :=
  match program with
  | RPFactReturn _ _ => True
  | RPFactView _ request next => rw_whole_request_external op value width body request /\
      rw_whole_fact_queries op value width body view unknown
        (next (rw_rp_view_plain_request view request))
  | RPFactLookup _ id next => Pos.size_nat id <= width /\
      rw_whole_fact_queries op value width body view unknown (next unknown)
  end.


Definition rw_fact_whole_operand_dimension {K Sort V H F}
    (rules : list (rw_rule K Sort V H)) (initial : rw_tracked_state K Sort V H)
    (input_facts : Map.t rw_id F) (output : rw_tracked_output K Sort V H)
    (retained : Map.t rw_id F) : nat :=
  S (rw_whole_tracked_dimension initial + rw_whole_tracked_dimension (rw_tracked_final output) +
    rw_whole_rules_dimension rules + rw_whole_event_attempt_dimension (rw_tracked_events output) +
    audit_trie_nodes input_facts + audit_trie_nodes retained).


Definition rw_whole_fact_strategy_external {K Sort V H F} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (dimension width body : nat) (unknown : F)
    (adapter : rw_rp_fact_strategy_adapter K Sort V H F) : Prop :=
  forall state,
    rw_whole_index_dimension state <= Nat.pow (S (dimension + width)) 8 ->
    rw_whole_index_atoms op sort value width body state ->
    let view := rw_index_view EK ES EV state in
    rw_whole_fact_control view unknown (rw_rp_fact_strategy_program adapter) <= body /\
    rw_whole_fact_queries op value width body view unknown (rw_rp_fact_strategy_program adapter).


Definition rw_whole_tracked_atoms {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (width body : nat) (state : rw_tracked_state K Sort V H) : Prop :=
  rw_whole_index_atoms op sort value width body (rw_tracked_machine state) /\
  rw_whole_provenance_atoms op sort value width body (rw_tracked_provenance state) /\
  rw_whole_witness_atoms op sort value width body (rw_tracked_witnesses state).


Record rw_fact_whole_invocation {K Sort V H F} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (hole : rw_queue_encoder_adapter H) (callbacks : rw_rp_rule_callbacks K Sort V H)
    (rules : list (rw_rule K Sort V H)) (unknown : F)
    (adapter : rw_rp_fact_strategy_adapter K Sort V H F) (initial : rw_tracked_state K Sort V H)
    (input_facts : Map.t rw_id F) (output : rw_tracked_output K Sort V H)
    (retained : Map.t rw_id F) (width body : nat) : Prop := RwFactWholeInvocation {
  rw_fact_whole_initial_atoms : rw_whole_tracked_atoms op sort value width body initial;
  rw_fact_whole_final_atoms : rw_whole_tracked_atoms op sort value width body
    (rw_tracked_final output);
  rw_fact_whole_rules_external : rw_whole_rules_external op sort value hole callbacks
    width body rules;
  rw_fact_whole_events_external : Forall
    (rw_whole_event_external EH op sort value hole callbacks width body rules)
    (rw_tracked_events output);
  rw_fact_whole_strategy_external : rw_whole_fact_strategy_external EK ES EV op sort value
    (rw_fact_whole_operand_dimension rules initial input_facts output retained) width body
    unknown adapter
}.

(** The fact-safe source ceiling includes initial rebuild, all queries, invalidations and output. *)

(** This statement fixes the rp fact whole bound statement contract. *)
Definition rw_rp_fact_whole_bound_statement : Prop :=
  forall K Sort V H F (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) (sig : rw_signature K Sort V)
    rules (unknown : F) adapter fuel initial facts width body,
  (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
  (forall s, fst (rw_queue_encoder_run sort s) = encode ES s) ->
  (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
  (forall h, fst (rw_queue_encoder_run hole h) = encode EH h) ->
  rw_rp_callbacks_agree EH sig callbacks rules -> Forall (rw_rule_wf sig) rules ->
  let '((output, retained), work) := rw_rp_fact_run_atomic EK ES EV op sort value hole callbacks
    rules unknown adapter fuel (initial, facts) in
  rw_fact_whole_invocation EK ES EV EH op sort value hole callbacks rules unknown adapter
    initial facts output retained width body ->
  (N.of_nat work <= rw_whole_source_ceiling fuel
    (rw_fact_whole_operand_dimension rules initial facts output retained) width body)%N.
```

## Galois.Rewrite.RewriteAuditSharedInterfaceRdCompareRealizesStatement

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditSharedInterfaceRdCompareRealizesStatement.v`.

```rocq
(** * RewriteAuditSharedInterfaceRdCompareRealizesStatement

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditQueueReference RewriteAuditSharedCompare
  RewriteAuditSharedExtract RewriteAuditSharedReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_shared_compare : forall {K Sort V}, encoding K -> encoding Sort ->
    encoding V ->
  rw_shared_tree K Sort V -> rw_shared_tree K Sort V -> option
    bool.

(** This statement fixes the rd compare realizes statement contract. *)
Definition rw_rd_compare_realizes_statement : Prop :=
  forall K Sort V (EK : encoding K)
    (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort :
    rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) lhs rhs,
  (forall
    k, fst (rw_queue_encoder_run op k) = encode EK k) ->
  (forall ty, fst (rw_queue_encoder_run
    sort ty) = encode ES ty) ->
  (forall v, fst (rw_queue_encoder_run value v) = encode EV v)
    ->
  exists work,
    rw_shared_compare_run op sort value lhs rhs (rw_shared_compare EK ES
    EV lhs rhs) work /\
    work <= rw_rd_compare_budget op sort value lhs rhs.

(** The public
    extractor realizes the same finite DP run whose work is bounded. *)


End FuturePublicImplementations.
```

## Galois.Rewrite.RewriteAuditSharedInterfaceRdExtractRealizesStatement

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditSharedInterfaceRdExtractRealizesStatement.v`.

```rocq
(** * RewriteAuditSharedInterfaceRdExtractRealizesStatement

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditQueueReference RewriteAuditSharedBoundsContracts
  RewriteAuditSharedExtract RewriteAuditSharedReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_shared_extract : forall {K Sort V}, encoding K -> encoding Sort -> encoding V ->

    (V -> nat) -> (K -> nat) -> rw_graph K Sort V -> rw_id -> option (rw_shared_tree K Sort
    V).

(** This statement fixes the rd extract realizes statement contract. *)
Definition rw_rd_extract_realizes_statement : Prop :=
  forall K Sort V (EK : encoding K) (ES :
    encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort :
    rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (vc : V -> nat *
    nat) (oc : K -> nat * nat) g root,
  (forall k, fst (rw_queue_encoder_run op k) = encode EK
    k) ->
  (forall ty, fst (rw_queue_encoder_run sort ty) = encode ES ty) ->
  (forall v, fst
    (rw_queue_encoder_run value v) = encode EV v) ->
  exists work,
    rw_shared_extract_run op
    sort value vc oc g root
      (rw_shared_extract EK ES EV (fun v => fst (vc v)) (fun k =>
    fst (oc k)) g root) work /\
    work <= rw_rd_extract_budget op sort value vc oc g
    root.

(** All public scalar observations agree with the fixed source mirrors on the same
    input. *)


End FuturePublicImplementations.
```

## Galois.Rewrite.RewriteAuditSharedPlain

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditSharedPlain.v`.

```rocq
(** * Fixed plain shared extraction and observations

    Plain computation retains the memo, immutable backpointers and additive tree objectives.
    For example, repeated children contribute repeatedly while their stored node is shared.
    Builds on: the shared representation, plain validation and fixed source data records. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Wellfounded.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditSharedCompare RewriteAuditSharedExtract
  RewriteAuditSharedReference.
Import List.ListNotations.
Local Coercion encode : encoding >-> Funclass.

Fixpoint rd_plain_pos_succ (p : positive) : positive :=
  match p with
  | xH => xO xH
  | xO rest => xI rest
  | xI rest => xO (rd_plain_pos_succ rest)
  end.

Fixpoint rd_plain_nat_positive (n : nat) : positive :=
  match n with 0 => xH | S rest => rd_plain_pos_succ (rd_plain_nat_positive rest) end.

Fixpoint rd_plain_pos_add (a b : positive) : positive :=
  match a, b with
  | xH, xH => xO xH
  | xH, xO y => xI y
  | xH, xI y => xO (rd_plain_pos_succ y)
  | xO x, xH => xI x
  | xI x, xH => xO (rd_plain_pos_succ x)
  | xO x, xO y => xO (rd_plain_pos_add x y)
  | xO x, xI y => xI (rd_plain_pos_add x y)
  | xI x, xO y => xI (rd_plain_pos_add x y)
  | xI x, xI y => xO (rd_plain_pos_succ (rd_plain_pos_add x y))
  end.

Definition rd_plain_N_add (a b : N) : N :=
  match a, b with
  | N0, _ => b
  | _, N0 => a
  | Npos x, Npos y => Npos (rd_plain_pos_add x y)
  end.

Fixpoint rd_plain_nat_N (n : nat) : N :=
  match n with 0 => 0%N | S rest => rd_plain_N_add 1%N (rd_plain_nat_N rest) end.

Fixpoint rd_plain_pos_nat (p : positive) : nat :=
  match p with
  | xH => 1
  | xO rest => let n := rd_plain_pos_nat rest in n + n
  | xI rest => let n := rd_plain_pos_nat rest in S (n + n)
  end.

Definition rd_plain_N_nat (n : N) : nat :=
  match n with N0 => 0 | Npos p => rd_plain_pos_nat p end.

Fixpoint rd_plain_pos_compare (otherwise : comparison) (p q : positive) : comparison :=
  match p, q with
  | xH, xH => otherwise
  | xH, xO _ | xH, xI _ => Lt
  | xO _, xH | xI _, xH => Gt
  | xO a, xO b | xI a, xI b => rd_plain_pos_compare otherwise a b
  | xO a, xI b => rd_plain_pos_compare Lt a b
  | xI a, xO b => rd_plain_pos_compare Gt a b
  end.

Definition rd_plain_N_compare (a b : N) : comparison :=
  match a, b with
  | N0, N0 => Eq
  | N0, _ => Lt
  | _, N0 => Gt
  | Npos x, Npos y => rd_plain_pos_compare Eq x y
  end.

Fixpoint rd_plain_headers_compare (xs ys : list positive) : comparison :=
  match xs, ys with
  | [], [] => Eq
  | [], _ :: _ => Lt
  | _ :: _, [] => Gt
  | x :: rest, y :: tail =>
    match rd_plain_pos_compare Eq x y with
    | Eq => rd_plain_headers_compare rest tail
    | answer => answer
    end
  end.

Definition rd_plain_header {K Sort V} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (node : rw_shared_node K Sort V) : list positive :=
  match node with
  | RWSharedVar _ _ _ ty v => [1%positive; encode ES ty; encode EV v; 1%positive]
  | RWSharedApp _ _ _ ty k children =>
    [2%positive; encode ES ty; encode EK k; encode nat_encoding (length children)]
  end.

Inductive rd_plain_compare_call : Type :=
  | RDPlainRoot (p q : positive) (memo : rw_rd_memo)
  | RDPlainChildren (xs ys : list positive) (memo : rw_rd_memo).

(** This fixed potential-subcall relation covers the literal root, head and tail call shapes. *)
Inductive rd_plain_compare_descend {K Sort V}
    (left right : Map.t positive (rw_shared_node K Sort V)) :
    rd_plain_compare_call -> rd_plain_compare_call -> Prop :=
  | RDPlainDescendChildren : forall p q memo a b,
      Map.get positive_encoding p left = Some a ->
      Map.get positive_encoding q right = Some b ->
      rd_plain_compare_descend left right
        (RDPlainChildren (rw_rd_children a) (rw_rd_children b) memo) (RDPlainRoot p q memo)
  | RDPlainDescendHead : forall x xs y ys memo,
      rd_plain_compare_descend left right
        (RDPlainRoot x y memo) (RDPlainChildren (x :: xs) (y :: ys) memo)
  | RDPlainDescendTail : forall x xs y ys memo middle,
      rd_plain_compare_descend left right
        (RDPlainChildren xs ys middle) (RDPlainChildren (x :: xs) (y :: ys) memo).

(** Full stored-graph validation makes this literal comparator subcall relation well founded. *)
Definition rw_rd_plain_compare_well_founded_type : Prop :=
  forall K Sort V (left right : rw_shared_tree K Sort V),
  rw_shared_validate left = true -> rw_shared_validate right = true ->
  well_founded (rd_plain_compare_descend
    (rw_shared_nodes K Sort V left) (rw_shared_nodes K Sort V right)).

Definition rd_plain_compare_body {K Sort V} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (left right : Map.t positive (rw_shared_node K Sort V))
    (call : rd_plain_compare_call)
    (recurse : forall child, rd_plain_compare_descend left right child call -> comparison *
  rw_rd_memo)
    : comparison * rw_rd_memo.
Proof.
  destruct call as [p q memo | xs ys memo].
  - destruct (Map.get (pair_encoding positive_encoding positive_encoding) (p, q) memo)
      as [cached |] eqn:Hmemo; [exact (cached, memo) |].
    destruct (Map.get positive_encoding p left) as [a |] eqn:Hleft;
      [|exact (Eq, memo)].
    destruct (Map.get positive_encoding q right) as [b |] eqn:Hright;
      [|exact (Eq, memo)].
    destruct (rd_plain_headers_compare (rd_plain_header EK ES EV a)
      (rd_plain_header EK ES EV b)) as [| |] eqn:Hheaders.
    + destruct (recurse (RDPlainChildren (rw_rd_children a) (rw_rd_children b) memo)
        (RDPlainDescendChildren left right p q memo a b Hleft Hright)) as [answer middle].
      exact (answer, Map.set (pair_encoding positive_encoding positive_encoding)
        (p, q) answer middle).
    + exact (Lt, Map.set (pair_encoding positive_encoding positive_encoding) (p, q) Lt memo).
    + exact (Gt, Map.set (pair_encoding positive_encoding positive_encoding) (p, q) Gt memo).
  - destruct xs as [|x xs]; destruct ys as [|y ys].
    + exact (Eq, memo).
    + exact (Lt, memo).
    + exact (Gt, memo).
    + destruct (recurse (RDPlainRoot x y memo)
        (RDPlainDescendHead left right x xs y ys memo)) as [head middle].
      destruct head.
      * exact (recurse (RDPlainChildren xs ys middle)
          (RDPlainDescendTail left right x xs y ys memo middle)).
      * exact (Lt, middle).
      * exact (Gt, middle).
Defined.

(** Accessibility drives exactly the fixed memo body, with no supplied algorithm operation. *)
Definition rd_plain_compare_execute {K Sort V} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (left right : Map.t positive (rw_shared_node K Sort V))
    (call : rd_plain_compare_call) (accessible : Acc (rd_plain_compare_descend left right) call)
    : comparison * rw_rd_memo :=
  @Fix_F rd_plain_compare_call (rd_plain_compare_descend left right)
    (fun _ => (comparison * rw_rd_memo)%type)
    (rd_plain_compare_body EK ES EV left right) call accessible.

(** The only builder argument is the library's own erased termination proof. *)
Definition rw_shared_compare_builder (Hwf : rw_rd_plain_compare_well_founded_type)
    {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (left right : rw_shared_tree K Sort V) : option bool.
Proof.
  destruct (rw_shared_validate left) eqn:Hleft;
    destruct (rw_shared_validate right) eqn:Hright.
  - pose (call := RDPlainRoot (rw_shared_root K Sort V left)
      (rw_shared_root K Sort V right) Map.empty).
    destruct (rd_plain_compare_execute EK ES EV (rw_shared_nodes K Sort V left)
      (rw_shared_nodes K Sort V right) call (Hwf K Sort V left right Hleft Hright call))
      as [answer memo].
    exact (Some (match answer with Gt => false | _ => true end)).
  - exact None.
  - exact None.
  - exact None.
Defined.

Definition rd_plain_candidate_get {K Sort V} (g : rw_graph K Sort V)
    (table : rw_rd_table) (id : rw_id) : option rw_rd_candidate :=
  match Map.get positive_encoding id (rw_class_roots g) with
  | None => None
  | Some root => Map.get positive_encoding root table
  end.

Fixpoint rd_plain_gather {K Sort V} (g : rw_graph K Sort V) (table : rw_rd_table)
    (ids : list rw_id) : option (list positive * N * N) :=
  match ids with
  | [] => Some ([], 0%N, 0%N)
  | id :: rest =>
    let head := rd_plain_candidate_get g table id in
    let tail := rd_plain_gather g table rest in
    match head, tail with
    | Some candidate, Some (pointers, cost, size) =>
      Some (rw_rd_pointer candidate :: pointers,
        rd_plain_N_add (rw_rd_cost candidate) cost, rd_plain_N_add (rw_rd_size candidate) size)
    | _, _ => None
    end
  end.

Definition rd_plain_allocate {K Sort V} (node : rw_shared_node K Sort V)
    (cost size : N) (store : rw_rd_store K Sort V) : rw_rd_candidate * rw_rd_store K Sort V :=
  let id := rw_rd_next store in
  (RwRdCandidate id cost size, RwRdStore (Map.set positive_encoding id node (rw_rd_nodes store))
    (rd_plain_pos_succ id)).

Definition rd_plain_production {K Sort V} (vc : V -> nat) (oc : K -> nat)
    (g : rw_graph K Sort V) (old : rw_rd_table) (node : rw_node K Sort V)
    (store : rw_rd_store K Sort V) : option rw_rd_candidate * rw_rd_store K Sort V :=
  match node with
  | RWNVar ty v =>
    let '(candidate, next) := rd_plain_allocate (RWSharedVar K Sort V ty v)
      (rd_plain_nat_N (vc v)) 1%N store in (Some candidate, next)
  | RWNApp ty op children =>
    match rd_plain_gather g old children with
    | None => (None, store)
    | Some (pointers, cost, size) =>
      let '(candidate, next) := rd_plain_allocate (RWSharedApp K Sort V ty op pointers)
        (rd_plain_N_add (rd_plain_nat_N (oc op)) cost) (rd_plain_N_add 1%N size) store in
      (Some candidate, next)
    end
  end.

Definition rd_plain_choose (Hwf : rw_rd_plain_compare_well_founded_type)
    {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (store : rw_rd_store K Sort V) (old fresh : rw_rd_candidate) : rw_rd_candidate :=
  match rd_plain_N_compare (rw_rd_cost old) (rw_rd_cost fresh) with
  | Lt => old
  | Gt => fresh
  | Eq => match rd_plain_N_compare (rw_rd_size old) (rw_rd_size fresh) with
    | Lt => old
    | Gt => fresh
    | Eq => match rw_shared_compare_builder Hwf EK ES EV
        (RwSharedTree K Sort V (rw_rd_pointer old) (rw_rd_nodes store))
        (RwSharedTree K Sort V (rw_rd_pointer fresh) (rw_rd_nodes store)) with
      | Some true => old
      | _ => fresh
      end
    end
  end.

Definition rd_plain_insert (Hwf : rw_rd_plain_compare_well_founded_type)
    {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (store : rw_rd_store K Sort V) (root : rw_id) (fresh : rw_rd_candidate)
    (table : rw_rd_table) : rw_rd_table :=
  let chosen := match Map.get positive_encoding root table with
    | None => fresh
    | Some old => rd_plain_choose Hwf EK ES EV store old fresh
    end in
  Map.set positive_encoding root chosen table.

Fixpoint rd_plain_round (Hwf : rw_rd_plain_compare_well_founded_type)
    {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (vc : V -> nat) (oc : K -> nat) (g : rw_graph K Sort V) (old : rw_rd_table)
    (entries : list (rw_id * (rw_id * rw_node K Sort V))) (table : rw_rd_table)
    (store : rw_rd_store K Sort V) : rw_rd_table * rw_rd_store K Sort V :=
  match entries with
  | [] => (table, store)
  | (_, (owner, node)) :: rest =>
    let root := Map.get positive_encoding owner (rw_class_roots g) in
    let '(produced, next) := rd_plain_production vc oc g old node store in
    let inserted := match root, produced with
      | Some root, Some fresh => rd_plain_insert Hwf EK ES EV next root fresh table
      | _, _ => table
      end in
    rd_plain_round Hwf EK ES EV vc oc g old rest inserted next
  end.

Fixpoint rd_plain_rounds (Hwf : rw_rd_plain_compare_well_founded_type)
    {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (vc : V -> nat) (oc : K -> nat) (g : rw_graph K Sort V)
    (entries : list (rw_id * (rw_id * rw_node K Sort V))) (rounds : positive)
    (table : rw_rd_table) (store : rw_rd_store K Sort V) : rw_rd_table * rw_rd_store K Sort V :=
  match rounds with
  | xH => rd_plain_round Hwf EK ES EV vc oc g table entries table store
  | xO p =>
    let '(middle, ms) := rd_plain_rounds Hwf EK ES EV vc oc g entries p table store in
    rd_plain_rounds Hwf EK ES EV vc oc g entries p middle ms
  | xI p =>
    let '(first, fs) := rd_plain_round Hwf EK ES EV vc oc g table entries table store in
    let '(middle, ms) := rd_plain_rounds Hwf EK ES EV vc oc g entries p first fs in
    rd_plain_rounds Hwf EK ES EV vc oc g entries p middle ms
  end.

(** The extractor runs fixed binary DP rounds and retains every allocated backpointer node. *)
Definition rw_shared_extract_builder (Hwf : rw_rd_plain_compare_well_founded_type)
    {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (vc : V -> nat) (oc : K -> nat) (g : rw_graph K Sort V) (root : rw_id)
    : option (rw_shared_tree K Sort V) :=
  match length (rw_roots g) with
  | 0 => None
  | S count =>
    let '(table, store) := rd_plain_rounds Hwf EK ES EV vc oc g (Map.elements (rw_nodes g))
      (rd_plain_nat_positive count) Map.empty (RwRdStore Map.empty 1%positive) in
    match rd_plain_candidate_get g table root with
    | None => None
    | Some candidate =>
      Some (RwSharedTree K Sort V (rw_rd_pointer candidate) (rw_rd_nodes store))
    end
  end.

Fixpoint rd_plain_shared_gather (table : rw_rd_table) (ids : list positive) : option (N * N) :=
  match ids with
  | [] => Some (0%N, 0%N)
  | id :: rest =>
    let head := Map.get positive_encoding id table in
    let tail := rd_plain_shared_gather table rest in
    match head, tail with
    | Some candidate, Some (cost, size) =>
      Some (rd_plain_N_add (rw_rd_cost candidate) cost, rd_plain_N_add (rw_rd_size candidate) size)
    | _, _ => None
    end
  end.

Definition rd_plain_scalar_node {K Sort V} (vc : V -> nat) (oc : K -> nat)
    (table : rw_rd_table) (id : positive) (node : rw_shared_node K Sort V)
    : option rw_rd_candidate :=
  match node with
  | RWSharedVar _ _ _ _ v => Some (RwRdCandidate id (rd_plain_nat_N (vc v)) 1%N)
  | RWSharedApp _ _ _ _ op children =>
    match rd_plain_shared_gather table children with
    | None => None
    | Some (cost, size) => Some (RwRdCandidate id
      (rd_plain_N_add (rd_plain_nat_N (oc op)) cost) (rd_plain_N_add 1%N size))
    end
  end.

Fixpoint rd_plain_scalar_pass {K Sort V} (vc : V -> nat) (oc : K -> nat)
    (old : rw_rd_table) (entries : list (positive * rw_shared_node K Sort V))
    (table : rw_rd_table) : rw_rd_table :=
  match entries with
  | [] => table
  | (id, node) :: rest =>
    let next := match rd_plain_scalar_node vc oc old id node with
      | None => table
      | Some candidate => Map.set positive_encoding id candidate table
      end in
    rd_plain_scalar_pass vc oc old rest next
  end.

Fixpoint rd_plain_scalar_rounds {K Sort V} (vc : V -> nat) (oc : K -> nat)
    (entries : list (positive * rw_shared_node K Sort V)) (rounds : positive)
    (table : rw_rd_table) : rw_rd_table :=
  match rounds with
  | xH => rd_plain_scalar_pass vc oc table entries table
  | xO p =>
    let middle := rd_plain_scalar_rounds vc oc entries p table in
    rd_plain_scalar_rounds vc oc entries p middle
  | xI p =>
    let first := rd_plain_scalar_pass vc oc table entries table in
    let middle := rd_plain_scalar_rounds vc oc entries p first in
    rd_plain_scalar_rounds vc oc entries p middle
  end.

Definition rd_plain_scalar_observe {K Sort V} (vc : V -> nat) (oc : K -> nat)
    (dag : rw_shared_tree K Sort V) : option (N * N) :=
  if rw_shared_validate dag then
    let entries := Map.elements (rw_shared_nodes K Sort V dag) in
    match length entries with
    | 0 => None
    | S count =>
      let table := rd_plain_scalar_rounds vc oc entries (rd_plain_nat_positive count) Map.empty in
      option_map (fun candidate => (rw_rd_cost candidate, rw_rd_size candidate))
        (Map.get positive_encoding (rw_shared_root K Sort V dag) table)
    end
  else None.

(** Binary cost sums every occurrence in the expanded tree without unfolding the shared DAG. *)
Definition rw_shared_tree_cost_binary {K Sort V} (vc : V -> nat) (oc : K -> nat)
    (dag : rw_shared_tree K Sort V) : option N :=
  option_map fst (rd_plain_scalar_observe vc oc dag).

(** Binary size uses the same fixed source pass and retains repeated child occurrences. *)
Definition rw_shared_tree_size_binary {K Sort V} (dag : rw_shared_tree K Sort V) : option N :=
  option_map snd (rd_plain_scalar_observe (fun _ => 0) (fun _ => 0) dag).

(** Unary cost converts the actual binary tree objective only after a successful observation. *)
Definition rw_shared_tree_cost {K Sort V} (vc : V -> nat) (oc : K -> nat)
    (dag : rw_shared_tree K Sort V) : option nat :=
  option_map rd_plain_N_nat (rw_shared_tree_cost_binary vc oc dag).
```

## Galois.Rewrite.RewriteAuditSharedInterfaceRdScalarRealizesStatement

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditSharedInterfaceRdScalarRealizesStatement.v`.

```rocq
(** * RewriteAuditSharedInterfaceRdScalarRealizesStatement

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditSharedObservers RewriteAuditSharedPlain
  RewriteAuditSharedReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_shared_tree_cost : forall {K Sort V}, (V -> nat) -> (K -> nat) ->

    rw_shared_tree K Sort V -> option nat.

Variable rw_shared_tree_cost_binary : forall {K
    Sort V}, (V -> nat) -> (K -> nat) ->
  rw_shared_tree K Sort V -> option N.

Variable rw_shared_tree_size_binary : forall {K Sort V}, rw_shared_tree K Sort V -> option N.

(**
    The actual public comparator realizes the fixed same-input operational relation.
    *)

(** This statement fixes the rd scalar realizes statement contract. *)
Definition rw_rd_scalar_realizes_statement : Prop :=
  forall K Sort V (vc : V ->
    nat * nat) (oc : K -> nat * nat)
    (dag : rw_shared_tree K Sort V),
  rw_shared_tree_cost
    (fun v => fst (vc v)) (fun k => fst (oc k)) dag =
    fst (rw_shared_tree_cost_atomic vc oc
    dag) /\
  rw_shared_tree_cost_binary (fun v => fst (vc v)) (fun k => fst (oc k)) dag =

    fst (rw_shared_tree_cost_binary_atomic vc oc dag) /\
  rw_shared_tree_size_binary dag = fst
    (rw_shared_tree_size_binary_atomic dag).




End FuturePublicImplementations.
```

## Galois.Rewrite.RewriteAuditSharedInterfaceSharedCompareAgreesContract

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditSharedInterfaceSharedCompareAgreesContract.v`.

```rocq
(** * RewriteAuditSharedInterfaceSharedCompareAgreesContract

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditSharedReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_shared_compare : forall {K Sort V}, encoding K -> encoding Sort ->
    encoding V ->
  rw_shared_tree K Sort V -> rw_shared_tree K Sort V -> option
    bool.

(** This statement fixes the shared compare agrees contract. *)
Definition rw_shared_compare_agrees_contract : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (left right : rw_shared_tree K Sort V) t u,
    rw_shared_wf left -> rw_shared_wf right ->
    rw_shared_unfold left = Some t -> rw_shared_unfold right = Some u ->
    rw_shared_compare EK ES EV left right =
      Some (rw_codes_leb (rw_tree_code EK ES EV t) (rw_tree_code EK ES EV u)).


End FuturePublicImplementations.
```

## Galois.Rewrite.RewriteAuditSharedInterfaceSharedCompareRejectContract

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditSharedInterfaceSharedCompareRejectContract.v`.

```rocq
(** * RewriteAuditSharedInterfaceSharedCompareRejectContract

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditSharedReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_shared_compare : forall {K Sort V}, encoding K -> encoding Sort ->
    encoding V ->
  rw_shared_tree K Sort V -> rw_shared_tree K Sort V -> option
    bool.

(** This statement fixes the shared compare reject contract. *)
Definition rw_shared_compare_reject_contract : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (left right : rw_shared_tree K Sort V),
    ~ rw_shared_wf left \/ ~ rw_shared_wf right -> rw_shared_compare EK ES EV left right = None.



End FuturePublicImplementations.
```

## Galois.Rewrite.RewriteAuditSharedInterfaceSharedExtractUnfoldContract

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditSharedInterfaceSharedExtractUnfoldContract.v`.

```rocq
(** * RewriteAuditSharedInterfaceSharedExtractUnfoldContract

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditSharedReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_shared_extract : forall {K Sort V}, encoding K -> encoding Sort -> encoding V ->

    (V -> nat) -> (K -> nat) -> rw_graph K Sort V -> rw_id -> option (rw_shared_tree K Sort
    V).

(** This statement fixes the shared extract unfold contract. *)
Definition rw_shared_extract_unfold_contract : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (sig : rw_signature K Sort V) vc oc (g : rw_graph K Sort V) c,
    rw_graph_wf sig g ->
    match rw_shared_extract EK ES EV vc oc g c,
          rw_extract_tree EK ES EV vc oc g c with
    | None, None => True
    | Some dag, Some tree => rw_shared_wf dag /\ rw_shared_unfold dag = Some tree
    | _, _ => False
    end.



End FuturePublicImplementations.
```

## Galois.Rewrite.RewriteAuditSharedInterfaceSharedTreeCostAgreesContract

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditSharedInterfaceSharedTreeCostAgreesContract.v`.

```rocq
(** * RewriteAuditSharedInterfaceSharedTreeCostAgreesContract

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditSharedPlain RewriteAuditSharedReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_shared_tree_cost : forall {K Sort V}, (V -> nat) -> (K -> nat) ->

    rw_shared_tree K Sort V -> option nat.

(** This statement fixes the shared tree cost agrees contract. *)
Definition rw_shared_tree_cost_agrees_contract : Prop :=
  forall K Sort V (vc : V -> nat) (oc : K -> nat)
    (dag : rw_shared_tree K Sort V) (tree : rw_term K Sort V),
    rw_shared_wf dag -> rw_shared_unfold dag = Some tree ->
    rw_shared_tree_cost vc oc dag = Some (rw_tree_cost vc oc tree).



End FuturePublicImplementations.
```

## Galois.Rewrite.RewriteAuditSharedInterfaceSharedTreeCostBinaryAgreesContract

Card: AUD-RW-MODELS

Source destination:
  `theories/Rewrite/RewriteAuditSharedInterfaceSharedTreeCostBinaryAgreesContract.v`.

```rocq
(** * RewriteAuditSharedInterfaceSharedTreeCostBinaryAgreesContract

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditSharedPlain RewriteAuditSharedReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_shared_tree_cost_binary : forall {K
    Sort V}, (V -> nat) -> (K -> nat) ->
  rw_shared_tree K Sort V -> option N.

(** This statement fixes the shared tree cost binary agrees contract. *)
Definition rw_shared_tree_cost_binary_agrees_contract : Prop :=
  forall K Sort V (vc : V -> nat) (oc : K -> nat)
    (dag : rw_shared_tree K Sort V) (tree : rw_term K Sort V),
    rw_shared_wf dag -> rw_shared_unfold dag = Some tree ->
    rw_shared_tree_cost_binary vc oc dag = Some (N.of_nat (rw_tree_cost vc oc tree)).



End FuturePublicImplementations.
```

## Galois.Rewrite.RewriteAuditSharedInterfaceSharedTreeSizeBinaryAgreesContract

Card: AUD-RW-MODELS

Source destination:
  `theories/Rewrite/RewriteAuditSharedInterfaceSharedTreeSizeBinaryAgreesContract.v`.

```rocq
(** * RewriteAuditSharedInterfaceSharedTreeSizeBinaryAgreesContract

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditSharedPlain RewriteAuditSharedReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_shared_tree_size_binary : forall {K Sort V}, rw_shared_tree K Sort V -> option N.

(**
    The actual public comparator realizes the fixed same-input operational relation.
    *)

(** This statement fixes the shared tree size binary agrees contract. *)
Definition rw_shared_tree_size_binary_agrees_contract : Prop :=
  forall K Sort V (dag : rw_shared_tree K Sort V) tree,
    rw_shared_wf dag -> rw_shared_unfold dag = Some tree ->
    rw_shared_tree_size_binary dag = Some (N.of_nat (rw_tree_size tree)).



End FuturePublicImplementations.
```

## Galois.Rewrite.RewriteAuditSharedInterfaceSharedObserversRejectContract

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditSharedInterfaceSharedObserversRejectContract.v`.

```rocq
(** * RewriteAuditSharedInterfaceSharedObserversRejectContract

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditSharedPlain RewriteAuditSharedReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_shared_tree_cost : forall {K Sort V}, (V -> nat) -> (K -> nat) ->

    rw_shared_tree K Sort V -> option nat.

Variable rw_shared_tree_cost_binary : forall {K
    Sort V}, (V -> nat) -> (K -> nat) ->
  rw_shared_tree K Sort V -> option N.

Variable rw_shared_tree_size_binary : forall {K Sort V}, rw_shared_tree K Sort V -> option N.

(**
    The actual public comparator realizes the fixed same-input operational relation.
    *)

(** This statement fixes the shared observers reject contract. *)
Definition rw_shared_observers_reject_contract : Prop :=
  forall K Sort V (vc : V -> nat) (oc : K -> nat) (dag : rw_shared_tree K Sort V),
    ~ rw_shared_wf dag -> rw_shared_unfold dag = None /\ rw_shared_tree_cost vc oc dag = None /\
    rw_shared_tree_cost_binary vc oc dag = None /\ rw_shared_tree_size_binary dag = None.



End FuturePublicImplementations.
```

## Galois.Rewrite.RewriteAuditPlainPrimitives

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditPlainPrimitives.v`.

```rocq
(** * RewriteAuditPlainPrimitives

    This module evaluates the fixed source phases without cost or receipt construction.
    For example, a lookup uses the actual plain map operation once.
    Builds on: the canonical Rewrite source equations and Collections. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexBuild RewriteAuditIndexPrepareReference
  RewriteAuditIndexReference RewriteAuditIndexTickReference RewriteAuditQueueReference.
Import List.ListNotations.
Local Coercion encode : encoding >-> Funclass.

Definition rw_plain_audit_positive_encode := positive_encoding.
Definition rw_plain_audit_nat_encode := nat_encoding.
Definition rw_plain_audit_pair_encode := @pair_encoding.
Definition rw_plain_rw_rd_pair_encode := pair_encoding positive_encoding positive_encoding.
Definition rw_plain_rw_rp_stamp_encode := pair_encoding nat_encoding nat_encoding.
Definition rw_plain_rw_queue_encoder_run {A} (E : encoding A) := encode E.
Definition rw_plain_rw_external_encoding_events {A} (E : encoding A) := E.
Definition rw_plain_rw_external_events_work := tt.
Definition rw_plain_audit_map_get := @Map.get.
Definition rw_plain_audit_map_set := @Map.set.
Definition rw_plain_audit_map_remove := @Map.remove.
Definition rw_plain_audit_map_elements := @Map.elements.
Definition rw_plain_audit_list_encode {A} (E : encoding A) := encode (list_encoding E).
Definition rw_plain_audit_positive_eqb := Pos.eqb.
Definition rw_plain_rw_fuel_pos_succ := Pos.succ.
Definition rw_plain_rw_fuel_length := @length.
Definition rw_plain_rw_fuel_add := Nat.add.
Definition rw_plain_rw_fuel_mul := Nat.mul.
Definition rw_plain_rw_fuel_to_positive := Pos.of_succ_nat.
Definition rw_plain_rw_rd_positive_compare_cont := Pos.compare_cont.
Definition rw_plain_rw_ri_positive_dec_atomic (a b : positive) : bool :=
  if Pos.eq_dec a b then true else false.
Definition rw_plain_rw_ri_find_atomic := @rw_index_find.
Definition rw_plain_rw_ri_canon_atomic := @rw_index_canonical_node.
Definition rw_plain_rw_ri_graph_atomic := @rw_index_graph.
Definition rw_plain_rw_ri_tick_atomic := @rw_index_tick.
Definition rw_plain_rw_ri_rebuild_atomic := @rw_index_rebuild.
Definition rw_plain_rw_ri_rebuild_fuel_atomic := @rw_ri_rebuild_fuel.
Definition rw_plain_rw_ri_bucket_ids {A} (E : encoding A) (_ : unit) (key : A)
    (table : Map.t A (FinSet.t rw_id)) : list rw_id :=
  let bucket := match Map.get E key table with Some b => b | None => FinSet.empty end in
  FinSet.elements bucket.

Definition rw_plain_rw_ri_prepare_once {K Sort V} (op : encoding K) (value : encoding V)
    (g : rw_graph K Sort V) : rw_index_state K Sort V :=
  let empty := RwRiBuildAcc Map.empty Map.empty Map.empty in
  let buckets := rw_ri_build_nodes_value op value g (rw_nodes_in g) empty in
  let dirty := FinSet.of_list positive_encoding (rw_nodes_in g) in
  let fresh := rw_ri_fresh_value g in
  RWIndexState g UnionFind.make (rw_ri_build_parents buckets) Map.empty Map.empty
    (rw_nodes_in g) dirty rw_pending_empty (rw_ri_build_ops buckets) (rw_ri_build_vars buckets)
  fresh.

Fixpoint rw_plain_rw_ri_max_entries_atomic {A K Sort V : Type}
    (entries : list (positive * A)) (current : positive) : positive :=
  match entries with
  | nil => current
  | (id, _) :: rest =>
    rw_plain_rw_ri_max_entries_atomic (K:=K) (Sort:=Sort) (V:=V) rest
      (Pos.max id current)
  end.

Definition rw_plain_rw_ri_pair_merge_atomic {K Sort V}
    (s dropped : rw_index_state K Sort V) (p : rw_pair) (remaining : rw_pending_queue)
    (ra rb : rw_id) (_ : list unit) : rw_index_state K Sort V * rw_index_event :=
  let forest := UnionFind.union positive_encoding ra rb (rw_index_forest s) in
  let root := fst (UnionFind.find positive_encoding ra forest) in
  let table := rw_index_parent_buckets s in
  let left_bucket := rw_index_bucket positive_encoding ra table in
  let right_bucket := rw_index_bucket positive_encoding rb table in
  let merged := FinSet.union positive_encoding left_bucket right_bucket in
  let without := Map.remove positive_encoding rb (Map.remove positive_encoding ra table) in
  let parents := if FinSet.is_empty merged then without
    else Map.set positive_encoding root merged without in
  let '(order, dirty) := rw_ri_mark_dirty (FinSet.elements merged)
    (rw_index_dirty_order s) (rw_index_dirty_set s) in
  let next := rw_ri_state_update s forest parents (rw_index_signatures s) (rw_index_node_keys s)
    order dirty remaining in
  (next, RWIndexCongruence p ra rb root).

Record rw_plain_callbacks (K Sort V H : Type) := RwPlainCallbacks {
  rw_plain_rw_rp_var_sort : V -> option Sort;
  rw_plain_rw_rp_operator_shape : K -> list Sort -> Sort -> bool;
  rw_plain_rw_rp_hole_sort : rw_rule K Sort V H -> H -> option Sort;
  rw_plain_guard : rw_rule K Sort V H -> rw_substitution K Sort V H -> bool
}.
Arguments RwPlainCallbacks {K Sort V H}.
Arguments rw_plain_rw_rp_var_sort {K Sort V H}.
Arguments rw_plain_rw_rp_operator_shape {K Sort V H}.
Arguments rw_plain_rw_rp_hole_sort {K Sort V H}.
Arguments rw_plain_guard {K Sort V H}.
Definition rw_plain_callbacks_of {K Sort V H} (sig : rw_signature K Sort V) :
    rw_plain_callbacks K Sort V H :=
  RwPlainCallbacks (rw_var_sort sig) (rw_operator_shape sig)
    rw_hole_sort (fun rule => rw_condition rule).
Definition rw_plain_rw_rp_guard_atomic {K Sort V H} (hole : encoding H)
    (callbacks : rw_plain_callbacks K Sort V H) (rule : rw_rule K Sort V H)
    (bindings : Map.t H (rw_term K Sort V)) : bool :=
  rw_plain_guard callbacks rule (fun h => Map.get hole h bindings).

Definition rw_plain_strategy (K Sort V H : Type) :=
  rw_index_state K Sort V -> option (rw_attempt K Sort V H).
Definition rw_plain_rw_rp_strategy_run {K Sort V H} (op : encoding K) (value : encoding V)
    (strategy : rw_plain_strategy K Sort V H) (state : rw_index_state K Sort V) := strategy state.
Definition rw_plain_fact_strategy (K Sort V H F : Type) :=
  rw_index_state K Sort V -> F -> Map.t rw_id F -> option (rw_attempt K Sort V H).
Definition rw_plain_rw_rp_fact_strategy_run {K Sort V H F} (op : encoding K) (value : encoding V)
    (strategy : rw_plain_fact_strategy K Sort V H F) (state : rw_index_state K Sort V)
    (unknown : F) (facts : Map.t rw_id F) := strategy state unknown facts.

Arguments rw_plain_audit_pair_encode {A B} _ _.
Arguments rw_plain_audit_map_get {K V} _ _ _.
Arguments rw_plain_audit_map_set {K V} _ _ _ _.
Arguments rw_plain_audit_map_remove {K V} _ _ _.
Arguments rw_plain_audit_map_elements {K V} _.
Arguments rw_plain_rw_fuel_length {A} _.
Arguments rw_plain_rw_ri_find_atomic {K Sort V} _ _.
Arguments rw_plain_rw_ri_canon_atomic {K Sort V} _ _.
Arguments rw_plain_rw_ri_graph_atomic {K Sort V} _.
Arguments rw_plain_rw_ri_tick_atomic {K Sort V} _ _ _ _.
Arguments rw_plain_rw_ri_rebuild_atomic {K Sort V} _ _ _ _.
Arguments rw_plain_rw_ri_rebuild_fuel_atomic {K Sort V} _.
```

## Galois.Rewrite.RewriteAuditPlainCore1

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditPlainCore1.v`.

```rocq
(** * RewriteAuditPlainCore1

    This module evaluates the fixed source phases without cost or receipt construction.
    For example, a lookup uses the actual plain map operation once.
    Builds on: the canonical Rewrite source equations and Collections. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexReference RewriteAuditIndexRun
  RewriteAuditPlainPrimitives.
Import List.ListNotations.
Local Coercion encode : encoding >-> Funclass.

Definition rw_plain_rw_ri_encoded_equal { A } ( adapter : encoding A ) ( a b : A ) : bool :=
let p := rw_plain_rw_queue_encoder_run adapter a in let q := rw_plain_rw_queue_encoder_run
  adapter b in let answer := rw_plain_rw_ri_positive_dec_atomic p q in answer.

Definition rw_plain_rw_ri_same_class_atomic { K Sort V } ( state : rw_index_state K Sort V ) ( a
  b : rw_id ) : bool :=
let first := rw_plain_rw_ri_find_atomic state a in match first with | None => false | Some x =>
  let second := rw_plain_rw_ri_find_atomic state b in match second with | None => false | Some y
  => let answer := rw_plain_audit_positive_eqb x y in answer end end.

Fixpoint rw_plain_rw_ri_member_atomic { K Sort V } ( op : encoding K ) ( sort : encoding Sort )
  ( value : encoding V ) ( state : rw_index_state K Sort V ) ( term : rw_term K Sort V ) ( root
  : rw_id ) : bool :=
match term with | RWVar ty v => let candidates := rw_plain_rw_ri_bucket_ids (
  rw_plain_rw_external_encoding_events value ) rw_plain_rw_external_events_work v (
  rw_index_variables state ) in let fix visit ( ids : list rw_id ) : bool := match ids with |
  nil => false | id :: rest => let found := rw_plain_audit_map_get
  rw_plain_audit_positive_encode id ( rw_nodes ( rw_index_base state ) ) in let head := match
  found with | Some ( owner , RWNVar ty' v' ) => let same_sort := rw_plain_rw_ri_encoded_equal
  sort ty ty' in if same_sort then let same_value := rw_plain_rw_ri_encoded_equal value v v' in
  if same_value then let same_class := rw_plain_rw_ri_same_class_atomic state root owner in
  same_class else false else false | _ => false end in let tail := visit rest in head || tail
  end in let answer := visit candidates in answer | RWApp ty k children => let candidates :=
  rw_plain_rw_ri_bucket_ids ( rw_plain_rw_external_encoding_events op )
  rw_plain_rw_external_events_work k ( rw_index_operators state ) in let fix visit ( ids : list
  rw_id ) : bool := match ids with | nil => false | id :: rest => let found :=
  rw_plain_audit_map_get rw_plain_audit_positive_encode id ( rw_nodes ( rw_index_base state ) )
  in let head := match found with | Some ( owner , RWNApp ty' k' child_ids ) => let same_sort :=
  rw_plain_rw_ri_encoded_equal sort ty ty' in if same_sort then let same_op :=
  rw_plain_rw_ri_encoded_equal op k k' in if same_op then let same_class :=
  rw_plain_rw_ri_same_class_atomic state root owner in let fix pairs ( terms : list ( rw_term K
  Sort V ) ) ( classes : list rw_id ) : bool := match terms , classes with | nil , nil => true |
  t :: ts , c :: cs => let head := rw_plain_rw_ri_member_atomic op sort value state t c in let
  tail := pairs ts cs in head && tail | _ , _ => false end in let same_children := pairs
  children child_ids in same_class && same_children else false else false | _ => false end in
  let tail := visit rest in head || tail end in let answer := visit candidates in answer end.

Definition rw_plain_rw_ri_grow_node { K Sort V } ( node : rw_node K Sort V ) ( state : rw_graph
  K Sort V * positive ) : ( rw_id * ( rw_graph K Sort V * positive ) ) :=
let ' ( graph , id ) := state in let aliases := rw_plain_audit_map_set
  rw_plain_audit_positive_encode id id ( rw_class_roots graph ) in let sorts :=
  rw_plain_audit_map_set rw_plain_audit_positive_encode id ( rw_node_sort node ) ( rw_sorts
  graph ) in let nodes := rw_plain_audit_map_set rw_plain_audit_positive_encode id ( id , node )
  ( rw_nodes graph ) in let fresh := rw_plain_rw_fuel_pos_succ id in ( id , ( RwGraph ( id ::
  rw_roots graph ) ( id :: rw_nodes_in graph ) aliases sorts nodes , fresh ) ).

Fixpoint rw_plain_rw_ri_grow_term { K Sort V } ( term : rw_term K Sort V ) ( state : rw_graph K
  Sort V * positive ) : ( rw_id * ( rw_graph K Sort V * positive ) ) :=
match term with | RWVar ty v => let out := rw_plain_rw_ri_grow_node ( RWNVar ty v ) state in out
  | RWApp ty op terms => let fix visit ( terms : list ( rw_term K Sort V ) ) ( state : rw_graph
  K Sort V * positive ) : ( list rw_id * ( rw_graph K Sort V * positive ) ) := match terms with
  | nil => ( nil , state ) | term :: rest => let '( id , next ) := rw_plain_rw_ri_grow_term term
  state in let '( ids , final ) := visit rest next in ( id :: ids , final ) end in let '( ids ,
  next ) := visit terms state in let out := rw_plain_rw_ri_grow_node ( RWNApp ty op ids ) next
  in out end.

Definition rw_plain_rw_ri_accept_atomic { K Sort V H } ( op : encoding K ) ( sort : encoding
  Sort ) ( value : encoding V ) ( state : rw_index_state K Sort V ) ( attempt : rw_attempt K
  Sort V H ) ( rhs : rw_term K Sort V ) : option ( rw_index_state K Sort V ) :=
let graph := rw_plain_rw_ri_graph_atomic state in let '( rhs_root , ( grown , _ ) ) :=
  rw_plain_rw_ri_grow_term rhs ( graph , rw_index_fresh state ) in let prepared :=
  rw_plain_rw_ri_prepare_once op value grown in let first := rw_plain_rw_ri_find_atomic prepared
  ( rw_attempt_root attempt ) in match first with | None => None | Some a => let second :=
  rw_plain_rw_ri_find_atomic prepared rhs_root in match second with | None => None | Some b =>
  let left_sort := rw_plain_audit_map_get rw_plain_audit_positive_encode a ( rw_sorts grown ) in
  match left_sort with | None => None | Some sa => let right_sort := rw_plain_audit_map_get
  rw_plain_audit_positive_encode b ( rw_sorts grown ) in match right_sort with | None => None |
  Some sb => let same_sort := rw_plain_rw_ri_encoded_equal sort sa sb in if same_sort then let
  '( machine , _ ) := rw_plain_rw_ri_pair_merge_atomic prepared prepared ( rw_attempt_root
  attempt , rhs_root ) ( rw_index_pending prepared ) a b nil in Some machine else None end end
  end end.

Fixpoint rw_plain_rw_rp_term_sorts { K Sort V } ( terms : list ( rw_term K Sort V ) ) : list Sort :=
match terms with | nil => nil | t :: rest => let tail := rw_plain_rw_rp_term_sorts rest in
  rw_sort t :: tail end.

Fixpoint rw_plain_rw_rp_type_atomic { K Sort V H } ( sort : encoding Sort ) ( callbacks :
  rw_plain_callbacks K Sort V H ) ( term : rw_term K Sort V ) : bool :=
match term with | RWVar ty v => let declared := rw_plain_rw_rp_var_sort callbacks v in match
  declared with | None => false | Some s => let answer := rw_plain_rw_ri_encoded_equal sort ty s
  in answer end | RWApp ty op children => let fix visit ( terms : list ( rw_term K Sort V ) ) :
  bool := match terms with | nil => true | t :: rest => let head := rw_plain_rw_rp_type_atomic
  sort callbacks t in let tail := visit rest in head && tail end in let typed := visit children
  in let sorts := rw_plain_rw_rp_term_sorts children in let shape :=
  rw_plain_rw_rp_operator_shape callbacks op sorts ty in typed && shape end.

Fixpoint rw_plain_rw_rp_sub_check_atomic { K Sort V H } ( sort : encoding Sort ) ( hole :
  encoding H ) ( callbacks : rw_plain_callbacks K Sort V H ) ( rule : rw_rule K Sort V H ) (
  holes : list H ) ( bindings : Map.t H ( rw_term K Sort V ) ) : bool :=
match holes with | nil => true | h :: rest => let declared := rw_plain_rw_rp_hole_sort callbacks
  rule h in let head := match declared with | None => false | Some ty => let binding :=
  rw_plain_audit_map_get ( rw_plain_rw_external_encoding_events hole ) h bindings in match
  binding with | None => false | Some term => let same_sort := rw_plain_rw_ri_encoded_equal sort
  ( rw_sort term ) ty in if same_sort then let typed := rw_plain_rw_rp_type_atomic sort
  callbacks term in typed else false end end in let tail := rw_plain_rw_rp_sub_check_atomic sort
  hole callbacks rule rest bindings in head && tail end.

Fixpoint rw_plain_rw_rp_instantiate_atomic { K Sort V H } ( hole : encoding H ) ( bindings :
  Map.t H ( rw_term K Sort V ) ) ( pattern : rw_pattern K Sort V H ) : option ( rw_term K Sort V
  ) :=
match pattern with | RWHole _ h => let out := rw_plain_audit_map_get (
  rw_plain_rw_external_encoding_events hole ) h bindings in out | RWPVar ty v => Some ( RWVar ty
  v ) | RWPApp ty op children => let fix visit ( ps : list ( rw_pattern K Sort V H ) ) : option
  ( list ( rw_term K Sort V ) ) := match ps with | nil => Some nil | p :: rest => let head :=
  rw_plain_rw_rp_instantiate_atomic hole bindings p in match head with | None => None | Some
  term => let tail := visit rest in option_map ( fun ts => term :: ts ) tail end end in let args
  := visit children in option_map ( RWApp ty op ) args end.

Definition rw_plain_rw_rp_rule_body_gate_atomic { K Sort V H } ( sort : encoding Sort ) ( hole :
  encoding H ) ( callbacks : rw_plain_callbacks K Sort V H ) ( rule : rw_rule K Sort V H ) (
  attempt : rw_attempt K Sort V H ) : option ( rw_term K Sort V * rw_term K Sort V ) :=
let bindings := rw_attempt_sub attempt in let typed := rw_plain_rw_rp_sub_check_atomic sort hole
  callbacks rule ( rw_holes rule ) bindings in let guard := rw_plain_rw_rp_guard_atomic hole
  callbacks rule bindings in if typed && guard then let lhs := rw_plain_rw_rp_instantiate_atomic
  hole bindings ( rw_lhs rule ) in match lhs with | None => None | Some left_term => let rhs :=
  rw_plain_rw_rp_instantiate_atomic hole bindings ( rw_rhs rule ) in option_map ( fun right_term
  => ( left_term , right_term ) ) rhs end else None.

Definition rw_plain_rw_rp_rule_gate_prepared_atomic { K Sort V H } ( sort : encoding Sort ) (
  hole : encoding H ) ( callbacks : rw_plain_callbacks K Sort V H ) ( table : Map.t nat (
  rw_rule K Sort V H ) ) ( attempt : rw_attempt K Sort V H ) : option ( rw_term K Sort V *
  rw_term K Sort V ) :=
let found := rw_plain_audit_map_get rw_plain_audit_nat_encode ( rw_attempt_rule attempt ) table
  in match found with | None => None | Some rule => let out :=
  rw_plain_rw_rp_rule_body_gate_atomic sort hole callbacks rule attempt in out end.

Definition rw_plain_rw_ri_rule_step_prepared_atomic { K Sort V H } ( op : encoding K ) ( sort :
  encoding Sort ) ( value : encoding V ) ( hole : encoding H ) ( callbacks : rw_plain_callbacks
  K Sort V H ) ( table : Map.t nat ( rw_rule K Sort V H ) ) ( state : rw_index_state K Sort V )
  ( attempt : rw_attempt K Sort V H ) : option ( rw_index_state K Sort V ) :=
let gate := rw_plain_rw_rp_rule_gate_prepared_atomic sort hole callbacks table attempt in match
  gate with | None => None | Some ( lhs , rhs ) => let represented :=
  rw_plain_rw_ri_member_atomic op sort value state lhs ( rw_attempt_root attempt ) in if
  represented then let out := rw_plain_rw_ri_accept_atomic op sort value state attempt rhs in
  out else None end.

Fixpoint rw_plain_rw_rp_rule_table_atomic { K Sort V H } ( rules : list ( rw_rule K Sort V H ) )
  ( index : nat ) : Map.t nat ( rw_rule K Sort V H ) :=
match rules with | nil => Map.empty | rule :: rest => let table :=
  rw_plain_rw_rp_rule_table_atomic rest ( S index ) in let out := rw_plain_audit_map_set
  rw_plain_audit_nat_encode index rule table in out end.

Definition rw_plain_rw_ri_rule_step_atomic { K Sort V H } ( op : encoding K ) ( sort : encoding
  Sort ) ( value : encoding V ) ( hole : encoding H ) ( callbacks : rw_plain_callbacks K Sort V
  H ) ( rules : list ( rw_rule K Sort V H ) ) ( state : rw_index_state K Sort V ) ( attempt :
  rw_attempt K Sort V H ) : option ( rw_index_state K Sort V ) :=
let table := rw_plain_rw_rp_rule_table_atomic rules 0 in let out :=
  rw_plain_rw_ri_rule_step_prepared_atomic op sort value hole callbacks table state attempt in out.

Definition rw_plain_rw_ri_apply_prepared_atomic { K Sort V H } ( op : encoding K ) ( sort :
  encoding Sort ) ( value : encoding V ) ( hole : encoding H ) ( callbacks : rw_plain_callbacks
  K Sort V H ) ( table : Map.t nat ( rw_rule K Sort V H ) ) ( state : rw_index_state K Sort V )
  ( attempt : rw_attempt K Sort V H ) : option ( rw_index_state K Sort V * list rw_index_event ) :=
let applied := rw_plain_rw_ri_rule_step_prepared_atomic op sort value hole callbacks table state
  attempt in match applied with | None => None | Some next => let out :=
  rw_plain_rw_ri_rebuild_atomic op sort value next in Some out end.

Definition rw_plain_rw_ri_run_once { K Sort V H } ( op : encoding K ) ( sort : encoding Sort ) (
  value : encoding V ) ( hole : encoding H ) ( callbacks : rw_plain_callbacks K Sort V H ) (
  table : Map.t nat ( rw_rule K Sort V H ) ) ( strategy : rw_plain_strategy K Sort V H ) ( run :
  rw_ri_runner K Sort V H ) : rw_ri_runner K Sort V H :=
if rw_ri_runner_stopped run then run else let state := rw_ri_runner_state run in let offer :=
  rw_plain_rw_rp_strategy_run op value strategy state in match offer with | None => RwRiRunner
  state true ( rw_ri_runner_events run ) | Some attempt => let applied :=
  rw_plain_rw_ri_apply_prepared_atomic op sort value hole callbacks table state attempt in match
  applied with | None => RwRiRunner state false ( RWRunRejected attempt :: rw_ri_runner_events
  run ) | Some ( next , events ) => RwRiRunner next false ( RWRunAccepted attempt events ::
  rw_ri_runner_events run ) end end.

Fixpoint rw_plain_rw_ri_run_repeat { K Sort V H } ( op : encoding K ) ( sort : encoding Sort ) (
  value : encoding V ) ( hole : encoding H ) ( callbacks : rw_plain_callbacks K Sort V H ) (
  table : Map.t nat ( rw_rule K Sort V H ) ) ( strategy : rw_plain_strategy K Sort V H ) ( fuel
  : positive ) ( run : rw_ri_runner K Sort V H ) : rw_ri_runner K Sort V H :=
if rw_ri_runner_stopped run then run else match fuel with | xH => let out :=
  rw_plain_rw_ri_run_once op sort value hole callbacks table strategy run in out | xO rest =>
  let middle := rw_plain_rw_ri_run_repeat op sort value hole callbacks table strategy rest run
  in let out := rw_plain_rw_ri_run_repeat op sort value hole callbacks table strategy rest
  middle in out | xI rest => let first := rw_plain_rw_ri_run_once op sort value hole callbacks
  table strategy run in let middle := rw_plain_rw_ri_run_repeat op sort value hole callbacks
  table strategy rest first in let out := rw_plain_rw_ri_run_repeat op sort value hole callbacks
  table strategy rest middle in out end.

Definition rw_plain_rw_ri_run_atomic { K Sort V H } ( op : encoding K ) ( sort : encoding Sort )
  ( value : encoding V ) ( hole : encoding H ) ( callbacks : rw_plain_callbacks K Sort V H ) (
  rules : list ( rw_rule K Sort V H ) ) ( strategy : rw_plain_strategy K Sort V H ) ( fuel : N )
  ( graph : rw_graph K Sort V ) : ( rw_run_result K Sort V * list rw_index_event * list (
  rw_run_event K Sort V H ) ) :=
match fuel with | N0 => ( RwRunResult graph RWFuelExhausted , nil , nil ) | Npos fuel => let
  table := rw_plain_rw_rp_rule_table_atomic rules 0 in let prepared :=
  rw_plain_rw_ri_prepare_once op value graph in let '( ready , initial_events ) :=
  rw_plain_rw_ri_rebuild_atomic op sort value prepared in let final := rw_plain_rw_ri_run_repeat
  op sort value hole callbacks table strategy fuel ( RwRiRunner ready false nil ) in let
  result_graph := rw_plain_rw_ri_graph_atomic ( rw_ri_runner_state final ) in ( RwRunResult
  result_graph ( if rw_ri_runner_stopped final then RWStopped else RWFuelExhausted ) ,
  initial_events , rw_ri_runner_events final ) end.

Fixpoint rw_plain_rw_rp_append { A } ( xs ys : list A ) : list A :=
match xs with | nil => ys | x :: rest => let tail := rw_plain_rw_rp_append rest ys in x :: tail end.
```

## Galois.Rewrite.RewriteAuditPlainCore2

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditPlainCore2.v`.

```rocq
(** * RewriteAuditPlainCore2

    This module evaluates the fixed source phases without cost or receipt construction.
    For example, a lookup uses the actual plain map operation once.
    Builds on: the canonical Rewrite source equations and Collections. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditPlainCore1 RewriteAuditPlainPrimitives
  RewriteAuditProofCarrier RewriteAuditProofClosure RewriteAuditSharedReference.
Import List.ListNotations.
Local Coercion encode : encoding >-> Funclass.

Definition rw_plain_rw_shared_unfold_atomic := @rw_shared_unfold.


Arguments rw_plain_rw_shared_unfold_atomic {K Sort V} _.

Fixpoint rw_plain_rw_rp_term_tokens { K Sort V } ( op : encoding K ) ( sort : encoding Sort ) (
  value : encoding V ) ( term : rw_term K Sort V ) : list positive :=
match term with | RWVar ty v => let s := rw_plain_rw_queue_encoder_run sort ty in let x :=
  rw_plain_rw_queue_encoder_run value v in [ 1 % positive ; s ; x ; 1 % positive ] | RWApp ty k
  children => let s := rw_plain_rw_queue_encoder_run sort ty in let x :=
  rw_plain_rw_queue_encoder_run op k in let arity := rw_plain_rw_fuel_length children in let
  arity_code := rw_plain_audit_nat_encode arity in let fix visit ( ts : list ( rw_term K Sort V
  ) ) : list positive := match ts with | nil => nil | t :: rest => let head :=
  rw_plain_rw_rp_term_tokens op sort value t in let tail := visit rest in let out :=
  rw_plain_rw_rp_append head tail in out end in let tokens := visit children in 2 % positive ::
  s :: x :: arity_code :: tokens end.

Definition rw_plain_rw_rp_term_key { K Sort V } ( op : encoding K ) ( sort : encoding Sort ) (
  value : encoding V ) ( term : rw_term K Sort V ) : positive :=
let tokens := rw_plain_rw_rp_term_tokens op sort value term in let code :=
  rw_plain_audit_list_encode rw_plain_audit_positive_encode tokens in code.

Fixpoint rw_plain_rw_rp_fresh_loop ( ids : list positive ) ( largest : positive ) : positive :=
match ids with | nil => let fresh := rw_plain_rw_fuel_pos_succ largest in fresh | id :: rest =>
  let order := rw_plain_rw_rd_positive_compare_cont Eq id largest in let next := match order
  with | Gt => id | _ => largest end in let fresh := rw_plain_rw_rp_fresh_loop rest next in
  fresh end.

Definition rw_plain_rw_rp_proof_get ( lhs rhs : positive ) ( index : rw_rp_proof_index ) :
  option positive :=
let answer := rw_plain_audit_map_get rw_plain_rw_rd_pair_encode ( lhs , rhs ) index in answer.

Definition rw_plain_rw_rp_proof_put ( lhs rhs id : positive ) ( index : rw_rp_proof_index ) :
  rw_rp_proof_index :=
let answer := rw_plain_audit_map_set rw_plain_rw_rd_pair_encode ( lhs , rhs ) id index in answer.

Definition rw_plain_rw_rp_add_evidence { K Sort V H } ( op : encoding K ) ( sort : encoding Sort
  ) ( value : encoding V ) ( stamp : nat * nat ) ( lhs rhs : rw_term K Sort V ) ( reason :
  rw_evidence_reason K Sort V H ) ( state : rw_rp_connection_state K Sort V H ) : ( positive *
  rw_rp_connection_state K Sort V H ) :=
let proof := rw_rp_proof state in let id := rw_plain_rw_rp_fresh_loop ( rw_provenance_ids proof
  ) 1 % positive in let node := RWEvidenceNode lhs rhs reason stamp in let nodes :=
  rw_plain_audit_map_set rw_plain_audit_positive_encode id node ( rw_provenance_nodes proof ) in
  let lk := rw_plain_rw_rp_term_key op sort value lhs in let rk := rw_plain_rw_rp_term_key op
  sort value rhs in let index := rw_plain_rw_rp_proof_put lk rk id ( rw_rp_index state ) in ( id
  , RwRpConnectionState ( RWProvenance ( id :: rw_provenance_ids proof ) nodes ) index ).

Fixpoint rw_plain_rw_rp_index_existing { K Sort V H } ( op : encoding K ) ( sort : encoding Sort
  ) ( value : encoding V ) ( ids : list positive ) ( proof : rw_provenance K Sort V H ) ( index
  : rw_rp_proof_index ) : rw_rp_proof_index :=
match ids with | nil => index | id :: rest => let found := rw_plain_audit_map_get
  rw_plain_audit_positive_encode id ( rw_provenance_nodes proof ) in match found with | None =>
  let out := rw_plain_rw_rp_index_existing op sort value rest proof index in out | Some node =>
  let lk := rw_plain_rw_rp_term_key op sort value ( rw_evidence_left node ) in let rk :=
  rw_plain_rw_rp_term_key op sort value ( rw_evidence_right node ) in let next :=
  rw_plain_rw_rp_proof_put lk rk id index in let out := rw_plain_rw_rp_index_existing op sort
  value rest proof next in out end end.

Definition rw_plain_rw_rp_try_symmetry { K Sort V H } ( op : encoding K ) ( sort : encoding Sort
  ) ( value : encoding V ) ( stamp : nat * nat ) ( lhs rhs : rw_term K Sort V ) ( state :
  rw_rp_connection_state K Sort V H ) : ( option positive * rw_rp_connection_state K Sort V H ) :=
let lk := rw_plain_rw_rp_term_key op sort value lhs in let rk := rw_plain_rw_rp_term_key op sort
  value rhs in let reverse := rw_plain_rw_rp_proof_get rk lk ( rw_rp_index state ) in match
  reverse with | None => ( None , state ) | Some id => let '( new , next ) :=
  rw_plain_rw_rp_add_evidence op sort value stamp lhs rhs ( RWEvidenceSym id ) state in ( Some
  new , next ) end.

Fixpoint rw_plain_rw_rp_try_transitivity { K Sort V H } ( op : encoding K ) ( sort : encoding
  Sort ) ( value : encoding V ) ( stamp : nat * nat ) ( lhs rhs : rw_term K Sort V ) ( middles :
  list ( rw_term K Sort V ) ) ( state : rw_rp_connection_state K Sort V H ) : ( option positive
  * rw_rp_connection_state K Sort V H ) :=
match middles with | nil => ( None , state ) | middle :: rest => let lk :=
  rw_plain_rw_rp_term_key op sort value lhs in let mk := rw_plain_rw_rp_term_key op sort value
  middle in let rk := rw_plain_rw_rp_term_key op sort value rhs in let first :=
  rw_plain_rw_rp_proof_get lk mk ( rw_rp_index state ) in match first with | None => let answer
  := rw_plain_rw_rp_try_transitivity op sort value stamp lhs rhs rest state in answer | Some a
  => let second := rw_plain_rw_rp_proof_get mk rk ( rw_rp_index state ) in match second with |
  None => let answer := rw_plain_rw_rp_try_transitivity op sort value stamp lhs rhs rest state
  in answer | Some b => let '( id , next ) := rw_plain_rw_rp_add_evidence op sort value stamp
  lhs rhs ( RWEvidenceTrans a b ) state in ( Some id , next ) end end end.

Fixpoint rw_plain_rw_rp_children_evidence { K Sort V H } ( op : encoding K ) ( sort : encoding
  Sort ) ( value : encoding V ) ( lhs rhs : list ( rw_term K Sort V ) ) ( state :
  rw_rp_connection_state K Sort V H ) : option ( list positive ) :=
match lhs , rhs with | nil , nil => Some nil | a :: xs , b :: ys => let lk :=
  rw_plain_rw_rp_term_key op sort value a in let rk := rw_plain_rw_rp_term_key op sort value b
  in let found := rw_plain_rw_rp_proof_get lk rk ( rw_rp_index state ) in match found with |
  None => None | Some id => let tail := rw_plain_rw_rp_children_evidence op sort value xs ys
  state in option_map ( fun ids => id :: ids ) tail end | _ , _ => None end.

Definition rw_plain_rw_rp_try_congruence { K Sort V H } ( op : encoding K ) ( sort : encoding
  Sort ) ( value : encoding V ) ( stamp : nat * nat ) ( lhs rhs : rw_term K Sort V ) ( state :
  rw_rp_connection_state K Sort V H ) : ( option positive * rw_rp_connection_state K Sort V H ) :=
match lhs , rhs with | RWApp s k xs , RWApp t l ys => let sc := rw_plain_rw_queue_encoder_run
  sort s in let tc := rw_plain_rw_queue_encoder_run sort t in let same_sort :=
  rw_plain_audit_positive_eqb sc tc in if same_sort then let kc := rw_plain_rw_queue_encoder_run
  op k in let lc := rw_plain_rw_queue_encoder_run op l in let same_op :=
  rw_plain_audit_positive_eqb kc lc in if same_op then let children :=
  rw_plain_rw_rp_children_evidence op sort value xs ys state in match children with | None => (
  None , state ) | Some ids => let '( id , next ) := rw_plain_rw_rp_add_evidence op sort value
  stamp lhs rhs ( RWEvidenceCongruence ids ) state in ( Some id , next ) end else ( None , state
  ) else ( None , state ) | _ , _ => ( None , state ) end.

Definition rw_plain_rw_rp_close_pair { K Sort V H } ( op : encoding K ) ( sort : encoding Sort )
  ( value : encoding V ) ( stamp : nat * nat ) ( terms : list ( rw_term K Sort V ) ) ( lhs rhs :
  rw_term K Sort V ) ( state : rw_rp_connection_state K Sort V H ) : rw_rp_connection_state K
  Sort V H :=
let lk := rw_plain_rw_rp_term_key op sort value lhs in let rk := rw_plain_rw_rp_term_key op sort
  value rhs in let present := rw_plain_rw_rp_proof_get lk rk ( rw_rp_index state ) in match
  present with | Some _ => state | None => let same := rw_plain_audit_positive_eqb lk rk in if
  same then let '( _ , next ) := rw_plain_rw_rp_add_evidence op sort value stamp lhs rhs
  RWEvidenceRefl state in next else let '( symmetric , first ) := rw_plain_rw_rp_try_symmetry op
  sort value stamp lhs rhs state in match symmetric with | Some _ => first | None => let '(
  transitive , second ) := rw_plain_rw_rp_try_transitivity op sort value stamp lhs rhs terms
  first in match transitive with | Some _ => second | None => let '( _ , final ) :=
  rw_plain_rw_rp_try_congruence op sort value stamp lhs rhs second in final end end end.

Fixpoint rw_plain_rw_rp_close_row { K Sort V H } ( op : encoding K ) ( sort : encoding Sort ) (
  value : encoding V ) ( stamp : nat * nat ) ( terms : list ( rw_term K Sort V ) ) ( lhs :
  rw_term K Sort V ) ( rights : list ( rw_term K Sort V ) ) ( state : rw_rp_connection_state K
  Sort V H ) : rw_rp_connection_state K Sort V H :=
match rights with | nil => state | rhs :: rest => let next := rw_plain_rw_rp_close_pair op sort
  value stamp terms lhs rhs state in let out := rw_plain_rw_rp_close_row op sort value stamp
  terms lhs rest next in out end.

Fixpoint rw_plain_rw_rp_close_pass { K Sort V H } ( op : encoding K ) ( sort : encoding Sort ) (
  value : encoding V ) ( stamp : nat * nat ) ( terms lefts : list ( rw_term K Sort V ) ) ( state
  : rw_rp_connection_state K Sort V H ) : rw_rp_connection_state K Sort V H :=
match lefts with | nil => state | lhs :: rest => let next := rw_plain_rw_rp_close_row op sort
  value stamp terms lhs terms state in let out := rw_plain_rw_rp_close_pass op sort value stamp
  terms rest next in out end.

Fixpoint rw_plain_rw_rp_close_rounds { K Sort V H } ( op : encoding K ) ( sort : encoding Sort )
  ( value : encoding V ) ( stamp : nat * nat ) ( terms : list ( rw_term K Sort V ) ) ( fuel :
  positive ) ( state : rw_rp_connection_state K Sort V H ) : rw_rp_connection_state K Sort V H :=
match fuel with | xH => let out := rw_plain_rw_rp_close_pass op sort value stamp terms terms
  state in out | xO rest => let middle := rw_plain_rw_rp_close_rounds op sort value stamp terms
  rest state in let out := rw_plain_rw_rp_close_rounds op sort value stamp terms rest middle in
  out | xI rest => let first := rw_plain_rw_rp_close_pass op sort value stamp terms terms state
  in let middle := rw_plain_rw_rp_close_rounds op sort value stamp terms rest first in let out
  := rw_plain_rw_rp_close_rounds op sort value stamp terms rest middle in out end.

Fixpoint rw_plain_rw_rp_subterms { K Sort V } ( term : rw_term K Sort V ) : list ( rw_term K
  Sort V ) :=
match term with | RWVar _ _ => [ term ] | RWApp _ _ children => let fix visit ( ts : list (
  rw_term K Sort V ) ) : list ( rw_term K Sort V ) := match ts with | nil => nil | t :: rest =>
  let head := rw_plain_rw_rp_subterms t in let tail := visit rest in let out :=
  rw_plain_rw_rp_append head tail in out end in let others := visit children in term :: others end.

Fixpoint rw_plain_rw_rp_nat_compare ( a b : nat ) : comparison :=
match a , b with | 0 , 0 => Eq | 0 , S _ => Lt | S _ , 0 => Gt | S x , S y => let answer :=
  rw_plain_rw_rp_nat_compare x y in answer end.

Fixpoint rw_plain_rw_rp_evidence_terms { K Sort V H } ( entries : list ( positive *
  rw_evidence_node K Sort V H ) ) ( largest_group : nat ) : ( list ( rw_term K Sort V ) * nat ) :=
match entries with | nil => ( nil , largest_group ) | ( _ , node ) :: rest => let group := fst (
  rw_evidence_time node ) in let order := rw_plain_rw_rp_nat_compare group largest_group in let
  next := match order with | Gt => group | _ => largest_group end in let lhs :=
  rw_plain_rw_rp_subterms ( rw_evidence_left node ) in let rhs := rw_plain_rw_rp_subterms (
  rw_evidence_right node ) in let '( tail , maximum ) := rw_plain_rw_rp_evidence_terms rest next
  in let both := rw_plain_rw_rp_append lhs rhs in let out := rw_plain_rw_rp_append both tail in
  ( out , maximum ) end.

Definition rw_plain_rw_rp_connect_atomic { K Sort V H } ( op : encoding K ) ( sort : encoding
  Sort ) ( value : encoding V ) ( proof : rw_provenance K Sort V H ) ( lhs rhs : rw_term K Sort
  V ) : option ( rw_provenance K Sort V H * positive ) :=
let entries := rw_plain_audit_map_elements ( rw_provenance_nodes proof ) in let '( known ,
  largest ) := rw_plain_rw_rp_evidence_terms entries 0 in let lefts := rw_plain_rw_rp_subterms
  lhs in let rights := rw_plain_rw_rp_subterms rhs in let both := rw_plain_rw_rp_append lefts
  rights in let terms := rw_plain_rw_rp_append both known in let index :=
  rw_plain_rw_rp_index_existing op sort value ( rw_provenance_ids proof ) proof Map.empty in let
  count := rw_plain_rw_fuel_length terms in let square := rw_plain_rw_fuel_mul count count in
  let fuel := rw_plain_rw_fuel_to_positive square in let final := rw_plain_rw_rp_close_rounds op
  sort value ( S largest , 0 ) terms fuel ( RwRpConnectionState proof index ) in let lk :=
  rw_plain_rw_rp_term_key op sort value lhs in let rk := rw_plain_rw_rp_term_key op sort value
  rhs in let answer := rw_plain_rw_rp_proof_get lk rk ( rw_rp_index final ) in option_map ( fun
  id => ( rw_rp_proof final , id ) ) answer.

Definition rw_plain_rw_rp_stamp_put ( stamp : nat * nat ) ( id : positive ) ( table : Map.t (
  nat * nat ) positive ) : Map.t ( nat * nat ) positive :=
let out := rw_plain_audit_map_set rw_plain_rw_rp_stamp_encode stamp id table in out.
```

## Galois.Rewrite.RewriteAuditPlainCore3

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditPlainCore3.v`.

```rocq
(** * RewriteAuditPlainCore3

    This module evaluates the fixed source phases without cost or receipt construction.
    For example, a lookup uses the actual plain map operation once.
    Builds on: the canonical Rewrite source equations and Collections. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexReference RewriteAuditPlainCore1
  RewriteAuditPlainCore2 RewriteAuditPlainPrimitives RewriteAuditProofCarrier
  RewriteAuditProofClosure RewriteAuditProofRun RewriteAuditProofSeed RewriteAuditProofTick
  RewriteAuditQueueReference RewriteAuditSharedReference.
Import List.ListNotations.
Local Coercion encode : encoding >-> Funclass.

Definition rw_plain_rw_rp_witness_merge { K Sort V } ( a b root pointer : positive ) ( store :
  rw_class_witness_store K Sort V ) : rw_class_witness_store K Sort V :=
let first := rw_plain_audit_map_remove rw_plain_audit_positive_encode a ( rw_class_witness_roots
  store ) in let second := rw_plain_audit_map_remove rw_plain_audit_positive_encode b first in
  let roots := rw_plain_audit_map_set rw_plain_audit_positive_encode root pointer second in
  RWClassWitnessStore ( rw_class_witness_nodes store ) roots.

Definition rw_plain_rw_rp_witness_read { K Sort V } ( id : rw_id ) ( store :
  rw_class_witness_store K Sort V ) : option ( positive * rw_term K Sort V ) :=
let pointer := rw_plain_audit_map_get rw_plain_audit_positive_encode id ( rw_class_witness_roots
  store ) in match pointer with | None => None | Some p => let tree :=
  rw_plain_rw_shared_unfold_atomic ( RwSharedTree K Sort V p ( rw_class_witness_nodes store ) )
  in option_map ( fun t => ( p , t ) ) tree end.

Definition rw_plain_rw_rp_connect_at_atomic { K Sort V H } ( op : encoding K ) ( sort : encoding
  Sort ) ( value : encoding V ) ( stamp : nat * nat ) ( proof : rw_provenance K Sort V H ) ( lhs
  rhs : rw_term K Sort V ) : option ( rw_provenance K Sort V H * positive ) :=
let entries := rw_plain_audit_map_elements ( rw_provenance_nodes proof ) in let '( known ,
  largest ) := rw_plain_rw_rp_evidence_terms entries 0 in let lefts := rw_plain_rw_rp_subterms
  lhs in let rights := rw_plain_rw_rp_subterms rhs in let both := rw_plain_rw_rp_append lefts
  rights in let terms := rw_plain_rw_rp_append both known in let index :=
  rw_plain_rw_rp_index_existing op sort value ( rw_provenance_ids proof ) proof Map.empty in let
  count := rw_plain_rw_fuel_length terms in let square := rw_plain_rw_fuel_mul count count in
  let fuel := rw_plain_rw_fuel_to_positive square in let final := rw_plain_rw_rp_close_rounds op
  sort value stamp terms fuel ( RwRpConnectionState proof index ) in let lk :=
  rw_plain_rw_rp_term_key op sort value lhs in let rk := rw_plain_rw_rp_term_key op sort value
  rhs in let answer := rw_plain_rw_rp_proof_get lk rk ( rw_rp_index final ) in option_map ( fun
  id => ( rw_rp_proof final , id ) ) answer.

Definition rw_plain_rw_rp_record_connection { K Sort V H } ( op : encoding K ) ( sort : encoding
  Sort ) ( value : encoding V ) ( stamp : nat * nat ) ( lhs rhs : rw_term K Sort V ) ( proof :
  rw_provenance K Sort V H ) : option ( rw_provenance K Sort V H * positive ) :=
let connection := rw_plain_rw_rp_connect_at_atomic op sort value stamp proof lhs rhs in match
  connection with | None => None | Some ( extended , id ) => let index :=
  rw_plain_rw_rp_index_existing op sort value ( rw_provenance_ids extended ) extended Map.empty
  in let state := RwRpConnectionState extended index in let '( refl , with_refl ) :=
  rw_plain_rw_rp_add_evidence op sort value stamp rhs rhs RWEvidenceRefl state in let '(
  event_id , final ) := rw_plain_rw_rp_add_evidence op sort value stamp lhs rhs (
  RWEvidenceTrans id refl ) with_refl in Some ( rw_rp_proof final , event_id ) end.

Definition rw_plain_rw_rp_tick_atomic { K Sort V H } ( op : encoding K ) ( sort : encoding Sort
  ) ( value : encoding V ) ( stamp : nat * nat ) ( state : rw_tracked_state K Sort V H ) :
  option ( rw_tracked_state K Sort V H * rw_index_event ) :=
let stepped := rw_plain_rw_ri_tick_atomic op sort value ( rw_tracked_machine state ) in match
  stepped with | None => None | Some ( next , event ) => match event with | RWIndexCongruence
  pair_value a b root => let store := rw_tracked_witnesses state in let lhs :=
  rw_plain_rw_rp_witness_read a store in match lhs with | None => None | Some ( left_pointer ,
  left_term ) => let rhs := rw_plain_rw_rp_witness_read b store in match rhs with | None => None
  | Some ( _ , right_term ) => let recorded := rw_plain_rw_rp_record_connection op sort value
  stamp left_term right_term ( rw_tracked_provenance state ) in match recorded with | None =>
  None | Some ( proof , id ) => let witnesses := rw_plain_rw_rp_witness_merge a b root
  left_pointer store in let events := rw_plain_rw_rp_stamp_put stamp id ( rw_tracked_event_nodes
  state ) in Some ( RWTrackedState next proof witnesses events , event ) end end end | _ => Some
  ( RWTrackedState next ( rw_tracked_provenance state ) ( rw_tracked_witnesses state ) (
  rw_tracked_event_nodes state ) , event ) end end.

Definition rw_plain_rw_rp_seed_node { K Sort V } ( node : rw_node K Sort V ) ( shared :
  rw_shared_node K Sort V ) ( acc : rw_rp_seed_acc K Sort V ) : ( ( rw_id * positive ) *
  rw_rp_seed_acc K Sort V ) :=
let id := rw_rp_seed_next acc in let pointer := rw_rp_seed_witness_next acc in let graph :=
  rw_rp_seed_graph acc in let store := rw_rp_seed_witnesses acc in let aliases :=
  rw_plain_audit_map_set rw_plain_audit_positive_encode id id ( rw_class_roots graph ) in let
  sorts := rw_plain_audit_map_set rw_plain_audit_positive_encode id ( rw_node_sort node ) (
  rw_sorts graph ) in let nodes := rw_plain_audit_map_set rw_plain_audit_positive_encode id ( id
  , node ) ( rw_nodes graph ) in let shared_nodes := rw_plain_audit_map_set
  rw_plain_audit_positive_encode pointer shared ( rw_class_witness_nodes store ) in let
  witness_roots := rw_plain_audit_map_set rw_plain_audit_positive_encode id pointer (
  rw_class_witness_roots store ) in let fresh := rw_plain_rw_fuel_pos_succ id in let
  witness_fresh := rw_plain_rw_fuel_pos_succ pointer in ( ( id , pointer ) , RwRpSeedAcc (
  RwGraph ( id :: rw_roots graph ) ( id :: rw_nodes_in graph ) aliases sorts nodes ) (
  RWClassWitnessStore shared_nodes witness_roots ) fresh witness_fresh ).

Fixpoint rw_plain_rw_rp_seed_term { K Sort V } ( term : rw_term K Sort V ) ( acc :
  rw_rp_seed_acc K Sort V ) : ( ( rw_id * positive ) * rw_rp_seed_acc K Sort V ) :=
match term with | RWVar ty v => let out := rw_plain_rw_rp_seed_node ( RWNVar ty v ) (
  RWSharedVar K Sort V ty v ) acc in out | RWApp ty op children => let fix visit ( ts : list (
  rw_term K Sort V ) ) ( state : rw_rp_seed_acc K Sort V ) : ( list rw_id * list positive *
  rw_rp_seed_acc K Sort V ) := match ts with | nil => ( nil , nil , state ) | t :: rest => let
  '( ( head , pointer ) , next ) := rw_plain_rw_rp_seed_term t state in let '( tail , pointers ,
  final ) := visit rest next in ( head :: tail , pointer :: pointers , final ) end in let '( ids
  , pointers , next ) := visit children acc in let out := rw_plain_rw_rp_seed_node ( RWNApp ty
  op ids ) ( RWSharedApp K Sort V ty op pointers ) next in out end.

Definition rw_plain_rw_rp_seed_atomic { K Sort V H } ( EK : encoding K ) ( ES : encoding Sort )
  ( EV : encoding V ) ( op : encoding K ) ( value : encoding V ) ( term : rw_term K Sort V ) : (
  rw_id * rw_tracked_state K Sort V H ) :=
let '( ( root , _ ) , acc ) := rw_plain_rw_rp_seed_term term rw_rp_seed_empty in let machine :=
  rw_plain_rw_ri_prepare_once op value ( rw_rp_seed_graph acc ) in ( root , RWTrackedState
  machine ( RWProvenance nil Map.empty ) ( rw_rp_seed_witnesses acc ) Map.empty ).

Definition rw_plain_rw_rp_rebuild_done { K Sort V H } ( state : rw_tracked_state K Sort V H *
  nat * list rw_index_event ) : bool :=
let ' ( tracked , _ , _ ) := state in match rw_index_dirty_order ( rw_tracked_machine tracked )
  , rw_pending_sequence ( rw_index_pending ( rw_tracked_machine tracked ) ) with | nil , nil =>
  true | _ , _ => false end.

Definition rw_plain_rw_rp_rebuild_once { K Sort V H } ( op : encoding K ) ( sort : encoding Sort
  ) ( value : encoding V ) ( group : nat ) ( state : rw_tracked_state K Sort V H * nat * list
  rw_index_event ) : ( rw_tracked_state K Sort V H * nat * list rw_index_event ) :=
let ' ( tracked , position , events ) := state in let next := rw_plain_rw_rp_tick_atomic op sort
  value ( group , S position ) tracked in match next with | None => state | Some ( final , event
  ) => ( final , S position , event :: events ) end.

Fixpoint rw_plain_rw_rp_rebuild_repeat { K Sort V H } ( op : encoding K ) ( sort : encoding Sort
  ) ( value : encoding V ) ( group : nat ) ( fuel : positive ) ( state : rw_tracked_state K Sort
  V H * nat * list rw_index_event ) : ( rw_tracked_state K Sort V H * nat * list rw_index_event ) :=
if rw_plain_rw_rp_rebuild_done state then state else match fuel with | xH => let out :=
  rw_plain_rw_rp_rebuild_once op sort value group state in out | xO rest => let middle :=
  rw_plain_rw_rp_rebuild_repeat op sort value group rest state in let out :=
  rw_plain_rw_rp_rebuild_repeat op sort value group rest middle in out | xI rest => let first :=
  rw_plain_rw_rp_rebuild_once op sort value group state in let middle :=
  rw_plain_rw_rp_rebuild_repeat op sort value group rest first in let out :=
  rw_plain_rw_rp_rebuild_repeat op sort value group rest middle in out end.

Fixpoint rw_plain_rw_ri_reverse_onto { A } ( xs acc : list A ) : list A :=
match xs with | nil => acc | x :: rest => let out := rw_plain_rw_ri_reverse_onto rest ( x :: acc
  ) in out end.

Definition rw_plain_rw_rp_rebuild_atomic { K Sort V H } ( op : encoding K ) ( sort : encoding
  Sort ) ( value : encoding V ) ( group : nat ) ( state : rw_tracked_state K Sort V H ) : (
  rw_tracked_state K Sort V H * list rw_index_event ) :=
let fuel := rw_plain_rw_ri_rebuild_fuel_atomic ( rw_tracked_machine state ) in let '( final , _
  , reversed ) := rw_plain_rw_rp_rebuild_repeat op sort value group fuel ( state , 0 , nil ) in
  let events := rw_plain_rw_ri_reverse_onto reversed nil in ( final , events ).

Definition rw_plain_rw_rp_rule_gate_atomic { K Sort V H } ( sort : encoding Sort ) ( hole :
  encoding H ) ( callbacks : rw_plain_callbacks K Sort V H ) ( rules : list ( rw_rule K Sort V H
  ) ) ( attempt : rw_attempt K Sort V H ) : option ( rw_term K Sort V * rw_term K Sort V ) :=
let table := rw_plain_rw_rp_rule_table_atomic rules 0 in let out :=
  rw_plain_rw_rp_rule_gate_prepared_atomic sort hole callbacks table attempt in out.

Definition rw_plain_rw_rp_accept_atomic { K Sort V H } ( EK : encoding K ) ( ES : encoding Sort
  ) ( EV : encoding V ) ( op : encoding K ) ( sort : encoding Sort ) ( value : encoding V ) (
  stamp : nat * nat ) ( state : rw_tracked_state K Sort V H ) ( attempt : rw_attempt K Sort V H
  ) ( lhs rhs : rw_term K Sort V ) : option ( rw_tracked_state K Sort V H ) :=
let graph := rw_plain_rw_ri_graph_atomic ( rw_tracked_machine state ) in let witness_entries :=
  rw_plain_audit_map_elements ( rw_class_witness_nodes ( rw_tracked_witnesses state ) ) in let
  largest := @ rw_plain_rw_ri_max_entries_atomic ( rw_shared_node K Sort V ) K Sort V
  witness_entries ( rw_index_fresh ( rw_tracked_machine state ) ) in let fresh :=
  rw_plain_rw_fuel_pos_succ largest in let acc := RwRpSeedAcc graph ( rw_tracked_witnesses state
  ) ( rw_index_fresh ( rw_tracked_machine state ) ) fresh in let '( ( rhs_root , _ ) , grown )
  := rw_plain_rw_rp_seed_term rhs acc in let prepared := rw_plain_rw_ri_prepare_once op value (
  rw_rp_seed_graph grown ) in let first := rw_plain_rw_ri_find_atomic prepared ( rw_attempt_root
  attempt ) in match first with | None => None | Some a => let second :=
  rw_plain_rw_ri_find_atomic prepared rhs_root in match second with | None => None | Some b =>
  let left_sort := rw_plain_audit_map_get rw_plain_audit_positive_encode a ( rw_sorts (
  rw_index_base prepared ) ) in match left_sort with | None => None | Some sa => let right_sort
  := rw_plain_audit_map_get rw_plain_audit_positive_encode b ( rw_sorts ( rw_index_base prepared
  ) ) in match right_sort with | None => None | Some sb => let same_sort :=
  rw_plain_rw_ri_encoded_equal sort sa sb in if same_sort then let old_witnesses :=
  rw_rp_seed_witnesses grown in let pointer := rw_plain_audit_map_get
  rw_plain_audit_positive_encode a ( rw_class_witness_roots old_witnesses ) in match pointer
  with | None => None | Some p => let '( machine , merge_event ) :=
  rw_plain_rw_ri_pair_merge_atomic prepared prepared ( a , b ) ( rw_index_pending prepared ) a b
  nil in let root := match merge_event with | RWIndexCongruence _ _ _ r => r | _ => a end in let
  witnesses := rw_plain_rw_rp_witness_merge a b root p old_witnesses in let proof :=
  rw_tracked_provenance state in let index := rw_plain_rw_rp_index_existing op sort value (
  rw_provenance_ids proof ) proof Map.empty in let '( id , extended ) :=
  rw_plain_rw_rp_add_evidence op sort value stamp lhs rhs ( RWEvidenceRule ( rw_attempt_rule
  attempt ) ( rw_attempt_sub attempt ) ) ( RwRpConnectionState proof index ) in let events :=
  rw_plain_rw_rp_stamp_put stamp id ( rw_tracked_event_nodes state ) in Some ( RWTrackedState
  machine ( rw_rp_proof extended ) witnesses events ) end else None end end end end.

Definition rw_plain_rw_rp_rule_step_prepared_atomic { K Sort V H } ( EK : encoding K ) ( ES :
  encoding Sort ) ( EV : encoding V ) ( op : encoding K ) ( sort : encoding Sort ) ( value :
  encoding V ) ( hole : encoding H ) ( callbacks : rw_plain_callbacks K Sort V H ) ( table :
  Map.t nat ( rw_rule K Sort V H ) ) ( position : nat ) ( state : rw_tracked_state K Sort V H )
  ( attempt : rw_attempt K Sort V H ) : option ( rw_tracked_state K Sort V H ) :=
let gate := rw_plain_rw_rp_rule_gate_prepared_atomic sort hole callbacks table attempt in match
  gate with | None => None | Some ( lhs , rhs ) => let represented :=
  rw_plain_rw_ri_member_atomic op sort value ( rw_tracked_machine state ) lhs ( rw_attempt_root
  attempt ) in if represented then let accepted := rw_plain_rw_rp_accept_atomic EK ES EV op sort
  value ( S position , 0 ) state attempt lhs rhs in accepted else None end.

Definition rw_plain_rw_rp_rule_step_atomic { K Sort V H } ( EK : encoding K ) ( ES : encoding
  Sort ) ( EV : encoding V ) ( op : encoding K ) ( sort : encoding Sort ) ( value : encoding V )
  ( hole : encoding H ) ( callbacks : rw_plain_callbacks K Sort V H ) ( rules : list ( rw_rule K
  Sort V H ) ) ( position : nat ) ( state : rw_tracked_state K Sort V H ) ( attempt : rw_attempt
  K Sort V H ) : option ( rw_tracked_state K Sort V H ) :=
let table := rw_plain_rw_rp_rule_table_atomic rules 0 in let out :=
  rw_plain_rw_rp_rule_step_prepared_atomic EK ES EV op sort value hole callbacks table position
  state attempt in out.

Definition rw_plain_rw_rp_apply_prepared_atomic { K Sort V H } ( EK : encoding K ) ( ES :
  encoding Sort ) ( EV : encoding V ) ( op : encoding K ) ( sort : encoding Sort ) ( value :
  encoding V ) ( hole : encoding H ) ( callbacks : rw_plain_callbacks K Sort V H ) ( table :
  Map.t nat ( rw_rule K Sort V H ) ) ( position : nat ) ( state : rw_tracked_state K Sort V H )
  ( attempt : rw_attempt K Sort V H ) : option ( rw_tracked_state K Sort V H * list
  rw_index_event ) :=
let stepped := rw_plain_rw_rp_rule_step_prepared_atomic EK ES EV op sort value hole callbacks
  table position state attempt in match stepped with | None => None | Some next => let out :=
  rw_plain_rw_rp_rebuild_atomic op sort value ( S position ) next in Some out end.

Definition rw_plain_rw_rp_apply_atomic { K Sort V H } ( EK : encoding K ) ( ES : encoding Sort )
  ( EV : encoding V ) ( op : encoding K ) ( sort : encoding Sort ) ( value : encoding V ) ( hole
  : encoding H ) ( callbacks : rw_plain_callbacks K Sort V H ) ( rules : list ( rw_rule K Sort V
  H ) ) ( position : nat ) ( state : rw_tracked_state K Sort V H ) ( attempt : rw_attempt K Sort
  V H ) : option ( rw_tracked_state K Sort V H * list rw_index_event ) :=
let table := rw_plain_rw_rp_rule_table_atomic rules 0 in let out :=
  rw_plain_rw_rp_apply_prepared_atomic EK ES EV op sort value hole callbacks table position
  state attempt in out.

Definition rw_plain_rw_rp_run_once { K Sort V H } ( EK : encoding K ) ( ES : encoding Sort ) (
  EV : encoding V ) ( op : encoding K ) ( sort : encoding Sort ) ( value : encoding V ) ( hole :
  encoding H ) ( callbacks : rw_plain_callbacks K Sort V H ) ( table : Map.t nat ( rw_rule K
  Sort V H ) ) ( strategy : rw_plain_strategy K Sort V H ) ( state : rw_rp_run_state K Sort V H
  ) : rw_rp_run_state K Sort V H :=
if rw_rp_stopped state then state else let tracked := rw_rp_current state in let offer :=
  rw_plain_rw_rp_strategy_run op value strategy ( rw_tracked_machine tracked ) in match offer
  with | None => RwRpRunState tracked true ( rw_rp_position state ) ( rw_rp_events state ) |
  Some attempt => let applied := rw_plain_rw_rp_apply_prepared_atomic EK ES EV op sort value
  hole callbacks table ( rw_rp_position state ) tracked attempt in match applied with | None =>
  RwRpRunState tracked false ( S ( rw_rp_position state ) ) ( RWRunRejected attempt ::
  rw_rp_events state ) | Some ( next , events ) => RwRpRunState next false ( S ( rw_rp_position
  state ) ) ( RWRunAccepted attempt events :: rw_rp_events state ) end end.
```

## Galois.Rewrite.RewriteAuditPlainCore4

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditPlainCore4.v`.

```rocq
(** * RewriteAuditPlainCore4

    This module evaluates the fixed source phases without cost or receipt construction.
    For example, a lookup uses the actual plain map operation once.
    Builds on: the canonical Rewrite source equations and Collections. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexReference RewriteAuditPlainCore1
  RewriteAuditPlainCore2 RewriteAuditPlainCore3 RewriteAuditPlainPrimitives
  RewriteAuditProofCarrier RewriteAuditProofRepresentation RewriteAuditProofRun
  RewriteAuditProofTick.
Import List.ListNotations.
Local Coercion encode : encoding >-> Funclass.

Fixpoint rw_plain_rw_rp_run_repeat { K Sort V H } ( EK : encoding K ) ( ES : encoding Sort ) (
  EV : encoding V ) ( op : encoding K ) ( sort : encoding Sort ) ( value : encoding V ) ( hole :
  encoding H ) ( callbacks : rw_plain_callbacks K Sort V H ) ( table : Map.t nat ( rw_rule K
  Sort V H ) ) ( strategy : rw_plain_strategy K Sort V H ) ( fuel : positive ) ( state :
  rw_rp_run_state K Sort V H ) : rw_rp_run_state K Sort V H :=
if rw_rp_stopped state then state else match fuel with | xH => let out :=
  rw_plain_rw_rp_run_once EK ES EV op sort value hole callbacks table strategy state in out | xO
  rest => let middle := rw_plain_rw_rp_run_repeat EK ES EV op sort value hole callbacks table
  strategy rest state in let out := rw_plain_rw_rp_run_repeat EK ES EV op sort value hole
  callbacks table strategy rest middle in out | xI rest => let first := rw_plain_rw_rp_run_once
  EK ES EV op sort value hole callbacks table strategy state in let middle :=
  rw_plain_rw_rp_run_repeat EK ES EV op sort value hole callbacks table strategy rest first in
  let out := rw_plain_rw_rp_run_repeat EK ES EV op sort value hole callbacks table strategy rest
  middle in out end.

Definition rw_plain_rw_rp_run_atomic { K Sort V H } ( EK : encoding K ) ( ES : encoding Sort ) (
  EV : encoding V ) ( op : encoding K ) ( sort : encoding Sort ) ( value : encoding V ) ( hole :
  encoding H ) ( callbacks : rw_plain_callbacks K Sort V H ) ( rules : list ( rw_rule K Sort V H
  ) ) ( strategy : rw_plain_strategy K Sort V H ) ( fuel : N ) ( seed : rw_term K Sort V ) : (
  rw_id * rw_tracked_output K Sort V H ) :=
let '( root , initial ) := rw_plain_rw_rp_seed_atomic EK ES EV op value seed in match fuel with
  | N0 => ( root , RwTrackedOutput initial RWFuelExhausted nil nil ) | Npos p => let table :=
  rw_plain_rw_rp_rule_table_atomic rules 0 in let '( ready , initial_events ) :=
  rw_plain_rw_rp_rebuild_atomic op sort value 0 initial in let final :=
  rw_plain_rw_rp_run_repeat EK ES EV op sort value hole callbacks table strategy p (
  RwRpRunState ready false 0 nil ) in ( root , RwTrackedOutput ( rw_rp_current final ) ( if
  rw_rp_stopped final then RWStopped else RWFuelExhausted ) initial_events ( rw_rp_events final
  ) ) end.

Definition rw_plain_rw_rp_fact_run_once { K Sort V H F } ( EK : encoding K ) ( ES : encoding
  Sort ) ( EV : encoding V ) ( op : encoding K ) ( sort : encoding Sort ) ( value : encoding V )
  ( hole : encoding H ) ( callbacks : rw_plain_callbacks K Sort V H ) ( table : Map.t nat (
  rw_rule K Sort V H ) ) ( unknown : F ) ( strategy : rw_plain_fact_strategy K Sort V H F ) (
  state : rw_rp_run_state K Sort V H * Map.t rw_id F ) : ( rw_rp_run_state K Sort V H * Map.t
  rw_id F ) :=
let ' ( run , facts ) := state in if rw_rp_stopped run then state else let tracked :=
  rw_rp_current run in let offer := rw_plain_rw_rp_fact_strategy_run op value strategy (
  rw_tracked_machine tracked ) unknown facts in match offer with | None => ( RwRpRunState
  tracked true ( rw_rp_position run ) ( rw_rp_events run ) , facts ) | Some attempt => let
  applied := rw_plain_rw_rp_apply_prepared_atomic EK ES EV op sort value hole callbacks table (
  rw_rp_position run ) tracked attempt in match applied with | None => ( RwRpRunState tracked
  false ( S ( rw_rp_position run ) ) ( RWRunRejected attempt :: rw_rp_events run ) , facts ) |
  Some ( next , events ) => ( RwRpRunState next false ( S ( rw_rp_position run ) ) (
  RWRunAccepted attempt events :: rw_rp_events run ) , Map.empty ) end end.

Fixpoint rw_plain_rw_rp_fact_run_repeat { K Sort V H F } ( EK : encoding K ) ( ES : encoding
  Sort ) ( EV : encoding V ) ( op : encoding K ) ( sort : encoding Sort ) ( value : encoding V )
  ( hole : encoding H ) ( callbacks : rw_plain_callbacks K Sort V H ) ( table : Map.t nat (
  rw_rule K Sort V H ) ) ( unknown : F ) ( strategy : rw_plain_fact_strategy K Sort V H F ) (
  fuel : positive ) ( state : rw_rp_run_state K Sort V H * Map.t rw_id F ) : ( rw_rp_run_state K
  Sort V H * Map.t rw_id F ) :=
if rw_rp_stopped ( fst state ) then state else match fuel with | xH => let out :=
  rw_plain_rw_rp_fact_run_once EK ES EV op sort value hole callbacks table unknown strategy
  state in out | xO rest => let middle := rw_plain_rw_rp_fact_run_repeat EK ES EV op sort value
  hole callbacks table unknown strategy rest state in let out := rw_plain_rw_rp_fact_run_repeat
  EK ES EV op sort value hole callbacks table unknown strategy rest middle in out | xI rest =>
  let first := rw_plain_rw_rp_fact_run_once EK ES EV op sort value hole callbacks table unknown
  strategy state in let middle := rw_plain_rw_rp_fact_run_repeat EK ES EV op sort value hole
  callbacks table unknown strategy rest first in let out := rw_plain_rw_rp_fact_run_repeat EK ES
  EV op sort value hole callbacks table unknown strategy rest middle in out end.

Definition rw_plain_rw_rp_fact_run_atomic { K Sort V H F } ( EK : encoding K ) ( ES : encoding
  Sort ) ( EV : encoding V ) ( op : encoding K ) ( sort : encoding Sort ) ( value : encoding V )
  ( hole : encoding H ) ( callbacks : rw_plain_callbacks K Sort V H ) ( rules : list ( rw_rule K
  Sort V H ) ) ( unknown : F ) ( strategy : rw_plain_fact_strategy K Sort V H F ) ( fuel : N ) (
  input : rw_tracked_state K Sort V H * Map.t rw_id F ) : ( rw_tracked_output K Sort V H * Map.t
  rw_id F ) :=
let ' ( initial , facts ) := input in match fuel with | N0 => ( RwTrackedOutput initial
  RWFuelExhausted nil nil , facts ) | Npos p => let table := rw_plain_rw_rp_rule_table_atomic
  rules 0 in let '( ready , initial_events ) := rw_plain_rw_rp_rebuild_atomic op sort value 0
  initial in let '( final , retained ) := rw_plain_rw_rp_fact_run_repeat EK ES EV op sort value
  hole callbacks table unknown strategy p ( RwRpRunState ready false 0 nil , Map.empty ) in (
  RwTrackedOutput ( rw_rp_current final ) ( if rw_rp_stopped final then RWStopped else
  RWFuelExhausted ) initial_events ( rw_rp_events final ) , retained ) end.

Definition rw_plain_rw_rp_selected_atomic { K Sort V H } ( op : encoding K ) ( sort : encoding
  Sort ) ( value : encoding V ) ( state : rw_tracked_state K Sort V H ) ( root : rw_id ) ( seed
  tree : rw_term K Sort V ) : option ( rw_provenance K Sort V H * positive ) :=
let machine := rw_tracked_machine state in let source_member := rw_plain_rw_ri_member_atomic op
  sort value machine seed root in let tree_member := rw_plain_rw_ri_member_atomic op sort value
  machine tree root in if source_member && tree_member then let out :=
  rw_plain_rw_rp_connect_atomic op sort value ( rw_tracked_provenance state ) seed tree in out
  else None.

Definition rw_plain_rw_rp_repr_emit { K Sort V } ( node : rw_repr_node K Sort V ) ( acc :
  rw_rp_repr_acc K Sort V ) : ( positive * rw_rp_repr_acc K Sort V ) :=
let id := rw_rp_repr_next acc in let nodes := rw_plain_audit_map_set
  rw_plain_audit_positive_encode id node ( rw_rp_repr_nodes acc ) in let fresh :=
  rw_plain_rw_fuel_pos_succ id in ( id , RwRpReprAcc ( id :: rw_rp_repr_ids acc ) nodes fresh ).

Fixpoint rw_plain_rw_rp_repr_term_atomic { K Sort V } ( op : encoding K ) ( sort : encoding Sort
  ) ( value : encoding V ) ( state : rw_index_state K Sort V ) ( term : rw_term K Sort V ) (
  root : rw_id ) ( acc : rw_rp_repr_acc K Sort V ) { struct term } : option ( positive *
  rw_rp_repr_acc K Sort V ) :=
let key_match := fun owner ty other_ty => let same_sort := rw_plain_rw_ri_encoded_equal sort ty
  other_ty in if same_sort then let same_class := rw_plain_rw_ri_same_class_atomic state root
  owner in same_class else false in match term with | RWVar ty v => let candidates :=
  rw_plain_rw_ri_bucket_ids ( rw_plain_rw_external_encoding_events value )
  rw_plain_rw_external_events_work v ( rw_index_variables state ) in let fix visit ( ids : list
  rw_id ) : option ( positive * rw_rp_repr_acc K Sort V ) := match ids with | nil => None | id
  :: rest => let found := rw_plain_audit_map_get rw_plain_audit_positive_encode id ( rw_nodes (
  rw_index_base state ) ) in let candidate := match found with | Some ( owner , RWNVar declared
  other ) => let same := key_match owner ty declared in if same then let same_value :=
  rw_plain_rw_ri_encoded_equal value v other in if same_value then let out :=
  rw_plain_rw_rp_repr_emit ( RWReprNode root id term nil ) acc in Some out else None else None |
  _ => None end in match candidate with | Some out => Some out | None => let out := visit rest
  in out end end in let out := visit candidates in out | RWApp ty key terms => let candidates :=
  rw_plain_rw_ri_bucket_ids ( rw_plain_rw_external_encoding_events op )
  rw_plain_rw_external_events_work key ( rw_index_operators state ) in let fix visit ( ids :
  list rw_id ) : option ( positive * rw_rp_repr_acc K Sort V ) := match ids with | nil => None |
  id :: rest => let found := rw_plain_audit_map_get rw_plain_audit_positive_encode id ( rw_nodes
  ( rw_index_base state ) ) in let candidate := match found with | Some ( owner , RWNApp
  declared other children ) => let same := key_match owner ty declared in if same then let
  same_op := rw_plain_rw_ri_encoded_equal op key other in if same_op then let fix descend ( ts :
  list ( rw_term K Sort V ) ) ( cs : list rw_id ) ( acc : rw_rp_repr_acc K Sort V ) : option (
  list positive * rw_rp_repr_acc K Sort V ) := match ts , cs with | nil , nil => Some ( nil ,
  acc ) | t :: ts , c :: cs => let head := rw_plain_rw_rp_repr_term_atomic op sort value state t
  c acc in match head with | None => None | Some ( pointer , next ) => let tail := descend ts cs
  next in option_map ( fun pair => ( pointer :: fst pair , snd pair ) ) tail end | _ , _ => None
  end in let children := descend terms children acc in match children with | None => None | Some
  ( pointers , next ) => let out := rw_plain_rw_rp_repr_emit ( RWReprNode root id term pointers
  ) next in Some out end else None else None | _ => None end in match candidate with | Some out
  => Some out | None => let out := visit rest in out end end in let out := visit candidates in
  out end.

Definition rw_plain_rw_rp_repr_find_atomic { K Sort V } ( op : encoding K ) ( sort : encoding
  Sort ) ( value : encoding V ) ( state : rw_index_state K Sort V ) ( root : rw_id ) ( term :
  rw_term K Sort V ) : option ( rw_repr_witness K Sort V ) :=
let found := rw_plain_rw_rp_repr_term_atomic op sort value state term root ( RwRpReprAcc nil
  Map.empty 1 % positive ) in option_map ( fun pair => RWReprWitness ( fst pair ) (
  rw_rp_repr_ids ( snd pair ) ) ( rw_rp_repr_nodes ( snd pair ) ) ) found.
```

## Galois.Rewrite.RewriteAuditProofPlainPublic

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditProofPlainPublic.v`.

```rocq
(** * RewriteAuditPlainPublic

    This module evaluates the fixed source phases without cost or receipt construction.
    For example, a lookup uses the actual plain map operation once.
    Builds on: the canonical Rewrite source equations and Collections. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexMatchReference RewriteAuditIndexReference
  RewriteAuditPlainCore1 RewriteAuditPlainCore2 RewriteAuditPlainCore3 RewriteAuditPlainCore4
  RewriteAuditPlainPrimitives RewriteAuditProofCarrier RewriteAuditProofRepresentation
  RewriteAuditProofRun RewriteAuditProofSemantic RewriteAuditProofTick.
Import List.ListNotations.
Local Coercion encode : encoding >-> Funclass.

Fixpoint rw_plain_repr_term_view { K Sort V } ( op : encoding K ) ( sort : encoding Sort ) (
  value : encoding V ) ( state : rw_phase_view K Sort V ) ( term : rw_term K Sort V ) ( root :
  rw_id ) ( acc : rw_rp_repr_acc K Sort V ) { struct term } : option ( positive * rw_rp_repr_acc
  K Sort V ) :=
let key_match := fun owner ty other_ty => let same_sort := rw_plain_rw_ri_encoded_equal sort ty
  other_ty in if same_sort then let same_class := rw_view_same_class state root owner in
  same_class else false in match term with | RWVar ty v => let candidates :=
  rw_view_variable_nodes state v in let fix visit ( ids : list rw_id ) : option ( positive *
  rw_rp_repr_acc K Sort V ) := match ids with | nil => None | id :: rest => let found :=
  rw_view_node state id in let candidate := match found with | Some ( owner , RWNVar declared
  other ) => let same := key_match owner ty declared in if same then let same_value :=
  rw_plain_rw_ri_encoded_equal value v other in if same_value then let out :=
  rw_plain_rw_rp_repr_emit ( RWReprNode root id term nil ) acc in Some out else None else None |
  _ => None end in match candidate with | Some out => Some out | None => let out := visit rest
  in out end end in let out := visit candidates in out | RWApp ty key terms => let candidates :=
  rw_view_operator_nodes state key in let fix visit ( ids : list rw_id ) : option ( positive *
  rw_rp_repr_acc K Sort V ) := match ids with | nil => None | id :: rest => let found :=
  rw_view_node state id in let candidate := match found with | Some ( owner , RWNApp declared
  other children ) => let same := key_match owner ty declared in if same then let same_op :=
  rw_plain_rw_ri_encoded_equal op key other in if same_op then let fix descend ( ts : list (
  rw_term K Sort V ) ) ( cs : list rw_id ) ( acc : rw_rp_repr_acc K Sort V ) : option ( list
  positive * rw_rp_repr_acc K Sort V ) := match ts , cs with | nil , nil => Some ( nil , acc ) |
  t :: ts , c :: cs => let head := rw_plain_repr_term_view op sort value state t c acc in match
  head with | None => None | Some ( pointer , next ) => let tail := descend ts cs next in
  option_map ( fun pair => ( pointer :: fst pair , snd pair ) ) tail end | _ , _ => None end in
  let children := descend terms children acc in match children with | None => None | Some (
  pointers , next ) => let out := rw_plain_rw_rp_repr_emit ( RWReprNode root id term pointers )
  next in Some out end else None else None | _ => None end in match candidate with | Some out =>
  Some out | None => let out := visit rest in out end end in let out := visit candidates in out end.


Definition rw_plain_repr_find_view { K Sort V } ( op : encoding K ) ( sort : encoding Sort ) (
  value : encoding V ) ( state : rw_phase_view K Sort V ) ( root : rw_id ) ( term : rw_term K
  Sort V ) : option ( rw_repr_witness K Sort V ) :=
let found := rw_plain_repr_term_view op sort value state term root ( RwRpReprAcc nil Map.empty 1
  % positive ) in option_map ( fun pair => RWReprWitness ( fst pair ) ( rw_rp_repr_ids ( snd
  pair ) ) ( rw_rp_repr_nodes ( snd pair ) ) ) found.

Definition rw_repr_find {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (view : rw_phase_view K Sort V) (root : rw_id) (term : rw_term K Sort V) :
    option (rw_repr_witness K Sort V) := rw_plain_repr_find_view EK ES EV view root term.

Definition rw_connect_class {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (graph : rw_graph K Sort V)
    (proof : rw_provenance K Sort V H) (root : rw_id) (lhs rhs : rw_term K Sort V)
    (witness : rw_repr_witness K Sort V) : option (rw_provenance K Sort V H * positive) :=
  rw_plain_rw_rp_connect_atomic EK ES EV proof lhs rhs.

Definition rw_tracked_tick {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (stamp : nat * nat) (state : rw_tracked_state K Sort V H) :
    option (rw_tracked_state K Sort V H * rw_index_event) :=
  rw_plain_rw_rp_tick_atomic EK ES EV stamp state.

Definition rw_tracked_rebuild {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (group : nat) (state : rw_tracked_state K Sort V H) :
    rw_tracked_state K Sort V H * list rw_index_event :=
  rw_plain_rw_rp_rebuild_atomic EK ES EV group state.

Definition rw_tracked_rule_step {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (sig : rw_signature K Sort V)
    (rules : list (rw_rule K Sort V H)) (position : nat)
    (state : rw_tracked_state K Sort V H) (attempt : rw_attempt K Sort V H) :
    option (rw_tracked_state K Sort V H) :=
  rw_plain_rw_rp_rule_step_atomic EK ES EV EK ES EV EH (rw_plain_callbacks_of sig)
    rules position state attempt.

Definition rw_tracked_run {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (sig : rw_signature K Sort V)
    (rules : list (rw_rule K Sort V H))
    (strategy : rw_snapshot_view K Sort V -> option (rw_attempt K Sort V H))
    (fuel : N) (seed : rw_term K Sort V) : rw_id * rw_tracked_output K Sort V H :=
  rw_plain_rw_rp_run_atomic EK ES EV EK ES EV EH (rw_plain_callbacks_of sig) rules
    (fun state => strategy (rw_index_view EK ES EV state)) fuel seed.

Definition rw_selected_explanation {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (state : rw_tracked_state K Sort V H) (root : rw_id)
    (seed tree : rw_term K Sort V) : option (rw_provenance K Sort V H * positive) :=
  rw_plain_rw_rp_selected_atomic EK ES EV state root seed tree.

Definition rw_factful_run {K Sort V H C F} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (sig : rw_signature K Sort V)
    (rules : list (rw_rule K Sort V H)) (an : rw_analysis K Sort V C F)
    (strategy : rw_fact_view K Sort V F -> option (rw_attempt K Sort V H))
    (fuel : N) (input : rw_tracked_state K Sort V H * Map.t rw_id F) :
    rw_tracked_output K Sort V H * Map.t rw_id F :=
  rw_plain_rw_rp_fact_run_atomic EK ES EV EK ES EV EH (rw_plain_callbacks_of sig) rules
    (rw_fact_unknown an)
    (fun state unknown facts => strategy (RWFactView (rw_index_view EK ES EV state)
      (fun id => match Map.get positive_encoding id facts with
        | Some fact => fact | None => unknown end))) fuel input.

Definition rw_tracked_apply {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) (rules : list (rw_rule K Sort V H))
    (position : nat) (state : rw_tracked_state K Sort V H) (attempt : rw_attempt K Sort V H) :=
  match rw_tracked_rule_step EK ES EV EH sig rules position state attempt with
  | None => None
  | Some intermediate => Some (rw_tracked_rebuild EK ES EV (S position) intermediate)
  end.

Definition rw_tracked_factful_apply {K Sort V H F} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (sig : rw_signature K Sort V)
    (rules : list (rw_rule K Sort V H)) (position : nat)
    (input : rw_tracked_state K Sort V H * Map.t rw_id F)
    (attempt : rw_attempt K Sort V H) :=
  let '(state, facts) := input in
  match rw_tracked_apply EK ES EV EH sig rules position state attempt with
  | None => None
  | Some (next, events) => Some ((next, rw_facts_invalidate facts), events)
  end.
```

## Galois.Rewrite.RewriteAuditProofInterfaceRpRunRealizesStatement

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditProofInterfaceRpRunRealizesStatement.v`.

```rocq
(** * RewriteAuditProofInterfaceRpRunRealizesStatement

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexProgramLaws RewriteAuditIndexPrograms
  RewriteAuditIndexReference RewriteAuditIndexRules RewriteAuditProofPlainPublic
  RewriteAuditProofRun RewriteAuditQueueReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_tracked_run : forall {K Sort V H},

     encoding K -> encoding Sort -> encoding V -> encoding H ->
  rw_signature K Sort V -> list
    (rw_rule K Sort V H) ->
  (rw_snapshot_view K Sort V -> option (rw_attempt K Sort V H)) ->

    N -> rw_term K Sort V -> rw_id * rw_tracked_output K Sort V H.

(** The actual public
    producer returns the output of this same complete source recurrence. *)

(** This statement fixes the rp run realizes statement contract. *)
Definition rw_rp_run_realizes_statement : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding
    Sort) (EV : encoding V) (EH : encoding H)
    (op : rw_queue_encoder_adapter K) (sort :
    rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole :
    rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) (sig :
    rw_signature K Sort V) rules
    (adapter : rw_rp_strategy_adapter K Sort V H) strategy
    execution fuel seed,
  (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->

    (forall ty, fst (rw_queue_encoder_run sort ty) = encode ES ty) ->
  (forall v, fst
    (rw_queue_encoder_run value v) = encode EV v) ->
  (forall h, fst (rw_queue_encoder_run hole
    h) = encode EH h) ->
  rw_rp_callbacks_agree EH sig callbacks rules ->

    rw_rp_strategy_adapter_laws EK ES EV adapter strategy execution ->
  fst (rw_rp_run_atomic
    EK ES EV op sort value hole callbacks rules adapter fuel seed) =
    rw_tracked_run EK ES EV
    EH sig rules strategy fuel seed.

(** Stop callbacks and rejected attempts consume the very
    same finite run budget. *)


End FuturePublicImplementations.
```

## Galois.Rewrite.RewriteAuditIndexPlainPublic

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditIndexPlainPublic.v`.

```rocq
(** * RewriteAuditPlainPublic

    This module evaluates the fixed source phases without cost or receipt construction.
    For example, a lookup uses the actual plain map operation once.
    Builds on: the canonical Rewrite source equations and Collections. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexReference RewriteAuditIndexTickReference
  RewriteAuditPlainCore1 RewriteAuditPlainPrimitives.
Import List.ListNotations.
Local Coercion encode : encoding >-> Funclass.

Definition rw_index_rule_step {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (sig : rw_signature K Sort V)
    (rules : list (rw_rule K Sort V H)) (state : rw_index_state K Sort V)
    (attempt : rw_attempt K Sort V H) : option (rw_index_state K Sort V) :=
  rw_plain_rw_ri_rule_step_atomic EK ES EV EH (rw_plain_callbacks_of sig) rules state attempt.

Definition rw_index_run {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (sig : rw_signature K Sort V)
    (rules : list (rw_rule K Sort V H))
    (strategy : rw_snapshot_view K Sort V -> option (rw_attempt K Sort V H))
    (fuel : N) (graph : rw_graph K Sort V) :
    rw_run_result K Sort V * list rw_index_event * list (rw_run_event K Sort V H) :=
  rw_plain_rw_ri_run_atomic EK ES EV EH (rw_plain_callbacks_of sig) rules
    (fun state => strategy (rw_index_view EK ES EV state)) fuel graph.

Definition rw_index_apply {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) (rules : list (rw_rule K Sort V H))
    (state : rw_index_state K Sort V) (attempt : rw_attempt K Sort V H) :=
  match rw_index_rule_step EK ES EV EH sig rules state attempt with
  | None => None
  | Some intermediate => Some (rw_index_rebuild EK ES EV intermediate)
  end.
```

## Galois.Rewrite.RewriteAuditIndexInterfaceRiRuleStepRealizesStatement

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditIndexInterfaceRiRuleStepRealizesStatement.v`.

```rocq
(** * RewriteAuditIndexInterfaceRiRuleStepRealizesStatement

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexPlainPublic RewriteAuditIndexProgramLaws
  RewriteAuditIndexReference RewriteAuditIndexRules RewriteAuditIndexRun RewriteAuditQueueReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_index_rule_step : forall {K Sort V H},
  encoding K -> encoding Sort -> encoding V -> encoding H -> rw_signature K Sort V ->
  list (rw_rule K Sort V H) -> rw_index_state K Sort V -> rw_attempt K Sort V H ->
  option (rw_index_state K Sort V).


(** This statement fixes the ri rule step realizes statement contract. *)
Definition rw_ri_rule_step_realizes_statement : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) sig rules state attempt,
  (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
  (forall s, fst (rw_queue_encoder_run sort s) = encode ES s) ->
  (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
  (forall h, fst (rw_queue_encoder_run hole h) = encode EH h) ->
  rw_rp_callbacks_agree EH sig callbacks rules ->
  fst (rw_ri_rule_step_atomic op sort value hole callbacks rules state attempt) =
    rw_index_rule_step EK ES EV EH sig rules state attempt.

(** Apply keeps the exact public accepted intermediate state and chronological rebuild events. *)


End FuturePublicImplementations.
```

## Galois.Rewrite.RewriteAuditIndexInterfaceRiApplyRealizesStatement

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditIndexInterfaceRiApplyRealizesStatement.v`.

```rocq
(** * RewriteAuditIndexInterfaceRiApplyRealizesStatement

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexPlainPublic RewriteAuditIndexProgramLaws
  RewriteAuditIndexReference RewriteAuditIndexRules RewriteAuditIndexRun
  RewriteAuditIndexTickReference RewriteAuditQueueReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_index_rule_step : forall {K Sort V H},
  encoding K -> encoding Sort -> encoding V -> encoding H -> rw_signature K Sort V ->
  list (rw_rule K Sort V H) -> rw_index_state K Sort V -> rw_attempt K Sort V H ->
  option (rw_index_state K Sort V).


Let rw_index_apply {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) (rules : list (rw_rule K Sort V H))
    (state : rw_index_state K Sort V) (attempt : rw_attempt K Sort V H) :=
  match rw_index_rule_step EK ES EV EH sig rules state attempt with
  | None => None
  | Some intermediate => Some (rw_index_rebuild EK ES EV intermediate)
  end.


(** This statement fixes the ri apply realizes statement contract. *)
Definition rw_ri_apply_realizes_statement : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) sig rules state attempt,
  (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
  (forall s, fst (rw_queue_encoder_run sort s) = encode ES s) ->
  (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
  (forall h, fst (rw_queue_encoder_run hole h) = encode EH h) ->
  rw_rp_callbacks_agree EH sig callbacks rules ->
  fst (rw_ri_apply_atomic op sort value hole callbacks rules state attempt) =
    rw_index_apply EK ES EV EH sig rules state attempt.

(** The full source recurrence returns the exact public run, stop reason, and event order. *)


End FuturePublicImplementations.
```

## Galois.Rewrite.RewriteAuditIndexInterfaceRiRunRealizesStatement

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditIndexInterfaceRiRunRealizesStatement.v`.

```rocq
(** * RewriteAuditIndexInterfaceRiRunRealizesStatement

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexPlainPublic RewriteAuditIndexProgramLaws
  RewriteAuditIndexPrograms RewriteAuditIndexReference RewriteAuditIndexRules
  RewriteAuditIndexRun RewriteAuditQueueReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_index_run : forall {K Sort V H},
  encoding K -> encoding Sort -> encoding V -> encoding H -> rw_signature K Sort V ->
  list (rw_rule K Sort V H) ->
  (rw_snapshot_view K Sort V -> option (rw_attempt K Sort V H)) -> N -> rw_graph K Sort V ->
  rw_run_result K Sort V * list rw_index_event * list (rw_run_event K Sort V H).

(** The fixed graph-only accepted rule model realizes its own plain public operation. *)

(** This statement fixes the ri run realizes statement contract. *)
Definition rw_ri_run_realizes_statement : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) sig rules
    (adapter : rw_rp_strategy_adapter K Sort V H) strategy execution fuel graph,
  (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
  (forall s, fst (rw_queue_encoder_run sort s) = encode ES s) ->
  (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
  (forall h, fst (rw_queue_encoder_run hole h) = encode EH h) ->
  rw_rp_callbacks_agree EH sig callbacks rules ->
  rw_rp_strategy_adapter_laws EK ES EV adapter strategy execution ->
  fst (rw_ri_run_atomic op sort value hole callbacks rules adapter fuel graph) =
    rw_index_run EK ES EV EH sig rules strategy fuel graph.

(** Every graph-only source run preserves the original semantic contract. *)


End FuturePublicImplementations.
```

## Galois.Rewrite.RewriteAuditIndexInterfaceIndexRunCleanTraceContract

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditIndexInterfaceIndexRunCleanTraceContract.v`.

```rocq
(** * RewriteAuditIndexInterfaceIndexRunCleanTraceContract

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexPlainPublic
  RewriteAuditIndexPrepareReference RewriteAuditIndexPublic RewriteAuditIndexReference
  RewriteAuditIndexTickReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_index_rule_step : forall {K Sort V H},
  encoding K -> encoding Sort -> encoding V -> encoding H -> rw_signature K Sort V ->
  list (rw_rule K Sort V H) -> rw_index_state K Sort V -> rw_attempt K Sort V H ->
  option (rw_index_state K Sort V).


Variable rw_index_run : forall {K Sort V H},
  encoding K -> encoding Sort -> encoding V -> encoding H -> rw_signature K Sort V ->
  list (rw_rule K Sort V H) ->
  (rw_snapshot_view K Sort V -> option (rw_attempt K Sort V H)) -> N -> rw_graph K Sort V ->
  rw_run_result K Sort V * list rw_index_event * list (rw_run_event K Sort V H).

(** The fixed graph-only accepted rule model realizes its own plain public operation. *)

Let rw_index_apply {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) (rules : list (rw_rule K Sort V H))
    (state : rw_index_state K Sort V) (attempt : rw_attempt K Sort V H) :=
  match rw_index_rule_step EK ES EV EH sig rules state attempt with
  | None => None
  | Some intermediate => Some (rw_index_rebuild EK ES EV intermediate)
  end.


(** This statement fixes the index run clean trace contract. *)
Definition rw_index_run_clean_trace_contract : Prop :=
  forall K Sort V H C (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) (admissible : rw_semantics K Sort V C -> Prop)
    (rules : list (rw_rule K Sort V H))
    strategy fuel (input : rw_graph K Sort V) result initial_events events,
    Forall (rw_rule_wf sig) rules -> Forall (rw_rule_sound sig admissible) rules ->
    rw_graph_wf sig input -> rw_graph_sound sig admissible rules input -> rw_productive input ->
rw_index_run EK ES EV EH sig rules strategy (Npos fuel) input = (result, initial_events,
    events) ->
    exists initial final,
      rw_index_rebuild EK ES EV (rw_index_build EK ES EV input) = (initial, initial_events) /\
      rw_index_clean_trace rw_index_graph (rw_index_view EK ES EV)
        (rw_index_apply EK ES EV EH sig rules) strategy initial (rev events) final /\
      rw_run_graph result = rw_index_graph final /\
      (rw_run_stop result = RWStopped -> strategy (rw_index_view EK ES EV final) = None).



End FuturePublicImplementations.
```

## Galois.Rewrite.RewriteAuditIndexInterfaceIndexRunZeroContract

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditIndexInterfaceIndexRunZeroContract.v`.

```rocq
(** * RewriteAuditIndexInterfaceIndexRunZeroContract

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexPlainPublic RewriteAuditIndexReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_index_run : forall {K Sort V H},
  encoding K -> encoding Sort -> encoding V -> encoding H -> rw_signature K Sort V ->
  list (rw_rule K Sort V H) ->
  (rw_snapshot_view K Sort V -> option (rw_attempt K Sort V H)) -> N -> rw_graph K Sort V ->
  rw_run_result K Sort V * list rw_index_event * list (rw_run_event K Sort V H).

(** The fixed graph-only accepted rule model realizes its own plain public operation. *)

(** This statement fixes the index run zero contract. *)
Definition rw_index_run_zero_contract : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) rules strategy (g : rw_graph K Sort V),
    rw_index_run EK ES EV EH sig rules strategy 0%N g =
      (RwRunResult g RWFuelExhausted, nil, nil).



End FuturePublicImplementations.
```

## Galois.Rewrite.RewriteAuditIndexInterfaceIndexRunCorrectContract

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditIndexInterfaceIndexRunCorrectContract.v`.

```rocq
(** * RewriteAuditIndexInterfaceIndexRunCorrectContract

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexPlainPublic RewriteAuditIndexReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_index_run : forall {K Sort V H},
  encoding K -> encoding Sort -> encoding V -> encoding H -> rw_signature K Sort V ->
  list (rw_rule K Sort V H) ->
  (rw_snapshot_view K Sort V -> option (rw_attempt K Sort V H)) -> N -> rw_graph K Sort V ->
  rw_run_result K Sort V * list rw_index_event * list (rw_run_event K Sort V H).

(** The fixed graph-only accepted rule model realizes its own plain public operation. *)

(** This statement fixes the index run correct contract. *)
Definition rw_index_run_correct_contract : Prop :=
  forall K Sort V H C (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H))
    strategy fuel (g : rw_graph K Sort V),
    Forall (rw_rule_wf sig) rules -> Forall (rw_rule_sound sig admissible) rules ->
    rw_graph_wf sig g -> rw_graph_sound sig admissible rules g -> rw_productive g ->
    let '(result, _, _) := rw_index_run EK ES EV EH sig rules strategy fuel g in
    rw_graph_wf sig (rw_run_graph result) /\
    rw_graph_sound sig admissible rules (rw_run_graph result) /\
    rw_productive (rw_run_graph result) /\ rw_extends g (rw_run_graph result) /\
    (fuel <> 0%N -> rw_clean (rw_run_graph result)).



End FuturePublicImplementations.
```

## Galois.Rewrite.RewriteAuditIndexInterfaceIndexRunCallbackBoundContract

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditIndexInterfaceIndexRunCallbackBoundContract.v`.

```rocq
(** * RewriteAuditIndexInterfaceIndexRunCallbackBoundContract

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexPlainPublic RewriteAuditIndexReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_index_run : forall {K Sort V H},
  encoding K -> encoding Sort -> encoding V -> encoding H -> rw_signature K Sort V ->
  list (rw_rule K Sort V H) ->
  (rw_snapshot_view K Sort V -> option (rw_attempt K Sort V H)) -> N -> rw_graph K Sort V ->
  rw_run_result K Sort V * list rw_index_event * list (rw_run_event K Sort V H).

(** The fixed graph-only accepted rule model realizes its own plain public operation. *)

(** This statement fixes the index run callback bound contract. *)
Definition rw_index_run_callback_bound_contract : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) rules strategy fuel (g : rw_graph K Sort V),
    let '(result, _, events) := rw_index_run EK ES EV EH sig rules strategy fuel g in
    (N.of_nat (length events) +
      match rw_run_stop result with RWStopped => 1%N | RWFuelExhausted => 0%N end <= fuel)%N.



End FuturePublicImplementations.
```

## Galois.Rewrite.RewriteAuditIndexInterfaceIndexRuleStepSupportedContract

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditIndexInterfaceIndexRuleStepSupportedContract.v`.

```rocq
(** * RewriteAuditIndexInterfaceIndexRuleStepSupportedContract

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexPlainPublic RewriteAuditIndexPublic
  RewriteAuditIndexReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_index_rule_step : forall {K Sort V H},
  encoding K -> encoding Sort -> encoding V -> encoding H -> rw_signature K Sort V ->
  list (rw_rule K Sort V H) -> rw_index_state K Sort V -> rw_attempt K Sort V H ->
  option (rw_index_state K Sort V).


(** This statement fixes the index rule step supported contract. *)
Definition rw_index_rule_step_supported_contract : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) (rules : list (rw_rule K Sort V H))
    (state next : rw_index_state K Sort V) attempt,
    Forall (rw_rule_wf sig) rules ->
    index_supported_valid EK ES EV sig state -> index_bucket_node_support EK ES EV state ->
    rw_index_rule_step EK ES EV EH sig rules state attempt = Some next ->
    index_supported_valid EK ES EV sig next /\ index_bucket_node_support EK ES EV next.




End FuturePublicImplementations.
```

## Galois.Rewrite.RewriteAuditProofInterfaceRpSelectedRealizesStatement

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditProofInterfaceRpSelectedRealizesStatement.v`.

```rocq
(** * RewriteAuditProofInterfaceRpSelectedRealizesStatement

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditProofCarrier RewriteAuditProofPlainPublic
  RewriteAuditProofSelected RewriteAuditProofTick RewriteAuditQueueReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_selected_explanation : forall {K Sort V H},
  encoding K -> encoding Sort -> encoding V -> rw_tracked_state K Sort V H -> rw_id ->
  rw_term K Sort V -> rw_term K Sort V -> option (rw_provenance K Sort V H * positive).

(** Selected explanations use the same fixed source computation on the same final state. *)

(** This statement fixes the rp selected realizes statement contract. *)
Definition rw_rp_selected_realizes_statement : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (state : rw_tracked_state K Sort V H) root seed tree,
  (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
  (forall s, fst (rw_queue_encoder_run sort s) = encode ES s) ->
  (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
  fst (rw_rp_selected_atomic op sort value state root seed tree) =
    rw_selected_explanation EK ES EV state root seed tree.

(** Checked rules preserve the semantic and connection invariants of the actual bounded run. *)


End FuturePublicImplementations.
```

## Galois.Rewrite.RewriteAuditProofInterfaceReprFindSpecContract

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditProofInterfaceReprFindSpecContract.v`.

```rocq
(** * RewriteAuditProofInterfaceReprFindSpecContract

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexReference RewriteAuditProofPlainPublic
  RewriteAuditProofRepresentation.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_repr_find : forall {K Sort V}, encoding K -> encoding Sort -> encoding V ->
  rw_phase_view K Sort V -> rw_id -> rw_term K Sort V -> option (rw_repr_witness K Sort V).

(** This statement fixes the repr find spec contract. *)
Definition rw_repr_find_spec_contract : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (sig : rw_signature K Sort V) (g : rw_graph K Sort V) view c t,
    rw_graph_wf sig g -> rw_view_agrees g view ->
    match rw_repr_find EK ES EV view c t with
    | Some w => rw_repr_witness_valid g c t w
    | None => ~ rw_represents g c t
    end.



End FuturePublicImplementations.
```

## Galois.Rewrite.RewriteAuditProofInterfaceTrackedExtractableContract

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditProofInterfaceTrackedExtractableContract.v`.

```rocq
(** * RewriteAuditProofInterfaceTrackedExtractableContract

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexReference RewriteAuditProofPlainPublic
  RewriteAuditProofRun RewriteAuditProofSemantic.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_tracked_run : forall {K Sort V H},

     encoding K -> encoding Sort -> encoding V -> encoding H ->
  rw_signature K Sort V -> list
    (rw_rule K Sort V H) ->
  (rw_snapshot_view K Sort V -> option (rw_attempt K Sort V H)) ->

    N -> rw_term K Sort V -> rw_id * rw_tracked_output K Sort V H.

(** The actual public
    producer returns the output of this same complete source recurrence. *)

(** This statement fixes the tracked extractable contract. *)
Definition rw_tracked_extractable_contract : Prop :=
  forall K Sort V H C (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (sig : rw_signature K Sort V) (admissible : rw_semantics K Sort V C -> Prop)
    (rules : list (rw_rule K Sort V H)),
    Forall (rw_rule_wf sig) rules -> Forall (rw_rule_sound sig admissible) rules ->
    forall seed, rw_typed sig seed -> forall strategy fuel vc oc,
    let '(root, result) := rw_tracked_run EK ES EV EH sig rules strategy fuel seed in
exists tree, rw_extract_tree EK ES EV vc oc (rw_tracked_graph (rw_tracked_final result))
    root = Some tree.



End FuturePublicImplementations.
```

## Galois.Rewrite.RewriteAuditProofInterfaceTrackedSelectedContract

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditProofInterfaceTrackedSelectedContract.v`.

```rocq
(** * RewriteAuditProofInterfaceTrackedSelectedContract

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexReference RewriteAuditProofCarrier
  RewriteAuditProofPlainPublic RewriteAuditProofRun RewriteAuditProofSemantic RewriteAuditProofTick.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_tracked_run : forall {K Sort V H},

     encoding K -> encoding Sort -> encoding V -> encoding H ->
  rw_signature K Sort V -> list
    (rw_rule K Sort V H) ->
  (rw_snapshot_view K Sort V -> option (rw_attempt K Sort V H)) ->

    N -> rw_term K Sort V -> rw_id * rw_tracked_output K Sort V H.

(** The actual public
    producer returns the output of this same complete source recurrence. *)

Variable rw_selected_explanation : forall {K Sort V H},
  encoding K -> encoding Sort -> encoding V -> rw_tracked_state K Sort V H -> rw_id ->
  rw_term K Sort V -> rw_term K Sort V -> option (rw_provenance K Sort V H * positive).

(** Selected explanations use the same fixed source computation on the same final state. *)

(** This statement fixes the tracked selected contract. *)
Definition rw_tracked_selected_contract : Prop :=
  forall K Sort V H C (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (sig : rw_signature K Sort V) (admissible : rw_semantics K Sort V C -> Prop)
    (rules : list (rw_rule K Sort V H)),
    Forall (rw_rule_wf sig) rules -> Forall (rw_rule_sound sig admissible) rules ->
    forall seed, rw_typed sig seed -> forall strategy fuel vc oc tree,
    let '(root, result) := rw_tracked_run EK ES EV EH sig rules strategy fuel seed in
    rw_extract_tree EK ES EV vc oc (rw_tracked_graph (rw_tracked_final result)) root = Some tree ->
    exists proof id node,
rw_selected_explanation EK ES EV (rw_tracked_final result) root seed tree = Some (proof,
    id) /\
      rw_provenance_valid EH sig rules proof /\
      Map.get positive_encoding id (rw_provenance_nodes proof) = Some node /\
      rw_evidence_left node = seed /\ rw_evidence_right node = tree.



End FuturePublicImplementations.
```

## Galois.Rewrite.RewriteAuditProofInterfaceTrackedRunInvariantsContract

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditProofInterfaceTrackedRunInvariantsContract.v`.

```rocq
(** * RewriteAuditProofInterfaceTrackedRunInvariantsContract

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexReference RewriteAuditProofCarrier
  RewriteAuditProofPlainPublic RewriteAuditProofRepresentation RewriteAuditProofRun
  RewriteAuditProofSemantic RewriteAuditProofTick RewriteAuditSharedReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_tracked_run : forall {K Sort V H},

     encoding K -> encoding Sort -> encoding V -> encoding H ->
  rw_signature K Sort V -> list
    (rw_rule K Sort V H) ->
  (rw_snapshot_view K Sort V -> option (rw_attempt K Sort V H)) ->

    N -> rw_term K Sort V -> rw_id * rw_tracked_output K Sort V H.

(** The actual public
    producer returns the output of this same complete source recurrence. *)

Variable rw_connect_class : forall {K Sort V H}, encoding K -> encoding Sort -> encoding V ->
    encoding H ->
  rw_graph K Sort V -> rw_provenance K Sort V H -> rw_id -> rw_term K Sort V -> rw_term K Sort V ->
  rw_repr_witness K Sort V -> option (rw_provenance K Sort V H * positive).


(** This statement fixes the tracked run invariants contract. *)
Definition rw_tracked_run_invariants_contract : Prop :=
  forall K Sort V H C (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (sig : rw_signature K Sort V) (admissible : rw_semantics K Sort V C -> Prop)
    (rules : list (rw_rule K Sort V H)),
    Forall (rw_rule_wf sig) rules -> Forall (rw_rule_sound sig admissible) rules ->
    forall seed, rw_typed sig seed -> forall strategy fuel,
    let '(root, result) := rw_tracked_run EK ES EV EH sig rules strategy fuel seed in
    let state := rw_tracked_final result in
    let g := rw_tracked_graph state in
    let proof := rw_tracked_provenance state in
    let witnesses := rw_tracked_witnesses state in
    rw_graph_wf sig g /\ rw_graph_sound sig admissible rules g /\ rw_productive g /\
    rw_represents g root seed /\ (fuel <> 0%N -> rw_clean g) /\
    rw_provenance_valid EH sig rules proof /\ rw_class_witnesses_valid g witnesses /\
    rw_class_connected EH sig rules (@rw_shared_unfold K Sort V)
      (rw_connect_class EK ES EV EH) g witnesses proof /\
    rw_tracked_event_index_valid state (rw_tracked_initial result) (rw_tracked_events result) /\
    rw_tracked_rule_nodes_covered state (rw_tracked_events result).




End FuturePublicImplementations.
```

## Galois.Rewrite.RewriteAuditProofInterfaceTrackedPhaseValid

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditProofInterfaceTrackedPhaseValid.v`.

```rocq
(** * RewriteAuditProofInterfaceTrackedPhaseValid

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexReference RewriteAuditProofCarrier
  RewriteAuditProofPlainPublic RewriteAuditProofRepresentation RewriteAuditProofSemantic
  RewriteAuditProofTick RewriteAuditSharedReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_connect_class : forall {K Sort V H}, encoding K -> encoding Sort -> encoding V ->
    encoding H ->
  rw_graph K Sort V -> rw_provenance K Sort V H -> rw_id -> rw_term K Sort V -> rw_term K Sort V ->
  rw_repr_witness K Sort V -> option (rw_provenance K Sort V H * positive).


Definition rw_tracked_phase_valid {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (sig : rw_signature K Sort V)
    (rules : list (rw_rule K Sort V H)) (state : rw_tracked_state K Sort V H) : Prop :=
  let machine := rw_tracked_machine state in
  let proof := rw_tracked_provenance state in
  let witnesses := rw_tracked_witnesses state in
  rw_index_valid EK ES EV sig machine /\ rw_provenance_valid EH sig rules proof /\
  rw_class_witnesses_valid (rw_index_graph machine) witnesses /\
  rw_class_connected EH sig rules (@rw_shared_unfold K Sort V)
    (rw_connect_class EK ES EV EH) (rw_index_graph machine) witnesses proof.


End FuturePublicImplementations.
```

## Galois.Rewrite.RewriteAuditProofInterfaceTrackedTickProjectionContract

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditProofInterfaceTrackedTickProjectionContract.v`.

```rocq
(** * RewriteAuditProofInterfaceTrackedTickProjectionContract

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexReference RewriteAuditIndexTickReference
  RewriteAuditProofCarrier RewriteAuditProofInterfaceTrackedPhaseValid
  RewriteAuditProofPlainPublic RewriteAuditProofRepresentation RewriteAuditProofSemantic
  RewriteAuditProofTick RewriteAuditSharedReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_connect_class : forall {K Sort V H}, encoding K -> encoding Sort -> encoding V ->
    encoding H ->
  rw_graph K Sort V -> rw_provenance K Sort V H -> rw_id -> rw_term K Sort V -> rw_term K Sort V ->
  rw_repr_witness K Sort V -> option (rw_provenance K Sort V H * positive).


Variable rw_tracked_tick : forall {K Sort V H}, encoding K -> encoding Sort -> encoding V ->
  (nat * nat) -> rw_tracked_state K Sort V H ->
  option (rw_tracked_state K Sort V H * rw_index_event).

Let rw_tracked_phase_valid {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (sig : rw_signature K Sort V)
    (rules : list (rw_rule K Sort V H)) (state : rw_tracked_state K Sort V H) : Prop :=
  let machine := rw_tracked_machine state in
  let proof := rw_tracked_provenance state in
  let witnesses := rw_tracked_witnesses state in
  rw_index_valid EK ES EV sig machine /\ rw_provenance_valid EH sig rules proof /\
  rw_class_witnesses_valid (rw_index_graph machine) witnesses /\
  rw_class_connected EH sig rules (@rw_shared_unfold K Sort V)
    (rw_connect_class EK ES EV EH) (rw_index_graph machine) witnesses proof.

(** This statement fixes the tracked tick projection contract. *)
Definition rw_tracked_tick_projection_contract : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (sig : rw_signature K Sort V) rules stamp (state : rw_tracked_state K Sort V H),
    rw_tracked_phase_valid EK ES EV EH sig rules state -> rw_tracked_stamp_fresh stamp state ->
    match rw_tracked_tick EK ES EV stamp state with
    | None => rw_index_tick EK ES EV (rw_tracked_machine state) = None
    | Some (next,event) =>
      rw_index_tick EK ES EV (rw_tracked_machine state) = Some (rw_tracked_machine next,event) /\
      rw_tracked_phase_valid EK ES EV EH sig rules next
    end.


End FuturePublicImplementations.
```

## Galois.Rewrite.RewriteAuditProofInterfaceTrackedTickCongruenceContract

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditProofInterfaceTrackedTickCongruenceContract.v`.

```rocq
(** * RewriteAuditProofInterfaceTrackedTickCongruenceContract

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexReference RewriteAuditProofCarrier
  RewriteAuditProofPlainPublic RewriteAuditProofSemantic RewriteAuditProofTick
  RewriteAuditSharedReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_tracked_tick : forall {K Sort V H}, encoding K -> encoding Sort -> encoding V ->
  (nat * nat) -> rw_tracked_state K Sort V H ->
  option (rw_tracked_state K Sort V H * rw_index_event).

(** This statement fixes the tracked tick congruence contract. *)
Definition rw_tracked_tick_congruence_contract : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) rules stamp
    (state next : rw_tracked_state K Sort V H) n m a b root,
    rw_provenance_valid EH sig rules (rw_tracked_provenance state) ->
    rw_class_witnesses_valid (rw_tracked_graph state) (rw_tracked_witnesses state) ->
    rw_tracked_tick EK ES EV stamp state = Some (next, RWIndexCongruence (n,m) a b root) ->
    forall left_id right_id left right,
      let store := rw_tracked_witnesses state in
      Map.get positive_encoding a (rw_class_witness_roots store) = Some left_id ->
      Map.get positive_encoding b (rw_class_witness_roots store) = Some right_id ->
      rw_shared_unfold (RwSharedTree K Sort V left_id (rw_class_witness_nodes store)) = Some left ->
rw_shared_unfold (RwSharedTree K Sort V right_id (rw_class_witness_nodes store)) = Some
    right ->
      exists id node,
Map.get (pair_encoding nat_encoding nat_encoding) stamp (rw_tracked_event_nodes next) =
    Some id /\
Map.get positive_encoding id (rw_provenance_nodes (rw_tracked_provenance next)) = Some
    node /\
rw_evidence_time node = stamp /\ rw_evidence_left node = left /\ rw_evidence_right node =
    right.



End FuturePublicImplementations.
```

## Galois.Rewrite.RewriteAuditProofInterfaceTrackedRebuildTraceCorrectContract

Card: AUD-RW-MODELS

Source destination:
  `theories/Rewrite/RewriteAuditProofInterfaceTrackedRebuildTraceCorrectContract.v`.

```rocq
(** * RewriteAuditProofInterfaceTrackedRebuildTraceCorrectContract

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexReference RewriteAuditIndexTickReference
  RewriteAuditProofCarrier RewriteAuditProofInterfaceTrackedPhaseValid
  RewriteAuditProofPlainPublic RewriteAuditProofRepresentation RewriteAuditProofSemantic
  RewriteAuditProofTick RewriteAuditSharedReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_connect_class : forall {K Sort V H}, encoding K -> encoding Sort -> encoding V ->
    encoding H ->
  rw_graph K Sort V -> rw_provenance K Sort V H -> rw_id -> rw_term K Sort V -> rw_term K Sort V ->
  rw_repr_witness K Sort V -> option (rw_provenance K Sort V H * positive).


Variable rw_tracked_tick : forall {K Sort V H}, encoding K -> encoding Sort -> encoding V ->
  (nat * nat) -> rw_tracked_state K Sort V H ->
  option (rw_tracked_state K Sort V H * rw_index_event).

Variable rw_tracked_rebuild : forall {K Sort V H}, encoding K -> encoding Sort -> encoding V ->
  nat -> rw_tracked_state K Sort V H -> rw_tracked_state K Sort V H * list rw_index_event.

Let rw_tracked_phase_valid {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (sig : rw_signature K Sort V)
    (rules : list (rw_rule K Sort V H)) (state : rw_tracked_state K Sort V H) : Prop :=
  let machine := rw_tracked_machine state in
  let proof := rw_tracked_provenance state in
  let witnesses := rw_tracked_witnesses state in
  rw_index_valid EK ES EV sig machine /\ rw_provenance_valid EH sig rules proof /\
  rw_class_witnesses_valid (rw_index_graph machine) witnesses /\
  rw_class_connected EH sig rules (@rw_shared_unfold K Sort V)
    (rw_connect_class EK ES EV EH) (rw_index_graph machine) witnesses proof.

(** This statement fixes the tracked rebuild trace correct contract. *)
Definition rw_tracked_rebuild_trace_correct_contract : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (sig : rw_signature K Sort V) rules group (state : rw_tracked_state K Sort V H),
    rw_tracked_phase_valid EK ES EV EH sig rules state -> rw_tracked_stamp_fresh (group,1) state ->
    let '(final,events) := rw_tracked_rebuild EK ES EV group state in
    rw_tracked_rebuild_trace (rw_tracked_tick EK ES EV) group 0 state events final /\
    rw_tracked_phase_valid EK ES EV EH sig rules final /\
    rw_index_rebuild EK ES EV (rw_tracked_machine state) = (rw_tracked_machine final,events).




End FuturePublicImplementations.
```

## Galois.Rewrite.RewriteAuditProofInterfaceTrackedApplyProjectsContract

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditProofInterfaceTrackedApplyProjectsContract.v`.

```rocq
(** * RewriteAuditProofInterfaceTrackedApplyProjectsContract

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexPlainPublic RewriteAuditIndexReference
  RewriteAuditIndexTickReference RewriteAuditProofCarrier
  RewriteAuditProofInterfaceTrackedPhaseValid RewriteAuditProofPlainPublic
  RewriteAuditProofRepresentation RewriteAuditProofSemantic RewriteAuditProofTick
  RewriteAuditSharedReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_index_rule_step : forall {K Sort V H},
  encoding K -> encoding Sort -> encoding V -> encoding H -> rw_signature K Sort V ->
  list (rw_rule K Sort V H) -> rw_index_state K Sort V -> rw_attempt K Sort V H ->
  option (rw_index_state K Sort V).


Variable rw_connect_class : forall {K Sort V H}, encoding K -> encoding Sort -> encoding V ->
    encoding H ->
  rw_graph K Sort V -> rw_provenance K Sort V H -> rw_id -> rw_term K Sort V -> rw_term K Sort V ->
  rw_repr_witness K Sort V -> option (rw_provenance K Sort V H * positive).


Variable rw_tracked_rebuild : forall {K Sort V H}, encoding K -> encoding Sort -> encoding V ->
  nat -> rw_tracked_state K Sort V H -> rw_tracked_state K Sort V H * list rw_index_event.

Variable rw_tracked_rule_step : forall {K Sort V H}, encoding K -> encoding Sort -> encoding V ->
    encoding H ->
  rw_signature K Sort V -> list (rw_rule K Sort V H) -> nat -> rw_tracked_state K Sort V H ->
  rw_attempt K Sort V H -> option (rw_tracked_state K Sort V H).

Let rw_index_apply {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) (rules : list (rw_rule K Sort V H))
    (state : rw_index_state K Sort V) (attempt : rw_attempt K Sort V H) :=
  match rw_index_rule_step EK ES EV EH sig rules state attempt with
  | None => None
  | Some intermediate => Some (rw_index_rebuild EK ES EV intermediate)
  end.


Let rw_tracked_phase_valid {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (sig : rw_signature K Sort V)
    (rules : list (rw_rule K Sort V H)) (state : rw_tracked_state K Sort V H) : Prop :=
  let machine := rw_tracked_machine state in
  let proof := rw_tracked_provenance state in
  let witnesses := rw_tracked_witnesses state in
  rw_index_valid EK ES EV sig machine /\ rw_provenance_valid EH sig rules proof /\
  rw_class_witnesses_valid (rw_index_graph machine) witnesses /\
  rw_class_connected EH sig rules (@rw_shared_unfold K Sort V)
    (rw_connect_class EK ES EV EH) (rw_index_graph machine) witnesses proof.

Let rw_tracked_apply {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) (rules : list (rw_rule K Sort V H))
    (position : nat) (state : rw_tracked_state K Sort V H) (attempt : rw_attempt K Sort V H) :=
  match rw_tracked_rule_step EK ES EV EH sig rules position state attempt with
  | None => None
  | Some intermediate => Some (rw_tracked_rebuild EK ES EV (S position) intermediate)
  end.

(** This statement fixes the tracked apply projects contract. *)
Definition rw_tracked_apply_projects_contract : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (sig : rw_signature K Sort V) (rules : list (rw_rule K Sort V H)) position
    (state : rw_tracked_state K Sort V H) attempt,
    Forall (rw_rule_wf sig) rules ->
    rw_tracked_phase_valid EK ES EV EH sig rules state ->
    rw_tracked_stamp_fresh (S position,0) state ->
    match rw_tracked_apply EK ES EV EH sig rules position state attempt with
    | None => rw_index_apply EK ES EV EH sig rules (rw_tracked_machine state) attempt = None
    | Some (next,events) =>
      rw_index_apply EK ES EV EH sig rules (rw_tracked_machine state) attempt =
Some (rw_tracked_machine next,events) /\ rw_tracked_phase_valid EK ES EV EH sig rules next
    /\
      exists id node,
Map.get (pair_encoding nat_encoding nat_encoding) (S position,0) (rw_tracked_event_nodes
    next) = Some id /\
Map.get positive_encoding id (rw_provenance_nodes (rw_tracked_provenance next)) = Some
    node /\
        rw_evidence_time node = (S position,0) /\
rw_evidence_reason_of node = RWEvidenceRule (rw_attempt_rule attempt) (rw_attempt_sub
    attempt)
    end.


End FuturePublicImplementations.
```

## Galois.Rewrite.RewriteAuditProofInterfaceTrackedFactfulApplyRejectContract

Card: AUD-RW-MODELS

Source destination:
  `theories/Rewrite/RewriteAuditProofInterfaceTrackedFactfulApplyRejectContract.v`.

```rocq
(** * RewriteAuditProofInterfaceTrackedFactfulApplyRejectContract

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexReference RewriteAuditProofPlainPublic
  RewriteAuditProofSemantic RewriteAuditProofTick.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_tracked_rebuild : forall {K Sort V H}, encoding K -> encoding Sort -> encoding V ->
  nat -> rw_tracked_state K Sort V H -> rw_tracked_state K Sort V H * list rw_index_event.

Variable rw_tracked_rule_step : forall {K Sort V H}, encoding K -> encoding Sort -> encoding V ->
    encoding H ->
  rw_signature K Sort V -> list (rw_rule K Sort V H) -> nat -> rw_tracked_state K Sort V H ->
  rw_attempt K Sort V H -> option (rw_tracked_state K Sort V H).

Let rw_tracked_apply {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) (rules : list (rw_rule K Sort V H))
    (position : nat) (state : rw_tracked_state K Sort V H) (attempt : rw_attempt K Sort V H) :=
  match rw_tracked_rule_step EK ES EV EH sig rules position state attempt with
  | None => None
  | Some intermediate => Some (rw_tracked_rebuild EK ES EV (S position) intermediate)
  end.

Let rw_tracked_factful_apply {K Sort V H F} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (sig : rw_signature K Sort V)
    (rules : list (rw_rule K Sort V H)) (position : nat)
    (input : rw_tracked_state K Sort V H * Map.t rw_id F)
    (attempt : rw_attempt K Sort V H) :=
  let '(state, facts) := input in
  match rw_tracked_apply EK ES EV EH sig rules position state attempt with
  | None => None
  | Some (next, events) => Some ((next, rw_facts_invalidate facts), events)
  end.

(** This statement fixes the tracked factful apply reject contract. *)
Definition rw_tracked_factful_apply_reject_contract : Prop :=
  forall K Sort V H F (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (sig : rw_signature K Sort V) rules position state (facts : Map.t rw_id F) attempt,
    rw_tracked_factful_apply EK ES EV EH sig rules position (state, facts) attempt = None <->
    rw_tracked_apply EK ES EV EH sig rules position state attempt = None.


End FuturePublicImplementations.
```

## Galois.Rewrite.RewriteAuditProofInterfaceTrackedFactfulApplyAcceptContract

Card: AUD-RW-MODELS

Source destination:
  `theories/Rewrite/RewriteAuditProofInterfaceTrackedFactfulApplyAcceptContract.v`.

```rocq
(** * RewriteAuditProofInterfaceTrackedFactfulApplyAcceptContract

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexReference RewriteAuditProofPlainPublic
  RewriteAuditProofSemantic RewriteAuditProofTick.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_tracked_rebuild : forall {K Sort V H}, encoding K -> encoding Sort -> encoding V ->
  nat -> rw_tracked_state K Sort V H -> rw_tracked_state K Sort V H * list rw_index_event.

Variable rw_tracked_rule_step : forall {K Sort V H}, encoding K -> encoding Sort -> encoding V ->
    encoding H ->
  rw_signature K Sort V -> list (rw_rule K Sort V H) -> nat -> rw_tracked_state K Sort V H ->
  rw_attempt K Sort V H -> option (rw_tracked_state K Sort V H).

Let rw_tracked_apply {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) (rules : list (rw_rule K Sort V H))
    (position : nat) (state : rw_tracked_state K Sort V H) (attempt : rw_attempt K Sort V H) :=
  match rw_tracked_rule_step EK ES EV EH sig rules position state attempt with
  | None => None
  | Some intermediate => Some (rw_tracked_rebuild EK ES EV (S position) intermediate)
  end.

Let rw_tracked_factful_apply {K Sort V H F} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (sig : rw_signature K Sort V)
    (rules : list (rw_rule K Sort V H)) (position : nat)
    (input : rw_tracked_state K Sort V H * Map.t rw_id F)
    (attempt : rw_attempt K Sort V H) :=
  let '(state, facts) := input in
  match rw_tracked_apply EK ES EV EH sig rules position state attempt with
  | None => None
  | Some (next, events) => Some ((next, rw_facts_invalidate facts), events)
  end.

(** This statement fixes the tracked factful apply accept contract. *)
Definition rw_tracked_factful_apply_accept_contract : Prop :=
  forall K Sort V H C F (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (sig : rw_signature K Sort V) rules (admissible : rw_semantics K Sort V C -> Prop)
    (an : rw_analysis K Sort V C F) position state facts attempt next retained events,
    rw_fact_store_valid admissible an (rw_tracked_graph state) facts ->
rw_tracked_factful_apply EK ES EV EH sig rules position (state, facts) attempt = Some
    ((next, retained), events) ->
    rw_tracked_apply EK ES EV EH sig rules position state attempt = Some (next, events) /\
retained = rw_facts_invalidate facts /\ rw_fact_store_valid admissible an
    (rw_tracked_graph next) retained.



End FuturePublicImplementations.
```

## Galois.Rewrite.RewriteAuditProofInterfaceFactfulRunZeroContract

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditProofInterfaceFactfulRunZeroContract.v`.

```rocq
(** * RewriteAuditProofInterfaceFactfulRunZeroContract

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditProofPlainPublic RewriteAuditProofRun
  RewriteAuditProofSemantic RewriteAuditProofTick.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_factful_run : forall {K Sort V H C F},
  encoding K -> encoding Sort -> encoding V -> encoding H ->
  rw_signature K Sort V -> list (rw_rule K Sort V H) -> rw_analysis K Sort V C F ->
  (rw_fact_view K Sort V F -> option (rw_attempt K Sort V H)) -> N ->
  rw_tracked_state K Sort V H * Map.t rw_id F ->
  rw_tracked_output K Sort V H * Map.t rw_id F.


(** This statement fixes the factful run zero contract. *)
Definition rw_factful_run_zero_contract : Prop :=
  forall K Sort V H C F (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) (rules : list (rw_rule K Sort V H))
    (an : rw_analysis K Sort V C F) strategy (state : rw_tracked_state K Sort V H) facts,
    rw_factful_run EK ES EV EH sig rules an strategy 0%N (state, facts) =
      (RwTrackedOutput state RWFuelExhausted nil nil, facts).



End FuturePublicImplementations.
```

## Galois.Rewrite.RewriteAuditProofInterfaceFactfulRunValidContract

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditProofInterfaceFactfulRunValidContract.v`.

```rocq
(** * RewriteAuditProofInterfaceFactfulRunValidContract

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditProofPlainPublic RewriteAuditProofRun
  RewriteAuditProofSemantic RewriteAuditProofTick.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_factful_run : forall {K Sort V H C F},
  encoding K -> encoding Sort -> encoding V -> encoding H ->
  rw_signature K Sort V -> list (rw_rule K Sort V H) -> rw_analysis K Sort V C F ->
  (rw_fact_view K Sort V F -> option (rw_attempt K Sort V H)) -> N ->
  rw_tracked_state K Sort V H * Map.t rw_id F ->
  rw_tracked_output K Sort V H * Map.t rw_id F.


(** This statement fixes the factful run valid contract. *)
Definition rw_factful_run_valid_contract : Prop :=
  forall K Sort V H C F (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) (rules : list (rw_rule K Sort V H))
    (admissible : rw_semantics K Sort V C -> Prop) (an : rw_analysis K Sort V C F)
    strategy fuel state facts result retained,
    rw_fact_store_valid admissible an (rw_tracked_graph state) facts ->
    rw_factful_run EK ES EV EH sig rules an strategy fuel (state, facts) =
      (result, retained) ->
    rw_fact_store_valid admissible an (rw_tracked_graph (rw_tracked_final result)) retained.



End FuturePublicImplementations.
```

## Galois.Rewrite.RewriteAuditProofInterfaceFactfulRunCallbackBoundContract

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditProofInterfaceFactfulRunCallbackBoundContract.v`.

```rocq
(** * RewriteAuditProofInterfaceFactfulRunCallbackBoundContract

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditProofPlainPublic RewriteAuditProofRun
  RewriteAuditProofSemantic RewriteAuditProofTick.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_factful_run : forall {K Sort V H C F},
  encoding K -> encoding Sort -> encoding V -> encoding H ->
  rw_signature K Sort V -> list (rw_rule K Sort V H) -> rw_analysis K Sort V C F ->
  (rw_fact_view K Sort V F -> option (rw_attempt K Sort V H)) -> N ->
  rw_tracked_state K Sort V H * Map.t rw_id F ->
  rw_tracked_output K Sort V H * Map.t rw_id F.


(** This statement fixes the factful run callback bound contract. *)
Definition rw_factful_run_callback_bound_contract : Prop :=
  forall K Sort V H C F (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) (rules : list (rw_rule K Sort V H))
    (an : rw_analysis K Sort V C F) strategy fuel (state : rw_tracked_state K Sort V H) facts,
    let '(result, _) := rw_factful_run EK ES EV EH sig rules an strategy fuel (state, facts) in
    (N.of_nat (length (rw_tracked_events result)) +
      match rw_tracked_stop result with RWStopped => 1 | RWFuelExhausted => 0 end <= fuel)%N.





End FuturePublicImplementations.
```

## Galois.Rewrite.RewriteAuditProofInterfaceRpReprRealizesStatement

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditProofInterfaceRpReprRealizesStatement.v`.

```rocq
(** * RewriteAuditProofInterfaceRpReprRealizesStatement

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexReference RewriteAuditProofPlainPublic
  RewriteAuditProofRepresentation RewriteAuditQueueReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_repr_find : forall {K Sort V}, encoding K -> encoding Sort -> encoding V ->
  rw_phase_view K Sort V -> rw_id -> rw_term K Sort V -> option (rw_repr_witness K Sort V).

(** This statement fixes the rp repr realizes statement contract. *)
Definition rw_rp_repr_realizes_statement : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) state root term,
  (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
  (forall s, fst (rw_queue_encoder_run sort s) = encode ES s) ->
  (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
  fst (rw_rp_repr_find_atomic op sort value state root term) =
    rw_repr_find EK ES EV (rw_snapshot_base (rw_index_view EK ES EV state)) root term.

(** The public connection uses the concrete finite proof closure on the supplied endpoints. *)


End FuturePublicImplementations.
```

## Galois.Rewrite.RewriteAuditProofInterfaceRpConnectRealizesStatement

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditProofInterfaceRpConnectRealizesStatement.v`.

```rocq
(** * RewriteAuditProofInterfaceRpConnectRealizesStatement

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditProofCarrier RewriteAuditProofClosure
  RewriteAuditProofPlainPublic RewriteAuditProofRepresentation RewriteAuditQueueReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_connect_class : forall {K Sort V H}, encoding K -> encoding Sort -> encoding V ->
    encoding H ->
  rw_graph K Sort V -> rw_provenance K Sort V H -> rw_id -> rw_term K Sort V -> rw_term K Sort V ->
  rw_repr_witness K Sort V -> option (rw_provenance K Sort V H * positive).


(** This statement fixes the rp connect realizes statement contract. *)
Definition rw_rp_connect_realizes_statement : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (graph : rw_graph K Sort V)
    (proof : rw_provenance K Sort V H) root lhs rhs witness,
  (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
  (forall s, fst (rw_queue_encoder_run sort s) = encode ES s) ->
  (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
  fst (rw_rp_connect_atomic op sort value proof lhs rhs) =
    rw_connect_class EK ES EV EH graph proof root lhs rhs witness.

(** The public tracked tick retains the exact indexed event and evidence mutation. *)


End FuturePublicImplementations.
```

## Galois.Rewrite.RewriteAuditProofInterfaceRpTickRealizesStatement

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditProofInterfaceRpTickRealizesStatement.v`.

```rocq
(** * RewriteAuditProofInterfaceRpTickRealizesStatement

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexReference RewriteAuditProofPlainPublic
  RewriteAuditProofTick RewriteAuditQueueReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_tracked_tick : forall {K Sort V H}, encoding K -> encoding Sort -> encoding V ->
  (nat * nat) -> rw_tracked_state K Sort V H ->
  option (rw_tracked_state K Sort V H * rw_index_event).

(** This statement fixes the rp tick realizes statement contract. *)
Definition rw_rp_tick_realizes_statement : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) stamp (state : rw_tracked_state K Sort V H),
  (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
  (forall s, fst (rw_queue_encoder_run sort s) = encode ES s) ->
  (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
  fst (rw_rp_tick_atomic op sort value stamp state) = rw_tracked_tick EK ES EV stamp state.

(** The public rebuild keeps the same chronological events and completed tracked state. *)


End FuturePublicImplementations.
```

## Galois.Rewrite.RewriteAuditProofInterfaceRpRebuildRealizesStatement

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditProofInterfaceRpRebuildRealizesStatement.v`.

```rocq
(** * RewriteAuditProofInterfaceRpRebuildRealizesStatement

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexReference RewriteAuditProofPlainPublic
  RewriteAuditProofRebuild RewriteAuditProofTick RewriteAuditQueueReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_tracked_rebuild : forall {K Sort V H}, encoding K -> encoding Sort -> encoding V ->
  nat -> rw_tracked_state K Sort V H -> rw_tracked_state K Sort V H * list rw_index_event.

(** This statement fixes the rp rebuild realizes statement contract. *)
Definition rw_rp_rebuild_realizes_statement : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) group (state : rw_tracked_state K Sort V H),
  (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
  (forall s, fst (rw_queue_encoder_run sort s) = encode ES s) ->
  (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
  fst (rw_rp_rebuild_atomic op sort value group state) = rw_tracked_rebuild EK ES EV group state.

(** The accepted rule step is the fixed gate, indexed membership, growth and original-ID capture. *)


End FuturePublicImplementations.
```

## Galois.Rewrite.RewriteAuditProofInterfaceRpRuleStepRealizesStatement

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditProofInterfaceRpRuleStepRealizesStatement.v`.

```rocq
(** * RewriteAuditProofInterfaceRpRuleStepRealizesStatement

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexProgramLaws RewriteAuditIndexRules
  RewriteAuditProofApply RewriteAuditProofPlainPublic RewriteAuditProofTick
  RewriteAuditQueueReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_tracked_rule_step : forall {K Sort V H}, encoding K -> encoding Sort -> encoding V ->
    encoding H ->
  rw_signature K Sort V -> list (rw_rule K Sort V H) -> nat -> rw_tracked_state K Sort V H ->
  rw_attempt K Sort V H -> option (rw_tracked_state K Sort V H).

(** This statement fixes the rp rule step realizes statement contract. *)
Definition rw_rp_rule_step_realizes_statement : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) sig rules position state attempt,
  (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
  (forall s, fst (rw_queue_encoder_run sort s) = encode ES s) ->
  (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
  (forall h, fst (rw_queue_encoder_run hole h) = encode EH h) ->
  rw_rp_callbacks_agree EH sig callbacks rules ->
  fst (rw_rp_rule_step_atomic EK ES EV op sort value hole callbacks rules position state attempt) =
    rw_tracked_rule_step EK ES EV EH sig rules position state attempt.

(** Public tracked apply includes its exact accepted rebuild and original attempt stamp. *)


End FuturePublicImplementations.
```

## Galois.Rewrite.RewriteAuditProofInterfaceRpApplyRealizesStatement

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditProofInterfaceRpApplyRealizesStatement.v`.

```rocq
(** * RewriteAuditProofInterfaceRpApplyRealizesStatement

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexProgramLaws RewriteAuditIndexReference
  RewriteAuditIndexRules RewriteAuditProofApply RewriteAuditProofPlainPublic
  RewriteAuditProofTick RewriteAuditQueueReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_tracked_rebuild : forall {K Sort V H}, encoding K -> encoding Sort -> encoding V ->
  nat -> rw_tracked_state K Sort V H -> rw_tracked_state K Sort V H * list rw_index_event.

Variable rw_tracked_rule_step : forall {K Sort V H}, encoding K -> encoding Sort -> encoding V ->
    encoding H ->
  rw_signature K Sort V -> list (rw_rule K Sort V H) -> nat -> rw_tracked_state K Sort V H ->
  rw_attempt K Sort V H -> option (rw_tracked_state K Sort V H).

Let rw_tracked_apply {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) (rules : list (rw_rule K Sort V H))
    (position : nat) (state : rw_tracked_state K Sort V H) (attempt : rw_attempt K Sort V H) :=
  match rw_tracked_rule_step EK ES EV EH sig rules position state attempt with
  | None => None
  | Some intermediate => Some (rw_tracked_rebuild EK ES EV (S position) intermediate)
  end.

(** This statement fixes the rp apply realizes statement contract. *)
Definition rw_rp_apply_realizes_statement : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) sig rules position state attempt,
  (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
  (forall s, fst (rw_queue_encoder_run sort s) = encode ES s) ->
  (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
  (forall h, fst (rw_queue_encoder_run hole h) = encode EH h) ->
  rw_rp_callbacks_agree EH sig callbacks rules ->
  fst (rw_rp_apply_atomic EK ES EV op sort value hole callbacks rules position state attempt) =
    rw_tracked_apply EK ES EV EH sig rules position state attempt.



End FuturePublicImplementations.
```

## Galois.Rewrite.RewriteAuditProofInterfaceRpFactfulApplyRealizesStatement

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditProofInterfaceRpFactfulApplyRealizesStatement.v`.

```rocq
(** * RewriteAuditProofInterfaceRpFactfulApplyRealizesStatement

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexProgramLaws RewriteAuditIndexReference
  RewriteAuditIndexRules RewriteAuditProofPlainPublic RewriteAuditProofRealizations
  RewriteAuditProofSemantic RewriteAuditProofTick RewriteAuditQueueReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_tracked_rebuild : forall {K Sort V H}, encoding K -> encoding Sort -> encoding V ->
  nat -> rw_tracked_state K Sort V H -> rw_tracked_state K Sort V H * list rw_index_event.

Variable rw_tracked_rule_step : forall {K Sort V H}, encoding K -> encoding Sort -> encoding V ->
    encoding H ->
  rw_signature K Sort V -> list (rw_rule K Sort V H) -> nat -> rw_tracked_state K Sort V H ->
  rw_attempt K Sort V H -> option (rw_tracked_state K Sort V H).

Let rw_tracked_apply {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) (rules : list (rw_rule K Sort V H))
    (position : nat) (state : rw_tracked_state K Sort V H) (attempt : rw_attempt K Sort V H) :=
  match rw_tracked_rule_step EK ES EV EH sig rules position state attempt with
  | None => None
  | Some intermediate => Some (rw_tracked_rebuild EK ES EV (S position) intermediate)
  end.

Let rw_tracked_factful_apply {K Sort V H F} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (sig : rw_signature K Sort V)
    (rules : list (rw_rule K Sort V H)) (position : nat)
    (input : rw_tracked_state K Sort V H * Map.t rw_id F)
    (attempt : rw_attempt K Sort V H) :=
  let '(state, facts) := input in
  match rw_tracked_apply EK ES EV EH sig rules position state attempt with
  | None => None
  | Some (next, events) => Some ((next, rw_facts_invalidate facts), events)
  end.

(** This statement fixes the rp factful apply realizes statement contract. *)
Definition rw_rp_factful_apply_realizes_statement : Prop :=
  forall K Sort V H F (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) sig rules position
    (input : rw_tracked_state K Sort V H * Map.t rw_id F) attempt,
  (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
  (forall s, fst (rw_queue_encoder_run sort s) = encode ES s) ->
  (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
  (forall h, fst (rw_queue_encoder_run hole h) = encode EH h) ->
  rw_rp_callbacks_agree EH sig callbacks rules ->
  fst (rw_rp_factful_apply_atomic EK ES EV op sort value hole callbacks rules position input
    attempt) =
    rw_tracked_factful_apply EK ES EV EH sig rules position input attempt.



End FuturePublicImplementations.
```

## Galois.Rewrite.RewriteAuditProofInterfaceRpFactRunRealizesStatement

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditProofInterfaceRpFactRunRealizesStatement.v`.

```rocq
(** * RewriteAuditProofInterfaceRpFactRunRealizesStatement

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexProgramLaws RewriteAuditIndexRules
  RewriteAuditProofFactPublic RewriteAuditProofFacts RewriteAuditProofPlainPublic
  RewriteAuditProofRun RewriteAuditProofSemantic RewriteAuditProofTick RewriteAuditQueueReference.
Import List.ListNotations.

Section FuturePublicImplementations.

Variable rw_factful_run : forall {K Sort V H C F},
  encoding K -> encoding Sort -> encoding V -> encoding H ->
  rw_signature K Sort V -> list (rw_rule K Sort V H) -> rw_analysis K Sort V C F ->
  (rw_fact_view K Sort V F -> option (rw_attempt K Sort V H)) -> N ->
  rw_tracked_state K Sort V H * Map.t rw_id F ->
  rw_tracked_output K Sort V H * Map.t rw_id F.


(** This statement fixes the rp fact run realizes statement contract. *)
Definition rw_rp_fact_run_realizes_statement : Prop :=
  forall K Sort V H C F (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) sig rules (an : rw_analysis K Sort V C F)
    adapter strategy fuel input,
  (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
  (forall s, fst (rw_queue_encoder_run sort s) = encode ES s) ->
  (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
  (forall h, fst (rw_queue_encoder_run hole h) = encode EH h) ->
  rw_rp_callbacks_agree EH sig callbacks rules ->
  rw_rp_fact_strategy_agrees EK ES EV an adapter strategy ->
  fst (rw_rp_fact_run_atomic EK ES EV op sort value hole callbacks rules
    (rw_fact_unknown an) adapter fuel input) =
    rw_factful_run EK ES EV EH sig rules an strategy fuel input.

(** Stored facts survive rejection and are invalidated before observing any extended graph. *)


End FuturePublicImplementations.
```

## Galois.Rewrite.RewriteAuditSharedPlainContracts

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditSharedPlainContracts.v`.

```rocq
(** * Fixed plain shared-operation contract bindings

    Every existing RD contract is instantiated by the actual fixed plain body or builder.
    For example, comparator agreement quantifies over its own erased termination proof only.
    Builds on: the plain computational bodies and the unchanged public contract schemas. *)

From Stdlib Require Import List Bool PArith NArith.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditQueueReference RewriteAuditSharedCompare
  RewriteAuditSharedExtract RewriteAuditSharedInterfaceRdCompareRealizesStatement
  RewriteAuditSharedInterfaceRdExtractRealizesStatement
  RewriteAuditSharedInterfaceRdScalarRealizesStatement
  RewriteAuditSharedInterfaceSharedCompareAgreesContract
  RewriteAuditSharedInterfaceSharedCompareRejectContract
  RewriteAuditSharedInterfaceSharedExtractUnfoldContract
  RewriteAuditSharedInterfaceSharedObserversRejectContract
  RewriteAuditSharedInterfaceSharedTreeCostAgreesContract
  RewriteAuditSharedInterfaceSharedTreeCostBinaryAgreesContract
  RewriteAuditSharedInterfaceSharedTreeSizeBinaryAgreesContract RewriteAuditSharedPlain.
Import List.ListNotations.
Local Coercion encode : encoding >-> Funclass.

(** The public comparator's unchanged realization type binds the fixed memo recursion. *)
Definition rw_rd_plain_compare_realizes_type (Hwf : rw_rd_plain_compare_well_founded_type) : Prop :=
  @rw_rd_compare_realizes_statement
    (@rw_shared_compare_builder Hwf).

(** The public extractor's unchanged realization type binds the fixed binary DP body. *)
Definition rw_rd_plain_extract_realizes_type (Hwf : rw_rd_plain_compare_well_founded_type) : Prop :=
  @rw_rd_extract_realizes_statement
    (@rw_shared_extract_builder Hwf).

(** The three scalar public bodies erase exactly their source work payloads. *)
Definition rw_rd_plain_scalar_realizes_type : Prop :=
  @rw_rd_scalar_realizes_statement
    (@rw_shared_tree_cost) (@rw_shared_tree_cost_binary) (@rw_shared_tree_size_binary).

(** The actual comparator preserves expanded preorder, sort and payload order. *)
Definition rw_rd_plain_compare_agrees_type (Hwf : rw_rd_plain_compare_well_founded_type) : Prop :=
  @rw_shared_compare_agrees_contract
    (@rw_shared_compare_builder Hwf).

(** Full validation rejects every malformed stored graph before memo recursion. *)
Definition rw_rd_plain_compare_reject_type (Hwf : rw_rd_plain_compare_well_founded_type) : Prop :=
  @rw_shared_compare_reject_contract
    (@rw_shared_compare_builder Hwf).

(** Shared extraction has the existing selected tree after separately accounted unfolding. *)
Definition rw_rd_plain_extract_unfold_type (Hwf : rw_rd_plain_compare_well_founded_type) : Prop :=
  @rw_shared_extract_unfold_contract
    (@rw_shared_extract_builder Hwf).

(** Unary cost preserves the expanded additive tree objective. *)
Definition rw_rd_plain_tree_cost_agrees_type : Prop :=
  @rw_shared_tree_cost_agrees_contract
    (@rw_shared_tree_cost).

(** Binary cost preserves the expanded additive tree objective. *)
Definition rw_rd_plain_tree_cost_binary_agrees_type : Prop :=
  @rw_shared_tree_cost_binary_agrees_contract
    (@rw_shared_tree_cost_binary).

(** Binary size counts repeated child occurrences rather than stored nodes. *)
Definition rw_rd_plain_tree_size_binary_agrees_type : Prop :=
  @rw_shared_tree_size_binary_agrees_contract
    (@rw_shared_tree_size_binary).

(** All three actual scalar bodies retain the exact malformed-input rejection contract. *)
Definition rw_rd_plain_observers_reject_type : Prop :=
  @rw_shared_observers_reject_contract
    (@rw_shared_tree_cost) (@rw_shared_tree_cost_binary) (@rw_shared_tree_size_binary).

(** Every fixed source comparator execution returns the actual plain builder's result. *)
Definition rw_rd_plain_compare_source_erases_type
    (Hwf : rw_rd_plain_compare_well_founded_type) : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    op sort value left right answer work,
  (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
  (forall ty, fst (rw_queue_encoder_run sort ty) = encode ES ty) ->
  (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
  rw_shared_compare_run op sort value left right answer work ->
  rw_shared_compare_builder Hwf EK ES EV left right = answer.

(** Every fixed extraction source run preserves the full returned shared store and root. *)
Definition rw_rd_plain_extract_source_erases_type
    (Hwf : rw_rd_plain_compare_well_founded_type) : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    op sort value vc oc g root answer work,
  (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
  (forall ty, fst (rw_queue_encoder_run sort ty) = encode ES ty) ->
  (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
  rw_shared_extract_run op sort value vc oc g root answer work ->
  rw_shared_extract_builder Hwf EK ES EV (fun v => fst (vc v))
    (fun k => fst (oc k)) g root = answer.

(** The literal DP production retains candidate objectives and all immutable allocated nodes. *)
Definition rw_rd_plain_production_source_erases_type : Prop :=
  forall K Sort V vc oc (g : RewriteEgraph.rw_graph K Sort V) old node store,
  rd_plain_production (fun v => fst (vc v)) (fun k => fst (oc k)) g old node store =
    fst (rw_rd_production vc oc g old node store).
```

## Galois.Rewrite.RewriteAuditIndexPlainContracts

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditIndexPlainContracts.v`.

```rocq
(** * RewriteAuditIndexPlainContracts

    These types fix public contracts to the actual plain source bodies.
    For example, no arbitrary same-value producer can replace the accepted rule body.
    Builds on: fixed source schemas, plain computations and own library termination types. *)

From Stdlib Require Import List Bool PArith NArith.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexInterfaceIndexRuleStepSupportedContract
  RewriteAuditIndexInterfaceIndexRunCallbackBoundContract
  RewriteAuditIndexInterfaceIndexRunCleanTraceContract
  RewriteAuditIndexInterfaceIndexRunCorrectContract
  RewriteAuditIndexInterfaceIndexRunZeroContract
  RewriteAuditIndexInterfaceRiApplyRealizesStatement
  RewriteAuditIndexInterfaceRiRuleStepRealizesStatement
  RewriteAuditIndexInterfaceRiRunRealizesStatement RewriteAuditIndexPlainPublic.
Import List.ListNotations.
Local Coercion encode : encoding >-> Funclass.

(** The exact rw_ri_rule_step_realizes type specializes the fixed plain computation. *)
Definition rw_ri_rule_step_realizes_fixed_type : Prop :=
  @rw_ri_rule_step_realizes_statement
    (@RewriteAuditIndexPlainPublic.rw_index_rule_step).

(** The exact rw_ri_apply_realizes type specializes the fixed plain computation. *)
Definition rw_ri_apply_realizes_fixed_type : Prop :=
  @rw_ri_apply_realizes_statement
    (@RewriteAuditIndexPlainPublic.rw_index_rule_step).

(** The exact rw_ri_run_realizes type specializes the fixed plain computation. *)
Definition rw_ri_run_realizes_fixed_type : Prop :=
  @rw_ri_run_realizes_statement
    (@RewriteAuditIndexPlainPublic.rw_index_run).

(** The exact rw_index_run_clean_trace type specializes the fixed plain computation. *)
Definition rw_index_run_clean_trace_fixed_type : Prop :=
  @rw_index_run_clean_trace_contract
    (@RewriteAuditIndexPlainPublic.rw_index_rule_step) (@RewriteAuditIndexPlainPublic.rw_index_run).

(** The exact rw_index_run_zero type specializes the fixed plain computation. *)
Definition rw_index_run_zero_fixed_type : Prop :=
  @rw_index_run_zero_contract
    (@RewriteAuditIndexPlainPublic.rw_index_run).

(** The exact rw_index_run_correct type specializes the fixed plain computation. *)
Definition rw_index_run_correct_fixed_type : Prop :=
  @rw_index_run_correct_contract
    (@RewriteAuditIndexPlainPublic.rw_index_run).

(** The exact rw_index_run_callback_bound type specializes the fixed plain computation. *)
Definition rw_index_run_callback_bound_fixed_type : Prop :=
  @rw_index_run_callback_bound_contract
    (@RewriteAuditIndexPlainPublic.rw_index_run).

(** The exact rw_index_rule_step_supported type specializes the fixed plain computation. *)
Definition rw_index_rule_step_supported_fixed_type : Prop :=
  @rw_index_rule_step_supported_contract
    (@RewriteAuditIndexPlainPublic.rw_index_rule_step).
```

## Galois.Rewrite.RewriteAuditProofPlainContracts

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditProofPlainContracts.v`.

```rocq
(** * RewriteAuditProofPlainContracts

    These types fix public contracts to the actual plain source bodies.
    For example, no arbitrary same-value producer can replace the accepted rule body.
    Builds on: fixed source schemas, plain computations and own library termination types. *)

From Stdlib Require Import List Bool PArith NArith.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexPlainPublic
  RewriteAuditProofInterfaceFactfulRunCallbackBoundContract
  RewriteAuditProofInterfaceFactfulRunValidContract
  RewriteAuditProofInterfaceFactfulRunZeroContract
  RewriteAuditProofInterfaceReprFindSpecContract
  RewriteAuditProofInterfaceRpApplyRealizesStatement
  RewriteAuditProofInterfaceRpConnectRealizesStatement
  RewriteAuditProofInterfaceRpFactRunRealizesStatement
  RewriteAuditProofInterfaceRpFactfulApplyRealizesStatement
  RewriteAuditProofInterfaceRpRebuildRealizesStatement
  RewriteAuditProofInterfaceRpReprRealizesStatement
  RewriteAuditProofInterfaceRpRuleStepRealizesStatement
  RewriteAuditProofInterfaceRpRunRealizesStatement
  RewriteAuditProofInterfaceRpSelectedRealizesStatement
  RewriteAuditProofInterfaceRpTickRealizesStatement
  RewriteAuditProofInterfaceTrackedApplyProjectsContract
  RewriteAuditProofInterfaceTrackedExtractableContract
  RewriteAuditProofInterfaceTrackedFactfulApplyAcceptContract
  RewriteAuditProofInterfaceTrackedFactfulApplyRejectContract
  RewriteAuditProofInterfaceTrackedRebuildTraceCorrectContract
  RewriteAuditProofInterfaceTrackedRunInvariantsContract
  RewriteAuditProofInterfaceTrackedSelectedContract
  RewriteAuditProofInterfaceTrackedTickCongruenceContract
  RewriteAuditProofInterfaceTrackedTickProjectionContract RewriteAuditProofPlainPublic.
Import List.ListNotations.
Local Coercion encode : encoding >-> Funclass.

(** The exact rw_rp_run_realizes type specializes the fixed plain computation. *)
Definition rw_rp_run_realizes_fixed_type : Prop :=
  @rw_rp_run_realizes_statement
    (@RewriteAuditProofPlainPublic.rw_tracked_run).

(** The exact rw_rp_selected_realizes type specializes the fixed plain computation. *)
Definition rw_rp_selected_realizes_fixed_type : Prop :=
  @rw_rp_selected_realizes_statement
    (@RewriteAuditProofPlainPublic.rw_selected_explanation).

(** The exact rw_repr_find_spec type specializes the fixed plain computation. *)
Definition rw_repr_find_spec_fixed_type : Prop :=
  @rw_repr_find_spec_contract
    (@RewriteAuditProofPlainPublic.rw_repr_find).

(** The exact rw_tracked_extractable type specializes the fixed plain computation. *)
Definition rw_tracked_extractable_fixed_type : Prop :=
  @rw_tracked_extractable_contract
    (@RewriteAuditProofPlainPublic.rw_tracked_run).

(** The exact rw_tracked_selected type specializes the fixed plain computation. *)
Definition rw_tracked_selected_fixed_type : Prop :=
  @rw_tracked_selected_contract
    (@RewriteAuditProofPlainPublic.rw_tracked_run)
  (@RewriteAuditProofPlainPublic.rw_selected_explanation).

(** The exact rw_tracked_run_invariants type specializes the fixed plain computation. *)
Definition rw_tracked_run_invariants_fixed_type : Prop :=
  @rw_tracked_run_invariants_contract
    (@RewriteAuditProofPlainPublic.rw_tracked_run) (@RewriteAuditProofPlainPublic.rw_connect_class).

(** The exact rw_tracked_tick_projection type specializes the fixed plain computation. *)
Definition rw_tracked_tick_projection_fixed_type : Prop :=
  @rw_tracked_tick_projection_contract
    (@RewriteAuditProofPlainPublic.rw_connect_class)
  (@RewriteAuditProofPlainPublic.rw_tracked_tick).

(** The exact rw_tracked_tick_congruence type specializes the fixed plain computation. *)
Definition rw_tracked_tick_congruence_fixed_type : Prop :=
  @rw_tracked_tick_congruence_contract
    (@RewriteAuditProofPlainPublic.rw_tracked_tick).

(** The exact rw_tracked_rebuild_trace_correct type specializes the fixed plain computation. *)
Definition rw_tracked_rebuild_trace_correct_fixed_type : Prop :=
  @rw_tracked_rebuild_trace_correct_contract
    (@RewriteAuditProofPlainPublic.rw_connect_class) (@RewriteAuditProofPlainPublic.rw_tracked_tick)
  (@RewriteAuditProofPlainPublic.rw_tracked_rebuild).

(** The exact rw_tracked_apply_projects type specializes the fixed plain computation. *)
Definition rw_tracked_apply_projects_fixed_type : Prop :=
  @rw_tracked_apply_projects_contract
    (@RewriteAuditIndexPlainPublic.rw_index_rule_step)
  (@RewriteAuditProofPlainPublic.rw_connect_class)
  (@RewriteAuditProofPlainPublic.rw_tracked_rebuild)
  (@RewriteAuditProofPlainPublic.rw_tracked_rule_step).

(** The exact rw_tracked_factful_apply_reject type specializes the fixed plain computation. *)
Definition rw_tracked_factful_apply_reject_fixed_type : Prop :=
  @rw_tracked_factful_apply_reject_contract
    (@RewriteAuditProofPlainPublic.rw_tracked_rebuild)
  (@RewriteAuditProofPlainPublic.rw_tracked_rule_step).

(** The exact rw_tracked_factful_apply_accept type specializes the fixed plain computation. *)
Definition rw_tracked_factful_apply_accept_fixed_type : Prop :=
  @rw_tracked_factful_apply_accept_contract
    (@RewriteAuditProofPlainPublic.rw_tracked_rebuild)
  (@RewriteAuditProofPlainPublic.rw_tracked_rule_step).

(** The exact rw_factful_run_zero type specializes the fixed plain computation. *)
Definition rw_factful_run_zero_fixed_type : Prop :=
  @rw_factful_run_zero_contract
    (@RewriteAuditProofPlainPublic.rw_factful_run).

(** The exact rw_factful_run_valid type specializes the fixed plain computation. *)
Definition rw_factful_run_valid_fixed_type : Prop :=
  @rw_factful_run_valid_contract
    (@RewriteAuditProofPlainPublic.rw_factful_run).

(** The exact rw_factful_run_callback_bound type specializes the fixed plain computation. *)
Definition rw_factful_run_callback_bound_fixed_type : Prop :=
  @rw_factful_run_callback_bound_contract
    (@RewriteAuditProofPlainPublic.rw_factful_run).

(** The exact rw_rp_repr_realizes type specializes the fixed plain computation. *)
Definition rw_rp_repr_realizes_fixed_type : Prop :=
  @rw_rp_repr_realizes_statement
    (@RewriteAuditProofPlainPublic.rw_repr_find).

(** The exact rw_rp_connect_realizes type specializes the fixed plain computation. *)
Definition rw_rp_connect_realizes_fixed_type : Prop :=
  @rw_rp_connect_realizes_statement
    (@RewriteAuditProofPlainPublic.rw_connect_class).

(** The exact rw_rp_tick_realizes type specializes the fixed plain computation. *)
Definition rw_rp_tick_realizes_fixed_type : Prop :=
  @rw_rp_tick_realizes_statement
    (@RewriteAuditProofPlainPublic.rw_tracked_tick).

(** The exact rw_rp_rebuild_realizes type specializes the fixed plain computation. *)
Definition rw_rp_rebuild_realizes_fixed_type : Prop :=
  @rw_rp_rebuild_realizes_statement
    (@RewriteAuditProofPlainPublic.rw_tracked_rebuild).

(** The exact rw_rp_rule_step_realizes type specializes the fixed plain computation. *)
Definition rw_rp_rule_step_realizes_fixed_type : Prop :=
  @rw_rp_rule_step_realizes_statement
    (@RewriteAuditProofPlainPublic.rw_tracked_rule_step).

(** The exact rw_rp_apply_realizes type specializes the fixed plain computation. *)
Definition rw_rp_apply_realizes_fixed_type : Prop :=
  @rw_rp_apply_realizes_statement
    (@RewriteAuditProofPlainPublic.rw_tracked_rebuild)
  (@RewriteAuditProofPlainPublic.rw_tracked_rule_step).

(** The exact rw_rp_factful_apply_realizes type specializes the fixed plain computation. *)
Definition rw_rp_factful_apply_realizes_fixed_type : Prop :=
  @rw_rp_factful_apply_realizes_statement
    (@RewriteAuditProofPlainPublic.rw_tracked_rebuild)
  (@RewriteAuditProofPlainPublic.rw_tracked_rule_step).

(** The exact rw_rp_fact_run_realizes type specializes the fixed plain computation. *)
Definition rw_rp_fact_run_realizes_fixed_type : Prop :=
  @rw_rp_fact_run_realizes_statement
    (@RewriteAuditProofPlainPublic.rw_factful_run).
```

## Galois.Rewrite.RewriteAuditSharedFixedContracts

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditSharedFixedContracts.v`.

```rocq
(** * RewriteAuditSharedFixedContracts

    These types fix public contracts to the actual plain source bodies.
    For example, no arbitrary same-value producer can replace the accepted rule body.
    Builds on: fixed source schemas, plain computations and own library termination types. *)

From Stdlib Require Import List Bool PArith NArith.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditSharedInterfaceRdCompareRealizesStatement
  RewriteAuditSharedInterfaceRdExtractRealizesStatement
  RewriteAuditSharedInterfaceRdScalarRealizesStatement
  RewriteAuditSharedInterfaceSharedCompareAgreesContract
  RewriteAuditSharedInterfaceSharedCompareRejectContract
  RewriteAuditSharedInterfaceSharedExtractUnfoldContract
  RewriteAuditSharedInterfaceSharedObserversRejectContract
  RewriteAuditSharedInterfaceSharedTreeCostAgreesContract
  RewriteAuditSharedInterfaceSharedTreeCostBinaryAgreesContract
  RewriteAuditSharedInterfaceSharedTreeSizeBinaryAgreesContract RewriteAuditSharedPlain.
Import List.ListNotations.
Local Coercion encode : encoding >-> Funclass.

(** The exact rw_rd_compare_realizes type specializes the fixed plain computation. *)
Definition rw_rd_compare_realizes_fixed_type (Hwf : rw_rd_plain_compare_well_founded_type) : Prop :=
  @rw_rd_compare_realizes_statement
    (@RewriteAuditSharedPlain.rw_shared_compare_builder Hwf).

(** The exact rw_rd_extract_realizes type specializes the fixed plain computation. *)
Definition rw_rd_extract_realizes_fixed_type (Hwf : rw_rd_plain_compare_well_founded_type) : Prop :=
  @rw_rd_extract_realizes_statement
    (@RewriteAuditSharedPlain.rw_shared_extract_builder Hwf).

(** The exact rw_rd_scalar_realizes type specializes the fixed plain computation. *)
Definition rw_rd_scalar_realizes_fixed_type : Prop :=
  @rw_rd_scalar_realizes_statement
    (@RewriteAuditSharedPlain.rw_shared_tree_cost)
  (@RewriteAuditSharedPlain.rw_shared_tree_cost_binary)
  (@RewriteAuditSharedPlain.rw_shared_tree_size_binary).

(** The exact rw_shared_compare_agrees type specializes the fixed plain computation. *)
Definition rw_shared_compare_agrees_fixed_type (Hwf : rw_rd_plain_compare_well_founded_type) :
  Prop :=
  @rw_shared_compare_agrees_contract
    (@RewriteAuditSharedPlain.rw_shared_compare_builder Hwf).

(** The exact rw_shared_compare_reject type specializes the fixed plain computation. *)
Definition rw_shared_compare_reject_fixed_type (Hwf : rw_rd_plain_compare_well_founded_type) :
  Prop :=
  @rw_shared_compare_reject_contract
    (@RewriteAuditSharedPlain.rw_shared_compare_builder Hwf).

(** The exact rw_shared_extract_unfold type specializes the fixed plain computation. *)
Definition rw_shared_extract_unfold_fixed_type (Hwf : rw_rd_plain_compare_well_founded_type) :
  Prop :=
  @rw_shared_extract_unfold_contract
    (@RewriteAuditSharedPlain.rw_shared_extract_builder Hwf).

(** The exact rw_shared_tree_cost_agrees type specializes the fixed plain computation. *)
Definition rw_shared_tree_cost_agrees_fixed_type : Prop :=
  @rw_shared_tree_cost_agrees_contract
    (@RewriteAuditSharedPlain.rw_shared_tree_cost).

(** The exact rw_shared_tree_cost_binary_agrees type specializes the fixed plain computation. *)
Definition rw_shared_tree_cost_binary_agrees_fixed_type : Prop :=
  @rw_shared_tree_cost_binary_agrees_contract
    (@RewriteAuditSharedPlain.rw_shared_tree_cost_binary).

(** The exact rw_shared_tree_size_binary_agrees type specializes the fixed plain computation. *)
Definition rw_shared_tree_size_binary_agrees_fixed_type : Prop :=
  @rw_shared_tree_size_binary_agrees_contract
    (@RewriteAuditSharedPlain.rw_shared_tree_size_binary).

(** The exact rw_shared_observers_reject type specializes the fixed plain computation. *)
Definition rw_shared_observers_reject_fixed_type : Prop :=
  @rw_shared_observers_reject_contract
    (@RewriteAuditSharedPlain.rw_shared_tree_cost)
  (@RewriteAuditSharedPlain.rw_shared_tree_cost_binary)
  (@RewriteAuditSharedPlain.rw_shared_tree_size_binary).
```

## Galois.Rewrite.RewriteAuditIndexPublicSource

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditIndexPublicSource.v`.

```rocq
(** * Fixed public Rewrite source family

    The root requires own termination proofs and concrete producer/source cost correspondence.
    For example, a public optimizer result and its ceiling use the same source-run witness.
    Builds on: fixed plain builders, exact public contracts and full source cost models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexDimensions4 RewriteAuditIndexExternal
  RewriteAuditIndexPlainPublic RewriteAuditIndexPrepareReference RewriteAuditIndexProgramLaws
  RewriteAuditIndexPrograms RewriteAuditIndexReference RewriteAuditIndexRules
  RewriteAuditIndexRun RewriteAuditIndexTickReference RewriteAuditIndexWholeContracts
  RewriteAuditPlainCore1 RewriteAuditPlainPrimitives RewriteAuditQueueReference.
Import List.ListNotations.
Local Coercion encode : encoding >-> Funclass.

(** The actual public indexed result has one matching source work witness and its own ceiling. *)
Definition rw_ri_public_source_cost_statement : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) (sig : rw_signature K Sort V)
    rules adapter strategy execution fuel graph width body,
  (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
  (forall s, fst (rw_queue_encoder_run sort s) = encode ES s) ->
  (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
  (forall h, fst (rw_queue_encoder_run hole h) = encode EH h) ->
  rw_rp_callbacks_agree EH sig callbacks rules -> Forall (rw_rule_wf sig) rules ->
  rw_rp_strategy_adapter_laws EK ES EV adapter strategy (execution strategy) ->
  let actual := RewriteAuditIndexPlainPublic.rw_index_run EK ES EV EH sig rules strategy fuel
  graph in
  let '(result, initial_events, events) := actual in
  rw_whole_graph_atoms op sort value width body graph ->
  rw_whole_rules_external op sort value hole callbacks width body rules ->
  (let table := rw_plain_rw_rp_rule_table_atomic rules 0 in
   let ready := fst (rw_index_rebuild EK ES EV (rw_index_build EK ES EV graph)) in
   forall n, (N.of_nat n < fuel)%N ->
   let run := Nat.iter n
     (rw_plain_rw_ri_run_once EK ES EV EH (rw_plain_callbacks_of sig) table
       (fun state => strategy (rw_index_view EK ES EV state))) (RwRiRunner ready false nil) in
   rw_ri_runner_stopped run = false ->
   let view := rw_index_view EK ES EV (rw_ri_runner_state run) in
   rw_whole_view_control view (rw_rp_strategy_program adapter) <= body /\
   rw_whole_view_queries op value width body view (rw_rp_strategy_program adapter) /\
   match rw_rp_view_plain view (rw_rp_strategy_program adapter) with
   | None => True
   | Some attempt => rw_whole_attempt_external EH op sort value hole callbacks width body rules
  attempt
   end) ->
  exists work,
    rw_ri_run_atomic op sort value hole callbacks rules adapter fuel graph = (actual, work) /\
    (N.of_nat work <= rw_whole_source_ceiling fuel
      (rw_ri_whole_operand_dimension rules graph result events) width body)%N.

(** The actual tracked root, state and events share the source work witness used by the bound. *)
```

## Galois.Rewrite.RewriteAuditProofPublicSource

Card: AUD-RW-MODELS

Source destination: `theories/Rewrite/RewriteAuditProofPublicSource.v`.

```rocq
(** * Fixed public Rewrite source family

    The root requires own termination proofs and concrete producer/source cost correspondence.
    For example, a public optimizer result and its ceiling use the same source-run witness.
    Builds on: fixed plain builders, exact public contracts and full source cost models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexDimensions RewriteAuditIndexDimensions4
  RewriteAuditIndexExternal RewriteAuditIndexProgramLaws RewriteAuditIndexPrograms
  RewriteAuditIndexReference RewriteAuditIndexRules RewriteAuditPlainCore1
  RewriteAuditPlainCore3 RewriteAuditPlainCore4 RewriteAuditPlainPrimitives
  RewriteAuditProofDimensions2 RewriteAuditProofDimensions3 RewriteAuditProofFactPublic
  RewriteAuditProofFactWholeContracts RewriteAuditProofFacts RewriteAuditProofPlainPublic
  RewriteAuditProofRun RewriteAuditProofSelected RewriteAuditProofSemantic RewriteAuditProofTick
  RewriteAuditProofWholeContracts RewriteAuditQueueReference.
Import List.ListNotations.
Local Coercion encode : encoding >-> Funclass.

(** The actual public indexed result has one matching source work witness and its own ceiling. *)
Definition rw_rp_public_source_cost_statement : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) (sig : rw_signature K Sort V)
    rules adapter strategy execution fuel seed width body,
  (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
  (forall s, fst (rw_queue_encoder_run sort s) = encode ES s) ->
  (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
  (forall h, fst (rw_queue_encoder_run hole h) = encode EH h) ->
  rw_rp_callbacks_agree EH sig callbacks rules -> Forall (rw_rule_wf sig) rules ->
  rw_typed sig seed -> rw_rp_strategy_adapter_laws EK ES EV adapter strategy (execution strategy) ->
  let actual := RewriteAuditProofPlainPublic.rw_tracked_run EK ES EV EH sig rules strategy fuel
  seed in
  rw_whole_term_atoms op sort value width body seed ->
  rw_whole_rules_external op sort value hole callbacks width body rules ->
  (let table := rw_plain_rw_rp_rule_table_atomic rules 0 in
   let initial := snd (@rw_plain_rw_rp_seed_atomic K Sort V H EK ES EV EK EV seed) in
   let ready := fst (RewriteAuditProofPlainPublic.rw_tracked_rebuild EK ES EV 0 initial) in
   forall n, (N.of_nat n < fuel)%N ->
   let run := Nat.iter n
     (rw_plain_rw_rp_run_once EK ES EV EK ES EV EH (rw_plain_callbacks_of sig) table
       (fun state => strategy (rw_index_view EK ES EV state))) (RwRpRunState ready false 0 nil) in
   rw_rp_stopped run = false ->
   let view := rw_index_view EK ES EV (rw_tracked_machine (rw_rp_current run)) in
   rw_whole_view_control view (rw_rp_strategy_program adapter) <= body /\
   rw_whole_view_queries op value width body view (rw_rp_strategy_program adapter) /\
   match rw_rp_view_plain view (rw_rp_strategy_program adapter) with
   | None => True
   | Some attempt => rw_whole_attempt_external EH op sort value hole callbacks width body rules
  attempt
   end) ->
  exists work,
    rw_rp_run_atomic EK ES EV op sort value hole callbacks rules adapter fuel seed = (actual,
  work) /\
    (N.of_nat work <= rw_whole_source_ceiling fuel
      (rw_rp_whole_operand_dimension rules seed (snd actual)) width body)%N.

(** The selected public proof, including rejection, shares its source work and finite-term
  ceiling. *)
Definition rw_rp_public_selected_source_cost_statement : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (state : rw_tracked_state K Sort V H)
    root seed tree width body,
  (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
  (forall s, fst (rw_queue_encoder_run sort s) = encode ES s) ->
  (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
  rw_whole_index_atoms op sort value width body (rw_tracked_machine state) ->
  rw_whole_provenance_atoms op sort value width body (rw_tracked_provenance state) ->
  rw_whole_term_atoms op sort value width body seed ->
  rw_whole_term_atoms op sort value width body tree ->
  let actual := RewriteAuditProofPlainPublic.rw_selected_explanation EK ES EV state root seed
  tree in
  let dimension := S (rw_whole_tracked_dimension state + Pos.size_nat root +
    rw_whole_term_dimension seed + rw_whole_term_dimension tree + width) in
  exists work,
    rw_rp_selected_atomic op sort value state root seed tree = (actual, work) /\
    (N.of_nat work <= 4294967296 * (1 + N.of_nat body) * N.pow (N.of_nat dimension)
      (128 + 16 * N.of_nat (rw_whole_term_dimension seed + rw_whole_term_dimension tree)))%N.

(** The actual fact-safe result and retained map share one source witness and its own ceiling. *)
Definition rw_rp_public_fact_source_cost_statement : Prop :=
  forall K Sort V H C F (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) (sig : rw_signature K Sort V)
    rules (an : rw_analysis K Sort V C F) adapter strategy execution fuel initial facts width body,
  (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
  (forall s, fst (rw_queue_encoder_run sort s) = encode ES s) ->
  (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
  (forall h, fst (rw_queue_encoder_run hole h) = encode EH h) ->
  rw_rp_callbacks_agree EH sig callbacks rules -> Forall (rw_rule_wf sig) rules ->
  rw_rp_fact_strategy_agrees EK ES EV an adapter strategy ->
  (forall (state : rw_tracked_state K Sort V H) facts,
    execution strategy (rw_fact_observe EK ES EV an state facts)
      (rw_rp_fact_strategy_program adapter)) ->
  let actual := RewriteAuditProofPlainPublic.rw_factful_run EK ES EV EH sig rules an strategy fuel
    (initial, facts) in
  rw_whole_tracked_atoms op sort value width body initial ->
  rw_whole_rules_external op sort value hole callbacks width body rules ->
  (let table := rw_plain_rw_rp_rule_table_atomic rules 0 in
   let ready := fst (RewriteAuditProofPlainPublic.rw_tracked_rebuild EK ES EV 0 initial) in
   let callback := fun state unknown retained => strategy
     (RWFactView (rw_index_view EK ES EV state)
       (fun id => match Map.get positive_encoding id retained with
         | Some fact => fact | None => unknown end)) in
   forall n, (N.of_nat n < fuel)%N ->
   let '(run, retained) := Nat.iter n
     (rw_plain_rw_rp_fact_run_once EK ES EV EK ES EV EH (rw_plain_callbacks_of sig) table
       (rw_fact_unknown an) callback) (RwRpRunState ready false 0 nil, Map.empty) in
   rw_rp_stopped run = false ->
   let view := rw_index_view EK ES EV (rw_tracked_machine (rw_rp_current run)) in
   rw_whole_fact_control view (rw_fact_unknown an) (rw_rp_fact_strategy_program adapter) <= body /\
   rw_whole_fact_queries op value width body view (rw_fact_unknown an)
     (rw_rp_fact_strategy_program adapter) /\
   match rw_rp_fact_plain view
     (fun id => match Map.get positive_encoding id retained with
       | Some fact => fact | None => rw_fact_unknown an end) (rw_rp_fact_strategy_program
  adapter) with
   | None => True
   | Some attempt => rw_whole_attempt_external EH op sort value hole callbacks width body rules
  attempt
   end) ->
  exists work,
    rw_rp_fact_run_atomic EK ES EV op sort value hole callbacks rules (rw_fact_unknown an)
      adapter fuel (initial, facts) = (actual, work) /\
    (N.of_nat work <= rw_whole_source_ceiling fuel
      (rw_fact_whole_operand_dimension rules initial facts (fst actual) (snd actual)) width body)%N.

(** The fixed tracked facade builder has an actual source run with the same value and work
  ceiling. *)
```

### Future proofs in `RewriteAuditIndexBucketAdequacy`

Card: AUD-RI

Source destination: `theories/Rewrite/RewriteAuditIndexBucketAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditIndexBucket.

Theorem rw_ri_bucket_add_erases :
  RewriteAuditIndexBucket.rw_ri_bucket_add_erases_contract.
Theorem rw_ri_bucket_remove_erases :
  RewriteAuditIndexBucket.rw_ri_bucket_remove_erases_contract.
Theorem rw_ri_bucket_add_bound :
  RewriteAuditIndexBucket.rw_ri_bucket_add_bound_contract.
Theorem rw_ri_bucket_remove_bound :
  RewriteAuditIndexBucket.rw_ri_bucket_remove_bound_contract.
```

### Future proofs in `RewriteAuditIndexCompareAdequacy`

Card: AUD-RI

Source destination: `theories/Rewrite/RewriteAuditIndexCompareAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditIndexCompare.

Theorem rw_ri_positive_dec_erases :
  RewriteAuditIndexCompare.rw_ri_positive_dec_erases_contract.
Theorem rw_ri_positive_dec_bound :
  RewriteAuditIndexCompare.rw_ri_positive_dec_bound_contract.
```

### Future proofs in `RewriteAuditIndexDirtyAdequacy`

Card: AUD-RI

Source destination: `theories/Rewrite/RewriteAuditIndexDirtyAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditIndexDirty.

Theorem rw_ri_dirty_client :
  RewriteAuditIndexDirty.rw_ri_dirty_client_contract.
```

### Future proofs in `RewriteAuditIndexFindAdequacy`

Card: AUD-RI

Source destination: `theories/Rewrite/RewriteAuditIndexFindAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditIndexFind.

Theorem rw_ri_find_erases :
  RewriteAuditIndexFind.rw_ri_find_erases_contract.
Theorem rw_ri_find_bound :
  RewriteAuditIndexFind.rw_ri_find_bound_contract.
Theorem rw_ri_canon_erases :
  RewriteAuditIndexFind.rw_ri_canon_erases_contract.
Theorem rw_ri_canon_bound :
  RewriteAuditIndexFind.rw_ri_canon_bound_contract.
```

### Future proofs in `RewriteAuditIndexMarkAdequacy`

Card: AUD-RI

Source destination: `theories/Rewrite/RewriteAuditIndexMarkAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditIndexMark.

Theorem rw_ri_mark_erases :
  RewriteAuditIndexMark.rw_ri_mark_erases_contract.
Theorem rw_ri_mark_bound :
  RewriteAuditIndexMark.rw_ri_mark_bound_contract.
```

### Future proofs in `RewriteAuditIndexMatchAdequacy`

Card: AUD-RI

Source destination: `theories/Rewrite/RewriteAuditIndexMatchAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditIndexMatch.

Theorem rw_ri_match_erases :
  RewriteAuditIndexMatch.rw_ri_match_erases_statement.
```

### Future proofs in `RewriteAuditIndexMatchReferenceAdequacy`

Card: AUD-RI

Source destination: `theories/Rewrite/RewriteAuditIndexMatchReferenceAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditIndexMatchReference.

Theorem rw_view_match_sound :
  RewriteAuditIndexMatchReference.rw_view_match_sound_contract.
Theorem rw_view_match_complete :
  RewriteAuditIndexMatchReference.rw_view_match_complete_contract.
Theorem rw_view_match_assignment :
  RewriteAuditIndexMatchReference.rw_view_match_assignment_contract.
Theorem rw_view_match_nodup :
  RewriteAuditIndexMatchReference.rw_view_match_nodup_contract.
```

### Future proofs in `RewriteAuditIndexMembershipAdequacy`

Card: AUD-RI

Source destination: `theories/Rewrite/RewriteAuditIndexMembershipAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditIndexMembership.

Theorem rw_ri_member_spec :
  RewriteAuditIndexMembership.rw_ri_member_spec_statement.
```

### Future proofs in `RewriteAuditIndexInterfaceIndexRuleStepSupportedContractAdequacy`

Card: AUD-RI

Source destination:
  `theories/Rewrite/RewriteAuditIndexInterfaceIndexRuleStepSupportedContractAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditIndexPlainContracts.

Theorem rw_index_rule_step_supported :
  RewriteAuditIndexPlainContracts.rw_index_rule_step_supported_fixed_type.
```

### Future proofs in `RewriteAuditIndexInterfaceIndexRunCallbackBoundContractAdequacy`

Card: AUD-RI

Source destination:
  `theories/Rewrite/RewriteAuditIndexInterfaceIndexRunCallbackBoundContractAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditIndexPlainContracts.

Theorem rw_index_run_callback_bound :
  RewriteAuditIndexPlainContracts.rw_index_run_callback_bound_fixed_type.
```

### Future proofs in `RewriteAuditIndexInterfaceIndexRunCleanTraceContractAdequacy`

Card: AUD-RI

Source destination:
  `theories/Rewrite/RewriteAuditIndexInterfaceIndexRunCleanTraceContractAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditIndexPlainContracts.

Theorem rw_index_run_clean_trace :
  RewriteAuditIndexPlainContracts.rw_index_run_clean_trace_fixed_type.
```

### Future proofs in `RewriteAuditIndexInterfaceIndexRunCorrectContractAdequacy`

Card: AUD-RI

Source destination: `theories/Rewrite/RewriteAuditIndexInterfaceIndexRunCorrectContractAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditIndexPlainContracts.

Theorem rw_index_run_correct :
  RewriteAuditIndexPlainContracts.rw_index_run_correct_fixed_type.
```

### Future proofs in `RewriteAuditIndexInterfaceIndexRunZeroContractAdequacy`

Card: AUD-RI

Source destination: `theories/Rewrite/RewriteAuditIndexInterfaceIndexRunZeroContractAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditIndexPlainContracts.

Theorem rw_index_run_zero :
  RewriteAuditIndexPlainContracts.rw_index_run_zero_fixed_type.
```

### Future proofs in `RewriteAuditIndexInterfaceRiApplyRealizesStatementAdequacy`

Card: AUD-RI

Source destination: `theories/Rewrite/RewriteAuditIndexInterfaceRiApplyRealizesStatementAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditIndexPlainContracts.

Theorem rw_ri_apply_realizes :
  RewriteAuditIndexPlainContracts.rw_ri_apply_realizes_fixed_type.
```

### Future proofs in `RewriteAuditIndexInterfaceRiRuleStepRealizesStatementAdequacy`

Card: AUD-RI

Source destination:
  `theories/Rewrite/RewriteAuditIndexInterfaceRiRuleStepRealizesStatementAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditIndexPlainContracts.

Theorem rw_ri_rule_step_realizes :
  RewriteAuditIndexPlainContracts.rw_ri_rule_step_realizes_fixed_type.
```

### Future proofs in `RewriteAuditIndexInterfaceRiRunRealizesStatementAdequacy`

Card: AUD-RI

Source destination: `theories/Rewrite/RewriteAuditIndexInterfaceRiRunRealizesStatementAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditIndexPlainContracts.

Theorem rw_ri_run_realizes :
  RewriteAuditIndexPlainContracts.rw_ri_run_realizes_fixed_type.
```

### Future proofs in `RewriteAuditIndexPreparationContractsAdequacy`

Card: AUD-RI

Source destination: `theories/Rewrite/RewriteAuditIndexPreparationContractsAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditIndexPreparationContracts.

Theorem rw_ri_prepare_once_bound :
  RewriteAuditIndexPreparationContracts.rw_ri_prepare_once_bound_statement.
```

### Future proofs in `RewriteAuditIndexPrepareAdequacy`

Card: AUD-RI

Source destination: `theories/Rewrite/RewriteAuditIndexPrepareAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditIndexPrepare.

Theorem rw_ri_prepare_once_erases :
  RewriteAuditIndexPrepare.rw_ri_prepare_once_erases_statement.
Theorem rw_ri_prepare_once_receipts :
  RewriteAuditIndexPrepare.rw_ri_prepare_once_receipts_statement.
```

### Future proofs in `RewriteAuditIndexPublicAdequacy`

Card: AUD-RI

Source destination: `theories/Rewrite/RewriteAuditIndexPublicAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditIndexPublic.

Theorem rw_index_clean :
  RewriteAuditIndexPublic.rw_index_clean_contract.
Theorem rw_index_sound :
  RewriteAuditIndexPublic.rw_index_sound_contract.
Theorem rw_index_witness :
  RewriteAuditIndexPublic.rw_index_witness_contract.
Theorem index_supported_cardinality :
  RewriteAuditIndexPublic.index_supported_cardinality_contract.
Theorem index_member_node_bound :
  RewriteAuditIndexPublic.index_member_node_bound_contract.
Theorem rw_index_build_supported :
  RewriteAuditIndexPublic.rw_index_build_supported_contract.
Theorem rw_index_tick_supported :
  RewriteAuditIndexPublic.rw_index_tick_supported_contract.
```

### Future proofs in `RewriteAuditIndexPublicSourceAdequacy`

Card: AUD-RI

Source destination: `theories/Rewrite/RewriteAuditIndexPublicSourceAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditIndexPublicSource.

Theorem rw_ri_public_source_cost :
  RewriteAuditIndexPublicSource.rw_ri_public_source_cost_statement.
```

### Future proofs in `RewriteAuditIndexRebuildAdequacy`

Card: AUD-RI

Source destination: `theories/Rewrite/RewriteAuditIndexRebuildAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditIndexRebuild.

Theorem rw_ri_tick_erases :
  RewriteAuditIndexRebuild.rw_ri_tick_erases_statement.
Theorem rw_ri_repeat_erases :
  RewriteAuditIndexRebuild.rw_ri_repeat_erases_statement.
Theorem rw_ri_repeat_tick_bound :
  RewriteAuditIndexRebuild.rw_ri_repeat_tick_bound_statement.
Theorem rw_ri_graph_erases :
  RewriteAuditIndexRebuild.rw_ri_graph_erases_statement.
Theorem rw_ri_rebuild_fuel_erases :
  RewriteAuditIndexRebuild.rw_ri_rebuild_fuel_erases_statement.
Theorem rw_ri_rebuild_erases :
  RewriteAuditIndexRebuild.rw_ri_rebuild_erases_statement.
Theorem rw_ri_pair_erases :
  RewriteAuditIndexRebuild.rw_ri_pair_erases_statement.
```

### Future proofs in `RewriteAuditIndexReferenceAdequacy`

Card: AUD-RI

Source destination: `theories/Rewrite/RewriteAuditIndexReferenceAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditIndexReference.

Theorem rw_snapshot_extract_agrees :
  RewriteAuditIndexReference.rw_snapshot_extract_agrees_contract.
```

### Future proofs in `RewriteAuditIndexRuleTableContractsAdequacy`

Card: AUD-RI

Source destination: `theories/Rewrite/RewriteAuditIndexRuleTableContractsAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditIndexRuleTableContracts.

Theorem rw_rp_rule_table_bound :
  RewriteAuditIndexRuleTableContracts.rw_rp_rule_table_bound_statement.
```

### Future proofs in `RewriteAuditIndexRulesAdequacy`

Card: AUD-RI

Source destination: `theories/Rewrite/RewriteAuditIndexRulesAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditIndexRules.

Theorem rw_rp_rule_table_erases :
  RewriteAuditIndexRules.rw_rp_rule_table_erases_statement.
Theorem rw_rp_instantiate_erases :
  RewriteAuditIndexRules.rw_rp_instantiate_erases_statement.
```

### Future proofs in `RewriteAuditIndexRunAdequacy`

Card: AUD-RI

Source destination: `theories/Rewrite/RewriteAuditIndexRunAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditIndexRun.

Theorem rw_ri_run_zero_source :
  RewriteAuditIndexRun.rw_ri_run_zero_source_statement.
Theorem rw_ri_run_semantic :
  RewriteAuditIndexRun.rw_ri_run_semantic_statement.
```

### Future proofs in `RewriteAuditIndexWholeContractsAdequacy`

Card: AUD-RI

Source destination: `theories/Rewrite/RewriteAuditIndexWholeContractsAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditIndexWholeContracts.

Theorem rw_ri_whole_bound :
  RewriteAuditIndexWholeContracts.rw_ri_whole_bound_statement.
Theorem rw_ri_match_bound :
  RewriteAuditIndexWholeContracts.rw_ri_match_bound_statement.
```

### Future proofs in `RewriteAuditProofCarrierAdequacy`

Card: AUD-RP-CORE

Source destination: `theories/Rewrite/RewriteAuditProofCarrierAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditProofCarrier.

Theorem rw_provenance_sound :
  RewriteAuditProofCarrier.rw_provenance_sound_contract.
```

### Future proofs in `RewriteAuditProofClosureAdequacy`

Card: AUD-RP-CORE

Source destination: `theories/Rewrite/RewriteAuditProofClosureAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditProofClosure.

Theorem rw_rp_term_key_agrees :
  RewriteAuditProofClosure.rw_rp_term_key_agrees_statement.
Theorem rw_rp_connect_complete :
  RewriteAuditProofClosure.rw_rp_connect_complete_statement.
Theorem rw_rp_connect_sound :
  RewriteAuditProofClosure.rw_rp_connect_sound_statement.
```

### Future proofs in `RewriteAuditProofFactPublicAdequacy`

Card: AUD-RP-CORE

Source destination: `theories/Rewrite/RewriteAuditProofFactPublicAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditProofFactPublic.

Theorem rw_rp_fact_run_valid :
  RewriteAuditProofFactPublic.rw_rp_fact_run_valid_statement.
Theorem rw_rp_fact_callback_bound :
  RewriteAuditProofFactPublic.rw_rp_fact_callback_bound_statement.
```

### Future proofs in `RewriteAuditProofFactWholeContractsAdequacy`

Card: AUD-RP-CORE

Source destination: `theories/Rewrite/RewriteAuditProofFactWholeContractsAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditProofFactWholeContracts.

Theorem rw_rp_fact_whole_bound :
  RewriteAuditProofFactWholeContracts.rw_rp_fact_whole_bound_statement.
```

### Future proofs in `RewriteAuditProofFactsAdequacy`

Card: AUD-RP-CORE

Source destination: `theories/Rewrite/RewriteAuditProofFactsAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditProofFacts.

Theorem rw_rp_fact_initial_invalidation :
  RewriteAuditProofFacts.rw_rp_fact_initial_invalidation_statement.
```

### Future proofs in `RewriteAuditProofInterfaceFactfulRunCallbackBoundContractAdequacy`

Card: AUD-RP-CORE

Source destination:
  `theories/Rewrite/RewriteAuditProofInterfaceFactfulRunCallbackBoundContractAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditProofPlainContracts.

Theorem rw_factful_run_callback_bound :
  RewriteAuditProofPlainContracts.rw_factful_run_callback_bound_fixed_type.
```

### Future proofs in `RewriteAuditProofInterfaceFactfulRunValidContractAdequacy`

Card: AUD-RP-CORE

Source destination: `theories/Rewrite/RewriteAuditProofInterfaceFactfulRunValidContractAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditProofPlainContracts.

Theorem rw_factful_run_valid :
  RewriteAuditProofPlainContracts.rw_factful_run_valid_fixed_type.
```

### Future proofs in `RewriteAuditProofInterfaceFactfulRunZeroContractAdequacy`

Card: AUD-RP-CORE

Source destination: `theories/Rewrite/RewriteAuditProofInterfaceFactfulRunZeroContractAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditProofPlainContracts.

Theorem rw_factful_run_zero :
  RewriteAuditProofPlainContracts.rw_factful_run_zero_fixed_type.
```

### Future proofs in `RewriteAuditProofInterfaceReprFindSpecContractAdequacy`

Card: AUD-RP-CORE

Source destination: `theories/Rewrite/RewriteAuditProofInterfaceReprFindSpecContractAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditProofPlainContracts.

Theorem rw_repr_find_spec :
  RewriteAuditProofPlainContracts.rw_repr_find_spec_fixed_type.
```

### Future proofs in `RewriteAuditProofInterfaceRpApplyRealizesStatementAdequacy`

Card: AUD-RP-CORE

Source destination: `theories/Rewrite/RewriteAuditProofInterfaceRpApplyRealizesStatementAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditProofPlainContracts.

Theorem rw_rp_apply_realizes :
  RewriteAuditProofPlainContracts.rw_rp_apply_realizes_fixed_type.
```

### Future proofs in `RewriteAuditProofInterfaceRpConnectRealizesStatementAdequacy`

Card: AUD-RP-CORE

Source destination:
  `theories/Rewrite/RewriteAuditProofInterfaceRpConnectRealizesStatementAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditProofPlainContracts.

Theorem rw_rp_connect_realizes :
  RewriteAuditProofPlainContracts.rw_rp_connect_realizes_fixed_type.
```

### Future proofs in `RewriteAuditProofInterfaceRpFactRunRealizesStatementAdequacy`

Card: AUD-RP-CORE

Source destination:
  `theories/Rewrite/RewriteAuditProofInterfaceRpFactRunRealizesStatementAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditProofPlainContracts.

Theorem rw_rp_fact_run_realizes :
  RewriteAuditProofPlainContracts.rw_rp_fact_run_realizes_fixed_type.
```

### Future proofs in `RewriteAuditProofInterfaceRpFactfulApplyRealizesStatementAdequacy`

Card: AUD-RP-CORE

Source destination:
  `theories/Rewrite/RewriteAuditProofInterfaceRpFactfulApplyRealizesStatementAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditProofPlainContracts.

Theorem rw_rp_factful_apply_realizes :
  RewriteAuditProofPlainContracts.rw_rp_factful_apply_realizes_fixed_type.
```

### Future proofs in `RewriteAuditProofInterfaceRpRebuildRealizesStatementAdequacy`

Card: AUD-RP-CORE

Source destination:
  `theories/Rewrite/RewriteAuditProofInterfaceRpRebuildRealizesStatementAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditProofPlainContracts.

Theorem rw_rp_rebuild_realizes :
  RewriteAuditProofPlainContracts.rw_rp_rebuild_realizes_fixed_type.
```

### Future proofs in `RewriteAuditProofInterfaceRpReprRealizesStatementAdequacy`

Card: AUD-RP-CORE

Source destination: `theories/Rewrite/RewriteAuditProofInterfaceRpReprRealizesStatementAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditProofPlainContracts.

Theorem rw_rp_repr_realizes :
  RewriteAuditProofPlainContracts.rw_rp_repr_realizes_fixed_type.
```

### Future proofs in `RewriteAuditProofInterfaceRpRuleStepRealizesStatementAdequacy`

Card: AUD-RP-CORE

Source destination:
  `theories/Rewrite/RewriteAuditProofInterfaceRpRuleStepRealizesStatementAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditProofPlainContracts.

Theorem rw_rp_rule_step_realizes :
  RewriteAuditProofPlainContracts.rw_rp_rule_step_realizes_fixed_type.
```

### Future proofs in `RewriteAuditProofInterfaceRpRunRealizesStatementAdequacy`

Card: AUD-RP-CORE

Source destination: `theories/Rewrite/RewriteAuditProofInterfaceRpRunRealizesStatementAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditProofPlainContracts.

Theorem rw_rp_run_realizes :
  RewriteAuditProofPlainContracts.rw_rp_run_realizes_fixed_type.
```

### Future proofs in `RewriteAuditProofInterfaceRpSelectedRealizesStatementAdequacy`

Card: AUD-RP-CORE

Source destination:
  `theories/Rewrite/RewriteAuditProofInterfaceRpSelectedRealizesStatementAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditProofPlainContracts.

Theorem rw_rp_selected_realizes :
  RewriteAuditProofPlainContracts.rw_rp_selected_realizes_fixed_type.
```

### Future proofs in `RewriteAuditProofInterfaceRpTickRealizesStatementAdequacy`

Card: AUD-RP-CORE

Source destination: `theories/Rewrite/RewriteAuditProofInterfaceRpTickRealizesStatementAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditProofPlainContracts.

Theorem rw_rp_tick_realizes :
  RewriteAuditProofPlainContracts.rw_rp_tick_realizes_fixed_type.
```

### Future proofs in `RewriteAuditProofInterfaceTrackedApplyProjectsContractAdequacy`

Card: AUD-RP-CORE

Source destination:
  `theories/Rewrite/RewriteAuditProofInterfaceTrackedApplyProjectsContractAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditProofPlainContracts.

Theorem rw_tracked_apply_projects :
  RewriteAuditProofPlainContracts.rw_tracked_apply_projects_fixed_type.
```

### Future proofs in `RewriteAuditProofInterfaceTrackedExtractableContractAdequacy`

Card: AUD-RP-CORE

Source destination:
  `theories/Rewrite/RewriteAuditProofInterfaceTrackedExtractableContractAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditProofPlainContracts.

Theorem rw_tracked_extractable :
  RewriteAuditProofPlainContracts.rw_tracked_extractable_fixed_type.
```

### Future proofs in `RewriteAuditProofInterfaceTrackedFactfulApplyAcceptContractAdequacy`

Card: AUD-RP-CORE

Source destination:
  `theories/Rewrite/RewriteAuditProofInterfaceTrackedFactfulApplyAcceptContractAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditProofPlainContracts.

Theorem rw_tracked_factful_apply_accept :
  RewriteAuditProofPlainContracts.rw_tracked_factful_apply_accept_fixed_type.
```

### Future proofs in `RewriteAuditProofInterfaceTrackedFactfulApplyRejectContractAdequacy`

Card: AUD-RP-CORE

Source destination:
  `theories/Rewrite/RewriteAuditProofInterfaceTrackedFactfulApplyRejectContractAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditProofPlainContracts.

Theorem rw_tracked_factful_apply_reject :
  RewriteAuditProofPlainContracts.rw_tracked_factful_apply_reject_fixed_type.
```

### Future proofs in `RewriteAuditProofInterfaceTrackedRebuildTraceCorrectContractAdequacy`

Card: AUD-RP-CORE

Source destination:
  `theories/Rewrite/RewriteAuditProofInterfaceTrackedRebuildTraceCorrectContractAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditProofPlainContracts.

Theorem rw_tracked_rebuild_trace_correct :
  RewriteAuditProofPlainContracts.rw_tracked_rebuild_trace_correct_fixed_type.
```

### Future proofs in `RewriteAuditProofInterfaceTrackedRunInvariantsContractAdequacy`

Card: AUD-RP-CORE

Source destination:
  `theories/Rewrite/RewriteAuditProofInterfaceTrackedRunInvariantsContractAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditProofPlainContracts.

Theorem rw_tracked_run_invariants :
  RewriteAuditProofPlainContracts.rw_tracked_run_invariants_fixed_type.
```

### Future proofs in `RewriteAuditProofInterfaceTrackedSelectedContractAdequacy`

Card: AUD-RP-CORE

Source destination: `theories/Rewrite/RewriteAuditProofInterfaceTrackedSelectedContractAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditProofPlainContracts.

Theorem rw_tracked_selected :
  RewriteAuditProofPlainContracts.rw_tracked_selected_fixed_type.
```

### Future proofs in `RewriteAuditProofInterfaceTrackedTickCongruenceContractAdequacy`

Card: AUD-RP-CORE

Source destination:
  `theories/Rewrite/RewriteAuditProofInterfaceTrackedTickCongruenceContractAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditProofPlainContracts.

Theorem rw_tracked_tick_congruence :
  RewriteAuditProofPlainContracts.rw_tracked_tick_congruence_fixed_type.
```

### Future proofs in `RewriteAuditProofInterfaceTrackedTickProjectionContractAdequacy`

Card: AUD-RP-CORE

Source destination:
  `theories/Rewrite/RewriteAuditProofInterfaceTrackedTickProjectionContractAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditProofPlainContracts.

Theorem rw_tracked_tick_projection :
  RewriteAuditProofPlainContracts.rw_tracked_tick_projection_fixed_type.
```

### Future proofs in `RewriteAuditProofPublicAdequacy`

Card: AUD-RP-CORE

Source destination: `theories/Rewrite/RewriteAuditProofPublicAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditProofPublic.

Theorem rw_rp_run_callback_bound :
  RewriteAuditProofPublic.rw_rp_run_callback_bound_statement.
Theorem rw_rp_run_zero :
  RewriteAuditProofPublic.rw_rp_run_zero_statement.
```

### Future proofs in `RewriteAuditProofPublicSourceAdequacy`

Card: AUD-RP-CORE

Source destination: `theories/Rewrite/RewriteAuditProofPublicSourceAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditProofPublicSource.

Theorem rw_rp_public_source_cost :
  RewriteAuditProofPublicSource.rw_rp_public_source_cost_statement.
Theorem rw_rp_public_selected_source_cost :
  RewriteAuditProofPublicSource.rw_rp_public_selected_source_cost_statement.
Theorem rw_rp_public_fact_source_cost :
  RewriteAuditProofPublicSource.rw_rp_public_fact_source_cost_statement.
```

### Future proofs in `RewriteAuditProofRebuildAdequacy`

Card: AUD-RP-CORE

Source destination: `theories/Rewrite/RewriteAuditProofRebuildAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditProofRebuild.

Theorem rw_rp_rebuild_projects :
  RewriteAuditProofRebuild.rw_rp_rebuild_projects_statement.
```

### Future proofs in `RewriteAuditProofRepresentationAdequacy`

Card: AUD-RP-CORE

Source destination: `theories/Rewrite/RewriteAuditProofRepresentationAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditProofRepresentation.

Theorem rw_rp_repr_find_spec :
  RewriteAuditProofRepresentation.rw_rp_repr_find_spec_statement.
```

### Future proofs in `RewriteAuditProofSeedAdequacy`

Card: AUD-RP-CORE

Source destination: `theories/Rewrite/RewriteAuditProofSeedAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditProofSeed.

Theorem rw_rp_seed_represents :
  RewriteAuditProofSeed.rw_rp_seed_represents_statement.
```

### Future proofs in `RewriteAuditProofSelectedAdequacy`

Card: AUD-RP-CORE

Source destination: `theories/Rewrite/RewriteAuditProofSelectedAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditProofSelected.

Theorem rw_rp_run_semantic :
  RewriteAuditProofSelected.rw_rp_run_semantic_statement.
Theorem rw_rp_selected_complete :
  RewriteAuditProofSelected.rw_rp_selected_complete_statement.
```

### Future proofs in `RewriteAuditProofSelectedContractsAdequacy`

Card: AUD-RP-CORE

Source destination: `theories/Rewrite/RewriteAuditProofSelectedContractsAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditProofSelectedContracts.

Theorem rw_rp_selected_bound :
  RewriteAuditProofSelectedContracts.rw_rp_selected_bound_statement.
Theorem rw_rp_repr_find_bound :
  RewriteAuditProofSelectedContracts.rw_rp_repr_find_bound_statement.
```

### Future proofs in `RewriteAuditProofSemanticAdequacy`

Card: AUD-RP-CORE

Source destination: `theories/Rewrite/RewriteAuditProofSemanticAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditProofSemantic.

Theorem rw_facts_invalidate_sound :
  RewriteAuditProofSemantic.rw_facts_invalidate_sound_contract.
Theorem rw_fact_store_total_valid :
  RewriteAuditProofSemantic.rw_fact_store_total_valid_contract.
Theorem rw_fact_store_total_after_invalidate :
  RewriteAuditProofSemantic.rw_fact_store_total_after_invalidate_contract.
Theorem rw_fact_observe_valid :
  RewriteAuditProofSemantic.rw_fact_observe_valid_contract.
```

### Future proofs in `RewriteAuditProofTickAdequacy`

Card: AUD-RP-CORE

Source destination: `theories/Rewrite/RewriteAuditProofTickAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditProofTick.

Theorem rw_rp_tick_captures :
  RewriteAuditProofTick.rw_rp_tick_captures_statement.
```

### Future proofs in `RewriteAuditProofWholeContractsAdequacy`

Card: AUD-RP-CORE

Source destination: `theories/Rewrite/RewriteAuditProofWholeContractsAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditProofWholeContracts.

Theorem rw_rp_whole_bound :
  RewriteAuditProofWholeContracts.rw_rp_whole_bound_statement.
```

### Future proofs in `RewriteAuditQueueContractsAdequacy`

Card: AUD-RQ

Source destination: `theories/Rewrite/RewriteAuditQueueContractsAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditQueueContracts.

Theorem rw_rq_rebuild_source_external :
  RewriteAuditQueueContracts.rw_rq_rebuild_source_external_statement.
Theorem rw_rq_rebuild_source_complete_contract :
  RewriteAuditQueueContracts.rw_rq_rebuild_source_complete_contract_statement.
Theorem rw_rq_source_call_count :
  RewriteAuditQueueContracts.rw_rq_source_call_count_statement.
Theorem rw_rq_rebuild_input_bound :
  RewriteAuditQueueContracts.rw_rq_rebuild_input_bound_statement.
```

### Future proofs in `RewriteAuditQueueKernelAdequacy`

Card: AUD-RQ

Source destination: `theories/Rewrite/RewriteAuditQueueKernelAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditQueueKernel.

Theorem rw_rq_get_receipt :
  RewriteAuditQueueKernel.rw_rq_get_receipt_statement.
Theorem rw_rq_receipt_bound :
  RewriteAuditQueueKernel.rw_rq_receipt_bound_statement.
Theorem rw_rq_receipts_bound :
  RewriteAuditQueueKernel.rw_rq_receipts_bound_statement.
```

### Future proofs in `RewriteAuditQueuePositiveAdequacy`

Card: AUD-RQ

Source destination: `theories/Rewrite/RewriteAuditQueuePositiveAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditQueuePositive.

Theorem rw_rq_decision_source_erases :
  RewriteAuditQueuePositive.rw_rq_decision_source_erases_statement.
Theorem rw_rq_decision_build_count :
  RewriteAuditQueuePositive.rw_rq_decision_build_count_statement.
Theorem rw_rq_decision_source_bound :
  RewriteAuditQueuePositive.rw_rq_decision_source_bound_statement.
```

### Future proofs in `RewriteAuditQueueRebuildAdequacy`

Card: AUD-RQ

Source destination: `theories/Rewrite/RewriteAuditQueueRebuildAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditQueueRebuild.

Theorem rw_rq_rebuild_source_erases :
  RewriteAuditQueueRebuild.rw_rq_rebuild_source_erases_statement.
Theorem rw_rq_rebuild_source_valid :
  RewriteAuditQueueRebuild.rw_rq_rebuild_source_valid_statement.
Theorem rw_rq_rebuild_source_bound :
  RewriteAuditQueueRebuild.rw_rq_rebuild_source_bound_statement.
Theorem rw_rq_prepend_source_linear :
  RewriteAuditQueueRebuild.rw_rq_prepend_source_linear_statement.
```

### Future proofs in `RewriteAuditQueueReferenceAdequacy`

Card: AUD-RQ

Source destination: `theories/Rewrite/RewriteAuditQueueReferenceAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditQueueReference.

Theorem rw_pending_pair_key_bits_exact :
  RewriteAuditQueueReference.rw_pending_pair_key_bits_exact_contract.
Theorem rw_pending_initial_with_count_correct :
  RewriteAuditQueueReference.rw_pending_initial_with_count_correct_contract.
Theorem rw_queue_step_agrees :
  RewriteAuditQueueReference.rw_queue_step_agrees_contract.
Theorem rw_pending_empty_valid :
  RewriteAuditQueueReference.rw_pending_empty_valid_contract.
Theorem rw_pending_insert_order :
  RewriteAuditQueueReference.rw_pending_insert_order_contract.
Theorem rw_pending_membership :
  RewriteAuditQueueReference.rw_pending_membership_contract.
Theorem rw_pending_pop_agrees :
  RewriteAuditQueueReference.rw_pending_pop_agrees_contract.
Theorem rw_pending_prepend_agrees :
  RewriteAuditQueueReference.rw_pending_prepend_agrees_contract.
Theorem rw_pair_universe_refines :
  RewriteAuditQueueReference.rw_pair_universe_refines_contract.
Theorem rw_pending_rebuild_agrees :
  RewriteAuditQueueReference.rw_pending_rebuild_agrees_contract.
Theorem rw_pending_initial_counted_correct :
  RewriteAuditQueueReference.rw_pending_initial_counted_correct_contract.
```

### Future proofs in `RewriteAuditSharedBoundsContractsAdequacy`

Card: AUD-RD

Source destination: `theories/Rewrite/RewriteAuditSharedBoundsContractsAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditSharedBoundsContracts.

Theorem rw_rd_extract_bound :
  RewriteAuditSharedBoundsContracts.rw_rd_extract_bound_statement.
Theorem rw_rd_extract_storage :
  RewriteAuditSharedBoundsContracts.rw_rd_extract_storage_statement.
Theorem rw_rd_scalar_bound :
  RewriteAuditSharedBoundsContracts.rw_rd_scalar_bound_statement.
Theorem rw_rd_unary_cost_bound :
  RewriteAuditSharedBoundsContracts.rw_rd_unary_cost_bound_statement.
```

### Future proofs in `RewriteAuditSharedCompareAdequacy`

Card: AUD-RD

Source destination: `theories/Rewrite/RewriteAuditSharedCompareAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditSharedCompare.

Theorem rw_rd_compare_total :
  RewriteAuditSharedCompare.rw_rd_compare_total_statement.
Theorem rw_rd_compare_unique :
  RewriteAuditSharedCompare.rw_rd_compare_unique_statement.
```

### Future proofs in `RewriteAuditSharedExtractAdequacy`

Card: AUD-RD

Source destination: `theories/Rewrite/RewriteAuditSharedExtractAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditSharedExtract.

Theorem rw_rd_compare_bound :
  RewriteAuditSharedExtract.rw_rd_compare_bound_statement.
Theorem rw_rd_extract_agrees :
  RewriteAuditSharedExtract.rw_rd_extract_agrees_statement.
Theorem rw_rd_extract_total :
  RewriteAuditSharedExtract.rw_rd_extract_total_statement.
Theorem rw_rd_extract_unique :
  RewriteAuditSharedExtract.rw_rd_extract_unique_statement.
```

### Future proofs in `RewriteAuditSharedInterfaceRdCompareRealizesStatementAdequacy`

Card: AUD-RD

Source destination:
  `theories/Rewrite/RewriteAuditSharedInterfaceRdCompareRealizesStatementAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditSharedPlainAdequacy.
From Galois.Rewrite Require Import RewriteAuditSharedFixedContracts.

Theorem rw_rd_compare_realizes :
  RewriteAuditSharedFixedContracts.rw_rd_compare_realizes_fixed_type
  Galois.Rewrite.RewriteAuditSharedPlainAdequacy.rw_rd_plain_compare_well_founded.
```

### Future proofs in `RewriteAuditSharedInterfaceRdExtractRealizesStatementAdequacy`

Card: AUD-RD

Source destination:
  `theories/Rewrite/RewriteAuditSharedInterfaceRdExtractRealizesStatementAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditSharedPlainAdequacy.
From Galois.Rewrite Require Import RewriteAuditSharedFixedContracts.

Theorem rw_rd_extract_realizes :
  RewriteAuditSharedFixedContracts.rw_rd_extract_realizes_fixed_type
  Galois.Rewrite.RewriteAuditSharedPlainAdequacy.rw_rd_plain_compare_well_founded.
```

### Future proofs in `RewriteAuditSharedInterfaceRdScalarRealizesStatementAdequacy`

Card: AUD-RD

Source destination:
  `theories/Rewrite/RewriteAuditSharedInterfaceRdScalarRealizesStatementAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditSharedFixedContracts.

Theorem rw_rd_scalar_realizes :
  RewriteAuditSharedFixedContracts.rw_rd_scalar_realizes_fixed_type.
```

### Future proofs in `RewriteAuditSharedInterfaceSharedCompareAgreesContractAdequacy`

Card: AUD-RD

Source destination:
  `theories/Rewrite/RewriteAuditSharedInterfaceSharedCompareAgreesContractAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditSharedPlainAdequacy.
From Galois.Rewrite Require Import RewriteAuditSharedFixedContracts.

Theorem rw_shared_compare_agrees :
  RewriteAuditSharedFixedContracts.rw_shared_compare_agrees_fixed_type
  Galois.Rewrite.RewriteAuditSharedPlainAdequacy.rw_rd_plain_compare_well_founded.
```

### Future proofs in `RewriteAuditSharedInterfaceSharedCompareRejectContractAdequacy`

Card: AUD-RD

Source destination:
  `theories/Rewrite/RewriteAuditSharedInterfaceSharedCompareRejectContractAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditSharedPlainAdequacy.
From Galois.Rewrite Require Import RewriteAuditSharedFixedContracts.

Theorem rw_shared_compare_reject :
  RewriteAuditSharedFixedContracts.rw_shared_compare_reject_fixed_type
  Galois.Rewrite.RewriteAuditSharedPlainAdequacy.rw_rd_plain_compare_well_founded.
```

### Future proofs in `RewriteAuditSharedInterfaceSharedExtractUnfoldContractAdequacy`

Card: AUD-RD

Source destination:
  `theories/Rewrite/RewriteAuditSharedInterfaceSharedExtractUnfoldContractAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditSharedPlainAdequacy.
From Galois.Rewrite Require Import RewriteAuditSharedFixedContracts.

Theorem rw_shared_extract_unfold :
  RewriteAuditSharedFixedContracts.rw_shared_extract_unfold_fixed_type
  Galois.Rewrite.RewriteAuditSharedPlainAdequacy.rw_rd_plain_compare_well_founded.
```

### Future proofs in `RewriteAuditSharedInterfaceSharedObserversRejectContractAdequacy`

Card: AUD-RD

Source destination:
  `theories/Rewrite/RewriteAuditSharedInterfaceSharedObserversRejectContractAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditSharedFixedContracts.

Theorem rw_shared_observers_reject :
  RewriteAuditSharedFixedContracts.rw_shared_observers_reject_fixed_type.
```

### Future proofs in `RewriteAuditSharedInterfaceSharedTreeCostAgreesContractAdequacy`

Card: AUD-RD

Source destination:
  `theories/Rewrite/RewriteAuditSharedInterfaceSharedTreeCostAgreesContractAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditSharedFixedContracts.

Theorem rw_shared_tree_cost_agrees :
  RewriteAuditSharedFixedContracts.rw_shared_tree_cost_agrees_fixed_type.
```

### Future proofs in `RewriteAuditSharedInterfaceSharedTreeCostBinaryAgreesContractAdequacy`

Card: AUD-RD

Source destination:
  `theories/Rewrite/RewriteAuditSharedInterfaceSharedTreeCostBinaryAgreesContractAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditSharedFixedContracts.

Theorem rw_shared_tree_cost_binary_agrees :
  RewriteAuditSharedFixedContracts.rw_shared_tree_cost_binary_agrees_fixed_type.
```

### Future proofs in `RewriteAuditSharedInterfaceSharedTreeSizeBinaryAgreesContractAdequacy`

Card: AUD-RD

Source destination:
  `theories/Rewrite/RewriteAuditSharedInterfaceSharedTreeSizeBinaryAgreesContractAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditSharedFixedContracts.

Theorem rw_shared_tree_size_binary_agrees :
  RewriteAuditSharedFixedContracts.rw_shared_tree_size_binary_agrees_fixed_type.
```

### Future proofs in `RewriteAuditSharedObserversAdequacy`

Card: AUD-RD

Source destination: `theories/Rewrite/RewriteAuditSharedObserversAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditSharedObservers.

Theorem rw_rd_scalar_agrees :
  RewriteAuditSharedObservers.rw_rd_scalar_agrees_statement.
Theorem rw_rd_scalar_reject :
  RewriteAuditSharedObservers.rw_rd_scalar_reject_statement.
```

### Future proofs in `RewriteAuditSharedPlainAdequacy`

Card: AUD-RD

Source destination: `theories/Rewrite/RewriteAuditSharedPlainAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditSharedPlain.

Theorem rw_rd_plain_compare_well_founded :
  RewriteAuditSharedPlain.rw_rd_plain_compare_well_founded_type.
```

### Future proofs in `RewriteAuditSharedPlainAdequacy`

Card: AUD-RD

Source destination: `theories/Rewrite/RewriteAuditSharedPlainAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditSharedPlainContracts.

Theorem rw_rd_plain_compare_source_erases :
  RewriteAuditSharedPlainContracts.rw_rd_plain_compare_source_erases_type
  rw_rd_plain_compare_well_founded.
Theorem rw_rd_plain_extract_source_erases :
  RewriteAuditSharedPlainContracts.rw_rd_plain_extract_source_erases_type
  rw_rd_plain_compare_well_founded.
Theorem rw_rd_plain_production_source_erases :
  RewriteAuditSharedPlainContracts.rw_rd_plain_production_source_erases_type.
```

### Future proofs in `RewriteAuditSharedReferenceAdequacy`

Card: AUD-RD

Source destination: `theories/Rewrite/RewriteAuditSharedReferenceAdequacy.v`.

```rocq
From Galois.Rewrite Require Import RewriteAuditSharedReference.

Theorem rw_shared_validate_spec :
  RewriteAuditSharedReference.rw_shared_validate_spec_contract.
Theorem rw_shared_validate_atomic_erases :
  RewriteAuditSharedReference.rw_shared_validate_atomic_erases_contract.
Theorem rw_shared_unfold_erases :
  RewriteAuditSharedReference.rw_shared_unfold_erases_statement.
Theorem rw_shared_unfold_total :
  RewriteAuditSharedReference.rw_shared_unfold_total_contract.
Theorem rw_shared_unfold_valid :
  RewriteAuditSharedReference.rw_shared_unfold_valid_contract.
Theorem rw_shared_unfold_atomic_erases :
  RewriteAuditSharedReference.rw_shared_unfold_atomic_erases_contract.
```

<!-- AUD-API-RW-END -->


<!-- AUD-API-RW-INSTALL-BEGIN -->

# Fixed public producer installations

These definitions use the library's own future well-foundedness proofs.

## `RewriteAuditSharedPlainAdequacy.rw_shared_compare`

Card: AUD-RD

Source destination: `theories/Rewrite/RewriteAuditSharedPlainAdequacy.v`.

```rocq
From Stdlib Require Import List PArith NArith.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEgraph RewriteExtract
  RewriteAuditSharedReference RewriteAuditSharedPlain.

Definition rw_shared_compare :  forall {K Sort V}, encoding K -> encoding Sort ->
    encoding V ->
  rw_shared_tree K Sort V -> rw_shared_tree K Sort V -> option
    bool :=
  @Galois.Rewrite.RewriteAuditSharedPlain.rw_shared_compare_builder
  rw_rd_plain_compare_well_founded.
```

## `RewriteAuditSharedPlainAdequacy.rw_shared_extract`

Card: AUD-RD

Source destination: `theories/Rewrite/RewriteAuditSharedPlainAdequacy.v`.

```rocq
From Stdlib Require Import List PArith NArith.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEgraph RewriteExtract
  RewriteAuditSharedReference RewriteAuditSharedPlain.

Definition rw_shared_extract :  forall {K Sort V}, encoding K -> encoding Sort -> encoding V ->

    (V -> nat) -> (K -> nat) -> rw_graph K Sort V -> rw_id -> option (rw_shared_tree K Sort
    V) :=
  @Galois.Rewrite.RewriteAuditSharedPlain.rw_shared_extract_builder
  rw_rd_plain_compare_well_founded.
```

<!-- AUD-API-RW-INSTALL-END -->

<!-- AUD-API-RW-TESTS-BEGIN -->

# Rewrite finite test fixtures

These checked finite examples do not prove the future universal theorems.

## Galois.Tests.Rewrite.RewriteAuditQueueExamples

Card: AUD-RQ

Test destination: `tests/Rewrite/RewriteAuditQueueExamples.v`.

```rocq
(** * RewriteAuditQueueExamples

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditQueueKernel RewriteAuditQueuePositive
  RewriteAuditQueueRebuild RewriteAuditQueueReference.
Import List.ListNotations.

Definition rw_rebuild_fixture_adapter : rw_queue_encoder_adapter positive :=
  RwQueueEncoderAdapter (fun p => (p, 1)).

Definition rw_rebuild_fixture_graph : rw_graph positive positive positive :=
  RwGraph [1%positive] [1%positive]
    (Map.set positive_encoding 1%positive 1%positive Map.empty)
    (Map.set positive_encoding 1%positive 1%positive Map.empty)
    (Map.set positive_encoding 1%positive (1%positive, RWNVar 1%positive 1%positive) Map.empty).

Example rw_rq_decision_first_mismatch_fixture :
  fst (rw_rq_decision_atomic 7%positive 2%positive) = false /\
  length (snd (rw_rq_decision_build 7%positive)) = 8.
Proof.
  vm_compute.
  split; reflexivity.
Qed.


Example rw_rq_source_nonempty_fixture :
  let source := rw_rq_rebuild_source rw_rebuild_fixture_adapter rw_rebuild_fixture_adapter
    rw_rebuild_fixture_adapter rw_rebuild_fixture_graph in
  rw_roots (rw_rq_value source) = [1%positive] /\
  0 < length (rw_rq_receipts source) /\
  rw_rq_receipts_work (rw_rq_receipts source) <= rw_rq_receipts_budget (rw_rq_receipts source).
Proof.
  vm_compute.
  repeat split; try reflexivity.
  all: lia.
Qed.
```

## Galois.Tests.Rewrite.RewriteAuditIndexExamples

Card: AUD-RI

Test destination: `tests/Rewrite/RewriteAuditIndexExamples.v`.

```rocq
(** * RewriteAuditIndexExamples

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexPair RewriteAuditIndexPrepareReference
  RewriteAuditIndexRebuild RewriteAuditIndexReference RewriteAuditQueueReference.
Import List.ListNotations.

Definition rw_index_congruence_fixture : rw_graph positive positive positive :=
  RwGraph [1%positive; 2%positive] [1%positive; 2%positive]
    (Map.set positive_encoding 2%positive 2%positive
      (Map.set positive_encoding 1%positive 1%positive Map.empty))
    (Map.set positive_encoding 2%positive 1%positive
      (Map.set positive_encoding 1%positive 1%positive Map.empty))
    (Map.set positive_encoding 2%positive (2%positive, RWNVar 1%positive 1%positive)
      (Map.set positive_encoding 1%positive (1%positive, RWNVar 1%positive 1%positive) Map.empty)).


Definition rw_ri_fixture_adapter : rw_queue_encoder_adapter positive := RwQueueEncoderAdapter
    (fun p => (p, 1)).

(** This statement fixes the ri rebuild source nonempty statement contract. *)
Definition rw_ri_rebuild_source_nonempty_statement : Prop :=
  let initial := rw_index_build
    positive_encoding positive_encoding positive_encoding
    rw_index_congruence_fixture in

    let '((final, events), work) := rw_ri_rebuild_atomic rw_ri_fixture_adapter

    rw_ri_fixture_adapter rw_ri_fixture_adapter initial in
  rw_index_dirty_order final = nil
    /\
  rw_pending_sequence (rw_index_pending final) = nil /\
  rw_roots (rw_index_graph final)
    = [2%positive] /\
  events = [RWIndexDirty 1%positive; RWIndexDirty 2%positive;

    RWIndexCongruence (2%positive, 1%positive) 2%positive 1%positive 2%positive] /\
  0 < work.



Example rw_ri_pair_first_missing_fixture :
  let
    initial := rw_index_build positive_encoding positive_encoding positive_encoding

    rw_index_congruence_fixture in
  rw_ri_pair_node_read_count (snd (rw_ri_pair_atomic
    rw_ri_fixture_adapter
    rw_ri_fixture_adapter rw_ri_fixture_adapter initial (3%positive,
    1%positive)
    rw_pending_empty)) = 1.
Proof.
  vm_compute.
  reflexivity.
Qed.

(** The
    complete costed rebuild exposes the expected nontrivial congruence result. *)

Example rw_ri_rebuild_source_fixture : rw_ri_rebuild_source_nonempty_statement.
Proof.

    vm_compute.
  repeat split; try reflexivity.
  lia.
Qed.
```

## Galois.Tests.Rewrite.RewriteAuditSharedExamples

Card: AUD-RD

Test destination: `tests/Rewrite/RewriteAuditSharedExamples.v`.

```rocq
(** * RewriteAuditSharedExamples

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditSharedExtract RewriteAuditSharedObservers
  RewriteAuditSharedReference.
From Galois.Tests.Rewrite Require Import RewriteAuditIndexExamples RewriteAuditQueueExamples.
Import List.ListNotations.

Definition rw_shared_validation_fixture_nodes : Map.t positive (rw_shared_node positive positive
    positive) :=
  Map.set positive_encoding 1%positive (RWSharedVar positive positive positive 1%positive
    1%positive) Map.empty.

Definition rw_shared_fan_fixture_nodes : Map.t positive (rw_shared_node positive positive
    positive) :=
  Map.set positive_encoding 3%positive
    (RWSharedApp positive positive positive 1%positive 1%positive [2%positive; 2%positive])
    (Map.set positive_encoding 2%positive
      (RWSharedApp positive positive positive 1%positive 1%positive [1%positive; 1%positive])
      rw_shared_validation_fixture_nodes).

Definition rw_shared_fan_fixture : rw_shared_tree positive positive positive :=
  RwSharedTree positive positive positive 3%positive rw_shared_fan_fixture_nodes.

(** This statement fixes the rd extract nonempty statement contract. *)
Definition rw_rd_extract_nonempty_statement : Prop
    :=
  exists dag work,
    rw_shared_extract_run rw_ri_fixture_adapter rw_ri_fixture_adapter
    rw_ri_fixture_adapter
      (fun _ => (0, 64)) (fun _ => (1, 64)) rw_rebuild_fixture_graph
    1%positive
      (Some dag) work /\
    rw_shared_unfold dag = Some (RWVar 1%positive
    1%positive) /\ 0 < work.

(** The repeated-subtree scalar fixture computes expanded size
    seven from three stored nodes. *)

Example rw_rd_scalar_fan_fixture :
  fst
    (rw_rd_scalar_observe (fun _ => (1, 64)) (fun _ => (1, 64))
    rw_shared_fan_fixture) =
    Some (7%N, 7%N).
Proof.
  vm_compute.
  reflexivity.
Qed.


(** The fixed relational extractor has a concrete successful nonempty execution. *)

Example rw_rd_extract_source_fixture : rw_rd_extract_nonempty_statement.
Proof.
  unfold
    rw_rd_extract_nonempty_statement.
  eexists.
  eexists.
  split.
  - eapply RDExtractFound.

       + reflexivity.
    + reflexivity.
    + reflexivity.
    + eapply RDRoundsOne.

    eapply RDRoundInsert.
      * reflexivity.
      * reflexivity.
      * eapply
    RDInsertAbsent; reflexivity.
      * apply RDRoundNil.
    + reflexivity.
  - vm_compute.

     split; [reflexivity | lia].
Qed.
```

## Galois.Tests.Rewrite.RewriteAuditProofExamples

Card: AUD-RP-CORE

Test destination: `tests/Rewrite/RewriteAuditProofExamples.v`.

```rocq
(** * RewriteAuditProofExamples

    This module fixes source equations, typed observations and contract statements.
    For example, failed lookups retain their original query and selected source cost.
    Builds on: Rewrite and the canonical Collections audit models. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexRules RewriteAuditProofApply
  RewriteAuditProofCarrier RewriteAuditProofSeed RewriteAuditProofTick RewriteAuditSharedReference.
From Galois.Tests.Rewrite Require Import RewriteAuditIndexExamples.
Import List.ListNotations.

Example rw_rp_seed_nonempty_fixture :
  let seed : rw_term positive positive positive :=
    RWApp
    1%positive 2%positive [RWVar 1%positive 3%positive; RWVar 1%positive 3%positive] in
  let
    '((root, state), _) := @rw_rp_seed_atomic positive positive positive positive

    positive_encoding positive_encoding positive_encoding
    rw_ri_fixture_adapter
    rw_ri_fixture_adapter seed in
  root = 3%positive /\
  rw_shared_unfold (RwSharedTree
    positive positive positive root
    (rw_class_witness_nodes (rw_tracked_witnesses state))) =
    Some seed.
Proof.
  vm_compute.
  split; reflexivity.
Qed.



Definition rw_rp_fixture_rule : rw_rule positive positive positive positive :=
  RwRule positive positive positive positive [1%positive] (fun _ => Some 1%positive)
    (RWHole 1%positive 1%positive)
    (RWPApp 1%positive 2%positive [RWHole 1%positive 1%positive])
    (fun _ => true).


Definition rw_rp_fixture_callbacks : rw_rp_rule_callbacks positive positive positive positive :=
  RwRpRuleCallbacks positive positive positive positive
    (fun _ => (Some 1%positive, 1))
    (fun _ _ _ => (true, 1))
    (fun _ _ => (Some 1%positive, 1))
    (fun _ => RPGuardReturn true 1).


Definition rw_rp_fixture_attempt : rw_attempt positive positive positive positive :=
  RwAttempt 0 1%positive
    (Map.set positive_encoding 1%positive (RWVar 1%positive 3%positive) Map.empty).

(** The concrete accepted phase records the original rule index under its actual event stamp. *)

Example rw_rp_accepted_source_fixture :
  let '((_, state), _) := @rw_rp_seed_atomic positive positive positive positive
    positive_encoding positive_encoding positive_encoding
    rw_ri_fixture_adapter rw_ri_fixture_adapter (RWVar 1%positive 3%positive) in
  match fst (rw_rp_rule_step_atomic positive_encoding positive_encoding positive_encoding
    rw_ri_fixture_adapter rw_ri_fixture_adapter rw_ri_fixture_adapter rw_ri_fixture_adapter
    rw_rp_fixture_callbacks [rw_rp_fixture_rule] 0 state rw_rp_fixture_attempt) with
  | None => false
  | Some next =>
    match Map.get (pair_encoding nat_encoding nat_encoding) (1, 0)
        (rw_tracked_event_nodes next) with
    | None => false
    | Some id =>
      match Map.get positive_encoding id (rw_provenance_nodes (rw_tracked_provenance next)) with
      | None => false
      | Some node =>
        match rw_evidence_reason_of node with
        | RWEvidenceRule index _ => Nat.eqb index 0
        | _ => false
        end
      end
    end
  end = true.
Proof.
  vm_compute.
  reflexivity.
Qed.
```

## Galois.Tests.Rewrite.RewriteAuditPlainExamples

Card: AUD-RP-CORE

Test destination: `tests/Rewrite/RewriteAuditPlainExamples.v`.

```rocq
(** * RewriteAuditPlainExamples

    This module evaluates the fixed source phases without cost or receipt construction.
    For example, a lookup uses the actual plain map operation once.
    Builds on: the canonical Rewrite source equations and Collections. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexPrepareReference RewriteAuditIndexPrograms
  RewriteAuditIndexReference RewriteAuditPlainCore3 RewriteAuditProofApply
  RewriteAuditProofPlainPublic RewriteAuditProofRepresentation RewriteAuditProofRun
  RewriteAuditProofSeed.
From Galois.Tests.Rewrite Require Import RewriteAuditIndexExamples RewriteAuditProofExamples.
Import List.ListNotations.
Local Coercion encode : encoding >-> Funclass.

Definition rw_plain_fixture_signature : rw_signature positive positive positive :=
  RwSignature positive positive positive (fun _ => Some 1%positive) (fun _ _ _ => true).

(** The actual plain seed retains exactly the source model's graph and duplicate-child witnesses. *)
Example rw_plain_seed_same_source_fixture :
  @rw_plain_rw_rp_seed_atomic positive positive positive positive
    positive_encoding positive_encoding positive_encoding positive_encoding positive_encoding
    (RWApp 1%positive 2%positive [RWVar 1%positive 3%positive; RWVar 1%positive 3%positive]) =
  fst (@rw_rp_seed_atomic positive positive positive positive
    positive_encoding positive_encoding positive_encoding rw_ri_fixture_adapter
  rw_ri_fixture_adapter
    (RWApp 1%positive 2%positive [RWVar 1%positive 3%positive; RWVar 1%positive 3%positive])).
Proof.
  vm_compute.
  reflexivity.
Qed.

(** The fixed public accepted rule body retains the entire source state, including its stamp. *)
Example rw_plain_accepted_same_source_fixture :
  let '((_, state), _) := @rw_rp_seed_atomic positive positive positive positive
    positive_encoding positive_encoding positive_encoding rw_ri_fixture_adapter
  rw_ri_fixture_adapter
    (RWVar 1%positive 3%positive) in
  rw_tracked_rule_step positive_encoding positive_encoding positive_encoding positive_encoding
    rw_plain_fixture_signature [rw_rp_fixture_rule] 0 state rw_rp_fixture_attempt =
  fst (rw_rp_rule_step_atomic positive_encoding positive_encoding positive_encoding
    rw_ri_fixture_adapter rw_ri_fixture_adapter rw_ri_fixture_adapter rw_ri_fixture_adapter
    rw_rp_fixture_callbacks [rw_rp_fixture_rule] 0 state rw_rp_fixture_attempt).
Proof.
  vm_compute.
  reflexivity.
Qed.

(** A positive-fuel public producer performs the initial rebuild before the genuine stop
  callback. *)
Example rw_plain_stopped_run_same_source_fixture :
  @rw_tracked_run positive positive positive positive
    positive_encoding positive_encoding positive_encoding positive_encoding
    rw_plain_fixture_signature nil (fun _ => None) 1%N (RWVar 1%positive 3%positive) =
  fst (rw_rp_run_atomic positive_encoding positive_encoding positive_encoding
    rw_ri_fixture_adapter rw_ri_fixture_adapter rw_ri_fixture_adapter rw_ri_fixture_adapter
    rw_rp_fixture_callbacks nil (RwRpStrategyAdapter positive positive positive positive
      (RPViewReturn None 0)) 1%N (RWVar 1%positive 3%positive)).
Proof.
  vm_compute.
  reflexivity.
Qed.

(** The public phase-view finder returns the same nonempty representation witness. *)
Example rw_plain_representation_same_source_fixture :
  let state := rw_index_build positive_encoding positive_encoding positive_encoding
    rw_index_congruence_fixture in
  rw_repr_find positive_encoding positive_encoding positive_encoding
    (rw_snapshot_base (rw_index_view positive_encoding positive_encoding positive_encoding state))
    1%positive (RWVar 1%positive 1%positive) =
  fst (rw_rp_repr_find_atomic rw_ri_fixture_adapter rw_ri_fixture_adapter rw_ri_fixture_adapter
    state 1%positive (RWVar 1%positive 1%positive)).
Proof.
  vm_compute.
  reflexivity.
Qed.
```

## Galois.Tests.Rewrite.RewriteAuditSharedPlainExamples

Card: AUD-RD

Test destination: `tests/Rewrite/RewriteAuditSharedPlainExamples.v`.

```rocq
(** * Plain shared-data clients and concrete comparator accessibility

    These examples execute retained sharing, repeated occurrences and malformed-input rejection.
    For example, three stored nodes contribute seven occurrences to the additive tree objective.
    Builds on: the actual plain scalar, comparator kernel and production allocation bodies. *)

From Stdlib Require Import List PArith NArith.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditSharedExtract RewriteAuditSharedPlain
  RewriteAuditSharedReference.
Import List.ListNotations.
Local Coercion encode : encoding >-> Funclass.

Definition rd_plain_variable_nodes (value : positive) :=
  Map.set positive_encoding 1%positive (RWSharedVar positive positive positive 1%positive value)
    Map.empty.

Definition rd_plain_fan_nodes :=
  Map.set positive_encoding 3%positive
    (RWSharedApp positive positive positive 1%positive 1%positive [2%positive; 2%positive])
    (Map.set positive_encoding 2%positive
      (RWSharedApp positive positive positive 1%positive 1%positive [1%positive; 1%positive])
      (rd_plain_variable_nodes 1%positive)).

Definition rd_plain_fan := RwSharedTree positive positive positive 3%positive rd_plain_fan_nodes.

Example rd_plain_repeated_tree_objective_closed :
  rw_shared_tree_cost_binary (fun _ => 1) (fun _ => 1) rd_plain_fan = Some 7%N /\
  rw_shared_tree_size_binary rd_plain_fan = Some 7%N /\
  rw_shared_tree_cost (fun _ => 1) (fun _ => 1) rd_plain_fan = Some 7%nat.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Definition rd_plain_unreachable_cycle :=
  RwSharedTree positive positive positive 1%positive
    (Map.set positive_encoding 2%positive
      (RWSharedApp positive positive positive 1%positive 1%positive [2%positive])
      (rd_plain_variable_nodes 1%positive)).

Example rd_plain_unreachable_cycle_rejected_closed :
  rw_shared_tree_cost_binary (fun _ => 1) (fun _ => 1) rd_plain_unreachable_cycle = None /\
  rw_shared_tree_size_binary rd_plain_unreachable_cycle = None.
Proof.
  vm_compute. split; reflexivity.
Qed.

Definition rd_plain_bad_stored_key :=
  RwSharedTree positive positive positive 1%positive
    (Trie.set 1%positive
      (2%positive, RWSharedVar positive positive positive 1%positive 1%positive) Trie.Empty).

Example rd_plain_stored_key_rejected_closed :
  rw_shared_tree_cost (fun _ => 1) (fun _ => 1) rd_plain_bad_stored_key = None.
Proof.
  vm_compute. reflexivity.
Qed.

(** This actual local accessibility witness covers the tested fixed root and its empty children. *)
Definition rd_plain_variable_accessible (left_value right_value : positive) :
  Acc (rd_plain_compare_descend (rd_plain_variable_nodes left_value)
    (rd_plain_variable_nodes right_value)) (RDPlainRoot 1%positive 1%positive Map.empty).
Proof.
  constructor. intros child Hdescend.
  inversion Hdescend as [p q memo a b Hleft Hright | |]; subst.
  vm_compute in Hleft, Hright.
  inversion Hleft; inversion Hright; subst.
  constructor. intros next Himpossible. inversion Himpossible.
Defined.

Example rd_plain_comparator_recursive_kernel_closed :
  rd_plain_compare_execute positive_encoding positive_encoding positive_encoding
    (rd_plain_variable_nodes 1%positive) (rd_plain_variable_nodes 1%positive)
    (RDPlainRoot 1%positive 1%positive Map.empty)
    (rd_plain_variable_accessible 1%positive 1%positive) =
  (Eq, Map.set (pair_encoding positive_encoding positive_encoding)
    (1%positive, 1%positive) Eq Map.empty).
Proof.
  vm_compute. reflexivity.
Qed.

Example rd_plain_comparator_order_kernel_closed :
  rd_plain_compare_execute positive_encoding positive_encoding positive_encoding
    (rd_plain_variable_nodes 1%positive) (rd_plain_variable_nodes 2%positive)
    (RDPlainRoot 1%positive 1%positive Map.empty)
    (rd_plain_variable_accessible 1%positive 2%positive) =
  (Lt, Map.set (pair_encoding positive_encoding positive_encoding)
    (1%positive, 1%positive) Lt Map.empty).
Proof.
  vm_compute. reflexivity.
Qed.

Definition rd_plain_variable_graph : rw_graph positive positive positive :=
  RwGraph [1%positive] [1%positive]
    (Map.set positive_encoding 1%positive 1%positive Map.empty)
    (Map.set positive_encoding 1%positive 1%positive Map.empty)
    (Map.set positive_encoding 1%positive (1%positive, RWNVar 1%positive 1%positive) Map.empty).

Example rd_plain_real_backpointer_allocation_closed :
  rd_plain_production (fun _ => 5) (fun _ => 9) rd_plain_variable_graph Map.empty
    (RWNVar 1%positive 1%positive) (RwRdStore Map.empty 1%positive) =
  (Some (RwRdCandidate 1%positive 5%N 1%N),
    RwRdStore (rd_plain_variable_nodes 1%positive) 2%positive).
Proof.
  vm_compute. reflexivity.
Qed.
```

<!-- AUD-API-RW-TESTS-END -->
