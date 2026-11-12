# Galois engines and front ends: design document

Scope: (1) one relational engine (egglog-style) under both Datalog and equality saturation, (2) SSA construction and destruction, (3) incremental and demand-driven re-analysis, (4) the executable pipeline, (5) triage of the specialised analyses, (6) work packages.

## Verification status

- **Checked in the Rocq 9.3 REPL:**
  - The layered module types (`FOO`, `FOO_TIME` and `FOO_PLAN`, joined by `Include`).
  - `Declare Module … with Module V := V with Module I := I` sharing across functors.
  - Ascribing a functor with `<: DATABASE_PLAN with Module V := V0 …`.
  - A functor whose parameter is a `SOLVER` over a `RESTRICT` that itself shares a `SYSTEM`.
  - The generic-join recursion: structural on the level, with `fold_left` over a lambda that calls the outer fix. The guard checker accepts it.
- **Not checked:** Argent is not installed in the environment, so no `TimeFun` call was run.
- **Not checked:** the remaining Rocq below is a specification sketch and has not been compiled.

## 0. Decisions at a glance

| Question | Decision |
|---|---|
| Engine | One functorial relational engine, `theories/Egglog/`. It has the following parts. |
| | Functional tables, where a relation, a constructor (e-class output) or a lattice-valued output carries a merge. |
| | A union-find (union by size) over ids. |
| | Generic join (worst-case-optimal join), driven by incrementally maintained trie indexes. |
| | Semi-naive rounds, closed by a *naive confirmation round*. |
| | Deferred rebuild over use lists. |
| | Extraction by Knuth's algorithm. |
| | Datalog and equality saturation are thin front ends that produce `program` values. |
| Datalog guarantee | Least model per stratum, so the result is the perfect model for stratified negation. Negation is an `Absent` atom over *frozen* tables of a lower stratum only. |
| Equality guarantees | After every rebuild the database is canonical and congruence-closed. Every derived equality and fact holds in every model of the rules. On a canonical database, matching equals the answers of the conjunctive query. `Saturated` implies the database is closed under the rules. |
| Extraction | Tree cost is optimal, by Knuth's generalisation of Dijkstra. DAG extraction is honest: a greedy DAG built from the tree choice, with proved `dag_cost ≤ tree_cost`. An external optimal (ILP or treewidth) DAG can be accepted through a verified checker. No optimal-DAG claim is made. |
| SSA construction | Cytron et al. from the library's dominance frontiers, pruned by per-variable liveness. It is an untrusted producer, validated by a Barthe–Demange–Pichardie style checker with a proved lockstep simulation. I chose it over Braun et al. (reasons in §2). |
| SSA destruction | Proved directly. It splits critical edges, which fixes the lost-copy problem. Each parallel copy is sequentialised by Boissinot et al.'s linear algorithm and validated by a symbolic-execution checker, which fixes the swap problem. |
| Incremental | One demand-driven, incremental state over `SYSTEM`, in the style of the local solvers and incremental top-down solver of Seidl et al. |
| | The invariant is "the domain is dependency-closed, and its values are a post-solution of its rows". The `least` part holds with a widening-free least solver. |
| | The region is solved by any core `SOLVER` over a restricted, seeded system and checked on that region only. |
| | Demanded abstract interpretation (DAIG) is adopted for its interface. Its from-scratch-consistency theorem is adopted only without widening. |
| Pipeline | Concrete functor applications live in `theories/Exec/` and are extracted as applied OCaml modules. There is one textual IR for functions plus Soufflé and egglog subsets, an OCaml driver and a benchmark harness. Parsing, lowering, printing, extraction and `ExtrOcamlBasic` are trusted. |

---

## 1. The relational engine (`theories/Egglog/`)

### 1.1 Citations

- **Engine design:**
  - Zhang, Wang, Flatt, Cao, Zucker, Rosenthal, Tatlock, Willsey, "Better Together: Unifying Datalog and Equality Saturation", PLDI 2023 (egglog): tables as functions with merge, union-find, semi-naive rounds with rebuilding, lattice-valued functions as e-class analyses.
  - Zhang, Wang, Willsey, Tatlock, "Relational E-Matching", POPL 2022: patterns become conjunctive queries on a canonical database, evaluated by generic join.
  - Willsey, Nandi, Wang, Flatt, Tatlock, Panchekha, "egg: Fast and Extensible Equality Saturation", POPL 2021: deferred rebuilding, parent (use) lists, analyses, runner limits.
- **Congruence closure:**
  - Downey, Sethi, Tarjan, "Variations on the common subexpression problem", JACM 27(4) 1980: O(m log m) by relabelling the smaller side.
  - Nelson, Oppen, JACM 27(2) 1980.
  - Nieuwenhuis, Oliveras, "Fast congruence closure and extensions", Inf. & Comp. 205(4) 2007.
  - Tarjan, van Leeuwen, JACM 31(2) 1984 (union by size).
- **Joins:**
  - Ngo, Porat, Ré, Rudra, "Worst-case optimal join algorithms", PODS 2012 / JACM 65(3) 2018.
  - Ngo, Ré, Rudra, "Skew strikes back", SIGMOD Record 42(4) 2013 (Generic Join).
  - Veldhuizen, "Leapfrog Triejoin", ICDT 2014.
  - Atserias, Grohe, Marx, "Size bounds and query plans for relational joins", FOCS 2008 / SICOMP 2013 (the AGM bound).
- **Datalog:**
  - Bancilhon 1986, and Balbin and Ramamohanarao, JLP 1987 (semi-naive evaluation).
  - Abiteboul, Hull, Vianu, *Foundations of Databases*, 1995, chapters 12, 13 and 15.
  - Apt, Blair, Walker 1988 and Przymusinski 1988 (stratified and perfect models).
- **Extraction:**
  - Knuth, "A generalization of Dijkstra's algorithm", IPL 6(1) 1977.
  - Goharshady, Lam, Parreaux, "Fast and Optimal Extraction for Sparse Equality Graphs", OOPSLA 2024 (optimal DAG extraction is NP-hard in general; their algorithm is parameterised by treewidth). It is cited for the external producer only.

### 1.2 What each fragment guarantees

- **Datalog fragment.** Every declaration is `ORel`. Actions are `Put` and `Let` only. No `Id` cell occurs. `Absent` is used only on frozen tables.
  - If the result is `Saturated`, the result database is the least database that contains the input and is closed under the rules (`run_least`).
  - Strata are run in sequence by the front end, with lower strata frozen. That gives the perfect model (`solve_exact`).
  - Termination: with `max_iter ≥ 2·H+2`, where H is the size of the Herbrand base, the result is `Saturated`.
- **Equality fragment.** This is everything else, with no `Absent`.
  - (a) After every `rebuild`, the database is canonical (every id in a row is a root) and functional, and therefore congruence-closed (`rebuild_congruent`). `same` is the least equivalence that contains the input unions and is closed under functional-dependency merging (`rebuild_same`).
  - (b) Soundness: for every model `M` that validates the rules, and every valuation that satisfies the input, an extended valuation satisfies the output (`run_sat`). Hence every derived equality holds in every model, and every lattice fact is sound.
  - (c) Matching completeness: on a canonical database, the join returns exactly the substitutions that satisfy the query (`Join.run_complete` together with `Run.naive_plans_complete`). In terms of terms, this is the e-matching statement `Eqsat.ematch_complete`.
  - (d) `Saturated` implies `closed`.
  - No minimality-up-to-renaming theorem is stated, and termination is enforced only by the limits.

### 1.3 Data (`Egglog/Syntax.v`, top level, groundwork)

```coq
From Stdlib Require Import List PArith NArith.

Inductive cell (V : Type) : Type := Id (i : positive) | Val (v : V).
Inductive term (V : Type) : Type := Var (x : positive) | Lit (v : V).
Inductive output : Type := ORel | OId | OLat (merge_op : positive).
Record decl : Type := Decl { name : positive; arity : nat; out : output; frozen : bool }.

Inductive atom (V : Type) : Type :=
  | Fun    (f : positive) (args : list (term V)) (res : option (term V)) (* None iff ORel *)
  | Prim   (p : positive) (args : list (term V)) (res : term V)
  | Absent (f : positive) (args : list (term V)).                       (* frozen f only *)

Inductive action (V : Type) : Type :=
  | Make  (x : positive) (f : positive) (args : list (term V))  (* OId: find or create *)
  | Put   (f : positive) (args : list (term V)) (res : option (term V))
  | Union (a b : term V)
  | Let   (x : positive) (p : positive) (args : list (term V)).

Record rule (V : Type) : Type := Rule { query : list (atom V); actions : list (action V) }.
Record program (V : Type) : Type := Program { decls : list decl; rules : list (rule V) }.
Record limits : Type := Limits { max_iter : N; max_ids : N }.
Inductive stop : Type := Saturated | IterLimit | IdLimit.

(* Untrusted planner output, validated by Run.check_plan. *)
Inductive source (V : Type) : Type := All (slot : nat) | New (slot : nat) | Const (c : cell V).
Record jplan : Type := JPlan { nvars : nat; cols : list (list nat) }.   (* per atom: increasing levels *)
Record cplan (V : Type) : Type := CPlan {
  rule_ix : nat; join : jplan; sources : list (source V);
  var_of : list positive;                 (* level -> query variable *)
  post : list nat }.                      (* indices of Prim/Absent atoms checked after the join *)
Record compiled (V : Type) : Type := Compiled {
  slots : list (positive * list nat);     (* (function, column permutation incl. output) *)
  naive : list (cplan V); seminaive : list (cplan V) }.

Definition datalog_fragment {V} (p : program V) : bool. (* all ORel, Put/Let only, Absent on frozen *)
Definition absent_free {V} (p : program V) : bool.
```

A merge is chosen per declaration by a merge-operator id (`OLat m`), so the program value carries it and the `VALUE` instance fixes the finite table of merges. Patterns and terms that the front ends execute over are *flat*: lists of nodes with child indices. That way `TimeFun` never meets a nested or local `fix`, and the nested inductive `expr` stays spec-only.

### 1.4 Fields required from the core (state them in the core signatures)

- **`KEY`**: `t`, `eqb`, `eqb_spec : reflect (a = b) (eqb a b)`, `encode`, `encode_inj`, `bits k := Pos.size_nat (encode k)`, and a time layer with `T_eqb ≤ c·(bits a + 1)` and `T_encode ≤ c·(bits+1)`.
  - **Not listed by the core, needed:** the combinators `KeyPos`, `KeyPair (A B : KEY)` and `KeyList (A : KEY)`, with `bits (a,b) ≤ 2(bits a + bits b) + 2` and `bits l ≤ 2·Σ bits + 2·length l + 2`, and a `KeyCell (V : KEY)` for `cell V.t`.
- **`MAP`**: `empty`, `get`, `set`, `remove`, `elements` with the usual laws and `NoDup (map fst (elements m))`. Time: get, set and remove cost at most `c·(bits k + 1)`, and `T_elements m ≤ c·(Σ_{k∈dom}(bits k+1) + 1)`.
- **`SET`**: the same operations as `MAP`, with `mem`, `add`, `remove` and `elements`.
- **`UNION_FIND`** (keys `positive`):
  - Operations: `empty`, `add : positive -> t -> t`, `find : positive -> t -> positive * t`, `union : positive -> positive -> t -> option (positive * positive) * t`. `union` returns `(winner, loser)` when the roots differ.
  - Spec functions: `repr`, `size_of : t -> positive -> nat` (the class cardinality) and `card`.
  - **Not listed, needed:** the law `union_by_size : union x y u = (Some (w,l), u') -> size_of u l <= size_of u w`. Without it, the rebuild bound degrades from O(S log n) to O(S·n).
  - Time: `T_find ≤ c·(log2 card + 1)·(bits + 1)`.
- **`PQ`** (Extract): `push`, `pop` (minimum), and the amortised contract `T_pop + Φ' ≤ c·(log2 P + 1)·(w+1) + Φ`.
- **Graph** (SSA):
  - First-order graphs with `succs`, `preds` and `nodes`.
  - The dominator tree as children lists with preorder and postorder numbers.
  - `dominates_b` at O(w) per query, by the interval test, with its spec.
  - `frontier : graph -> MAP (list positive)` with `df_spec` and contract `O((n + e + Σ|DF|)·w)` (Cooper–Harvey–Kennedy 2001).
  - An SCC condensation with an exactness spec (used by the Datalog stratifier).
- **`SYSTEM`** (Incremental): `prog key row val frame`, `rows`, `target`, `start`, `resume`, and the spec layer `eval`, `post_solution`, `monotone` and `reads_within`.
  - **Not listed, needed:** executable `deps : prog -> row -> list key` and `rows_of : prog -> key -> list row`, each with a time contract linear in its output; a `KEY` on `row`; and `check_post_rows : prog -> list row -> (key -> val) -> bool` with soundness restricted to the listed rows.
- **`SOLVER`**: `run : prog -> policy -> N -> outcome` and `check_post`.
  - **Not listed, needed:** a spec function `work : prog -> nat` with `T_run ≤ c_solve·(work p + 1)`.
  - **Optional extension `LEAST_SOLVER`:** `widening_free : policy -> Prop` and `run_least : monotone p -> widening_free pol -> run … = Solved s -> forall s', post_solution p s' -> s ⊑ s'`. This is the existing "reached-least" argument. Without it, Incremental claims soundness only.
- **From the domains architect:** for e-class analyses, a merge sound for the concretisation: `γ a ∩ γ b ⊆ γ (merge a b)`, which is a meet. The engine only needs it inside the *model*, so the concrete `VALUE` instance cites the domain's `meet` law.

### 1.5 `ValueSig.v`

```coq
Module Type VALUE.
  Include KEY.
  Parameter prim  : positive -> list t -> option t.
  Parameter merge : positive -> t -> t -> t.               (* merge operator id -> join *)
  Parameter merge_comm  : forall m a b, merge m a b = merge m b a.
  Parameter merge_assoc : forall m a b c, merge m a (merge m b c) = merge m (merge m a b) c.
  Parameter merge_idem  : forall m a, merge m a a = a.
End VALUE.
Module Type VALUE_TIME.
  Include VALUE.
  Parameter prim_work : positive -> list t -> nat.          (* spec *)
  Parameter T_prim : positive -> list t -> nat.
  Parameter T_merge : positive -> t -> t -> nat.
  Parameter c_val : nat.
  Parameter T_prim_le  : forall p xs, T_prim p xs <= c_val * (prim_work p xs + 1).
  Parameter T_merge_le : forall m a b, T_merge m a b <= c_val * (bits a + bits b + 1).
End VALUE_TIME.

Module Type COST.                                            (* for Extract *)
  Declare Module V : VALUE.
  Parameter fn_cost : positive -> list N -> N.
  Parameter val_cost : V.t -> N.
  Parameter fn_cost_mono  : forall f cs ds, Forall2 N.le cs ds -> (fn_cost f cs <= fn_cost f ds)%N.
  Parameter fn_cost_super : forall f cs c, In c cs -> (c <= fn_cost f cs)%N.   (* Knuth's superiority *)
  Parameter T_fn_cost : positive -> list N -> nat.  Parameter c_cost : nat.
  Parameter T_fn_cost_le : forall f cs, T_fn_cost f cs <= c_cost * (length cs + 1) * (list_bits cs + 1).
End COST.
```

### 1.6 `Model.v` (specification only; groundwork writes it)

```coq
Section Model.
Context {V : Type} (prim : positive -> list V -> option V) (merge : positive -> V -> V -> V).

Record view : Type := View {                       (* what a DATABASE exposes *)
  row  : positive -> list (cell V) -> option (cell V) -> Prop;
  same : positive -> positive -> Prop;
  kind : positive -> option output }.

Record model : Type := Model {
  carrier : Type;
  rel : positive -> list (carrier + V) -> Prop;
  con : positive -> list (carrier + V) -> carrier;         (* total: an algebra *)
  lat : positive -> list (carrier + V) -> V -> Prop;       (* abstract value is sound *)
  lat_merge : forall f m k a b, lat f k a -> lat f k b -> lat f k (merge m a b) }.

Definition den {M} (nu : positive -> carrier M) (c : cell V) : carrier M + V :=
  match c with Id i => inl (nu i) | Val v => inr v end.
Definition holds M nu (w : view) f k o : Prop :=
  match kind w f, o with
  | Some ORel, None => rel M f (map (den nu) k)
  | Some OId, Some (Id i) => con M f (map (den nu) k) = nu i
  | Some (OLat _), Some (Val v) => lat M f (map (den nu) k) v
  | _, _ => False end.
Definition sat M nu w : Prop :=
  (forall f k o, row w f k o -> holds M nu w f k o) /\ (forall i j, same w i j -> nu i = nu j).

Definition env := positive -> option (cell V).
Definition atom_holds (w : view) (s : env) (a : atom V) : Prop.   (* Fun: row; Prim: prim; Absent: no row *)
Definition matches w (q : list (atom V)) (s : env) : Prop := Forall (atom_holds w s) q.
Fixpoint present (w : view) (s : env) (acts : list (action V)) : Prop.
  (* Make x f k: exists i, row w f k (Some (Id i)) /\ present w s[x:=Id i] rest
     Put f k (Some r): exists o, row w f k (Some o) /\ cell_le w f r o /\ ...  (ids: same; values: merge r o = o)
     Put f k None: exists o, row w f k o /\ ...;  Union a b: same/equal;  Let: prim None => True *)
Definition closed (p : program V) (w : view) : Prop :=
  forall r s, In r (rules p) -> matches w (query r) s -> present w s (actions r).
Definition valid (M : model) (p : program V) : Prop.   (* every rule: model body => model actions *)
Inductive derives (p : program V) (w0 : view) : positive -> list (cell V) -> Prop.   (* Datalog *)
Inductive expr : Type := EApp (f : positive) (args : list expr) | ELit (v : V).
Inductive represents (w : view) : cell V -> expr -> Prop :=
  | rep_lit v : represents w (Val v) (ELit v)
  | rep_app f k i j args : row w f k (Some (Id j)) -> same w i j ->
      Forall2 (represents w) k args -> represents w (Id i) (EApp f args).
Definition denote M : expr -> carrier M + V.          (* EApp f es => inl (con M f (map denote es)) *)
End Model.
```

### 1.7 `IndexSig.v`: trie index stored as an edge map

Representation:
- Nodes are `positive`.
- `edges : MAP (KeyPair KeyPos KeyCell) positive` maps a node and a cell to the child node.
- `kids : MAP KeyPos (SET.t * N * N)` holds, per node, the child set, the child count and the tuple count.
- `next` is the fresh-node counter. Node ids are never reclaimed.
- Counters are `N`, never `nat`.

```coq
Module Type INDEX.
  Declare Module V : VALUE.
  Parameter t : Type.
  Parameter empty : t.
  Parameter insert : list (cell V.t) -> t -> t.
  Parameter remove : list (cell V.t) -> t -> t.
  Parameter root : t -> positive.
  Parameter child : t -> positive -> cell V.t -> option positive.
  Parameter children : t -> positive -> list (cell V.t).
  Parameter degree : t -> positive -> N.
  (* spec *)
  Parameter wf : nat -> t -> Prop.                                   (* all tuples have this arity *)
  Parameter mem : t -> list (cell V.t) -> Prop.
  Parameter node : t -> positive -> list (cell V.t) -> Prop.         (* node n stands for prefix *)
  Parameter wf_empty : forall a, wf a empty.
  Parameter wf_insert : forall a r ix, wf a ix -> length r = a -> wf a (insert r ix).
  Parameter wf_remove : forall a r ix, wf a ix -> wf a (remove r ix).
  Parameter mem_insert : forall a r ix u, wf a ix -> length r = a -> (mem (insert r ix) u <-> u = r \/ mem ix u).
  Parameter mem_remove : forall a r ix u, wf a ix -> (mem (remove r ix) u <-> u <> r /\ mem ix u).
  Parameter mem_arity : forall a ix u, wf a ix -> mem ix u -> length u = a.
  Parameter node_root : forall a ix, wf a ix -> node ix (root ix) [].
  Parameter node_live : forall a ix n pre, wf a ix -> node ix n pre -> pre <> [] -> exists suf, mem ix (pre ++ suf).
  Parameter node_fun  : forall a ix n m pre, wf a ix -> node ix n pre -> node ix m pre -> n = m.
  Parameter child_spec : forall a ix n pre c, wf a ix -> node ix n pre ->
    (forall m, child ix n c = Some m <-> node ix m (pre ++ [c])) /\
    (child ix n c = None <-> ~ exists suf, mem ix (pre ++ c :: suf)).
  Parameter children_spec : forall a ix n pre c, wf a ix -> node ix n pre ->
    (In c (children ix n) <-> exists m, child ix n c = Some m) /\ NoDup (children ix n).
  Parameter degree_spec : forall a ix n pre, wf a ix -> node ix n pre ->
    N.to_nat (degree ix n) = length (children ix n).
End INDEX.
Module Type INDEX_TIME.
  Include INDEX.
  Parameter width : t -> list (cell V.t) -> nat.      (* spec: max over cells and node ids of bits *)
  Parameter T_insert T_remove : list (cell V.t) -> t -> nat.
  Parameter T_child : t -> positive -> cell V.t -> nat.
  Parameter T_children : t -> positive -> nat.  Parameter T_degree : t -> positive -> nat.
  Parameter c_ix : nat.
  Parameter T_insert_le : forall r ix, T_insert r ix <= c_ix * (length r + 1) * (width ix r + 1).
  Parameter T_remove_le : forall r ix, T_remove r ix <= c_ix * (length r + 1) * (width ix r + 1).
  Parameter T_child_le : forall ix n c, T_child ix n c <= c_ix * (width ix [c] + 1).
  Parameter T_children_le : forall ix n, T_children ix n <= c_ix * (N.to_nat (degree ix n) + 1) * (width ix [] + 1).
  Parameter T_degree_le : forall ix n, T_degree ix n <= c_ix * (width ix [] + 1).
End INDEX_TIME.
Module Type INDEX_PLAN.
  Include INDEX_TIME.
  Parameter inv : t -> Prop.   (* edges/kids consistent: count = |kids|, tuple counts, nodes < next *)
  Parameter inv_wf : forall a ix, wf a ix <-> inv ix /\ (forall u, mem ix u -> length u = a).
  Parameter insert_path : forall ix r, inv ix -> inv (insert r ix).       (* walk, allocate, bump counts *)
  Parameter remove_path : forall ix r, inv ix -> inv (remove r ix).       (* decrement, unlink at zero *)
  Parameter T_insert_step : forall ix n c, T_insert_step ix n c <= 4 * c_map * (width ix [c] + 1) + 4.
End INDEX_PLAN.
```

- **Proof sketch.** `inv` holds when, for each node, the stored count equals `|kids|` and the tuple count equals the number of member suffixes. `mem` and `node` are defined from `edges` by paths. Each law follows from the single-step path lemmas by induction on the row.
- **Cost.** One insert or remove does `|r|` edge-map accesses. The bound is Θ(a·w), tight by `T_get_ge` of the trie.
- **Size.** About 650 lines.

### 1.8 `JoinSig.v`: Generic Join

```coq
Module Type JOIN.
  Declare Module V : VALUE.
  Declare Module I : INDEX with Module V := V.
  Parameter run : jplan -> list I.t -> list (list (cell V.t)).
  Definition project (lv : list nat) (b : list (cell V.t)) : option (list (cell V.t)) :=
    fold_right (fun i acc => match nth_error b i, acc with Some c, Some l => Some (c :: l) | _, _ => None end)
               (Some []) lv.
  Definition answer (p : jplan) (ixs : list I.t) (b : list (cell V.t)) : Prop :=
    length b = nvars p /\ Forall2 (fun lv ix => exists u, project lv b = Some u /\ I.mem ix u) (cols p) ixs.
  Definition wf_plan (p : jplan) (ixs : list I.t) : Prop :=
    length (cols p) = length ixs /\
    Forall2 (fun lv ix => StronglySorted lt lv /\ Forall (fun i => i < nvars p) lv /\ I.wf (length lv) ix) (cols p) ixs /\
    (forall i, i < nvars p -> exists lv, In lv (cols p) /\ In i lv).      (* every variable bound *)
  Parameter run_sound : forall p ixs b, wf_plan p ixs -> In b (run p ixs) -> answer p ixs b.
  Parameter run_complete : forall p ixs b, wf_plan p ixs -> answer p ixs b -> In b (run p ixs).
  Parameter run_nodup : forall p ixs, wf_plan p ixs -> NoDup (run p ixs).
End JOIN.
Module Type JOIN_TIME.
  Include JOIN.
  Declare Module IT : INDEX_TIME with Module V := V.        (* shares I in the implementation *)
  Parameter work : jplan -> list I.t -> nat.                 (* spec; mirrors the recursion *)
  Parameter wmax : jplan -> list I.t -> nat.                 (* spec; max index width *)
  Parameter T_run : jplan -> list I.t -> nat.  Parameter c_join : nat.
  Parameter T_run_le : forall p ixs, wf_plan p ixs -> T_run p ixs <= c_join * (work p ixs + 1) * (wmax p ixs + 1).
  Parameter T_run_ge : forall p ixs, wf_plan p ixs -> work p ixs <= T_run p ixs.       (* tightness *)
End JOIN_TIME.
```

- **Algorithm.** `go lvl ns pre acc`, structural on the remaining level count. At level `i`:
  - The participants `P_i` are the atoms whose next column is `i`.
  - Pick `j*` in `P_i` with the least `degree` at its current node. Ties go to the lowest position.
  - For each `c` in `children(j*)`, probe `child` in every other participant. If all exist, advance their nodes and recurse.
- **The `work` spec.** `work(i, ns) = 1 + |P_i|·(1 + deg_{j*}) + Σ_{c survives} work(i+1, ns')`.

```coq
Module Type JOIN_PLAN.
  Include JOIN_TIME.
  Parameter nodes_ok : jplan -> list I.t -> nat -> list (cell V.t) -> list positive -> Prop.
    (* atom j's node stands for project (filter (<lvl) lv_j) (rev pre) *)
  Parameter go : nat -> jplan -> list I.t -> list positive -> list (cell V.t) -> list (list (cell V.t)) -> list (list (cell V.t)).
  Parameter nodes_ok_root : forall p ixs, wf_plan p ixs -> nodes_ok p ixs 0 [] (map I.root ixs).
  Parameter step_ok : forall p ixs l pre ns c ns', wf_plan p ixs -> nodes_ok p ixs l pre ns ->
    advance p ixs l ns c = Some ns' -> nodes_ok p ixs (S l) (c :: pre) ns'.
  Parameter advance_none : forall p ixs l pre ns c, wf_plan p ixs -> nodes_ok p ixs l pre ns ->
    advance p ixs l ns c = None -> forall b, firstn (S l) b = rev (c :: pre) -> ~ answer p ixs b.
  Parameter go_sound : forall p ixs l pre ns acc b, nodes_ok p ixs l pre ns -> In b (go (nvars p - l) p ixs ns pre acc) ->
    In b acc \/ (answer p ixs b /\ firstn l b = rev pre).
  Parameter go_complete : forall p ixs l pre ns acc b, nodes_ok p ixs l pre ns -> answer p ixs b ->
    firstn l b = rev pre -> In b (go (nvars p - l) p ixs ns pre acc).
  Parameter go_nodup : (* disjoint prefixes => disjoint outputs *) ...
  Parameter T_go_le : forall p ixs l pre ns acc, nodes_ok p ixs l pre ns ->
    T_go (nvars p - l) p ixs ns pre acc <= c_join * (work_at p ixs l ns + 1) * (wmax p ixs + 1).
End JOIN_PLAN.
```

- **Cost reference.** Ngo–Ré–Rudra 2013, the Generic Join analysis.
- **AGM corollary, not a deliverable.** `work ≤ |cols|·nvars·AGM(q, |R_j|)` follows from the query-decomposition lemma (NPRR 2012, §4). The proved, tight bound is in terms of `work`.
- **Size.** About 1,000 lines.

### 1.9 `DatabaseSig.v`: tables, union-find, use lists, indexes, rebuild

State (in `Database.v`; the record type is top level and parameterised by its field types):
- `tables : FM.t (TM.t (option cell))`, holding key ↦ output per function.
- `uf`, `next`.
- `uses : UM.t (list (positive * list cell))`, keyed by class root.
- `pending : list positive`, the union losers.
- `all`, `fresh : SM.t I.t`, the slot indexes.
- `changed : bool`.

```coq
Module Type DATABASE.
  Declare Module V : VALUE.
  Declare Module I : INDEX with Module V := V.
  Parameter t : Type.
  Parameter init : list decl -> list (positive * list nat) -> t.        (* decls, index slots *)
  Parameter find : positive -> t -> positive * t.
  Parameter lookup : positive -> list (cell V.t) -> t -> option (option (cell V.t)) * t.
  Parameter make : positive -> list (cell V.t) -> t -> positive * t.     (* OId find-or-create *)
  Parameter put : positive -> list (cell V.t) -> option (cell V.t) -> t -> t.
  Parameter union : positive -> positive -> t -> t.
  Parameter rebuild : t -> t.
  Parameter index : nat -> bool -> t -> I.t.         (* slot, fresh-only? *)
  Parameter advance : t -> t.                        (* empties fresh indexes, clears changed *)
  Parameter changed : t -> bool.
  Parameter ids : t -> N.
  (* spec *)
  Parameter wf : t -> Prop.
  Parameter view : t -> Model.view (V := V.t).        (* row, same, kind *)
  Parameter repr : t -> positive -> positive.
  Parameter pending : t -> nat.
  Definition canonical db := forall f k o, row (view db) f k o ->
    forall i, In (Id i) (k ++ option_to_list o) -> repr db i = i.
  Inductive cong (db : t) : positive -> positive -> Prop :=      (* FD-congruence closure *)
    | cong_same i j : same (view db) i j -> cong db i j
    | cong_fd f k1 k2 i j : row (view db) f k1 (Some (Id i)) -> row (view db) f k2 (Some (Id j)) ->
        Forall2 (cell_rel (cong db)) k1 k2 -> cong db i j
    | cong_sym ... | cong_trans ... .

  Parameter same_repr : forall db i j, wf db -> same (view db) i j <-> repr db i = repr db j.
  Parameter wf_init : forall ds sl, wf (init ds sl).
  Parameter wf_put : forall f k o db, wf db -> kind_ok db f k o -> wf (put f k o db).
  Parameter wf_make : forall f k db, wf db -> wf (snd (make f k db)).
  Parameter wf_union : forall i j db, wf db -> wf (union i j db).
  Parameter wf_rebuild : forall db, wf db -> wf (rebuild db).
  Parameter wf_advance : forall db, wf db -> wf (advance db) /\ view (advance db) = view db /\ changed (advance db) = false.
  Parameter find_spec : forall i db, wf db -> fst (find i db) = repr db i /\ view (snd (find i db)) = view db.
  Parameter row_functional : forall db f k o1 o2, wf db -> row (view db) f k o1 -> row (view db) f k o2 -> o1 = o2.

  (* put: canonicalise, then insert or merge (OLat) or queue a union (OId conflict) *)
  Parameter put_rows : forall f k o db, wf db -> kind_ok db f k o ->
    let ck := map (canon db) k in let co := option_map (canon db) o in
    (forall f' k' o', row (view (put f k o db)) f' k' o' <->
       (row (view db) f' k' o' /\ (f', k') <> (f, ck)) \/
       (f' = f /\ k' = ck /\ combine db f (old db f ck) co = o')).
  Parameter put_same : forall f k o db i j, wf db -> kind_ok db f k o ->
    same (view (put f k o db)) i j <-> eqv_closure (fun a b => same (view db) a b \/ conflict db f k o a b) i j.
  Parameter put_quiet : forall f k o db, wf db -> kind_ok db f k o -> changed db = false ->
    changed (put f k o db) = false -> view (put f k o db) = view db /\ present_put (view db) f (map (canon db) k) o.
  Parameter make_spec : forall f k db, wf db -> kind db f = Some OId ->
    let '(i, db') := make f k db in
    (exists j, row (view db) f (map (canon db) k) (Some (Id j)) /\ i = repr db j /\ db' = db) \/
    (fresh_id db i /\ row (view db') f (map (canon db) k) (Some (Id i)) /\ extends_by db db' f k i).
  Parameter union_same : forall i j db k l, wf db ->
    same (view (union i j db)) k l <-> eqv_closure (fun a b => same (view db) a b \/ (a, b) = (i, j)) k l.
  Parameter union_rows : forall i j db, wf db -> row (view (union i j db)) = row (view db).

  (* rebuild: congruence closure + canonical rows with merged outputs *)
  Parameter rebuild_canonical : forall db, wf db -> canonical (rebuild db) /\ pending (rebuild db) = 0.
  Parameter rebuild_same : forall db i j, wf db -> same (view (rebuild db)) i j <-> cong db i j.
  Parameter rebuild_keeps : forall db f k o, wf db -> row (view db) f k o ->
    exists o', row (view (rebuild db)) f (map (canon (rebuild db)) k) o' /\ out_le (rebuild db) f (option_map (canon (rebuild db)) o) o'.
  Parameter rebuild_from : forall db f k' o', wf db -> row (view (rebuild db)) f k' o' ->
    exists srcs, srcs <> [] /\ Forall (fun '(k, o) => row (view db) f k o /\ map (canon (rebuild db)) k = k') srcs /\
                 o' = merged (rebuild db) f (map snd srcs).
  Parameter rebuild_idle : forall db, wf db -> canonical db -> pending db = 0 -> rebuild db = db.
  Parameter rebuild_congruent : forall db f k1 k2 i j, wf db -> pending db = 0 ->
    row (view db) f k1 (Some (Id i)) -> row (view db) f k2 (Some (Id j)) -> Forall2 (cell_rel (same (view db))) k1 k2 -> same (view db) i j.

  (* indexes *)
  Parameter index_all : forall db s new u, wf db -> I.mem (index s new db) u ->
    exists f perm k o, slot_of db s = Some (f, perm) /\ row (view db) f k o /\ u = permute perm (k ++ option_to_list o).
  Parameter index_all_complete : forall db s f perm k o, wf db -> slot_of db s = Some (f, perm) ->
    row (view db) f k o -> I.mem (index s false db) (permute perm (k ++ option_to_list o)).
  Parameter index_wf : forall db s new f perm, wf db -> slot_of db s = Some (f, perm) -> I.wf (length perm) (index s new db).
End DATABASE.
```

- **Semantic corollaries (proved once in `DATABASE_PLAN`, used by `Run`):**
  - `put_sat`, `make_sat` (extends ν by `ν i := con M f (den ν k)`), `union_sat` (under `ν i = ν j`) and `rebuild_sat`.
  - `rebuild_sat : sat M ν (view db) -> sat M ν (view (rebuild db))`. In the model, functional dependency forces `con f (den k1) = con f (den k2)` when the keys are congruent. `lat_merge` covers merged lattice outputs.
- **Time layer.**

```coq
Module Type DATABASE_TIME.
  Include DATABASE.
  Parameter unit : t -> nat.               (* spec: (log2 (ids db) + 1) * (max cell/key bits + 1) *)
  Parameter slots_of : t -> positive -> nat.   (* index slots of f *)
  Parameter potential : N -> t -> nat.     (* spec; B = id budget *)
  Parameter T_put T_make T_lookup ... T_union T_rebuild T_index T_advance : ... -> nat.
  Parameter c_db : nat.
  Parameter potential_init : forall B ds sl, potential B (init ds sl) = 0.
  Parameter T_put_amort : forall B f k o db, wf db -> ids (put f k o db) <= B ->
    T_put f k o db + potential B (put f k o db) <=
      c_db * (length k + 2) * (slots_of db f + 1) * (N.log2 B + 1) * unit db + potential B db.
  Parameter T_make_amort : (* same shape as put *).
  Parameter T_union_amort : forall B i j db, wf db ->
    T_union i j db + potential B (union i j db) <= c_db * unit db + potential B db.
  Parameter T_rebuild_amort : forall B db, wf db -> ids (rebuild db) <= B ->
    T_rebuild db + potential B (rebuild db) <= c_db * (pending db + 1) * unit db + potential B db.
  Parameter T_index_le : forall s new db, T_index s new db <= c_db * (Nat.log2 (S s) + 1).
  Parameter T_advance_le : forall db, T_advance db <= c_db * (num_slots db + 1).
End DATABASE_TIME.
```

- **The potential and its literature basis.** `potential B db = c·Σ_{use entries e} (N.log2 B − N.log2 (class_size (id e)))·(arity(e)+1)·(slots+1)` plus `c·|stale entries|`. This is DST's "relabel the smaller side" argument: under union by size, an entry is re-filed only when its id's class at least doubles.
- **Total rebuild cost for a run.** `O(S·a·log B·unit)`, where `S` is the number of rows inserted by actions. This matches DST and Nieuwenhuis–Oliveras up to the trie factor.

```coq
Module Type DATABASE_PLAN.
  Include DATABASE_TIME.
  Parameter inv : t -> Prop.
    (* I1 tables functional; I2 every id in a row has (f,k) in uses(repr id) (stale entries allowed);
       I3 every row holding a non-root id has an entry in uses(x) for some x in pending;
       I4 all-index <-> rows (permuted), fresh ⊆ all; I5 ids < next; I6 uf wf; I7 kinds respected *)
  Parameter inv_wf : forall db, wf db <-> inv db.
  Parameter rstep : t -> t + t.                          (* process one use entry of the head loser *)
  Parameter rstep_inv : forall db db', inv db -> rstep db = inl db' -> inv db'.
  Parameter rstep_cong : forall db db' i j, inv db -> rstep db = inl db' -> (cong db' i j <-> cong db i j).
  Parameter rstep_keeps : (* rebuild_keeps for one step *) ...
  Parameter rstep_from  : (* rebuild_from for one step *) ...
  Parameter rstep_done : forall db r, inv db -> rstep db = inr r -> canonical r /\ pending r = 0 /\ r = db.
  Parameter fuel_enough : forall db, inv db -> rebuild_measure db < rebuild_fuel db.
  Parameter rstep_measure : forall db db', inv db -> rstep db = inl db' -> rebuild_measure db' < rebuild_measure db.
  Parameter T_rstep_go : forall B db db', inv db -> ids db' <= B -> rstep db = inl db' ->
    T_rstep db + potential B db' < potential B db + c_db * unit db.         (* paid by doubling *)
  Parameter T_rstep_stop : forall db r, inv db -> rstep db = inr r -> T_rstep db <= c_db * unit db.
End DATABASE_PLAN.
```

- **Loop.** `rebuild := loop_fuel rstep (rebuild_fuel db)`. The fuel is computed from the data: `(log2 ids + 2)·(entries + 1) + pending + 1`. The contract follows from `T_loop_fuel_le` with `Phi := potential B`.
- **Size.** About 1,900 lines, the largest proof risk.
- **Reuse.** Its invariants are read from `EgraphCoreInvariant.v` and `EgraphCoreRebuildSemantic.v`.

### 1.10 `RunSig.v`: rule application, semi-naive rounds, saturation

```coq
Module Type RUN.
  Declare Module V : VALUE.
  Declare Module I : INDEX with Module V := V.
  Declare Module J : JOIN with Module V := V with Module I := I.
  Declare Module D : DATABASE with Module V := V with Module I := I.
  Parameter plan : program V.t -> compiled V.t.                     (* untrusted planner *)
  Parameter check_plan : program V.t -> compiled V.t -> bool.
  Parameter load : program V.t -> compiled V.t -> D.t.                (* empty db with slots *)
  Parameter round : program V.t -> compiled V.t -> bool (* naive *) -> D.t -> D.t.
  Parameter run : program V.t -> compiled V.t -> limits -> D.t -> stop * D.t.
  Definition plans_ok p cp := check_plan p cp = true.
  Definition grows db db' : Prop :=                  (* rows and equalities persist modulo canon *)
    (forall i j, same (D.view db) i j -> same (D.view db') i j) /\
    (forall f k o, row (D.view db) f k o -> exists o', row (D.view db') f (map (canon db') k) o' /\ out_le db' f (option_map (canon db') o) o').

  Parameter run_wf : forall p cp lim db, plans_ok p cp -> D.wf db -> D.wf (snd (run p cp lim db)) /\ D.canonical (snd (run p cp lim db)).
  Parameter run_grows : forall p cp lim db, plans_ok p cp -> D.wf db -> grows db (snd (run p cp lim db)).
  Parameter run_sat : forall p cp lim db (M : model) nu, plans_ok p cp -> D.wf db -> absent_free p = true ->
    valid M p -> sat M nu (D.view db) ->
    exists nu', (forall i, D.ids db > 0 -> (i < D.ids db)%positive -> nu' i = nu i) /\ sat M nu' (D.view (snd (run p cp lim db))).
  Parameter run_closed : forall p cp lim db db', plans_ok p cp -> D.wf db ->
    run p cp lim db = (Saturated, db') -> closed p (D.view db').
  Parameter run_derives : forall p cp lim db f k o, plans_ok p cp -> D.wf db -> datalog_fragment p = true ->
    no_ids db -> row (D.view (snd (run p cp lim db))) f k o -> derives p (D.view db) f k.
  Parameter run_least : forall p cp lim db db', plans_ok p cp -> D.wf db -> datalog_fragment p = true -> no_ids db ->
    run p cp lim db = (Saturated, db') -> forall w, closed p w -> includes (D.view db) w -> includes (D.view db') w.
  Parameter run_terminates : forall p cp lim db, plans_ok p cp -> D.wf db -> datalog_fragment p = true -> no_ids db ->
    N.to_nat (max_iter lim) >= 2 * herbrand p db + 2 -> fst (run p cp lim db) = Saturated.
  Parameter run_limits : forall p cp lim db, (fst (run p cp lim db) = IdLimit -> D.ids (snd (run p cp lim db)) > max_ids lim).
End RUN.
```

- **Loop.** `run` is `loop_fuel` with fuel `max_iter`. Each iteration does the following.
  - It runs semi-naive plans: for each rule and each pivot atom `i`, atom `i` reads `New` and the other atoms read `All`. Duplicates are absorbed because actions are idempotent.
  - Each match's actions are applied, then `rebuild` and `advance` run.
  - When a semi-naive round leaves `changed = false`, the next round is a **naive confirmation round** with every atom reading `All`.
  - If the naive round is also quiet, the result is `Saturated`, and closure is *proved* (`naive_quiet_closed`).
  - **Consequence.** Semi-naive completeness is an optimisation that is never needed for correctness. Exactly one naive round at the end is tested, not proved.
  - `IdLimit` is checked after each round.

```coq
Module Type RUN_TIME.
  Include RUN.  (* with D : DATABASE_TIME, J : JOIN_TIME *)
  Parameter trace : program V.t -> compiled V.t -> limits -> D.t -> list (bool * D.t).   (* spec: round starts *)
  Parameter round_work : program V.t -> compiled V.t -> bool -> D.t -> nat.
    (* Σ_plans J.work + Σ_matches (|actions|+|post|) *)
  Parameter T_run : program V.t -> compiled V.t -> limits -> D.t -> nat.  Parameter c_run : nat.
  Parameter T_run_le : forall p cp lim db, plans_ok p cp -> D.wf db ->
    T_run p cp lim db <= c_run * (sum (map (fun '(nv, d) => (round_work p cp nv d + 1) * (act_unit p (N.of_nat B) d))
                                          (trace p cp lim db))) + D.potential B db
    (* where B := max_ids lim + overshoot p *).
  Parameter T_check_plan_le : forall p cp, T_check_plan p cp <= c_run * (size p + size cp + 1) * (wbits p + 1).
End RUN_TIME.
Module Type RUN_PLAN.
  Include RUN_TIME.
  Parameter plan_match_sound : forall p cp db c b, plans_ok p cp -> D.wf db -> In c (all_plans cp) ->
    In b (bindings cp c db) -> matches (D.view db) (query (rule_at p (rule_ix c))) (env_of c b).
  Parameter naive_plans_complete : forall p cp db r s, plans_ok p cp -> D.wf db -> D.canonical db -> In r (rules p) ->
    matches (D.view db) (query r) s -> exists c b, In c (naive cp) /\ In b (bindings cp c db) /\ agrees (env_of c b) s (query_vars r).
  Parameter apply_wf : forall p acts s db, D.wf db -> D.wf (apply acts s db).
  Parameter apply_sat : forall M nu p r s db, valid M p -> In r (rules p) -> matches (D.view db) (query r) s ->
    sat M nu (D.view db) -> exists nu', extends nu nu' /\ sat M nu' (D.view (apply (actions r) s db)).
  Parameter apply_quiet_present : forall acts s db, D.wf db -> D.changed db = false ->
    D.changed (apply acts s db) = false -> present (D.view db) s acts.
  Parameter apply_grows : forall acts s db, D.wf db -> grows db (apply acts s db).
  Parameter apply_derives : (* Datalog fragment: each inserted row derives *) ...
  Parameter naive_quiet_closed : forall p cp db, plans_ok p cp -> D.wf db -> D.canonical db -> D.changed db = false ->
    D.changed (round p cp true db) = false -> closed p (D.view db).
  Parameter round_progress : (* Datalog: changed => some new row; quiet naive => Saturated *) ...
  Parameter T_round_le : forall p cp nv db, plans_ok p cp -> D.wf db ->
    T_round p cp nv db + D.potential B (round p cp nv db) <= c_run * (round_work p cp nv db + 1) * act_unit p B db + D.potential B db.
End RUN_PLAN.
```

- **Matching completeness.** Proved for naive plans on a canonical database: `Join.run_complete` together with `index_all_complete`. This is the relational e-matching theorem.
- **Size.** About 1,700 lines.

### 1.11 `ExtractSig.v`

```coq
Module Type EXTRACT.
  Declare Module V : VALUE. Declare Module I : INDEX with Module V := V.
  Declare Module D : DATABASE with Module V := V with Module I := I.
  Declare Module C : COST with Module V := V.
  Parameter best : D.t -> list (positive * (N * (positive * list (cell V.t)))).   (* root -> cost, chosen row *)
  Parameter extract : D.t -> positive -> option (list (positive * (positive * list (cell V.t)))).  (* DAG, children first *)
  Parameter check_dag : D.t -> positive -> list (positive * (positive * list (cell V.t))) -> option N.
  Parameter tree_cost : expr -> N.            (* spec, from C.fn_cost / C.val_cost *)
  Parameter best_row : forall db c n f k, D.wf db -> D.canonical db -> In (c, (n, (f, k))) (best db) ->
    row (D.view db) f k (Some (Id c)) /\ n = C.fn_cost f (map (cost_of (best db)) k).
  Parameter best_optimal : forall db c e, D.wf db -> D.canonical db -> represents (D.view db) (Id c) e ->
    exists n ch, In (c, (n, ch)) (best db) /\ (n <= tree_cost e)%N.
  Parameter best_attained : forall db c n ch, D.wf db -> D.canonical db -> In (c, (n, ch)) (best db) ->
    exists e, represents (D.view db) (Id c) e /\ tree_cost e = n.
  Parameter check_dag_sound : forall db c g n, D.wf db -> check_dag db c g = Some n ->
    dag_valid (D.view db) c g /\ n = dag_cost g /\ exists e, represents (D.view db) (Id c) e /\ unfold g c = Some e.
  Parameter extract_checked : forall db c g, D.wf db -> D.canonical db -> extract db c = Some g ->
    exists n m, check_dag db c g = Some n /\ In (c, (m, _)) (best db) /\ (n <= m)%N.
End EXTRACT.
Module Type EXTRACT_TIME.
  Include EXTRACT.
  Parameter R : D.t -> nat.  (* OId rows *)  Parameter a : D.t -> nat.  Parameter c_ex : nat.
  Parameter T_best_le : forall db, D.wf db -> T_best db <= c_ex * (R db * (a db + 1) + R db * (Nat.log2 (R db) + 1)) * (D.unit db + 1).
  Parameter T_check_dag_le : forall db c g, T_check_dag db c g <= c_ex * (length g + 1) * (a db + 1) * (D.unit db + 1).
  Parameter T_extract_le : forall db c, T_extract db c <= T_best db + c_ex * (R db + 1) * (a db + 1) * (D.unit db + 1).
End EXTRACT_TIME.
```

- **Plan (Knuth's invariant).**
  - `knuth_inv`: finalised classes hold costs ≤ every represented tree's cost.
  - A node enters the heap when its counter of unfinalised children reaches 0.
  - The popped minimum is final because of `fn_cost_super` and `fn_cost_mono`. Proving this is `pop_final`.
  - Then come `counter_spec`, `finalised_attained`, `T_step_amort` (via the core `PQ` potential), and the `loop_fuel` lemma with fuel `R+1`.
- **Size.** About 900 lines.
- **Certificate-checked.** An external optimal-DAG producer (ILP, or the treewidth algorithm of Goharshady et al.) run by the driver is accepted only through `check_dag`. No optimality is claimed for it.

### 1.12 Datalog front end (`theories/Datalog/`)

- **`Syntax.v`** converts the landed `DatalogSyntax.v`: `term`, `atom`, `literal`, `rule`. A program becomes plain data, `arities : list (positive * nat)`, with no `encoding` record or `arity_c` closure. The predicate is `safe_rule`.
- **`Model.v`** converts `DatalogModel.v`: `derives`, `perfect_model`, `least_model`.
- **`StratifySig.v` and `Stratify.v`:** a producer (the core SCC condensation plus longest-path levels) and a checker.

```coq
Module Type STRATIFY.
  Parameter stratify : dprogram -> option (list (positive * nat)).
  Parameter check_strat : dprogram -> list (positive * nat) -> bool.
  Parameter check_strat_sound : forall p lv, check_strat p lv = true -> stratification p (lookup lv).
  Parameter stratify_sound : forall p lv, stratify p = Some lv -> check_strat p lv = true.     (* by construction: returns only checked *)
  Parameter stratify_complete : forall p, stratify p = None -> ~ exists st, stratification p st.  (* from SCC exactness *)
  (* time: T_stratify p <= c * (|preds| + |literals| + 1) * (w + 1) ; T_check_strat same *)
End STRATIFY.
Module Type SOLVE.
  Declare Module E : RUN with Module V := KeyPosValue.      (* constants are positives *)
  Parameter compile_stratum : dprogram -> list (positive * nat) -> nat -> program positive.
  Parameter solve : dprogram -> list (positive * list positive) -> N -> outcome.  (* Solved db | OutOfFuel | Rejected *)
  Parameter solve_exact : forall p facts fuel db, program_wf p facts -> solve p facts fuel = Solved db ->
    forall q t, holds_db db q t <-> perfect_model p facts q t.
  Parameter solve_unstratifiable : forall p facts fuel, stratify p = None -> solve p facts fuel = Rejected.
  Parameter solve_adequate : forall p facts fuel, program_wf p facts -> (exists st, stratification p st) ->
    N.to_nat fuel >= 2 * herbrand p facts + 2 -> exists db, solve p facts fuel = Solved db.
  (* time: T_solve <= T_stratify + Σ_strata T_run bound (Run.T_run_le) *)
End SOLVE.
```

- **Plan.**
  - `compile_matches`: an engine match of `compile_stratum` coincides with satisfaction of the Datalog body, with negated atoms reading the frozen lower strata.
  - `stratum_least`, from `Run.run_least` and `run_derives`.
  - `strata_perfect`: induction on the levels, using the lemmas of the converted `DatalogExact.v`.
- **Size.** About 1,200 lines in all.

### 1.13 Equality-saturation front end (`theories/Eqsat/`)

- **`Syntax.v`:**
  - A flat pattern: `fpat := { nodes : list (pnode V); root : nat }` with `pnode := PHole h | PApp f (list nat) | PLit v`.
  - A flat term: `fexpr`, which is post-order.
  - `rewrite := { lhs : fpat; rhs : fpat; cond : list (atom V) }`.
  - Spec unfolding to `Model.expr`.

```coq
Module Type SATURATE.
  Declare Module E : RUN.   Declare Module X : EXTRACT with Module D := E.D.
  Parameter compile : list (positive * decl) -> list rewrite -> program E.V.t.
  Parameter add_expr : fexpr E.V.t -> E.D.t -> positive * E.D.t.
  Parameter saturate : list rewrite -> limits -> list (fexpr E.V.t) -> stop * E.D.t * list positive.
  Definition valid_rw (M : model) (rw : rewrite) : Prop :=
    forall tau, cond_holds M tau (cond rw) -> denote_pat M tau (lhs rw) = denote_pat M tau (rhs rw).
  Parameter add_expr_represents : forall e db, E.D.wf db -> represents (E.D.view (snd (add_expr e db))) (Id (fst (add_expr e db))) (unflat e).
  Parameter compile_valid : forall M ds rws, Forall (valid_rw M) rws -> valid M (compile ds rws).
  Parameter saturate_sound : forall M rws lim es st db cs i j e1 e2, Forall (valid_rw M) rws ->
    saturate rws lim es = (st, db, cs) -> represents (E.D.view db) (Id i) e1 -> represents (E.D.view db) (Id j) e2 ->
    same (E.D.view db) i j -> denote M e1 = denote M e2.     (* terms from the inputs' closure *)
  Parameter ematch_complete : forall db rw tau c, E.D.wf db -> E.D.canonical db ->
    represents (E.D.view db) (Id c) (inst tau (lhs rw)) -> cond_in_db db tau (cond rw) ->
    exists s, matches (E.D.view db) (flatten_lhs rw) s /\ s root_var = Some (Id (E.D.repr db c)).
  Parameter saturated_closed : forall rws lim es db cs rw tau c, saturate rws lim es = (Saturated, db, cs) ->
    In rw rws -> represents (E.D.view db) (Id c) (inst tau (lhs rw)) -> cond_in_db db tau (cond rw) ->
    represents (E.D.view db) (Id c) (inst tau (rhs rw)).
End SATURATE.
```

- **Soundness formulation.** Soundness is stated against every algebra `M`. A term represented in the result denotes `ν(class)` (`represents_den`). `run_sat` then gives the equal denotations.
- **E-class analyses** are `OLat m` functions written as ordinary rules, for example `const(Add a b) := prim add (const a) (const b)`. Constant folding (egg's "modify") is the rule `const(c) = v ⟹ union c (Make Num v)`.
- **Plan.** `flatten_spec`, `inst_represents`, `add_expr_step`, `represents_den`, `compile_rule_valid` and `closed_represents`.
- **Size.** About 1,100 lines.

### 1.14 Proved directly versus certificate-checked

- **Proved directly:** Index, Join, Database (all laws, including rebuild), Run soundness, closure (through the naive round) and Datalog leastness, the extraction tree optimality, and the Datalog and Eqsat front ends.
- **Checked:**
  - Join plans (`check_plan`), so the planner and its variable-order heuristics are untrusted.
  - The stratification (`check_strat`).
  - External DAG extractions (`check_dag`).
- **Tested, not proved:**
  - Semi-naive completeness, observed as exactly one confirmation round on the fixtures.
  - Extraction tie-breaking.

### 1.15 Cost summary

| Operation | Tight bound | Reference |
|---|---|---|
| Index insert/remove | Θ(a·w) | trie paths |
| Join | Θ(`work`·w); `work ≤` AGM·\|q\|·nvars (stated, not proved) | NPRR 2012, NRR 2013, Veldhuizen 2014 |
| put/make (amortised) | O(a·slots·log B·unit) | — |
| rebuild, whole run | O(S·a·log B·unit) amortised | DST 1980, Nieuwenhuis–Oliveras 2007 |
| union | O(log n·w), worst case | Tarjan–van Leeuwen 1984 (union by size) |
| run | Σ over rounds of (`round_work` + 1)·`act_unit` + Φ₀ | egglog §4, semi-naive |
| extract (tree) | O((R·a + R log R)·unit) | Knuth 1977 |

### 1.16 Landed files: convert, merge or go

- **`theories/Datalog/`:**
  - *Convert:* `DatalogSyntax.v` → `Datalog/Syntax.v`; `DatalogModel.v` → `Datalog/Model.v`; `DatalogStratify.v` → `Datalog/Stratify.v`. The stratify statements are kept and the algorithm is replaced by SCC.
  - *Merge as lemma sources:* `DatalogExact.v` (leastness) into `Datalog/Solve.v` and `Run.run_least`; `DatalogFire.v` (`fire_rule_exact`) into `Model.matches`; `DatalogJoinProof.v` into `Join`; `DatalogSemiNaivePivot.v` into the semi-naive planner.
  - *Go:* `DatalogRelation`, `DatalogCompile`, `DatalogCompileProof`, `DatalogSolve`, `DatalogSolveProof`, `DatalogEngine*`, `DatalogJoin`, `DatalogJoinCost`, `DatalogJoinFireCost`, `DatalogJoinPrepare*`, `DatalogJoinPreparedFire`, `DatalogJoinUpdateCost`, every `DatalogSemiNaive*` except the merged pivot file, `DatalogCost` and `DatalogPipelineCost`.
- **`theories/Egraph/`:**
  - *Convert:* `EgraphSyntax.v` → `Eqsat/Syntax.v` (flattened); `EgraphRules.v` (`EggSem` and rule soundness) → the `Eqsat` model and `valid_rw`.
  - *Merge:* `EgraphCoreRepresentation.v` (`represents`, `same_class`, `clean`) → `Egglog/Model.v` and `DatabaseSig.canonical`; `EgraphCoreInvariant.v`, `EgraphCoreSemantic.v`, `EgraphCoreRebuildSemantic.v` and `EgraphCoreRepair*.v` → the invariants of `DATABASE_PLAN`, as reading material.
  - *Go:* `EgraphEquality.v` (the syntactic `rel`, superseded by model soundness; revisit for explanations), `EgraphGraph`, `EgraphIndex`, `EgraphRebuild`, `EgraphSpec`, `EgraphInsertSpec`, `EgraphKernelCost`, and `EgraphCore{Forest,Work,Maintained,Domain,View,Batch,Transition,Progress,Structural,Index,Observation}`.
- **`theories/Fixpoint/`:** the statement of `FixpointLocalLeast.region_least` moves into `Incremental`. The other `FixpointLocal*` files are the core's call.

### 1.17 Size and risks

- **Size:** about 9,500 Rocq lines (Index 650, Join 1,000, Database 1,900, Run 1,700, Extract 900, Datalog 1,200, Eqsat 1,100, Model lemmas 300, Syntax and Model definitions 450 as groundwork).
- **Risks:**
  1. The rebuild spec (`rebuild_from`, `merged`) is the hardest proof. Mitigation: the step-level plan, and inheriting the egg kernel's invariants.
  2. The core may not provide `union_by_size` returning winner and loser. The fallback is a weaker bound.
  3. Index node ids are never reclaimed, so `width` grows with `log(total inserts)`. This is acceptable and is stated in `unit`.
  4. `TimeFun` coverage: no local or mutual fix. Executable data is kept flat for this reason. Groundwork must run `TimeFun` on every stub.
  5. Lattice merges have no termination argument and rely on limits only.
  6. The naive confirmation round costs one full join per saturation.

---

## 2. SSA construction and destruction (`theories/Ssa/`)

### 2.1 Citations

- **Construction:**
  - Cytron, Ferrante, Rosen, Wegman, Zadeck, TOPLAS 13(4) 1991.
  - Choi, Cytron, Ferrante, POPL 1991 (pruned SSA).
  - Briggs, Cooper, Harvey, Simpson, SPE 28(8) 1998 (semi-pruned SSA; the lost-copy and swap problems).
  - Sreedhar and Gao, POPL 1995.
  - Braun, Buchwald, Hack, Leißa, Mallon, Zwinkau, CC 2013.
  - Buchwald, Lohner, Ullrich, "Verified construction of static single assignment form", CC 2016.
- **Validation:** Barthe, Demange, Pichardie, "Formal verification of an SSA-based middle-end for CompCert", TOPLAS 36(1) 2014 (an untrusted generator with a verified validator).
- **Destruction:**
  - Sreedhar, Ju, Gillies, Santhanam, SAS 1999.
  - Boissinot, Darte, Rastello, Dupont de Dinechin, Guillon, CGO 2009 (parallel-copy sequentialisation, Algorithm 1).
  - Rideau, Serpette, Leroy, "Tilting at windmills with Coq", JAR 40(4) 2008.
- **Liveness:** Appel and Palsberg, *Modern Compiler Implementation*, §19; Brandner, Boissinot, Darte, Dupont de Dinechin, Rastello, INRIA RR-7503 2011 (per-variable path exploration).

### 2.2 Choice: Cytron with a validator, not Braun

- Braun's algorithm needs no dominance. However:
  - Its lookups recurse through predecessors with incomplete φs and sealing.
  - Removing trivial φs rewires use lists in a cascade, which is mutable-style state that is awkward in plain Gallina under `TimeFun`.
  - It needs an SCC post-pass for minimality on irreducible graphs.
  - The verified version (Buchwald et al.) is a large Isabelle development that we would port wholesale.
- The library already has proved dominators and frontiers. The Barthe–Demange–Pichardie route needs no proof about the producer at all: one validator theorem covers any construction, including a future Braun producer.
- Renaming over the dominator tree is trivial with persistent maps, because no stacks need popping.
- **Decision:** Cytron placement on the iterated dominance frontier, pruned by liveness, followed by dominator-tree renaming. Construction is validated; destruction is proved.

### 2.3 Data (`Ssa/Lang.v`, groundwork): one language for both forms

```coq
Inductive exit (X G : Type) : Type :=
  | Jump (b : positive) (args : list X)
  | Branch (g : G) (xs : list X) (b1 : positive) (a1 : list X) (b2 : positive) (a2 : list X)
  | Return (xs : list X).
Record block (X K G : Type) := Block { params : list X; code : list (X * K * list X); term : exit X G }.
Record func (X K G : Type) := Func { entry : positive; inputs : list X; blocks : list (positive * block X K G) }.
(* Imp: X = variables, no params/args, reassignment allowed.  SSA: X = values, unique definitions. *)
Inductive result (C : Type) := Returned (cs : list C) | Wrong | Timeout.

Module Type OPS.
  Parameter K G C : Type.
  Parameter eval : K -> list C -> option C.  Parameter test : G -> list C -> option bool.
  Parameter mov : K.  Parameter eval_mov : forall c, eval mov [c] = Some c.
End OPS.
(* Module Interp (O : OPS): run : nat -> func positive O.K O.G -> list O.C -> result O.C,
   block step: params := args (parallel, read in the old env), code in order, exit; missing var => Wrong. *)
Definition imp_form (p : func positive K G) : Prop.     (* no params, no args *)
Definition ssa_wf (s : func positive K G) : Prop.       (* unique defs; each use dominated by its def (strict) *)
```

If the core's SSA presentation is first-order data with the same shape, `Lang.v` re-exports it. Otherwise `Lang.v` carries `to_presentation` with a lemma that `ssa_wf` implies the core `ssa_laws`. Needed from the core: block parameters plus edge arguments as data, and no `_c` closures.

### 2.4 Signatures

```coq
Module Type LIVE.            (* untrusted producer; the validator checks what it relies on *)
  Parameter live_in : func positive K G -> list (positive * list positive).
  Parameter T_live_in : func positive K G -> nat. Parameter c_live : nat.
  Parameter T_live_in_le : forall p, T_live_in p <= c_live * (size p + live_size p + 1) * (w p + 1).
    (* live_size p = Σ_x Σ_{b ∈ L_x} (1 + indeg b): path exploration, Brandner et al. 2011 *)
End LIVE.

Module Type VALIDATE.
  Declare Module O : OPS.
  Definition cert := (list (positive * list (positive * positive)) * list (positive * list positive))%type. (* env, live *)
  Parameter check : func positive O.K O.G -> func positive O.K O.G -> cert -> bool.
  Parameter check_ssa : func positive O.K O.G -> bool.
  Parameter check_sound : forall p s c, imp_form p -> check p s c = true ->
    forall n ins, Interp.run n s ins = Interp.run n p ins.               (* lockstep *)
  Parameter check_ssa_sound : forall s, check_ssa s = true -> ssa_wf s.
  Parameter T_check_le : forall p s c, T_check p s c <= c_val * (size p + size s + cert_size c + 1) * (w p + 1).
  Parameter T_check_ssa_le : forall s, T_check_ssa s <= c_val * (size s + T_dom_bound s + 1) * (w s + 1).
End VALIDATE.
```

- **The checks.** For each block `b`, with `Γ := env b`, the checker does the following.
  - `dom Γ ⊇ live b`.
  - Each statement `(x, k, ys) ↔ (v, k, map Γ ys)`: every `y` is in `defined_so_far ∪ live b`, and then `Γ := Γ[x ↦ v]`.
  - The exit matches with arguments renamed.
  - For each edge `b → c` and each `x ∈ live c`: `x ∈ defined_in b ∨ x ∈ live b`, which is the liveness post-condition. Also, if `env c x` is parameter `i` of `c`, then `args[i] = Γ x`; otherwise `env c x = Γ x`.
  - At entry, `live entry ⊆ inputs`, and the SSA inputs are `map (env entry) inputs`.
- **Plan.**
  - `sim b σ_s σ_i := ∀ x ∈ live b, σ_s (env b x) = σ_i x`, with option-valued environments.
  - `code_sim`: one statement preserves the extended relation.
  - `edge_sim`: parameter binding re-establishes `sim c`.
  - `block_sim`: one block step gives equal outcomes, `Wrong` with `Wrong`, or related states.
  - `run_sim`: induction on fuel gives `check_sound`.
  - Dominance in `check_ssa` uses the core `dominates_b`.

```coq
Module Type BUILD.
  Declare Module O : OPS. Declare Module Va : VALIDATE with Module O := O.
  Parameter produce : func positive O.K O.G -> option (func positive O.K O.G * Va.cert).   (* Cytron *)
  Parameter build : func positive O.K O.G -> option (func positive O.K O.G).
    (* produce, then Va.check && Va.check_ssa; None if either fails *)
  Parameter build_correct : forall p s, imp_form p -> build p = Some s ->
    ssa_wf s /\ forall n ins, Interp.run n s ins = Interp.run n p ins.
  Parameter T_build_le : forall p, T_build p <= c_build *
    (size p + n p + e p + df_size p + Σ_x Σ_{b ∈ IDF_x} (1 + |DF b|) + live_size p + phi_args p + 1) * (w p + 1).
End BUILD.
```

- **Producer plan (cost only).** It runs the core dominators and DF, then `live_in`, then per-variable IDF worklists over DF filtered by liveness, then renaming with a persistent `Γ` in dominator-tree preorder. Renaming is a `loop_fuel` over an explicit stack with fuel `2n+1`.
  - Lemmas: `T_place_var_le` (Cytron §5: each block enters the worklist once per variable), `T_rename_le` (each statement and each edge argument costs O(w)), and `T_build_le`.
  - Validator completeness (the producer's output passes) is tested, not proved.

```coq
Module Type PARMOVE.
  Parameter seq : list (positive * positive) -> positive -> list (positive * positive).   (* Boissinot Alg. 1 *)
  Parameter check_moves : list (positive * positive) -> positive -> list (positive * positive) -> bool.
  Parameter check_moves_sound : forall par tmp sq, NoDup (map fst par) -> ~ In tmp (map fst par ++ map snd par) ->
    check_moves par tmp sq = true -> forall env x, x <> tmp -> exec_seq sq env x = exec_par par env x.
  Parameter T_seq_le : forall par tmp, T_seq par tmp <= c_pm * (length par + 1) * (bits_of par + 1).
  Parameter T_check_moves_le : forall par tmp sq, T_check_moves par tmp sq <= c_pm * (length par + length sq + 1) * (bits_of (par ++ sq) + 1).
  Parameter seq_length : forall par tmp, length (seq par tmp) <= 2 * length par.
End PARMOVE.

Module Type DESTROY.
  Declare Module O : OPS.
  Parameter destroy : func positive O.K O.G -> option (func positive O.K O.G).
    (* split critical edges into fresh blocks; per edge, seq (params c, args e) with a fresh temp, checked *)
  Parameter destroy_imp : forall s p, destroy s = Some p -> imp_form p.
  Parameter destroy_correct : forall s p, ssa_wf s -> destroy s = Some p -> forall n ins r, r <> Timeout ->
    (Interp.run n s ins = r -> Interp.run (2 * n) p ins = r) /\ (Interp.run n p ins = r -> Interp.run n s ins = r).
  Parameter T_destroy_le : forall s, T_destroy s <= c_ds * (size s + edge_args s + crit s + 1) * (w s + 1).
End DESTROY.
```

- **Why each problem is gone.**
  - Lost copy: every edge whose target has parameters and whose source has more than one successor is split, so no copy clobbers a value live on a sibling path (Briggs et al. 1998).
  - Swap: copies are a checked sequentialisation of a parallel assignment.
  - No coalescing is done: every SSA value keeps its own variable. Coalescing is future work (Boissinot et al. 2009, Sreedhar et al. 1999).
- **Plan.** `split_preserves` (one extra step per split edge), `edge_copy_sim` (from `check_moves_sound` and `eval_mov`), `block_sim`, `run_mono` (fuel monotonicity) and `destroy_correct`.
- **Size.** About 3,950 lines: Lang lemmas 200, Live 300, Validate 1,100, Build 1,100, ParMove 450, Destroy 800.
- **Risks.** Option-valued environments in the simulation; the dominance query depends on the core numbering; producer completeness is only tested.

---

## 3. Incremental and demand-driven re-analysis (`theories/Incremental/`)

### 3.1 Citations

- Muthukumar and Hermenegildo, JLP 1992 (the top-down solver).
- Fecht and Seidl, "A faster solver for general systems of equations", SCP 35 1999.
- Seidl and Vogler, "Three improvements to the top-down solver", PPDP 2018.
- Seidl, Erhard, Vogler, "Incremental abstract interpretation", LNCS 12065, 2020.
- Stade, Tilscher, Seidl, "The top-down solver verified", CAV 2024.
- Stein, Chang, Sridharan, "Demanded abstract interpretation", PLDI 2021.

### 3.2 Fit

- The state is a dependency-closed domain of solved keys with an influence map: Seidl's `stable` set and `infl`.
- `demand` extends the domain backwards from roots (local solving).
- `edit` destabilises the forward closure of changed rows (incremental TD).
- The region is solved by any core `SOLVER` over a restricted, seeded system and checked only on that region. A frame lemma covers the rest.
- DAIG's from-scratch consistency *under widening* depends on its fixed per-loop unrolling strategy. Our solver is strategy-agnostic, so with widening we claim soundness only, and equality only without widening.

```coq
Module Type SYSTEM_DEPS.   (* core SYSTEM + the extra executable fields of §1.4 *)
  Include SYSTEM.
  Declare Module KeyK : KEY with Definition t := key.   Declare Module RowK : KEY with Definition t := row.
  Parameter deps : prog -> row -> list key.  Parameter rows_of : prog -> key -> list row.
  Parameter reads_within : forall p r look1 look2, (forall x, In x (deps p r) -> look1 x = look2 x) -> eval p r look1 = eval p r look2.
  Parameter rows_of_spec : forall p x r, In r (rows_of p x) <-> In r (rows p) /\ target p r = x.
End SYSTEM_DEPS.

Module Type RESTRICT.     (* prog' = (p, frozen values, selected rows); seeds frozen keys with Ret *)
  Declare Module S : SYSTEM_DEPS.  Include SYSTEM_DEPS.
  Parameter mk : S.prog -> list (S.key * S.val) -> list S.row -> prog.
  Parameter restrict_post : forall p fz rs s, post_solution (mk p fz rs) s ->
    (forall r, In r rs -> S.L.leb (S.eval p r s) (s (S.target p r)) = true) /\ (forall x v, In (x, v) fz -> S.L.leb v (s x) = true).
End RESTRICT.

Module Type INCREMENTAL.
  Declare Module S : SYSTEM_DEPS.
  Parameter state : Type.  Parameter init : state.
  Parameter value : state -> S.key -> option S.val.
  Parameter demand : S.prog -> S.policy -> list S.key -> N -> state -> outcome * state.
  Parameter edit : S.prog -> S.prog -> list S.row -> state -> state.
  (* spec *)
  Definition dom st x := exists v, value st x = Some v.
  Definition closed p (D : S.key -> Prop) := forall r x, In r (S.rows p) -> D (S.target p r) -> In x (S.deps p r) -> D x.
  Definition post_on p st := forall r, In r (S.rows p) -> dom st (S.target p r) ->
    S.L.leb (S.eval p r (fun x => default (value st x))) (default (value st (S.target p r))) = true.
  Definition inv p st := closed p (dom st) /\ post_on p st.
  Definition least_on p st := forall s, S.post_solution p s -> forall x v, value st x = Some v -> S.L.leb v (s x) = true.
  Definition edit_covers p p' (ch : list S.row) := forall r, ~ In r ch ->
    (In r (S.rows p) <-> In r (S.rows p')) /\ (In r (S.rows p) -> S.target p r = S.target p' r /\
      S.deps p r = S.deps p' r /\ forall look, S.eval p r look = S.eval p' r look).
  Parameter init_inv : forall p, inv p init /\ least_on p init.
  Parameter demand_inv : forall p pol roots fuel st o st', inv p st -> demand p pol roots fuel st = (o, st') -> inv p st'.
  Parameter demand_covers : forall p pol roots fuel st st', inv p st -> demand p pol roots fuel st = (Done, st') ->
    forall x, In x roots -> dom st' x.
  Parameter demand_noop : forall p pol roots fuel st, (forall x, In x roots -> dom st x) ->
    demand p pol roots fuel st = (Done, st).
  Parameter edit_inv : forall p p' ch st, edit_covers p p' ch -> inv p st -> inv p' (edit p p' ch st).
  Parameter edit_keeps : forall p p' ch st x v, value (edit p p' ch st) x = Some v -> value st x = Some v.
  (* needs LEAST_SOLVER *)
  Parameter demand_least : forall p pol roots fuel st o st', S.monotone p -> widening_free pol ->
    inv p st -> least_on p st -> demand p pol roots fuel st = (o, st') -> least_on p st'.
  Parameter edit_least : forall p p' ch st, edit_covers p p' ch -> inv p st -> least_on p st -> least_on p' (edit p p' ch st).
  Parameter from_scratch_agrees : forall p st s x v, S.monotone p -> inv p st -> least_on p st ->
    least_solution p s -> value st x = Some v -> S.L.leb (s x) v = true /\ S.L.leb v (s x) = true.
End INCREMENTAL.
Module Type INCREMENTAL_TIME.
  Include INCREMENTAL.
  Parameter region : S.prog -> list S.key -> state -> list S.row.        (* spec: new rows discovered *)
  Parameter invalidated : S.prog -> list S.row -> state -> list S.key.  (* spec *)
  Parameter T_demand_le : forall p pol roots fuel st, inv p st ->
    T_demand p pol roots fuel st <= c_inc * (Σ_{r ∈ region p roots st} (length (S.deps p r) + 1) + length roots + 1) * (w + 1)
                                   + Sol.T_bound (R.mk p (frozen p roots st) (region p roots st)).
  Parameter T_edit_le : forall p p' ch st,
    T_edit p p' ch st <= c_inc * (Σ_{x ∈ invalidated p' ch st} (infl_deg st x + 1) + Σ_{r ∈ ch} (length (S.deps p' r) + 1) + 1) * (w + 1).
End INCREMENTAL_TIME.
```

- **Functor.** `Module Incremental (S : SYSTEM_DEPS) (R : RESTRICT with Module S := S) (Sol : SOLVER with Module Sys := R) (KM : MAP …) (KS : SET …)`. The shape was checked in the REPL.
- **Certificate-checked.** `demand` runs `Sol.run` on `R.mk p frozen region`, then `check_post_rows` on the region rows only. A failure gives `Rejected` and leaves the state unchanged.
- **Plan.**
  - `discover_closed`: the backward closure plus the old domain is closed.
  - `frame_post`: rows targeting the old domain read only the old domain, so `post_on` carries over.
  - `merge_inv`.
  - `invalidate_closed`: the forward closure under `infl` is removed. Stale `infl` edges only over-approximate.
  - `edit_frame`: unchanged rows that target the kept domain read only the kept domain, by `closed` and `reads_within`.
  - `region_least_restricted`: `LEAST_SOLVER.run_least` on the restricted system, plus seeds that are ≤ every post-solution by `least_on`, gives `least_on`.
  - `from_scratch_agrees`: patch `s` with `value` on the domain to get a post-solution, as in the current `region_least`.
- **Size.** About 1,600 lines (Restrict 350, Incremental 1,250).
- **Risks.**
  - It depends on the core exposing executable `deps`, `rows_of` and `check_post_rows`, and `LEAST_SOLVER`.
  - `edit_covers` is a semantic premise discharged by the front ends, for example "edges not leaving the edited block keep their rows".
  - Soundness itself never depends on that premise for the checked region, only for the frame.

---

## 4. The executable pipeline

### 4.1 Layout

- `theories/Exec/Instances.v` applies the functors to concrete modules:
  - `PosKey`, `TrieMap`, `TrieSet` and `UnionFindSize` from the core.
  - A `ZValue : VALUE_TIME` with prims add, sub, mul, div, lt and eq, and merges min, max and interval-meet.
  - `Engine := Run …`, `DatalogSolve`, `Eqsat`, `Ssa` over a `ZOps : OPS`, the analyses over the core frameworks, and `Incremental`.
- `theories/Exec/Roots.v` defines plain-data entry points that take lists, positives and `Z`, for example `egglog_run`, `datalog_solve`, `ssa_build`, `ssa_destroy`, `analyze_interval` and `reanalyze`. No functor types appear at the boundary.
- `extraction/Extract.v` uses `Require Import ExtrOcamlBasic.` and `Separate Extraction Roots.` Functor applications extract as OCaml applications; only applied modules are rooted. A dune `rocq.extraction` stanza produces `galois_extracted`.
  - No `ExtrOcamlNatInt` and no Zarith mapping by default, so the cost model (`positive`/`N` per bit) stays honest. An opt-in `bench` profile may add `ExtrOcamlZBigInt`, listed in its trusted base.
- `driver/` (OCaml, Core and Command):
  - `ir.ml`, `lex.ml`, `parse_imp.ml`, `parse_dl.ml` (Soufflé subset), `parse_egg.ml` (egglog subset), `intern.ml`, `lower.ml`, `print.ml`, `main.ml`.
  - Subcommands: `galois ssa|analyze|datalog|egglog FILE`.
  - Exit codes: 0 on success, 1 on a parse error, 2 on `Rejected` or `OutOfFuel`.
- `bench/`: `gen.ml` generates families at doubling sizes:
  - Datalog transitive closure on chains, cycles and G(n,p).
  - Andersen and Steensgaard on synthetic programs.
  - Eqsat associativity and commutativity on n leaves, iteration-limited.
  - SSA build and destroy on nested loops with V variables.
  - Incremental edits on a chain of n blocks.
  - `bench.ml` times the extracted roots and prints CSV `(family, n, seconds, predicted_bound)` with a log-log slope check.

### 4.2 Textual IR

```
func   ::= "func" IDENT "(" [IDENT {"," IDENT}] ")" "{" block+ "}"
block  ::= LABEL ":" { stmt ";" } exit ";"
stmt   ::= IDENT "=" OP "(" [arg {"," arg}] ")" | IDENT "=" arg
arg    ::= IDENT | INT
exit   ::= "goto" LABEL | "if" OP "(" args ")" "goto" LABEL "else" LABEL | "return" [args]
-- Datalog: ".decl p(x:number, ...)", facts "p(1,2).", rules "h(x) :- a(x,y), !b(y)."
-- egglog: (datatype ..) (function f (S..) T [:merge min|max|meet]) (relation ..) (rule (..) (..))
--         (rewrite l r [:when (..)]) (union a b) (let x e) (run N) (extract e) (check ..)
```

### 4.3 Trusted base

1. The Rocq kernel and Stdlib, with no axioms and closed `Print Assumptions` on every root.
2. The *statements*: `Egglog/Model.v`, `Datalog/Model.v` (`perfect_model`), `Ssa/Lang.v` (the interpreter), the core `post_solution` and the analysis semantics.
3. Extraction (Letouzey), the `ExtrOcamlBasic` mappings, and the OCaml compiler and runtime.
4. The driver: lexers, parsers, name interning, lowering and printing. A wrong parse gives a wrong question, not an unsound answer to the question asked.
5. For cost claims only: Argent's `TimeFun` translator, the `TimePrim` table and its agreement with the extraction mapping.

Untrusted: every producer (planner, SCC stratifier, SSA builder, liveness, sequentialiser, solvers, external DAG extractors), the benchmark generators, and any SMT or ILP tool.

### 4.4 Tests (only what no theorem states)

- Parser round trips and positions (OCaml expect tests).
- Producer completeness: `build`, `destroy` and `stratify` never return `None` or `Rejected` on fixtures.
- Exactly one naive confirmation round on Datalog fixtures.
- Extraction tie-breaking.
- End-to-end driver outputs.
- The benchmark slopes.

---

## 5. Triage of the specialised analyses

| Analysis | Now? | Behind | Route | Subsumed by the engine? | Cost to convert |
|---|---|---|---|---|---|
| PRE (about 17k lines of SSAPRE/FRG in `Analyses/Ssa/AnalysesSsaPre*`) | **No**; delete | the core gen/kill framework | Later: Lazy Code Motion (Knoop, Rüthing, Steffen, PLDI 1992), four bit-vector problems plus placement and a transformation proof. SSAPRE (Kennedy et al., TOPLAS 1999) is too large to port. | No; it is a transformation | about 3k new lines; porting the old code is not worth it |
| GVN (6.4k, `Analyses/Equality`) | After the batches | `Eqsat` and a `CONGRUENCE` checker | Pessimistic value numbering is congruence closure over SSA (DST 1980): constructor rows `op(args)=v` with φ as `phi(block, args)`; just run the engine. Optimistic (Alpern, Wegman, Zadeck, POPL 1988; Click PLDI 1995) uses an untrusted Hopcroft refinement producer, a `check_congruence` checker in O(n·a·w), and a proved theorem "a congruence partition implies equal runtime values", by induction on execution. | Pessimistic yes; optimistic via the checker | about 1.2k |
| SCEV (8.5k, `Analyses/Loops`) | Later | `Ssa/Lang` plus a checker | Chains of recurrences (Bachmann, Wang, Zima, ISSAC 1994; van Engelen, CC 2001; Pop, Cohen, Silber 2005) with an untrusted recogniser. The checker verifies that the header φ's initial argument equals the base and its back-edge argument equals `v ⊕ step` symbolically; soundness is by induction on iterations. | Chrec algebra could run as Eqsat rules; not needed | about 1.5k |
| SSA liveness (1.1k) | **Now** (WP2) | `Ssa/Live.v` | Per-variable path exploration (Brandner et al. 2011), used as the SSA certificate. Boissinot's fast liveness checking (CGO 2008) is later. | — | 300 |
| Memory SSA (legacy, about 6k, complete in the old architecture) | Later | `Ssa/Build` over the core memory presentation | Chow et al., CC 1996 (HSSA) and Novillo 2007: run the SSA builder with "variables" = alias classes from the core alias oracle (a may-def is a def plus a use). The validator theorem carries over. | Subsumed by the SSA builder | about 800 |
| Points-to (legacy Andersen and unification) | After the batches; small | `Datalog` and `Egglog` programs | Andersen (1994) is four Datalog rules (Whaley and Lam, PLDI 2004; Bravenboer and Smaragdakis, OOPSLA 2009). Steensgaard (POPL 1996) is egglog: `pts : Var -> Id` with `union` on assignments; functional-dependency rebuild performs the "conditional join" unification. Soundness: the client proves the rules valid in the concrete memory semantics (`Model.valid`); `run_sat` and `solve_exact` do the rest. | **Yes, fully** | about 800 for both, with soundness |

All of `theories/Analyses/` goes; the legacy archive keeps the reference proofs.

---

## 6. Work packages

Each session owns disjoint paths and never edits `*Sig.v`. Every `Sig` file lists `FOO`, `FOO_TIME` and `FOO_PLAN` as above. The statements in each `FOO_PLAN` are the chain a session closes, one lemma at a time.

| WP | Batch | Owns | Closes | Lines | Hours |
|---|---|---|---|---|---|
| **WP1 Engine kernel** | 1 | `theories/Egglog/{Index,Join,Database,ModelFacts}.v`; `tests/Egglog/{Index,Join,Database}Test.v` | `INDEX_PLAN`, `JOIN_PLAN`, `DATABASE_PLAN` (including `rebuild_sat`, `put_sat`, `make_sat`, `union_sat`) | about 3,850 | 5–6 |
| **WP2 SSA** | 1 | `theories/Ssa/{Live,Validate,Build,ParMove,Destroy}.v`; `tests/Ssa/*` | `LIVE`, `VALIDATE`, `BUILD` (cost plus correctness), `PARMOVE`, `DESTROY` | about 3,750 | 5 |
| **WP3 Run and front ends** | 2 | `theories/Egglog/Run.v`; `theories/Datalog/{Stratify,Solve}.v`; `theories/Eqsat/{Compile,Saturate}.v`; their tests | `RUN_PLAN`, `STRATIFY`, `SOLVE`, `SATURATE` | about 4,000 | 5–6 |
| **WP4 Extraction, incremental, clients** | 2 | `theories/Egglog/Extract.v`; `theories/Incremental/{Restrict,Incremental}.v`; `theories/Exec/{Instances,Roots}.v`; `theories/Clients/{Andersen,Steensgaard}.v`; tests | `EXTRACT_PLAN`, `INCREMENTAL_PLAN`, `RESTRICT`, the client validity lemmas | about 3,650 | 5 |

- **Priority** if my area gets fewer than four sessions: WP1 > WP3 > WP2 > WP4.
  - With two sessions: WP1 in batch 1 and WP3 in batch 2.
  - With three: add WP2 in batch 1.
- WP3 could start in batch 1 because it is written against frozen signatures. I sequence it after WP1 so the `DATABASE` laws are validated first.

**Groundwork for our own agents, before batch 1:**
1. Delete or convert the landed files as in §1.16; delete `theories/Analyses/`.
2. Write the data files: `Egglog/Syntax.v`, `Egglog/Model.v` (definitions only), `Datalog/Syntax.v`, `Datalog/Model.v` (ported), `Eqsat/Syntax.v` (flat forms and unflattening), `Ssa/Lang.v` (data and interpreter).
3. Write every `*Sig.v` above, with the needed core fields of §1.4 present in the core signatures, and compile them against the core `Sig` stubs.
4. Write the stub `Foo.v` files, each ascribed `<: FOO_PLAN`, with `Admitted`.
   - Run `TimeFun` on every stub body shape. Expect no local fix, no stored closures and `N` counters, and confirm with Argent.
   - Give the internal state record types at top level, parameterised by their field types.
5. Write the dune files, test skeletons, extraction skeleton and `Roots.v` signatures.
6. Write the OCaml driver and parsers against the stubbed extraction. This can continue during batch 1.

**What remains after both batches:**
- The end-to-end driver and the benchmark runs (own agents).
- GVN with its congruence checker, SCEV with its chrec checker, the memory SSA instance and LCM.
- The AGM corollary for `Join.work`.
- An O(α(n)·w) amortised union-find (Charguéraud–Pottier).
- A proof of semi-naive completeness, which would remove the confirmation round's cost from the bound.
- Proof-producing explanations (Flatt et al., "Small proofs from congruence closure", FMCAD 2022) with a checker.
- An optional Braun producer behind the same validator.
- DAIG-style consistency under widening.

### Critical files for implementation
- /home/nandhagk/Projects/argent/docs/design.md (sections 4, 5 and 7: loop combinators, signature conventions, defunctionalisation)
- /home/nandhagk/Projects/galois-integrate/theories/Egraph/EgraphCoreInvariant.v (the rebuild invariants for `DATABASE_PLAN`)
- /home/nandhagk/Projects/galois-integrate/theories/Datalog/DatalogStratify.v and /home/nandhagk/Projects/galois-integrate/theories/Datalog/DatalogModel.v (to convert)
- /home/nandhagk/Projects/galois-integrate/theories/Fixpoint/FixpointLocalLeast.v (`region_least`, reused by Incremental)
- /home/nandhagk/Projects/galois-integrate/theories/Graph/GraphFrontierSweep.v and /home/nandhagk/Projects/galois-integrate/theories/Program/ProgramSsa.v (frontiers for Cytron; the SSA presentation that `Ssa/Lang.v` must match or adapt)