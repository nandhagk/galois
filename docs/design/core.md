# Galois core architecture: final design

## 0. Status, validation and reconciliation

**What was checked.** Every module-system pattern this design relies on was run in the Rocq 9.3 REPL; section 9 lists them with outcomes. Three larger pieces compiled end to end:

1. A miniature of the whole stack (keys, lattices, queries, `SYSTEM`, a solver, `check_post`, certification with narrowing, a CFG presentation, the abstract-interpretation framework with its soundness theorem **proved**, an interval domain, a non-relational state, a toy language). The analysis ran under `vm_compute`, the soundness theorem was instantiated, a concrete corollary (`i = 10` at the loop exit) closed with `Qed`, and the code tower extracted to OCaml functors with no proof or time fields.
2. The union-find skeleton of section 6, as written there except for the `TimeFun` lines.
3. The converted `Dual` combinator of section 7, at all three levels.

**What was not checked.** `Argent` has no theories yet, so no `TimeFun` call was run. Where a time function is needed in a validated snippet I wrote by hand the definition `TimeFun` is specified to generate, and say so. I did check, with a small Elpi command in the Argent shell, that the *lookup rule* `TimeFun` depends on behaves as needed under `Include` (section 9, V9). The user-story code in section 5 uses the final catalog names; the miniature that compiled differs in the ways listed there. Line estimates are estimates.

**One slip.** A scratch command created an empty directory `/tmp/claude-galois-scratch`. Nothing was written into it and no repository was touched. I left it in place rather than run a delete.

### 0.1 Requests from the other two architects

Accepted as asked:

| From | Request | Where |
|---|---|---|
| engines, domains | `KEY` with `t`, `eqb`, `eqb_spec`, `encode`, `encode_inj`, `bits`, and `T_eqb`, `T_encode` in `bits` | §3.1 |
| engines | pair and list key combinators with bit bounds | §3.1; my bounds are tighter (`2·bits a + bits b − 1`; lists `2·Σbits − length + 1`) and imply theirs |
| domains | `OptKey` | core `OptionKey`, same encoding (`None ↦ 1`, `Some x ↦ (encode x)~0`) |
| engines, domains | `MAP`: `empty get set remove merge forall2b existsb fold elements`, spec `nodes`, laws, per-key and higher-order time contracts, `T_elements` in `Σ(bits k + 1)` | §3.1 |
| engines | `SET` | §3.1 |
| engines | `UNION_FIND` on `positive`, `union` returning `(winner, loser)`, `repr`, `size_of`, `card`, `union_by_size`, `T_find ≤ c·(log2 card + 1)·(bits + 1)` | §6, complete skeleton |
| engines | `PQ` with amortised contract and exported potential | §3.1 |
| engines | first-order graphs with `succs preds nodes`; dominator tree as children lists with pre/post numbers; `dominates_b` in O(w); `frontier` with `df_spec` and the Cooper–Harvey–Kennedy bound; SCC exactness | §3.4 |
| domains | `Wto.heads` and the cycle-cut corollary | `Wto.check_cuts`, §3.4 |
| domains | `WIDENING` with `wparam`, `wrank`, `wrank_widen`, `wrank_widen_le`, `widen_stable`, `narrow_between` | §3.2, verbatim; `is_bot` added to `LATTICE` |
| domains | `VALUE_DOMAIN` fields and laws, `LANG`, `term`, `STATE_DOMAIN` fields and laws | §3.3 |
| engines, domains | `SYSTEM.post_solution`, `check`, `check_sound`, `T_check_le`, `check_post_rows` | §3.5 (`Check.check`, `Check.check_rows`) |
| engines | `SOLVER.run : prog -> policy -> N -> outcome`, spec `work`, `T_run ≤ c·(work + 1)`, optional `LEAST_SOLVER` | §3.5 |
| domains | the theorem that a certified post-solution covers the reachable states | `InterpSound.covers` with `Certified.analyze_sound`, §3.7 |
| coordinator | `Z`, `N`, `positive` priced by bit length | rule R12 |
| coordinator | no `Datalog` package; term front end named `Egraph` | §2 |

Changed, with the reason:

| Request | What I give instead | Why |
|---|---|---|
| Time layer as a separate functor argument, `(L : LANG) (LT : LANG_TIME L)` (domains) | one bundled argument, `(L : LANG_T)` | `TimeFun` finds `L.T_eval` only as a sibling of `L.eval`, in the same module path. Checked: section 9, V9 |
| `FOO_TIME` that `Include`s `FOO` (engines) | `FOO_TIME` is the layer; the bundle is `FOO_T := FOO <+ FOO_TIME` | Read their `(X : FOO_TIME)` as `(X : FOO_T)`. Content is identical |
| `Declare Module V : …` inside a signature, shared by `with Module` (both) | the component is a parameter of the module type: `STATE_DOMAIN X L V`, `MAP X` | A nested module cannot be strengthened by a later layer, so a signature that nests `V : VALUE_DOMAIN` can never offer `V.T_forward`. Parameters layer cleanly |
| `SYSTEM` with nested `KEY` modules for keys and rows (engines) | inline `key_code`, `row_code`; adapters `SystemKey`, `SystemRow` produce `KEY` modules | Same reason; it also lets a framework define derived keys (pairs, sums) with a code function and no module plumbing |
| `rows_of` and a key on rows in the base `SYSTEM` (engines) | an extension layer `LOCAL` (`LOCAL_SYSTEM := SYSTEM <+ LOCAL`), plus a generic `Indexed` functor that supplies it for any system | Only demand-driven clients need it. The global solver numbers rows by position, so ordinary frameworks need no edge keys |
| `eval p r look : val` (engines) | `eval p r look : option (val * list (key * val))`; `post_solution` is stated through the boolean `row_ok` | Side contributions and the query fuel are part of the meaning. Their `leb (eval …) (s (target …)) = true` becomes `row_ok … = true` |
| `rows_of_spec` over `target` only (engines) | over `writes p r := target p r :: sides p r` | A row outside the domain can contribute into it through `Side` |
| `Policy` and `Narrow` in package `Widening` (domains) | they live in `Fixpoint/`; `Widening` keeps `Mining` | The solver consumes them, and `Fixpoint` may not depend on `Domains`. Their statements are kept verbatim |
| `Record policy` inside functor `Policy`, `heads : MX.t head_cfg` (domains) | a top-level `policy (W : Type)` with `heads : PTrie.t head_cfg` keyed by key code | Records inside functors are generative (checked by the earlier session), and the shared convention forbids them |
| `elements` in increasing `encode` order (domains) | trie order (the landed `code_compare`), sorted and duplicate-free | That is what a trie traversal yields in linear time; numeric order would cost a sort |
| laws on `elements` unconditional | they carry a premise `wf m` that every operation preserves | A keyed trie stores the key next to the value; a hand-built value could store a key at the wrong code |
| SCC *condensation* (engines) | kept as a small derived function, deferred | Its only consumer was the Datalog stratifier, which is no longer built |

New requests from me:
- **Domains:** a spec-only `BUDGET` instance for `Interval` and `Env` (an invariant on values, a size bound, a widening-rank bound; §3.5). Only the timed tower needs it.
- **Domains:** the state-level `Disj` and `Partition` should `Include` the lattice-level `Disjunction` and `MapLattice` for their lattice part.
- **Engines:** `Incremental.demand` replaces the landed local engine, so `FixpointLocal*` is theirs to harvest before it is deleted.
- **Argent:** a mutual or nested `fix` (needed by `term`, a domains risk) and the `CostStd` contracts for `N.pred`, `N.succ`, `Pos.eqb`, `N.leb`, `N.add`, `N.size_nat`.

---

## 1. Design rules, final

**R1. Four layers per component, in `FooSig.v`.** Dependencies of a component are parameters of its module types.

```coq
Module Type FOO_OPS  (K : KEY_OPS).                            (* what runs; this is what extraction sees *)
Module Type FOO_SPEC (K : KEY_OPS) (Import F : FOO_OPS K).     (* optional; Definitions only *)
Module Type FOO_LAWS (K : KEY) (Import F : FOO_OPS K).         (* spec Parameters and functional laws *)
Module Type FOO      (K : KEY)   := FOO_OPS K <+ FOO_SPEC K <+ FOO_LAWS K.   (* the functional layer *)
Module Type FOO_TIME (K : KEY_T) (Import F : FOO K).           (* T_op, constants, contracts, bigO *)
Module Type FOO_T    (K : KEY_T) := FOO K <+ FOO_TIME K.
Module Type FOO_PLAN (K : KEY_T) (Import F : FOO_T K).         (* internals, named constants, lemma chain *)
Module Type FOO_ALL  (K : KEY_T) := FOO_T K <+ FOO_PLAN K.
```

- `_OPS` holds types, functions and closed constants, and nothing else.
- `_SPEC` holds derived definitions with bodies (`bits`, `post_solution`). A signature gets them through `<+`, an implementation through `Include FOO_SPEC K.`, so each is written once and Rocq checks the bodies agree (V5).
- `_LAWS` holds spec-only parameters, named in a `(* spec: … *)` pragma, and the laws.
- `_TIME` holds one `Parameter T_op` per operation (with a companion after each function argument), named constants `c_foo`, contracts `T_op x <= c_foo * (…)` or amortised contracts over an exported potential, and the published `bigO` corollaries.
- `_PLAN` holds the internals the proof talks about (as `Parameter`s, with their `T_`), named constants `k_*` whose values the implementer chooses, invariants and potentials as manifest definitions, and the chain: `F`-lemmas, then `T`-lemmas, ending at the contracts.
- Laws are written with `Parameter` inside module types (Argent's lint reads that keyword). `Axiom` is a synonym there and creates no axiom.

**R2. Three modules per component, in `Foo.v`, as an `Include` chain.**

```coq
Module FooCode (K : KEY_OPS) <: FOO_OPS K.   (* definitions only *)                       End FooCode.
Module Foo     (K : KEY)     <: FOO K.       Include FooCode K. (* spec, laws *)          End Foo.
Module FooT    (K : KEY_T)   <: FOO_ALL K.   Include Foo K. (* TimeFun, contracts, plan *) End FooT.
```

- A level with no content is omitted. A solver has no laws layer, so `WorklistT` includes `WorklistCode`.
- `FooCode K`, `Foo K` and `FooT K` have convertible operations. `Check (eq_refl : @Mc.get = @M.get)` passed (V3).
- A soundness functor that needs extra parameters (a semantics, a link) is a sibling of `FooT`: `FooSound (…) (M : SEMANTICS P) (K : LINK …)` also starts with `Include Foo …`.

**R3. A client states the layers it needs by the type of each parameter.** `(L : LATTICE_OPS)` to run, `(L : LATTICE)` to prove, `(L : LATTICE_T)` to bound. Each dependency is one module argument. Time fields are never passed as a separate argument (V9).

**R4. Running without law proofs stays possible, by construction.** The code tower takes `_OPS` arguments, so a domain with no proofs runs and extracts with no `Admitted` anywhere. Certification needs no laws either: `check` reflects `post_solution` definitionally. A client proves only what its theorem uses.

**R5. Value-dependent parameters are values.**
- A program, a policy and widening parameters are ordinary data. A signature that needs one declares an abstract type for it: `prog`, `wparam`.
- A bit width is part of the operator or of the abstract value (`BitsLang` operators carry widths).
- A height that depends on data is a function of data: `wrank : wparam -> t -> nat`.
- Laws that hold only for sensible data are guarded by a spec predicate (`wf : prog -> Prop`, `wf : t -> Prop`).
- A module-level constant (`Module Type CAP. Parameter k : nat. …`) is allowed only for a value fixed for the life of the extracted program.

**R6. Data is top level and first order.** Inductives and records are declared outside functors, parameterised by types (`query K A F`, `policy W`, `digraph`, `wto`, `uf`). No closure is stored in data. A callback is a functor parameter (visitors, transfer functions) or a function argument with a companion.

**R7. Generic executable helpers are top-level higher-order functions.** `eval_query`, `row_ok`, `pair_code`, `loopN` take their callbacks as arguments. There is then one definition and one `T_`, and no functor instance to share.

**R8. Sharing and diamonds.**
- Ascription is always `<:`, never `:`. Types stay transparent, so two applications of a functor to the same arguments agree by conversion (V2).
- No `Declare Module` in a signature (see 0.1). A shared component is a parameter.
- A functor does not instantiate another functor whose instance appears in its own signature or code; it takes the instance as a parameter. Otherwise the `Include` chain would carry a code-level copy that the law-level lemmas do not mention syntactically. Wiring is done in leaf "kit" modules (`Exec/Instances.v`) and in examples.
- Every functor application is named before it is passed on: `Module AB := PairKey A B. Module M := TrieMap AB.` Rocq rejects `MAP (PairKey A B)` (failed pattern F1).
- Concrete cores (`PTrie`, `digraph`, `uf`, `Heap`) are plain modules; keyed views are thin transparent functors over them.

**R9. Certify rather than verify, wherever a checker is cheap.** A solver, the WTO builder, the dominator builder and (in the other areas) the SSA builder and planners are untrusted producers. Each has a cost proof and a checker with a soundness proof. A producer has no soundness proof.

**R10. Loops.** `loop_fuel` (Argent) with `nat` fuel computed from data, for short loops (query evaluation, a union-find walk). `loopN` (`Base/Loop.v`) for long loops with caller-supplied `N` fuel: it recurses on `Acc N.lt`, so no unary fuel is built and extraction drops the proof (V8: 200,000 iterations with fuel 10¹² ran in 0.13 s under `vm_compute`). Its potential lemma gives a bound with an additive `N.size_nat fuel` and no other dependence on fuel.

**R11. Statements are frozen; plans can be wrong.** A session never edits `*Sig.v`. Extra lemmas in `Foo.v` are free. If a `PLAN` lemma is false or useless, the session proves the `_TIME` or `_LAWS` contract by another route and leaves that lemma `Admitted` with `(* PLAN-DEFECT: reason *)`; our agents repair the plan after the batch. A defect in a public layer is reported and stops work on that component.

**R12. Arithmetic.** `positive`, `N` and `Z` are priced per bit through Argent's derived time functions. Counters that grow with the input are `N`. `nat` is for spec values, loop fuel computed from small data, and counters bounded by a small program constant.

**R13. Lints** (added to `just/lint.rules`): `Include` of a module type whose name does not end in `_SPEC` (it turns `Parameter`s into axioms, F3); `Declare Module`; `Inductive`, `Record` or `Variant` between `Module X (` and `End X`; module ascription with `:`; a functor parameter typed `FOO_TIME` rather than `FOO_T`.

**Extraction shape.** Roots are applications of `…Code` functors to `…Code` instances, gathered by the engines architect in `Exec/Instances.v` and `Exec/Roots.v`. The OCaml has module types that list operations only, functors over them, and applied modules. If a certified module is extracted instead, the OCaml also carries every `T_` function and constant as dead code, because extraction keeps all fields of a module it needs (F2). That is the reason for the separate code tower.

---

## 2. Package map

```
Argent (external; rocq-elpi)      TimeFun, bigO, loop, loop_fuel, amortised, CostStd
   |
  Base      Key Code Trie Map Set Intern UnionFind Heap Loop
   |  \
   |   Graph      Data Spec Digraph Search Scc Wto Dom Frontier Loops
   |    |
  Lattice   LatticeSig Gamma Simple Flat WithBot WithTop Product Reduced
   |    |   MapLattice Sets Dual Bounded Disjunction
   |    |
  Fixpoint  Query SystemSig Policy Schedule Check Narrow Certified Worklist Indexed     (Base, Lattice, Graph)
   |
  Program   SemanticsSig CfgSig VarsSig SsaSig CallsSig MemorySig                       (Base, Graph)
   |
  Framework Dense GenKill Interp Sparse Summary Ifds Ide                                (Fixpoint, Program, Lattice)

  Bits        operator table and bit-vector semantics                (Base)
  Domains     LangSig ValueSig Harness Interval KnownBits Wrapped …  (Base, Lattice, Bits)
  States      Env Partition Disjunction RelEnv                       (Domains, Lattice, Base)
  Relational  LinForm Linearize Zone Octagon LinCert Karr Poly       (Domains, States)
  Widening    Mining                                                 (Domains, Fixpoint)
  Alarms      Checks Alarms BitsChecks                               (States, Framework)

  Egglog      Syntax Model Value Index Join Database Run Extract     (Base)
  Egraph      Syntax Compile Saturate                                (Egglog)
  Ssa         Lang Live Validate Build ParMove Destroy               (Base, Graph, Program)
  Incremental Restrict Incremental                                   (Fixpoint)
  Clients     Andersen Steensgaard                                   (Egglog, Egraph)
  Exec        Instances Roots                                        (everything)
  Float       deferred; Flocq; outside the default build
```

- `Argent` sits below everything and is the only user of rocq-elpi. Packages import it for `TimeFun`, `bigO`, the two loop combinators and `CostStd`.
- Core is `Base`, `Lattice`, `Graph`, `Fixpoint`, `Program`, `Framework`. Domains own `Bits`, `Domains`, `States`, `Relational`, `Widening`, `Alarms`, `Float`. Engines own `Egglog`, `Egraph`, `Ssa`, `Incremental`, `Clients`, `Exec`.
- Gone: `Cost` (replaced by Argent), `Datalog` (positive Datalog is the relation-only fragment of `Egglog`), `Analyses`.
- Three cross-area edges need care: `Widening → Fixpoint`, `Alarms → Framework`, `Incremental → Fixpoint`. None points back into core.

---

## 3. Signature catalog

Every component below has the three implementation modules of R2 unless stated. Time layers are abbreviated to their contracts; each contract has a `Parameter T_op` of the matching type and a named constant.

### 3.1 Base

**Keys** (`Base/KeySig.v`, `Base/Key.v`, `Base/Code.v`)

```coq
Module Type TYPE. Parameter t : Type. End TYPE.

Module Type KEY_OPS.
  Parameter t : Type.
  Parameter encode : t -> positive.
  Parameter eqb : t -> t -> bool.
End KEY_OPS.
Module Type KEY_SPEC (Import K : KEY_OPS).
  Definition bits (k : t) : nat := Pos.size_nat (encode k).
End KEY_SPEC.
Module Type KEY_LAWS (Import K : KEY_OPS).
  Parameter encode_inj : forall a b, encode a = encode b -> a = b.
  Parameter eqb_spec : forall a b, reflect (a = b) (eqb a b).
End KEY_LAWS.
Module Type KEY := KEY_OPS <+ KEY_SPEC <+ KEY_LAWS.
Module Type KEY_TIME (Import K : KEY).
  Parameter T_encode : t -> nat.
  Parameter T_eqb : t -> t -> nat.
  Parameter c_key : nat.
  Parameter T_encode_le : forall k, T_encode k <= c_key * (bits k + 1).
  Parameter T_eqb_le : forall a b, T_eqb a b <= c_key * (bits a + 1).
End KEY_TIME.
Module Type KEY_T := KEY <+ KEY_TIME.
```

A `KEY_OPS` module is also a `TYPE`. Instances: `PosKey`, `NKey`, `ZKey`, `NatKey`, `BoolKey`, `UnitKey`.

Codes are top-level functions (R7); the key functors are thin wrappers.

```coq
Fixpoint glue (a b : positive) : positive :=             (* a, self-delimited, then b *)
  match a with xH => b~0 | xO a' => (glue a' b)~0~1 | xI a' => (glue a' b)~1~1 end.
Definition pair_code {A B} (fa : A -> positive) (fb : B -> positive) (x : A * B) : positive :=
  glue (fa (fst x)) (fb (snd x)).
Definition sum_code {A B} (fa : A -> positive) (fb : B -> positive) (x : A + B) : positive :=
  match x with inl a => (fa a)~0 | inr b => (fb b)~1 end.
Definition option_code {A} (f : A -> positive) (x : option A) : positive :=
  match x with None => 1 | Some a => (f a)~0 end.
Fixpoint list_code {A} (f : A -> positive) (l : list A) : positive :=
  match l with nil => 1 | x :: r => glue (f x) (list_code f r) end.

Lemma glue_inj  : forall a b a' b', glue a b = glue a' b' -> a = a' /\ b = b'.
Lemma glue_bits : forall a b, Pos.size_nat (glue a b) = 2 * Pos.size_nat a + Pos.size_nat b - 1.
Lemma T_glue_le : forall a b, T_glue a b <= c_glue * (Pos.size_nat a + 1).

Module PairKey (A B : KEY) <: KEY.     (* t := A.t * B.t;  bits (a, b) = 2 * A.bits a + B.bits b - 1 *)
Module SumKey  (A B : KEY) <: KEY.     (* bits = component bits + 1 *)
Module OptionKey (A : KEY) <: KEY.
Module ListKey   (A : KEY) <: KEY.     (* bits l <= 2 * list_sum (map A.bits l) + 1 *)
```

This replaces the 1,157-line `BaseCode.v` (code trees, bit streams, decoders). A key needs injectivity, not a decoder.

**Trie core** (`Base/TrieSig.v`, `Base/Trie.v`; the plain modules `PTrieCode`, `PTrie`, `PTrieT`). The landed canonical trie, so equality of tries is Leibniz equality.

```coq
Module Type TRIE_OPS.
  Parameter t : Type -> Type.
  Parameter empty    : forall {A}, t A.
  Parameter is_empty : forall {A}, t A -> bool.
  Parameter get      : forall {A}, positive -> t A -> option A.
  Parameter set      : forall {A}, positive -> A -> t A -> t A.
  Parameter remove   : forall {A}, positive -> t A -> t A.
  Parameter merge    : forall {A B C}, (option A -> option B -> option C) -> t A -> t B -> t C.
  Parameter forall2b : forall {A B}, (option A -> option B -> bool) -> t A -> t B -> bool.
  Parameter existsb  : forall {A}, (A -> bool) -> t A -> bool.
  Parameter map      : forall {A B}, (A -> B) -> t A -> t B.
  Parameter fold     : forall {A B}, (B -> positive -> A -> B) -> t A -> B -> B.
  Parameter elements : forall {A}, t A -> list (positive * A).
End TRIE_OPS.
Module Type TRIE_SPEC (Import T : TRIE_OPS).
  Definition weight {A} (m : t A) : nat :=
    list_sum (List.map (fun kv => Pos.size_nat (fst kv) + 1) (elements m)).
End TRIE_SPEC.
Module Type TRIE_LAWS (Import T : TRIE_OPS) (Import S : TRIE_SPEC T).
  (* spec: nodes trie_lt *)
  Parameter nodes : forall {A}, t A -> nat.
  Parameter trie_lt : positive -> positive -> Prop.
  Parameter get_empty : forall A p, get p (@empty A) = None.
  Parameter get_set_same  : forall A p (a : A) m, get p (set p a m) = Some a.
  Parameter get_set_other : forall A p q (a : A) m, p <> q -> get p (set q a m) = get p m.
  Parameter get_remove_same  : forall A p (m : t A), get p (remove p m) = None.
  Parameter get_remove_other : forall A p q (m : t A), p <> q -> get p (remove q m) = get p m.
  Parameter get_merge : forall A B C (f : option A -> option B -> option C) m1 m2 p,
    f None None = None -> get p (merge f m1 m2) = f (get p m1) (get p m2).
  Parameter forall2b_spec : forall A B (f : option A -> option B -> bool) m1 m2, f None None = true ->
    (forall2b f m1 m2 = true <-> forall p, f (get p m1) (get p m2) = true).
  Parameter existsb_spec : forall A (f : A -> bool) m,
    existsb f m = true <-> exists p a, get p m = Some a /\ f a = true.
  Parameter get_map : forall A B (f : A -> B) m p, get p (map f m) = option_map f (get p m).
  Parameter elements_spec : forall A (m : t A) p a, In (p, a) (elements m) <-> get p m = Some a.
  Parameter elements_sorted : forall A (m : t A),
    StronglySorted (fun x y => trie_lt (fst x) (fst y)) (elements m).
  Parameter elements_nodup : forall A (m : t A), NoDup (List.map fst (elements m)).
  Parameter fold_spec : forall A B (f : B -> positive -> A -> B) m b,
    fold f m b = fold_left (fun acc kv => f acc (fst kv) (snd kv)) (elements m) b.
  Parameter ext : forall A (m n : t A), (forall p, get p m = get p n) -> m = n.
  Parameter nodes_set : forall A p (a : A) m, nodes (set p a m) <= nodes m + Pos.size_nat p.
  Parameter nodes_le_weight : forall A (m : t A), nodes m <= weight m.
End TRIE_LAWS.
Module Type TRIE := TRIE_OPS <+ TRIE_SPEC <+ TRIE_LAWS.
Module Type TRIE_TIME (Import T : TRIE).
  Parameter c_trie : nat.
  Parameter T_get_le : forall A p (m : t A), T_get p m <= c_trie * (Pos.size_nat p + 1).
  (* T_set_le, T_remove_le: the same bound *)
  Parameter T_merge_le : forall A B C (f : option A -> option B -> option C) T_f m1 m2 k,
    (forall a b, T_f a b <= k) -> T_merge f T_f m1 m2 <= c_trie * (k + 1) * (nodes m1 + nodes m2 + 1).
  (* T_forall2b_le: the same shape.  T_existsb_le, T_map_le, T_fold_le: c_trie * (k + 1) * (nodes m + 1) *)
  Parameter T_elements_le : forall A (m : t A), T_elements m <= c_trie * (weight m + 1).
  Parameter get_tight : forall A p (m : t A), Pos.size_nat p <= T_get p m.      (* lower-bound witness *)
End TRIE_TIME.
```

**Maps and sets** (`MapSig.v`, `Map.v`, `SetSig.v`, `Set.v`)

```coq
Definition kmap (K A : Type) : Type := PTrie.t (K * A).       (* top level: the keyed store *)

Module Type MAP_OPS (K : KEY_OPS).
  Parameter t : Type -> Type.
  Parameter empty    : forall {A}, t A.
  Parameter get      : forall {A}, K.t -> t A -> option A.
  Parameter set      : forall {A}, K.t -> A -> t A -> t A.
  Parameter remove   : forall {A}, K.t -> t A -> t A.
  Parameter merge    : forall {A B C}, (option A -> option B -> option C) -> t A -> t B -> t C.
  Parameter forall2b : forall {A B}, (option A -> option B -> bool) -> t A -> t B -> bool.
  Parameter existsb  : forall {A}, (A -> bool) -> t A -> bool.
  Parameter fold     : forall {A B}, (B -> K.t -> A -> B) -> t A -> B -> B.
  Parameter elements : forall {A}, t A -> list (K.t * A).
End MAP_OPS.
Module Type MAP_SPEC (K : KEY_OPS) (Import M : MAP_OPS K).
  Definition weight {A} (m : t A) : nat :=
    list_sum (List.map (fun kv => Pos.size_nat (K.encode (fst kv)) + 1) (elements m)).
End MAP_SPEC.
Module Type MAP_LAWS (K : KEY) (Import M : MAP_OPS K).
  (* spec: wf nodes *)
  Parameter wf : forall {A}, t A -> Prop.
  Parameter nodes : forall {A}, t A -> nat.
  (* wf_empty, wf_set, wf_remove, wf_merge: every operation preserves wf *)
  (* get_empty, get_set_same, get_set_other, get_remove_*, get_merge, forall2b_spec, existsb_spec:
     as TRIE_LAWS, on K.t, with no wf premise *)
  Parameter elements_spec : forall A (m : t A) k a, wf m -> (In (k, a) (elements m) <-> get k m = Some a).
  Parameter elements_nodup : forall A (m : t A), wf m -> NoDup (List.map fst (elements m)).
  Parameter fold_spec : forall A B (f : B -> K.t -> A -> B) m b,
    fold f m b = fold_left (fun acc ka => f acc (fst ka) (snd ka)) (elements m) b.
  Parameter ext : forall A (m n : t A), wf m -> wf n -> (forall k, get k m = get k n) -> m = n.
End MAP_LAWS.
Module Type MAP (K : KEY) := MAP_OPS K <+ MAP_SPEC K <+ MAP_LAWS K.
Module Type MAP_TIME (K : KEY_T) (Import M : MAP K).
  Parameter c_map : nat.
  Parameter T_get_le : forall A k (m : t A), T_get k m <= c_map * (K.bits k + 1).   (* also set, remove *)
  Parameter T_merge_le : forall A B C (f : option A -> option B -> option C) T_f m1 m2 c,
    (forall a b, T_f a b <= c) -> T_merge f T_f m1 m2 <= c_map * (c + 1) * (nodes m1 + nodes m2 + 1).
  (* T_forall2b_le, T_existsb_le, T_fold_le: the same shape *)
  Parameter T_elements_le : forall A (m : t A), wf m -> T_elements m <= c_map * (weight m + 1).
End MAP_TIME.
Module Type MAP_T (K : KEY_T) := MAP K <+ MAP_TIME K.

Module TrieMapCode (K : KEY_OPS) <: MAP_OPS K.     (* t A := kmap K.t A;  get k m := option_map snd (PTrie.get (K.encode k) m) *)
Module TrieMap (K : KEY) <: MAP K.
Module TrieMapT (K : KEY_T) <: MAP_T K.
```

`SET_OPS (K)` has `t empty mem add remove union inter diff subset equal elements fold`, with laws by `mem` and the same time shapes (binary operations cost `c·(nodes s + nodes u + 1)`). `TrieSet (K)` has `t := PTrie.t K.t`.

**Interning** (`InternSig.v`, `Intern.v`): `INTERN_OPS (K)` has `t`, `empty`, `intern : K.t -> t -> positive * t`, `find : K.t -> t -> option positive`, `name : positive -> t -> option K.t`, `size : t -> N`. Laws: ids are stable, injective and dense (`1 … size`); `name` inverts `intern`. Time: `c·(K.bits k + N.size_nat (size s) + 1)`.

**Union-find:** section 6.

**Priority queue** (`HeapSig.v`, `Heap.v`; items are `positive`, priorities are `N`). The landed lazy-deletion binomial heap.

```coq
Module Type PQ_OPS.
  Parameter t : Type.
  Parameter empty : t.
  Parameter push : N -> positive -> t -> t.               (* insert, or lower the priority of a live item *)
  Parameter pop  : t -> option (N * positive * t).        (* a live item of least priority *)
  Parameter size : t -> N.
End PQ_OPS.
Module Type PQ_LAWS (Import Q : PQ_OPS).
  (* spec: wf prio pending *)
  Parameter wf : t -> Prop.
  Parameter prio : t -> positive -> option N.
  Parameter pending : t -> nat.                           (* stored entries, stale ones included *)
  (* wf_empty, wf_push, wf_pop; prio_empty; prio_push (minimum of the old and new priority);
     pop_min (the popped priority is least and the item is no longer live); pop_none iff no live item *)
End PQ_LAWS.
Module Type PQ := PQ_OPS <+ PQ_LAWS.
Module Type PQ_TIME (Import Q : PQ).
  Parameter phi : nat -> nat -> t -> nat.                 (* potential, for a capacity P and a width w *)
  Parameter c_pq : nat.
  Definition unit_pq (P w : nat) : nat := (Nat.log2 P + 1) * (w + 1).
  Parameter T_push_amort : forall P w p x q, wf q -> pending q < P ->
    Pos.size_nat x + N.size_nat p <= w ->
    T_push p x q + phi P w (push p x q) <= c_pq * unit_pq P w + phi P w q.
  Parameter T_pop_amort : forall P w q, wf q -> pending q <= P ->
    T_pop q + match pop q with Some (_, _, q') => phi P w q' | None => 0 end
      <= c_pq * unit_pq P w + phi P w q.
  Parameter phi_empty : forall P w, phi P w empty = 0.
End PQ_TIME.
```

**Loop** (`Base/Loop.v`, no signature file; top level)

```coq
Definition loopN {S R} (step : S -> S + R) (fuel : N) (s : S) : S + R.    (* Argent.loop on (fuel, s) *)
Lemma loopN_done : forall S R (step : S -> S + R) (Inv : S -> Prop) (Phi : S -> nat) fuel s,
  (forall s s1, Inv s -> step s = inl s1 -> Inv s1 /\ Phi s1 < Phi s) ->
  Inv s -> (N.of_nat (Phi s) < fuel)%N -> exists r, loopN step fuel s = inr r.
Lemma T_loopN_le : forall S R (step : S -> S + R) T_step Inv Phi Tstop fuel s,
  (forall s s1, Inv s -> step s = inl s1 -> Inv s1 /\ T_step s + Phi s1 < Phi s) ->
  (forall s r, Inv s -> step s = inr r -> T_step s <= Tstop) ->
  Inv s -> T_loopN step T_step fuel s <= c_loopN * (Phi s + Tstop + N.size_nat fuel + 1).
```

The `N.size_nat fuel` term pays for the first long borrow of the binary counter; decrements are O(1) amortised after that.

### 3.2 Lattice (`Lattice/LatticeSig.v`)

```coq
Module Type LATTICE_OPS.
  Parameter t : Type.
  Parameter leb : t -> t -> bool.
  Parameter bot : t.
  Parameter is_bot : t -> bool.
  Parameter join : t -> t -> t.
End LATTICE_OPS.
Module Type LATTICE_LAWS (Import L : LATTICE_OPS).
  Parameter leb_refl  : forall a, leb a a = true.
  Parameter leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Parameter bot_least : forall a, leb bot a = true.
  Parameter is_bot_bot : is_bot bot = true.
  Parameter is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Parameter join_ub_l : forall a b, leb a (join a b) = true.
  Parameter join_ub_r : forall a b, leb b (join a b) = true.
End LATTICE_LAWS.
Module Type LATTICE := LATTICE_OPS <+ LATTICE_LAWS.
Module Type LATTICE_TIME (Import L : LATTICE_OPS).
  (* spec: size *)
  Parameter size : t -> nat.
  Parameter T_leb T_join : t -> t -> nat.
  Parameter T_is_bot : t -> nat.
  Parameter c_lat : nat.
  Parameter T_leb_le  : forall a b, T_leb a b  <= c_lat * (size a + size b + 1).
  Parameter T_join_le : forall a b, T_join a b <= c_lat * (size a + size b + 1).
  Parameter T_is_bot_le : forall a, T_is_bot a <= c_lat * (size a + 1).
End LATTICE_TIME.
Module Type LATTICE_T := LATTICE <+ LATTICE_TIME.

(* extensions; each is a layer over LATTICE_OPS and composes with <+ *)
Module Type HAS_TOP_OPS  (Import L : LATTICE_OPS). Parameter top : t. End HAS_TOP_OPS.
Module Type HAS_TOP_LAWS (Import L : LATTICE_OPS) (Import T : HAS_TOP_OPS L).
  Parameter top_greatest : forall a, leb a top = true.
End HAS_TOP_LAWS.
Module Type HAS_MEET_OPS  (Import L : LATTICE_OPS). Parameter meet : t -> t -> t. End HAS_MEET_OPS.
Module Type HAS_MEET_LAWS (Import L : LATTICE_OPS) (Import M : HAS_MEET_OPS L).
  Parameter meet_lb_l : forall a b, leb (meet a b) a = true.
  Parameter meet_lb_r : forall a b, leb (meet a b) b = true.
End HAS_MEET_LAWS.
Module Type HAS_MEET_TIME (Import L : LATTICE_OPS) (Import LT : LATTICE_TIME L) (Import M : HAS_MEET_OPS L).
  Parameter T_meet : t -> t -> nat.
  Parameter T_meet_le : forall a b, T_meet a b <= c_lat * (size a + size b + 1).
End HAS_MEET_TIME.

Module Type WIDENING_OPS (Import L : LATTICE_OPS).
  Parameter wparam : Type.
  Parameter widen : wparam -> t -> t -> t.
  Parameter narrow : t -> t -> t.
End WIDENING_OPS.
Module Type WIDENING_LAWS (Import L : LATTICE_OPS) (Import W : WIDENING_OPS L).
  (* spec: wrank *)
  Parameter wrank : wparam -> t -> nat.
  Parameter widen_ub_l : forall p a b, leb a (widen p a b) = true.
  Parameter widen_ub_r : forall p a b, leb b (widen p a b) = true.
  Parameter widen_stable : forall p a b, leb b a = true -> widen p a b = a.
  Parameter wrank_widen : forall p a b, is_bot a = false -> leb b a = false ->
    wrank p (widen p a b) < wrank p a.
  Parameter wrank_widen_le : forall p a b, is_bot a = false -> wrank p (widen p a b) <= wrank p a.
  Parameter narrow_between : forall a b, leb b a = true ->
    leb b (narrow a b) = true /\ leb (narrow a b) a = true.
End WIDENING_LAWS.
Module Type WIDENING_TIME (Import L : LATTICE_OPS) (Import LT : LATTICE_TIME L) (Import W : WIDENING_OPS L).
  (* spec: wsize *)
  Parameter wsize : wparam -> nat.
  Parameter T_widen : wparam -> t -> t -> nat.
  Parameter T_narrow : t -> t -> nat.
  Parameter T_widen_le  : forall p a b, T_widen p a b <= c_lat * (size a + size b + wsize p + 1).
  Parameter T_narrow_le : forall a b, T_narrow a b <= c_lat * (size a + size b + 1).
End WIDENING_TIME.

Module Type HEIGHT (Import L : LATTICE).            (* laws only *)
  Parameter rank : t -> nat.
  Parameter height : nat.
  Parameter rank_le : forall a, rank a <= height.
  Parameter rank_strict : forall a b, leb a b = true -> leb b a = false -> rank a < rank b.
End HEIGHT.
Module Type LUB (Import L : LATTICE).
  Parameter join_least : forall a b c, leb a c = true -> leb b c = true -> leb (join a b) c = true.
End LUB.

(* bundles *)
Module Type WLATTICE_OPS := LATTICE_OPS <+ WIDENING_OPS.                                 (* what a solver needs *)
Module Type WLATTICE     := WLATTICE_OPS <+ LATTICE_LAWS <+ WIDENING_LAWS.
Module Type WLATTICE_T   := WLATTICE <+ LATTICE_TIME <+ WIDENING_TIME.
Module Type BLATTICE_OPS := LATTICE_OPS <+ HAS_TOP_OPS <+ HAS_MEET_OPS.                  (* bounded, with meet *)
Module Type BLATTICE     := BLATTICE_OPS <+ LATTICE_LAWS <+ HAS_TOP_LAWS <+ HAS_MEET_LAWS.
Module Type BLATTICE_T   := BLATTICE <+ LATTICE_TIME <+ HAS_MEET_TIME.
Module Type ALATTICE_OPS := LATTICE_OPS <+ HAS_TOP_OPS <+ HAS_MEET_OPS <+ WIDENING_OPS.  (* what a domain offers *)
```

**`GAMMA`** (`Lattice/Gamma.v`; spec only, one layer)

```coq
Module Type GAMMA (C : TYPE) (L : LATTICE_OPS).
  Parameter gamma : L.t -> C.t -> Prop.
  Parameter gamma_mono : forall a b c, L.leb a b = true -> gamma a c -> gamma b c.
End GAMMA.
Module Type GAMMA_BOT  (C : TYPE) (L : LATTICE_OPS) (Import G : GAMMA C L).
  Parameter gamma_bot : forall a c, L.is_bot a = true -> ~ gamma a c.
End GAMMA_BOT.
(* GAMMA_TOP: gamma top c.   GAMMA_MEET: gamma a c -> gamma b c -> gamma (meet a b) c. *)
```

**Combinators.** Each is `XCode (…_OPS) <: …_OPS`, `X (…) <: …`, `XT (…_T) <: …_T`.

| Functor | Parameters | Result | Notes |
|---|---|---|---|
| `BoolLat`, `UnitLat` | — | `BLATTICE_T`, `HEIGHT` | plain modules |
| `Flat` | `K : KEY` | `BLATTICE` with `HEIGHT` 2 | carrier `flat K.t` (top-level `FBot`, `FVal`, `FTop`) |
| `WithBot` | `L : LATTICE` | `LATTICE` | `option L.t`; landed `Adjoin` |
| `WithTop` | `L : LATTICE` | `LATTICE <+ HAS_TOP` | landed `Lift` |
| `Product` | `A B : LATTICE` | `LATTICE` | componentwise; `wparam := A.wparam * B.wparam`, `wrank` is the sum |
| `ProductGamma` | `A B`, `GA : GAMMA C A`, `GB : GAMMA C B` | `GAMMA C (Product A B)` | conjunction |
| `Reduced` | `A B : BLATTICE`, `R : REDUCER A B` | `BLATTICE` | `REDUCER_OPS` has `reduce : A.t * B.t -> A.t * B.t`; laws `reduce_lower`, and `reduce_sound` against two `GAMMA`s. Reduce after join and transfer, never after widening |
| `MapLattice` | `K : KEY`, `M : MAP K`, `L : LATTICE` | `LATTICE` | carrier `M.t L.t`, an absent key reads as `L.bot`; `leb` is `M.forall2b`, `join` is `M.merge`; with `L : WLATTICE`, widening is pointwise and `wrank` sums the bindings |
| `MaySet`, `MustSet` | `K : KEY`, `S : SET K` | `LATTICE` | union with `⊆`; and `option S.t` with intersection, `None` being the universe |
| `Dual` | `L : BLATTICE` | `BLATTICE` | section 7 |
| `Bounded` | `K`, `S : SET K`, a universe value | `HEIGHT` for `MaySet` restricted to the universe | landed `LatticeBounded` |
| `Disjunction` | `L : WLATTICE`, `C : CAP` | `WLATTICE` | lists of at most `C.k` elements, Hoare order, `compact`; the domains' state-level `Disj` adds the transfers |
| `Partition` | `Tk : KEY`, `MT : MAP Tk`, `L : LATTICE` | `LATTICE` | `MapLattice Tk MT L` plus `inject`, `merge`, `retag` (trace partitioning) |
| `JoinWidening` | `L : LATTICE`, `H : HEIGHT L` | `WIDENING_OPS <+ WIDENING_LAWS` | `wparam := unit`; `widen _ a b := if leb b a then a else join a b`; `narrow a b := a`; `wrank _ a := H.height - H.rank a` |

The landed equality-partition lattice (`LatticePartition*`, 1,035 lines) had only GVN as a consumer and goes to the archive.

### 3.3 `VALUE_DOMAIN` and `STATE_DOMAIN` (signatures only; `Domains/LangSig.v`, `Domains/ValueSig.v`, `States/StateSig.v`)

The fields are the domains architect's, put in layered and parameterised form. The shapes below type-checked (V10).

```coq
Inductive term (K X : Type) : Type := Leaf (x : X) | Node (k : K) (ts : list (term K X)).
(* sequence, eval_term, eval_terms, tsize, upd: as in the domains document *)

Module Type LANG_OPS.
  Parameter op guard val : Type.
  Parameter eval : op -> list val -> option val.
  Parameter literal : op -> option Z.
End LANG_OPS.
Module Type LANG_LAWS (Import L : LANG_OPS).
  Parameter holds : guard -> list val -> Prop.
End LANG_LAWS.
Module Type LANG := LANG_OPS <+ LANG_LAWS.
(* LANG_TIME (Import L : LANG): work, T_eval, T_literal, c_lang, T_eval_le, T_literal_le.  LANG_T := LANG <+ LANG_TIME *)

Module Type VALUE_DOMAIN_OPS (L : LANG_OPS).
  Include ALATTICE_OPS.     (* t leb bot is_bot join top meet wparam widen narrow *)
  Parameter forward  : L.op -> list t -> t.
  Parameter backward : L.op -> t -> list t -> list t.
  Parameter guard    : L.guard -> list t -> list t.
End VALUE_DOMAIN_OPS.
Module Type VALUE_DOMAIN_LAWS (L : LANG) (Import V : VALUE_DOMAIN_OPS L).
  Parameter gamma : t -> L.val -> Prop.
  (* gamma_mono, gamma_bot, gamma_top, gamma_meet, is_bot_sound,
     forward_sound, backward_sound, backward_refines, guard_sound, guard_refines: as the domains document *)
End VALUE_DOMAIN_LAWS.
Module Type VALUE_DOMAIN (L : LANG) :=
  VALUE_DOMAIN_OPS L <+ LATTICE_LAWS <+ HAS_TOP_LAWS <+ HAS_MEET_LAWS <+ WIDENING_LAWS <+ VALUE_DOMAIN_LAWS L.
(* VALUE_DOMAIN_TIME (L : LANG_T) (Import D : VALUE_DOMAIN L): size, work, gwork, c_val and the contracts.
   VALUE_DOMAIN_T (L : LANG_T) := VALUE_DOMAIN L <+ VALUE_DOMAIN_TIME L *)

Module Type STATE_DOMAIN_OPS (X : KEY_OPS) (L : LANG_OPS) (V : VALUE_DOMAIN_OPS L).
  Include ALATTICE_OPS.
  Parameter assign : X.t -> term L.op X.t -> t -> t.
  Parameter havoc  : X.t -> t -> t.
  Parameter assume : L.guard -> list (term L.op X.t) -> t -> t.
  Parameter eval   : term L.op X.t -> t -> V.t.
End STATE_DOMAIN_OPS.
Module Type STATE_DOMAIN_LAWS (X : KEY) (L : LANG) (V : VALUE_DOMAIN L) (Import D : STATE_DOMAIN_OPS X L V).
  Parameter gamma : t -> (X.t -> L.val) -> Prop.
  Parameter gamma_mono : forall a b st, leb a b = true -> gamma a st -> gamma b st.
  Parameter gamma_bot : forall st, ~ gamma bot st.
  Parameter gamma_top : forall st, gamma top st.
  Parameter assign_sound : forall x e s st c, gamma s st -> eval_term L.eval st e = Some c ->
    gamma (assign x e s) (upd X.eqb st x c).
  Parameter havoc_sound : forall x s st c, gamma s st -> gamma (havoc x s) (upd X.eqb st x c).
  Parameter assume_sound : forall g es s st cs, gamma s st -> eval_terms L.eval st es = Some cs ->
    L.holds g cs -> gamma (assume g es s) st.
  Parameter eval_sound : forall e s st c, gamma s st -> eval_term L.eval st e = Some c -> V.gamma (eval e s) c.
End STATE_DOMAIN_LAWS.
Module Type STATE_DOMAIN (X : KEY) (L : LANG) (V : VALUE_DOMAIN L) :=
  STATE_DOMAIN_OPS X L V <+ LATTICE_LAWS <+ HAS_TOP_LAWS <+ WIDENING_LAWS <+ STATE_DOMAIN_LAWS X L V.
```

The domains' functor headers become, for example, `Module Env (X : KEY) (M : MAP X) (L : LANG) (V : VALUE_DOMAIN L) <: STATE_DOMAIN X L V`, with `EnvCode` over the `_OPS` types and `EnvT` over the `_T` types.

### 3.4 Graph

**Data and specification** (`Graph/Data.v`, `Graph/Spec.v`; top level)

```coq
Record digraph  := Digraph { verts : list positive; succ : PTrie.t (list positive) }.
Record prepared := Prepared { base : digraph; pred : PTrie.t (list positive); nv : N; ne : N }.
Definition succs (g : digraph) (v : positive) : list positive :=
  match PTrie.get v (succ g) with Some l => l | None => nil end.
Definition preds (g : prepared) (v : positive) : list positive := (* likewise on pred *).
Definition nodes (g : prepared) : list positive := verts (base g).

Inductive wto := WNil | WVertex (v : positive) (rest : wto) | WLoop (head : positive) (body rest : wto).
Record scc := Scc { comp : PTrie.t positive; comps : list (list positive) }.
Record domtree := DomTree { idom : PTrie.t positive; kids : PTrie.t (list positive);
                            pre : PTrie.t N; post : PTrie.t N }.
Record loops := Loops { header : PTrie.t positive; parent : PTrie.t positive; body : PTrie.t (list positive) }.
Inductive edge_kind := Tree | Back | Done.            (* target unseen, on the stack, finished *)

(* Spec.v: edge g u v := In v (succs g u);  path, reach g roots v, cycle g vs;
   dominates g r u v := every path from r to v contains u;
   wf_graph g := every successor is a vertex and verts has no duplicates *)
```

A typed presentation becomes a `digraph` through its key codes. `Digraph.prepare : digraph -> prepared` costs `c·(n + e + 1)·(w + 1)`, where `w` is the largest vertex bit length.

**Search** (`SearchSig.v`, `Search.v`). The visitor is a functor parameter.

```coq
Module Type VISITOR_OPS.
  Parameter state : Type.
  Parameter enter : positive -> state -> state.
  Parameter leave : positive -> state -> state.
  Parameter edge  : edge_kind -> positive -> positive -> state -> state.
End VISITOR_OPS.
(* VISITOR_TIME: spec vwork : state -> nat; each callback costs at most c_vis * (vwork s + 1) *)

Module Type SEARCH_OPS (V : VISITOR_OPS).
  Parameter dfs : prepared -> list positive -> V.state -> V.state.
End SEARCH_OPS.
(* SEARCH_LAWS: spec trace : prepared -> list positive -> list event (top-level event type);
     dfs_fold      dfs g roots s is the fold of the visitor over trace g roots;
     trace_reach   a vertex is entered iff it is reachable from roots, and then exactly once;
     trace_nested  enter and leave events are well parenthesised;
     trace_edges   every edge out of a visited vertex appears once, with its correct kind.
   SEARCH_TIME: with vwork bounded by B along the run,
     T_dfs g roots s <= c_dfs * (n_reach + e_reach + length roots + 1) * (w + V.c_vis * (B + 1)).
   Loop: explicit stack under loopN with fuel 2 * (nv + ne) + 1; potential 2 * unvisited + pending edges. *)
```

**SCC** (`SccSig.v`, `Scc.v`; `Scc := Search TarjanVisitor` plus a wrapper)
- `Scc.run : prepared -> scc`.
- `comp_spec : wf_graph g -> (get u comp = get v comp <-> u and v reach each other)`.
- `comps_order`: every edge goes to the same or an earlier component in `comps`.
- `T_run g <= c_scc * (n + e + 1) * (w + 1)`.

**Weak topological order** (`WtoSig.v`, `Wto.v`)

```coq
Module Type WTO_OPS.
  Parameter build : prepared -> list positive -> wto.         (* producer: Bourdoncle over the SCC hierarchy *)
  Parameter check : prepared -> list positive -> wto -> bool.
  Parameter heads : wto -> list positive.
  Parameter ranks : wto -> PTrie.t positive.                  (* position in the linear order *)
End WTO_OPS.
(* WTO_LAWS:
     check_sound  check g roots w = true -> is_wto g roots w                       (landed check_correct)
     check_cuts   check g roots w = true -> forall vs, cycle (base g) vs -> (forall v, In v vs -> reach g roots v) ->
                    exists h, In h vs /\ In h (heads w)                             (landed cycles_have_head)
     ranks_forward check g roots w = true -> edge u v -> reach g roots u ->
                    rank u < rank v \/ (In v (heads w) /\ rank v <= rank u)          (landed ranks_forward)
   WTO_TIME: T_check <= c * (n + e + 1) * (w + 1);  T_build <= c * (n + e + 1) * (depth + 1) * (w + 1),
     depth being the loop nesting depth (spec). *)
```

**Dominators** (`DomSig.v`, `Dom.v`)

```coq
Module Type DOM_OPS.
  Parameter build : prepared -> positive -> PTrie.t positive.          (* producer: immediate-dominator candidates *)
  Parameter check : prepared -> positive -> PTrie.t positive -> bool.
  Parameter tree  : prepared -> positive -> PTrie.t positive -> domtree.   (* children lists, pre and post numbers *)
  Parameter dominates_b : domtree -> positive -> positive -> bool.     (* interval test *)
End DOM_OPS.
(* DOM_LAWS:
     check_sound   check g r m = true -> exact g r m                                (landed DomCheck.check_sound)
     dominates_b_spec  check g r m = true -> reach g [r] v ->
                       reflect (dominates (base g) r u v) (dominates_b (tree g r m) u v)
     kids_spec     the children lists are the inverse of idom, each in preorder.
   DOM_TIME: T_check and T_tree <= c * (n + e + 1) * (w + 1);  T_dominates_b <= c * (w + 1);
     T_build <= c * (n + e + 1) * (Nat.log2 n + 1) * (w + 1)   (simple Lengauer–Tarjan). *)
```

The exact linear bound for the landed checker must be re-derived from `GraphCheckDomCost`. I read its statements, not its proof, so the checker's contract above is the target, not a carried fact.

**Frontiers** (`FrontierSig.v`, `Frontier.v`)
- `df : prepared -> domtree -> PTrie.t (list positive)`.
- `idf : prepared -> domtree -> list positive -> list positive`.
- `df_spec : In y (df x) <-> (exists p, edge p y /\ dominates r x p) /\ ~ strictly_dominates r x y`.
- `idf_spec`: the least set containing the frontiers of the seeds and closed under `df`.
- `T_df <= c * (n + e + Σ|df| + 1) * (w + 1)` (Cooper–Harvey–Kennedy); `T_idf <= c * (Σ over visited x of |df x| + 1) * (w + 1)`.

**Loop forest** (`LoopsSig.v`, `Loops.v`)
- `forest : prepared -> domtree -> loops`; `reducible_b : prepared -> domtree -> bool`.
- Laws: headers are the targets of back edges whose target dominates the source; `body h` is the natural loop of `h`; `parent` is innermost containment; `reducible_b` reflects "every retreating edge is a back edge".
- Time: `c * (n + e + 1) * (depth + 1) * (w + 1)`.

### 3.5 Fixpoint

**Queries** (`Fixpoint/Query.v`; top level)

```coq
Inductive query (K A F : Type) : Type :=
  | Ret  (a : A)
  | Ask  (x : K) (f : F)
  | Side (x : K) (a : A) (q : query K A F).

Fixpoint peel {K A F} (q : query K A F) (acc : list (K * A)) : (A + K * F) * list (K * A) :=
  match q with
  | Ret a => (inl a, acc)
  | Ask x f => (inr (x, f), acc)
  | Side x a q1 => peel q1 ((x, a) :: acc)
  end.
Definition eval_step {K A F} (resume : F -> A -> query K A F) (look : K -> A)
    (s : query K A F * list (K * A)) : query K A F * list (K * A) + A * list (K * A) :=
  match peel (fst s) (snd s) with
  | (inl a, acc) => inr (a, rev acc)
  | (inr (x, f), acc) => inl (resume f (look x), acc)
  end.
Definition eval_query {K A F} (resume : F -> A -> query K A F) (look : K -> A) (fuel : nat)
    (q : query K A F) : option (A * list (K * A)) :=
  match loop_fuel (eval_step resume look) fuel (q, nil) with inr o => Some o | inl _ => None end.
Definition row_ok {K A} (leb : A -> A -> bool) (look : K -> A) (x : K)
    (o : option (A * list (K * A))) : bool :=
  match o with
  | None => false
  | Some (a, ss) => leb a (look x) && forallb (fun xa => leb (snd xa) (look (fst xa))) ss
  end.
Definition look_or {K A} (code : K -> positive) (d : A) (m : kmap K A) (x : K) : A :=
  match PTrie.get (code x) m with Some (_, a) => a | None => d end.
```

`peel`, `eval_step`, `row_ok` and a `forallb` check over them compiled and computed in the miniature. The checker follows from `forallb_forall` in one line.

**Systems** (`Fixpoint/SystemSig.v`)

```coq
Module Type SYSTEM_OPS (L : LATTICE_OPS).
  Parameter prog key row frame : Type.
  Parameter key_code : key -> positive.
  Parameter rows   : prog -> list row.
  Parameter target : prog -> row -> key.
  Parameter start  : prog -> row -> query key L.t frame.
  Parameter resume : prog -> frame -> L.t -> query key L.t frame.
  Parameter deps   : prog -> row -> list key.      (* every key the row may read, with multiplicity *)
  Parameter sides  : prog -> row -> list key.      (* every key it may contribute to besides its target *)
End SYSTEM_OPS.
Module Type SYSTEM_SPEC (L : LATTICE_OPS) (Import S : SYSTEM_OPS L).
  Definition val := L.t.
  Definition eval (p : prog) (r : row) (look : key -> L.t) : option (L.t * list (key * L.t)) :=
    eval_query (resume p) look (Datatypes.S (length (deps p r))) (start p r).
  Definition post_on (p : prog) (rs : list row) (look : key -> L.t) : Prop :=
    forall r, In r rs -> row_ok L.leb look (target p r) (eval p r look) = true.
  Definition post_solution (p : prog) (look : key -> L.t) : Prop := post_on p (rows p) look.
  Definition writes (p : prog) (r : row) : list key := target p r :: sides p r.
  Definition below (s u : key -> L.t) : Prop := forall x, L.leb (s x) (u x) = true.
  Definition monotone (p : prog) : Prop :=
    forall r s u, In r (rows p) -> below s u -> out_leb L.leb (eval p r s) (eval p r u).
  Definition key_bits (x : key) : nat := Pos.size_nat (key_code x).
End SYSTEM_SPEC.
Module Type SYSTEM_LAWS (L : LATTICE) (Import S : SYSTEM_OPS L) (Import SS : SYSTEM_SPEC L S).
  (* spec: wf *)
  Parameter wf : prog -> Prop.
  Parameter key_code_inj : forall a b, key_code a = key_code b -> a = b.
  Parameter eval_total : forall p r look, wf p -> In r (rows p) -> eval p r look <> None.
  Parameter reads_within : forall p r s u, wf p -> In r (rows p) ->
    (forall x, In x (deps p r) -> s x = u x) -> eval p r s = eval p r u.
  Parameter sides_within : forall p r look a ss x b, wf p -> In r (rows p) ->
    eval p r look = Some (a, ss) -> In (x, b) ss -> In x (sides p r).
End SYSTEM_LAWS.
Module Type SYSTEM (L : LATTICE) := SYSTEM_OPS L <+ SYSTEM_SPEC L <+ SYSTEM_LAWS L.

Module Type SYSTEM_TIME (L : LATTICE_T) (Import S : SYSTEM L).
  (* spec: row_work kw *)
  Parameter row_work : prog -> nat -> nat.        (* one start or resume step on values of size <= s *)
  Parameter kw : prog -> nat.                     (* the largest key bit length *)
  Parameter c_sys : nat.
  Parameter row_work_mono : forall p s s', s <= s' -> row_work p s <= row_work p s'.
  Parameter key_bits_le : forall p r x, wf p -> In r (rows p) -> In x (writes p r ++ deps p r) -> key_bits x <= kw p.
  Parameter T_key_code_le : forall x, T_key_code x <= c_sys * (key_bits x + 1).
  Parameter T_rows_le   : forall p, wf p -> T_rows p <= c_sys * (length (rows p) + 1).
  Parameter T_target_le : forall p r, wf p -> In r (rows p) -> T_target p r <= c_sys * (row_work p 0 + 1).
  Parameter T_start_le  : forall p r, wf p -> In r (rows p) -> T_start p r <= c_sys * (row_work p 0 + 1).
  Parameter T_resume_le : forall p f a, wf p -> T_resume p f a <= c_sys * (row_work p (L.size a) + 1).
  Parameter T_deps_le   : forall p r, wf p -> In r (rows p) -> T_deps p r <= c_sys * (length (deps p r) + 1) * (kw p + 1).
  Parameter T_sides_le  : forall p r, wf p -> In r (rows p) -> T_sides p r <= c_sys * (length (sides p r) + 1) * (kw p + 1).
End SYSTEM_TIME.
Module Type SYSTEM_T (L : LATTICE_T) := SYSTEM L <+ SYSTEM_TIME L.

(* extension for demand-driven clients *)
Module Type LOCAL_OPS (L : LATTICE_OPS) (Import S : SYSTEM_OPS L).
  Parameter row_code : row -> positive.
  Parameter rows_of : prog -> key -> list row.
End LOCAL_OPS.
Module Type LOCAL_LAWS (L : LATTICE) (Import S : SYSTEM L) (Import X : LOCAL_OPS L S).
  Parameter row_code_inj : forall p a b, In a (rows p) -> In b (rows p) -> row_code a = row_code b -> a = b.
  Parameter rows_of_spec : forall p x r, wf p -> (In r (rows_of p x) <-> In r (rows p) /\ In x (writes p r)).
End LOCAL_LAWS.
Module Type LOCAL_SYSTEM (L : LATTICE) := SYSTEM L <+ LOCAL_OPS L <+ LOCAL_LAWS L.
(* LOCAL_TIME: T_row_code_le in bits;  T_rows_of p x <= c_loc * (length (rows_of p x) + key_bits x + 1) *)

Module IndexedCode (L : LATTICE_OPS) (S : SYSTEM_OPS L) <: SYSTEM_OPS L.
  (* prog := indexed S.prog S.row (top-level record: program, numbered rows, write index);
     row := positive * S.row;  row_code := fst;  rows_of := one index lookup;
     prepare : S.prog -> prog costs c * (C + D + 1) * (kw + Nat.log2 C + 1) *)
Module SystemKeyCode (L : LATTICE_OPS) (S : SYSTEM_OPS L) <: KEY_OPS.     (* t := S.key; encode := S.key_code *)
```

The `SYSTEM_OPS` shape with inline keys, the `LOCAL` extension and the adapter compiled (V10).

**Policy** (`Fixpoint/PolicySig.v`, `Policy.v`). The domains architect's design, hosted here.

```coq
Record head_cfg := HeadCfg { delay : nat; narrow_passes : nat }.
Record policy (W : Type) := Policy {
  prio  : PTrie.t positive;        (* priority of each key code; absent means 1 *)
  heads : PTrie.t head_cfg;        (* widening points, by key code *)
  wp    : W;                       (* widening parameters, e.g. thresholds *)
  passes : nat }.                  (* global narrowing passes *)

Module Type POLICY_OPS (L : WLATTICE_OPS).
  Parameter update : policy L.wparam -> positive -> nat -> L.t -> L.t -> L.t * nat.
  (* if leb new old then (old, cnt)
     else no head at this code: (join old new, cnt)
     else below the delay: (join old new, S cnt), otherwise (widen wp old new, S cnt) *)
End POLICY_OPS.
Module Type POLICY_LAWS (L : WLATTICE) (Import P : POLICY_OPS L).
  (* update_ub, update_stable, head_pot, head_strict_steps, head_updates_le:
     the domains document, section 4, with the code-keyed heads *)
End POLICY_LAWS.
```

**Schedule** (`ScheduleSig.v`, `Schedule.v`). A policy is computed from the system's dependency graph and the library's WTO. This ends the duplicate order that `Nested.code` had.

```coq
Module Type SCHEDULE_OPS (L : WLATTICE_OPS) (S : SYSTEM_OPS L).
  Parameter dep_graph : S.prog -> digraph.               (* d -> y for each row r, d in deps r, y in writes r *)
  Parameter of_wto : wto -> head_cfg -> L.wparam -> nat -> policy L.wparam.
  Parameter plan : S.prog -> head_cfg -> L.wparam -> nat -> option (policy L.wparam).
                                                         (* Wto.build, then Wto.check; None when the check fails *)
  Parameter cuts : S.prog -> policy L.wparam -> bool.    (* every dependency edge that does not strictly
                                                            raise prio enters a head *)
End SCHEDULE_OPS.
(* SCHEDULE_LAWS: of_wto_cuts (the domains' statement, from Wto.check_cuts);
     plan_cuts : plan p cfg w n = Some pol -> cuts p pol = true;  cuts_spec.
   SCHEDULE_TIME: T_plan p <= c * (C p + D p + 1) * (depth + 1) * (S.kw p + 1);  T_cuts linear. *)
```

**Solvers** (`SolverSig.v`)

```coq
Inductive reason := Bad_policy | Check_failed.
Inductive outcome (M : Type) := Solved (m : M) | OutOfFuel (m : M) | Rejected (why : reason).

Module Type SOLVER_OPS (L : WLATTICE_OPS) (S : SYSTEM_OPS L).
  Parameter run : S.prog -> policy L.wparam -> N -> outcome (kmap S.key L.t).
End SOLVER_OPS.
Module Type SOLVER_TIME (L : WLATTICE_T) (S : SYSTEM_T L) (Import V : SOLVER_OPS L S).
  (* spec: fits work fuel_for *)
  Parameter fits : S.prog -> policy L.wparam -> Prop.
  Parameter work : S.prog -> policy L.wparam -> nat.
  Parameter fuel_for : S.prog -> policy L.wparam -> N.
  Parameter T_run : S.prog -> policy L.wparam -> N -> nat.
  Parameter c_solve : nat.
  Parameter T_run_le : forall p pol fuel, fits p pol ->
    T_run p pol fuel <= c_solve * (work p pol + N.size_nat fuel + 1).
  Parameter run_enough : forall p pol fuel, fits p pol -> (fuel_for p pol <= fuel)%N ->
    exists m, run p pol fuel = Solved m.
End SOLVER_TIME.
Module Type SOLVER_T (L : WLATTICE_T) (S : SYSTEM_T L) := SOLVER_OPS L S <+ SOLVER_TIME L S.
Module Type SOLVER_LEAST (L : WLATTICE) (S : SYSTEM L) (Import V : SOLVER_OPS L S).     (* optional *)
  Definition widening_free (pol : policy L.wparam) : Prop := forall c, PTrie.get c (heads pol) = None.
  Parameter run_least : forall p pol fuel m s', S.wf p -> S.monotone p -> widening_free pol ->
    run p pol fuel = Solved m -> S.post_solution p s' ->
    forall x, L.leb (look_or S.key_code L.bot m x) (s' x) = true.
End SOLVER_LEAST.
```

- A solver has **no functional laws**. Its answer is checked. That removes every engine soundness proof in the tree.
- `run_enough` rules out a solver that always gives up. It is in the time layer because it is a corollary of the same potential (`loopN_done`).
- A solver that returns garbage is caught at run time and by the precision tests.

**Checking and certification** (`CheckSig.v`, `Check.v`, `Narrow.v`, `Certified.v`)

```coq
Module Type CHECK_OPS (L : LATTICE_OPS) (S : SYSTEM_OPS L).
  Parameter look : kmap S.key L.t -> S.key -> L.t.                         (* look_or S.key_code L.bot *)
  Parameter check_rows : S.prog -> list S.row -> kmap S.key L.t -> bool.
  Parameter check : S.prog -> kmap S.key L.t -> bool.                      (* check_rows p (S.rows p) *)
End CHECK_OPS.
Module Type CHECK_LAWS (L : LATTICE) (S : SYSTEM L) (Import C : CHECK_OPS L S).
  Parameter check_rows_iff : forall p rs m, check_rows p rs m = true <-> S.post_on p rs (look m).
  Parameter check_sound : forall p m, check p m = true -> S.post_solution p (look m).
End CHECK_LAWS.
(* CHECK_TIME, with B a bound on the sizes of the values in m:
   T_check_rows p rs m <= c_chk * Σ_{r in rs} (length (S.deps p r) + length (S.sides p r) + 1)
                                 * (S.row_work p B + S.kw p + L.c_lat * (B + 1) + 1) *)

Module Narrow (L : WLATTICE) (S : SYSTEM L) (C : CHECK L S).
  (* narrow_pass p m: recompute every key from the rows, narrow against the old value,
     keep the result only if check accepts it.
     narrow_pass_post, narrow_pass_below, narrow_pass_exact_mono, T_narrow_passes_le:
     the domains document, section 4 *)

Module Certified (L : WLATTICE) (S : SYSTEM L) (V : SOLVER_OPS L S).
  Definition analyze (p : S.prog) (pol : policy L.wparam) (fuel : N) : outcome (kmap S.key L.t) :=
    match V.run p pol fuel with
    | Solved m => if check p m then Solved (refine p (passes pol) m) else Rejected Check_failed
    | o => o
    end.
  Theorem analyze_sound : forall p pol fuel m, analyze p pol fuel = Solved m -> S.post_solution p (look m).
  (* CertifiedT: T_analyze <= T_run + (passes + 1) * (T_check + one evaluation of every row) *)
```

`analyze_sound` has no hypothesis: no lattice law, no system law. It was proved in the miniature in six lines, with the narrowing fallback.

**Engines that remain: one.**

| Landed engine | Lines | Fate |
|---|---|---|
| Worklist (`FixpointWorklist*`, `IndexCost`) | 3,109 | **Kept; the default.** Priority worklist; widening, delay and narrowing through `policy` |
| Kleene | 877 | Deleted. Round-robin is the worklist with a constant priority |
| Nested | 3,505 | Deleted. Its iteration order is a `policy` built by `Schedule` from the library's WTO. The recursive strategy can return later as another `SOLVER` instance |
| Total | 1,622 | Deleted. Fuel computed from the bound is `fuel_for`, and `loopN` makes it cheap |
| Narrow | 722 | Rewritten as the solver-independent `Narrow` (about 250 lines) |
| Local, Partial | 2,293 | Deleted from core. Demand-driven solving is `Incremental.demand` (engines): region discovery, a restricted system, any `SOLVER`, `check_rows` on the region. The engines' WP4 harvests `FixpointLocalLeast` first |

**Worklist** (`WorklistSig.v`, `Worklist.v`)

```coq
Module WorklistCode (L : WLATTICE_OPS) (S : SYSTEM_OPS L) (P : POLICY_OPS L) (Q : PQ_OPS) <: SOLVER_OPS L S.
  (* prepare: number the rows; infl : key code -> rows that read it; queue all rows.
     step:    pop the row of least prio (target); eval it against the store; P.update the target and
              each side contribution; on a change, push the readers.  Loop: loopN.
     state:   top-level record wl_state (store, counters, queue), parameterised by its field types *)

Module Type BUDGET (L : WLATTICE_T) (S : SYSTEM_T L).      (* spec only: what the client promises about values *)
  Parameter inv   : S.prog -> L.t -> Prop.
  Parameter vsize : S.prog -> nat.
  Parameter wmax  : S.prog -> L.wparam -> nat.
  Parameter inv_bot  : forall p, inv p L.bot.
  Parameter inv_join : forall p a b, inv p a -> inv p b -> inv p (L.join a b).
  Parameter inv_widen : forall p w a b, inv p a -> inv p b -> inv p (L.widen w a b).
  Parameter inv_rows : forall p r look a ss, S.wf p -> In r (S.rows p) -> (forall x, inv p (look x)) ->
    S.eval p r look = Some (a, ss) -> inv p a /\ Forall (fun xa => inv p (snd xa)) ss.
  Parameter size_le  : forall p a, inv p a -> L.size a <= vsize p.
  Parameter wrank_le : forall p w a, inv p a -> L.wrank w a <= wmax p w.
End BUDGET.

(* WORKLIST_TIME (… B : BUDGET L S), with
     C p := length (S.rows p)
     D p := Σ_r (length (S.deps p r) + length (S.sides p r) + 1)
     unit p := S.row_work p (B.vsize p) + L.c_lat * (B.vsize p + 1) + (Nat.log2 (C p) + 1) * (S.kw p + 1)
     prep p := (C p + D p) * (S.kw p + Nat.log2 (C p) + 1)
     rounds p pol := 1 + Σ_{h in heads pol} (delay h + B.wmax p (wp pol) + 2)
     fits p pol := S.wf p /\ Sched.cuts p pol = true
     work p pol := prep p + (C p + D p) * rounds p pol * unit p *)
Parameter T_run_le : forall p pol fuel, fits p pol ->
  T_run p pol fuel <= c_wl * (work p pol + N.size_nat fuel + 1).
Parameter T_run_height_le : forall p pol fuel h, S.wf p -> widening_free pol ->
  (forall a b, B.inv p a -> B.inv p b -> L.leb a b = true -> L.leb b a = false -> rk a < rk b <= h) ->
  T_run p pol fuel <= c_wl * (prep p + (C p + h * D p) * unit p + N.size_nat fuel + 1).
Parameter run_bigO : bigO (fun x => fits (fst x) (snd x))
  (fun x => work (fst x) (snd x)) (fun x => T_run (fst x) (snd x) (fuel_for (fst x) (snd x))).
```

`WORKLIST_PLAN`, in outline:
- `W1_prepare`: `T_prepare p <= k * prep p`.
- `W2_eval`: one row evaluation costs at most `k * (length deps + 1) * unit p`, on stores whose values satisfy `inv`.
- `W3_update`: `P.update` keeps `inv`; the readers pushed on a change cost `k * degree * unit_pq`, amortised against `Q.phi`.
- `W4_credit` (finite height): potential `k * (|queue| + Σ_x (h - rank x) * degree x) * unit + Q.phi`; each step lowers it by its cost. This is the landed credit invariant of `FixpointWorklistCost`.
- `W5_round` (widening at heads): between two changes of a head value, the least priority popped among non-head targets never decreases, so each non-head row is evaluated at most once and head rows at most `1 + deps` times. A round therefore costs at most `(C + D) * unit`. This uses `cuts`.
- `W6_rounds`: there are at most `rounds p pol` rounds, by the domains' `head_updates_le` and `B.wrank_le`.
- `W7_run`: `loopN` with the potential `(remaining rounds) * (C + D) * unit + queue credit`.

`W5` is new mathematics; I argued it on paper and it is not checked. If it slips, `T_run_height_le` and the same credit argument with every key a head (`rounds` replaced by `delay + wmax + 2` per key) still give a contract for widening analyses.

### 3.6 Program presentations

A presentation is a module that reads a program type; the program is a value.

```coq
Module Type SEMANTICS (P : TYPE).                  (* spec only *)
  Parameter state : Type.
  Parameter initial : P.t -> state -> Prop.
  Parameter step : P.t -> state -> state -> Prop.
End SEMANTICS.
Inductive reachable {S} (init : S -> Prop) (step : S -> S -> Prop) : S -> Prop := (* init, step *).
(* TRACES (P) (M : SEMANTICS P): event, lstep, endings and same_behaviour, ported from ProgramSemantics;
   used by transformations, for example SSA destruction *)

Module Type CFG_OPS (P : TYPE) (N : KEY_OPS) (E : TYPE).
  Parameter entries : P.t -> list N.t.
  Parameter edges : P.t -> list E.t.
  Parameter src : P.t -> E.t -> N.t.
  Parameter dst : P.t -> E.t -> N.t.
End CFG_OPS.
Module Type CFG_ADJ_OPS (P : TYPE) (N : KEY_OPS) (E : TYPE) (Import C : CFG_OPS P N E).
  Parameter nodes : P.t -> list N.t.
  Parameter out : P.t -> N.t -> list E.t.
  Parameter inc : P.t -> N.t -> list E.t.
End CFG_ADJ_OPS.
(* CFG_LAWS: wf; out_spec and inc_spec against edges, src and dst.  CFG_TIME: linear in the output.
   Program/Cfg.v: graph_of : P.t -> digraph through N.encode, and a Prepared functor that supplies
   CFG_ADJ_OPS from CFG_OPS by building the tables once. *)

Module Type CFG_LINK (P : TYPE) (N : KEY) (E : TYPE) (C : CFG_OPS P N E) (M : SEMANTICS P).
  Parameter point : M.state -> N.t.
  Parameter taken : P.t -> M.state -> M.state -> E.t -> Prop.
  Parameter init_entry : forall p s, M.initial p s -> In (point s) (C.entries p).
  Parameter step_edge : forall p s s1, reachable (M.initial p) (M.step p) s -> M.step p s s1 ->
    exists e, taken p s s1 e /\ In e (C.edges p) /\ C.src p e = point s /\ C.dst p e = point s1.
End CFG_LINK.
```

| Presentation | Operations | Semantic link (laws) |
|---|---|---|
| `VARS (P N E C) (X : KEY)` | `uses`, `defs : P.t -> E.t -> list X.t`; `exits : P.t -> N.t -> list X.t` | `VARS_LINK`: a store reader `get : state -> X.t -> val`; `defs_frame` (a variable not defined on the edge keeps its value); `uses_determine` (two states that agree on the uses take the same edge and agree on the defs) |
| `SSA (P N E C) (V : KEY)` | `def : P.t -> V.t -> definition`; `home : P.t -> V.t -> N.t`; `params : P.t -> N.t -> list V.t`; `args : P.t -> E.t -> list (V.t * V.t)` | `SSA_LAWS`: one definition per value; uses are dominated by definitions (through `Dom`). `SSA_LINK`: `venv : state -> V.t -> option val`; a defined value keeps its value while control stays dominated by its home (landed `ProgramStrict`). The engines' `Ssa/Lang` instantiates this |
| `CALLS (P) (F S : KEY)` | `functions`, `roots`, `sites_of : P.t -> F.t -> list S.t`, `caller_of`, `resolve : P.t -> S.t -> list F.t`; derived `call_graph : P.t -> digraph` | `CALLS_LINK`: `active : state -> list F.t`; every call step is from a listed site to a resolved callee; the stack is a path in the call graph |
| `ICFG` | `CFG` plus `kind : P.t -> E.t -> edge_kind` (`Intra`, `Call s`, `Return s`, `CallToReturn s`) | `ICFG_LINK`: matched call and return edges |
| `ALIAS (R : KEY)` | `disjoint`, `covers : R.t -> R.t -> bool` | `ALIAS_LAWS`, against `holds : state -> R.t -> loc -> Prop`: `disjoint r q = true` means no location is in both; `covers r q = true` means inclusion |
| `MEMORY (P N E C) (R : KEY) (A : ALIAS R)` | `effects : P.t -> E.t -> list (effect R.t)` (top-level `Read`, `Write`, `Alloc`, `Free`, `Barrier`) | `MEMORY_LINK`: a region disjoint from every written region keeps its contents across the edge; every byte read or written is covered by a listed effect |

### 3.7 Frameworks

Each framework is `XCode <: SYSTEM_OPS L`, `X <: SYSTEM L` and `XT <: SYSTEM_T L`, plus a sibling `XSound`. All of them give the solver the same thing, a system.

**Dense** (`Framework/DenseSig.v`, `Dense.v`)

```coq
Inductive direction := Forward | Backward.
Inductive dense_row (N E : Type) := Seed (n : N) | Flow (e : E).

Module Type FLOW_OPS (P : TYPE) (N : KEY_OPS) (E : TYPE) (L : LATTICE_OPS).
  Parameter dir : direction.
  Parameter boundary : P.t -> N.t -> L.t.           (* the value seeded at entries (forward) or at exits (backward) *)
  Parameter transfer : P.t -> E.t -> L.t -> L.t.
End FLOW_OPS.

Module DenseCode (P : TYPE) (N : KEY_OPS) (E : TYPE) (C : CFG_OPS P N E)
                 (L : LATTICE_OPS) (T : FLOW_OPS P N E L) <: SYSTEM_OPS L.
  (* key := N.t; key_code := N.encode; row := dense_row N.t E.t; frame := E.t;
     forward:  start (Flow e) := Ask (C.src p e) e;  resume e a := Ret (T.transfer p e a);
               target (Flow e) := C.dst p e;  deps (Flow e) := [C.src p e];  sides := nil;
     backward: src and dst exchanged *)

Module DenseSound (P N E C L T) (M : SEMANTICS P) (K : FLOW_LINK P N E C L T M).
  Include Dense P N E C L T.
  (* FLOW_LINK: point; gamma : L.t -> M.state -> Prop with gamma_mono; init_sound;
     step_sound: every step follows an edge whose transfer preserves gamma *)
  Theorem covers : forall p look, T.dir = Forward -> post_solution p look ->
    forall s, reachable (M.initial p) (M.step p) s -> K.gamma (look (K.point s)) s.
  (* covers_backward: with BACKWARD_LINK, the value at a point holds of every execution suffix from it
     (landed FrameworkDenseForward, Witness, Agreement) *)
```

With `C : CFG_OPS <+ CFG_ADJ_OPS` and `E : KEY_OPS`, `DenseLocalCode <: LOCAL_SYSTEM_OPS L` answers `rows_of` from `C.inc`.

**Gen/kill** (`GenKill.v`): `GenKill (P N E C) (F : KEY) (S : SET F) (G : GENKILL_OPS P E F S)`, where `GENKILL_OPS` has `dir`, `may : bool`, `gen`, `kill : P.t -> E.t -> S.t` and `init : P.t -> S.t`. It is `Dense` over `MaySet` or `MustSet` with `transfer p e a := S.union (gen p e) (S.diff a (kill p e))`.
- `may_covers`: a fact generated on some path and not killed afterwards is in the solution at the path's end.
- `must_covers`: the dual.
- With `SOLVER_LEAST`: the solution equals the path meaning exactly (landed `GenkillLeast`).

**Environment abstract interpretation** (`Interp.v`)

```coq
Inductive action (K G X : Type) :=
  | Assign (x : X) (e : term K X) | Havoc (x : X) | Assume (g : G) (es : list (term K X)).
(* exec (ev) (holds) (eqb) : (X -> V) -> action K G X -> (X -> V) -> Prop; exec_all for lists.  Top level. *)

Module Type ACTIONS_OPS (P : TYPE) (E : TYPE) (X : KEY_OPS) (L : LANG_OPS).
  Parameter actions : P.t -> E.t -> list (action L.op L.guard X.t).
End ACTIONS_OPS.
Module Type INTERP_LINK (P : TYPE) (N : KEY) (E : TYPE) (C : CFG_OPS P N E) (X : KEY) (L : LANG)
                        (A : ACTIONS_OPS P E X L) (M : SEMANTICS P).
  Parameter point : M.state -> N.t.
  Parameter store : M.state -> X.t -> L.val.
  Parameter init_entry : forall p s, M.initial p s -> In (point s) (C.entries p).
  Parameter step_edge : forall p s s1, M.step p s s1 ->
    exists e, In e (C.edges p) /\ C.src p e = point s /\ C.dst p e = point s1 /\
      exec_all L.eval L.holds X.eqb (store s) (A.actions p e) (store s1).
End INTERP_LINK.

Module InterpCode (P N E C) (X : KEY_OPS) (L : LANG_OPS) (V : VALUE_DOMAIN_OPS L)
                  (A : ACTIONS_OPS P E X L) (D : STATE_DOMAIN_OPS X L V) <: SYSTEM_OPS D.
  (* an inner module Flow (boundary := D.top; transfer := a fold of D.assign, D.havoc, D.assume over the
     actions), then Include DenseCode P N E C D Flow *)

Module InterpSound (P N E C) (X : KEY) (L : LANG) (V : VALUE_DOMAIN L) (A) (D : STATE_DOMAIN X L V)
                   (M : SEMANTICS P) (K : INTERP_LINK P N E C X L A M).
  Include Interp P N E C X L V A D.
  Theorem covers : forall p look, post_solution p look ->
    forall s, reachable (M.initial p) (M.step p) s -> D.gamma (look (K.point s)) (K.store s).
```

`covers` was proved in the miniature in about 25 lines, from `gamma_mono`, `gamma_top` and the three transfer laws. It uses no lattice law. This is the theorem the domains' `analysis_no_alarm_safe` instantiates.

**Sparse SSA** (`Sparse.v`): `Sparse (P N E C) (S : SSA …) (L : LANG) (V : VALUE_DOMAIN L) (T : SSA_TRANSFER_OPS)`. Keys are SSA values, or values and edges for conditional propagation (`sum_code`). There is one row per definition; a φ row asks each argument.
- `covers : post_solution p look -> reachable s -> SL.venv s v = Some c -> V.gamma (look v) c`. It needs `SSA_LAWS` and `SSA_LINK`. Ported from `FrameworkSparseSound`.

**Summaries** (`Summary.v`): `Summary (P) (F S : KEY) (CL : CALLS P F S) (L : LATTICE) (B : BODY_OPS)`. Keys are functions, or `(function, context)` through `pair_code`. A function's row asks the summaries of its callees and may `Side`-contribute entry facts to them.
- `covers`: every finished call satisfies its callee's summary; every call entry is covered by the entry fact. Ported from `FrameworkSummarySound`.

**IFDS and IDE** (`Ifds.v`, `Ide.v`): `Ifds (P N E) (I : ICFG …) (F : KEY) (FL : FLOW_FUN_OPS)`, with `FLOW_FUN_OPS` having `flow : P.t -> E.t -> F.t -> list F.t` and `seeds`. Keys are path edges `(d1, n, d2)` through `pair_code`, values are booleans. It is a `LOCAL_SYSTEM`, so that `Incremental.demand` explores only reachable path edges. `Ide` replaces booleans by micro-functions over a `LATTICE`.
- `covers : post_solution p look -> valid_path p entry n pi -> In d (path_facts pi) -> look (d0, n, d) = true`. Ported from `FrameworkTabSound` and `TabPaths`.
- The bespoke tabulation engine (records, queues, jump closures: about 4,700 lines beyond its cost files) is not converted. At batch-3 time the alternative of four rules on `Egglog`, whose least-model theorem gives the same statement, should be weighed against this functor.

---

## 4. Disposition of landed code

Lines are today's (`galois-integrate`); targets are estimates.

| Family | Lines | Action | Target | Reason |
|---|---|---|---|---|
| **Cost** (all) | 1,597 | delete | 0 | replaced by Argent; `Base/Loop.v` (120) is new |
| All `*Cost/*Credit/*Debt/*Potential/*Budget` files in core packages | 21,488 (Base 2,746, Graph 10,447, Fixpoint 4,950, Framework 3,345) | delete, after harvesting each potential and invariant into the matching `PLAN` | 0 | tick theorems are re-proved against derived time functions |
| `BaseEncoding`, `BaseEq`, `BaseKeyTactics` | 537 | merge | `Key.v` 250 | records become `KEY` |
| `BaseCode` | 1,157 | rewrite | `Code.v` 250 | `glue` codes; decoders have no consumer |
| `BaseTrie`, `BaseTrieMerge` | 1,125 | convert in place | `Trie.v` 800 | sound core; value proofs carry |
| `BaseMap`, `BaseSet` | 1,698 | convert | `Map.v` 600, `Set.v` 350 | thin functors; the 682 `(E : encoding K)` binders vanish |
| `BaseUnionFind`, `Rank`, `Loop` | 1,949 | rewrite, harvesting proofs | `UnionFind.v` 900 | union by size on `positive` (engines' interface) |
| `BaseHeap`, `HeapBinomial`, `HeapLoop` | 2,195 | convert | `Heap.v` 1,100 | lazy-deletion heap behind `PQ` |
| `BaseIntern`, `BaseIndex` | 966 | convert | 550 | interning; grouping used by the solver index |
| `BaseSlot`, `Prepared`, `Memo`, `MemoState`, `IntervalSet`, `Rel`, `Certify`, tactics | 2,613 | delete (archive) | 0 | consumers were `Analyses` and the deferred `Memory`; raw `PTrie` access replaces slots; a boolean check plus a theorem replaces `certify` |
| `LatticeCore`, `Height`, `Concrete`, `Domain` | 797 | rewrite as signatures | `LatticeSig.v`, `Gamma.v` 450 | records become module types |
| `LatticeKit`, `KitFamily`, `Sub`, `Tactics` | 775 | delete | 0 | functor parameters replace kits; `BUDGET` replaces invariant subtypes |
| `LatticeSimple`, `Flat`, `Adjoin`, `Lift`, `Product`, `Dual`, `Set`, `Bounded`, `Reduced` | 2,341 | convert in place | 1,700 | the combinators of §3.2 |
| `LatticeEnv` | 1,242 | split | `MapLattice.v` 450; the rest to the domains' `States/Env` | lattice part and state part |
| `LatticeDisjunction` | 632 | convert | `Disjunction.v` 400 | lattice part; the domains add the transfers |
| `LatticePartition*` | 1,035 | delete (archive) | 0 | only GVN used it |
| `GraphModel`, `GraphPrepared` | 1,202 | rewrite | `Data.v`, `Spec.v`, `Digraph.v` 600 | closures become first-order data |
| `GraphSearch*`, `Visitor`, `ColourSpec`, `PathsSpec` (non-cost) | 5,585 | convert in place | 3,300 | visitor record becomes a functor parameter |
| `GraphTarjan*`, `SccSpec`, `Condense` (non-cost) | 4,578 | convert | 2,600 | SCC as a search client |
| `GraphHier*`, `WeakOrder*`, `CheckWto` (non-cost) | 3,200 | convert | 2,200 | keep `check_correct`, `cycles_have_head`, `ranks_forward`; the producer keeps code only |
| `GraphDom*`, `GraphCheckDom` (non-cost) | about 12,000 | keep the checker, its specification and one producer; delete the other producers, backends and transports | 4,500 | certified by the checker. This family needs a file-level pass before conversion; I did not read all 60 files |
| `GraphFrontier*` (non-cost) | 2,276 | convert | 1,500 | SSA construction needs it |
| `GraphLoop*`, `Reducibility` | 1,337 | convert | 900 | loop forest |
| `GraphReach`, `GraphWalk` | 1,254 | delete | 0 | no consumer; reachability is a 40-line search client |
| `GraphFixtures` | 430 | move to `tests/` | — | fixtures |
| `FixpointQuery`, `System`, `Analysis`, `Solver`, `Eval`, `Check`, `Certified`, `Analyze`, `Index`, `Least` | 1,848 | rewrite (small, sound kernel) | 1,500 | `Query`, `SystemSig`, `Policy`, `Schedule`, `Check`, `Certified`, `Indexed` |
| `FixpointWorklist`, `WorklistWiden`, `WorklistProof` | 1,730 | convert the code; drop the soundness proof, keeping its invariants for `SOLVER_LEAST` | `Worklist.v` 450 code + 1,100 time proofs | the default engine |
| `FixpointKleene`, `Nested*`, `Total*`, `Cut`, `Cycles` | 4,180 non-cost | delete | 0 | §3.5 |
| `FixpointNarrow*` | 342 non-cost | rewrite | `Narrow.v` 250 | solver-independent |
| `FixpointLocal*`, `Partial` | 1,414 non-cost | delete after the engines harvest | 0 | replaced by `Incremental` |
| `ProgramSemantics`, `Steps`, `Runs`, `Simulation` | 693 | convert | 500 | `SEMANTICS`, `TRACES` |
| `ProgramCfg`, `Link`, `EdgeProjection`, `Completion` | 492 | convert | 400 | `CFG`, links |
| `ProgramSsa`, `SsaPoints`, `Strict` | 1,082 | convert | 800 | `SSA`; align with the engines' `Ssa/Lang` |
| `ProgramCalls`, `Icfg`, `Memory`, `Effects` | 722 | convert | 650 | `CALLS`, `ICFG`, `MEMORY`, `ALIAS` |
| `ProgramSkeleton*`, `Structured` | 2,931 | delete (archive) | 0 | structured-syntax machinery; the IR is block-and-goto. Confirm with the engines architect before deleting |
| `FrameworkDense*`, `Env*`, `Util`, `Rows` | 1,725 | convert | 1,100 | `Dense`, `Interp` |
| `FrameworkBitvector`, `Genkill*` | 2,057 | convert | 1,300 | `GenKill` |
| `FrameworkSparse*` | 1,803 | convert | 1,400 | `Sparse` |
| `FrameworkSummary*` | 1,827 | convert | 1,300 | `Summary` |
| `FrameworkTab*` model and soundness, `Ifds`, `Ide` | about 3,000 | port into the system functors | 1,800 | `Ifds`, `Ide` |
| `FrameworkTab*` engine | about 4,700 | delete | 0 | bespoke tabulation engine |
| `FrameworkRegion`, `Stack`, `Micro` | 399 | delete | 0 | go with the skeleton machinery |
| **Core total** | about 104,000 | | **about 35,000**, plus about 4,500 of `*Sig.v` | |

Outside core, for the record: `Analyses` (32,756) is deleted, `Datalog` (8,686) and `Egraph` (8,867) are the engines', `Domains` (20,243) the domains', `Bits` (3,018) is kept.

---

## 5. The user story

The shortest honest client: a flowchart language whose edges assign or test, the library's interval domain and environment state, the default solver, the certified run, the soundness theorem, and extraction.

**What compiled.** A miniature of this file and of the library pieces it uses, in one REPL session. The miniature differs from the text below as follows:
- expressions had fixed arity instead of the nested `term`, and each edge carried one action;
- `SYSTEM` took its key as a `KEY` parameter instead of inline codes;
- fuel was `nat`, and the solver behind `SOLVER_OPS` was a 20-line round-robin;
- the hint field was named `hint`;
- the laws of the interval and state domains were `Admitted`.

Proved in the miniature: `check_post_iff`, `analyze_sound`, the framework's `covers`, both link lemmas, `count_covers` and `exit_value`. `Print Assumptions exit_value` listed exactly the five admitted state-domain laws. The text below was not compiled.

```coq
From Stdlib Require Import List PArith ZArith Lia.
From Galois.Base      Require Import Key Trie Map Heap.
From Galois.Fixpoint  Require Import Query Policy Worklist Certified.
From Galois.Program   Require Import SemanticsSig CfgSig.
From Galois.Framework Require Import Interp.
From Galois.Domains   Require Import LangSig ZLang Interval.
From Galois.States    Require Import Env.
Import ListNotations.

(* 1. The language: a flowchart; an edge assigns or tests. *)
Inductive instr :=
  | Set_  (x : positive) (e : term zop positive)
  | Guard (g : zguard) (es : list (term zop positive)).
Record toy := Toy { entry : positive; code : list (positive * instr * positive) }.

Module ToyProg <: TYPE. Definition t := toy. End ToyProg.
Module ToyEdge <: TYPE. Definition t := (positive * instr * positive)%type. End ToyEdge.

Module ToyCfg <: CFG_OPS ToyProg PosKey ToyEdge.        (* how to read a toy program as a CFG *)
  Definition entries (p : toy) : list positive := [entry p].
  Definition edges (p : toy) : list ToyEdge.t := code p.
  Definition src (p : toy) (e : ToyEdge.t) : positive := fst (fst e).
  Definition dst (p : toy) (e : ToyEdge.t) : positive := snd e.
End ToyCfg.

Module ToyActions <: ACTIONS_OPS ToyProg ToyEdge PosKey ZLang.
  Definition actions (p : toy) (e : ToyEdge.t) : list (action zop zguard positive) :=
    match snd (fst e) with Set_ x ex => [Assign x ex] | Guard g es => [Assume g es] end.
End ToyActions.

(* 2. Its semantics: a state is a program point and a store. *)
Module ToySem <: SEMANTICS ToyProg.
  Definition state := (positive * (positive -> Z))%type.
  Definition initial (p : toy) (s : state) : Prop := fst s = entry p.
  Definition step (p : toy) (s s1 : state) : Prop :=
    exists e, In e (code p) /\ fst (fst e) = fst s /\ snd e = fst s1 /\
      exec_all ZLang.eval ZLang.holds PosKey.eqb (snd s) (ToyActions.actions p e) (snd s1).
End ToySem.

(* 3. The link: the only proofs the client owes. *)
Module ToyLink <: INTERP_LINK ToyProg PosKey ToyEdge ToyCfg PosKey ZLang ToyActions ToySem.
  Definition point (s : ToySem.state) : positive := fst s.
  Definition store (s : ToySem.state) : positive -> Z := snd s.
  Lemma init_entry : forall p s, ToySem.initial p s -> In (point s) (ToyCfg.entries p).
  Proof. intros p s H. left. symmetry. exact H. Qed.
  Lemma step_edge : forall p s s1, ToySem.step p s s1 ->
    exists e, In e (ToyCfg.edges p) /\ ToyCfg.src p e = point s /\ ToyCfg.dst p e = point s1 /\
      exec_all ZLang.eval ZLang.holds PosKey.eqb (store s) (ToyActions.actions p e) (store s1).
  Proof. intros p s s1 H. exact H. Qed.
End ToyLink.

(* 4. Wiring: every functor application is named. *)
Module XM    := TrieMap PosKey.
Module Dom   := Env PosKey XM ZLang Interval.                 (* library interval domain, library state *)
Module Sys   := InterpSound ToyProg PosKey ToyEdge ToyCfg PosKey ZLang Interval ToyActions Dom ToySem ToyLink.
Module Pol   := Policy Dom.
Module Solve := WorklistCode Dom Sys Pol Heap.                (* a solver needs no proofs *)
Module Run   := Certified Dom Sys Solve.

(* 5. A program:  i := 0; while (i < 10) i := i + 1 *)
Definition i : positive := 1.
Definition lit (z : Z) : term zop positive := Node (ZConst z) [].
Definition count : toy := Toy 1
  [ (1, Set_ i (lit 0), 2);
    (2, Guard ZLt [Leaf i; lit 10], 3);
    (3, Set_ i (Node ZAdd [Leaf i; lit 1]), 2);
    (2, Guard ZGe [Leaf i; lit 10], 4) ]%positive.

(* The policy is a value: widen at node 2, no thresholds, two narrowing passes. *)
Definition pol : policy Interval.wparam :=
  Policy PTrie.empty (PTrie.set 2%positive (HeadCfg 0 0) PTrie.empty) Thresholds.none 2.

Eval vm_compute in Run.analyze count pol 100%N.

(* 6. Soundness, instantiated. *)
Theorem count_covers : forall m, Run.analyze count pol 100%N = Solved m ->
  forall s, reachable (ToySem.initial count) (ToySem.step count) s ->
  Dom.gamma (Run.look m (fst s)) (snd s).
Proof. intros m H s Hs. exact (Sys.covers count _ (Run.analyze_sound _ _ _ _ H) s Hs). Qed.

Corollary exit_value : forall s, reachable (ToySem.initial count) (ToySem.step count) s ->
  fst s = 4%positive -> snd s i = 10%Z.
Proof.
  intros s Hs Hpc.
  destruct (Run.analyze count pol 100%N) as [m|m|why] eqn:H; [|vm_compute in H; discriminate..].
  pose proof (count_covers m H s Hs) as Hg.
  vm_compute in H. injection H as <-. rewrite Hpc in Hg.
  specialize (Hg i). cbn in Hg. lia.
Qed.
```

- The client writes 2 link lemmas and no law about lattices, solvers or maps.
- In the miniature the raw solver left `i ∈ [0, +∞)` at node 2. The certified run with two narrowing passes was precise enough for `exit_value` to close.
- A threshold list in `wp` is the other way to that precision; it changes the policy value and nothing else.
- The cost theorem is the same wiring one level up (`EnvT`, `InterpT`, `WorklistT`, `CertifiedT`, with a `BUDGET` for intervals) and reads `RunT.T_analyze count pol fuel <= c * (work count pol + …)`. The client proves nothing new if its presentation modules come with `TimeFun` lines and the four contracts of `CFG_TIME` and `ACTIONS_TIME`.

**Extraction.** The code tower has the same wiring with the `Code` suffix, and `eq_refl` links the two (it did in the miniature: `Check (eq_refl : RunX.analyze = Run.analyze)`).

```coq
Module XMx := TrieMapCode PosKey.        Module DomX := EnvCode PosKey XMx ZLang IntervalCode.
Module SysX := InterpCode ToyProg PosKey ToyEdge ToyCfg PosKey ZLang IntervalCode ToyActions DomX.
Module PolX := PolicyCode DomX.          Module SolveX := WorklistCode DomX SysX PolX HeapCode.
Module RunX := CertifiedCode DomX SysX SolveX.
Extraction "toy.ml" RunX.
```

Shape of the OCaml, trimmed from the miniature's actual output (its names):

```ocaml
module type WLATTICE_OPS = sig
  type t
  val leb : t -> t -> bool
  val bot : t
  val join : t -> t -> t
  type hint
  val widen : hint -> t -> t -> t
  val narrow : t -> t -> t
end
module RoundRobinCode =
 functor (X:KEY_OPS) -> functor (L:WLATTICE_OPS) ->
 functor (S:sig
   type prog  type row  type frame
   val rows : prog -> row list
   val target : prog -> row -> X.t
   val start : prog -> row -> (X.t, L.t, frame) query
   val resume : prog -> frame -> L.t -> (X.t, L.t, frame) query
   val deps : prog -> row -> X.t list
 end) ->
 struct
  type store = L.t PTrie.t
  let look = ...   let update = ...   let row_step = ...   let step = ...
  let run p pol fuel = ...
 end
module EnvCode = functor (P:TYPE) -> functor (N:KEY_OPS) -> ... ->
 struct
  module Flow = struct let entry = ...  let transfer = ... end
  type prog = P.t
  type row = (N.t, E.t) dense_row
  let rows = ...  let target = ...  let start = ...  let resume = ...  let deps = ...
 end
```

No law, no `T_` and no proof argument appears. The engines' `Exec/Roots.v` then exposes plain-data entry points so that no functor type reaches the driver.

---

## 6. One complete skeleton: union-find

This is the engines' interface (`positive` keys, union by size, `(winner, loser)`). Both files compiled as shown, with one substitution: in place of the nine `TimeFun` lines the REPL had nine placeholder definitions `Definition T_x … : nat := 0`. Bodies are real, so the test file can run before any proof exists. For a component whose algorithm is open, a body is a stub such as `Definition find x u := (x, u).`

Checked: `find 7`, `find 1` and `find 9` after three unions gave `(2, 2, 9)`; a redundant union returned `None`; `Check (eq_refl : UnionFindCode.find = UnionFindT.find)` passed; `Print Assumptions UnionFindT.find_bigO` listed only the admitted `T_find_le`.

```coq
(* theories/Base/UnionFindSig.v *)
From Stdlib Require Import List PArith NArith Arith.
From Argent Require Import Time.
From Galois.Base Require Import Trie.

Module Type UNION_FIND_OPS.
  Parameter t : Type.
  Parameter empty : t.
  Parameter add   : positive -> t -> t.
  Parameter find  : positive -> t -> positive * t.
  Parameter union : positive -> positive -> t -> option (positive * positive) * t.   (* Some (winner, loser) *)
End UNION_FIND_OPS.

Module Type UNION_FIND_LAWS (Import U : UNION_FIND_OPS).
  (* spec: wf mem repr size_of card width *)
  Parameter wf      : t -> Prop.
  Parameter mem     : t -> positive -> Prop.
  Parameter repr    : t -> positive -> positive.
  Parameter size_of : t -> positive -> nat.
  Parameter card    : t -> nat.
  Parameter width   : t -> nat.
  Parameter wf_empty : wf empty.
  Parameter wf_add   : forall x u, wf u -> wf (add x u).
  Parameter wf_find  : forall x u, wf u -> wf (snd (find x u)).
  Parameter wf_union : forall x y u, wf u -> wf (snd (union x y u)).
  Parameter mem_add   : forall x u y, wf u -> (mem (add x u) y <-> mem u y \/ y = x).
  Parameter mem_find  : forall x u y, wf u -> (mem (snd (find x u)) y <-> mem u y).
  Parameter mem_union : forall x y u z, wf u -> (mem (snd (union x y u)) z <-> mem u z \/ z = x \/ z = y).
  Parameter repr_empty : forall x, repr empty x = x.
  Parameter repr_idem  : forall u x, wf u -> repr u (repr u x) = repr u x.
  Parameter repr_add   : forall x u y, wf u -> repr (add x u) y = repr u y.
  Parameter find_repr  : forall x u, wf u -> fst (find x u) = repr u x.
  Parameter find_same  : forall x u y, wf u -> repr (snd (find x u)) y = repr u y.
  Parameter union_none : forall x y u u1, wf u -> union x y u = (None, u1) ->
    repr u x = repr u y /\ forall z, repr u1 z = repr u z.
  Parameter union_some : forall x y u w l u1, wf u -> union x y u = (Some (w, l), u1) ->
    repr u x <> repr u y /\
    ((w = repr u x /\ l = repr u y) \/ (w = repr u y /\ l = repr u x)) /\
    forall z, repr u1 z = if Pos.eqb (repr u z) l then w else repr u z.
  Parameter union_by_size : forall x y u w l u1, wf u -> union x y u = (Some (w, l), u1) ->
    size_of u l <= size_of u w.
  Parameter size_of_union : forall x y u w l u1, wf u -> union x y u = (Some (w, l), u1) ->
    size_of u1 w = size_of u w + size_of u l.
  Parameter size_of_le_card : forall u x, wf u -> mem u x -> size_of u x <= card u.
  Parameter card_empty : card empty = 0.
  Parameter card_add   : forall x u, wf u -> card (add x u) <= card u + 1.
  Parameter card_find  : forall x u, wf u -> card (snd (find x u)) = card u.
  Parameter card_union : forall x y u, wf u -> card (snd (union x y u)) <= card u + 2.
  Parameter width_mem  : forall u x, wf u -> mem u x -> Pos.size_nat x <= width u.
End UNION_FIND_LAWS.
Module Type UNION_FIND := UNION_FIND_OPS <+ UNION_FIND_LAWS.

Module Type UNION_FIND_TIME (Import U : UNION_FIND).
  Parameter T_add   : positive -> t -> nat.
  Parameter T_find  : positive -> t -> nat.
  Parameter T_union : positive -> positive -> t -> nat.
  Parameter c_uf : nat.
  Parameter T_add_le : forall x u, wf u ->
    T_add x u <= c_uf * (Pos.size_nat x + Nat.log2 (card u) + 2).
  Parameter T_find_le : forall x u, wf u ->
    T_find x u <= c_uf * (Nat.log2 (card u) + 1) * (Nat.max (width u) (Pos.size_nat x) + 1).
  Parameter T_union_le : forall x y u, wf u ->
    T_union x y u <= c_uf * (Nat.log2 (card u + 2) + 1)
                          * (Nat.max (width u) (Nat.max (Pos.size_nat x) (Pos.size_nat y)) + 1).
  (* published *)
  Parameter find_bigO : bigO (fun xu : positive * t => wf (snd xu))
    (fun xu => (Nat.log2 (card (snd xu)) + 1) * (Nat.max (width (snd xu)) (Pos.size_nat (fst xu)) + 1))
    (fun xu => T_find (fst xu) (snd xu)).
End UNION_FIND_TIME.
Module Type UNION_FIND_T := UNION_FIND <+ UNION_FIND_TIME.

Module Type UNION_FIND_PLAN (Import U : UNION_FIND_T).
  (* internals the chain talks about *)
  Parameter parent_of : positive -> t -> positive.
  Parameter walk_step : t -> positive * list positive -> positive * list positive + positive * list positive.
  Parameter walk      : positive -> t -> positive * list positive.
  Parameter compress  : positive -> list positive -> t -> t.
  Parameter link      : positive -> positive -> t -> t.
  Parameter T_parent_of : positive -> t -> nat.
  Parameter T_walk_step : t -> positive * list positive -> nat.
  Parameter T_walk      : positive -> t -> nat.
  Parameter T_compress  : positive -> list positive -> t -> nat.
  Parameter T_link      : positive -> positive -> t -> nat.
  Parameter k_get k_step k_walk k_comp k_link : nat.          (* the implementer chooses the values *)
  Definition is_root (u : t) (x : positive) : Prop := parent_of x u = x.
  Definition ranked (u : t) (rk : positive -> nat) : Prop :=   (* ghost ranks: nothing is stored *)
    (forall x, mem u x -> ~ is_root u x -> rk x < rk (parent_of x u)) /\
    (forall r, mem u r -> is_root u r -> 2 ^ rk r <= size_of u r).
  (* F: functional chain *)
  Parameter F1_ranked    : forall u, wf u -> exists rk, ranked u rk.
  Parameter F2_rank_log  : forall u rk x, wf u -> ranked u rk -> mem u x -> rk x <= Nat.log2 (card u).
  Parameter F3_walk_root : forall x u, wf u -> fst (walk x u) = repr u x.
  Parameter F4_walk_path : forall x u, wf u -> mem u x ->
    length (snd (walk x u)) <= Nat.log2 (card u) /\
    forall y, In y (snd (walk x u)) -> mem u y /\ repr u y = repr u x.
  Parameter F5_compress  : forall u rk r path, wf u -> ranked u rk -> is_root u r ->
    (forall y, In y path -> mem u y /\ repr u y = r /\ y <> r) -> ranked (compress r path u) rk.
  Parameter F6_link      : forall u rk w l, wf u -> ranked u rk -> is_root u w -> is_root u l -> w <> l ->
    size_of u l <= size_of u w ->
    ranked (link w l u) (fun x => if Pos.eqb x w then Nat.max (rk w) (S (rk l)) else rk x).
  (* T: time chain; T_find_le follows from T3, T4 and F4, T_union_le from T_find_le twice and T5 *)
  Parameter T1_parent_of : forall x u, T_parent_of x u <= k_get * (Pos.size_nat x + 1).
  Parameter T2_walk_step : forall u s, wf u -> mem u (fst s) -> T_walk_step u s <= k_step * (width u + 1).
  Parameter T3_walk      : forall x u, wf u ->          (* loop_bound, Phi s := remaining rank * (k_step * (w + 1) + 1) *)
    T_walk x u <= k_walk * (Nat.log2 (card u) + 1) * (Nat.max (width u) (Pos.size_nat x) + 1).
  Parameter T4_compress  : forall r path u, wf u -> (forall y, In y path -> mem u y) ->
    T_compress r path u <= k_comp * (length path + 1) * (width u + 1).
  Parameter T5_link      : forall w l u, wf u -> mem u w -> mem u l ->
    T_link w l u <= k_link * (width u + Nat.log2 (card u) + 2).
End UNION_FIND_PLAN.
Module Type UNION_FIND_ALL := UNION_FIND_T <+ UNION_FIND_PLAN.
```

```coq
(* theories/Base/UnionFind.v *)
From Stdlib Require Import List PArith NArith Arith Lia.
From Argent Require Import Time Loop.
From Galois.Base Require Import Trie UnionFindSig.
Import ListNotations.

Record uf : Type := UF { parents : PTrie.t positive; sizes : PTrie.t N; count : N }.

Module UnionFindCode <: UNION_FIND_OPS.
  Definition t := uf.
  Definition empty : t := UF PTrie.empty PTrie.empty 0.
  Definition parent_of (x : positive) (u : t) : positive :=
    match PTrie.get x (parents u) with Some p => p | None => x end.
  Definition size_at (r : positive) (u : t) : N :=
    match PTrie.get r (sizes u) with Some n => n | None => 1%N end.
  Definition add (x : positive) (u : t) : t :=
    match PTrie.get x (parents u) with
    | Some _ => u
    | None => UF (PTrie.set x x (parents u)) (PTrie.set x 1%N (sizes u)) (N.succ (count u))
    end.
  Definition walk_step (u : t) (s : positive * list positive)
      : positive * list positive + positive * list positive :=
    let p := parent_of (fst s) u in
    if Pos.eqb p (fst s) then inr s else inl (p, fst s :: snd s).
  Definition walk (x : positive) (u : t) : positive * list positive :=
    match loop_fuel (walk_step u) (S (N.size_nat (count u))) (x, []) with inl s => s | inr s => s end.
  Definition compress (root : positive) (path : list positive) (u : t) : t :=
    UF (fold_left (fun m y => PTrie.set y root m) path (parents u)) (sizes u) (count u).
  Definition find (x : positive) (u : t) : positive * t :=
    let r := walk x u in (fst r, compress (fst r) (snd r) u).
  Definition link (w l : positive) (u : t) : t :=
    UF (PTrie.set l w (parents u)) (PTrie.set w (size_at w u + size_at l u)%N (sizes u)) (count u).
  Definition union (x y : positive) (u : t) : option (positive * positive) * t :=
    let fx := find x (add y (add x u)) in
    let fy := find y (snd fx) in
    let rx := fst fx in
    let ry := fst fy in
    let u2 := snd fy in
    if Pos.eqb rx ry then (None, u2)
    else if N.leb (size_at ry u2) (size_at rx u2) then (Some (rx, ry), link rx ry u2)
    else (Some (ry, rx), link ry rx u2).
End UnionFindCode.

Module UnionFind <: UNION_FIND.
  Include UnionFindCode.
  Definition support (u : t) : list positive := map fst (PTrie.elements (parents u)).
  Definition mem (u : t) (x : positive) : Prop := PTrie.get x (parents u) <> None.
  Definition card (u : t) : nat := N.to_nat (count u).
  Definition repr (u : t) (x : positive) : positive := Nat.iter (card u) (fun y => parent_of y u) x.
  Definition size_of (u : t) (x : positive) : nat :=
    length (filter (fun y => Pos.eqb (repr u y) (repr u x)) (support u)).
  Definition width (u : t) : nat := fold_right (fun y w => Nat.max (Pos.size_nat y) w) 0 (support u).
  Definition is_root (u : t) (x : positive) : Prop := parent_of x u = x.
  Definition ranked (u : t) (rk : positive -> nat) : Prop :=
    (forall x, mem u x -> ~ is_root u x -> rk x < rk (parent_of x u)) /\
    (forall r, mem u r -> is_root u r -> 2 ^ rk r <= size_of u r).
  Definition wf (u : t) : Prop :=
    card u = length (support u) /\
    (forall x p, PTrie.get x (parents u) = Some p -> mem u p) /\
    (forall r, mem u r -> is_root u r -> N.to_nat (size_at r u) = size_of u r) /\
    exists rk, ranked u rk.
  Lemma wf_empty : wf empty. Proof. Admitted.
  Lemma wf_add   : forall x u, wf u -> wf (add x u). Proof. Admitted.
  Lemma wf_find  : forall x u, wf u -> wf (snd (find x u)). Proof. Admitted.
  Lemma wf_union : forall x y u, wf u -> wf (snd (union x y u)). Proof. Admitted.
  Lemma mem_add   : forall x u y, wf u -> (mem (add x u) y <-> mem u y \/ y = x). Proof. Admitted.
  Lemma mem_find  : forall x u y, wf u -> (mem (snd (find x u)) y <-> mem u y). Proof. Admitted.
  Lemma mem_union : forall x y u z, wf u -> (mem (snd (union x y u)) z <-> mem u z \/ z = x \/ z = y).
  Proof. Admitted.
  Lemma repr_empty : forall x, repr empty x = x. Proof. reflexivity. Qed.
  Lemma repr_idem  : forall u x, wf u -> repr u (repr u x) = repr u x. Proof. Admitted.
  Lemma repr_add   : forall x u y, wf u -> repr (add x u) y = repr u y. Proof. Admitted.
  Lemma find_repr  : forall x u, wf u -> fst (find x u) = repr u x. Proof. Admitted.
  Lemma find_same  : forall x u y, wf u -> repr (snd (find x u)) y = repr u y. Proof. Admitted.
  Lemma union_none : forall x y u u1, wf u -> union x y u = (None, u1) ->
    repr u x = repr u y /\ forall z, repr u1 z = repr u z. Proof. Admitted.
  Lemma union_some : forall x y u w l u1, wf u -> union x y u = (Some (w, l), u1) ->
    repr u x <> repr u y /\
    ((w = repr u x /\ l = repr u y) \/ (w = repr u y /\ l = repr u x)) /\
    forall z, repr u1 z = if Pos.eqb (repr u z) l then w else repr u z. Proof. Admitted.
  Lemma union_by_size : forall x y u w l u1, wf u -> union x y u = (Some (w, l), u1) ->
    size_of u l <= size_of u w. Proof. Admitted.
  Lemma size_of_union : forall x y u w l u1, wf u -> union x y u = (Some (w, l), u1) ->
    size_of u1 w = size_of u w + size_of u l. Proof. Admitted.
  Lemma size_of_le_card : forall u x, wf u -> mem u x -> size_of u x <= card u. Proof. Admitted.
  Lemma card_empty : card empty = 0. Proof. reflexivity. Qed.
  Lemma card_add   : forall x u, wf u -> card (add x u) <= card u + 1. Proof. Admitted.
  Lemma card_find  : forall x u, wf u -> card (snd (find x u)) = card u. Proof. reflexivity. Qed.
  Lemma card_union : forall x y u, wf u -> card (snd (union x y u)) <= card u + 2. Proof. Admitted.
  Lemma width_mem  : forall u x, wf u -> mem u x -> Pos.size_nat x <= width u. Proof. Admitted.
End UnionFind.

Module UnionFindT <: UNION_FIND_ALL.
  Include UnionFind.
  TimeFun parent_of. TimeFun size_at. TimeFun add. TimeFun walk_step. TimeFun walk.
  TimeFun compress. TimeFun find. TimeFun link. TimeFun union.
  Definition k_get  : nat := PTrie.c_trie + 2.               (* STUB constants: adjust while proving *)
  Definition k_step : nat := k_get + 4.
  Definition k_walk : nat := 2 * k_step + 4.
  Definition k_comp : nat := PTrie.c_trie + 3.
  Definition k_link : nat := 2 * PTrie.c_trie + 6.
  Definition c_uf   : nat := 4 * (k_walk + k_comp + k_link + PTrie.c_trie + 4).
  Lemma F1_ranked    : forall u, wf u -> exists rk, ranked u rk.
  Proof. intros u H. exact (proj2 (proj2 (proj2 H))). Qed.
  Lemma F2_rank_log  : forall u rk x, wf u -> ranked u rk -> mem u x -> rk x <= Nat.log2 (card u).
  Proof. Admitted.
  Lemma F3_walk_root : forall x u, wf u -> fst (walk x u) = repr u x. Proof. Admitted.
  Lemma F4_walk_path : forall x u, wf u -> mem u x ->
    length (snd (walk x u)) <= Nat.log2 (card u) /\
    forall y, In y (snd (walk x u)) -> mem u y /\ repr u y = repr u x. Proof. Admitted.
  Lemma F5_compress  : forall u rk r path, wf u -> ranked u rk -> is_root u r ->
    (forall y, In y path -> mem u y /\ repr u y = r /\ y <> r) -> ranked (compress r path u) rk.
  Proof. Admitted.
  Lemma F6_link      : forall u rk w l, wf u -> ranked u rk -> is_root u w -> is_root u l -> w <> l ->
    size_of u l <= size_of u w ->
    ranked (link w l u) (fun x => if Pos.eqb x w then Nat.max (rk w) (S (rk l)) else rk x).
  Proof. Admitted.
  Lemma T1_parent_of : forall x u, T_parent_of x u <= k_get * (Pos.size_nat x + 1). Proof. Admitted.
  Lemma T2_walk_step : forall u s, wf u -> mem u (fst s) -> T_walk_step u s <= k_step * (width u + 1).
  Proof. Admitted.
  Lemma T3_walk      : forall x u, wf u ->
    T_walk x u <= k_walk * (Nat.log2 (card u) + 1) * (Nat.max (width u) (Pos.size_nat x) + 1).
  Proof. Admitted.
  Lemma T4_compress  : forall r path u, wf u -> (forall y, In y path -> mem u y) ->
    T_compress r path u <= k_comp * (length path + 1) * (width u + 1). Proof. Admitted.
  Lemma T5_link      : forall w l u, wf u -> mem u w -> mem u l ->
    T_link w l u <= k_link * (width u + Nat.log2 (card u) + 2). Proof. Admitted.
  Lemma T_add_le : forall x u, wf u ->
    T_add x u <= c_uf * (Pos.size_nat x + Nat.log2 (card u) + 2). Proof. Admitted.
  Lemma T_find_le : forall x u, wf u ->
    T_find x u <= c_uf * (Nat.log2 (card u) + 1) * (Nat.max (width u) (Pos.size_nat x) + 1).
  Proof. Admitted.
  Lemma T_union_le : forall x y u, wf u ->
    T_union x y u <= c_uf * (Nat.log2 (card u + 2) + 1)
                          * (Nat.max (width u) (Nat.max (Pos.size_nat x) (Pos.size_nat y)) + 1).
  Proof. Admitted.
  Theorem find_bigO : bigO (fun xu : positive * t => wf (snd xu))
    (fun xu => (Nat.log2 (card (snd xu)) + 1) * (Nat.max (width (snd xu)) (Pos.size_nat (fst xu)) + 1))
    (fun xu => T_find (fst xu) (snd xu)).
  Proof. exists c_uf. intros [x u] H. cbn [fst snd] in *. pose proof (T_find_le x u H). nia. Qed.
End UnionFindT.
```

Notes for the session that fills it:
- The bound is the worst case, Θ(log n · w), valid for every version of the structure.
- Compression is in the code. The invariant survives it because ranks are ghost: compression changes no rank, and a root's `2 ^ rank <= size` is unaffected.
- The fuel is `S (N.size_nat (count u))`, which is at least `log2 card + 1`; the count is binary so that computing the fuel costs O(log n).
- The amortised O(α(n)·w) bound stays a stretch goal behind the same signature.

---

## 7. The conversion recipe

**Input:** one landed file `theories/<Pkg>/<Pkg><Name>.v`, the frozen `<Name>Sig.v`, and the `Sig` files of what it uses. **Output:** `theories/<Pkg>/<Name>.v` with `<Name>Code`, `<Name>`, `<Name>T`.

Steps 1, 2 and 7 are textual (Haiku). Steps 3 to 6 need a model that reads Rocq (Sonnet).

1. **Header.** New file name without the package prefix. Replace `From Galois.Cost Require Import …` by `From Argent Require Import Time.` Require the component's `Sig` and its dependencies' `Sig` files.
2. **Delete.** Every theorem whose name ends in `_cost`, `_cost_le`, `_cost_equation` or starts with `ticks_`; every `Import Cost.Notations`; every `Arguments … : simpl never` for a deleted name. Keep each `f_equation` until step 3 has used it.
3. **Make each function pure.** For `Definition f_c … : Cost.t T := body`, write `Definition f … : T := body'`, where `body'` is `body` after these rewrites, applied everywhere:

   | Monadic | Pure |
   |---|---|
   | `Cost.ret e` | `e` |
   | `Cost.step ;; e` | `e` |
   | `let* x := m in k` | `let x := m in k` |
   | `Cost.bind m (fun x => k)` | `let x := m in k` |
   | `Cost.map g m` | `g m` |
   | `Cost.value e` | `e` |
   | `Cost.lift w g a` | `g a` |
   | `Cost.refine m H` | `m` |
   | `g_c args` | `g args` |
   | `fold_left_c`, `map_c`, `forallb_c`, `app_c` | `fold_left`, `map`, `forallb`, `app` |

   Delete the old `Definition f := Cost.value (f_c …)`. **Oracle:** the result must be the body stated by `f_equation`, up to the renames of step 4. If it is not, stop and report. Then delete `f_equation`.
4. **Dictionaries become functor parameters,** as the `Sig` says.
   - A binder `(E : encoding K)` becomes the parameter `K : KEY_OPS`; `encode E x` becomes `K.encode x`; the type `K` becomes `K.t`.
   - `(L : lattice A)` becomes `L : LATTICE_OPS`; `leb L a b` becomes `L.leb a b`; `A` becomes `L.t`.
   - A hypothesis `encoding_laws E` or `lattice_laws L` disappears: the plain functor takes `K : KEY`, `L : LATTICE`, and a use `(leb_refl H)` becomes `L.leb_refl`.
   - A record of closures (a visitor, a graph's `out_c`, a policy's `order_c`) becomes the functor parameter or the first-order data named in the `Sig`.
5. **Place the code.** Move every `Inductive` and `Record` above the first functor. Put the definitions in `Module <Name>Code (…_OPS) <: <NAME>_OPS … .` Compile this module alone before going on.
6. **Port the value lemmas** into `Module <Name> (…) <: <NAME> … .`, after `Include <Name>Code … .` and `Include <NAME>_SPEC … .` Rename to the `Sig`'s names. In each proof delete `autorewrite with galois_cost`, `cost_simpl`, `rewrite Cost.value_bind` and its relatives, and `change (Cost.value …)`; replace `rewrite f_equation` by `unfold f` or `cbn [f]`.
7. **Time tower.** `Module <Name>T (…_T) <: <NAME>_ALL … .`, `Include <Name> … .`, one `TimeFun` per definition of the code module in dependency order, each constant as `Definition c_x : nat := 1. (* STUB *)`, and every `_TIME` and `_PLAN` lemma stated and closed with `Proof. Admitted.`
8. **Gate.** The file compiles. The ported test file gives, under `vm_compute`, the values the old tests gave. Paste the old expected values; do not recompute them.

**When a proof breaks.**
- Haiku never repairs. It replaces the proof by `Proof. Admitted. (* CONVERT: <old theorem name>: <first line of the error> *)`.
- Sonnet may spend 15 minutes per proof. Allowed: unfolding differently, renaming hypotheses, replacing a rewrite with a deleted equation by `unfold` or `cbn`, reordering `intros`. Not allowed: changing a statement, adding a hypothesis, changing a definition, editing a `Sig`. After 15 minutes, the same `CONVERT` tag.
- If a statement in the `Sig` cannot be matched by the landed lemma (it is stronger, or false), leave it `Admitted` with `(* SIG-QUESTION: … *)` and report it. The `Sig` wins.
- `just admits` counts `CONVERT`, `STUB`, `PLAN-DEFECT` and plain `Admitted` separately, so each session sees what it inherits.

**Worked example: `LatticeDual.v`** (103 lines). Before, in excerpt:

```coq
Definition dual {A} (L : lattice A) (T : top L) (meet_c : A -> A -> Cost.t A) : lattice A :=
  {| leb_c := fun a b => Cost.step ;; leb_c L b a;
     join_c := fun a b => Cost.step ;; meet_c a b;
     widen_c := fun a b => Cost.step ;; meet_c a b;
     narrow_c := fun a _ => Cost.step ;; Cost.ret a;
     bot := top_value T |}.
Theorem leb_dual {A} (L : lattice A) (T : top L) meet_c a b : leb (dual L T meet_c) a b = leb L b a.
Theorem dual_laws {A} (L : lattice A) (T : top L) meet_c :
  lattice_laws L -> meet_laws L (fun a b => Cost.value (meet_c a b)) -> lattice_laws (dual L T meet_c).
Proof. intros H M; constructor.
  - intro a; apply (leb_refl H).
  - intros a b c Hab Hbc; eapply (leb_trans H); eassumption.
  - apply (top_greatest T).
  - apply (meet_lower_l M). …
Theorem dual_cost {A} (L : lattice A) (T : top L) meet_c inv k :
  cost_bounded_on L inv k -> (forall a b, inv a -> inv b -> (Cost.ticks (meet_c a b) <= k)%N) ->
  cost_bounded_on (dual L T meet_c) inv (k + 1)%N.
```

After (compiled; the four `T_` definitions are what `TimeFun` is specified to generate, written by hand for the check):

```coq
Module DualCode (L : BLATTICE_OPS) <: BLATTICE_OPS.
  Definition t := L.t.
  Definition leb (a b : t) : bool := L.leb b a.
  Definition bot : t := L.top.
  Definition is_bot (a : t) : bool := L.leb L.top a.
  Definition join (a b : t) : t := L.meet a b.
  Definition top : t := L.bot.
  Definition meet (a b : t) : t := L.join a b.
End DualCode.

Module Dual (L : BLATTICE) <: BLATTICE.
  Include DualCode L.
  Lemma leb_refl : forall a, leb a a = true.
  Proof. intro a; apply L.leb_refl. Qed.
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof. unfold leb; intros a b c Hab Hbc; eapply L.leb_trans; eassumption. Qed.
  Lemma bot_least : forall a, leb bot a = true.
  Proof. intro a; apply L.top_greatest. Qed.
  Lemma is_bot_bot : is_bot bot = true.
  Proof. apply L.leb_refl. Qed.
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof. unfold is_bot, leb; intros a b H; eapply L.leb_trans; [apply L.top_greatest|exact H]. Qed.
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof. intros a b; apply L.meet_lb_l. Qed.
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof. intros a b; apply L.meet_lb_r. Qed.
  Lemma top_greatest : forall a, leb a top = true.
  Proof. intro a; apply L.bot_least. Qed.
  Lemma meet_lb_l : forall a b, leb (meet a b) a = true.
  Proof. intros a b; apply L.join_ub_l. Qed.
  Lemma meet_lb_r : forall a b, leb (meet a b) b = true.
  Proof. intros a b; apply L.join_ub_r. Qed.
End Dual.

Module DualT (L : BLATTICE_T) <: BLATTICE_T.
  Include Dual L.
  TimeFun leb. TimeFun is_bot. TimeFun join. TimeFun meet.
  (* generates: T_leb a b := 1 + L.T_leb b a;      T_is_bot a := 1 + L.T_leb L.top a;
                T_join a b := 1 + L.T_meet a b;    T_meet a b := 1 + L.T_join a b *)
  Definition size (a : t) : nat := L.size a + L.size L.top.
  Definition c_lat : nat := L.c_lat + 1.
  Lemma T_leb_le : forall a b, T_leb a b <= c_lat * (size a + size b + 1).
  Proof. intros a b; unfold T_leb, c_lat, size; pose proof (L.T_leb_le b a); nia. Qed.
  Lemma T_join_le : forall a b, T_join a b <= c_lat * (size a + size b + 1).
  Proof. intros a b; unfold T_join, c_lat, size; pose proof (L.T_meet_le a b); nia. Qed.
  Lemma T_is_bot_le : forall a, T_is_bot a <= c_lat * (size a + 1).
  Proof. intros a; unfold T_is_bot, c_lat, size; pose proof (L.T_leb_le L.top a); nia. Qed.
  Lemma T_meet_le : forall a b, T_meet a b <= c_lat * (size a + size b + 1).
  Proof. intros a b; unfold T_meet, c_lat, size; pose proof (L.T_join_le a b); nia. Qed.
End DualT.
```

What happened to each landed item:
- The record literal became seven definitions; `meet_c` and `T` became fields of the parameter.
- `leb_dual` and `join_dual` are gone: they hold by `reflexivity` and nobody rewrites with them.
- `dual_laws` became the ten lemmas; its script survives line for line.
- `dual_lub`, `dual_top` and `dual_height` become a small `DualHeight (L) (H : HEIGHT L) (J : LUB L)` functor with the same script.
- `dual_cost` is deleted and replaced by four one-line contracts.
- The result is also more general: the dual of a `BLATTICE` is a `BLATTICE`, so `Dual (Dual L)` type-checks.

---

## 8. Sizes and effort

**Target lines per core package** (implementation; `*Sig.v` in brackets):

| Package | Today | Target | Of which proofs to write in sessions |
|---|---|---|---|
| Base | 14,986 | 4,900 [900] | about 2,400 |
| Lattice | 6,822 | 3,000 [450] | about 400 (the rest is carried) |
| Graph | 41,330 | 13,000 [700] | about 4,400 |
| Fixpoint | 14,293 | 3,300 [650] | about 2,600 |
| Program | 5,920 | 2,350 [450] | about 300 |
| Framework | 18,872 | 6,900 [700] | about 3,500 (about 900 now, the rest in batch 3) |
| Total | 103,820 (with Cost) | 33,450 [3,850] | about 13,600 |

**Groundwork, before batch 1** (our agents). "Parallel" means the task compiles against signatures and lower-level code modules only.

| Id | Task | Who | Size | Parallel? |
|---|---|---|---|---|
| G0 | Argent usable: `TimeFun` on functor bodies and included definitions, `CostStd` for `Pos`, `N`, `Z` and lists, `loop`, `loop_fuel` | Argent's owner | prerequisite | no; everything timed waits for it. Code and plain towers do not |
| G1 | Core `*Sig.v` files, transcribed from §3 and compiled; then checksum | Opus, 2 agents | 3,850 lines, about 6 h | first; blocks G3 to G6 and both other areas' `Sig` files |
| G2 | Top-level data and helpers, written in full: `Base/Code.v`, `Base/Loop.v`, `Fixpoint/Query.v`, `Graph/Data.v`, `Graph/Spec.v`, the action and row types | Opus | 900 lines, 2 h | after G1's `KEY` and `TRIE` |
| G3 | Code towers by the recipe, steps 1 to 5, one agent per package | Sonnet, with Haiku for steps 1 and 2 | 12,000 lines out | yes, six in parallel |
| G4 | Plain towers, step 6, with `CONVERT` tags | Sonnet | 15,000 lines out | yes, per package, after its G3 |
| G5 | Timed towers, step 7, with the `PLAN` chains drafted from the potentials in the deleted cost files | Opus drafts, Sonnet transcribes | 4,000 lines of statements | yes, per component |
| G6 | New code with no landed source: `UnionFind` (§6), `Schedule`, `Indexed`, `Narrow`, `Certified`, `Policy`, the `Ifds` and `Ide` systems | Opus | 2,000 lines | yes |
| G7 | Deletions and the archive manifest | Haiku | 55,000 lines removed | after G3 confirms nothing imports them |
| G8 | Build plumbing: dune files, the `Sig` checksum, `just admits` with the four tags, `just audit`, the lints of R13 | Sonnet | 1 h | yes |
| G9 | Tests: old fixtures as `vm_compute` expectations; one usage example per package; `examples/Toy.v` from §5 | Sonnet | 1,500 lines | per package, after its G3 |

G3 for Graph is the long pole (the dominator family needs its file-level pass first). Everything else in G3 to G6 is two to three agent-hours per package.

**Session work packages for the core.** A session owns its paths, their tests, and never a `*Sig.v`.

| WP | Batch | Owns | Closes | Lines |
|---|---|---|---|---|
| **K1 Foundations** | **1** | `Base/{Code,Trie,Map,Set,Heap,Loop,UnionFind,Intern}.v`; `Fixpoint/{Check,Certified,Policy,Narrow,Worklist}.v`; `Framework/{Dense,Interp}.v` | In this order: (1) `TRIE_PLAN`, `MAP_TIME`, `SET_TIME`; (2) `T_loopN_le`, `loopN_done`; (3) `CHECK_TIME`, `Certified`; (4) `Dense` and `Interp`: `covers`, `SYSTEM_TIME`; (5) `POLICY_LAWS` (`head_strict_steps`, `head_updates_le`), `Narrow`; (6) `PQ_TIME`; (7) `WORKLIST_PLAN` W1–W4, `T_run_height_le`, `run_enough`; (8) `Code` (`glue_inj`, bits, time); (9) `UNION_FIND_PLAN`; (10) `Intern` | about 5,000 |
| **K2 Graph and order** | **2** | `Graph/{Digraph,Search,Scc,Wto,Dom,Frontier}.v`; `Fixpoint/Schedule.v`; `Framework/GenKill.v`; and `Fixpoint/Worklist.v` again | `SEARCH_PLAN` (potential `2·unvisited + pending`); `SCC_TIME`; `WTO`: `check_sound`, `check_cuts`, `ranks_forward`, times; `DOM`: `check_sound` repairs, `dominates_b_spec`, checker and numbering times; `FRONTIER`: `df_spec`, time; `SCHEDULE`; `WORKLIST_PLAN` W5–W7 (`T_run_le`); `GenKill` covers | about 5,200 |
| **K3 The rest** | 3 | `Graph/{Loops}.v`, `Dom` producer time; `Framework/{Sparse,Summary,Ifds,Ide}.v`; `Fixpoint/Indexed.v`; `Lattice/*` time layers that groundwork left | `SOLVER_LEAST` for `Worklist`; `GenKill` exactness; `Sparse`, `Summary`, `Ifds`, `Ide` covers and time; `LOOPS`; `T_build` for dominators; `INDEXED` | about 3,400 |

- **Inside K1, the cut line is after item 7.** Items 1 to 7 give the user story with its soundness theorem and a cost theorem. Items 8 to 10 are consumed elsewhere only as `Parameter`s, so they can slip into K2 without blocking anyone.
- Items 3 and 4 are the only core *proofs* that the end-to-end soundness theorem needs, and both are short (I proved their miniature versions).

**Ordering by how much depends on each core package.**
1. `Base` (every package).
2. `Lattice` signatures (domains, fixpoint, frameworks); the combinators are small and mostly carried.
3. `Fixpoint` (frameworks, `Incremental`, `Widening`, `Alarms` through the frameworks).
4. `Framework` `Dense` and `Interp` (the end-to-end theorem, `Alarms`).
5. `Graph` (`Ssa` needs dominators and frontiers; `Schedule` needs the WTO).
6. `Program` presentations beyond `CFG` and `SEMANTICS`; `Sparse`, `Summary`, `Ifds`, `Ide`.

**The six sessions, shared by the three areas.** The three documents together ask for about thirteen sessions of work. My recommendation is two per area:

| Batch | Core | Domains | Engines |
|---|---|---|---|
| 1 | **K1** | **D-A**: their S2 without `Policy` and `Narrow` (now in K1), plus `States/Env` and `Alarms/Alarms` from S3 (about 4,900 lines) | **WP1** engine kernel |
| 2 | **K2** | **D-B**: their S1, the value core (harness, `Const`, `Sign`, `Congruence`, `Product`, `Reduced`, `BitsLang`) | **WP3** `Run` and the `Egraph` front end; without Datalog it has room for `Extract` |
| 3 (deferred) | K3 | S3's `Partition`, `Disjunction`, `RelEnv`, `BitsChecks`; S4 bit-level domains; S5 zones and octagons; S6 Karr and polyhedra | WP2 SSA; WP4 `Incremental` and `Clients` |

- **Must be in batch 1 for anything to work end to end:** K1 (through item 7) and D-A. Together they are the whole user story: a certified interval analysis with widening control, alarms, a soundness theorem and a cost theorem.
- WP1 is independent of both and starts the second end-to-end line, the relational engine.
- **Deferred to a third batch, in the order I would bring them back:**
  1. WP2 (SSA): a required feature, and it unlocks `Sparse`.
  2. S5 (zones and octagons).
  3. WP4 (`Incremental`).
  4. S4.
  5. S6.
  6. K3.
- **If the owner wants SSA inside the six sessions**, swap it for D-B. The driver's integer language needs only `ZLang` and `Interval`, so D-B is not on the end-to-end path. I recommend against the swap only because D-B's harness is the foundation every later value domain is written on.
- Every deferred component still exists after groundwork as a compiling skeleton with stated theorems. Deferral changes which admits are closed, not which features are present.

---

## 9. Risks, and the patterns tried

**Validated in the Rocq 9.3 REPL**

| # | Pattern | Result |
|---|---|---|
| V1 | Parameterised layers joined by `<+`: `MAP_T (K : KEY_T) := MAP K <+ MAP_TIME K`, with `MAP_TIME (K : KEY_T) (Import M : MAP K)` | accepted; `Print Module Type` shows the flattened signature |
| V2 | Thin transparent functor ascribed with `<:`; two applications give convertible types and operations, and the type equals the concrete core | `eq_refl` accepted three times |
| V3 | Code functor over `_OPS`, certified functor with `Include FooCode K`, ascribed to `FOO_T <+ FOO_PLAN`; the two agree | `Check (eq_refl : @Mc.get = @M.get)` |
| V4 | An implementation whose lemma differs from the signature is rejected at application or ascription | "Signature components for field get_set_same do not match" |
| V5 | A definition-only layer (`KEY_SPEC`) used through `<+` in a signature and `Include KEY_SPEC.` in a module and in a functor; a different body is rejected | "the body of definitions differs" |
| V6 | A layer with two and with three self-applied parameters in a `<+` chain (`KEY_LAWS`, `HAS_MEET_TIME`) | accepted |
| V7 | The whole stack in miniature: inner module passed to `Include DenseCode … Flow`; `Include SYSTEM_SPEC N D.`; soundness functor including the system functor; solver and certification functors; `vm_compute`; theorem instantiation by plain application; `Print Assumptions`; extraction of the code tower | all accepted; see §5 |
| V8 | `N` fuel on `Acc` with `Acc_intro_generator 32 N.lt_wf_0` | 200,000 iterations, fuel 10¹², 0.13 s; extraction drops the proof |
| V9 | (Argent shell, Elpi) after `Include FoldCode L` in a functor, an included constant and its sibling are located in the *including* module, and a parameter's field at the parameter's path; after `Include` of a plain module, the included constant equals the original as a global reference | the sibling rule finds `Fold.T_twice` and `L.T_join`. Hence R2 and R3 |
| V10 | The final shapes: `KEY` with `eqb` and `bits`; nested `term` with `eval_term`; `LANG`; `LATTICE` with `is_bot`; `WIDENING`; `VALUE_DOMAIN`; `STATE_DOMAIN (X) (L) (V)`; `SYSTEM` with inline keys; the `LOCAL` extension; the key adapter | all type-check |
| V11 | The union-find skeleton (§6) and the converted `Dual` (§7) | compile; tests compute |

**Failed, or behaving differently from what one might assume**

| # | Pattern | Outcome | Consequence |
|---|---|---|---|
| F1 | A module type applied to a functor application, `LOOP (LoopOps Down)` (earlier session) | syntax error | name every application (R8) |
| F2 | Extraction of a functor whose parameter signature has `T_` fields | every field is extracted, in the signature and in every instance, `c_` constants included | the separate code tower (R2) |
| F3 | `Include` of a module type that has a `Parameter` | the parameter becomes an axiom of the including module, silently | lint: only `_SPEC` types may be included (R13) |
| F4 | An inductive declared inside a functor (earlier session) | two applications give incompatible types | data at top level (R6) |
| F5 | A separate time module as a second functor argument | compiles, but the time function is not at the operation's path, so `TimeFun`'s sibling rule cannot find it | bundled `_T` arguments (R3); the domains' headers change |
| F6 | `Fail Module X (…) <: T.` to test rejection | "has not failed": an interactive module fails only at `End` | test rejection by applying a checking functor, as in V4 |

**Risks**

1. **`TimeFun` has never run on this code.** The design assumes it accepts included definitions (V9 covers the lookup, not the derivation), partial applications and lambdas passed as arguments, and convoy-free code. If it cannot handle included definitions, the fallback is to put the `TimeFun` lines in the code module and accept `T_` dead code in the OCaml. Nothing else changes.
2. **Nested `term`.** The domains' evaluators recurse through `list`, which needs Argent's nested or mutual `fix`. Core is not exposed: `Interp` folds over a list of actions and never recurses on a term.
3. **The round argument for widening at heads (`W5`)** is new and unchecked. The fallback contract is described in §3.5.
4. **`BUDGET`.** The timed worklist contract needs an invariant on values with a size bound and a rank bound. For intervals over `Z` the size bound depends on the program's constants and thresholds; the domains architect must supply the instance, and it may be the hardest part of the end-to-end cost theorem.
5. **The dominator family** (about 12,000 non-cost lines in 60 files) was sized from its file list. Its conversion needs a reading pass first, and K2 may have to leave the producer's time bound to K3.
6. **K1 is full.** Five thousand lines is the measured ceiling for one session. The order inside K1 is chosen so that what slips is not on the end-to-end path.
7. **Fuel in bounds.** With `N` fuel every solver bound carries an additive `N.size_nat fuel`. That is honest and negligible, but it must appear in the published statements, and the engines' `T_run ≤ c·(work + 1)` becomes `c·(work + N.size_nat fuel + 1)`.
8. **Plans drafted by agents can be false.** R11 keeps a false plan lemma from blocking a contract, but each defect costs session time. The union-find and worklist plans above use named constants throughout so that no constant can be wrong.
9. **Two towers to wire.** A client who wants clean OCaml writes its wiring twice (with and without the `Code` suffix). The link is `eq_refl`, and the engines' `Exec/Instances.v` does it once for the library's own roots.
10. **Deleting `ProgramSkeleton*` and the tabulation engine** removes about 7,600 lines of proved code on my reading of their headers and consumers. Both stay in the archive; the first should be confirmed with the engines architect.

### Critical Files for Implementation
- /home/nandhagk/Projects/galois-integrate/theories/Fixpoint/FixpointWorklistCost.v
- /home/nandhagk/Projects/galois-integrate/theories/Fixpoint/FixpointCheck.v
- /home/nandhagk/Projects/galois-integrate/theories/Base/BaseTrieMerge.v
- /home/nandhagk/Projects/galois-integrate/theories/Graph/GraphCheckWto.v
- /home/nandhagk/Projects/argent/docs/design.md
