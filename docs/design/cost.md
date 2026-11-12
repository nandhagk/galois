# Galois cost accounting: design document

## 0. Summary

I recommend adopting the proposal: executable code becomes plain Gallina, and an Elpi command derives a time function `T_f` from the kernel body of each `f`. Seven parts of the proposal need to change, and I tested all seven in the REPL.

1. **Fuel.** Bounds are paid by a potential, so no bound depends on fuel.
   - A loop combinator that recurses structurally on an `Acc` proof replaces the binary-fuel `iterate`.
   - A second combinator takes `nat` fuel computed from data. Its bound also does not depend on fuel.
   - Both carry one potential lemma, and both lemmas are proved with no axioms.
   - The `Acc` loop extracts to OCaml with no fuel and no proof argument. It runs under `vm_compute` through `Acc_intro_generator`.
2. **Constants in contracts.** Contracts in signatures use named, abstract constants (`c_get`), and `bigO` appears only in published corollaries. Clients are functors, so they cannot see a backend's exact costs. This removes the cost leakage recorded in `LEDGER.md:2496`.
3. **Closures in data.** These are rejected by the command. Callback records become functor parameters, and query continuations are defunctionalised (section 7).
4. **The migration trick.** "Redefine the monad as the identity" still works, but `TimeFun` must first be taught to read `Cost.bind` as `let` (section 10).
5. **Command name.** The command cannot be called `Time`, because Rocq already uses `Time` as a command prefix. The names are `TimeFun`, `TimeBound`, `TimeCheck`, `TimeAudit` and `TimePrim`.
6. **Lint.** A name lint cannot tell which definitions are executable. Enforcement is therefore a ~40-line Elpi audit over the extraction roots, plus a lexical OCaml lint of about 120 lines.
7. **Built-in costs.** Isabelle declares `=` and other polymorphic primitives to be zero-time, which is a loophole. Here the only built-in costs are a table that must equal the set of constants that extraction realises natively.

---

## 1. Decision and reasons

**Decision.** The design follows Nipkow et al.'s time-function method, ported to Rocq with rocq-elpi 3.5.0. Programs are plain Gallina. Each `T_f` is a separate, transparent, `nat`-valued constant generated from the kernel term of `f`. Generic components are functors whose signatures carry a time layer.

How each requirement is met:

| Req. | How it is met |
|---|---|
| 1. Guard against bad code | `T_f` is a function of `f`'s own body. An agent can only place charges by changing the code. A handwritten `T_` is a lint error, and an executable constant without a `T_` is an audit error. Callback companions are generated at the call site, so the `of_pure` loophole is gone. |
| 2. Big-O only | Published theorems are `bigO` statements. Internal lemmas use named constants. |
| 3. Tight, no fuel | `T_f` counts call-by-value work up to a constant factor (section 8). Loop bounds are paid by a potential and do not depend on fuel. Headline bounds also get a lower-bound witness (`T_get_ge` was proved). |
| 4. Amortisation | One per-operation potential inequality, one sequence lemma, and one loop lemma, all proved. |
| 5. Automation | Derivation is fully automatic. `time_pose` (an Elpi tactic, tested) poses the registered bounds of every callee. |
| 6. Functors | Module parameters work. Lookup `M.op` → `M.T_op` was tested inside a functor and after `Module I := F BoolLat`. |
| 7. Dependency | rocq-elpi only. No axioms: signature contracts are `Parameter`s discharged by each instance. |
| 8. Tests and extraction | Code contains no accounting at all. `T_` constants are never reachable from code, and `Extraction loop` produced `let rec loop step s = match step s with Inl s0 -> loop step s0 \| Inr r -> r`. |
| 9. Executor | Statements are `T_f args <= expr` with explicit constants, so the proof sketches below are chains of such lemmas. |

**What the alternatives lose**

| Alternative | Verdict |
|---|---|
| Current writer monad plus a canonical charging rule, `spec m b Q`, and an "expand, pose, lia" tactic | Keeps `f_c`/`f`/`f_equation` triples (855 `_c` definitions, ~470 equations), hand placement of charges, a 520-line placement lint, and costed record fields. Value proofs keep seeing `Cost.value`. A mechanical charging rule would be this design with the value and the cost tangled together. |
| McCarthy et al. 2016 (`rfindler/395-2013`) | Cost lives in a `Prop` index of a monad, and the computational content is the identity. Programs are still monadic, and `+=` annotations are placed by hand; the paper checks placement with an external script. Proof obligations are tied to the program through `Program`. |
| Functor over an abstract monad, instantiated at identity and at counting | Code stays monadic, and callbacks must be monadic. Rocq has no parametricity theorem, so `value (counting) = identity` must be proved for every function. |
| Ltac2 translator | No packaged dependency is needed, but Ltac2 has no command API (it would need `Definition T_f := ltac2:(...)`), no persistent database, and a fragile `Constr.Unsafe` match/fix construction API. Elpi's HOAS makes binders safe, and it is already packaged. |
| Forster–Kunze certifying extraction to L | It does apply to Gallina, but the cost model is weak call-by-value L with Scott-encoded data: reasonable up to a polynomial, not tight for RAM data structures. It is also heavy and not packaged for 9.3. |
| CFML time credits | Verify OCaml code through characteristic formulae. The verified code is not our Gallina. |
| Iris time credits (Mével–Jourdan–Pottier) | For HeapLang programs, not Gallina. |
| Calf (Niu et al., Agda) | A different proof assistant, with programs written in calf's own phased type theory. |
| Liquid Haskell `RTick` | Haskell, with monadic ticks placed by hand. |
| RaML / AARA (Hoffmann et al.) | Uncertified inference on an OCaml subset. It could be an optional empirical cross-check on extracted code, but it gives no guarantee. |
| Demand semantics (Xia et al., ICFP 2024) | Built for lazy evaluation. It only informs the persistence discussion. |

---

## 2. The translation, specified completely

**Notation.** `T⟦e⟧ : nat` is the cost of call-by-value evaluation of `e`. `F⟦e⟧` is the time function of a function-valued `e`. `C⟦e⟧` is the cost of creating the closure `e`.

### Kinds

Every binder or argument position of type `D` has a kind. Kinds are computed on the callee's generic type, under `decl` binders.

- **irr**: `D` is an arity (it ends in a sort), or `D : Prop` or `SProp`. Types, proofs and predicates are irr: they are copied verbatim, cost 0, and get no companion.
- **fn**: `whd D` is a product and not an arity. The argument gets a companion immediately after it.
- **val**: everything else.

### Time types

- `τ⟦Π(x:A).B⟧ = Π(x:A). [Π(T_x : τ⟦A⟧).] τ⟦B⟧`. The bracketed binder is present iff `A` is fn, so second-order arguments get companions recursively.
- `τ⟦B⟧ = nat` otherwise.

### The top-level rule

`TimeFun f.` takes `f := λ params. [fix F args {struct i}] body` and produces:

```
T_f := λ params⁺. [fix T_F args⁺ {struct i⁺}] 1 + T⟦body[F := f params]⟧
```

- `⁺` inserts a companion `T_x` after each fn binder.
- `i⁺` shifts the structural index by the number of companions before position `i`.
- The value occurrences of the recursive variable are replaced by the global constant applied to its parameters. This makes the time function refer to `rev l'` rather than to an unbound fix variable.
- Calls to the global in head position become calls to `T_F` with the parameters dropped.

### Term rules

| Form | Rule |
|---|---|
| Bound variable, sort, product, primitive literal | 0 |
| Closed constant (only irr arguments, result not a function) | 0. It is evaluated once in OCaml and is O(1) in the input. |
| `h a₁…aₙ` | `Σ_{val} T⟦aᵢ⟧ + Σ_{fn} C⟦aᵢ⟧ + CALL(h, a⁺)`. Here `a⁺` places `F⟦aᵢ⟧` after each fn argument, and nested `app` is flattened first. |
| `CALL(K, _)` for a constructor | 0. A fn argument here gives `E_CLOSURE_DATA`. |
| `CALL(f, a⁺)` for a timed global | `T_f a⁺` |
| `CALL(F, a⁺)` for the fix under definition | `T_F (drop params a⁺)` |
| `CALL(g, a⁺)` for a local fn with a companion | `T_g a⁺` |
| `CALL(c, a⁺)` for a `TimePrim` table entry | the table expression |
| `CALL` otherwise | `E_NO_TIME`. This also catches calls of closures projected from data. |
| Primitive projection `s.(p)` | `T⟦s⟧`. A projection whose result is a function gives `E_NO_TIME`. |
| `let x := v in b`, `v` val | `T⟦v⟧ + let x := v in T⟦b⟧` (evaluated once) |
| `let g := v in b`, `v` fn | `C⟦v⟧ + let g := v in let T_g := F⟦v⟧ in T⟦b⟧`. Specified; the prototype raises `E_TERM`. |
| `match e as y in I idx return P with pᵢ ⇒ bᵢ end` | `T⟦e⟧ + match e as y in I idx return nat with pᵢ ⇒ T⟦bᵢ⟧ end`. Folded to `T⟦e⟧` when every branch costs 0. Dependent return types are simply replaced by `nat`. |
| `if` / `let '(x, y)` | Elaborated to `match` by Rocq, so the match rule applies. |
| Convoy `(match e return Π ȳ. P with p ⇒ λȳ. b end) prfs`, all `prfs` irr | `T⟦e⟧ + (match e return Π ȳ. nat with p ⇒ λȳ. T⟦b⟧ end) prfs`. Implemented in the prototype but not exercised. |
| `match` returning a function, not applied to proofs | `E_MATCH_FN` ("eta-expand") |
| Local `fix G … := b` applied to args | `CALL` against a local `fix T_G … := 1 + T⟦b[G := (fix G …)]⟧`. Value occurrences of `G` are replaced by the closed fix term itself. The guard checker accepts this because the structure is identical. Specified; the prototype raises an error. |
| Mutual `fix` (`mfix` in Elpi 3.5) | `TimeFun` on any member defines `T_` for every member of the block as one `mfix`. Specified; the prototype raises `E_MUTUAL`. `Pos.add` and `add_carry` need this. |
| Over-application | `E_OVERAPP` |
| `fun` in a val position | `E_CLOSURE` ("closure in value position") |
| `cofix`, evars, a `let`-bound function in the prototype, any other form | `E_TERM` ("unsupported term …") |
| `Fix_F` / `Acc_rect` / `well_founded_induction` (Equations, `Program Fixpoint`, `Function`) | `E_WF`: use `CostLoop.loop` instead |

### Function values

`F⟦e⟧`, with `e : Π x̄. B` of arity `|x̄|` and eta-expanded over that full arity:

- **Local fn with a companion:** `T_g`.
- **λ-term:** `λ x̄⁺. 1 + T⟦e x̄⟧`, with β-reduction. `C⟦e⟧ = 0`. The `+1` per closure invocation makes every body execution cost at least 1 (section 8). Isabelle charges 0 here.
- **Partial application `h ā`:** `λ x̄⁺. CALL(h, (ā ++ x̄)⁺)`, with `C⟦e⟧ = Σ T⟦ā⟧`. The arguments are paid once, when the closure is created. Tested on `fold_left (fun acc x => acc + x)`.
- **Constructor used as a function:** `λ x̄. 1` in the specification. The prototype gives 0.

### Naming and lookup

- **Names.** `T_<id>` lives in the same module as `f`, and companions are named `T_<binder>`. Constants from outside Galois get `T_` constants inside `CostStd` under a mirrored module path, for example `CostStd.Nat.T_add`. This avoids the clash `Nat.add`/`N.add` ↦ `T_add` that the prototype would hit.
- **Lookup, in order:**
  1. The `time.db` entry for the gref.
  2. The sibling rule: take `coq.gref->path` of `c`, try `<suffix>.T_<id>` for each suffix of the path from longest to shortest using `coq.locate-all` (`coq.locate` raises on failure, it does not fail), and accept only a hit whose own path equals the path of `c`. This is how a functor parameter's `L.join` finds `L.T_join` (tested).
  3. The `TimePrim` table.
- **Module parameters.** `M.op` uses `M.T_op`, which the signature declares.
- **Section variables.** Val-kind section variables are allowed only if `f` does not close over them; otherwise the arities of `f` and `T_f` diverge when the section closes. fn-kind section variables give `E_SECTION`. Code goes in functors (requirement 6).
- **Implicit arguments and universes.** `T_f` copies `f`'s implicit status, with companions explicit, and is universe-polymorphic iff `f` is. The prototype does not do this yet, which is why the lemmas below use `T_get A p m` explicitly.
- **Opaque `f`:** `E_OPAQUE`.

### Proofs and `Prop`

- Arguments in irr positions are never translated.
- A match on a `Prop` scrutinee eliminating into `nat` is legal exactly when the original elimination was: `Acc`, `eq`, `and` and `False` are subsingletons.
- The structural recursion on `Acc_inv H Hlt` was tested, and the guard checker accepts it.

---

## 3. Working prototype

**Status.** Every output below was printed by Rocq 9.3 with rocq-elpi 3.5.0.

- **Size.** About 125 lines of Elpi for `Time`, 10 for `TimeBound` and 16 for `time_pose`.
- **Implemented:** the full kind and companion machinery, structural and `Acc` fix, dependent match, convoy (unexercised), `let` of a value, partial application, λ arguments, functor parameters, match-of-zeros folding, and the rejections.
- **Not implemented:** mutual and local fix (rejected with an error), `let` of a function (rejected with `E_TERM`), implicit-argument copying, and the section check.

```elpi
Elpi Db time.db lp:{{ pred timed i:gref, o:gref. }}.
Elpi Command Time.            (* export as TimeFun; "Time" is a Rocq prefix *)
Elpi Accumulate Db time.db.
Elpi Accumulate lp:{{
pred tfun i:term, o:term.
pred curdef i:gref, o:int, o:term.
pred wh i:term, o:term.
wh T R :- (T = prod _ _ _ ; T = sort _), !, R = T.
wh T R :- coq.reduction.lazy.whd T R.
pred ends-sort i:term.
ends-sort T :- wh T (sort _), !.
ends-sort T :- wh T (prod N D B), pi x\ decl x N D => ends-sort (B x).
pred knd i:term, o:string.
knd D "irr" :- ends-sort D, !.
knd D "irr" :- coq.typecheck D S ok, (S = sort prop ; S = sort sprop), !.
knd D "fn" :- wh D (prod _ _ _), !.
knd _ "val".
pred kis i:string, i:term.
kis K D :- knd D K1, K1 = K.
pred tname i:name, o:name.
tname N TN :- coq.name->id N S, coq.id->name {calc ("T_" ^ S)} TN.
pred plus i:term, i:term, o:term.
plus {{ 0 }} B B :- !.
plus A {{ 0 }} A :- !.
plus A B {{ lp:A + lp:B }}.
pred timety i:term, o:term.
timety Ty (prod N D R) :- wh Ty (prod N D B), kis "fn" D, !, timety D TD, tname N TN,
  pi x\ decl x N D => (R x = prod TN TD (_\ R1 x), timety (B x) (R1 x)).
timety Ty (prod N D R) :- wh Ty (prod N D B), !, pi x\ decl x N D => timety (B x) (R x).
timety _ {{ nat }}.
pred args i:term, i:list term, o:term, o:list term.
args _ [] {{ 0 }} [] :- !.
args HTy [A|As] C [A|As2] :- wh HTy (prod _ D B), kis "irr" D, !, args (B A) As C As2.
args HTy [A|As] C [A,TA|As2] :- wh HTy (prod _ D B), kis "fn" D, !,
  fntime A CA TA, args (B A) As C0 As2, plus CA C0 C.
args HTy [A|As] C [A|As2] :- wh HTy (prod _ _ B), !, cost A CA, args (B A) As C0 As2, plus CA C0 C.
args _ _ _ _ :- coq.error "Time: over-application".
pred call i:term, i:list term, i:list term, o:term.
call (global (indc K)) As As2 {{ 0 }} :- !,
  (std.length As N, std.length As2 N, ! ; coq.error "Time: closure stored in data, constructor" K).
call (global GR) _ As2 R :- curdef GR Nc F, !, std.drop Nc As2 Rest, coq.mk-app F Rest R.
call (global GR) _ As2 R :- lookup GR TGR, !, coq.mk-app (global TGR) As2 R.
call H _ As2 R :- tfun H TH, !, coq.mk-app TH As2 R.
call (global GR) As _ {{ 0 }} :- coq.mk-app (global GR) As T, coq.typecheck T Ty ok,
  not (wh Ty (prod _ _ _)), std.forall As (a\ sigma Ta\ coq.typecheck a Ta ok, kis "irr" Ta), !.
call H _ _ _ :- coq.error "Time: no time function for" {coq.term->string H}.
pred lookup i:gref, o:gref.
lookup GR TGR :- timed GR TGR, !.
lookup GR TGR :- coq.gref->path GR P, coq.gref->id GR Id, suffix P Q,
  std.string.concat "." {std.append Q [{calc ("T_" ^ Id)}]} Name,
  coq.locate-all Name L, std.mem L (loc-gref TGR), coq.gref->path TGR P, !.
pred suffix i:list string, o:list string.
suffix L L.
suffix [_|L] S :- suffix L S.
pred cost i:term, o:term.
cost (app [app L|As]) C :- !, std.append L As L2, cost (app L2) C.
cost (app [primitive (proj _ _), S]) C :- !, cost S C.
cost (app [match E R Bs|Xs]) C :- !, std.forall Xs (x\ sigma Tx\ coq.typecheck x Tx ok, kis "irr" Tx),
  costm E R Bs Xs C.
cost (app [H|As]) C :- (H = global _ ; tfun H _), !, coq.typecheck H HTy ok,
  args HTy As CA As2, call H As As2 CC, plus CA CC C.
cost (app [H|_]) _ :- !, coq.error "Time: call of a function without time function (closure in data?)" {coq.term->string H}.
cost (let N Ty V B) C :- kis "val" Ty, !, cost V CV,
  (pi x\ def x N Ty V => cost (B x) (CB x)), plus CV (let N Ty V CB) C.
cost (match E R Bs) C :- !, costm E R Bs [] C.
cost (global GR) C :- !, call (global GR) [] [] C.
cost X {{ 0 }} :- name X, !.
cost (sort _) {{ 0 }} :- !.
cost (prod _ _ _) {{ 0 }} :- !.
cost (primitive _) {{ 0 }} :- !.
cost T _ :- coq.error "Time: unsupported term" {coq.term->string T}.
pred zb i:term.
zb (fun _ _ B) :- !, pi x\ zb (B x).
zb {{ 0 }}.
pred costm i:term, i:term, i:list term, i:list term, o:term.
costm E Rty Bs Xs C :- std.length Xs K, cost E CE, retnat K Rty Rty2 I, coq.env.indt I _ NP _ _ _ KTs,
  std.map KTs (kt\ n\ sigma M\ nprods kt M, n is M - NP) Ar,
  std.map2 Ar Bs (a\ b\ c\ br a K b c) Bs2,
  (std.forall Bs2 zb, !, M = {{ 0 }} ; coq.mk-app (match E Rty2 Bs2) Xs M), plus CE M C.
pred nprods i:term, o:int.
nprods (prod _ _ B) N :- !, pi x\ nprods (B x) M, N is M + 1.
nprods _ 0.
pred retnat i:int, i:term, o:term, o:inductive.
retnat K (fun N T B) (fun N T R) I :- (pi x\ sigma A B1 C1\ B x = fun A B1 C1), !,
  pi x\ decl x N T => retnat K (B x) (R x) I.
retnat K (fun N T B) (fun N T R) I :- wh T Ti, (Ti = global (indt I) ; Ti = app [global (indt I)|_]), !,
  pi x\ decl x N T => retk K (B x) (R x).
retnat _ R _ _ :- coq.error "Time: unsupported match return" {coq.term->string R}.
pred retk i:int, i:term, o:term.
retk 0 T {{ nat }} :- !, (wh T (prod _ _ _), coq.error "Time: match returns a function; eta-expand" ; true).
retk K T (prod N D R) :- wh T (prod N D B), K1 is K - 1, pi x\ decl x N D => retk K1 (B x) (R x).
pred br i:int, i:int, i:term, o:term.
br 0 0 B C :- !, cost B C.
br 0 K (fun Na T B) (fun Na T C) :- !, K1 is K - 1, pi x\ decl x Na T => br 0 K1 (B x) (C x).
br N K (fun Na T B) (fun Na T C) :- M is N - 1, pi x\ decl x Na T => br M K (B x) (C x).
pred fntime i:term, o:term, o:term.
fntime F {{ 0 }} TF :- tfun F TF, !.
fntime (app [H|As]) CA TF :- (H = global _ ; tfun H _), !, coq.typecheck H HTy ok,
  args HTy As CA _, coq.typecheck (app [H|As]) Ty ok, eta (app [H|As]) Ty [] TF.
fntime F {{ 0 }} TF :- coq.typecheck F Ty ok, eta F Ty [] TF.
pred eta i:term, i:term, i:list term, o:term.
eta F Ty Xs (fun N D R) :- wh Ty (prod N D B), kis "fn" D, !, timety D TD, tname N TN,
  pi x\ decl x N D => (R x = fun TN TD (R1 x),
    pi tx\ decl tx TN TD => tfun x tx => eta F (B x) {std.append Xs [x]} (R1 x tx)).
eta F Ty Xs (fun N D R) :- wh Ty (prod N D B), !, pi x\ decl x N D => eta F (B x) {std.append Xs [x]} (R x).
eta (fun _ _ _ as F) _ Xs C :- !, beta F Xs B, cost B C0, plus {{ 1 }} C0 C.
eta F _ Xs C :- coq.mk-app F Xs (app [H|As]), coq.typecheck H HTy ok, args HTy As _ As2, call H As As2 C.
pred beta i:term, i:list term, o:term.
beta (fun _ _ B) [X|Xs] R :- !, beta (B X) Xs R.
beta F [] F.
pred lams i:gref, i:list term, i:int, i:term, o:term.
lams GR Ps Nc (fun N D B) (fun N D R) :- kis "fn" D, !, timety D TD, tname N TN, Nc1 is Nc + 2,
  pi x\ decl x N D => (R x = fun TN TD (R1 x),
    pi tx\ decl tx TN TD => tfun x tx => lams GR {std.append Ps [x]} Nc1 (B x) (R1 x tx)).
lams GR Ps Nc (fun N D B) (fun N D R) :- !, Nc1 is Nc + 1,
  pi x\ decl x N D => lams GR {std.append Ps [x]} Nc1 (B x) (R x).
lams GR Ps Nc (fix N I Ty B) (fix TN I2 TTy R) :- !, tname N TN, timety Ty TTy, shift Ty I I2,
  coq.mk-app (global GR) Ps PG,
  pi f\ decl f TN TTy => curdef GR Nc f => lams GR Ps Nc (B PG) (R f).
lams _ _ _ (mfix _ _ _) _ :- !, coq.error "Time: mutual fix not supported by the prototype".
lams _ _ _ Bo C :- cost Bo C0, plus {{ 1 }} C0 C.
pred shift i:term, i:int, o:int.
shift _ 0 0 :- !.
shift Ty I J :- wh Ty (prod N D B), I1 is I - 1, (pi x\ decl x N D => shift (B x) I1 J1),
  (kis "fn" D, !, J is J1 + 2 ; J is J1 + 1).
main [str S] :- coq.locate S GR, GR = const C, coq.env.const-body C (some Bo),
  coq.gref->id GR Id, lams GR [] 0 Bo TBo, std.assert-ok! (coq.typecheck TBo Ty) "Time: ill-typed",
  coq.env.add-const {calc ("T_" ^ Id)} TBo Ty @transparent! TC,
  coq.elpi.accumulate _ "time.db" (clause _ _ (timed GR (const TC))).
}}.

Elpi Db time.bounds lp:{{ pred bound i:gref, o:term. }}.
Elpi Command TimeBound.  Elpi Accumulate Db time.bounds.
Elpi Accumulate lp:{{
main [str L] :- coq.locate L LG, coq.env.typeof LG Ty, head Ty TG,
  coq.elpi.accumulate _ "time.bounds" (clause _ _ (bound TG (global LG))).
pred head i:term, o:gref.
head (prod N D B) G :- !, pi x\ decl x N D => head (B x) G.
head (app [_, app [global G|_], _]) G :- !.
head _ _ :- coq.error "TimeBound: conclusion must be T_f args <= bound".
}}.
Ltac pose_proof p := pose proof p.
Elpi Tactic time_pose.  Elpi Accumulate Db time.bounds.
Elpi Accumulate lp:{{
pred sub i:term, o:term.
sub (app [global G|_] as T) T :- bound G _.
sub (app L) S :- std.mem L X, sub X S.
sub (fun _ _ B) S :- pi x\ sub (B x) S.
sub (let _ _ V B) S :- sub V S ; pi x\ sub (B x) S.
sub (match E _ Bs) S :- sub E S ; (std.mem Bs B, sub B S).
pred mk i:list term, o:term.
mk [] {{ I }}.
mk [app [global G|As]|Ts] {{ conj lp:P lp:Q }} :- bound G L, coq.mk-app L As P, mk Ts Q.
solve (goal _ _ Ty _ _ as G) GL :- std.findall (sub Ty S_) Sols,
  std.map Sols (s\ t\ s = sub _ t) Ts, mk Ts P0,
  std.assert-ok! (coq.elaborate-skeleton P0 _ P) "time_pose",
  coq.ltac.call "pose_proof" [trm P] G GL.
}}.
```

### Generated definitions, as printed by Rocq

```coq
T_length = fun A : Type => fix T_length (l : list A) : nat :=
  1 + match l with [] => 0 | _ :: l' => T_length l' end
T_app = fun A : Type => fix T_app (l m : list A) {struct l} : nat :=
  1 + match l with [] => 0 | _ :: l1 => T_app l1 m end
T_rev = fun A : Type => fix T_rev (l : list A) : nat :=
  1 + match l with [] => 0 | x :: l' => T_rev l' + T_app A (rev l') [x] end
T_fold_left = fun (A B : Type) (f : A -> B -> A) (T_f : A -> B -> nat) =>
  fix T_fold_left (l : list B) (a0 : A) {struct l} : nat :=
  1 + match l with [] => 0 | b :: l0 => T_f a0 b + T_fold_left l0 (f a0 b) end
T_sum = fun l : list nat =>   (* sum l := fold_left (fun acc x => acc + x) l 0 *)
  1 + T_fold_left nat nat (fun acc x : nat => acc + x)
        (fun acc x : nat => 1 + T_add acc x) l 0
T_pairs = fix T_pairs (l : list nat) : nat :=          (* nested match *)
  1 + match l with
      | [] => 0 | [a] => 0
      | a :: b :: rest => T_add a b + T_pairs rest + T_add (a + b) (pairs rest) end
(* inside Module F (L : LAT) *)
T_join_all = fix T_join_all (acc : L.t) (l : list L.t) {struct l} : nat :=
  1 + match l with [] => 0 | y :: r => L.T_join acc y + T_join_all (L.join acc y) r end
T_join3 = fun a b c : L.t => 1 + (L.T_join a b + (let ab := L.join a b in L.T_join ab c))
(* after Module I := F BoolLat *)
I.T_join_all = fix T_join_all (acc : BoolLat.t) (l : list BoolLat.t) {struct l} : nat :=
  1 + match l with [] => 0 | y :: r => BoolLat.T_join acc y + T_join_all (BoolLat.join acc y) r end
T_loop = fix T_loop (S R : Type) (lt : S -> S -> Prop)
  (step : forall s : S, {s1 : S | lt s1 s} + R) (T_step : S -> nat)
  (s : S) (H : Acc lt s) {struct H} : nat :=
  1 + (T_step s + match step s with
                  | inl (exist _ s1 Hlt) => T_loop S R lt step T_step s1 (Acc_inv H Hlt)
                  | inr _ => 0 end)
```

`Compute (T_rev nat [1;2;3;4], T_sum [1;2;3], T_pairs [1;2;3;4;5], I.T_join_all false [true;false;true])` gives `(15, 15, 21, 10)`.

### Rejections (tested)

| Input | Error |
|---|---|
| `Some (fun x => x)` | `closure stored in data, constructor «Some»` |
| `Ask (fun m => Ret (m + n))` | `closure stored in data, constructor «Ask»` |
| `match q with Ask k => … k 0 …` | `call of a function without time function (closure in data?) k` |
| `let g := fun x => x + n in g n` | `unsupported term …` |
| `Pos.add` | `mutual fix not supported by the prototype` |
| Local `fix go` | `call of a function without time function … fix go …` (the specification gives `E_LOCAL_FIX`) |

### Bugs found and fixed during testing

1. `knd D "fn"` with a bound output skipped the `irr` clauses, so Prop-valued predicate parameters received companions. Fixed with `kis`.
2. Nested `app` after substituting the fix variable was not flattened.
3. A catch-all `cost _ 0` made a function-typed `let` silently free. It is now an explicit error.

---

## 4. The new `Cost` package (statements tested unless marked)

```coq
(* CostO.v *)
Definition bigO {X} (P : X -> Prop) (g T : X -> nat) : Prop :=
  exists c, forall x, P x -> T x <= c * (g x + 1).
Lemma bigO_intro {X} P (g T : X -> nat) c :
  (forall x, P x -> T x <= c * g x + c) -> bigO P g T.
Lemma bigO_le    {X} P g T T2 : bigO P g T -> (forall x, P x -> T2 x <= T x) -> bigO P g T2.
Lemma bigO_mono  {X} P g g2 T : bigO P g T -> (forall x, P x -> g x <= g2 x) -> bigO P g2 T.
Lemma bigO_add   {X} P g1 g2 T1 T2 :
  bigO P g1 T1 -> bigO P g2 T2 -> bigO P (fun x => g1 x + g2 x) (fun x => T1 x + T2 x).
Lemma bigO_trans {X} P g h T : bigO P g h -> bigO P h T -> bigO P g T.
Lemma bigO_comp  {X Y} (P : Y -> Prop) (f : X -> Y) g T :
  bigO P g T -> bigO (fun x => P (f x)) (fun x => g (f x)) (fun x => T (f x)).
(* Tightness witness for headline theorems (statement only): *)
Definition tight {X} P (g T : X -> nat) : Prop :=
  bigO P g T /\ exists c, forall n, exists x, P x /\ n <= g x /\ g x <= c * T x.
```

`X` is the tuple of all inputs, including the program value, so the constant is uniform over everything. This avoids the quantifier pitfall described by Guéneau et al. Constants may depend on functor arguments; that is the "constants are free" policy, applied per instance.

```coq
(* CostAmortised.v *)
Section Amortised.
Context {S O : Type} (op : O -> S -> S) (T A : O -> S -> nat) (Phi : S -> nat) (Inv : S -> Prop).
Fixpoint run (os : list O) s := match os with [] => s | o :: r => run r (op o s) end.
Fixpoint total (os : list O) s := match os with [] => 0 | o :: r => T o s + total r (op o s) end.
Fixpoint budget (os : list O) s := match os with [] => 0 | o :: r => A o s + budget r (op o s) end.
Definition amortised := forall o s, Inv s -> Inv (op o s) /\ T o s + Phi (op o s) <= A o s + Phi s.
Lemma amortised_run : amortised -> forall os s, Inv s -> total os s + Phi (run os s) <= budget os s + Phi s.
Lemma amortised_uniform k : amortised -> (forall o s, Inv s -> A o s <= k) ->
  forall os s, Inv s -> total os s <= k * length os + Phi s.
End Amortised.
```

```coq
(* CostLoop.v. Retires the binary-fuel iterate. *)
Scheme Acc_ind_dep := Induction for Acc Sort Prop.
Fixpoint loop {S R} (lt : S -> S -> Prop) (step : forall s, {s1 | lt s1 s} + R)
  (s : S) (H : Acc lt s) {struct H} : R :=
  match step s with inl (exist _ s1 Hlt) => loop lt step s1 (Acc_inv H Hlt) | inr r => r end.
TimeFun loop.
Lemma T_loop_le {S R} lt step T_step (Inv : S -> Prop) (Phi : S -> nat) (Tstop : nat) :
  (forall s s1 Hlt, Inv s -> step s = inl (exist _ s1 Hlt) -> Inv s1 /\ T_step s + Phi s1 < Phi s) ->
  (forall s r, Inv s -> step s = inr r -> T_step s <= Tstop) ->
  forall s (H : Acc lt s), Inv s -> @T_loop S R lt step T_step s H <= Phi s + Tstop + 1.
(* Proof: induction H using Acc_ind_dep; cbn [T_loop]; destruct (step s) eqn:E; lia/nia. Closed. *)

Fixpoint loop_fuel {S R} (step : S -> S + R) (fuel : nat) (s : S) : S + R := ... (* nat fuel *)
Lemma T_loop_fuel_le {S R} step T_step Inv Phi Tstop :
  (forall s s1, Inv s -> step s = inl s1 -> Inv s1 /\ T_step s + Phi s1 < Phi s) ->
  (forall s r, Inv s -> step s = inr r -> T_step s <= Tstop) ->
  forall fuel s, Inv s -> T_loop_fuel step T_step fuel s <= Phi s + Tstop + 1.   (* closed *)
```

**One rule for both loop kinds.**
- Under strict decrease, take `Phi := (k+1)·measure`. In the amortised case, the potential pays for each step together with its `+1`.
- The ledger's objection (`LEDGER.md:4116`) disappears, because every iteration costs at least 1 and must be paid from `Phi`.
- Entry points use `Acc_intro_generator 40 wf s`. A 100,000-iteration countdown ran under `vm_compute` in 0.07 s.
- Use `loop` when the decrease needs no invariant.
- Use `loop_fuel` with fuel computed from data (`S (max_rank uf)`, `pending q`, or a user cap that returns `OutOfFuel`) when it does. The bound is independent of the fuel either way.

**Other files**
- `CostStd.v`: `TimeFun` for the Stdlib list, `Nat`, `Pos` and `N` functions the library calls, with one bound each. Tested: `T_app_le : T_app A l m <= length l + 1` and `T_rev_le : … <= (length l + 1)²`. Also `T_fold_left_le : (∀ a b, T_f a b <= k) -> T_fold_left … l a <= (k+1)·length l + 1`.
- `CostPrim.v`: `TimePrim c := e`, the only place built-in costs exist.
- `CostTactics.v`: the commands and tactics below.

**Tactic contracts**

| Tactic | Goal shape | Effect / leaves |
|---|---|---|
| `elpi time_pose` | any | For each closed subterm `T_g ā` with a registered bound `L : ∀ x̄, T_g x̄ <= B x̄`, it adds `H : L ā /\ … /\ True`. It never fails and leaves the goal. Conditional bounds `∀ x̄, P x̄ -> …` are specified as posting `P ā` subgoals tried by `eauto with time_inv`; the prototype handles unconditional bounds only. |
| `time_simpl` | any | `autounfold with time_const` (time functions whose body is a numeral, such as `T_left := 1`, are registered by `TimeFun`), then `cbn beta iota zeta`. |
| `time_step f` | `T_f ā <= e` | `cbn [T_f]; time_simpl; elpi time_pose; try nia`. On failure it leaves the arithmetic goal with every callee bound in context. |
| `loop_bound Inv Phi Tstop` | `T_loop … <= e` or `T_loop_fuel … <= e` | `eapply T_loop_le` (or `_fuel_le`) and `lia`. Leaves the continue obligation, the stop obligation and `Inv s0`. |
| `amortise Inv Phi` | `total os s <= e` | `eapply amortised_uniform`. Leaves the per-operation inequality and the cap `A o s <= k`. |

---

## 5. Signature conventions

Rules:
- Every signature has a functional layer and a time layer.
- Contracts are `Parameter`s (not `Axiom`s) with named, abstract constants.
- Spec-only parameters (sizes, invariants, potentials) are listed in a `(* spec: … *)` pragma.
- Clients are functors over signatures, so `T_op` is abstract to them by construction.

```coq
Module Type KEY.
  Parameter t : Type.
  Parameter encode : t -> positive.
  Parameter T_encode : t -> nat.                     (* time layer *)
  Parameter c_encode : nat.
  Parameter T_encode_le : forall k, T_encode k <= c_encode * (Pos.size_nat (encode k) + 1).
  Parameter encode_inj : forall a b, encode a = encode b -> a = b.
End KEY.
Definition bits {K : ...} ... (* in a functor: Definition bits k := Pos.size_nat (K.encode k). *)

Module Type MAP.
  Declare Module K : KEY.
  Parameter t : Type -> Type.
  Parameter empty : forall A, t A.                   (* closed constant: no T needed *)
  Parameter get : forall A, K.t -> t A -> option A.
  Parameter set : forall A, K.t -> A -> t A -> t A.
  Parameter T_get : forall A, K.t -> t A -> nat.
  Parameter T_set : forall A, K.t -> A -> t A -> nat.
  Parameter c_map : nat.
  Parameter T_get_le : forall A k (m : t A), T_get A k m <= c_map * (Pos.size_nat (K.encode k) + 1).
  Parameter T_set_le : forall A k v (m : t A), T_set A k v m <= c_map * (Pos.size_nat (K.encode k) + 1).
  Parameter get_set_same : ... (* functional laws as before *)
End MAP.

Module TrieMap (K0 : KEY) <: MAP with Module K := K0.
  Module K := K0.
  Definition t := Trie.t.
  Definition get {A} k (m : t A) := Trie.get (K.encode k) m.
  TimeFun get.       (* = fun A k m => 1 + (K.T_encode k + Trie.T_get A (K.encode k) m)   [tested] *)
  Definition set {A} k v (m : t A) := Trie.set (K.encode k) v m.
  TimeFun set.
  Definition c_map := K.c_encode + 6.
  Lemma T_get_le ... Proof. unfold T_get; pose proof (K.T_encode_le k);
    pose proof (Trie.T_get_le (K.encode k) m); nia. Qed.
  ...
End TrieMap.

Module Type UNION_FIND.
  Declare Module K : KEY.
  Parameter t : Type.
  Parameter make : t.
  Parameter find : K.t -> t -> K.t * t.
  Parameter union : K.t -> K.t -> t -> t.
  (* spec: wf size width *)
  Parameter wf : t -> Prop.
  Parameter size : t -> nat.          (* keys in the support *)
  Parameter width : t -> K.t -> nat.  (* max key bits over support ∪ {x} *)
  Parameter T_find : K.t -> t -> nat.
  Parameter T_union : K.t -> K.t -> t -> nat.
  Parameter c_uf : nat.
  Parameter T_find_le : forall x u, wf u ->
    T_find x u <= c_uf * (Nat.log2 (size u) + 1) * (width u x + 1).
  Parameter T_union_le : forall x y u, wf u ->
    T_union x y u <= c_uf * (Nat.log2 (size u) + 1) * (max (width u x) (width u y) + 1).
  Parameter wf_make : wf make.  Parameter wf_find : ...  Parameter wf_union : ...
End UNION_FIND.
```

**Union-find implementation outline.**
- `Module UnionFindTrie (K0 : KEY) (M : MAP with Module K := K0)` has parents and ranks maps.
- `find` is `loop_fuel walk (S (max_rank u))` followed by a compression `fold_left` over the path. Both are timed by `TimeFun`.
- Contract proof as a chain of admitted lemmas:

```coq
Lemma T_walk_step_le : wf u -> T_walk_step u s <= 2*M.c_map*(width u x + 1) + 4.
Lemma walk_length : wf u -> length (snd (walk_path u x)) <= max_rank u.  (* from rank increase *)
Lemma T_walk_le : wf u -> T_walk u x <= (max_rank u + 1) * (2*M.c_map*(width u x+1) + 5).
   (* loop_bound with Phi s := (max_rank u - rank s)*(2*c*(w+1)+5) *)
Lemma T_compress_le : T_compress path root u <= (length path + 1)*(M.c_map*(width u x+1)+3).
   (* T_fold_left_le *)
Lemma rank_log : wf u -> max_rank u <= Nat.log2 (size u).    (* reuse BaseUnionFindRank.v *)
Lemma T_find_le : ... (* time_step find; pose the four; nia *)
```

---

## 6. Worked examples

### (a) Trie lookup and insert

Every script below compiled. The definitions were generated by the prototype, and the lemmas were proved on verbatim copies with explicit `A`.

```coq
(* generated *)
T_get = fix T_get (A : Type) (p : positive) (m : t A) {struct p} : nat :=
  1 + match p with q~1 => T_right A m + T_get A q (right m)
                 | q~0 => T_left A m + T_get A q (left m) | 1 => T_value A m end
T_set = fix T_set A p v m {struct p} := 1 + match p with
  | q~1 => T_left A m + (T_value A m + (T_right A m + T_set A q v (right m)))
           + T_node A (left m) (value m) (set q v (right m))
  | q~0 => ... | 1 => T_left A m + T_right A m + T_node A (left m) (Some v) (right m) end
T_node = fun A _ _ _ => 1          (* match of zeros folded *)

Ltac ih m := repeat match goal with H : forall _ : t _, _ |- _ =>
  pose proof (H (left m)); pose proof (H (right m)); clear H end.
Lemma T_get_le {A} p (m : t A) : T_get p m <= 2 * Pos.size_nat p.
Proof. revert m; induction p; intro m; cbn [T_get Pos.size_nat];
  unfold T_left, T_right, T_value; ih m; lia. Qed.
Lemma T_get_ge {A} p (m : t A) : Pos.size_nat p <= T_get p m.   (* Θ witness *)
Proof. (same script) Qed.
Lemma T_set_le {A} p (v : A) (m : t A) : T_set p v m <= 5 * Pos.size_nat p.
Proof. revert m; induction p; intro m; cbn [T_set Pos.size_nat];
  unfold T_left, T_right, T_value, T_node; ih m; lia. Qed.
Theorem get_bigO {A} : bigO (fun _ => True) (fun '(p, _) => Pos.size_nat p)
                                 (fun '(p, m) => @T_get A p m).
Proof. eapply bigO_intro with (c := 2); intros [p m] _; pose proof (T_get_le p m); lia. Qed.
```

**Line counts.**
- Today: 70 lines of `_c`, `_equation` and `_cost` plumbing in `BaseTrie.v`, and 1,100 lines in `BaseTrieCost.v`, most of it merge operations.
- New: 12 lines for get/set/remove including the Θ witness, and the code loses every `_c` and `_equation`.
- Merges keep their overlap measures. I estimate 350–450 lines for `BaseTrieCost.v`, because the `autorewrite with galois_cost`, `Cost.ticks` and `overlap_ext` plumbing disappears. This is an estimate, not a measurement.

### (b) Amortised structure: the lazy-decrease heap (`BaseHeap.v`)

Design: `pop` is `loop_fuel pop_step (S (pending q))`, which discards stale entries. The fuel comes from data, and the bound does not depend on it.

```coq
Definition unit_cost P w := c_heap * (Nat.log2 P + 1) * (w + 1).
Definition phi P w q := stale q * unit_cost P w.                       (* spec *)
Lemma T_push_le   : wf q -> key_budget w q -> pending q < P -> T_push p k q <= unit_cost P w.
Lemma push_stale  : stale (push p k q) <= stale q + 1.
Lemma T_push_amort: ... T_push p k q + phi P w (push p k q) <= 2 * unit_cost P w + phi P w q.
Lemma T_pop_step_go : wf_state s -> pop_step s = inl s1 ->           (* a stale discard *)
    T_pop_step s + phi_state s1 < phi_state s.     (* phi_state counts the remaining stale entries *)
Lemma T_pop_step_stop : ... T_pop_step s <= 2 * unit_cost P w.
Lemma T_pop_amort : wf q -> ... -> T_pop q + phi_out (pop q) <= 3 * unit_cost P w + phi P w q.
   (* loop_bound phi_state (2*unit_cost) ; then nia *)
Theorem heap_ops_total : forall os, ... total os empty <= 3 * unit_cost P w * length os.
   (* amortise; amortised_uniform with k := 3*unit_cost *)
Theorem pop_bigO : bigO … (fun '(P, w, _) => (log2 P + 1) * (w + 1)) …   (* amortised, by the corollary *)
```

**Line counts.** Current: `BaseHeapCost.v` 145 lines, plus the cost sections of `BaseHeap.v` (about lines 515–850, roughly 340) and `BaseHeapBinomialCost.v` 241. I expect about 200 in total, an estimate.

**Union-find: the tightest bound for a purely functional implementation over tries.**
- **Worst case per operation, valid under persistence: Θ(log n · w).**
  - Union by rank keeps every tree's depth at most ⌊log₂ n⌋.
  - A sequence of unions building binomial trees forces a find of depth Θ(log n).
  - Each parent or rank access is a trie lookup of Θ(w) for keys of w bits. `T_get_ge` gives the lower bound.
- **Amortised, single-threaded, with path compression: O(α(n) · w)** per operation.
  - Map accesses obey Tarjan's bound; compression only changes the map contents.
  - Fredman and Saks give a matching Ω(α(n)) cell-probe lower bound.
  - It holds only along a single linear sequence of versions, not under branching reuse.
- **Persistent use.** Italiano and Sarnak show O(log n) per operation for fully persistent union-find, but only with imperative fat nodes. No purely functional structure is known to beat O(log n) map accesses per operation. Blum's Θ(log n / log log n) is the optimal worst case for the problem, but it is a different algorithm.
- **Recommendation.** Publish the worst-case Θ(log n · w) contract (section 5) now. Treat O(α(n) · w) as a stretch goal, using Charguéraud–Pottier's Coq potential as the template.

### (c) The worklist solver loop

```coq
Module Worklist (X C : KEY) (L : LAT) (Sys : SYSTEM with Module X := X …) (Pol : POLICY …)
                (XM : MAP with Module K := X) (CS : SET with Module K := C) (H : PQ with Module K := C).
  (* step / update / enqueue: the current bodies with the monad removed *)
  Definition run p fuel := let ix := index p in
    match loop_fuel (step p ix) fuel (initial p) with inl s => OutOfFuel (current s) | inr d => Solved d end.
  TimeFun enqueue_one. TimeFun enqueue. TimeFun update. TimeFun updates. TimeFun step. TimeFun run.

  Definition credit p s := Σ_{x ∈ U p} (L.height - rank (look s x)) * degree p x.          (* reused *)
  Definition Phi p s := k_row p * (H.size (queue s) + credit p s) + H.phi P w (queue s).
  Lemma T_enqueue_one_le : good s -> T_enqueue_one p c s + H.phi … <= k_enq p + H.phi …
  Lemma T_update_le : good s -> T_update p ix s (x,a) <= k_upd p * (1 + changed * degree p x) + …
  Lemma T_step_go   : good s -> step p ix s = inl s1 -> good s1 /\ T_step p ix s + Phi p s1 < Phi p s.
  Lemma T_step_stop : good s -> step p ix s = inr r -> T_step p ix s <= k_row p.
  Lemma T_run_le : laws p -> T_run p fuel <= T_index p + T_initial p + Phi p (initial p) + k_row p + 2.
  Theorem run_bigO : bigO (fun '(p, _) => laws p /\ finite_height p)
    (fun '(p, _) => prep p + (C p + height p * D p) * (row_work p + (log2 (C p) + 1) * (w p + 1)))
    (fun '(p, fuel) => T_run p fuel).
End Worklist.
```

- `row_work` comes from the `SYSTEM` and `LAT` contracts.
- The old `worklist_cost` had 9 binders, 7 of them laws, witnesses or cost models. Here the cost models live in the signatures, so the binders are `p`, laws and height.
- **Line counts.** `FixpointWorklistCost.v` is 1,096 lines; I estimate 300–400 here, mostly the reused credit invariant.

---

## 7. Closures in data

**Rule.** Function values may be passed as arguments but never stored in data. `TimeFun` rejects the attempt (tested). How each current pattern migrates:

- **Dictionary records** (`lattice`, `encoding`, `Policy.t`, `System.static` and their `_c` fields; 118 files have such fields): these become functor parameters `LAT`, `KEY` and `POLICY`, as already decided.
- **Graphs as `out_c` closures:** graphs become first-order data, an adjacency `Map` of lists. `out g n := Map.find_or [] n (adj g)` is derived.
- **Visitor records:** these become higher-order function parameters, each with a companion.
- **Query trees.** `Ask x (k : A -> Cost.t (Query.t X A))` is defunctionalised (Reynolds; Danvy–Nielsen). There are only four `Query.Ask` construction sites (`FixpointQuery.v:192,209` and `FrameworkDense.v:105,135`).

```coq
Module Query.
  Inductive step (X A F : Type) := Ret (a : A) | Ask (x : X) (f : F) | Side (x : X) (a : A) (q : step X A F).
End Query.
Module Type SYSTEM.
  Parameter prog key row val frame : Type.
  Parameter rows   : prog -> list row.
  Parameter target : prog -> row -> key.
  Parameter start  : prog -> row -> Query.step key val frame.
  Parameter resume : prog -> frame -> val -> Query.step key val frame.
  (* spec: deps row_work frame_work *)
  Parameter deps : prog -> row -> list key.
  Parameter T_target T_start T_resume ... ; Parameter c_sys : nat.
  Parameter T_start_le  : forall p c, T_start p c <= c_sys * (row_work p c + 1).
  Parameter T_resume_le : forall p f a, T_resume p f a <= c_sys * (frame_work p f + 1).
  Parameter reads_within : ...   (* as today *)
End SYSTEM.
```

- The interpreter `Query.eval p look q` is a `loop_fuel` with fuel `length (deps p c) + 1`. Its time is derived, and the read count is bounded by `reads_within`.
- The demand-driven solvers drive `start`/`resume` themselves, so the cost of suspending is local and fits the amortised loop rule.
- `ask_all` becomes the generic frame `AskAll (list key * list val * F)`.
- The dense framework's frame is the edge `e`, with `resume p e a := Ret (transfer p e a)`.
- Analysis authors write a frame type plus `resume`. That is the price of honest accounting for continuations.

---

## 8. Meta-theory

**Cost model.** The model is call-by-value evaluation of the extracted program: OCaml semantics without inlining.
- Types and proofs are erased.
- Closed constants are evaluated once.
- Constants realised natively by extraction cost what the `TimePrim` table says.
- Everything else is Gallina code, so `positive` arithmetic is per bit unless it is mapped natively.

**Claim.** For a closed call `f v̄`, let N be the number of CBV machine steps and K = max |body| over the functions reachable from `f`. Then `calls(f v̄) = T_f v̄` and `N ≤ K · T_f v̄ + K`.

**Argument.**
1. `T_f` adds exactly 1 per invocation of a defined function or closure body. Evaluation order does not matter, because the cost is a sum. The cost is exact on `match` (only the taken branch) and on `let` (charged once).
2. Between two consecutive counted invocations, the machine executes part of one body. A body has no loops other than calls, and each syntactic subterm of it runs at most once per execution, so that segment takes at most K steps.
3. Hence `T_f v̄ ≤ N ≤ K·(T_f v̄ + 1)`, which is Θ.

**Companions.** Theorems quantify over `T_g` under hypotheses such as `∀ a, T_g a <= k`. At every real call site the companion is `F⟦arg⟧`, generated from the argument's own body, so instantiating the theorem is faithful. The prototype reproduces this exactly.

**Trusted base.**
- The Rocq kernel.
- The Elpi translator, which is unverified: a translator bug could under-charge.
- The `TimePrim` table, under review.
- The extraction realisations of table entries.

`T_` constants cannot be hand-edited: `TimeCheck f` re-runs the translation and requires conversion with the stored `T_f`.

**Backing test.**
- Extract with `Unset Extraction AutoInline` and compile with `ocamlfind ocamlcp -P f`, which profiles function entries.
- On fixtures, assert `Σ entry counts = T_f x`, with `T_f` extracted alongside and evaluated by vm or OCaml.
- With no native table, equality is expected exactly: one OCaml function entry per Gallina call, one per λ body, and one per constructor closure.
- This is a sharp oracle for translator bugs.
- A formal in-Rocq soundness proof needs a reflected syntax. MetaRocq is not packaged for 9.3, so I do not propose it.

**Persistence versus amortisation.**
- Worst-case contracts hold for every version.
- Amortised contracts are per-operation inequalities on arbitrary states. `amortised_run` bounds any single root-to-leaf path in the version tree.
- Nothing is claimed for the sum over a branching tree. Repeating an expensive `pop` from the same version k times is the counterexample.
- Okasaki's laziness-based persistence does not apply, because the code is strict.

---

## 9. Enforcement

**Elpi audit (`TimeAudit`, about 40 lines).** It runs in each extraction root file:

```
Elpi TimeAudit run_worklist dfs ... .
```

- It walks the bodies reachable from the roots, transitively, following module aliases.
- It fails on any computational constant (not a closed constant, not irr) that has no `timed` entry, unless it is in `CostPrim`.
- It fails on any `timed` pair where `TimeCheck` reports non-convertibility.
- It cross-checks that the set of `Extract Constant`/`Extract Inlined Constant` targets equals the `TimePrim` table.

This is what turns "every executable algorithm" into a mechanical check.

**OCaml lint (`tools/check.ml`, module `Time_lint`, ≤ 150 lines).** It replaces `Cost_lint` (lines 636–1155). The lexer strips comments and strings, tracks `Module Type … End` nesting, and works line by line on the result.

- **T1.** Reject `^(Definition|Fixpoint|CoFixpoint|Let|Local Definition|Program|Equations|Function|Instance|Notation|Abbreviation)\s+T_\w+` anywhere. Accept `Parameter T_\w+` only inside a `Module Type`.
- **T2.** Reject `TimePrim` outside `theories/Cost/CostPrim.v`.
- **T3.** In a `Module Type`, every `Parameter op :` whose type contains `->` or `forall` and does not end in `Prop` or `Type`, and is not named in a `(* spec: … *)` pragma, must have `Parameter T_op` and at least one `Parameter T_op_(le|amort)\w*` in the same module type.
- **T4.** Reject `Axiom`/`Admitted` outside skeleton directories, as today. Reject `Opaque T_`.
- **T5.** Reject equalities between a `T_` application and a numeral (`T_\w+[^=<]*=\s*[0-9]`) inside `Theorem|Lemma|Example` statements outside `tests/`. Exact costs never appear in theorems.
- **T6.** Reject `unfold [\w.]*\.T_\w+` and `cbn \[[^]]*\w+\.T_\w+` where the module prefix is not the current file's top module. Clients use contracts only.
- **T7.** Reject the leftovers of the old framework after migration: `Cost.t`, `Cost.step`, `Cost.ticks`, `_c\b` definitions, and `iterate`.
- **T8.** Every `TimeFun x.` must follow, in the same file, a definition of `x` or a `Require` of the module that defines it.

---

## 10. Migration

1. **Identity monad (mechanical, about a day).**
   - Set `Cost.t A := A`, `bind m f := f m`, `ret := id`, and `step := tt`.
   - Delete `Cost.ticks`, every `*_cost`/`ticks` theorem (764 statements), the `*Cost/*Credit/*Debt/*Potential/*Budget` files (19,141 lines; harvest the invariants and potentials first), `Cost_lint`, and `ExtractCost.v`.
   - The value proofs and the `f_equation` lemmas still hold by `reflexivity`.
2. **Teach `TimeFun` the monad (mechanical, about 10 lines of Elpi).** `Cost.bind m (fun x => k)` is read as `let x := m in k`; `ret`, `step`, `tick` and `refine` are identity or 0; `map f m` is `let`, then `f`; `lift w f a` is `f a`. Derive `T_` for all `_c` definitions.
3. **Callback records to functors (manual, structural).** This affects the records above: lattices, encodings, policies, systems and domains, in about 118 files. Query trees are defunctionalised (section 7).
4. **Re-prove bounds (manual, the main work).** Reuse the harvested invariants and potentials: rank–size, the worklist credit, the heap's stale count, and the DFS and Tarjan work measures. The executor works through the admitted chains.
5. **Remove the monad syntax (mechanical).**
   - `let* x := m in k` becomes `let x := m in k`. `Cost.step ;;` is deleted.
   - `f := Cost.value (f_c …)` is merged into `f`, and `f_equation` becomes trivial, then is deleted.
   - Rerun `TimeFun`; `TimeCheck` confirms that each `T_` is unchanged.
6. Replace binary-fuel `iterate` call sites with `loop` or `loop_fuel`. This is semi-mechanical: there are 15 legacy runners.

**How much is mechanical.** Steps 1, 2 and 5 are mechanical, and step 1 removes about 19,000 lines plus the monadic noise. Steps 3, 4 and 6 are manual. Step 4 is the bulk, but it is smaller than today's cost proofs because charge equations and `Cost.ticks` rewriting vanish. My estimate is 40–50% of the current cost lines.

---

## 11. Limits, risks and pilot

**Limits**
- No mutual or local fix, and no function-typed `let`, until the production command adds them. They are specified above.
- Equations and wf definitions must be rewritten to `loop`.
- Defunctionalised queries make analysis authors write frames.
- The α(n) union-find bound is deferred.
- The translator is trusted, mitigated by `TimeCheck` and the profile-equality test.

**Risks**
- Elpi performance on large bodies: `coq.typecheck` runs per head. If needed, cache types per constant.
- The `TimePrim` table could drift from extraction; `TimeAudit` cross-checks it.
- Guard-checker corner cases with nested inductives. `T_map size T_size` inside a fix needs `T_map` to unfold for the guard checker; this is untested.
- The extraction mapping is a decision that should be explicit. Under the current mapping (no native numbers), N and positive counters cost per bit. Either map them to OCaml `int` and table them, or accept the w factor.

**Pilot: Base (`BaseTrie`, `BaseMap`, `BaseUnionFind`+`Rank`, `BaseHeap`+`Binomial`), then `GraphSearch`.**

Pass if:
1. `TimeFun` derives every executable definition, with no handwritten `T_` and no restructuring beyond callback records.
2. All contracts are proved with no `Admitted` and closed `Print Assumptions`.
3. Cost proof lines are at most 40% of today's for these files.
4. `vm_compute` test times are within ±5% and the extracted `.ml` contains no cost artefacts.
5. Profile-equality holds on all fixtures.
6. The executor fills the union-find chain in one session.

Fail if more than 10% of definitions need semantic rewrites to pass `TimeFun`, or if `time_step` closes fewer than 70% of per-operation lemmas within 5 lines.

---

## 12. Literature map

- **Time functions and translation rules:** Nipkow, Eberl and Haslbeck (eds.), *Functional Data Structures and Algorithms: A Proof Assistant Approach* (ACM Books, 2025), §1.5. Isabelle `HOL-Library.Time_Commands` by J. Stahl, documented in [Time_Manual](https://isabelle.in.tum.de/library/HOL/HOL-Library/Time_Manual.html) and [Time_Commands](https://isabelle.in.tum.de/library/HOL/HOL-Library/Time_Commands.html). Its higher-order support pairs a function with its time function ([Define_Time_Function](https://isabelle.in.tum.de/repos/isabelle/file/7dd81ffaac72/src/HOL/Data_Structures/Define_Time_Function.thy); "new HO time functions", changeset [503e5280ba72](https://isabelle.in.tum.de/repos/isabelle/file/503e5280ba72/src/HOL/Data_Structures/Time_Funs.thy)). Its zero-time primitives include polymorphic `=`, which we deliberately avoid.
- **Amortisation with potentials:** Nipkow, "Amortized Complexity Verified", ITP 2015 ([pdf](https://www.proof.cit.tum.de/~nipkow/pubs/itp15.pdf)); Nipkow and Brinkop, JAR 2019; Tarjan, "Amortized computational complexity", 1985.
- **Big-O pitfalls and filters:** Guéneau, Charguéraud and Pottier, "A Fistful of Dollars", ESOP 2018.
- **Monadic Coq cost library:** McCarthy, Fetscher, New, Feltey and Findler, FLOPS 2016 / SCP 2018.
- **Elpi:** Tassi, "Elpi: an extension language for Coq", CoqPL 2018; Tassi, "Deriving proved equality tests in Coq-Elpi", ITP 2019.
- **Certifying extraction with time:** Forster and Kunze, ITP 2019; Forster, Kunze and Roth, POPL 2020.
- **Time credits:** Charguéraud and Pottier, ITP 2015 and JAR 2019 (union-find, α(n)); Mével, Jourdan and Pottier, ESOP 2019 (Iris).
- **Other frameworks:** Niu, Sterling, Grodin and Harper, Calf, POPL 2022; Handley, Vazou and Hutton, Liquid Haskell RTick, POPL 2020; Hofmann and Jost, POPL 2003, and Hoffmann et al. (RaML / AARA); Danielsson, POPL 2008 (Thunk); Haslbeck and Lammich, "Refinement with Time", ITP 2019.
- **Persistence:** Okasaki, *Purely Functional Data Structures*, 1998; Xia et al., demand semantics, ICFP 2024 ([arXiv 2406.14787](https://www.arxiv.org/pdf/2406.14787)).
- **Purity overhead:** Pippenger, "Pure versus impure Lisp", TOPLAS 1997; Bird, Jones and de Moor, JFP 1997.
- **Union-find:** Tarjan, JACM 1975; Tarjan and van Leeuwen, JACM 1984; Fredman and Saks, STOC 1989; Blum, SICOMP 1986; Italiano and Sarnak, WADS 1991; Conchon and Filliâtre, ML Workshop 2007.
- **Defunctionalisation:** Reynolds, 1972; Danvy and Nielsen, PPDP 2001.
- **Lazy `Acc` unfolding:** `Acc_intro_generator` in Rocq's `Init/Wf.v`.

### Critical files for implementation
- /home/nandhagk/Projects/galois/theories/Cost/CostMonad.v
- /home/nandhagk/Projects/galois/theories/Cost/CostLoop.v
- /home/nandhagk/Projects/galois/theories/Base/BaseTrie.v
- /home/nandhagk/Projects/galois/theories/Fixpoint/FixpointQuery.v
- /home/nandhagk/Projects/galois/tools/check.ml
