# Rules for batch sessions

## 1. Ownership and frozen statements

Work only in the paths assigned by the session prompt. Never edit a `*Sig.v` file. The
signature takes precedence over other text, and `just frozen` must pass. Do not change a
definition fixed by a signature. Replace code bodies only where marked `STUB-CODE`.
Extra lemmas, helper definitions and internal modules in owned files are allowed.

The design copies record the original design. The released signatures and implementations
govern their interfaces when they differ from those copies. `DOM_OPS.build` returns a parent
map and a low-high order, and `DOM_OPS.check` takes both. `NatKey` has no timed instance.
System row codes have program-scoped injectivity, so there is no global `SystemRowT`. Policy
update clocks use `N`. The worklist tracks armed readers and live queue entries. Word domains
use `Bits/Word.v` and `Bits/Op.v`, and `EnvBudget` supplies a canonical word budget functor.

`HEIGHT.rank_mono` supports sum ranks for products. `ReducedT` takes `JOIN_SIZE`
instances for both components as well as `REDUCER_T`. Widening time charges `wsize` per
component through `wunits`, and `BUDGET.wunits_le` bounds those units for invariant states.
Value domains and their bases have downward bottom-recognition laws. Product and reduced
product recognize a bottom in either component with `orb` and treat recognized bottoms as
least. `Env` concretization of a reached map requires no recognized bottom in the map.
Karr and Poly state `normal` and `normal_s` premises on the relevant time contracts and
preserve these properties in their plans. A normal row has distinct coefficient keys.
Word evaluation charges raw integer operand sizes as well as widths.

The reviewed helpers `Base/Code.v`, `Base/Loop.v` and `Fixpoint/Query.v` are excluded from
`just/frozen.sha256` so that their owners can prove existing lemmas. Keep their reviewed
statements and definitions unchanged. Every file listed in the checksum stays unchanged.

## 2. Work and checks

Follow `AGENTS.md` and the session prompt. Read landed proofs at commit `87192fe` using
`git show 87192fe:<path>`. Prove the plan lemmas in order, build each file with `just vo`,
and commit each item. Run `just session-check`, `just admits` and `just owned` at each
checkpoint. The session prompt specifies the checkpoint and delivery procedure.

## 3. Unfinished proofs and defects

Keep each statement unchanged. After 20 minutes without progress on a lemma, leave it
`Admitted` with `(* OPEN: what is missing *)` and continue. If a plan lemma is false or
useless, prove its contract by another route and leave the lemma `Admitted` with
`(* PLAN-DEFECT: reason, counterexample if any *)`. If a law or time statement is false,
stop work on that component and leave it `Admitted` with `(* SIG-QUESTION: reason *)`.
Port the landed proof named by a `CONVERT` tag. Renaming and unfolding are allowed.
Never weaken a statement or add a hypothesis to a signature lemma.

## 4. Tags

A tag is the first word of a comment on the same line as `Admitted`, or on the line of the
definition that it marks. `just admits` counts the tags per package, and an `Admitted` with no
tag counts as plain.

| Tag | Form | Meaning | Written by |
| --- | --- | --- | --- |
| `CONVERT` | `Proof. Admitted. (* CONVERT: <old name>: <first error line> *)` | A landed proof did not survive conversion. The session ports the proof that the tag names. | Groundwork |
| `STUB` | `Proof. Admitted. (* STUB *)`, and `Definition c_x : N := 1. (* STUB *)` | A time or plan lemma written by recipe step 7, or a constant whose value the session chooses. | Groundwork |
| `STUB-CODE` | `(* STUB-CODE *)` on the line before a definition | A placeholder body for a new algorithm. The session that owns the file writes the code. | Groundwork |
| `SIG-QUESTION` | `Proof. Admitted. (* SIG-QUESTION: <reason> *)` | The statement is believed true, nothing landed proves it, and a reviewer should look at it. | Groundwork and sessions |
| `PLAN-DEFECT` | `Proof. Admitted. (* PLAN-DEFECT: <reason> *)` | A plan lemma is false or useless (R11). | Sessions only |
| `OPEN` | `Proof. Admitted. (* OPEN: <what is missing> *)` | A session left the lemma for later. | Sessions only |
| none | `Proof. Admitted.` | A new obligation with no landed proof, such as a law of new code. | Groundwork |

Never write `admit`, `give_up` or `Abort`, and never write `Axiom` or `Parameter` outside a
module type.

## 5. Design rules R1 to R13

The rules are copied from core §1, lines 65–129. Later decisions amend them.

- R8 and the paragraph on the extraction shape name `Exec/Instances.v`. The lint forbids the word
  `Instances`, so that file is `Exec/Kit.v` (plan conflict 6). Nothing in this run writes it.
- `BoundedSetCode` takes `SET` laws to construct its Boolean subtype proof. Extraction erases
  that proof. This is the sole exception to operations-only code dependencies.
- R11 binds the batch sessions. Groundwork writes the `Sig` files, and §3 of this file is its
  rule for wrong statements.
- The first lint of R13 concerns `Include` inside a module (a `Module ... End` body), where a
  `Parameter` of the included type becomes an axiom (F3). `Include` of a module type inside
  another module type keeps its parameters, as in `VALUE_DOMAIN_OPS` (core §3.3), and is allowed.

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

**R4. Running without law proofs stays possible, by construction.** Code functors take `_OPS` arguments, apart from the approved `BoundedSetCode` exception stated above. A domain with no proofs can otherwise run and extract with no `Admitted` anywhere. Certification needs no laws either: `check` reflects `post_solution` definitionally. A client proves only what its theorem uses.

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

## 6. Module patterns

The two tables are copied without change from core §9, lines 1794–1819.

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

## 7. Layout and naming

- A new file is `theories/<Pkg>/<Name>.v`, without the package prefix of the old files. Its
  signatures are in `theories/<Pkg>/<Name>Sig.v`, and its tests in `tests/<Pkg>/<Name>Test.v`.
  Basenames may repeat across packages (plan conflict 14), so `Domains/ValueSig.v` and
  `Egglog/ValueSig.v` can both exist.
- `Set` is a keyword of Rocq, so a file named `Set.v` cannot be required. The set of core §3.1
  lives in `Base/TrieSet.v`, with its signature in `Base/SetSig.v`.
- Every `Require` names its root, as in `From Galois.Base Require Import KeySig Trie.`,
  `From Argent Require Import Time.` and `From Stdlib Require Import List.` A bare `Require` fails
  the lint.
- The theory of package `<Pkg>` is `Galois.<Pkg>`, its tests are `Galois.Tests.<Pkg>`, and the
  examples are `Galois.Examples`.
- A module type is named by its component in capitals, followed by the layer, as in `FOO_OPS`,
  `FOO_SPEC`, `FOO_LAWS`, `FOO`, `FOO_TIME`, `FOO_T`, `FOO_PLAN` and `FOO_ALL`. A module type that
  states the theorems of a soundness functor ends in `_SOUND`, for example `DENSE_SOUND`, so that
  every theorem a session proves has a frozen statement (plan conflict 8).
- The modules of a component are `FooCode`, `Foo` and `FooT` (R2), and a soundness functor is
  `FooSound`.
- In the time layer, the time function of `op` is `T_op`, its contract is `T_op_le`, a contract
  constant is `c_<name>`, a plan constant is `k_<name>`, the plan lemmas are `F1_<name>`,
  `F2_<name>`, … and `T1_<name>`, `T2_<name>`, …, and a published corollary is `<op>_bigO`.
- Inductive types and records are declared at top level, parameterised by types (R6).
- Each package depends on the packages below, besides `Stdlib` and `Argent`. Lane 1 writes these
  dependencies into the dune files. Two edges are missing from the package map of core §2.
  `Framework` needs `Domains` and `States`, because `Interp` uses `LANG`, `VALUE_DOMAIN` and
  `STATE_DOMAIN`. `States` needs `Fixpoint`, because `EnvBudget` instantiates `BUDGET`.

| Package | Depends on |
| --- | --- |
| `Base` | nothing else |
| `Lattice`, `Graph`, `Bits`, `Egglog` | `Base` |
| `Fixpoint` | `Base`, `Lattice`, `Graph` |
| `Program` | `Base`, `Graph` |
| `Domains` | `Base`, `Lattice`, `Bits` |
| `States` | `Domains`, `Fixpoint` and theirs |
| `Framework` | `Fixpoint`, `Program`, `Domains`, `States` and theirs |
| `Relational` | `States` and its dependencies |
| `Widening` | `Domains`, `Fixpoint` and theirs |
| `Alarms` | `States`, `Framework` and theirs |
| `Egraph` | `Egglog` and its dependencies |
| `Ssa` | `Base`, `Graph`, `Program` |
| `Incremental` | `Fixpoint` and its dependencies |
| `Clients` | `Egglog`, `Egraph` and theirs |

## 8. Writing a `Sig` file

A signature file states one component, or a few closely related ones, in the layers of R1. The
complete model is `UnionFindSig.v` in core §6, lines 1327–1439. Write a signature file in the
following order.

1. Write the requires. Import `From Argent Require Import Time.` for the commands, and also
   `BigO` when a statement uses `bigO`.
2. Put above the first module type the top-level data and helper functions that the statements
   mention (R6, R7), each executable helper followed by its `TimeFun` line. This top-level code
   is part of the frozen statement.
3. Write the layers in the order `FOO_OPS`, `FOO_SPEC`, `FOO_LAWS`, `FOO`, `FOO_TIME`, `FOO_T`,
   `FOO_PLAN`, `FOO_ALL`, and leave out a layer that has no content. Each dependency is a
   parameter typed by the layer that it needs (R1, R3). An `_OPS` layer takes `_OPS` parameters,
   a `_LAWS` layer takes functional bundles, and `_TIME` and `_PLAN` layers take `_T` bundles.
4. Start the spec parameters of a `_LAWS` or `_TIME` layer with a pragma that lists them, such as
   `(* spec: wf nodes *)`.
5. Write every statement out in full. Where the design abbreviates ("`T_set_le`, `T_remove_le`:
   the same bound"), write each lemma. Where the design gives only prose, state it in Rocq. That
   is Sol's work, and the lane file says where.
6. In `_TIME`, declare one `Parameter T_op` per operation, with the type that `TimeFun` derives.
   A time function returns `N`, and that type adds a companion with values in `N` right after
   each function argument, so the time function of `merge` has the type
   `forall {A B C}, (option A -> option B -> option C) -> (option A -> option B -> N) -> t A -> t B -> N`.
   Then declare the named constants, the contracts, and the published `bigO` corollaries, all by
   the rule "Time values are binary" below.
7. In `_PLAN`, declare the internals that the proof talks about as `Parameter`s with their `T_`,
   the plan constants `k_*`, the invariants and potentials as definitions, and the chain of `F`
   lemmas and then `T` lemmas that ends at the contracts. A plan is good when a session can prove
   its lemmas in order, each from the earlier ones and the layers above. Check each lemma against
   the code before you write it down.
8. Compile with `just vo`. The layers fit together when the three modules of the matching `Foo.v`
   ascribe to them (§9). Test that a wrong implementation is rejected only by applying a checking
   functor (V4), never with `Fail Module` (F6).

**Time values are binary.** This rule holds from Argent revision `c88e642` on, and it governs
every statement about time in a signature, an implementation, a helper and a test.

- A time function, a companion of a function argument, a time constant (`c_*`, `k_*`), the
  potential of a time bound and the bound itself have type `N`.
- A size keeps its type. A length, a bit length, a node count, a rank, a height and the fuel of
  `loop_fuel` stay in `nat`, and so does a definition that combines sizes, such as `unit_pq`.
- A size enters a bound through `N.of_nat`. Wrap each largest subterm of type `nat` once, so
  `T_get k m <= c_map * (K.bits k + 1)` becomes
  `(T_get k m <= c_map * N.of_nat (K.bits k + 1))%N`. A size that is already an `N` enters as
  it is.
- Write each time statement in `N_scope`, with `%N` on the statement. The size function of a
  `bigO` statement returns `N`.
- A design document that states a time contract in `nat` is read by this rule.

## 9. Writing `Foo.v`

`Foo.v` holds the three modules of R2. The design gives two complete models.

- The converted combinator `Dual` (core §7, lines 1655–1707) shows all three levels with real
  proofs.
- The union-find (core §6, lines 1441–1583) shows new code with real bodies, laws left
  `Admitted`, and a timed module with `TimeFun` lines, stub constants and admitted plan lemmas.

Write `Foo.v` in the following order.

1. The requires, then every `Inductive` and `Record` at top level (R6).
2. `Module FooCode (K : KEY_OPS) <: FOO_OPS K.` with definitions only. Compile it alone before
   going on. A placeholder body for a new algorithm carries `(* STUB-CODE *)`, has the type that
   the signature fixes, and must be accepted by `TimeFun`.
3. `Module Foo (K : KEY) <: FOO K.` starts with `Include FooCode K.` and, when the signature has a
   `_SPEC` layer, `Include FOO_SPEC K.` (V5). Then come the definitions of the spec parameters and
   the laws, as `Lemma`s with the names of the signature.
4. `Module FooT (K : KEY_T) <: FOO_ALL K.` starts with `Include Foo K.` Then come the `TimeFun`
   lines, the constants, the definitions that the plan declares as parameters, the plan lemmas,
   the contracts and the `bigO` corollaries.
5. A soundness functor `FooSound` is a sibling of `FooT` and starts with `Include Foo …` (R2).

A level that has no content is left out, so a solver's `WorklistT` includes `WorklistCode`.

## 10. `TimeFun` in the timed layer

`TimeFun` (Argent, `/home/nandhagk/Projects/argent/docs/manual.md`) derives `T_f` from the body
of `f` and places it beside `f`. Use it as follows.

- Import `From Argent Require Import Time Tactics Std.` in a file that derives or bounds time
  functions. `Std` holds the time functions of the standard library (`Nat.T_add`, `Pos.T_compare`
  and so on), and `TimeFun` needs them for every standard function that the code calls. Import
  `Loop` for `loop` and `loop_fuel`, and `BigO` for `bigO`.
- Run `TimeFun` on a top-level helper at top level, right after its definition. Run it on the
  operations of a component inside `FooT`, after `Include Foo K.`, with one `TimeFun` per
  definition of `FooCode`, callees first. After `Include`, `TimeFun` finds the included
  definitions and the time fields of the parameters by the sibling rule (V9), so time
  fields travel inside `_T` bundles (R3) and never as a separate argument (F5).
- Never write a time function by hand, because `TimeCheck` and `TimeAudit` fail on one.
  `TimePrim` declares a trusted cost, so use it only when the master agrees, and add a line under
  "Open problems".
- Do not run `TimeFun`, `TimePrim`, `TimeUnfold` or `TimeBound` for a constant of another library
  inside a functor, because Argent drops what such a command records when the functor ends.
- Short loops use Argent's `loop_fuel` with `nat` fuel computed from data. Long loops use `loopN`
  of `Base/Loop.v` with `N` fuel (R10).
- Use `time_step` and `time_cbn` in a time proof. A plain `cbn` or `simpl` unfolds the arithmetic
  of `N` on a numeral, and `lia` cannot read the result.
- In groundwork, every constant is `Definition c_x : N := 1. (* STUB *)` and every time and plan
  lemma is `Proof. Admitted. (* STUB *)`. A lemma that `time_step` proves in one line may keep
  that proof.

`TimeFun` rejects what it cannot account for, and each rejection has a fix.

| Code | Fix |
| --- | --- |
| `E_CLOSURE_DATA`, `E_CLOSURE` | A function is stored in data. Make the callback a functor parameter or a function argument (R6, R7). |
| `E_NO_TIME` | A callee has no time function. Run `TimeFun` on it first, or import `Argent.Std` for a standard function. |
| `E_WF` | The definition uses `Fix` or `Acc_rect`. Use `loop`, `loop_fuel` or `loopN`. |
| `E_MATCH_FN` | A `match` returns a function. Eta-expand it. |
| `E_SECTION` | The definition uses a section variable. Make it a functor parameter. |
| `E_OPAQUE` | A callee is opaque. End its definition with `Defined`, or call a transparent version. |

No worker writes a timed tower (recipe step 7) before the master announces that Gate P passed.
The two exceptions are Lane 2's Gate P check and Lane 4's check of `eval_term`. When `TimeFun`
fails on an included definition, stop and report. The fallback of core §9, risk 1 (line 1823),
is the master's decision.

## 11. The conversion recipe

The recipe is copied from core §7, lines 1595–1631. The model names are replaced as the owner
decided, so "Luna" stands where the design says Haiku and "Terra" where it says Sonnet. Sol may do
everything that the recipe allows Terra.

**Input:** one landed file `theories/<Pkg>/<Pkg><Name>.v`, the frozen `<Name>Sig.v`, and the `Sig` files of what it uses. **Output:** `theories/<Pkg>/<Name>.v` with `<Name>Code`, `<Name>`, `<Name>T`.

Steps 1, 2 and 7 are textual (Luna). Steps 3 to 6 need a model that reads Rocq (Terra).

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
5. **Place the code.** Move every `Inductive` and `Record` above the first functor. Put the definitions in `Module <Name>Code (…_OPS) <: <NAME>_OPS … .` Apply the `BoundedSetCode` exception in §5 where its subtype requires it. Compile this module alone before going on.
6. **Port the value lemmas** into `Module <Name> (…) <: <NAME> … .`, after `Include <Name>Code … .` and `Include <NAME>_SPEC … .` Rename to the `Sig`'s names. In each proof delete `autorewrite with galois_cost`, `cost_simpl`, `rewrite Cost.value_bind` and its relatives, and `change (Cost.value …)`; replace `rewrite f_equation` by `unfold f` or `cbn [f]`.
7. **Time tower.** `Module <Name>T (…_T) <: <NAME>_ALL … .`, `Include <Name> … .`, one `TimeFun` per definition of the code module in dependency order, each constant as `Definition c_x : N := 1. (* STUB *)`, and every `_TIME` and `_PLAN` lemma stated and closed with `Proof. Admitted.`
8. **Gate.** The file compiles. The ported test file gives, under `vm_compute`, the values the old tests gave. Paste the old expected values; do not recompute them.

**When a proof breaks.**
- Luna never repairs. It replaces the proof by `Proof. Admitted. (* CONVERT: <old theorem name>: <first line of the error> *)`.
- Terra may spend 15 minutes per proof. Allowed: unfolding differently, renaming hypotheses, replacing a rewrite with a deleted equation by `unfold` or `cbn`, reordering `intros`. Not allowed: changing a statement, adding a hypothesis, changing a definition, editing a `Sig`. After 15 minutes, the same `CONVERT` tag.
- If a statement in the `Sig` cannot be matched by the landed lemma (it is stronger, or false), leave it `Admitted` with `(* SIG-QUESTION: … *)` and report it. The `Sig` wins.
- `just admits` counts `CONVERT`, `STUB`, `PLAN-DEFECT` and plain `Admitted` separately, so each session sees what it inherits.

The worked example of the recipe is the conversion of `LatticeDual.v` in core §7, lines
1633–1716. Steps 1 and 2 never need a build. Run `just vo` after steps 5, 6 and 7. Steps 1, 2
and 7 are the textual steps that a lane file gives to Luna.

## 12. Tests

- A test is an `Example` in `tests/<Pkg>/<Name>Test.v`, proved by `vm_compute` and
  `reflexivity`.
- A ported test keeps the expected value of the old test. Paste the old value, and do not
  recompute it (recipe step 8). When the new code gives a different value, turn the `Example`
  into a comment that holds both values, and add a line under "Open problems".
- A test runs code only, through the code tower or the plain functor, and never a time function.
- A test runs only code that exists on `main`. A test that needs another lane's code waits for
  that code to merge.

## 13. Session delivery

Deliver the patch series and completed handoff specified in the session prompt. Record
closed and open items, tagged defects, and `just admits` before and after. If the final
full check fails, revert the last failing commit and report it in the handoff.
