# Egglog programs from Rocq inductives: groundwork, then chat-session cards

The owner approved this plan on 2026-11-18. Where the front end differs from it, the guide
(`docs/guide/egglog.md`) and the signatures (`theories/Front/*Sig.v`) describe the code.

## Context

Clients write engine programs by hand as raw syntax with table and variable numbers, such as
`Rule positive [Fun positive 2 [Var 1; Var 2] None; …] [Put 5 [Var 1; Var 3] None]`. They also
number their models, seeds and encoders (`f = 1%positive`, `Cell x => EApp 6 [ELit x]`). Each
program duplicates a specification that the client already states as an inductive:

- `may_points` in `AndersenSig.v` is Andersen's program.
- `pointer_term` and `pointer_congruence` in `SteensgaardSig.v` are Steensgaard's.

Each client then proves by hand that the numbered copy computes the inductive.

The goal has four parts:

- The specification inductive is also the program.
- One command, `Egglog Andersen from may_points.`, derives the engine program.
- Theorems proved once say that the engine computes exactly that inductive.
- No client or test file spells out a table or variable number.

The command is an Elpi command, like Argent's `TimeFun`, so users write only Rocq.

The work follows the batch process of P1. The main session does the groundwork: it writes and
tests all executable code, writes the signatures with their proof plans, and leaves every proof
as a marked STUB. An Opus review checks the signatures and the cards. The chat sessions then
prove the STUBs from cards.

The existing Steensgaard `solve_exact` is proved relative to a `Q : POINTER_QUOTIENT` that
nothing instantiates, so it is conditional. Theorem G makes it unconditional.

## What users write

```coq
Egglog Andersen from may_points.             (* may_points unchanged *)
Egglog Steensgaard from pointer_congruence.  (* pointer_term, pointer_congruence unchanged *)

Inductive math := Num (n : Z) | Var (x : string) | Add (a b : math) | Mul (a b : math).
Inductive basic : math -> math -> Prop :=
  | add_comm a b : basic (Add a b) (Add b a)
  | distribute a b c : basic (Mul a (Add b c)) (Add (Mul a b) (Mul a c))
  | fold_add a b : basic (Add (Num a) (Num b)) (Num (a + b))
  | fold_mul a b : basic (Mul (Num a) (Num b)) (Num (a * b)).
Egglog Basic from basic.

Example expr1_is_expr2 : Basic.equal 10 expr1 expr2 = true.
Proof. vm_compute. reflexivity. Qed.
```

The command reads an inductive by these rules.

- **Sorts and outputs.** A datatype argument is a class (`SId`). An argument with an
  `Encode A V` instance is a value (`SVal`). Datatype constructors are `OId` tables.
  Prop-valued inductives are `ORel` tables. Tables declared `with merge` are `OLat` tables.
- **Inputs.** Premises such as `In (Addr x a) (constraints q)` read the tables of the
  parameters, so a client's facts are its input record.
- **Rules.** Binders become variables, numbered in binder order. Premises become query atoms.
  The conclusion becomes `Put`, a union, or a rewrite.
  - An equation becomes a union when the premises bind every variable, and both sides are
    built.
  - Otherwise it becomes a rewrite: the left side is matched and the right side is built.
  - Refl, sym, trans and congruence constructors are the e-graph's own laws and produce no
    rule.
- **Other features.** Primitives such as `Z.add` are registered together with their agreement
  proofs. Extraction costs come from a `Cost` instance. Rulesets are separate inductives over
  the same tables, and schedules are Gallina combinators over runs.

The command generates a module `P` with the following.

- `P.spec` and `P.program`.
- `P.facts`, the row encoders, `P.encode` and `P.decode`, `P.relation` and `P.algebra`.
- `P.equal`, `P.extract` and `P.solve`.
- The glue lemma `R args <-> Spec.holds P.spec …`, proved by a generic tactic when the command
  runs. A reifier bug therefore stops the definition and never yields a false theorem.

## Generic theorems, with the statements frozen in groundwork

These are functors over the engine modules and use only frozen contracts (`run_derives`,
`run_least`, `run_closed`, `run_terminates`, `run_sat`, `saturate_sound`, `saturate_facts`,
`saturated_closed`, `ematch_complete`, `best_optimal`, `extract_checked`). `audit.allow` stays
empty, so the proofs use no axioms.

- **R, relations.**
  - A saturated solve holds a row exactly when `Spec.holds` does.
  - Every outcome is sound.
  - Fuel of at least the Herbrand bound saturates a primitive-free spec.
- **G, union rules over inputs.** At saturation, `P.equal t u = true ↔ Spec.equiv … t u` for
  all terms.
  - Completeness: the saturated classes, extended freely to all terms, satisfy every equation.
  - Soundness: a reference congruence closure, defined over the finite set of subterms of the
    ground equations and used only in proofs, gives an algebra whose equality is exactly
    `equiv`. This needs no quotient axiom.
- **E, rewrites.**
  - Equal classes are equal in every algebra that satisfies the rules, so any `eval` that the
    rewrites preserve is preserved.
  - At saturation, terms that rewrite steps connect from represented terms share a class.
  - Extraction returns a term of the same class with minimum cost among represented terms.
- **L, lattice tables.** A stored value is a join of derivable values, and at saturation the
  join of all of them.
- **S, schedules.** Soundness holds for any schedule. Completeness holds when the last step
  saturates every ruleset.

The client contracts (`solve_exact`, `points_spec`, `concrete_sound`) become corollaries. Their
statements are unchanged, except that `STEENSGAARD_EXACT` loses `Q`.

## Groundwork (main session)

1. **Argent.** Commit the bump on `cx/argent`, which passed its full gate (`cx-gates-1.log`).
   Merge it into `main`, push, and remove the worktree.
2. **Base.** Branch `eg/base` from `p1r/base` (`60fda13b`), so that it has the final `RunSig`
   and can reuse the `p1r-base` release's toolchain and cache. The batch only adds files and
   edits the clients, so it is file-disjoint from stage 2 and runs in parallel with it.
3. **Executable code, complete and tested.** None of it waits for a proof.
   - `Egglog/Spec.v`: the embedding, `holds`, `equiv`, `compile`, the checker `spec_ok` and the
     glue tactic.
   - `Egglog/Encode.v`: `Encode`, `Cost`, the primitive registry, rows and runners.
   - `Egglog/Derive.v`: the Elpi command, generic where possible, with `TimeFun` on the shared
     functions.
   - Derive every example and both clients, and validate their glue lemmas. A test `VALUE`
     instance supplies `Z`, `string` and named primitives.
4. **Signatures and proof plans.** `SpecSig.v`, `CongruenceRefSig.v` and `ExactSig.v`, each
   with operations, laws, time contracts and a `*_PLAN` module type, following
   `docs/design/rules.md`. The implementations (`Spec.v` lemmas, `CongruenceRef.v`, `Exact.v`)
   have one `Admitted. (* STUB … *)` per plan step.
5. **Clients.**
   - `AndersenSig.v` and `SteensgaardSig.v` derive their programs, models, seeds and encoders.
     These frozen-file changes are approved with this plan.
   - `Andersen.v` and `Steensgaard.v` keep their executable code on the generated encoders, and
     their contracts become STUB corollaries.
6. **Tests and docs.**
   - New `tests/Egglog/DeriveTest.v` checks each reading rule.
   - New `tests/Clients/EgglogExamplesTest.v` ports `path`, `points-to`,
     `unification-points-to`, `eqsat-basic`, `fibonacci`, `birewrite` and `schedule-demo`. All
     pass under `vm_compute`.
   - Convert the non-stage-2 tests.
   - Add a `just lint` rule against numeral codes and variable numbers.
   - `docs/guide/egglog.md` replaces the stale `datalog.md`, and `rules.md` gains the rule.
7. **Gate and handoff.**
   - Run `gates.sh` on `eg/base`: `session-check` and `audit --admitted-ok` pass, and the
     STUBs are counted.
   - Refreeze.
   - An Opus review checks the signatures and the cards, and every finding is fixed.
   - Build the kit: a bundle of `origin/main..eg/base`, `OWNERSHIP`, the cards and
     `SHA256SUMS`, made with a `mkkit` like `mkkit-p1r.sh`.
   - Test the bootstrap against the `p1r-base` release.

## Cards (chat sessions)

Each card is at most ~6 hours, with every item required, and owns disjoint files. Every card
proves against frozen signatures only, so all of them can run at once, subject to the executor's
six parallel sessions shared with stage 2. These are the planned cards. Hours are estimates, and
a card over ~6 hours is split before dispatch.

| Card | Owns | Proves |
| --- | --- | --- |
| EG-SIM | `Spec.v` proofs | compile laws, simulation `derives ⇔ holds`, `spec_ok` soundness |
| EG-R | `Exact/Relational.v` | theorem R with termination and complexity |
| EG-REF1, EG-REF2 | `CongruenceRef.v` | the reference closure: soundness, then completeness and the exact algebra |
| EG-G | `Exact/Ground.v` | theorem G |
| EG-E | `Exact/Rewrite.v` | theorem E and extraction decoding |
| EG-LS | `Exact/Lattice.v`, `Exact/Schedule.v` | theorems L and S |
| EG-ENC | `Encode.v` proofs | `decode`/`encode` round trips, registry agreements, costs |
| EG-AND | `Andersen.v` | Andersen's contracts as corollaries |
| EG-STE | `Steensgaard.v` | Steensgaard's contracts as corollaries |

The main session integrates each delivery into `eg/base` with the gates. `eg/base` merges into
`main` after stage 2.

## Features that wait for the engine, and why

Everything in egglog's core is in this batch. That covers datatypes, relations, `:merge`
functions, `rule`, `rewrite`, `birewrite`, `:when`, `set`, `union`, `let`, primitives, `run`,
`check`, `extract`, `push` and `pop`, rulesets, `run-schedule`, `:cost`, and containers of
values.

`subsume` and containers of class ids need new engine actions in `Syntax.v`, `Database.v`,
`Run.v` and `Join.v`, which stage 2 owns now. `delete` has no least model, so it can only get a
soundness theorem. These three form an engine batch, planned with cards when stage 2 merges.

## Verification

- At handoff:
  - Every executable example passes under `vm_compute` through generated encoders, never
    against numbered terms.
  - The glue lemmas check for all programs.
  - The gates pass with the STUBs counted, and the Opus review has no open finding.
- At the end:
  - `just admits` reports 0.
  - `Print Assumptions` of the theorems and the corollaries is closed, so `just audit` passes
    with an empty allow list.
  - The full gate passes.
  - `refreeze` changes only the planned signatures.
  - The lint rule passes.
