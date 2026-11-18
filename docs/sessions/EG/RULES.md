# Rules of the EG sessions

Each EG session proves the STUB lemmas of one file of the Egglog front end (`theories/Front`) or
of a client (`theories/Clients`). Its card names the file, the base commit `BASE` of `main`, the
lemmas and the order of work. These rules bind every EG session, and a card adds to them.
`docs/guide/egglog.md` explains the front end, and `PLAN.md` beside this file gives the design.

## Scope

- Edit only the file that your card owns, and the test file if your card names one.
  `git diff --name-only BASE..HEAD` lists those paths and no other.
- Never edit a `*Sig.v` file, `theories/Front/Spec.v`, or a file listed in `just/frozen.sha256`.
  `just frozen` must pass.
- Prove against the public statements only. These are the front-end signatures
  (`theories/Front/*Sig.v`, `Spec.v`, `SpecFacts.v`) and the engine contracts
  (`theories/Egglog/*Sig.v`, `Model.v`, `Sorts.v`, `Syntax.v`). Never unfold a definition of
  `Run.v`, `Database.v`, `Join.v`, `Index.v` or `Extract.v`.
- A lemma of your file that is no field of a module type is a helper. A helper may gain premises,
  change or go when every field that used it is proved again. Name each changed helper in the
  handoff.
- A constant `c_*` or `k_*` that no law of its signature fixes may take a new value. The value is
  a closed expression over the public constants of the functor parameters. Every field that uses
  it is proved again, and the handoff records the old and the new value. Never unfold a constant
  of a parameter.

## Proofs

- Never write `Axiom`, `admit`, `give_up`, `Abort` or a hand-written clock (`TimePrim`). Clocks are
  derived by `TimeFun` and never written by hand.
- Never import `Psatz`, `Lra`, `Reals`, `FunctionalExtensionality` or MathComp.
- Write a large `nat` literal as a product, such as `8 * 4096`. Split nonlinear arithmetic into
  small lemmas, because broad `nia` and `ring` calls over large contexts ran out of time and
  memory in earlier sessions.
- After 45 minutes without progress on one lemma, leave it `Admitted. (* OPEN: what is missing *)`
  and go on.
- A statement that is false for the code stays `Admitted. (* SIG-QUESTION: reason *)`. Give a
  counterexample that `vm_compute` checks, in the handoff.
- The lint forbids a numeral written as a table code or a variable number in `theories/Clients`
  and `tests/Front`. Use the generated `P.<Table>_code` constants.

## Tools

- Never use Python. Use `just` in the released environment for every build and check, and never
  run `dune` directly.
- Run one build at a time, in the background with a log, and build one file with
  `just vo theories/Front/<File>.v`.
- If a compiler runs out of memory under an address-space limit, set `OCAMLRUNPARAM=d=4`.

## Checkpoints

Write a checkpoint every 15 minutes. A checkpoint runs no build. Commit the lemmas that you closed
since the last checkpoint, then run these commands, where `<ID>` is your card and `<n>` counts
the checkpoints from 01.

```sh
  mkdir -p ~/out/patches && rm -f ~/out/patches/*.patch
  git format-patch BASE..HEAD -o ~/out/patches
  cp -n docs/sessions/HANDOFF.md ~/out/HANDOFF-EG-<ID>.md   # then bring it up to date
  tar -czf ~/EG-<ID>-checkpoint-<n>.tar.gz -C ~/out .
```

Every 90 minutes, and before the deliverable, also run the full checks.

```sh
  just session-check                       # fmt, build, tests, lint, frozen
  just audit --admitted-ok Front Clients   # your package and its dependencies
  just admits > /tmp/admits.txt
  git diff --name-only BASE..HEAD          # your paths only
```

## Deliverable

Deliver `~/out/patches/*.patch` from `BASE` and `~/out/HANDOFF-EG-<ID>.md`, and nothing else.
The handoff records:

- the lemmas closed;
- the lemmas left, with their tags;
- each `SIG-QUESTION` with its counterexample;
- each changed helper;
- each changed constant, with its old and new value;
- `just admits` before and after.

If a full check fails at the end, revert the last failing commit and say so in the handoff.
