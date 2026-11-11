# Workflow

## Environment

Enter `nix develop` at the repository root. The pinned toolchain provides Rocq 9.3.0, Stdlib
9.2.0, Flocq 4.2.2, OCaml 5.5.0, dune 3.23.1, ocamlformat 0.29.0 and just 1.58.0.
Run builds, tests, checks and formatting through `just`.

## Commands

The recipes run in `galois.slice` with a default 10 GB shared memory cap and no swap when a
systemd user session exists. Without one, such as in a container, they run directly. The
environment variable `GALOIS_JOBS` sets the number of parallel jobs and defaults to 2. There is
no build lock. `just doc` writes under `_build/`, which is never tracked or edited by hand.

| Command | Action |
| --- | --- |
| `just list` | List recipes. |
| `just build` | Build the theories and extraction clients. |
| `just test` | Build the Rocq tests and examples and run OCaml inline tests. |
| `just check` | Check formatting, build, test, run `just lint` and check the frozen files. |
| `just audit` | Build, then check every compiled module with `rocqchk`. Package names limit the modules. |
| `just admits` | Count `Admitted.` and `Admit Obligations` in each package. |
| `just fmt` | Format OCaml and dune sources. |
| `just doc` | Generate the API reference. |
| `just clean` | Remove this worktree's build outputs. |
| `just slice-cap` | Set the shared memory cap and disable swap. |

## Layout

Each package lives in `theories/<Package>/` and declares its `Galois.<Package>` theory.
The `Analyses` families each have their own theory. Every `.v` basename starts with its
package name and is unique among theories, examples and tests.

Tests mirror packages in `tests/<Package>/`.
Guides live in `docs/guide/`.

## Rocq style

Open each file with a documentation title, purpose, concrete example and `Builds on:` line.
Group imports by origin, starting with Stdlib, and keep imports outside modules and sections.
Use two-space indentation, lines of at most 100 columns and a final newline. Keep files under
1,500 lines and aim for 800. Put each constructor, field and match branch on its own line.

Comment each public theorem and contract definition. Use `Theorem` for public claims, `Lemma`
for helpers and `Local Lemma` for file-private helpers. Split long proofs into named lemmas, name
hypotheses by meaning, and use focused goals. Put `Proof.` and `Qed.` on separate lines. Do not
use `timeout`. Keep interactive commands and extraction directives out of theories and examples.

Dictionaries are explicit parametric records, and separate `Prop` records hold laws. Consumers
use public names and specification lemmas without unfolding another package's definitions.
See [guarantees](guarantees.md) for the proof policy.

## Costed code

The target cost discipline uses the following checklist.

- Define `f_c` once and define `f` as its `Cost.value` projection. Prove `f_equation`.
- Tick each recursion step, loop iteration and callback call. Charge nonconstant operations
  through costed calls or `tick_bits`, and use literal tick amounts.
- Give callback records costed fields and pure accessors. State their laws using pure accessors.
- Prove `f_cost` using named measures and constants, and add a `bigO` corollary.
- State amortised bounds as per-operation potential inequalities for persistent structures.
- Use `CostLoop.iterate` for binary-fuel loops and `fix_wf` for well-founded recursion.
- Account for key bits, preparation, callbacks and output in bounds.

## Tests

Rocq tests are `Example`s proved by `vm_compute`. Cover positive, negative and boundary cases.
Test costed algorithms on small fixtures that compute ticks. Use checked hand-written fixtures
when a test needs a result from another package. OCaml tests are inline expect tests.

## Commits

Write an imperative subject and a body that says what changed and why. Stage explicit paths.
