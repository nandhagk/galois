# Agent instructions

Galois is a Rocq library of verified program analyses, being rebuilt as described in
`docs/architecture.md`. Read `README.md`, `docs/architecture.md` and `docs/workflow.md` before
working.

## Skills

Before editing a matching file, read the skill and the references it requires, and apply it to
every line you change. This file and `docs/workflow.md` take precedence over a skill.

| Files | Skill |
| --- | --- |
| `*.v` | `.agents/skills/rocq/SKILL.md` |
| `*.ml`, `*.mli`, `dune`, `dune-project` | `.agents/skills/ocaml/SKILL.md` |
| `justfile`, `*.just` | `.agents/skills/just/SKILL.md` |

## Design invariants

- Core packages depend only on the Rocq standard library. Only `Float` uses Flocq.
- Dictionaries are explicit records parametric in their types, with laws in separate `Prop`
  records. No typeclasses, instances, canonical structures or functors; modules are namespaces.
- Keys have injective encodings into `positive`, and preparation interns them to dense IDs. Maps
  and sets are canonical binary tries.
- Computational records hold data and functions; semantic links and laws are separate `Prop`
  records. Running an analysis needs no semantics and no termination proof.
- The core algorithms are written in the cost monad of `theories/Cost` and carry cost theorems,
  following `docs/guide/cost.md`.
- Consumers use other packages only through their public names and spec lemmas.
- Every `.v` basename is unique and starts with its package name. Theories contain no `Extract`
  directives.
- Every claim is proved. No axioms, `Admitted`, `admit`, `give_up` or unproved statement
  definitions. The one exception: a theorem whose file imports `Galois.Float` may depend on
  exactly the four approved axioms listed in `docs/guarantees.md`. The checker in `checker/` enforces this through `just check`.

## Work and verification

- Use `just` inside `nix develop` for every build, test, check and format. Never run `dune`
  directly and never edit `_build/`. All builds share the 10 GB `galois.slice`; there is no build
  lock.
- Rocq tests are `Example`s in `tests/`, checked by `vm_compute`. OCaml tests are inline expect
  tests at the bottom of the module's own `.ml`.
- Work on your own branch. Stage and commit explicit paths. Never rewrite
  `main`, force-push or push to `origin`.
- Do not use Python.
