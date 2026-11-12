# Agent instructions

Galois is a Rocq library of verified program analyses. Read `README.md`,
`docs/architecture.md`, `docs/workflow.md` and the design in `docs/design/` before working.

## Skills

Before editing a matching file, read the skill and the references it requires, and apply it to
every line you change. This file and `docs/workflow.md` take precedence over a skill.

| Files | Skill |
| --- | --- |
| `*.v` | `.agents/skills/rocq/SKILL.md` |
| `*.ml`, `*.mli`, `dune`, `dune-project` | `.agents/skills/ocaml/SKILL.md` |
| `justfile`, `*.just` | `.agents/skills/just/SKILL.md` |

## Design invariants

- Component signatures in `FooSig.v` separate operations, functional laws, time contracts and
  proof plans. An optional specification layer contains derived definitions.
- Implementations in `Foo.v` use `FooCode`, `Foo` and `FooT` modules in an `Include` chain.
  Dependencies are explicit module parameters, and code modules require operations only.
- Declare data types at top level. Records contain no closures. Pass callbacks as arguments or
  module parameters.
- Use transparent ascription `<:`. Name each functor application before passing it as an argument.
- Use `From`-qualified `Require` commands. File basenames need no package prefix.
- Use Argent to derive time functions and state cost contracts. Consumers use public interfaces.
- Mark unfinished proofs with `CONVERT`, `STUB`, `SIG-QUESTION`, `PLAN-DEFECT` or `OPEN` as
  applicable. Mark placeholder code with `STUB-CODE`. See `docs/design/rules.md` for their forms.

## Work and verification

- Use `just` inside `nix develop` for every build, test, check and format. Never run `dune`
  directly and never edit `_build/`. All builds share the 10 GB `galois.slice`; there is no build
  lock.
- Use `just vo FILE` to build one Rocq file. Use `just session-check` for formatting, theories,
  Rocq tests, examples, lint and frozen files. Use `just admits` to report unfinished proofs and
  `just audit` to check assumptions.
- Rocq tests are `Example`s in `tests/`, checked by `vm_compute`. OCaml tests are inline expect
  tests at the bottom of the module's own `.ml`.
- Work on your own branch. Stage and commit explicit paths. Never rewrite
  `main`, force-push or push to `origin`.
- Do not use Python.
