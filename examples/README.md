Reference clients live in `Tutorial/`, `While/`, `Ssa/`, `SsaValues/`, `SsaMemory/`,
`SsaLoops/` and `SsaFloat/`. Their theories use the logical root `Galois.Examples`, and their
Rocq basenames start with `Examples`. Clients exercise the redesigned library through its public
interfaces. The old clients stay in `legacy/examples/` during the migration.
