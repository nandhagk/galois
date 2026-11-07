The redesigned library lives in `theories/<Package>/` under the logical root
`Galois.<Package>`. Each package declares its own `rocq.theory`, and every Rocq basename starts
with its package name. The `Analyses` families have separate theories under
`Analyses/<Family>/`, and stage-5 extensions live under `Next/<Extension>/`. The reference
library stays in `legacy/theories/` under `GaloisLegacy` during the migration.
