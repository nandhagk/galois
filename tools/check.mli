open Core

(** Audits authored Rocq sources under the repository root, defaulting to the working directory.
    Claims are replayed using the pinned Rocq executable and built dependency load paths.
    New and legacy sources have separate package inventories and basename namespaces.
    New layout checks include Domains/Memory and the supported Examples client test mirrors.
    A theorem's Float axiom allowance requires an explicit import from Galois.Float or
    GaloisLegacy.Float. A Float package path alone grants no allowance.
    Layout checks warn when a new Rocq file exceeds 1,500 lines.
    [GALOIS_CHECK_JOBS] selects one or two claims workers and defaults to two. Invalid values
    fail when claims are requested; other checks ignore the setting.
    Import hygiene requires the pinned Stdlib sources available through ROCQPATH.
    Computational declarations in new theories and examples also receive cost-erasure lint.
    Proofs and Prop laws may observe counts.
    The [extraction] subcommand preserves the four-artifact legacy inventory. The
    [cost-extraction] subcommand inspects nonempty lists of new generated artifacts.
    Both reject the exact cost-observation sentinel. Their Dune aliases require successful
    compilation of the corresponding generated libraries. *)
val command : Command.t
