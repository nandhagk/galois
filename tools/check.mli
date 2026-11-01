open Core

(** Audits authored Rocq sources under the repository root, defaulting to the working directory.
    Claims are replayed using the pinned Rocq executable and built dependency load paths.
    [GALOIS_CHECK_JOBS] selects one or two claims workers and defaults to two. Invalid values
    fail when claims are requested; other checks ignore the setting.
    Import hygiene requires the pinned Stdlib sources available through ROCQPATH.
    The [extraction] subcommand inspects the four generated artifacts supplied by Dune; its
    alias also requires successful compilation of the generated library. *)
val command : Command.t
