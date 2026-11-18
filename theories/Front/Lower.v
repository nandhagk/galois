(** * Lowering laws

    The laws of the lowering, assembled from the files that prove their parts.
    [LowerValues] and [LowerModels] relate patterns to their values, meanings and represented
    terms. [LowerComplete], [LowerSound] and [LowerValid] prove the laws about whole programs
    from them, and the soundness and validity proofs share the plan [LowerScopes] on purpose,
    because both read how a rule scopes its variables.
    For example, [LowerLaws.lower_sound] and [LowerLaws.lower_complete] together say that the
    lowered program of a relational specification derives exactly its derived rows.

    Builds on: the lowering signature and the files of its parts. *)

From Galois.Front Require Import LowerSig LowerValues LowerModels LowerScopes LowerComplete
  LowerSound LowerValid.

Module CompleteLaws := LowerComplete LowerValues.

Module SoundLaws := LowerSound LowerValues LowerScopes.

Module ValidLaws := LowerValid LowerValues LowerModels LowerScopes.

Module LowerLaws <: LOWER_LAWS.
  Include LowerValues.
  Include LowerModels.
  Include CompleteLaws.
  Include SoundLaws.
  Include ValidLaws.
End LowerLaws.
