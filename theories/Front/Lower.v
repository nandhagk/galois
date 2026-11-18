(** * Lowering laws

    The laws of the lowering, assembled from the files that prove their parts.
    [LowerQueries] and [LowerBuilds] relate patterns to their values, [LowerModels] relates
    them to their meanings and represented terms, and [LowerBodies] relates bodies to their
    premises. [LowerComplete], [LowerSound] and [LowerValid] prove the laws about whole
    programs from them, and the soundness and validity proofs share the plan of [LowerKinds]
    and [LowerScopes] on purpose, because both read how a rule scopes its variables.
    For example, [LowerLaws.lower_sound] and [LowerLaws.lower_complete] together say that the
    lowered program of a relational specification derives exactly its derived rows.

    Builds on: the lowering signature and the files of its parts. *)

From Galois.Front Require Import LowerSig LowerQueries LowerBuilds LowerModels LowerBodies
  LowerKinds LowerScopes LowerComplete LowerSound LowerValid.

Module LowerValues <: LOWER_VALUES.
  Include LowerQueries.
  Include LowerBuilds.
End LowerValues.

Module LowerPlan <: LOWER_PLAN.
  Include LowerKinds.
  Include LowerScopes.
End LowerPlan.

Module CompleteLaws := LowerComplete LowerValues LowerBodies.

Module SoundLaws := LowerSound LowerValues LowerPlan.

Module ValidLaws := LowerValid LowerValues LowerModels LowerPlan.

Module LowerLaws <: LOWER_LAWS.
  Include LowerValues.
  Include LowerModels.
  Include LowerBodies.
  Include CompleteLaws.
  Include SoundLaws.
  Include ValidLaws.
End LowerLaws.
