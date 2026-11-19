(** * Ground equational exactness

    The theorems of a ground specification, assembled from the files that prove their parts.
    [GroundSound.v] proves soundness from the exact model, and [GroundComplete.v] proves
    completeness from the model of the classes, which [GroundClasses.v] and
    [GroundSatisfies.v] build, and from the instances that [GroundBuild.v] builds. The parts
    share on purpose the plans that this module instantiates once.
    For example, [Ground] applied to Steensgaard's runner gives the theorems that its
    [solve_exact] reads.

    Builds on: the ground signature and the files of its parts. *)

From Galois.Egglog Require Import ValueSig IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import LowerSig RunnerSig CongruenceRefSig GroundSig GroundSound
  GroundClasses GroundBuild GroundSatisfies GroundComplete.

Module Ground (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R) (F : RUNNER_FACTS V I J D R X) (LW : LOWER_LAWS)
    (CR : CONGRUENCE_REF V) <: GROUND V I J D R X.
  Module Denote := GroundDenote V LW.
  Module Classes := GroundClasses V I J D R X F LW.
  Module Build := GroundBuild V I J D R X F LW.
  Module Satisfies := GroundSatisfies V I J D R X F Classes Build.
  Module SoundLaws := GroundSound V I J D R X F LW CR.
  Module CompleteLaws := GroundComplete V I J D R X F LW Denote Classes Satisfies Build.
  Include SoundLaws.
  Include CompleteLaws.
End Ground.
