(** * Equality saturation, proved

    The theorems of equality saturation, assembled from the files that prove their parts.
    [RewriteSound.v] proves the soundness theorems, and [RewriteClosed.v] proves closure under
    rewrite steps. The parts share on purpose the plans of [RewriteTerms.v] and
    [RewriteMatch.v], which this module instantiates.
    For example, [Rewrite] applied to the arithmetic runner of the tests gives [equal_sound]
    for the folding rules.

    Builds on: the rewrite signature and the files of its parts. *)

From Galois.Egglog Require Import ValueSig IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import LowerSig RunnerSig RewriteSig RewriteTerms RewriteSound
  RewriteMatch RewriteClosed.

Module Rewrite (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R) (F : RUNNER_FACTS V I J D R X) (LW : LOWER_LAWS)
    <: REWRITE V I J D R X.
  Module Terms := RewriteTerms V I J D R X.
  Module Match := RewriteMatch V I J D R X.
  Module SoundLaws := RewriteSound V I J D R X F LW Terms.
  Module ClosedLaws := RewriteClosed V I J D R X F LW Terms Match.
  Include SoundLaws.
  Include ClosedLaws.
End Rewrite.
