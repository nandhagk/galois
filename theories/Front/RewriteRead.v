(** * Rewrites that read derived rows and lattice values, proved

    The theorems of rewrites that read rows, assembled from the files that prove their parts.
    [RewriteReadHeads.v] and [RewriteReadModel.v] build the model of the relations,
    [RewriteReadSound.v] proves that stored rows and values are sound, [RewriteReadValues.v]
    and [RewriteReadSorts.v] read the premises and the right side of a rewrite step,
    [RewriteReadClosed.v] proves closure under steps that read the outcome, and
    [RewriteReadRows.v] proves that derived rows are stored and closure under steps that read
    them. This module instantiates the plans that the parts share.

    For example, [RewriteRead] applied to a runner of constant propagation with rewrites says
    that a saturated outcome joins every term with its rewrites by known constants.

    Builds on: the signature of rewrites that read rows and the files of its parts. *)

From Galois.Egglog Require Import ValueSig IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import LowerSig RunnerSig LatticeReadQueries RewriteTerms RewriteMatch
  RewriteReadSig RewriteReadHeads RewriteReadModel RewriteReadSound RewriteReadValues
  RewriteReadSorts RewriteReadClosed RewriteReadRows.

Module RewriteRead (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R) (F : RUNNER_FACTS V I J D R X) (LW : LOWER_LAWS)
    (PS : LOWER_PLAN) <: REWRITE_READ V I J D R X.
  Module Terms := RewriteTerms V I J D R X.
  Module Match := RewriteMatch V I J D R X.
  Module Queries := LatticeReadQueries LW.
  Module ValuePlan := RewriteReadModel V PS RewriteReadHeads.
  Module Sides := RewriteReadSorts V.
  Module SoundLaws := RewriteReadSound V I J D R X F LW Terms ValuePlan.
  Module ClosedLaws :=
    RewriteReadClosed V I J D R X F LW Queries Terms Match RewriteReadValues Sides.
  Module RowLaws := RewriteReadRows V I J D R X F LW Terms ClosedLaws.
  Include SoundLaws.
  Include ClosedLaws.
  Include RowLaws.
End RewriteRead.
