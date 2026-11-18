(** * Lattice tables, proved

    The theorems of lattice tables, assembled from the files that prove their parts.
    [LatticeSound.v] proves that a stored value is a merge of assigned values, and
    [LatticeComplete.v] proves that a saturated outcome stores each assigned value below it.
    Each part instantiates its own plan, [Model] or [Assign].
    For example, [Lattice] applied to a runner of upper bounds says that a saturated run stores
    exactly the maximum of the derived bounds.

    Builds on: the lattice signature and the files of its parts. *)

From Galois.Egglog Require Import ValueSig IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import LowerSig RunnerSig LatticeSig LatticeSound LatticeComplete.

Module Lattice (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R) (F : RUNNER_FACTS V I J D R X) (LW : LOWER_LAWS)
    (PS : LOWER_PLAN) <: LATTICE V I J D R X.
  Module SoundLaws := LatticeSound V I J D R X F LW PS.
  Module CompleteLaws := LatticeComplete V I J D R X F LW.
  Include SoundLaws.
  Include CompleteLaws.
End Lattice.
