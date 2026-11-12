(** * Reduced products

    A descending reducer normalises comparisons and joins while widening stays unreduced.
    For example, a boolean reducer can clear the second slot when the first is false.
    Builds on: LatticeSig and Argent time interfaces. *)

From Stdlib Require Import Bool Arith NArith Lia.
From Argent Require Import Time.
From Galois.Lattice Require Import LatticeSig.

Module ReducedCode (A B : BLATTICE_OPS) (R : REDUCER_OPS A B) <: BLATTICE_OPS.
  Definition t := (A.t * B.t)%type.
  Definition leb (x y : t) :=
    let r := R.reduce x in andb (A.leb (fst r) (fst y)) (B.leb (snd r) (snd y)).
  Definition bot : t := (A.bot, B.bot).
  Definition is_bot (x : t) := andb (A.is_bot (fst x)) (B.is_bot (snd x)).
  Definition join (x y : t) := R.reduce (A.join (fst x) (fst y), B.join (snd x) (snd y)).
  Definition top : t := (A.top, B.top).
  Definition meet (x y : t) : t := (A.meet (fst x) (fst y), B.meet (snd x) (snd y)).
End ReducedCode.
