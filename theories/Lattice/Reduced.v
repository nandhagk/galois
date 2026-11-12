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

Module Reduced (A B : BLATTICE) (R : REDUCER A B) <: BLATTICE.
  Include ReducedCode A B R.
  Lemma leb_refl : forall a, leb a a = true.
  Proof. Admitted.
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof. Admitted.
  Lemma bot_least : forall a, leb bot a = true.
  Proof. Admitted.
  Lemma is_bot_bot : is_bot bot = true.
  Proof. Admitted.
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof. Admitted.
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof. Admitted.
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof. Admitted.
  Lemma top_greatest : forall a, leb a top = true.
  Proof. Admitted.
  Lemma meet_lb_l : forall a b, leb (meet a b) a = true.
  Proof. Admitted.
  Lemma meet_lb_r : forall a b, leb (meet a b) b = true.
  Proof. Admitted.
End Reduced.
