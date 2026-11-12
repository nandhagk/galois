(** * Reduced products

    A descending reducer normalises comparisons and joins while widening stays unreduced.
    For example, a boolean reducer can clear the second slot when the first is false.
    Builds on: LatticeSig and Argent time interfaces. *)

From Stdlib Require Import Bool Arith NArith Lia.
From Argent Require Import Time Std.
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

Module ReducedT (A B : BLATTICE_T) (R : REDUCER_T A B) <: BLATTICE_T.
  Include Reduced A B R.

  TimeFun leb.
  TimeFun is_bot.
  TimeFun join.
  TimeFun meet.

  Definition size (x : t) : nat := A.size (fst x) + B.size (snd x) + 1.
  Definition c_lat : N := 1. (* STUB *)

  Lemma T_leb_le : forall a b, (T_leb a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_join_le : forall a b, (T_join a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_is_bot_le : forall a, (T_is_bot a <= c_lat * N.of_nat (size a + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_meet_le : forall a b, (T_meet a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
End ReducedT.

Module ReducedHeight (A B : BLATTICE) (R : REDUCER A B)
    (P : LATTICE with Definition t := (A.t * B.t)%type
                  with Definition leb :=
                    (fun x y => andb (A.leb (fst x) (fst y)) (B.leb (snd x) (snd y))))
    (H : HEIGHT P)
    (Lat : BLATTICE with Definition t := (A.t * B.t)%type
                     with Definition leb :=
                       (fun x y => let r := R.reduce x in
                         andb (A.leb (fst r) (fst y)) (B.leb (snd r) (snd y))))
    <: HEIGHT Lat.
  Definition rank (x : Lat.t) := H.rank (R.reduce x).
  Definition height := H.height.

  Lemma rank_le : forall a, rank a <= height.
  Proof. intro a; apply H.rank_le. Qed.

  Lemma rank_strict : forall a b, Lat.leb a b = true -> Lat.leb b a = false ->
    rank a < rank b.
  Proof. Admitted. (* CONVERT: reduced_height: missing rank_monotone in HEIGHT *)
End ReducedHeight.
