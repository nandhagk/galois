(** * Independent small-width reduction oracle

    This test enumerates every mask and endpoint pair at widths two and three.
    For example, it computes the least component hull by joining all feasible concrete words.
    Builds on: DomainsSignedBounds and public mask joins. *)

From Stdlib Require Import ZArith List Bool.
From Galois.Bits Require Import BitsWord.
From Galois.Domains Require Import DomainsTnum DomainsSignedBounds.
Import List.ListNotations.

Local Open Scope Z_scope.

Definition sb_oracle_words (w : width) : list Z :=
  map Z.of_nat (seq 0 (Z.to_nat (modulus w))).

Definition sb_oracle_feasible (w : width) (s : bool) (t : tnum) (lo hi z : Z) : bool :=
  Bool.eqb (msb w z) s && (Z.land z (wrap w (zeros t)) =? 0) &&
    (Z.land (wrap w (ones t)) (Z.lnot z) =? 0) && (lo <=? z) && (z <=? hi).

Definition sb_oracle_reference (w : width) (s : bool) (t : tnum) (lo hi : Z) : sb_half :=
  match filter (sb_oracle_feasible w s t lo hi) (sb_oracle_words w) with
  | [] => SBEmpty
  | z :: rest =>
    SBRange (fold_left (fun acc x => tnum_join w acc (tnum_const w x)) rest (tnum_const w z))
      (fold_left Z.min rest z) (fold_left Z.max rest z)
  end.

Definition sb_oracle_half_eqb (a b : sb_half) : bool :=
  match a, b with
  | SBEmpty, SBEmpty => true
  | SBRange ta la ua, SBRange tb lb ub =>
    (zeros ta =? zeros tb) && (ones ta =? ones tb) && (la =? lb) && (ua =? ub)
  | _, _ => false
  end.

Definition sb_oracle_exhaustive (w : width) : bool :=
  let words := sb_oracle_words w in
  forallb (fun zeros => forallb (fun ones => forallb (fun lo => forallb (fun hi =>
    forallb (fun s => sb_oracle_half_eqb (sb_reduce_half w s (SBRange (Tnum zeros ones) lo hi))
      (sb_oracle_reference w s (Tnum zeros ones) lo hi)) [false; true]) words) words) words) words.

Example sb_word_exhaustive_width_two : sb_oracle_exhaustive 2%positive = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example sb_word_exhaustive_width_three : sb_oracle_exhaustive 3%positive = true.
Proof.
  vm_compute. reflexivity.
Qed.
