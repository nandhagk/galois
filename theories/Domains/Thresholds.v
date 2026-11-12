(** * Threshold trees

    Threshold trees store sorted distinct integers and search for nearby bounds.
    For example, the least threshold above four in [0; 8] is eight.
    Builds on: ThresholdsSig. *)

From Stdlib Require Import List ZArith Arith.
From Galois.Domains Require Import ThresholdsSig.
Import List.ListNotations.

Module ThresholdsCode <: THRESHOLDS_OPS.
  Fixpoint insert (z : Z) (xs : list Z) : list Z :=
    match xs with
    | [] => [z]
    | x :: rest =>
      if Z.eqb z x then xs
      else if Z.ltb z x then z :: xs else x :: insert z rest
    end.

  Fixpoint sort (xs : list Z) : list Z :=
    match xs with
    | [] => []
    | x :: rest => insert x (sort rest)
    end.

  Fixpoint build (fuel : nat) (xs : list Z) : ttree :=
    match fuel with
    | 0 => TLeaf
    | S fuel =>
      let middle := length xs / 2 in
      match skipn middle xs with
      | [] => TLeaf
      | x :: rhs => TNode (build fuel (firstn middle xs)) x (build fuel rhs)
      end
    end.

  Definition make (xs : list Z) : ttree :=
    let sorted := sort xs in build (length sorted) sorted.

  Fixpoint below (tree : ttree) (z : Z) : option Z :=
    match tree with
    | TLeaf => None
    | TNode lhs value rhs =>
      if Z.leb value z then
        match below rhs z with
        | Some x => Some (Z.max value x)
        | None => Some value
        end
      else below lhs z
    end.

  Fixpoint above (tree : ttree) (z : Z) : option Z :=
    match tree with
    | TLeaf => None
    | TNode lhs value rhs =>
      if Z.leb z value then
        match above lhs z with
        | Some x => Some (Z.min value x)
        | None => Some value
        end
      else above rhs z
    end.
End ThresholdsCode.
