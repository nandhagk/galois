(** * Datalog syntax and relation examples

    Grounding and valid relation operations compute on small tuples.
    For example, grounding a repeated variable repeats its assigned constant.
    Builds on: DatalogSyntax, DatalogRelation and LatticeSet. *)

From Stdlib Require Import List PArith.
From Galois.Base Require Import BaseSet.
From Galois.Lattice Require Import LatticeCore LatticeSet.
From Galois.Datalog Require Import DatalogSyntax DatalogRelation.
Import List.ListNotations.

Example ground_repeated_variable :
  ground (fun _ => 2%positive)
    (Atom true [TVar 0; TConst 1%positive; TVar 0]) =
  (true, [2%positive; 1%positive; 2%positive]).
Proof.
  vm_compute. reflexivity.
Qed.

Definition one_row := set_of_list tuple_encoding [[1%positive; 2%positive]].
Definition another_row := set_of_list tuple_encoding [[2%positive; 1%positive]].

Example relation_union_membership :
  (FinSet.mem tuple_encoding [1%positive; 2%positive]
      (set_raw (join relation_lattice one_row another_row)),
   FinSet.mem tuple_encoding [2%positive; 1%positive]
      (set_raw (join relation_lattice one_row another_row)),
   FinSet.mem tuple_encoding [1%positive; 1%positive]
      (set_raw (join relation_lattice one_row another_row))) = (true, true, false).
Proof.
  vm_compute. reflexivity.
Qed.
