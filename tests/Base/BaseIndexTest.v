(** * Stable bucket fixtures

    Grouping checks interleaved buckets, absent keys and empty input.
    For example, one bucket retains both its first and last input values.
    Builds on: BaseIndex and BaseEncoding. *)

From Stdlib Require Import List NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseIndex.
Import List.ListNotations.

Definition grouped := Index.group_by bool_encoding Nat.even [2; 1; 4; 3; 6].

Example index_order : Index.find bool_encoding true grouped = [2; 4; 6].
Proof.
  vm_compute. reflexivity.
Qed.

Example index_missing :
  Index.find bool_encoding false (Index.group_by bool_encoding Nat.even [2; 4]) = [].
Proof.
  vm_compute. reflexivity.
Qed.

Example index_empty :
  Index.find bool_encoding true (Index.group_by bool_encoding Nat.even []) = [].
Proof.
  vm_compute. reflexivity.
Qed.

Example index_ticks :
  Cost.ticks (Index.group_by_c bool_encoding
    (Cost.lift (fun _ => 1%N) Nat.even) []) = 0%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example index_singleton_ticks :
  Cost.ticks (Index.group_by_c bool_encoding
    (Cost.lift (fun _ => 1%N) Nat.even) [2]) = 11%N.
Proof.
  vm_compute. reflexivity.
Qed.
