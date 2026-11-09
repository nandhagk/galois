(** * Footprint index examples

    These examples inspect the ranges stored at a site after writes.
    For example, adjacent writes merge without affecting another site.
    Builds on: DomainsFootprint. *)

From Stdlib Require Import List ZArith NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Domains.Memory Require Import DomainsFootprint.
Import List.ListNotations.
Local Open Scope Z_scope.

Definition footprint_test_encoding := codec_enc positive_codec.

Definition footprint_test_index : footprint_index positive :=
  footprint_add footprint_test_encoding (Footprint 1%positive 2 5)
    (footprint_add footprint_test_encoding (Footprint 1%positive 0 2) Map.empty).

Example footprint_adjacent_writes :
  footprint_lookup footprint_test_encoding 1%positive footprint_test_index = [(0, 5)].
Proof.
  vm_compute. reflexivity.
Qed.

Example footprint_other_site_empty :
  footprint_lookup footprint_test_encoding 2%positive footprint_test_index = [].
Proof.
  vm_compute. reflexivity.
Qed.

Example footprint_empty_write :
  footprint_lookup footprint_test_encoding 1%positive
    (footprint_add footprint_test_encoding (Footprint 1%positive 3 3) Map.empty) = [].
Proof.
  vm_compute. reflexivity.
Qed.

Example footprint_remove_splits :
  footprint_lookup footprint_test_encoding 1%positive
    (footprint_remove footprint_test_encoding (Footprint 1%positive 1 4)
      footprint_test_index) = [(0, 1); (4, 5)].
Proof.
  vm_compute. reflexivity.
Qed.

(** The charged write path has a nonzero cost on this concrete index. *)
Example footprint_add_ticks_positive :
  (0 < Cost.ticks
    (footprint_add_c footprint_test_encoding (Footprint 1%positive 5 7)
      footprint_test_index))%N.
Proof.
  vm_compute. reflexivity.
Qed.

(** The charged removal path has a nonzero cost on this concrete index. *)
Example footprint_remove_ticks_positive :
  (0 < Cost.ticks
    (footprint_remove_c footprint_test_encoding (Footprint 1%positive 1 4)
      footprint_test_index))%N.
Proof.
  vm_compute. reflexivity.
Qed.
