(** * Live priority-queue fixtures

    These fixtures distinguish numeric code ties, strict decreases and empty pop.
    For example, equal-priority codes one and two pop in that numeric order.
    Builds on: BaseHeap and BaseEncoding. *)

From Stdlib Require Import List NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseHeap.
Import List.ListNotations.

Definition queued := Heap.push positive_encoding 5%positive 2%positive
  (Heap.push positive_encoding 5%positive 1%positive Heap.empty).

Example heap_tie :
  option_map (fun e => (fst (fst e), snd (fst e))) (Heap.pop positive_encoding queued) =
    Some (5, 1)%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_decrease :
  Heap.priority positive_encoding 2%positive
    (Heap.push positive_encoding 3%positive 2%positive queued) = Some 3%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_increase_ignored :
  Heap.push positive_encoding 9%positive 1%positive queued = queued.
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_empty : Heap.pop positive_encoding (@Heap.empty positive) = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_push_ticks :
  Cost.ticks (Heap.push_c positive_encoding 1%positive 1%positive Heap.empty) = 6%N.
Proof.
  vm_compute. reflexivity.
Qed.
