(** * Live priority-queue fixtures

    These fixtures distinguish numeric code ties, strict decreases and empty pop.
    For example, equal-priority codes one and two pop in that numeric order.
    Builds on: Heap and Key. *)

From Stdlib Require Import List NArith.
From Galois.Base Require Import Trie Heap.
Import List.ListNotations.

Definition queued := HeapCode.push 5%N 2%positive
  (HeapCode.push 5%N 1%positive HeapCode.empty).

Example heap_tie :
  option_map (fun e => let '(p, k, _) := e in (p, k)) (HeapCode.pop queued) =
    Some (5%N, 1%positive).
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_decrease :
  PTrieCode.get 2%positive (live
    (HeapCode.push 3%N 2%positive queued)) = Some 3%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_increase_ignored :
  HeapCode.push 9%N 1%positive queued = queued.
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_empty : HeapCode.pop HeapCode.empty = None.
Proof.
  vm_compute. reflexivity.
Qed.

(* BaseHeapTest.heap_push_ticks retires with Cost.ticks. Heap priorities now use N.
   heap_tie and heap_decrease retain the old numeric priorities 5 and 3 through
   that carrier change. priority reads the public live map in heap_decrease. *)
