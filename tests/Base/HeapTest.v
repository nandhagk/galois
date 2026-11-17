(** * Live priority-queue fixtures

    These fixtures distinguish numeric code ties, strict decreases and empty pop.
    For example, equal-priority codes one and two pop in that numeric order.
    Builds on: Heap and Key.

    Groups:
    - PopTests: which entry pop returns, and what an empty heap gives.
    - PushTests: how a later push changes the priority of an entry.
    - EntryTests: the order in which the entries of a heap are listed. *)

From Stdlib Require Import List NArith.
From Galois.Base Require Import Trie Heap.
Import List.ListNotations.

(** * Fixtures *)

(** Two entries of priority 5, pushed with codes 1 and then 2. *)
Definition queued := HeapCode.push 5%N 2%positive
  (HeapCode.push 5%N 1%positive HeapCode.empty).

(** * Pop *)

Module PopTests.

  (** Among equal priorities, pop returns the entry with the smaller code. *)
  Example equal_priority_pops_smaller_code :
    option_map (fun e => let '(p, k, _) := e in (p, k)) (HeapCode.pop queued) =
      Some (5%N, 1%positive).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Popping an empty heap gives no entry. *)
  Example empty_heap_pops_none : HeapCode.pop HeapCode.empty = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

End PopTests.

(** * Push *)

Module PushTests.

  (** A push with a lower priority lowers the priority of the entry. *)
  Example lower_priority_replaces_entry :
    PTrieCode.get 2%positive (live
      (HeapCode.push 3%N 2%positive queued)) = Some 3%N.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A push with a higher priority leaves the heap unchanged. *)
  Example higher_priority_push_is_ignored :
    HeapCode.push 9%N 1%positive queued = queued.
  Proof.
    vm_compute. reflexivity.
  Qed.

End PushTests.

(** * Entries *)

Module EntryTests.

  (** Heap entries are listed in tree traversal order, skipping empty slots. *)
  Example entries_follow_tree_order :
    heap_entries [Some (HeapTree (1%N, 1%positive)
      [HeapTree (2%N, 2%positive) [HeapTree (3%N, 3%positive) []];
        HeapTree (4%N, 4%positive) []]); None;
      Some (HeapTree (5%N, 5%positive) [])] =
    [(1%N, 1%positive); (2%N, 2%positive); (3%N, 3%positive);
      (4%N, 4%positive); (5%N, 5%positive)].
  Proof.
    vm_compute. reflexivity.
  Qed.

End EntryTests.

(* BaseHeapTest.heap_push_ticks retires with Cost.ticks. Heap priorities now use N.
   heap_tie and heap_decrease retain the old numeric priorities 5 and 3 through
   that carrier change. priority reads the public live map in heap_decrease. *)
