(** * Binomial and stale-entry accounting fixtures

    These observations exercise carrying, cached-code ties and repeated stale discards.
    For example, removing a decreased key leaves two obsolete entries for a later pop.
    Builds on: BaseHeapCost and BaseHeapBinomialCost. *)

From Stdlib Require Import List NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseHeapCost BaseHeapBinomial
  BaseHeapBinomialCost.
Import List.ListNotations.

Definition stale_queue :=
  Heap.push positive_encoding 10%positive 2%positive
    (Heap.push positive_encoding 1%positive 1%positive
      (Heap.push positive_encoding 5%positive 1%positive
        (Heap.push positive_encoding 9%positive 1%positive Heap.empty))).

Definition stale_after_live :=
  match Heap.pop positive_encoding stale_queue with
  | None => Heap.empty
  | Some (_, _, q) => q
  end.

Definition stale_after_discards :=
  match Heap.pop positive_encoding stale_after_live with
  | None => Heap.empty
  | Some (_, _, q) => q
  end.

Example heap_pending_before :
  (Heap.pending_count stale_queue, Heap.live_count stale_queue, Heap.stale stale_queue) =
    (4, 2, 2).
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_first_live :
  option_map (fun e => (fst (fst e), snd (fst e)))
    (Heap.pop positive_encoding stale_queue) = Some (1, 1)%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_pending_after_live :
  (Heap.pending_count stale_after_live, Heap.live_count stale_after_live,
    Heap.stale stale_after_live) = (3, 1, 2).
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_pop_discards_two :
  option_map (fun e => (fst (fst e), snd (fst e)))
    (Heap.pop positive_encoding stale_after_live) = Some (10, 2)%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_pending_after_discards :
  (Heap.pending_count stale_after_discards, Heap.live_count stale_after_discards,
    Heap.stale stale_after_discards) = (0, 0, 0).
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_live_pop_ticks :
  Cost.ticks (Heap.pop_c positive_encoding stale_queue) = 17%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_stale_pop_ticks :
  Cost.ticks (Heap.pop_c positive_encoding stale_after_live) = 37%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_later_empty_ticks :
  Cost.ticks (Heap.pop_c positive_encoding stale_after_discards) = 1%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_stale_potential_credit :
  N.leb
    (Cost.ticks (Heap.pop_c positive_encoding stale_after_live) +
      Heap.heap_potential 4 2 stale_after_discards)
    (Heap.heap_cost 4 2 + Heap.heap_potential 4 2 stale_after_live) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_empty_forest :
  HeapBinomial.remove_min ([] : HeapBinomial.heap positive) = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_cached_tie :
  HeapBinomial.precedesb ((5, 1, 2)%positive) ((5, 2, 1)%positive) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_ignored_push_ticks :
  Cost.ticks (Heap.push_c positive_encoding 10%positive 1%positive stale_queue) = 4%N.
Proof.
  vm_compute. reflexivity.
Qed.

Definition many_decreases :=
  List.fold_left
    (fun q n => Heap.push positive_encoding (Pos.of_nat (S (128 - n))) 1%positive q)
    (List.seq 0 128) Heap.empty.

Definition many_stale :=
  match Heap.pop positive_encoding many_decreases with
  | None => Heap.empty
  | Some (_, _, q) => q
  end.

Example heap_many_stale_count :
  (Heap.pending_count many_stale, Heap.live_count many_stale, Heap.stale many_stale) =
    (127, 0, 127).
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_pop_exceeds_operation_budget :
  N.ltb (Heap.heap_cost 128 1) (Cost.ticks (Heap.pop_c positive_encoding many_stale)) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_many_stale_ticks :
  Cost.ticks (Heap.pop_c positive_encoding many_stale) = 2192%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_many_stale_credit :
  N.leb (Cost.ticks (Heap.pop_c positive_encoding many_stale))
    (Heap.heap_cost 128 1 + Heap.heap_potential 128 1 many_stale) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_later_pop_below_operation_budget :
  N.ltb (Cost.ticks (Heap.pop_c positive_encoding (@Heap.empty positive)))
    (Heap.heap_cost 128 1) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_later_pop_credit :
  N.leb (Cost.ticks (Heap.pop_c positive_encoding (@Heap.empty positive)) +
    Heap.heap_potential 128 1 (@Heap.empty positive))
    (Heap.heap_cost 128 1 + Heap.heap_potential 128 1 (@Heap.empty positive)) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_operation_budget :
  HeapCost.heap_cost 128 1 = 1024%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example heap_many_stale_potential :
  HeapCost.heap_potential 128 1 many_stale = 65024%N.
Proof.
  vm_compute. reflexivity.
Qed.

Definition raw_counter_queue :=
  Heap.Queue [Some (HeapBinomial.Tree ((1, 1, 1)%positive) [])]
    (Map.set positive_encoding 1%positive 1%positive Map.empty) 99 1.

Example heap_raw_counter_removal :
  match Heap.pop positive_encoding raw_counter_queue with
  | None => false
  | Some (_, _, rest) =>
    match Heap.priority positive_encoding 1%positive rest with
    | None => true
    | Some _ => false
    end
  end = true.
Proof.
  vm_compute. reflexivity.
Qed.
