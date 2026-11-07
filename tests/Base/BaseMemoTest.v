(** * Memo-cache fixtures

    Hits retain cached results and misses extend the cache.
    For example, repeated input keys compute the same list as the reference function.
    Builds on: BaseMemo and BaseEncoding. *)

From Stdlib Require Import List NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseMemo.
Import List.ListNotations.

Definition memo_result := Memo.get_or nat_encoding S 2 Memo.empty.

Example memo_miss : fst memo_result = 3.
Proof.
  vm_compute. reflexivity.
Qed.

Example memo_hit :
  Memo.get_or nat_encoding S 2 (snd memo_result) = (3, snd memo_result).
Proof.
  vm_compute. reflexivity.
Qed.

Example memo_other_absent : Map.get nat_encoding 1 (snd memo_result) = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example memo_empty_list :
  fst (Memo.map_memo nat_encoding S [] Memo.empty) = [].
Proof.
  vm_compute. reflexivity.
Qed.

Example memo_list : fst (Memo.map_memo nat_encoding S [2; 1; 2] Memo.empty) = [3; 2; 3].
Proof.
  vm_compute. reflexivity.
Qed.

Example memo_charged_callback :
  Cost.ticks (Memo.get_or_c nat_encoding (Cost.lift (fun _ => 100%N) S) 2 Memo.empty) =
    105%N.
Proof.
  vm_compute. reflexivity.
Qed.
