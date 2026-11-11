(** * Changed-key queue invariant clients

    These clients use the public queue laws on actual finite pending sets.
    For example, inserting and popping key one returns a coherent empty worklist.
    Builds on: FrameworkTabQueue. *)

From Stdlib Require Import List PArith.
From Galois.Base Require Import BaseEncoding BaseSet.
From Galois.Framework Require Import FrameworkTabQueue.
Import List.ListNotations.

Example inserted_key_is_queued :
  TabQueue.coherent positive_encoding [1%positive]
    (FinSet.add positive_encoding 1%positive FinSet.empty).
Proof.
  apply TabQueue.insert_coherent.
  - exact positive_encoding_laws.
  - apply TabQueue.empty_coherent.
  - apply FinSet.mem_empty.
Qed.

Example popped_key_is_not_stale :
  TabQueue.coherent positive_encoding []
    (FinSet.remove positive_encoding 1%positive
      (FinSet.add positive_encoding 1%positive FinSet.empty)).
Proof.
  apply TabQueue.pop_coherent.
  - exact positive_encoding_laws.
  - exact inserted_key_is_queued.
Qed.

Example duplicate_work_is_not_coherent pending :
  ~ TabQueue.coherent positive_encoding [1%positive; 1%positive] pending.
Proof.
  intros [Hwf [Hnodup Hmembers]].
  inversion Hnodup as [|key rest Hnot Htail]; subst key rest.
  apply Hnot; left; reflexivity.
Qed.
