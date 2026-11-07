(** * Dense slot map observations

    These examples check direct IDs, prepared keys and abstract conversions.
    For example, unknown keys cannot create a slot outside the interned universe.
    Builds on: BaseSlot and BaseIntern. *)

From Stdlib Require Import NArith List.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseIntern BaseSlot.
Import List.ListNotations.

Definition universe := Intern.of_list positive_encoding [13%positive; 2%positive].
Definition slots := Slot.of_list [(1%positive, 130); (2%positive, 20)].
Definition abstract := Map.of_list positive_encoding
  [(13%positive, 130); (2%positive, 20); (3%positive, 30)].

Example direct_ids :
  (Slot.get 1 slots, Slot.get 2 slots, Slot.get 3 slots) = (Some 130, Some 20, None).
Proof.
  vm_compute. reflexivity.
Qed.

Example prepared_lookup :
  (Slot.prepare_slot positive_encoding universe 13%positive,
    Slot.lookup positive_encoding universe slots 13%positive) = (Some 1%positive, Some 130).
Proof.
  vm_compute. reflexivity.
Qed.

Example outside_rejected :
  (Slot.lookup positive_encoding universe slots 3%positive,
    Slot.update positive_encoding universe slots 3%positive 30) = (None, None).
Proof.
  vm_compute. reflexivity.
Qed.

Example prepared_update :
  option_map (Slot.get 1) (Slot.update positive_encoding universe slots 13%positive 131) =
    Some (Some 131).
Proof.
  vm_compute. reflexivity.
Qed.

Example remove_slot : Slot.get 1 (Slot.remove 1 slots) = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example slot_enumeration : Slot.elements slots = [(2%positive, 20); (1%positive, 130)].
Proof.
  vm_compute. reflexivity.
Qed.

Example abstract_conversion :
  Map.elements (Slot.to_map positive_encoding universe slots) =
    [(2%positive, 20); (13%positive, 130)].
Proof.
  vm_compute. reflexivity.
Qed.

Example abstract_projection :
  Slot.of_map positive_encoding universe abstract = slots.
Proof.
  vm_compute. reflexivity.
Qed.

Example batch_preparation :
  Slot.read_slots slots (Slot.prepare_slots positive_encoding universe
    [2%positive; 3%positive; 13%positive]) = [Some 20; None; Some 130].
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_slots : Slot.elements (@Slot.empty nat) = [].
Proof.
  vm_compute. reflexivity.
Qed.

Example direct_bit_costs :
  (Cost.ticks (Slot.get_c 13 slots), Cost.ticks (Slot.set_c 13 131 slots),
    Cost.ticks (Slot.remove_c 13 slots)) = (4%N, 4%N, 4%N).
Proof.
  vm_compute. reflexivity.
Qed.
