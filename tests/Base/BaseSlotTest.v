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

(** The physical code deliberately differs from the positive key stored beside the value. *)
Definition malformed_abstract : Map.t positive nat :=
  Map.set_code 1%positive 13%positive 130 Map.empty.

Definition conversion_control : Map.t positive nat :=
  Map.set positive_encoding 13%positive 130 Map.empty.

Example malformed_conversion_observes_stored_key :
  let converted := Slot.of_map positive_encoding universe malformed_abstract in
  (Map.get positive_encoding 13%positive malformed_abstract,
    Slot.lookup positive_encoding universe converted 13%positive,
    Slot.elements converted, Intern.size universe) =
    (None, Some 130, [(1%positive, 130)], 2%nat).
Proof.
  vm_compute. reflexivity.
Qed.

Example conversion_universe_wf : Intern.wf positive_encoding universe.
Proof.
  apply (Intern.wf_of_list positive_encoding positive_encoding_laws).
Qed.

(** Numeric output validity does not require well-formedness of the malformed abstract map. *)
Example malformed_conversion_is_valid :
  Slot.valid universe (Slot.of_map positive_encoding universe malformed_abstract).
Proof.
  apply (Slot.slot_of_map_valid positive_encoding positive_encoding_laws).
  exact conversion_universe_wf.
Qed.

Example conversion_control_wf : Map.wf positive_encoding conversion_control.
Proof.
  apply Map.wf_set. apply Map.wf_empty.
Qed.

Example conversion_control_lookup_spec :
  Slot.lookup positive_encoding universe
    (Slot.of_map positive_encoding universe conversion_control) 13%positive =
    Map.get positive_encoding 13%positive conversion_control.
Proof.
  rewrite (Slot.slot_of_map_lookup positive_encoding positive_encoding_laws)
    by (try exact conversion_universe_wf; exact conversion_control_wf).
  vm_compute. reflexivity.
Qed.

Example conversion_control_lookup :
  let converted := Slot.of_map positive_encoding universe conversion_control in
  (Map.get positive_encoding 13%positive conversion_control,
    Slot.lookup positive_encoding universe converted 13%positive) = (Some 130, Some 130).
Proof.
  vm_compute. reflexivity.
Qed.

Example conversion_control_round_trip :
  Slot.to_map positive_encoding universe
    (Slot.of_map positive_encoding universe conversion_control) = conversion_control.
Proof.
  vm_compute. reflexivity.
Qed.

Example conversion_control_refines :
  Slot.refines positive_encoding universe
    (Slot.of_map positive_encoding universe conversion_control) conversion_control.
Proof.
  pose proof (Slot.slot_to_map_refines positive_encoding positive_encoding_laws universe
    (Slot.of_map positive_encoding universe conversion_control) conversion_universe_wf
    (Slot.slot_of_map_valid positive_encoding positive_encoding_laws universe
      conversion_control conversion_universe_wf)) as Hrefines.
  now rewrite conversion_control_round_trip in Hrefines.
Qed.
