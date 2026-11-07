(** * Dense interning fixtures

    These fixtures cover reuse, reverse lookup and empty tables.
    For example, [2; 1; 2] uses exactly two IDs.
    Builds on: BaseIntern and BaseEncoding. *)

From Stdlib Require Import List NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseIntern.
Import List.ListNotations.

Definition interned := Intern.of_list nat_encoding [2; 1; 2].

Example intern_first : Intern.find nat_encoding 2 interned = Some 1%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example intern_reuse : Intern.size interned = 2.
Proof.
  vm_compute. reflexivity.
Qed.

Example intern_inverse : Intern.key_of 2%positive interned = Some 1.
Proof.
  vm_compute. reflexivity.
Qed.

Example intern_missing : Intern.find nat_encoding 3 interned = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example intern_empty : Intern.key_of 1%positive (@Intern.empty nat) = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example intern_ticks :
  Cost.ticks (Intern.intern_c nat_encoding 0 Intern.empty) = 6%N.
Proof.
  vm_compute. reflexivity.
Qed.

(** Reverse lookup reads back through forward lookup, while the frontier has no binding. *)
Example intern_reverse_forward :
  (match Intern.key_of 2%positive interned with
  | Some k => Intern.find nat_encoding k interned
  | None => None
  end, Intern.key_of 3%positive interned) = (Some 2%positive, None).
Proof.
  vm_compute. reflexivity.
Qed.

(** Public interner observations agree with the exposed forward and inverse map fields. *)
Example intern_map_observations :
  (Intern.find nat_encoding 1 interned, Intern.key_of 2%positive interned) =
    (Map.get nat_encoding 1 (Intern.table interned),
      Map.get positive_encoding 2%positive (Intern.inverse interned)).
Proof.
  vm_compute. reflexivity.
Qed.
