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
  Cost.ticks (Intern.intern_c nat_encoding 0 Intern.empty) = 9%N.
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

(** The empty allocation frontier is one and its size is zero. *)
Example intern_empty_frontier_size :
  (Pos.to_nat (Intern.next (@Intern.empty nat)), Intern.size (@Intern.empty nat)) = (1, 0).
Proof.
  vm_compute. reflexivity.
Qed.

(** Repeated keys leave the frontier exactly one past the count of distinct allocations. *)
Example intern_repeated_frontier_size :
  (Pos.to_nat (Intern.next interned), S (Intern.size interned)) = (3, 3).
Proof.
  vm_compute. reflexivity.
Qed.

(** The final allocated ID is in the size domain, while the frontier and its successor are outside. *)
Example intern_size_domain_boundary :
  (Nat.leb (Pos.to_nat 2%positive) (Intern.size interned),
    Nat.leb (Pos.to_nat (Intern.next interned)) (Intern.size interned),
    Nat.leb (Pos.to_nat (Pos.succ (Intern.next interned))) (Intern.size interned)) =
    (true, false, false).
Proof.
  vm_compute. reflexivity.
Qed.

(** A client of an arbitrary well-formed interner uses the size bridges without unfolding it. *)
Example intern_symbolic_size_client {K} (E : encoding K) (HE : encoding_laws E)
    (s : Intern.t K) i :
  Intern.wf E s ->
  Pos.to_nat (Intern.next s) = S (Intern.size s) /\
  (Pos.to_nat i <= Intern.size s <-> exists k, Intern.find E k s = Some i).
Proof.
  intro Hwf. split.
  - exact (Intern.next_size E HE s Hwf).
  - exact (Intern.ids_size E HE i s Hwf).
Qed.
