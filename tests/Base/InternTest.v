(** * Dense interning fixtures

    These fixtures cover reuse, reverse lookup and empty tables.
    For example, [2; 1; 2] uses exactly two IDs.
    Builds on: Intern, Map and Key. *)

From Stdlib Require Import List NArith.
From Galois.Base Require Import Key Map Intern.
Import List.ListNotations.

Module NatMap := TrieMapCode NatKeyCode.
Module NatIntern := InternCode NatKeyCode NatMap.
Definition intern_list xs := fold_left (fun s k => snd (NatIntern.intern k s)) xs NatIntern.empty.
Definition interned := intern_list [2; 1; 2].

Example intern_first : NatIntern.find 2 interned = Some 1%positive.
Proof. vm_compute. reflexivity. Qed.
Example intern_reuse : NatIntern.size interned = 2%N.
Proof. vm_compute. reflexivity. Qed.
Example intern_inverse : NatIntern.name 2%positive interned = Some 1.
Proof. vm_compute. reflexivity. Qed.
Example intern_missing : NatIntern.find 3 interned = None.
Proof. vm_compute. reflexivity. Qed.
Example intern_empty : NatIntern.name 1%positive NatIntern.empty = None.
Proof. vm_compute. reflexivity. Qed.
Example intern_reverse_forward :
  (match NatIntern.name 2%positive interned with
   | Some k => NatIntern.find k interned
   | None => None
   end, NatIntern.name 3%positive interned) = (Some 2%positive, None).
Proof. vm_compute. reflexivity. Qed.
Example intern_size_domain_boundary :
  (N.leb 2 (NatIntern.size interned), N.leb 3 (NatIntern.size interned),
    N.leb 4 (NatIntern.size interned)) = (true, false, false).
Proof. vm_compute. reflexivity. Qed.
Example intern_numeric_first : NatIntern.find 9 (intern_list [9; 4; 7]) = Some 1%positive.
Proof. vm_compute. reflexivity. Qed.
Example intern_numeric_last : NatIntern.find 7 (intern_list [9; 4; 7]) = Some 3%positive.
Proof. vm_compute. reflexivity. Qed.
Example intern_empty_index : NatIntern.find 9 (intern_list []) = None.
Proof. vm_compute. reflexivity. Qed.

(* Cost, representation and symbolic law examples are in BaseInternTest.v at 87192fe. *)
