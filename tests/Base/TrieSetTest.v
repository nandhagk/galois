(** * Finite-set fixtures

    These fixtures cover duplicate keys, set operations and empty input.
    For example, removing a singleton's member empties it.
    Builds on: TrieSet and Key. *)

From Stdlib Require Import List NArith.
From Galois.Base Require Import Key TrieSet Trie.
Import List.ListNotations.

Module PosSet := TrieSetCode PosKeyCode.
Definition left_set := fold_right PosSet.add PosSet.empty [1; 2; 1]%positive.
Definition right_set := fold_right PosSet.add PosSet.empty [2; 3]%positive.

Example set_members : PosSet.elements left_set = [2; 1]%positive.
Proof. vm_compute. reflexivity. Qed.

Example set_intersection : PosSet.elements (PosSet.inter left_set right_set) = [2]%positive.
Proof. vm_compute. reflexivity. Qed.

Example set_difference : PosSet.elements (PosSet.diff left_set right_set) = [1]%positive.
Proof. vm_compute. reflexivity. Qed.

Example set_nonmember : PosSet.mem 3%positive left_set = false.
Proof. vm_compute. reflexivity. Qed.

Example set_empty : PosSet.equal PosSet.empty PosSet.empty = true.
Proof. vm_compute. reflexivity. Qed.

(* Cost and law examples are in BaseSetTest.v at 87192fe. *)

Module UnitSet := TrieSetCode UnitKeyCode.
Definition raw_unit_set : UnitSet.t := PTrieCode.set 2%positive tt PTrieCode.empty.
Example set_raw_code :
  (UnitSet.mem tt raw_unit_set, UnitSet.has 2%positive raw_unit_set,
   UnitSet.subset raw_unit_set UnitSet.empty) = (false, true, false).
Proof. vm_compute. reflexivity. Qed.
