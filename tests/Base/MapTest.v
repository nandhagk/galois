(** * Map interface fixtures

    These fixtures observe replacement, deletion and canonical enumeration.
    For example, codes two, one and three have the trie traversal order.
    Builds on: Map and Key. *)

From Stdlib Require Import List NArith.
From Galois.Base Require Import Key Map Trie.
Import List.ListNotations.

Module PosMap := TrieMapCode PosKeyCode.
Definition sample := fold_left (fun m kv => PosMap.set (fst kv) (snd kv) m)
  [(1%positive, 10); (2%positive, 20); (3%positive, 30); (1%positive, 11)] PosMap.empty.

Example map_found : PosMap.get 1%positive sample = Some 11.
Proof. vm_compute. reflexivity. Qed.

Example map_absent : PosMap.get 4%positive sample = None.
Proof. vm_compute. reflexivity. Qed.

Example map_trie_order : List.map fst (PosMap.elements sample) = [2; 1; 3]%positive.
Proof. vm_compute. reflexivity. Qed.

Example map_update_absent :
  let old := PosMap.get 4%positive sample in
  PosMap.get 4%positive (PosMap.set 4%positive (match old with Some v => v | None => 40 end)
    sample) = Some 40.
Proof. vm_compute. reflexivity. Qed.

Example map_remove_last :
  PosMap.elements (PosMap.remove 1%positive (PosMap.set 1%positive 0 PosMap.empty)) = [].
Proof. vm_compute. reflexivity. Qed.

Example map_empty : PosMap.elements (PosMap.empty : PosMap.t nat) = [].
Proof. vm_compute. reflexivity. Qed.

Example map_combination :
  PosMap.elements (PosMap.merge (fun a b => match a with Some _ => a | None => b end)
    sample PosMap.empty) = [(2%positive, 20); (1%positive, 11); (3%positive, 30)].
Proof. vm_compute. reflexivity. Qed.

(* The old update and is_empty operations are expressed through get, set and elements above.
   Cost and law examples are in BaseMapTest.v at 87192fe. *)

Module UnitMap := TrieMapCode UnitKeyCode.
Definition raw_unit_map : UnitMap.t bool := PTrieCode.set 2%positive (tt, true) PTrieCode.empty.
Example map_raw_code :
  (UnitMap.get tt raw_unit_map, UnitMap.find 2%positive raw_unit_map,
   UnitMap.existsb (fun b => b) raw_unit_map) = (None, Some true, true).
Proof. vm_compute. reflexivity. Qed.
