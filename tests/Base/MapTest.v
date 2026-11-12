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
  (match PosMap.elements (PosMap.remove 1%positive (PosMap.set 1%positive 0 PosMap.empty)) with
   | [] => true
   | _ => false
   end) = true.
Proof. vm_compute. reflexivity. Qed.

Example map_empty : PosMap.elements (PosMap.empty : PosMap.t nat) = [].
Proof. vm_compute. reflexivity. Qed.

Example map_combination :
  PosMap.elements (PosMap.merge (fun a b => match a with Some _ => a | None => b end)
    sample PosMap.empty) = [(2%positive, 20); (1%positive, 11); (3%positive, 30)].
Proof. vm_compute. reflexivity. Qed.

Example map_costed_comparison_value :
  PosMap.forall2b (fun v w =>
    match v, w with
    | Some v, Some w => Nat.eqb v w
    | None, None => true
    | _, _ => false
    end) sample sample = true.
Proof.
  vm_compute. reflexivity.
Qed.

Definition malformed_storage : PosMap.t nat :=
  PTrieCode.set 1%positive (2%positive, 10) PTrieCode.empty.
Module CollisionKey.
  Definition t := positive.
  Definition encode (_ : t) := 1%positive.
  Definition eqb (_ _ : t) := true.
End CollisionKey.
Module CollisionMap := TrieMapCode CollisionKey.

Example malformed_storage_update_client :
  PosMap.get 1%positive (PosMap.set 3%positive 30 malformed_storage) = Some 10.
Proof.
  vm_compute. reflexivity.
Qed.

Example colliding_keys_update_client :
  CollisionMap.get 1%positive
    (CollisionMap.set 2%positive 20
      (CollisionMap.set 2%positive 10 CollisionMap.empty)) = Some 20.
Proof.
  vm_compute. reflexivity.
Qed.

(* BaseMapTest.map_remove_last expresses is_empty through elements above.
   map_costed_combination and map_costed_comparison
   keep their value coordinates in map_combination and map_costed_comparison_value.
   Their tick comparisons and map_reference_ticks retire with Cost.ticks.
   raw_set_client and malformed_storage_control are symbolic law clients.
   colliding_keys_update_client uses a constant encoder through the operations
   layer, which requires no injectivity proof. *)

Module UnitMap := TrieMapCode UnitKeyCode.
Definition raw_unit_map : UnitMap.t bool := PTrieCode.set 2%positive (tt, true) PTrieCode.empty.
Example map_raw_code :
  (UnitMap.get tt raw_unit_map, UnitMap.find 2%positive raw_unit_map,
   UnitMap.existsb (fun b => b) raw_unit_map) = (None, Some true, true).
Proof. vm_compute. reflexivity. Qed.
