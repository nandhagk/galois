(** * Map interface fixtures

    These fixtures observe replacement, deletion and canonical enumeration.
    For example, codes two, one and three have the trie traversal order.
    Builds on: Map and Key.

    Groups:
    - [LookupTests] Reading values of a map, present or absent.
    - [UpdateTests] Adding and removing keys.
    - [EnumerationTests] The order and the content of the elements of a map.
    - [ComparisonTests] Equality of a map with itself.
    - [CollisionTests] Maps whose keys share one encoded code, or whose storage is malformed.
    - [RawTests] A map over a unit key, read back through its raw code. *)

From Stdlib Require Import List NArith.
From Galois.Base Require Import Key Map Trie.
Import List.ListNotations.

(** * Fixtures *)

(** Positive-keyed maps built by the trie map functor. *)
Module PosMap := TrieMapCode PosKeyCode.

(** A map with keys 1, 2 and 3, where key 1 is set twice and ends at 11. *)
Definition sample :=
  fold_left (fun m kv => PosMap.set (fst kv) (snd kv) m)
    [(1%positive, 10); (2%positive, 20); (3%positive, 30); (1%positive, 11)] PosMap.empty.

(** A key type whose every key encodes to the same code. *)
Module CollisionKey.
  Definition t := positive.
  Definition encode (_ : t) := 1%positive.
  Definition eqb (_ _ : t) := true.
End CollisionKey.

(** Maps over the colliding key type. *)
Module CollisionMap := TrieMapCode CollisionKey.

(** A trie whose root binding is stored under a key that does not match its path. *)
Definition malformed_storage : PosMap.t nat :=
  PTrieCode.set 1%positive (2%positive, 10) PTrieCode.empty.

(** Maps over unit keys. *)
Module UnitMap := TrieMapCode UnitKeyCode.

(** A raw trie with one binding, stored at key 2 with the value true. *)
Definition raw_unit_map : UnitMap.t bool :=
  PTrieCode.set 2%positive (tt, true) PTrieCode.empty.

(** * Lookup *)

Module LookupTests.

  (** A key set twice reads its last value. *)
  Example get_returns_last_set_value : PosMap.get 1%positive sample = Some 11.
  Proof. vm_compute. reflexivity. Qed.

  (** A key that was never set reads as absent. *)
  Example absent_key_gives_none : PosMap.get 4%positive sample = None.
  Proof. vm_compute. reflexivity. Qed.

  (** A unit key that was never set reads as absent in a raw map. *)
  Example unit_key_absent_from_raw_map : UnitMap.get tt raw_unit_map = None.
  Proof. vm_compute. reflexivity. Qed.

  (** A raw map finds the value stored at its key. *)
  Example raw_map_finds_stored_value : UnitMap.find 2%positive raw_unit_map = Some true.
  Proof. vm_compute. reflexivity. Qed.

  (** A raw map has a true value somewhere. *)
  Example raw_map_has_true_value : UnitMap.existsb (fun b => b) raw_unit_map = true.
  Proof. vm_compute. reflexivity. Qed.

End LookupTests.

(** * Update *)

Module UpdateTests.

  (** Setting an absent key adds it with the value that was set. *)
  Example set_adds_absent_key :
    PosMap.get 4%positive (PosMap.set 4%positive 40 sample) = Some 40.
  Proof. vm_compute. reflexivity. Qed.

  (** Removing the only key leaves a map with no elements. *)
  Example removing_only_key_empties_map :
    PosMap.elements (PosMap.remove 1%positive (PosMap.set 1%positive 0 PosMap.empty)) = [].
  Proof. vm_compute. reflexivity. Qed.

End UpdateTests.

(** * Enumeration *)

Module EnumerationTests.

  (** The keys of the sample map are listed in trie order. *)
  Example keys_list_in_trie_order :
    List.map fst (PosMap.elements sample) = [2; 1; 3]%positive.
  Proof. vm_compute. reflexivity. Qed.

  (** The empty map has no elements. *)
  Example empty_map_has_no_elements : PosMap.elements (PosMap.empty : PosMap.t nat) = [].
  Proof. vm_compute. reflexivity. Qed.

  (** Merging the sample with an empty map keeps its entries in trie order. *)
  Example merge_with_empty_keeps_entries :
    PosMap.elements (PosMap.merge (fun a b => match a with Some _ => a | None => b end)
      sample PosMap.empty) = [(2%positive, 20); (1%positive, 11); (3%positive, 30)].
  Proof. vm_compute. reflexivity. Qed.

End EnumerationTests.

(** * Comparison *)

Module ComparisonTests.

  (** A map compares equal to itself at every key. *)
  Example map_equals_itself :
    PosMap.forall2b (fun v w =>
      match v, w with
      | Some v, Some w => Nat.eqb v w
      | None, None => true
      | _, _ => false
      end) sample sample = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

End ComparisonTests.

(** * Collisions *)

Module CollisionTests.

  (** Updating a malformed trie keeps the entry that the trie stored. *)
  Example update_keeps_malformed_entry_readable :
    PosMap.get 1%positive (PosMap.set 3%positive 30 malformed_storage) = Some 10.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Keys that encode to one code overwrite each other. *)
  Example colliding_keys_overwrite_each_other :
    CollisionMap.get 1%positive
      (CollisionMap.set 2%positive 20
        (CollisionMap.set 2%positive 10 CollisionMap.empty)) = Some 20.
  Proof.
    vm_compute. reflexivity.
  Qed.

End CollisionTests.

(* BaseMapTest.map_remove_last expresses is_empty through elements above.
   map_costed_combination and map_costed_comparison
   keep their value coordinates in map_combination and map_costed_comparison_value.
   Their tick comparisons and map_reference_ticks retire with Cost.ticks.
   raw_set_client and malformed_storage_control are symbolic law clients.
   colliding_keys_update_client uses a constant encoder through the operations
   layer, which requires no injectivity proof. *)
