(** * Map interface fixtures

    These fixtures observe replacement, deletion and canonical enumeration.
    For example, codes two, one and three have the trie traversal order.
    Builds on: Map and Key. *)

From Stdlib Require Import List NArith.
From Galois.Base Require Import Key Map.
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

(* The is_empty observation in BaseMapTest.v at 87192fe has no current operation. *)

Example map_empty : PosMap.elements (PosMap.empty : PosMap.t nat) = [].
Proof. vm_compute. reflexivity. Qed.

Example map_combination :
  PosMap.elements (PosMap.merge (fun a b => match a with Some _ => a | None => b end)
    sample PosMap.empty) = [(2%positive, 20); (1%positive, 11); (3%positive, 30)].
Proof. vm_compute. reflexivity. Qed.

(* Update, cost and law examples are in BaseMapTest.v at 87192fe. *)
