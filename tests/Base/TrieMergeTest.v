(** * Trie merge tests

    These examples cover shared and disjoint bindings.
    For example, a callback combines values at a shared key.
    Builds on: Trie. *)

From Stdlib Require Import List NArith.
From Galois.Base Require Import Trie.
Import List.ListNotations.

Definition left_map : PTrieCode.t nat := PTrieCode.set 1 10 (PTrieCode.set 2 20 PTrieCode.empty).
Definition right_map : PTrieCode.t nat := PTrieCode.set 1 100 (PTrieCode.set 3 300 PTrieCode.empty).
Definition inter_add a b := match a, b with Some x, Some y => Some (x + y) | _, _ => None end.
Definition difference {A B} (a : option A) (b : option B) :=
  match b with Some _ => None | None => a end.
Definition union_add a b :=
  match a, b with Some x, Some y => Some (x + y) | Some x, None => Some x
  | None, Some y => Some y | None, None => None end.

Example inter_shared : PTrieCode.elements (PTrieCode.merge inter_add left_map right_map) =
  [(1%positive, 110)].
Proof. vm_compute. reflexivity. Qed.
Example diff_shared : PTrieCode.elements (PTrieCode.merge difference left_map right_map) =
  [(2%positive, 20)].
Proof. vm_compute. reflexivity. Qed.
Example union_order : PTrieCode.elements (PTrieCode.merge union_add left_map right_map) =
  [(2%positive, 20); (1%positive, 110); (3%positive, 300)].
Proof. vm_compute. reflexivity. Qed.
Example combine_changes_one_side :
  PTrieCode.elements (PTrieCode.merge
    (fun a (_ : option bool) => option_map S a) left_map PTrieCode.empty) =
    [(2%positive, 21); (1%positive, 11)].
Proof. vm_compute. reflexivity. Qed.
Example subset_reject :
  PTrieCode.forall2 (fun _ b => match b with Some _ => true | None => false end)
    left_map right_map = false.
Proof. vm_compute. reflexivity. Qed.
Example empty_comparison :
  PTrieCode.forall2 (fun (_ : nat) (_ : option nat) => false) PTrieCode.empty right_map = true.
Proof. vm_compute. reflexivity. Qed.

Example union_empty : PTrieCode.merge union_add left_map PTrieCode.empty = left_map.
Proof. vm_compute. reflexivity. Qed.
Example inter_empty : PTrieCode.merge inter_add left_map PTrieCode.empty = PTrieCode.empty.
Proof. vm_compute. reflexivity. Qed.
Example diff_empty :
  PTrieCode.merge difference left_map (PTrieCode.empty : PTrieCode.t bool) = left_map.
Proof. vm_compute. reflexivity. Qed.
Example inter_disjoint :
  PTrieCode.merge inter_add (PTrieCode.set 2 20 PTrieCode.empty)
    (PTrieCode.set 3 30 PTrieCode.empty) = PTrieCode.empty.
Proof. vm_compute. reflexivity. Qed.
Example diff_equal : PTrieCode.merge difference left_map left_map = PTrieCode.empty.
Proof. vm_compute. reflexivity. Qed.
Example inter_equal :
  PTrieCode.merge (fun a b => match a, b with Some x, Some _ => Some x | _, _ => None end)
    left_map left_map = left_map.
Proof. vm_compute. reflexivity. Qed.
Example union_equal :
  PTrieCode.merge (fun a b => match a with Some _ => a | None => b end)
    left_map left_map = left_map.
Proof. vm_compute. reflexivity. Qed.
Example empty_left :
  (PTrieCode.elements (PTrieCode.merge inter_add PTrieCode.empty right_map),
    PTrieCode.elements (PTrieCode.merge difference (PTrieCode.empty : PTrieCode.t nat) right_map)) =
  ([], []).
Proof. vm_compute. reflexivity. Qed.
