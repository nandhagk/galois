(** * Sparse zone operations

    These examples exercise code on finite difference constraints and malformed stored labels.
    For example, closure composes bounds three and four into an upper bound seven.
    Builds on: Zone, trie maps and the integer language. *)

From Stdlib Require Import ZArith.
From Galois.Base Require Import Key Map Trie.
From Galois.Domains Require Import ZLang.
From Galois.States Require Import EnvSig.
From Galois.Relational Require Import Linearize Zone.

Module ZoneKey := OptionKeyCode PosKeyCode.
Module ZoneMap := TrieMapCode ZoneKey.
Module Forms := LinearizeCode PosKeyCode ZLangCode.
Module Zones := ZoneCode PosKeyCode ZoneKey ZoneMap ZLangCode Forms.

Definition x := Some 1%positive.
Definition y := Some 2%positive.

(** Constraint insertion retains an already stronger upper bound. *)
Example insertion_minimum :
  Zones.entry (Zones.add_cons None x 9%Z
    (Zones.add_cons None x 3%Z ZoneMap.empty)) None x = Some 3%Z.
Proof.
  vm_compute. reflexivity.
Qed.

(** Joining two upper bounds retains their maximum. *)
Example join_common_bound :
  match Zones.join (Reached (Zones.add_cons None x 3%Z ZoneMap.empty))
    (Reached (Zones.add_cons None x 5%Z ZoneMap.empty)) with
  | Reached m => Zones.entry m None x
  | Unreached => None
  end = Some 5%Z.
Proof.
  vm_compute. reflexivity.
Qed.

(** Empty stored rows impose no finite constraint. *)
Example empty_rows_are_top :
  let s := Reached (ZoneMap.set x ZoneMap.empty ZoneMap.empty) in
  (Zones.leb s Zones.top, Zones.leb Zones.top s) = (true, true).
Proof.
  vm_compute. reflexivity.
Qed.

(** Floyd-Warshall closure composes a two-edge path. *)
Example closure_composes_bounds :
  let m := Zones.add_cons None x 3%Z (Zones.add_cons x y 4%Z ZoneMap.empty) in
  match Zones.close m with
  | Reached closed => Zones.entry closed None y
  | Unreached => None
  end = Some 7%Z.
Proof.
  vm_compute. reflexivity.
Qed.

(** Closure materializes the zero walk at a column-only endpoint. *)
Example closure_column_diagonal :
  match Zones.close (Zones.add_cons None x 3%Z ZoneMap.empty) with
  | Reached closed => (Zones.entry closed None None, Zones.entry closed x x)
  | Unreached => (None, None)
  end = (Some 0%Z, Some 0%Z).
Proof.
  vm_compute. reflexivity.
Qed.

(** A negative cycle makes the state unreachable. *)
Example closure_negative_cycle :
  Zones.close (Zones.add_cons None x (-1)%Z
    (Zones.add_cons x None 0%Z ZoneMap.empty)) = Unreached.
Proof.
  vm_compute. reflexivity.
Qed.

(** Incremental closure composes the new edge with an existing prefix. *)
Example incremental_composes_bounds :
  match Zones.incr_close x y 4%Z (Zones.add_cons None x 3%Z ZoneMap.empty) with
  | Reached closed => Zones.entry closed None y
  | Unreached => None
  end = Some 7%Z.
Proof.
  vm_compute. reflexivity.
Qed.

(** Incremental closure detects a cycle through its inserted edge. *)
Example incremental_negative_cycle :
  Zones.incr_close x None (-4)%Z (Zones.add_cons None x 3%Z ZoneMap.empty) = Unreached.
Proof.
  vm_compute. reflexivity.
Qed.

(** An unsupported pivot adds no matrix row. *)
Example absent_pivot_keeps_empty :
  Zones.fw_round x ZoneMap.empty = ZoneMap.empty.
Proof.
  vm_compute. reflexivity.
Qed.

(** A round follows encoded lookup even when stored labels do not match their codes. *)
Example raw_labels_do_not_redirect_round :
  let row := PTrieCode.set 4%positive (None, 7%Z) PTrieCode.empty in
  let m := PTrieCode.set 2%positive (None, row) PTrieCode.empty in
  Zones.entry (Zones.fw_round None m) x y = Some 7%Z.
Proof.
  vm_compute. reflexivity.
Qed.
