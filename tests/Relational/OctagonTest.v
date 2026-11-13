(** * Sparse octagon operations

    These examples observe the code tower on small signed difference matrices.
    For example, tightening a bound preserves the stronger bound already stored.
    Builds on: Octagon, keyed trie maps and the integer language. *)

From Stdlib Require Import List ZArith.
From Galois.Base Require Import Key Map.
From Galois.Domains Require Import ZLang.
From Galois.States Require Import EnvSig.
From Galois.Relational Require Import Linearize Octagon.

Module OctKey := PairKeyCode PosKeyCode BoolKeyCode.
Module OctMap := TrieMapCode OctKey.
Module Forms := LinearizeCode PosKeyCode ZLangCode.
Module Oct := OctagonCode PosKeyCode OctKey OctMap ZLangCode Forms.

Definition positive_x := (1%positive, true).
Definition positive_y := (2%positive, true).

(** Adding a weaker bound does not discard either existing signed constraint. *)
Example insertion_keeps_stronger_twins :
  let m := Oct.put positive_x positive_y (-100)%Z
    (Oct.put (Oct.flip positive_y) (Oct.flip positive_x) (-2)%Z OctMap.empty) in
  let m' := Oct.add_cons positive_x positive_y 0%Z m in
  (Oct.entry m' positive_x positive_y,
   Oct.entry m' (Oct.flip positive_y) (Oct.flip positive_x)) =
  (Some (-100)%Z, Some (-2)%Z).
Proof.
  vm_compute. reflexivity.
Qed.

(** Joining retains the weaker common bound and never runs closure. *)
Example join_common_bound :
  let a := Reached (Oct.add_cons positive_x positive_y 3%Z OctMap.empty) in
  let b := Reached (Oct.add_cons positive_x positive_y 5%Z OctMap.empty) in
  match Oct.join a b with
  | Reached m => Oct.entry m positive_x positive_y
  | Unreached => None
  end = Some 5%Z.
Proof.
  vm_compute. reflexivity.
Qed.

(** Empty rows do not create a strict order step at rank zero. *)
Example empty_rows_are_top :
  let s := Reached (OctMap.set positive_x OctMap.empty OctMap.empty) in
  (Oct.leb s Oct.top, Oct.leb Oct.top s) = (true, true).
Proof.
  vm_compute. reflexivity.
Qed.

(** Widening removes a bound whose candidate is weaker. *)
Example widening_unstable_bound :
  let a := Reached (Oct.add_cons positive_x positive_y 3%Z OctMap.empty) in
  let b := Reached (Oct.add_cons positive_x positive_y 5%Z OctMap.empty) in
  match Oct.widen 0 a b with
  | Reached m => Oct.entry m positive_x positive_y
  | Unreached => Some 0%Z
  end = None.
Proof.
  vm_compute. reflexivity.
Qed.

(** Forgetting a variable removes both of its signed occurrences. *)
Example havoc_signed_rows_and_columns :
  let s := Reached (Oct.add_cons positive_x positive_y 3%Z OctMap.empty) in
  match Oct.havoc 1%positive s with
  | Reached m =>
    (Oct.entry m positive_x positive_y,
     Oct.entry m (Oct.flip positive_y) (Oct.flip positive_x))
  | Unreached => (Some 0%Z, Some 0%Z)
  end = (None, None).
Proof.
  vm_compute. reflexivity.
Qed.

(** An odd negative unary bound rounds down, never toward zero. *)
Example tighten_negative_odd_bound :
  let m := Oct.add_cons (Oct.flip positive_x) positive_x (-5)%Z OctMap.empty in
  Oct.entry (Oct.tighten m) (Oct.flip positive_x) positive_x = Some (-6)%Z.
Proof.
  vm_compute. reflexivity.
Qed.

(** Integer closure strengthens an odd unary bound to its nearest even lower bound. *)
Example tight_closure_unary_bound :
  let m := Oct.add_cons (Oct.flip positive_x) positive_x 5%Z OctMap.empty in
  match Oct.tclose m with
  | Reached closed => Oct.entry closed (Oct.flip positive_x) positive_x
  | Unreached => None
  end = Some 4%Z.
Proof.
  vm_compute. reflexivity.
Qed.

(** Opposite unary bounds detect an empty integer interval. *)
Example tight_closure_inconsistent :
  let m := Oct.add_cons (Oct.flip positive_x) positive_x 0%Z
    (Oct.add_cons positive_x (Oct.flip positive_x) (-2)%Z OctMap.empty) in
  Oct.tclose m = Unreached.
Proof.
  vm_compute. reflexivity.
Qed.

(** Strengthening combines the upper bound on x with the lower bound on y. *)
Example strengthen_unary_bounds :
  let m := Oct.add_cons (Oct.flip positive_x) positive_x 4%Z
    (Oct.add_cons positive_y (Oct.flip positive_y) (-6)%Z OctMap.empty) in
  Oct.entry (Oct.strengthen m) positive_y positive_x = Some (-1)%Z.
Proof.
  vm_compute. reflexivity.
Qed.

(** Floyd-Warshall composes a pair of signed difference constraints. *)
Example closure_composes_path :
  let z := (3%positive, true) in
  let m := Oct.add_cons positive_x positive_y 3%Z
    (Oct.add_cons positive_y z 4%Z OctMap.empty) in
  Oct.entry (Oct.fw m) positive_x z = Some 7%Z.
Proof.
  vm_compute. reflexivity.
Qed.

(** Incremental closure propagates the new edge through an old suffix. *)
Example incremental_closure_composes_path :
  let z := (3%positive, true) in
  let m := Oct.add_cons positive_y z 4%Z OctMap.empty in
  match Oct.incr_close positive_x positive_y 3%Z m with
  | Reached closed =>
    (Oct.entry closed positive_x z,
     Oct.entry closed (Oct.flip z) (Oct.flip positive_x))
  | Unreached => (None, None)
  end = (Some 7%Z, Some 7%Z).
Proof.
  vm_compute. reflexivity.
Qed.
