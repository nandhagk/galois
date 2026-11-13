(** * Sparse octagon operations

    These examples observe the code tower on small signed difference matrices.
    For example, tightening a bound preserves the stronger bound already stored.
    Builds on: Octagon, keyed trie maps and the integer language. *)

From Stdlib Require Import List ZArith.
From Galois.Base Require Import Key Map Trie.
From Galois.Domains Require Import LangSig ValueSig IntervalSig ZLang.
From Galois.States Require Import EnvSig.
From Galois.Relational Require Import Linearize Octagon.
Import ListNotations.

Module OctKey := PairKeyCode PosKeyCode BoolKeyCode.
Module OctMap := TrieMapCode OctKey.
Module Forms := ZLinearizeCode PosKeyCode.
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

Definition repeated_label_row (target : OctKey.t) : OctMap.t Z :=
  PTrieCode.set (OctKey.encode target) (positive_y, 1%Z) PTrieCode.empty.

Definition repeated_label_matrix : Oct.dbm :=
  let z := (3%positive, true) in
  PTrieCode.set (OctKey.encode positive_x) (positive_y, repeated_label_row positive_y)
    (PTrieCode.set (OctKey.encode positive_y) (positive_y, repeated_label_row z)
      (PTrieCode.set (OctKey.encode (Oct.flip z))
        (positive_y, repeated_label_row (Oct.flip positive_y))
        (PTrieCode.set (OctKey.encode (Oct.flip positive_y))
          (positive_y, repeated_label_row (Oct.flip positive_x)) PTrieCode.empty))).

(** The raw codes form a coherent matrix although all stored labels name one pivot. *)
Example repeated_label_matrix_coherent : forall i j,
  Oct.entry repeated_label_matrix i j =
  Oct.entry repeated_label_matrix (Oct.flip j) (Oct.flip i).
Proof.
  intros [p s] [q t].
  destruct p as [p|p|]; try destruct p as [p|p|];
    destruct q as [q|q|]; try destruct q as [q|q|];
    destruct s, t; vm_compute; fold @trie_get; rewrite ?PTrie.get_empty; reflexivity.
Qed.

(** Label-based pivot enumeration does not preserve coherence on this raw input. *)
Example repeated_label_closure_asymmetric :
  let z := (3%positive, true) in
  match Oct.tclose repeated_label_matrix with
  | Reached closed =>
    (Oct.entry closed positive_x z,
     Oct.entry closed (Oct.flip z) (Oct.flip positive_x))
  | Unreached => (None, None)
  end = (Some 2%Z, None).
Proof.
  vm_compute. reflexivity.
Qed.

(** Range evaluation rounds unary bounds before combining an affine expression. *)
Example affine_range_negative_coefficient :
  let m := Oct.add_cons positive_x (Oct.flip positive_x) (-4)%Z
    (Oct.add_cons (Oct.flip positive_x) positive_x 10%Z OctMap.empty) in
  Oct.range (Node ZSub [Node (ZConst 10%Z) []; Leaf 1%positive]) (Reached m) =
    (Fin 5%Z, Fin 8%Z).
Proof.
  vm_compute. reflexivity.
Qed.

(** An octagonal sum supplies both signed twins after a strict integer guard. *)
Example assume_strict_sum :
  match Oct.assume (ZGuardCmp Lt)
    [Node ZAdd [Leaf 1%positive; Leaf 2%positive]; Node (ZConst 4%Z) []] Oct.top with
  | Reached m =>
    (Oct.entry m (Oct.flip positive_y) positive_x,
     Oct.entry m (Oct.flip positive_x) positive_y)
  | Unreached => (None, None)
  end = (Some 3%Z, Some 3%Z).
Proof.
  vm_compute. reflexivity.
Qed.

(** A unary strict guard doubles its integral difference bound. *)
Example assume_unary_strict :
  match Oct.assume (ZGuardCmp Lt)
    [Leaf 1%positive; Node (ZConst 4%Z) []] Oct.top with
  | Reached m => Oct.entry m (Oct.flip positive_x) positive_x
  | Unreached => None
  end = Some 6%Z.
Proof.
  vm_compute. reflexivity.
Qed.

(** A doubled unary coefficient retains the tighter integral upper bound. *)
Example assume_doubled_unary :
  Oct.range (Leaf 1%positive)
    (Oct.assume (ZGuardCmp Lt)
      [Node ZMul [Node (ZConst 2%Z) []; Leaf 1%positive]; Node (ZConst 6%Z) []]
      Oct.top) = (NegInf, Fin 2%Z).
Proof.
  vm_compute. reflexivity.
Qed.

(** An impossible constant comparison is detected without a distinguished zero literal. *)
Example assume_false_constants :
  Oct.assume (ZGuardCmp Lt)
    [Node (ZConst 5%Z) []; Node (ZConst 2%Z) []] Oct.top = Unreached.
Proof.
  vm_compute. reflexivity.
Qed.

(** A constant assignment gives an exact singleton from the unconstrained state. *)
Example assign_constant :
  Oct.range (Leaf 1%positive)
    (Oct.assign 1%positive (Node (ZConst 7%Z) []) Oct.top) = (Fin 7%Z, Fin 7%Z).
Proof.
  vm_compute. reflexivity.
Qed.

(** A negative copy preserves the signed equality and the resulting unary interval. *)
Example assign_negative_copy :
  let m := Oct.add_cons positive_y (Oct.flip positive_y) (-2)%Z
    (Oct.add_cons (Oct.flip positive_y) positive_y 8%Z OctMap.empty) in
  let next := Oct.assign 1%positive
    (Node ZSub [Node (ZConst 3%Z) []; Leaf 2%positive]) (Reached m) in
  (Oct.range (Leaf 1%positive) next,
   match next with
   | Reached n =>
     (Oct.entry n (Oct.flip positive_y) positive_x,
      Oct.entry n positive_x (Oct.flip positive_y))
   | Unreached => (None, None)
   end) = ((Fin (-1)%Z, Fin 2%Z), (Some 3%Z, Some (-3)%Z)).
Proof.
  vm_compute. reflexivity.
Qed.

(** A self translation shifts both signed literals and retains foreign-variable relations. *)
Example assign_self_shift :
  let m := Oct.add_cons positive_x positive_y 4%Z
    (Oct.add_cons positive_x (Oct.flip positive_x) (-4)%Z
      (Oct.add_cons (Oct.flip positive_x) positive_x 10%Z OctMap.empty)) in
  let next := Oct.assign 1%positive
    (Node ZAdd [Leaf 1%positive; Node (ZConst 2%Z) []]) (Reached m) in
  (Oct.range (Leaf 1%positive) next,
   match next with
   | Reached n =>
     (Oct.entry n positive_x positive_y,
      Oct.entry n (Oct.flip positive_y) (Oct.flip positive_x))
   | Unreached => (None, None)
   end) = ((Fin 4%Z, Fin 7%Z), (Some 2%Z, Some 2%Z)).
Proof.
  vm_compute. reflexivity.
Qed.

(** A negative self assignment conservatively retains the evaluated output interval. *)
Example assign_negative_self_range :
  let m := Oct.add_cons positive_x (Oct.flip positive_x) (-4)%Z
    (Oct.add_cons (Oct.flip positive_x) positive_x 10%Z OctMap.empty) in
  Oct.range (Leaf 1%positive)
    (Oct.assign 1%positive
      (Node ZSub [Node (ZConst 3%Z) []; Leaf 1%positive]) (Reached m)) =
    (Fin (-2)%Z, Fin 1%Z).
Proof.
  vm_compute. reflexivity.
Qed.
