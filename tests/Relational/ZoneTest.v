(** * Sparse zone operations

    These examples exercise code on finite difference constraints and malformed stored labels.
    For example, closure composes bounds three and four into an upper bound seven.
    Builds on: Zone, trie maps and the integer language. *)

From Stdlib Require Import List ZArith.
From Galois.Base Require Import Key Map Trie.
From Galois.Bits Require Import Op.
From Galois.Domains Require Import LangSig ValueSig IntervalSig ZLang BitsLang.
From Galois.States Require Import EnvSig.
From Galois.Relational Require Import Linearize Zone.
Import List.ListNotations.

Module ZoneKey := OptionKeyCode PosKeyCode.
Module ZoneMap := TrieMapCode ZoneKey.
Module Forms := ZLinearizeCode PosKeyCode.
Module Zones := ZoneCode PosKeyCode ZoneKey ZoneMap ZLangCode Forms.
Module WordForms := BitsLinearizeUCode PosKeyCode.
Module WordZones := ZoneCode PosKeyCode ZoneKey ZoneMap BitsLangCode WordForms.

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

(** Affine range queries combine lower bounds, upper bounds and coefficient signs. *)
Example affine_range_negative_coefficient :
  let m := Zones.add_cons x None (-2)%Z
    (Zones.add_cons None x 5%Z ZoneMap.empty) in
  Zones.range (Node ZSub [Node (ZConst 10%Z) []; Leaf 1%positive]) (Reached m) =
    (Fin 5%Z, Fin 8%Z).
Proof.
  vm_compute. reflexivity.
Qed.

(** A constant affine expression has a singleton range without matrix entries. *)
Example constant_range :
  Zones.range (Node ZAdd [Node (ZConst 3%Z) []; Node (ZConst 4%Z) []]) Zones.top =
    (Fin 7%Z, Fin 7%Z).
Proof.
  vm_compute. reflexivity.
Qed.

(** A strict integer guard lowers the corresponding non-strict edge by one. *)
Example assume_strict_difference :
  match Zones.assume (ZGuardCmp Lt)
    [Node ZSub [Leaf 1%positive; Leaf 2%positive]; Node (ZConst 4%Z) []] Zones.top with
  | Reached m => Zones.entry m y x
  | Unreached => None
  end = Some 3%Z.
Proof.
  vm_compute. reflexivity.
Qed.

(** Equality inserts both directions of an affine copy relation. *)
Example assume_affine_equality :
  match Zones.assume (ZGuardCmp Eq)
    [Leaf 1%positive; Node ZAdd [Leaf 2%positive; Node (ZConst 3%Z) []]] Zones.top with
  | Reached m => (Zones.entry m y x, Zones.entry m x y)
  | Unreached => (None, None)
  end = (Some 3%Z, Some (-3)%Z).
Proof.
  vm_compute. reflexivity.
Qed.

(** An impossible constant guard yields a negative diagonal and bottom. *)
Example assume_false_constants :
  Zones.assume (ZGuardCmp Lt)
    [Node (ZConst 5%Z) []; Node (ZConst 2%Z) []] Zones.top = Unreached.
Proof.
  vm_compute. reflexivity.
Qed.

(** Constant assignment supplies an exact singleton even from top. *)
Example assign_constant :
  Zones.range (Leaf 1%positive)
    (Zones.assign 1%positive (Node (ZConst 7%Z) []) Zones.top) = (Fin 7%Z, Fin 7%Z).
Proof.
  vm_compute. reflexivity.
Qed.

(** Copy assignment preserves both the affine relation and its implied unary range. *)
Example assign_copy_relation :
  let m := Zones.add_cons y None (-1)%Z (Zones.add_cons None y 4%Z ZoneMap.empty) in
  let next := Zones.assign 1%positive
    (Node ZAdd [Leaf 2%positive; Node (ZConst 3%Z) []]) (Reached m) in
  (Zones.range (Leaf 1%positive) next,
   match next with Reached n => (Zones.entry n y x, Zones.entry n x y)
     | Unreached => (None, None) end) =
    ((Fin 4%Z, Fin 7%Z), (Some 3%Z, Some (-3)%Z)).
Proof.
  vm_compute. reflexivity.
Qed.

(** Self assignment translates existing constraints without forgetting their relations. *)
Example assign_self_shift :
  let m := Zones.add_cons x y 4%Z (Zones.add_cons x None (-2)%Z
    (Zones.add_cons None x 5%Z ZoneMap.empty)) in
  let next := Zones.assign 1%positive
    (Node ZAdd [Leaf 1%positive; Node (ZConst 2%Z) []]) (Reached m) in
  (Zones.range (Leaf 1%positive) next,
   match next with Reached n => Zones.entry n x y | Unreached => None end) =
    ((Fin 4%Z, Fin 7%Z), Some 2%Z).
Proof.
  vm_compute. reflexivity.
Qed.

(** Non-unit affine assignment retains the computed output interval. *)
Example assign_affine_range :
  let m := Zones.add_cons y None (-1)%Z (Zones.add_cons None y 4%Z ZoneMap.empty) in
  Zones.range (Leaf 1%positive)
    (Zones.assign 1%positive
      (Node ZAdd [Node ZMul [Node (ZConst 2%Z) []; Leaf 2%positive];
         Node (ZConst 1%Z) []]) (Reached m)) = (Fin 3%Z, Fin 9%Z).
Proof.
  vm_compute. reflexivity.
Qed.

(** A wrapped affine copy remains exact when the original bounds rule out overflow. *)
Example assign_word_without_wrap :
  let m := WordZones.add_cons x None (-2)%Z
    (WordZones.add_cons None x 5%Z ZoneMap.empty) in
  WordZones.range (Leaf 1%positive)
    (WordZones.assign 1%positive
      (Node (BOp bvadd) [Leaf 1%positive; Node (BConst 8%positive 3%Z) []])
      (Reached m)) = (Fin 5%Z, Fin 8%Z).
Proof.
  vm_compute. reflexivity.
Qed.

(** Possible overflow forgets the old equality and retains the word's wrapping interval. *)
Example assign_word_with_wrap :
  let m := WordZones.add_cons x None (-250)%Z
    (WordZones.add_cons None x 255%Z ZoneMap.empty) in
  WordZones.range (Leaf 1%positive)
    (WordZones.assign 1%positive
      (Node (BOp bvadd) [Leaf 1%positive; Node (BConst 8%positive 10%Z) []])
      (Reached m)) = (Fin 0%Z, Fin 255%Z).
Proof.
  vm_compute. reflexivity.
Qed.

(** Exact comparison checks all stored entries, including explicit zero diagonals. *)
Definition bound_equal (a b : option Z) : bool :=
  match a, b with
  | Some u, Some v => Z.eqb u v
  | None, None => true
  | _, _ => false
  end.

Definition same_entries (a b : Zones.t) : bool :=
  match a, b with
  | Reached ma, Reached mb =>
    ZoneMap.forall2b
      (fun ra rb => ZoneMap.forall2b bound_equal (Zones.row_of ra) (Zones.row_of rb)) ma mb
  | Unreached, Unreached => true
  | _, _ => false
  end.

(** Three constrained variables provide a closed input with a present copy source. *)
Definition assignment_closed_state : Zones.t :=
  Zones.assume (ZGuardCmp Lt)
    [Node ZSub [Leaf 2%positive; Leaf 3%positive]; Node (ZConst 2%Z) []]
  (Zones.assume (ZGuardCmp Lt)
    [Node ZSub [Leaf 3%positive; Leaf 2%positive]; Node (ZConst 3%Z) []]
  (Zones.assume (ZGuardCmp Lt) [Leaf 2%positive; Node (ZConst 5%Z) []]
  (Zones.assume (ZGuardCmp Lt) [Node (ZConst (-1)%Z) []; Leaf 2%positive]
  (Zones.assume (ZGuardCmp Lt) [Leaf 1%positive; Node (ZConst 11%Z) []]
  (Zones.assume (ZGuardCmp Lt) [Node (ZConst (-1)%Z) []; Leaf 1%positive] Zones.top))))).

(** Closing the assignment fixture changes none of its entries. *)
Example assignment_fixture_closed :
  same_entries
    (match assignment_closed_state with Reached m => Zones.close m | Unreached => Unreached end)
    assignment_closed_state = true.
Proof.
  vm_compute. reflexivity.
Qed.

(** Row and column copying agrees with the old two refinements on a closed state. *)
Example assign_closed_copy_same_entries :
  same_entries
    (Zones.assign 1%positive
      (Node ZAdd [Leaf 2%positive; Node (ZConst 3%Z) []]) assignment_closed_state)
    (Zones.refine x y (-3)%Z
      (Zones.refine y x 3%Z (Zones.havoc 1%positive assignment_closed_state))) = true.
Proof.
  vm_compute. reflexivity.
Qed.

(** A source absent from the input still receives the old zero diagonal. *)
Example assign_absent_source_same_entries :
  same_entries (Zones.assign 1%positive (Node (ZConst 7%Z) []) Zones.top)
    (Zones.refine x None (-7)%Z
      (Zones.refine None x 7%Z (Zones.havoc 1%positive Zones.top))) = true.
Proof.
  vm_compute. reflexivity.
Qed.

(** Widening drops a bound that remains implied by a two-edge path. *)
Definition assignment_widened_state : Zones.t :=
  let later := Zones.assume (ZGuardCmp Lt)
    [Node ZSub [Leaf 3%positive; Leaf 2%positive]; Node (ZConst 2%Z) []]
    (Zones.assume (ZGuardCmp Lt) [Leaf 2%positive; Node (ZConst 2%Z) []]
      (Zones.assume (ZGuardCmp Lt)
        [Node (ZConst (-1)%Z) []; Leaf 2%positive] Zones.top)) in
  let earlier := Zones.assume (ZGuardCmp Lt)
    [Leaf 3%positive; Node (ZConst 2%Z) []] later in
  Zones.widen 0%nat earlier later.

(** Assignment remains sound after widening without closing unrelated entries. *)
Example assign_widened_range :
  Zones.range (Leaf 1%positive)
    (Zones.assign 1%positive
      (Node ZAdd [Leaf 2%positive; Node (ZConst 3%Z) []]) assignment_widened_state) =
    (Fin 3%Z, Fin 4%Z).
Proof.
  vm_compute. reflexivity.
Qed.

(** A non-unit expression with only a lower bound takes the one-sided interval path. *)
Example assign_one_sided_lower :
  let s := Zones.assume (ZGuardCmp Lt)
    [Node (ZConst (-1)%Z) []; Leaf 2%positive] Zones.top in
  Zones.range (Leaf 1%positive)
    (Zones.assign 1%positive
      (Node ZMul [Node (ZConst 2%Z) []; Leaf 2%positive]) s) = (Fin 0%Z, PosInf).
Proof.
  vm_compute. reflexivity.
Qed.

(** A missing lower bound omits the copied lower row. *)
Example assign_one_sided_upper :
  let s := Zones.assume (ZGuardCmp Lt)
    [Leaf 2%positive; Node (ZConst 4%Z) []] Zones.top in
  Zones.range (Leaf 1%positive)
    (Zones.assign 1%positive
      (Node ZMul [Node (ZConst 2%Z) []; Leaf 2%positive]) s) = (NegInf, Fin 6%Z).
Proof.
  vm_compute. reflexivity.
Qed.

(** An unconstrained non-unit expression adds no bound. *)
Example assign_unbounded_interval :
  Zones.assign 1%positive
    (Node ZMul [Node (ZConst 2%Z) []; Leaf 2%positive]) Zones.top = Zones.top.
Proof.
  vm_compute. reflexivity.
Qed.

(** Crossed bounds in an inconsistent raw matrix make interval assignment unreachable. *)
Example assign_crossed_interval :
  let m := Zones.add_cons y None (-5)%Z (Zones.add_cons None y 2%Z ZoneMap.empty) in
  Zones.assign 1%positive
    (Node ZMul [Node (ZConst 2%Z) []; Leaf 2%positive]) (Reached m) = Unreached.
Proof.
  vm_compute. reflexivity.
Qed.
