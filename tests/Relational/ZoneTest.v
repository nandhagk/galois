(** * Sparse zone operations

    These examples exercise code on finite difference constraints and malformed stored labels.
    For example, closure composes bounds three and four into an upper bound seven.
    Builds on: Zone, trie maps and the integer language.

    Groups:
    - [ConstraintTests] Inserting bounds into a zone and reading empty rows.
    - [JoinTests] Keeping the larger of two upper bounds.
    - [ClosureTests] Composing bounds along paths and detecting negative cycles.
    - [RangeTests] Reading the interval of an affine form.
    - [AssumeTests] Adding the constraints of a guard.
    - [AssignTests] Assigning affine forms and word forms.
    - [AssignClosedTests] Assignments on closed and widened fixtures. *)

From Stdlib Require Import List ZArith.
From Galois.Base Require Import Key Map Trie.
From Galois.Bits Require Import Op.
From Galois.Domains Require Import LangSig ValueSig IntervalSig ZLang BitsLang.
From Galois.States Require Import EnvSig.
From Galois.Relational Require Import Linearize Zone.
Import List.ListNotations.

(** * Fixtures *)

Module ZoneKey := OptionKeyCode PosKeyCode.
Module ZoneMap := TrieMapCode ZoneKey.
Module Forms := ZLinearizeCode PosKeyCode.
Module Zones := ZoneCode PosKeyCode ZoneKey ZoneMap ZLangCode Forms.

(** The variable x, as the key of a zone entry. *)
Definition x := Some 1%positive.

(** The variable y, as the key of a zone entry. *)
Definition y := Some 2%positive.

(** Two zone states agree when every stored bound matches, including explicit zero diagonals. *)
Definition bound_equal (a b : option Z) : bool :=
  match a, b with
  | Some u, Some v => Z.eqb u v
  | None, None => true
  | _, _ => false
  end.

(** Two zone states agree when every row stores the same bounds in both. *)
Definition same_entries (a b : Zones.t) : bool :=
  match a, b with
  | Reached ma, Reached mb =>
    ZoneMap.forall2b
      (fun ra rb => ZoneMap.forall2b bound_equal (Zones.row_of ra) (Zones.row_of rb)) ma mb
  | Unreached, Unreached => true
  | _, _ => false
  end.

(** * Constraints *)

Module ConstraintTests.

  (** A zone whose only stored row is empty, for the variable x. *)
  Definition empty_row_state : Zones.t :=
    Reached (ZoneMap.set x ZoneMap.empty ZoneMap.empty).

  (** Inserting a weaker upper bound keeps the tighter bound already stored. *)
  Example insertion_keeps_tighter_bound :
    Zones.entry (Zones.add_cons None x 9%Z
      (Zones.add_cons None x 3%Z ZoneMap.empty)) None x = Some 3%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An empty stored row is below the unconstrained zone. *)
  Example empty_rows_are_below_top :
    Zones.leb empty_row_state Zones.top = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The unconstrained zone is below an empty stored row. *)
  Example top_is_below_empty_rows :
    Zones.leb Zones.top empty_row_state = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

End ConstraintTests.

(** * Join *)

Module JoinTests.

  (** Joining two upper bounds on x keeps the larger one. *)
  Example join_keeps_larger_bound :
    match Zones.join (Reached (Zones.add_cons None x 3%Z ZoneMap.empty))
      (Reached (Zones.add_cons None x 5%Z ZoneMap.empty)) with
    | Reached m => Zones.entry m None x
    | Unreached => None
    end = Some 5%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

End JoinTests.

(** * Closure *)

Module ClosureTests.

  (** Closure composes the bounds x <= 3 and x - y <= 4 into an upper bound 7 on y. *)
  Example closure_composes_two_edges :
    let m := Zones.add_cons None x 3%Z (Zones.add_cons x y 4%Z ZoneMap.empty) in
    match Zones.close m with
    | Reached closed => Zones.entry closed None y
    | Unreached => None
    end = Some 7%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Closure gives the zero walk at the column-only endpoint a zero bound. *)
  Example zero_walk_at_column_only_endpoint :
    match Zones.close (Zones.add_cons None x 3%Z ZoneMap.empty) with
    | Reached closed => Zones.entry closed None None
    | Unreached => None
    end = Some 0%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Closure gives the zero walk at x a zero diagonal. *)
  Example zero_walk_on_x_diagonal :
    match Zones.close (Zones.add_cons None x 3%Z ZoneMap.empty) with
    | Reached closed => Zones.entry closed x x
    | Unreached => None
    end = Some 0%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A negative cycle through x makes the state unreachable. *)
  Example negative_cycle_is_unreachable :
    Zones.close (Zones.add_cons None x (-1)%Z
      (Zones.add_cons x None 0%Z ZoneMap.empty)) = Unreached.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Incremental closure composes the new edge with the existing bound on x. *)
  Example incremental_composes_new_edge :
    match Zones.incr_close x y 4%Z (Zones.add_cons None x 3%Z ZoneMap.empty) with
    | Reached closed => Zones.entry closed None y
    | Unreached => None
    end = Some 7%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Incremental closure detects a cycle through the inserted edge. *)
  Example incremental_cycle_is_unreachable :
    Zones.incr_close x None (-4)%Z (Zones.add_cons None x 3%Z ZoneMap.empty) = Unreached.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A pivot with no entry in the matrix adds no row to the matrix. *)
  Example absent_pivot_adds_no_row :
    Zones.fw_round x ZoneMap.empty = ZoneMap.empty.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A round follows the encoded lookup, so labels that differ from their codes do not matter. *)
  Example round_follows_encoded_lookup :
    let row := PTrieCode.set 4%positive (None, 7%Z) PTrieCode.empty in
    let m := PTrieCode.set 2%positive (None, row) PTrieCode.empty in
    Zones.entry (Zones.fw_round None m) x y = Some 7%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

End ClosureTests.

(** * Range *)

Module RangeTests.

  (** A negative coefficient on the variable swaps its lower and upper bounds in the range. *)
  Example negative_coefficient_swaps_bounds :
    let m := Zones.add_cons x None (-2)%Z
      (Zones.add_cons None x 5%Z ZoneMap.empty) in
    Zones.range (Node ZSub [Node (ZConst 10%Z) []; Leaf 1%positive]) (Reached m) =
      (Fin 5%Z, Fin 8%Z).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A constant affine expression has a singleton range without matrix entries. *)
  Example constant_expression_has_singleton_range :
    Zones.range (Node ZAdd [Node (ZConst 3%Z) []; Node (ZConst 4%Z) []]) Zones.top =
      (Fin 7%Z, Fin 7%Z).
  Proof.
    vm_compute. reflexivity.
  Qed.

End RangeTests.

(** * Assume *)

Module AssumeTests.

  (** A strict integer guard lowers the corresponding non-strict edge by one. *)
  Example strict_guard_lowers_edge_by_one :
    match Zones.assume (ZGuardCmp Lt)
      [Node ZSub [Leaf 1%positive; Leaf 2%positive]; Node (ZConst 4%Z) []] Zones.top with
    | Reached m => Zones.entry m y x
    | Unreached => None
    end = Some 3%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Equality stores the bound 3 on the entry for the pair (y, x). *)
  Example equality_inserts_forward_bound :
    match Zones.assume (ZGuardCmp Eq)
      [Leaf 1%positive; Node ZAdd [Leaf 2%positive; Node (ZConst 3%Z) []]] Zones.top with
    | Reached m => Zones.entry m y x
    | Unreached => None
    end = Some 3%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Equality stores the bound -3 on the entry for the pair (x, y). *)
  Example equality_inserts_backward_bound :
    match Zones.assume (ZGuardCmp Eq)
      [Leaf 1%positive; Node ZAdd [Leaf 2%positive; Node (ZConst 3%Z) []]] Zones.top with
    | Reached m => Zones.entry m x y
    | Unreached => None
    end = Some (-3)%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An impossible constant guard yields a negative diagonal and bottom. *)
  Example false_constant_guard_is_unreachable :
    Zones.assume (ZGuardCmp Lt)
      [Node (ZConst 5%Z) []; Node (ZConst 2%Z) []] Zones.top = Unreached.
  Proof.
    vm_compute. reflexivity.
  Qed.

End AssumeTests.

(** * Assign *)

Module AssignTests.

  (** The word forms of the zone domain, at the bit-vector language. *)
  Module WordForms := BitsLinearizeUCode PosKeyCode.
  Module WordZones := ZoneCode PosKeyCode ZoneKey ZoneMap BitsLangCode WordForms.

  (** The state with bounds on y, which the copy assignment reads from. *)
  Definition copy_source_state :=
    Zones.add_cons y None (-1)%Z (Zones.add_cons None y 4%Z ZoneMap.empty).

  (** The state after assigning x := y + 3 to the copy source. *)
  Definition copy_result_state : Zones.t :=
    Zones.assign 1%positive
      (Node ZAdd [Leaf 2%positive; Node (ZConst 3%Z) []]) (Reached copy_source_state).

  (** Assigning a constant gives the variable an exact singleton, even from top. *)
  Example constant_assignment_gives_singleton :
    Zones.range (Leaf 1%positive)
      (Zones.assign 1%positive (Node (ZConst 7%Z) []) Zones.top) = (Fin 7%Z, Fin 7%Z).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A copy assignment keeps the unary range that the source implies. *)
  Example copy_assignment_gives_range :
    Zones.range (Leaf 1%positive) copy_result_state = (Fin 4%Z, Fin 7%Z).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A copy assignment records the bound 3 on the entry for the pair (y, x). *)
  Example copy_assignment_keeps_forward_bound :
    match copy_result_state with
    | Reached n => Zones.entry n y x
    | Unreached => None
    end = Some 3%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A copy assignment records the bound -3 on the entry for the pair (x, y). *)
  Example copy_assignment_keeps_backward_bound :
    match copy_result_state with
    | Reached n => Zones.entry n x y
    | Unreached => None
    end = Some (-3)%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The state with bounds on x and y, which the self assignment shifts. *)
  Definition self_shift_source :=
    Zones.add_cons x y 4%Z (Zones.add_cons x None (-2)%Z
      (Zones.add_cons None x 5%Z ZoneMap.empty)).

  (** The state after the self assignment x := x + 2. *)
  Definition self_shift_result : Zones.t :=
    Zones.assign 1%positive
      (Node ZAdd [Leaf 1%positive; Node (ZConst 2%Z) []]) (Reached self_shift_source).

  (** A self assignment shifts the range of x by its constant. *)
  Example self_shift_gives_shifted_range :
    Zones.range (Leaf 1%positive) self_shift_result = (Fin 4%Z, Fin 7%Z).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A self assignment keeps the relation to y, shifted by the constant. *)
  Example self_shift_keeps_relation :
    match self_shift_result with
    | Reached n => Zones.entry n x y
    | Unreached => None
    end = Some 2%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A non-unit affine assignment retains the output interval it computes. *)
  Example affine_assignment_gives_output_interval :
    let m := Zones.add_cons y None (-1)%Z (Zones.add_cons None y 4%Z ZoneMap.empty) in
    Zones.range (Leaf 1%positive)
      (Zones.assign 1%positive
        (Node ZAdd [Node ZMul [Node (ZConst 2%Z) []; Leaf 2%positive];
           Node (ZConst 1%Z) []]) (Reached m)) = (Fin 3%Z, Fin 9%Z).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A word copy stays exact when the original bounds rule out overflow. *)
  Example word_copy_without_overflow_stays_exact :
    let m := WordZones.add_cons x None (-2)%Z
      (WordZones.add_cons None x 5%Z ZoneMap.empty) in
    WordZones.range (Leaf 1%positive)
      (WordZones.assign 1%positive
        (Node (BOp bvadd) [Leaf 1%positive; Node (BConst 8%positive 3%Z) []])
        (Reached m)) = (Fin 5%Z, Fin 8%Z).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A word copy that may overflow forgets the old bounds and keeps the wrapping interval. *)
  Example word_copy_with_overflow_wraps :
    let m := WordZones.add_cons x None (-250)%Z
      (WordZones.add_cons None x 255%Z ZoneMap.empty) in
    WordZones.range (Leaf 1%positive)
      (WordZones.assign 1%positive
        (Node (BOp bvadd) [Leaf 1%positive; Node (BConst 8%positive 10%Z) []])
        (Reached m)) = (Fin 0%Z, Fin 255%Z).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A source with only a lower bound gives the assigned variable a half-line range. *)
  Example lower_bound_only_gives_half_line :
    let s := Zones.assume (ZGuardCmp Lt)
      [Node (ZConst (-1)%Z) []; Leaf 2%positive] Zones.top in
    Zones.range (Leaf 1%positive)
      (Zones.assign 1%positive
        (Node ZMul [Node (ZConst 2%Z) []; Leaf 2%positive]) s) = (Fin 0%Z, PosInf).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A source with only an upper bound gives the assigned variable an upper limit alone. *)
  Example upper_bound_only_gives_upper_limit :
    let s := Zones.assume (ZGuardCmp Lt)
      [Leaf 2%positive; Node (ZConst 4%Z) []] Zones.top in
    Zones.range (Leaf 1%positive)
      (Zones.assign 1%positive
        (Node ZMul [Node (ZConst 2%Z) []; Leaf 2%positive]) s) = (NegInf, Fin 6%Z).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An unconstrained non-unit expression adds no bound to the zone. *)
  Example unbounded_source_adds_no_bound :
    Zones.assign 1%positive
      (Node ZMul [Node (ZConst 2%Z) []; Leaf 2%positive]) Zones.top = Zones.top.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Crossed bounds in an inconsistent raw matrix make the interval assignment unreachable. *)
  Example crossed_source_bounds_are_unreachable :
    let m := Zones.add_cons y None (-5)%Z (Zones.add_cons None y 2%Z ZoneMap.empty) in
    Zones.assign 1%positive
      (Node ZMul [Node (ZConst 2%Z) []; Leaf 2%positive]) (Reached m) = Unreached.
  Proof.
    vm_compute. reflexivity.
  Qed.

End AssignTests.

(** * Assign on closed fixtures *)

Module AssignClosedTests.

  (** Three constrained variables give a closed input that has a present copy source. *)
  Definition assignment_closed_state : Zones.t :=
    Zones.assume (ZGuardCmp Lt)
      [Node ZSub [Leaf 2%positive; Leaf 3%positive]; Node (ZConst 2%Z) []]
    (Zones.assume (ZGuardCmp Lt)
      [Node ZSub [Leaf 3%positive; Leaf 2%positive]; Node (ZConst 3%Z) []]
    (Zones.assume (ZGuardCmp Lt) [Leaf 2%positive; Node (ZConst 5%Z) []]
    (Zones.assume (ZGuardCmp Lt) [Node (ZConst (-1)%Z) []; Leaf 2%positive]
    (Zones.assume (ZGuardCmp Lt) [Leaf 1%positive; Node (ZConst 11%Z) []]
    (Zones.assume (ZGuardCmp Lt) [Node (ZConst (-1)%Z) []; Leaf 1%positive] Zones.top))))).

  (** A state widened from an earlier one, which keeps a two-edge path and drops a bound. *)
  Definition assignment_widened_state : Zones.t :=
    let later := Zones.assume (ZGuardCmp Lt)
      [Node ZSub [Leaf 3%positive; Leaf 2%positive]; Node (ZConst 2%Z) []]
      (Zones.assume (ZGuardCmp Lt) [Leaf 2%positive; Node (ZConst 2%Z) []]
        (Zones.assume (ZGuardCmp Lt)
          [Node (ZConst (-1)%Z) []; Leaf 2%positive] Zones.top)) in
    let earlier := Zones.assume (ZGuardCmp Lt)
      [Leaf 3%positive; Node (ZConst 2%Z) []] later in
    Zones.widen 0%nat earlier later.

  (** Closing the closed fixture changes none of its entries. *)
  Example closed_fixture_is_fixed_by_closure :
    same_entries
      (match assignment_closed_state with Reached m => Zones.close m | Unreached => Unreached end)
      assignment_closed_state = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The closed fixture bounds the first variable to the range from 0 to 10. *)
  Example closed_fixture_bounds_first_variable :
    Zones.range (Leaf 1%positive) assignment_closed_state = (Fin 0%Z, Fin 10%Z).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The closed fixture bounds the second variable to the range from 0 to 4. *)
  Example closed_fixture_bounds_second_variable :
    Zones.range (Leaf 2%positive) assignment_closed_state = (Fin 0%Z, Fin 4%Z).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The closed fixture bounds the third variable to the range from -1 to 6. *)
  Example closed_fixture_bounds_third_variable :
    Zones.range (Leaf 3%positive) assignment_closed_state = (Fin (-1)%Z, Fin 6%Z).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A copy on a closed state keeps the same entries as the two-refinement specification. *)
  Example closed_copy_matches_two_refinements :
    same_entries
      (Zones.assign 1%positive
        (Node ZAdd [Leaf 2%positive; Node (ZConst 3%Z) []]) assignment_closed_state)
      (Zones.refine x y (-3)%Z
        (Zones.refine y x 3%Z (Zones.havoc 1%positive assignment_closed_state))) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A source absent from the input still gets the zero diagonal of the old state. *)
  Example absent_source_matches_two_refinements :
    same_entries (Zones.assign 1%positive (Node (ZConst 7%Z) []) Zones.top)
      (Zones.refine x None (-7)%Z
        (Zones.refine None x 7%Z (Zones.havoc 1%positive Zones.top))) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The widened fixture keeps its bound from None to y. *)
  Example widened_fixture_keeps_upper_bound :
    match assignment_widened_state with
    | Reached m => Zones.entry m None y
    | Unreached => None
    end = Some 1%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The widened fixture keeps the two-edge path from y to the third variable. *)
  Example widened_fixture_keeps_two_edge_path :
    match assignment_widened_state with
    | Reached m => Zones.entry m y (Some 3%positive)
    | Unreached => None
    end = Some 1%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The widened fixture has no entry for the composed bound from None to the third variable. *)
  Example widened_fixture_drops_composed_entry :
    match assignment_widened_state with
    | Reached m => Zones.entry m None (Some 3%positive)
    | Unreached => None
    end = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An assignment after widening keeps the range of its result sound. *)
  Example assignment_after_widening_stays_sound :
    Zones.range (Leaf 1%positive)
      (Zones.assign 1%positive
        (Node ZAdd [Leaf 2%positive; Node (ZConst 3%Z) []]) assignment_widened_state) =
      (Fin 3%Z, Fin 4%Z).
  Proof.
    vm_compute. reflexivity.
  Qed.

End AssignClosedTests.
