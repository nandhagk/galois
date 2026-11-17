(** * Sparse octagon operations

    These examples observe the code tower on small signed difference matrices.
    For example, tightening a bound preserves the stronger bound already stored.
    Builds on: Octagon, keyed trie maps and the integer language.

    Groups:
    - [CoherenceTests] Whether a signed matrix is symmetric and well formed.
    - [ClosureTests] Composing bounds and detecting contradictions.
    - [TightenTests] Rounding unary bounds to even integers.
    - [InsertionTests] Adding and forgetting constraints.
    - [LatticeTests] Joining, ordering and widening matrices.
    - [AssumeTests] Adding the constraints of a guard.
    - [RangeTests] The bounds of an affine form.
    - [AssignTests] Assigning affine forms to a variable.
    - [AgreeTests] The fast assignment paths against their specifications.
    - [OddEntriesTests] Strong closure on a matrix with an odd unary entry. *)

From Stdlib Require Import List ZArith Lia.
From Galois.Base Require Import Key Map Trie.
From Galois.Domains Require Import LangSig ValueSig IntervalSig ZLang.
From Galois.States Require Import EnvSig.
From Galois.Relational Require Import Linearize Octagon.
Import ListNotations.

(** * Fixtures *)

Module OctKey := PairKeyCode PosKeyCode BoolKeyCode.
Module OctMap := TrieMapCode OctKey.
Module Forms := ZLinearizeCode PosKeyCode.
Module Oct := OctagonCode PosKeyCode OctKey OctMap ZLangCode Forms.

(** The signed literal x, that is, the pair of the variable 1 and the positive sign. *)
Definition positive_x := (1%positive, true).

(** The signed literal y, that is, the pair of the variable 2 and the positive sign. *)
Definition positive_y := (2%positive, true).

(** The negative signed literal of y. *)
Definition negative_y := Oct.flip positive_y.

Module OctLawKey := PairKey PosKey BoolKey.
Module OctLawMap := TrieMap OctLawKey.

(** A matrix whose only stored row is empty, for the signed literal x. *)
Definition isolated_positive_row : Oct.dbm :=
  OctMap.set positive_x OctMap.empty OctMap.empty.

(** A raw matrix whose stored labels all name one pivot, although their codes differ. *)
Definition repeated_label_row (target : OctKey.t) : OctMap.t Z :=
  PTrieCode.set (OctKey.encode target) (positive_y, 1%Z) PTrieCode.empty.

(** A raw matrix with four rows, each with a repeated label that names the same pivot. *)
Definition repeated_label_matrix : Oct.dbm :=
  let z := (3%positive, true) in
  PTrieCode.set (OctKey.encode positive_x) (positive_y, repeated_label_row positive_y)
    (PTrieCode.set (OctKey.encode positive_y) (positive_y, repeated_label_row z)
      (PTrieCode.set (OctKey.encode (Oct.flip z))
        (positive_y, repeated_label_row (Oct.flip positive_y))
        (PTrieCode.set (OctKey.encode (Oct.flip positive_y))
          (positive_y, repeated_label_row (Oct.flip positive_x)) PTrieCode.empty))).

(** A matrix with a unary bound on x, given by two raw entries under the same label. *)
Definition repeated_unary_labels : Oct.dbm :=
  PTrieCode.set (OctKey.encode positive_x)
    (positive_x, PTrieCode.set (OctKey.encode (Oct.flip positive_x))
      (positive_x, (-5)%Z) PTrieCode.empty)
    (PTrieCode.set (OctKey.encode positive_y) (positive_x, PTrieCode.empty) PTrieCode.empty).

(** The unary source on x, with the negative and positive bounds used by the range examples. *)
Definition negative_unary_source : Oct.dbm :=
  Oct.add_cons positive_x (Oct.flip positive_x) (-4)%Z
    (Oct.add_cons (Oct.flip positive_x) positive_x 10%Z OctMap.empty).

Module OctTimeKey := PairKeyT PosKeyT BoolKeyT.
Module OctTimeMap := TrieMapT OctTimeKey.
Module OctTimeForms := ZLinearizeT PosKeyT.
Module OctTime := OctagonT PosKeyT OctTimeKey OctTimeMap ZLangT ZNum OctTimeForms.

(** * Coherence *)

Module CoherenceTests.

  (** An isolated row stores no finite entry at any pair of signed literals. *)
  Example isolated_row_has_no_entries : forall i j,
    Oct.entry isolated_positive_row i j = None.
  Proof.
    intros i j. unfold Oct.entry, isolated_positive_row.
    change ((match OctLawMap.get i
      (OctLawMap.set positive_x (@OctLawMap.empty Z) OctLawMap.empty) with
      | Some row => OctLawMap.get j row | None => None end) = None).
    rewrite OctLawMap.get_find, OctLawMap.find_set.
    destruct (Pos.eqb (OctLawKey.encode i) (OctLawKey.encode positive_x)).
    - apply OctLawMap.get_empty.
    - now rewrite OctLawMap.find_empty.
  Qed.

  (** An isolated row is coherent, since each entry equals its flipped twin. *)
  Example isolated_row_is_coherent : forall i j,
    Oct.entry isolated_positive_row i j =
    Oct.entry isolated_positive_row (Oct.flip j) (Oct.flip i).
  Proof.
    intros i j. now rewrite !isolated_row_has_no_entries.
  Qed.

  (** The outer map of an isolated row is well formed. *)
  Example isolated_row_map_is_wf :
    OctLawMap.wf isolated_positive_row.
  Proof.
    apply OctLawMap.wf_set, OctLawMap.wf_empty.
  Qed.

  (** Every inner row of an isolated row is well formed. *)
  Example isolated_row_inner_maps_are_wf :
    forall p row, OctLawMap.find p isolated_positive_row = Some row -> OctLawMap.wf row.
  Proof.
    intros p row Hrow.
    change (OctLawMap.find p
      (OctLawMap.set positive_x (@OctLawMap.empty Z) OctLawMap.empty) = Some row) in Hrow.
    rewrite OctLawMap.find_set, OctLawMap.find_empty in Hrow.
    destruct (Pos.eqb p (OctLawKey.encode positive_x)); [|discriminate].
    injection Hrow as <-. apply OctLawMap.wf_empty.
  Qed.

  (** The raw codes form a coherent matrix although all stored labels name one pivot. *)
  Example repeated_label_matrix_is_coherent : forall i j,
    Oct.entry repeated_label_matrix i j =
    Oct.entry repeated_label_matrix (Oct.flip j) (Oct.flip i).
  Proof.
    intros [p s] [q t].
    destruct p as [p|p|]; try destruct p as [p|p|];
      destruct q as [q|q|]; try destruct q as [q|q|];
      destruct s, t; vm_compute; fold @trie_get; rewrite ?PTrie.get_empty; reflexivity.
  Qed.

End CoherenceTests.

(** * Closure *)

Module ClosureTests.

  (** Closing an isolated row gives its own signed literal the zero diagonal. *)
  Example isolated_row_closes_own_diagonal :
    match Oct.tclose isolated_positive_row with
    | Reached closed => Oct.entry closed positive_x positive_x
    | Unreached => None
    end = Some 0%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Closing an isolated row leaves the flipped diagonal open, so the closure is asymmetric. *)
  Example isolated_row_leaves_flipped_diagonal_open :
    match Oct.tclose isolated_positive_row with
    | Reached closed => Oct.entry closed (Oct.flip positive_x) (Oct.flip positive_x)
    | Unreached => None
    end = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Floyd-Warshall composes a pair of signed difference constraints. *)
  Example fw_composes_path :
    let z := (3%positive, true) in
    let m := Oct.add_cons positive_x positive_y 3%Z
      (Oct.add_cons positive_y z 4%Z OctMap.empty) in
    Oct.entry (Oct.fw m) positive_x z = Some 7%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Incremental closure propagates the new edge through an old suffix to the target. *)
  Example incremental_closure_composes_path :
    let z := (3%positive, true) in
    let m := Oct.add_cons positive_y z 4%Z OctMap.empty in
    match Oct.incr_close positive_x positive_y 3%Z m with
    | Reached closed => Oct.entry closed positive_x z
    | Unreached => None
    end = Some 7%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Incremental closure also fills the flipped twin of the propagated bound. *)
  Example incremental_closure_composes_twin :
    let z := (3%positive, true) in
    let m := Oct.add_cons positive_y z 4%Z OctMap.empty in
    match Oct.incr_close positive_x positive_y 3%Z m with
    | Reached closed => Oct.entry closed (Oct.flip z) (Oct.flip positive_x)
    | Unreached => None
    end = Some 7%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Closing the raw repeated-label matrix gives the forward entry the bound 2. *)
  Example repeated_labels_close_forward_entry :
    let z := (3%positive, true) in
    match Oct.tclose repeated_label_matrix with
    | Reached closed => Oct.entry closed positive_x z
    | Unreached => None
    end = Some 2%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Closing the raw repeated-label matrix leaves the flipped twin entry open. *)
  Example repeated_labels_leave_twin_open :
    let z := (3%positive, true) in
    match Oct.tclose repeated_label_matrix with
    | Reached closed => Oct.entry closed (Oct.flip z) (Oct.flip positive_x)
    | Unreached => None
    end = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

End ClosureTests.

(** * Tighten *)

Module TightenTests.

  (** An odd negative unary bound rounds down, never toward zero. *)
  Example tighten_rounds_odd_bound_down :
    let m := Oct.add_cons (Oct.flip positive_x) positive_x (-5)%Z OctMap.empty in
    Oct.entry (Oct.tighten m) (Oct.flip positive_x) positive_x = Some (-6)%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Integer closure strengthens an odd unary bound to its nearest even lower bound. *)
  Example tight_closure_rounds_unary_bound_to_even :
    let m := Oct.add_cons (Oct.flip positive_x) positive_x 5%Z OctMap.empty in
    match Oct.tclose m with
    | Reached closed => Oct.entry closed (Oct.flip positive_x) positive_x
    | Unreached => None
    end = Some 4%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Opposite unary bounds detect an empty integer interval. *)
  Example opposite_unary_bounds_are_unreached :
    let m := Oct.add_cons (Oct.flip positive_x) positive_x 0%Z
      (Oct.add_cons positive_x (Oct.flip positive_x) (-2)%Z OctMap.empty) in
    Oct.tclose m = Unreached.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Strengthening combines the upper bound on x with the lower bound on y. *)
  Example strengthen_combines_unary_bounds :
    let m := Oct.add_cons (Oct.flip positive_x) positive_x 4%Z
      (Oct.add_cons positive_y (Oct.flip positive_y) (-6)%Z OctMap.empty) in
    Oct.entry (Oct.strengthen m) positive_y positive_x = Some (-1)%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Repeated raw labels round the validated unary entry to the same even bound. *)
  Example repeated_labels_tighten_once :
    Oct.entry (Oct.tighten repeated_unary_labels) positive_x (Oct.flip positive_x) = Some (-6)%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

End TightenTests.

(** * Insertion *)

Module InsertionTests.

  (** The matrix with a strong bound from y to x and a weaker bound from x to y. *)
  Definition twin_source : Oct.dbm :=
    Oct.put positive_x positive_y (-100)%Z
      (Oct.put (Oct.flip positive_y) (Oct.flip positive_x) (-2)%Z OctMap.empty).

  (** The matrix after adding the weaker bound 0 from x to y to the twin source. *)
  Definition twin_result : Oct.dbm :=
    Oct.add_cons positive_x positive_y 0%Z twin_source.

  (** Adding a weaker bound keeps the stronger entry on the first signed twin. *)
  Example insertion_keeps_first_twin :
    Oct.entry twin_result positive_x positive_y = Some (-100)%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Adding a weaker bound keeps the stronger entry on the second signed twin. *)
  Example insertion_keeps_second_twin :
    Oct.entry twin_result (Oct.flip positive_y) (Oct.flip positive_x) = Some (-2)%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Forgetting y removes the entry from x to y. *)
  Example havoc_clears_forward_entry :
    match Oct.havoc 1%positive (Reached (Oct.add_cons positive_x positive_y 3%Z OctMap.empty)) with
    | Reached m => Oct.entry m positive_x positive_y
    | Unreached => Some 0%Z
    end = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Forgetting y removes the entry on its signed twin as well. *)
  Example havoc_clears_twin_entry :
    match Oct.havoc 1%positive (Reached (Oct.add_cons positive_x positive_y 3%Z OctMap.empty)) with
    | Reached m => Oct.entry m (Oct.flip positive_y) (Oct.flip positive_x)
    | Unreached => Some 0%Z
    end = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

End InsertionTests.

(** * Lattice *)

Module LatticeTests.

  (** The state with the bound x - y <= 3. *)
  Definition bound3_state : Oct.t :=
    Reached (Oct.add_cons positive_x positive_y 3%Z OctMap.empty).

  (** The state with the bound x - y <= 5. *)
  Definition bound5_state : Oct.t :=
    Reached (Oct.add_cons positive_x positive_y 5%Z OctMap.empty).

  (** The state with no finite entry, for the signed literal x. *)
  Definition empty_row_state : Oct.t :=
    Reached (OctMap.set positive_x OctMap.empty OctMap.empty).

  (** Joining retains the weaker common bound and never runs closure. *)
  Example join_keeps_weaker_common_bound :
    match Oct.join bound3_state bound5_state with
    | Reached m => Oct.entry m positive_x positive_y
    | Unreached => None
    end = Some 5%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Widening removes a bound whose candidate is weaker. *)
  Example widening_drops_unstable_bound :
    match Oct.widen 0 bound3_state bound5_state with
    | Reached m => Oct.entry m positive_x positive_y
    | Unreached => Some 0%Z
    end = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An empty row is below the unconstrained octagon, without a strict order step. *)
  Example empty_row_is_below_top :
    Oct.leb empty_row_state Oct.top = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The unconstrained octagon is below an empty row. *)
  Example top_is_below_empty_row :
    Oct.leb Oct.top empty_row_state = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

End LatticeTests.

(** * Assume *)

Module AssumeTests.

  (** An octagonal sum supplies both signed twins after a strict integer guard. *)
  Example strict_sum_supplies_forward_twin :
    match Oct.assume (ZGuardCmp Lt)
      [Node ZAdd [Leaf 1%positive; Leaf 2%positive]; Node (ZConst 4%Z) []] Oct.top with
    | Reached m => Oct.entry m (Oct.flip positive_y) positive_x
    | Unreached => None
    end = Some 3%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An octagonal sum supplies the opposite twin after a strict integer guard. *)
  Example strict_sum_supplies_backward_twin :
    match Oct.assume (ZGuardCmp Lt)
      [Node ZAdd [Leaf 1%positive; Leaf 2%positive]; Node (ZConst 4%Z) []] Oct.top with
    | Reached m => Oct.entry m (Oct.flip positive_x) positive_y
    | Unreached => None
    end = Some 3%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A unary strict guard doubles its integral difference bound. *)
  Example unary_strict_doubles_bound :
    match Oct.assume (ZGuardCmp Lt)
      [Leaf 1%positive; Node (ZConst 4%Z) []] Oct.top with
    | Reached m => Oct.entry m (Oct.flip positive_x) positive_x
    | Unreached => None
    end = Some 6%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A doubled unary coefficient gives the tighter integral upper bound as the upper endpoint. *)
  Example doubled_unary_upper_endpoint :
    snd (Oct.range (Leaf 1%positive)
      (Oct.assume (ZGuardCmp Lt)
        [Node ZMul [Node (ZConst 2%Z) []; Leaf 1%positive]; Node (ZConst 6%Z) []]
        Oct.top)) = Fin 2%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A doubled unary coefficient gives no lower endpoint. *)
  Example doubled_unary_lower_endpoint :
    fst (Oct.range (Leaf 1%positive)
      (Oct.assume (ZGuardCmp Lt)
        [Node ZMul [Node (ZConst 2%Z) []; Leaf 1%positive]; Node (ZConst 6%Z) []]
        Oct.top)) = NegInf.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An impossible constant comparison is detected without a distinguished zero literal. *)
  Example false_constant_guard_is_unreached :
    Oct.assume (ZGuardCmp Lt)
      [Node (ZConst 5%Z) []; Node (ZConst 2%Z) []] Oct.top = Unreached.
  Proof.
    vm_compute. reflexivity.
  Qed.

End AssumeTests.

(** * Range *)

Module RangeTests.

  (** A negative coefficient takes the lower endpoint of the form from the upper bound. *)
  Example affine_range_lower_endpoint :
    fst (Oct.range (Node ZSub [Node (ZConst 10%Z) []; Leaf 1%positive])
      (Reached negative_unary_source)) = Fin 5%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A negative coefficient takes the upper endpoint of the form from the lower bound. *)
  Example affine_range_upper_endpoint :
    snd (Oct.range (Node ZSub [Node (ZConst 10%Z) []; Leaf 1%positive])
      (Reached negative_unary_source)) = Fin 8%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

End RangeTests.

(** * Assign *)

Module AssignTests.

  (** A constant assignment from the unconstrained state gives the lower endpoint 7. *)
  Example constant_assignment_lower_endpoint :
    fst (Oct.range (Leaf 1%positive)
      (Oct.assign 1%positive (Node (ZConst 7%Z) []) Oct.top)) = Fin 7%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A constant assignment from the unconstrained state gives the upper endpoint 7. *)
  Example constant_assignment_upper_endpoint :
    snd (Oct.range (Leaf 1%positive)
      (Oct.assign 1%positive (Node (ZConst 7%Z) []) Oct.top)) = Fin 7%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The negative copy source relates y to itself with the signed difference bounds 8 and -2. *)
  Definition negative_copy_source : Oct.dbm :=
    Oct.add_cons positive_y (Oct.flip positive_y) (-2)%Z
      (Oct.add_cons (Oct.flip positive_y) positive_y 8%Z OctMap.empty).

  (** The state after the negative copy x := 3 - y from the source. *)
  Definition negative_copy_result : Oct.t :=
    Oct.assign 1%positive (Node ZSub [Node (ZConst 3%Z) []; Leaf 2%positive])
      (Reached negative_copy_source).

  (** A negative copy gives the lower endpoint of the copied variable. *)
  Example negative_copy_lower_endpoint :
    fst (Oct.range (Leaf 1%positive) negative_copy_result) = Fin (-1)%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A negative copy gives the upper endpoint of the copied variable. *)
  Example negative_copy_upper_endpoint :
    snd (Oct.range (Leaf 1%positive) negative_copy_result) = Fin 2%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A negative copy keeps the entry from the flipped y to x, with the bound 3. *)
  Example negative_copy_keeps_forward_entry :
    match negative_copy_result with
    | Reached n => Oct.entry n (Oct.flip positive_y) positive_x
    | Unreached => None
    end = Some 3%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A negative copy keeps the entry from x to the flipped y, with the bound -3. *)
  Example negative_copy_keeps_backward_entry :
    match negative_copy_result with
    | Reached n => Oct.entry n positive_x (Oct.flip positive_y)
    | Unreached => None
    end = Some (-3)%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The self translation source shifts the signed literals of x by two. *)
  Definition self_shift_source : Oct.dbm :=
    Oct.add_cons positive_x positive_y 4%Z
      (Oct.add_cons positive_x (Oct.flip positive_x) (-4)%Z
        (Oct.add_cons (Oct.flip positive_x) positive_x 10%Z OctMap.empty)).

  (** The state after the self translation x := x + 2 from the source. *)
  Definition self_shift_result : Oct.t :=
    Oct.assign 1%positive (Node ZAdd [Leaf 1%positive; Node (ZConst 2%Z) []])
      (Reached self_shift_source).

  (** A self translation gives the lower endpoint of the shifted variable. *)
  Example self_shift_lower_endpoint :
    fst (Oct.range (Leaf 1%positive) self_shift_result) = Fin 4%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A self translation gives the upper endpoint of the shifted variable. *)
  Example self_shift_upper_endpoint :
    snd (Oct.range (Leaf 1%positive) self_shift_result) = Fin 7%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A self translation keeps the entry from x to y, shifted to the bound 2. *)
  Example self_shift_keeps_forward_entry :
    match self_shift_result with
    | Reached n => Oct.entry n positive_x positive_y
    | Unreached => None
    end = Some 2%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A self translation keeps the flipped entry on the other side, with the bound 2. *)
  Example self_shift_keeps_twin_entry :
    match self_shift_result with
    | Reached n => Oct.entry n (Oct.flip positive_y) (Oct.flip positive_x)
    | Unreached => None
    end = Some 2%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A negative self assignment conservatively gives the lower endpoint of the output interval. *)
  Example negative_self_assignment_lower_endpoint :
    fst (Oct.range (Leaf 1%positive)
      (Oct.assign 1%positive (Node ZSub [Node (ZConst 3%Z) []; Leaf 1%positive])
        (Reached negative_unary_source))) = Fin (-2)%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A negative self assignment conservatively gives the upper endpoint of the output interval. *)
  Example negative_self_assignment_upper_endpoint :
    snd (Oct.range (Leaf 1%positive)
      (Oct.assign 1%positive (Node ZSub [Node (ZConst 3%Z) []; Leaf 1%positive])
        (Reached negative_unary_source))) = Fin 1%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

End AssignTests.

(** * Agree *)

Module AgreeTests.

  (** Entrywise comparison in both directions gives equality at every pair of signed literals. *)
  Lemma same_entries_by_comparison : forall a b,
    Oct.leb a b = true -> Oct.leb b a = true -> OctTime.same_entries a b.
  Proof.
    intros [|a] [|b] Hab Hba; cbn [OctTime.same_entries].
    - constructor.
    - discriminate Hba.
    - discriminate Hab.
    - intros i j.
      pose proof (proj1 (OctTime.leb_entries a b) Hab
        (OctTimeKey.encode i) (OctTimeKey.encode j)) as Hforward.
      pose proof (proj1 (OctTime.leb_entries b a) Hba
        (OctTimeKey.encode i) (OctTimeKey.encode j)) as Hbackward.
      rewrite !OctTime.raw_entry_get in Hforward, Hbackward.
      destruct (OctTime.entry a i j) as [c|]; destruct (OctTime.entry b i j) as [d|];
        cbn [OctTime.bound_leb] in Hforward, Hbackward; try discriminate; try reflexivity.
      f_equal. apply Z.le_antisymm; now apply Z.leb_le.
  Qed.

  (** Incremental assumptions close the relation x - y <= 1 with 0 <= x <= 9. *)
  Definition assignment_closed_state : Oct.t :=
    Oct.assume (ZGuardCmp Lt) [Leaf 1%positive; Node (ZConst 10%Z) []]
      (Oct.assume (ZGuardCmp Gt) [Leaf 1%positive; Node (ZConst (-1)%Z) []]
        (Oct.assume (ZGuardCmp Lt)
          [Node ZSub [Leaf 1%positive; Leaf 2%positive]; Node (ZConst 2%Z) []] Oct.top)).

  (** The half expression 2y + 2, whose coefficient is doubled before the constant is added. *)
  Definition assignment_half_expr : term ZLangCode.op positive :=
    Node ZAdd [Node ZMul [Node (ZConst 2%Z) []; Leaf 2%positive]; Node (ZConst 2%Z) []].

  (** A closed positive copy keeps every entry of the two-refinement specification. *)
  Example closed_copy_agrees_with_specification :
    OctTime.same_entries
      (Oct.assign 1%positive
        (Node ZAdd [Leaf 2%positive; Node (ZConst 3%Z) []]) assignment_closed_state)
      (Oct.assign_copy 1%positive positive_y 3%Z assignment_closed_state).
  Proof.
    apply same_entries_by_comparison; vm_compute; reflexivity.
  Qed.

  (** A closed negative copy keeps both signs of the source relation. *)
  Example closed_negative_copy_agrees_with_specification :
    OctTime.same_entries
      (Oct.assign 1%positive
        (Node ZSub [Node (ZConst 3%Z) []; Leaf 2%positive]) assignment_closed_state)
      (Oct.assign_copy 1%positive (Oct.flip positive_y) 3%Z assignment_closed_state).
  Proof.
    apply same_entries_by_comparison; vm_compute; reflexivity.
  Qed.

  (** Negative self assignment takes the finite interval branch with bounds zero and nine. *)
  Example closed_interval_agrees_with_refinements :
    OctTime.same_entries
      (Oct.assign 1%positive
        (Node ZSub [Node (ZConst 9%Z) []; Leaf 1%positive]) assignment_closed_state)
      (Oct.add_range 1%positive (Fin 0%Z, Fin 9%Z) (Oct.havoc 1%positive assignment_closed_state)).
  Proof.
    apply same_entries_by_comparison; vm_compute; reflexivity.
  Qed.

  (** Interval assignment strengthens the relation from y to x to the bound 10. *)
  Example closed_interval_strengthens_forward_relation :
    match Oct.assign 1%positive
      (Node ZSub [Node (ZConst 9%Z) []; Leaf 1%positive]) assignment_closed_state with
    | Reached m => Oct.entry m positive_y positive_x
    | Unreached => None
    end = Some 10%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Interval assignment strengthens the relation from x to the flipped y to the bound 1. *)
  Example closed_interval_strengthens_backward_relation :
    match Oct.assign 1%positive
      (Node ZSub [Node (ZConst 9%Z) []; Leaf 1%positive]) assignment_closed_state with
    | Reached m => Oct.entry m positive_x (Oct.flip positive_y)
    | Unreached => None
    end = Some 1%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A doubled source has a finite lower bound and no finite upper bound. *)
  Example one_sided_interval_agrees_with_refinements :
    OctTime.same_entries
      (Oct.assign 1%positive assignment_half_expr assignment_closed_state)
      (Oct.add_range 1%positive (Fin 0%Z, PosInf) (Oct.havoc 1%positive assignment_closed_state)).
  Proof.
    apply same_entries_by_comparison; vm_compute; reflexivity.
  Qed.

  (** The one-sided assignment exposes its finite lower bound as the lower endpoint. *)
  Example one_sided_interval_lower_endpoint :
    fst (Oct.range (Leaf 1%positive)
      (Oct.assign 1%positive assignment_half_expr assignment_closed_state)) = Fin 0%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The one-sided assignment has no finite upper endpoint. *)
  Example one_sided_interval_has_no_upper_endpoint :
    snd (Oct.range (Leaf 1%positive)
      (Oct.assign 1%positive assignment_half_expr assignment_closed_state)) = PosInf.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The direct positive copy matches the old specification on a tightly closed state. *)
  Example fast_copy_agrees_with_specification :
    OctTime.same_entries
      (Oct.assign_copy_fast 1%positive positive_y 3%Z assignment_closed_state)
      (Oct.assign_copy 1%positive positive_y 3%Z assignment_closed_state).
  Proof.
    apply same_entries_by_comparison; vm_compute; reflexivity.
  Qed.

  (** The direct negative copy matches the old specification on a tightly closed state. *)
  Example fast_negative_copy_agrees_with_specification :
    OctTime.same_entries
      (Oct.assign_copy_fast 1%positive (Oct.flip positive_y) 3%Z assignment_closed_state)
      (Oct.assign_copy 1%positive (Oct.flip positive_y) 3%Z assignment_closed_state).
  Proof.
    apply same_entries_by_comparison; vm_compute; reflexivity.
  Qed.

  (** The direct finite interval installs the same strengthened entries as two refinements. *)
  Example fast_interval_agrees_with_specification :
    OctTime.same_entries
      (Oct.add_range_fast 1%positive (Fin 0%Z, Fin 9%Z)
        (Oct.havoc 1%positive assignment_closed_state))
      (Oct.add_range 1%positive (Fin 0%Z, Fin 9%Z)
        (Oct.havoc 1%positive assignment_closed_state)).
  Proof.
    apply same_entries_by_comparison; vm_compute; reflexivity.
  Qed.

  (** A finite lower side installs the same strengthened entries as the specification. *)
  Example fast_lower_interval_agrees_with_specification :
    OctTime.same_entries
      (Oct.add_range_fast 1%positive (Fin 0%Z, PosInf)
        (Oct.havoc 1%positive assignment_closed_state))
      (Oct.add_range 1%positive (Fin 0%Z, PosInf)
        (Oct.havoc 1%positive assignment_closed_state)).
  Proof.
    apply same_entries_by_comparison; vm_compute; reflexivity.
  Qed.

  (** A finite upper side installs the same strengthened entries as the specification. *)
  Example fast_upper_interval_agrees_with_specification :
    OctTime.same_entries
      (Oct.add_range_fast 1%positive (NegInf, Fin 9%Z)
        (Oct.havoc 1%positive assignment_closed_state))
      (Oct.add_range 1%positive (NegInf, Fin 9%Z)
        (Oct.havoc 1%positive assignment_closed_state)).
  Proof.
    apply same_entries_by_comparison; vm_compute; reflexivity.
  Qed.

  (** A crossed finite range produces the unreachable state. *)
  Example fast_crossed_interval_is_unreached :
    Oct.add_range_fast 1%positive (Fin 1%Z, Fin 0%Z)
      (Oct.havoc 1%positive assignment_closed_state) = Unreached.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An interval with no finite side leaves the already forgotten matrix unchanged. *)
  Example fast_unbounded_interval_leaves_matrix :
    Oct.add_range_fast 1%positive (NegInf, PosInf)
      (Oct.havoc 1%positive assignment_closed_state) =
      Oct.havoc 1%positive assignment_closed_state.
  Proof.
    vm_compute. reflexivity.
  Qed.

End AgreeTests.

(** * Odd entries *)

Module OddEntriesTests.

  (** The matrix with a unary entry on y of value 1 and zero diagonals on y and its twin. *)
  Definition strong_odd_matrix : OctTime.dbm :=
    OctTime.put positive_y positive_y 0%Z
      (OctTime.put negative_y negative_y 0%Z
        (OctTime.put positive_y negative_y 1%Z OctTimeMap.empty)).

  (** The odd unary entry is its own signed twin, and the two diagonals agree. *)
  Local Lemma odd_coherent : OctTime.coherent strong_odd_matrix.
  Proof.
    assert (Heq : strong_odd_matrix = OctTime.add_cons positive_y positive_y 0%Z
      (OctTime.add_cons positive_y negative_y 1%Z OctTimeMap.empty)) by (vm_compute; reflexivity).
    rewrite Heq. repeat apply OctTime.coherent_add_cons. exact OctTime.coherent_top.
  Qed.

  (** Only the positive and negative literals of y occur in this matrix. *)
  Local Lemma odd_support : forall i,
    In (OctTimeKey.encode i) (OctTime.support strong_odd_matrix) ->
    i = positive_y \/ i = negative_y.
  Proof.
    intros i Hin. unfold strong_odd_matrix in Hin. rewrite !OctTime.support_put in Hin.
    change (OctTimeKey.encode i = OctTimeKey.encode positive_y \/
      OctTimeKey.encode i = OctTimeKey.encode positive_y \/
      OctTimeKey.encode i = OctTimeKey.encode negative_y \/
      OctTimeKey.encode i = OctTimeKey.encode negative_y \/
      OctTimeKey.encode i = OctTimeKey.encode positive_y \/
      OctTimeKey.encode i = OctTimeKey.encode negative_y \/ False) in Hin.
    destruct Hin as [H|[H|[H|[H|[H|[H|H]]]]]]; try contradiction;
      apply OctTimeKey.encode_inj in H; tauto.
  Qed.

  (** The matrix has exactly its two diagonals and its odd unary entry. *)
  Local Lemma odd_entry_cases : forall i j d, OctTime.entry strong_odd_matrix i j = Some d ->
    (i = positive_y /\ j = positive_y /\ d = 0%Z) \/
    (i = negative_y /\ j = negative_y /\ d = 0%Z) \/
    (i = positive_y /\ j = negative_y /\ d = 1%Z).
  Proof.
    intros i j d.
    assert (Hempty : OctTime.entry OctTimeMap.empty i j = None).
    { unfold OctTime.entry. now rewrite OctTimeMap.get_empty. }
    unfold strong_odd_matrix. rewrite !OctTime.entry_put, Hempty.
    destruct (OctTimeKey.eqb_spec i positive_y) as [Hi|Hi];
      destruct (OctTimeKey.eqb_spec j positive_y) as [Hj|Hj];
      destruct (OctTimeKey.eqb_spec i negative_y) as [Hi'|Hi'];
      destruct (OctTimeKey.eqb_spec j negative_y) as [Hj'|Hj'];
      intros Hentry; inversion Hentry; subst; tauto.
  Qed.

  (** Strong closure permits a finite odd unary bound. *)
  Example odd_matrix_is_strongly_closed : OctTime.strongly_closed strong_odd_matrix.
  Proof.
    split; [exact odd_coherent|]. split.
    - intros i Hin. apply odd_support in Hin.
      destruct Hin as [Hi|Hi]; subst i; vm_compute; reflexivity.
    - split.
      + intros i j k a z Hleft Hright.
        apply odd_entry_cases in Hleft. apply odd_entry_cases in Hright.
        destruct Hleft as [[Hi [Hk Ha]]|[[Hi [Hk Ha]]|[Hi [Hk Ha]]]];
          destruct Hright as [[Hk' [Hj Hz]]|[[Hk' [Hj Hz]]|[Hk' [Hj Hz]]]];
          subst; try discriminate.
        all: eexists; split; [vm_compute; reflexivity|lia].
      + intros i j a z Hleft Hright.
        apply odd_entry_cases in Hleft. apply odd_entry_cases in Hright.
        destruct Hleft as [[Hi [Hk Ha]]|[[Hi [Hk Ha]]|[Hi [Hk Ha]]]];
          destruct Hright as [[Hk' [Hj Hz]]|[[Hk' [Hj Hz]]|[Hk' [Hj Hz]]]];
          subst; try discriminate.
        all: eexists; split; [vm_compute; reflexivity|lia].
  Qed.

  (** Tight closure excludes this matrix because its unary entry is odd. *)
  Example odd_matrix_is_not_tightly_closed : ~ OctTime.tightly_closed strong_odd_matrix.
  Proof.
    intros [_ Heven]. specialize (Heven positive_y 1%Z eq_refl). vm_compute in Heven. discriminate.
  Qed.

  (** The closing interval assignment tightens the unrelated odd unary entry to zero. *)
  Example closing_interval_tightens_odd_unrelated_entry :
    match Oct.add_range 1%positive (Fin 0%Z, Fin 0%Z)
      (Oct.havoc 1%positive (Reached strong_odd_matrix)) with
    | Reached m => OctTime.entry m positive_y negative_y
    | Unreached => None
    end = Some 0%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The direct update keeps the odd foreign unary entry, unlike the tight closure. *)
  Example fast_interval_keeps_odd_unrelated_entry :
    match Oct.add_range_fast 1%positive (Fin 0%Z, Fin 0%Z)
      (Oct.havoc 1%positive (Reached strong_odd_matrix)) with
    | Reached m => Oct.entry m positive_y negative_y
    | Unreached => None
    end = Some 1%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Public assignment keeps a foreign odd unary entry, without tightening the matrix. *)
  Example assign_keeps_odd_unrelated_entry :
    match Oct.assign 1%positive (Node (ZConst 0%Z) []) (Reached strong_odd_matrix) with
    | Reached m => Oct.entry m positive_y negative_y
    | Unreached => None
    end = Some 1%Z.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The strong-but-not-tight counterexample also satisfies every map well-formedness condition. *)
  Example odd_matrix_is_wf : OctTime.dbm_wf strong_odd_matrix.
  Proof.
    unfold strong_odd_matrix. repeat apply OctTime.put_wf. apply OctTime.dbm_empty_wf.
  Qed.

End OddEntriesTests.
