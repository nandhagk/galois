(** * Product fixtures

    These clients exercise a flat boolean value paired with a boolean fact.
    For example, joining unequal known values produces a flat top coordinate.
    Builds on: Product, Flat and Simple.

    Groups:
    - [PairTests] Pairs of flat and boolean coordinates, with their order and join.
    - [UnitPairTests] Pairs of a boolean and a unit coordinate.
    - [BoolPairTests] Pairs of two boolean coordinates, incomparable ones included.
    - [MeasureTests] Heights and ranks of the product lattices. *)

From Stdlib Require Import Bool NArith List.
From Galois.Base Require Import Key.
From Galois.Lattice Require Import Product Flat Simple JoinWidening.
Import List.ListNotations.

(** * Fixtures *)

(** The flat boolean lattice, as a code module. *)
Module FlatBool := FlatCode BoolKeyCode.

(** The product of a flat boolean and a boolean, as a code module. *)
Module PairFixture := ProductCode FlatBool BoolLatCode.

(** The flat boolean lattice, as a lattice module. *)
Module FlatBoolLat := Flat BoolKey.

(** The height structure of the flat boolean lattice. *)
Module FlatBoolHeight := FlatHeight BoolKey FlatBoolLat.

(** The product of the flat boolean and the boolean lattice. *)
Module PairLat := Product FlatBoolLat BoolLat.

(** The height structure of that product. *)
Module PairHeight := ProductHeight FlatBoolLat BoolLat FlatBoolHeight BoolLatHeight PairLat.

(** The widening rank of that product. *)
Module PairRank := JoinWidening PairLat PairHeight.

(** The product of a boolean and a unit lattice, as a code module. *)
Module BoolUnit := ProductCode BoolLatCode UnitLatCode.

(** The product of two boolean lattices. *)
Module BoolPair := Product BoolLat BoolLat.

(** The height structure of the product of two boolean lattices. *)
Module BoolPairHeight := ProductHeight BoolLat BoolLat BoolLatHeight BoolLatHeight BoolPair.

(** The widening rank of the product of two boolean lattices. *)
Module BoolPairRank := JoinWidening BoolPair BoolPairHeight.

(** * Pair *)

Module PairTests.

  (** Joining unequal known values gives a flat top in the first coordinate. *)
  Example product_join_gives_top_in_first_coordinate :
    PairFixture.join (FVal false, false) (FVal true, true) = (FTop, true).
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A pair with a different known value is not below the other pair. *)
  Example product_pair_not_below_other :
    PairFixture.leb (FVal false, true) (FVal true, true) = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Joining bottom in the first coordinate keeps the other pair. *)
  Example product_bottom_join_keeps_other_pair :
    PairFixture.join (FBot, false) (FVal true, false) = (FVal true, false).
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A top pair is below itself. *)
  Example product_top_pair_below_itself :
    PairFixture.leb (FTop, true) (FTop, true) = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

End PairTests.

(** * Unit pair *)

Module UnitPairTests.

  (** Equal pairs compare as ordered. *)
  Example equal_pairs_compare_as_ordered :
    BoolUnit.leb (false, tt) (false, tt) = true.
  Proof. vm_compute. reflexivity. Qed.

  (** Joining equal pairs gives the same pair. *)
  Example equal_pairs_join_to_themselves :
    BoolUnit.join (false, tt) (false, tt) = (false, tt).
  Proof. vm_compute. reflexivity. Qed.

  (** A false pair is below a true pair. *)
  Example false_pair_below_true_pair :
    BoolUnit.leb (false, tt) (true, tt) = true.
  Proof. vm_compute. reflexivity. Qed.

  (** Joining a false pair with a true pair gives the true pair. *)
  Example false_and_true_pairs_join_to_true :
    BoolUnit.join (false, tt) (true, tt) = (true, tt).
  Proof. vm_compute. reflexivity. Qed.

  (** A true pair is not below a false pair. *)
  Example true_pair_not_below_false_pair :
    BoolUnit.leb (true, tt) (false, tt) = false.
  Proof. vm_compute. reflexivity. Qed.

End UnitPairTests.

(** * Boolean pair *)

Module BoolPairTests.

  (** A pair of true and false is not below a pair of false and true. *)
  Example incomparable_pair_not_below_other :
    BoolPair.leb (true, false) (false, true) = false.
  Proof. vm_compute. reflexivity. Qed.

  (** A pair of false and true is not below a pair of true and false. *)
  Example incomparable_pair_not_below_first :
    BoolPair.leb (false, true) (true, false) = false.
  Proof. vm_compute. reflexivity. Qed.

  (** Joining two incomparable pairs gives the pair of both true coordinates. *)
  Example incomparable_pairs_join_to_top :
    BoolPair.join (true, false) (false, true) = (true, true).
  Proof. vm_compute. reflexivity. Qed.

End BoolPairTests.

(** * Measures *)

Module MeasureTests.

  (** The ranks of the four pairs of booleans are zero, one, one and two. *)
  Example full_product_ranks :
    map BoolPairHeight.rank [(false, false); (true, false); (false, true); (true, true)] =
      [0; 1; 1; 2].
  Proof. vm_compute. reflexivity. Qed.

  (** The widening ranks of the four pairs of booleans are two, one, one and zero. *)
  Example full_product_widening_ranks :
    map (BoolPairRank.wrank tt) [(false, false); (true, false); (false, true); (true, true)] =
      [2; 1; 1; 0].
  Proof. vm_compute. reflexivity. Qed.

  (** The product of two boolean lattices has height two. *)
  Example full_product_height_is_two : BoolPairHeight.height = 2.
  Proof. vm_compute. reflexivity. Qed.

  (** The height is two again on the same product. *)
  Example full_product_height_repeated_is_two : BoolPairHeight.height = 2.
  Proof. vm_compute. reflexivity. Qed.

  (** The rank of the top pair of the flat-and-boolean product is three. *)
  Example pair_rank_of_top_is_three : PairHeight.rank (FTop, true) = 3.
  Proof. vm_compute. reflexivity. Qed.

  (** The height of the flat-and-boolean product is three. *)
  Example pair_height_is_three : PairHeight.height = 3.
  Proof. vm_compute. reflexivity. Qed.

  (** The widening rank of the bottom pair is three. *)
  Example pair_widening_rank_of_bottom_is_three : PairRank.wrank tt (FBot, false) = 3.
  Proof. vm_compute. reflexivity. Qed.

  (** The height of the flat-and-boolean product is three on the widening client too. *)
  Example pair_height_is_three_on_widening_client : PairHeight.height = 3.
  Proof. vm_compute. reflexivity. Qed.

End MeasureTests.

(* LatticeProductTest.product_leb_ticks, product_join_ticks and
   product_callback_charges retire with Cost.ticks and its costed callbacks.
   LatticeKitTest.pair_equal, pair_ordered, pair_rejected and pair_incomparable
   keep their value coordinates through Product above. Their tick coordinates
   retire with Cost. family_measures has the same ranks and bounds in
   family_full_product_measures.
   family_empty_boundary expects a supported predicate and (rank, bound) = (0, 0).
   family_duplicate_boundary expects (2, 3) because its inventory repeats true.
   These require the deleted family_height inventory parameter. ProductHeight
   counts the two actual coordinates once and exports no inventory parameter.
   subtype_unordered_narrow expects (3, 0), subtype_ordered_narrow expects 1,
   and subtype_join_boundary expects (1, false) after dropping Cost coordinates.
   They test the guarded sub_lattice adapter on the invariant n <= 2.
   subtype_bool_measures expects (0, 1, 1, 0) on proof-carrying booleans.
   Sub, Kit and KitFamily retire under core section 4. BoundedSet restricts sets
   to a universe and supplies no general sub_lattice operation on nat or bool.
   The indexed gamma and agreement clients and all pilot/family/subtype law
   clients depend on those deleted dictionary adapters. *)
