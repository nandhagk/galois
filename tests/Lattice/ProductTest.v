(** * Product fixtures

    These clients exercise a flat boolean value paired with a boolean fact.
    For example, joining unequal known values produces a flat top coordinate.
    Builds on: Product, Flat and Simple. *)

From Stdlib Require Import Bool NArith List.
From Galois.Base Require Import Key.
From Galois.Lattice Require Import Product Flat Simple JoinWidening.
Import List.ListNotations.

Module FlatBool := FlatCode BoolKeyCode.
Module PairFixture := ProductCode FlatBool BoolLatCode.
Module FlatBoolLat := Flat BoolKey.
Module FlatBoolHeight := FlatHeight BoolKey FlatBoolLat.
Module PairLat := Product FlatBoolLat BoolLat.
Module PairHeight := ProductHeight FlatBoolLat BoolLat FlatBoolHeight BoolLatHeight PairLat.
Module PairRank := JoinWidening PairLat PairHeight.
Module BoolUnit := ProductCode BoolLatCode UnitLatCode.
Module BoolPair := Product BoolLat BoolLat.
Module BoolPairHeight := ProductHeight BoolLat BoolLat BoolLatHeight BoolLatHeight BoolPair.
Module BoolPairRank := JoinWidening BoolPair BoolPairHeight.

Example product_positive :
  PairFixture.join (FVal false, false) (FVal true, true) = (FTop, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example product_negative :
  PairFixture.leb (FVal false, true) (FVal true, true) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example product_bottom :
  PairFixture.join (FBot, false) (FVal true, false) = (FVal true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example product_top :
  PairFixture.leb (FTop, true) (FTop, true) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example product_measure_client :
  (PairHeight.height, PairHeight.rank (FTop, true),
   PairHeight.height, PairRank.wrank tt (FBot, false)) = (3, 3, 3, 3).
Proof.
  vm_compute. reflexivity.
Qed.

(* LatticeProductTest.product_leb_ticks, product_join_ticks and
   product_callback_charges retire with Cost.ticks and its costed callbacks. *)

Example pair_equal :
  (BoolUnit.leb (false, tt) (false, tt), BoolUnit.join (false, tt) (false, tt)) =
  (true, (false, tt)).
Proof.
  vm_compute. reflexivity.
Qed.

Example pair_ordered :
  (BoolUnit.leb (false, tt) (true, tt), BoolUnit.join (false, tt) (true, tt)) =
  (true, (true, tt)).
Proof.
  vm_compute. reflexivity.
Qed.

Example pair_rejected : BoolUnit.leb (true, tt) (false, tt) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example pair_incomparable :
  (BoolPair.leb (true, false) (false, true), BoolPair.leb (false, true) (true, false),
   BoolPair.join (true, false) (false, true)) = (false, false, (true, true)).
Proof.
  vm_compute. reflexivity.
Qed.

Example family_full_product_measures :
  (map BoolPairHeight.rank [(false, false); (true, false); (false, true); (true, true)],
   map (BoolPairRank.wrank tt) [(false, false); (true, false); (false, true); (true, true)],
   BoolPairHeight.height, BoolPairHeight.height) = ([0; 1; 1; 2], [2; 1; 1; 0], 2, 2).
Proof.
  vm_compute. reflexivity.
Qed.

(* LatticeKitTest.pair_equal, pair_ordered, pair_rejected and pair_incomparable
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
