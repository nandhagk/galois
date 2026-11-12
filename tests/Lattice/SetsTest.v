(** * Set lattice fixtures

    These examples check may and must ordering and joins.
    For example, the may join contains both singleton members.
    Builds on: Sets, TrieSet and Key. *)

From Stdlib Require Import List NArith.
From Galois.Base Require Import Key TrieSet Trie.
From Galois.Lattice Require Import Sets JoinWidening.
Import List.ListNotations.

Module PosSet := TrieSetCode PosKeyCode.
Module May := MaySetCode PosKeyCode PosSet.
Module Must := MustSetCode PosKeyCode PosSet.
Module MayWide := JoinWideningCode May.
Module MustWide := JoinWideningCode Must.
Definition s0 := PosSet.empty.
Definition s1 := PosSet.add 1%positive s0.
Definition s2 := PosSet.add 2%positive s0.
Definition s12 := PosSet.add 1%positive s2.
Definition s123 := PosSet.add 3%positive s12.

Example may_boundary_and_order :
  (May.leb s0 s1, May.leb s1 s1, May.leb s1 s2, May.leb s2 s1) =
  (true, true, false, false).
Proof. vm_compute. reflexivity. Qed.
Example may_operations : PosSet.elements (May.join s1 s2) = [2%positive; 1%positive].
Proof. vm_compute. reflexivity. Qed.
Example may_widen_narrow :
  (PosSet.elements (MayWide.widen tt s1 s2), PosSet.elements (MayWide.narrow s1 s2)) =
  ([2%positive; 1%positive], [1%positive]).
Proof. vm_compute. reflexivity. Qed.
Example may_chain_has_three_strict_steps :
  List.map (fun p => (May.leb (fst p) (snd p), May.leb (snd p) (fst p)))
    [(s0, s1); (s1, s12); (s12, s123)] =
  [(true, false); (true, false); (true, false)].
Proof. vm_compute. reflexivity. Qed.
Example must_boundary_and_order :
  (Must.leb None (Some s123), Must.leb (Some s123) None,
    Must.leb (Some s1) (Some s2), Must.leb (Some s2) (Some s1)) =
  (true, false, false, false).
Proof. vm_compute. reflexivity. Qed.
Example must_operations : option_map PosSet.elements (Must.join (Some s1) (Some s2)) = Some [].
Proof. vm_compute. reflexivity. Qed.
Example must_widen_narrow :
  (option_map PosSet.elements (MustWide.widen tt (Some s1) (Some s2)),
   option_map PosSet.elements (MustWide.narrow (Some s1) (Some s2))) =
  (Some [], Some [1%positive]).
Proof. vm_compute. reflexivity. Qed.

Example duplicate_values_keep_the_original_set :
  PosSet.elements (PosSet.add 1%positive (PosSet.add 1%positive PosSet.empty)) = [1%positive].
Proof. vm_compute. reflexivity. Qed.

Definition constructed_set := PosSet.add 2%positive (PosSet.add 2%positive s0).

Example constructed_enumeration_comparison_reflexive :
  PosSet.subset constructed_set constructed_set = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_enumeration_comparison : PosSet.subset s0 constructed_set = true.
Proof.
  vm_compute. reflexivity.
Qed.

Definition mismatched_raw_set := PTrieCode.set 1%positive 2%positive PTrieCode.empty.

Example raw_enumeration_differs_from_membership :
  (PosSet.elements mismatched_raw_set, PosSet.mem 1%positive mismatched_raw_set,
   PosSet.mem 2%positive mismatched_raw_set) = ([2%positive], true, false).
Proof.
  vm_compute. reflexivity.
Qed.

(* LatticeSetTest.raw_enumeration_comparison_not_reflexive expects false from its
   local list model. TrieSet.subset compares stored codes and returns true on the
   corresponding mismatched_raw_set compared with itself. The list-model fixture
   retires because it is not an operation of the replacement set implementation.
   may_height_reaches_bound is bounded_chain_reaches_bound in BoundedTest. It uses
   BoundedHeight on clipped values of the public restricted carrier.
   must_height_fresh_bottom_overhead expects ([0; 1; 2; 3; 4], 4), and
   must_empty_universe_still_has_a_step expects (0, 1, 1). MustSet has an unrestricted
   option carrier and no HEIGHT adapter. Its elements can exceed any fixed finite
   universe, so a total HEIGHT cannot reuse the old invariant-guarded measure.
   may_cost_observations, nonunit_encoder_and_duplicate_cells_are_charged,
   empty_conversion_does_not_call_nonunit_encoder and empty_union_retains_backend_overhead
   retire with Cost.ticks. nonempty_union_retains_members_and_charges keeps its
   elements coordinate in may_operations. Its tick predicate retires with Cost. *)
