(** * Set lattice fixtures

    These examples check may and must ordering and joins.
    For example, the may join contains both singleton members.
    Builds on: Sets, TrieSet and Key.

    Groups:
    - [MayTests] The may lattice, where a set is above the sets it contains.
    - [MustTests] The must lattice, with an unrestricted option carrier.
    - [EnumerationTests] Comparisons and listings of trie sets. *)

From Stdlib Require Import List NArith.
From Galois.Base Require Import Key TrieSet Trie.
From Galois.Lattice Require Import Sets JoinWidening.
Import List.ListNotations.

(** * Fixtures *)

(** Positive-keyed sets built by the trie set functor. *)
Module PosSet := TrieSetCode PosKeyCode.

(** The may lattice over positive-keyed sets. *)
Module May := MaySetCode PosKeyCode PosSet.

(** The must lattice over positive-keyed sets. *)
Module Must := MustSetCode PosKeyCode PosSet.

(** The widening adapters of the may and must lattices. *)
Module MayWide := JoinWideningCode May.
Module MustWide := JoinWideningCode Must.

(** The empty set, then the singletons and sets of keys 1, 2 and 3. *)
Definition s0 := PosSet.empty.
Definition s1 := PosSet.add 1%positive s0.
Definition s2 := PosSet.add 2%positive s0.
Definition s12 := PosSet.add 1%positive s2.
Definition s123 := PosSet.add 3%positive s12.

(** * May *)

Module MayTests.

  (** The empty set is below the singleton of 1. *)
  Example may_empty_below_singleton : May.leb s0 s1 = true.
  Proof. vm_compute. reflexivity. Qed.

  (** A singleton is below itself. *)
  Example may_singleton_below_itself : May.leb s1 s1 = true.
  Proof. vm_compute. reflexivity. Qed.

  (** The singleton of 1 is not below the singleton of 2. *)
  Example may_one_not_below_two : May.leb s1 s2 = false.
  Proof. vm_compute. reflexivity. Qed.

  (** The singleton of 2 is not below the singleton of 1. *)
  Example may_two_not_below_one : May.leb s2 s1 = false.
  Proof. vm_compute. reflexivity. Qed.

  (** The may join of two singletons lists both members. *)
  Example may_join_lists_both_members :
    PosSet.elements (May.join s1 s2) = [2%positive; 1%positive].
  Proof. vm_compute. reflexivity. Qed.

  (** Widening two singletons keeps both members. *)
  Example may_widen_keeps_both_members :
    PosSet.elements (MayWide.widen tt s1 s2) = [2%positive; 1%positive].
  Proof. vm_compute. reflexivity. Qed.

  (** Narrowing two singletons keeps the first member. *)
  Example may_narrow_keeps_first_member :
    PosSet.elements (MayWide.narrow s1 s2) = [1%positive].
  Proof. vm_compute. reflexivity. Qed.

  (** The first step of the chain is strict in the may order. *)
  Example may_first_step_is_strict :
    (May.leb s0 s1, May.leb s1 s0) = (true, false).
  Proof. vm_compute. reflexivity. Qed.

  (** The second step of the chain is strict in the may order. *)
  Example may_second_step_is_strict :
    (May.leb s1 s12, May.leb s12 s1) = (true, false).
  Proof. vm_compute. reflexivity. Qed.

  (** The third step of the chain is strict in the may order. *)
  Example may_third_step_is_strict :
    (May.leb s12 s123, May.leb s123 s12) = (true, false).
  Proof. vm_compute. reflexivity. Qed.

End MayTests.

(** * Must *)

Module MustTests.

  (** No must set is below a must set of 1, 2 and 3. *)
  Example must_none_below_some : Must.leb None (Some s123) = true.
  Proof. vm_compute. reflexivity. Qed.

  (** A must set of 1, 2 and 3 is not below no must set. *)
  Example must_some_not_below_none : Must.leb (Some s123) None = false.
  Proof. vm_compute. reflexivity. Qed.

  (** The must singleton of 1 is not below the must singleton of 2. *)
  Example must_one_not_below_two : Must.leb (Some s1) (Some s2) = false.
  Proof. vm_compute. reflexivity. Qed.

  (** The must singleton of 2 is not below the must singleton of 1. *)
  Example must_two_not_below_one : Must.leb (Some s2) (Some s1) = false.
  Proof. vm_compute. reflexivity. Qed.

  (** The must join of disjoint singletons is empty. *)
  Example must_join_of_disjoint_is_empty :
    option_map PosSet.elements (Must.join (Some s1) (Some s2)) = Some [].
  Proof. vm_compute. reflexivity. Qed.

  (** Widening two disjoint must singletons gives the empty set. *)
  Example must_widen_is_empty :
    option_map PosSet.elements (MustWide.widen tt (Some s1) (Some s2)) = Some [].
  Proof. vm_compute. reflexivity. Qed.

  (** Narrowing two must singletons keeps the member 1 of the first. *)
  Example must_narrow_keeps_one :
    option_map PosSet.elements (MustWide.narrow (Some s1) (Some s2)) = Some [1%positive].
  Proof. vm_compute. reflexivity. Qed.

End MustTests.

(** * Enumeration *)

Module EnumerationTests.

  (** Adding the same key twice keeps the set with one member. *)
  Example duplicate_values_keep_the_original_set :
    PosSet.elements (PosSet.add 1%positive (PosSet.add 1%positive PosSet.empty)) = [1%positive].
  Proof. vm_compute. reflexivity. Qed.

  (** A set built by repeated adds is a subset of itself. *)
  Example constructed_enumeration_comparison_reflexive :
    PosSet.subset (PosSet.add 2%positive (PosSet.add 2%positive s0))
      (PosSet.add 2%positive (PosSet.add 2%positive s0)) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The empty set is a subset of a constructed set. *)
  Example empty_enumeration_comparison :
    PosSet.subset s0 (PosSet.add 2%positive (PosSet.add 2%positive s0)) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A raw set holds key 1 with the stored code 2, so its listing is the code 2. *)
  Example raw_elements_list_stored_code :
    PosSet.elements (PTrieCode.set 1%positive 2%positive PTrieCode.empty) = [2%positive].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The raw set has key 1 as a member. *)
  Example raw_set_has_key_one :
    PosSet.mem 1%positive (PTrieCode.set 1%positive 2%positive PTrieCode.empty) = true.

  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The raw set does not have key 2 as a member. *)
  Example raw_set_lacks_key_two :
    PosSet.mem 2%positive (PTrieCode.set 1%positive 2%positive PTrieCode.empty) = false.

  Proof.
    vm_compute. reflexivity.
  Qed.

End EnumerationTests.

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
   elements coordinate in MayTests. Its tick predicate retires with Cost. *)
