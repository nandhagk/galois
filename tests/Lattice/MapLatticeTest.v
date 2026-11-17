(** * Map lattice fixtures

    These examples check a sparse map with a bottom default.
    For example, joining two singleton maps keeps both bindings.
    Builds on: MapLattice, Map, Key and Simple.

    Groups:
    - OrderTests: the order of maps with a bottom default.
    - JoinTests: joins of singleton maps, and joins of a map with itself.
    - WideningTests: widening and narrowing of maps.
    - SetterTests: the default of a map at keys that were set or not set.
    - LiftTests: the lifted environment with a fresh bottom.
    - BoundTests: the time bounds of inclusion, join and the bottom test. *)

From Stdlib Require Import List NArith.
From Galois.Base Require Import Key Map.
From Galois.Lattice Require Import MapLattice Simple WithBot JoinWidening.
Import List.ListNotations.

(** * Fixtures *)

(** Positive-keyed maps built by the trie map functor. *)
Module PosMap := TrieMapCode PosKeyCode.

(** The lattice of environments, that is maps from positive keys to booleans. *)
Module Env := MapLatticeCode PosKeyCode PosMap BoolLatCode.

(** The widening adapter of the environment lattice. *)
Module EnvWide := JoinWideningCode Env.

(** The environment lattice with a fresh bottom added. *)
Module LiftedEnv := WithBotCode Env.

(** The timed map and environment, for the time bounds. *)
Module TimedPosMap := TrieMapT PosKeyT.
Module TimedEnv := MapLatticeT PosKeyT TimedPosMap BoolLatT.

(** The empty map. *)
Definition e0 : PosMap.t bool := PosMap.empty.

(** The map that binds key 1 to true. *)
Definition e1 := PosMap.set 1%positive true e0.

(** The map that binds key 2 to true. *)
Definition e2 := PosMap.set 2%positive true e0.

(** * Order *)

Module OrderTests.

  (** The empty map is below the map of key 1. *)
  Example empty_map_below_singleton : Env.leb e0 e1 = true.
  Proof. vm_compute. reflexivity. Qed.

  (** The map of key 1 is not below the map of key 2. *)
  Example singleton_not_below_other_singleton : Env.leb e1 e2 = false.
  Proof. vm_compute. reflexivity. Qed.

  (** A map compared with itself, after a repeated set, is below itself. *)
  Example constructed_bottom_default_comparison_reflexive :
    let m := PosMap.set 1%positive true (PosMap.set 1%positive false PosMap.empty) in
    Env.leb m m = true.
  Proof. vm_compute. reflexivity. Qed.

End OrderTests.

(** * Join *)

Module JoinTests.

  (** Joining two singleton maps keeps both bindings, the later one first. *)
  Example join_keeps_both_bindings :
    PosMap.elements (Env.join e1 e2) = [(2%positive, true); (1%positive, true)].
  Proof. vm_compute. reflexivity. Qed.

  (** Joining a singleton map with itself keeps its one binding. *)
  Example singleton_self_join : PosMap.elements (Env.join e1 e1) = [(1%positive, true)].
  Proof.
    vm_compute. reflexivity.
  Qed.

End JoinTests.

(** * Widening *)

Module WideningTests.

  (** Widening two singleton maps keeps both bindings. *)
  Example widen_keeps_both_bindings :
    PosMap.elements (EnvWide.widen tt e1 e2) = [(2%positive, true); (1%positive, true)].
  Proof. vm_compute. reflexivity. Qed.

  (** Narrowing two singleton maps keeps the binding of the first. *)
  Example narrow_keeps_first_binding :
    PosMap.elements (EnvWide.narrow e1 e2) = [(1%positive, true)].
  Proof. vm_compute. reflexivity. Qed.

End WideningTests.

(** * Setters *)

Module SetterTests.

  (** A key set to true has the default true of a set key. *)
  Example set_key_has_true_default :
    Env.default (PosMap.get 1%positive (PosMap.set 1%positive true e0)) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A key that was not set has the bottom default false. *)
  Example unset_key_has_false_default :
    Env.default (PosMap.get 2%positive (PosMap.set 1%positive true e0)) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End SetterTests.

(** * Lifted *)

Module LiftTests.

  (** A reached empty environment is above the fresh bottom. *)
  Example lifted_environment_reached_empty_is_above_fresh_bottom :
    LiftedEnv.leb (Some e0) None = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End LiftTests.

(** * Bounds *)

Module BoundTests.

  (** Comparison charges the sum of the public sizes, including missing-key defaults. *)
  Example map_inclusion_bigO_bound :
    (TimedEnv.T_leb e1 e2 <=
      TimedEnv.c_lat * (N.of_nat (TimedEnv.size e1 + TimedEnv.size e2) + 1))%N.
  Proof.
    apply N.leb_le. vm_compute. reflexivity.
  Qed.

  (** Joining disjoint singletons fits the same two-map size measure. *)
  Example map_join_bigO_bound :
    (TimedEnv.T_join e1 e2 <=
      TimedEnv.c_lat * (N.of_nat (TimedEnv.size e1 + TimedEnv.size e2) + 1))%N.
  Proof.
    apply N.leb_le. vm_compute. reflexivity.
  Qed.

  (** The bottom test fits the size of one nonempty map. *)
  Example map_bottom_bigO_bound :
    (TimedEnv.T_is_bot e1 <= TimedEnv.c_lat * (N.of_nat (TimedEnv.size e1) + 1))%N.
  Proof.
    apply N.leb_le. vm_compute. reflexivity.
  Qed.

End BoundTests.

(* LatticeEnvTest.bottom_default_operations is split between
   JoinTests and OrderTests above. setter_value_and_fresh_bottom_observations keeps
   its bottom-default coordinates in SetterTests.
   duplicate_raw_lookup expects Some false from a list with duplicate stored codes.
   raw_bottom_default_comparison_not_reflexive and
   raw_top_default_comparison_not_reflexive expect false from that local list model.
   The canonical trie cannot store two cells at one code, so those malformed-list
   observations retire with the list model. constructed_top_default_comparison_reflexive
   expects true under the old top-default comparator. MapLattice supplies a bottom
   default. Its constructed_bottom_default_comparison_reflexive is checked above.
   top_default_left_narrow_is_not_an_exact_family expects (false, true).
   top_default_absorbing_join expects (false, Some [], Some [],
   Some [(2%positive, false); (1%positive, false)]).
   top_default_fresh_bottom_boundary expects (true, false, None, Some true).
   top_default_core_has_no_least_empty_map expects (false, false).
   empty_index_top_policy_still_distinguishes_fresh_bottom expects (false, true).
   The top-default coordinates of setter_value_and_fresh_bottom_observations
   expect (Some false, None). These use the old policy-parametric env operations.
   core section 4 moves state operations to States.Env. That component takes a
   LANG and VALUE_DOMAIN and uses reach states. A reached map containing a bottom
   binding is detected as bottom by is_bot and compared as bottom by leb. The old
   boolean top-policy fixtures deliberately retain false bindings as reached
   states. MapLattice has neither that policy nor fresh unreachable states, so
   these fixtures have no equivalent operation in its public interface.
   lifted_environment_empty_universe_measures expects (0, 1, 1, 1, 0, 1).
   both_policy_measure_boundaries expects (1, 3, 0, 4, 4, 1, 1).
   top_policy_chain_reaches_the_lifted_bound expects ranks [0; 1; 2; 3; 4] and
   four (true, false) comparisons. duplicate_universe_counts_repeated_environment_slots
   expects (2, 3). These use env_height/env_wrank inventory measures. MapLattice
   exports no HEIGHT or universe parameter. States.EnvBudget supplies a budget
   over supported variables rather than the old env_height dictionary.
   environment_cost_boundaries retires with Cost.ticks.
   environment_retains_component_callback_charges keeps its join elements
   [(1%positive, true)] in singleton_self_join above. Its ticks retire with Cost.
   ordinary_boolean_weak_laws_in_both_policies,
   ordinary_boolean_least_joins_in_both_policies, bottom_policy_exact_family and
   top_policy_exact_family use the deleted policy and KitFamily law dictionaries.
   lifted_environment_reached_empty_is_supported,
   supported_nondefault_values_in_both_policies,
   empty_universe_rejects_nondefault_bottom_map and
   empty_universe_rejects_nondefault_top_map use the deleted within_env predicate.
   empty_index_top_policy_has_total_weak_laws uses the deleted policy dictionary.
   empty_index_intersection_is_universal, empty_index_reached_meaning_is_universal,
   empty_index_fresh_meaning_is_empty, indexed_component_gamma_laws,
   indexed_environment_meaning_distinguishes_coordinates,
   indexed_environment_agreement_distinguishes_coordinates and
   indexed_meaning_transport_client are symbolic clients of the deleted
   concretisation and agreement dictionaries and their KitFamily adapters. *)
