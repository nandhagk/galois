(** * Map lattice fixtures

    These examples check a sparse map with a bottom default.
    For example, joining two singleton maps keeps both bindings.
    Builds on: MapLattice, Map, Key and Simple. *)

From Stdlib Require Import List NArith.
From Galois.Base Require Import Key Map.
From Galois.Lattice Require Import MapLattice Simple WithBot JoinWidening.
Import List.ListNotations.

Module PosMap := TrieMapCode PosKeyCode.
Module Env := MapLatticeCode PosKeyCode PosMap BoolLatCode.
Module EnvWide := JoinWideningCode Env.
Module LiftedEnv := WithBotCode Env.
Definition e0 : PosMap.t bool := PosMap.empty.
Definition e1 := PosMap.set 1%positive true e0.
Definition e2 := PosMap.set 2%positive true e0.

Example bottom_default_operations :
  (Env.leb e0 e1, Env.leb e1 e2, PosMap.elements (Env.join e1 e2)) =
  (true, false, [(2%positive, true); (1%positive, true)]).
Proof. vm_compute. reflexivity. Qed.

Example constructed_bottom_default_comparison_reflexive :
  let m := PosMap.set 1%positive true (PosMap.set 1%positive false PosMap.empty) in
  Env.leb m m = true.
Proof. vm_compute. reflexivity. Qed.

Example bottom_default_widen_narrow :
  (PosMap.elements (EnvWide.widen tt e1 e2), PosMap.elements (EnvWide.narrow e1 e2)) =
  ([(2%positive, true); (1%positive, true)], [(1%positive, true)]).
Proof. vm_compute. reflexivity. Qed.

Example setter_bottom_default_observations :
  (Env.default (PosMap.get 1%positive (PosMap.set 1%positive true e0)),
   Env.default (PosMap.get 2%positive (PosMap.set 1%positive true e0))) = (true, false).
Proof.
  vm_compute. reflexivity.
Qed.

Example lifted_environment_reached_empty_is_above_fresh_bottom :
  LiftedEnv.leb (Some e0) None = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example singleton_self_join : PosMap.elements (Env.join e1 e1) = [(1%positive, true)].
Proof.
  vm_compute. reflexivity.
Qed.

(* LatticeEnvTest.bottom_default_operations is split between
   bottom_default_operations and bottom_default_widen_narrow above.
   setter_value_and_fresh_bottom_observations keeps its bottom-default coordinates
   in setter_bottom_default_observations.
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
   lifted_environment_reached_empty_is_above_fresh_bottom expects false and uses
   the public WithBot composition checked above.
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
