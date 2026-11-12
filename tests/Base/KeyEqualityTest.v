(** * Encoded equality tests

    Equality tests distinguish matching, different and boundary keys.
    For example, lists compare by their injective serialized codes.
    Builds on: Key and Code. *)

From Stdlib Require Import Bool List NArith.
From Galois.Base Require Import Key Code.
Import List.ListNotations.

Module NatList := ListKeyCode NatKeyCode.

Local Open Scope positive_scope.

Example equality_accepts : NatList.eqb [1; 2]%nat [1; 2]%nat = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example equality_rejects : NatList.eqb [1; 2]%nat [2; 1]%nat = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example equality_empty_boundary : NatList.eqb [] [] = true.
Proof.
  vm_compute. reflexivity.
Qed.

(* BaseEqTest.equality_ticks retires with Cost.ticks.
   BaseKeyTacticsTest.key_positive and key_negative have the same observations
   below. key_boundary expects Some None from option_of_code and retires with the
   decoder API. case_key_goal, case_key_hypothesis, case_key_raw,
   case_key_raw_hypothesis and case_key_mixed test the retired case_key tactic.
   solve_pair, solve_list, solve_option and solve_roundtrip_cyclic_equalities test
   the retired solve_roundtrip tactic and codec dictionaries. The tactics family
   retires under core section 4, including BaseTacticsTest and BaseTacticsInvTest.
   Their local executable fixtures inv_option_self_reference_model,
   lookup_fixture_success and lookup_fixture_none exercise local tactic models
   and Cost binds. They have no public replacement operation. *)

Example key_positive : PosKeyCode.eqb 1 1 = true.
Proof. vm_compute. reflexivity. Qed.

Example key_negative : PosKeyCode.eqb 1 2 = false.
Proof. vm_compute. reflexivity. Qed.
