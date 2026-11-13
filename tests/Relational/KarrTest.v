(** * Linear equality fixtures

    These examples exercise elimination, affine hulls and raw coefficient normalization.
    For example, the hull of (0, 0) and (1, 1) retains x = y.
    Builds on: Key, ZLang, Linearize, LinCert and Karr. *)

From Stdlib Require Import List ZArith.
From Galois.Base Require Import Key.
From Galois.Domains Require Import LangSig ValueSig ZLang.
From Galois.States Require Import EnvSig.
From Galois.Relational Require Import LinForm LinCertSig Linearize LinCert Karr.
Import List.ListNotations.
Local Open Scope Z_scope.

Module Forms := LinearizeCode PosKeyCode ZLangCode.
Module Certificates := LinCertCode PosKeyCode.
Module Equalities := KarrCode PosKeyCode ZLangCode Forms Certificates.

Definition x0 : lcons positive := LCons _ [(1%positive, 1)] REq 0.
Definition x1 : lcons positive := LCons _ [(1%positive, 1)] REq 1.
Definition y0 : lcons positive := LCons _ [(2%positive, 1)] REq 0.
Definition y1 : lcons positive := LCons _ [(2%positive, 1)] REq 1.
Definition same : lcons positive := LCons _ [(1%positive, 1); (2%positive, -1)] REq 0.

Example exact_row_division_scales_all_tracked_fields :
  karr_divide 2 (KRow [2; -4] 6 [8; 0] 10) = KRow [1; -2] 3 [4; 0] 5.
Proof.
  vm_compute. reflexivity.
Qed.

Example inexact_weight_keeps_the_integer_cross_product :
  karr_divide 2 (KRow [2; -4] 6 [3; 0] 10) = KRow [2; -4] 6 [3; 0] 10.
Proof.
  vm_compute. reflexivity.
Qed.

Example zero_divisor_keeps_the_integer_cross_product :
  karr_divide 0 (KRow [2; -4] 6 [8; 0] 10) = KRow [2; -4] 6 [8; 0] 10.
Proof.
  vm_compute. reflexivity.
Qed.

Example reached_empty_is_top : Equalities.leb (Reached [x1]) (Reached []) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example independent_equations_do_not_entail :
  Equalities.leb (Reached [x1]) (Reached [y1]) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example row_combination_is_detected :
  Equalities.leb (Reached [x1; y1]) (Reached [same]) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example infeasible_left_is_below_unrelated_rows :
  Equalities.leb (Reached [x0; x1]) (Reached [y1]) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example infeasible_left_is_below_unreached :
  Equalities.leb (Reached [x0; x1]) Unreached = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example duplicate_keys_cancel_before_elimination :
  Equalities.is_bot
    (Reached [LCons _ [(1%positive, 1); (1%positive, -1)] REq 1]) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example literal_inequality_is_retained :
  let r := LCons _ [(1%positive, 1)] RLe 3 in
  Equalities.leb (Reached [r]) (Reached [r]) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example inequality_is_not_treated_as_equality :
  Equalities.leb (Reached [LCons _ [(1%positive, 1)] RLe 1]) (Reached [x1]) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example unsupported_inequality_residual_is_rejected_before_checking :
  Equalities.target_certificate [LCons _ [(1%positive, 1)] RLe 0]
    (LCons _ [(1%positive, 2)] RLe 0) = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrong_equality_residual_is_rejected_before_checking :
  Equalities.target_certificate [x0] x1 = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example stronger_inequality_residual_is_rejected_before_checking :
  Equalities.target_certificate [x1] (LCons _ [(1%positive, 1)] RLe 0) = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example scaled_rational_row_is_detected :
  Equalities.leb (Reached [LCons _ [(1%positive, 2)] REq 1])
    (Reached [LCons _ [(1%positive, 4)] REq 2]) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example rational_solution_is_not_an_integer_contradiction :
  Equalities.is_bot (Reached [LCons _ [(1%positive, 2)] REq 1]) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example affine_hull_retains_the_diagonal :
  Equalities.leb (Equalities.join (Reached [x0; y0]) (Reached [x1; y1]))
    (Reached [same]) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example affine_hull_drops_the_endpoint :
  Equalities.leb (Equalities.join (Reached [x0; y0]) (Reached [x1; y1]))
    (Reached [x0]) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example havoc_preserves_an_eliminated_consequence :
  Equalities.leb (Equalities.havoc 1%positive (Reached [same; x1]))
    (Reached [y1]) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example havoc_frees_the_selected_variable :
  Equalities.leb (Equalities.havoc 1%positive (Reached [same; x1]))
    (Reached [x1]) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example havoc_checks_a_consequence_of_duplicate_source_terms :
  let source :=
    [LCons _ [(1%positive, 1); (2%positive, 1); (2%positive, 1)] REq 0;
     LCons _ [(1%positive, 1); (3%positive, 1); (3%positive, 1)] REq 0] in
  Equalities.leb (Equalities.havoc 1%positive (Reached source))
    (Reached [LCons _ [(2%positive, -2); (3%positive, 2)] REq 0]) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example havoc_retains_an_inequality_after_selected_key_cancellation :
  Equalities.havoc 1%positive
    (Reached [LCons _ [(1%positive, 1); (1%positive, -1);
      (2%positive, 2); (2%positive, -1)] RLe 7]) =
    Reached [LCons _ [(2%positive, 1)] RLe 7].
Proof.
  vm_compute. reflexivity.
Qed.

Example substitution_merges_repeated_keys :
  Equalities.subst 1%positive (Lin _ [(2%positive, 1)] 3)
    (LCons _ [(1%positive, 2); (2%positive, 1)] REq 8) =
    LCons _ [(2%positive, 3)] REq 2.
Proof.
  vm_compute. reflexivity.
Qed.

Example substitution_zero_aggregate_keeps_the_other_key :
  Equalities.subst 1%positive
    (Lin _ [(2%positive, 1); (2%positive, -1); (3%positive, 2)] 5)
    (LCons _ [(1%positive, 1); (1%positive, -1); (2%positive, 3)] RLe 7) =
    LCons _ [(2%positive, 3)] RLe 7.
Proof.
  vm_compute. reflexivity.
Qed.

Example substitution_preserves_an_alternating_zero_form :
  Equalities.subst 1%positive
    (Lin _ [(2%positive, -1); (2%positive, 1); (2%positive, -1); (2%positive, 1)] 0)
    (LCons _ [(2%positive, 1); (2%positive, 1); (1%positive, 1); (1%positive, 1)] REq 0) =
    LCons _ [(2%positive, 2)] REq 0.
Proof.
  vm_compute. reflexivity.
Qed.

Example unsupported_assignment_uses_havoc :
  Equalities.assign 1%positive (Leaf 2%positive) (Reached [x1; y1]) =
    Equalities.havoc 1%positive (Reached [x1; y1]).
Proof.
  vm_compute. reflexivity.
Qed.

(** The generic linearizer has no recognized forms; these fixtures test its affine worker. *)
Example affine_assignment_updates_its_old_value :
  Equalities.assign_rows 1%positive (Lin _ [(1%positive, 1)] 1) [x1] =
    [LCons _ [(1%positive, 1)] REq 2].
Proof.
  vm_compute. reflexivity.
Qed.

Example negative_self_coefficient_preserves_inequality_direction :
  Equalities.assign_rows 1%positive (Lin _ [(1%positive, -2)] 3)
    [LCons _ [(1%positive, 1)] RLe 4] =
    [LCons _ [(1%positive, -1)] RLe 5].
Proof.
  vm_compute. reflexivity.
Qed.

Example canceled_old_value_uses_projection_and_the_defining_equality :
  Equalities.leb
    (Reached (Equalities.assign_rows 1%positive
      (Lin _ [(1%positive, 1); (1%positive, -1); (2%positive, 1)] 1) [x1; y1]))
    (Reached [LCons _ [(1%positive, 1)] REq 2; y1]) = true.
Proof.
  vm_compute. reflexivity.
Qed.

(** Three nonunit pivots require exact division by earlier pivots. *)
Definition coupled : list (lcons positive) :=
  [LCons _ [(1%positive, 2); (2%positive, 1); (3%positive, 1)] REq 3;
   LCons _ [(1%positive, 1); (2%positive, 3); (3%positive, 2)] REq 5;
   LCons _ [(1%positive, 3); (3%positive, 4)] REq (-1)].

Example three_pivots_recover_the_unique_solution :
  Equalities.leb (Reached coupled)
    (Reached [x1; LCons _ [(2%positive, 1)] REq 2;
      LCons _ [(3%positive, 1)] REq (-1)]) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example three_pivots_detect_a_late_contradiction :
  Equalities.is_bot
    (Reached (coupled ++ [LCons _ [(1%positive, 5); (2%positive, -2);
      (3%positive, 3)] REq 0])) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example pivot_exchange_preserves_the_solution :
  Equalities.leb
    (Reached [LCons _ [(2%positive, 2); (3%positive, 1)] REq 3;
      LCons _ [(1%positive, 3); (3%positive, 2)] REq 1;
      LCons _ [(1%positive, 1); (2%positive, 1)] REq 3])
    (Reached [x1; LCons _ [(2%positive, 1)] REq 2;
      LCons _ [(3%positive, 1)] REq (-1)]) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example negative_pivots_preserve_the_solution :
  Equalities.leb
    (Reached [LCons _ [(1%positive, -2); (2%positive, -1);
      (3%positive, -1)] REq (-3);
      LCons _ [(1%positive, 1); (2%positive, 3); (3%positive, 2)] REq 5;
      LCons _ [(1%positive, 3); (3%positive, 4)] REq (-1)])
    (Reached [x1; LCons _ [(2%positive, 1)] REq 2;
      LCons _ [(3%positive, 1)] REq (-1)]) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example canceled_private_pivots_leave_the_real_equations :
  Equalities.leb
    (Reached [LCons _ [(4%positive, 1); (4%positive, -1);
      (1%positive, 2); (2%positive, 1)] REq 4;
      LCons _ [(5%positive, 1); (5%positive, -1);
        (1%positive, 1); (2%positive, 3)] REq 7])
    (Reached [x1; LCons _ [(2%positive, 1)] REq 2]) = true.
Proof.
  vm_compute. reflexivity.
Qed.

(** The minor model uses a determinant independent of the elimination recurrence. *)
Example laplace_determinant_of_coupled_coefficients :
  karr_determinant 3 [[2; 1; 1]; [1; 3; 2]; [3; 0; 4]] = 17.
Proof.
  vm_compute. reflexivity.
Qed.

Definition coupled_seeds : list karr_row :=
  Equalities.seed_rows (Equalities.variables coupled) (length coupled) 0
    (map Equalities.normalize_row coupled).

Example instrumented_bareiss_returns_the_actual_basis :
  fst (karr_bareiss_record 3 1 coupled_seeds) =
    Equalities.equality_basis (Equalities.variables coupled) coupled.
Proof.
  vm_compute. reflexivity.
Qed.

Example coupled_trace_entries_are_independent_augmented_minors :
  forallb (fun z => existsb (Z.eqb z)
    (karr_signed_minors 8 (map karr_row_entries coupled_seeds)))
    (snd (karr_bareiss_record 3 1 coupled_seeds)) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Definition exchanged_negative_seeds : list karr_row :=
  [KRow [0; 2; 1] 3 [1; 0; 0] 0;
   KRow [-3; 0; -2] (-1) [0; 1; 0] 0;
   KRow [-1; -1; 0] (-3) [0; 0; 1] 0].

Example exchanged_negative_trace_entries_are_independent_augmented_minors :
  forallb (fun z => existsb (Z.eqb z)
    (karr_signed_minors 8 (map karr_row_entries exchanged_negative_seeds)))
    (snd (karr_bareiss_record 3 1 exchanged_negative_seeds)) = true.
Proof.
  vm_compute. reflexivity.
Qed.

(** Repeated source coefficients are merged before a finite affine query is certified. *)
Example range_merges_repeated_source_coefficients :
  Equalities.range_linear
    [LCons _ [(1%positive, 3); (1%positive, -1)] REq 6]
    (Lin _ [(1%positive, 1)] 1) = (Fin 4, Fin 4).
Proof.
  vm_compute. reflexivity.
Qed.

(** A raw duplicate chain is shared by elimination and the final certificate check. *)
Example range_checks_a_prepared_duplicate_chain :
  Equalities.range_linear
    [LCons _ [(1%positive, 1); (2%positive, -1); (2%positive, -1)] REq 0;
     LCons _ [(2%positive, 1); (2%positive, 1)] REq 6]
    (Lin _ [(1%positive, 2)] 1) = (Fin 13, Fin 13).
Proof.
  vm_compute. reflexivity.
Qed.

(** A query outside the equality span retains the unbounded result. *)
Example range_keeps_an_undetermined_query_unbounded :
  Equalities.range_linear
    [LCons _ [(1%positive, 3); (1%positive, -1)] REq 6]
    (Lin _ [(2%positive, 1)] 0) = (NegInf, PosInf).
Proof.
  vm_compute. reflexivity.
Qed.

(** An empty source still certifies a constant affine form. *)
Example range_certifies_an_empty_source_constant :
  Equalities.range_linear [] (Lin _ [] 7) = (Fin 7, Fin 7).
Proof.
  vm_compute. reflexivity.
Qed.
