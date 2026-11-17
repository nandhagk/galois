(** * Linear equality fixtures

    These examples exercise elimination, affine hulls and raw coefficient normalization.
    For example, the hull of (0, 0) and (1, 1) retains x = y.

    Groups:
    - [DivideTests] Dividing a row exactly by a weight.
    - [FusedDivideTests] Dividing a row exactly by a weight in one pass.
    - [EntailTests] Whether one system of equalities entails another.
    - [BottomTests] Integer and rational contradictions.
    - [CertificateTests] The residual of a target certificate.
    - [HullTests] The affine hull of two systems.
    - [FusedHullTests] The affine hull computed in one pass.
    - [HavocTests] Forgetting a variable.
    - [SubstTests] Substituting an expression for a variable.
    - [AssignTests] Assigning an expression to a variable.
    - [PivotTests] Eliminating coupled equalities.
    - [BareissTests] The minors of the elimination and the determinant.
    - [RangeTests] The bounds of an affine form.
    - [SharedBasisTests] Entailment checked against a shared basis.
    - [WidenTests] Widening keeps equivalent systems.
    - [FusedBasisTests] Fraction-free rows kept and projected in one pass.

    Builds on: Key, ZLang, Linearize, LinCert and Karr. *)

From Stdlib Require Import List ZArith.
From Galois.Base Require Import Key.
From Galois.Domains Require Import LangSig ValueSig ZLang.
From Galois.States Require Import EnvSig.
From Galois.Relational Require Import LinForm LinCertSig Linearize LinCert Karr.
Import List.ListNotations.
Local Open Scope Z_scope.

(** * Fixtures *)

Module Forms := LinearizeCode PosKeyCode ZLangCode.
Module Certificates := LinCertCode PosKeyCode.
Module Equalities := KarrCode PosKeyCode ZLangCode Forms Certificates.

(** The equality x = 0. *)
Definition x0 : lcons positive := LCons _ [(1%positive, 1)] REq 0.

(** The equality x = 1. *)
Definition x1 : lcons positive := LCons _ [(1%positive, 1)] REq 1.

(** The equality y = 0. *)
Definition y0 : lcons positive := LCons _ [(2%positive, 1)] REq 0.

(** The equality y = 1. *)
Definition y1 : lcons positive := LCons _ [(2%positive, 1)] REq 1.

(** The equality x - y = 0, which x = 1 and y = 1 both satisfy. *)
Definition same : lcons positive := LCons _ [(1%positive, 1); (2%positive, -1)] REq 0.

(** Three coupled equalities over x, y and z, with a unique solution. *)
Definition coupled : list (lcons positive) :=
  [LCons _ [(1%positive, 2); (2%positive, 1); (3%positive, 1)] REq 3;
   LCons _ [(1%positive, 1); (2%positive, 3); (3%positive, 2)] REq 5;
   LCons _ [(1%positive, 3); (3%positive, 4)] REq (-1)].

(** * Divide *)

Module DivideTests.

  (** An exact weight divides every tracked field of the row. *)
  Example exact_division_scales_every_field :
    karr_divide 2 (KRow [2; -4] 6 [8; 0] 10) = KRow [1; -2] 3 [4; 0] 5.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An inexact weight leaves the row as its integer cross product. *)
  Example inexact_weight_keeps_row :
    karr_divide 2 (KRow [2; -4] 6 [3; 0] 10) = KRow [2; -4] 6 [3; 0] 10.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A zero divisor leaves the row unchanged, as an integer cross product. *)
  Example zero_divisor_keeps_row :
    karr_divide 0 (KRow [2; -4] 6 [8; 0] 10) = KRow [2; -4] 6 [8; 0] 10.
  Proof.
    vm_compute. reflexivity.
  Qed.

End DivideTests.

(** * Fused division *)

Module FusedDivideTests.

  (** A negative divisor divides the complete row, including its sign. *)
  Example negative_divisor_is_accepted :
    karr_divide_fused (-2) (KRow [6; -4] 10 [2; -6] 2) =
      KRow [-3; 2] (-5) [-1; 3] (-1).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A nonzero remainder in a later weight restores the complete original row. *)
  Example inexact_weight_restores_row :
    karr_divide_fused 2 (KRow [2; -4] 6 [3; 0] 10) = KRow [2; -4] 6 [3; 0] 10.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The zero divisor guard keeps the original row without attempting division. *)
  Example zero_divisor_keeps_row :
    karr_divide_fused 0 (KRow [2; -4] 6 [8; 0] 10) = KRow [2; -4] 6 [8; 0] 10.
  Proof.
    vm_compute. reflexivity.
  Qed.

End FusedDivideTests.

(** * Entailment *)

Module EntailTests.

  (** The reached state with no equalities is top, so any reached state is below it. *)
  Example empty_reached_is_top :
    Equalities.leb (Reached [x1]) (Reached []) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An independent equation is not entailed by another equation on a different variable. *)
  Example independent_equation_is_not_entailed :
    Equalities.leb (Reached [x1]) (Reached [y1]) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The equalities x = 1 and y = 1 together entail x - y = 0. *)
  Example combination_is_entailed :
    Equalities.leb (Reached [x1; y1]) (Reached [same]) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Rows already in the shared basis are skipped and the entailment still holds. *)
  Example shared_basis_skips_present_rows :
    Equalities.leb (Reached [same; x1; y1]) (Reached [y1; same]) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The equality x - y = 0. *)
  Definition xy : lcons positive := LCons _ [(1%positive, 1); (2%positive, -1)] REq 0.

  (** The equality y - z = 0. *)
  Definition yz : lcons positive := LCons _ [(2%positive, 1); (3%positive, -1)] REq 0.

  (** The equality x - z = 0, which follows from xy and yz but is not one of them. *)
  Definition xz : lcons positive := LCons _ [(1%positive, 1); (3%positive, -1)] REq 0.

  (** The equality x - z = 1, which contradicts xz. *)
  Definition shifted_xz : lcons positive := LCons _ [(1%positive, 1); (3%positive, -1)] REq 1.

  (** The shared basis finds a consequence that no source row states directly. *)
  Example shared_basis_finds_absent_consequence :
    Equalities.leb (Reached [xy; yz]) (Reached [xz]) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The shared basis rejects a target that is not a consequence of the source rows. *)
  Example shared_basis_rejects_nonconsequence :
    Equalities.leb (Reached [xy; yz]) (Reached [shifted_xz]) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An infeasible source is below every reached row, so it entails them all. *)
  Example infeasible_source_is_below_any_row :
    Equalities.leb (Reached [x0; x1]) (Reached [y1]) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An infeasible source is below the unreached state. *)
  Example infeasible_source_is_below_unreached :
    Equalities.leb (Reached [x0; x1]) Unreached = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A literal inequality entails itself. *)
  Example literal_inequality_entails_itself :
    let r := LCons _ [(1%positive, 1)] RLe 3 in
    Equalities.leb (Reached [r]) (Reached [r]) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An inequality does not entail an equality on the same variable. *)
  Example inequality_does_not_entail_equality :
    Equalities.leb (Reached [LCons _ [(1%positive, 1)] RLe 1]) (Reached [x1]) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A scaled rational row, 2x = 1, entails its scaled copy 4x = 2. *)
  Example scaled_rational_row_is_entailed :
    Equalities.leb (Reached [LCons _ [(1%positive, 2)] REq 1])
      (Reached [LCons _ [(1%positive, 4)] REq 2]) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

End EntailTests.

(** * Bottom *)

Module BottomTests.

  (** Two opposite copies of the same key cancel and leave the contradiction 0 = 1. *)
  Example duplicate_keys_cancel_to_bottom :
    Equalities.is_bot
      (Reached [LCons _ [(1%positive, 1); (1%positive, -1)] REq 1]) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A rational solution of 2x = 1 is not a contradiction over the integers. *)
  Example rational_solution_is_not_bottom :
    Equalities.is_bot (Reached [LCons _ [(1%positive, 2)] REq 1]) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End BottomTests.

(** * Certificate *)

Module CertificateTests.

  (** An unsupported inequality residual is rejected before any check. *)
  Example unsupported_inequality_residual_has_no_certificate :
    Equalities.target_certificate [LCons _ [(1%positive, 1)] RLe 0]
      (LCons _ [(1%positive, 2)] RLe 0) = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A wrong equality residual is rejected before any check. *)
  Example wrong_equality_residual_has_no_certificate :
    Equalities.target_certificate [x0] x1 = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A stronger inequality residual than the source allows is rejected before any check. *)
  Example stronger_inequality_residual_has_no_certificate :
    Equalities.target_certificate [x1] (LCons _ [(1%positive, 1)] RLe 0) = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

End CertificateTests.

(** * Hull *)

Module HullTests.

  (** The affine hull of two points keeps the diagonal x = y that both points satisfy. *)
  Example join_keeps_the_diagonal :
    Equalities.leb (Equalities.join (Reached [x0; y0]) (Reached [x1; y1]))
      (Reached [same]) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The affine hull of two points drops the endpoint that is not on the hull. *)
  Example join_drops_the_endpoint :
    Equalities.leb (Equalities.join (Reached [x0; y0]) (Reached [x1; y1]))
      (Reached [x0]) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A zero-width source row cannot produce a nonzero hull equality. *)
  Example zero_width_hull_rows_are_discarded :
    Equalities.affine_hull [LCons _ [] REq 0] [LCons _ [] REq 0] = [].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The origin of three variables, as three equalities. *)
  Definition origin_rows : list (lcons positive) :=
    [LCons _ [(1%positive, 1)] REq 0;
     LCons _ [(2%positive, 1)] REq 0;
     LCons _ [(3%positive, 1)] REq 0].

  (** The point (2, 4, 6), as three equalities. *)
  Definition point_246_rows : list (lcons positive) :=
    [LCons _ [(1%positive, 1)] REq 2;
     LCons _ [(2%positive, 1)] REq 4;
     LCons _ [(3%positive, 1)] REq 6].

  (** The hull of the two points, y = 2x and z = 3x, with unit leading coefficients. *)
  Definition line_246_rows : list (lcons positive) :=
    [LCons _ [(2%positive, 1); (1%positive, -2)] REq 0;
     LCons _ [(1%positive, -3); (3%positive, 1)] REq 0].

  (** The three-dimensional point hull divides every output by its common coefficient factor. *)
  Example affine_hull_divides_common_factors :
    Equalities.affine_hull origin_rows point_246_rows = line_246_rows.
  Proof.
    vm_compute. reflexivity.
  Qed.

End HullTests.

(** * Fused hull *)

Module FusedHullTests.

  (** The origin is the first point of the fused hull fixture. *)
  Definition fused_hull_origin : list (lcons positive) :=
    [LCons _ [(1%positive, 1)] REq 0;
     LCons _ [(2%positive, 1)] REq 0;
     LCons _ [(3%positive, 1)] REq 0].

  (** The point with even coordinates is the second point of the fused hull fixture. *)
  Definition fused_hull_even_point : list (lcons positive) :=
    [LCons _ [(1%positive, 1)] REq 2;
     LCons _ [(2%positive, 1)] REq 4;
     LCons _ [(3%positive, 1)] REq 6].

  (** The fused hull gives the same gcd-normalized output as its specification. *)
  Example fused_hull_matches_specification :
    Equalities.affine_hull fused_hull_origin fused_hull_even_point =
      Equalities.affine_hull_spec fused_hull_origin fused_hull_even_point.
  Proof.
    vm_compute. reflexivity.
  Qed.

End FusedHullTests.

(** * Havoc *)

Module HavocTests.

  (** Forgetting x keeps every consequence of the remaining rows. *)
  Example havoc_keeps_consequences_of_the_rest :
    Equalities.leb (Equalities.havoc 1%positive (Reached [same; x1]))
      (Reached [y1]) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Forgetting x frees it, so x = 1 is no longer entailed. *)
  Example havoc_frees_the_variable :
    Equalities.leb (Equalities.havoc 1%positive (Reached [same; x1]))
      (Reached [x1]) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The two source rows, each with a repeated term in the variable 2 or 3. *)
  Definition duplicate_source_rows : list (lcons positive) :=
    [LCons _ [(1%positive, 1); (2%positive, 1); (2%positive, 1)] REq 0;
     LCons _ [(1%positive, 1); (3%positive, 1); (3%positive, 1)] REq 0].

  (** Forgetting x keeps a consequence of the source rows whose repeated terms are merged. *)
  Example havoc_keeps_consequence_of_duplicate_terms :
    Equalities.leb (Equalities.havoc 1%positive (Reached duplicate_source_rows))
      (Reached [LCons _ [(2%positive, -2); (3%positive, 2)] REq 0]) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An inequality survives forgetting x even after the key of x cancels inside it. *)
  Example havoc_keeps_inequality_after_cancellation :
    Equalities.havoc 1%positive
      (Reached [LCons _ [(1%positive, 1); (1%positive, -1);
        (2%positive, 2); (2%positive, -1)] RLe 7]) =
      Reached [LCons _ [(2%positive, 1)] RLe 7].
  Proof.
    vm_compute. reflexivity.
  Qed.

End HavocTests.

(** * Subst *)

Module SubstTests.

  (** Substituting x := 3 + y merges the repeated keys of the substituted row. *)
  Example subst_merges_repeated_keys :
    Equalities.subst 1%positive (Lin _ [(2%positive, 1)] 3)
      (LCons _ [(1%positive, 2); (2%positive, 1)] REq 8) =
      LCons _ [(2%positive, 3)] REq 2.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A key whose total coefficient cancels to zero still keeps the other key. *)
  Example subst_keeps_key_with_zero_total :
    Equalities.subst 1%positive
      (Lin _ [(2%positive, 1); (2%positive, -1); (3%positive, 2)] 5)
      (LCons _ [(1%positive, 1); (1%positive, -1); (2%positive, 3)] RLe 7) =
      LCons _ [(2%positive, 3)] RLe 7.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An alternating sum of the same key keeps the net coefficient of the surviving key. *)
  Example subst_keeps_alternating_zero_form :
    Equalities.subst 1%positive
      (Lin _ [(2%positive, -1); (2%positive, 1); (2%positive, -1); (2%positive, 1)] 0)
      (LCons _ [(2%positive, 1); (2%positive, 1); (1%positive, 1); (1%positive, 1)] REq 0) =
      LCons _ [(2%positive, 2)] REq 0.
  Proof.
    vm_compute. reflexivity.
  Qed.

End SubstTests.

(** * Assign *)

Module AssignTests.

  (** Assigning a leaf copies its source variable into the target. *)
  Example leaf_assignment_copies_source :
    Equalities.assign 1%positive (Leaf 2%positive) (Reached [x1; y1]) =
      Reached [LCons _ [(2%positive, -1); (1%positive, 1)] REq 0; y1].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An affine assignment rewrites the old value of the target as the new one. *)
  Example affine_assignment_updates_old_value :
    Equalities.assign_rows 1%positive (Lin _ [(1%positive, 1)] 1) [x1] =
      [LCons _ [(1%positive, 1)] REq 2].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A negative self coefficient keeps the direction of the inequality it rewrites. *)
  Example negative_self_coefficient_keeps_direction :
    Equalities.assign_rows 1%positive (Lin _ [(1%positive, -2)] 3)
      [LCons _ [(1%positive, 1)] RLe 4] =
      [LCons _ [(1%positive, -1)] RLe 5].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A canceled old value is recovered from the projection and the defining equality. *)
  Example canceled_old_value_is_projected :
    Equalities.leb
      (Reached (Equalities.assign_rows 1%positive
        (Lin _ [(1%positive, 1); (1%positive, -1); (2%positive, 1)] 1) [x1; y1]))
      (Reached [LCons _ [(1%positive, 1)] REq 2; y1]) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

End AssignTests.

(** * Pivot *)

Module PivotTests.

  (** Three nonunit pivots require exact division by the earlier pivots. *)
  Example three_pivots_recover_unique_solution :
    Equalities.leb (Reached coupled)
      (Reached [x1; LCons _ [(2%positive, 1)] REq 2;
        LCons _ [(3%positive, 1)] REq (-1)]) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A contradiction that appears only after three pivots is still detected. *)
  Example late_contradiction_is_detected :
    Equalities.is_bot
      (Reached (coupled ++ [LCons _ [(1%positive, 5); (2%positive, -2);
        (3%positive, 3)] REq 0])) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Exchanging pivots keeps the same unique solution of the system. *)
  Example pivot_exchange_keeps_solution :
    Equalities.leb
      (Reached [LCons _ [(2%positive, 2); (3%positive, 1)] REq 3;
        LCons _ [(1%positive, 3); (3%positive, 2)] REq 1;
        LCons _ [(1%positive, 1); (2%positive, 1)] REq 3])
      (Reached [x1; LCons _ [(2%positive, 1)] REq 2;
        LCons _ [(3%positive, 1)] REq (-1)]) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Negative pivots keep the same unique solution of the system. *)
  Example negative_pivots_keep_solution :
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

  (** Pivots on private variables cancel out, leaving the equations on the real variables. *)
  Example canceled_private_pivots_are_hidden :
    Equalities.leb
      (Reached [LCons _ [(4%positive, 1); (4%positive, -1);
        (1%positive, 2); (2%positive, 1)] REq 4;
        LCons _ [(5%positive, 1); (5%positive, -1);
          (1%positive, 1); (2%positive, 3)] REq 7])
      (Reached [x1; LCons _ [(2%positive, 1)] REq 2]) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

End PivotTests.

(** * Bareiss *)

Module BareissTests.

  (** The determinant of the coupled coefficients, computed by cofactor expansion. *)
  Example laplace_determinant_of_coupled_matrix :
    karr_determinant 3 [[2; 1; 1]; [1; 3; 2]; [3; 0; 4]] = 17.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The seed rows of the coupled equalities, before elimination. *)
  Definition coupled_seeds : list karr_row :=
    Equalities.seed_rows (Equalities.variables coupled) (length coupled) 0
      (map Equalities.normalize_row coupled).

  (** The instrumented Bareiss run returns the equality basis of the coupled system. *)
  Example bareiss_returns_equality_basis :
    fst (karr_bareiss_record 3 1 coupled_seeds) =
      Equalities.equality_basis (Equalities.variables coupled) coupled.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Every trace entry of the coupled run is an independent augmented minor. *)
  Example coupled_trace_entries_are_minors :
    forallb (fun z => existsb (Z.eqb z)
      (karr_signed_minors 8 (map karr_row_entries coupled_seeds)))
      (snd (karr_bareiss_record 3 1 coupled_seeds)) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The seed rows of a system with negative pivots, in an exchanged order. *)
  Definition exchanged_negative_seeds : list karr_row :=
    [KRow [0; 2; 1] 3 [1; 0; 0] 0;
     KRow [-3; 0; -2] (-1) [0; 1; 0] 0;
     KRow [-1; -1; 0] (-3) [0; 0; 1] 0].

  (** Every trace entry of the exchanged negative run is an independent augmented minor. *)
  Example exchanged_negative_trace_entries_are_minors :
    forallb (fun z => existsb (Z.eqb z)
      (karr_signed_minors 8 (map karr_row_entries exchanged_negative_seeds)))
      (snd (karr_bareiss_record 3 1 exchanged_negative_seeds)) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

End BareissTests.

(** * Range *)

Module RangeTests.

  (** The lower endpoint merges the two coefficients of x before the query is read. *)
  Example range_merges_repeated_coefficients_lower :
    fst (Equalities.range_linear
      [LCons _ [(1%positive, 3); (1%positive, -1)] REq 6]
      (Lin _ [(1%positive, 1)] 1)) = Fin 4.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The upper endpoint of the same query is the merged value as well. *)
  Example range_merges_repeated_coefficients_upper :
    snd (Equalities.range_linear
      [LCons _ [(1%positive, 3); (1%positive, -1)] REq 6]
      (Lin _ [(1%positive, 1)] 1)) = Fin 4.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A raw duplicate chain is shared by elimination and the final certificate check. *)
  Example range_checks_duplicate_chain_lower :
    fst (Equalities.range_linear
      [LCons _ [(1%positive, 1); (2%positive, -1); (2%positive, -1)] REq 0;
       LCons _ [(2%positive, 1); (2%positive, 1)] REq 6]
      (Lin _ [(1%positive, 2)] 1)) = Fin 13.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The upper endpoint of the duplicate chain is also 13. *)
  Example range_checks_duplicate_chain_upper :
    snd (Equalities.range_linear
      [LCons _ [(1%positive, 1); (2%positive, -1); (2%positive, -1)] REq 0;
       LCons _ [(2%positive, 1); (2%positive, 1)] REq 6]
      (Lin _ [(1%positive, 2)] 1)) = Fin 13.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A query outside the equality span keeps an unbounded lower endpoint. *)
  Example undetermined_query_has_no_lower_bound :
    fst (Equalities.range_linear
      [LCons _ [(1%positive, 3); (1%positive, -1)] REq 6]
      (Lin _ [(2%positive, 1)] 0)) = NegInf.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A query outside the equality span keeps an unbounded upper endpoint. *)
  Example undetermined_query_has_no_upper_bound :
    snd (Equalities.range_linear
      [LCons _ [(1%positive, 3); (1%positive, -1)] REq 6]
      (Lin _ [(2%positive, 1)] 0)) = PosInf.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An empty source still certifies the lower endpoint of a constant affine form. *)
  Example empty_source_certifies_constant_lower :
    fst (Equalities.range_linear [] (Lin _ [] 7)) = Fin 7.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An empty source still certifies the upper endpoint of a constant affine form. *)
  Example empty_source_certifies_constant_upper :
    snd (Equalities.range_linear [] (Lin _ [] 7)) = Fin 7.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A wider affine query on a rational source point has an exact integer lower endpoint. *)
  Example wide_query_has_exact_lower_endpoint :
    fst (Equalities.range_linear [LCons _ [(1%positive, 2)] REq 3]
      (Lin _ [(1%positive, 1024)] 5)) = Fin 1541.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A wider affine query on a rational source point has an exact integer upper endpoint. *)
  Example wide_query_has_exact_upper_endpoint :
    snd (Equalities.range_linear [LCons _ [(1%positive, 2)] REq 3]
      (Lin _ [(1%positive, 1024)] 5)) = Fin 1541.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A contradictory source gives an unbounded lower endpoint. *)
  Example contradictory_source_has_no_lower_bound :
    fst (Equalities.range_linear
      [LCons _ [(1%positive, 1)] REq 0; LCons _ [(1%positive, 1)] REq 1]
      (Lin _ [(1%positive, 1)] 0)) = NegInf.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A contradictory source gives an unbounded upper endpoint. *)
  Example contradictory_source_has_no_upper_bound :
    snd (Equalities.range_linear
      [LCons _ [(1%positive, 1)] REq 0; LCons _ [(1%positive, 1)] REq 1]
      (Lin _ [(1%positive, 1)] 0)) = PosInf.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A rational endpoint with no exact integer quotient gives an unbounded lower endpoint. *)
  Example inexact_integer_endpoint_has_no_lower_bound :
    fst (Equalities.range_linear [LCons _ [(1%positive, 2)] REq 3]
      (Lin _ [(1%positive, 1)] 0)) = NegInf.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A rational endpoint with no exact integer quotient gives an unbounded upper endpoint. *)
  Example inexact_integer_endpoint_has_no_upper_bound :
    snd (Equalities.range_linear [LCons _ [(1%positive, 2)] REq 3]
      (Lin _ [(1%positive, 1)] 0)) = PosInf.
  Proof.
    vm_compute. reflexivity.
  Qed.

End RangeTests.

(** * Shared basis *)

Module SharedBasisTests.

  (** A contradiction in the shared basis is found even for a target over another variable. *)
  Example contradiction_covers_target_only_variables :
    Equalities.leb
      (Reached
        [LCons _ [(1%positive, 1)] REq 0; LCons _ [(1%positive, 1)] REq 1])
      (Reached [LCons _ [(2%positive, 1)] REq 7]) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The shared basis certifies a missing affine consequence after the contradiction scan. *)
  Example basis_retains_absent_consequence :
    Equalities.leb
      (Reached
        [LCons _ [(1%positive, 1)] REq 2; LCons _ [(2%positive, 1)] REq 3])
      (Reached [LCons _ [(1%positive, 1); (2%positive, 1)] REq 5]) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An independent target is not entailed when the shared basis is consistent. *)
  Example basis_rejects_absent_nonconsequence :
    Equalities.leb
      (Reached [LCons _ [(1%positive, 1)] REq 2])
      (Reached [LCons _ [(2%positive, 1)] REq 3]) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A literal target is discharged before the shared basis is constructed. *)
  Example basis_keeps_syntactic_filter :
    Equalities.leb
      (Reached [LCons _ [(1%positive, 1)] REq 2])
      (Reached [LCons _ [(1%positive, 1)] REq 2]) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

End SharedBasisTests.

(** * Widen *)

Module WidenTests.

  (** Three equalities between neighbouring variables of x, y, z and w. *)
  Definition widening_chain_rows : list (lcons positive) :=
    [LCons _ [(1%positive, 1); (2%positive, -1)] REq 0;
     LCons _ [(2%positive, 1); (3%positive, -1)] REq 0;
     LCons _ [(3%positive, 1); (4%positive, -1)] REq 0].

  (** Three absent consequences that describe the same equality space as the chain. *)
  Definition widening_consequence_rows : list (lcons positive) :=
    [LCons _ [(1%positive, 1); (3%positive, -1)] REq 0;
     LCons _ [(2%positive, 1); (4%positive, -1)] REq 0;
     LCons _ [(1%positive, 1); (4%positive, -1)] REq 0].

  (** Widening keeps the first state when the shared basis proves reverse inclusion. *)
  Example widen_keeps_equivalent_chain :
    Equalities.widen 4%nat (Reached widening_chain_rows) (Reached widening_consequence_rows) =
      Reached widening_chain_rows.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Widening keeps the consequences when the chain is the later state and proves inclusion. *)
  Example widen_keeps_equivalent_consequences :
    Equalities.widen 4%nat (Reached widening_consequence_rows) (Reached widening_chain_rows) =
      Reached widening_consequence_rows.
  Proof.
    vm_compute. reflexivity.
  Qed.

End WidenTests.

(** * Fused basis *)

Module FusedBasisTests.

  (** A triangular system whose exact division steps give fraction-free rows. *)
  Definition fused_triangular_equalities : list (lcons positive) :=
    [LCons _ [(1%positive, 2); (2%positive, 1)] REq 0;
     LCons _ [(2%positive, 2); (3%positive, 1)] REq 0;
     LCons _ [(3%positive, 2)] REq 0].

  (** The fraction-free rows of the elimination, with their multiplier vectors and scales. *)
  Definition fused_triangular_basis : list karr_row :=
    [KRow [2; 1; 0] 0 [1; 0; 0] 0;
     KRow [0; 4; 2] 0 [0; 2; 0] 0;
     KRow [0; 0; 8] 0 [0; 0; 4] 0].

  (** The fused elimination keeps coefficients, multiplier vectors, scales and row order. *)
  Example basis_keeps_fraction_free_rows :
    Equalities.equality_basis [1; 2; 3]%positive fused_triangular_equalities =
      fused_triangular_basis.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Projecting through the fused basis keeps the complete integer row. *)
  Example projection_keeps_integer_row :
    Equalities.project 1%positive
      [LCons _ [(1%positive, 1); (2%positive, 1)] REq 0;
       LCons _ [(1%positive, 1); (2%positive, -1)] REq 0] =
      [LCons _ [(2%positive, -2)] REq 0].
  Proof.
    vm_compute. reflexivity.
  Qed.

End FusedBasisTests.
