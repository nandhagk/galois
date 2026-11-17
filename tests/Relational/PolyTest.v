(** * Polyhedral computation fixtures

    These examples exercise rational constraints, elimination and their expression wrappers.
    For example, 2*x <= 1 does not rationally entail x <= 0.
    The groups are:
    - Certificate, which checks certificates of entailment and their rational endpoints.
    - Stop, which checks that a stopped search agrees with the full run.
    - Prune, which checks that removing constant tautologies keeps the result.
    - Parallel, which merges rows that share a left-hand side.
    - Eliminate, which eliminates a variable by Fourier-Motzkin and projects it.
    - Normalize, which divides a constraint by the gcd of its coefficients.
    - Assign, which assigns an affine form to a variable.
    - Range, which computes the bounds of an affine form.
    - Substitute and Prepare, which merge repeated keys before an operation.
    - Order, Bottom and Join, which compare, join and widen polyhedra.
    - Syntactic, which checks the fast paths that avoid the elimination engine.
    Builds on: Poly, LinCert, Linearize, ZLang and positive keys. *)

From Stdlib Require Import List ZArith.
From Galois.Base Require Import Key.
From Galois.Domains Require Import LangSig ValueSig IntervalSig ZLang.
From Galois.States Require Import EnvSig.
From Galois.Relational Require Import LinForm LinCertSig LinCert Linearize PolySig Poly.
Import List.ListNotations.

Local Open Scope Z_scope.

(** * Fixtures *)

Module FixtureLinearize := LinearizeCode PosKeyCode ZLangCode.
Module FixtureCertificate := LinCertCode PosKeyCode.
Module FixturePoly := PolyCode PosKeyCode ZLangCode FixtureLinearize FixtureCertificate.
Module GcdFixtureLinearize := ZLinearizeCode PosKeyCode.
Module GcdFixturePoly := PolyCode PosKeyCode ZLangCode GcdFixtureLinearize FixtureCertificate.

(** The row x <= b, for the variable x. *)
Definition upper_x (b : Z) : lcons positive := LCons _ [(1%positive, 1)] RLe b.

(** The row -x <= -b, which says x >= b. *)
Definition lower_x (b : Z) : lcons positive := LCons _ [(1%positive, -1)] RLe (-b).

(** The equality x = b. *)
Definition equal_x (b : Z) : lcons positive := LCons _ [(1%positive, 1)] REq b.

(** The equality y = b. *)
Definition equal_y (b : Z) : lcons positive := LCons _ [(2%positive, 1)] REq b.

(** The affine term 2x + 1, which the gcd examples assign to x or read as a range. *)
Definition gcd_assignment_term : term ZLangCode.op positive :=
  Node ZAdd [Node ZMul [Node (ZConst 2) []; Leaf 1%positive]; Node (ZConst 1) []].

(** The entailment decided by the full run of the engine, without stopping early. *)
Definition full_run_entails_row (P : list (lcons positive)) (c : lcons positive) : bool :=
  match FixturePoly.entail_engine_spec (FixturePoly.poly_normal_rows P)
      (poly_normal_row PosKeyCode.encode c) with
  | Some _ => true
  | None => false
  end.

(** * Certificate *)

Module CertificateTests.

  (** A strict rational countermodel to x <= 0 gives no entailment certificate. *)
  Example fractional_countermodel_has_no_certificate :
    FixturePoly.entail_cert [LCons _ [(1%positive, 2)] RLe 1] (upper_x 0) = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A tight rational endpoint gives a certificate without a cut. *)
  Example tight_endpoint_has_cut_free_certificate :
    FixturePoly.entail_cert [LCons _ [(1%positive, 2)] RLe 2]
      (LCons _ [(1%positive, 3)] RLe 3) = Some (Cert [3] 2 false).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A raw chain keeps its original certificate indices after shared normalization. *)
  Definition raw_certificate_chain : list (lcons positive) :=
    [LCons _ [(1%positive, 1); (2%positive, -1); (2%positive, -1)] REq 0;
     LCons _ [(2%positive, 1); (3%positive, -1); (3%positive, -1)] REq 0;
     LCons _ [(3%positive, 1)] RLe 0].

  (** The certificate found for a raw chain is accepted by the checker. *)
  Example raw_chain_certificate_is_checked :
    (match FixturePoly.entail_cert raw_certificate_chain (upper_x 0) with
     | Some k => FixtureCertificate.check_entails raw_certificate_chain (upper_x 0) k
     | None => false
     end) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Canceled source coordinates do not affect the shared normalized entailment engine. *)
  Example canceled_source_keys_are_checked :
    (let P := [LCons _ [(1%positive, 1); (1%positive, -1); (2%positive, 1)] RLe 0] in
     let c := LCons _ [(2%positive, 1)] RLe 0 in
     match FixturePoly.entail_cert P c with
     | Some k => FixtureCertificate.check_entails P c k
     | None => false
     end) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Target normalization preserves acceptance against its original repeated occurrences. *)
  Example repeated_target_is_checked :
    (let c := LCons _ [(2%positive, 1); (2%positive, -1); (1%positive, 2)] RLe 4 in
     match FixturePoly.entail_cert [upper_x 2] c with
     | Some k => FixtureCertificate.check_entails [upper_x 2] c k
     | None => false
     end) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An empty source can certify a tautology whose raw coefficients cancel. *)
  Example empty_source_certifies_canceled_target :
    FixturePoly.entail_cert [] (LCons _ [(1%positive, 1); (1%positive, -1)] RLe 0) =
      Some (Cert [] 1 false).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A direct equality target keeps its exact equality certificate. *)
  Example direct_equality_has_certificate :
    FixturePoly.entail_cert [equal_x 2] (equal_x 2) = Some (Cert [1] 1 false).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A one-sided inequality gives no certificate for an equality conclusion. *)
  Example direct_equality_rejects_halfspace :
    FixturePoly.entail_cert [upper_x 0] (equal_x 0) = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A source contradiction certifies an equality with the canonical positive scale. *)
  Example source_contradiction_certifies_equality :
    (let P := [equal_x 0; equal_x 1] in
     match FixturePoly.entail_cert P (equal_y 7) with
     | Some k => FixtureCertificate.check_entails P (equal_y 7) k
     | None => false
     end) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A divided strict row still entails its target. *)
  Example divided_row_entails_target :
    FixturePoly.entails_row [LCons _ [(1%positive, 2)] RLe 2]
      (LCons _ [(1%positive, 4)] RLe 4) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

End CertificateTests.

(** * Stop *)

Module StopTests.

  (** A source of x <= 3, y <= 4 and 2z <= 10, whose first eliminated variable proves the target. *)
  Definition stop_first_source : list (lcons positive) :=
    [upper_x 3; LCons _ [(2%positive, 1)] RLe 4; LCons _ [(3%positive, 2)] RLe 10].

  (** The target z <= 6, which the source entails. *)
  Definition stop_first_target : lcons positive := LCons _ [(3%positive, 1)] RLe 6.

  (** A source chain of x - y <= 0, y - z <= 0 and z <= 2, which needs all three variables. *)
  Definition stop_chain_source : list (lcons positive) :=
    [LCons _ [(1%positive, 1); (2%positive, -1)] RLe 0;
     LCons _ [(2%positive, 1); (3%positive, -1)] RLe 0;
     LCons _ [(3%positive, 1)] RLe 2].

  (** The stopped search proves the target after the first variable is eliminated. *)
  Example stopped_search_proves_target :
    FixturePoly.entails_row stop_first_source stop_first_target = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The full run agrees that the target follows from the source. *)
  Example stopped_search_agrees_with_full_run :
    full_run_entails_row stop_first_source stop_first_target = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The stopped run keeps both unrelated rows, since it never visits them. *)
  Example stopped_run_keeps_unvisited_rows :
    map poly_constraint
      (poly_run_stop PosKeyCode.encode PosKeyCode.eqb
        (poly_variables PosKeyCode.encode (stop_first_target :: stop_first_source))
        (poly_initial PosKeyCode.encode
          ((poly_negate stop_first_target, true) ::
            map (fun r => (r, false)) stop_first_source))) =
      [upper_x 3; LCons _ [(2%positive, 1)] RLe 4; LCons _ [] RLe (-2)].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The stopped search proves a chain that needs all three variables. *)
  Example stopped_search_proves_full_chain :
    FixturePoly.entails_row stop_chain_source (upper_x 2) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The full run agrees that the chain entails the bound z <= 2. *)
  Example full_run_proves_full_chain :
    full_run_entails_row stop_chain_source (upper_x 2) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The stopped search rejects a bound that the chain does not entail. *)
  Example stopped_search_rejects_chain_failure :
    FixturePoly.entails_row stop_chain_source (upper_x 1) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The full run rejects the same bound that the chain does not entail. *)
  Example full_run_rejects_chain_failure :
    full_run_entails_row stop_chain_source (upper_x 1) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End StopTests.

(** * Prune *)

Module PruneTests.

  (** A source whose elimination of z derives a constant tautology along the way. *)
  Definition prune_source : list (lcons positive) :=
    [LCons _ [(3%positive, 1)] RLe 1;
     LCons _ [(3%positive, -1)] RLe 0;
     LCons _ [(1%positive, 2)] RLe 4].

  (** The initial rows for the target x <= b against prune_source. *)
  Definition prune_rows (b : Z) : list (poly_row positive) :=
    poly_initial PosKeyCode.encode
      ((poly_negate (upper_x b), true) :: map (fun r => (r, false)) prune_source).

  (** The pruned search proves the target after the tautology is discarded. *)
  Example pruned_search_proves_target :
    FixturePoly.entails_row prune_source (upper_x 2) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The full run agrees that the target follows from the pruned source. *)
  Example full_run_proves_pruned_target :
    full_run_entails_row prune_source (upper_x 2) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Pruning keeps the contradiction and removes the unrelated constant row. *)
  Example pruning_keeps_contradiction :
    map poly_constraint (poly_run_prune_stop PosKeyCode.encode PosKeyCode.eqb
        [3%positive; 1%positive] (prune_rows 2)) =
      [LCons _ [] RLe 0].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Without pruning, the full run keeps the constant rows it derives. *)
  Example full_run_keeps_constant_rows :
    map poly_constraint (poly_run_stop PosKeyCode.encode PosKeyCode.eqb
        [3%positive; 1%positive] (prune_rows 2)) =
      [LCons _ [] RLe 1; LCons _ [] RLe 0].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The pruned search rejects a bound that the source does not entail. *)
  Example pruned_search_rejects_failure :
    FixturePoly.entails_row prune_source (upper_x 1) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The full run rejects the same bound that the source does not entail. *)
  Example full_run_rejects_failure :
    full_run_entails_row prune_source (upper_x 1) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A failed pruned run discards both non-strict and strict-positive constant rows. *)
  Example failed_pruned_run_discards_constant_rows :
    map poly_constraint (poly_run_prune_stop PosKeyCode.encode PosKeyCode.eqb
        [3%positive; 1%positive] (prune_rows 1)) = [].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A failed full run keeps both constant rows that the pruned run discards. *)
  Example failed_full_run_keeps_constant_rows :
    map poly_constraint (poly_run_stop PosKeyCode.encode PosKeyCode.eqb
        [3%positive; 1%positive] (prune_rows 1)) =
      [LCons _ [] RLe 1; LCons _ [] RLe 2].
  Proof.
    vm_compute. reflexivity.
  Qed.

End PruneTests.

(** * Parallel *)

Module ParallelTests.

  (** A bare row with the given constraint and strictness, and no certificate weights. *)
  Definition bare_row (c : lcons positive) (strict : bool) : poly_row positive :=
    PolyRow _ c [] strict.

  (** The constraint and strictness of a row, as a pair for comparison. *)
  Definition row_view (r : poly_row positive) : lcons positive * bool :=
    (poly_constraint r, poly_strict r).

  (** Whether some row in the list is an equality with right-hand side b. *)
  Definition has_equality (b : Z) (rows : list (poly_row positive)) : bool :=
    existsb (fun r => match lrel (poly_constraint r) with
      | REq => Z.eqb (rhs (poly_constraint r)) b
      | RLe => false
      end) rows.

  (** The entailment decided by the pruned engine, used as the reference for the parallel merge. *)
  Definition reference_entails_row (P : list (lcons positive)) (c : lcons positive) : bool :=
    match FixturePoly.entail_engine_pruned (FixturePoly.poly_normal_rows P)
        (poly_normal_row PosKeyCode.encode c) with
    | Some _ => true
    | None => false
    end.

  (** The source whose two upper bounds on x both mention z. *)
  Definition parallel_source : list (lcons positive) :=
    [LCons _ [(1%positive, 1); (3%positive, 1)] RLe 3;
     LCons _ [(1%positive, 1); (3%positive, 1)] RLe 5;
     LCons _ [(3%positive, -1)] RLe 0].

  (** The initial rows for the target c against the source P, with c negated. *)
  Definition initial_rows (P : list (lcons positive)) (c : lcons positive) :=
    poly_initial PosKeyCode.encode
      ((poly_negate (poly_normal_row PosKeyCode.encode c), true) ::
        map (fun r => (r, false)) (FixturePoly.poly_normal_rows P)).

  (** The rows after the first stage of the engine on the source and target x <= 4. *)
  Definition first_stage_rows : list (poly_row positive) :=
    poly_step PosKeyCode.encode PosKeyCode.eqb 3%positive
      (initial_rows parallel_source (upper_x 4)).

  (** The rows after the first stage, with parallel rows merged. *)
  Definition first_stage_merged : list (poly_row positive) :=
    poly_parallel_post PosKeyCode.encode first_stage_rows.

  (** A source that is inconsistent without any equality, for an equality target. *)
  Definition inconsistent_source : list (lcons positive) :=
    [LCons _ [(1%positive, 1)] RLe (-1);
     LCons _ [(1%positive, -1)] RLe 0].

  (** The merge keeps the lowest right-hand side when the rows come in one order. *)
  Example merge_selects_strongest_bound_first_order :
    map row_view (poly_parallel_merge PosKeyCode.encode
        [bare_row (upper_x 5) false; bare_row (upper_x 3) false;
         bare_row (upper_x 4) false]) =
      [(upper_x 3, false)].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The merge keeps the lowest right-hand side when the rows come in the reverse order. *)
  Example merge_selects_strongest_bound_reverse_order :
    map row_view (poly_parallel_merge PosKeyCode.encode
        [bare_row (upper_x 4) false; bare_row (upper_x 3) false;
         bare_row (upper_x 5) false]) =
      [(upper_x 3, false)].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Strictness wins an equal-bound tie when the strict row comes last. *)
  Example merge_keeps_strict_tie_first_order :
    map row_view (poly_parallel_merge PosKeyCode.encode
        [bare_row (upper_x 3) false; bare_row (upper_x 3) true]) =
      [(upper_x 3, true)].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Strictness wins an equal-bound tie when the strict row comes first. *)
  Example merge_keeps_strict_tie_reverse_order :
    map row_view (poly_parallel_merge PosKeyCode.encode
        [bare_row (upper_x 3) true; bare_row (upper_x 3) false]) =
      [(upper_x 3, true)].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Distinct equality bounds stay distinct rows even at the same left-hand side. *)
  Definition distinct_equality_rows : list (poly_row positive) :=
    poly_parallel_merge PosKeyCode.encode
      [bare_row (equal_x 2) false; bare_row (equal_x 3) false].

  (** The merge keeps two rows for the two distinct equalities. *)
  Example distinct_equalities_stay_distinct :
    length distinct_equality_rows = 2%nat.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The merged rows include the equality with right-hand side 2. *)
  Example distinct_equalities_keep_bound_2 :
    has_equality 2 distinct_equality_rows = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The merged rows include the equality with right-hand side 3. *)
  Example distinct_equalities_keep_bound_3 :
    has_equality 3 distinct_equality_rows = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The reference engine proves the target x <= 4 from the parallel source. *)
  Example reference_engine_accepts_target :
    reference_entails_row parallel_source (upper_x 4) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The current engine proves the same target x <= 4 from the parallel source. *)
  Example current_engine_accepts_target :
    FixturePoly.entails_row parallel_source (upper_x 4) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The reference engine rejects the target x <= 2, which the stronger row does not imply. *)
  Example reference_engine_rejects_target :
    reference_entails_row parallel_source (upper_x 2) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The current engine rejects the same target x <= 2. *)
  Example current_engine_rejects_target :
    FixturePoly.entails_row parallel_source (upper_x 2) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The first stage gives three rows that the filter keeps, before merging. *)
  Example first_stage_keeps_three_rows :
    length (filter poly_keep first_stage_rows) = 3%nat.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Merging the first stage leaves two rows, since two share the left-hand side. *)
  Example first_stage_merges_to_two_rows :
    length first_stage_merged = 2%nat.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The merged first stage keeps the bound 3 on x, the tighter of the two. *)
  Example first_stage_keeps_bound_3_on_x :
    map (fun r => rhs (poly_constraint r))
      (filter (fun r => Z.eqb
        (poly_coefficient PosKeyCode.eqb 1%positive (poly_constraint r)) 1) first_stage_merged) =
      [3].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The reference engine accepts an equality target from a source that is inconsistent. *)
  Example reference_engine_accepts_equality_from_inconsistency :
    reference_entails_row inconsistent_source (equal_x 0) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The current engine accepts the same equality target from the inconsistent source. *)
  Example current_engine_accepts_equality_from_inconsistency :
    FixturePoly.entails_row inconsistent_source (equal_x 0) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

End ParallelTests.

(** * Eliminate *)

Module EliminateTests.

  (** Opposite inequalities eliminate their common variable with exact multipliers. *)
  Example opposite_rows_eliminate_exactly :
    FixturePoly.fm_elim 1%positive
      [LCons _ [(1%positive, 1); (2%positive, 1)] RLe 3; lower_x 1] =
      [Tracked _ (LCons _ [(2%positive, 1)] RLe 2) [1; 1]].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A negative equality pivot keeps the other inequality's orientation. *)
  Example negative_equality_pivot_keeps_orientation :
    FixturePoly.fm_elim 1%positive
      [LCons _ [(1%positive, -2); (2%positive, 1)] REq 4; upper_x 3] =
      [Tracked _ (LCons _ [] REq 0) [0; 0];
       Tracked _ (LCons _ [(2%positive, 1)] RLe 10) [1; 2]].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A newly combined row sheds the common factor of its coefficients. *)
  Example combined_row_drops_common_factor :
    map row_of (FixturePoly.fm_elim 1%positive
      [LCons _ [(1%positive, 2); (2%positive, 2)] RLe 6;
       LCons _ [(1%positive, -2)] RLe (-2)]) =
      [LCons _ [(2%positive, 2)] RLe 4].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The checked projection accepts the divided elimination row. *)
  Example havoc_checks_divided_row :
    FixturePoly.havoc 1%positive
      (Reached [LCons _ [(1%positive, 2); (2%positive, 2)] RLe 6;
        LCons _ [(1%positive, -2)] RLe (-2)]) =
      Reached [LCons _ [(2%positive, 2)] RLe 4].
  Proof.
    vm_compute. reflexivity.
  Qed.

End EliminateTests.

(** * Normalize *)

Module NormalizeTests.

  (** Exact division handles negative equality coefficients and right-hand sides. *)
  Example signed_equality_divides_by_gcd :
    poly_constraint (poly_gcd_normalize
      (PolyRow positive (LCons _ [(1%positive, -6); (2%positive, 9)] REq (-12))
        [-3; 6] false)) =
      LCons _ [(1%positive, -2); (2%positive, 3)] REq (-4).
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An indivisible multiplier prevents division even when the constraint has a common factor. *)
  Example indivisible_multiplier_blocks_division :
    poly_constraint (poly_gcd_normalize
      (PolyRow positive (LCons _ [(1%positive, 4)] RLe 8) [1] false)) =
      LCons _ [(1%positive, 4)] RLe 8.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An indivisible right-hand side prevents any rounding into an integer cut. *)
  Example indivisible_bound_blocks_rounding :
    poly_constraint (poly_gcd_normalize
      (PolyRow positive (LCons _ [(1%positive, 2)] RLe 1) [2] false)) =
      LCons _ [(1%positive, 2)] RLe 1.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The all-zero strict row remains a contradiction when its gcd is zero. *)
  Example zero_strict_row_stays_contradiction :
    poly_contradiction (poly_gcd_normalize
      (PolyRow positive (LCons _ [] RLe 0) [0; 0] true)) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

End NormalizeTests.

(** * Assign *)

Module AssignTests.

  (** Assignment divides the new equality and its certificate by their shared factor. *)
  Example assignment_divides_new_row :
    FixturePoly.assign_linear 1%positive (Lin _ [(1%positive, 2)] 1)
      [LCons _ [(1%positive, 4)] REq 0] =
      [LCons _ [] REq 0; LCons _ [(1%positive, 2)] REq 2].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The numeric term wrapper reaches the same normalized assignment result. *)
  Example numeric_assignment_divides_new_row :
    GcdFixturePoly.assign 1%positive gcd_assignment_term
      (Reached [LCons _ [(1%positive, 4)] REq 0]) =
      Reached [LCons _ [] REq 0; LCons _ [(1%positive, 2)] REq 2].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A self-dependent affine assignment is below the expected state. *)
  Example self_dependent_assignment_uses_temporary :
    FixturePoly.leb
      (Reached (FixturePoly.assign_linear 1%positive
        (Lin _ [(1%positive, 1); (2%positive, 1)] 0) [equal_x 1; equal_y 2]))
      (Reached [equal_x 3; equal_y 2]) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A noninvertible assignment keeps the new equality and the surviving variables. *)
  Example noninvertible_assignment_keeps_new_equality :
    FixturePoly.leb
      (Reached (FixturePoly.assign_linear 1%positive
        (Lin _ [(2%positive, 1)] 2) [equal_x 10; equal_y 3]))
      (Reached [equal_x 5; equal_y 3]) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

End AssignTests.

(** * Range *)

Module RangeTests.

  (** Projected bounds include the constant part of a queried linear form. *)
  Example constant_shift_lower_endpoint :
    fst (FixturePoly.range_linear [lower_x 2; upper_x 5] (Lin _ [(1%positive, 1)] 1)) =
      Fin 3.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Projected bounds include the constant part of a queried linear form. *)
  Example constant_shift_upper_endpoint :
    snd (FixturePoly.range_linear [lower_x 2; upper_x 5] (Lin _ [(1%positive, 1)] 1)) =
      Fin 6.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Integer upper bounds round down at a fractional rational endpoint. *)
  Example range_rounds_upper_endpoint :
    snd (FixturePoly.range_linear [LCons _ [(1%positive, 2)] RLe 5]
      (Lin _ [(1%positive, 1)] 0)) = Fin 2.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A source with only an upper bound has no lower endpoint. *)
  Example upper_only_range_has_no_lower_endpoint :
    fst (FixturePoly.range_linear [LCons _ [(1%positive, 2)] RLe 5]
      (Lin _ [(1%positive, 1)] 0)) = NegInf.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Integer lower bounds round up at a fractional rational endpoint. *)
  Example range_rounds_lower_endpoint :
    fst (FixturePoly.range_linear [LCons _ [(1%positive, -2)] RLe (-5)]
      (Lin _ [(1%positive, 1)] 0)) = Fin 3.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A source with only a lower bound has no upper endpoint. *)
  Example lower_only_range_has_no_upper_endpoint :
    snd (FixturePoly.range_linear [LCons _ [(1%positive, -2)] RLe (-5)]
      (Lin _ [(1%positive, 1)] 0)) = PosInf.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A weaker second candidate leaves the first finite upper endpoint unchanged. *)
  Example weaker_upper_candidate_is_skipped :
    snd (FixturePoly.range_linear [upper_x 3; upper_x 5]
      (Lin _ [(1%positive, 1)] 0)) = Fin 3.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Without a lower bound, the candidates have no lower endpoint. *)
  Example upper_candidates_have_no_lower_endpoint :
    fst (FixturePoly.range_linear [upper_x 3; upper_x 5]
      (Lin _ [(1%positive, 1)] 0)) = NegInf.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A stronger second candidate is still checked and tightens the upper endpoint. *)
  Example stronger_upper_candidate_tightens_endpoint :
    snd (FixturePoly.range_linear [upper_x 5; upper_x 3]
      (Lin _ [(1%positive, 1)] 0)) = Fin 3.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Without a lower bound, the stronger candidate has no lower endpoint. *)
  Example stronger_upper_candidate_has_no_lower_endpoint :
    fst (FixturePoly.range_linear [upper_x 5; upper_x 3]
      (Lin _ [(1%positive, 1)] 0)) = NegInf.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An equality candidate fixes the lower endpoint before redundant bounds are skipped. *)
  Example equality_candidate_fixes_lower_endpoint :
    fst (FixturePoly.range_linear [equal_x 3; upper_x 5; lower_x 1]
      (Lin _ [(1%positive, 1)] 0)) = Fin 3.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An equality candidate fixes the upper endpoint before redundant bounds are skipped. *)
  Example equality_candidate_fixes_upper_endpoint :
    snd (FixturePoly.range_linear [equal_x 3; upper_x 5; lower_x 1]
      (Lin _ [(1%positive, 1)] 0)) = Fin 3.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Range checking merges repeated keys and removes canceled source variables once. *)
  Example repeated_source_keys_have_upper_endpoint :
    snd (FixturePoly.range_linear
      [LCons _ [(1%positive, 3); (1%positive, -1);
        (2%positive, 7); (2%positive, -7)] RLe 5]
      (Lin _ [(1%positive, 1)] 0)) = Fin 2.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Range checking merges repeated keys, so the source has no lower endpoint. *)
  Example repeated_source_keys_have_no_lower_endpoint :
    fst (FixturePoly.range_linear
      [LCons _ [(1%positive, 3); (1%positive, -1);
        (2%positive, 7); (2%positive, -7)] RLe 5]
      (Lin _ [(1%positive, 1)] 0)) = NegInf.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A raw equality with repeated keys retains its exact queried value as the lower endpoint. *)
  Example repeated_equality_lower_endpoint :
    fst (FixturePoly.range_linear [LCons _ [(1%positive, 3); (1%positive, -1)] REq 6]
      (Lin _ [(1%positive, 1)] 1)) = Fin 4.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A raw equality with repeated keys retains its exact queried value as the upper endpoint. *)
  Example repeated_equality_upper_endpoint :
    snd (FixturePoly.range_linear [LCons _ [(1%positive, 3); (1%positive, -1)] REq 6]
      (Lin _ [(1%positive, 1)] 1)) = Fin 4.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Dividing a projected equality preserves its exact rational lower endpoint. *)
  Example divided_projection_lower_endpoint :
    fst (FixturePoly.range_linear [LCons _ [(1%positive, 4)] REq 0]
      (Lin _ [(1%positive, 2)] 1)) = Fin 1.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Dividing a projected equality preserves its exact rational upper endpoint. *)
  Example divided_projection_upper_endpoint :
    snd (FixturePoly.range_linear [LCons _ [(1%positive, 4)] REq 0]
      (Lin _ [(1%positive, 2)] 1)) = Fin 1.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The numeric term wrapper returns the same lower endpoint from the divided projection. *)
  Example numeric_divided_projection_lower_endpoint :
    fst (GcdFixturePoly.range gcd_assignment_term
      (Reached [LCons _ [(1%positive, 4)] REq 0])) = Fin 1.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The numeric term wrapper returns the same upper endpoint from the divided projection. *)
  Example numeric_divided_projection_upper_endpoint :
    snd (GcdFixturePoly.range gcd_assignment_term
      (Reached [LCons _ [(1%positive, 4)] REq 0])) = Fin 1.
  Proof.
    vm_compute. reflexivity.
  Qed.

End RangeTests.

(** * Prepare *)

Module PrepareTests.

  (** The raw affine form whose alternating unit coefficients cancel to the constant 7. *)
  Definition prepared_zero_form : lin positive :=
    Lin _ (repeat (2%positive, 1) 8 ++
      concat (repeat [(2%positive, -1); (2%positive, 1)] 8) ++
      repeat (2%positive, -1) 8) 7.

  (** Signed preparation merges long alternating updates and keeps the constant. *)
  Example preparation_cancels_alternating_units :
    poly_prepare_form PosKeyCode.encode prepared_zero_form = Lin _ [] 7.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A fixture linearizer that returns the prepared form for every term. *)
  Module PreparedFixtureLinearize.
    Definition lin_of (_ : term ZLangCode.op positive) : option (lin positive * wrapr) :=
      Some (prepared_zero_form, NoWrap).
    Definition atoms_of (_ : ZLangCode.guard) (_ : list (term ZLangCode.op positive))
        : list (atom positive) := [].
  End PreparedFixtureLinearize.

  Module PreparedFixturePoly :=
    PolyCode PosKeyCode ZLangCode PreparedFixtureLinearize FixtureCertificate.

  (** The same prepared form reaches both the assignment row and its final checker. *)
  Example assignment_uses_prepared_form :
    PreparedFixturePoly.assign 1%positive (Leaf 2%positive) (Reached []) =
      Reached [equal_x 7].
  Proof.
    vm_compute. reflexivity.
  Qed.

End PrepareTests.

(** * Substitute *)

Module SubstituteTests.

  (** Substitution sums all occurrences of the substituted and surviving variables. *)
  Example subst_sums_repeated_keys :
    FixturePoly.subst 1%positive (Lin _ [(2%positive, 2)] 1)
      (LCons _ [(1%positive, 1); (1%positive, 2); (2%positive, -1)] RLe 7) =
      LCons _ [(2%positive, 5)] RLe 4.
  Proof.
    vm_compute. reflexivity.
  Qed.

End SubstituteTests.

(** * Bottom *)

Module BottomTests.

  (** Rationally inconsistent inequalities are recognized as bottom. *)
  Example inconsistent_inequalities_are_bottom :
    FixturePoly.is_bot (Reached [upper_x 0; lower_x 1]) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Inconsistent equalities also entail the explicit unreachable state. *)
  Example inconsistent_equalities_are_below_unreached :
    FixturePoly.leb (Reached [equal_x 0; equal_x 1]) Unreached = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An integer divisibility obstruction is not a rational contradiction. *)
  Example rational_solution_is_not_bottom :
    FixturePoly.is_bot (Reached [LCons _ [(1%positive, 2)] REq 1]) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End BottomTests.

(** * Order *)

Module OrderTests.

  (** Checking both inequality directions recognizes an equality conclusion. *)
  Example opposite_bounds_entail_equality :
    FixturePoly.leb (Reached [upper_x 2; lower_x 2]) (Reached [equal_x 2]) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

End OrderTests.

(** * Join *)

Module JoinTests.

  (** The weak join retains the shared weaker bound. *)
  Example join_keeps_shared_weaker_bound :
    FixturePoly.join (Reached [upper_x 1]) (Reached [upper_x 2]) = Reached [upper_x 2].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A shared row appears once while a distinct weaker row remains in the join. *)
  Example join_keeps_distinct_weaker_row :
    FixturePoly.join
      (Reached [upper_x 3; LCons _ [(2%positive, 1)] RLe 4])
      (Reached [upper_x 3; LCons _ [(2%positive, 1)] RLe 6]) =
      Reached [upper_x 3; LCons _ [(2%positive, 1)] RLe 6].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Deduplication preserves the order and multiplicity of the retained left rows. *)
  Example join_keeps_left_occurrences :
    FixturePoly.join (Reached [upper_x 3; upper_x 3]) (Reached [upper_x 3]) =
      Reached [upper_x 3; upper_x 3].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Widening drops the old bound that the candidate violates. *)
  Example widening_drops_violated_bound :
    FixturePoly.widen tt (Reached [upper_x 1]) (Reached [upper_x 2]) = Reached [].
  Proof.
    vm_compute. reflexivity.
  Qed.

End JoinTests.

(** * Syntactic *)

Module SyntacticTests.

  (** A present or stronger row is found by the fast path, which avoids the engine. *)
  Example fast_path_finds_present_and_dominated_rows :
    (match FixturePoly.poly_fast [upper_x 3] (upper_x 3),
        FixturePoly.poly_fast [upper_x 3] (upper_x 5) with
     | Some _, Some _ => true
     | _, _ => false
     end) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A weaker bound is accepted by inclusion of its polyhedron. *)
  Example weaker_bound_is_accepted :
    FixturePoly.leb (Reached [upper_x 3]) (Reached [upper_x 5]) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A stronger bound is rejected by inclusion of its polyhedron. *)
  Example stronger_bound_is_rejected :
    FixturePoly.leb (Reached [upper_x 5]) (Reached [upper_x 3]) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An equality supplies both inequality directions and its own equality conclusion. *)
  Example equality_entails_both_directions :
    map (FixturePoly.entails_row [equal_x 2])
      [upper_x 2; lower_x 2; equal_x 2] = [true; true; true].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The fast path finds the lower bound that an equality implies. *)
  Example fast_path_finds_equality_lower_bound :
    (match FixturePoly.poly_fast [equal_x 2] (lower_x 2) with
     | Some _ => true
     | None => false
     end) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A sum consequence falls through the fast path to certified elimination. *)
  Example sum_consequence_uses_engine :
    (let P := [upper_x 3; LCons _ [(2%positive, 1)] RLe 4] in
     let c := LCons _ [(1%positive, 1); (2%positive, 1)] RLe 7 in
     match FixturePoly.poly_fast P c with
     | None => FixturePoly.entails_row P c
     | Some _ => false
     end) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Raw repeated keys keep their meaning when their identical source is selected. *)
  Example repeated_row_is_checked :
    (let c := LCons _ [(1%positive, 1); (1%positive, 2)] RLe 9 in
     match FixturePoly.poly_fast [c] c with
     | Some k => FixtureCertificate.check_entails [c] c k
     | None => false
     end) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Inclusion keeps a shared row when the left side has an extra row. *)
  Example subset_inclusion_keeps_shared_row :
    (let y := LCons _ [(2%positive, 1)] RLe 4 in
     FixturePoly.leb (Reached [upper_x 3; y]) (Reached [y])) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Widening keeps a shared row when both sides are the same row. *)
  Example widening_keeps_shared_row :
    FixturePoly.widen tt (Reached [upper_x 3]) (Reached [upper_x 3]) =
      Reached [upper_x 3].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A failed first equality direction makes the entailment of the equality false. *)
  Example failed_first_direction_rejects_upper_bound :
    FixturePoly.entails_row [lower_x 3] (upper_x 3) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A failed first equality direction stops before checking the other direction. *)
  Example failed_first_direction_keeps_no_row :
    FixturePoly.keep_row [lower_x 3] (equal_x 3) = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End SyntacticTests.
