(** * Certified analysis and total joining

    Fuelled analysis certifies the reference engine and total joining supplies finite-height fuel.
    For example, an empty system solves on its first stationary round.
    Builds on: FixpointCertified and FixpointKleene. *)

From Stdlib Require Import List PArith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Lattice Require Import LatticeCore LatticeHeight.
From Galois.Fixpoint Require Import FixpointSystem FixpointLeast FixpointAnalysis FixpointSolver
  FixpointKleene FixpointCertified.
Import Cost.Notations.

Definition analyze_ref_c {X C A} (a : Analysis.t X C A) fuel :=
  analyze_with_c Kleene.solver a fuel.
Definition analyze_ref {X C A} (a : Analysis.t X C A) fuel :=
  Cost.value (analyze_ref_c a fuel).
Definition analyze_c {X C A} (a : Analysis.t X C A) fuel := analyze_ref_c a fuel.
Definition analyze {X C A} (a : Analysis.t X C A) fuel := Cost.value (analyze_c a fuel).

(** Finite-height fuel covers all declared output occurrences and a final stationary probe. *)
Definition reference_fuel {X C A} (a : Analysis.t X C A) (HT : Terminates.t a) :=
  Pos.of_succ_nat
    (length (Kleene.output_keys (Analysis.system a) (Analysis.static a)
      (System.constraints (Analysis.system a))) * bound (Terminates.hgt HT) + 1).

(** Computing the threshold retains static callback, list traversal and arithmetic work. *)
Definition reference_fuel_c {X C A} (a : Analysis.t X C A) (HT : Terminates.t a) :=
  let* keys := Kleene.output_keys_c (Analysis.system a) (Analysis.static a)
    (System.constraints (Analysis.system a)) in
  let* count := length_c keys in
  Cost.step ;;
  Cost.ret (Pos.of_succ_nat (count * bound (Terminates.hgt HT) + 1)).

(** Charged threshold preparation agrees with the public rank-capacity threshold. *)
Theorem reference_fuel_equation {X C A} (a : Analysis.t X C A) HT :
  Cost.value (reference_fuel_c a HT) = reference_fuel a HT.
Proof.
  unfold reference_fuel_c; autorewrite with galois_cost; reflexivity.
Qed.

(** The finite-height threshold produces a certified solved result. *)
Theorem analyze_ref_adequate {X C A} (a : Analysis.t X C A)
    (HL : Analysis.laws a) (HT : Terminates.t a) :
  exists s, analyze_ref a (reference_fuel a HT) = Outcome.Solved s.
Proof.
  destruct (Kleene.kleene_fuel_adequate a HL HT (reference_fuel a HT))
    as [m Hsolved].
  - unfold reference_fuel; rewrite SuccNat2Pos.id_succ; lia.
  - apply (analyze_with_accepts Kleene.solver a _ m Hsolved).
    exact (Solver.solved_sound Kleene.kleene_solver_laws a _ m HL Hsolved).
Qed.

(** Charged threshold preparation supplies the same adequate fuel. *)
Theorem analyze_prepared_adequate {X C A} (a : Analysis.t X C A)
    (HL : Analysis.laws a) (HT : Terminates.t a) :
  exists s, analyze_ref a (Cost.value (reference_fuel_c a HT)) = Outcome.Solved s.
Proof.
  rewrite reference_fuel_equation; apply (analyze_ref_adequate a HL HT).
Qed.

(** Joining analysis has a solved fuel under substantive invariant-relative height evidence. *)
Theorem analyze_adequate {X C A} (a : Analysis.t X C A) :
  Analysis.laws a -> Terminates.t a -> Analysis.joining a ->
  exists fuel s, analyze a fuel = Outcome.Solved s.
Proof.
  intros HL HT Hjoining; exists (reference_fuel a HT); apply analyze_ref_adequate, HL.
Qed.

(** A solved joining analysis is least under weak laws, least joins and query monotonicity. *)
Theorem analyze_least {X C A} (a : Analysis.t X C A) fuel s :
  Analysis.laws a -> lub_laws (Analysis.lat a) ->
  monotone_system (Analysis.lat a) (Analysis.system a) -> Analysis.joining a ->
  Policy.narrowing (Analysis.policy a) = 0 ->
  analyze a fuel = Outcome.Solved s ->
  least_solution (Analysis.lat a) (Analysis.system a) (proj1_sig s).
Proof.
  intros HL Hlub Hmono Hjoining Hnarrow Hsolved.
  destruct (analyze_with_candidate Kleene.solver a fuel s Hsolved) as [m [Hrun Hcandidate]].
  apply (reached_least (Analysis.key_enc a) (Analysis.key_laws HL)
    (Analysis.lat a) (Analysis.system a)).
  - exact (Analysis.lattice_law HL).
  - exact Hlub.
  - exact Hmono.
  - rewrite Hcandidate; apply (Kleene.kleene_reached a fuel m Hrun).
  - exact (proj2_sig s).
Qed.

(** A solved outcome contains its certificate as computational data. *)
Definition solved_result {X A R} (r : Outcome.t X A R)
    (Hsolved : exists s, r = Outcome.Solved s) : R.
Proof.
  destruct r as [s|m|why].
  - exact s.
  - exfalso; destruct Hsolved as [s H]; discriminate.
  - exfalso; destruct Hsolved as [s H]; discriminate.
Defined.

(** Extracting a total result selects the same solved outcome. *)
Theorem solved_result_spec {X A R} (r : Outcome.t X A R) Hsolved :
  r = Outcome.Solved (solved_result r Hsolved).
Proof.
  destruct r as [s|m|why]; [reflexivity| |];
    destruct Hsolved as [s H]; discriminate.
Qed.

(** Total joining uses finite-height fuel independently of any requested widening policy. *)
Definition solve_c {X C A} (a : Analysis.t X C A) (HL : Analysis.laws a)
    (HT : Terminates.t a) :=
  let* fuel := Cost.refine (reference_fuel_c a HT)
    (P := fun fuel => fuel = Cost.value (reference_fuel_c a HT)) eq_refl in
  Cost.map (fun r => solved_result (proj1_sig r) (proj2_sig r))
    (Cost.refine (analyze_ref_c a (proj1_sig fuel))
      (P := fun r => exists s, r = Outcome.Solved s)
      (eq_ind_r
        (fun f => exists s, Cost.value (analyze_ref_c a f) = Outcome.Solved s)
        (analyze_prepared_adequate a HL HT) (proj2_sig fuel))).

Definition solve {X C A} (a : Analysis.t X C A) HL HT := Cost.value (solve_c a HL HT).

(** Total joining returns the result of the certified reference run at its computed threshold. *)
Theorem solve_run {X C A} (a : Analysis.t X C A) HL HT :
  analyze_ref a (reference_fuel a HT) = Outcome.Solved (solve a HL HT).
Proof.
  unfold solve, solve_c; autorewrite with galois_cost.
  cbn [proj1_sig proj2_sig].
  rewrite <- (reference_fuel_equation a HT) at 1.
  apply solved_result_spec.
Qed.

(** Total joining is least under the separate least-join and monotonicity laws. *)
Theorem solve_least {X C A} (a : Analysis.t X C A) HL HT :
  lub_laws (Analysis.lat a) -> monotone_system (Analysis.lat a) (Analysis.system a) ->
  least_solution (Analysis.lat a) (Analysis.system a) (proj1_sig (solve a HL HT)).
Proof.
  intros Hlub Hmono.
  destruct (analyze_with_candidate Kleene.solver a _ _ (solve_run a HL HT))
    as [m [Hrun Hcandidate]].
  apply (reached_least (Analysis.key_enc a) (Analysis.key_laws HL)
    (Analysis.lat a) (Analysis.system a)).
  - exact (Analysis.lattice_law HL).
  - exact Hlub.
  - exact Hmono.
  - rewrite Hcandidate; apply (Kleene.kleene_reached a _ m Hrun).
  - exact (proj2_sig (solve a HL HT)).
Qed.

Arguments analyze_ref_c {X C A} a fuel : simpl never.
Arguments analyze_ref {X C A} a fuel : simpl never.
Arguments analyze_c {X C A} a fuel : simpl never.
Arguments analyze {X C A} a fuel : simpl never.
Arguments solve_c {X C A} a HL HT : simpl never.
Arguments solve {X C A} a HL HT : simpl never.
