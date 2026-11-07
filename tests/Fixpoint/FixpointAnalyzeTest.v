(** * Certified analysis outcomes

    Computation covers solved runs, exhaustion and rejection of an unlawful solver.
    For example, fuel one retains the unchecked partial cycle assignment.
    Builds on: FixpointAnalyze and FixpointCheckTest. *)

From Stdlib Require Import List Bool PArith NArith Lia.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Lattice Require Import LatticeCore LatticeHeight LatticeSimple.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointEval FixpointAnalysis
  FixpointSolver FixpointCertified FixpointKleene FixpointAnalyze.
From Galois.Tests.Fixpoint Require Import FixpointCheckTest.
Import List.ListNotations Cost.Notations.

Local Open Scope nat_scope.

Definition cycle_analysis :=
  Analysis.Make nat_encoding nat_encoding bool_lattice cycle_system cycle_static (Policy.flat nat).
Definition empty_analysis :=
  Analysis.Make nat_encoding nat_encoding bool_lattice empty_system empty_static (Policy.flat nat).

Definition cycle_observe fuel :=
  match analyze_ref cycle_analysis fuel with
  | Outcome.Solved s => Some (map (proj1_sig s) [0; 1; 2; 99])
  | _ => None
  end.

Example cycle_solved : cycle_observe 3 = Some [true; true; false; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example cycle_exhausted :
  match analyze_ref cycle_analysis 1 with
  | Outcome.OutOfFuel have => map (lookup nat_encoding bool_lattice have) [0; 1; 2]
  | _ => []
  end = [true; false; false].
Proof.
  vm_compute; reflexivity.
Qed.

Definition bad_solver : Solver.t nat nat bool :=
  Solver.Make (fun _ _ => Cost.ret (Outcome.Solved Map.empty)).

Example bad_candidate_rejected :
  match analyze_with bad_solver cycle_analysis 1 with
  | Outcome.Rejected Reason.Check_failed => true
  | _ => false
  end = true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition boolean_check_c (charge : N) (b : bool) : Cost.t bool :=
  Cost.tick charge ;; Cost.ret b.

Definition boolean_check_sound charge b :
  Cost.value (boolean_check_c charge b) = true -> b = true := fun H => H.

Example charged_certification_accepts :
  (option_map (@proj1_sig bool (fun b => b = true))
     (Cost.value (certify_checked_c (fun b => b = true) (boolean_check_c 4)
       (boolean_check_sound 4) true)),
   Cost.ticks (certify_checked_c (fun b => b = true) (boolean_check_c 4)
     (boolean_check_sound 4) true)) = (Some true, 5%N).
Proof.
  vm_compute; reflexivity.
Qed.

Example charged_certification_rejects :
  (option_map (@proj1_sig bool (fun b => b = true))
     (Cost.value (certify_checked_c (fun b => b = true) (boolean_check_c 4)
       (boolean_check_sound 4) false)),
   Cost.ticks (certify_checked_c (fun b => b = true) (boolean_check_c 4)
     (boolean_check_sound 4) false)) = (None, 5%N).
Proof.
  vm_compute; reflexivity.
Qed.

Example zero_callee_certification_overhead :
  (Cost.ticks (certify_checked_c (fun b => b = true) (boolean_check_c 0)
     (boolean_check_sound 0) true),
   Cost.ticks (certify_checked_c (fun b => b = true) (boolean_check_c 0)
     (boolean_check_sound 0) false)) = (1%N, 1%N).
Proof.
  vm_compute; reflexivity.
Qed.

Definition cycle_static_laws : System.static_laws cycle_static.
Proof.
  constructor; intros c s x Hin;
    unfold cycle_static, cycle_system, System.rhs, System.deps, System.side_targets in *;
    cbn in *; destruct (Nat.eqb c 0), (Nat.eqb c 1); cbn in *; exact Hin.
Qed.

Definition cycle_laws : Analysis.laws cycle_analysis.
Proof.
  constructor.
  - exact nat_encoding_laws.
  - exact nat_encoding_laws.
  - exact bool_laws.
  - exact cycle_static_laws.
Qed.

Definition cycle_terminates : Terminates.t cycle_analysis.
Proof.
  refine (@Terminates.Finite nat nat bool cycle_analysis (fun _ => True) bool_height I _ _).
  - intros; exact I.
  - intros; exact I.
Defined.

Example total_cycle :
  map (proj1_sig (solve cycle_analysis cycle_laws cycle_terminates)) [0; 1; 2; 99] =
    [true; true; false; false].
Proof.
  vm_compute; reflexivity.
Qed.

Definition cycle_budget : Kleene.Budget.t := Kleene.Budget.Make 3 3 0 1 2 1 0 0.

Local Lemma cycle_cost_keys x :
  Kleene.cost_key cycle_analysis x -> x = 0 \/ x = 1 \/ x = 2.
Proof.
  change ((In x [0; 1; 2; 0; 0; 0] \/
    exists c, In c [0; 1; 2; 0] /\
      In x (if Nat.eqb c 0 then [1] else if Nat.eqb c 1 then [0] else [])) ->
    x = 0 \/ x = 1 \/ x = 2).
  intros [Hout|[c [Hc Hread]]].
  - cbn in Hout; intuition congruence.
  - destruct Hc as [Hc|[Hc|[Hc|[Hc|Hbad]]]]; [| | | |contradiction];
      subst c; cbn in Hread; intuition congruence.
Qed.

Definition cycle_cost_model : Kleene.cost_model cycle_analysis cycle_budget.
Proof.
  constructor.
  - intros x Hkey; apply cycle_cost_keys in Hkey.
    destruct Hkey as [Hkey|[Hkey|Hkey]]; subst x; split; vm_compute; easy.
  - intros [] []; split; reflexivity.
  - intros c Hc; split; reflexivity.
  - intros m c Hsupport Hc; change (In c [0; 1; 2; 0]) in Hc.
    destruct Hc as [<-|[<-|[<-|[<-|Hbad]]]]; [| | | |contradiction].
    + eapply Query.within_bound with (n := 2).
      * apply Query.within_ask; [reflexivity|apply Query.within_ret].
      * change (2 <= 3)%nat; lia.
    + eapply Query.within_bound with (n := 2).
      * apply Query.within_ask; [reflexivity|apply Query.within_ret].
      * change (2 <= 3)%nat; lia.
    + apply Query.within_side, Query.within_side, Query.within_ret.
    + eapply Query.within_bound with (n := 2).
      * apply Query.within_ask; [reflexivity|apply Query.within_ret].
      * change (2 <= 3)%nat; lia.
  - intros m c Hsupport Hc; change (In c [0; 1; 2; 0]) in Hc.
    destruct Hc as [<-|[<-|[<-|[<-|Hbad]]]]; [| | | |contradiction].
    + change (1 <= 3)%nat; lia.
    + change (1 <= 3)%nat; lia.
    + change (3 <= 3)%nat; reflexivity.
    + change (1 <= 3)%nat; lia.
Qed.

Example cycle_round_budget :
  Kleene.Budget.round cycle_budget
    (length (Kleene.output_keys cycle_system cycle_static [0; 1; 2; 0])) 4 = 1656%N.
Proof.
  vm_compute; reflexivity.
Qed.

(** The cycle cost bound is instantiated from primitive budgets on all supported maps. *)
Theorem cycle_solver_cost fuel :
  (Cost.ticks (Kleene.run_c cycle_analysis fuel) <= 1658 * N.pos fuel)%N.
Proof.
  exact (Kleene.kleene_supported_cost cycle_analysis nat_encoding_laws cycle_static_laws
    cycle_budget cycle_cost_model fuel).
Qed.

Example cycle_driver_preserves_support :
  match Cost.value (iterate (Kleene.step_c cycle_analysis) 3 Map.empty) with
  | inl m => Kleene.supported cycle_analysis m
  | inr m => Kleene.supported cycle_analysis m
  end.
Proof.
  exact (Kleene.iterate_supported cycle_analysis nat_encoding_laws cycle_static_laws
    3 Map.empty (Kleene.supported_empty cycle_analysis)).
Qed.

Example unrelated_binding_is_not_supported :
  ~ Kleene.supported cycle_analysis (Map.set nat_encoding 99 false Map.empty).
Proof.
  intros [_ Hsupport].
  pose proof (Map.get_set_same nat_encoding 99 false Map.empty (Map.wf_empty nat_encoding))
    as Hget.
  specialize (Hsupport 99 false Hget).
  change (In 99 [0; 1; 2; 0; 0; 0]) in Hsupport.
  cbn in Hsupport; intuition discriminate.
Qed.

Example empty_solved :
  match analyze_ref empty_analysis 1 with
  | Outcome.Solved s => map (proj1_sig s) [0; 99]
  | _ => []
  end = [false; false].
Proof.
  vm_compute; reflexivity.
Qed.

Definition number_le (a b : option nat) :=
  match a, b with
  | Some x, Some y => Nat.leb x y
  | None, Some _ => false
  | _, None => true
  end.

Definition number_join (a b : option nat) :=
  match a, b with
  | Some x, Some y => Some (Nat.max x y)
  | _, _ => None
  end.

Definition number_lattice :=
  of_pure number_le (Some 0) number_join (fun _ _ => None) (fun _ b => b).

Definition number_succ (a : option nat) :=
  match a with
  | Some n => Some (S n)
  | None => None
  end.

Definition number_system : System.t nat nat (option nat) :=
  System.Make [0; 1; 2; 3] (fun c => Cost.ret c)
    (fun c => Cost.ret
      (if Nat.eqb c 0 then Query.Ask 2 (fun a =>
        Cost.step ;; Cost.ret (Query.Ret (number_succ a)))
       else if Nat.eqb c 1 then Query.Ask 0 (fun a => Cost.ret (Query.Ret a))
       else if Nat.eqb c 2 then Query.Ask 1 (fun a => Cost.ret (Query.Ret a))
       else Query.Side 1 (Some 2) (Query.Side 1 (Some 1) (Query.Ret (Some 0))))).

Definition number_static : System.static number_system :=
  System.Static
    (fun c => Cost.ret (if Nat.eqb c 0 then [2] else if Nat.eqb c 1 then [0]
      else if Nat.eqb c 2 then [1] else []))
    (fun c => Cost.ret (if Nat.eqb c 0 then [] else if Nat.eqb c 1 then []
      else if Nat.eqb c 2 then [] else [1; 1])).

Definition number_policy :=
  Policy.Make (fun x : nat => Cost.ret (if Nat.eqb x 3 then 1%positive else 2%positive))
    (fun x => Cost.ret (Nat.eqb x 0)) 0 0.

Definition number_analysis :=
  Analysis.Make nat_encoding nat_encoding number_lattice number_system number_static number_policy.

Example joining_unbounded_exhausts :
  match analyze_ref number_analysis 8 with
  | Outcome.OutOfFuel have =>
    map (lookup nat_encoding number_lattice have) [0; 1; 2; 3; 99]
  | _ => []
  end = [Some 8; Some 8; Some 8; Some 0; Some 0].
Proof.
  vm_compute; reflexivity.
Qed.
