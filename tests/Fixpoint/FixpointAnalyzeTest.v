(** * Certified analysis outcomes

    Computation covers solved runs, exhaustion and rejection of an unlawful solver.
    For example, fuel one retains the unchecked partial cycle assignment.
    Builds on: FixpointAnalyze and FixpointCheckTest. *)

From Stdlib Require Import List Bool PArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Lattice Require Import LatticeCore LatticeHeight LatticeSimple.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointEval FixpointAnalysis
  FixpointSolver FixpointCertified FixpointAnalyze.
From Galois.Tests.Fixpoint Require Import FixpointCheckTest.
Import List.ListNotations Cost.Notations.

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
