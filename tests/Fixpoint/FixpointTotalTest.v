(** * Executable total joining clients

    Numeric fuel makes the actual total engine compute on cyclic and empty systems.
    For example, a repeated side target seeds a cycle whose rows also contain a duplicate.
    Builds on: FixpointTotal, FixpointKleene and the boolean height. *)

From Stdlib Require Import List Bool Arith NArith PArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Lattice Require Import LatticeCore LatticeSimple.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointAnalysis FixpointSolver
  FixpointLeast FixpointTotalKernel FixpointTotal FixpointKleene.
Import List.ListNotations.

Module TotalTest.

Definition cycle : System.t nat nat bool :=
  System.Make [0; 1; 2; 0] (fun c => Cost.ret c)
    (fun c => Cost.ret (match c with
      | O => Query.Ask 1 (fun b => Cost.ret (Query.Ret b))
      | S O => Query.Ask 0 (fun b => Cost.ret (Query.Ret b))
      | _ => Query.Side 0 true (Query.Side 0 false (Query.Ret false))
      end)).

Definition summaries : System.static cycle :=
  System.Static
    (fun c => Cost.ret (match c with O => [1] | S O => [0] | _ => [] end))
    (fun c => Cost.ret (match c with O => [] | S O => [] | _ => [0; 0] end)).

Definition analysis : Analysis.t nat nat bool :=
  Analysis.Make nat_encoding nat_encoding bool_lattice cycle summaries (Policy.flat nat).

Definition laws : Analysis.laws analysis.
Proof.
  constructor.
  - exact nat_encoding_laws.
  - exact nat_encoding_laws.
  - exact bool_laws.
  - constructor; intros c s x Hin; destruct c as [|[|c]];
      vm_compute in *; exact Hin.
Qed.

Definition termination : Terminates.t analysis.
Proof.
  refine (@Terminates.Finite nat nat bool analysis (fun _ => True) bool_height _ _ _);
    intros; exact I.
Defined.

Example cyclic_total :
  map (lookup nat_encoding bool_lattice (Total.run analysis termination)) [0; 1; 2; 99] =
    [true; true; false; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example cyclic_certified_total :
  map (proj1_sig (Total.solve analysis laws termination)) [0; 1; 2; 99] =
    [true; true; false; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example reference_agrees :
  match Solver.run Kleene.solver analysis 10%positive with
  | Outcome.Solved m => m = Total.run analysis termination
  | _ => False
  end.
Proof.
  vm_compute; reflexivity.
Qed.

Example numeric_fuel_retains_duplicate_reads :
  Pos.to_nat (TotalKernel.fuel analysis termination) = 8%nat.
Proof.
  vm_compute; reflexivity.
Qed.

Definition empty_system : System.t nat nat bool :=
  System.Make [] (fun c => Cost.ret c) (fun _ => Cost.ret (Query.Ret true)).

Definition empty_analysis : Analysis.t nat nat bool :=
  Analysis.Make nat_encoding nat_encoding bool_lattice empty_system
    (System.Static (fun _ => Cost.ret []) (fun _ => Cost.ret [])) (Policy.flat nat).

Definition empty_laws : Analysis.laws empty_analysis.
Proof.
  constructor.
  - exact nat_encoding_laws.
  - exact nat_encoding_laws.
  - exact bool_laws.
  - constructor; intros c s x Hin; vm_compute in Hin; contradiction.
Qed.

Definition empty_termination : Terminates.t empty_analysis.
Proof.
  refine (@Terminates.Finite nat nat bool empty_analysis (fun _ => True) bool_height _ _ _);
    intros; exact I.
Defined.

Example empty_total : Total.run empty_analysis empty_termination = Map.empty.
Proof.
  vm_compute; reflexivity.
Qed.

Example empty_certified_total :
  proj1_sig (Total.solve empty_analysis empty_laws empty_termination) 99 = false.
Proof.
  vm_compute; reflexivity.
Qed.

(** The importing post client discharges all key, lattice, static and termination premises. *)
Theorem post_client :
  post_solution bool_lattice cycle
    (lookup nat_encoding bool_lattice (Total.run analysis termination)).
Proof.
  exact (Total.total_post analysis laws termination).
Qed.

(** The importing adequacy client certifies that the actual numeric loop stops. *)
Theorem adequate_client :
  exists m, Cost.value (TotalKernel.loop_c analysis
    (FixpointIndex.index_system nat_encoding cycle summaries)
    (TotalKernel.fuel analysis termination)) = inr m.
Proof.
  exact (Total.total_solved analysis laws termination).
Qed.

(** Total computation retains its nonzero setup and loop charges. *)
Example total_is_charged : (0 < Cost.ticks (Total.run_c analysis termination))%N.
Proof.
  vm_compute; reflexivity.
Qed.

End TotalTest.
Import TotalTest.
