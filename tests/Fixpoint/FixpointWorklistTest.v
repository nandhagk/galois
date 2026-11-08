(** * Priority worklist observations

    Fixtures distinguish exhaustion, self invalidation, duplicate rows and delayed widening.
    For example, a self-reading row needs a second evaluation and a final empty probe.
    Builds on: FixpointWorklist and the reference solver fixtures. *)

From Stdlib Require Import List Bool NArith PArith.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet BaseHeapCost.
From Galois.Lattice Require Import LatticeCore LatticeSimple.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointAnalysis
  FixpointSolver FixpointLeast FixpointKleene FixpointWorklist FixpointWorklistProof
  FixpointWorklistCost.
From Galois.Tests.Fixpoint Require Import FixpointCheckTest FixpointAnalyzeTest.
Import List.ListNotations Cost.Notations.

Local Open Scope nat_scope.

Definition worklist_observe (a : Analysis.t nat nat bool) fuel :=
  match Worklist.run a fuel with
  | Outcome.Solved m => Some (map (lookup nat_encoding bool_lattice m) [0; 1; 2; 99])
  | _ => None
  end.

Example empty_one_probe :
  Worklist.run empty_analysis 1 = Outcome.Solved Map.empty.
Proof.
  vm_compute; reflexivity.
Qed.

Example cycle_with_repeated_row_and_side_targets :
  worklist_observe cycle_analysis 8 = Some [true; true; false; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example cycle_matches_reference :
  worklist_observe cycle_analysis 8 =
    match Solver.run Kleene.solver cycle_analysis 8 with
    | Outcome.Solved m => Some (map (lookup nat_encoding bool_lattice m) [0; 1; 2; 99])
    | _ => None
    end.
Proof.
  vm_compute; reflexivity.
Qed.

Example fuel_exhaustion_keeps_partial_assignment :
  match Worklist.run cycle_analysis 1 with
  | Outcome.OutOfFuel m => map (lookup nat_encoding bool_lattice m) [0; 1; 2]
  | _ => []
  end = [false; false; false].
Proof.
  vm_compute; reflexivity.
Qed.

Definition self_system : System.t nat nat bool :=
  System.Make [0] (fun c => Cost.ret c)
    (fun _ => Cost.ret (Query.Ask 0
      (fun _ => Cost.ret (Query.Side 0 true (Query.Ret false))))).

Definition self_static : System.static self_system :=
  System.Static (fun _ => Cost.ret [0; 0]) (fun _ => Cost.ret [0; 0]).

Definition self_analysis :=
  Analysis.Make nat_encoding nat_encoding bool_lattice self_system self_static (Policy.flat nat).

Example self_change_requeues_popped_row :
  match Worklist.step self_analysis (index_system nat_encoding self_system self_static)
    (Worklist.initial self_analysis) with
  | inl s =>
    (FinSet.mem nat_encoding 0 (Worklist.queued s),
     Worklist.evaluations s,
     lookup nat_encoding bool_lattice (Worklist.current s) 0)
  | inr _ => (false, 0%nat, false)
  end = (true, 1%nat, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example final_probe_is_required :
  worklist_observe self_analysis 2 = None /\
  worklist_observe self_analysis 3 = Some [true; false; false; false].
Proof.
  vm_compute; auto.
Qed.

Definition widening_lattice : lattice (bool * bool) :=
  of_pure
    (fun a b => (negb (fst a) || fst b) && (negb (snd a) || snd b))
    (false, false)
    (fun a b => (fst a || fst b, snd a || snd b))
    (fun _ _ => (true, true))
    (fun a b => (fst a && fst b, snd a && snd b)).

Definition widening_system : System.t nat nat (bool * bool) :=
  System.Make [0] (fun c => Cost.ret c) (fun _ => Cost.ret (Query.Ret (true, false))).
Definition widening_static : System.static widening_system :=
  System.Static (fun _ => Cost.ret []) (fun _ => Cost.ret []).
Definition widening_analysis delay :=
  Analysis.Make nat_encoding nat_encoding widening_lattice widening_system widening_static
    (Policy.Make (fun _ => Cost.ret 1%positive) (fun _ => Cost.ret true) delay 0).

Definition widening_observe delay :=
  match Worklist.run (widening_analysis delay) 2 with
  | Outcome.Solved m => lookup nat_encoding widening_lattice m 0
  | _ => (false, false)
  end.

Example zero_delay_widens_first_change :
  widening_observe 0 = (true, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example positive_delay_joins_first_change :
  widening_observe 1 = (true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Definition charged_policy : Policy.t nat :=
  Policy.Make
    (fun _ => Cost.tick 7 ;; Cost.ret 1%positive)
    (fun _ => Cost.tick 11 ;; Cost.ret false) 0 0.
Definition charged_analysis :=
  Analysis.Make nat_encoding nat_encoding bool_lattice self_system self_static charged_policy.

Example callback_charges_are_retained :
  (Cost.ticks (Worklist.run_c charged_analysis 3) -
    Cost.ticks (Worklist.run_c self_analysis 3))%N = 25%N.
Proof.
  vm_compute; reflexivity.
Qed.

Example duplicate_initial_rows_do_not_duplicate_heap_entries :
  Heap.size (Worklist.queue (Worklist.initial cycle_analysis)) = 3%nat.
Proof.
  vm_compute; reflexivity.
Qed.

Example selected_query_and_queue_work_is_charged :
  (0 < Cost.ticks (Worklist.run_c self_analysis 3))%N.
Proof.
  vm_compute; reflexivity.
Qed.

(** The actual duplicate-preserving reader lists instantiate the joining evaluation bound. *)
Theorem cycle_evaluation_prefix_bound n next :
  runs (Worklist.step_c cycle_analysis (index_system nat_encoding cycle_system cycle_static))
    n (Worklist.initial cycle_analysis) (inl next) -> n <= 10.
Proof.
  exact (WorklistCost.worklist_evals_bound cycle_analysis cycle_laws cycle_terminates
    (fun _ => eq_refl) _ (index_system_laws nat_encoding nat_encoding_laws _ _) n next).
Qed.

(** The public adequacy theorem gives solved fuel without assuming a whole-run result. *)
Theorem cycle_adequate fuel :
  10 < Pos.to_nat fuel -> exists m, Worklist.run cycle_analysis fuel = Outcome.Solved m.
Proof.
  exact (WorklistCost.worklist_fuel_enough cycle_analysis cycle_laws cycle_terminates
    (fun _ => eq_refl) fuel).
Qed.

(** The full solver-law client proves soundness and reached leastness for solved cycle runs. *)
Theorem cycle_priority_least fuel m (HM : monotone_system bool_lattice cycle_system) :
  Worklist.run cycle_analysis fuel = Outcome.Solved m ->
  least_solution bool_lattice cycle_system (lookup nat_encoding bool_lattice m).
Proof.
  intro Hrun; apply (proj2 (WorklistProof.worklist_reached_least cycle_analysis fuel m
    cycle_laws bool_lub (fun _ => eq_refl) HM Hrun)).
Qed.

Definition chain_query c : Query.t nat bool :=
  if Nat.eqb c 0 then Query.Ret true
  else Query.Ask (Nat.pred c) (fun value => Cost.ret (Query.Ret value)).

Definition chain_system : System.t nat nat bool :=
  System.Make [0; 1; 2; 3; 4] (fun c => Cost.ret c) (fun c => Cost.ret (chain_query c)).
Definition charged_chain_system : System.t nat nat bool :=
  System.Make [0; 1; 2; 3; 4] (fun c => Cost.ret c)
    (fun c => Cost.step ;; Cost.ret (chain_query c)).
Definition chain_static : System.static chain_system :=
  System.Static (fun c => Cost.ret (if Nat.eqb c 0 then [] else [Nat.pred c]))
    (fun _ => Cost.ret []).
Definition charged_chain_static : System.static charged_chain_system :=
  System.Static (fun c => Cost.ret (if Nat.eqb c 0 then [] else [Nat.pred c]))
    (fun _ => Cost.ret []).
Definition chain_analysis :=
  Analysis.Make nat_encoding nat_encoding bool_lattice chain_system chain_static (Policy.flat nat).
Definition charged_chain_analysis :=
  Analysis.Make nat_encoding nat_encoding bool_lattice charged_chain_system
    charged_chain_static (Policy.flat nat).

Example chain_five_charged_evaluations :
  (Cost.ticks (Worklist.run_c charged_chain_analysis 10) -
    Cost.ticks (Worklist.run_c chain_analysis 10))%N = 5%N.
Proof.
  vm_compute; reflexivity.
Qed.

Example chain_counts_use_prepared_lists :
  (WorklistCost.constraint_count chain_analysis,
   WorklistCost.dependency_count chain_analysis
     (index_system nat_encoding chain_system chain_static)) = (5, 4).
Proof.
  vm_compute; reflexivity.
Qed.

Example chain_exhausts_before_empty_probe :
  match Worklist.run chain_analysis 5 with
  | Outcome.OutOfFuel m => map (lookup nat_encoding bool_lattice m) [0; 1; 2; 3; 4]
  | _ => []
  end = [true; true; true; true; true].
Proof.
  vm_compute; reflexivity.
Qed.
