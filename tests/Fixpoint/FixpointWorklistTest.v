(** * Priority worklist observations

    Fixtures distinguish exhaustion, self invalidation, duplicate rows and delayed widening.
    For example, a self-reading row needs a second evaluation and a final empty probe.
    Builds on: FixpointWorklist and the reference solver fixtures. *)

From Stdlib Require Import List Bool Arith NArith PArith Lia Relations.Relation_Operators.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet BaseHeapCost.
From Galois.Lattice Require Import LatticeCore LatticeHeight LatticeSimple.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointAnalysis
  FixpointSolver FixpointLeast FixpointKleene FixpointWorklist FixpointWorklistProof
  FixpointWorklistCost FixpointCycles FixpointWorklistWiden.
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

Definition priority_policy : Policy.t nat :=
  Policy.Make
    (fun x => Cost.ret
      (if Nat.eqb x 2 then 1%positive else if Nat.eqb x 1 then 2%positive else 3%positive))
    (fun _ => Cost.ret false) 0 0.
Definition priority_analysis :=
  Analysis.Make nat_encoding nat_encoding bool_lattice cycle_system cycle_static priority_policy.

Example target_priority_changes_the_evaluation_order :
  worklist_observe cycle_analysis 4 = None /\
  worklist_observe priority_analysis 4 = Some [true; true; false; false].
Proof.
  vm_compute; auto.
Qed.

Example duplicate_enqueue_charges_membership_without_reinvoking_priority :
  let empty := @Worklist.State nat nat bool Map.empty Heap.empty FinSet.empty Map.empty 0 in
  (Cost.ticks (Worklist.enqueue_c charged_analysis [0%nat; 0%nat] empty) -
    Cost.ticks (Worklist.enqueue_c charged_analysis [0%nat] empty))%N = 4%N.
Proof.
  vm_compute; reflexivity.
Qed.

Definition output_order_system : System.t nat nat (bool * bool) :=
  System.Make [0] (fun c => Cost.ret c)
    (fun _ => Cost.ret (Query.Side 0 (true, false) (Query.Ret (true, true)))).
Definition output_order_static : System.static output_order_system :=
  System.Static (fun _ => Cost.ret []) (fun _ => Cost.ret [0; 0]).
Definition output_order_analysis :=
  Analysis.Make nat_encoding nat_encoding widening_lattice output_order_system output_order_static
    (Policy.Make (fun _ => Cost.ret 1%positive) (fun _ => Cost.ret true) 2 0).

Example primary_precedes_sides_and_below_side_does_not_spend_delay :
  match Worklist.step output_order_analysis
    (index_system nat_encoding output_order_system output_order_static)
    (Worklist.initial output_order_analysis) with
  | inl s =>
    (lookup nat_encoding widening_lattice (Worklist.current s) 0,
     Map.find_or nat_encoding 2 0 (Worklist.delays s))
  | inr _ => ((false, false), 2)
  end = ((true, true), 1).
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

Definition counter_le (a b : option nat) :=
  match a, b with
  | Some x, Some y => Nat.leb x y
  | None, Some _ => false
  | _, None => true
  end.
Definition counter_join (a b : option nat) :=
  match a, b with
  | Some x, Some y => Some (Nat.max x y)
  | _, _ => None
  end.
Definition counter_lattice :=
  of_pure counter_le (Some 0) counter_join (fun _ _ => None) (fun _ b => b).

Definition counter_laws : lattice_laws counter_lattice.
Proof.
  constructor.
  - intros [x|]; cbn; [apply Nat.leb_refl|reflexivity].
  - intros [x|] [y|] [z|]; cbn; try discriminate; try reflexivity.
    intros Hxy Hyz; apply Nat.leb_le in Hxy; apply Nat.leb_le in Hyz; apply Nat.leb_le; lia.
  - intros [x|]; reflexivity.
  - intros [x|] [y|]; cbn; try reflexivity; apply Nat.leb_le, Nat.le_max_l.
  - intros [x|] [y|]; cbn; try reflexivity; apply Nat.leb_le, Nat.le_max_r.
  - intros [x|] [y|]; reflexivity.
  - intros [x|] [y|]; reflexivity.
  - intros x y Hxy; exact Hxy.
  - intros [x|] [y|] Hxy; cbn; try reflexivity; apply Nat.leb_refl.
Qed.

Definition counter_wrank : widening_rank counter_lattice.
Proof.
  refine (@WideningRank _ counter_lattice (fun _ => True)
    (fun value => match value with Some _ => 1 | None => 0 end) 1 _ _ _).
  - intros [x|] _; cbn; lia.
  - intros [x|] [y|] _ _ Hbelow; cbn; lia.
  - intros [x|] [y|] _ _ Hbelow; cbn in *; try discriminate; lia.
Defined.

Definition counter_successor (value : option nat) :=
  match value with
  | Some n => Some (S n)
  | None => None
  end.
Definition counter_system : System.t nat nat (option nat) :=
  System.Make [0] (fun c => Cost.ret c)
    (fun _ => Cost.ret (Query.Ask 0 (fun value => Cost.ret (Query.Ret (counter_successor value))))).
Definition counter_static : System.static counter_system :=
  System.Static (fun _ => Cost.ret [0]) (fun _ => Cost.ret []).
Definition counter_analysis selected :=
  Analysis.Make nat_encoding nat_encoding counter_lattice counter_system counter_static
    (Policy.Make (fun _ => Cost.ret 1%positive) (fun _ => Cost.ret selected) 2 0).

Definition counter_analysis_laws : Analysis.laws (counter_analysis true).
Proof.
  constructor.
  - exact nat_encoding_laws.
  - exact nat_encoding_laws.
  - exact counter_laws.
  - constructor; intros c s x Hin; exact Hin.
Qed.

Definition counter_cuts :
  cuts_every_cycle counter_static (Policy.widen_at (Analysis.policy (counter_analysis true))).
Proof.
  intros x Hcycle; induction Hcycle as [y z [_ Hfalse]|y z w Hleft IHleft Hright IHright].
  - discriminate.
  - exact IHleft.
Qed.

Example delayed_counter_cut_terminates :
  match Worklist.run (counter_analysis true) 5 with
  | Outcome.Solved m => lookup nat_encoding counter_lattice m 0 = None
  | _ => False
  end.
Proof.
  vm_compute; reflexivity.
Qed.

Example uncut_counter_keeps_growing :
  match Worklist.run (counter_analysis false) 8 with
  | Outcome.OutOfFuel _ => true
  | _ => false
  end = true.
Proof.
  vm_compute; reflexivity.
Qed.

(** Rank and delay credits instantiate the widening adequacy theorem on an unbounded counter. *)
Theorem counter_widening_adequate fuel :
  8 <= Pos.to_nat fuel ->
  exists m, Worklist.run (counter_analysis true) fuel = Outcome.Solved m.
Proof.
  exact (WorklistWiden.worklist_widen_fuel_enough (counter_analysis true) counter_analysis_laws
    counter_wrank counter_cuts fuel).
Qed.
