(** * SCC summary policy cycle boundary

    A single representative of an SCC need not meet every cycle in that SCC.
    For example, two mutually recursive functions can each have a self-call.
    Builds on: FrameworkSummary and GraphModel. *)

From Stdlib Require Import List Bool PArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Lattice Require Import LatticeCore LatticeSimple.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCalls.
From Galois.Fixpoint Require Import FixpointSystem FixpointCheck FixpointLeast FixpointAnalysis
  FixpointSolver FixpointKleene FixpointAnalyze.
From Galois.Framework Require Import FrameworkSummary FrameworkSummarySched FrameworkSummaryClosure.
Import List.ListNotations.

Module SummarySchedBoundary.

(** Both listed functions call both functions, including themselves. *)
Definition calls : Calls.t nat nat :=
  Calls.of_pure [0; 1] [0]
    (fun f => match f with 0 => [0] | 1 => [1] | _ => [] end)
    (fun p => p)
    (fun p => match p with 0 | 1 => [0; 1] | _ => [] end)
    nat_encoding nat_encoding.

(** This predicate records the head-only policy observation checked at commit 07c2861.
    It is historical test data and is not the current computational policy. *)
Definition historical_head_only f := Nat.eqb f 1.

Example selected_representative :
  (historical_head_only 0, historical_head_only 1) = (false, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example current_all_listed :
  (Policy.widen_at (summary_policy_scc calls) 0,
   Policy.widen_at (summary_policy_scc calls) 1,
   Policy.widen_at (summary_policy_scc calls) 2) = (true, true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example zero_self_edge :
  Graph.out (Calls.graph calls) 0 = [CallEdge 0 0; CallEdge 0 1].
Proof.
  vm_compute; reflexivity.
Qed.

(** The counterexample has a closed, duplicate-free, correctly sourced graph. *)
Theorem calls_wf : graph_wf (Calls.graph calls).
Proof.
  apply call_graph_wf.
  - repeat constructor; cbn; intuition discriminate.
  - intros f [<-|[]]; left; reflexivity.
  - intros f p Hsite.
    destruct f as [|[|f]]; cbn in Hsite; try contradiction;
      destruct Hsite as [<-|[]]; split; [reflexivity| |reflexivity|];
      cbn; auto.
  - intros p g Htarget.
    destruct p as [|[|p]]; cbn in Htarget; try contradiction;
      exact Htarget.
Qed.

(** Function zero has a nonempty cycle consisting of its self-call. *)
Theorem zero_cycle :
  path (Calls.graph calls) 0 [CallEdge 0 0] 0.
Proof.
  change (path (Calls.graph calls)
    (Graph.source (Calls.graph calls) (CallEdge 0 0)) [CallEdge 0 0] 0).
  constructor.
  - vm_compute; auto.
  - constructor.
Qed.

(** The historical head-only policy misses a cycle on a well-formed call graph. *)
Theorem historical_policy_scc_does_not_cut :
  ~ cycles_cut (Calls.graph calls)
      (fun f => historical_head_only f = true).
Proof.
  intro Hcut.
  destruct (Hcut 0 [CallEdge 0 0] (or_introl eq_refl) zero_cycle
    ltac:(discriminate)) as [Hselected|[e [Hin Hselected]]].
  - vm_compute in Hselected; discriminate.
  - destruct Hin as [<-|[]].
    vm_compute in Hselected; discriminate.
Qed.

End SummarySchedBoundary.

Module SummarySchedFixture.

Example repaired_cycles_cut :
  cycles_cut (Calls.graph SummarySchedBoundary.calls)
    (fun f => Policy.widen_at (summary_policy_scc SummarySchedBoundary.calls) f = true).
Proof.
  apply SummarySched.policy_scc_cuts; exact nat_encoding_laws.
Qed.

Example repaired_self_cycles :
  (Policy.widen_at (summary_policy_scc SummarySchedBoundary.calls)
     (Graph.target (Calls.graph SummarySchedBoundary.calls) (CallEdge 0 0)),
   Policy.widen_at (summary_policy_scc SummarySchedBoundary.calls)
     (Graph.target (Calls.graph SummarySchedBoundary.calls) (CallEdge 1 1))) =
    (true, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example ordinary_mutual_cycle :
  path (Calls.graph SummarySchedBoundary.calls) 0 [CallEdge 0 1; CallEdge 1 0] 0.
Proof.
  change (path (Calls.graph SummarySchedBoundary.calls)
    (Graph.source (Calls.graph SummarySchedBoundary.calls) (CallEdge 0 1))
    [CallEdge 0 1; CallEdge 1 0] 0).
  constructor; [vm_compute; auto|].
  change (path (Calls.graph SummarySchedBoundary.calls)
    (Graph.source (Calls.graph SummarySchedBoundary.calls) (CallEdge 1 0))
    [CallEdge 1 0] 0).
  constructor; [vm_compute; auto|constructor].
Qed.

Definition recursive_calls : Calls.t nat nat :=
  Calls.of_pure [0; 1; 2] [0]
    (fun f => match f with 0 => [0] | 1 => [1] | 2 => [2] | _ => [] end)
    (fun p => p)
    (fun p => match p with 0 => [1] | 1 => [2] | 2 => [1] | _ => [] end)
    nat_encoding nat_encoding.

Example callee_first_order :
  map (Policy.order (summary_policy_scc recursive_calls)) [0; 1; 2] =
    [4; 3; 3]%positive.
Proof.
  vm_compute; reflexivity.
Qed.

Example exact_prepared_reach_sets :
  map (fun f => map (fun g =>
    FinSet.mem nat_encoding g
      (SummaryClosure.row recursive_calls (Cost.value (Summary.closure_c recursive_calls)) f))
    [0; 1; 2]) [0; 1; 2] =
    [[true; true; true]; [false; true; true]; [false; true; true]].
Proof.
  vm_compute; reflexivity.
Qed.

Definition single : Calls.t nat nat :=
  Calls.of_pure [0] [0] (fun _ => []) (fun _ => 0) (fun _ => [])
    nat_encoding nat_encoding.

Example singleton_policy_boundary :
  (Policy.order (summary_policy_scc single) 0,
   Policy.widen_at (summary_policy_scc single) 0,
   Policy.widen_at (summary_policy_scc single) 1) = (2%positive, true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Definition pair_calls : Calls.t nat nat :=
  Calls.of_pure [0; 1] [0]
    (fun f => match f with 0 => [0] | 1 => [1] | _ => [] end)
    (fun p => p)
    (fun p => match p with 0 => [1] | 1 => [0] | _ => [] end)
    nat_encoding nat_encoding.

Definition antitone : Summary.spec nat nat bool :=
  Summary.Make bool_lattice (fun _ => Cost.ret false) (fun _ _ a => Cost.ret (negb a)).

Definition first_zero : Policy.t nat :=
  Policy.Make (fun f => Cost.ret (if Nat.eqb f 0 then 1 else 2)%positive)
    (fun _ => Cost.ret false) 0 0.

Definition first_one : Policy.t nat :=
  Policy.Make (fun f => Cost.ret (if Nat.eqb f 1 then 1 else 2)%positive)
    (fun _ => Cost.ret false) 0 0.

(** This fixture engine performs policy-ordered shared raises.
    It is not an execution of analyze_ref, whose row order is fixed. *)
Definition scheduled_raises (pol : Policy.t nat) :=
  let sys := Analysis.system (summary_analysis pair_calls antitone) in
  let order := if Pos.leb (Policy.order pol 0) (Policy.order pol 1)
    then [Summary.SLocal 0; Summary.SLocal 1; Summary.SCall 0 1; Summary.SCall 1 0]
    else [Summary.SLocal 1; Summary.SLocal 0; Summary.SCall 1 0; Summary.SCall 0 1] in
  fst (Kleene.round nat_encoding bool_lattice sys order Map.empty).

Example nonmonotone_two_schedules :
  (map (lookup nat_encoding bool_lattice (scheduled_raises first_zero)) [0; 1],
   map (lookup nat_encoding bool_lattice (scheduled_raises first_one)) [0; 1]) =
    ([true; false], [false; true]).
Proof.
  vm_compute; reflexivity.
Qed.

Example both_schedules_are_checked_post_solutions :
  (check_post bool_lattice (Analysis.system (summary_analysis pair_calls antitone))
     (lookup nat_encoding bool_lattice (scheduled_raises first_zero)),
   check_post bool_lattice (Analysis.system (summary_analysis pair_calls antitone))
     (lookup nat_encoding bool_lattice (scheduled_raises first_one))) = (true, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example negation_is_not_monotone :
  ~ monotone_fun bool_lattice bool_lattice (Summary.via_call antitone 0 1).
Proof.
  intro Hmono; specialize (Hmono false true eq_refl); vm_compute in Hmono; discriminate.
Qed.

Definition observe_ref pol :=
  match analyze_ref (SummarySched.using_policy (summary_analysis pair_calls antitone) pol) 8 with
  | Outcome.Solved s => Some (map (proj1_sig s) [0; 1])
  | _ => None
  end.

Example reference_ignores_policy_order :
  (observe_ref first_zero, observe_ref first_one) =
    (Some [true; false], Some [true; false]).
Proof.
  vm_compute; reflexivity.
Qed.

End SummarySchedFixture.
