(** * Gen/kill fixture solutions

    Examples run loop liveness, reaching definitions and diamond availability.
    For example, a fact generated on only one diamond arm is unavailable at the join.
    Builds on: FrameworkBitvector and FrameworkDenseTest. *)

From Stdlib Require Import List Bool NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseSet.
From Galois.Lattice Require Import LatticeCore LatticeSet.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg.
From Galois.Fixpoint Require Import FixpointSystem FixpointCheck FixpointAnalysis FixpointAnalyze.
From Galois.Framework Require Import FrameworkDense FrameworkBitvector.
From Galois.Tests.Framework Require Import FrameworkDenseTest.
Import List.ListNotations.

Definition live_problem :=
  Bitvector.of_pure loop nat_encoding [0; 1] Backward
    (fun e => match e with 1 => [0] | 2 => [1] | _ => [] end)
    (fun e => match e with 0 => [0] | _ => [] end) (fun _ => Some []).

Definition reaching_problem :=
  Bitvector.of_pure loop nat_encoding [0; 1] Forward
    (fun e => match e with 0 => [0] | 1 => [1] | _ => [] end)
    (fun e => match e with 1 => [0] | _ => [] end) (fun _ => Some []).

Definition available_problem :=
  Bitvector.of_pure diamond nat_encoding [7; 8] Forward
    (fun e => match e with 0 => [7] | 2 => [8] | _ => [] end)
    (fun _ => []) (fun _ => Some []).

(** The guide's liveness constructor uses costed Vars readers without a semantics. *)
Definition liveness {N E X} (P : Vars.t N E X) :=
  Bitvector.may_analysis
    (Bitvector.Make (Vars.cfg P) (Vars.var_enc P) (Vars.universe P) Backward
      (Vars.uses_c P) (Vars.defs_c P)
      (fun n => Cost.map Some (Vars.exits_c P n))).

Definition sets_observe {C} (a : Analysis.t nat C (set_t nat_encoding)) ns :=
  option_map (map (fun s => FinSet.elements (set_raw s))) (observe a 16 ns).

Definition must_observe {C} (a : Analysis.t nat C (must_t nat_encoding)) ns :=
  option_map (map (fun s => match s with
    | All => None
    | Only s => Some (FinSet.elements (set_raw s))
    end)) (observe a 16 ns).

Example liveness_loop :
  sets_observe (Bitvector.may_analysis live_problem) [0; 1; 2] =
    Some [[1]; [1; 0]; []].
Proof.
  vm_compute; reflexivity.
Qed.

Example reaching_loop :
  sets_observe (Bitvector.may_analysis reaching_problem) [0; 1; 2] =
    Some [[]; [1; 0]; [1; 0]].
Proof.
  vm_compute; reflexivity.
Qed.

Example available_diamond :
  must_observe (Bitvector.must_analysis available_problem) [0; 1; 2; 3; 99] =
    Some [Some []; Some [7]; Some []; Some []; None].
Proof.
  vm_compute; reflexivity.
Qed.

Example may_hand_candidate :
  check_post (Analysis.lat (Bitvector.may_analysis live_problem))
    (Analysis.system (Bitvector.may_analysis live_problem))
    (fun n => set_of_list nat_encoding
      (match n with 0 => [1] | 1 => [0; 1] | _ => [] end)) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example must_hand_candidate :
  check_post (Analysis.lat (Bitvector.must_analysis available_problem))
    (Analysis.system (Bitvector.must_analysis available_problem))
    (fun n => Only (set_of_list nat_encoding (if Nat.eqb n 1 then [7] else []))) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example may_missing_uses_rejected :
  check_post (Analysis.lat (Bitvector.may_analysis live_problem))
    (Analysis.system (Bitvector.may_analysis live_problem))
    (fun _ => set_empty nat_encoding) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example must_wrong_join_rejected :
  check_post (Analysis.lat (Bitvector.must_analysis available_problem))
    (Analysis.system (Bitvector.must_analysis available_problem))
    (fun _ => Only (set_of_list nat_encoding [7])) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Definition empty_problem :=
  Bitvector.of_pure empty nat_encoding [] Forward
    (fun _ => []) (fun _ => []) (fun _ => None).

Example empty_may :
  sets_observe (Bitvector.may_analysis empty_problem) [0] = Some [[]].
Proof.
  vm_compute; reflexivity.
Qed.

Example empty_must :
  must_observe (Bitvector.must_analysis empty_problem) [0] = Some [None].
Proof.
  vm_compute; reflexivity.
Qed.

Definition tick_problem (es : list nat) :=
  Bitvector.of_pure
    (Cfg.Make (Graph.of_pure [0] [0] (fun _ => es) (fun _ => 0) (fun _ => 0))
      nat_encoding nat_encoding)
    nat_encoding [0] Forward (fun _ => [0]) (fun _ => []) (fun _ => None).

Example prepare_tick_doubling :
  (Cost.ticks (Bitvector.prepare_c (tick_problem [0])),
   Cost.ticks (Bitvector.prepare_c (tick_problem [0; 0]))) = (37%N, 67%N).
Proof.
  vm_compute; reflexivity.
Qed.

Example prepare_tick_second_doubling :
  Cost.ticks (Bitvector.prepare_c (tick_problem [0; 0; 0; 0])) = 127%N.
Proof.
  vm_compute; reflexivity.
Qed.
