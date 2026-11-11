(** * Call-chain cost controls

    These controls count the actual monadic jump and checker work on generated call chains.
    For example, the doubled chain contains twice as many call and matching-return pairs.
    Builds on: FrameworkTabulate and finite graph presentations. *)

From Stdlib Require Import List NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg ProgramIcfg.
From Galois.Lattice Require Import LatticeCore LatticeHeight LatticeSimple.
From Galois.Framework Require Import FrameworkMicro FrameworkIfds FrameworkTabulate
  FrameworkTabCost.
Import List.ListNotations.

Definition call_chain (n : nat) : Ifds.t nat nat nat unit :=
  Ifds.of_pure
    (Icfg.of_pure
      (Cfg.Make (Graph.of_pure [0] (seq 0 (S (2 * n)))
        (fun k => if Nat.ltb k (2 * n) then [k] else [])
        (fun e => e) S) nat_encoding nat_encoding)
      nat_encoding
      (fun e => if Nat.even e then Icfg.Call (Nat.div2 e) else Icfg.Return (Nat.div2 e)))
    unit_encoding [] (fun _ d => [d]).

Definition call_chain_run_c n :=
  Tab.tabulate_c (Ifds.as_ide (call_chain n)) 0 1024%positive.

Example doubled_chain_cost_increases :
  (0 < Cost.ticks (call_chain_run_c 2) /\
    Cost.ticks (call_chain_run_c 2) < Cost.ticks (call_chain_run_c 4))%N.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example empty_chain_cost_is_nonzero : (0 < Cost.ticks (call_chain_run_c 0))%N.
Proof.
  vm_compute; reflexivity.
Qed.

Example doubled_chain_reaches_its_matching_exit :
  match Tab.tabulate (Ifds.as_ide (call_chain 4)) 0 1024%positive with
  | Tab.Certified _ => true
  | _ => false
  end = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example boolean_update_rank_increases :
  (rank bool_height false < rank bool_height (join bool_lattice false true))%nat.
Proof.
  apply TabCost.update_rank_progress; try exact bool_laws; exact Logic.I || reflexivity.
Qed.

Definition chain_rank_fuel n :=
  TabCost.rank_fuel (Tab.prepare (Ifds.as_ide (call_chain n)) 0) (bound bool_height).

Example constructed_rank_budget_runs_the_doubled_chain :
  match Tab.tabulate (Ifds.as_ide (call_chain 4)) 0 (chain_rank_fuel 4) with
  | Tab.Certified _ => true
  | _ => false
  end = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example rank_budget_retains_the_prepared_inventory n :
  Pos.to_nat (chain_rank_fuel n) =
    S ((1 + bound bool_height) *
      length (Tab.inventory (Tab.prepare (Ifds.as_ide (call_chain n)) 0))).
Proof.
  apply TabCost.rank_fuel_numeric.
Qed.
