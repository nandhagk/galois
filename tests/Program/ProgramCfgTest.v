(** * Presentation fixtures

    Small presentations check enumeration, primitive charges and open syntax readers.
    For example, a self-loop remains an edge occurrence.
    Builds on: ProgramCfg, ProgramSsaPoints, ProgramCalls, ProgramIcfg and ProgramMemory. *)

From Stdlib Require Import List NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg ProgramLink ProgramSsa ProgramSsaPoints
  ProgramCalls ProgramIcfg ProgramEffects ProgramMemory.
Import List.ListNotations.

Definition three : Cfg.t nat nat :=
  Cfg.Make (Graph.of_pure [0] [0; 1; 2]
    (fun n => match n with 0 => [0] | 1 => [1; 2] | _ => [] end)
    (fun e => match e with 0 => 0 | _ => 1 end)
    (fun e => match e with 0 => 1 | 1 => 1 | _ => 2 end))
    nat_encoding nat_encoding.

Definition empty : Cfg.t nat nat :=
  Cfg.Make (Graph.of_pure [] [] (fun _ => []) (fun e => e) (fun e => e))
    nat_encoding nat_encoding.

Definition vars : Vars.t nat nat nat :=
  Vars.of_pure three nat_encoding
    (fun e => match e with 0 => [0; 1] | _ => [1] end)
    (fun _ => [0]) (fun n => match n with 2 => [2] | _ => [] end).

Example three_edges : Cfg.edges three = [0; 1; 2].
Proof.
  vm_compute; reflexivity.
Qed.

Example self_loop :
  (Graph.source (Cfg.graph three) 1, Graph.target (Cfg.graph three) 1) = (1, 1).
Proof.
  vm_compute; reflexivity.
Qed.

Example missing_node : Graph.out (Cfg.graph three) 9 = [].
Proof.
  vm_compute; reflexivity.
Qed.

Example no_edges : Cfg.edges empty = [].
Proof.
  vm_compute; reflexivity.
Qed.

Example variable_universe : Vars.universe vars = [1; 0; 2].
Proof.
  vm_compute; reflexivity.
Qed.

Example variable_primitive_ticks : Cost.ticks (Vars.uses_c vars 0) = 1%N.
Proof.
  vm_compute; reflexivity.
Qed.

Definition ssa : Ssa.t nat nat nat unit bool :=
  Ssa.of_pure three nat_encoding [0; 1]
    (fun x => match x with 0 => Param 0 0 | _ => Op tt [0] end)
    (fun _ => 0) (fun _ => [0]) (fun _ => [1]) (fun _ => [(true, [0; 1])]).

Example multi_operand_guard : Ssa.guards ssa 0 = [(true, [0; 1])].
Proof.
  vm_compute; reflexivity.
Qed.

Example ssa_definition : Ssa.def ssa 1 = Op tt [0].
Proof.
  vm_compute; reflexivity.
Qed.

Example ssa_callback_ticks : Cost.ticks (Ssa.def_c ssa 1) = 1%N.
Proof.
  vm_compute; reflexivity.
Qed.

Definition calls : Calls.t nat nat :=
  Calls.of_pure [0; 1] [0] (fun f => if Nat.eqb f 0 then [0; 1] else [])
    (fun _ => 0) (fun p => if Nat.eqb p 0 then [0; 1] else [])
    nat_encoding nat_encoding.

Example recursive_call_edges :
  Graph.out (Calls.graph calls) 0 = [CallEdge 0 0; CallEdge 0 1].
Proof.
  vm_compute; reflexivity.
Qed.

Example unresolved_site : Calls.resolve calls 1 = [].
Proof.
  vm_compute; reflexivity.
Qed.

Example empty_calls : Graph.out (Calls.graph calls) 1 = [].
Proof.
  vm_compute; reflexivity.
Qed.

Definition icfg : Icfg.t nat nat nat :=
  Icfg.of_pure three nat_encoding
    (fun e => match e with 0 => Icfg.Call 7 | 1 => Icfg.Internal | _ => Icfg.Return 7 end).

Example icfg_kinds :
  (Icfg.edge_kind icfg 0, Icfg.edge_kind icfg 1, Icfg.edge_kind icfg 2) =
  (Icfg.Call 7, Icfg.Internal, Icfg.Return 7).
Proof.
  vm_compute; reflexivity.
Qed.

Definition flags : Effects.t unit :=
  Effects.of_pure (fun _ => false) (fun _ => false) (fun _ => true) (fun _ => false)
    (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false).

Example effect_flags :
  (Effects.may_trap flags tt, Effects.observes flags tt) = (true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Definition alias : Alias.t bool :=
  Alias.of_pure (fun _ _ => false) (fun r q => (r || negb q)%bool) true.

Example barrier_regions :
  (Memory.effect_reads alias Memory.Barrier, Memory.effect_writes alias Memory.Barrier) =
    ([true], [true]).
Proof.
  vm_compute; reflexivity.
Qed.

Example pure_write_has_no_read : Memory.effect_reads alias (Memory.Write false) = [].
Proof.
  vm_compute; reflexivity.
Qed.

Example alias_primitive_ticks : Cost.ticks (Alias.covers_c alias true false) = 1%N.
Proof.
  vm_compute; reflexivity.
Qed.
