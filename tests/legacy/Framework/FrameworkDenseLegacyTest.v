(** * Dense and gen/kill legacy comparisons

    The legacy diamond includes an unreachable component and nonterminal observations.
    For example, exit use eight propagates backward through the unreachable edge.
    Builds on: FrameworkBitvector and the legacy liveness and available generators. *)

From Stdlib Require Import List Bool PArith.
From Galois.Base Require Import BaseEncoding BaseSet.
From Galois.Lattice Require Import LatticeSet.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg.
From Galois.Fixpoint Require Import FixpointAnalysis.
From Galois.Framework Require Import FrameworkDense FrameworkBitvector.
From Galois.Tests.Framework Require Import FrameworkDenseTest FrameworkBitvectorTest.
From GaloisLegacy.Collections Require CollectionsEncoding CollectionsMap CollectionsFinSet.
From GaloisLegacy.Order Require OrderLattice.
From GaloisLegacy.Graph Require GraphCore.
From GaloisLegacy.Fixpoint Require FixpointSystem FixpointWorklist FixpointIndex.
From GaloisLegacy.Views Require ViewsGraph.
From GaloisLegacy.Analyses Require AnalysesLiveness AnalysesAvailable.
Import List.ListNotations.

Definition old_graph : GraphCore.Graph.t nat nat :=
  GraphCore.Graph.Make [0] [0; 1; 2; 3; 4; 5; 6]
    (fun n => match n with
      | 0 => [0; 1] | 1 => [2] | 2 => [3] | 3 => [4] | 5 => [5] | _ => []
      end)
    (fun e => match e with 0 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | _ => 5 end)
    (fun e => match e with 0 => 1 | 1 => 2 | 2 | 3 => 3 | 4 => 4 | _ => 6 end).

Definition old_view : ViewsGraph.graph_view nat unit nat nat :=
  ViewsGraph.GraphView old_graph (fun n => n)
    (fun _ _ _ _ => False) (fun _ _ _ => False).

Definition uses e := match e with 0 | 4 => [0] | 5 => [9] | _ => [] end.
Definition defs e := match e with 0 | 1 | 2 => [0] | 5 => [9] | _ => [] end.
Definition exits n := match n with 4 => [0] | 6 => [8] | _ => [] end.
Definition gen e := match e with 0 | 4 => [7] | _ => [] end.

Definition old_vars : AnalysesLiveness.var_view nat unit nat nat nat unit :=
  AnalysesLiveness.VarView old_view uses defs exits (fun _ _ => tt).

Definition old_expr : AnalysesAvailable.genkill_view nat unit nat nat nat unit :=
  AnalysesAvailable.GenKillView old_view gen (fun _ _ => false) (fun _ _ => Some tt).

Definition new_cfg :=
  Cfg.Make
    (Graph.of_pure (GraphCore.Graph.entries old_graph) (GraphCore.Graph.nodes old_graph)
      (GraphCore.Graph.out old_graph) (GraphCore.Graph.source old_graph)
      (GraphCore.Graph.target old_graph))
    nat_encoding nat_encoding.

Definition new_live :=
  Bitvector.of_pure new_cfg nat_encoding [0; 8; 9] Backward uses defs
    (fun n => Some (exits n)).

Definition new_avail :=
  Bitvector.of_pure new_cfg nat_encoding [7] Forward gen (fun _ => []) (fun _ => Some []).

Definition old_run {C A} (L : OrderLattice.lattice A)
    (S : FixpointSystem.System.t nat C A) (EC : CollectionsEncoding.encoding C)
    (SS : FixpointSystem.System.static S) :=
  FixpointWorklist.run_worklist CollectionsEncoding.nat_encoding EC L
    (FixpointWorklist.Scheduler (fun _ => 1%positive) (fun _ => false))
    FixpointWorklist.Joining S
    (FixpointWorklist.Declared SS
      (FixpointIndex.index_system CollectionsEncoding.nat_encoding S SS)) 256%positive.

Definition old_live_system :=
  AnalysesLiveness.liveness_system CollectionsEncoding.nat_encoding old_vars.
Definition old_live_lat :=
  AnalysesLiveness.live_lattice CollectionsEncoding.nat_encoding old_vars.
Definition old_live_result :=
  old_run old_live_lat old_live_system
    (ViewsGraph.dense_constraint_encoding CollectionsEncoding.nat_encoding
      CollectionsEncoding.nat_encoding)
    (AnalysesLiveness.liveness_static CollectionsEncoding.nat_encoding old_vars).

Definition old_avail_system :=
  AnalysesAvailable.available_system CollectionsEncoding.nat_encoding old_expr.
Definition old_avail_lat :=
  AnalysesAvailable.avail_lattice CollectionsEncoding.nat_encoding old_expr.
Definition old_avail_result :=
  old_run old_avail_lat old_avail_system
    (ViewsGraph.dense_constraint_encoding CollectionsEncoding.nat_encoding
      CollectionsEncoding.nat_encoding) (ViewsGraph.forward_static _ _ _).

Definition coordinates : list (nat * nat) :=
  flat_map (fun n => map (fun f => (n, f)) [0; 7; 8; 9]) [0; 1; 2; 3; 4; 5; 6].

Definition old_live_observe :=
  match old_live_result with
  | None => None
  | Some m => Some (map (fun nf =>
      AnalysesLiveness.fmem CollectionsEncoding.nat_encoding (snd nf)
        (FixpointSystem.lookup CollectionsEncoding.nat_encoding old_live_lat m (fst nf)))
      coordinates)
  end.

Definition new_live_observe (a : Analysis.t nat (Dense.constraint nat nat) (set_t nat_encoding)) :=
  option_map (fun ss =>
    map (fun nf => FinSet.mem nat_encoding (snd nf)
      (set_raw (nth (fst nf) ss (set_empty nat_encoding)))) coordinates)
    (observe a 32 [0; 1; 2; 3; 4; 5; 6]).

Example liveness_differential :
  new_live_observe (Bitvector.may_analysis new_live) = old_live_observe.
Proof.
  vm_compute; reflexivity.
Qed.

Example dense_liveness_differential :
  new_live_observe (Dense.analysis (Bitvector.may_dense new_live (Bitvector.prepare new_live))
    (Policy.by_code nat_encoding)) = old_live_observe.
Proof.
  vm_compute; reflexivity.
Qed.

Definition old_avail_observe :=
  match old_avail_result with
  | None => None
  | Some m => Some (map (fun n =>
      AnalysesLiveness.fmem CollectionsEncoding.nat_encoding 7
        (FixpointSystem.lookup CollectionsEncoding.nat_encoding old_avail_lat m n))
      [0; 1; 2; 3; 4; 5; 6])
  end.

Definition new_avail_observe
    (a : Analysis.t nat (Dense.constraint nat nat) (must_t nat_encoding)) :=
  option_map (map (fun v => match v with
    | All => true
    | Only s => FinSet.mem nat_encoding 7 (set_raw s)
    end)) (observe a 32 [0; 1; 2; 3; 4; 5; 6]).

Example available_differential :
  new_avail_observe (Bitvector.must_analysis new_avail) = old_avail_observe.
Proof.
  vm_compute; reflexivity.
Qed.

Example dense_available_differential :
  new_avail_observe
    (Dense.analysis (Bitvector.must_dense new_avail (Bitvector.prepare new_avail))
      (Policy.by_code nat_encoding)) = old_avail_observe.
Proof.
  vm_compute; reflexivity.
Qed.

Example liveness_unreachable_nonterminal_boundary :
  old_live_observe =
    new_live_observe (Bitvector.may_analysis new_live) /\
  match old_live_result, old_avail_result with Some _, Some _ => true | _, _ => false end = true.
Proof.
  vm_compute; split; reflexivity.
Qed.
