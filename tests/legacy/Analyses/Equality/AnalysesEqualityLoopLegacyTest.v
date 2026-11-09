(** * Total-query loop compatibility

    The same raw SSA callbacks are adapted to the new and legacy numbering presentations.
    For example, an unlisted nullary operation remains true in both public finite-round queries.
    Builds on: AnalysesEqualityLoop and legacy AnalysesNumbering. *)

From Stdlib Require Import List Bool Arith PArith NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseCode.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg ProgramSsa.
From Galois.Analyses.Equality Require Import AnalysesEqualityProblem AnalysesEqualityLoop.
From GaloisLegacy.Graph Require GraphCore.
From GaloisLegacy.Views Require ViewsGraph ViewsSsa.
From GaloisLegacy.Analyses Require AnalysesNumbering.
Import List.ListNotations.

Local Open Scope nat_scope.

Definition old_graph (g : GraphModel.Graph.t nat (nat * nat)) : GraphCore.Graph.t nat (nat * nat) :=
  GraphCore.Graph.Make (GraphModel.Graph.entries g) (GraphModel.Graph.nodes g)
    (GraphModel.Graph.out g) (GraphModel.Graph.source g) (GraphModel.Graph.target g).

Definition old_definition (p : Ssa.t nat (nat * nat) nat nat unit) x :
    ViewsSsa.definition nat nat nat :=
  match Ssa.def p x with
  | ProgramSsa.Op op args => ViewsSsa.Op op args
  | ProgramSsa.Param b i => ViewsSsa.Param b i
  | ProgramSsa.Arbitrary => ViewsSsa.Arbitrary
  end.

Definition old_view (p : Ssa.t nat (nat * nat) nat nat unit) :
    ViewsSsa.ssa_view unit unit nat (nat * nat) nat nat unit :=
  ViewsSsa.SsaView
    (ViewsGraph.GraphView (old_graph (Cfg.graph (Ssa.cfg p)))
      (fun _ => 0) (fun _ _ _ _ => False) (fun _ _ _ => False))
    (old_definition p) (Ssa.home p) (Ssa.params p) (Ssa.args p)
    (fun _ => []) (fun _ _ => None) (fun _ _ => None) (fun _ => false).

Definition old_problem (np : Numbering.problem nat (nat * nat) nat nat unit) :=
  AnalysesNumbering.NumberingProblem (old_view (Numbering.ssa np))
    (Numbering.pure np) (Ssa.values (Numbering.ssa np)).

Definition old_loop (lp : Numbering.loop_info nat) :=
  AnalysesNumbering.LoopInfo (Numbering.header lp) (Numbering.body lp).

Definition old_invariant np lp x := AnalysesNumbering.invariant_in (old_problem np) (old_loop lp) x.

Definition compatibility_cfg : Cfg.t nat (nat * nat) :=
  Cfg.Make
    (GraphModel.Graph.of_pure [0] [0; 1]
      (fun n => if Nat.eqb n 0 then [(0, 1)] else if Nat.eqb n 1 then [(1, 1)] else [])
      fst snd)
    nat_encoding (codec_enc (pair_codec nat_codec nat_codec)).

Definition compatibility_loop :=
  Numbering.LoopInfo 1 (Cost.lift (fun _ => 1%N) (fun n => Nat.eqb n 1)).

Definition sparse_problem inventory :=
  Numbering.of_pure
    (Ssa.of_pure compatibility_cfg nat_encoding inventory
      (fun x =>
        match x with
        | 0 => ProgramSsa.Op 0 [1]
        | 1 => ProgramSsa.Op 0 []
        | 3 => ProgramSsa.Op 1 []
        | 4 => ProgramSsa.Param 1 0
        | _ => ProgramSsa.Arbitrary
        end)
      (fun _ => 1) (fun _ => []) (fun _ => []) (fun _ => @nil (unit * list nat)))
    nat_encoding (Nat.eqb 0).

Example legacy_unlisted_nullary :
  (NumberingLoop.invariant_in (sparse_problem [2]) compatibility_loop 1,
    old_invariant (sparse_problem [2]) compatibility_loop 1) = (true, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example legacy_malformed_inside_operand :
  (NumberingLoop.invariant_in (sparse_problem [0; 2]) compatibility_loop 0,
    old_invariant (sparse_problem [0; 2]) compatibility_loop 0) = (true, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example legacy_impurity_and_parameters :
  (NumberingLoop.invariant_in (sparse_problem [0; 2]) compatibility_loop 3,
    old_invariant (sparse_problem [0; 2]) compatibility_loop 3,
    NumberingLoop.invariant_in (sparse_problem [0; 2]) compatibility_loop 4,
    old_invariant (sparse_problem [0; 2]) compatibility_loop 4) = (false, false, false, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example legacy_empty_boundary :
  (NumberingLoop.invariant_in (sparse_problem []) compatibility_loop 1,
    old_invariant (sparse_problem []) compatibility_loop 1) = (false, false).
Proof.
  vm_compute; reflexivity.
Qed.

Definition closed_problem :=
  Numbering.of_pure
    (Ssa.of_pure compatibility_cfg nat_encoding [0; 1; 2; 3; 4; 5]
      (fun x =>
        match x with
        | 0 => ProgramSsa.Op 0 []
        | 1 => ProgramSsa.Op 0 [0; 0]
        | 2 => ProgramSsa.Op 0 [1]
        | 3 => ProgramSsa.Op 0 [4]
        | 4 => ProgramSsa.Op 0 [3]
        | 5 => ProgramSsa.Param 1 0
        | _ => ProgramSsa.Arbitrary
        end)
      (fun _ => 1) (fun _ => []) (fun _ => []) (fun _ => @nil (unit * list nat)))
    nat_encoding (Nat.eqb 0).

Example legacy_closed_chain_and_cycle :
  map (fun x =>
    (NumberingLoop.invariant_in closed_problem compatibility_loop x,
      old_invariant closed_problem compatibility_loop x)) [0; 1; 2; 3; 4; 5] =
    [(true, true); (true, true); (true, true); (false, false); (false, false); (false, false)].
Proof.
  vm_compute; reflexivity.
Qed.
