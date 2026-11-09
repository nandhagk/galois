(** * Hand-written numbering presentations

    These fixtures provide syntax directly, independently of any SSA producer.
    For example, two addition definitions share operands across consecutive blocks.
    Builds on: AnalysesEqualityProblem and ProgramSsa. *)

From Stdlib Require Import List Bool Arith NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseCode.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg ProgramSsa.
From Galois.Analyses.Equality Require Import AnalysesEqualityProblem.
Import List.ListNotations.

Module EqualityFixture.

Definition cfg : Cfg.t nat (nat * nat) :=
  Cfg.Make
    (Graph.of_pure [0] [0; 1; 2]
      (fun b => if Nat.eqb b 0 then [(0, 1)]
        else if Nat.eqb b 1 then [(1, 1); (1, 2)] else [])
      fst snd)
    nat_encoding (codec_enc (pair_codec nat_codec nat_codec)).

Definition syntax : Ssa.t nat (nat * nat) nat nat unit :=
  Ssa.of_pure cfg nat_encoding [0; 1; 2; 3; 4; 5; 6; 7]
    (fun x =>
      match x with
      | 0 => Param 0 0
      | 1 => Param 0 1
      | 2 => Op 0 [0; 1]
      | 3 => Op 0 [0; 1]
      | 4 => Op 1 [0; 1]
      | 5 => Param 1 0
      | 6 => Param 1 1
      | 7 => Param 2 0
      | _ => Arbitrary
      end)
    (fun x => if Nat.leb x 2 then 0 else if Nat.eqb x 7 then 2 else 1)
    (fun b => if Nat.eqb b 0 then [0; 1]
      else if Nat.eqb b 1 then [5; 6] else if Nat.eqb b 2 then [7] else [])
    (fun e => if Nat.eqb (fst e) 0 then [2; 2]
      else if Nat.eqb (snd e) 1 then [6; 5] else [3])
    (fun _ => []).

Definition problem := Numbering.of_pure syntax nat_encoding (Nat.eqb 0).

Example pure_addition : Numbering.pure problem 0 = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example impure_operation : Numbering.pure problem 1 = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example unknown_definition : Ssa.def syntax 8 = Arbitrary.
Proof.
  vm_compute; reflexivity.
Qed.

Example purity_callback_charged : Cost.ticks (Numbering.pure_c problem 0) = 1%N.
Proof.
  vm_compute; reflexivity.
Qed.

End EqualityFixture.
