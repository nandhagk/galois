(** * Sorted substitution examples

    Instantiation visits applications and returns failure for absent holes.
    For example, a repeated hole yields two copies of its bound term.
    Builds on: EgraphSyntax. *)

From Stdlib Require Import List NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Egraph Require Import EgraphSyntax.
Import List.ListNotations.

Definition sample_sub : EggSubst.t nat bool nat bool :=
  EggSubst.of_pure (fun h : bool => if h then Some (EggTerm.Var true 3) else None).

Example instantiate_repeated :
  EggSubst.instantiate sample_sub
    (EggPattern.App true 0 [EggPattern.Hole true true; EggPattern.Hole true true]) =
  Some (EggTerm.App true 0 [EggTerm.Var true 3; EggTerm.Var true 3]).
Proof.
  vm_compute. reflexivity.
Qed.

Example instantiate_missing :
  EggSubst.instantiate sample_sub (EggPattern.Hole true false) = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example instantiate_empty :
  EggSubst.instantiate_args sample_sub [] = Some [].
Proof.
  vm_compute. reflexivity.
Qed.

Example instantiate_hole_cost :
  Cost.ticks (EggSubst.instantiate_c sample_sub (EggPattern.Hole true true)) = 3%N.
Proof.
  vm_compute. reflexivity.
Qed.
