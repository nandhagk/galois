(** * IDE composition observations

    Matched returns compose caller, call, callee and return functions.
    For example, reversing the call and return changes the observed affine result.
    Builds on: Framework.Ide and Framework.IfdsTest. *)

From Stdlib Require Import List Bool Arith.
From Galois.Base Require Import Key.
From Galois.Lattice Require Import LatticeSig.
From Galois.Framework Require Import IfdsSig IdeSig Ide.
From Galois.Tests.Framework Require Import IfdsTest.
Import List.ListNotations.

Module Values <: LATTICE_OPS.
  Definition t := nat.
  Definition leb := Nat.leb.
  Definition bot := 0.
  Definition is_bot n := Nat.eqb n 0.
  Definition join := Nat.max.
End Values.
Module Affine <: MICRO_OPS Values.
  Definition t := (nat * nat)%type.
  Definition leb (f g : t) := Nat.eqb (fst f) (fst g) && Nat.eqb (snd f) (snd g).
  Definition bot : t := (0, 0).
  Definition is_bot (f : t) := leb f bot.
  Definition join (f _ : t) := f.
  Definition identity : t := (1, 0).
  Definition compose (f g : t) := (fst f * fst g, fst f * snd g + snd f).
  Definition apply (f : t) x := fst f * x + snd f.
End Affine.
Module Flow <: IDE_FLOW_OPS Prog NatKeyCode Edge Fact Values Affine.
  Definition facts := Flow.facts.
  Definition flow := Flow.flow.
  Definition seeds := Flow.seeds.
  Definition weight (_ : unit) e (_ _ : option unit) : Affine.t :=
    match e with 0 => (1, 1) | 2 => (1, 3) | _ => (1, 0) end.
End Flow.
Module A := IdeCode Prog NatKeyCode Edge Graph NatKeyCode Icfg Fact Values Affine Flow.

Example matched_return_composition_is_not_reversed :
  (A.finish tt (PathReturn None 0 2 None (Some tt) None None) [(1, 0); (2, 0)],
   Affine.apply (Affine.compose (1, 1) (Affine.compose (2, 0) (1, 3))) 4) =
    ((2, 5), 15).
Proof. vm_compute; reflexivity. Qed.
