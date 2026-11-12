(** * IDE composition observations

    Matched returns compose caller, call, callee and return functions.
    For example, reversing the call and return changes the observed affine result.
    Builds on: Framework.Ide and Framework.IfdsTest. *)

From Stdlib Require Import List Bool Arith ZArith.
From Galois.Base Require Import Key.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import ConstSig.
From Galois.Fixpoint Require Import Query.
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

Module ZValues <: LATTICE_OPS.
  Definition t := Z.
  Definition leb := Z.leb.
  Definition bot := 0%Z.
  Definition is_bot n := Z.eqb n 0%Z.
  Definition join := Z.max.
End ZValues.

Module Translation <: MICRO_OPS ZValues.
  Definition t := flat Z.
  Definition leb (a b : t) := match a, b with
    | FBot, _ | _, FTop => true
    | FVal x, FVal y => Z.eqb x y
    | _, _ => false
    end.
  Definition bot : t := FBot.
  Definition is_bot (a : t) := match a with FBot => true | _ => false end.
  Definition join (a b : t) := match a, b with
    | FBot, _ => b | _, FBot => a
    | FVal x, FVal y => if Z.eqb x y then a else FTop
    | _, _ => FTop
    end.
  Definition identity : t := FVal 0%Z.
  Definition compose (a b : t) := match a, b with
    | FBot, _ | _, FBot => FBot
    | FVal x, FVal y => FVal (x + y)%Z
    | _, _ => FTop
    end.
  Definition apply (f : t) (x : Z) := match f with
    | FVal z => (x + z)%Z
    | _ => 0%Z
    end.
End Translation.
Module AffineFlow <: IDE_FLOW_OPS Prog NatKeyCode Edge Fact ZValues Translation.
  Definition facts (_ : unit) : list (option unit) := [None].
  Definition flow (_ : unit) (_ : nat) (d : option unit) := [d].
  Definition seeds (_ : unit) : list (nat * option unit) := [(0, None)].
  Definition weight (_ : unit) e (_ _ : option unit) : Translation.t :=
    FVal (if Nat.eqb e 1 then 1%Z else 0%Z).
End AffineFlow.
Module ASys := IdeCode Prog NatKeyCode Edge Graph NatKeyCode Icfg Fact ZValues Translation AffineFlow.
Definition affine_lookup (k : ASys.key) : Translation.t :=
  match snd k with
  | (0, None) | (1, None) => FVal 0%Z
  | (2, None) | (3, None) => FVal 1%Z
  | _ => FBot
  end.
Definition affine_check lookup := forallb (fun r =>
  row_ok Translation.leb lookup (ASys.target tt r)
    (eval_query (ASys.resume tt) lookup (S (length (ASys.deps tt r))) (ASys.start tt r)))
  (ASys.rows tt).

Example affine_jump_accepts : affine_check affine_lookup = true.
Proof. vm_compute; reflexivity. Qed.

Example affine_jump_rejects_missing_return :
  affine_check (fun k => if Nat.eqb (fst (snd k)) 3 then FBot else affine_lookup k) = false.
Proof. vm_compute; reflexivity. Qed.

Example affine_different_unlisted_integer : Translation.apply (FVal 1%Z) 1000000%Z = 1000001%Z.
Proof. vm_compute; reflexivity. Qed.
