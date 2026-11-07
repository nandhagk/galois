(** * Concretisation tactic clients

    Search closes semantic goals and leaves unsupported list algebra to its caller.
    For example, a product top follows from both component fullness laws.
    Builds on: DomainsTactics and DomainsValueTest. *)

From Stdlib Require Import List.
From Galois.Lattice Require Import LatticeConcrete LatticeSimple.
From Galois.Domains Require Import DomainsValue DomainsTactics.
From Galois.Tests.Domains Require Import DomainsValueTest.
Import List.ListNotations.

Example solve_operator :
  gamma (@bool_gamma unit) (ValueAbs.op reach_values tt [true]) tt.
Proof.
  pose proof reach_value_laws.
  assert (Hxs : Forall2 (gamma (@bool_gamma unit)) [true] [tt]).
  { constructor; [reflexivity|constructor]. }
  assert (He : ValueSem.eval unit_sem tt [tt] = Some tt) by reflexivity.
  gamma_solver.
Qed.

Example solve_top : gamma (@bool_gamma unit) (ValueAbs.top reach_values) tt.
Proof. pose proof reach_value_laws. gamma_solver. Qed.

Example solve_empty_relation :
  Forall2 (gamma (@bool_gamma unit)) [] [].
Proof. gamma_solver. Qed.

Example solve_related_operands :
  Forall2 (gamma (@bool_gamma unit)) [ValueAbs.top reach_values] [tt].
Proof. pose proof reach_value_laws. gamma_solver. Qed.

Example leave_list_algebra (xs ys zs : list nat) :
  True /\ ((xs ++ ys) ++ zs = xs ++ (ys ++ zs)).
Proof.
  gamma_solver. rewrite app_assoc. reflexivity.
Qed.
