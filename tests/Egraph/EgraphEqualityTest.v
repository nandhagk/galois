(** * Equality fixture observations

    Partial evaluation exposes the values compared by generated equality.
    For example, two undefined variables both denote [None].
    Builds on: EgraphEquality. *)

From Stdlib Require Import List.
From Galois.Egraph Require Import EgraphSyntax EgraphRules EgraphEquality.
Import List.ListNotations.

Definition fixture_sem : EggSem.t nat nat nat :=
  EggSem.Make nat nat nat (fun _ => None) (fun _ _ => Some 0).

Example undefined_results_agree :
  EggSem.denote fixture_sem (EggTerm.Var true 1) =
  EggSem.denote fixture_sem (EggTerm.Var true 2).
Proof.
  vm_compute. reflexivity.
Qed.

Example defined_and_undefined_differ :
  EggSem.denote fixture_sem (EggTerm.App true 0 []) <>
  EggSem.denote fixture_sem (EggTerm.Var true 1).
Proof.
  vm_compute. discriminate.
Qed.
