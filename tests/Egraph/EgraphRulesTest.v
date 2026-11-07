(** * Partial semantics and guards

    Evaluation stops at an undefined child, and guards read the supplied facts.
    For example, a guard can reject a fact even when a rule has no missing holes.
    Builds on: EgraphRules. *)

From Stdlib Require Import List NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding.
From Galois.Egraph Require Import EgraphSyntax EgraphRules.
Import List.ListNotations.

Definition sample_sem : EggSem.t nat bool nat :=
  EggSem.Make nat bool nat (fun v => if v then Some 4 else None)
    (fun _ args => Some (length args)).

Definition sample_rule : EggRule.t nat bool bool bool bool :=
  EggRule.Make nat bool bool bool bool bool_encoding [true]
    (fun h => Cost.lift (fun _ => 1%N) (fun h : bool => if h then Some true else None) h)
    (EggPattern.Hole true true) (EggPattern.Hole true true)
    (fun facts => Cost.lift (fun _ => 1%N) facts true).

Example denote_defined :
  EggSem.denote sample_sem (EggTerm.App true 0 [EggTerm.Var true true]) = Some 1.
Proof.
  vm_compute. reflexivity.
Qed.

Example denote_undefined :
  EggSem.denote sample_sem (EggTerm.App true 0 [EggTerm.Var true false]) = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example guard_rejects :
  EggRule.guard sample_rule (fun _ => false) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example guard_accepts :
  EggRule.guard sample_rule (fun _ => true) = true.
Proof.
  vm_compute. reflexivity.
Qed.
