(** * Equality fixture observations

    Partial evaluation exposes the values compared by generated equality.
    For example, two undefined variables both denote [None].
    Builds on: EgraphEquality. *)

From Stdlib Require Import List NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding.
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

Definition equality_alg : EggAlg.t nat bool nat :=
  EggAlg.of_pure nat_encoding bool_encoding nat_encoding
    (fun _ => Some true) (fun _ _ _ => true).

Definition equality_facts : EggFact.t bool nat bool nat nat :=
  EggFact.Make bool nat bool nat nat (fun _ _ => True) (fun _ _ => Cost.ret true).

Definition ground_rule : EggRule.t nat bool nat unit bool :=
  EggRule.Make nat bool nat unit bool unit_encoding []
    (fun _ => Cost.ret None)
    (EggPattern.Var true 1) (EggPattern.Var true 2) (fun _ => Cost.ret true).

Definition unused_sub : EggSubst.t nat bool nat unit := fun _ => Cost.ret None.

(** The fixture contains an actual guarded rule derivation between distinct variable terms. *)
Theorem ground_rule_derivation :
  EggEqual.rel equality_alg (fun sem => sem = fixture_sem) equality_facts [ground_rule]
    (EggTerm.Var true 1) (EggTerm.Var true 2).
Proof.
  apply (EggEqual.rule equality_alg (fun sem => sem = fixture_sem) equality_facts
    [ground_rule] ground_rule unused_sub (fun _ => true)).
  - left; reflexivity.
  - intros h s Hsort; discriminate.
  - intros h term Hin; contradiction.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** The fixture's ground rule is semantically sound for its explicitly chosen partial model. *)
Theorem ground_rule_sound :
  EggRule.sound equality_alg (fun sem => sem = fixture_sem) equality_facts ground_rule.
Proof.
  intros sub phi l r Hsub Hfacts Hguard Hleft Hright.
  change (Some (EggTerm.Var true 1) = Some l) in Hleft.
  change (Some (EggTerm.Var true 2) = Some r) in Hright.
  injection Hleft as <-; injection Hright as <-.
  intros sem Hsem; subst sem; reflexivity.
Qed.
