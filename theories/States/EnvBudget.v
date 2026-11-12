(** * Independent environment budget groundwork

    The tower shares program-derived candidates and their endpoint obligation.
    For example, endpoint membership bounds each finite endpoint's bit size.
    Builds on: EnvBudgetSig. *)

From Stdlib Require Import ZArith.
From Argent Require Import Std.
From Galois.Base Require Import KeySig MapSig.
From Galois.Domains Require Import IntervalSig ValueSig.
From Galois.States Require Import EnvBudgetSig.
Module EnvBudgetCode (X : KEY_OPS) (M : MAP_OPS X) <: ENV_BUDGET_SPEC X M.
  Include ENV_BUDGET_SPEC X M.
End EnvBudgetCode.

Module EnvBudget (X : KEY) (M : MAP X) <: ENV_BUDGET X M.
  Include EnvBudgetCode X M.

  (** Program metadata bounds both finite endpoints of an invariant interval. *)
  Lemma interval_size_le : forall p lo hi,
    interval_inv p (I lo hi) ->
    (match lo with Fin z => Z.size_nat z | _ => 0 end) <= interval_vsize p /\
    (match hi with Fin z => Z.size_nat z | _ => 0 end) <= interval_vsize p.
  Proof. Admitted.
End EnvBudget.

(* Spec-only candidates add no executable operations or time contracts. *)
Module EnvBudgetT (X : KEY_T) (M : MAP_T X) <: ENV_BUDGET X M.
  Include EnvBudget X M.
End EnvBudgetT.
