(** * Program-derived interval budget candidates

    These definitions record finite endpoint and variable-support candidates.
    For example, a program containing only zero has an endpoint limit of zero.
    Builds on: EnvSig, IntervalSig and WorklistSig. *)

From Stdlib Require Import List ZArith.
From Argent Require Import Std.
From Galois.Base Require Import KeySig MapSig.
From Galois.Domains Require Import IntervalSig ThresholdsSig ValueSig.
From Galois.States Require Import EnvSig.
From Galois.Fixpoint Require Import WorklistSig.

Record budget_program (X : Type) := BudgetProgram {
  budget_constants : list Z;
  budget_thresholds : list Z;
  budget_variables : list X
}.

Arguments budget_constants {X} _.
Arguments budget_thresholds {X} _.
Arguments budget_variables {X} _.

Module Type ENV_BUDGET_SPEC (X : KEY_OPS) (M : MAP_OPS X).
  Definition prog := budget_program X.t.
  Definition endpoint_limit (p : prog) : nat :=
    fold_right Nat.max 0
      (map Z.size_nat (budget_constants p ++ budget_thresholds p)).
  Definition endpoint_inv (p : prog) (b : bnd) : Prop :=
    match b with
    | Fin z => Z.size_nat z <= endpoint_limit p
    | _ => True
    end.
  Definition interval_inv (p : prog) (a : itv) : Prop :=
    match a with
    | IBot => True
    | I lo hi => endpoint_inv p lo /\ endpoint_inv p hi
    end.
  (** Stored occurrences carry both the support and endpoint restrictions. *)
  Definition env_inv (p : prog) (s : reach (M.t itv)) : Prop :=
    match s with
    | Unreached => True
    | Reached m => Forall (fun xa =>
        In (fst xa) (budget_variables p) /\ interval_inv p (snd xa)) (M.elements m) /\
        NoDup (map fst (M.elements m))
    end.
  Definition interval_vsize := endpoint_limit.
  Definition env_vsize (p : prog) : nat :=
    fold_right Nat.add 0
      (map (fun x => Pos.size_nat (X.encode x) + endpoint_limit p + 1)
        (budget_variables p)).
  Fixpoint threshold_values (w : ttree) : list Z :=
    match w with
    | TLeaf => nil
    | TNode l z r => threshold_values l ++ z :: threshold_values r
    end.
  Definition interval_wmax (_ : prog) (w : ttree) : nat :=
    2 * (length (threshold_values w) + 1).
  Definition env_wmax (p : prog) (w : ttree) : nat :=
    length (budget_variables p) * interval_wmax p w.
End ENV_BUDGET_SPEC.

Module Type ENV_BUDGET_LAWS (X : KEY) (M : MAP X)
    (Import B : ENV_BUDGET_SPEC X M).
  (** Every represented endpoint is bounded by the program metadata. *)
  Parameter interval_size_le : forall p lo hi,
    interval_inv p (I lo hi) ->
    (match lo with Fin z => Z.size_nat z | _ => 0 end) <= interval_vsize p /\
    (match hi with Fin z => Z.size_nat z | _ => 0 end) <= interval_vsize p.
End ENV_BUDGET_LAWS.

Module Type ENV_BUDGET (X : KEY) (M : MAP X) :=
  ENV_BUDGET_SPEC X M <+ ENV_BUDGET_LAWS X M.

(* SIG-QUESTION: These candidates do not implement BUDGET. Arbitrary widening
   parameters can introduce thresholds exceeding endpoint_limit p. Repeated
   arithmetic rows can also exceed this limit without widening. Program metadata
   has no supplied connection to SYSTEM_T rows or ENV_T operations. The public
   inv_bot, inv_join, inv_widen, inv_rows, size_le and wrank_le duties stay in
   WorklistSig unchanged. No closure claim is admitted here. *)

(* The separately public WORKLIST_TIME.T_run_all_heads_le remains the fallback
   when the W5 round argument is unavailable. It still requires BUDGET, S.wf and
   all_heads. It requires no cuts premise. It cannot replace a missing budget. *)
