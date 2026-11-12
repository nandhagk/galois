(** * Integer environment budget instance

    The budget uses the finite variables and row execution of an integer program.
    For example, every assignment writes a declared variable.
    Builds on: EnvIntBudgetSig and SystemSig. *)

From Stdlib Require Import List.
From Galois.Base Require Import KeySig MapSig.
From Galois.Domains Require Import ValueSig IntervalSig ThresholdsSig CutIntervalSig.
From Galois.States Require Import EnvSig EnvIntBudgetSig.
From Galois.Fixpoint Require Import SystemSig.

Local Open Scope nat_scope.

Module EnvIntBudget (X : KEY_T) (M : MAP_T X) (C : INTERVAL_CUTOFF)
    (L : Z_LANGUAGE_T) (T : THRESHOLDS_T) (V : CUT_INTERVAL_T C L T)
    (E : ENV_ALL X M L V) (S : SYSTEM_T E)
    (P : ENV_INT_PROGRAM X M C L T V E S) <: BUDGET E S.
  Include ENV_INT_BUDGET_SPEC X M C L T V E S P.

  (** Bottom satisfies the scoped environment invariant. *)
  Lemma inv_bot : forall p, inv p E.bot.
  Proof. Admitted. (* STUB *)
  (** Joining scoped environments preserves the invariant. *)
  Lemma inv_join : forall p a b, inv p a -> inv p b -> inv p (E.join a b).
  Proof. Admitted. (* STUB *)
  (** Narrowing scoped environments preserves the invariant. *)
  Lemma inv_narrow : forall p a b, inv p a -> inv p b -> inv p (E.narrow a b).
  Proof. Admitted. (* STUB *)
  (** Widening scoped environments preserves the invariant. *)
  Lemma inv_widen : forall p w a b, inv p a -> inv p b -> inv p (E.widen w a b).
  Proof. Admitted. (* STUB *)
  (** Scoped rows preserve the invariant on all contributions. *)
  Lemma inv_rows : forall p r look a ss, S.wf p -> In r (S.rows p) ->
    (forall x, inv p (look x)) -> S.eval p r look = Some (a, ss) ->
    inv p a /\ Forall (fun xa => inv p (snd xa)) ss.
  Proof. Admitted. (* STUB *)
  (** The declared variables bound the size of a scoped environment. *)
  Lemma size_le : forall p a, inv p a -> E.size a <= vsize p.
  Proof. Admitted. (* STUB *)
  (** The declared variables bound the number of widening units. *)
  Lemma wunits_le : forall p a, inv p a -> E.wunits a <= wunits p.
  Proof. Admitted. (* STUB *)
  (** The declared variables and thresholds bound widening rank. *)
  Lemma wrank_le : forall p w a, inv p a -> E.wrank w a <= wmax p w.
  Proof. Admitted. (* STUB *)
End EnvIntBudget.
