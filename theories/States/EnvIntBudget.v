(** * Integer environment budget instance

    The budget uses the finite variables and row execution of an integer program.
    For example, every assignment writes a declared variable.
    Builds on: EnvIntBudgetSig and SystemSig. *)

From Stdlib Require Import List PArith Bool Lia.
From Stdlib.Sorting Require Import Permutation.
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

  (** Every successful lookup in an invariant map names a declared variable. *)
  Lemma inv_get : forall p m x a, inv p (Reached m) ->
    M.get x m = Some a -> In x (P.variables p).
  Proof.
    intros p m x a [Hwf Hsupport] Hget.
    rewrite Forall_forall in Hsupport.
    apply (Hsupport (x, a)).
    apply (proj2 (M.elements_spec V.t m x a Hwf)). exact Hget.
  Qed.

  (** Consistent maps with declared lookup keys satisfy the environment invariant. *)
  Lemma inv_of_get : forall p m, M.wf m ->
    (forall x a, M.get x m = Some a -> In x (P.variables p)) -> inv p (Reached m).
  Proof.
    intros p m Hwf Hget. split; [exact Hwf|]. apply Forall_forall.
    intros [x a] Hin. apply (Hget x a).
    apply (proj1 (M.elements_spec V.t m x a Hwf)). exact Hin.
  Qed.

  (** A merge preserving absence stores only keys from its two invariant inputs. *)
  Lemma inv_merge : forall p ma mb (f : option V.t -> option V.t -> option V.t),
    inv p (Reached ma) -> inv p (Reached mb) -> f None None = None ->
    inv p (Reached (M.merge f ma mb)).
  Proof.
    intros p ma mb f Ha Hb Hnone. apply inv_of_get.
    - apply M.wf_merge; [exact (proj1 Ha)|exact (proj1 Hb)].
    - intros x a Hget. rewrite (M.get_merge V.t V.t V.t f ma mb x Hnone) in Hget.
      destruct (M.get x ma) as [va|] eqn:Hleft.
      + exact (inv_get p ma x va Ha Hleft).
      + destruct (M.get x mb) as [vb|] eqn:Hright.
        * exact (inv_get p mb x vb Hb Hright).
        * now rewrite Hnone in Hget.
  Qed.

  (** Bottom satisfies the scoped environment invariant. *)
  Lemma inv_bot : forall p, inv p E.bot.
  Proof.
    intro p. rewrite E.F_bot. constructor.
  Qed.

  (** Joining scoped environments preserves the invariant. *)
  Lemma inv_join : forall p a b, inv p a -> inv p b -> inv p (E.join a b).
  Proof.
    intros p a b Ha Hb. rewrite E.F_join.
    destruct a as [|ma], b as [|mb]; try assumption.
    rewrite E.F_join_map. apply inv_merge; [exact Ha|exact Hb|reflexivity].
  Qed.

  (** Narrowing scoped environments preserves the invariant. *)
  Lemma inv_narrow : forall p a b, inv p a -> inv p b -> inv p (E.narrow a b).
  Proof.
    intros p a b Ha Hb. rewrite E.F_narrow. destruct (E.is_bot b); [exact Hb|].
    destruct a as [|ma], b as [|mb]; try assumption.
    apply inv_merge; [exact Ha|exact Hb|reflexivity].
  Qed.

  (** Widening scoped environments preserves the invariant. *)
  Lemma inv_widen : forall p w a b, inv p a -> inv p b -> inv p (E.widen w a b).
  Proof.
    intros p w a b Ha Hb. rewrite E.F_widen. destruct (E.leb b a); [exact Ha|].
    destruct a as [|ma], b as [|mb]; try assumption.
    apply inv_merge; [exact Ha|exact Hb|reflexivity].
  Qed.

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
