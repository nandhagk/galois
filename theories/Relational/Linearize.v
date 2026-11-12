(** * Numeric linearization placeholders

    These modules provide the interface for numeric linearization.
    For example, an unrecognized expression returns no linear form.
    Builds on: LinearizeSig. *)

From Stdlib Require Import List ZArith.
From Argent Require Import Time Std.
From Galois.Base Require Import KeySig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.Relational Require Import LinForm LinearizeSig.

Module LinearizeCode (X : KEY_OPS) (L : LANG_OPS) <: LINEARIZE_OPS X L.
  (* STUB-CODE *)
  Definition lin_of (_ : term L.op X.t) : option (lin X.t * wrapr) := None.
  (* STUB-CODE *)
  Definition atoms_of (_ : L.guard) (_ : list (term L.op X.t)) : list (atom X.t) := nil.
End LinearizeCode.

Module Linearize (X : KEY) (L : LANG) (N : NUM_VIEW L) <: LINEARIZE X L N.
  Include LinearizeCode X L.
  Lemma lin_sound : forall st e c f r,
    eval_term L.eval st e = Some c -> lin_of e = Some (f, r) ->
    N.num c = wrap_into r (eval_lin (fun x => N.num (st x)) f).
  Proof. Admitted.
  Lemma atoms_sound : forall g es st cs,
    eval_terms L.eval st es = Some cs -> L.holds g cs ->
    Forall (atom_holds (fun x => N.num (st x))) (atoms_of g es).
  Proof. Admitted.
End Linearize.

Module LinearizeT (X : KEY_T) (L : LANG_T) (N : NUM_VIEW L) <: LINEARIZE_ALL X L N.
  Include Linearize X L N.
  Definition bits_e (_ : term L.op X.t) : nat := 0.
  Definition bits_es (_ : L.guard) (_ : list (term L.op X.t)) : nat := 0.
  TimeFun lin_of.
  TimeFun atoms_of.
  Definition c_linearize : N := 1. (* STUB *)
  Lemma T_lin_of_le : forall e,
    (T_lin_of e <= c_linearize * N.of_nat ((tsize e)%nat) * N.of_nat ((bits_e e + 1)%nat))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_atoms_of_le : forall g es,
    (T_atoms_of g es <= c_linearize * N.of_nat ((fold_right Nat.add 0 (map tsize es) + 1)%nat) *
      N.of_nat ((bits_es g es + 1)%nat))%N.
  Proof. Admitted. (* STUB *)
  Lemma wrap_into_id : forall lo hi z, (lo <= z <= hi)%Z ->
    wrap_into (WrapTo lo hi) z = z.
  Proof. Admitted. (* STUB *)
End LinearizeT.
