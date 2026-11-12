(** * Numeric linearization

    Linearization recognizes affine expressions and wrapped comparisons.
    For example, integer addition can yield an unwrapped linear form.
    Builds on: KeySig, LangSig, ValueSig and LinForm. *)

From Stdlib Require Import List ZArith.
From Galois.Base Require Import KeySig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.Relational Require Import LinForm.

Module Type LINEARIZE_OPS (X : KEY_OPS) (L : LANG_OPS).
  Parameter lin_of : term L.op X.t -> option (lin X.t * wrapr).
  Parameter atoms_of : L.guard -> list (term L.op X.t) -> list (atom X.t).
End LINEARIZE_OPS.

Module Type LINEARIZE_LAWS (X : KEY) (L : LANG) (N : NUM_VIEW L)
    (Import F : LINEARIZE_OPS X L).
  (** Recognized forms reproduce successful concrete evaluation in the numeric view. *)
  Parameter lin_sound : forall st e c f r,
    eval_term L.eval st e = Some c -> lin_of e = Some (f, r) ->
    N.num c = wrap_into r (eval_lin (fun x => N.num (st x)) f).
  (** Every emitted atom follows from the concrete guard. *)
  Parameter atoms_sound : forall g es st cs,
    eval_terms L.eval st es = Some cs -> L.holds g cs ->
    Forall (atom_holds (fun x => N.num (st x))) (atoms_of g es).
End LINEARIZE_LAWS.

Module Type LINEARIZE (X : KEY) (L : LANG) (N : NUM_VIEW L) :=
  LINEARIZE_OPS X L <+ LINEARIZE_LAWS X L N.

Module Type LINEARIZE_TIME (X : KEY_T) (L : LANG_T) (N : NUM_VIEW L)
    (Import F : LINEARIZE X L N).
  (* spec: bits_e bits_es *)
  Parameter bits_e : term L.op X.t -> nat.
  Parameter bits_es : L.guard -> list (term L.op X.t) -> nat.
  Parameter T_lin_of : term L.op X.t -> N.
  Parameter T_atoms_of : L.guard -> list (term L.op X.t) -> N.
  Parameter c_linearize : N.
  (** Linearization charges the term size and maximum coefficient or key size. *)
  Parameter T_lin_of_le : forall e,
    (T_lin_of e <= c_linearize * N.of_nat ((tsize e)%nat) * N.of_nat ((bits_e e + 1)%nat))%N.
  (** Guard linearization charges all operand terms. *)
  Parameter T_atoms_of_le : forall g es,
    (T_atoms_of g es <= c_linearize * N.of_nat ((fold_right Nat.add 0 (map tsize es) + 1)%nat) *
      N.of_nat ((bits_es g es + 1)%nat))%N.
End LINEARIZE_TIME.

Module Type LINEARIZE_T (X : KEY_T) (L : LANG_T) (N : NUM_VIEW L) :=
  LINEARIZE X L N <+ LINEARIZE_TIME X L N.

Module Type LINEARIZE_PLAN (X : KEY_T) (L : LANG_T) (N : NUM_VIEW L)
    (Import F : LINEARIZE_T X L N).
  (** In-range wrapped integers retain their value. *)
  Parameter wrap_into_id : forall lo hi z, (lo <= z <= hi)%Z ->
    wrap_into (WrapTo lo hi) z = z.
End LINEARIZE_PLAN.

Module Type LINEARIZE_ALL (X : KEY_T) (L : LANG_T) (N : NUM_VIEW L) :=
  LINEARIZE_T X L N <+ LINEARIZE_PLAN X L N.
