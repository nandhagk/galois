(** * Numeric linearization

    The language-independent linearizer recognizes variable leaves.
    For example, a leaf becomes one unit coefficient and an unwrapped zero constant.
    Builds on: LinearizeSig. *)

From Stdlib Require Import List ZArith Lia.
From Argent Require Import Time Tactics Std.
From Galois.Base Require Import KeySig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.Relational Require Import LinForm LinearizeSig.

Module LinearizeCode (X : KEY_OPS) (L : LANG_OPS) <: LINEARIZE_OPS X L.
  Definition lin_of (e : term L.op X.t) : option (lin X.t * wrapr) :=
    match e with
    | Leaf x => Some (Lin X.t ((x, 1%Z) :: nil) 0%Z, NoWrap)
    | Node _ _ => None
    end.
  (* STUB-CODE *)
  Definition atoms_of (_ : L.guard) (_ : list (term L.op X.t)) : list (atom X.t) := nil.
End LinearizeCode.

Module Linearize (X : KEY) (L : LANG) (N : NUM_VIEW L) <: LINEARIZE X L N.
  Include LinearizeCode X L.
  Lemma lin_sound : forall st e c f r,
    eval_term L.eval st e = Some c -> lin_of e = Some (f, r) ->
    N.num c = wrap_into r (eval_lin (fun x => N.num (st x)) f).
  Proof.
    intros st [x | o es] c f r Heval Hlin; cbn [lin_of] in Hlin.
    - inversion Hlin; subst f r. cbn [eval_term] in Heval.
      inversion Heval; subst c.
      change (N.num (st x) = (1 * N.num (st x) + 0 + 0)%Z). ring.
    - discriminate.
  Qed.
  Lemma atoms_sound : forall g es st cs,
    eval_terms L.eval st es = Some cs -> L.holds g cs ->
    Forall (atom_holds (fun x => N.num (st x))) (atoms_of g es).
  Proof. Admitted. (* STUB *)
End Linearize.

Module LinearizeT (X : KEY_T) (L : LANG_T) (N : NUM_VIEW L) <: LINEARIZE_ALL X L N.
  Include Linearize X L N.
  Definition bits_e (e : term L.op X.t) : nat :=
    match e with
    | Leaf x => X.bits x + 1
    | Node _ _ => 0
    end.
  (* STUB-CODE *)
  Definition bits_es (_ : L.guard) (_ : list (term L.op X.t)) : nat := 0.
  TimeFun lin_of.
  TimeFun atoms_of.
  Definition form_bits (f : lin X.t) : nat :=
    fold_right Nat.max (Z.size_nat (cst f))
      (map (fun p => X.bits (fst p) + Z.size_nat (snd p)) (coef f)).
  Definition wrap_bits (r : wrapr) : nat :=
    match r with NoWrap => 0 | WrapTo lo hi => Z.size_nat lo + Z.size_nat hi end.
  (** Recognized forms fit the charged term size and bit size. *)
  Lemma lin_of_size : forall e f r, lin_of e = Some (f, r) ->
    length (coef f) <= tsize e /\ form_bits f + wrap_bits r <= bits_e e.
  Proof.
    intros [x | o es] f r Hlin; cbn [lin_of] in Hlin.
    - inversion Hlin; subst f r.
      change (1 <= 1 /\ Nat.max (X.bits x + 1) 0 + 0 <= X.bits x + 1)%nat.
      rewrite Nat.max_0_r. split; lia.
    - discriminate.
  Qed.
  (** Emitted atoms fit the charged operand sizes and bit size. *)
  Lemma atoms_of_size : forall g es,
    length (atoms_of g es) <= 2 * fold_right Nat.add 1 (map tsize es) /\
    Forall (fun a =>
      length (coef (al a)) + length (coef (ar a)) <= fold_right Nat.add 0 (map tsize es) /\
      form_bits (al a) + wrap_bits (alw a) + form_bits (ar a) + wrap_bits (arw a) <=
        bits_es g es) (atoms_of g es).
  Proof. Admitted. (* STUB *)
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
  Proof.
    intros lo hi z Hbounds. unfold wrap_into.
    rewrite Z.mod_small by lia. lia.
  Qed.
End LinearizeT.
