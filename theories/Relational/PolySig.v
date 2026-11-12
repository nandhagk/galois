(** * Certified polyhedral states

    Polyhedra check Fourier-Motzkin producer results before using them as constraints.
    For example, widening keeps old constraints certified by the new state.
    Builds on: EnvSig, NumStateSig and LinCertSig. *)

From Stdlib Require Import List ZArith QArith.
From Argent Require Import Std.
From Galois.Base Require Import KeySig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.States Require Import EnvSig.
From Galois.Relational Require Import LinForm LinearizeSig NumStateSig LinCertSig.

Local Open Scope nat_scope.

Record tracked (X : Type) := Tracked {
  row_of : lcons X;
  mults_of : list Z
}.

Arguments row_of {X} _.
Arguments mults_of {X} _.

(** Fourier-Motzkin work keeps the original dimension in every elimination charge. *)
Fixpoint fmcost (dim fuel rows bits : nat) : nat :=
  match fuel with
  | 0 => 1
  | S k => rows^2 * (dim + rows) * (bits + 1)^2 +
      fmcost dim k (rows^2 / 4 + rows) (2 * bits + 1)
  end.

Module Type POLY_OPS (X : KEY_OPS) (L : LANG_OPS) (F : LINEARIZE_OPS X L)
    (C : LINCERT_OPS X).
  Include NUM_STATE_OPS X L F
    with Definition t := reach (list (lcons X.t))
    with Definition wparam := list (lcons X.t).
  Parameter subst : X.t -> lin X.t -> lcons X.t -> lcons X.t.
  Parameter fm_elim : X.t -> list (lcons X.t) -> list (tracked X.t).
  Parameter entail_cert : list (lcons X.t) -> lcons X.t -> option cert.
End POLY_OPS.

Module Type POLY_BASE (X : KEY) (L : LANG) (N : NUM_VIEW L)
    (F : LINEARIZE X L N) (C : LINCERT X) :=
  POLY_OPS X L F C <+ LATTICE_LAWS <+ HAS_TOP_LAWS <+ WIDENING_LAWS <+
  NUM_STATE_LAWS X L N F.

Module Type POLY_LAWS (X : KEY) (L : LANG) (N : NUM_VIEW L)
    (F : LINEARIZE X L N) (C : LINCERT X) (Import D : POLY_BASE X L N F C).
  (** Reached polyhedra denote simultaneous integer solutions of their constraints. *)
  Parameter ngamma_reached : forall P v, ngamma (Reached P) v <-> Forall (sat v) P.
  (** Unreachable polyhedra have no integer solution. *)
  Parameter ngamma_unreached : forall v, ~ ngamma Unreached v.
End POLY_LAWS.

Module Type POLY (X : KEY) (L : LANG) (N : NUM_VIEW L)
    (F : LINEARIZE X L N) (C : LINCERT X) :=
  POLY_BASE X L N F C <+ POLY_LAWS X L N F C.

Module Type POLY_TIME (X : KEY_T) (L : LANG_T) (N : NUM_VIEW L)
    (F : LINEARIZE_T X L N) (C : LINCERT_T X) (Import D : POLY X L N F C).
  Include NUM_STATE_TIME X L N F D.
  (* spec: n ell *)
  Parameter n ell : list (lcons X.t) -> nat.
  Parameter T_subst : X.t -> lin X.t -> lcons X.t -> nat.
  Parameter T_fm_elim : X.t -> list (lcons X.t) -> nat.
  Parameter T_entail_cert : list (lcons X.t) -> lcons X.t -> nat.
  Parameter c_poly : nat.
  (** One elimination charges all row pairs and their tracked multipliers. *)
  Parameter T_fm_elim_le : forall x P, T_fm_elim x P <= c_poly * (length P)^2 *
    (n P + length P) * (ell P + 1)^2.
  (** Certificate production follows the full Fourier-Motzkin recurrence. *)
  Parameter T_entail_cert_le : forall P c, T_entail_cert P c <= c_poly *
    fmcost (n P) (n P) (length P + 1) (ell P + C.row_bits c).
End POLY_TIME.

Module Type POLY_T (X : KEY_T) (L : LANG_T) (N : NUM_VIEW L)
    (F : LINEARIZE_T X L N) (C : LINCERT_T X) :=
  POLY X L N F C <+ POLY_TIME X L N F C.

Module Type POLY_PLAN (X : KEY_T) (L : LANG_T) (N : NUM_VIEW L)
    (F : LINEARIZE_T X L N) (C : LINCERT_T X) (Import D : POLY_T X L N F C).
  (** Every produced row equals its tracked linear combination. *)
  Parameter fm_step_mults : forall P x r, In r (fm_elim x P) ->
    C.combine P (mults_of r) = Some (row_of r).
  (** Successful certificates pass the independent checker. *)
  Parameter entail_cert_checks : forall P c k,
    entail_cert P c = Some k -> C.check_entails P c k = true.
  (** Failure to find an entailment certificate yields a rational countermodel. *)
  Parameter fm_complete_Q : forall P c, entail_cert P c = None ->
    exists v : X.t -> Q, Forall (satQ v) P /\ ~ satQ v c.
  (** Elimination keeps at most all opposite-sign pairs and the zero rows. *)
  Parameter fm_rows_le : forall x P, length (fm_elim x P) <= (length P)^2 / 4 + length P.
  (** One elimination at most doubles entry bit lengths plus a carry. *)
  Parameter ell_fm_le : forall x P,
    ell (map row_of (fm_elim x P)) <= 2 * ell P + 1.
  (** Substitution agrees with updating the interpreted variable. *)
  Parameter subst_sat : forall v x f r, sat v (subst x f r) <->
    sat (upd X.eqb v x (eval_lin v f)) r.
  (** Widening rank counts the constraints that can still be dropped. *)
  Parameter wrank_rows : forall p P, wrank p (Reached P) = length P.
  (** Every widened constraint was already an old constraint. *)
  Parameter widen_rows : forall p a b P,
    widen p (Reached a) (Reached b) = Reached P -> incl P a.
End POLY_PLAN.

Module Type POLY_ALL (X : KEY_T) (L : LANG_T) (N : NUM_VIEW L)
    (F : LINEARIZE_T X L N) (C : LINCERT_T X) :=
  POLY_T X L N F C <+ POLY_PLAN X L N F C.
