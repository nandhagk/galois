(** * Linear equality states

    Karr states represent affine equalities and check producer results with certificates.
    For example, havoc removes the equalities that constrain its selected variable.
    Builds on: EnvSig, NumStateSig and LinCertSig. *)

From Stdlib Require Import List ZArith QArith.
From Argent Require Import Std.
From Galois.Base Require Import KeySig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.States Require Import EnvSig.
From Galois.Relational Require Import LinForm LinearizeSig NumStateSig LinCertSig.

Local Open Scope nat_scope.

Module Type KARR_OPS (X : KEY_OPS) (L : LANG_OPS) (F : LINEARIZE_OPS X L)
    (C : LINCERT_OPS X).
  Include NUM_STATE_OPS X L F
    with Definition t := reach (list (lcons X.t)) with Definition wparam := nat.
  Parameter subst : X.t -> lin X.t -> lcons X.t -> lcons X.t.
  Parameter affine_hull : list (lcons X.t) -> list (lcons X.t) -> list (lcons X.t).
  Parameter entail_cert : list (lcons X.t) -> lcons X.t -> option cert.
End KARR_OPS.

Module Type KARR_BASE (X : KEY) (L : LANG) (N : NUM_VIEW L)
    (F : LINEARIZE X L N) (C : LINCERT X) :=
  KARR_OPS X L F C <+ LATTICE_LAWS <+ HAS_TOP_LAWS <+ WIDENING_LAWS <+
  NUM_STATE_LAWS X L N F.

Module Type KARR_LAWS (X : KEY) (L : LANG) (N : NUM_VIEW L)
    (F : LINEARIZE X L N) (C : LINCERT X) (Import D : KARR_BASE X L N F C).
  (** Reached equality systems denote their simultaneous integer solutions. *)
  Parameter ngamma_reached : forall P v, ngamma (Reached P) v <-> Forall (sat v) P.
  (** Unreachable equality systems have no solution. *)
  Parameter ngamma_unreached : forall v, ~ ngamma Unreached v.
End KARR_LAWS.

Module Type KARR (X : KEY) (L : LANG) (N : NUM_VIEW L)
    (F : LINEARIZE X L N) (C : LINCERT X) :=
  KARR_BASE X L N F C <+ KARR_LAWS X L N F C.

Module Type KARR_TIME (X : KEY_T) (L : LANG_T) (N : NUM_VIEW L)
    (F : LINEARIZE_T X L N) (C : LINCERT_T X) (Import D : KARR X L N F C).
  Include NUM_STATE_TIME X L N F D.
  (* spec: n ell *)
  Parameter n ell : t -> nat.
  Parameter T_subst : X.t -> lin X.t -> lcons X.t -> nat.
  Parameter T_affine_hull : list (lcons X.t) -> list (lcons X.t) -> nat.
  Parameter T_entail_cert : list (lcons X.t) -> lcons X.t -> nat.
  Parameter c_karr : nat.
  Definition ellB (dim bits : nat) : nat := dim * (bits + Nat.log2 dim + 1).
  (** Join charges cubic fraction-free elimination at the Hadamard bit bound. *)
  Parameter T_join_karr_le : forall a b, T_join a b <= c_karr * (n a + n b)^3 *
    (ellB (n a + n b) (ell a + ell b) + 1)^2.
End KARR_TIME.

Module Type KARR_T (X : KEY_T) (L : LANG_T) (N : NUM_VIEW L)
    (F : LINEARIZE_T X L N) (C : LINCERT_T X) :=
  KARR X L N F C <+ KARR_TIME X L N F C.

Module Type KARR_PLAN (X : KEY_T) (L : LANG_T) (N : NUM_VIEW L)
    (F : LINEARIZE_T X L N) (C : LINCERT_T X) (Import D : KARR_T X L N F C).
  Definition echelon (P : list (lcons X.t)) : Prop :=
    Forall (fun r => lrel r = REq) P /\
    (forall i r, nth_error P i = Some r -> exists x a, In (x, a) (lhs r) /\ a <> 0%Z /\
      forall j s, nth_error P j = Some s -> i <> j ->
        forall b, In (x, b) (lhs s) -> b = 0%Z).
  (* spec: affine_dim bareiss_entries input_minors *)
  Parameter affine_dim : nat -> t -> nat.
  Parameter bareiss_entries input_minors : list (lcons X.t) -> list Z.
  (** Substitution agrees with a concrete update. *)
  Parameter subst_sat : forall v x f r, sat v (subst x f r) <->
    sat (upd X.eqb v x (eval_lin v f)) r.
  (** Echelon systems decide rational inclusion completely. *)
  Parameter leb_complete_Q : forall a b, echelon a ->
    (forall v : X.t -> Q, Forall (satQ v) a -> Forall (satQ v) b) ->
    leb (Reached a) (Reached b) = true.
  (** Every fraction-free intermediate entry is an input minor. *)
  Parameter bareiss_minor : forall P z, In z (bareiss_entries P) -> In z (input_minors P).
  (** Widening uses affine hull join. *)
  Parameter widen_join : forall p a b, widen p a b = join a b.
  (** Rank measures the dimension left to gain within the program's variable budget. *)
  Parameter wrank_dim : forall p a, wrank p a = p + 1 - affine_dim p a.
  (** Every successful entailment certificate is accepted. *)
  Parameter entail_cert_checks : forall P c k,
    entail_cert P c = Some k -> C.check_entails P c k = true.
End KARR_PLAN.

Module Type KARR_ALL (X : KEY_T) (L : LANG_T) (N : NUM_VIEW L)
    (F : LINEARIZE_T X L N) (C : LINCERT_T X) :=
  KARR_T X L N F C <+ KARR_PLAN X L N F C.
