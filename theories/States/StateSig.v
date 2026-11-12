(** * State domains

    State domains describe concrete environments and refine them through assignments and guards.
    For example, havoc permits every value for the selected variable.
    Builds on: KeySig, LatticeSig, LangSig and ValueSig. *)

From Stdlib Require Import List NArith.
From Galois.Base Require Import KeySig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig.

Module Type STATE_DOMAIN_OPS (X : KEY_OPS) (L : LANG_OPS) (V : VALUE_DOMAIN_OPS L).
  Include ALATTICE_OPS.
  Parameter assign : X.t -> term L.op X.t -> t -> t.
  Parameter havoc : X.t -> t -> t.
  Parameter assume : L.guard -> list (term L.op X.t) -> t -> t.
  Parameter eval : term L.op X.t -> t -> V.t.
End STATE_DOMAIN_OPS.

Module Type STATE_DOMAIN_LAWS (X : KEY) (L : LANG) (V : VALUE_DOMAIN L)
    (Import D : STATE_DOMAIN_OPS X L V).
  (* spec: gamma *)
  Parameter gamma : t -> (X.t -> L.val) -> Prop.
  (** Abstract inclusion entails inclusion of concrete environments. *)
  Parameter gamma_mono : forall a b st, leb a b = true -> gamma a st -> gamma b st.
  (** Bottom describes no concrete environment. *)
  Parameter gamma_bot : forall st, ~ gamma bot st.
  (** Top describes every concrete environment. *)
  Parameter gamma_top : forall st, gamma top st.
  (** Assignment contains each successful concrete update. *)
  Parameter assign_sound : forall x e s st c,
    gamma s st -> eval_term L.eval st e = Some c ->
    gamma (assign x e s) (upd X.eqb st x c).
  (** Havoc contains every concrete update of the selected variable. *)
  Parameter havoc_sound : forall x s st c,
    gamma s st -> gamma (havoc x s) (upd X.eqb st x c).
  (** Assuming a true guard retains its concrete environment. *)
  Parameter assume_sound : forall g es s st cs,
    gamma s st -> eval_terms L.eval st es = Some cs -> L.holds g cs ->
    gamma (assume g es s) st.
  (** Abstract evaluation describes every successful concrete result. *)
  Parameter eval_sound : forall e s st c,
    gamma s st -> eval_term L.eval st e = Some c -> V.gamma (eval e s) c.
End STATE_DOMAIN_LAWS.

Module Type STATE_DOMAIN (X : KEY) (L : LANG) (V : VALUE_DOMAIN L) :=
  STATE_DOMAIN_OPS X L V <+ LATTICE_LAWS <+ HAS_TOP_LAWS <+ WIDENING_LAWS <+
  STATE_DOMAIN_LAWS X L V.

Module Type STATE_TRANSFER_TIME (X : KEY_T) (L : LANG_T) (V : VALUE_DOMAIN_T L)
    (Import D : STATE_DOMAIN X L V).
  (* spec: assign_work havoc_work assume_work eval_work *)
  Parameter assign_work : X.t -> term L.op X.t -> t -> nat.
  Parameter havoc_work : X.t -> t -> nat.
  Parameter assume_work : L.guard -> list (term L.op X.t) -> t -> nat.
  Parameter eval_work : term L.op X.t -> t -> nat.
  Parameter T_assign : X.t -> term L.op X.t -> t -> N.
  Parameter T_havoc : X.t -> t -> N.
  Parameter T_assume : L.guard -> list (term L.op X.t) -> t -> N.
  Parameter T_eval : term L.op X.t -> t -> N.
  Parameter c_state : N.
  (** Assignment charges its domain-specific traversal and transfer work. *)
  Parameter T_assign_le : forall x e s,
    (T_assign x e s <= c_state * N.of_nat (assign_work x e s + 1))%N.
  (** Havoc charges its domain-specific update work. *)
  Parameter T_havoc_le : forall x s, (T_havoc x s <= c_state * N.of_nat (havoc_work x s + 1))%N.
  (** Assumption charges its domain-specific guard and refinement work. *)
  Parameter T_assume_le : forall g es s,
    (T_assume g es s <= c_state * N.of_nat (assume_work g es s + 1))%N.
  (** Evaluation charges its domain-specific traversal and transfer work. *)
  Parameter T_eval_le : forall e s, (T_eval e s <= c_state * N.of_nat (eval_work e s + 1))%N.
End STATE_TRANSFER_TIME.

Module Type STATE_LATTICE_TIME (X : KEY_T) (L : LANG_T) (V : VALUE_DOMAIN_T L)
    (Import D : STATE_DOMAIN X L V).
  Include LATTICE_TIME D.
  (* spec: wsize wunits *)
  Parameter wsize : wparam -> nat.
  Parameter wunits : t -> nat.
  Parameter T_widen : wparam -> t -> t -> N.
  Parameter T_narrow : t -> t -> N.
  (** Widening charges both states and its parameters. *)
  Parameter T_widen_le : forall p a b,
    (T_widen p a b <= c_lat * N.of_nat
      ((wunits a + wunits b) * wsize p + (size a + size b + wsize p + 1)))%N.
  (** Narrowing charges both states. *)
  Parameter T_narrow_le : forall a b,
    (T_narrow a b <= c_lat * N.of_nat (size a + size b + 1))%N.
End STATE_LATTICE_TIME.

Module Type STATE_DOMAIN_TIME (X : KEY_T) (L : LANG_T) (V : VALUE_DOMAIN_T L)
    (D : STATE_DOMAIN X L V) :=
  STATE_LATTICE_TIME X L V D <+ STATE_TRANSFER_TIME X L V D.

Module Type STATE_DOMAIN_T (X : KEY_T) (L : LANG_T) (V : VALUE_DOMAIN_T L) :=
  STATE_DOMAIN X L V <+ STATE_DOMAIN_TIME X L V.
