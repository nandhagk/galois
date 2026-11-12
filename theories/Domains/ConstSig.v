(** * Flat constant domain interfaces

    A constant domain records bottom, one concrete value or top.
    For example, joining distinct singleton values gives top.
    Builds on: ValueSig and HarnessSig. *)

From Stdlib Require Import List.
From Argent Require Import BigO.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig HarnessSig.

Inductive flat (A : Type) : Type :=
  | FBot
  | FVal (a : A)
  | FTop.

Arguments FBot {A}.
Arguments FVal {A} a.
Arguments FTop {A}.

Module Type VAL_EQ_OPS (L : LANG_OPS).
  Parameter eqb : L.val -> L.val -> bool.
End VAL_EQ_OPS.

Module Type VAL_EQ_LAWS (L : LANG) (Import E : VAL_EQ_OPS L).
  (** Equality testing reflects concrete equality. *)
  Parameter eqb_spec : forall a b, eqb a b = true <-> a = b.
End VAL_EQ_LAWS.

Module Type VAL_EQ (L : LANG) := VAL_EQ_OPS L <+ VAL_EQ_LAWS L.

Module Type VAL_EQ_TIME (L : LANG_T) (Import E : VAL_EQ L).
  (* spec: vsize *)
  Parameter vsize : L.val -> nat.
  Parameter T_eqb : L.val -> L.val -> nat.
  Parameter c_eq : nat.
  (** Equality charges both concrete values. *)
  Parameter T_eqb_le : forall a b, T_eqb a b <= c_eq * (vsize a + vsize b + 1).
End VAL_EQ_TIME.

Module Type VAL_EQ_T (L : LANG_T) := VAL_EQ L <+ VAL_EQ_TIME L.

Module Type CONST_OPS (L : LANG_OPS) (E : VAL_EQ_OPS L).
  Include VALUE_DOMAIN_OPS L with Definition t := flat L.val with Definition wparam := unit.
  Parameter point : t -> option L.val.
  Parameter abst : L.val -> t.
End CONST_OPS.

Module Type CONST_SPEC (L : LANG_OPS) (E : VAL_EQ_OPS L) (Import D : CONST_OPS L E).
  Definition flat_gamma (a : t) (c : L.val) : Prop :=
    match a with FBot => False | FVal v => c = v | FTop => True end.
  Definition level (a : t) : nat := match a with FBot => 0 | FVal _ => 1 | FTop => 2 end.
End CONST_SPEC.

Module Type CONST (L : LANG) (E : VAL_EQ L) :=
  CONST_OPS L E <+ CONST_SPEC L E <+
  LATTICE_LAWS <+ HAS_TOP_LAWS <+ HAS_MEET_LAWS <+ WIDENING_LAWS <+
  VALUE_DOMAIN_LAWS L.

Module Type CONST_TIME (L : LANG_T) (E : VAL_EQ_T L) (Import D : CONST L E).
  Include VALUE_DOMAIN_TIME L D.
  Parameter T_point : t -> nat.
  Parameter T_abst : L.val -> nat.
  Parameter c_const : nat.
  (** Flat point recognition takes constant time. *)
  Parameter T_point_le : forall a, T_point a <= c_const.
  (** Flat singleton construction takes constant time. *)
  Parameter T_abst_le : forall c, T_abst c <= c_const.
  (** Generic constant transfer has the published operator-work bound. *)
  Parameter forward_bigO : bigO (fun _ => True)
    (fun ox => work (fst ox) (snd ox)) (fun ox => T_forward (fst ox) (snd ox)).
End CONST_TIME.

Module Type CONST_T (L : LANG_T) (E : VAL_EQ_T L) := CONST L E <+ CONST_TIME L E.

Module Type CONST_PLAN (L : LANG_T) (E : VAL_EQ_T L) (Import D : CONST_T L E).
  Parameter points : list t -> option (list L.val).
  Parameter T_points : list t -> nat.
  Parameter k_const_points k_const_forward : nat.
  (** The concretization agrees with the flat representation. *)
  Parameter F1_gamma : forall a c, gamma a c <-> flat_gamma a c.
  (** Widening uses the finite-height join. *)
  Parameter F2_widen : forall p a b, widen p a b = join a b.
  (** Widening rank is the complement of the flat level. *)
  Parameter F3_wrank : forall p a, wrank p a = 2 - level a.
  (** Flat ranks have height two. *)
  Parameter F4_rank_le : forall a, level a <= 2.
  (** Singleton collection identifies every represented operand list. *)
  Parameter F5_points_sound : forall xs cs vs,
    Forall2 gamma xs cs -> points xs = Some vs -> vs = cs.
  (** Point collection charges a list traversal. *)
  Parameter T1_points : forall xs, T_points xs <= k_const_points * (length xs + 1).
  (** Concrete evaluation and singleton construction bound the point branch. *)
  Parameter T2_forward_points : forall o xs cs, points xs = Some cs ->
    T_forward o xs <= k_const_forward *
      (length xs + L.T_eval o cs +
       match L.eval o cs with Some c => T_abst c | None => 0 end + 1).
End CONST_PLAN.

Module Type CONST_ALL (L : LANG_T) (E : VAL_EQ_T L) := CONST_T L E <+ CONST_PLAN L E.
