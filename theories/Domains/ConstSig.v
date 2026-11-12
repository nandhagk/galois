(** * Flat constant domain interfaces

    A constant domain records bottom, one concrete value or top.
    For example, joining distinct singleton values gives top.
    Builds on: ValueSig and HarnessSig. *)

From Stdlib Require Import List ZArith.
From Argent Require Import BigO.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig HarnessSig WordSig.

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
  Parameter T_eqb : L.val -> L.val -> N.
  Parameter c_eq : N.
  (** Equality charges both concrete values. *)
  Parameter T_eqb_le : forall a b, (T_eqb a b <= c_eq * N.of_nat ((vsize a + vsize b + 1)%nat))%N.
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
  Parameter T_point : t -> N.
  Parameter T_abst : L.val -> N.
  Parameter c_const : N.
  (** Flat point recognition takes constant time. *)
  Parameter T_point_le : forall a, (T_point a <= c_const)%N.
  (** Flat singleton construction takes constant time. *)
  Parameter T_abst_le : forall c, (T_abst c <= c_const)%N.
  (** Generic constant transfer has the published operator-work bound. *)
  Parameter forward_bigO : (bigO (fun _ => True)
    (fun ox => N.of_nat ((work (fst ox) (snd ox))%nat)) (fun ox => T_forward (fst ox) (snd ox)))%N.
End CONST_TIME.

Module Type CONST_T (L : LANG_T) (E : VAL_EQ_T L) := CONST L E <+ CONST_TIME L E.

Module Type CONST_PLAN (L : LANG_T) (E : VAL_EQ_T L) (Import D : CONST_T L E).
  Parameter points : list t -> option (list L.val).
  Parameter T_points : list t -> N.
  Parameter k_const_points k_const_forward : N.
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
  (** Singleton recognition reads the flat constructor. *)
  Parameter F6_point : forall a, point a =
    match a with FVal c => Some c | _ => None end.
  (** Singleton abstraction records its concrete argument. *)
  Parameter F7_abst : forall c, abst c = FVal c.
  (** Point collection charges a list traversal. *)
  Parameter T1_points : forall xs,
    (T_points xs <= k_const_points * N.of_nat (length xs + 1))%N.
  (** Concrete evaluation and singleton construction bound the point branch. *)
  Parameter T2_forward_points : forall o xs cs, points xs = Some cs ->
    (T_forward o xs <= k_const_forward *
      (N.of_nat ((length xs)%nat) + L.T_eval o cs +
       match L.eval o cs with Some c => T_abst c | None => 0 end + 1))%N.
End CONST_PLAN.

Module Type CONST_ALL (L : LANG_T) (E : VAL_EQ_T L) := CONST_T L E <+ CONST_PLAN L E.

Module Type CONST_WORD_PAYLOAD (L : WORD_LANGUAGE) :=
  WORD_PAYLOAD L with Definition p := flat Z.
Module Type CONST_WORD_PAYLOAD_T (L : WORD_LANGUAGE_T) :=
  WORD_PAYLOAD_T L with Definition p := flat Z.
Module Type CONST_WORD_TABLE (L : WORD_LANGUAGE) (W : CONST_WORD_PAYLOAD L) :=
  WORD_TABLE L W.
Module Type CONST_WORD_TABLE_T (L : WORD_LANGUAGE_T) (W : CONST_WORD_PAYLOAD_T L) :=
  WORD_TABLE_T L W.

Module Type CONST_WORD_TABLE_PLAN (L : WORD_LANGUAGE_T) (W : CONST_WORD_PAYLOAD_T L)
    (Import T : CONST_WORD_TABLE_T L W).
  Parameter shortcut : L.op -> (positive * W.p) -> (positive * W.p) -> option Z.
  Parameter backward_one backward_two :
    L.op -> positive -> W.p -> list (positive * W.p) -> option (list W.p).
  Parameter T_shortcut : L.op -> (positive * W.p) -> (positive * W.p) -> N.
  Parameter T_backward_one T_backward_two :
    L.op -> positive -> W.p -> list (positive * W.p) -> N.
  Parameter k_const_word : N.
  (** An annihilator shortcut identifies every defined concrete result. *)
  Parameter F1_shortcut_sound : forall o a b z cs rw v,
    shortcut o a b = Some z ->
    Forall2 (fun wp c => fst wp = fst c /\ W.pgamma (fst wp) (snd wp) (snd c))
      (a :: b :: nil) cs -> L.eval_op o cs = Some (rw, v) -> v = z.
  (** Unary inverses retain every operand consistent with the result. *)
  Parameter F2_backward_one_sound : forall o rw q xs ys cs z,
    backward_one o rw q xs = Some ys ->
    Forall2 (fun wp c => fst wp = fst c /\ W.pgamma (fst wp) (snd wp) (snd c)) xs cs ->
    L.eval_op o cs = Some (rw, z) -> W.pgamma rw q z ->
    Forall2 (fun wp c => W.pgamma (fst wp) (snd wp) (snd c))
      (combine (map fst xs) ys) cs.
  (** Binary inverses retain every operand consistent with the result. *)
  Parameter F3_backward_two_sound : forall o rw q xs ys cs z,
    backward_two o rw q xs = Some ys ->
    Forall2 (fun wp c => fst wp = fst c /\ W.pgamma (fst wp) (snd wp) (snd c)) xs cs ->
    L.eval_op o cs = Some (rw, z) -> W.pgamma rw q z ->
    Forall2 (fun wp c => W.pgamma (fst wp) (snd wp) (snd c))
      (combine (map fst xs) ys) cs.
  (** Shortcuts charge both operand widths. *)
  Parameter T1_shortcut : forall o a b, (T_shortcut o a b <=
    k_const_word * N.of_nat (((Pos.to_nat (fst a) + Pos.to_nat (fst b) + 1) ^ 2)%nat))%N.
  (** Unary inverses have the published quadratic width bound. *)
  Parameter T2_backward_one : forall o rw q xs, (T_backward_one o rw q xs <=
    k_const_word * N.of_nat
      (((Pos.to_nat rw +
        fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2)%nat))%N.
  (** Binary inverses have the published quadratic width bound. *)
  Parameter T3_backward_two : forall o rw q xs, (T_backward_two o rw q xs <=
    k_const_word * N.of_nat
      (((Pos.to_nat rw +
        fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2)%nat))%N.
End CONST_WORD_TABLE_PLAN.

Module Type CONST_WORD_TABLE_ALL (L : WORD_LANGUAGE_T) (W : CONST_WORD_PAYLOAD_T L) :=
  CONST_WORD_TABLE_T L W <+ CONST_WORD_TABLE_PLAN L W.
