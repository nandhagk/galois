(** * Word payload interfaces

    Payloads describe integers at an explicit positive width.
    For example, tagging a singleton payload at width eight describes one eight-bit word.
    Builds on: LangSig and HarnessSig. *)

From Stdlib Require Import ZArith List.
From Argent Require Import Std BigO.
From Galois.Bits Require Import Word Op.
From Galois.Domains Require Import LangSig HarnessSig.

Inductive tagged (P : Type) : Type :=
  | TBot
  | TVal (w : positive) (p : P)
  | TAny.

Arguments TBot {P}.
Arguments TVal {P} w p.
Arguments TAny {P}.

(** The concrete word language uses the fixed-width bit operations. *)
Module Type WORD_LANGUAGE_OPS.
  Definition op := Op.op.
  Definition wrap := Word.wrap.
  Definition signed := Word.signed.
  Definition eval_op := Op.eval_op.
  Definition result_width := Op.result_width.
End WORD_LANGUAGE_OPS.

Module Type WORD_LANGUAGE_LAWS (Import L : WORD_LANGUAGE_OPS).
  Definition is_word := Word.is_word.
  (** Every wrapped integer is a normalized word. *)
  Parameter wrap_is_word : forall w z, is_word w (wrap w z).
  (** Concrete evaluation returns a normalized result of the checked width. *)
  Parameter eval_op_is_word : forall o cs w z, eval_op o cs = Some (w, z) ->
    is_word w z /\ result_width o (map fst cs) = Some w.
End WORD_LANGUAGE_LAWS.

Module Type WORD_LANGUAGE := WORD_LANGUAGE_OPS <+ WORD_LANGUAGE_LAWS.

Module Type WORD_LANGUAGE_TIME (Import L : WORD_LANGUAGE).
  Parameter T_wrap T_signed : positive -> Z -> N.
  Parameter T_eval_op : op -> list (positive * Z) -> N.
  Parameter T_result_width : op -> list positive -> N.
  Parameter c_word : N.
  (** Concrete word evaluation has the published operand-width bound. *)
  Parameter T_eval_op_le : forall o cs, (T_eval_op o cs <=
    c_word * N.of_nat (((fold_right Nat.add 0 (map (fun c => Pos.to_nat (fst c)) cs) + 1) ^
    2)%nat))%N.
End WORD_LANGUAGE_TIME.

Module Type WORD_LANGUAGE_T := WORD_LANGUAGE <+ WORD_LANGUAGE_TIME.

Module Type WORD_PAYLOAD_OPS (L : WORD_LANGUAGE_OPS).
  Parameter p : Type.
  Parameter pleb : positive -> p -> p -> bool.
  Parameter pjoin pmeet : positive -> p -> p -> p.
  Parameter pbot ptop : positive -> p.
  Parameter pis_bot : positive -> p -> bool.
  Parameter pconst : positive -> Z -> p.
  Parameter ppoint : positive -> p -> option Z.
End WORD_PAYLOAD_OPS.

Module Type WORD_PAYLOAD_LAWS (L : WORD_LANGUAGE) (Import W : WORD_PAYLOAD_OPS L).
  (* spec: pgamma *)
  Parameter pgamma : positive -> p -> Z -> Prop.
  (** Width-specific inclusion is reflexive. *)
  Parameter pleb_refl : forall w a, pleb w a a = true.
  (** Width-specific inclusion is transitive. *)
  Parameter pleb_trans : forall w a b c,
    pleb w a b = true -> pleb w b c = true -> pleb w a c = true.
  (** Bottom is below every payload. *)
  Parameter pbot_least : forall w a, pleb w (pbot w) a = true.
  (** Top is above every payload. *)
  Parameter ptop_greatest : forall w a, pleb w a (ptop w) = true.
  (** The bottom test recognizes bottom. *)
  Parameter pis_bot_bot : forall w, pis_bot w (pbot w) = true.
  (** Recognized bottoms are below every payload. *)
  Parameter pis_bot_least : forall w a b, pis_bot w a = true -> pleb w a b = true.
  (** Join contains the left payload. *)
  Parameter pjoin_ub_l : forall w a b, pleb w a (pjoin w a b) = true.
  (** Join contains the right payload. *)
  Parameter pjoin_ub_r : forall w a b, pleb w b (pjoin w a b) = true.
  (** Meet refines the left payload. *)
  Parameter pmeet_lb_l : forall w a b, pleb w (pmeet w a b) a = true.
  (** Meet refines the right payload. *)
  Parameter pmeet_lb_r : forall w a b, pleb w (pmeet w a b) b = true.
  (** Inclusion retains represented integers. *)
  Parameter pgamma_mono : forall w a b z,
    pleb w a b = true -> pgamma w a z -> pgamma w b z.
  (** Bottom represents no integer. *)
  Parameter pgamma_bot : forall w z, ~ pgamma w (pbot w) z.
  (** Top contains every normalized integer at its width. *)
  Parameter ptop_full : forall w z, L.is_word w z -> pgamma w (ptop w) z.
  (** Meet retains every common integer. *)
  Parameter pgamma_meet : forall w a b z,
    pgamma w a z -> pgamma w b z -> pgamma w (pmeet w a b) z.
  (** Recognized bottoms contain no integer. *)
  Parameter pis_bot_sound : forall w a z, pis_bot w a = true -> ~ pgamma w a z.
  (** A constant payload contains the wrapped integer. *)
  Parameter pconst_sound : forall w z, pgamma w (pconst w z) (L.wrap w z).
  (** A recognized point identifies all represented integers. *)
  Parameter ppoint_sound : forall w a z v,
    ppoint w a = Some v -> pgamma w a z -> z = v.
End WORD_PAYLOAD_LAWS.

Module Type WORD_PAYLOAD (L : WORD_LANGUAGE) :=
  WORD_PAYLOAD_OPS L <+ WORD_PAYLOAD_LAWS L.

Module Type WORD_PAYLOAD_TIME (L : WORD_LANGUAGE_T) (Import W : WORD_PAYLOAD L).
  (* spec: psize *)
  Parameter psize : positive -> p -> nat.
  Parameter T_pleb : positive -> p -> p -> N.
  Parameter T_pjoin T_pmeet : positive -> p -> p -> N.
  Parameter T_pis_bot T_ppoint : positive -> p -> N.
  Parameter T_pconst : positive -> Z -> N.
  Parameter c_payload : N.
  (** Payload inclusion charges the two payload sizes. *)
  Parameter T_pleb_le : forall w a b,
    (T_pleb w a b <= c_payload * N.of_nat ((psize w a + psize w b + 1)%nat))%N.
  (** Payload join charges the two payload sizes. *)
  Parameter T_pjoin_le : forall w a b,
    (T_pjoin w a b <= c_payload * N.of_nat ((psize w a + psize w b + 1)%nat))%N.
  (** Payload meet charges the two payload sizes. *)
  Parameter T_pmeet_le : forall w a b,
    (T_pmeet w a b <= c_payload * N.of_nat ((psize w a + psize w b + 1)%nat))%N.
  (** Bottom recognition charges the payload size. *)
  Parameter T_pis_bot_le : forall w a,
    (T_pis_bot w a <= c_payload * N.of_nat ((psize w a + 1)%nat))%N.
  (** Point recognition charges the payload size. *)
  Parameter T_ppoint_le : forall w a,
    (T_ppoint w a <= c_payload * N.of_nat ((psize w a + 1)%nat))%N.
  (** Constant abstraction charges the width and literal bit size. *)
  Parameter T_pconst_le : forall w z, (T_pconst w z <=
    c_payload * N.of_nat (((Pos.to_nat w + Z.size_nat z + 1) ^ 2)%nat))%N.
End WORD_PAYLOAD_TIME.

Module Type WORD_PAYLOAD_T (L : WORD_LANGUAGE_T) := WORD_PAYLOAD L <+ WORD_PAYLOAD_TIME L.

Module Type WORD_TABLE_OPS (L : WORD_LANGUAGE_OPS) (W : WORD_PAYLOAD_OPS L).
  Parameter wfwd : L.op -> positive -> list (positive * W.p) -> option W.p.
  Parameter wbwd : L.op -> positive -> W.p -> list (positive * W.p) -> option (list W.p).
End WORD_TABLE_OPS.

Module Type WORD_TABLE_LAWS (L : WORD_LANGUAGE) (W : WORD_PAYLOAD L)
    (Import T : WORD_TABLE_OPS L W).
  (** A forward word entry retains each concrete result at its checked width. *)
  Parameter wfwd_sound : forall o rw wps cs z r, wfwd o rw wps = Some r ->
    Forall2 (fun wp c => fst wp = fst c /\ W.pgamma (fst wp) (snd wp) (snd c)) wps cs ->
    L.eval_op o cs = Some (rw, z) -> W.pgamma rw r z.
  (** A backward word entry retains each concrete operand in its original position. *)
  Parameter wbwd_sound : forall o rw q wps ys cs z, wbwd o rw q wps = Some ys ->
    Forall2 (fun wp c => fst wp = fst c /\ W.pgamma (fst wp) (snd wp) (snd c)) wps cs ->
    L.eval_op o cs = Some (rw, z) -> W.pgamma rw q z ->
    Forall2 (fun wp c => W.pgamma (fst wp) (snd wp) (snd c))
      (combine (map fst wps) ys) cs.
End WORD_TABLE_LAWS.

Module Type WORD_TABLE (L : WORD_LANGUAGE) (W : WORD_PAYLOAD L) :=
  WORD_TABLE_OPS L W <+ WORD_TABLE_LAWS L W.

Module Type WORD_TABLE_TIME (L : WORD_LANGUAGE_T) (W : WORD_PAYLOAD_T L)
    (Import T : WORD_TABLE L W).
  Parameter T_wfwd : L.op -> positive -> list (positive * W.p) -> N.
  Parameter T_wbwd : L.op -> positive -> W.p -> list (positive * W.p) -> N.
  Parameter c_word_table : N.
  (** Forward table time has the published quadratic width bound. *)
  Parameter T_wfwd_le : forall o rw xs,
    (T_wfwd o rw xs <= c_word_table * N.of_nat
      (((Pos.to_nat rw +
        fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2)%nat))%N.
  (** Backward table time has the published quadratic width bound. *)
  Parameter T_wbwd_le : forall o rw q xs,
    (T_wbwd o rw q xs <= c_word_table * N.of_nat
      (((Pos.to_nat rw +
        fold_right Nat.add 0 (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2)%nat))%N.
End WORD_TABLE_TIME.

Module Type WORD_TABLE_T (L : WORD_LANGUAGE_T) (W : WORD_PAYLOAD_T L) :=
  WORD_TABLE L W <+ WORD_TABLE_TIME L W.

Module Type WORD_PLAN (L : WORD_LANGUAGE_T) (W : WORD_PAYLOAD_T L)
    (T : WORD_TABLE_T L W).
  Parameter untag : list (tagged W.p) -> option (list (positive * W.p)).
  Parameter retag : list positive -> list W.p -> list (tagged W.p).
  Parameter T_untag : list (tagged W.p) -> N.
  Parameter T_retag : list positive -> list W.p -> N.
  Parameter k_untag k_retag : N.
  Definition tagged_gamma (a : tagged W.p) (c : positive * Z) : Prop :=
    match a with
    | TBot => False
    | TAny => True
    | TVal w p => fst c = w /\ L.is_word w (snd c) /\ W.pgamma w p (snd c)
    end.
  (** Untagging retains widths and payload interpretations. *)
  Parameter F1_untag_sound : forall xs cs wps,
    Forall2 tagged_gamma xs cs -> untag xs = Some wps ->
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      W.pgamma (fst wp) (snd wp) (snd c)) wps cs.
  (** Retagging restores the original operand widths. *)
  Parameter F2_retag_sound : forall ws ps cs,
    Forall2 (fun w c => fst c = w /\ L.is_word w (snd c)) ws cs ->
    Forall2 (fun wp c => W.pgamma (fst wp) (snd wp) (snd c)) (combine ws ps) cs ->
    length ps = length ws -> Forall2 tagged_gamma (retag ws ps) cs.
  (** Untagging charges one constant step per tag. *)
  Parameter T1_untag : forall xs, (T_untag xs <= k_untag * N.of_nat ((length xs + 1)%nat))%N.
  (** Retagging charges one constant step per operand. *)
  Parameter T2_retag : forall ws ps,
    (T_retag ws ps <= k_retag * N.of_nat ((length ws + length ps + 1)%nat))%N.
End WORD_PLAN.
