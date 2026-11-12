(** * Interval backward operations

    Result assumptions refine comparisons and nonwrapping arithmetic.
    For example, equality to one refines both operands of an equality test.
    Builds on: IntervalOps and fixed-width word operators. *)

From Stdlib Require Import ZArith List Bool Lia.
From Galois.Bits Require Import Word Op.
From Galois.Domains Require Import IntervalOps ThresholdsSig IntervalSig ValueSig WordSig.
Import List.ListNotations.
Local Open Scope Z_scope.

Module IntervalBackCode (T : THRESHOLDS_OPS).
  Include IntervalOpsCode T.
Definition interval_is_point (i : itv) (z : Z) : bool :=
  match interval_finite i with
  | Some (lo, hi) => Z.eqb lo z && Z.eqb hi z
  | None => false
  end.

Definition interval_assume_pair (o : op) (w : width) (a b q : itv) : itv * itv :=
  match o with
  | bveq => if interval_is_point q 1 then interval_assume_equal a b
            else if interval_is_point q 0 then interval_assume_neq a b else (a, b)
  | bvne => if interval_is_point q 0 then interval_assume_equal a b
            else if interval_is_point q 1 then interval_assume_neq a b else (a, b)
  | bvult => if interval_is_point q 1 then interval_assume_ult a b
             else if interval_is_point q 0 then interval_swap (interval_assume_ule b a)
             else (a, b)
  | bvule => if interval_is_point q 1 then interval_assume_ule a b
             else if interval_is_point q 0 then interval_swap (interval_assume_ult b a)
             else (a, b)
  | bvslt => if interval_is_point q 1 then interval_assume_signed w true true a b
             else if interval_is_point q 0 then interval_assume_signed w true false a b
             else (a, b)
  | bvsle => if interval_is_point q 1 then interval_assume_signed w false true a b
             else if interval_is_point q 0 then interval_assume_signed w false false a b
             else (a, b)
  | bvadd => interval_assume_add w a b q
  | bvsub => interval_assume_sub a b q
  | _ => (a, b)
  end.

  Definition interval_bwd1 rw q (xs : list (width * itv)) : list itv :=
    match xs with
    | [(w, a)] => [interval_assume_rewrap rw (interval_clip w a) q]
    | _ => []
    end.
  Definition interval_bwd2 o (_ : width) q (xs : list (width * itv)) : list itv :=
    match xs with
    | [(wa, a); (wb, b)] =>
      let refined := interval_assume_pair o wa (interval_clip wa a) (interval_clip wb b) q in
      [fst refined; snd refined]
    | _ => []
    end.
End IntervalBackCode.

Module IntervalPayloadCode (L : WORD_LANGUAGE_OPS) (T : THRESHOLDS_OPS)
    <: (WORD_PAYLOAD_OPS L with Definition p := itv).
  Include IntervalOpsCode T.
  Definition p := itv.
  Definition pleb (_ : positive) a b := interval_leb a b.
  Definition pjoin (_ : positive) a b := interval_join a b.
  Definition pmeet (_ : positive) a b := interval_meet a b.
  Definition pbot (_ : positive) := IBot.
  Definition ptop w := interval_top w.
  Definition pis_bot w a := match interval_clip w a with IBot => true | _ => false end.
  Definition pconst w z := interval_const w z.
  Definition ppoint w a := interval_singleton (interval_clip w a).
  Definition pwparam := ttree.
  Definition pwiden ts w a b :=
    if pleb w b a then a else interval_widen ts a b.
  Definition pnarrow (_ : positive) a b := interval_narrow a b.
End IntervalPayloadCode.

Module IntervalWordTableCode (L : WORD_LANGUAGE_OPS) (T : THRESHOLDS_OPS)
    (D : WORD_PAYLOAD_OPS L with Definition p := itv) <: WORD_TABLE_OPS L D.
  Include IntervalBackCode T.
  Definition wfwd (o : L.op) (rw : positive) (xs : list (positive * D.p)) : option D.p :=
    match o, xs with
    | (bvnot | bvneg | bvclz | bvctz | bvpopcnt | bvzext _ | bvtrunc _ | bvsext _),
        [(w, a)] =>
      let a := interval_clip w a in
      Some (match o with
        | bvnot => interval_not rw a
        | bvneg => interval_neg rw a
        | bvclz | bvctz | bvpopcnt => interval_counts rw
        | bvzext _ | bvtrunc _ => interval_rewrap rw a
        | _ => interval_sext rw w a
        end)
    | (bvadd | bvsub | bvmul | bvudiv | bvurem | bvsdiv | bvsrem | bvsmod |
       bvand | bvor | bvxor | bvshl | bvlshr | bvashr | bveq | bvne |
       bvult | bvule | bvslt | bvsle | bvconcat), [(wa, a); (wb, b)] =>
      let a := interval_clip wa a in
      let b := interval_clip wb b in
      Some (match o with
        | bvadd => interval_add rw a b | bvsub => interval_sub rw a b
        | bvmul => interval_mul rw a b | bvudiv => interval_udiv rw a b
        | bvurem => interval_urem rw a b | bvsdiv => interval_sdiv rw a b
        | bvsrem => interval_srem rw a b | bvsmod => interval_smod rw a b
        | bvand => interval_and rw a b | bvor | bvxor => interval_or_xor rw a b
        | bvshl => interval_shl rw a b | bvlshr => interval_lshr rw a b
        | bvashr => interval_ashr rw a b | bveq => interval_eq a b
        | bvne => interval_bool_not (interval_eq a b) | bvult => interval_ult a b
        | bvule => interval_ule a b | bvslt => interval_signed_compare wa true a b
        | bvsle => interval_signed_compare wa false a b
        | _ => interval_concat rw wb a b
        end)
    | bvite, [_; (wa, a); (wb, b)] =>
      Some (interval_join (interval_clip wa a) (interval_clip wb b))
    | _, _ => None
    end.
  Definition wbwd (o : L.op) (rw : positive) (q : D.p)
      (xs : list (positive * D.p)) : option (list D.p) :=
    match o, xs with
    | (bvzext _ | bvtrunc _), [_] => Some (interval_bwd1 rw q xs)
    | (bveq | bvne | bvult | bvule | bvslt | bvsle | bvadd | bvsub), [_; _] =>
      Some (interval_bwd2 o rw q xs)
    | _, _ => None
    end.
End IntervalWordTableCode.

Local Close Scope Z_scope.

Module IntervalPayload (L : WORD_LANGUAGE) (T : THRESHOLDS) <: INTERVAL_PAYLOAD L.
  Include IntervalPayloadCode L T.
  (** Every bound is below itself. *)
  Theorem bound_leb_refl : forall a, bound_leb a a = true.
  Proof.
    intros [|z|]; cbn; try reflexivity.
    apply Z.leb_refl.
  Qed.
  
  (** Bound comparison is transitive. *)
  Theorem bound_leb_trans : forall a b c,
    bound_leb a b = true -> bound_leb b c = true -> bound_leb a c = true.
  Proof.
    intros [|x|] [|y|] [|z|]; cbn; try discriminate; try reflexivity.
    intros Hxy Hyz. apply Z.leb_le in Hxy. apply Z.leb_le in Hyz.
    apply Z.leb_le. lia.
  Qed.
  
  (** Any two bounds are comparable. *)
  Theorem bound_leb_total : forall a b, bound_leb a b = true \/ bound_leb b a = true.
  Proof.
    intros [|x|] [|y|]; cbn; try (now left); try (now right).
    destruct (Z.leb x y) eqn:Hxy; [now left|right].
    apply Z.leb_gt in Hxy. apply Z.leb_le. lia.
  Qed.
  
  (** The minimum is below its left input. *)
  Theorem bound_min_lower_l : forall a b, bound_leb (bound_min a b) a = true.
  Proof.
    intros a b. unfold bound_min. destruct (bound_leb a b) eqn:Hab.
    - apply bound_leb_refl.
    - destruct (bound_leb_total a b) as [H|H]; congruence.
  Qed.
  
  (** The minimum is below its right input. *)
  Theorem bound_min_lower_r : forall a b, bound_leb (bound_min a b) b = true.
  Proof.
    intros a b. unfold bound_min. destruct (bound_leb a b) eqn:Hab.
    - exact Hab.
    - apply bound_leb_refl.
  Qed.
  
  (** A common lower bound is below the minimum. *)
  Theorem bound_min_greatest : forall a b c,
    bound_leb c a = true -> bound_leb c b = true -> bound_leb c (bound_min a b) = true.
  Proof.
    intros a b c Ha Hb. unfold bound_min. destruct (bound_leb a b); assumption.
  Qed.
  
  (** The maximum is above its left input. *)
  Theorem bound_max_upper_l : forall a b, bound_leb a (bound_max a b) = true.
  Proof.
    intros a b. unfold bound_max. destruct (bound_leb a b) eqn:Hab.
    - exact Hab.
    - apply bound_leb_refl.
  Qed.
  
  (** The maximum is above its right input. *)
  Theorem bound_max_upper_r : forall a b, bound_leb b (bound_max a b) = true.
  Proof.
    intros a b. unfold bound_max. destruct (bound_leb a b) eqn:Hab.
    - apply bound_leb_refl.
    - destruct (bound_leb_total a b) as [H|H]; congruence.
  Qed.
  
  (** The maximum is below every common upper bound. *)
  Theorem bound_max_least : forall a b c,
    bound_leb a c = true -> bound_leb b c = true -> bound_leb (bound_max a b) c = true.
  Proof.
    intros a b c Ha Hb. unfold bound_max. destruct (bound_leb a b); assumption.
  Qed.

  Definition pgamma (w : positive) (a : p) (z : Z) : Prop :=
    L.is_word w z /\ match a with IBot => False | I lo hi => in_bnd lo hi z end.
  Definition pwrank (ts : pwparam) (_ : positive) (a : p) : nat :=
    match a with
    | IBot => 0
    | I lo hi =>
      ((match hi with Fin z => 1 + length (filter (fun u => (z <? u)%Z) (T.vals ts))
        | _ => 0 end) +
       (match lo with Fin z => 1 + length (filter (fun u => (u <? z)%Z) (T.vals ts))
        | _ => 0 end))%nat
    end.
  (** Widening contains both payloads. *)
  Lemma pwiden_ub_l : forall q w a b, pleb w a (pwiden q w a b) = true.
  Proof. Admitted.
  Lemma pwiden_ub_r : forall q w a b, pleb w b (pwiden q w a b) = true.
  Proof. Admitted.
  (** Stable widening retains the previous payload. *)
  Lemma pwiden_stable : forall q w a b, pleb w b a = true -> pwiden q w a b = a.
  Proof. Admitted.
  (** An unstable nonbottom widening strictly lowers the rank. *)
  Lemma pwrank_widen : forall q w a b, pis_bot w a = false -> pleb w b a = false ->
    (pwrank q w (pwiden q w a b) < pwrank q w a)%nat.
  Proof. Admitted.
  (** Nonbottom widening does not increase rank. *)
  Lemma pwrank_widen_le : forall q w a b, pis_bot w a = false ->
    (pwrank q w (pwiden q w a b) <= pwrank q w a)%nat.
  Proof. Admitted.
  (** Narrowing lies between ordered inputs. *)
  Lemma pnarrow_between : forall w a b, pleb w b a = true ->
    pleb w b (pnarrow w a b) = true /\ pleb w (pnarrow w a b) a = true.
  Proof. Admitted.
  (** Width-specific inclusion is reflexive. *)
  Lemma pleb_refl : forall w a, pleb w a a = true.
  Proof.
  intro w. intros [|l h]; cbn; [reflexivity|].
    now rewrite !bound_leb_refl.

  Qed.
  (** Width-specific inclusion is transitive. *)
  Lemma pleb_trans : forall w a b c,
    pleb w a b = true -> pleb w b c = true -> pleb w a c = true.
  Proof.
  intro w. intros [|la ha] [|lb hb] [|lc hc]; cbn; try discriminate; try reflexivity.
    intros Hab Hbc. apply andb_true_iff in Hab as [Hlb Hhb].
    apply andb_true_iff in Hbc as [Hlc Hhc]. apply andb_true_iff. split;
      eapply bound_leb_trans; eassumption.

  Qed.
  (** Bottom is below every payload. *)
  Lemma pbot_least : forall w a, pleb w (pbot w) a = true.
  Proof.
  intro w. intros [|l h]; reflexivity.

  Qed.
  (** Top is above every payload. *)
  Lemma ptop_greatest : forall w a, pleb w a (ptop w) = true.
  Proof. Admitted.
  (** The bottom test recognizes bottom. *)
  Lemma pis_bot_bot : forall w, pis_bot w (pbot w) = true.
  Proof. Admitted.
  (** Recognized bottoms are below every payload. *)
  Lemma pis_bot_least : forall w a b, pis_bot w a = true -> pleb w a b = true.
  Proof. Admitted.
  (** Join contains the left payload. *)
  Lemma pjoin_ub_l : forall w a b, pleb w a (pjoin w a b) = true.
  Proof.
  intro w. intros [|la ha] [|lb hb]; cbn; try reflexivity; try (now rewrite !bound_leb_refl).
    apply andb_true_iff. split; [apply bound_min_lower_l|apply bound_max_upper_l].

  Qed.
  (** Join contains the right payload. *)
  Lemma pjoin_ub_r : forall w a b, pleb w b (pjoin w a b) = true.
  Proof.
  intro w. intros [|la ha] [|lb hb]; cbn; try reflexivity; try (now rewrite !bound_leb_refl).
    apply andb_true_iff. split; [apply bound_min_lower_r|apply bound_max_upper_r].

  Qed.
  (** Meet refines the left payload. *)
  Lemma pmeet_lb_l : forall w a b, pleb w (pmeet w a b) a = true.
  Proof.

  intros w [|la ha] [|lb hb]; cbn; try reflexivity.
  destruct (bounds_nonempty (bound_max la lb) (bound_min ha hb)); cbn; [|reflexivity].
  apply andb_true_iff. split; [apply bound_max_upper_l|apply bound_min_lower_l].

  Qed.
  (** Meet refines the right payload. *)
  Lemma pmeet_lb_r : forall w a b, pleb w (pmeet w a b) b = true.
  Proof. Admitted.
  (** Inclusion retains represented integers. *)
  Lemma pgamma_mono : forall w a b z,
    pleb w a b = true -> pgamma w a z -> pgamma w b z.
  Proof. Admitted. (* CONVERT: interval_word_laws: The variable gamma_monotone was not found in the current environment. *)
  (** Bottom represents no integer. *)
  Lemma pgamma_bot : forall w z, ~ pgamma w (pbot w) z.
  Proof.
intros w z [_ Hempty]. exact Hempty.

  Qed.
  (** Top contains every normalized integer at its width. *)
  Lemma ptop_full : forall w z, L.is_word w z -> pgamma w (ptop w) z.
  Proof.
    intros w z Hword. split; [exact Hword|].
    unfold ptop, interval_top, in_bnd.
    destruct Hword as [Hlower Hupper]. split; lia.
  Qed.
  (** Meet retains every common integer. *)
  Lemma pgamma_meet : forall w a b z,
    pgamma w a z -> pgamma w b z -> pgamma w (pmeet w a b) z.
  Proof. Admitted. (* CONVERT: interval_meet_sound: No such assumption. *)
  (** Recognized bottoms contain no integer. *)
  Lemma pis_bot_sound : forall w a z, pis_bot w a = true -> ~ pgamma w a z.
  Proof. Admitted. (* CONVERT: interval_shape_laws: Expects a disjunctive pattern with 3 branches. *)
  (** Every payload below a recognized bottom is recognized as bottom. *)
  Lemma pis_bot_below : forall w a b,
    pleb w a b = true -> pis_bot w b = true -> pis_bot w a = true.
  Proof. Admitted.
  (** A constant payload contains the wrapped integer. *)
  Lemma pconst_sound : forall w z, pgamma w (pconst w z) (L.wrap w z).
  Proof.
    intros w z. split; [apply L.wrap_is_word|].
    unfold pconst, interval_const, in_bnd. split; reflexivity.
  Qed.
  (** A recognized point identifies all represented integers. *)
  Lemma ppoint_sound : forall w a z v,
    ppoint w a = Some v -> L.is_word w z -> pgamma w a z -> z = v.
  Proof. Admitted. (* CONVERT: interval_is_point_sound: The reference interval_is_point was not found in the current *)
End IntervalPayload.

Module IntervalWordTable (L : WORD_LANGUAGE) (T : THRESHOLDS) (W : INTERVAL_PAYLOAD L)
    <: INTERVAL_WORD_TABLE L W.
  Include IntervalWordTableCode L T W.
  (** A forward word entry retains each concrete result at its checked width. *)
  Lemma wfwd_sound : forall o rw wps cs z r, wfwd o rw wps = Some r ->
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      W.pgamma (fst wp) (snd wp) (snd c)) wps cs ->
    L.eval_op o cs = Some (rw, z) -> W.pgamma rw r z.
  Proof. Admitted. (* CONVERT: interval_table_laws: Unexpected name (no introduction patterns were expected in the *)
  (** A backward word entry retains each concrete operand in its original position. *)
  Lemma wbwd_sound : forall o rw q wps ys cs z, wbwd o rw q wps = Some ys ->
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      W.pgamma (fst wp) (snd wp) (snd c)) wps cs ->
    L.eval_op o cs = Some (rw, z) -> W.pgamma rw q z ->
    Forall2 (fun wp c => W.pgamma (fst wp) (snd wp) (snd c))
      (combine (map fst wps) ys) cs.
  Proof. Admitted. (* CONVERT: interval_table_laws: Unexpected name (no introduction patterns were expected in the *)
End IntervalWordTable.
