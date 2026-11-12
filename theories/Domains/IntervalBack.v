(** * Interval backward operations

    Result assumptions refine comparisons and nonwrapping arithmetic.
    For example, equality to one refines both operands of an equality test.
    Builds on: IntervalOps and fixed-width word operators. *)

From Stdlib Require Import ZArith List Bool Lia.
From Argent Require Import Time Std.
From Galois.Bits Require Import Word Op.
From Galois.Domains Require Import IntervalOps ThresholdsSig IntervalSig ValueSig WordSig.
Import List.ListNotations.
Local Open Scope Z_scope.

Module IntervalBackCode (T : THRESHOLDS_OPS) (S : INTERVAL_SCALAR_OPS T).
  Include IntervalOpsCode T S.
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
    (S : INTERVAL_SCALAR_OPS T)
    <: (WORD_PAYLOAD_OPS L with Definition p := itv).
  Definition p := itv.
  Definition interval_top (w : positive) := I (Fin 0) (Fin (Word.modulus w - 1)).
  Definition interval_clip w a := interval_payload_clip S.interval_meet w a.
  Definition pleb w a b := S.interval_leb (interval_clip w a) (interval_clip w b).
  Definition pjoin w a b := S.interval_join (interval_clip w a) (interval_clip w b).
  Definition pmeet w a b := S.interval_meet (interval_clip w a) (interval_clip w b).
  Definition pbot (_ : positive) := IBot.
  Definition ptop w := interval_top w.
  Definition pis_bot w a := S.interval_is_bot (interval_clip w a).
  Definition pconst w z := I (Fin (Word.wrap w z)) (Fin (Word.wrap w z)).
  Definition ppoint w a := S.interval_singleton (interval_clip w a).
  Definition pwparam := ttree.
  Definition pwiden ts w a b :=
    if pleb w b a then a else interval_clip w
      (S.interval_stable_widen ts (interval_clip w a) (interval_clip w b)).
  Definition pnarrow w a b := S.interval_narrow (interval_clip w a) (interval_clip w b).
End IntervalPayloadCode.

Module IntervalWordTableCode (L : WORD_LANGUAGE_OPS) (T : THRESHOLDS_OPS)
    (S : INTERVAL_SCALAR_OPS T)
    (D : WORD_PAYLOAD_OPS L with Definition p := itv) <: WORD_TABLE_OPS L D.
  Include IntervalBackCode T S.
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

Module IntervalPayload (L : WORD_LANGUAGE) (T : THRESHOLDS) (S : INTERVAL_SCALAR_OPS T)
    <: INTERVAL_PAYLOAD_PINNED L T S.
  Include IntervalPayloadCode L T S.
  Include S.
  Include INTERVAL_PAYLOAD_SPEC T S.
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
  Definition pwrank := payload_wrank.
  (** Widening contains both payloads. *)
  Lemma pwiden_ub_l : forall q w a b, pleb w a (pwiden q w a b) = true.
  Proof. Admitted. (* CONVERT: interval_laws: In environment *)
  Lemma pwiden_ub_r : forall q w a b, pleb w b (pwiden q w a b) = true.
  Proof. Admitted. (* CONVERT: interval_laws: In environment *)
  (** Stable widening retains the previous payload. *)
  Lemma pwiden_stable : forall q w a b, pleb w b a = true -> pwiden q w a b = a.
  Proof. Admitted.
  (** An unstable nonbottom widening strictly lowers the rank. *)
  Lemma pwrank_widen : forall q w a b, pis_bot w a = false -> pleb w b a = false ->
    (pwrank q w (pwiden q w a b) < pwrank q w a)%nat.
  Proof. Admitted. (* CONVERT: interval_widening_rank_on: The variable interval_rank was not found in the current environment. *)
  (** Nonbottom widening does not increase rank. *)
  Lemma pwrank_widen_le : forall q w a b, pis_bot w a = false ->
    (pwrank q w (pwiden q w a b) <= pwrank q w a)%nat.
  Proof. Admitted. (* CONVERT: interval_widening_rank_on: No product even after head-reduction. *)
  (** Narrowing lies between ordered inputs. *)
  Lemma pnarrow_between : forall w a b, pleb w b a = true ->
    pleb w b (pnarrow w a b) = true /\ pleb w (pnarrow w a b) a = true.
  Proof. Admitted. (* CONVERT: pnarrow_between: clipped operands prevent the raw interval case split. *)
  (** Width-specific inclusion is reflexive. *)
  Lemma pleb_refl : forall w a, pleb w a a = true.
  Proof.
    intros w a. unfold pleb. destruct (interval_clip w a) as [|l h]; cbn; [reflexivity|].
    now rewrite !bound_leb_refl.
  Qed.
  (** Width-specific inclusion is transitive. *)
  Lemma pleb_trans : forall w a b c,
    pleb w a b = true -> pleb w b c = true -> pleb w a c = true.
  Proof.
    intros w a b c. unfold pleb.
    destruct (interval_clip w a) as [|la ha];
      destruct (interval_clip w b) as [|lb hb];
      destruct (interval_clip w c) as [|lc hc]; cbn; try discriminate; try reflexivity.
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
  Proof. Admitted. (* CONVERT: pjoin_ub_l: Unable to unify raw order with clipped order. *)
  (** Join contains the right payload. *)
  Lemma pjoin_ub_r : forall w a b, pleb w b (pjoin w a b) = true.
  Proof. Admitted. (* CONVERT: pjoin_ub_r: Unable to unify raw order with clipped order. *)
  (** Meet refines the left payload. *)
  Lemma pmeet_lb_l : forall w a b, pleb w (pmeet w a b) a = true.
  Proof. Admitted. (* CONVERT: pmeet_lb_l: The variable lb was not found. *)
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
    unfold pconst, in_bnd. split; reflexivity.
  Qed.
  (** A recognized point identifies all represented integers. *)
  Lemma ppoint_sound : forall w a z v,
    ppoint w a = Some v -> L.is_word w z -> pgamma w a z -> z = v.
  Proof. Admitted. (* CONVERT: interval_is_point_sound: The reference interval_is_point was not found in the current *)

  (** Payload inclusion reads both operands through the word range. *)
  Lemma F_pleb : forall w a b, pleb w a b = S.interval_leb
    (interval_payload_clip S.interval_meet w a) (interval_payload_clip S.interval_meet w b).
  Proof. Admitted.
  (** Payload bottom recognition reads the clipped interval. *)
  Lemma F_pis_bot : forall w a, pis_bot w a =
    S.interval_is_bot (interval_payload_clip S.interval_meet w a).
  Proof. Admitted.
  (** Payload join combines clipped operands. *)
  Lemma F_pjoin : forall w a b, pjoin w a b = S.interval_join
    (interval_payload_clip S.interval_meet w a) (interval_payload_clip S.interval_meet w b).
  Proof. Admitted.
  (** Payload meet combines clipped operands. *)
  Lemma F_pmeet : forall w a b, pmeet w a b = S.interval_meet
    (interval_payload_clip S.interval_meet w a) (interval_payload_clip S.interval_meet w b).
  Proof. Admitted.
  (** Payload widening retains stable raw values and clips unstable results. *)
  Lemma F_pwiden : forall q w a b, pwiden q w a b =
    if pleb w b a then a else interval_payload_clip S.interval_meet w
      (S.interval_stable_widen q (interval_payload_clip S.interval_meet w a)
        (interval_payload_clip S.interval_meet w b)).
  Proof. Admitted.
  (** Payload narrowing combines clipped operands. *)
  Lemma F_pnarrow : forall w a b, pnarrow w a b = S.interval_narrow
    (interval_payload_clip S.interval_meet w a) (interval_payload_clip S.interval_meet w b).
  Proof. Admitted.
  (** Payload rank treats unsigned word boundaries as terminal endpoints. *)
  Lemma F_pwrank : forall q w a, pwrank q w a = payload_wrank q w a.
  Proof. Admitted.
  (** Payload bottom is the empty interval. *)
  Lemma F_pbot : forall w, pbot w = IBot.
  Proof. Admitted.
  (** Payload top is the inclusive unsigned word range. *)
  Lemma F_ptop : forall w, ptop w = I (Fin 0) (Fin (Word.modulus w - 1)).
  Proof. Admitted.
  (** Payload constants are wrapped singleton intervals. *)
  Lemma F_pconst : forall w z, pconst w z = I (Fin (L.wrap w z)) (Fin (L.wrap w z)).
  Proof. Admitted.
  (** Payload points are recognized after clipping. *)
  Lemma F_ppoint : forall w a, ppoint w a =
    S.interval_singleton (interval_payload_clip S.interval_meet w a).
  Proof. Admitted.
  (** Payload concretization intersects raw endpoints with normalized words. *)
  Lemma F_pgamma : forall w a z, pgamma w a z <-> L.is_word w z /\
    match a with IBot => False | I lo hi => in_bnd lo hi z end.
  Proof. Admitted.
End IntervalPayload.

Module IntervalPayloadT (L : WORD_LANGUAGE_T) (T : THRESHOLDS_T)
    (S : INTERVAL_SCALAR_T T) <: INTERVAL_PAYLOAD_ALL L T S.
  Include IntervalPayload L T S.

  TimeFun interval_top.
  TimeFun interval_clip.
  TimeFun pleb.
  TimeFun pjoin.
  TimeFun pmeet.
  TimeFun pbot.
  TimeFun ptop.
  TimeFun pis_bot.
  TimeFun pconst.
  TimeFun ppoint.
  TimeFun pwiden.
  TimeFun pnarrow.

  Definition psize (w : positive) (a : p) : nat := Pos.to_nat w + interval_bits a + 1.
  Definition pwsize (q : pwparam) : nat := (T.depth q + 1) * (T.tree_bits q + 1).
  Definition c_payload : N := 1%N. (* STUB *)
  Definition k_payload_clip : N := 1%N. (* STUB *)

  (** Joined payloads fit within the combined operand sizes. *)
  Lemma pjoin_size : forall w a b,
    (N.of_nat (psize w (pjoin w a b)) <=
      c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Met payloads fit within the combined operand sizes. *)
  Lemma pmeet_size : forall w a b,
    (N.of_nat (psize w (pmeet w a b)) <=
      c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Widened payloads fit within the operand and parameter sizes. *)
  Lemma pwiden_size : forall q w a b,
    (N.of_nat (psize w (pwiden q w a b)) <=
      c_payload * N.of_nat (psize w a + psize w b + pwsize q + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Narrowed payloads fit within the combined operand sizes. *)
  Lemma pnarrow_size : forall w a b,
    (N.of_nat (psize w (pnarrow w a b)) <=
      c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Payload widening charges both operands and its parameters. *)
  Lemma T_pwiden_le : forall q w a b,
    (T_pwiden q w a b <=
      c_payload * N.of_nat (psize w a + psize w b + pwsize q + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Payload narrowing charges both raw payload sizes. *)
  Lemma T_pnarrow_le : forall w a b,
    (T_pnarrow w a b <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Payload inclusion charges both raw payload sizes. *)
  Lemma T_pleb_le : forall w a b,
    (T_pleb w a b <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Payload join charges both raw payload sizes. *)
  Lemma T_pjoin_le : forall w a b,
    (T_pjoin w a b <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Payload meet charges both raw payload sizes. *)
  Lemma T_pmeet_le : forall w a b,
    (T_pmeet w a b <= c_payload * N.of_nat (psize w a + psize w b + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Payload bottom recognition charges the raw endpoint bits and width. *)
  Lemma T_pis_bot_le : forall w a,
    (T_pis_bot w a <= c_payload * N.of_nat (psize w a + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Payload point recognition charges the raw endpoint bits and width. *)
  Lemma T_ppoint_le : forall w a,
    (T_ppoint w a <= c_payload * N.of_nat (psize w a + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Constant abstraction charges the width and raw literal bits. *)
  Lemma T_pconst_le : forall w z,
    (T_pconst w z <= c_payload *
      N.of_nat ((Pos.to_nat w + Z.size_nat z + 1) ^ 2))%N.
  Proof. Admitted. (* STUB *)
  (** Payload size charges its width and the raw endpoint bits. *)
  Lemma F_psize : forall w a, psize w a = Pos.to_nat w + interval_bits a + 1.
  Proof. Admitted. (* STUB *)
  (** Widening parameter size charges a threshold search path. *)
  Lemma F_pwsize : forall q, pwsize q = (T.depth q + 1) * (T.tree_bits q + 1).
  Proof. Admitted. (* STUB *)
  (** Payload rank never exceeds the scalar threshold envelope. *)
  Lemma F_pwrank_le : forall q w a, pwrank q w a <= 2 * (length (T.vals q) + 1).
  Proof. Admitted. (* STUB *)
  (** Constructing the unsigned modulus charges the resulting word width. *)
  Lemma T_modulus_le : forall w,
    (Word.T_modulus w <= k_payload_clip * N.of_nat (Pos.to_nat w + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Concrete wrapping charges the width and raw literal bits. *)
  Lemma T_wrap_le : forall w z,
    (Word.T_wrap w z <= k_payload_clip *
      N.of_nat ((Pos.to_nat w + Z.size_nat z + 1) ^ 2))%N.
  Proof. Admitted. (* STUB *)
  (** Clipping pays for the word bound and the raw endpoint bits. *)
  Lemma T_clip_le : forall w a,
    (T_interval_payload_clip S.interval_meet S.T_interval_meet w a <=
      k_payload_clip * N.of_nat (psize w a + 1))%N.
  Proof. Admitted. (* STUB *)
End IntervalPayloadT.

Module IntervalWordTable (L : WORD_LANGUAGE) (T : THRESHOLDS) (S : INTERVAL_SCALAR_OPS T)
    (W : INTERVAL_PAYLOAD_PINNED L T S)
    <: INTERVAL_WORD_TABLE L W.
  Include IntervalWordTableCode L T S W.
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
