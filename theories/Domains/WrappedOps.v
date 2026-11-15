(** * Circular word interval operations

    Transfers refine and evaluate circular intervals through linear pieces.
    For example, a binary operation checks each piece at the signed pole.
    Builds on: Wrapped, IntervalBack and WordSig. *)

From Stdlib Require Import ZArith List Bool Lia.
From Argent Require Import Time.
From Galois.Bits Require Import Word Op Fun Testbit Arith Tactics.
From Galois.Domains Require Import ValueSig WordSig WrappedSig Wrapped IntervalSig IntervalBack
  Thresholds BitsLang Tagged.
Import List.ListNotations.
Local Open Scope Z_scope.

Module WrappedIntervalBack.
  Include (IntervalBackCode ThresholdsCode WrappedScalar).
  TimeFun interval_top.
  TimeFun interval_checked.
  TimeFun interval_sign.
  TimeFun interval_neg.
  TimeFun interval_udiv.
  TimeFun interval_urem.
  TimeFun interval_assume_add.
  TimeFun interval_assume_sub.
  TimeFun interval_assume_rewrap.
  TimeFun interval_is_point.
  TimeFun interval_assume_equal.
  TimeFun interval_assume_ult.
  TimeFun interval_assume_ule.
  TimeFun interval_swap.
  TimeFun interval_assume_neq.
  TimeFun interval_assume_signed.
  TimeFun interval_assume_pair.
End WrappedIntervalBack.

Module WrappedIntervalPayload := IntervalPayloadCode WordLanguageCode ThresholdsCode WrappedScalar.
Module WrappedIntervalTable.
  Include (IntervalWordTableCode WordLanguageCode ThresholdsCode WrappedScalar
    WrappedIntervalPayload).
  TimeFun interval_top.
  TimeFun interval_const.
  TimeFun interval_clip.
  TimeFun interval_checked.
  TimeFun interval_add.
  TimeFun interval_add_modular.
  TimeFun interval_sub.
  TimeFun interval_mul.
  TimeFun interval_neg.
  TimeFun interval_concat.
  TimeFun interval_rewrap.
  TimeFun interval_counts.
  TimeFun interval_udiv.
  TimeFun interval_urem.
  TimeFun interval_not.
  TimeFun interval_and.
  TimeFun interval_mask.
  TimeFun interval_or_xor.
  TimeFun interval_truth.
  TimeFun interval_bool_not.
  TimeFun interval_ult.
  TimeFun interval_ule.
  TimeFun interval_eq.
  TimeFun interval_shl.
  TimeFun interval_lshr.
  TimeFun interval_sign.
  TimeFun interval_signed.
  TimeFun interval_sext.
  TimeFun interval_signed_compare.
  TimeFun interval_sdiv.
  TimeFun interval_srem.
  TimeFun interval_mod_choice.
  TimeFun interval_smod_base.
  TimeFun interval_smod.
  TimeFun interval_ashr_small.
  TimeFun interval_ashr.
  TimeFun wfwd.
End WrappedIntervalTable.

Definition wrapped_project (target source : width) (q : wrapped) : wrapped :=
  let pieces := wrapped_parts source q in
  wrapped_join target
    (wrapped_of_interval target (fst pieces)) (wrapped_of_interval target (snd pieces)).
TimeFun wrapped_project.

Definition wrapped_signed_piece (division : bool) (w : width) (a b : itv) : wrapped :=
  match a, b with
  | IBot, _ | _, IBot => WBot
  | _, _ =>
    match WrappedIntervalBack.interval_sign w a, WrappedIntervalBack.interval_sign w b with
    | Some sa, Some sb =>
      let aa := if sa then WrappedIntervalBack.interval_neg w a else a in
      let bb := if sb then WrappedIntervalBack.interval_neg w b else b in
      let magnitude := wrapped_of_interval w
        (if division then WrappedIntervalBack.interval_udiv w aa bb
         else WrappedIntervalBack.interval_urem w aa bb) in
      if (if division then xorb sa sb else sa) then wrapped_neg w magnitude else magnitude
    | _, _ => WFull
    end
  end.
TimeFun wrapped_signed_piece.

Definition wrapped_pair_join (wa wb : width) (a b : wrapped * wrapped) : wrapped * wrapped :=
  (wrapped_join wa (fst a) (fst b), wrapped_join wb (snd a) (snd b)).
TimeFun wrapped_pair_join.

Module WrappedOpsCode (L : WORD_LANGUAGE_OPS) (W : WRAPPED_OPS L).
  Module IP := IntervalPayloadCode L ThresholdsCode WrappedScalar.
  Module IT := IntervalWordTableCode L ThresholdsCode WrappedScalar IP.

  Definition piece_forward (o : op) (xs : list (width * itv)) (rw : width) : wrapped :=
    if existsb (fun x => match snd x with IBot => true | _ => false end) xs then WBot else
    match WrappedIntervalTable.wfwd o rw xs with
    | Some result => wrapped_of_interval rw result
    | None => WFull
    end.

  Definition forward_unary (o : op) (w : width) (a : wrapped) (rw : width) : wrapped :=
    let pieces := wrapped_parts w a in
    wrapped_join rw (piece_forward o [(w, fst pieces)] rw)
      (piece_forward o [(w, snd pieces)] rw).

  Definition piece_binary (o : op) (wa wb : width) (a b : itv) (rw : width) : wrapped :=
    match o with
    | bvsdiv => wrapped_signed_piece true rw a b
    | bvsrem => wrapped_signed_piece false rw a b
    | _ => piece_forward o [(wa, a); (wb, b)] rw
    end.

  Definition piece_cut (o : op) (wa wb : width) (a b : itv) (rw : width) : wrapped :=
    let pa := wrapped_pole_cut wa a in
    let pb := wrapped_pole_cut wb b in
    wrapped_join_four rw
      (piece_binary o wa wb (fst pa) (fst pb) rw)
      (piece_binary o wa wb (fst pa) (snd pb) rw)
      (piece_binary o wa wb (snd pa) (fst pb) rw)
      (piece_binary o wa wb (snd pa) (snd pb) rw).

  Definition forward_binary (o : op) (wa wb : width) (a b : wrapped) (rw : width) : wrapped :=
    let pa := wrapped_parts wa a in
    let pb := wrapped_parts wb b in
    wrapped_join_four rw
      (piece_cut o wa wb (fst pa) (fst pb) rw)
      (piece_cut o wa wb (fst pa) (snd pb) rw)
      (piece_cut o wa wb (snd pa) (fst pb) rw)
      (piece_cut o wa wb (snd pa) (snd pb) rw).

  Definition forward_raw (o : op) (rw : width) (xs : list (width * wrapped)) : option wrapped :=
    match xs with
    | [(w, a)] => Some (match o with
      | bvneg => W.wrapped_neg rw a
      | bvzext _ | bvtrunc _ => wrapped_project rw w a
      | _ => forward_unary o w a rw
      end)
    | [(wa, a); (wb, b)] => Some (match o with
      | bvadd => W.wrapped_add rw a b
      | bvsub => W.wrapped_sub rw a b
      | bvmul => W.wrapped_mul rw a b
      | _ => forward_binary o wa wb a b rw
      end)
    | [_; (_, a); (_, b)] => match o with bvite => Some (W.pjoin rw a b) | _ => None end
    | _ => None
    end.

  Definition assume_consistent (o : op) (wa wb : width) (a b q : itv) : bool :=
    match result_width o [wa; wb] with
    | Some rw =>
      let result := match WrappedIntervalTable.wfwd o rw [(wa, a); (wb, b)] with
        | Some r => r | None => WrappedIntervalBack.interval_top rw end in
      match WrappedScalar.interval_meet result q with IBot => false | _ => true end
    | None => false
    end.

  Definition assume_piece_raw (o : op) (wa wb : width) (a b q : itv) : wrapped * wrapped :=
    match a, b, q with
    | IBot, _, _ | _, IBot, _ | _, _, IBot => (WBot, WBot)
    | _, _, _ =>
      if assume_consistent o wa wb a b q then
        let refined := WrappedIntervalBack.interval_assume_pair o wa a b q in
        (wrapped_of_interval wa (fst refined), wrapped_of_interval wb (snd refined))
      else (WBot, WBot)
    end.

  Definition assume_piece (o : op) (wa wb : width) (a b q : itv) : wrapped * wrapped :=
    let pa := wrapped_pole_cut wa a in
    let pb := wrapped_pole_cut wb b in
    wrapped_pair_join wa wb
      (wrapped_pair_join wa wb (assume_piece_raw o wa wb (fst pa) (fst pb) q)
        (assume_piece_raw o wa wb (fst pa) (snd pb) q))
      (wrapped_pair_join wa wb (assume_piece_raw o wa wb (snd pa) (fst pb) q)
        (assume_piece_raw o wa wb (snd pa) (snd pb) q)).

  Definition assume_result (o : op) (wa wb : width) (a b : itv) (rw : width) (q : wrapped)
      : wrapped * wrapped :=
    let results := wrapped_parts rw q in
    wrapped_pair_join wa wb (assume_piece o wa wb a b (fst results))
      (assume_piece o wa wb a b (snd results)).

  Definition assume_binary_base (o : op) (wa wb : width) (a b : wrapped) (rw : width)
      (q : wrapped) : wrapped * wrapped :=
    let pa := wrapped_parts wa a in
    let pb := wrapped_parts wb b in
    let candidates := wrapped_pair_join wa wb
      (wrapped_pair_join wa wb (assume_result o wa wb (fst pa) (fst pb) rw q)
        (assume_result o wa wb (fst pa) (snd pb) rw q))
      (wrapped_pair_join wa wb (assume_result o wa wb (snd pa) (fst pb) rw q)
        (assume_result o wa wb (snd pa) (snd pb) rw q)) in
    (wrapped_meet wa a (fst candidates), wrapped_meet wb b (snd candidates)).

  Definition assume_binary (o : op) (wa wb : width) (a b : wrapped) (rw : width)
      (q : wrapped) : wrapped * wrapped :=
    match o with
    | bvadd => (wrapped_meet wa a (wrapped_sub wa q b), wrapped_meet wb b (wrapped_sub wb q a))
    | bvsub => (wrapped_meet wa a (wrapped_add wa q b), wrapped_meet wb b (wrapped_sub wb a q))
    | _ => assume_binary_base o wa wb a b rw q
    end.

  Definition assume_trunc (w : width) (a : wrapped) (rw : width) (q : wrapped) : wrapped :=
    let pa := wrapped_parts w a in
    let pq := wrapped_parts rw q in
    wrapped_meet w a (wrapped_join_four w
      (wrapped_of_interval w (WrappedIntervalBack.interval_assume_rewrap rw (fst pa) (fst pq)))
      (wrapped_of_interval w (WrappedIntervalBack.interval_assume_rewrap rw (fst pa) (snd pq)))
      (wrapped_of_interval w (WrappedIntervalBack.interval_assume_rewrap rw (snd pa) (fst pq)))
      (wrapped_of_interval w (WrappedIntervalBack.interval_assume_rewrap rw (snd pa) (snd pq)))).

  Definition assume_unary (o : op) (w : width) (a : wrapped) (rw : width) (q : wrapped)
      : wrapped :=
    match o with
    | bvzext _ | bvsext _ => wrapped_meet w a (wrapped_project w rw q)
    | bvtrunc _ => assume_trunc w a rw q
    | _ => wrapped_norm w a
    end.

  Definition backward_raw (o : op) (rw : width) (q : wrapped)
      (xs : list (width * wrapped)) : option (list wrapped) :=
    match xs with
    | [(w, a)] => Some [assume_unary o w a rw q]
    | [(wa, a); (wb, b)] => let p := assume_binary o wa wb a b rw q in Some [fst p; snd p]
    | _ => None
    end.
  Definition backward (o : op) (rw : width) (q : wrapped)
      (xs : list (width * wrapped)) : list wrapped :=
    match backward_raw o rw q xs with
    | Some ys => ys
    | None => map (fun wp => wrapped_norm (fst wp) (snd wp)) xs
    end.
End WrappedOpsCode.

Module WrappedTableCode (L : WORD_LANGUAGE_OPS) (W : WRAPPED_OPS L) <: WORD_TABLE_OPS L W.
  Module Ops := WrappedOpsCode L W.
  Include Ops.
  Definition wfwd := forward_raw.
  Definition wbwd := backward_raw.
End WrappedTableCode.

Module WrappedTable (L : WORD_LANGUAGE) (W : WRAPPED L) <: WRAPPED_TABLE L W.
  Include WrappedTableCode L W.
  Lemma wfwd_sound : forall o rw wps cs z r, wfwd o rw wps = Some r ->
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      W.pgamma (fst wp) (snd wp) (snd c)) wps cs ->
    L.eval_op o cs = Some (rw, z) -> W.pgamma rw r z.
  Proof. Admitted. (* STUB: F2-6 adds public arithmetic soundness laws to WRAPPED. *)
  Lemma wbwd_sound : forall o rw q wps ys cs z, wbwd o rw q wps = Some ys ->
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      W.pgamma (fst wp) (snd wp) (snd c)) wps cs ->
    L.eval_op o cs = Some (rw, z) -> W.pgamma rw q z ->
    Forall2 (fun wp c => W.pgamma (fst wp) (snd wp) (snd c))
      (combine (map fst wps) ys) cs.
  Proof. Admitted. (* STUB: F2-6 adds gamma_arc to WRAPPED. *)
End WrappedTable.

Module WrappedTableClock (L : WORD_LANGUAGE_T) (W : WRAPPED_T L).
  Include WrappedTable L W.
  TimeFun piece_forward.
  TimeFun forward_unary.
  TimeFun piece_binary.
  TimeFun piece_cut.
  TimeFun forward_binary.
  TimeFun forward_raw.
  TimeFun wfwd.
  TimeFun assume_consistent.
  TimeFun assume_piece_raw.
  TimeFun assume_piece.
  TimeFun assume_result.
  TimeFun assume_binary_base.
  TimeFun assume_binary.
  TimeFun assume_trunc.
  TimeFun assume_unary.
  TimeFun backward_raw.
  TimeFun wbwd.
End WrappedTableClock.

Module WrappedTableT (L : WORD_LANGUAGE_T) (W : WRAPPED_T L)
    <: WRAPPED_TABLE_T L W.
  Include WrappedTableClock L W.
  Definition c_word_table : N := 1. (* STUB *)
  Lemma T_wfwd_le : forall o rw xs,
    (T_wfwd o rw xs <= c_word_table * N.of_nat
      (((Pos.to_nat rw + fold_right Nat.add 0
          (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        fold_right Nat.add 0
          (map (fun x => W.psize (fst x) (snd x)) xs))%nat))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_wbwd_le : forall o rw q xs,
    (T_wbwd o rw q xs <= c_word_table * N.of_nat
      (((Pos.to_nat rw + fold_right Nat.add 0
          (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        W.psize rw q +
        fold_right Nat.add 0
          (map (fun x => W.psize (fst x) (snd x)) xs))%nat))%N.
  Proof. Admitted. (* STUB *)
  Lemma wfwd_size_le : forall o rw xs r, wfwd o rw xs = Some r ->
    (N.of_nat (W.psize rw r) <= c_word_table * N.of_nat
      (((Pos.to_nat rw + fold_right Nat.add 0
          (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        fold_right Nat.add 0
          (map (fun x => W.psize (fst x) (snd x)) xs))%nat))%N.
  Proof. Admitted. (* STUB *)
  Lemma wbwd_size_le : forall o rw q xs ys, wbwd o rw q xs = Some ys ->
    (N.of_nat ((length ys + fold_right Nat.add 0
      (map (fun wy => W.psize (fst wy) (snd wy)) (combine (map fst xs) ys)))%nat) <=
      c_word_table * N.of_nat
        (((Pos.to_nat rw + fold_right Nat.add 0
            (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
          W.psize rw q + fold_right Nat.add 0
            (map (fun x => W.psize (fst x) (snd x)) xs))%nat))%N.
  Proof. Admitted. (* STUB *)
End WrappedTableT.

Theorem wrapped_project_sound target source q z :
  wrapped_gamma source q z ->
  wrapped_gamma target (wrapped_project target source q) (wrap target z).
Proof.
  intro Hq. apply wrapped_parts_spec in Hq.
  unfold wrapped_project. apply wrapped_join_sound. destruct Hq as [[_ Hq]|[_ Hq]].
  - left. now apply wrapped_of_interval_sound.
  - right. now apply wrapped_of_interval_sound.
Qed.
Definition wrapped_pair_gamma wa wb (a : wrapped * wrapped) (x y : Z) : Prop :=
  wrapped_gamma wa (fst a) x /\ wrapped_gamma wb (snd a) y.

Theorem wrapped_pole_cut_sound w a z :
  interval_pgamma w a z ->
  interval_pgamma w (fst (wrapped_pole_cut w a)) z \/
  interval_pgamma w (snd (wrapped_pole_cut w a)) z.
Proof.
  intro Ha. pose proof (proj1 Ha) as Hword.
  unfold wrapped_pole_cut. cbn [fst snd].
  destruct (Z_lt_ge_dec z (half w)) as [Hlow|Hhigh].
  - left. apply wrapped_interval_meet_sound; [exact Ha|].
    split; [exact Hword|]. change (0 <= z <= half w - 1). destruct Hword. lia.
  - right. apply wrapped_interval_meet_sound; [exact Ha|].
    split; [exact Hword|]. change (half w <= z <= modulus w - 1). destruct Hword. lia.
Qed.

Theorem wrapped_pair_join_sound wa wb a b x y :
  wrapped_pair_gamma wa wb a x y \/ wrapped_pair_gamma wa wb b x y ->
  wrapped_pair_gamma wa wb (wrapped_pair_join wa wb a b) x y.
Proof.
  intros [[Hax Hay]|[Hbx Hby]]; split; apply wrapped_join_sound;
    first [now left|now right].
Qed.
Theorem wrapped_signed_piece_sound division w a b x y :
  interval_pgamma w a x -> interval_pgamma w b y ->
  wrapped_gamma w (wrapped_signed_piece division w a b)
    (if division then wsdiv w x y else wsrem w x y).
Proof.
  destruct a as [|lo hi], b as [|lo' hi']; intros Ha Hb;
    try (exact (False_rect _ (proj2 Ha))); try (exact (False_rect _ (proj2 Hb))).
  pose proof (proj2 (WrappedIntervalSound.interval_pgamma_spec w (I lo hi) x) Ha) as Hia.
  pose proof (proj2 (WrappedIntervalSound.interval_pgamma_spec w (I lo' hi') y) Hb) as Hib.
  unfold wrapped_signed_piece.
  destruct (WrappedIntervalBack.interval_sign w (I lo hi)) as [sa|] eqn:Hsa;
    destruct (WrappedIntervalBack.interval_sign w (I lo' hi')) as [sb|] eqn:Hsb;
    try (destruct division; [apply wsdiv_is_word|apply wsrem_is_word]).
  pose proof (WrappedIntervalSound.interval_sign_sound w (I lo hi) x sa Hia Hsa) as Hx.
  pose proof (WrappedIntervalSound.interval_sign_sound w (I lo' hi') y sb Hib Hsb) as Hy.
  destruct division; destruct sa, sb; rewrite ?wsdiv_value, ?wsrem_value, Hx, Hy;
    cbn [xorb]; repeat rewrite wneg_value;
    try apply wrapped_neg_sound; apply wrapped_interval_value_sound;
    apply WrappedIntervalSound.interval_pgamma_spec;
    first [apply WrappedIntervalSound.interval_udiv_sound |
      apply WrappedIntervalSound.interval_urem_sound];
    try apply WrappedIntervalSound.interval_neg_sound; assumption.
Qed.

Definition wrapped_interval_payload_sound (wp : width * itv) (y : word) : Prop :=
  fst wp = fst y /\ interval_pgamma (fst wp) (snd wp) (snd y).


Module WrappedIntervalCheckedPayload := IntervalPayload WordLanguage ThresholdsT WrappedScalar.
Module WrappedIntervalCheckedTable := IntervalWordTable WordLanguage ThresholdsT WrappedScalar
  WrappedIntervalCheckedPayload.

(** Piece operands supply the checked interval table's payload relation. *)
Local Lemma wrapped_interval_inputs xs cs :
  Forall2 wrapped_interval_payload_sound xs cs ->
  Forall2 (fun wp c => fst wp = fst c /\ WordLanguage.is_word (fst c) (snd c) /\
    WrappedIntervalCheckedPayload.pgamma (fst wp) (snd wp) (snd c)) xs cs.
Proof.
  intro Hinputs. induction Hinputs as [|[w a] [v x] xs cs Hhead Htail IH].
  - constructor.
  - unfold wrapped_interval_payload_sound in Hhead. cbn [fst snd] in Hhead.
    destruct Hhead as [Hwidth Ha]. subst v. constructor; [|exact IH].
    split; [reflexivity|]. split; [exact (proj1 Ha)|].
    apply WrappedIntervalCheckedPayload.F_pgamma. exact Ha.
Qed.

(** Successful evaluation belongs to the interval entry or its top fallback. *)
Local Lemma wrapped_interval_forward_sound o xs cs rw z :
  Forall2 wrapped_interval_payload_sound xs cs -> eval_op o cs = Some (rw, z) ->
  interval_pgamma rw
    (match WrappedIntervalTable.wfwd o rw xs with
     | Some result => result
     | None => WrappedIntervalBack.interval_top rw
     end) z.
Proof.
  intros Hinputs Heval.
  destruct (WrappedIntervalTable.wfwd o rw xs) as [result|] eqn:Hentry.
  - apply (proj1 (WrappedIntervalCheckedPayload.F_pgamma rw result z)).
    eapply WrappedIntervalCheckedTable.wfwd_sound;
      [exact Hentry|exact (wrapped_interval_inputs xs cs Hinputs)|exact Heval].
  - apply WrappedIntervalSound.interval_pgamma_spec.
    apply WrappedIntervalSound.interval_top_sound.
    exact (eval_op_is_word _ _ _ Heval).
Qed.

(** Represented interval operands cannot trigger the syntactic bottom test. *)
Local Lemma wrapped_interval_inputs_nonbottom xs cs :
  Forall2 wrapped_interval_payload_sound xs cs ->
  existsb (fun x => match snd x with IBot => true | _ => false end) xs = false.
Proof.
  intro Hinputs. induction Hinputs as [|[w a] [v x] xs cs Hhead Htail IH].
  - reflexivity.
  - destruct Hhead as [Hwidth Ha]. destruct a as [|lo hi].
    + exact (False_rect _ (proj2 Ha)).
    + exact IH.
Qed.


Module WrappedIntervalRefineSound.
  Include WrappedIntervalBack.
  Module Sound := WrappedIntervalSound.
  Local Abbreviation interval_pgamma := Sound.interval_pgamma.

  (** A successful point test identifies the represented concrete value. *)
Local Lemma interval_is_point_sound (w : width) i z value :
    interval_pgamma w i value -> interval_is_point i z = true -> value = z.
  Proof.
    intros Hi Hpoint. unfold interval_is_point in Hpoint.
    destruct (interval_finite_helper i) as [[lo hi]|] eqn:Hfinite; [|discriminate].
    apply andb_true_iff in Hpoint as [Hlo Hhi]. apply Z.eqb_eq in Hlo. apply Z.eqb_eq in Hhi.
    pose proof (Sound.interval_finite_sound w i lo hi value Hi Hfinite). lia.
  Qed.

  (** Scalar backward refinement retains each operand satisfying the result fact. *)
Lemma interval_assume_pair_sound o (w v : width) a b q x y (rw : width) z :
    interval_pgamma w a x -> interval_pgamma v b y -> interval_pgamma rw q z ->
    eval_op o [(w, x); (v, y)] = Some (rw, z) ->
    interval_pgamma w (fst (interval_assume_pair o w a b q)) x /\
    interval_pgamma v (snd (interval_assume_pair o w a b q)) y.
  Proof.
    intros Ha Hb Hq Heval. destruct o; try (solve [split; assumption]).
    all: assert (Hwv : w = v) by
      (match type of Heval with
       | eval_op ?o _ = _ =>
         first
           [ eapply (eval_op_fun2_width o); [reflexivity|exact Heval]
           | eapply (eval_op_cmp_width o); [reflexivity|exact Heval] ]
       end); subst v.
    - rewrite (eval_op_fun2 bvadd w x y BAdd eq_refl) in Heval.
      cbn [eval_binary_tag] in Heval.
      inversion Heval; subst rw z. rewrite Fun.wadd_value in Hq.
      now apply Sound.interval_assume_add_sound.
    - rewrite (eval_op_fun2 bvsub w x y BSub eq_refl) in Heval.
      cbn [eval_binary_tag] in Heval.
      inversion Heval; subst rw z. rewrite Fun.wsub_value in Hq.
      now apply Sound.interval_assume_sub_sound.
    - unfold interval_assume_pair.
      rewrite (eval_op_cmp bveq w x y CEq eq_refl) in Heval.
      cbn [eval_comparison_tag] in Heval.
      rewrite (wrap_id w x (proj1 Ha)), (wrap_id w y (proj1 Hb)) in Heval.
      destruct (interval_is_point q 1) eqn:Hpoint.
      + pose proof (interval_is_point_sound rw q 1 z Hq Hpoint) as Hz.
        inversion Heval; subst rw z. destruct (Z.eqb x y) eqn:Heq; [|discriminate].
        apply Z.eqb_eq in Heq. subst y. now apply Sound.interval_assume_equal_sound.
      + destruct (interval_is_point q 0) eqn:Hpoint0; [|split; assumption].
        pose proof (interval_is_point_sound rw q 0 z Hq Hpoint0) as Hz.
        inversion Heval; subst rw z. destruct (Z.eqb x y) eqn:Heq; [discriminate|].
        apply Z.eqb_neq in Heq. now apply Sound.interval_assume_neq_sound.
    - unfold interval_assume_pair.
      rewrite (eval_op_cmp bvne w x y CNe eq_refl) in Heval.
      cbn [eval_comparison_tag] in Heval.
      rewrite (wrap_id w x (proj1 Ha)), (wrap_id w y (proj1 Hb)) in Heval.
      destruct (interval_is_point q 0) eqn:Hpoint.
      + pose proof (interval_is_point_sound rw q 0 z Hq Hpoint) as Hz.
        inversion Heval; subst rw z. destruct (Z.eqb x y) eqn:Heq; [|discriminate].
        apply Z.eqb_eq in Heq. subst y. now apply Sound.interval_assume_equal_sound.
      + destruct (interval_is_point q 1) eqn:Hpoint1; [|split; assumption].
        pose proof (interval_is_point_sound rw q 1 z Hq Hpoint1) as Hz.
        inversion Heval; subst rw z. destruct (Z.eqb x y) eqn:Heq; [discriminate|].
        apply Z.eqb_neq in Heq. now apply Sound.interval_assume_neq_sound.
    - unfold interval_assume_pair.
      rewrite (eval_op_cmp bvult w x y CUlt eq_refl) in Heval.
      cbn [eval_comparison_tag] in Heval. rewrite Fun.wult_value in Heval.
      rewrite (wrap_id w x (proj1 Ha)), (wrap_id w y (proj1 Hb)) in Heval.
      destruct (interval_is_point q 1) eqn:Hpoint.
      + pose proof (interval_is_point_sound rw q 1 z Hq Hpoint) as Hz.
        inversion Heval; subst rw z. destruct (Z.ltb x y) eqn:Hlt; [|discriminate].
        apply Z.ltb_lt in Hlt. now apply Sound.interval_assume_ult_sound.
      + destruct (interval_is_point q 0) eqn:Hpoint0; [|split; assumption].
        pose proof (interval_is_point_sound rw q 0 z Hq Hpoint0) as Hz.
        inversion Heval; subst rw z. destruct (Z.ltb x y) eqn:Hlt; [discriminate|].
        apply Z.ltb_ge in Hlt.
        destruct (Sound.interval_assume_ule_sound w w b a y x Hb Ha Hlt) as [Hfirst Hsecond].
        split; assumption.
    - unfold interval_assume_pair.
      rewrite (eval_op_cmp bvule w x y CUle eq_refl) in Heval.
      cbn [eval_comparison_tag] in Heval. rewrite Fun.wule_value in Heval.
      rewrite (wrap_id w x (proj1 Ha)), (wrap_id w y (proj1 Hb)) in Heval.
      destruct (interval_is_point q 1) eqn:Hpoint.
      + pose proof (interval_is_point_sound rw q 1 z Hq Hpoint) as Hz.
        inversion Heval; subst rw z. destruct (Z.leb x y) eqn:Hle; [|discriminate].
        apply Z.leb_le in Hle. now apply Sound.interval_assume_ule_sound.
      + destruct (interval_is_point q 0) eqn:Hpoint0; [|split; assumption].
        pose proof (interval_is_point_sound rw q 0 z Hq Hpoint0) as Hz.
        inversion Heval; subst rw z. destruct (Z.leb x y) eqn:Hle; [discriminate|].
        apply Z.leb_gt in Hle.
        destruct (Sound.interval_assume_ult_sound w w b a y x Hb Ha Hle) as [Hfirst Hsecond].
        split; assumption.
    - unfold interval_assume_pair.
      rewrite (eval_op_cmp bvslt w x y CSlt eq_refl) in Heval.
      cbn [eval_comparison_tag] in Heval. rewrite Fun.wslt_value in Heval.
      destruct (interval_is_point q 1) eqn:Hpoint.
      + pose proof (interval_is_point_sound rw q 1 z Hq Hpoint) as Hz.
        inversion Heval; subst rw z. destruct (Z.ltb (signed w x) (signed w y)) eqn:Hlt;
          [|discriminate]. now apply Sound.interval_assume_signed_sound.
      + destruct (interval_is_point q 0) eqn:Hpoint0; [|split; assumption].
        pose proof (interval_is_point_sound rw q 0 z Hq Hpoint0) as Hz.
        inversion Heval; subst rw z. destruct (Z.ltb (signed w x) (signed w y)) eqn:Hlt;
          [discriminate|]. now apply Sound.interval_assume_signed_sound.
    - unfold interval_assume_pair.
      rewrite (eval_op_cmp bvsle w x y CSle eq_refl) in Heval.
      cbn [eval_comparison_tag] in Heval. rewrite Fun.wsle_value in Heval.
      destruct (interval_is_point q 1) eqn:Hpoint.
      + pose proof (interval_is_point_sound rw q 1 z Hq Hpoint) as Hz.
        inversion Heval; subst rw z. destruct (Z.leb (signed w x) (signed w y)) eqn:Hle;
          [|discriminate]. now apply Sound.interval_assume_signed_sound.
      + destruct (interval_is_point q 0) eqn:Hpoint0; [|split; assumption].
        pose proof (interval_is_point_sound rw q 0 z Hq Hpoint0) as Hz.
        inversion Heval; subst rw z. destruct (Z.leb (signed w x) (signed w y)) eqn:Hle;
          [discriminate|]. now apply Sound.interval_assume_signed_sound.
  Qed.
End WrappedIntervalRefineSound.

(** The scalar refinement result also satisfies the endpoint-based interval meaning. *)
Local Lemma wrapped_interval_assume_pair_sound o wa wb a b q x y rw z :
  interval_pgamma wa a x -> interval_pgamma wb b y -> interval_pgamma rw q z ->
  eval_op o [(wa, x); (wb, y)] = Some (rw, z) ->
  interval_pgamma wa (fst (WrappedIntervalBack.interval_assume_pair o wa a b q)) x /\
  interval_pgamma wb (snd (WrappedIntervalBack.interval_assume_pair o wa a b q)) y.
Proof.
  intros Ha Hb Hq Heval.
  pose proof (WrappedIntervalRefineSound.interval_assume_pair_sound o wa wb a b q x y rw z
    (proj2 (WrappedIntervalSound.interval_pgamma_spec wa a x) Ha)
    (proj2 (WrappedIntervalSound.interval_pgamma_spec wb b y) Hb)
    (proj2 (WrappedIntervalSound.interval_pgamma_spec rw q z) Hq) Heval) as [Hleft Hright].
  split; now apply WrappedIntervalSound.interval_pgamma_spec.
Qed.

(** Rewrapping refinement retains operands whose projected value satisfies the result. *)
Local Lemma wrapped_interval_assume_rewrap_sound rw w a q x :
  interval_pgamma w a x -> interval_pgamma rw q (wrap rw x) ->
  interval_pgamma w (WrappedIntervalBack.interval_assume_rewrap rw a q) x.
Proof.
  intros Ha Hq. apply WrappedIntervalSound.interval_pgamma_spec.
  apply (WrappedIntervalSound.interval_assume_rewrap_sound rw w a q x);
    now apply WrappedIntervalSound.interval_pgamma_spec.
Qed.

Module WrappedTransferClaims (L : WORD_LANGUAGE_OPS).
  Module P := WrappedCode L.
  Module O := WrappedOpsCode L P.
Theorem wrapped_assume_consistent_sound o wa wb a b q x y rw z :
  interval_pgamma wa a x -> interval_pgamma wb b y -> interval_pgamma rw q z ->
  eval_op o [(wa, x); (wb, y)] = Some (rw, z) ->
  O.assume_consistent o wa wb a b q = true.
Proof.
  intros Ha Hb Hq Heval.
  assert (Hinputs : Forall2 wrapped_interval_payload_sound
      [(wa, a); (wb, b)] [(wa, x); (wb, y)]).
  { constructor; [split; [reflexivity|exact Ha]|].
    constructor; [split; [reflexivity|exact Hb]|constructor]. }
  pose proof (wrapped_interval_forward_sound o _ _ rw z Hinputs Heval) as Hforward.
  pose proof (wrapped_interval_meet_sound rw _ _ z Hforward Hq) as Hmeet.
  pose proof (eval_op_width _ _ _ Heval) as Hwidth.
  change (result_width o [wa; wb] = Some rw) in Hwidth.
  unfold O.assume_consistent. rewrite Hwidth.
  change (match WrappedScalar.interval_meet
    (match WrappedIntervalTable.wfwd o rw [(wa, a); (wb, b)] with
     | Some r => r | None => WrappedIntervalBack.interval_top rw end) q with
    | IBot => false | I _ _ => true end = true).
  destruct (WrappedScalar.interval_meet
    (match WrappedIntervalTable.wfwd o rw [(wa, a); (wb, b)] with
     | Some r => r | None => WrappedIntervalBack.interval_top rw end) q).
  - exact (False_rect _ (proj2 Hmeet)).
  - reflexivity.
Qed.


(** A consistent nonempty piece retains both satisfying operands. *)
Local Lemma wrapped_assume_piece_raw_sound o wa wb a b q x y rw z :
  interval_pgamma wa a x -> interval_pgamma wb b y -> interval_pgamma rw q z ->
  eval_op o [(wa, x); (wb, y)] = Some (rw, z) ->
  wrapped_pair_gamma wa wb (O.assume_piece_raw o wa wb a b q) x y.
Proof.
  intros Ha Hb Hq Heval.
  destruct (wrapped_interval_assume_pair_sound o wa wb a b q x y rw z Ha Hb Hq Heval)
    as [Hleft Hright].
  pose proof (wrapped_assume_consistent_sound o wa wb a b q x y rw z Ha Hb Hq Heval) as Hcheck.
  destruct a as [|la ha]; [exact (False_rect _ (proj2 Ha))|].
  destruct b as [|lb hb]; [exact (False_rect _ (proj2 Hb))|].
  destruct q as [|lq hq]; [exact (False_rect _ (proj2 Hq))|].
  unfold O.assume_piece_raw. rewrite Hcheck.
  split; now apply wrapped_interval_value_sound.
Qed.

(** The four pole combinations cover every satisfying operand pair. *)
Local Lemma wrapped_assume_piece_sound o wa wb a b q x y rw z :
  interval_pgamma wa a x -> interval_pgamma wb b y -> interval_pgamma rw q z ->
  eval_op o [(wa, x); (wb, y)] = Some (rw, z) ->
  wrapped_pair_gamma wa wb (O.assume_piece o wa wb a b q) x y.
Proof.
  intros Ha Hb Hq Heval.
  apply wrapped_pole_cut_sound in Ha. apply wrapped_pole_cut_sound in Hb.
  unfold O.assume_piece. apply wrapped_pair_join_sound.
  destruct Ha as [Ha|Ha]; destruct Hb as [Hb|Hb].
  - left. apply wrapped_pair_join_sound. left.
    eapply wrapped_assume_piece_raw_sound; eassumption.
  - left. apply wrapped_pair_join_sound. right.
    eapply wrapped_assume_piece_raw_sound; eassumption.
  - right. apply wrapped_pair_join_sound. left.
    eapply wrapped_assume_piece_raw_sound; eassumption.
  - right. apply wrapped_pair_join_sound. right.
    eapply wrapped_assume_piece_raw_sound; eassumption.
Qed.

(** Splitting the result fact retains every concrete satisfying result. *)
Local Lemma wrapped_assume_result_sound o wa wb a b rw q x y z :
  interval_pgamma wa a x -> interval_pgamma wb b y -> wrapped_gamma rw q z ->
  eval_op o [(wa, x); (wb, y)] = Some (rw, z) ->
  wrapped_pair_gamma wa wb (O.assume_result o wa wb a b rw q) x y.
Proof.
  intros Ha Hb Hq Heval. apply wrapped_parts_spec in Hq.
  unfold O.assume_result. apply wrapped_pair_join_sound.
  destruct Hq as [Hq|Hq].
  - left. eapply wrapped_assume_piece_sound; eassumption.
  - right. eapply wrapped_assume_piece_sound; eassumption.
Qed.

Theorem wrapped_assume_binary_base_sound o wa wb a b rw q x y z :
  wrapped_gamma wa a x -> wrapped_gamma wb b y -> wrapped_gamma rw q z ->
  eval_op o [(wa, x); (wb, y)] = Some (rw, z) ->
  wrapped_pair_gamma wa wb (O.assume_binary_base o wa wb a b rw q) x y.
Proof.
  intros Ha Hb Hq Heval.
  pose proof (proj1 (wrapped_parts_spec wa a x) Ha) as Hpa.
  pose proof (proj1 (wrapped_parts_spec wb b y) Hb) as Hpb.
  unfold O.assume_binary_base.
  match goal with |- wrapped_pair_gamma _ _
    (wrapped_meet _ _ (fst ?candidates), _) _ _ =>
    assert (Hcandidates : wrapped_pair_gamma wa wb candidates x y)
  end.
  { apply wrapped_pair_join_sound. destruct Hpa as [Hpa|Hpa]; destruct Hpb as [Hpb|Hpb].
    - left. apply wrapped_pair_join_sound. left.
      eapply wrapped_assume_result_sound; eassumption.
    - left. apply wrapped_pair_join_sound. right.
      eapply wrapped_assume_result_sound; eassumption.
    - right. apply wrapped_pair_join_sound. left.
      eapply wrapped_assume_result_sound; eassumption.
    - right. apply wrapped_pair_join_sound. right.
      eapply wrapped_assume_result_sound; eassumption. }
  destruct Hcandidates as [Hleft Hright]. split; now apply wrapped_meet_sound.
Qed.

Theorem wrapped_assume_binary_base_lower o wa wb a b rw q :
  wrapped_leb wa (fst (O.assume_binary_base o wa wb a b rw q)) a = true /\
  wrapped_leb wb (snd (O.assume_binary_base o wa wb a b rw q)) b = true.
Proof.
  unfold O.assume_binary_base. split; apply wrapped_meet_lower_left.
Qed.

Theorem wrapped_assume_trunc_sound w a rw q x :
  wrapped_gamma w a x -> wrapped_gamma rw q (wrap rw x) ->
  wrapped_gamma w (O.assume_trunc w a rw q) x.
Proof.
  intros Ha Hq. unfold O.assume_trunc. apply wrapped_meet_sound; [exact Ha|].
  apply wrapped_parts_spec in Ha. apply wrapped_parts_spec in Hq.
  apply wrapped_join_four_sound.
  destruct Ha as [Ha|Ha]; destruct Hq as [Hq|Hq].
  - left. apply wrapped_interval_value_sound.
    now apply (wrapped_interval_assume_rewrap_sound rw).
  - right; left. apply wrapped_interval_value_sound.
    now apply (wrapped_interval_assume_rewrap_sound rw).
  - right; right; left. apply wrapped_interval_value_sound.
    now apply (wrapped_interval_assume_rewrap_sound rw).
  - right; right; right. apply wrapped_interval_value_sound.
    now apply (wrapped_interval_assume_rewrap_sound rw).
Qed.

Local Lemma wrapped_add_cancel w x y : wrap w (wrap w (x + y) - y) = wrap w x.
Proof.
  rewrite (wrap_sub w (wrap w (x + y)) y), wrap_wrap, <- wrap_sub.
  replace (x + y - y) with x by lia. reflexivity.
Qed.

Local Lemma wrapped_sub_cancel_left w x y : wrap w (wrap w (x - y) + y) = wrap w x.
Proof.
  rewrite (wrap_add w (wrap w (x - y)) y), wrap_wrap, <- wrap_add.
  replace (x - y + y) with x by lia. reflexivity.
Qed.

Local Lemma wrapped_sub_cancel_right w x y : wrap w (x - wrap w (x - y)) = wrap w y.
Proof.
  rewrite (wrap_sub w x (wrap w (x - y))), wrap_wrap, <- wrap_sub.
  replace (x - (x - y)) with y by lia. reflexivity.
Qed.

Local Lemma wrapped_assume_add_sound w a b q x y :
  wrapped_gamma w a x -> wrapped_gamma w b y -> wrapped_gamma w q (wadd w x y) ->
  wrapped_pair_gamma w w (O.assume_binary bvadd w w a b w q) x y.
Proof.
  intros Ha Hb Hq. split; apply wrapped_meet_sound; try assumption.
  - pose proof (wrapped_sub_sound w q b (wadd w x y) y Hq Hb) as Hleft.
    rewrite wadd_value, wrapped_add_cancel, (wrap_id w x (wrapped_gamma_word _ _ _ Ha))
      in Hleft. exact Hleft.
  - pose proof (wrapped_sub_sound w q a (wadd w x y) x Hq Ha) as Hright.
    rewrite wadd_value in Hright. replace (x + y) with (y + x) in Hright by lia.
    rewrite wrapped_add_cancel, (wrap_id w y (wrapped_gamma_word _ _ _ Hb)) in Hright.
    exact Hright.
Qed.

Local Lemma wrapped_assume_sub_sound w a b q x y :
  wrapped_gamma w a x -> wrapped_gamma w b y -> wrapped_gamma w q (wsub w x y) ->
  wrapped_pair_gamma w w (O.assume_binary bvsub w w a b w q) x y.
Proof.
  intros Ha Hb Hq. split; apply wrapped_meet_sound; try assumption.
  - pose proof (wrapped_add_sound w q b (wsub w x y) y Hq Hb) as Hleft.
    rewrite wsub_value, wrapped_sub_cancel_left, (wrap_id w x (wrapped_gamma_word _ _ _ Ha))
      in Hleft. exact Hleft.
  - pose proof (wrapped_sub_sound w a q x (wsub w x y) Ha Hq) as Hright.
    rewrite wsub_value, wrapped_sub_cancel_right, (wrap_id w y (wrapped_gamma_word _ _ _ Hb))
      in Hright. exact Hright.
Qed.

Theorem wrapped_assume_binary_sound o wa wb a b rw q x y z :
  wrapped_gamma wa a x -> wrapped_gamma wb b y -> wrapped_gamma rw q z ->
  eval_op o [(wa, x); (wb, y)] = Some (rw, z) ->
  wrapped_pair_gamma wa wb (O.assume_binary o wa wb a b rw q) x y.
Proof.
  intros Ha Hb Hq Heval.
  op_cases o by (eapply wrapped_assume_binary_base_sound; eassumption).
  - pose proof (eval_op_fun2_width bvadd BAdd wa wb x y (rw, z) eq_refl Heval) as ->.
    rewrite (eval_op_fun2 bvadd wb x y BAdd eq_refl) in Heval.
    cbn [eval_binary_tag] in Heval. inversion Heval; subst rw z.
    now apply wrapped_assume_add_sound.
  - pose proof (eval_op_fun2_width bvsub BSub wa wb x y (rw, z) eq_refl Heval) as ->.
    rewrite (eval_op_fun2 bvsub wb x y BSub eq_refl) in Heval.
    cbn [eval_binary_tag] in Heval. inversion Heval; subst rw z.
    now apply wrapped_assume_sub_sound.
Qed.

Theorem wrapped_assume_binary_lower o wa wb a b rw q :
  wrapped_leb wa (fst (O.assume_binary o wa wb a b rw q)) a = true /\
  wrapped_leb wb (snd (O.assume_binary o wa wb a b rw q)) b = true.
Proof.
  op_cases o by apply wrapped_assume_binary_base_lower;
    split; apply wrapped_meet_lower_left.
Qed.

Theorem wrapped_assume_unary_sound o w a rw q x z :
  wrapped_gamma w a x -> wrapped_gamma rw q z -> eval_op o [(w, x)] = Some (rw, z) ->
  wrapped_gamma w (O.assume_unary o w a rw q) x.
Proof.
  intros Ha Hq Heval. pose proof (wrapped_gamma_word w a x Ha) as Hword.
  op_cases o by exact (proj2 (wrapped_norm_gamma w a x) Ha).
  - rewrite eval_op_zext in Heval. inversion Heval; subst rw z.
    apply wrapped_meet_sound; [exact Ha|].
    pose proof (wrapped_project_sound w (w + extra)%positive q _ Hq) as Hproject.
    rewrite wrap_narrow, wrap_wrap, (wrap_id w x Hword) in Hproject.
    + exact Hproject.
    + apply width_add_le.
  - rewrite eval_op_sext in Heval. inversion Heval; subst rw z.
    apply wrapped_meet_sound; [exact Ha|].
    pose proof (wrapped_project_sound w (w + extra)%positive q _ Hq) as Hproject.
    rewrite wrap_narrow, wrap_signed, (wrap_id w x Hword) in Hproject.
    + exact Hproject.
    + apply width_add_le.
  - rewrite eval_op_trunc in Heval. destruct (Pos.leb target w); [|discriminate].
    rewrite (wrap_id w x Hword) in Heval. inversion Heval; subst rw z.
    now apply wrapped_assume_trunc_sound.
Qed.

Theorem wrapped_assume_unary_lower o w a rw q :
  wrapped_leb w (O.assume_unary o w a rw q) a = true.
Proof.
  op_cases o by exact (proj2 (wrapped_norm_leb w a)); apply wrapped_meet_lower_left.
Qed.

Theorem wrapped_piece_forward_sound o xs cs rw z :
  Forall2 wrapped_interval_payload_sound xs cs -> eval_op o cs = Some (rw, z) ->
  wrapped_gamma rw (O.piece_forward o xs rw) z.
Proof.
  intros Hinputs Heval. unfold O.piece_forward.
  rewrite (wrapped_interval_inputs_nonbottom xs cs Hinputs).
  pose proof (wrapped_interval_forward_sound o xs cs rw z Hinputs Heval) as Hforward.
  destruct (WrappedIntervalTable.wfwd o rw xs).
  - now apply wrapped_interval_value_sound.
  - exact (proj1 Hforward).
Qed.

Theorem wrapped_forward_unary_sound o w a x rw z :
  wrapped_gamma w a x -> eval_op o [(w, x)] = Some (rw, z) ->
  wrapped_gamma rw (O.forward_unary o w a rw) z.
Proof.
  intros Ha Heval. apply wrapped_parts_spec in Ha.
  unfold O.forward_unary. apply wrapped_join_sound. destruct Ha as [Ha|Ha].
  - left. eapply wrapped_piece_forward_sound; [|exact Heval].
    constructor; [split; [reflexivity|exact Ha]|constructor].
  - right. eapply wrapped_piece_forward_sound; [|exact Heval].
    constructor; [split; [reflexivity|exact Ha]|constructor].
Qed.


(** Signed division and remainder use their pole-piece magnitude calculation. *)
Local Lemma wrapped_piece_binary_sound o wa wb a b x y rw z :
  interval_pgamma wa a x -> interval_pgamma wb b y ->
  eval_op o [(wa, x); (wb, y)] = Some (rw, z) ->
  wrapped_gamma rw (O.piece_binary o wa wb a b rw) z.
Proof.
  intros Ha Hb Heval.
  assert (Hbase : wrapped_gamma rw (O.piece_forward o [(wa, a); (wb, b)] rw) z).
  { eapply wrapped_piece_forward_sound; [|exact Heval].
    constructor; [split; [reflexivity|exact Ha]|].
    constructor; [split; [reflexivity|exact Hb]|constructor]. }
  op_cases o by exact Hbase.
  - pose proof (eval_op_fun2_width bvsdiv BSdiv wa wb x y (rw, z) eq_refl Heval) as ->.
    rewrite (eval_op_fun2 bvsdiv wb x y BSdiv eq_refl) in Heval.
    cbn [eval_binary_tag] in Heval. inversion Heval; subst rw z.
    apply (wrapped_signed_piece_sound true); assumption.
  - pose proof (eval_op_fun2_width bvsrem BSrem wa wb x y (rw, z) eq_refl Heval) as ->.
    rewrite (eval_op_fun2 bvsrem wb x y BSrem eq_refl) in Heval.
    cbn [eval_binary_tag] in Heval. inversion Heval; subst rw z.
    apply (wrapped_signed_piece_sound false); assumption.
Qed.

(** Cutting both operands at their signed poles retains the concrete pair. *)
Local Lemma wrapped_piece_forward_cut_sound o wa wb a b x y rw z :
  interval_pgamma wa a x -> interval_pgamma wb b y ->
  eval_op o [(wa, x); (wb, y)] = Some (rw, z) ->
  wrapped_gamma rw (O.piece_cut o wa wb a b rw) z.
Proof.
  intros Ha Hb Heval.
  apply wrapped_pole_cut_sound in Ha. apply wrapped_pole_cut_sound in Hb.
  unfold O.piece_cut. apply wrapped_join_four_sound.
  destruct Ha as [Ha|Ha]; destruct Hb as [Hb|Hb].
  - left. eapply wrapped_piece_binary_sound; eassumption.
  - right; left. eapply wrapped_piece_binary_sound; eassumption.
  - right; right; left. eapply wrapped_piece_binary_sound; eassumption.
  - right; right; right. eapply wrapped_piece_binary_sound; eassumption.
Qed.

Theorem wrapped_forward_binary_sound o wa wb a b x y rw z :
  wrapped_gamma wa a x -> wrapped_gamma wb b y ->
  eval_op o [(wa, x); (wb, y)] = Some (rw, z) ->
  wrapped_gamma rw (O.forward_binary o wa wb a b rw) z.
Proof.
  intros Ha Hb Heval. apply wrapped_parts_spec in Ha. apply wrapped_parts_spec in Hb.
  unfold O.forward_binary. apply wrapped_join_four_sound.
  destruct Ha as [Ha|Ha]; destruct Hb as [Hb|Hb].
  - left. eapply wrapped_piece_forward_cut_sound; eassumption.
  - right; left. eapply wrapped_piece_forward_cut_sound; eassumption.
  - right; right; left. eapply wrapped_piece_forward_cut_sound; eassumption.
  - right; right; right. eapply wrapped_piece_forward_cut_sound; eassumption.
Qed.
End WrappedTransferClaims.

Definition wrapped_rewrap (target source : width) (q : wrapped) : wrapped :=
  wrapped_project target source q.
Theorem wrapped_rewrap_sound target source q z :
  wrapped_gamma source q z ->
  wrapped_gamma target (wrapped_rewrap target source q) (wrap target z).
Proof.
  apply wrapped_project_sound.
Qed.


(** Unsigned bounds retain precise endpoints for arcs that do not cross zero. *)
Definition wrapped_unsigned_range (w : width) (a : wrapped) : bnd * bnd :=
  match a with
  | WBot => (PosInf, NegInf)
  | WFull => (Fin 0, Fin (modulus w - 1))
  | WItv lo hi =>
    let lo' := arc_wrap w lo in
    let hi' := arc_wrap w hi in
    if lo' <=? hi' then (Fin lo', Fin hi') else (Fin 0, Fin (modulus w - 1))
  end.

(** Every represented word lies between its circular payload's unsigned bounds. *)
Lemma wrapped_unsigned_range_sound w a z : wrapped_gamma w a z ->
  in_bnd (fst (wrapped_unsigned_range w a)) (snd (wrapped_unsigned_range w a)) z.
Proof.
  destruct a as [| |lo hi]; intro Ha; [exact (False_rect _ Ha)| |].
  - change (0 <= z <= modulus w - 1). destruct Ha. lia.
  - cbn [wrapped_unsigned_range]. rewrite !arc_wrap_agrees.
    destruct (wrap w lo <=? wrap w hi) eqn:Hends.
    + change (wrap w lo <= z <= wrap w hi).
      destruct Ha as [Hz Hoffset].
      pose proof (wrap_is_word w lo) as Hlo. pose proof (wrap_is_word w hi) as Hhi.
      rewrite <- (wrapped_offset_origin w lo z), <- (wrapped_offset_wrap w lo hi) in Hoffset.
      rewrite !wrapped_offset_word_cases in Hoffset by assumption.
      rewrite Hends in Hoffset. apply Z.leb_le in Hends.
      destruct (wrap w lo <=? z) eqn:Hzlo;
        [apply Z.leb_le in Hzlo|apply Z.leb_gt in Hzlo];
        destruct Hlo, Hhi, Hz; lia.
    + change (0 <= z <= modulus w - 1). destruct Ha as [[Hzlo Hzhi] _]. lia.
Qed.

Module WrappedNumU <: NUM_VIEW BitsLang.
  Definition num (c : word) : Z := snd c.
End WrappedNumU.

Module WrappedRangeCode
    (D : VALUE_DOMAIN_OPS BitsLangCode with Definition t := tagged wrapped).
  Definition range (a : D.t) : bnd * bnd :=
    match a with
    | TBot => (PosInf, NegInf)
    | TVal w p => wrapped_unsigned_range w p
    | TAny => (NegInf, PosInf)
    end.
End WrappedRangeCode.

Module WrappedRange (L : WORD_LANGUAGE) (W : WRAPPED L)
    (D : VALUE_DOMAIN BitsLang with Definition t := tagged W.p
      with Definition gamma := tagged_gamma L.is_word W.pgamma)
    <: RANGE_QUERY BitsLang WrappedNumU D.
  Include WrappedRangeCode D.

  (** The unsigned query covers every concrete word represented by the tagged domain. *)
  Lemma range_sound : forall a c,
    D.gamma a c -> in_bnd (fst (range a)) (snd (range a)) (WrappedNumU.num c).
  Proof.
    intros [|w p|] [v z] Hgamma.
    - exact (False_rect _ Hgamma).
    - destruct Hgamma as [Hwidth [Hword Hp]]. apply W.gamma_arc in Hp.
      apply wrapped_unsigned_range_sound.
      destruct p as [| |lo hi]; cbn [W.arc_gamma wrapped_gamma] in *; try exact Hp.
      unfold W.offset in Hp. unfold wrapped_offset. rewrite !arc_wrap_agrees. exact Hp.
    - split; constructor.
  Qed.
End WrappedRange.

(* The landed transfer stack used closure-bearing shape/table/word records. The
   current WORD_TABLE interface takes the payload as a module and states its soundness
   directly. These exact source bundle claims have no corresponding old record type.
Theorem wrapped_shape_laws :
  transfer_sem wrapped_shape (payload_sound wrapped_gamma)
    (word_output wrapped_gamma) word_context.
Theorem wrapped_table_laws :
  table_laws wrapped_table wrapped_shape (payload_sound wrapped_gamma)
    (word_output wrapped_gamma) word_context.
Theorem wrapped_table_refines :
  table_refines wrapped_table wrapped_shape
    (fun wp p => wrapped_leb (fst wp) p (snd wp) = true).
Theorem wrapped_word_laws : word_laws wrapped_word_domain wrapped_gamma.
Theorem wrapped_numeric_laws :
  numeric_laws wrapped_domain (tagged_gamma wrapped_gamma).

   The following source equations and entry claim refer to removed Cost values and
   closure-valued table entries. Timing will derive clocks for the current operations.
Theorem wrapped_pair_union_value wa wb a b :
  Cost.value (wrapped_pair_union_c wa wb a b) =
  wrapped_pair_join wa wb (Cost.value a) (Cost.value b).
Theorem wrapped_union_four_value w a b c d :
  Cost.value (wrapped_union_four_c w a b c d) =
  wrapped_join_four w (Cost.value a) (Cost.value b) (Cost.value c) (Cost.value d).
Theorem wrapped_union_value w a b :
  Cost.value (wrapped_union_c w a b) = wrapped_join w (Cost.value a) (Cost.value b).
Theorem wrapped_fwd_entry_sound o n f rw xs cs z :
  wrapped_fwd_entry o n = Some f -> length xs = n ->
  Forall2 (payload_sound wrapped_gamma) xs cs -> eval_op o cs = Some (rw, z) ->
  wrapped_gamma rw (Cost.value (f rw xs)) z.
*)
