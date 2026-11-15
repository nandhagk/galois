(** * Circular word interval operations

    Transfers refine and evaluate circular intervals through linear pieces.
    For example, a binary operation checks each piece at the signed pole.
    Builds on: Wrapped, IntervalBack and WordSig. *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From Argent Require Import Time Tactics Std.
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

Module WrappedTransferSound (L : WORD_LANGUAGE_OPS) (P : WRAPPED_OPS L).
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
End WrappedTransferSound.

Module WrappedTransferClaims (L : WORD_LANGUAGE_OPS).
  Module P := WrappedCode L.
  Include WrappedTransferSound L P.
End WrappedTransferClaims.

Definition wrapped_rewrap (target source : width) (q : wrapped) : wrapped :=
  wrapped_project target source q.
Theorem wrapped_rewrap_sound target source q z :
  wrapped_gamma source q z ->
  wrapped_gamma target (wrapped_rewrap target source q) (wrap target z).
Proof.
  apply wrapped_project_sound.
Qed.


Module WrappedTable (L : WORD_LANGUAGE) (W : WRAPPED L) <: WRAPPED_TABLE L W.
  Include WrappedTableCode L W.
  Module Claims := WrappedTransferSound L W.

  (** The public payload semantics agrees with the checked circular helpers. *)
  Local Lemma gamma_wrapped w a z : W.pgamma w a z <-> wrapped_gamma w a z.
  Proof.
    rewrite W.gamma_arc. destruct a as [| |lo hi];
      cbn [W.arc_gamma wrapped_gamma]; try reflexivity.
    unfold W.offset, wrapped_offset. rewrite !arc_wrap_agrees. reflexivity.
  Qed.

  (** Unfolding only local wrappers exposes the common circular transfer helpers. *)
  Local Lemma forward_unary_same o w a rw :
    forward_unary o w a rw = Claims.O.forward_unary o w a rw.
  Proof.
    cbv beta iota zeta delta [forward_unary Ops.forward_unary Claims.O.forward_unary
      piece_forward Ops.piece_forward Claims.O.piece_forward]. reflexivity.
  Qed.

  (** Both binary code instances call the same pole-cut helper implementations. *)
  Local Lemma forward_binary_same o wa wb a b rw :
    forward_binary o wa wb a b rw = Claims.O.forward_binary o wa wb a b rw.
  Proof.
    cbv beta iota zeta delta [forward_binary Ops.forward_binary Claims.O.forward_binary
      piece_cut Ops.piece_cut Claims.O.piece_cut
      piece_binary Ops.piece_binary Claims.O.piece_binary
      piece_forward Ops.piece_forward Claims.O.piece_forward]. reflexivity.
  Qed.

  (** A unary entry uses the supplied negation law and the checked piece transfers. *)
  Local Lemma forward_one_sound o w a x rw z r :
    wfwd o rw [(w, a)] = Some r -> is_word w x -> W.pgamma w a x ->
    eval_op o [(w, x)] = Some (rw, z) -> W.pgamma rw r z.
  Proof.
    intros Hentry Hword Ha Heval.
    change (Some (match o with
      | bvneg => W.wrapped_neg rw a
      | bvzext _ | bvtrunc _ => wrapped_project rw w a
      | _ => forward_unary o w a rw
      end) = Some r) in Hentry.
    injection Hentry as <-.
    assert (Hbase : W.pgamma rw (forward_unary o w a rw) z).
    { rewrite (forward_unary_same o w a rw). apply (proj2 (gamma_wrapped _ _ _)).
      exact (Claims.wrapped_forward_unary_sound o w a x rw z
        (proj1 (gamma_wrapped w a x) Ha) Heval). }
    destruct o.
    all: lazymatch type of Heval with
    | eval_op bvneg _ = _ => idtac
    | eval_op (bvzext _) _ = _ => idtac
    | eval_op (bvtrunc _) _ = _ => idtac
    | _ => exact Hbase
    end.
    all: clear Hbase.
    - pose proof (eval_op_fun1 bvneg w x UNeg eq_refl) as Hop.
      rewrite Hop in Heval. injection Heval as <- <-.
      exact (W.wrapped_neg_sound w a x (eval_unary_tag UNeg w x) Hword Ha Hop).
    - rewrite eval_op_zext, (wrap_id w x Hword) in Heval. injection Heval as <- <-.
      apply (proj2 (gamma_wrapped _ _ _)).
      exact (wrapped_project_sound (w + extra)%positive w a x
        (proj1 (gamma_wrapped w a x) Ha)).
    - rewrite eval_op_trunc in Heval. destruct (Pos.leb target w); [|discriminate].
      rewrite (wrap_id w x Hword) in Heval. injection Heval as <- <-.
      apply (proj2 (gamma_wrapped _ _ _)).
      exact (wrapped_project_sound target w a x (proj1 (gamma_wrapped w a x) Ha)).
  Qed.

  (** Binary arithmetic uses supplied laws while other operators use the checked pole cuts. *)
  Local Lemma forward_two_sound o wa wb a b x y rw z r :
    wfwd o rw [(wa, a); (wb, b)] = Some r ->
    is_word wa x -> is_word wb y -> W.pgamma wa a x -> W.pgamma wb b y ->
    eval_op o [(wa, x); (wb, y)] = Some (rw, z) -> W.pgamma rw r z.
  Proof.
    intros Hentry Hx Hy Ha Hb Heval.
    change (Some (match o with
      | bvadd => W.wrapped_add rw a b
      | bvsub => W.wrapped_sub rw a b
      | bvmul => W.wrapped_mul rw a b
      | _ => forward_binary o wa wb a b rw
      end) = Some r) in Hentry.
    injection Hentry as <-.
    assert (Hbase : W.pgamma rw (forward_binary o wa wb a b rw) z).
    { rewrite (forward_binary_same o wa wb a b rw). apply (proj2 (gamma_wrapped _ _ _)).
      exact (Claims.wrapped_forward_binary_sound o wa wb a b x y rw z
        (proj1 (gamma_wrapped wa a x) Ha) (proj1 (gamma_wrapped wb b y) Hb) Heval). }
    destruct o.
    all: lazymatch type of Heval with
    | eval_op bvadd _ = _ => idtac
    | eval_op bvsub _ = _ => idtac
    | eval_op bvmul _ = _ => idtac
    | _ => exact Hbase
    end.
    all: clear Hbase.
    - pose proof (eval_op_fun2_width bvadd BAdd wa wb x y (rw, z) eq_refl Heval) as ->.
      pose proof (eval_op_fun2 bvadd wb x y BAdd eq_refl) as Hop.
      rewrite Hop in Heval. injection Heval as <- <-.
      exact (W.wrapped_add_sound wb a b x y (eval_binary_tag BAdd wb x y) Hx Hy Ha Hb Hop).
    - pose proof (eval_op_fun2_width bvsub BSub wa wb x y (rw, z) eq_refl Heval) as ->.
      pose proof (eval_op_fun2 bvsub wb x y BSub eq_refl) as Hop.
      rewrite Hop in Heval. injection Heval as <- <-.
      exact (W.wrapped_sub_sound wb a b x y (eval_binary_tag BSub wb x y) Hx Hy Ha Hb Hop).
    - pose proof (eval_op_fun2_width bvmul BMul wa wb x y (rw, z) eq_refl Heval) as ->.
      pose proof (eval_op_fun2 bvmul wb x y BMul eq_refl) as Hop.
      rewrite Hop in Heval. injection Heval as <- <-.
      exact (W.wrapped_mul_sound wb a b x y (eval_binary_tag BMul wb x y) Hx Hy Ha Hb Hop).
  Qed.

  (** Selection joins the two arms after concrete evaluation verifies their widths. *)
  Local Lemma forward_three_sound o wc wa wb c a b k x y rw z r :
    wfwd o rw [(wc, c); (wa, a); (wb, b)] = Some r ->
    is_word wa x -> is_word wb y -> W.pgamma wa a x -> W.pgamma wb b y ->
    eval_op o [(wc, k); (wa, x); (wb, y)] = Some (rw, z) -> W.pgamma rw r z.
  Proof.
    intros Hentry Hx Hy Ha Hb Heval.
    change (match o with bvite => Some (W.pjoin rw a b) | _ => None end = Some r) in Hentry.
    destruct o; try discriminate Hentry. injection Hentry as <-.
    destruct (eval_op_ite_width wc wa wb k x y (rw, z) Heval) as [Hcondition Harms].
    subst wc wb. rewrite eval_op_ite in Heval.
    rewrite (wrap_id wa x Hx), (wrap_id wa y Hy) in Heval.
    destruct (wrap 1%positive k =? 1); injection Heval as <- <-.
    - exact (W.pgamma_mono wa a (W.pjoin wa a b) x (W.pjoin_ub_l wa a b) Ha).
    - exact (W.pgamma_mono wa b (W.pjoin wa a b) y (W.pjoin_ub_r wa a b) Hb).
  Qed.

  Lemma wfwd_sound : forall o rw wps cs z r, wfwd o rw wps = Some r ->
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      W.pgamma (fst wp) (snd wp) (snd c)) wps cs ->
    L.eval_op o cs = Some (rw, z) -> W.pgamma rw r z.
  Proof.
    intros o rw wps cs z r Hentry Hinputs Heval.
    change (eval_op o cs = Some (rw, z)) in Heval.
    destruct wps as [|[w1 a1] [|[w2 a2] [|[w3 a3] [|extra rest]]]];
      try discriminate Hentry.
    - inversion Hinputs as [|wp [v1 x1] tail values [Hwidth [Hword Ha]] Htail]; subst.
      inversion Htail; subst. change (w1 = v1) in Hwidth. subst v1.
      exact (forward_one_sound o w1 a1 x1 rw z r Hentry Hword Ha Heval).
    - inversion Hinputs as [|wp [v1 x1] tail values [Hwidth1 [Hword1 Ha]] Htail]; subst.
      inversion Htail as [|wp [v2 x2] tail' values' [Hwidth2 [Hword2 Hb]] Hlast]; subst.
      inversion Hlast; subst.
      change (w1 = v1) in Hwidth1. change (w2 = v2) in Hwidth2. subst v1 v2.
      exact (forward_two_sound o w1 w2 a1 a2 x1 x2 rw z r
        Hentry Hword1 Hword2 Ha Hb Heval).
    - inversion Hinputs as [|wp [v1 x1] tail values [Hwidth1 [Hword1 Hc]] Htail]; subst.
      inversion Htail as [|wp [v2 x2] tail' values' [Hwidth2 [Hword2 Ha]] Hlast]; subst.
      inversion Hlast as [|wp [v3 x3] tail'' values'' [Hwidth3 [Hword3 Hb]] Hnil]; subst.
      inversion Hnil; subst.
      change (w1 = v1) in Hwidth1. change (w2 = v2) in Hwidth2.
      change (w3 = v3) in Hwidth3. subst v1 v2 v3.
      exact (forward_three_sound o w1 w2 w3 a1 a2 a3 x1 x2 x3 rw z r
        Hentry Hword2 Hword3 Ha Hb Heval).
  Qed.
  Lemma wbwd_sound : forall o rw q wps ys cs z, wbwd o rw q wps = Some ys ->
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      W.pgamma (fst wp) (snd wp) (snd c)) wps cs ->
    L.eval_op o cs = Some (rw, z) -> W.pgamma rw q z ->
    Forall2 (fun wp c => W.pgamma (fst wp) (snd wp) (snd c))
      (combine (map fst wps) ys) cs.
  Proof.
    intros o rw q wps ys cs z Hentry Hinputs Heval Hq.
    change (eval_op o cs = Some (rw, z)) in Heval.
    destruct wps as [|[w1 a1] [|[w2 a2] [|extra rest]]]; try discriminate Hentry.
    - change (Some [Claims.O.assume_unary o w1 a1 rw q] = Some ys) in Hentry.
      injection Hentry as <-.
      inversion Hinputs as [|wp [v1 x1] tail values [Hwidth [Hword Ha]] Htail]; subst.
      inversion Htail; subst. change (w1 = v1) in Hwidth. subst v1.
      constructor; [|constructor]. apply (proj2 (gamma_wrapped _ _ _)).
      exact (Claims.wrapped_assume_unary_sound o w1 a1 rw q x1 z
        (proj1 (gamma_wrapped w1 a1 x1) Ha) (proj1 (gamma_wrapped rw q z) Hq) Heval).
    - change (Some [fst (Claims.O.assume_binary o w1 w2 a1 a2 rw q);
        snd (Claims.O.assume_binary o w1 w2 a1 a2 rw q)] = Some ys) in Hentry.
      injection Hentry as <-.
      inversion Hinputs as [|wp [v1 x1] tail values [Hwidth1 [Hword1 Ha]] Htail]; subst.
      inversion Htail as [|wp [v2 x2] tail' values' [Hwidth2 [Hword2 Hb]] Hlast]; subst.
      inversion Hlast; subst.
      change (w1 = v1) in Hwidth1. change (w2 = v2) in Hwidth2. subst v1 v2.
      pose proof (Claims.wrapped_assume_binary_sound o w1 w2 a1 a2 rw q x1 x2 z
        (proj1 (gamma_wrapped w1 a1 x1) Ha) (proj1 (gamma_wrapped w2 a2 x2) Hb)
        (proj1 (gamma_wrapped rw q z) Hq) Heval) as [Hleft Hright].
      constructor.
      + apply (proj2 (gamma_wrapped _ _ _)). exact Hleft.
      + constructor; [|constructor]. apply (proj2 (gamma_wrapped _ _ _)). exact Hright.
  Qed.
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

(** Normalization stores at most two word-sized endpoints for table consumers. *)
Lemma wrapped_norm_bits_bound : forall w a,
  (wrapped_bits (wrapped_norm w a) <= 2 * Pos.to_nat w)%nat.
Proof.
  exact Galois.Domains.Wrapped.wrapped_norm_bits.
Qed.

(** A circular join normalizes its stored endpoints before a table reads them. *)
Lemma wrapped_join_bits_bound : forall w a b,
  (wrapped_bits (wrapped_join w a b) <= 2 * Pos.to_nat w)%nat.
Proof.
  exact Galois.Domains.Wrapped.wrapped_join_bits.
Qed.

(** Concrete circular negation normalizes both output endpoints. *)
Lemma wrapped_neg_bits_bound : forall w a,
  (wrapped_bits (wrapped_neg w a) <= 2 * Pos.to_nat w)%nat.
Proof.
  exact Galois.Domains.Wrapped.wrapped_neg_bits.
Qed.

(** Each signed-pole cut stores endpoints within its operand width. *)
Lemma wrapped_pole_cut_bits_bound : forall w a,
  (interval_bits (fst (wrapped_pole_cut w a)) <= Pos.to_nat w)%nat /\
  (interval_bits (snd (wrapped_pole_cut w a)) <= Pos.to_nat w)%nat.
Proof.
  intros w a. destruct (Galois.Domains.Wrapped.wrapped_pole_cut_word_shape w a) as [Hl Hr].
  split; apply wrapped_word_interval_bits; assumption.
Qed.

(** The concrete interval table supplies the same genuine clocks used by wrapped pieces. *)
Module WrappedIntervalPayloadBounds :=
  IntervalPayloadT WordLanguageT ThresholdsT WrappedScalar.
Module WrappedIntervalTableBounds :=
  IntervalWordTableT WordLanguageT ThresholdsT WrappedScalar WrappedIntervalPayloadBounds.

(** The separately generated forward clocks agree with the certified interval table. *)
Lemma wrapped_interval_forward_clock : forall o rw xs,
  WrappedIntervalTable.T_wfwd o rw xs = WrappedIntervalTableBounds.T_wfwd o rw xs.
Proof.
  reflexivity.
Qed.

(** Interval-pair refinement uses the certified table's backward primitive clock. *)
Lemma wrapped_interval_pair_clock : forall o w a b q,
  WrappedIntervalBack.T_interval_assume_pair o w a b q =
    WrappedIntervalTableBounds.T_interval_assume_pair o w a b q.
Proof.
  reflexivity.
Qed.

(** Circular projection finishes with a normalized join at the target width. *)
Lemma wrapped_project_bits : forall target source q,
  (wrapped_bits (wrapped_project target source q) <= 2 * Pos.to_nat target)%nat.
Proof.
  intros. unfold wrapped_project. apply wrapped_join_bits_bound.
Qed.

(** Interval payload storage adds only its endpoint bits and two width charges. *)
Lemma wrapped_interval_input_storage : forall xs : list (width * itv),
  (fold_right Nat.add 0%nat
    (map (fun x => WrappedIntervalPayloadBounds.psize (fst x) (snd x)) xs) <=
    2 * fold_right Nat.add 0%nat (map (fun x => Pos.to_nat (fst x)) xs) +
      fold_right Nat.add 0%nat (map (fun x => interval_bits (snd x)) xs))%nat.
Proof.
  induction xs as [|[w a] xs IH]; cbn [map fold_right fst snd].
  - lia.
  - change (Pos.to_nat w + interval_bits a + 1 +
      fold_right Nat.add 0%nat
        (map (fun x => WrappedIntervalPayloadBounds.psize (fst x) (snd x)) xs) <=
      2 * (Pos.to_nat w + fold_right Nat.add 0%nat
        (map (fun x => Pos.to_nat (fst x)) xs)) +
        (interval_bits a + fold_right Nat.add 0%nat
          (map (fun x => interval_bits (snd x)) xs)))%nat.
    pose proof (Pos2Nat.is_pos w). lia.
Qed.

(** The fixed interval implementation has a uniform quadratic forward clock. *)
Lemma wrapped_interval_forward_time : forall o rw xs,
  (WrappedIntervalTable.T_wfwd o rw xs <= 8796093022208 * N.of_nat
    ((Pos.to_nat rw + fold_right Nat.add 0%nat
      (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
      fold_right Nat.add 0%nat (map (fun x => interval_bits (snd x)) xs)))%N.
Proof.
  intros o rw xs.
  pose proof (WrappedIntervalTableBounds.T_wfwd_le o rw xs) as Htime.
  rewrite <- wrapped_interval_forward_clock in Htime.
  assert (Hcoefficient : WrappedIntervalTableBounds.c_word_table = 2132065000000%N)
    by reflexivity.
  rewrite Hcoefficient in Htime.
  pose proof (wrapped_interval_input_storage xs) as Hstorage.
  set (widths := fold_right Nat.add 0%nat
    (map (fun x : width * itv => Pos.to_nat (fst x)) xs)) in *.
  set (bits := fold_right Nat.add 0%nat
    (map (fun x : width * itv => interval_bits (snd x)) xs)) in *.
  set (inputs := fold_right Nat.add 0%nat
    (map (fun x : width * itv =>
      WrappedIntervalPayloadBounds.psize (fst x) (snd x)) xs)) in *.
  change (inputs <= 2 * widths + bits)%nat in Hstorage.
  change (WrappedIntervalTable.T_wfwd o rw xs <= 2132065000000 * N.of_nat
    ((Pos.to_nat rw + widths + 1) ^ 2 + inputs))%N in Htime.
  change (WrappedIntervalTable.T_wfwd o rw xs <= 8796093022208 * N.of_nat
    ((Pos.to_nat rw + widths + 1) ^ 2 + bits))%N.
  clearbody widths bits inputs.
  assert (Hbudget : ((Pos.to_nat rw + widths + 1) ^ 2 + inputs <=
    3 * ((Pos.to_nat rw + widths + 1) ^ 2 + bits))%nat).
  { clear -Hstorage. cbn [Nat.pow]. nia. }
  pose proof (time_of_nat_le _ _ Hbudget) as HbudgetN.
  rewrite Nat2N.inj_mul in HbudgetN.
  set (budget := N.of_nat ((Pos.to_nat rw + widths + 1) ^ 2 + bits)) in *.
  clearbody budget. clear Hbudget Hstorage. nia.
Qed.
TimeBound wrapped_interval_forward_time.

(** Forward interval results have linear endpoint storage in the requested widths. *)
Lemma wrapped_interval_forward_bits : forall o rw xs r,
  WrappedIntervalTable.wfwd o rw xs = Some r ->
  (interval_bits r <= 128 * (Pos.to_nat rw + fold_right Nat.add 0%nat
    (map (fun x => Pos.to_nat (fst x)) xs) + 1))%nat.
Proof.
  exact WrappedIntervalTableBounds.table_wfwd_linear_bits.
Qed.

(** Sign inspection has the certified primitive interval clock. *)
Lemma wrapped_interval_sign_time : forall w a,
  (WrappedIntervalBack.T_interval_sign w a <=
    300 * N.of_nat ((Pos.to_nat w + interval_bits a + 1) ^ 2))%N.
Proof.
  exact WrappedIntervalTableBounds.table_sign_time.
Qed.
TimeBound wrapped_interval_sign_time.

(** Negating an interval has the certified primitive interval clock. *)
Lemma wrapped_interval_neg_time : forall w a,
  (WrappedIntervalBack.T_interval_neg w a <=
    1000 * N.of_nat ((Pos.to_nat w + interval_bits a + 1) ^ 2))%N.
Proof.
  exact WrappedIntervalTableBounds.table_neg_time.
Qed.
TimeBound wrapped_interval_neg_time.

(** Primitive quotient approximation charges endpoint arithmetic quadratically. *)
Lemma wrapped_interval_udiv_time : forall w a b,
  (WrappedIntervalBack.T_interval_udiv w a b <= 2000 * N.of_nat
    ((Pos.to_nat w + interval_bits a + interval_bits b + 1) ^ 2))%N.
Proof.
  exact WrappedIntervalTableBounds.table_udiv_time.
Qed.
TimeBound wrapped_interval_udiv_time.

(** Primitive remainder approximation charges endpoint arithmetic quadratically. *)
Lemma wrapped_interval_urem_time : forall w a b,
  (WrappedIntervalBack.T_interval_urem w a b <= 2000 * N.of_nat
    ((Pos.to_nat w + interval_bits a + interval_bits b + 1) ^ 2))%N.
Proof.
  exact WrappedIntervalTableBounds.table_urem_time.
Qed.
TimeBound wrapped_interval_urem_time.

(** Pairwise circular joins normalize each coordinate at its own width. *)
Lemma wrapped_pair_join_bits : forall wa wb a b,
  (wrapped_bits (fst (wrapped_pair_join wa wb a b)) <= 2 * Pos.to_nat wa)%nat /\
  (wrapped_bits (snd (wrapped_pair_join wa wb a b)) <= 2 * Pos.to_nat wb)%nat.
Proof.
  intros. unfold wrapped_pair_join. cbn [fst snd]. split; apply wrapped_join_bits_bound.
Qed.


(** Projection splits a normalized source and joins two normalized target intervals. *)
Lemma wrapped_project_time : forall target source q,
  (T_wrapped_project target source q <= 1048576 * N.of_nat
    (Pos.to_nat target + Pos.to_nat source + wrapped_bits q + 1))%N.
Proof.
  intros target source q.
  pose proof (wrapped_parts_bits source q) as [Hl Hr].
  set (parts := wrapped_parts source q) in *.
  pose proof (wrapped_of_interval_bits target (fst parts)) as Hleft.
  pose proof (wrapped_of_interval_bits target (snd parts)) as Hright.
  set (left := wrapped_of_interval target (fst parts)) in *.
  set (right := wrapped_of_interval target (snd parts)) in *.
  time_unfold T_wrapped_project. cbn beta iota zeta.
  fold parts left right. clearbody parts left right.
  time_simpl. time_pose. rewrite ?Nat2N.inj_add in *. lia.
Qed.
TimeBound wrapped_project_time.

(** A coordinatewise join charges its two normalized circular joins. *)
Lemma wrapped_pair_join_time : forall wa wb a b,
  (T_wrapped_pair_join wa wb a b <= 262144 * N.of_nat
    (Pos.to_nat wa + Pos.to_nat wb + wrapped_bits (fst a) + wrapped_bits (snd a) +
      wrapped_bits (fst b) + wrapped_bits (snd b) + 1))%N.
Proof.
  intros wa wb a b. time_unfold T_wrapped_pair_join. cbn beta iota zeta.
  time_simpl. time_pose. rewrite ?Nat2N.inj_add in *. lia.
Qed.
TimeBound wrapped_pair_join_time.

(** Binary width checking never reads metadata belonging to unary operations. *)
Lemma wrapped_binary_result_width_bits : forall o wa wb rw,
  result_width o [wa; wb] = Some rw ->
  (Pos.to_nat rw <= Pos.to_nat wa + Pos.to_nat wb + 1)%nat.
Proof.
  intros o wa wb rw Hresult. destruct o; cbn [result_width] in Hresult;
    try discriminate Hresult;
    try (destruct (Pos.eqb wa wb); [injection Hresult as <-; cbn; lia|discriminate]).
  injection Hresult as <-. rewrite Pos2Nat.inj_add. lia.
Qed.

(** The binary width checker uses one positive comparison or addition. *)
Lemma wrapped_binary_result_width_time : forall o wa wb,
  (T_result_width o [wa; wb] <=
    128 * N.of_nat (Pos.to_nat wa + Pos.to_nat wb + 1))%N.
Proof.
  intros o wa wb.
  pose proof (WordTime.positive_size_value wa) as Ha.
  pose proof (WordTime.positive_size_value wb) as Hb.
  destruct o; time_unfold T_result_width; cbn beta iota zeta;
    time_simpl; time_pose;
    repeat match goal with
    | |- context [if ?test then _ else _] => destruct test
    end;
    cbn beta iota zeta; rewrite ?Nat2N.inj_add in *; lia.
Qed.

(** Pair refinement shares the certified concrete interval primitive clock. *)
Lemma wrapped_interval_refine_time : forall o w a b q,
  (WrappedIntervalBack.T_interval_assume_pair o w a b q <= 1073741824 * N.of_nat
    ((Pos.to_nat w + interval_bits a + interval_bits b + 1) ^ 2 + interval_bits q))%N.
Proof.
  intros o w a b q.
  pose proof (WrappedIntervalTableBounds.table_assume_pair_time o w a b q) as Htime.
  rewrite <- wrapped_interval_pair_clock in Htime.
  change (WrappedIntervalBack.T_interval_assume_pair o w a b q <=
    328010000 * N.of_nat
      ((Pos.to_nat w + interval_bits a + interval_bits b + 1) ^ 2 + interval_bits q))%N
    in Htime.
  lia.
Qed.
TimeBound wrapped_interval_refine_time.

(** Pair refinement adds only linear endpoint storage to both coordinates. *)
Lemma wrapped_interval_refine_bits : forall o w a b q,
  (interval_bits (fst (WrappedIntervalBack.interval_assume_pair o w a b q)) +
    interval_bits (snd (WrappedIntervalBack.interval_assume_pair o w a b q)) <=
    2 * (interval_bits a + interval_bits b + interval_bits q + 2))%nat.
Proof.
  exact WrappedIntervalTableBounds.table_assume_pair_bits.
Qed.

(** Truncation refinement uses the same generated clock as the interval table. *)
Lemma wrapped_interval_rewrap_clock : forall rw a q,
  WrappedIntervalBack.T_interval_assume_rewrap rw a q =
    WrappedIntervalTableBounds.T_interval_assume_rewrap rw a q.
Proof.
  reflexivity.
Qed.

(** Rewrapping keeps the requested result's raw endpoint cost linear. *)
Lemma wrapped_interval_rewrap_time : forall rw a q,
  (WrappedIntervalBack.T_interval_assume_rewrap rw a q <= 8388608 * N.of_nat
    ((Pos.to_nat rw + interval_bits a + 1) ^ 2 + interval_bits q))%N.
Proof.
  intros rw a q.
  pose proof (WrappedIntervalTableBounds.table_assume_rewrap_time rw a q) as Htime.
  rewrite <- wrapped_interval_rewrap_clock in Htime.
  change (WrappedIntervalBack.T_interval_assume_rewrap rw a q <=
    3280100 * N.of_nat ((Pos.to_nat rw + interval_bits a + 1) ^ 2 + interval_bits q))%N
    in Htime.
  lia.
Qed.
TimeBound wrapped_interval_rewrap_time.

(** Rewrapping retains its input or intersects it with the requested result. *)
Lemma wrapped_interval_rewrap_bits : forall rw a q,
  (interval_bits (WrappedIntervalBack.interval_assume_rewrap rw a q) <=
    interval_bits a + interval_bits q)%nat.
Proof.
  intros rw a q. unfold WrappedIntervalBack.interval_assume_rewrap.
  destruct (interval_finite_helper a) as [[lo hi]|]; [|lia].
  destruct ((0 <=? lo) && (hi <? modulus rw))%bool; [|lia].
  apply WrappedScalar.interval_meet_bits.
Qed.

(** The backward fallback uses the already bounded full unsigned interval. *)
Lemma wrapped_backward_top_time : forall w,
  (WrappedIntervalBack.T_interval_top w <= 64 * N.of_nat (Pos.to_nat w + 1))%N.
Proof.
  exact wrapped_interval_top_time.
Qed.
TimeBound wrapped_backward_top_time.

(** The backward full interval has one word-sized finite endpoint. *)
Lemma wrapped_backward_top_bits : forall w,
  (interval_bits (WrappedIntervalBack.interval_top w) <= Pos.to_nat w)%nat.
Proof.
  exact wrapped_interval_top_bits.
Qed.

(** Clipping at the pole bounds each result independently of raw endpoint size. *)
Lemma wrapped_backward_pole_bits : forall w a,
  (interval_bits (fst (wrapped_pole_cut w a)) <= Pos.to_nat w)%nat /\
  (interval_bits (snd (wrapped_pole_cut w a)) <= Pos.to_nat w)%nat.
Proof.
  exact wrapped_pole_cut_bits_bound.
Qed.

(** Addition finishes in a normalized arc or a constant extreme. *)
Lemma wrapped_backward_add_bits : forall w a b,
  (wrapped_bits (wrapped_add w a b) <= 2 * Pos.to_nat w)%nat.
Proof.
  intros w [| |la ha] [| |lb hb];
    try (change (0 <= 2 * Pos.to_nat w)%nat; lia).
  unfold wrapped_add. destruct (modulus w <?
    wrapped_size w (WItv la ha) + wrapped_size w (WItv lb hb));
    [change (0 <= 2 * Pos.to_nat w)%nat; lia|apply wrapped_norm_bits_bound].
Qed.

(** Subtraction inherits the normalized result of circular addition. *)
Lemma wrapped_backward_sub_bits : forall w a b,
  (wrapped_bits (wrapped_sub w a b) <= 2 * Pos.to_nat w)%nat.
Proof.
  intros. unfold wrapped_sub. apply wrapped_backward_add_bits.
Qed.

(** A fixed width expansion scales a square without involving clock expressions. *)
Lemma wrapped_backward_square_scale : forall a b k,
  (a <= k * b)%nat -> (a ^ 2 <= k * k * b ^ 2)%nat.
Proof.
  intros a b k Hle. rewrite !Nat.pow_2_r.
  eapply Nat.le_trans; [apply Nat.mul_le_mono; exact Hle|].
  clear Hle a. nia.
Qed.

(** Linear width work is contained in a positive width-square budget. *)
Lemma wrapped_backward_square_floor : forall n,
  (1 <= n)%nat -> (n <= n ^ 2)%nat.
Proof.
  intros n Hpositive. rewrite Nat.pow_2_r.
  replace n with (n * 1)%nat at 1 by lia. now apply Nat.mul_le_mono_l.
Qed.

(** Rewrapping two width-bounded pieces uses only their declared width square. *)
Lemma wrapped_interval_rewrap_time_word : forall w rw a q,
  (interval_bits a <= Pos.to_nat w)%nat ->
  (interval_bits q <= Pos.to_nat rw)%nat ->
  (WrappedIntervalBack.T_interval_assume_rewrap rw a q <= 16777216 * N.of_nat
    ((Pos.to_nat w + Pos.to_nat rw + 1) ^ 2))%N.
Proof.
  intros w rw a q Ha Hq.
  pose proof (wrapped_interval_rewrap_time rw a q) as Htime.
  assert (Hsquare : ((Pos.to_nat rw + interval_bits a + 1) ^ 2 <=
    (Pos.to_nat w + Pos.to_nat rw + 1) ^ 2)%nat)
    by (apply Nat.pow_le_mono_l; lia).
  pose proof (wrapped_backward_square_floor (Pos.to_nat w + Pos.to_nat rw + 1)
    ltac:(lia)) as Hfloor.
  assert (Hbudget : ((Pos.to_nat rw + interval_bits a + 1) ^ 2 + interval_bits q <=
    2 * (Pos.to_nat w + Pos.to_nat rw + 1) ^ 2)%nat) by lia.
  pose proof (time_of_nat_le _ _ Hbudget) as HbudgetN.
  rewrite Nat2N.inj_mul in HbudgetN. lia.
Qed.

Module WrappedTableStorageProof (L : WORD_LANGUAGE_T) (W : WRAPPED_T L).
  Module O := WrappedOpsCode L W.

  (** Every one-operand path ends in supplied negation or a normalized concrete join. *)
  Lemma forward_one_bits : forall o w rw a r,
    O.forward_raw o rw [(w, a)] = Some r ->
    (wrapped_bits r <= 2 * Pos.to_nat rw)%nat.
  Proof.
    intros o w rw a r Hresult.
    pose proof (W.wrapped_result_bits rw a a) as [_ [_ [_ Hneg]]].
    unfold O.forward_raw in Hresult. cbn beta iota zeta in Hresult.
    injection Hresult as <-. destruct o.
    all: lazymatch goal with
    | |- context [O.forward_unary _ _ _ _] =>
        unfold O.forward_unary; apply wrapped_join_bits_bound
    | |- context [wrapped_project _ _ _] => apply wrapped_project_bits
    | |- context [W.wrapped_neg _ _] => exact Hneg
    end.
  Qed.

  (** Every two-operand path ends in supplied arithmetic or a normalized four-piece join. *)
  Lemma forward_two_bits : forall o wa wb rw a b r,
    O.forward_raw o rw [(wa, a); (wb, b)] = Some r ->
    (wrapped_bits r <= 2 * Pos.to_nat rw)%nat.
  Proof.
    intros o wa wb rw a b r Hresult.
    pose proof (W.wrapped_result_bits rw a b) as [Hadd [Hsub [Hmul _]]].
    unfold O.forward_raw in Hresult. cbn beta iota zeta in Hresult.
    injection Hresult as <-. destruct o.
    all: lazymatch goal with
    | |- context [O.forward_binary _ _ _ _ _ _] =>
        unfold O.forward_binary; apply wrapped_join_four_bits
    | |- context [W.wrapped_add _ _ _] => exact Hadd
    | |- context [W.wrapped_sub _ _ _] => exact Hsub
    | |- context [W.wrapped_mul _ _ _] => exact Hmul
    end.
  Qed.

  (** Unary backward transfer normalizes or intersects the original operand. *)
  Lemma assume_unary_bits : forall o w a rw q,
    (wrapped_bits (O.assume_unary o w a rw q) <= 2 * Pos.to_nat w)%nat.
  Proof.
    intros o w a rw q. destruct o; cbn [O.assume_unary].
    all: lazymatch goal with
    | |- context [O.assume_trunc _ _ _ _] =>
        unfold O.assume_trunc; apply wrapped_meet_bits
    | |- context [wrapped_norm _ _] => apply wrapped_norm_bits_bound
    | |- context [wrapped_meet _ _ _] => apply wrapped_meet_bits
    end.
  Qed.

  (** Both backward binary results are normalized intersections at their operand widths. *)
  Lemma assume_binary_bits : forall o wa wb a b rw q,
    (wrapped_bits (fst (O.assume_binary o wa wb a b rw q)) <= 2 * Pos.to_nat wa)%nat /\
    (wrapped_bits (snd (O.assume_binary o wa wb a b rw q)) <= 2 * Pos.to_nat wb)%nat.
  Proof.
    intros o wa wb a b rw q. destruct o;
      cbn [O.assume_binary O.assume_binary_base fst snd];
      split; apply wrapped_meet_bits.
  Qed.
  (** Normalized result storage fits a fixed part of the common width-square budget. *)
  Lemma bounded_result_storage : forall rw (xs : list (width * wrapped)) r,
    (wrapped_bits r <= 2 * Pos.to_nat rw)%nat ->
    (N.of_nat (W.psize rw r) <= 4 * N.of_nat
      ((Pos.to_nat rw + fold_right Nat.add 0%nat
        (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        fold_right Nat.add 0%nat (map (fun x => W.psize (fst x) (snd x)) xs)))%N.
  Proof.
    intros rw xs r Hbits. rewrite W.psize_bits.
    rewrite <- (Nat2N.inj_mul 4). apply time_of_nat_le.
    set (widths := fold_right Nat.add 0%nat
      (map (fun x : width * wrapped => Pos.to_nat (fst x)) xs)).
    set (inputs := fold_right Nat.add 0%nat
      (map (fun x : width * wrapped => W.psize (fst x) (snd x)) xs)).
    clearbody widths inputs. cbn [Nat.pow]. nia.
  Qed.

  (** Supplied selection uses its payload size law; other forward results are normalized. *)
  Lemma forward_storage : forall o rw xs r, O.forward_raw o rw xs = Some r ->
    (N.of_nat (W.psize rw r) <= (4 * W.c_payload + 4) * N.of_nat
      ((Pos.to_nat rw + fold_right Nat.add 0%nat
        (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 +
        fold_right Nat.add 0%nat (map (fun x => W.psize (fst x) (snd x)) xs)))%N.
  Proof.
    intros o rw xs r Hresult.
    destruct xs as [|[wa a] [|[wb b] [|[wc c] [|extra xs]]]];
      try discriminate Hresult.
    - pose proof (bounded_result_storage rw [(wa, a)] r
        (forward_one_bits o wa rw a r Hresult)) as Hsize. nia.
    - pose proof (bounded_result_storage rw [(wa, a); (wb, b)] r
        (forward_two_bits o wa wb rw a b r Hresult)) as Hsize. nia.
    - change (match o with bvite => Some (W.pjoin rw b c) | _ => None end = Some r)
        in Hresult.
      destruct o; try discriminate Hresult. injection Hresult as <-.
      pose proof (W.pjoin_size rw b c) as Hjoin.
      set (budget := ((Pos.to_nat rw + Pos.to_nat wa + Pos.to_nat wb +
        Pos.to_nat wc + 1) ^ 2 + W.psize wa a + W.psize wb b + W.psize wc c)%nat).
      assert (Hinput : (W.psize rw b + W.psize rw c + 1 <= 4 * budget)%nat).
      { unfold budget. rewrite !W.psize_bits. cbn [Nat.pow]. nia. }
      pose proof (time_of_nat_le _ _ Hinput) as Hbudget.
      rewrite Nat2N.inj_mul in Hbudget.
      cbn [map fold_right fst snd]. rewrite !Nat.add_0_r, !Nat.add_assoc.
      fold budget. clearbody budget. nia.
  Qed.

  (** Backward outputs have one normalized payload for each retained operand. *)
  Lemma backward_storage : forall o rw q xs ys, O.backward_raw o rw q xs = Some ys ->
    (N.of_nat (length ys + fold_right Nat.add 0%nat
      (map (fun wy => W.psize (fst wy) (snd wy)) (combine (map fst xs) ys))) <=
      4 * N.of_nat
        ((Pos.to_nat rw + fold_right Nat.add 0%nat
          (map (fun x => Pos.to_nat (fst x)) xs) + 1) ^ 2 + W.psize rw q +
          fold_right Nat.add 0%nat (map (fun x => W.psize (fst x) (snd x)) xs)))%N.
  Proof.
    intros o rw q xs ys Hresult.
    destruct xs as [|[wa a] [|[wb b] [|extra xs]]]; try discriminate Hresult.
    - injection Hresult as <-.
      pose proof (assume_unary_bits o wa a rw q) as Hbits.
      cbn [length map fold_right combine fst snd]. rewrite !Nat.add_0_r.
      rewrite <- (Nat2N.inj_mul 4). apply time_of_nat_le.
      rewrite !W.psize_bits. cbn [Nat.pow]. nia.
    - injection Hresult as <-.
      pose proof (assume_binary_bits o wa wb a b rw q) as [Ha Hb].
      cbn [length map fold_right combine fst snd]. rewrite !Nat.add_0_r.
      rewrite <- (Nat2N.inj_mul 4). apply time_of_nat_le.
      rewrite !W.psize_bits. cbn [Nat.pow]. nia.
  Qed.
End WrappedTableStorageProof.

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
