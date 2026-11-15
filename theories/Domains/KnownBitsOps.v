(** * Known-bit word operations

    These operations connect known-bit masks to word transfers.
    For example, evaluating a zero-preserving operator keeps known zero bits.
    Builds on: KnownBits and the bit-vector operations. *)

From Stdlib Require Import ZArith List Bool Lia.
From Argent Require Import Time Tactics Std.
From Galois.Bits Require Import Word Op Fun Arith.
From Galois.Domains Require Import ValueSig WordSig KnownBitsSig KnownBits BitsLang Tagged.
Import List.ListNotations.
Local Open Scope Z_scope.

Module KnownBitsOpsCode (L : WORD_LANGUAGE_OPS) (C : TNUM_CONFIG)
    (K : KNOWN_BITS_OPS L C).
  Definition tnum_forward_raw (o : op) (wps : list (width * tnum)) (rw : width) : tnum :=
    match o, wps with
    | bvnot, [(_, a)] => K.tnum_not rw a
    | bvneg, [(_, a)] => K.tnum_neg rw a
    | (bvclz | bvctz | bvpopcnt), [_] => tnum_count rw
    | bvadd, [(_, a); (_, b)] => K.tnum_add rw a b
    | bvsub, [(_, a); (_, b)] => K.tnum_sub rw a b
    | bvmul, [(w, a); (v, b)] =>
      if Pos.eqb w rw && Pos.eqb v rw then K.tnum_mul rw a b
      else tnum_mul rw a b
    | bvudiv, [(_, a); (_, b)] => tnum_udiv rw a b
    | bvurem, [(_, a); _] => tnum_urem rw a
    | bvsrem, [(_, a); _] => tnum_srem rw a
    | bvand, [(_, a); (_, b)] => K.tnum_and rw a b
    | bvor, [(_, a); (_, b)] => K.tnum_or rw a b
    | bvxor, [(_, a); (_, b)] => K.tnum_xor rw a b
    | (bvshl | bvlshr | bvashr | bvrotl | bvrotr), [(_, a); (_, b)] =>
      K.tnum_variable o rw a b
    | (bveq | bvne | bvult | bvule | bvslt | bvsle), [(w, a); (_, b)] =>
      tnum_compare o w a b
    | bvite, [(_, c); (_, a); (_, b)] => tnum_ite rw c a b
    | (bvzext _ | bvtrunc _), [(w, a)] => tnum_map w rw (tnum_wrap rw) a
    | bvsext _, [(w, a)] => tnum_map w rw (fun x => tnum_wrap rw (signed w x)) a
    | bvextract _ lo, [(w, a)] => tnum_map w rw (fun x => tnum_wrap rw (x / 2 ^ Z.of_nat lo)) a
    | bvconcat, [(w, a); (v, b)] => tnum_concat w v a b
    | _, _ => tnum_top
    end.
End KnownBitsOpsCode.

Module KnownBitsOpsClock (L : WORD_LANGUAGE_T) (C : TNUM_CONFIG) (K : KNOWN_BITS_T L C).
  Include KnownBitsOpsCode L C K.
  TimeFun tnum_forward_raw.
End KnownBitsOpsClock.

Definition tnum_payload_sound (wp : width * tnum) (y : word) : Prop :=
  fst wp = fst y /\ is_word (fst y) (snd y) /\ tnum_gamma (fst wp) (snd wp) (snd y).

(** Pointwise agreement suffices because a mask map reads only its two endpoints. *)
Lemma tnum_map_ext : forall sw rw f g a,
  (forall x, f x = g x) -> tnum_map sw rw f a = tnum_map sw rw g a.
Proof.
  intros sw rw f g a Hagree. unfold tnum_map. now rewrite !Hagree.
Qed.

Module ForwardClaims (L : WORD_LANGUAGE_OPS) (C : TNUM_CONFIG).
  Module P := KnownBitsCode L C.
  Module F := KnownBitsOpsCode L C P.
Lemma tnum_forward_mul_same : forall w a b,
  F.tnum_forward_raw bvmul [(w, a); (w, b)] w =
    tnum_mul_with (C.multiplier) w a b.
Proof.
  intros w a b. unfold F.tnum_forward_raw. now rewrite !Pos.eqb_refl.
Qed.
Lemma tnum_forward_one_sound : forall o w a x rw z,
  is_word w x -> tnum_gamma w a x -> eval_op o [(w, x)] = Some (rw, z) ->
  tnum_gamma rw (F.tnum_forward_raw o [(w, a)] rw) z.
Proof.
  intros o w a x rw z Hx Ha Heval. destruct o; try apply tnum_top_sound.
  - rewrite (eval_op_fun1 bvnot w x UNot eq_refl) in Heval.
    injection Heval as <- <-. now apply tnum_not_sound.
  - rewrite (eval_op_fun1 bvneg w x UNeg eq_refl) in Heval.
    injection Heval as <- <-. now apply tnum_neg_sound.
  - rewrite (eval_op_fun1 bvclz w x UClz eq_refl) in Heval.
    injection Heval as <- <-. exact (tnum_count_sound bvclz w UClz x ltac:(tauto) eq_refl).
  - rewrite (eval_op_fun1 bvctz w x UCtz eq_refl) in Heval.
    injection Heval as <- <-. exact (tnum_count_sound bvctz w UCtz x ltac:(tauto) eq_refl).
  - rewrite (eval_op_fun1 bvpopcnt w x UPopcnt eq_refl) in Heval.
    injection Heval as <- <-.
    exact (tnum_count_sound bvpopcnt w UPopcnt x ltac:(tauto) eq_refl).
  - rewrite eval_op_zext in Heval. injection Heval as <- <-.
    rewrite (wrap_id w x Hx).
    change (tnum_gamma (w + extra)%positive
      (tnum_map w (w + extra)%positive (tnum_wrap (w + extra)%positive) a)
      (wrap (w + extra)%positive x)).
    rewrite (tnum_map_ext _ _ _ (wrap (w + extra)%positive) a) by
      apply tnum_wrap_agrees.
    apply tnum_map_sound; try assumption. apply tnum_zext_copy, width_add_le.
  - rewrite eval_op_sext in Heval. injection Heval as <- <-.
    change (tnum_gamma (w + extra)%positive
      (tnum_map w (w + extra)%positive
        (fun v => tnum_wrap (w + extra)%positive (signed w v)) a)
      (wrap (w + extra)%positive (signed w x))).
    rewrite (tnum_map_ext _ _ _
      (fun v => wrap (w + extra)%positive (signed w v)) a) by
      (intro v; apply tnum_wrap_agrees).
    apply (tnum_map_sound w (w + extra)%positive
      (fun v => wrap (w + extra)%positive (signed w v)) a x); try assumption.
    apply tnum_sext_copy.
  - rewrite eval_op_trunc in Heval. destruct (Pos.leb target w) eqn:Hle;
      [|discriminate].
    injection Heval as <- <-. rewrite (wrap_id w x Hx).
    change (tnum_gamma target (tnum_map w target (tnum_wrap target) a) (wrap target x)).
    rewrite (tnum_map_ext _ _ _ (wrap target) a) by apply tnum_wrap_agrees.
    apply tnum_map_sound; try assumption. apply tnum_trunc_copy. now apply Pos.leb_le.
  - rewrite eval_op_extract in Heval.
    destruct (Nat.leb lo hi && Nat.ltb hi (Pos.to_nat w)) eqn:Hshape;
      [|discriminate].
    injection Heval as <- <-. rewrite (wrap_id w x Hx).
    apply andb_true_iff in Hshape as [Hlo Hhi].
    apply Nat.leb_le in Hlo. apply Nat.ltb_lt in Hhi.
    change (tnum_gamma (Pos.of_nat (S (hi - lo)))
      (tnum_map w (Pos.of_nat (S (hi - lo)))
        (fun v => tnum_wrap (Pos.of_nat (S (hi - lo))) (v / 2 ^ Z.of_nat lo)) a)
      (wrap (Pos.of_nat (S (hi - lo))) (x / 2 ^ Z.of_nat lo))).
    rewrite (tnum_map_ext _ _ _
      (fun v => wrap (Pos.of_nat (S (hi - lo))) (v / 2 ^ Z.of_nat lo)) a) by
      (intro v; apply tnum_wrap_agrees).
    apply (tnum_map_sound w (Pos.of_nat (S (hi - lo)))
      (fun v => wrap (Pos.of_nat (S (hi - lo))) (v / 2 ^ Z.of_nat lo)) a x);
      try assumption. apply tnum_extract_copy; [lia|].
    rewrite <- positive_nat_Z, Nat2Pos.id by lia.
    rewrite <- (positive_nat_Z w). lia.
Qed.

Lemma tnum_binary_transfer_sound : forall o w f a b x y,
  word_fun2 o = Some f -> is_word w x -> is_word w y ->
  tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (F.tnum_forward_raw o [(w, a); (w, b)] w) (eval_binary_tag f w x y).
Proof.
  intros o w f a b x y Hf Hx Hy Ha Hb.
  destruct o; try discriminate Hf; injection Hf as <-;
    first [now apply tnum_add_sound|now apply tnum_sub_sound|
      rewrite tnum_forward_mul_same; now apply tnum_mul_with_sound|
      now apply tnum_udiv_sound|now apply tnum_urem_sound|apply tnum_top_sound|
      now apply tnum_srem_sound|now apply tnum_and_sound|now apply tnum_or_sound|
      now apply tnum_xor_sound|
      eapply tnum_variable_sound; try eassumption; try reflexivity;
        unfold tnum_shift_op; tauto].
Qed.
Lemma tnum_forward_fun2_sound : forall o w v f a b x y rw z,
  word_fun2 o = Some f -> is_word w x -> is_word v y ->
  tnum_gamma w a x -> tnum_gamma v b y ->
  eval_op o [(w, x); (v, y)] = Some (rw, z) ->
  tnum_gamma rw (F.tnum_forward_raw o [(w, a); (v, b)] rw) z.
Proof.
  intros o w v f a b x y rw z Hf Hx Hy Ha Hb Heval.
  pose proof (eval_op_fun2_width o f w v x y (rw, z) Hf Heval) as ->.
  rewrite (eval_op_fun2 o v x y f Hf) in Heval.
  injection Heval as <- <-. now apply (tnum_binary_transfer_sound o v f).
Qed.
Lemma tnum_forward_cmp_sound : forall o w v f a b x y rw z,
  word_cmp o = Some f -> is_word w x -> is_word v y ->
  tnum_gamma w a x -> tnum_gamma v b y ->
  eval_op o [(w, x); (v, y)] = Some (rw, z) ->
  tnum_gamma rw (F.tnum_forward_raw o [(w, a); (v, b)] rw) z.
Proof.
  intros o w v f a b x y rw z Hf Hx Hy Ha Hb Heval.
  pose proof (eval_op_cmp_width o f w v x y (rw, z) Hf Heval) as ->.
  rewrite (eval_op_cmp o v x y f Hf) in Heval. injection Heval as <- <-.
  pose proof (tnum_compare_sound o v f a b x y Hf Hx Hy Ha Hb) as Hsound.
  destruct o; try discriminate Hf; exact Hsound.
Qed.
Lemma tnum_forward_two_sound : forall o w v a b x y rw z,
  is_word w x -> is_word v y -> tnum_gamma w a x -> tnum_gamma v b y ->
  eval_op o [(w, x); (v, y)] = Some (rw, z) ->
  tnum_gamma rw (F.tnum_forward_raw o [(w, a); (v, b)] rw) z.
Proof.
  intros o w v a b x y rw z Hx Hy Ha Hb Heval.
  destruct o; try apply tnum_top_sound;
    try (eapply tnum_forward_fun2_sound; try eassumption; reflexivity);
    try (eapply tnum_forward_cmp_sound; try eassumption; reflexivity).
  rewrite eval_op_concat in Heval. injection Heval as <- <-.
  rewrite (wrap_id w x Hx), (wrap_id v y Hy).
  apply tnum_gamma_wrap. now apply tnum_concat_sound.
Qed.
Lemma tnum_forward_three_sound : forall o w v u c a b k x y rw z,
  is_word w k -> is_word v x -> is_word u y ->
  tnum_gamma w c k -> tnum_gamma v a x -> tnum_gamma u b y ->
  eval_op o [(w, k); (v, x); (u, y)] = Some (rw, z) ->
  tnum_gamma rw (F.tnum_forward_raw o [(w, c); (v, a); (u, b)] rw) z.
Proof.
  intros o w v u c a b k x y rw z Hk Hx Hy Hc Ha Hb Heval.
  destruct o; try apply tnum_top_sound.
  destruct (eval_op_ite_width w v u k x y (rw, z) Heval) as [Hw Hvu]. subst w u.
  rewrite eval_op_ite in Heval. injection Heval as <- <-.
  rewrite (wrap_id 1%positive k Hk), (wrap_id v x Hx), (wrap_id v y Hy).
  now apply tnum_ite_sound.
Qed.
Theorem known_bits_nullary : forall o rw, F.tnum_forward_raw o [] rw = tnum_top.
Proof. destruct o; reflexivity. Qed.
End ForwardClaims.

Module KnownBitsForwardProof (L : WORD_LANGUAGE_OPS) (C : TNUM_CONFIG).
  Module P := KnownBitsCode L C.
  Module F := KnownBitsOpsCode L C P.
  Module Claims := ForwardClaims L C.

  (** Every supplied forward entry preserves successful concrete evaluation. *)
  Theorem tnum_forward_raw_sound : forall o wps ys rw z,
    Forall2 tnum_payload_sound wps ys -> eval_op o ys = Some (rw, z) ->
    tnum_gamma rw (F.tnum_forward_raw o wps rw) z.
  Proof.
    intros o wps ys rw z Hgamma Heval.
    destruct wps as [|[w a] [|[v b] [|[u c] [|wp rest]]]].
    - destruct o; apply tnum_top_sound.
    - inversion Hgamma as [|wp y wps' tail Hhead Htail]; subst. inversion Htail; subst.
      destruct y as [wy x]. destruct Hhead as [Hwx [Hx Ha]]. cbn in Hwx, Hx, Ha. subst wy.
      exact (Claims.tnum_forward_one_sound o w a x rw z Hx Ha Heval).
    - inversion Hgamma as [|wp y wps' tail Hhead Htail]; subst.
      inversion Htail as [|wp y' wps' tail' Hhead' Htail']; subst. inversion Htail'; subst.
      destruct y as [wy x], y' as [vy y].
      destruct Hhead as [Hwx [Hx Ha]], Hhead' as [Hvy [Hy Hb]].
      cbn in Hwx, Hvy, Hx, Hy, Ha, Hb. subst wy vy.
      exact (Claims.tnum_forward_two_sound o w v a b x y rw z Hx Hy Ha Hb Heval).
    - inversion Hgamma as [|wp y wps' tail Hhead Htail]; subst.
      inversion Htail as [|wp y' wps' tail' Hhead' Htail']; subst.
      inversion Htail' as [|wp y'' wps' tail'' Hhead'' Htail'']; subst.
      inversion Htail''; subst. destruct y as [wy x], y' as [vy y], y'' as [uy t].
      destruct Hhead as [Hwx [Hx Ha]], Hhead' as [Hvy [Hy Hb]], Hhead'' as [Hut [Ht Hc]].
      cbn in Hwx, Hvy, Hut, Hx, Hy, Ht, Ha, Hb, Hc. subst wy vy uy.
      exact (Claims.tnum_forward_three_sound o w v u a b c x y t rw z
        Hx Hy Ht Ha Hb Hc Heval).
    - destruct o; apply tnum_top_sound.
  Qed.
End KnownBitsForwardProof.
Theorem known_bits_eval_primitive_bound : forall o (xs : list word),
  Nat.eqb (length xs) (arity o) = true -> (length xs <= 3)%nat.
Proof.
  intros o xs Hlength. apply Nat.eqb_eq in Hlength. rewrite Hlength.
  destruct o; repeat constructor.
Qed.

(* The landed shape, table and word-law bundles used removed closure-bearing records.
   WORD_TABLE now states the corresponding operation-level contracts, which the supplied
   payload proof below derives from the arithmetic and gamma laws of KNOWN_BITS.
Lemma known_bits_shape_laws :
  transfer_sem known_bits_shape (payload_sound tnum_gamma) (word_output tnum_gamma)
    word_context.
Theorem known_bits_table_laws : forall opts,
  table_laws (known_bits_table opts) known_bits_shape (payload_sound tnum_gamma)
    (word_output tnum_gamma) word_context.
Lemma known_bits_table_refines : forall opts,
  table_refines (known_bits_table opts) known_bits_shape
    (fun wp q => leb (tnum_lattice (fst wp)) q (snd wp) = true).
Theorem known_bits_word_builder_laws : forall opts,
  word_laws (known_bits_word_builder opts) tnum_gamma.
Theorem known_bits_word_laws : forall opts,
  word_laws (known_bits_word_domain opts) tnum_gamma.

   These source statements refer to removed charged wrappers. The corresponding
   uncharged evaluation is eval_op and the configured forward body is F.tnum_forward_raw.
Theorem known_bits_eval_equation : forall o xs,
  Cost.value (known_bits_eval_c o xs) = eval_op o xs.
Theorem known_bits_nonempty_delegation : forall opts o x xs rw,
  pforward_c (known_bits_word_domain opts) o (x :: xs) rw =
    pforward_c (known_bits_word_builder opts) o (x :: xs) rw.
Theorem known_bits_nonmultiplication_agrees : forall opts opts' o, o <> bvmul ->
  pforward_c (known_bits_word_domain opts) o =
    pforward_c (known_bits_word_domain opts') o.
*)

(** Supplied payload operations are used only through their public soundness laws. *)
Module KnownBitsSuppliedForwardProof (L : WORD_LANGUAGE) (C : TNUM_CONFIG)
    (K : KNOWN_BITS L C).
  Module F := KnownBitsOpsCode L C K.
  Module Base := ForwardClaims L C.

  Lemma tnum_forward_one_sound : forall o w a x rw z,
    is_word w x -> tnum_gamma w a x -> eval_op o [(w, x)] = Some (rw, z) ->
    tnum_gamma rw (F.tnum_forward_raw o [(w, a)] rw) z.
  Proof.
    intros o w a x rw z Hx Ha Heval.
    pose proof (Base.tnum_forward_one_sound o w a x rw z Hx Ha Heval) as Hbase.
    pose proof (proj2 (K.gamma_tnum w a x) Ha) as Hpayload.
    destruct o; try exact Hbase.
    - pose proof (eval_op_fun1 bvnot w x UNot eq_refl) as Hop.
      rewrite Hop in Heval. injection Heval as <- <-.
      apply (proj1 (K.gamma_tnum _ _ _)).
      eapply K.tnum_not_sound; eassumption.
    - pose proof (eval_op_fun1 bvneg w x UNeg eq_refl) as Hop.
      rewrite Hop in Heval. injection Heval as <- <-.
      apply (proj1 (K.gamma_tnum _ _ _)).
      eapply K.tnum_neg_sound; eassumption.
  Qed.

  Lemma tnum_binary_transfer_sound : forall o w f a b x y,
    word_fun2 o = Some f -> is_word w x -> is_word w y ->
    tnum_gamma w a x -> tnum_gamma w b y ->
    tnum_gamma w (F.tnum_forward_raw o [(w, a); (w, b)] w)
      (eval_binary_tag f w x y).
  Proof.
    intros o w f a b x y Hf Hx Hy Ha Hb.
    pose proof (Base.tnum_binary_transfer_sound o w f a b x y Hf Hx Hy Ha Hb) as Hbase.
    pose proof (proj2 (K.gamma_tnum w a x) Ha) as Hleft.
    pose proof (proj2 (K.gamma_tnum w b y) Hb) as Hright.
    pose proof (eval_op_fun2 o w x y f Hf) as Heval.
    destruct o; try discriminate Hf; try exact Hbase.
    all: cbn [F.tnum_forward_raw]; try rewrite !Pos.eqb_refl;
      cbn [andb]; try rewrite K.multiplier_selected;
      apply (proj1 (K.gamma_tnum _ _ _)).
    all: first [eapply (K.tnum_add_sound w a b x y); eassumption
      | eapply (K.tnum_sub_sound w a b x y); eassumption
      | eapply (K.tnum_and_sound w a b x y); eassumption
      | eapply (K.tnum_or_sound w a b x y); eassumption
      | eapply (K.tnum_xor_sound w a b x y); eassumption
      | eapply (K.tnum_mul_with_sound C.multiplier w a b x y); eassumption
      | eapply (K.tnum_variable_sound _ w a b x y); [cbn; tauto|eassumption|eassumption|
          eassumption|eassumption|eassumption]].
  Qed.

  Lemma tnum_forward_fun2_sound : forall o w v f a b x y rw z,
    word_fun2 o = Some f -> is_word w x -> is_word v y ->
    tnum_gamma w a x -> tnum_gamma v b y ->
    eval_op o [(w, x); (v, y)] = Some (rw, z) ->
    tnum_gamma rw (F.tnum_forward_raw o [(w, a); (v, b)] rw) z.
  Proof.
    intros o w v f a b x y rw z Hf Hx Hy Ha Hb Heval.
    pose proof (eval_op_fun2_width o f w v x y (rw, z) Hf Heval) as ->.
    rewrite (eval_op_fun2 o v x y f Hf) in Heval.
    injection Heval as <- <-. now apply (tnum_binary_transfer_sound o v f).
  Qed.

  Lemma tnum_forward_two_sound : forall o w v a b x y rw z,
    is_word w x -> is_word v y -> tnum_gamma w a x -> tnum_gamma v b y ->
    eval_op o [(w, x); (v, y)] = Some (rw, z) ->
    tnum_gamma rw (F.tnum_forward_raw o [(w, a); (v, b)] rw) z.
  Proof.
    intros o w v a b x y rw z Hx Hy Ha Hb Heval.
    pose proof (Base.tnum_forward_two_sound o w v a b x y rw z Hx Hy Ha Hb Heval)
      as Hbase.
    destruct o; try exact Hbase;
      eapply tnum_forward_fun2_sound; try eassumption; reflexivity.
  Qed.

  Lemma tnum_forward_three_sound : forall o w v u c a b k x y rw z,
    is_word w k -> is_word v x -> is_word u y ->
    tnum_gamma w c k -> tnum_gamma v a x -> tnum_gamma u b y ->
    eval_op o [(w, k); (v, x); (u, y)] = Some (rw, z) ->
    tnum_gamma rw (F.tnum_forward_raw o [(w, c); (v, a); (u, b)] rw) z.
  Proof.
    intros o w v u c a b k x y rw z Hk Hx Hy Hc Ha Hb Heval.
    pose proof (Base.tnum_forward_three_sound o w v u c a b k x y rw z
      Hk Hx Hy Hc Ha Hb Heval) as Hbase.
    destruct o; exact Hbase.
  Qed.

  (** Successful evaluation is retained by any payload satisfying KNOWN_BITS. *)
  Theorem tnum_forward_raw_sound : forall o wps ys rw z,
    Forall2 tnum_payload_sound wps ys -> eval_op o ys = Some (rw, z) ->
    tnum_gamma rw (F.tnum_forward_raw o wps rw) z.
  Proof.
    intros o wps ys rw z Hgamma Heval.
    destruct wps as [|[w a] [|[v b] [|[u c] [|wp rest]]]].
    - destruct o; apply tnum_top_sound.
    - inversion Hgamma as [|wp y wps' tail Hhead Htail]; subst. inversion Htail; subst.
      destruct y as [wy x]. destruct Hhead as [Hwx [Hx Ha]]. cbn in Hwx, Hx, Ha. subst wy.
      exact (tnum_forward_one_sound o w a x rw z Hx Ha Heval).
    - inversion Hgamma as [|wp y wps' tail Hhead Htail]; subst.
      inversion Htail as [|wp y' wps' tail' Hhead' Htail']; subst. inversion Htail'; subst.
      destruct y as [wy x], y' as [vy y].
      destruct Hhead as [Hwx [Hx Ha]], Hhead' as [Hvy [Hy Hb]].
      cbn in Hwx, Hvy, Hx, Hy, Ha, Hb. subst wy vy.
      exact (tnum_forward_two_sound o w v a b x y rw z Hx Hy Ha Hb Heval).
    - inversion Hgamma as [|wp y wps' tail Hhead Htail]; subst.
      inversion Htail as [|wp y' wps' tail' Hhead' Htail']; subst.
      inversion Htail' as [|wp y'' wps' tail'' Hhead'' Htail'']; subst.
      inversion Htail''; subst. destruct y as [wy x], y' as [vy y], y'' as [uy t].
      destruct Hhead as [Hwx [Hx Ha]], Hhead' as [Hvy [Hy Hb]], Hhead'' as [Hut [Ht Hc]].
      cbn in Hwx, Hvy, Hut, Hx, Hy, Ht, Ha, Hb, Hc. subst wy vy uy.
      exact (tnum_forward_three_sound o w v u a b c x y t rw z
        Hx Hy Ht Ha Hb Hc Heval).
    - destruct o; apply tnum_top_sound.
  Qed.
End KnownBitsSuppliedForwardProof.

