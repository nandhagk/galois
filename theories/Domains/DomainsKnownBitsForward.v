(** * Known-bit forward entries

    Forward entries retain the legacy precision policy and select multiplication as data.
    For example, the default multiplier uses width-many staged partial products.
    Builds on: the known-bit arithmetic, expansion and comparison families. *)

From Stdlib Require Import ZArith List Bool Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Bits Require Import BitsWord BitsFun BitsOp BitsArith.
From Galois.Domains Require Import DomainsNumeric DomainsTnum DomainsTnumArith
  DomainsTnumShift DomainsTnumExpand DomainsTnumMul DomainsTnumCompare.
Import List.ListNotations.

Local Open Scope Z_scope.

(** Multiplication selection is executable data independent of its soundness laws. *)
Record known_bits_options : Type := KnownBitsOptions {
  known_bits_multiplier : tnum_mul_choice
}.

Definition known_bits_default_options : known_bits_options := KnownBitsOptions MulStages.

Definition tnum_forward_raw_c (opts : known_bits_options) (o : op)
    (wps : list (width * tnum)) (rw : width) : Cost.t tnum :=
  match o, wps with
  | bvnot, [(_, a)] => Cost.ret (tnum_not rw a)
  | bvneg, [(_, a)] => Cost.ret (tnum_neg rw a)
  | (bvclz | bvctz | bvpopcnt), [_] => Cost.ret (tnum_count rw)
  | bvadd, [(_, a); (_, b)] => Cost.ret (tnum_add rw a b)
  | bvsub, [(_, a); (_, b)] => Cost.ret (tnum_sub rw a b)
  | bvmul, [(w, a); (v, b)] =>
    if Pos.eqb w rw && Pos.eqb v rw then
      tnum_mul_with_c (known_bits_multiplier opts) rw a b
    else Cost.ret (tnum_mul rw a b)
  | bvudiv, [(_, a); (_, b)] => Cost.ret (tnum_udiv rw a b)
  | bvurem, [(_, a); _] => Cost.ret (tnum_urem rw a)
  | bvsrem, [(_, a); _] => Cost.ret (tnum_srem rw a)
  | bvand, [(_, a); (_, b)] => Cost.ret (tnum_and rw a b)
  | bvor, [(_, a); (_, b)] => Cost.ret (tnum_or rw a b)
  | bvxor, [(_, a); (_, b)] => Cost.ret (tnum_xor rw a b)
  | (bvshl | bvlshr | bvashr | bvrotl | bvrotr), [(_, a); (_, b)] =>
    tnum_variable_c o rw a b
  | (bveq | bvne | bvult | bvule | bvslt | bvsle), [(w, a); (_, b)] =>
    Cost.ret (tnum_compare o w a b)
  | bvite, [(_, c); (_, a); (_, b)] => Cost.ret (tnum_ite rw c a b)
  | (bvzext _ | bvtrunc _), [(w, a)] => Cost.ret (tnum_map w rw (wrap rw) a)
  | bvsext _, [(w, a)] => Cost.ret (tnum_map w rw (fun x => wrap rw (signed w x)) a)
  | bvextract _ lo, [(w, a)] =>
    Cost.ret (tnum_map w rw (fun x => wrap rw (x / 2 ^ Z.of_nat lo)) a)
  | bvconcat, [(w, a); (v, b)] => Cost.ret (tnum_concat w v a b)
  | _, _ => Cost.ret tnum_top
  end.

Definition tnum_forward_raw (opts : known_bits_options) (o : op)
    (wps : list (width * tnum)) (rw : width) : tnum :=
  Cost.value (tnum_forward_raw_c opts o wps rw).

Lemma tnum_forward_mul_same : forall opts w a b,
  tnum_forward_raw opts bvmul [(w, a); (w, b)] w =
    tnum_mul_with (known_bits_multiplier opts) w a b.
Proof.
  intros opts w a b. unfold tnum_forward_raw, tnum_forward_raw_c.
  rewrite !Pos.eqb_refl. reflexivity.
Qed.

Lemma tnum_forward_one_sound : forall opts o w a x rw z,
  is_word w x -> tnum_gamma w a x -> eval_op o [(w, x)] = Some (rw, z) ->
  tnum_gamma rw (tnum_forward_raw opts o [(w, a)] rw) z.
Proof.
  intros opts o w a x rw z Hx Ha Heval. destruct o; try apply tnum_top_sound.
  - rewrite (eval_op_fun1 bvnot w x wnot eq_refl) in Heval.
    injection Heval as <- <-. now apply tnum_not_sound.
  - rewrite (eval_op_fun1 bvneg w x wneg eq_refl) in Heval.
    injection Heval as <- <-. now apply tnum_neg_sound.
  - rewrite (eval_op_fun1 bvclz w x wclz eq_refl) in Heval.
    injection Heval as <- <-. exact (tnum_count_sound bvclz w wclz x ltac:(tauto) eq_refl).
  - rewrite (eval_op_fun1 bvctz w x wctz eq_refl) in Heval.
    injection Heval as <- <-. exact (tnum_count_sound bvctz w wctz x ltac:(tauto) eq_refl).
  - rewrite (eval_op_fun1 bvpopcnt w x wpopcnt eq_refl) in Heval.
    injection Heval as <- <-. exact (tnum_count_sound bvpopcnt w wpopcnt x ltac:(tauto) eq_refl).
  - rewrite eval_op_zext in Heval. injection Heval as <- <-.
    rewrite (wrap_id w x Hx). apply tnum_map_sound; try assumption.
    apply tnum_zext_copy, width_add_le.
  - rewrite eval_op_sext in Heval. injection Heval as <- <-.
    apply (tnum_map_sound w (w + extra)%positive
      (fun v => wrap (w + extra)%positive (signed w v)) a x); try assumption.
    apply tnum_sext_copy.
  - rewrite eval_op_trunc in Heval. destruct (Pos.leb target w) eqn:Hle; [|discriminate].
    injection Heval as <- <-. rewrite (wrap_id w x Hx).
    apply tnum_map_sound; try assumption. apply tnum_trunc_copy. now apply Pos.leb_le.
  - rewrite eval_op_extract in Heval.
    destruct (Nat.leb lo hi && Nat.ltb hi (Pos.to_nat w)) eqn:Hshape; [|discriminate].
    injection Heval as <- <-. rewrite (wrap_id w x Hx).
    apply andb_true_iff in Hshape as [Hlo Hhi].
    apply Nat.leb_le in Hlo. apply Nat.ltb_lt in Hhi.
    apply (tnum_map_sound w (Pos.of_nat (S (hi - lo)))
      (fun v => wrap (Pos.of_nat (S (hi - lo))) (v / 2 ^ Z.of_nat lo)) a x);
      try assumption. apply tnum_extract_copy; [lia|].
    rewrite <- positive_nat_Z, Nat2Pos.id by lia.
    rewrite <- (positive_nat_Z w). lia.
Qed.

Lemma tnum_binary_transfer_sound : forall opts o w f a b x y,
  word_fun2 o = Some f -> is_word w x -> is_word w y ->
  tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_forward_raw opts o [(w, a); (w, b)] w) (f w x y).
Proof.
  intros opts o w f a b x y Hf Hx Hy Ha Hb.
  destruct o; try discriminate Hf; injection Hf as <-;
    first [now apply tnum_add_sound|now apply tnum_sub_sound|
      rewrite tnum_forward_mul_same; now apply tnum_mul_with_sound|
      now apply tnum_udiv_sound|now apply tnum_urem_sound|apply tnum_top_sound|
      now apply tnum_srem_sound|now apply tnum_and_sound|now apply tnum_or_sound|
      now apply tnum_xor_sound|
      eapply tnum_variable_sound; try eassumption; try reflexivity;
        unfold tnum_shift_op; tauto].
Qed.

Lemma tnum_forward_fun2_sound : forall opts o w v f a b x y rw z,
  word_fun2 o = Some f -> is_word w x -> is_word v y ->
  tnum_gamma w a x -> tnum_gamma v b y ->
  eval_op o [(w, x); (v, y)] = Some (rw, z) ->
  tnum_gamma rw (tnum_forward_raw opts o [(w, a); (v, b)] rw) z.
Proof.
  intros opts o w v f a b x y rw z Hf Hx Hy Ha Hb Heval.
  pose proof (eval_op_fun2_width o f w v x y (rw, z) Hf Heval) as ->.
  rewrite (eval_op_fun2 o v x y f Hf) in Heval.
  injection Heval as <- <-. now apply (tnum_binary_transfer_sound opts o v f).
Qed.

Lemma tnum_forward_cmp_sound : forall opts o w v f a b x y rw z,
  word_cmp o = Some f -> is_word w x -> is_word v y ->
  tnum_gamma w a x -> tnum_gamma v b y ->
  eval_op o [(w, x); (v, y)] = Some (rw, z) ->
  tnum_gamma rw (tnum_forward_raw opts o [(w, a); (v, b)] rw) z.
Proof.
  intros opts o w v f a b x y rw z Hf Hx Hy Ha Hb Heval.
  pose proof (eval_op_cmp_width o f w v x y (rw, z) Hf Heval) as ->.
  rewrite (eval_op_cmp o v x y f Hf) in Heval. injection Heval as <- <-.
  pose proof (tnum_compare_sound o v f a b x y Hf Hx Hy Ha Hb) as Hsound.
  destruct o; try discriminate Hf; exact Hsound.
Qed.

Lemma tnum_forward_two_sound : forall opts o w v a b x y rw z,
  is_word w x -> is_word v y -> tnum_gamma w a x -> tnum_gamma v b y ->
  eval_op o [(w, x); (v, y)] = Some (rw, z) ->
  tnum_gamma rw (tnum_forward_raw opts o [(w, a); (v, b)] rw) z.
Proof.
  intros opts o w v a b x y rw z Hx Hy Ha Hb Heval.
  destruct o; try apply tnum_top_sound;
    try (eapply tnum_forward_fun2_sound; try eassumption; reflexivity);
    try (eapply tnum_forward_cmp_sound; try eassumption; reflexivity).
  rewrite eval_op_concat in Heval. injection Heval as <- <-.
  rewrite (wrap_id w x Hx), (wrap_id v y Hy).
  apply tnum_gamma_wrap. now apply tnum_concat_sound.
Qed.

Lemma tnum_forward_three_sound : forall opts o w v u c a b k x y rw z,
  is_word w k -> is_word v x -> is_word u y ->
  tnum_gamma w c k -> tnum_gamma v a x -> tnum_gamma u b y ->
  eval_op o [(w, k); (v, x); (u, y)] = Some (rw, z) ->
  tnum_gamma rw (tnum_forward_raw opts o [(w, c); (v, a); (u, b)] rw) z.
Proof.
  intros opts o w v u c a b k x y rw z Hk Hx Hy Hc Ha Hb Heval.
  destruct o; try apply tnum_top_sound.
  destruct (eval_op_ite_width w v u k x y (rw, z) Heval) as [Hw Hvu]. subst w u.
  rewrite eval_op_ite in Heval. injection Heval as <- <-.
  rewrite (wrap_id 1%positive k Hk), (wrap_id v x Hx), (wrap_id v y Hy).
  now apply tnum_ite_sound.
Qed.

(** Every supplied forward entry preserves the result of successful evaluation. *)
Theorem tnum_forward_raw_sound : forall opts o wps ys rw z,
  Forall2 (payload_sound tnum_gamma) wps ys -> eval_op o ys = Some (rw, z) ->
  tnum_gamma rw (tnum_forward_raw opts o wps rw) z.
Proof.
  intros opts o wps ys rw z Hgamma Heval.
  destruct wps as [|[w a] [|[v b] [|[u c] [|wp rest]]]].
  - destruct o; apply tnum_top_sound.
  - inversion Hgamma as [|wp y wps' tail Hhead Htail]; subst. inversion Htail; subst.
    destruct y as [wy x]. destruct Hhead as [Hwx [Hx Ha]]. cbn in Hwx, Hx, Ha. subst wy.
    exact (tnum_forward_one_sound opts o w a x rw z Hx Ha Heval).
  - inversion Hgamma as [|wp y wps' tail Hhead Htail]; subst.
    inversion Htail as [|wp y' wps' tail' Hhead' Htail']; subst. inversion Htail'; subst.
    destruct y as [wy x], y' as [vy y].
    destruct Hhead as [Hwx [Hx Ha]], Hhead' as [Hvy [Hy Hb]].
    cbn in Hwx, Hvy, Hx, Hy, Ha, Hb. subst wy vy.
    exact (tnum_forward_two_sound opts o w v a b x y rw z Hx Hy Ha Hb Heval).
  - inversion Hgamma as [|wp y wps' tail Hhead Htail]; subst.
    inversion Htail as [|wp y' wps' tail' Hhead' Htail']; subst.
    inversion Htail' as [|wp y'' wps' tail'' Hhead'' Htail'']; subst.
    inversion Htail''; subst. destruct y as [wy x], y' as [vy y], y'' as [uy t].
    destruct Hhead as [Hwx [Hx Ha]], Hhead' as [Hvy [Hy Hb]], Hhead'' as [Hut [Ht Hc]].
    cbn in Hwx, Hvy, Hut, Hx, Hy, Ht, Ha, Hb, Hc. subst wy vy uy.
    exact (tnum_forward_three_sound opts o w v u a b c x y t rw z Hx Hy Ht Ha Hb Hc Heval).
  - destruct o; apply tnum_top_sound.
Qed.
