(** * Local range forward dispatch

    Range transfers use the direct endpoint rules and the public Bits evaluation interface.
    For example, singleton unsigned division evaluates exactly.
    Builds on: DomainsSignedBoundsArith, Control, Shift, Mod and DomainsKnownBits. *)

From Stdlib Require Import ZArith List Bool Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Bits Require Import BitsWord BitsFun BitsOp BitsArith.
From Galois.Domains Require Import DomainsNumeric DomainsKnownBits DomainsSignedBounds
  DomainsSignedBoundsRange DomainsSignedBoundsArith DomainsSignedBoundsControl
  DomainsSignedBoundsShift DomainsSignedBoundsMod.
Import List.ListNotations Cost.Notations.

Local Open Scope Z_scope.

Definition sb_range_top (w : width) : list sb_range := [(0, modulus w - 1)].

Lemma sb_range_top_sound : forall w z, is_word w z -> sb_ranges_gamma w (sb_range_top w) z.
Proof.
  intros w z Hw. split; [exact Hw|]. exists (0, modulus w - 1). split; [now left|].
  unfold sb_range_gamma, is_word in *. cbn [fst snd]. lia.
Qed.

Definition sb_bool_not_range (a : sb_range) : sb_range := (1 - snd a, 1 - fst a).

Lemma sb_bool_not_range_sound : forall a (b : bool),
  sb_range_gamma a (if b then 1 else 0) ->
  sb_range_gamma (sb_bool_not_range a) (if negb b then 1 else 0).
Proof.
  intros [lo hi] b H. unfold sb_bool_not_range, sb_range_gamma in *.
  destruct b; cbn [fst snd negb] in *; lia.
Qed.

Definition sb_compare_ranges (o : op) (w : width) (a b : sb_range) : list sb_range :=
  [match o with
  | bveq => sb_equal_range a b
  | bvne => sb_bool_not_range (sb_equal_range a b)
  | bvult => sb_order_range true a b
  | bvule => sb_order_range false a b
  | bvslt => sb_order_range true (sb_signed_range w a) (sb_signed_range w b)
  | bvsle => sb_order_range false (sb_signed_range w a) (sb_signed_range w b)
  | _ => (0, 1)
  end].

Lemma sb_compare_ranges_sound : forall o w f a b x y,
  word_cmp o = Some f -> is_word w x -> is_word w y ->
  sb_range_gamma a x -> sb_range_gamma b y ->
  sb_ranges_gamma 1%positive (sb_compare_ranges o w a b)
    (if f w x y then 1 else 0).
Proof.
  intros o w f a b x y Hf Hx Hy Ha Hb.
  split; [destruct (f w x y); [apply one_is_word|apply zero_is_word]|].
  unfold sb_compare_ranges. eexists. split; [now left|].
  destruct o; try discriminate Hf; injection Hf as <-.
  - rewrite (wrap_id w x Hx), (wrap_id w y Hy). now apply sb_equal_range_sound.
  - rewrite (wrap_id w x Hx), (wrap_id w y Hy).
    apply sb_bool_not_range_sound. now apply sb_equal_range_sound.
  - rewrite wult_value, (wrap_id w x Hx), (wrap_id w y Hy).
    exact (sb_order_range_sound true a b x y Ha Hb).
  - rewrite wule_value, (wrap_id w x Hx), (wrap_id w y Hy).
    exact (sb_order_range_sound false a b x y Ha Hb).
  - rewrite wslt_value. apply (sb_order_range_sound true); now apply sb_signed_range_sound.
  - rewrite wsle_value. apply (sb_order_range_sound false); now apply sb_signed_range_sound.
Qed.

Definition sb_range_sext (rw w : width) (a : sb_range) : list sb_range :=
  match sb_range_sign w a with
  | Some _ =>
    let r := sb_signed_range w a in sb_mod_ranges rw (fst r) (snd r)
  | None => sb_range_top rw
  end.

Lemma sb_range_sext_sound : forall rw w a x,
  is_word w x -> sb_range_gamma a x ->
  sb_ranges_gamma rw (sb_range_sext rw w a) (wrap rw (signed w x)).
Proof.
  intros rw w a x Hx Ha. unfold sb_range_sext.
  destruct (sb_range_sign w a).
  - apply sb_mod_ranges_sound. exact (sb_signed_range_sound w a x Hx Ha).
  - apply sb_range_top_sound, wrap_is_word.
Qed.

Definition sb_range_forward_raw_c (o : op) (wps : list (width * sb_range)) (rw : width)
    : Cost.t (list sb_range) :=
  match o, wps with
  | bvnot, [(_, a)] => Cost.ret (sb_range_not rw a)
  | bvneg, [(_, a)] => Cost.ret (sb_range_neg rw a)
  | (bvclz | bvctz | bvpopcnt), [_] => Cost.ret (sb_range_count rw)
  | bvadd, [(_, a); (_, b)] => Cost.ret (sb_range_add rw a b)
  | bvsub, [(_, a); (_, b)] => Cost.ret (sb_range_sub rw a b)
  | bvmul, [(_, a); (_, b)] => Cost.ret (sb_range_mul rw a b)
  | bvudiv, [(_, a); (_, b)] => Cost.ret (sb_range_udiv rw a b)
  | bvurem, [(_, a); (_, b)] => Cost.ret (sb_range_urem rw a b)
  | bvsdiv, [(_, a); (_, b)] => sb_range_signed_divrem_c true rw a b
  | bvsrem, [(_, a); (_, b)] => sb_range_signed_divrem_c false rw a b
  | bvsmod, [(_, a); (_, b)] => Cost.ret (sb_range_smod rw a b)
  | bvand, [(_, a); (_, b)] => Cost.ret (sb_range_and rw a b)
  | (bvor | bvxor), [(_, a); (_, b)] => Cost.ret (sb_range_or_xor rw a b)
  | bvshl, [(_, a); (_, b)] => Cost.ret (sb_range_shl rw a b)
  | bvlshr, [(_, a); (_, b)] => Cost.ret (sb_range_lshr rw a b)
  | bvashr, [(_, a); (_, b)] => Cost.ret (sb_range_ashr rw a b)
  | (bveq | bvne | bvult | bvule | bvslt | bvsle), [(w, a); (_, b)] =>
    Cost.ret (sb_compare_ranges o w a b)
  | bvite, [_; (_, a); (_, b)] => Cost.ret (sb_range_cover rw a b)
  | (bvzext _ | bvtrunc _), [(_, a)] => Cost.ret (sb_mod_ranges rw (fst a) (snd a))
  | bvsext _, [(w, a)] => Cost.ret (sb_range_sext rw w a)
  | bvconcat, [(_, a); (w, b)] => Cost.ret (sb_range_concat rw w a b)
  | _, _ => Cost.ret (sb_range_top rw)
  end.

Definition sb_range_forward_raw (o : op) (wps : list (width * sb_range)) (rw : width)
    : list sb_range := Cost.value (sb_range_forward_raw_c o wps rw).

Lemma sb_range_forward_one_sound : forall o w a x rw z,
  is_word w x -> sb_range_gamma a x -> eval_op o [(w, x)] = Some (rw, z) ->
  sb_ranges_gamma rw (sb_range_forward_raw o [(w, a)] rw) z.
Proof.
  intros o w a x rw z Hx Ha Heval.
  pose proof (eval_op_is_word o [(w, x)] (rw, z) Heval) as Hresult.
  destruct o; try (now apply sb_range_top_sound).
  - rewrite (eval_op_fun1 bvnot w x wnot eq_refl) in Heval.
    injection Heval as <- <-. now apply sb_range_not_sound.
  - rewrite (eval_op_fun1 bvneg w x wneg eq_refl) in Heval.
    injection Heval as <- <-. now apply sb_range_neg_sound.
  - rewrite (eval_op_fun1 bvclz w x wclz eq_refl) in Heval.
    injection Heval as <- <-. exact (sb_range_count_sound bvclz w wclz x ltac:(tauto) eq_refl).
  - rewrite (eval_op_fun1 bvctz w x wctz eq_refl) in Heval.
    injection Heval as <- <-. exact (sb_range_count_sound bvctz w wctz x ltac:(tauto) eq_refl).
  - rewrite (eval_op_fun1 bvpopcnt w x wpopcnt eq_refl) in Heval.
    injection Heval as <- <-.
    exact (sb_range_count_sound bvpopcnt w wpopcnt x ltac:(tauto) eq_refl).
  - rewrite eval_op_zext in Heval. injection Heval as <- <-.
    rewrite (wrap_id w x Hx). now apply sb_mod_ranges_sound.
  - rewrite eval_op_sext in Heval. injection Heval as <- <-. now apply sb_range_sext_sound.
  - rewrite eval_op_trunc in Heval. destruct (Pos.leb target w); [|discriminate].
    injection Heval as <- <-. rewrite (wrap_id w x Hx). now apply sb_mod_ranges_sound.
Qed.

Lemma sb_range_forward_binary_sound : forall o w f a b x y,
  word_fun2 o = Some f -> is_word w x -> is_word w y ->
  sb_range_gamma a x -> sb_range_gamma b y ->
  sb_ranges_gamma w (sb_range_forward_raw o [(w, a); (w, b)] w) (f w x y).
Proof.
  intros o w f a b x y Hf Hx Hy Ha Hb.
  pose proof (word_fun2_is_word o f w x y Hf) as Hresult.
  destruct o; try discriminate Hf; injection Hf as <-;
    first [now apply sb_range_add_sound|now apply sb_range_sub_sound|
      now apply sb_range_mul_sound|now apply sb_range_udiv_sound|
      now apply sb_range_urem_sound|now apply (sb_range_signed_divrem_sound true)|
      now apply (sb_range_signed_divrem_sound false)|now apply sb_range_smod_sound|
      now apply sb_range_and_sound|
      exact (proj1 (sb_range_or_xor_sound w a b x y Hx Hy Ha Hb))|
      exact (proj2 (sb_range_or_xor_sound w a b x y Hx Hy Ha Hb))|
      now apply sb_range_shl_sound|now apply sb_range_lshr_sound|
      now apply sb_range_ashr_sound|now apply sb_range_top_sound].
Qed.

Lemma sb_range_forward_two_sound : forall o w v a b x y rw z,
  is_word w x -> is_word v y -> sb_range_gamma a x -> sb_range_gamma b y ->
  eval_op o [(w, x); (v, y)] = Some (rw, z) ->
  sb_ranges_gamma rw (sb_range_forward_raw o [(w, a); (v, b)] rw) z.
Proof.
  intros o w v a b x y rw z Hx Hy Ha Hb Heval.
  pose proof (eval_op_is_word o [(w, x); (v, y)] (rw, z) Heval) as Hresult.
  destruct (word_fun2 o) as [f|] eqn:Hf.
  - pose proof (eval_op_fun2_width o f w v x y (rw, z) Hf Heval) as ->.
    rewrite (eval_op_fun2 o v x y f Hf) in Heval. injection Heval as <- <-.
    now apply (sb_range_forward_binary_sound o v f).
  - destruct (word_cmp o) as [f|] eqn:Hcmp.
    + pose proof (eval_op_cmp_width o f w v x y (rw, z) Hcmp Heval) as ->.
      rewrite (eval_op_cmp o v x y f Hcmp) in Heval. injection Heval as <- <-.
      pose proof (sb_compare_ranges_sound o v f a b x y Hcmp Hx Hy Ha Hb) as Hsound.
      destruct o; try discriminate Hcmp; exact Hsound.
    + destruct o; try discriminate Hf; try discriminate Hcmp;
        try (now apply sb_range_top_sound).
      rewrite eval_op_concat in Heval. injection Heval as <- <-.
      rewrite (wrap_id w x Hx), (wrap_id v y Hy). now apply sb_range_concat_sound.
Qed.

Lemma sb_range_forward_three_sound : forall o w v u c a b k x y rw z,
  is_word w k -> is_word v x -> is_word u y ->
  sb_range_gamma c k -> sb_range_gamma a x -> sb_range_gamma b y ->
  eval_op o [(w, k); (v, x); (u, y)] = Some (rw, z) ->
  sb_ranges_gamma rw (sb_range_forward_raw o [(w, c); (v, a); (u, b)] rw) z.
Proof.
  intros o w v u c a b k x y rw z Hk Hx Hy Hc Ha Hb Heval.
  pose proof (eval_op_is_word o [(w, k); (v, x); (u, y)] (rw, z) Heval) as Hresult.
  destruct o; try (now apply sb_range_top_sound).
  destruct (eval_op_ite_width w v u k x y (rw, z) Heval) as [Hw Hvu]. subst w u.
  rewrite eval_op_ite in Heval. injection Heval as <- <-.
  rewrite (wrap_id 1%positive k Hk), (wrap_id v x Hx), (wrap_id v y Hy).
  apply sb_range_cover_sound; destruct (k =? 1); tauto.
Qed.

(** Each direct range rule describes the result of every successful normalized word evaluation. *)
Theorem sb_range_forward_raw_sound : forall o wps ys rw z,
  Forall2 (payload_sound sb_range_pgamma) wps ys -> eval_op o ys = Some (rw, z) ->
  sb_ranges_gamma rw (sb_range_forward_raw o wps rw) z.
Proof.
  intros o wps ys rw z Hgamma Heval.
  pose proof (eval_op_is_word o ys (rw, z) Heval) as Hresult.
  destruct wps as [|[w a] [|[v b] [|[u c] [|wp rest]]]].
  - destruct o; now apply sb_range_top_sound.
  - inversion Hgamma as [|wp y wps' tail Hhead Htail]; subst. inversion Htail; subst.
    destruct y as [wy x]. destruct Hhead as [Hwx [Hx Ha]]. cbn in Hwx, Hx, Ha. subst wy.
    exact (sb_range_forward_one_sound o w a x rw z Hx Ha Heval).
  - inversion Hgamma as [|wp y wps' tail Hhead Htail]; subst.
    inversion Htail as [|wp y' wps' tail' Hhead' Htail']; subst. inversion Htail'; subst.
    destruct y as [wy x], y' as [vy y].
    destruct Hhead as [Hwx [Hx Ha]], Hhead' as [Hvy [Hy Hb]].
    cbn in Hwx, Hvy, Hx, Hy, Ha, Hb. subst wy vy.
    exact (sb_range_forward_two_sound o w v a b x y rw z Hx Hy Ha Hb Heval).
  - inversion Hgamma as [|wp y wps' tail Hhead Htail]; subst.
    inversion Htail as [|wp y' wps' tail' Hhead' Htail']; subst.
    inversion Htail' as [|wp y'' wps' tail'' Hhead'' Htail'']; subst.
    inversion Htail''; subst. destruct y as [wy x], y' as [vy y], y'' as [uy t].
    destruct Hhead as [Hwx [Hx Ha]], Hhead' as [Hvy [Hy Hb]], Hhead'' as [Hut [Ht Hc]].
    cbn in Hwx, Hvy, Hut, Hx, Hy, Ht, Ha, Hb, Hc. subst wy vy uy.
    exact (sb_range_forward_three_sound o w v u a b c x y t rw z Hx Hy Ht Ha Hb Hc Heval).
  - destruct o; now apply sb_range_top_sound.
Qed.

Fixpoint sb_range_points_c (xs : list (width * sb_range)) : Cost.t (option (list word)) :=
  match xs with
  | [] => Cost.ret (Some [])
  | (w, r) :: rest =>
    Cost.step ;;
    if fst r =? snd r then
      Cost.map (fun tail =>
        match tail with
        | Some tail => Some ((w, fst r) :: tail)
        | None => None
        end) (sb_range_points_c rest)
    else Cost.ret None
  end.

Lemma sb_range_points_sound : forall xs cs points,
  Forall2 (payload_sound sb_range_pgamma) xs cs ->
  Cost.value (sb_range_points_c xs) = Some points -> points = cs.
Proof.
  intros xs cs points Hpayload. revert points.
  induction Hpayload as [|[w [lo hi]] [v z] xs cs Hhead Htail IH]; intros points Hpoints.
  - injection Hpoints as <-. reflexivity.
  - cbn [sb_range_points_c fst snd] in Hpoints. autorewrite with galois_cost in Hpoints.
    destruct (lo =? hi) eqn:Hsingle; [|discriminate].
    autorewrite with galois_cost in Hpoints.
    destruct (Cost.value (sb_range_points_c xs)) as [tail|] eqn:Hrest; [|discriminate].
    injection Hpoints as <-.
    destruct Hhead as [Hwidth [Hz Hrange]]. cbn [fst snd] in Hwidth. subst v.
    apply Z.eqb_eq in Hsingle. unfold sb_range_pgamma, sb_range_gamma in Hrange.
    cbn [fst snd] in Hrange.
    assert (Hvalue : lo = z) by lia. subst z.
    now rewrite (IH tail eq_refl).
Qed.

(** The legacy singleton path skips counts and the separate signed division/remainder rules. *)
Definition sb_range_forward_c (o : op) (xs : list (width * sb_range)) (rw : width)
    : Cost.t (list sb_range) :=
  match o with
  | (bvpopcnt | bvsdiv | bvsrem) => sb_range_forward_raw_c o xs rw
  | _ =>
    let* points := sb_range_points_c xs in
    match points with
    | Some cs =>
      let* result := Cost.step ;; known_bits_eval_c o cs in
      Cost.ret
        (match result with
        | Some (_, z) => [(z, z)]
        | None => []
        end)
    | None => sb_range_forward_raw_c o xs rw
    end
  end.

Definition sb_range_forward (o : op) (xs : list (width * sb_range)) (rw : width)
    : list sb_range := Cost.value (sb_range_forward_c o xs rw).

(** Direct range dispatch and its optional singleton path preserve every concrete result. *)
Theorem sb_range_forward_sound : forall o xs cs rw z,
  Forall2 (payload_sound sb_range_pgamma) xs cs -> eval_op o cs = Some (rw, z) ->
  sb_ranges_gamma rw (sb_range_forward o xs rw) z.
Proof.
  intros o xs cs rw z Hpayload Heval.
  assert (Hraw : sb_ranges_gamma rw (sb_range_forward_raw o xs rw) z)
    by now apply (sb_range_forward_raw_sound o xs cs).
  destruct o; try exact Hraw.
  all: unfold sb_range_forward, sb_range_forward_c; autorewrite with galois_cost.
  all: destruct (Cost.value (sb_range_points_c xs)) as [points|] eqn:Hpoints;
    [|exact Hraw].
  all: pose proof (sb_range_points_sound xs cs points Hpayload Hpoints) as ->.
  all: autorewrite with galois_cost; rewrite known_bits_eval_equation, Heval.
  all: split; [exact (eval_op_is_word _ cs (rw, z) Heval)|].
  all: exists (z, z); split; [now left|]; unfold sb_range_gamma; cbn [fst snd]; lia.
Qed.
