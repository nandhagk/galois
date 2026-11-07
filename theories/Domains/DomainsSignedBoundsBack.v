(** * Local backward range constraints

    Binary comparisons refine inclusive endpoints and retain the original operand widths.
    For example, x < 4 tightens an unsigned [0,7] operand to [0,3].
    Builds on: DomainsSignedBoundsForward and public Bits comparison equations. *)

From Stdlib Require Import ZArith List Bool Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Bits Require Import BitsWord BitsFun BitsOp BitsArith BitsTestbit.
From Galois.Domains Require Import DomainsNumeric DomainsTnumBack DomainsSignedBounds
  DomainsSignedBoundsRange DomainsSignedBoundsArith DomainsSignedBoundsForward
  DomainsSignedBoundsConsistency.
Import List.ListNotations Cost.Notations.

Local Open Scope Z_scope.

Definition sb_range_intersect (a b : sb_range) : sb_range :=
  (Z.max (fst a) (fst b), Z.min (snd a) (snd b)).

Lemma sb_range_intersect_sound : forall a b z,
  sb_range_gamma a z -> sb_range_gamma b z -> sb_range_gamma (sb_range_intersect a b) z.
Proof.
  intros a b z Ha Hb. unfold sb_range_intersect, sb_range_gamma in *.
  cbn [fst snd]. lia.
Qed.

Definition sb_range_point (a : sb_range) (c : Z) : bool := (fst a =? c) && (snd a =? c).

Lemma sb_range_point_sound : forall a z c,
  sb_range_gamma a z -> sb_range_point a c = true -> z = c.
Proof.
  intros a z c Ha Hpoint. unfold sb_range_point in Hpoint.
  apply andb_true_iff in Hpoint as [Hl Hu]. apply Z.eqb_eq in Hl, Hu.
  unfold sb_range_gamma in Ha. lia.
Qed.

Lemma sb_bool_point_sound : forall a (b wanted : bool),
  sb_range_gamma a (if b then 1 else 0) ->
  sb_range_point a (if wanted then 1 else 0) = true -> b = wanted.
Proof.
  intros a b wanted Ha Hpoint.
  pose proof (sb_range_point_sound a _ _ Ha Hpoint) as Heq.
  destruct b, wanted; try reflexivity; discriminate.
Qed.

Definition sb_range_exclude (a : sb_range) (c : Z) : sb_range :=
  if fst a =? c then (fst a + 1, snd a) else
  if snd a =? c then (fst a, snd a - 1) else a.

Lemma sb_range_exclude_sound : forall a x c,
  sb_range_gamma a x -> x <> c -> sb_range_gamma (sb_range_exclude a c) x.
Proof.
  intros [lo hi] x c Ha Hneq.
  unfold sb_range_exclude, sb_range_gamma in *. cbn [fst snd] in *.
  destruct (lo =? c) eqn:Hl; [apply Z.eqb_eq in Hl; cbn [fst snd]; lia|].
  destruct (hi =? c) eqn:Hu; [apply Z.eqb_eq in Hu; cbn [fst snd]; lia|exact Ha].
Qed.

Definition sb_assume_equal_ranges (a b : sb_range) : sb_range * sb_range :=
  (sb_range_intersect a b, sb_range_intersect b a).

Definition sb_assume_neq_ranges (a b : sb_range) : sb_range * sb_range :=
  (if fst b =? snd b then sb_range_exclude a (fst b) else a,
   if fst a =? snd a then sb_range_exclude b (fst a) else b).

Lemma sb_assume_equal_ranges_sound : forall a b x y,
  sb_range_gamma a x -> sb_range_gamma b y -> x = y ->
  sb_range_gamma (fst (sb_assume_equal_ranges a b)) x /\
  sb_range_gamma (snd (sb_assume_equal_ranges a b)) y.
Proof.
  intros a b x y Ha Hb ->. split; apply sb_range_intersect_sound; assumption.
Qed.

Lemma sb_assume_neq_ranges_sound : forall a b x y,
  sb_range_gamma a x -> sb_range_gamma b y -> x <> y ->
  sb_range_gamma (fst (sb_assume_neq_ranges a b)) x /\
  sb_range_gamma (snd (sb_assume_neq_ranges a b)) y.
Proof.
  intros a b x y Ha Hb Hneq. unfold sb_assume_neq_ranges. cbn [fst snd]. split.
  - destruct (fst b =? snd b) eqn:Hpoint; [|exact Ha].
    apply Z.eqb_eq in Hpoint. apply sb_range_exclude_sound; [exact Ha|].
    unfold sb_range_gamma in Hb. assert (Hy : y = fst b) by lia. congruence.
  - destruct (fst a =? snd a) eqn:Hpoint; [|exact Hb].
    apply Z.eqb_eq in Hpoint. apply sb_range_exclude_sound; [exact Hb|].
    unfold sb_range_gamma in Ha. assert (Hx : x = fst a) by lia. congruence.
Qed.

Definition sb_assume_order_ranges (strict result : bool) (a b : sb_range)
    : sb_range * sb_range :=
  let d := if strict then 1 else 0 in
  if result then
    ((fst a, Z.min (snd a) (snd b - d)), (Z.max (fst b) (fst a + d), snd b))
  else
    ((Z.max (fst a) (fst b + (1 - d)), snd a),
     (fst b, Z.min (snd b) (snd a - (1 - d)))).

Lemma sb_assume_order_ranges_sound : forall (strict result : bool) a b x y,
  sb_range_gamma a x -> sb_range_gamma b y ->
  (if strict then x <? y else x <=? y) = result ->
  sb_range_gamma (fst (sb_assume_order_ranges strict result a b)) x /\
  sb_range_gamma (snd (sb_assume_order_ranges strict result a b)) y.
Proof.
  intros strict result a b x y Ha Hb Horder.
  unfold sb_assume_order_ranges, sb_range_gamma in *.
  destruct strict, result; cbn [fst snd] in *;
    first [apply Z.ltb_lt in Horder|apply Z.ltb_ge in Horder|
      apply Z.leb_le in Horder|apply Z.leb_gt in Horder]; split; lia.
Qed.

Lemma sb_same_sign_difference : forall w x y,
  is_word w x -> is_word w y -> msb w x = msb w y ->
  signed w x - signed w y = x - y.
Proof.
  intros w x y Hx Hy Hsign. rewrite !signed_value, (wrap_id w x Hx), (wrap_id w y Hy).
  rewrite !msb_half, (wrap_id w x Hx), (wrap_id w y Hy) in Hsign.
  destruct (x <? half w), (y <? half w); cbn in Hsign; try discriminate; ring.
Qed.

Lemma sb_same_sign_comparison : forall w (strict : bool) x y,
  is_word w x -> is_word w y -> msb w x = msb w y ->
  (if strict then signed w x <? signed w y else signed w x <=? signed w y) =
  (if strict then x <? y else x <=? y).
Proof.
  intros w strict x y Hx Hy Hsign.
  pose proof (sb_same_sign_difference w x y Hx Hy Hsign) as Hd.
  destruct strict.
  - destruct (signed w x <? signed w y) eqn:Hs, (x <? y) eqn:Hu; try reflexivity;
      apply Z.ltb_lt in Hs || apply Z.ltb_ge in Hs;
      apply Z.ltb_lt in Hu || apply Z.ltb_ge in Hu; lia.
  - destruct (signed w x <=? signed w y) eqn:Hs, (x <=? y) eqn:Hu; try reflexivity;
      apply Z.leb_le in Hs || apply Z.leb_gt in Hs;
      apply Z.leb_le in Hu || apply Z.leb_gt in Hu; lia.
Qed.

Definition sb_assume_signed_ranges (w : width) (strict result : bool) (a b : sb_range)
    : sb_range * sb_range :=
  match sb_range_sign w a, sb_range_sign w b with
  | Some sa, Some sb =>
    if Bool.eqb sa sb then sb_assume_order_ranges strict result a b else (a, b)
  | _, _ => (a, b)
  end.

Lemma sb_assume_signed_ranges_sound : forall w (strict result : bool) a b x y,
  is_word w x -> is_word w y -> sb_range_gamma a x -> sb_range_gamma b y ->
  (if strict then signed w x <? signed w y else signed w x <=? signed w y) = result ->
  sb_range_gamma (fst (sb_assume_signed_ranges w strict result a b)) x /\
  sb_range_gamma (snd (sb_assume_signed_ranges w strict result a b)) y.
Proof.
  intros w strict result a b x y Hx Hy Ha Hb Horder. unfold sb_assume_signed_ranges.
  destruct (sb_range_sign w a) as [sa|] eqn:Hsa;
    destruct (sb_range_sign w b) as [sb|] eqn:Hsb; try (split; assumption).
  destruct (Bool.eqb sa sb) eqn:Hsame; [|split; assumption].
  pose proof (sb_range_sign_sound w a x sa Hx Ha Hsa) as Hsignx.
  pose proof (sb_range_sign_sound w b y sb Hy Hb Hsb) as Hsigny.
  assert (Hsign : msb w x = msb w y).
  { rewrite Hsignx, Hsigny. destruct sa, sb; cbn in Hsame; congruence. }
  rewrite (sb_same_sign_comparison w strict x y Hx Hy Hsign) in Horder.
  now apply sb_assume_order_ranges_sound.
Qed.

Definition sb_assume_pair_ranges (o : op) (w : width) (a b q : sb_range)
    : sb_range * sb_range :=
  match o with
  | bveq =>
    if sb_range_point q 1 then sb_assume_equal_ranges a b else
    if sb_range_point q 0 then sb_assume_neq_ranges a b else (a, b)
  | bvne =>
    if sb_range_point q 0 then sb_assume_equal_ranges a b else
    if sb_range_point q 1 then sb_assume_neq_ranges a b else (a, b)
  | bvult =>
    if sb_range_point q 1 then sb_assume_order_ranges true true a b else
    if sb_range_point q 0 then sb_assume_order_ranges true false a b else (a, b)
  | bvule =>
    if sb_range_point q 1 then sb_assume_order_ranges false true a b else
    if sb_range_point q 0 then sb_assume_order_ranges false false a b else (a, b)
  | bvslt =>
    if sb_range_point q 1 then sb_assume_signed_ranges w true true a b else
    if sb_range_point q 0 then sb_assume_signed_ranges w true false a b else (a, b)
  | bvsle =>
    if sb_range_point q 1 then sb_assume_signed_ranges w false true a b else
    if sb_range_point q 0 then sb_assume_signed_ranges w false false a b else (a, b)
  | _ => (a, b)
  end.

(** Every supported comparison constraint preserves the two concrete input range members. *)
Theorem sb_assume_pair_ranges_sound : forall o w f a b q x y,
  word_cmp o = Some f -> is_word w x -> is_word w y ->
  sb_range_gamma a x -> sb_range_gamma b y ->
  sb_range_gamma q (if f w x y then 1 else 0) ->
  sb_range_gamma (fst (sb_assume_pair_ranges o w a b q)) x /\
  sb_range_gamma (snd (sb_assume_pair_ranges o w a b q)) y.
Proof.
  intros o w f a b q x y Hf Hx Hy Ha Hb Hq.
  assert (Htrue : sb_range_point q 1 = true -> f w x y = true)
    by exact (sb_bool_point_sound q (f w x y) true Hq).
  assert (Hfalse : sb_range_point q 0 = true -> f w x y = false)
    by exact (sb_bool_point_sound q (f w x y) false Hq).
  clear Hq. destruct o; try discriminate Hf; injection Hf as <-;
    cbn [sb_assume_pair_ranges].
  - rewrite (wrap_id w x Hx), (wrap_id w y Hy) in Htrue, Hfalse.
    destruct (sb_range_point q 1) eqn:Hone.
    + apply sb_assume_equal_ranges_sound; try assumption.
      apply Z.eqb_eq. now apply Htrue.
    + destruct (sb_range_point q 0) eqn:Hzero; [|split; assumption].
      apply sb_assume_neq_ranges_sound; try assumption. apply Z.eqb_neq. now apply Hfalse.
  - rewrite (wrap_id w x Hx), (wrap_id w y Hy) in Htrue, Hfalse.
    destruct (sb_range_point q 0) eqn:Hzero.
    + apply sb_assume_equal_ranges_sound; try assumption.
      specialize (Hfalse eq_refl). apply negb_false_iff, Z.eqb_eq in Hfalse. exact Hfalse.
    + destruct (sb_range_point q 1) eqn:Hone; [|split; assumption].
      apply sb_assume_neq_ranges_sound; try assumption.
      specialize (Htrue eq_refl). apply negb_true_iff, Z.eqb_neq in Htrue. exact Htrue.
  - rewrite wult_value, (wrap_id w x Hx), (wrap_id w y Hy) in Htrue, Hfalse.
    destruct (sb_range_point q 1) eqn:Hone.
    + apply sb_assume_order_ranges_sound; try assumption. now apply Htrue.
    + destruct (sb_range_point q 0) eqn:Hzero; [|split; assumption].
      apply sb_assume_order_ranges_sound; try assumption. now apply Hfalse.
  - rewrite wule_value, (wrap_id w x Hx), (wrap_id w y Hy) in Htrue, Hfalse.
    destruct (sb_range_point q 1) eqn:Hone.
    + apply sb_assume_order_ranges_sound; try assumption. now apply Htrue.
    + destruct (sb_range_point q 0) eqn:Hzero; [|split; assumption].
      apply sb_assume_order_ranges_sound; try assumption. now apply Hfalse.
  - rewrite wslt_value in Htrue, Hfalse.
    destruct (sb_range_point q 1) eqn:Hone.
    + apply sb_assume_signed_ranges_sound; try assumption. now apply Htrue.
    + destruct (sb_range_point q 0) eqn:Hzero; [|split; assumption].
      apply sb_assume_signed_ranges_sound; try assumption. now apply Hfalse.
  - rewrite wsle_value in Htrue, Hfalse.
    destruct (sb_range_point q 1) eqn:Hone.
    + apply sb_assume_signed_ranges_sound; try assumption. now apply Htrue.
    + destruct (sb_range_point q 0) eqn:Hzero; [|split; assumption].
      apply sb_assume_signed_ranges_sound; try assumption. now apply Hfalse.
Qed.

Definition sb_range_overlap (a b : sb_range) : bool :=
  Z.max (fst a) (fst b) <=? Z.min (snd a) (snd b).

Lemma sb_range_overlap_sound : forall a b z,
  sb_range_gamma a z -> sb_range_gamma b z -> sb_range_overlap a b = true.
Proof.
  intros a b z Ha Hb. apply Z.leb_le. unfold sb_range_gamma in *. lia.
Qed.

Lemma sb_mod_ranges_word_sound : forall w a x,
  is_word w x -> sb_range_gamma a x ->
  sb_ranges_gamma w (sb_mod_ranges w (fst a) (snd a)) x.
Proof.
  intros w a x Hx Ha. rewrite <- (wrap_id w x Hx).
  now apply sb_mod_ranges_sound.
Qed.

Definition sb_binary_general_back_c (o : op) (wa wb : width) (a b : sb_range)
    (rw : width) (q : sb_range) : Cost.t (list sb_range * list sb_range) :=
  let* forward := sb_consistency_c o wa wb a b rw in
  let* consistent := existsb_c (fun r => Cost.step ;; Cost.ret (sb_range_overlap r q)) forward in
  if consistent then
    let refined := sb_assume_pair_ranges o wa a b q in
    Cost.ret (sb_mod_ranges wa (fst (fst refined)) (snd (fst refined)),
      sb_mod_ranges wb (fst (snd refined)) (snd (snd refined)))
  else Cost.ret ([], []).

Lemma sb_binary_general_back_equation : forall o wa wb a b rw q,
  Cost.value (sb_binary_general_back_c o wa wb a b rw q) =
  if existsb (fun r => sb_range_overlap r q) (sb_consistency o wa wb a b rw) then
    let refined := sb_assume_pair_ranges o wa a b q in
    (sb_mod_ranges wa (fst (fst refined)) (snd (fst refined)),
      sb_mod_ranges wb (fst (snd refined)) (snd (snd refined)))
  else ([], []).
Proof.
  intros o wa wb a b rw q. unfold sb_binary_general_back_c.
  rewrite !Cost.value_bind, value_existsb_c.
  change (existsb (fun r => Cost.value (Cost.step ;; Cost.ret (sb_range_overlap r q)))
    (Cost.value (sb_consistency_c o wa wb a b rw))) with
    (existsb (fun r => sb_range_overlap r q) (sb_consistency o wa wb a b rw)).
  destruct (existsb (fun r => sb_range_overlap r q)
    (sb_consistency o wa wb a b rw)); reflexivity.
Qed.

Lemma sb_binary_general_back_sound : forall o wa wb a b rw q x y z,
  is_word wa x -> is_word wb y -> sb_range_gamma a x -> sb_range_gamma b y ->
  sb_range_gamma q z -> eval_op o [(wa, x); (wb, y)] = Some (rw, z) ->
  sb_ranges_gamma wa (fst (Cost.value (sb_binary_general_back_c o wa wb a b rw q))) x /\
  sb_ranges_gamma wb (snd (Cost.value (sb_binary_general_back_c o wa wb a b rw q))) y.
Proof.
  intros o wa wb a b rw q x y z Hx Hy Ha Hb Hq Heval.
  assert (Hpayload : Forall2 (payload_sound sb_range_pgamma)
    [(wa, a); (wb, b)] [(wa, x); (wb, y)]).
  { constructor; [split; [reflexivity|split; assumption]|].
    constructor; [split; [reflexivity|split; assumption]|constructor]. }
  destruct (sb_consistency_sound o wa wb a b rw x y z Hx Hy Ha Hb Heval)
    as [Hz [r [Hin Hr]]].
  assert (Hconsistent : existsb (fun r => sb_range_overlap r q)
    (sb_consistency o wa wb a b rw) = true).
  { apply existsb_exists. exists r. split; [exact Hin|].
    now apply (sb_range_overlap_sound r q z). }
  assert (Hpair : sb_range_gamma (fst (sb_assume_pair_ranges o wa a b q)) x /\
    sb_range_gamma (snd (sb_assume_pair_ranges o wa a b q)) y).
  { destruct (word_cmp o) as [f|] eqn:Hcmp.
    - pose proof (eval_op_cmp_width o f wa wb x y (rw, z) Hcmp Heval) as ->.
      rewrite (eval_op_cmp o wb x y f Hcmp) in Heval. injection Heval as <- <-.
      now apply (sb_assume_pair_ranges_sound o wb f).
    - destruct o; try discriminate Hcmp; split; assumption. }
  rewrite sb_binary_general_back_equation, Hconsistent.
  split; apply sb_mod_ranges_word_sound; tauto.
Qed.

Definition sb_binary_ranges_back_c (o : op) (wa wb : width) (a b : sb_range)
    (rw : width) (q : sb_range) : Cost.t (list sb_range * list sb_range) :=
  match o with
  | bvadd => Cost.ret (sb_range_sub wa q b, sb_range_sub wb q a)
  | bvsub => Cost.ret (sb_range_add wa q b, sb_range_sub wb a q)
  | _ => sb_binary_general_back_c o wa wb a b rw q
  end.

(** Binary backward bounds use modular inverses for arithmetic and direct constraints otherwise. *)
Theorem sb_binary_ranges_back_sound : forall o wa wb a b rw q x y z,
  is_word wa x -> is_word wb y -> sb_range_gamma a x -> sb_range_gamma b y ->
  sb_range_gamma q z -> eval_op o [(wa, x); (wb, y)] = Some (rw, z) ->
  sb_ranges_gamma wa (fst (Cost.value (sb_binary_ranges_back_c o wa wb a b rw q))) x /\
  sb_ranges_gamma wb (snd (Cost.value (sb_binary_ranges_back_c o wa wb a b rw q))) y.
Proof.
  intros o wa wb a b rw q x y z Hx Hy Ha Hb Hq Heval.
  destruct o; try exact
    (sb_binary_general_back_sound _ wa wb a b rw q x y z Hx Hy Ha Hb Hq Heval).
  - pose proof (eval_op_fun2_width bvadd wadd wa wb x y (rw, z) eq_refl Heval) as ->.
    rewrite (eval_op_fun2 bvadd wb x y wadd eq_refl) in Heval. injection Heval as <- <-.
    split.
    + rewrite <- (proj1 (tnum_add_sub_cancel wb x y Hx Hy)).
      now apply sb_range_sub_sound.
    + rewrite wadd_comm in Hq. rewrite <- (proj1 (tnum_add_sub_cancel wb y x Hy Hx)).
      now apply sb_range_sub_sound.
  - pose proof (eval_op_fun2_width bvsub wsub wa wb x y (rw, z) eq_refl Heval) as ->.
    rewrite (eval_op_fun2 bvsub wb x y wsub eq_refl) in Heval. injection Heval as <- <-.
    split.
    + rewrite <- (proj1 (proj2 (tnum_add_sub_cancel wb x y Hx Hy))).
      now apply sb_range_add_sound.
    + rewrite <- (proj2 (proj2 (tnum_add_sub_cancel wb x y Hx Hy))).
      now apply sb_range_sub_sound.
Qed.

Definition sb_unary_ranges_back (o : op) (w : width) (a : sb_range)
    (rw : width) (q : sb_range) : list sb_range :=
  match o with
  | bvzext _ | bvsext _ => sb_mod_ranges w (fst q) (snd q)
  | bvtrunc _ =>
    if (0 <=? fst a) && (snd a <? modulus rw)
    then
      let r := sb_range_intersect a q in sb_mod_ranges w (fst r) (snd r)
    else sb_mod_ranges w (fst a) (snd a)
  | _ => sb_mod_ranges w (fst a) (snd a)
  end.

(** Unary width changes project fitting result ranges at the original operand width. *)
Theorem sb_unary_ranges_back_sound : forall o w a rw q x z,
  is_word w x -> sb_range_gamma a x -> sb_range_gamma q z ->
  eval_op o [(w, x)] = Some (rw, z) ->
  sb_ranges_gamma w (sb_unary_ranges_back o w a rw q) x.
Proof.
  intros o w a rw q x z Hx Ha Hq Heval. destruct o;
    try (now apply sb_mod_ranges_word_sound).
  - rewrite eval_op_zext in Heval. injection Heval as <- <-.
    pose proof (sb_mod_ranges_sound w (fst q) (snd q) _ Hq) as H.
    rewrite wrap_narrow, wrap_wrap, (wrap_id w x Hx) in H;
      [exact H|apply width_add_le].
  - rewrite eval_op_sext in Heval. injection Heval as <- <-.
    pose proof (sb_mod_ranges_sound w (fst q) (snd q) _ Hq) as H.
    rewrite wrap_narrow, wrap_signed, (wrap_id w x Hx) in H;
      [exact H|apply width_add_le].
  - rewrite eval_op_trunc in Heval. destruct (Pos.leb target w); [|discriminate].
    injection Heval as <- <-. rewrite (wrap_id w x Hx) in Hq.
    unfold sb_unary_ranges_back.
    destruct ((0 <=? fst a) && (snd a <? modulus target)) eqn:Hfit;
      [|now apply sb_mod_ranges_word_sound].
    apply andb_true_iff in Hfit as [Hl Hu]. apply Z.leb_le in Hl. apply Z.ltb_lt in Hu.
    assert (Hxsmall : is_word target x) by (unfold is_word, sb_range_gamma in *; lia).
    rewrite (wrap_id target x Hxsmall) in Hq. apply sb_mod_ranges_word_sound; [exact Hx|].
    now apply sb_range_intersect_sound.
Qed.

Definition sb_ranges_backward_c (o : op) (xs : list (width * sb_range)) (rw : width)
    (q : sb_range) : Cost.t (list (list sb_range)) :=
  match xs with
  | [(w, a)] => Cost.ret [sb_unary_ranges_back o w a rw q]
  | [(wa, a); (wb, b)] =>
    Cost.map (fun p => [fst p; snd p]) (sb_binary_ranges_back_c o wa wb a b rw q)
  | _ => map_c (fun wr => Cost.step ;;
      Cost.ret (sb_mod_ranges (fst wr) (fst (snd wr)) (snd (snd wr)))) xs
  end.

Definition sb_ranges_backward (o : op) (xs : list (width * sb_range)) (rw : width)
    (q : sb_range) : list (list sb_range) := Cost.value (sb_ranges_backward_c o xs rw q).

Lemma sb_ranges_identity_sound : forall xs cs,
  Forall2 (payload_sound sb_range_pgamma) xs cs ->
  Forall2 (fun wp_y rs => sb_ranges_gamma (fst (fst wp_y)) rs (snd (snd wp_y)))
    (combine xs cs)
    (map (fun wr => sb_mod_ranges (fst wr) (fst (snd wr)) (snd (snd wr))) xs).
Proof.
  intros xs cs Hpayload.
  induction Hpayload as [|[w a] [v x] xs cs Hhead Htail IH]; cbn [map combine fst snd];
    constructor.
  - destruct Hhead as [Hwidth [Hw Ha]]. cbn [fst snd] in Hwidth, Ha. subst v.
    now apply sb_mod_ranges_word_sound.
  - exact IH.
Qed.

(** Local backward range dispatch preserves each operand at its own recorded width. *)
Theorem sb_ranges_backward_sound : forall o xs cs rw q z,
  Forall2 (payload_sound sb_range_pgamma) xs cs -> sb_range_gamma q z ->
  eval_op o cs = Some (rw, z) ->
  Forall2 (fun wp_y rs => sb_ranges_gamma (fst (fst wp_y)) rs (snd (snd wp_y)))
    (combine xs cs) (sb_ranges_backward o xs rw q).
Proof.
  intros o xs cs rw q z Hpayload Hq Heval.
  destruct xs as [|[w a] [|[v b] [|extra rest]]].
  - constructor.
  - inversion Hpayload as [|wp c xs' cs' Hhead Htail]; subst. inversion Htail; subst.
    destruct c as [u x]. destruct Hhead as [Hwidth [Hw Ha]].
    cbn [fst snd] in Hwidth, Ha. subst u.
    constructor; [now apply (sb_unary_ranges_back_sound o w a rw q x z)|constructor].
  - inversion Hpayload as [|wp c xs' cs' Hhead Htail]; subst.
    inversion Htail as [|wp' c' xs'' cs'' Hhead' Hnil]; subst. inversion Hnil; subst.
    destruct c as [u x], c' as [u' y].
    destruct Hhead as [Hwidth [Hw Ha]], Hhead' as [Hwidth' [Hw' Hb]].
    cbn [fst snd] in Hwidth, Hwidth', Ha, Hb. subst u u'.
    destruct (sb_binary_ranges_back_sound o w v a b rw q x y z Hw Hw' Ha Hb Hq Heval)
      as [Hl Hr].
    unfold sb_ranges_backward, sb_ranges_backward_c. rewrite Cost.value_map.
    constructor; [exact Hl|constructor; [exact Hr|constructor]].
  - unfold sb_ranges_backward, sb_ranges_backward_c. rewrite value_map_c.
    now apply sb_ranges_identity_sound.
Qed.

(** Range backward dispatch retains the operand count even without a feasible concrete tuple. *)
Theorem sb_ranges_backward_length : forall o xs rw q,
  length (sb_ranges_backward o xs rw q) = length xs.
Proof.
  intros o [|[w a] [|[v b] [|extra rest]]] rw q;
    unfold sb_ranges_backward, sb_ranges_backward_c;
    try rewrite Cost.value_map; try rewrite value_map_c; try rewrite length_map; reflexivity.
Qed.
