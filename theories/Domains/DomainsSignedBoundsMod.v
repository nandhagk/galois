(** * Local signed-modulus range rules

    Signed modulus combines ordinary unsigned magnitude bounds and divisor-sign constraints.
    For example, a strictly positive divisor keeps the result between zero and that divisor.
    Builds on: DomainsSignedBoundsArith and public Bits signed-modulus equations. *)

From Stdlib Require Import ZArith List Bool Lia.
From Galois.Bits Require Import BitsWord BitsFun BitsOp BitsTestbit BitsArith.
From Galois.Domains Require Import DomainsSignedBounds DomainsSignedBoundsRange
  DomainsSignedBoundsArith.
Import List.ListNotations.

Local Open Scope Z_scope.

Definition sb_urem_bound (w : width) (a b : sb_range) : sb_range :=
  hd (0, modulus w - 1) (sb_range_urem w a b).

Lemma sb_urem_one_range : forall w a b, sb_range_urem w a b = [sb_urem_bound w a b].
Proof.
  intros w [la ua] [lb ub]. unfold sb_urem_bound, sb_range_urem.
  destruct ((0 <=? la) && (0 <? lb) && (la / ub =? ua / lb));
    rewrite sb_checked_ranges_pair; reflexivity.
Qed.

Lemma sb_urem_bound_sound : forall w a b x y,
  is_word w x -> is_word w y -> sb_range_gamma a x -> sb_range_gamma b y ->
  sb_range_gamma (sb_urem_bound w a b) (wurem w x y).
Proof.
  intros w a b x y Hx Hy Ha Hb.
  pose proof (sb_range_urem_sound w a b x y Hx Hy Ha Hb) as H.
  rewrite sb_urem_one_range in H. now apply sb_single_range_gamma in H.
Qed.

Definition sb_neg_bound (w : width) (a : sb_range) : sb_range :=
  if snd a =? 0 then (0, 0) else
  if 0 <? fst a then sb_checked_range w (modulus w - snd a) (modulus w - fst a)
  else (0, modulus w - 1).

Lemma sb_neg_bound_sound : forall w a x,
  is_word w x -> sb_range_gamma a x -> sb_range_gamma (sb_neg_bound w a) (wneg w x).
Proof.
  intros w [lo hi] x Hw Ha. unfold sb_neg_bound.
  cbn [fst snd]. destruct (hi =? 0) eqn:Hzero.
  - apply Z.eqb_eq in Hzero. assert (Hx0 : x = 0)
      by (unfold sb_range_gamma, is_word in *; cbn [fst snd] in *; lia).
    subst x. rewrite wneg_value, Z.opp_0, wrap_0. unfold sb_range_gamma. cbn. lia.
  - destruct (0 <? lo) eqn:Hpositive.
    + apply Z.ltb_lt in Hpositive. apply sb_checked_range_sound;
        [rewrite wneg_value; apply wrap_is_word|].
      assert (Hvalue : wneg w x = modulus w - x).
      { rewrite wneg_value, wrap_mod. symmetry. apply Z.mod_unique with (q := -1).
        - left. unfold is_word, sb_range_gamma in *. cbn [fst snd] in *. lia.
        - ring. }
      rewrite Hvalue. unfold sb_range_gamma in Ha. cbn [fst snd] in Ha. lia.
    + pose proof (word_fun1_is_word bvneg wneg w x eq_refl) as Hword.
      unfold sb_range_gamma, is_word in *. cbn [fst snd]. lia.
Qed.

Definition sb_add_modular_bound (w : width) (a b : sb_range) : sb_range :=
  if (modulus w <=? fst a + fst b) && (snd a + snd b <? 2 * modulus w) then
    sb_checked_range w (fst a + fst b - modulus w) (snd a + snd b - modulus w)
  else sb_checked_range w (fst a + fst b) (snd a + snd b).

Lemma sb_add_modular_bound_sound : forall w a b x y,
  is_word w x -> is_word w y -> sb_range_gamma a x -> sb_range_gamma b y ->
  sb_range_gamma (sb_add_modular_bound w a b) (wadd w x y).
Proof.
  intros w [la ua] [lb ub] x y Hx Hy Ha Hb.
  unfold sb_range_gamma in Ha, Hb. cbn [fst snd] in Ha, Hb.
  unfold sb_add_modular_bound. cbn [fst snd].
  destruct ((modulus w <=? la + lb) && (ua + ub <? 2 * modulus w)) eqn:Hwrap.
  - apply andb_true_iff in Hwrap as [Hl Hu]. apply Z.leb_le in Hl. apply Z.ltb_lt in Hu.
    apply sb_checked_range_sound; [rewrite wadd_value; apply wrap_is_word|].
    rewrite wadd_value, sb_wrap_one_subtract by lia. lia.
  - pose proof (sb_checked_ranges_wrapped_sound w (la + lb) (ua + ub) (x + y)
      ltac:(lia)) as H.
    rewrite sb_checked_ranges_pair in H. apply sb_single_range_gamma in H.
    rewrite wadd_value. exact H.
Qed.

Definition sb_mod_choice_bound (u candidate : sb_range) : sb_range :=
  if 0 <? fst u then candidate else
  if snd u =? 0 then (0, 0)
  else (Z.min 0 (fst candidate), Z.max 0 (snd candidate)).

Lemma sb_mod_choice_bound_sound : forall w u candidate r z,
  is_word w r -> sb_range_gamma u r -> sb_range_gamma candidate z ->
  sb_range_gamma (sb_mod_choice_bound u candidate) (if r =? 0 then r else z).
Proof.
  intros w [lu uu] [lc uc] r z Hr Hu Hcandidate.
  unfold sb_mod_choice_bound, sb_range_gamma in *. cbn [fst snd] in *.
  destruct (0 <? lu) eqn:Hpositive.
  - apply Z.ltb_lt in Hpositive. rewrite (proj2 (Z.eqb_neq r 0)) by lia. exact Hcandidate.
  - destruct (uu =? 0) eqn:Hzero.
    + apply Z.eqb_eq in Hzero. assert (Hr0 : r = 0) by (unfold is_word in Hr; lia).
      subst r. cbn. lia.
    + destruct (r =? 0) eqn:Hrzero.
      * apply Z.eqb_eq in Hrzero. subst r. cbn [fst snd]. lia.
      * cbn [fst snd]. lia.
Qed.

Definition sb_smod_base_bound (w : width) (a b : sb_range) : sb_range :=
  match sb_range_sign w a, sb_range_sign w b with
  | Some sa, Some sb =>
    let aa := sb_range_magnitude w sa a in
    let bb := sb_range_magnitude w sb b in
    let u := sb_urem_bound w aa bb in
    let candidate :=
      match sa, sb with
      | false, false => u
      | true, false => sb_add_modular_bound w (sb_neg_bound w u) b
      | false, true => sb_add_modular_bound w u b
      | true, true => sb_neg_bound w u
      end in
    sb_mod_choice_bound u candidate
  | _, _ => (0, modulus w - 1)
  end.

Lemma sb_smod_base_bound_sound : forall w a b x y,
  is_word w x -> is_word w y -> sb_range_gamma a x -> sb_range_gamma b y ->
  sb_range_gamma (sb_smod_base_bound w a b) (wsmod w x y).
Proof.
  intros w a b x y Hx Hy Ha Hb. unfold sb_smod_base_bound.
  destruct (sb_range_sign w a) as [sa|] eqn:Hsa;
    destruct (sb_range_sign w b) as [sb|] eqn:Hsb.
  2,3,4: pose proof (wsmod_is_word w x y); unfold sb_range_gamma, is_word in *;
    cbn [fst snd]; lia.
  pose proof (sb_range_sign_sound w a x sa Hx Ha Hsa) as Hsx.
  pose proof (sb_range_sign_sound w b y sb Hy Hb Hsb) as Hsy.
  pose proof (sb_range_magnitude_sound w a x sa Hx Ha Hsa) as Hmagx.
  pose proof (sb_range_magnitude_sound w b y sb Hy Hb Hsb) as Hmagy.
  assert (Hnx : is_word w (wneg w x)) by (rewrite wneg_value; apply wrap_is_word).
  assert (Hny : is_word w (wneg w y)) by (rewrite wneg_value; apply wrap_is_word).
  destruct sa, sb; rewrite wsmod_value, Hsx, Hsy; cbn [xorb];
    rewrite ?(wrap_id w x Hx), ?(wrap_id w y Hy).
  all: apply (sb_mod_choice_bound_sound w); try apply wurem_is_word;
    try solve [apply sb_urem_bound_sound; assumption].
  - apply sb_neg_bound_sound; [apply wurem_is_word|].
    apply sb_urem_bound_sound; assumption.
  - apply sb_add_modular_bound_sound; try assumption;
      [rewrite wneg_value; apply wrap_is_word|].
    apply sb_neg_bound_sound; [apply wurem_is_word|].
    apply sb_urem_bound_sound; assumption.
  - apply sb_add_modular_bound_sound; try assumption; [apply wurem_is_word|].
    apply sb_urem_bound_sound; assumption.
Qed.

Definition sb_range_smod (w : width) (a b : sb_range) : list sb_range :=
  let base := sb_smod_base_bound w a b in
  match sb_range_sign w b with
  | Some false =>
    if 0 <? fst b then [(Z.max (fst base) 0, Z.min (snd base) (snd b - 1))]
    else [base]
  | _ => [base]
  end.

(** A strictly positive divisor adds its nonnegative signed-modulus upper bound. *)
Theorem sb_range_smod_sound : forall w a b x y,
  is_word w x -> is_word w y -> sb_range_gamma a x -> sb_range_gamma b y ->
  sb_ranges_gamma w (sb_range_smod w a b) (wsmod w x y).
Proof.
  intros w a b x y Hx Hy Ha Hb.
  pose proof (sb_smod_base_bound_sound w a b x y Hx Hy Ha Hb) as Hbase.
  split; [apply wsmod_is_word|]. unfold sb_range_smod.
  destruct (sb_range_sign w b) as [[|]|] eqn:Hsign.
  1,3: eexists; split; [now left|exact Hbase].
  destruct (0 <? fst b) eqn:Hpositive.
  2: { eexists. split; [now left|exact Hbase]. }
  apply Z.ltb_lt in Hpositive.
  pose proof (sb_range_sign_sound w b y false Hy Hb Hsign) as Hsy.
  assert (Hsignedy : signed w y = y)
    by (rewrite signed_nonnegative, (wrap_id w y Hy) by exact Hsy; reflexivity).
  pose proof (proj1 (wsmod_sign w x y) ltac:(rewrite Hsignedy;
    unfold sb_range_gamma in Hb; lia)) as Hmod.
  assert (Hresult : is_word w (wsmod w x y)) by apply wsmod_is_word.
  assert (Hsignr : msb w (wsmod w x y) = false).
  { destruct (msb w (wsmod w x y)) eqn:Hs; [|reflexivity].
    pose proof (proj2 (signed_neg_iff_msb w (wsmod w x y)) Hs). lia. }
  rewrite signed_nonnegative, (wrap_id w _ Hresult), Hsignedy in Hmod by exact Hsignr.
  eexists. split; [now left|].
  unfold sb_range_gamma in *. cbn [fst snd]. lia.
Qed.
