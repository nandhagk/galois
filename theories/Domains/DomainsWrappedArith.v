(** * Pole-aware circular arithmetic

    Modular endpoint sums and signed and unsigned pole cuts bound circular arithmetic.
    For example, adding [250,255] and [1,7] gives the eight-bit arc [251,6].
    Builds on: DomainsWrappedParts and the interval scalar family. *)

From Stdlib Require Import ZArith List Bool Lia.
From Galois.Lattice Require Import LatticeConcrete.
From Galois.Bits Require Import BitsWord BitsFun BitsTestbit BitsArith.
From Galois.Domains Require Import DomainsBound DomainsInterval DomainsIntervalArith
  DomainsIntervalSigned DomainsWrapped DomainsWrappedParts.

Local Open Scope Z_scope.

Definition wrapped_add (w : width) (a b : wrapped) : wrapped :=
  match a, b with
  | WBot, _ | _, WBot => WBot
  | WItv lo hi, WItv lo' hi' =>
    if modulus w <? wrapped_size w a + wrapped_size w b then WFull
    else wrapped_norm w (WItv (lo + lo') (hi + hi'))
  | _, _ => WFull
  end.

Definition wrapped_neg (w : width) (a : wrapped) : wrapped :=
  match a with
  | WItv lo hi => wrapped_norm w (WItv (- hi) (- lo))
  | _ => a
  end.

Definition wrapped_sub (w : width) (a b : wrapped) : wrapped :=
  wrapped_add w a (wrapped_neg w b).

Local Lemma wrapped_offset_sum w a b x y :
  wrapped_offset w (a + b) (x + y) =
  (wrapped_offset w a x + wrapped_offset w b y) mod modulus w.
Proof.
  unfold wrapped_offset.
  replace (x + y - (a + b)) with ((x - a) + (y - b)) by ring.
  apply Z.add_mod. apply modulus_nonzero.
Qed.

Local Lemma wrapped_offset_neg w a b :
  wrapped_offset w (- b) (- a) = wrapped_offset w a b.
Proof.
  unfold wrapped_offset. f_equal. ring.
Qed.

(** Circular addition contains every modular sum of represented operands. *)
Theorem wrapped_add_sound w a b x y :
  wrapped_gamma w a x -> wrapped_gamma w b y ->
  wrapped_gamma w (wrapped_add w a b) (wrap w (x + y)).
Proof.
  destruct a as [| |lo hi], b as [| |lo' hi']; intros Hx Hy;
    cbn [wrapped_add] in *; try contradiction; try apply wrap_is_word.
  destruct (modulus w <? wrapped_size w (WItv lo hi) + wrapped_size w (WItv lo' hi'))
    eqn:Hfull; [apply wrap_is_word|].
  apply Z.ltb_ge in Hfull.
  apply (proj2 (wrapped_norm_gamma w (WItv (lo + lo') (hi + hi')) _)).
  destruct Hx as [Hx Hoffsetx], Hy as [Hy Hoffsety].
  split; [apply wrap_is_word|].
  rewrite wrapped_offset_word, !wrapped_offset_sum.
  pose proof (wrapped_offset_range w lo x).
  pose proof (wrapped_offset_range w lo' y).
  cbn [wrapped_size] in Hfull.
  rewrite !Z.mod_small by lia. lia.
Qed.

(** Circular negation contains every modular additive inverse. *)
Theorem wrapped_neg_sound w a x :
  wrapped_gamma w a x -> wrapped_gamma w (wrapped_neg w a) (wrap w (- x)).
Proof.
  destruct a as [| |lo hi]; intro Hx; cbn [wrapped_neg] in *;
    try contradiction; try apply wrap_is_word.
  apply (proj2 (wrapped_norm_gamma w (WItv (- hi) (- lo)) _)).
  destruct Hx as [Hx Hoffset]. split; [apply wrap_is_word|].
  rewrite wrapped_offset_word, !wrapped_offset_neg.
  rewrite (wrapped_offset_difference w lo x hi) by exact Hoffset.
  pose proof (wrapped_offset_range w lo x). lia.
Qed.

(** Circular subtraction contains every modular difference. *)
Theorem wrapped_sub_sound w a b x y :
  wrapped_gamma w a x -> wrapped_gamma w b y ->
  wrapped_gamma w (wrapped_sub w a b) (wrap w (x - y)).
Proof.
  intros Hx Hy. unfold wrapped_sub.
  replace (wrap w (x - y)) with (wrap w (x + wrap w (- y))).
  - apply wrapped_add_sound; [exact Hx|now apply wrapped_neg_sound].
  - replace (x - y) with (x + - y) by ring.
    rewrite (wrap_add w x (- y)), (wrap_add w x (wrap w (- y))), wrap_wrap. reflexivity.
Qed.

Definition wrapped_mul_piece (w : width) (a b : interval) : wrapped :=
  match a, b with
  | IBot, _ | _, IBot => WBot
  | Itv (Fin lo) (Fin hi), Itv (Fin lo') (Fin hi') =>
    wrapped_range w
      (Z.min (Z.min (lo * lo') (lo * hi')) (Z.min (hi * lo') (hi * hi')))
      (Z.max (Z.max (lo * lo') (lo * hi')) (Z.max (hi * lo') (hi * hi')))
  | _, _ => WFull
  end.

Local Lemma wrapped_product_bounds a b c d x y :
  a <= x <= b -> c <= y <= d ->
  Z.min (Z.min (a * c) (a * d)) (Z.min (b * c) (b * d)) <= x * y <=
  Z.max (Z.max (a * c) (a * d)) (Z.max (b * c) (b * d)).
Proof.
  intros Hx Hy.
  set (lo := Z.min (Z.min (a * c) (a * d)) (Z.min (b * c) (b * d))).
  set (hi := Z.max (Z.max (a * c) (a * d)) (Z.max (b * c) (b * d))).
  assert (Hlo : lo <= a * c /\ lo <= a * d /\ lo <= b * c /\ lo <= b * d).
  { unfold lo. repeat split; repeat rewrite Z.min_le_iff; intuition lia. }
  assert (Hhi : a * c <= hi /\ a * d <= hi /\ b * c <= hi /\ b * d <= hi).
  { unfold hi. repeat split; repeat rewrite Z.max_le_iff; intuition lia. }
  destruct Hlo as [Hac [Had [Hbc Hbd]]], Hhi as [Hac' [Had' [Hbc' Hbd']]].
  destruct (Z_le_gt_dec 0 x); destruct (Z_le_gt_dec 0 c); destruct (Z_le_gt_dec 0 d); nia.
Qed.

(** Four endpoint products contain every product in a finite integer rectangle. *)
Theorem wrapped_mul_piece_sound w a b x y :
  gamma interval_gamma a x -> gamma interval_gamma b y ->
  wrapped_gamma w (wrapped_mul_piece w a b) (wrap w (x * y)).
Proof.
  destruct a as [|lo hi], b as [|lo' hi']; intros Hx Hy; cbn [wrapped_mul_piece];
    try contradiction; try apply wrap_is_word.
  destruct lo as [|lo|], hi as [|hi|], lo' as [|lo'|], hi' as [|hi'|];
    cbn [wrapped_mul_piece]; try apply wrap_is_word.
  cbn [interval_gamma gamma bound_leb] in Hx, Hy.
  destruct Hx as [Hlo Hhi], Hy as [Hlo' Hhi'].
  apply Z.leb_le in Hlo, Hhi, Hlo', Hhi'.
  apply wrapped_range_sound. now apply wrapped_product_bounds.
Qed.

Definition wrapped_shift_interval (delta : Z) (a : interval) : interval :=
  let shift := fun b =>
    match b with
    | Fin z => Fin (z + delta)
    | _ => b
    end in
  match a with
  | IBot => IBot
  | Itv lo hi => Itv (shift lo) (shift hi)
  end.

(** Translating finite endpoints retains the translated mathematical interval meaning. *)
Theorem wrapped_shift_interval_sound delta a z :
  gamma interval_gamma a z -> gamma interval_gamma (wrapped_shift_interval delta a) (z + delta).
Proof.
  destruct a as [|lo hi]; intro Hz; [exact Hz|].
  destruct lo as [|lo|], hi as [|hi|];
    cbn [wrapped_shift_interval interval_gamma gamma bound_leb] in *;
    try tauto; rewrite ?Z.leb_le in *; intuition lia.
Qed.

Local Lemma wrapped_signed_bias w x :
  is_word w x -> signed w x = wrap w (x + half w) - half w.
Proof.
  intro Hx. rewrite signed_value, (wrap_id w x Hx).
  pose proof (modulus_half w) as Hmod.
  pose proof (half_pos w) as Hhalf. destruct Hx as [Hlo Hhi].
  destruct (x <? half w) eqn:Hsign.
  - apply Z.ltb_lt in Hsign. rewrite wrap_id by (split; lia). lia.
  - apply Z.ltb_ge in Hsign.
    assert (Hwrap : wrap w (x + half w) = x + half w - modulus w).
    { rewrite wrap_mod. symmetry. apply Z.mod_unique with (q := 1); lia. }
    rewrite Hwrap. lia.
Qed.

Definition wrapped_signed_parts (w : width) (a : wrapped) : interval * interval :=
  let biased := wrapped_parts w (wrapped_add w a (WItv (half w) (half w))) in
  (wrapped_shift_interval (- half w) (fst biased),
   wrapped_shift_interval (- half w) (snd biased)).

(** Biasing the sign bit and cutting at zero covers the signed interpretation of each word. *)
Theorem wrapped_signed_parts_sound w a z :
  wrapped_gamma w a z ->
  gamma interval_gamma (fst (wrapped_signed_parts w a)) (signed w z) \/
  gamma interval_gamma (snd (wrapped_signed_parts w a)) (signed w z).
Proof.
  intro Hz. pose proof (wrapped_gamma_word w a z Hz) as Hword.
  assert (Hhalf : wrapped_gamma w (WItv (half w) (half w)) (half w)).
  { split.
    - split; pose proof (half_pos w); pose proof (modulus_half w); lia.
    - lia. }
  pose proof (wrapped_add_sound w a _ z _ Hz Hhalf) as Hbiased.
  apply wrapped_parts_spec in Hbiased.
  unfold wrapped_signed_parts. cbn [fst snd].
  rewrite (wrapped_signed_bias w z Hword).
  replace (wrap w (z + half w) - half w) with (wrap w (z + half w) + - half w) by ring.
  destruct Hbiased as [[_ Hfirst]|[_ Hsecond]].
  - left. now apply wrapped_shift_interval_sound.
  - right. now apply wrapped_shift_interval_sound.
Qed.

Definition wrapped_mul_parts (w : width) (a b : interval * interval) : wrapped :=
  wrapped_join_four w
    (wrapped_mul_piece w (fst a) (fst b))
    (wrapped_mul_piece w (fst a) (snd b))
    (wrapped_mul_piece w (snd a) (fst b))
    (wrapped_mul_piece w (snd a) (snd b)).

Local Lemma wrapped_mul_parts_sound w a b x y :
  (gamma interval_gamma (fst a) x \/ gamma interval_gamma (snd a) x) ->
  (gamma interval_gamma (fst b) y \/ gamma interval_gamma (snd b) y) ->
  wrapped_gamma w (wrapped_mul_parts w a b) (wrap w (x * y)).
Proof.
  intros Hx Hy. unfold wrapped_mul_parts. apply wrapped_join_four_sound.
  destruct Hx as [Hx|Hx]; destruct Hy as [Hy|Hy].
  - left. now apply wrapped_mul_piece_sound.
  - right; left. now apply wrapped_mul_piece_sound.
  - right; right; left. now apply wrapped_mul_piece_sound.
  - right; right; right. now apply wrapped_mul_piece_sound.
Qed.

Local Lemma wrapped_interval_meet_gamma a b z :
  gamma interval_gamma a z -> gamma interval_gamma b z ->
  gamma interval_gamma (interval_meet a b) z.
Proof.
  destruct a as [|la ha], b as [|lb hb]; intros Ha Hb; try contradiction.
  destruct Ha as [Hla Hha], Hb as [Hlb Hhb].
  assert (Hlo : bound_leb (bound_max la lb) (Fin z) = true).
  { apply bound_max_least; assumption. }
  assert (Hhi : bound_leb (Fin z) (bound_min ha hb) = true).
  { apply bound_min_greatest; assumption. }
  assert (Hordered : bound_leb (bound_max la lb) (bound_min ha hb) = true).
  { eapply bound_leb_trans; eassumption. }
  assert (Hnonempty : bounds_nonempty (bound_max la lb) (bound_min ha hb) = true).
  { destruct (bound_max la lb), (bound_min ha hb); cbn in *; try discriminate; assumption. }
  cbn [interval_meet]. rewrite Hnonempty. split; assumption.
Qed.

Definition wrapped_mul_cut (pole : Z) (a : interval) : interval * interval :=
  (interval_meet a (Itv NegInf (Fin (pole - 1))),
   interval_meet a (Itv (Fin pole) PosInf)).

(** Cutting a linear piece at an arbitrary pole retains all of its integers. *)
Theorem wrapped_mul_cut_sound pole a z :
  gamma interval_gamma a z ->
  gamma interval_gamma (fst (wrapped_mul_cut pole a)) z \/
  gamma interval_gamma (snd (wrapped_mul_cut pole a)) z.
Proof.
  intro Ha. unfold wrapped_mul_cut. cbn [fst snd].
  destruct (Z_lt_ge_dec z pole) as [Hlow|Hhigh].
  - left. apply wrapped_interval_meet_gamma; [exact Ha|].
    cbn [interval_gamma gamma bound_leb]. split; [reflexivity|]. apply Z.leb_le. lia.
  - right. apply wrapped_interval_meet_gamma; [exact Ha|].
    cbn [interval_gamma gamma bound_leb]. split; [apply Z.leb_le; lia|reflexivity].
Qed.

Definition wrapped_mul_both_parts (w : width) (pole : Z) (a b : interval * interval) : wrapped :=
  let a0 := wrapped_mul_cut pole (fst a) in
  let a1 := wrapped_mul_cut pole (snd a) in
  let b0 := wrapped_mul_cut pole (fst b) in
  let b1 := wrapped_mul_cut pole (snd b) in
  wrapped_join_four w
    (wrapped_mul_parts w a0 b0) (wrapped_mul_parts w a0 b1)
    (wrapped_mul_parts w a1 b0) (wrapped_mul_parts w a1 b1).

Local Lemma wrapped_mul_both_parts_sound w pole a b x y :
  (gamma interval_gamma (fst a) x \/ gamma interval_gamma (snd a) x) ->
  (gamma interval_gamma (fst b) y \/ gamma interval_gamma (snd b) y) ->
  wrapped_gamma w (wrapped_mul_both_parts w pole a b) (wrap w (x * y)).
Proof.
  intros Hx Hy. unfold wrapped_mul_both_parts. apply wrapped_join_four_sound.
  destruct Hx as [Hx|Hx]; destruct Hy as [Hy|Hy].
  - left. apply wrapped_mul_parts_sound; now apply wrapped_mul_cut_sound.
  - right; left. apply wrapped_mul_parts_sound; now apply wrapped_mul_cut_sound.
  - right; right; left. apply wrapped_mul_parts_sound; now apply wrapped_mul_cut_sound.
  - right; right; right. apply wrapped_mul_parts_sound; now apply wrapped_mul_cut_sound.
Qed.

Definition wrapped_mul (w : width) (a b : wrapped) : wrapped :=
  let unsigned := wrapped_mul_both_parts w (half w) (wrapped_parts w a) (wrapped_parts w b) in
  let signed := wrapped_mul_both_parts w 0 (wrapped_signed_parts w a) (wrapped_signed_parts w b) in
  if wrapped_size w unsigned <=? wrapped_size w signed then unsigned else signed.

(** Both signed and unsigned pole-cut product candidates contain every modular product. *)
Theorem wrapped_mul_sound w a b x y :
  wrapped_gamma w a x -> wrapped_gamma w b y ->
  wrapped_gamma w (wrapped_mul w a b) (wmul w x y).
Proof.
  intros Hx Hy. unfold wrapped_mul.
  destruct (wrapped_size w _ <=? wrapped_size w _) eqn:Hsize.
  - rewrite wmul_value. apply wrapped_mul_both_parts_sound.
    + apply wrapped_parts_spec in Hx. unfold interval_pgamma in Hx. tauto.
    + apply wrapped_parts_spec in Hy. unfold interval_pgamma in Hy. tauto.
  - rewrite wmul_signed. apply wrapped_mul_both_parts_sound;
      now apply wrapped_signed_parts_sound.
Qed.

Definition wrapped_signed_piece_raw (division : bool) (w : width) (a b : interval) : wrapped :=
  match interval_sign w a, interval_sign w b with
  | Some sa, Some sb =>
    let aa := if sa then interval_neg w a else a in
    let bb := if sb then interval_neg w b else b in
    let magnitude := wrapped_of_interval w
      (if division then interval_udiv w aa bb else interval_urem w aa bb) in
    if (if division then xorb sa sb else sa) then wrapped_neg w magnitude else magnitude
  | _, _ => WFull
  end.

Local Lemma wrapped_signed_piece_raw_sound division w a b x y :
  interval_pgamma w a x -> interval_pgamma w b y ->
  wrapped_gamma w (wrapped_signed_piece_raw division w a b)
    (if division then wsdiv w x y else wsrem w x y).
Proof.
  intros Ha Hb. unfold wrapped_signed_piece_raw.
  destruct (interval_sign w a) as [sa|] eqn:Hsa;
    destruct (interval_sign w b) as [sb|] eqn:Hsb;
    try (destruct division; [apply wsdiv_is_word|apply wsrem_is_word]).
  pose proof (interval_sign_sound w a x sa Ha Hsa) as Hx.
  pose proof (interval_sign_sound w b y sb Hb Hsb) as Hy.
  destruct division; destruct sa, sb; rewrite ?wsdiv_value, ?wsrem_value, Hx, Hy;
    cbn [xorb]; repeat rewrite wneg_value;
    try apply wrapped_neg_sound; apply wrapped_interval_value_sound;
    first [apply interval_udiv_sound|apply interval_urem_sound];
    try apply interval_neg_sound; assumption.
Qed.

Definition wrapped_signed_piece (division : bool) (w : width) (a b : interval) : wrapped :=
  match a, b with
  | IBot, _ | _, IBot => WBot
  | _, _ => wrapped_signed_piece_raw division w a b
  end.

(** Empty pole pieces contribute no outcomes and every nonempty signed piece is sound. *)
Theorem wrapped_signed_piece_sound division w a b x y :
  interval_pgamma w a x -> interval_pgamma w b y ->
  wrapped_gamma w (wrapped_signed_piece division w a b)
    (if division then wsdiv w x y else wsrem w x y).
Proof.
  destruct a as [|lo hi], b as [|lo' hi']; intros Ha Hb;
    try (exact (False_rect _ (proj2 Ha))); try (exact (False_rect _ (proj2 Hb))).
  apply wrapped_signed_piece_raw_sound; assumption.
Qed.

Definition wrapped_project (target source : width) (q : wrapped) : wrapped :=
  let pieces := wrapped_parts source q in
  wrapped_join target
    (wrapped_of_interval target (fst pieces)) (wrapped_of_interval target (snd pieces)).

(** Width projection retains the wrapped value of every represented source word. *)
Theorem wrapped_project_sound target source q z :
  wrapped_gamma source q z ->
  wrapped_gamma target (wrapped_project target source q) (wrap target z).
Proof.
  intro Hq. apply wrapped_parts_spec in Hq.
  unfold wrapped_project. apply wrapped_join_sound. destruct Hq as [[_ Hq]|[_ Hq]].
  - left. now apply wrapped_of_interval_sound.
  - right. now apply wrapped_of_interval_sound.
Qed.

Definition wrapped_pole_cut (w : width) (a : interval) : interval * interval :=
  (interval_meet a (Itv (Fin 0) (Fin (half w - 1))),
   interval_meet a (Itv (Fin (half w)) (Fin (modulus w - 1)))).

(** Cutting at the signed pole retains every normalized interval value. *)
Theorem wrapped_pole_cut_sound w a z :
  interval_pgamma w a z ->
  interval_pgamma w (fst (wrapped_pole_cut w a)) z \/
  interval_pgamma w (snd (wrapped_pole_cut w a)) z.
Proof.
  intro Ha. pose proof (proj1 Ha) as Hword.
  unfold wrapped_pole_cut. cbn [fst snd].
  destruct (Z_lt_ge_dec z (half w)) as [Hlow|Hhigh].
  - left. apply interval_meet_sound; [exact Ha|].
    split; [exact Hword|]. cbn [interval_gamma gamma bound_leb].
    split; apply Z.leb_le; destruct Hword; lia.
  - right. apply interval_meet_sound; [exact Ha|].
    split; [exact Hword|]. cbn [interval_gamma gamma bound_leb].
    split; apply Z.leb_le; destruct Hword; lia.
Qed.
