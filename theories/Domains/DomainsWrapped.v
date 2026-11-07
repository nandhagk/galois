(** * Circular word intervals

    Circular arcs represent inclusive contiguous sets of words across either numeric pole.
    For example, the eight-bit arc [250,3] contains 255 and zero.
    Builds on: public Bits word equations and LatticeConcrete. *)

From Stdlib Require Import ZArith List Bool Lia.
From Galois.Lattice Require Import LatticeCore LatticeConcrete.
From Galois.Bits Require Import BitsWord.

Local Open Scope Z_scope.

Inductive wrapped : Type :=
  | WBot
  | WFull
  | WItv (lo hi : Z).

Definition wrapped_offset (w : width) (origin x : Z) : Z :=
  (x - origin) mod modulus w.

Definition wrapped_size (w : width) (a : wrapped) : Z :=
  match a with
  | WBot => 0
  | WFull => modulus w
  | WItv lo hi => wrapped_offset w lo hi + 1
  end.

(** Arc membership measures clockwise distance from its inclusive lower endpoint. *)
Definition wrapped_gamma (w : width) (a : wrapped) (z : Z) : Prop :=
  match a with
  | WBot => False
  | WFull => is_word w z
  | WItv lo hi => is_word w z /\ wrapped_offset w lo z <= wrapped_offset w lo hi
  end.

Definition wrapped_norm (w : width) (a : wrapped) : wrapped :=
  match a with
  | WItv lo hi =>
    if wrapped_offset w lo hi =? modulus w - 1
    then WFull else WItv (wrap w lo) (wrap w hi)
  | _ => a
  end.

(** Clockwise offsets lie in the unsigned word range. *)
Theorem wrapped_offset_range w c x : 0 <= wrapped_offset w c x < modulus w.
Proof.
  apply Z.mod_pos_bound. apply modulus_pos.
Qed.

(** An endpoint has zero distance from itself. *)
Theorem wrapped_offset_self w c : wrapped_offset w c c = 0.
Proof.
  unfold wrapped_offset. rewrite Z.sub_diag.
  apply Z.mod_0_l. apply modulus_nonzero.
Qed.

(** Normalizing both endpoints leaves their clockwise offset unchanged. *)
Theorem wrapped_offset_wrap w c x :
  wrapped_offset w (wrap w c) (wrap w x) = wrapped_offset w c x.
Proof.
  unfold wrapped_offset. rewrite !wrap_mod. symmetry. apply Zminus_mod.
Qed.

(** Normalizing the observed word leaves its clockwise offset unchanged. *)
Theorem wrapped_offset_word w c x :
  wrapped_offset w c (wrap w x) = wrapped_offset w c x.
Proof.
  unfold wrapped_offset. rewrite !wrap_mod.
  rewrite Zminus_mod, Z.mod_mod by apply modulus_nonzero.
  symmetry. apply Zminus_mod.
Qed.

(** Normalizing the origin leaves its clockwise offset unchanged. *)
Theorem wrapped_offset_origin w c x :
  wrapped_offset w (wrap w c) x = wrapped_offset w c x.
Proof.
  unfold wrapped_offset. rewrite !wrap_mod.
  rewrite Zminus_mod, Z.mod_mod by apply modulus_nonzero.
  symmetry. apply Zminus_mod.
Qed.

(** Clockwise offsets compose by modular addition. *)
Theorem wrapped_offset_add w c a x :
  wrapped_offset w c x =
  (wrapped_offset w c a + wrapped_offset w a x) mod modulus w.
Proof.
  unfold wrapped_offset.
  replace (x - c) with ((a - c) + (x - a)) by ring.
  apply Z.add_mod. apply modulus_nonzero.
Qed.

(** Changing the origin subtracts its old clockwise offset. *)
Theorem wrapped_offset_sub w c a x :
  wrapped_offset w a x =
  (wrapped_offset w c x - wrapped_offset w c a) mod modulus w.
Proof.
  unfold wrapped_offset.
  replace (x - a) with ((x - c) - (a - c)) by ring.
  apply Zminus_mod.
Qed.

(** Advancing by an unsigned offset gives that offset after normalization. *)
Theorem wrapped_offset_step w c k :
  0 <= k < modulus w -> wrapped_offset w c (wrap w (c + k)) = k.
Proof.
  intro Hk. rewrite wrapped_offset_word.
  unfold wrapped_offset. replace (c + k - c) with k by ring.
  apply Z.mod_small. exact Hk.
Qed.

(** Every represented circular value is a normalized word. *)
Theorem wrapped_gamma_word w a z : wrapped_gamma w a z -> is_word w z.
Proof.
  destruct a; cbn; tauto.
Qed.

(** Arc normalization leaves concrete membership unchanged. *)
Theorem wrapped_norm_gamma w a z :
  wrapped_gamma w (wrapped_norm w a) z <-> wrapped_gamma w a z.
Proof.
  destruct a as [| |lo hi]; cbn [wrapped_norm]; try tauto.
  destruct (wrapped_offset w lo hi =? modulus w - 1) eqn:Hfull.
  - apply Z.eqb_eq in Hfull. cbn [wrapped_gamma].
    pose proof (wrapped_offset_range w lo z) as Hrange. split; [|tauto].
    intro Hz. split; [exact Hz|lia].
  - cbn [wrapped_gamma].
    rewrite wrapped_offset_origin, wrapped_offset_wrap. reflexivity.
Qed.

(** Arc normalization leaves cardinality unchanged. *)
Theorem wrapped_norm_size w a : wrapped_size w (wrapped_norm w a) = wrapped_size w a.
Proof.
  destruct a as [| |lo hi]; cbn [wrapped_norm]; try reflexivity.
  destruct (wrapped_offset w lo hi =? modulus w - 1) eqn:Hfull.
  - apply Z.eqb_eq in Hfull. cbn [wrapped_size]. lia.
  - cbn [wrapped_size]. now rewrite wrapped_offset_wrap.
Qed.

(** Every cardinality lies between zero and the word modulus. *)
Theorem wrapped_size_bounds w a : 0 <= wrapped_size w a <= modulus w.
Proof.
  destruct a as [| |lo hi]; cbn [wrapped_size];
    pose proof (modulus_pos w); try lia.
  pose proof (wrapped_offset_range w lo hi). lia.
Qed.

Definition wrapped_leb (w : width) (a b : wrapped) : bool :=
  match a, b with
  | WBot, _ => true
  | _, WFull => true
  | _, WBot => false
  | WFull, WItv lo hi => wrapped_offset w lo hi =? modulus w - 1
  | WItv a b, WItv c d =>
    (wrapped_offset w c d =? modulus w - 1) ||
    (wrapped_offset w c a + wrapped_offset w a b <=? wrapped_offset w c d)
  end.

Local Lemma wrapped_arc_inclusion w a b c d :
  (forall z, is_word w z -> wrapped_offset w a z <= wrapped_offset w a b ->
    wrapped_offset w c z <= wrapped_offset w c d) <->
  wrapped_offset w c d = modulus w - 1 \/
  wrapped_offset w c a + wrapped_offset w a b <= wrapped_offset w c d.
Proof.
  pose proof (wrapped_offset_range w a b) as Hab.
  pose proof (wrapped_offset_range w c d) as Hcd.
  pose proof (wrapped_offset_range w c a) as Hca.
  split.
  - intro Hincl. destruct (Z.eq_dec (wrapped_offset w c d) (modulus w - 1))
      as [Hfull|Hproper]; [now left|right].
    pose proof (Hincl (wrap w a) (wrap_is_word w a)) as Hstart.
    rewrite wrapped_offset_word, wrapped_offset_self in Hstart.
    specialize (Hstart ltac:(lia)).
    assert (Hsum : wrapped_offset w c a + wrapped_offset w a b < modulus w).
    { destruct (Z_lt_ge_dec (wrapped_offset w c a + wrapped_offset w a b)
        (modulus w)) as [Hlt|Hge]; [exact Hlt|].
      set (k := modulus w - 1 - wrapped_offset w c a).
      assert (Hk : 0 <= k < modulus w) by (unfold k; lia).
      specialize (Hincl (wrap w (a + k)) (wrap_is_word w (a + k))).
      rewrite wrapped_offset_step in Hincl by exact Hk.
      specialize (Hincl ltac:(unfold k; lia)).
      rewrite (wrapped_offset_add w c a), wrapped_offset_step in Hincl by exact Hk.
      replace (wrapped_offset w c a + k) with (modulus w - 1) in Hincl
        by (unfold k; ring).
      rewrite Z.mod_small in Hincl by lia. lia. }
    pose proof (Hincl (wrap w b) (wrap_is_word w b)) as Hend.
    rewrite !wrapped_offset_word in Hend. specialize (Hend ltac:(lia)).
    rewrite (wrapped_offset_add w c a b), Z.mod_small in Hend by lia. exact Hend.
  - intros [Hfull|Hsum] z Hz Haz.
    + pose proof (wrapped_offset_range w c z). lia.
    + pose proof (wrapped_offset_range w a z).
      rewrite (wrapped_offset_add w c a z), Z.mod_small; lia.
Qed.

(** Boolean containment agrees with inclusion of concrete circular word sets. *)
Theorem wrapped_leb_spec w left right :
  wrapped_leb w left right = true <->
  forall z, wrapped_gamma w left z -> wrapped_gamma w right z.
Proof.
  destruct left as [| |a b], right as [| |c d]; cbn [wrapped_leb wrapped_gamma];
    try (split; [intros; tauto|intros; reflexivity]).
  - split; [discriminate|intro Hempty].
    exfalso. exact (Hempty 0 (zero_is_word w)).
  - rewrite Z.eqb_eq. split.
    + intros Hfull z Hz. split; [exact Hz|].
      pose proof (wrapped_offset_range w c z). lia.
    + intro Hall.
      specialize (Hall (wrap w (c + (modulus w - 1)))
        (wrap_is_word w (c + (modulus w - 1)))).
      destruct Hall as [_ Hlast].
      rewrite wrapped_offset_step in Hlast by (pose proof (modulus_pos w); lia).
      pose proof (wrapped_offset_range w c d). lia.
  - split; [discriminate|intro Hempty].
    exfalso. apply (Hempty (wrap w a)). split; [apply wrap_is_word|].
    rewrite wrapped_offset_word, wrapped_offset_self.
    pose proof (wrapped_offset_range w a b). lia.
  - rewrite Bool.orb_true_iff, Z.eqb_eq, Z.leb_le, <- wrapped_arc_inclusion.
    split.
    + intros Hincl z [Hz Haz]. split; [exact Hz|]. now apply Hincl.
    + intros Hincl z Hz Haz. apply (Hincl z). split; assumption.
Qed.

(** Containment is reflexive. *)
Theorem wrapped_leb_refl w a : wrapped_leb w a a = true.
Proof.
  apply wrapped_leb_spec. tauto.
Qed.

(** Containment is transitive. *)
Theorem wrapped_leb_trans w a b c :
  wrapped_leb w a b = true -> wrapped_leb w b c = true -> wrapped_leb w a c = true.
Proof.
  intros Hab Hbc. apply wrapped_leb_spec.
  pose proof (proj1 (wrapped_leb_spec w a b) Hab) as Hab_gamma.
  pose proof (proj1 (wrapped_leb_spec w b c) Hbc) as Hbc_gamma. auto.
Qed.

(** Normalization gives equivalent arcs in both containment directions. *)
Theorem wrapped_norm_leb w a :
  wrapped_leb w a (wrapped_norm w a) = true /\
  wrapped_leb w (wrapped_norm w a) a = true.
Proof.
  split; apply wrapped_leb_spec; intros z Hz.
  - exact (proj2 (wrapped_norm_gamma w a z) Hz).
  - exact (proj1 (wrapped_norm_gamma w a z) Hz).
Qed.

Definition wrapped_cover (w : width) (a b candidate : wrapped) : bool :=
  wrapped_leb w a candidate && wrapped_leb w b candidate.

Definition wrapped_choose (w : width) (a b first second : wrapped) : wrapped :=
  if wrapped_cover w a b first then
    if wrapped_cover w a b second then
      if wrapped_size w first <=? wrapped_size w second then first else second
    else first
  else if wrapped_cover w a b second then second else WFull.

Definition wrapped_join (w : width) (a b : wrapped) : wrapped :=
  wrapped_norm w
    (if wrapped_leb w a b then b else
     if wrapped_leb w b a then a else
     match a, b with
     | WItv lo hi, WItv lo' hi' =>
       wrapped_choose w a b (WItv lo hi') (WItv lo' hi)
     | _, _ => WFull
     end).

(** Containment cannot decrease cardinality. *)
Theorem wrapped_size_monotone w left right :
  wrapped_leb w left right = true -> wrapped_size w left <= wrapped_size w right.
Proof.
  intro Hle.
  pose proof (wrapped_size_bounds w left) as Ha.
  pose proof (wrapped_size_bounds w right) as Hb.
  destruct left as [| |a b], right as [| |c d];
    cbn [wrapped_leb wrapped_size] in *; try discriminate;
    try (apply Z.eqb_eq in Hle); try lia.
  apply Bool.orb_true_iff in Hle as [Hfull|Hspan].
  - apply Z.eqb_eq in Hfull. lia.
  - apply Z.leb_le in Hspan. pose proof (wrapped_offset_range w c a). lia.
Qed.

Local Lemma wrapped_choose_cover w a b first second :
  wrapped_cover w a b (wrapped_choose w a b first second) = true.
Proof.
  unfold wrapped_choose.
  destruct (wrapped_cover w a b first) eqn:Hfirst;
    destruct (wrapped_cover w a b second) eqn:Hsecond;
    try (destruct (wrapped_size w first <=? wrapped_size w second)); try assumption.
  all: unfold wrapped_cover; destruct a, b; reflexivity.
Qed.

Local Lemma wrapped_choose_size w a b first second target :
  (wrapped_cover w a b first = true /\ wrapped_size w first <= target) \/
  (wrapped_cover w a b second = true /\ wrapped_size w second <= target) ->
  wrapped_size w (wrapped_choose w a b first second) <= target.
Proof.
  intro Hcandidate. unfold wrapped_choose.
  destruct (wrapped_cover w a b first) eqn:Hfirst;
    destruct (wrapped_cover w a b second) eqn:Hsecond;
    try (destruct (wrapped_size w first <=? wrapped_size w second) eqn:Hsize);
    try (apply Z.leb_le in Hsize); try (apply Z.leb_gt in Hsize);
    destruct Hcandidate as [[Hcandidate Hbound]|[Hcandidate Hbound]]; try discriminate; lia.
Qed.

(** Candidate-cover join contains both inputs. *)
Theorem wrapped_join_cover w a b : wrapped_cover w a b (wrapped_join w a b) = true.
Proof.
  unfold wrapped_cover. apply Bool.andb_true_iff.
  unfold wrapped_join.
  destruct (wrapped_leb w a b) eqn:Hab.
  - split.
    + eapply wrapped_leb_trans; [exact Hab|apply wrapped_norm_leb].
    + apply wrapped_norm_leb.
  - destruct (wrapped_leb w b a) eqn:Hba.
    + split.
      * apply wrapped_norm_leb.
      * eapply wrapped_leb_trans; [exact Hba|apply wrapped_norm_leb].
    + assert (Hcover : wrapped_cover w a b
        (match a, b with
         | WItv lo hi, WItv lo' hi' =>
           wrapped_choose w a b (WItv lo hi') (WItv lo' hi)
         | _, _ => WFull
         end) = true).
      { destruct a, b; try reflexivity. apply wrapped_choose_cover. }
      apply Bool.andb_true_iff in Hcover as [Hleft Hright].
      split; eapply wrapped_leb_trans; try eassumption; apply wrapped_norm_leb.
Qed.

(** Offsets compose as ordinary addition when the sum does not wrap. *)
Theorem wrapped_offset_linear w c a x :
  wrapped_offset w c a + wrapped_offset w a x < modulus w ->
  wrapped_offset w c x = wrapped_offset w c a + wrapped_offset w a x.
Proof.
  intro Hbound. rewrite (wrapped_offset_add w c a x).
  apply Z.mod_small. pose proof (wrapped_offset_range w c a).
  pose proof (wrapped_offset_range w a x). lia.
Qed.

(** Ordered offsets subtract without modular wraparound. *)
Theorem wrapped_offset_difference w c a x :
  wrapped_offset w c a <= wrapped_offset w c x ->
  wrapped_offset w a x = wrapped_offset w c x - wrapped_offset w c a.
Proof.
  intro Hle. rewrite (wrapped_offset_sub w c a x).
  apply Z.mod_small. pose proof (wrapped_offset_range w c a).
  pose proof (wrapped_offset_range w c x). lia.
Qed.

Local Lemma wrapped_candidate_size w a b c d e f :
  wrapped_offset w e a + wrapped_offset w a b <= wrapped_offset w e f ->
  wrapped_offset w e c + wrapped_offset w c d <= wrapped_offset w e f ->
  wrapped_offset w e a <= wrapped_offset w e c ->
  wrapped_offset w e a + wrapped_offset w a b <=
    wrapped_offset w e c + wrapped_offset w c d ->
  wrapped_cover w (WItv a b) (WItv c d) (WItv a d) = true /\
  wrapped_size w (WItv a d) <= wrapped_size w (WItv e f).
Proof.
  intros Hab Hcd Hstart Hend.
  pose proof (wrapped_offset_range w e f) as Hspan.
  pose proof (wrapped_offset_range w e a) as Ha.
  pose proof (wrapped_offset_range w e c) as Hc.
  pose proof (wrapped_offset_range w c d) as Hcd_range.
  assert (Hd : wrapped_offset w e d = wrapped_offset w e c + wrapped_offset w c d).
  { apply wrapped_offset_linear. lia. }
  assert (Had : wrapped_offset w a d =
      wrapped_offset w e c + wrapped_offset w c d - wrapped_offset w e a).
  { rewrite (wrapped_offset_difference w e a d) by lia. lia. }
  assert (Hac : wrapped_offset w a c = wrapped_offset w e c - wrapped_offset w e a).
  { apply wrapped_offset_difference. exact Hstart. }
  split.
  - unfold wrapped_cover. apply Bool.andb_true_iff. split;
      cbn [wrapped_leb]; apply Bool.orb_true_iff; right; apply Z.leb_le.
    + rewrite wrapped_offset_self, Had. lia.
    + rewrite Hac, Had. lia.
  - cbn [wrapped_size]. rewrite Had. lia.
Qed.

Local Lemma wrapped_candidate_exists w a b c d e f :
  wrapped_offset w e f <> modulus w - 1 ->
  wrapped_leb w (WItv a b) (WItv e f) = true ->
  wrapped_leb w (WItv c d) (WItv e f) = true ->
  wrapped_leb w (WItv a b) (WItv c d) = false ->
  wrapped_leb w (WItv c d) (WItv a b) = false ->
  (wrapped_cover w (WItv a b) (WItv c d) (WItv a d) = true /\
   wrapped_size w (WItv a d) <= wrapped_size w (WItv e f)) \/
  (wrapped_cover w (WItv a b) (WItv c d) (WItv c b) = true /\
   wrapped_size w (WItv c b) <= wrapped_size w (WItv e f)).
Proof.
  intros Hproper Hac Hbc Hab Hba.
  cbn [wrapped_leb] in Hac, Hbc.
  destruct (wrapped_offset w e f =? modulus w - 1) eqn:Hfull.
  - apply Z.eqb_eq in Hfull. contradiction.
  - cbn in Hac, Hbc. apply Z.leb_le in Hac, Hbc.
    destruct (Z_le_gt_dec (wrapped_offset w e a) (wrapped_offset w e c))
      as [Hstart|Hstart].
    + left. apply wrapped_candidate_size; try assumption.
      destruct (Z_le_gt_dec (wrapped_offset w e a + wrapped_offset w a b)
        (wrapped_offset w e c + wrapped_offset w c d)) as [Hend|Hend]; [exact Hend|].
      assert (Hca : wrapped_offset w a c = wrapped_offset w e c - wrapped_offset w e a)
        by (apply wrapped_offset_difference; exact Hstart).
      assert (Hcontra : wrapped_leb w (WItv c d) (WItv a b) = true).
      { cbn [wrapped_leb]. apply Bool.orb_true_iff. right. apply Z.leb_le. lia. }
      congruence.
    + right.
      assert (Hend : wrapped_offset w e c + wrapped_offset w c d <=
          wrapped_offset w e a + wrapped_offset w a b).
      { destruct (Z_le_gt_dec (wrapped_offset w e c + wrapped_offset w c d)
          (wrapped_offset w e a + wrapped_offset w a b)) as [Hend|Hend]; [exact Hend|].
        assert (Hac' : wrapped_offset w c a = wrapped_offset w e a - wrapped_offset w e c)
          by (apply wrapped_offset_difference; lia).
        assert (Hcontra : wrapped_leb w (WItv a b) (WItv c d) = true).
        { cbn [wrapped_leb]. apply Bool.orb_true_iff. right. apply Z.leb_le. lia. }
        congruence. }
      destruct (wrapped_candidate_size w c d a b e f Hbc Hac ltac:(lia) Hend)
        as [Hcover Hsize]. split; [|exact Hsize].
      unfold wrapped_cover in *. now rewrite Bool.andb_comm.
Qed.

Local Lemma wrapped_join_size w left right target :
  wrapped_leb w left target = true -> wrapped_leb w right target = true ->
  wrapped_size w (wrapped_join w left right) <= wrapped_size w target.
Proof.
  intros Hac Hbc. unfold wrapped_join. rewrite wrapped_norm_size.
  destruct (wrapped_leb w left right) eqn:Hab.
  - now apply wrapped_size_monotone.
  - destruct (wrapped_leb w right left) eqn:Hba.
    + now apply wrapped_size_monotone.
    + destruct left as [| |a b], right as [| |c d];
        cbn [wrapped_leb] in Hab, Hba; try discriminate.
      destruct target as [| |e f].
      * discriminate.
      * apply wrapped_size_bounds.
      * destruct (Z.eq_dec (wrapped_offset w e f) (modulus w - 1)) as [Hfull|Hproper].
        -- pose proof (wrapped_size_bounds w
             (wrapped_choose w (WItv a b) (WItv c d) (WItv a d) (WItv c b))).
           cbn [wrapped_size]. lia.
        -- apply wrapped_choose_size.
           exact (wrapped_candidate_exists w a b c d e f Hproper Hac Hbc Hab Hba).
Qed.

Definition wrapped_double (w : width) (a : wrapped) : wrapped :=
  match a with
  | WBot => WBot
  | WFull => WFull
  | WItv lo hi =>
    let size := wrapped_size w a in
    if modulus w <=? 3 * size then WFull
    else wrapped_norm w (WItv (lo - size) (hi + size))
  end.

Definition wrapped_widen (w : width) (a b : wrapped) : wrapped :=
  if wrapped_leb w b a then wrapped_norm w a
  else wrapped_join w (wrapped_double w a) b.

Definition wrapped_narrow (w : width) (a b : wrapped) : wrapped :=
  match wrapped_norm w a with
  | WFull => wrapped_norm w b
  | _ => wrapped_norm w a
  end.

Local Lemma wrapped_expand_span w lo hi size :
  wrapped_offset w (lo - size) (hi + size) =
  (wrapped_offset w lo hi + 2 * size) mod modulus w.
Proof.
  unfold wrapped_offset.
  replace (hi + size - (lo - size)) with ((hi - lo) + 2 * size) by ring.
  symmetry. apply Z.add_mod_idemp_l. apply modulus_nonzero.
Qed.

Local Lemma wrapped_expand_size w lo hi :
  let size := wrapped_size w (WItv lo hi) in
  3 * size < modulus w ->
  wrapped_size w (WItv (lo - size) (hi + size)) = 3 * size.
Proof.
  intros size Hbound. cbn [wrapped_size]. rewrite wrapped_expand_span.
  pose proof (wrapped_offset_range w lo hi). unfold size, wrapped_size in *.
  rewrite Z.mod_small by lia. lia.
Qed.

(** Expanding an arc covers its original clockwise range. *)
Theorem wrapped_double_upper w a : wrapped_leb w a (wrapped_double w a) = true.
Proof.
  destruct a as [| |lo hi]; cbn [wrapped_double]; try reflexivity.
  set (size := wrapped_size w (WItv lo hi)).
  destruct (modulus w <=? 3 * size) eqn:Hfull; [reflexivity|].
  apply Z.leb_gt in Hfull.
  eapply (wrapped_leb_trans w _ (WItv (lo - size) (hi + size))).
  2: exact (proj1 (wrapped_norm_leb w (WItv (lo - size) (hi + size)))).
  cbn [wrapped_leb]. apply Bool.orb_true_iff. right. apply Z.leb_le.
  rewrite wrapped_expand_span.
  pose proof (wrapped_offset_range w lo hi) as Hspan.
  assert (Hsize : size = wrapped_offset w lo hi + 1) by reflexivity.
  assert (Hstart : wrapped_offset w (lo - size) lo = size).
  { unfold wrapped_offset. replace (lo - (lo - size)) with size by ring.
    apply Z.mod_small. lia. }
  rewrite Hstart, Z.mod_small by lia. lia.
Qed.

(** Expansion triples cardinality until the full word circle is reached. *)
Theorem wrapped_double_size w a :
  wrapped_size w (wrapped_double w a) =
  Z.min (modulus w) (3 * wrapped_size w a).
Proof.
  destruct a as [| |lo hi]; cbn [wrapped_double].
  - cbn [wrapped_size]. pose proof (modulus_pos w). lia.
  - cbn [wrapped_size]. pose proof (modulus_pos w). lia.
  - destruct (modulus w <=? 3 * wrapped_size w (WItv lo hi)) eqn:Hfull.
    + apply Z.leb_le in Hfull. cbn [wrapped_size] in *. lia.
    + apply Z.leb_gt in Hfull. rewrite wrapped_norm_size, wrapped_expand_size by exact Hfull.
      lia.
Qed.

(** Circular lattices use cardinality-minimal covers and expanding widening. *)
Definition wrapped_lattice (w : width) : lattice wrapped :=
  of_pure (wrapped_leb w) WBot (wrapped_join w) (wrapped_widen w) (wrapped_narrow w).

(** Circular intervals satisfy all weak lattice and widening bounds. *)
Theorem wrapped_laws w : lattice_laws (wrapped_lattice w).
Proof.
  constructor; cbn.
  - apply wrapped_leb_refl.
  - apply wrapped_leb_trans.
  - intro a. reflexivity.
  - intros a b. exact (proj1 (proj1 (Bool.andb_true_iff _ _) (wrapped_join_cover w a b))).
  - intros a b. exact (proj2 (proj1 (Bool.andb_true_iff _ _) (wrapped_join_cover w a b))).
  - intros a b. unfold wrapped_widen. destruct (wrapped_leb w b a) eqn:Hba.
    + apply wrapped_norm_leb.
    + eapply wrapped_leb_trans; [apply wrapped_double_upper|].
      exact (proj1 (proj1 (Bool.andb_true_iff _ _) (wrapped_join_cover w _ b))).
  - intros a b. unfold wrapped_widen. destruct (wrapped_leb w b a) eqn:Hba.
    + eapply wrapped_leb_trans; [exact Hba|apply wrapped_norm_leb].
    + exact (proj2 (proj1 (Bool.andb_true_iff _ _) (wrapped_join_cover w _ b))).
  - intros a b Hba. unfold wrapped_narrow.
    destruct (wrapped_norm w a) eqn:Ha.
    + reflexivity.
    + eapply wrapped_leb_trans; [exact (proj2 (wrapped_norm_leb w b))|exact Hba].
    + rewrite <- Ha. exact (proj2 (wrapped_norm_leb w a)).
  - intros a b Hba. unfold wrapped_narrow.
    destruct (wrapped_norm w a) eqn:Ha.
    + rewrite <- Ha. eapply wrapped_leb_trans; [exact Hba|].
      exact (proj1 (wrapped_norm_leb w a)).
    + exact (proj1 (wrapped_norm_leb w b)).
    + rewrite <- Ha. eapply wrapped_leb_trans; [exact Hba|].
      exact (proj1 (wrapped_norm_leb w a)).
Qed.

(** Candidate-cover join has minimum cardinality among every circular upper bound. *)
Theorem wrapped_join_minimal w a b c :
  leb (wrapped_lattice w) a c = true -> leb (wrapped_lattice w) b c = true ->
  wrapped_size w (join (wrapped_lattice w) a b) <= wrapped_size w c.
Proof.
  apply wrapped_join_size.
Qed.

(** Circular containment retains every represented word. *)
Theorem wrapped_gamma_laws w :
  concretisation_laws (wrapped_lattice w) (Concretisation wrapped Z (wrapped_gamma w)).
Proof.
  constructor. intros a b z Hle Hz. exact (proj1 (wrapped_leb_spec w a b) Hle z Hz).
Qed.
