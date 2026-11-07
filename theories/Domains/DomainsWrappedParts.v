(** * Linear pieces of circular arcs

    Canonical arcs split at zero into at most two unsigned intervals.
    For example, [250,3] splits into [250,255] and [0,3] at width eight.
    Builds on: DomainsWrapped and DomainsInterval. *)

From Stdlib Require Import ZArith List Bool Lia.
From Galois.Lattice Require Import LatticeCore LatticeConcrete.
From Galois.Bits Require Import BitsWord.
From Galois.Domains Require Import DomainsBound DomainsInterval DomainsWrapped.

Local Open Scope Z_scope.

Definition wrapped_range (w : width) (lo hi : Z) : wrapped :=
  if hi <? lo then WBot else
  if modulus w - 1 <=? hi - lo then WFull else wrapped_norm w (WItv lo hi).

(** Projecting a linear range contains every wrapped integer in that range. *)
Theorem wrapped_range_sound w lo hi z :
  lo <= z <= hi -> wrapped_gamma w (wrapped_range w lo hi) (wrap w z).
Proof.
  intro Hz. unfold wrapped_range.
  destruct (hi <? lo) eqn:Hempty; [apply Z.ltb_lt in Hempty; lia|].
  destruct (modulus w - 1 <=? hi - lo) eqn:Hfull; [apply wrap_is_word|].
  apply Z.leb_gt in Hfull. apply (proj2 (wrapped_norm_gamma w (WItv lo hi) _)).
  split; [apply wrap_is_word|].
  rewrite wrapped_offset_word. unfold wrapped_offset.
  rewrite !Z.mod_small by lia. lia.
Qed.

Definition wrapped_of_interval (w : width) (i : interval) : wrapped :=
  match i with
  | IBot => WBot
  | Itv (Fin lo) (Fin hi) => wrapped_range w lo hi
  | _ => WFull
  end.

(** Linear interval projection contains every represented integer after wrapping. *)
Theorem wrapped_of_interval_sound w i z :
  gamma interval_gamma i z -> wrapped_gamma w (wrapped_of_interval w i) (wrap w z).
Proof.
  destruct i as [|lo hi]; intro Hz; [exact Hz|].
  destruct lo as [|lo|], hi as [|hi|]; cbn [wrapped_of_interval]; try apply wrap_is_word.
  cbn [interval_gamma gamma bound_leb] in Hz.
  destruct Hz as [Hlo Hhi]. apply Z.leb_le in Hlo, Hhi.
  apply wrapped_range_sound. lia.
Qed.

(** A normalized represented interval value is unchanged by circular projection. *)
Theorem wrapped_interval_value_sound w i z :
  interval_pgamma w i z -> wrapped_gamma w (wrapped_of_interval w i) z.
Proof.
  intros [Hword Hz]. rewrite <- (wrap_id w z Hword).
  now apply wrapped_of_interval_sound.
Qed.

Definition wrapped_parts_raw (w : width) (a : wrapped) : interval * interval :=
  match a with
  | WBot => (IBot, IBot)
  | WFull => (interval_top w, IBot)
  | WItv lo hi =>
    let lo' := wrap w lo in
    let hi' := wrap w hi in
    if lo' <=? hi' then (Itv (Fin lo') (Fin hi'), IBot)
    else (Itv (Fin lo') (Fin (modulus w - 1)), Itv (Fin 0) (Fin hi'))
  end.

Definition wrapped_parts (w : width) (a : wrapped) : interval * interval :=
  wrapped_parts_raw w (wrapped_norm w a).

(** Between two normalized words an offset has at most one wraparound. *)
Theorem wrapped_offset_word_cases w c z :
  is_word w c -> is_word w z ->
  wrapped_offset w c z = if c <=? z then z - c else z - c + modulus w.
Proof.
  intros Hc Hz. unfold wrapped_offset.
  destruct (c <=? z) eqn:Hle.
  - apply Z.leb_le in Hle. apply Z.mod_small. destruct Hc, Hz. lia.
  - apply Z.leb_gt in Hle. symmetry. apply Z.mod_unique with (q := -1);
      destruct Hc, Hz; lia.
Qed.

Local Lemma wrapped_arc_normalize_gamma w lo hi z :
  wrapped_gamma w (WItv lo hi) z <->
  wrapped_gamma w (WItv (wrap w lo) (wrap w hi)) z.
Proof.
  cbn [wrapped_gamma]. rewrite wrapped_offset_origin, wrapped_offset_wrap. reflexivity.
Qed.

Local Lemma wrapped_parts_raw_spec w a z :
  wrapped_gamma w a z <->
  interval_pgamma w (fst (wrapped_parts_raw w a)) z \/
  interval_pgamma w (snd (wrapped_parts_raw w a)) z.
Proof.
  destruct a as [| |lo hi].
  - change (False <-> (is_word w z /\ False) \/ (is_word w z /\ False)). tauto.
  - cbn [wrapped_gamma wrapped_parts_raw fst snd interval_pgamma interval_gamma gamma].
    split; [intro Hz; left; now apply interval_top_sound|].
    intros [[Hz _]|[_ Hempty]]; [exact Hz|contradiction].
  - rewrite wrapped_arc_normalize_gamma. cbn [wrapped_parts_raw fst snd].
    pose proof (wrap_is_word w lo) as Hlo.
    pose proof (wrap_is_word w hi) as Hhi.
    destruct (wrap w lo <=? wrap w hi) eqn:Hends;
      cbn [fst snd wrapped_gamma]; unfold interval_pgamma, interval_gamma;
      cbn [gamma bound_leb]; rewrite !Z.leb_le; split.
    + intros [Hz Hoffset]. left. split; [exact Hz|].
      rewrite !wrapped_offset_word_cases in Hoffset by assumption.
      rewrite Hends in Hoffset. apply Z.leb_le in Hends.
      destruct (wrap w lo <=? z) eqn:Hzlo; [apply Z.leb_le in Hzlo|apply Z.leb_gt in Hzlo];
        destruct Hlo, Hhi, Hz; lia.
    + intros [[Hz [Hzlo Hzhi]]|[_ Hempty]]; [|contradiction].
      split; [exact Hz|].
      rewrite !wrapped_offset_word_cases by assumption. rewrite Hends.
      assert (Hlower : (wrap w lo <=? z) = true) by (apply Z.leb_le; exact Hzlo).
      rewrite Hlower. lia.
    + intros [Hz Hoffset].
      rewrite !wrapped_offset_word_cases in Hoffset by assumption. rewrite Hends in Hoffset.
      destruct (wrap w lo <=? z) eqn:Hzlo.
      * apply Z.leb_le in Hzlo. left. split; [exact Hz|]. destruct Hz. lia.
      * apply Z.leb_gt in Hzlo. right. split; [exact Hz|]. destruct Hz. lia.
    + intros [[Hz [Hzlo Hzhi]]|[Hz [Hzlo Hzhi]]]; split; try exact Hz;
        rewrite !wrapped_offset_word_cases by assumption; rewrite Hends;
        destruct (wrap w lo <=? z) eqn:Hzlo';
        try (apply Z.leb_le in Hzlo'); try (apply Z.leb_gt in Hzlo');
        destruct Hlo, Hhi, Hz; apply Z.leb_gt in Hends; lia.
Qed.

(** The two unsigned pieces describe the same concrete set as the original arc. *)
Theorem wrapped_parts_spec w a z :
  wrapped_gamma w a z <->
  interval_pgamma w (fst (wrapped_parts w a)) z \/
  interval_pgamma w (snd (wrapped_parts w a)) z.
Proof.
  unfold wrapped_parts. rewrite <- wrapped_parts_raw_spec.
  symmetry. apply wrapped_norm_gamma.
Qed.

(** Circular normalization is idempotent, including raw full-circle aliases. *)
Theorem wrapped_norm_idempotent w a :
  wrapped_norm w (wrapped_norm w a) = wrapped_norm w a.
Proof.
  destruct a as [| |lo hi]; cbn [wrapped_norm]; try reflexivity.
  destruct (wrapped_offset w lo hi =? modulus w - 1) eqn:Hfull; [reflexivity|].
  cbn [wrapped_norm]. rewrite wrapped_offset_wrap, Hfull, !wrap_wrap. reflexivity.
Qed.

(** The endpoints of a normalized proper arc are normalized words. *)
Theorem wrapped_norm_endpoints w a lo hi :
  wrapped_norm w a = WItv lo hi -> is_word w lo /\ is_word w hi.
Proof.
  destruct a as [| |l h]; cbn [wrapped_norm]; try discriminate.
  destruct (wrapped_offset w l h =? modulus w - 1); [discriminate|].
  intro Hnorm. inversion Hnorm; subst lo hi. split; apply wrap_is_word.
Qed.

(** Normalizing before splitting does not change the unsigned pieces. *)
Theorem wrapped_parts_normalized w a :
  wrapped_parts w (wrapped_norm w a) = wrapped_parts w a.
Proof.
  unfold wrapped_parts. now rewrite wrapped_norm_idempotent.
Qed.

Definition wrapped_join_four (w : width) (a b c d : wrapped) : wrapped :=
  wrapped_join w (wrapped_join w a b) (wrapped_join w c d).

(** A circular join retains either input's concrete words. *)
Theorem wrapped_join_sound w a b z :
  wrapped_gamma w a z \/ wrapped_gamma w b z -> wrapped_gamma w (wrapped_join w a b) z.
Proof.
  intros [Ha|Hb].
  - exact (gamma_monotone (wrapped_gamma_laws w) a _ z
      (join_upper_l (wrapped_laws w) a b) Ha).
  - exact (gamma_monotone (wrapped_gamma_laws w) b _ z
      (join_upper_r (wrapped_laws w) a b) Hb).
Qed.

(** Four-way join retains every case produced by two binary arc cuts. *)
Theorem wrapped_join_four_sound w a b c d z :
  wrapped_gamma w a z \/ wrapped_gamma w b z \/
  wrapped_gamma w c z \/ wrapped_gamma w d z ->
  wrapped_gamma w (wrapped_join_four w a b c d) z.
Proof.
  intro Hcases. unfold wrapped_join_four.
  apply wrapped_join_sound. destruct Hcases as [Ha|[Hb|[Hc|Hd]]].
  - left. apply wrapped_join_sound. now left.
  - left. apply wrapped_join_sound. now right.
  - right. apply wrapped_join_sound. now left.
  - right. apply wrapped_join_sound. now right.
Qed.

Definition wrapped_meet (w : width) (a b : wrapped) : wrapped :=
  let pa := wrapped_parts w a in
  let pb := wrapped_parts w b in
  let candidate := wrapped_join_four w
    (wrapped_of_interval w (interval_meet (fst pa) (fst pb)))
    (wrapped_of_interval w (interval_meet (fst pa) (snd pb)))
    (wrapped_of_interval w (interval_meet (snd pa) (fst pb)))
    (wrapped_of_interval w (interval_meet (snd pa) (snd pb))) in
  if wrapped_leb w candidate a then candidate else wrapped_norm w a.

(** Piecewise intersection retains every word common to both arcs. *)
Theorem wrapped_meet_sound w a b z :
  wrapped_gamma w a z -> wrapped_gamma w b z -> wrapped_gamma w (wrapped_meet w a b) z.
Proof.
  intros Ha Hb. unfold wrapped_meet.
  destruct (wrapped_leb w _ a) eqn:Hleft.
  - pose proof (wrapped_gamma_word w a z Ha) as Hz.
    apply wrapped_parts_spec in Ha. apply wrapped_parts_spec in Hb.
    apply wrapped_join_four_sound.
    destruct Ha as [Ha|Ha]; destruct Hb as [Hb|Hb].
    + left. apply wrapped_interval_value_sound. now apply interval_meet_sound.
    + right; left. apply wrapped_interval_value_sound. now apply interval_meet_sound.
    + right; right; left. apply wrapped_interval_value_sound. now apply interval_meet_sound.
    + right; right; right. apply wrapped_interval_value_sound. now apply interval_meet_sound.
  - exact (proj2 (wrapped_norm_gamma w a z) Ha).
Qed.

(** The guarded intersection is always below its left input. *)
Theorem wrapped_meet_lower_left w a b : wrapped_leb w (wrapped_meet w a b) a = true.
Proof.
  unfold wrapped_meet.
  match goal with
  | |- context [if ?test then _ else _] => destruct test eqn:Hleft
  end.
  - exact Hleft.
  - exact (proj2 (wrapped_norm_leb w a)).
Qed.
