(** * Constant known-bit shifts

    Bit-copy maps transfer facts through shifts and changes of word width.
    For example, shifting a known low one left by two makes bit two a known one.
    Builds on: DomainsTnum and the public Bits shift and signed-bit laws. *)

From Stdlib Require Import ZArith Bool Lia.
From Galois.Bits Require Import BitsWord BitsFun BitsOp BitsTestbit BitsArith.
From Galois.Domains Require Import DomainsTnum.

Local Open Scope Z_scope.

(** Each output bit is either a fixed zero or a copy of one valid source bit. *)
Definition tnum_bit_copy (sw rw : width) (f : Z -> Z) : Prop :=
  forall i, 0 <= i < Zpos rw ->
    (forall x, is_word sw x -> Z.testbit (f x) i = false) \/
    exists j, 0 <= j < Zpos sw /\
      forall x, is_word sw x -> Z.testbit (f x) i = Z.testbit x j.

Definition tnum_map (sw rw : width) (f : Z -> Z) (a : tnum) : tnum :=
  Tnum (wnot rw (f (tnum_max sw a))) (wrap rw (f (tnum_min sw a))).

(** Applying a bit-copy map to the endpoints retains every concrete mapped value. *)
Theorem tnum_map_sound : forall sw rw f a x,
  tnum_bit_copy sw rw f -> is_word sw x -> tnum_gamma sw a x ->
  tnum_gamma rw (tnum_map sw rw f a) (f x).
Proof.
  intros sw rw f a x Hcopy Hx Ha. apply tnum_gamma_bits in Ha.
  destruct Ha as [Hz Ho]. apply tnum_gamma_bits. split; intros i Hi Hbit;
    cbn [tnum_map zeros ones] in Hbit.
  - rewrite tnum_not_bit in Hbit by exact Hi. apply negb_true_iff in Hbit.
    destruct (Hcopy i Hi) as [Hclear|[j [Hj Hsource]]]; [now apply Hclear|].
    rewrite Hsource in Hbit by apply wnot_is_word.
    rewrite Hsource by exact Hx. unfold tnum_max in Hbit.
    rewrite tnum_not_bit in Hbit by exact Hj. apply negb_false_iff in Hbit.
    now apply Hz.
  - rewrite tnum_wrap_bit in Hbit by exact Hi.
    destruct (Hcopy i Hi) as [Hclear|[j [Hj Hsource]]].
    + rewrite Hclear in Hbit by apply wrap_is_word. discriminate.
    + rewrite Hsource in Hbit by apply wrap_is_word. rewrite Hsource by exact Hx.
      unfold tnum_min in Hbit. rewrite tnum_wrap_bit in Hbit by exact Hj. now apply Ho.
Qed.

(** A concrete left shift copies the source suffix and supplies low zero bits. *)
Theorem tnum_shl_copy : forall w k, is_word w k ->
  tnum_bit_copy w w (fun x => wshl w x k).
Proof.
  intros w k Hk i Hi. destruct (k <=? i) eqn:Hsmall.
  - apply Z.leb_le in Hsmall. right. exists (i - k). split; [unfold is_word in Hk; lia|].
    intros x Hx. rewrite testbit_wshl by (try assumption; lia).
    rewrite (proj2 (Z.ltb_lt i (Zpos w)) (proj2 Hi)),
      (proj2 (Z.leb_le k i) Hsmall). reflexivity.
  - left. intros x Hx. rewrite testbit_wshl by (try assumption; lia).
    rewrite Hsmall, andb_false_r. reflexivity.
Qed.

(** A logical right shift copies the source prefix and supplies high zero bits. *)
Theorem tnum_lshr_copy : forall w k, is_word w k ->
  tnum_bit_copy w w (fun x => wlshr w x k).
Proof.
  intros w k Hk i Hi. destruct (Z_lt_ge_dec (i + k) (Zpos w)) as [Hsmall|Hbig].
  - right. exists (i + k). split; [unfold is_word in Hk; lia|].
    intros x Hx. rewrite testbit_wlshr by (try assumption; lia).
    now rewrite (proj2 (Z.ltb_lt i (Zpos w)) (proj2 Hi)).
  - left. intros x Hx. rewrite testbit_wlshr by (try assumption; lia).
    rewrite (word_bits_high w x (i + k) Hx ltac:(lia)). apply andb_false_r.
Qed.

(** An arithmetic right shift copies source bits and repeats the sign bit. *)
Theorem tnum_ashr_copy : forall w k, is_word w k ->
  tnum_bit_copy w w (fun x => washr w x k).
Proof.
  intros w k Hk i Hi. right. exists (Z.min (i + k) (Zpos w - 1)).
  split; [unfold is_word in Hk; lia|]. intros x Hx.
  rewrite testbit_washr by (try assumption; lia).
  now rewrite (proj2 (Z.ltb_lt i (Zpos w)) (proj2 Hi)).
Qed.

Definition tnum_shift (o : op) (w : width) (a : tnum) (k : Z) : tnum :=
  match word_fun2 o with
  | Some f => tnum_map w w (fun x => f w x k) a
  | None => tnum_top
  end.

(** Each supported constant shift contains the corresponding concrete result. *)
Theorem tnum_shift_sound : forall o w a x k f,
  (o = bvshl \/ o = bvlshr \/ o = bvashr) ->
  word_fun2 o = Some f -> is_word w x -> is_word w k -> tnum_gamma w a x ->
  tnum_gamma w (tnum_shift o w a k) (f w x k).
Proof.
  intros o w a x k f Ho Hf Hx Hk Ha. unfold tnum_shift. rewrite Hf.
  apply (tnum_map_sound w w (fun z => f w z k) a x); try assumption.
  destruct Ho as [Ho|[Ho|Ho]]; subst o; injection Hf as <-.
  - now apply tnum_shl_copy.
  - now apply tnum_lshr_copy.
  - now apply tnum_ashr_copy.
Qed.

(** Zero extension copies low bits and supplies zero in the additional positions. *)
Theorem tnum_zext_copy : forall sw rw, (sw <= rw)%positive ->
  tnum_bit_copy sw rw (fun x => wrap rw x).
Proof.
  intros sw rw Hwidth i Hi. destruct (Z_lt_ge_dec i (Zpos sw)) as [Hlow|Hhigh].
  - right. exists i. split; [lia|]. intros x Hx. now rewrite tnum_wrap_bit by exact Hi.
  - left. intros x Hx. rewrite tnum_wrap_bit by exact Hi.
    apply (word_bits_high sw x i Hx). lia.
Qed.

(** Truncation copies precisely the low result-width bits. *)
Theorem tnum_trunc_copy : forall sw rw, (rw <= sw)%positive ->
  tnum_bit_copy sw rw (fun x => wrap rw x).
Proof.
  intros sw rw Hwidth i Hi. right. exists i. split.
  - apply Pos2Z.pos_le_pos in Hwidth. lia.
  - intros x Hx. now rewrite tnum_wrap_bit by exact Hi.
Qed.

(** Extraction copies its contiguous source slice. *)
Theorem tnum_extract_copy : forall sw rw lo,
  0 <= lo -> Zpos rw + lo <= Zpos sw ->
  tnum_bit_copy sw rw (fun x => wrap rw (x / 2 ^ lo)).
Proof.
  intros sw rw lo Hlo Hwidth i Hi. right. exists (i + lo). split; [lia|].
  intros x Hx. rewrite tnum_wrap_bit by exact Hi. now rewrite Z.div_pow2_bits by lia.
Qed.

(** A scalar left-shift amount saturates at the width before constructing a power. *)
Definition tnum_shl_scalar_value (w : width) (k x : Z) : Z :=
  wshl w x (Z.min k (Zpos w)).

Definition tnum_shl_scalar (w : width) (k : Z) (a : tnum) : tnum :=
  tnum_map w w (tnum_shl_scalar_value w k) a.

(** Saturating a nonnegative left-shift amount retains the concrete scalar result. *)
Theorem tnum_shl_scalar_sound : forall w k a x,
  0 <= k -> is_word w x -> tnum_gamma w a x ->
  tnum_gamma w (tnum_shl_scalar w k a) (tnum_shl_scalar_value w k x).
Proof.
  intros w k a x Hk Hx Ha. apply tnum_map_sound; try assumption.
  apply tnum_shl_copy. apply count_is_word. lia.
Qed.
