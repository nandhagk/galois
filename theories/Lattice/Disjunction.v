(** * Capped disjunction lattices

    Lists denote unions and compare by coverage of every alternative.
    For example, cap one collapses two incomparable flat values to their top.
    Builds on: LatticeSig and Argent time interfaces. *)

From Stdlib Require Import List Bool Arith NArith Lia.
From Argent Require Import Time Tactics Std.
From Galois.Lattice Require Import LatticeSig DisjunctionSig Bounded.
Import List.ListNotations.

Definition cap_predecessor (n : nat) : nat :=
  match n with
  | 0 => 0
  | S k => k
  end.

TimeFun cap_predecessor.

Module DisjunctionCode (L : LATTICE_OPS) (C : CAP) <: DISJUNCTION_OPS L C.
  Definition t := {xs : list L.t | Nat.leb (length xs) C.k = true}.
  Definition raw_leb (xs ys : list L.t) := forallb (fun x => existsb (L.leb x) ys) xs.
  Definition leb (xs ys : t) := raw_leb (proj1_sig xs) (proj1_sig ys).
  Definition bot : t := exist _ [] eq_refl.
  Definition is_bot (xs : t) := match proj1_sig xs with [] => true | _ => false end.
  Definition join_all (xs : list L.t) : L.t :=
    match xs with
    | [] => L.bot
    | x :: rest => fold_left L.join rest x
    end.
  Fixpoint compact_tail (n : nat) (xs : list L.t) : list L.t :=
    match n, xs with
    | S m, x :: rest => x :: compact_tail m rest
    | _, _ => [join_all xs]
    end.
  Definition compact (xs : list L.t) :=
    match C.k with
    | 0 => []
    | S k => if Nat.leb (length xs) (S k) then xs else compact_tail k xs
    end.

  Lemma compact_tail_length n xs : length (compact_tail n xs) <= S n.
  Proof.
    revert xs; induction n as [|n IH]; intros [|x xs]; cbn; try lia.
    specialize (IH xs); lia.
  Qed.

  Lemma compact_inside xs : Nat.leb (length (compact xs)) C.k = true.
  Proof.
    unfold compact; destruct C.k as [|k]; cbn; [reflexivity |].
    destruct (Nat.leb (length xs) (S k)) eqn:Hbound; [exact Hbound |].
    apply Nat.leb_le, compact_tail_length.
  Qed.

  Definition clip (xs : list L.t) : t := exist _ (compact xs) (compact_inside xs).
  Definition join (xs ys : t) := clip (proj1_sig xs ++ proj1_sig ys).
End DisjunctionCode.

Module Disjunction (L : LATTICE) (C : CAP) <: DISJUNCTION L C.
  Include DisjunctionCode L C.

  Lemma raw_leb_spec xs ys : raw_leb xs ys = true <->
    forall x, In x xs -> exists y, In y ys /\ L.leb x y = true.
  Proof.
    unfold raw_leb; rewrite forallb_forall.
    split; intros H x Hin; specialize (H x Hin); now apply existsb_exists in H.
  Qed.

  (** Order compares the projected lists by Hoare coverage. *)
  Lemma leb_spec xs ys : leb xs ys = true <->
    forall x, In x (proj1_sig xs) ->
      exists y, In y (proj1_sig ys) /\ L.leb x y = true.
  Proof.
    apply raw_leb_spec.
  Qed.

  (** Bottom projects to the empty list. *)
  Lemma bot_raw : proj1_sig bot = [].
  Proof. Admitted. (* STUB *)

  (** The bottom test recognizes exactly the empty projected list. *)
  Lemma is_bot_spec xs : is_bot xs = true <-> proj1_sig xs = [].
  Proof. Admitted. (* STUB *)

  (** Joining clips the concatenation of the projected operands. *)
  Lemma join_clip xs ys : join xs ys = clip (proj1_sig xs ++ proj1_sig ys).
  Proof. Admitted. (* STUB *)

  (** Clipping preserves a raw list that already fits the cap. *)
  Lemma clip_small xs : length xs <= C.k -> proj1_sig (clip xs) = xs.
  Proof. Admitted. (* STUB *)

  (** At cap zero clipping discards every raw alternative. *)
  Lemma clip_zero xs : C.k = 0 -> proj1_sig (clip xs) = [].
  Proof. Admitted. (* STUB *)

  Lemma leb_refl xs : leb xs xs = true.
  Proof.
    apply raw_leb_spec; intros x Hin; exists x; split; [exact Hin | apply L.leb_refl].
  Qed.

  Lemma leb_trans xs ys zs : leb xs ys = true -> leb ys zs = true -> leb xs zs = true.
  Proof.
    unfold leb; rewrite !raw_leb_spec; intros Hxy Hyz x Hin.
    destruct (Hxy x Hin) as [y [Hy Hle]], (Hyz y Hy) as [z [Hz Hle']].
    exists z; split; [exact Hz | eapply L.leb_trans; eassumption].
  Qed.

  Lemma bot_least xs : leb bot xs = true.
  Proof. reflexivity. Qed.
  Lemma is_bot_bot : is_bot bot = true.
  Proof. reflexivity. Qed.
  Lemma is_bot_least xs ys : is_bot xs = true -> leb xs ys = true.
  Proof. destruct xs as [[|x xs] H]; cbn; congruence. Qed.

  Local Lemma fold_upper_start xs a : L.leb a (fold_left L.join xs a) = true.
  Proof.
    revert a; induction xs as [|x xs IH]; intro a; cbn.
    - apply L.leb_refl.
    - eapply L.leb_trans; [apply L.join_ub_l | apply IH].
  Qed.
  Local Lemma fold_upper_member xs a x : In x xs ->
    L.leb x (fold_left L.join xs a) = true.
  Proof.
    revert a; induction xs as [|y xs IH]; intros a Hin; cbn in *; [contradiction |].
    destruct Hin as [<- | Hin].
    - eapply L.leb_trans; [apply L.join_ub_r | apply fold_upper_start].
    - apply IH; exact Hin.
  Qed.
  Lemma join_all_upper xs x : In x xs -> L.leb x (join_all xs) = true.
  Proof.
    destruct xs as [|a xs]; cbn; intro Hin; [contradiction |].
    destruct Hin as [<- | Hin]; auto using fold_upper_start, fold_upper_member.
  Qed.
  Local Lemma compact_tail_equation n xs :
    compact_tail n xs = firstn n xs ++ [join_all (skipn n xs)].
  Proof.
    revert xs; induction n as [|n IH]; intros [|x xs]; cbn; auto.
    now rewrite IH.
  Qed.
  Local Lemma compact_covers k xs : C.k = S k -> raw_leb xs (compact xs) = true.
  Proof.
    intro Hcap; unfold compact; rewrite Hcap.
    destruct (Nat.leb (length xs) (S k)); [apply raw_leb_spec; intros x Hin;
      exists x; split; [exact Hin | apply L.leb_refl] |].
    rewrite compact_tail_equation; apply raw_leb_spec; intros x Hin.
    rewrite <- (firstn_skipn k xs) in Hin; apply in_app_iff in Hin.
    destruct Hin as [Hp | Hs].
    - exists x; split; [apply in_app_iff; auto | apply L.leb_refl].
    - exists (join_all (skipn k xs)); split.
      + apply in_app_iff; right; now left.
      + apply join_all_upper; exact Hs.
  Qed.

  (** With a positive cap clipping covers every raw alternative. *)
  Lemma clip_covers xs : 0 < C.k ->
    forall x, In x xs -> exists y, In y (proj1_sig (clip xs)) /\ L.leb x y = true.
  Proof. Admitted. (* STUB *)
  Local Lemma zero_empty (xs : t) : C.k = 0 -> proj1_sig xs = [].
  Proof.
    destruct xs as [[|x xs] Hbound]; cbn; [reflexivity |].
    intro Hcap; rewrite Hcap in Hbound; discriminate.
  Qed.
  Lemma join_ub_l xs ys : leb xs (join xs ys) = true.
  Proof.
    destruct C.k as [|k] eqn:Hcap.
    - unfold leb, join, clip; cbn; rewrite (zero_empty xs Hcap); reflexivity.
    - unfold leb, join, clip; cbn; apply raw_leb_spec; intros x Hin.
      pose proof (compact_covers k (proj1_sig xs ++ proj1_sig ys) Hcap) as Hcover.
      apply (proj1 (raw_leb_spec _ _) Hcover x), in_or_app; now left.
  Qed.
  Lemma join_ub_r xs ys : leb ys (join xs ys) = true.
  Proof.
    destruct C.k as [|k] eqn:Hcap.
    - unfold leb, join, clip; cbn; rewrite (zero_empty ys Hcap); reflexivity.
    - unfold leb, join, clip; cbn; apply raw_leb_spec; intros x Hin.
      pose proof (compact_covers k (proj1_sig xs ++ proj1_sig ys) Hcap) as Hcover.
      apply (proj1 (raw_leb_spec _ _) Hcover x), in_or_app; now right.
  Qed.
End Disjunction.

Module DisjunctionT (L : LATTICE_T) (J : JOIN_SIZE L) (C : CAP)
    <: DISJUNCTION_ALL L J C.
  Include Disjunction L C.
  TimeFun raw_leb.
  TimeFun leb.
  TimeFun is_bot.
  TimeFun join_all.
  TimeFun compact_tail.
  TimeFun compact.
  TimeFun clip.
  TimeFun join.

  Definition size (xs : t) : nat :=
    fold_right (fun a n => (L.size a + 1 + n)%nat) 1 (proj1_sig xs).

  (** Raw alternatives contribute their value sizes and one list-cell unit each. *)
  Local Definition raw_size (xs : list L.t) : nat :=
    fold_right (fun a n => (L.size a + 1 + n)%nat) 0%nat xs.

  (** Each join step can grow both accumulated work and the resulting value. *)
  Local Definition join_growth : N := (2 * (L.c_lat + 1))%N.

  Definition c_lat : N :=
    (64 * ((L.c_lat + 1) * N.of_nat ((C.k + 1) * (C.k + 1)) +
      join_growth ^ N.of_nat (2 * C.k + 2) * N.of_nat (2 * C.k + 2) + 1))%N.
  (** The lattice constant pays for at least one call. *)
  Lemma c_lat_pos : (1 <= c_lat)%N.
  Proof.
    unfold c_lat. nia.
  Qed.

  (** The public size adds one terminal unit to raw alternative size. *)
  Local Lemma size_raw (xs : t) : size xs = raw_size (proj1_sig xs) + 1.
  Proof.
    destruct xs as [xs Hcap]. unfold size, raw_size. cbn [proj1_sig]. clear Hcap.
    induction xs as [|x xs IH]; cbn [fold_right]; lia.
  Qed.

  (** Raw size is additive across concatenation. *)
  Local Lemma raw_size_app xs ys : raw_size (xs ++ ys) = raw_size xs + raw_size ys.
  Proof.
    induction xs as [|x xs IH]; unfold raw_size in *; cbn [app fold_right]; lia.
  Qed.

  (** Raw size is the cell count plus the sum of component sizes. *)
  Local Lemma raw_size_values xs :
    raw_size xs = length xs + fold_right (fun a n => (L.size a + n)%nat) 0%nat xs.
  Proof.
    induction xs as [|x xs IH]; unfold raw_size in *; cbn [length fold_right]; lia.
  Qed.

  (** Every member's size fits within the total raw size. *)
  Local Lemma raw_size_member x xs : In x xs -> L.size x + 1 <= raw_size xs.
  Proof.
    induction xs as [|y ys IH]; cbn [In]; intro Hin; [contradiction|].
    change (L.size x + 1 <= L.size y + 1 + raw_size ys).
    destruct Hin as [<-|Hin]; [lia|]. specialize (IH Hin). lia.
  Qed.

  (** List cells alone never exceed raw alternative size. *)
  Local Lemma raw_size_length xs : length xs <= raw_size xs.
  Proof.
    rewrite raw_size_values. lia.
  Qed.

  (** A memberwise callback budget suffices for existential traversal. *)
  Local Lemma exists_clock_in (f : L.t -> bool) (T_f : L.t -> N) budget xs :
    (forall x, In x xs -> (T_f x <= budget)%N) ->
    (List.T_existsb f T_f xs <= (budget + 2) * N.of_nat (length xs) + 1)%N.
  Proof.
    induction xs as [|x xs IH]; intro Hbound.
    - time_unfold @List.T_existsb. cbn [length]. lia.
    - specialize (IH (fun y Hin => Hbound y (or_intror Hin))).
      pose proof (Hbound x (or_introl eq_refl)) as Hx.
      time_unfold @List.T_existsb; time_simpl.
      destruct (f x); cbn [length]; rewrite ?Nat2N.inj_succ; nia.
  Qed.

  (** A memberwise callback budget suffices for universal traversal. *)
  Local Lemma forall_clock_in (f : L.t -> bool) (T_f : L.t -> N) budget xs :
    (forall x, In x xs -> (T_f x <= budget)%N) ->
    (List.T_forallb f T_f xs <= (budget + 2) * N.of_nat (length xs) + 1)%N.
  Proof.
    induction xs as [|x xs IH]; intro Hbound.
    - time_unfold @List.T_forallb. cbn [length]. lia.
    - specialize (IH (fun y Hin => Hbound y (or_intror Hin))).
      pose proof (Hbound x (or_introl eq_refl)) as Hx.
      time_unfold @List.T_forallb; time_simpl.
      destruct (f x); cbn [length]; rewrite ?Nat2N.inj_succ; nia.
  Qed.

  (** The growth factor reserves at least two units for each join step. *)
  Local Lemma join_growth_positive : (2 <= join_growth)%N.
  Proof.
    unfold join_growth. lia.
  Qed.

  (** A join's clock and output size fit within one multiplicative growth step. *)
  Local Lemma join_step_budget a b tail :
    (1 + L.T_join a b + N.of_nat (L.size (L.join a b)) + tail + 1 <=
      join_growth * (N.of_nat (L.size a) + N.of_nat (L.size b) + tail + 2))%N.
  Proof.
    pose proof (L.T_join_le a b) as Hclock.
    pose proof (J.join_size a b) as Hsize.
    unfold join_growth. repeat rewrite Nat2N.inj_add in *. nia.
  Qed.

  (** The fold budget tracks actual work and the size passed to later joins. *)
  Local Lemma fold_join_clock_size xs : forall a,
    (List.T_fold_left L.join L.T_join xs a +
      N.of_nat (L.size (fold_left L.join xs a)) + 1 <=
      join_growth ^ N.of_nat (length xs + 1) *
        N.of_nat (L.size a + raw_size xs + 1))%N.
  Proof.
    induction xs as [|x xs IH]; intro a.
    - time_unfold @List.T_fold_left. cbn [fold_left length raw_size fold_right].
      rewrite N.pow_1_r. repeat rewrite Nat2N.inj_add.
      pose proof join_growth_positive. nia.
    - specialize (IH (L.join a x)).
      pose proof (join_step_budget a x (N.of_nat (raw_size xs))) as Hstep.
      set (scale := (join_growth ^ N.of_nat (length xs + 1))%N) in *.
      assert (Hscale_positive : (1 <= scale)%N).
      { unfold scale. assert (Hnonzero : join_growth <> 0%N) by
          (pose proof join_growth_positive; lia).
        pose proof (N.pow_nonzero join_growth (N.of_nat (length xs + 1)) Hnonzero).
        lia. }
      pose proof (N.mul_le_mono_l _ _ scale Hstep) as Hscaled.
      pose proof (N.mul_le_mono_r 1 scale (1 + L.T_join a x)%N Hscale_positive) as Hpaid.
      time_unfold @List.T_fold_left. cbn [fold_left length].
      replace (S (length xs) + 1) with (S (length xs + 1)) by lia.
      rewrite Nat2N.inj_succ, N.pow_succ_r'. fold scale.
      set (budget := (N.of_nat (L.size a) + N.of_nat (L.size x) +
        N.of_nat (raw_size xs) + 2)%N) in *.
      assert (Hbudget : N.of_nat (L.size a + raw_size (x :: xs) + 1) = budget).
      { unfold budget, raw_size. cbn [fold_right]. repeat rewrite Nat2N.inj_add. lia. }
      rewrite Hbudget. fold budget in Hscaled.
      replace (join_growth * scale * budget)%N with
        (scale * (join_growth * budget))%N by ring.
      repeat rewrite Nat2N.inj_add in IH.
      repeat rewrite N.mul_add_distr_l in IH, Hscaled, Hpaid.
      rewrite N.mul_1_l in Hpaid. lia.
  Qed.

  (** A nonempty list starts from its first value, so no bottom-size bound is needed. *)
  Local Lemma join_all_clock_size xs : xs <> [] ->
    (T_join_all xs + N.of_nat (L.size (join_all xs)) + 1 <=
      join_growth ^ N.of_nat (length xs + 1) * N.of_nat (raw_size xs + 1))%N.
  Proof.
    destruct xs as [|x xs]; intro Hnonempty; [contradiction|].
    pose proof (fold_join_clock_size xs x) as Hfold.
    change (List.T_fold_left L.join L.T_join xs x) with
      (List.T_fold_left L.join (fun a b => L.T_join a b) xs x) in Hfold.
    pose proof join_growth_positive as Hgrowth.
    assert (Hnonzero : join_growth <> 0%N) by lia.
    pose proof (N.pow_nonzero join_growth (N.of_nat (length xs + 1)) Hnonzero) as Hpower.
    time_unfold @T_join_all. cbn [join_all length].
    replace (S (length xs) + 1) with (S (length xs + 1)) by lia.
    rewrite Nat2N.inj_succ, N.pow_succ_r'.
    unfold raw_size in *. cbn [fold_right] in *.
    repeat rewrite Nat2N.inj_add in *. nia.
  Qed.

  (** Order testing takes time bounded by both disjunction sizes. *)
  Lemma T_leb_le : forall a b,
    (T_leb a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Joining takes time bounded by both disjunction sizes. *)
  Lemma T_join_le : forall a b,
    (T_join a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Bottom testing takes time bounded by the disjunction size. *)
  Lemma T_is_bot_le : forall a,
    (T_is_bot a <= c_lat * N.of_nat (size a + 1))%N.
  Proof.
    intros [xs Hcap]. pose proof c_lat_pos as Hpositive.
    time_unfold @T_is_bot; time_simpl. unfold size; cbn [proj1_sig].
    destruct xs; cbn [fold_right]; rewrite ?Nat2N.inj_add; nia.
  Qed.
  (** Clipping charges raw length and component sizes within twice the cap. *)
  Lemma T_clip_le : forall xs, length xs <= 2 * C.k ->
    (T_clip xs <= c_lat * N.of_nat
      (length xs + fold_right (fun a n => (L.size a + n)%nat) 0%nat xs + 1)%nat)%N.
  Proof. Admitted. (* STUB *)
  (** A join has size bounded by the sizes of its operands. *)
  Lemma join_size : forall a b,
    (N.of_nat (size (join a b)) <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
End DisjunctionT.
