(** * Total signed-bound component order

    Exact reduction makes semantic inclusion decidable for arbitrary raw halves.
    For example, an inverted raw range compares equal to the empty half.
    Builds on: DomainsSignedBounds and LatticeCore. *)

From Stdlib Require Import ZArith Bool Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Lattice Require Import LatticeCore.
From Galois.Bits Require Import BitsWord BitsFun BitsTestbit.
From Galois.Domains Require Import DomainsTnum DomainsSignedBounds.
Import Cost.Notations.

Local Open Scope Z_scope.

(** A feasible half always records the selected concrete sign. *)
Theorem sb_half_word_sign : forall w s h z,
  sb_half_gamma w s h z -> is_word w z /\ msb w z = s.
Proof.
  intros w s [|t lo hi] z Hz;
    unfold sb_half_gamma, sb_bit_gamma, sb_interval_gamma in Hz; tauto.
Qed.

Definition sb_order_c (w : width) (a b : sb_half) : Cost.t bool :=
  match a, b with
  | SBEmpty, _ => Cost.ret true
  | _, SBEmpty => Cost.ret false
  | SBRange ta la ua, SBRange tb lb ub =>
    let* bits := Cost.step ;; leb_c (tnum_lattice w) ta tb in
    Cost.ret (bits && (lb <=? la) && (ua <=? ub))
  end.

Definition sb_order (w : width) (a b : sb_half) : bool :=
  Cost.value (sb_order_c w a b).

(** Raw component comparison uses mask inclusion and inclusive endpoint containment. *)
Theorem sb_order_equation : forall w a b,
  sb_order w a b =
  match a, b with
  | SBEmpty, _ => true
  | _, SBEmpty => false
  | SBRange ta la ua, SBRange tb lb ub =>
    leb (tnum_lattice w) ta tb && (lb <=? la) && (ua <=? ub)
  end.
Proof.
  intros w [|ta la ua] [|tb lb ub]; unfold sb_order, sb_order_c;
    autorewrite with galois_cost; reflexivity.
Qed.

Definition sb_leb_c (w : width) (s : bool) (a b : sb_half) : Cost.t bool :=
  let* a' := sb_reduce_half_c w s a in
  let* b' := sb_reduce_half_c w s b in
  sb_order_c w a' b'.

Definition sb_leb (w : width) (s : bool) (a b : sb_half) : bool :=
  Cost.value (sb_leb_c w s a b).

(** Semantic comparison retains both exact reductions and the component comparison cost. *)
Theorem sb_leb_equation : forall w s a b,
  sb_leb w s a b = sb_order w (sb_reduce_half w s a) (sb_reduce_half w s b).
Proof.
  intros w s a b. unfold sb_leb, sb_leb_c. autorewrite with galois_cost. reflexivity.
Qed.

Lemma sb_order_summary : forall w s S a b,
  sb_summary w S a ->
  (forall x, S x -> sb_half_gamma w s b x) -> sb_order w a b = true.
Proof.
  intros w s S [|ta la ua] [|tb lb ub] Ha Hsub; rewrite sb_order_equation;
    try reflexivity.
  - destruct Ha as [_ [Hlo _]]. specialize (Hsub la Hlo). destruct Hsub. contradiction.
  - destruct Ha as [Hnorm [Hlo [Hhi [Hsound Hbest]]]].
    pose proof (Hsub la Hlo) as Hlower. pose proof (Hsub ua Hhi) as Hupper.
    apply sb_half_gamma_range in Hlower, Hupper.
    rewrite !andb_true_iff, !Z.leb_le. split; [split|]; try tauto.
    apply Hbest. intros x Hx. pose proof (Hsub x Hx) as Hout.
    apply sb_half_gamma_range in Hout. tauto.
Qed.

(** Raw component inclusion preserves the half meaning without a normalization premise. *)
Theorem sb_order_sound : forall w s a b z,
  sb_order w a b = true -> sb_half_gamma w s a z -> sb_half_gamma w s b z.
Proof.
  intros w s [|ta la ua] [|tb lb ub] z Hle Hz;
    rewrite sb_order_equation in Hle;
    try discriminate; try (destruct Hz; contradiction).
  rewrite !andb_true_iff, !Z.leb_le in Hle.
  apply sb_half_gamma_range in Hz. apply sb_half_gamma_range.
  destruct Hle as [[Hbits Hlo] Hhi], Hz as [Hw [Hs [Ht Hb]]].
  split; [exact Hw|]. split; [exact Hs|]. split;
    [eapply tnum_gamma_monotone; eassumption|lia].
Qed.

(** Reduced component comparison decides semantic inclusion on the entire raw carrier. *)
Theorem sb_leb_spec : forall w s a b,
  sb_leb w s a b = true <->
  forall z, sb_half_gamma w s a z -> sb_half_gamma w s b z.
Proof.
  intros w s a b. rewrite sb_leb_equation. split.
  - intros Hle z Hz. apply (proj1 (sb_reduce_half_gamma w s b z)).
    eapply sb_order_sound; [exact Hle|]. now apply sb_reduce_half_gamma.
  - intro Hsub. eapply sb_order_summary; [apply sb_reduce_half_summary|].
    intros x Hx. apply sb_reduce_half_gamma. now apply Hsub.
Qed.

Lemma sb_summary_cover : forall w s S a q,
  sb_summary w S a -> (forall x, S x -> sb_half_gamma w s q x) ->
  forall z, sb_half_gamma w s a z -> sb_half_gamma w s q z.
Proof.
  intros w s S a q Hsummary Hsub z Hz. eapply sb_order_sound; [|exact Hz].
  now apply (sb_order_summary w s S).
Qed.

Definition sb_join_c (w : width) (s : bool) (a b : sb_half) : Cost.t sb_half :=
  let* a' := sb_reduce_half_c w s a in
  let* b' := sb_reduce_half_c w s b in
  sb_reduce_half_c w s (sb_merge w a' b').

Definition sb_join (w : width) (s : bool) (a b : sb_half) : sb_half :=
  Cost.value (sb_join_c w s a b).

(** Half join reduces both inputs and their merged component hull. *)
Theorem sb_join_equation : forall w s a b,
  sb_join w s a b =
  sb_reduce_half w s (sb_merge w (sb_reduce_half w s a) (sb_reduce_half w s b)).
Proof.
  intros w s a b. unfold sb_join, sb_join_c. autorewrite with galois_cost. reflexivity.
Qed.

Lemma sb_join_summary : forall w s a b,
  sb_summary w (fun x => sb_half_gamma w s a x \/ sb_half_gamma w s b x)
    (sb_merge w (sb_reduce_half w s a) (sb_reduce_half w s b)).
Proof.
  intros. apply sb_merge_summary; apply sb_reduce_half_summary.
Qed.

(** Half join contains every feasible word of either raw input. *)
Theorem sb_join_upper : forall w s a b z,
  sb_half_gamma w s a z \/ sb_half_gamma w s b z -> sb_half_gamma w s (sb_join w s a b) z.
Proof.
  intros w s a b z Hz. rewrite sb_join_equation. apply sb_reduce_half_gamma.
  pose proof (sb_join_summary w s a b) as Hsummary.
  destruct (sb_merge w (sb_reduce_half w s a) (sb_reduce_half w s b)) as [|t lo hi].
  - exfalso. exact (Hsummary z Hz).
  - destruct Hsummary as [Hnorm [Hlo [Hhi [Hsound Hbest]]]].
    destruct (Hsound z Hz) as [Hw [Ht Hb]]. apply sb_half_gamma_range.
    split; [exact Hw|]. split; [|now split].
    destruct Hz as [Hz|Hz]; exact (proj2 (sb_half_word_sign w s _ z Hz)).
Qed.

(** Half join is least under exact semantic comparison of the raw carrier. *)
Theorem sb_join_least : forall w s a b q,
  sb_leb w s a q = true -> sb_leb w s b q = true -> sb_leb w s (sb_join w s a b) q = true.
Proof.
  intros w s a b q Ha Hb.
  pose proof (proj1 (sb_leb_spec w s a q) Ha) as Hacover.
  pose proof (proj1 (sb_leb_spec w s b q) Hb) as Hbcover.
  apply (proj2 (sb_leb_spec w s (sb_join w s a b) q)).
  intros z Hz. rewrite sb_join_equation, sb_reduce_half_gamma in Hz.
  eapply sb_summary_cover; [apply sb_join_summary| |exact Hz].
  intros x [Hx|Hx]; [now apply Hacover|now apply Hbcover].
Qed.

Definition signed_bounds_leb_c (w : width) (a b : signed_bounds) : Cost.t bool :=
  let* zero := sb_leb_c w false (sb_zero a) (sb_zero b) in
  let* one := sb_leb_c w true (sb_one a) (sb_one b) in
  Cost.ret (zero && one).

Definition signed_bounds_leb (w : width) (a b : signed_bounds) : bool :=
  Cost.value (signed_bounds_leb_c w a b).

(** Payload comparison combines the two semantic half comparisons. *)
Theorem signed_bounds_leb_equation : forall w a b,
  signed_bounds_leb w a b =
  sb_leb w false (sb_zero a) (sb_zero b) && sb_leb w true (sb_one a) (sb_one b).
Proof.
  intros w a b. unfold signed_bounds_leb, signed_bounds_leb_c.
  autorewrite with galois_cost. reflexivity.
Qed.

Definition signed_bounds_join_c (w : width) (a b : signed_bounds) : Cost.t signed_bounds :=
  let* zero := sb_join_c w false (sb_zero a) (sb_zero b) in
  let* one := sb_join_c w true (sb_one a) (sb_one b) in
  Cost.ret (SignedBounds zero one).

Definition signed_bounds_join (w : width) (a b : signed_bounds) : signed_bounds :=
  Cost.value (signed_bounds_join_c w a b).

(** Payload join retains all four input-half searches and the two merged-half searches. *)
Theorem signed_bounds_join_equation : forall w a b,
  signed_bounds_join w a b =
  SignedBounds (sb_join w false (sb_zero a) (sb_zero b))
    (sb_join w true (sb_one a) (sb_one b)).
Proof.
  intros w a b. unfold signed_bounds_join, signed_bounds_join_c.
  autorewrite with galois_cost. reflexivity.
Qed.

(** Payload comparison decides semantic inclusion for arbitrary raw bounds and masks. *)
Theorem signed_bounds_leb_spec : forall w a b,
  signed_bounds_leb w a b = true <->
  forall z, signed_bounds_gamma w a z -> signed_bounds_gamma w b z.
Proof.
  intros w a b. rewrite signed_bounds_leb_equation, andb_true_iff, !sb_leb_spec. split.
  - intros [Hzero Hone] z [Hz|Hz]; [left; now apply Hzero|right; now apply Hone].
  - intro Hsub. split; intros z Hz; specialize (Hsub z);
      destruct (Hsub ltac:(unfold signed_bounds_gamma; tauto)) as [Hout|Hout];
      try exact Hout; apply sb_half_word_sign in Hz, Hout;
      destruct Hz as [_ Hs], Hout as [_ Ht]; congruence.
Qed.

(** Payload join contains every feasible input word. *)
Theorem signed_bounds_join_sound : forall w a b z,
  signed_bounds_gamma w a z \/ signed_bounds_gamma w b z ->
  signed_bounds_gamma w (signed_bounds_join w a b) z.
Proof.
  intros w a b z Hz. rewrite signed_bounds_join_equation.
  unfold signed_bounds_gamma in *. cbn [sb_zero sb_one].
  destruct Hz as [[Hz|Hz]|[Hz|Hz]];
    first [left; apply sb_join_upper; tauto|right; apply sb_join_upper; tauto].
Qed.

(** Payload join is least in the semantic preorder. *)
Theorem signed_bounds_join_least : forall w a b q,
  signed_bounds_leb w a q = true -> signed_bounds_leb w b q = true ->
  signed_bounds_leb w (signed_bounds_join w a b) q = true.
Proof.
  intros w a b q Ha Hb. rewrite signed_bounds_leb_equation in *.
  rewrite signed_bounds_join_equation. cbn [sb_zero sb_one].
  apply andb_true_iff in Ha, Hb. apply andb_true_iff. split; apply sb_join_least; tauto.
Qed.

(** This base dictionary exposes legacy join widening for the explicit WidenJoin choice. *)
Definition signed_bounds_join_lattice (w : width) : lattice signed_bounds :=
  {| leb_c := signed_bounds_leb_c w;
     join_c := signed_bounds_join_c w;
     widen_c := signed_bounds_join_c w;
     narrow_c := fun a _ => signed_bounds_reduce_c w a;
     bot := SignedBounds SBEmpty SBEmpty |}.

(** The base dictionary obeys total weak laws without assuming raw inputs are normalized. *)
Theorem signed_bounds_join_laws : forall w, lattice_laws (signed_bounds_join_lattice w).
Proof.
  intro w. constructor.
  - intro a. apply signed_bounds_leb_spec. auto.
  - intros a b c Hab Hbc. change (signed_bounds_leb w a c = true).
    change (signed_bounds_leb w a b = true) in Hab.
    change (signed_bounds_leb w b c = true) in Hbc.
    pose proof (proj1 (signed_bounds_leb_spec w a b) Hab) as Hab'.
    pose proof (proj1 (signed_bounds_leb_spec w b c) Hbc) as Hbc'.
    apply signed_bounds_leb_spec. auto.
  - intro a. reflexivity.
  - intros a b. apply signed_bounds_leb_spec. intros z Hz.
    apply signed_bounds_join_sound. now left.
  - intros a b. apply signed_bounds_leb_spec. intros z Hz.
    apply signed_bounds_join_sound. now right.
  - intros a b. apply signed_bounds_leb_spec. intros z Hz.
    apply signed_bounds_join_sound. now left.
  - intros a b. apply signed_bounds_leb_spec. intros z Hz.
    apply signed_bounds_join_sound. now right.
  - intros a b _. apply signed_bounds_leb_spec. intros z Hz.
    change (signed_bounds_gamma w (signed_bounds_reduce w a) z) in Hz.
    now rewrite signed_bounds_reduce_gamma in Hz.
  - intros a b Hba. change (signed_bounds_leb w b a = true) in Hba.
    pose proof (proj1 (signed_bounds_leb_spec w b a) Hba) as Hba'.
    apply signed_bounds_leb_spec. intros z Hz. apply signed_bounds_reduce_gamma. auto.
Qed.

(** The base dictionary's join is least on the full raw carrier. *)
Theorem signed_bounds_join_lub : forall w, lub_laws (signed_bounds_join_lattice w).
Proof.
  intro w. constructor. apply signed_bounds_join_least.
Qed.

Definition sb_half_meet_c (w : width) (s : bool) (a b : sb_half) : Cost.t sb_half :=
  let* a' := sb_reduce_half_c w s a in
  let* b' := sb_reduce_half_c w s b in
  sb_reduce_half_c w s
    (match a', b' with
    | SBRange ta la ua, SBRange tb lb ub =>
      SBRange (tnum_meet w ta tb) (Z.max la lb) (Z.min ua ub)
    | _, _ => SBEmpty
    end).

Definition sb_half_meet (w : width) (s : bool) (a b : sb_half) : sb_half :=
  Cost.value (sb_half_meet_c w s a b).

(** Half intersection retains the full reductions of both operands and the result. *)
Theorem sb_half_meet_equation : forall w s a b,
  sb_half_meet w s a b =
  sb_reduce_half w s
    (match sb_reduce_half w s a, sb_reduce_half w s b with
    | SBRange ta la ua, SBRange tb lb ub =>
      SBRange (tnum_meet w ta tb) (Z.max la lb) (Z.min ua ub)
    | _, _ => SBEmpty
    end).
Proof.
  intros w s a b. unfold sb_half_meet, sb_half_meet_c.
  autorewrite with galois_cost. reflexivity.
Qed.

(** Half intersection denotes exactly the shared feasible words. *)
Theorem sb_half_meet_gamma : forall w s a b z,
  sb_half_gamma w s (sb_half_meet w s a b) z <->
  sb_half_gamma w s a z /\ sb_half_gamma w s b z.
Proof.
  intros w s a b z. rewrite sb_half_meet_equation, sb_reduce_half_gamma.
  rewrite <- (sb_reduce_half_gamma w s a z), <- (sb_reduce_half_gamma w s b z).
  destruct (sb_reduce_half w s a) as [|ta la ua],
    (sb_reduce_half w s b) as [|tb lb ub];
    unfold sb_half_gamma, sb_bit_gamma, sb_interval_gamma, sb_range_gamma;
    cbn [fst snd]; try tauto.
  rewrite tnum_meet_gamma, Z.max_lub_iff, Z.min_glb_iff. tauto.
Qed.

Definition signed_bounds_meet_c (w : width) (a b : signed_bounds) : Cost.t signed_bounds :=
  let* zero := sb_half_meet_c w false (sb_zero a) (sb_zero b) in
  let* one := sb_half_meet_c w true (sb_one a) (sb_one b) in
  Cost.ret (SignedBounds zero one).

Definition signed_bounds_meet (w : width) (a b : signed_bounds) : signed_bounds :=
  Cost.value (signed_bounds_meet_c w a b).

(** Payload meet computes each sign intersection independently. *)
Theorem signed_bounds_meet_equation : forall w a b,
  signed_bounds_meet w a b =
  SignedBounds (sb_half_meet w false (sb_zero a) (sb_zero b))
    (sb_half_meet w true (sb_one a) (sb_one b)).
Proof.
  intros w a b. unfold signed_bounds_meet, signed_bounds_meet_c.
  autorewrite with galois_cost. reflexivity.
Qed.

(** Payload meet denotes exactly the intersection of the two original raw meanings. *)
Theorem signed_bounds_meet_gamma : forall w a b z,
  signed_bounds_gamma w (signed_bounds_meet w a b) z <->
  signed_bounds_gamma w a z /\ signed_bounds_gamma w b z.
Proof.
  intros w a b z. rewrite signed_bounds_meet_equation.
  unfold signed_bounds_gamma. cbn [sb_zero sb_one].
  rewrite !sb_half_meet_gamma. split; [tauto|].
  intros [[Ha|Ha] [Hb|Hb]]; try tauto;
    pose proof (sb_half_word_sign w _ _ z Ha) as [_ Hsa];
    pose proof (sb_half_word_sign w _ _ z Hb) as [_ Hsb]; congruence.
Qed.
