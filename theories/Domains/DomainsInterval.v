(** * Integer intervals and threshold widening

    Intervals use extended integer endpoints and a shared prepared threshold tree.
    For example, widening [2,4] toward [1,12] with thresholds [0,10,20] gives [0,20].
    Builds on: DomainsBound, DomainsThreshold and LatticeConcrete. *)

From Stdlib Require Import ZArith List Bool Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Lattice Require Import LatticeCore LatticeConcrete.
From Galois.Bits Require Import BitsWord.
From Galois.Domains Require Import DomainsBound DomainsThreshold.
Import List.ListNotations.

Inductive interval : Type :=
  | IBot
  | Itv (lo hi : bound).

Definition widen_lower (ts : threshold_tree) (old next : bound) : bound :=
  if bound_leb old next then old else
    match next with
    | NegInf => NegInf
    | Fin z => lower_threshold ts z
    | PosInf => PosInf
    end.

Definition widen_upper (ts : threshold_tree) (old next : bound) : bound :=
  if bound_leb next old then old else
    match next with
    | NegInf => NegInf
    | Fin z => upper_threshold ts z
    | PosInf => PosInf
    end.

Definition narrow_bound (old next : bound) : bound :=
  match old with
  | Fin _ => old
  | _ => next
  end.

(** Widening the lower endpoint covers the next endpoint. *)
Theorem widen_lower_next : forall ts old next,
  bound_leb (widen_lower ts old next) next = true.
Proof.
  intros ts old next. unfold widen_lower. destruct (bound_leb old next) eqn:Hle.
  - exact Hle.
  - destruct next; cbn; try reflexivity. apply lower_threshold_lower.
Qed.

(** Widening the lower endpoint covers the old endpoint. *)
Theorem widen_lower_old : forall ts old next,
  bound_leb (widen_lower ts old next) old = true.
Proof.
  intros ts old next. unfold widen_lower. destruct (bound_leb old next) eqn:Hle.
  - apply bound_leb_refl.
  - eapply (bound_leb_trans _ next old).
    + destruct next as [|z|].
      * reflexivity.
      * apply lower_threshold_lower.
      * destruct old; discriminate.
    + destruct (bound_leb_total old next) as [H|H]; congruence.
Qed.

(** Widening the upper endpoint covers the next endpoint. *)
Theorem widen_upper_next : forall ts old next,
  bound_leb next (widen_upper ts old next) = true.
Proof.
  intros ts old next. unfold widen_upper. destruct (bound_leb next old) eqn:Hle.
  - exact Hle.
  - destruct next; cbn; try reflexivity. apply upper_threshold_upper.
Qed.

(** Widening the upper endpoint covers the old endpoint. *)
Theorem widen_upper_old : forall ts old next,
  bound_leb old (widen_upper ts old next) = true.
Proof.
  intros ts old next. unfold widen_upper. destruct (bound_leb next old) eqn:Hle.
  - apply bound_leb_refl.
  - eapply (bound_leb_trans old next _).
    + destruct (bound_leb_total old next) as [H|H]; congruence.
    + destruct next as [|z|].
      * destruct old; discriminate.
      * apply upper_threshold_upper.
      * reflexivity.
Qed.

Definition interval_leb (a b : interval) : bool :=
  match a, b with
  | IBot, _ => true
  | Itv _ _, IBot => false
  | Itv l h, Itv l' h' => bound_leb l' l && bound_leb h h'
  end.

Definition interval_join (a b : interval) : interval :=
  match a, b with
  | IBot, _ => b
  | _, IBot => a
  | Itv l h, Itv l' h' => Itv (bound_min l l') (bound_max h h')
  end.

Definition interval_widen (ts : threshold_tree) (a b : interval) : interval :=
  match a, b with
  | IBot, _ => b
  | _, IBot => a
  | Itv l h, Itv l' h' => Itv (widen_lower ts l l') (widen_upper ts h h')
  end.

Definition interval_narrow (a b : interval) : interval :=
  match a, b with
  | IBot, _ => IBot
  | _, IBot => a
  | Itv l h, Itv l' h' => Itv (narrow_bound l l') (narrow_bound h h')
  end.

(** The caller prepares thresholds once and shares the tree across lattice calls. *)
Definition interval_lattice (ts : threshold_tree) : lattice interval :=
  of_pure interval_leb IBot interval_join (interval_widen ts) interval_narrow.

(** An interval denotes all integers between its inclusive endpoints. *)
Definition interval_gamma : concretisation interval Z :=
  {| gamma i z :=
       match i with
       | IBot => False
       | Itv l h => bound_leb l (Fin z) = true /\ bound_leb (Fin z) h = true
       end |}.

(** Payload meaning requires a normalized word in the interval. *)
Definition interval_pgamma (w : width) (i : interval) (z : Z) : Prop :=
  is_word w z /\ gamma interval_gamma i z.

Definition interval_top (w : width) : interval :=
  Itv (Fin 0) (Fin (modulus w - 1)).

Definition interval_const (w : width) (z : Z) : interval :=
  Itv (Fin (wrap w z)) (Fin (wrap w z)).

(** Every normalized word belongs to its width-specific top. *)
Theorem interval_top_sound : forall w z, is_word w z -> interval_pgamma w (interval_top w) z.
Proof.
  intros w z Hword. split; [exact Hword|].
  unfold interval_top, interval_gamma. cbn [gamma bound_leb].
  destruct Hword as [Hlower Hupper]. split; apply Z.leb_le; lia.
Qed.

(** A constant contains the wrapped input integer. *)
Theorem interval_const_sound : forall w z,
  interval_pgamma w (interval_const w z) (wrap w z).
Proof.
  intros w z. split; [apply wrap_is_word|].
  unfold interval_const, interval_gamma. cbn [gamma bound_leb].
  now rewrite Z.leb_refl.
Qed.

(** Nonempty endpoints exclude impossible infinite singletons. *)
Definition bounds_nonempty (lo hi : bound) : bool :=
  match lo, hi with
  | PosInf, _ => false
  | _, NegInf => false
  | _, _ => bound_leb lo hi
  end.

Definition interval_meet (a b : interval) : interval :=
  match a, b with
  | Itv l h, Itv l' h' =>
    let lo := bound_max l l' in
    let hi := bound_min h h' in
    if bounds_nonempty lo hi then Itv lo hi else IBot
  | _, _ => IBot
  end.

Definition interval_finite (i : interval) : option (Z * Z) :=
  match i with
  | Itv (Fin lo) (Fin hi) => Some (lo, hi)
  | _ => None
  end.

(** Boundwise order, hull, widening and narrowing obey the weak lattice laws. *)
Theorem interval_laws : forall ts, lattice_laws (interval_lattice ts).
Proof.
  intro ts. constructor.
  - intros [|l h]; cbn; [reflexivity|].
    now rewrite !bound_leb_refl.
  - intros [|la ha] [|lb hb] [|lc hc]; cbn; try discriminate; try reflexivity.
    intros Hab Hbc. apply andb_true_iff in Hab as [Hlb Hhb].
    apply andb_true_iff in Hbc as [Hlc Hhc]. apply andb_true_iff. split;
      eapply bound_leb_trans; eassumption.
  - intros [|l h]; reflexivity.
  - intros [|la ha] [|lb hb]; cbn; try reflexivity; try (now rewrite !bound_leb_refl).
    apply andb_true_iff. split; [apply bound_min_lower_l|apply bound_max_upper_l].
  - intros [|la ha] [|lb hb]; cbn; try reflexivity; try (now rewrite !bound_leb_refl).
    apply andb_true_iff. split; [apply bound_min_lower_r|apply bound_max_upper_r].
  - intros [|la ha] [|lb hb]; cbn; try reflexivity; try (now rewrite !bound_leb_refl).
    apply andb_true_iff. split; [apply widen_lower_old|apply widen_upper_old].
  - intros [|la ha] [|lb hb]; cbn; try reflexivity; try (now rewrite !bound_leb_refl).
    apply andb_true_iff. split; [apply widen_lower_next|apply widen_upper_next].
  - intros [|la ha] [|lb hb]; cbn; try discriminate; try reflexivity;
      try (intros _; now rewrite !bound_leb_refl).
    intros Hle. apply andb_true_iff in Hle as [Hl Hh]. apply andb_true_iff. split.
    + unfold narrow_bound. destruct la; try assumption; apply bound_leb_refl.
    + unfold narrow_bound. destruct ha; try assumption; apply bound_leb_refl.
  - intros [|la ha] [|lb hb]; cbn; try discriminate; try reflexivity;
      try (intros _; now rewrite !bound_leb_refl).
    intros Hle. apply andb_true_iff in Hle as [Hl Hh]. apply andb_true_iff. split.
    + unfold narrow_bound. destruct la; try assumption; apply bound_leb_refl.
    + unfold narrow_bound. destruct ha; try assumption; apply bound_leb_refl.
Qed.

(** The hull is the least upper bound for boundwise order. *)
Theorem interval_lub : forall ts, lub_laws (interval_lattice ts).
Proof.
  intro ts. constructor.
  intros [|la ha] [|lb hb] [|lc hc]; cbn; try discriminate; try tauto.
  intros Ha Hb. apply andb_true_iff in Ha as [Hla Hha].
  apply andb_true_iff in Hb as [Hlb Hhb]. apply andb_true_iff. split.
  - now apply bound_min_greatest.
  - now apply bound_max_least.
Qed.

(** Increasing an interval in boundwise order retains every concrete integer. *)
Theorem interval_gamma_laws : forall ts,
  concretisation_laws (interval_lattice ts) interval_gamma.
Proof.
  intro ts. constructor.
  intros [|la ha] [|lb hb] z Hle Hgamma; cbn in *; try contradiction; try discriminate.
  apply andb_true_iff in Hle as [Hlower Hupper]. destruct Hgamma as [Hlo Hhi].
  split.
  - eapply bound_leb_trans; eassumption.
  - change (bound_leb (Fin z) hb = true).
    eapply bound_leb_trans; eassumption.
Qed.

(** Bottom denotes no integer. *)
Theorem interval_gamma_bot_empty : forall ts,
  bottom_empty (interval_lattice ts) interval_gamma.
Proof.
  intro ts. constructor. intros z H. exact H.
Qed.

(** The intersection lies below its left input even for malformed endpoints. *)
Theorem interval_meet_lower_left : forall ts a b,
  leb (interval_lattice ts) (interval_meet a b) a = true.
Proof.
  intros ts [|la ha] [|lb hb]; cbn; try reflexivity.
  destruct (bounds_nonempty (bound_max la lb) (bound_min ha hb)); cbn; [|reflexivity].
  apply andb_true_iff. split; [apply bound_max_upper_l|apply bound_min_lower_l].
Qed.

(** Intersecting two intervals retains their common concrete words. *)
Theorem interval_meet_sound : forall w a b z,
  interval_pgamma w a z -> interval_pgamma w b z ->
  interval_pgamma w (interval_meet a b) z.
Proof.
  intros w [|la ha] [|lb hb] z Ha Hb; cbn in Ha, Hb; try tauto.
  destruct Ha as [Hw [Hla Hha]]. destruct Hb as [_ [Hlb Hhb]].
  assert (Hlo : bound_leb (bound_max la lb) (Fin z) = true).
  { apply bound_max_least; assumption. }
  assert (Hhi : bound_leb (Fin z) (bound_min ha hb) = true).
  { apply bound_min_greatest; assumption. }
  assert (Hordered : bound_leb (bound_max la lb) (bound_min ha hb) = true).
  { eapply bound_leb_trans; eassumption. }
  assert (Hnonempty : bounds_nonempty (bound_max la lb) (bound_min ha hb) = true).
  { destruct (bound_max la lb), (bound_min ha hb); cbn in *; try discriminate; assumption. }
  cbn [interval_meet]. rewrite Hnonempty. split; [exact Hw|].
  split; assumption.
Qed.

Definition interval_clip (w : width) (a : interval) : interval :=
  interval_meet a (interval_top w).

(** Clipping to the operand width retains every represented word. *)
Theorem interval_clip_sound : forall w a z,
  interval_pgamma w a z -> interval_pgamma w (interval_clip w a) z.
Proof.
  intros w a z Ha. apply interval_meet_sound; [exact Ha|].
  apply interval_top_sound. exact (proj1 Ha).
Qed.

(** A singleton observation identifies every represented concrete word. *)
Definition interval_singleton (a : interval) : option Z :=
  match interval_finite a with
  | Some (lo, hi) => if Z.eqb lo hi then Some lo else None
  | None => None
  end.

(** Finite endpoints bound every represented integer. *)
Theorem interval_finite_sound : forall w i lo hi z,
  interval_pgamma w i z -> interval_finite i = Some (lo, hi) -> (lo <= z <= hi)%Z.
Proof.
  intros w [|[|l|] [|h|]] lo hi z Hgamma Hfinite;
    cbn [interval_finite] in Hfinite; try discriminate.
  inversion Hfinite; subst lo hi. destruct Hgamma as [_ [Hlo Hhi]].
  cbn [interval_gamma gamma bound_leb] in Hlo, Hhi.
  apply Z.leb_le in Hlo. apply Z.leb_le in Hhi. lia.
Qed.

(** A successful singleton observation returns the concrete word value. *)
Theorem interval_singleton_sound : forall w a x c,
  interval_pgamma w a x -> interval_singleton a = Some c -> x = c.
Proof.
  intros w a x c Ha Hsingle. unfold interval_singleton in Hsingle.
  destruct (interval_finite a) as [[lo hi]|] eqn:Hfinite; [|discriminate].
  destruct (Z.eqb lo hi) eqn:Heq; [|discriminate].
  inversion Hsingle; subst c. apply Z.eqb_eq in Heq.
  pose proof (interval_finite_sound w a lo hi x Ha Hfinite). lia.
Qed.

(** Joining intervals retains either input's concrete words. *)
Theorem interval_join_sound : forall ts w a b z,
  interval_pgamma w a z \/ interval_pgamma w b z ->
  interval_pgamma w (join (interval_lattice ts) a b) z.
Proof.
  intros ts w a b z [[Hw Ha]|[Hw Hb]]; split; try assumption.
  - exact (gamma_join_l (interval_lattice ts) interval_gamma a b z
      (interval_laws ts) (interval_gamma_laws ts) Ha).
  - exact (gamma_join_r (interval_lattice ts) interval_gamma a b z
      (interval_laws ts) (interval_gamma_laws ts) Hb).
Qed.
