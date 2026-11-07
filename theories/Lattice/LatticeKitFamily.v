(** * Indexed-family combinator kit

    Families reflect order through arbitrarily indexed component observations.
    For example, a finite set has one boolean observation for each key.
    Builds on: LatticeCore, LatticeHeight, LatticeConcrete and LatticeKit. *)

From Stdlib Require Import Bool Arith Lia List.
From Galois.Lattice Require Import LatticeCore LatticeHeight LatticeConcrete LatticeKit.

(** A family reflects order and commutes with every component operation and bottom. *)
Record family {I B A} (L : lattice B) (LA : lattice A) (p : I -> B -> A) : Prop := {
  family_leb : forall x y, leb L x y = true <-> forall i, leb LA (p i x) (p i y) = true;
  family_bot : forall i, p i (bot L) = bot LA;
  family_join : forall i x y, p i (join L x y) = join LA (p i x) (p i y);
  family_widen : forall i x y, p i (widen L x y) = widen LA (p i x) (p i y);
  family_narrow : forall i x y, p i (narrow L x y) = narrow LA (p i x) (p i y)
}.

Arguments family_leb {I B A L LA p}.
Arguments family_bot {I B A L LA p}.
Arguments family_join {I B A L LA p}.
Arguments family_widen {I B A L LA p}.
Arguments family_narrow {I B A L LA p}.

(** This local step replaces a family comparison hypothesis by all its slot comparisons. *)
Local Ltac family_order F H :=
  let Hslots := fresh "Hslots" in
  pose proof (proj1 (family_leb F _ _) H) as Hslots;
  clear H; rename Hslots into H.

(** Family meaning requires every observation's meaning for the same concrete value. *)
Definition family_gamma {I B A C} (G : concretisation A C) (p : I -> B -> A) :
    concretisation B C :=
  {| gamma := fun x c => forall i, gamma G (p i x) c |}.

(** Family agreement requires every observation's agreement. *)
Definition family_agree {I B A C} (R : agreement A C) (p : I -> B -> A) :
    agreement B C :=
  {| agree := fun a x y => forall i, agree R (p i a) x y |}.

(** Finite support requires invariant slots everywhere and default-equivalent slots outside U. *)
Definition family_inv {I B A} (LA : lattice A) (p : I -> B -> A)
    (U : list I) (d : A) (inv : A -> Prop) (x : B) : Prop :=
  (forall i, inv (p i x)) /\
  (forall i, ~ In i U -> equivalent LA (p i x) d).

Local Lemma list_bool_cases {I} (U : list I) (f : I -> bool) :
  (forall i, In i U -> f i = true) \/ exists i, In i U /\ f i = false.
Proof.
  induction U as [| i U IH].
  - left; intros j Hj; contradiction.
  - destruct (f i) eqn:Hi.
    + destruct IH as [Hall | [j [Hj Hfalse]]].
      * left; intros j [Heq | Hj]; [subst j; exact Hi | apply Hall, Hj].
      * right; exists j; split; [right; exact Hj | exact Hfalse].
    + right; exists i; split; [left; reflexivity | exact Hi].
Qed.

Section Family.
Context {I B A : Type} {L : lattice B} {LA : lattice A} {p : I -> B -> A}
  (F : family L LA p).

(** Component weak laws imply the family's weak laws. *)
Theorem family_laws : lattice_laws LA -> lattice_laws L.
Proof.
  intro H; constructor.
  - intro x; apply (family_leb F); intro i; apply (leb_refl H).
  - intros x y z Hxy Hyz.
    family_order F Hxy; family_order F Hyz.
    apply (family_leb F); intro i; eapply (leb_trans H); [apply Hxy | apply Hyz].
  - intro x; apply (family_leb F); intro i; rewrite (family_bot F); apply (bot_least H).
  - intros x y; apply (family_leb F); intro i.
    rewrite (family_join F); apply (join_upper_l H).
  - intros x y; apply (family_leb F); intro i.
    rewrite (family_join F); apply (join_upper_r H).
  - intros x y; apply (family_leb F); intro i.
    rewrite (family_widen F); apply (widen_upper_l H).
  - intros x y; apply (family_leb F); intro i.
    rewrite (family_widen F); apply (widen_upper_r H).
  - intros x y Hyx; family_order F Hyx; apply (family_leb F); intro i.
    rewrite (family_narrow F); apply (narrow_lower H), Hyx.
  - intros x y Hyx; family_order F Hyx; apply (family_leb F); intro i.
    rewrite (family_narrow F); apply (narrow_upper H), Hyx.
Qed.

(** Component least joins imply least joins in the family. *)
Theorem family_lub : lub_laws LA -> lub_laws L.
Proof.
  intro H; constructor; intros x y z Hxz Hyz.
  family_order F Hxz; family_order F Hyz.
  apply (family_leb F); intro i; rewrite (family_join F).
  apply (join_least H); [apply Hxz | apply Hyz].
Qed.

(** A value whose every observation is component top is family top. *)
Definition family_top (T : top LA) (t : B)
    (Ht : forall i, p i t = top_value T) : top L.
Proof.
  refine {| top_value := t |}; intro x; apply (family_leb F); intro i.
  rewrite Ht; apply (top_greatest T).
Defined.

(** Pointwise component invariants are closed under the family operations. *)
Theorem family_closed {inv} : closed_on LA inv ->
  closed_on L (fun x => forall i, inv (p i x)).
Proof.
  intro H; constructor.
  - intro i; rewrite (family_bot F); apply (bot_inv H).
  - intros x y Hx Hy i; rewrite (family_join F); apply (join_inv H); auto.
  - intros x y Hx Hy i; rewrite (family_widen F); apply (widen_inv H); auto.
  - intros x y Hx Hy Hyx i; family_order F Hyx.
    rewrite (family_narrow F); apply (narrow_inv H); auto.
Qed.

(** Supported closure additionally needs default stability of widening and ordered narrowing. *)
Theorem family_support_closed (U : list I) (d : A) {inv} :
  lattice_laws LA -> lub_laws LA -> closed_on LA inv ->
  equivalent LA (bot LA) d ->
  (forall a b, inv a -> inv b -> equivalent LA a d -> equivalent LA b d ->
    equivalent LA (widen LA a b) d) ->
  (forall a b, inv a -> inv b -> leb LA b a = true ->
    equivalent LA a d -> equivalent LA b d -> equivalent LA (narrow LA a b) d) ->
  closed_on L (family_inv LA p U d inv).
Proof.
  intros H Hlub C Hbot Hw Hn; constructor.
  - split.
    + intro i; rewrite (family_bot F); apply (bot_inv C).
    + intros i _; rewrite (family_bot F); exact Hbot.
  - intros x y [Hx Houtx] [Hy Houty]; split.
    + intro i; rewrite (family_join F); apply (join_inv C); auto.
    + intros i Hi; rewrite (family_join F).
      destruct (Houtx i Hi) as [Hxd Hdx], (Houty i Hi) as [Hyd Hdy]; split.
      * apply (join_least Hlub); assumption.
      * eapply (leb_trans H); [exact Hdx | apply (join_upper_l H)].
  - intros x y [Hx Houtx] [Hy Houty]; split.
    + intro i; rewrite (family_widen F); apply (widen_inv C); auto.
    + intros i Hi; rewrite (family_widen F); apply Hw; auto.
  - intros x y [Hx Houtx] [Hy Houty] Hyx; family_order F Hyx; split.
    + intro i; rewrite (family_narrow F); apply (narrow_inv C); auto.
    + intros i Hi; rewrite (family_narrow F); apply Hn; auto.
Qed.

(** A false family comparison has a false observation in U if all outside observations pass. *)
Theorem family_false_in (U : list I) x y :
  (forall i, ~ In i U -> leb LA (p i x) (p i y) = true) ->
  leb L x y = false -> exists i, In i U /\ leb LA (p i x) (p i y) = false.
Proof.
  intros Hout Hfalse; destruct (list_bool_cases U (fun i => leb LA (p i x) (p i y)))
    as [Hall | Hbad]; [| exact Hbad].
  assert (Htrue : leb L x y = true).
  { apply (family_leb F); intro i.
    destruct (leb LA (p i x) (p i y)) eqn:Hi; [reflexivity |].
    assert (Hnot : ~ In i U) by (intro Hin; specialize (Hall i Hin); congruence).
    specialize (Hout i Hnot); congruence. }
  congruence.
Qed.

(** Finite sums of component heights measure joins under the default-support invariant. *)
Definition family_height (U : list I) (d : A) {inv}
    (H : lattice_laws LA) (Hlub : lub_laws LA) (C : closed_on LA inv)
    (R : height_on LA inv) : height_on L (family_inv LA p U d inv).
Proof.
  refine {| rank := fun x => msum U (fun i => rank R (p i x));
            bound := msum U (fun _ => bound R) |}.
  - intros x [Hx _]; apply msum_bounded; intros i _; apply (rank_bounded R), Hx.
  - intros x y [Hx _] [Hy _] Hxy; family_order F Hxy.
    apply msum_bounded; intros i _; apply (rank_monotone R); auto.
  - intros x y [Hx Houtx] [Hy Houty] Hstrict.
    assert (Houtside : forall i, ~ In i U ->
      leb LA (p i (join L x y)) (p i x) = true).
    { intros i Hi; rewrite (family_join F).
      destruct (Houtx i Hi) as [Hxd Hdx], (Houty i Hi) as [Hyd Hdy].
      apply (join_least Hlub); [apply (leb_refl H) |].
      eapply (leb_trans H); eassumption. }
    destruct (family_false_in U (join L x y) x Houtside Hstrict) as [i [Hin Hi]].
    apply msum_grows.
    + intros j _; rewrite (family_join F).
      apply (rank_monotone R); [apply Hx | apply (join_inv C); auto | apply (join_upper_l H)].
    + exists i; split; [exact Hin |].
      rewrite (family_join F) in Hi |- *; apply (join_rank_grows R); auto.
Defined.

(** Finite sums of component widening credits decrease on every escaping family input. *)
Definition family_wrank (U : list I) (d : A) {inv}
    (H : lattice_laws LA) (W : widening_rank_on LA inv) :
    widening_rank_on L (family_inv LA p U d inv).
Proof.
  refine {| wrank := fun x => msum U (fun i => wrank W (p i x));
            wbound := msum U (fun _ => wbound W) |}.
  - intros x [Hx _]; apply msum_bounded; intros i _; apply (wrank_bounded W), Hx.
  - intros x y [Hx _] [Hy _] _; apply msum_bounded; intros i _.
    rewrite (family_widen F); apply (widening_rank_nonincreasing W); auto.
  - intros x y [Hx Houtx] [Hy Houty] Hstrict.
    assert (Houtside : forall i, ~ In i U -> leb LA (p i y) (p i x) = true).
    { intros i Hi; destruct (Houtx i Hi) as [Hxd Hdx], (Houty i Hi) as [Hyd Hdy].
      eapply (leb_trans H); eassumption. }
    destruct (family_false_in U y x Houtside Hstrict) as [i [Hin Hi]].
    apply msum_grows.
    + intros j _; rewrite (family_widen F); apply (widening_rank_nonincreasing W); auto.
    + exists i; split; [exact Hin |].
      rewrite (family_widen F); apply (widen_rank_progress W); auto.
Defined.

Context {C : Type} (G : concretisation A C) (R : agreement A C).

(** Universal slot meaning is monotone when each component meaning is monotone. *)
Theorem family_gamma_laws : concretisation_laws LA G ->
  concretisation_laws L (family_gamma G p).
Proof.
  intro HG; constructor; intros x y c Hxy Hc i.
  family_order F Hxy.
  eapply (gamma_monotone HG); [apply Hxy | apply Hc].
Qed.

(** A chosen observation witnesses empty family bottom. *)
Theorem family_bot_empty (i : I) : bottom_empty LA G -> bottom_empty L (family_gamma G p).
Proof.
  intro HG; constructor; intros c Hc; specialize (Hc i); cbn in Hc.
  rewrite (family_bot F) in Hc; exact (gamma_bot_empty HG c Hc).
Qed.

(** Component fullness gives fullness of a family top. *)
Theorem family_top_full (T : top LA) t Ht :
  top_full T G -> top_full (family_top T t Ht) (family_gamma G p).
Proof.
  intro HG; constructor; intros c i; cbn; rewrite Ht; apply (gamma_top_full HG).
Qed.

(** Universal slot agreement preserves reflexivity and antitonicity. *)
Theorem family_agree_laws : agreement_laws LA R ->
  agreement_laws L (family_agree R p).
Proof.
  intro HR; constructor.
  - intros x c i; apply (agree_refl HR).
  - intros x y c d Hxy Hcd i; family_order F Hxy.
    eapply (agree_antitone HR); [apply Hxy | apply Hcd].
Qed.

(** Universal slot agreement transports the component join-agreement law. *)
Theorem family_agree_join : agreement_join_law LA R ->
  agreement_join_law L (family_agree R p).
Proof.
  intro HR; constructor; intros x y c d Hx Hy i; cbn.
  rewrite (family_join F); apply (agree_join HR); [apply Hx | apply Hy].
Qed.
End Family.
