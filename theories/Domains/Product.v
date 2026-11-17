(** * Value products

    Products apply value transfers to each component independently.
    For example, a forward transfer pairs the two component results.

    Main results
    - [forward_complexity] Product forward transfer has the published work bound.
    - [backward_complexity] Backward transfer has the published work-plus-request class.
    - [guard_complexity] Guard transfer has the published guard-work class.

    Builds on: ProductSig and lattice products. *)

From Stdlib Require Import List NArith Bool Lia PeanoNat.
From Argent Require Import Time Tactics Std Complexity.
Import ComplexityNotations.
From Galois.Lattice Require Import Product.
From Galois.Domains Require Import LangSig ValueSig ProductSig.

Definition product_is_bot {A B} (ba : A -> bool) (bb : B -> bool) (x : A * B) :=
  orb (ba (fst x)) (bb (snd x)).

TimeFun product_is_bot.

Definition product_leb {A B} (ba : A -> bool) (bb : B -> bool)
    (la : A -> A -> bool) (lb : B -> B -> bool) (x y : A * B) :=
  orb (product_is_bot ba bb x) (andb (la (fst x) (fst y)) (lb (snd x) (snd y))).

TimeFun product_leb.

Definition product_pair {A B} (fa : A -> A -> A) (fb : B -> B -> B) (x y : A * B) :=
  (fa (fst x) (fst y), fb (snd x) (snd y)).

TimeFun product_pair.

Definition product_normalize {A B} (ba : A -> bool) (bb : B -> bool)
    (a : A) (b : B) (x : A * B) :=
  if product_is_bot ba bb x then (a, b) else x.

TimeFun product_normalize.

Definition product_widen {A B PA PB} (ba : A -> bool) (bb : B -> bool)
    (wa : PA -> A -> A -> A) (wb : PB -> B -> B -> B) (p : PA * PB) (x y : A * B) :=
  if product_is_bot ba bb y then x
  else (wa (fst p) (fst x) (fst y), wb (snd p) (snd x) (snd y)).

TimeFun product_widen.

Definition product_narrow {A B} (ba : A -> bool) (bb : B -> bool)
    (na : A -> A -> A) (nb : B -> B -> B) (x y : A * B) :=
  if product_is_bot ba bb y then y else product_pair na nb x y.

TimeFun product_narrow.

Definition product_forward {A B O} (ba : A -> bool) (bb : B -> bool) (a : A) (b : B)
    (fa : O -> list A -> A) (fb : O -> list B -> B) (o : O) (xs : list (A * B)) :=
  product_normalize ba bb a b (fa o (map fst xs), fb o (map snd xs)).

TimeFun product_forward.

Definition product_backward {A B O} (ba : A -> bool) (bb : B -> bool) (a : A) (b : B)
    (fa : O -> A -> list A -> list A) (fb : O -> B -> list B -> list B)
    (o : O) (r : A * B) (xs : list (A * B)) :=
  map (product_normalize ba bb a b)
    (combine (fa o (fst r) (map fst xs)) (fb o (snd r) (map snd xs))).

TimeFun product_backward.

Definition product_guard {A B G} (ba : A -> bool) (bb : B -> bool) (a : A) (b : B)
    (fa : G -> list A -> list A) (fb : G -> list B -> list B)
    (g : G) (xs : list (A * B)) :=
  map (product_normalize ba bb a b) (combine (fa g (map fst xs)) (fb g (map snd xs))).

TimeFun product_guard.

Module ProductCode (L : LANG_OPS) (A B : VALUE_DOMAIN_OPS L) <: PRODUCT_OPS L A B.
  Definition t := (A.t * B.t)%type.
  Definition bot : t := (A.bot, B.bot).
  Definition is_bot := product_is_bot A.is_bot B.is_bot.
  Definition leb := product_leb A.is_bot B.is_bot A.leb B.leb.
  Definition join := product_pair A.join B.join.
  Definition normalize := product_normalize A.is_bot B.is_bot A.bot B.bot.
  Definition top : t := (A.top, B.top).
  Definition meet (x y : t) : t := normalize (product_pair A.meet B.meet x y).
  Definition wparam := (A.wparam * B.wparam)%type.
  Definition widen := product_widen A.is_bot B.is_bot A.widen B.widen.
  Definition narrow := product_narrow A.is_bot B.is_bot A.narrow B.narrow.
  Definition forward := product_forward A.is_bot B.is_bot A.bot B.bot A.forward B.forward.
  Definition backward := product_backward A.is_bot B.is_bot A.bot B.bot A.backward B.backward.
  Definition guard := product_guard A.is_bot B.is_bot A.bot B.bot A.guard B.guard.
End ProductCode.

Module Product (L : LANG) (A B : VALUE_DOMAIN L) <: PRODUCT L A B.
  Include ProductCode L A B.
  Definition wrank (p : wparam) (a : t) : nat :=
    A.wrank (fst p) (fst a) + B.wrank (snd p) (snd a).
  Definition gamma (a : t) (c : L.val) : Prop := A.gamma (fst a) c /\ B.gamma (snd a) c.

  (** Coordinate inclusion entails product inclusion, even for recognized bottoms. *)
  Lemma components_below : forall a b,
    A.leb (fst a) (fst b) = true -> B.leb (snd a) (snd b) = true -> leb a b = true.
  Proof.
    intros a b Ha Hb. unfold leb, product_leb.
    apply orb_true_iff. right. apply andb_true_iff. split; assumption.
  Qed.

  (** A nonbottom source must compare below its target in both coordinates. *)
  Lemma nonbottom_components : forall a b, is_bot a = false -> leb a b = true ->
    A.leb (fst a) (fst b) = true /\ B.leb (snd a) (snd b) = true.
  Proof.
    intros a b Hbot Hle.
    change (orb (is_bot a) (andb (A.leb (fst a) (fst b))
      (B.leb (snd a) (snd b))) = true) in Hle.
    rewrite Hbot in Hle. now apply andb_true_iff in Hle.
  Qed.

  (** Product bottom recognition descends through the product order. *)
  Lemma bottom_downward : forall a b,
    leb a b = true -> is_bot b = true -> is_bot a = true.
  Proof.
    intros a b Hle Hbot. destruct (is_bot a) eqn:Ha; [reflexivity|].
    destruct (nonbottom_components a b Ha Hle) as [Hleft Hright].
    unfold is_bot, product_is_bot in Hbot, Ha.
    apply orb_false_iff in Ha as [Ha Hb]. apply orb_true_iff in Hbot as [Hbot|Hbot].
    - pose proof (A.is_bot_below (fst a) (fst b) Hleft Hbot). congruence.
    - pose proof (B.is_bot_below (snd a) (snd b) Hright Hbot). congruence.
  Qed.

  (** A bottom in either coordinate excludes every shared concrete value. *)
  Lemma bottom_empty : forall a c, is_bot a = true -> ~ gamma a c.
  Proof.
    intros [a b] c Hbot [Ha Hb].
    change (orb (A.is_bot a) (B.is_bot b) = true) in Hbot.
    apply orb_true_iff in Hbot as [Hbot|Hbot].
    - exact (A.is_bot_sound a c Hbot Ha).
    - exact (B.is_bot_sound b c Hbot Hb).
  Qed.

  (** Normalizing a recognized bottom descends in each coordinate. *)
  Lemma normalize_components_lower : forall a,
    A.leb (fst (normalize a)) (fst a) = true /\
    B.leb (snd (normalize a)) (snd a) = true.
  Proof.
    intros [a b]. unfold normalize, product_normalize.
    destruct (product_is_bot A.is_bot B.is_bot (a, b)); cbn [fst snd]; split.
    - apply A.bot_least.
    - apply B.bot_least.
    - apply A.leb_refl.
    - apply B.leb_refl.
  Qed.

  (** Normalization refines the original product value. *)
  Lemma normalize_lower : forall a, leb (normalize a) a = true.
  Proof.
    intro a. destruct (normalize_components_lower a) as [Ha Hb].
    now apply components_below.
  Qed.

  (** Normalization retains every concrete value represented by the pair. *)
  Lemma normalize_sound : forall a c, gamma a c -> gamma (normalize a) c.
  Proof.
    intros a c Hgamma. unfold normalize, product_normalize.
    destruct (product_is_bot A.is_bot B.is_bot a) eqn:Hbot; [|exact Hgamma].
    exfalso. exact (bottom_empty a c Hbot Hgamma).
  Qed.

  Lemma leb_refl : forall a, leb a a = true.
  Proof.
    intro a. apply components_below; [apply A.leb_refl|apply B.leb_refl].
  Qed.
  (** The order composes through an intermediate value. *)
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof.
    intros a b c Hab Hbc. destruct (is_bot a) eqn:Ha.
    - unfold leb, product_leb. change (product_is_bot A.is_bot B.is_bot a = true) in Ha.
      now rewrite Ha.
    - destruct (is_bot b) eqn:Hb.
      { pose proof (bottom_downward a b Hab Hb). congruence. }
      destruct (nonbottom_components a b Ha Hab) as [HabA HabB].
      destruct (nonbottom_components b c Hb Hbc) as [HbcA HbcB].
      apply components_below; [eapply A.leb_trans|eapply B.leb_trans]; eassumption.
  Qed.
  (** Bottom is below every value. *)
  Lemma bot_least : forall a, leb bot a = true.
  Proof.
    intro a. apply components_below; [apply A.bot_least|apply B.bot_least].
  Qed.
  (** The bottom test recognizes bottom. *)
  Lemma is_bot_bot : is_bot bot = true.
  Proof.
    unfold is_bot, product_is_bot, bot. cbn [fst snd].
    rewrite A.is_bot_bot. reflexivity.
  Qed.
  (** Every recognized bottom is below every value. *)
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof.
    intros a b Hbot. unfold leb, product_leb.
    change (product_is_bot A.is_bot B.is_bot a = true) in Hbot. now rewrite Hbot.
  Qed.
  (** Join is above its left operand. *)
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof.
    intros a b. apply components_below; [apply A.join_ub_l|apply B.join_ub_l].
  Qed.
  (** Join is above its right operand. *)
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof.
    intros a b. apply components_below; [apply A.join_ub_r|apply B.join_ub_r].
  Qed.

  Lemma top_greatest : forall a, leb a top = true.
  Proof.
    intro a. apply components_below; [apply A.top_greatest|apply B.top_greatest].
  Qed.

  Lemma meet_lb_l : forall a b, leb (meet a b) a = true.
  Proof.
    intros a b. unfold meet. eapply leb_trans; [apply normalize_lower|].
    apply components_below; [apply A.meet_lb_l|apply B.meet_lb_l].
  Qed.
  (** Widening is above its previous value. *)
  Lemma widen_ub_l : forall p a b, leb a (widen p a b) = true.
  Proof.
    intros p a b. unfold widen, product_widen.
    destruct (product_is_bot A.is_bot B.is_bot b); [apply leb_refl|].
    apply components_below; [apply A.widen_ub_l|apply B.widen_ub_l].
  Qed.
  (** Widening is above its candidate value. *)
  Lemma widen_ub_r : forall p a b, leb b (widen p a b) = true.
  Proof.
    intros p a b. unfold widen, product_widen.
    destruct (product_is_bot A.is_bot B.is_bot b) eqn:Hbot.
    - apply is_bot_least. exact Hbot.
    - apply components_below; [apply A.widen_ub_r|apply B.widen_ub_r].
  Qed.
  (** A candidate below the previous value leaves widening unchanged. *)
  Lemma widen_stable : forall p a b, leb b a = true -> widen p a b = a.
  Proof.
    intros [pa pb] [a b] [c d] Hle. unfold widen, product_widen.
    destruct (product_is_bot A.is_bot B.is_bot (c, d)) eqn:Hbot; [reflexivity|].
    destruct (nonbottom_components (c, d) (a, b) Hbot Hle) as [Ha Hb].
    cbn [fst snd] in Ha, Hb |- *.
    rewrite (A.widen_stable pa a c Ha), (B.widen_stable pb b d Hb). reflexivity.
  Qed.
  (** An unstable widening from a nonbottom strictly decreases rank. *)
  Lemma wrank_widen : forall p a b, is_bot a = false -> leb b a = false ->
    wrank p (widen p a b) < wrank p a.
  Proof.
    intros [pa pb] [a b] [c d] Hbot Hle.
    change (orb (A.is_bot a) (B.is_bot b) = false) in Hbot.
    apply orb_false_iff in Hbot as [Ha Hb].
    change (orb (is_bot (c, d)) (andb (A.leb c a) (B.leb d b)) = false) in Hle.
    apply orb_false_iff in Hle as [Hcandidate Hle].
    unfold widen, product_widen. change (product_is_bot A.is_bot B.is_bot (c, d) = false)
      in Hcandidate. rewrite Hcandidate. unfold wrank. cbn [fst snd].
    pose proof (A.wrank_widen_le pa a c Ha) as Hleft.
    pose proof (B.wrank_widen_le pb b d Hb) as Hright.
    apply andb_false_iff in Hle as [Hle|Hle].
    - pose proof (A.wrank_widen pa a c Ha Hle). lia.
    - pose proof (B.wrank_widen pb b d Hb Hle). lia.
  Qed.
  (** Widening from a nonbottom does not increase rank. *)
  Lemma wrank_widen_le : forall p a b, is_bot a = false -> wrank p (widen p a b) <= wrank p a.
  Proof.
    intros p a b Hbot. destruct (leb b a) eqn:Hle.
    - rewrite (widen_stable p a b Hle). lia.
    - pose proof (wrank_widen p a b Hbot Hle). lia.
  Qed.
  (** Narrowing stays between an ordered candidate and previous value. *)
  Lemma narrow_between : forall a b, leb b a = true ->
    leb b (narrow a b) = true /\ leb (narrow a b) a = true.
  Proof.
    intros a b Hle. unfold narrow, product_narrow.
    destruct (product_is_bot A.is_bot B.is_bot b) eqn:Hbot.
    - split; [apply leb_refl|exact Hle].
    - destruct (nonbottom_components b a Hbot Hle) as [Ha Hb].
      destruct (A.narrow_between (fst a) (fst b) Ha) as [Ha1 Ha2].
      destruct (B.narrow_between (snd a) (snd b) Hb) as [Hb1 Hb2].
      split; apply components_below; assumption.
  Qed.

  (** Abstract inclusion entails concrete inclusion. *)
  Lemma gamma_mono : forall a b c, leb a b = true -> gamma a c -> gamma b c.
  Proof.
    intros a b c Hle Hgamma. destruct (is_bot a) eqn:Hbot.
    - exfalso. exact (bottom_empty a c Hbot Hgamma).
    - destruct (nonbottom_components a b Hbot Hle) as [Ha Hb].
      destruct Hgamma as [Hleft Hright]. split.
      + exact (A.gamma_mono (fst a) (fst b) c Ha Hleft).
      + exact (B.gamma_mono (snd a) (snd b) c Hb Hright).
  Qed.
  (** Bottom describes no concrete value. *)
  Lemma gamma_bot : forall c, ~ gamma bot c.
  Proof.
    intros c [Ha Hb]. exact (A.gamma_bot c Ha).
  Qed.
  (** Top describes every concrete value. *)
  Lemma gamma_top : forall c, gamma top c.
  Proof.
    intro c. change (A.gamma A.top c /\ B.gamma B.top c).
    split; [apply A.gamma_top|apply B.gamma_top].
  Qed.
  (** Meet retains values described by both operands. *)
  Lemma gamma_meet : forall a b c, gamma a c -> gamma b c -> gamma (meet a b) c.
  Proof.
    intros a b c [HaA HaB] [HbA HbB]. apply normalize_sound. split.
    - exact (A.gamma_meet (fst a) (fst b) c HaA HbA).
    - exact (B.gamma_meet (snd a) (snd b) c HaB HbB).
  Qed.
  (** A positive bottom test excludes every concrete value. *)
  Lemma is_bot_sound : forall a c, is_bot a = true -> ~ gamma a c.
  Proof.
    exact bottom_empty.
  Qed.
  (** Every value below a recognized bottom is recognized as bottom. *)
  Lemma is_bot_below : forall a b, leb a b = true -> is_bot b = true -> is_bot a = true.
  Proof.
    exact bottom_downward.
  Qed.

  (** Related products project to related argument lists for both components. *)
  Lemma arguments_sound : forall xs cs, Forall2 gamma xs cs ->
    Forall2 A.gamma (map fst xs) cs /\ Forall2 B.gamma (map snd xs) cs.
  Proof.
    intros xs cs Hfacts.
    induction Hfacts as [|[a b] c xs cs [Ha Hb] Htail [IHleft IHright]];
      cbn; split; constructor; assumption.
  Qed.

  (** Zipping corresponding sound component results retains their shared meaning. *)
  Lemma zip_sound : forall xs ys cs,
    Forall2 A.gamma xs cs -> Forall2 B.gamma ys cs ->
    Forall2 gamma (map normalize (combine xs ys)) cs.
  Proof.
    intros xs ys cs Hleft. revert ys.
    induction Hleft as [|a c xs cs Ha Htail IH]; intros ys Hright.
    - inversion Hright; subst. constructor.
    - inversion Hright as [|b c' ys' cs' Hb Hrest]; subst.
      cbn [combine map]. constructor.
      + apply normalize_sound. split; assumption.
      + now apply IH.
  Qed.

  (** Zipping component refinements preserves every original product position. *)
  Lemma zip_refines : forall xs ys zs,
    Forall2 (fun y x => A.leb y x = true) ys (map fst xs) ->
    Forall2 (fun z x => B.leb z x = true) zs (map snd xs) ->
    Forall2 (fun y x => leb y x = true) (map normalize (combine ys zs)) xs.
  Proof.
    intro xs. induction xs as [|[a b] xs IH]; intros ys zs Hleft Hright.
    - inversion Hleft; inversion Hright; subst. constructor.
    - cbn [map fst snd] in Hleft, Hright.
      inversion Hleft as [|y a' ys' axs' Hy Hys]; subst.
      inversion Hright as [|z b' zs' bxs' Hz Hzs]; subst.
      cbn [combine map]. constructor.
      + eapply leb_trans; [apply normalize_lower|]. apply components_below; assumption.
      + now apply IH.
  Qed.

  (** Forward transfer contains every successful concrete result. *)
  Lemma forward_sound : forall o xs cs c,
    Forall2 gamma xs cs -> L.eval o cs = Some c -> gamma (forward o xs) c.
  Proof.
    intros o xs cs c Hfacts Heval.
    destruct (arguments_sound xs cs Hfacts) as [Hleft Hright].
    unfold forward, product_forward. apply normalize_sound. split.
    - exact (A.forward_sound o (map fst xs) cs c Hleft Heval).
    - exact (B.forward_sound o (map snd xs) cs c Hright Heval).
  Qed.
  (** Backward transfer retains operands consistent with the abstract result. *)
  Lemma backward_sound : forall o r xs cs c,
    Forall2 gamma xs cs -> L.eval o cs = Some c -> gamma r c ->
    Forall2 gamma (backward o r xs) cs.
  Proof.
    intros o r xs cs c Hfacts Heval [HrA HrB].
    destruct (arguments_sound xs cs Hfacts) as [Hleft Hright].
    unfold backward, product_backward. apply zip_sound.
    - exact (A.backward_sound o (fst r) (map fst xs) cs c Hleft Heval HrA).
    - exact (B.backward_sound o (snd r) (map snd xs) cs c Hright Heval HrB).
  Qed.
  (** Backward transfer refines each operand in its original position. *)
  Lemma backward_refines : forall o r xs,
    Forall2 (fun y x => leb y x = true) (backward o r xs) xs.
  Proof.
    intros o r xs. unfold backward, product_backward. apply zip_refines.
    - apply A.backward_refines.
    - apply B.backward_refines.
  Qed.
  (** Guard transfer retains operands satisfying the concrete guard. *)
  Lemma guard_sound : forall g xs cs,
    Forall2 gamma xs cs -> L.holds g cs -> Forall2 gamma (guard g xs) cs.
  Proof.
    intros g xs cs Hfacts Hholds.
    destruct (arguments_sound xs cs Hfacts) as [Hleft Hright].
    unfold guard, product_guard. apply zip_sound.
    - exact (A.guard_sound g (map fst xs) cs Hleft Hholds).
    - exact (B.guard_sound g (map snd xs) cs Hright Hholds).
  Qed.
  (** Guard transfer refines each operand in its original position. *)
  Lemma guard_refines : forall g xs,
    Forall2 (fun y x => leb y x = true) (guard g xs) xs.
  Proof.
    intros g xs. unfold guard, product_guard. apply zip_refines.
    - apply A.guard_refines.
    - apply B.guard_refines.
  Qed.
End Product.

Module ProductT (L : LANG_T) (A B : VALUE_DOMAIN_T L) <: PRODUCT_ALL L A B.
  Include Product L A B.

  TimeFun bot.
  TimeFun is_bot.
  TimeFun leb.
  TimeFun join.
  TimeFun normalize.
  TimeFun top.
  TimeFun meet.
  TimeFun widen.
  TimeFun narrow.
  TimeFun forward.
  TimeFun backward.
  TimeFun guard.

  Definition size (a : t) : nat := A.size (fst a) + B.size (snd a).
  Definition work (o : L.op) (xs : list t) : nat :=
    A.work o (map fst xs) + B.work o (map snd xs) + length xs.
  Definition gwork (g : L.guard) (xs : list t) : nat :=
    A.gwork g (map fst xs) + B.gwork g (map snd xs) + length xs.
  Definition wsize (p : wparam) : nat := A.wsize (fst p) + B.wsize (snd p).
  Definition wunits (_ : t) : nat := 0.
  Definition k_core : N :=
    (A.c_val + B.c_val + N.of_nat (A.size A.bot + B.size B.bot) + 16)%N.
  Definition c_val : N := (64 * k_core * k_core)%N.
  Definition c_lat : N := c_val.
  (** The lattice constant pays for at least one call. *)
  Lemma c_lat_pos : (1 <= c_lat)%N.
  Proof.
    unfold c_lat, c_val, k_core. nia.
  Qed.
  Definition c_product : N := (16 * k_core)%N.

  Local Lemma core_bounds :
    (16 <= k_core /\ A.c_val <= k_core /\ B.c_val <= k_core /\
      N.of_nat (A.size A.bot + B.size B.bot) <= k_core)%N.
  Proof.
    unfold k_core. lia.
  Qed.

  Local Lemma core_A : (A.c_val <= k_core)%N.
  Proof.
    exact (proj1 (proj2 core_bounds)).
  Qed.

  Local Lemma core_B : (B.c_val <= k_core)%N.
  Proof.
    exact (proj1 (proj2 (proj2 core_bounds))).
  Qed.

  Local Lemma scale_callback : forall ticks coefficient own budget,
    (ticks <= coefficient * N.of_nat own)%N -> (coefficient <= k_core)%N ->
    (own <= budget)%nat -> (ticks <= k_core * N.of_nat budget)%N.
  Proof.
    intros ticks coefficient own budget Htime Hcoefficient Hsize.
    eapply N.le_trans; [exact Htime|]. apply N.mul_le_mono; [exact Hcoefficient|].
    lia.
  Qed.

  Local Lemma nat_bound : forall n m, (n <= m)%nat -> (N.of_nat n <= N.of_nat m)%N.
  Proof.
    intros n m Hle. lia.
  Qed.

  Local Lemma basic_coefficient : (4 * k_core + 16 <= c_val)%N.
  Proof.
    pose proof (proj1 core_bounds). unfold c_val. nia.
  Qed.

  Local Lemma basic_budget : forall budget,
    (4 * (k_core * budget) + 16 * budget <= c_val * budget)%N.
  Proof.
    intro budget. replace (4 * (k_core * budget) + 16 * budget)%N with
      ((4 * k_core + 16) * budget)%N by ring.
    apply N.mul_le_mono_r. exact basic_coefficient.
  Qed.

  Local Lemma core_budget_dom : forall budget, (budget <= k_core * budget)%N.
  Proof.
    intro budget. replace budget with (1 * budget)%N at 1 by ring.
    apply N.mul_le_mono_r. pose proof (proj1 core_bounds). lia.
  Qed.

  Local Lemma closed_bottom_budget : forall budget, (1 <= budget)%N ->
    (N.of_nat (A.size A.bot + B.size B.bot) <= k_core * budget)%N.
  Proof.
    intros budget Hbudget. eapply N.le_trans.
    - exact (proj2 (proj2 (proj2 core_bounds))).
    - replace k_core with (k_core * 1)%N at 1 by ring.
      now apply N.mul_le_mono_l.
  Qed.

  (** Normalization can introduce only the fixed pair of component bottoms. *)
  Lemma normalize_size_bound : forall x,
    (size (normalize x) <= size x + A.size A.bot + B.size B.bot)%nat.
  Proof.
    intros [a b]. unfold normalize, product_normalize.
    destruct (product_is_bot A.is_bot B.is_bot (a, b)); unfold size; cbn [fst snd]; lia.
  Qed.

  (** Bottom testing and the final branch are linear in the raw pair size. *)
  Lemma normalize_time_bound : forall x,
    (T_normalize x <= 4 * k_core * N.of_nat (size x + 1))%N.
  Proof.
    intros [a b]. set (budget := N.of_nat (size (a, b) + 1)).
    assert (Hbudget : (1 <= budget)%N).
    { unfold budget. rewrite Nat2N.inj_add. lia. }
    assert (Ha : (A.T_is_bot a <= k_core * budget)%N).
    { eapply scale_callback; [apply A.T_is_bot_le|exact core_A|]. unfold size. cbn. lia. }
    assert (Hb : (B.T_is_bot b <= k_core * budget)%N).
    { eapply scale_callback; [apply B.T_is_bot_le|exact core_B|]. unfold size. cbn. lia. }
    assert (Hcore : (16 * budget <= k_core * budget)%N).
    { apply N.mul_le_mono_r. exact (proj1 core_bounds). }
    replace (4 * k_core * budget)%N with (4 * (k_core * budget))%N by ring.
    time_unfold T_normalize. time_unfold @T_product_normalize.
    time_unfold @T_product_is_bot. time_cbn. time_pose.
    destruct (product_is_bot A.is_bot B.is_bot (a, b)); lia.
  Qed.

  (** Summing product sizes separates into the two projected sums. *)
  Lemma sum_sizes : forall xs,
    fold_right Nat.add 0%nat (map size xs) =
    (fold_right Nat.add 0%nat (map A.size (map fst xs)) +
      fold_right Nat.add 0%nat (map B.size (map snd xs)))%nat.
  Proof.
    intro xs. induction xs as [|[a b] xs IH]; cbn [map fold_right fst snd].
    - reflexivity.
    - unfold size at 1. cbn [fst snd]. lia.
  Qed.

  Local Lemma wide_budget : forall budget,
    (16 * (k_core * k_core * budget) + 16 * (k_core * budget) + 32 * budget <=
      c_val * budget)%N.
  Proof.
    intro budget. replace
      (16 * (k_core * k_core * budget) + 16 * (k_core * budget) + 32 * budget)%N with
      ((16 * k_core * k_core + 16 * k_core + 32) * budget)%N by ring.
    apply N.mul_le_mono_r. pose proof (proj1 core_bounds). unfold c_val. nia.
  Qed.

  (** Truncating a pair of lists cannot increase either component's size sum. *)
  Lemma combine_size_bound : forall xs ys,
    (fold_right Nat.add 0%nat (map size (combine xs ys)) <=
      fold_right Nat.add 0%nat (map A.size xs) +
      fold_right Nat.add 0%nat (map B.size ys))%nat.
  Proof.
    intro xs. induction xs as [|a xs IH]; intros [|b ys];
      cbn [combine map fold_right]; try lia.
    unfold size at 1. cbn [fst snd]. pose proof (IH ys). lia.
  Qed.

  (** Each normalized list entry can add at most one closed bottom pair. *)
  Lemma normalize_list_size_bound : forall xs,
    (fold_right Nat.add 0%nat (map size (map normalize xs)) <=
      fold_right Nat.add 0%nat (map size xs) +
      length xs * (A.size A.bot + B.size B.bot))%nat.
  Proof.
    intro xs. induction xs as [|x xs IH]; cbn [map fold_right length].
    - lia.
    - pose proof (normalize_size_bound x). rewrite Nat.mul_succ_l. lia.
  Qed.

  Lemma paired_size_bound : forall xs ys,
    (fold_right Nat.add 0%nat (map size (map normalize (combine xs ys))) <=
      fold_right Nat.add 0%nat (map A.size xs) +
      fold_right Nat.add 0%nat (map B.size ys) +
      length xs * (A.size A.bot + B.size B.bot))%nat.
  Proof.
    intros xs ys. pose proof (normalize_list_size_bound (combine xs ys)) as Hnormal.
    pose proof (combine_size_bound xs ys) as Hpair.
    assert (Hlength : (length (combine xs ys) <= length xs)%nat).
    { rewrite length_combine. apply Nat.le_min_l. }
    assert (Hbottom : (length (combine xs ys) * (A.size A.bot + B.size B.bot) <=
      length xs * (A.size A.bot + B.size B.bot))%nat).
    { now apply Nat.mul_le_mono_r. }
    lia.
  Qed.

  Local Lemma paired_size_budget : forall xs ys budget,
    (N.of_nat (fold_right Nat.add 0%nat (map A.size xs)) <= k_core * budget)%N ->
    (N.of_nat (fold_right Nat.add 0%nat (map B.size ys)) <= k_core * budget)%N ->
    (N.of_nat (length xs) <= budget)%N ->
    (N.of_nat (fold_right Nat.add 0%nat (map size (map normalize (combine xs ys)))) <=
      c_val * budget)%N.
  Proof.
    intros xs ys budget Ha Hb Hlength.
    pose proof (nat_bound _ _ (paired_size_bound xs ys)) as Hsize.
    assert (Hbottom : (N.of_nat (length xs) * N.of_nat (A.size A.bot + B.size B.bot) <=
      k_core * budget)%N).
    { rewrite (N.mul_comm (N.of_nat (length xs))). apply N.mul_le_mono.
      - exact (proj2 (proj2 (proj2 core_bounds))).
      - exact Hlength. }
    pose proof (basic_budget budget) as Htotal.
    rewrite !Nat2N.inj_add, Nat2N.inj_mul in Hsize.
    rewrite Nat2N.inj_add in Hbottom. lia.
  Qed.

  (** Mapping charges the supplied clock once for each input cell. *)
  Lemma map_time_sum {X Y : Type} (f : X -> Y) (clock bound : X -> N) xs :
    (forall x, (clock x <= bound x)%N) ->
    (ListDef.T_map f clock xs <= fold_right N.add 0%N (map bound xs) +
      N.of_nat (length xs) + 1)%N.
  Proof.
    intro Hclock. induction xs as [|x xs IH].
    - time_unfold @ListDef.T_map. time_cbn. lia.
    - time_unfold @ListDef.T_map. time_cbn.
      pose proof (Hclock x). cbn [map fold_right length].
      lia.
  Qed.

  (** Projecting a list costs a constant amount per pair. *)
  Lemma fst_map_time_bound : forall xs : list (A.t * B.t),
    (ListDef.T_map (@fst A.t B.t) (fun x => Datatypes.T_fst x) xs <=
      2 * N.of_nat (length xs) + 1)%N.
  Proof.
    intro xs. apply (ListDef.T_map_le _ _ 1%N). apply Datatypes.T_fst_le.
  Qed.

  Lemma snd_map_time_bound : forall xs : list (A.t * B.t),
    (ListDef.T_map (@snd A.t B.t) (fun x => Datatypes.T_snd x) xs <=
      2 * N.of_nat (length xs) + 1)%N.
  Proof.
    intro xs. apply (ListDef.T_map_le _ _ 1%N). apply Datatypes.T_snd_le.
  Qed.

  (** The helper callback costs no more than the exported normalization clock. *)
  Lemma normalize_map_time_bound : forall xs,
    (ListDef.T_map (product_normalize A.is_bot B.is_bot A.bot B.bot)
      (fun x => T_product_normalize A.is_bot (fun a => A.T_is_bot a)
        B.is_bot (fun b => B.T_is_bot b) A.bot B.bot x) xs <=
      fold_right N.add 0%N (map T_normalize xs) + N.of_nat (length xs) + 1)%N.
  Proof.
    intro xs. apply map_time_sum. intro x. time_unfold T_normalize. lia.
  Qed.

  (** Normalizing several pairs charges their total size and list length. *)
  Lemma normalize_sum_time_bound : forall xs,
    (fold_right N.add 0%N (map T_normalize xs) <= 4 * k_core *
      (N.of_nat (fold_right Nat.add 0%nat (map size xs)) + N.of_nat (length xs)))%N.
  Proof.
    intro xs. induction xs as [|x xs IH].
    - cbn [map fold_right length]. lia.
    - cbn [map fold_right length]. rewrite Nat2N.inj_add, time_of_nat_succ.
      pose proof (normalize_time_bound x) as Hhead.
      rewrite Nat2N.inj_add in Hhead.
      replace (4 * k_core *
        (N.of_nat (size x) + N.of_nat (fold_right Nat.add 0%nat (map size xs)) +
          (N.of_nat (length xs) + 1)))%N with
        (4 * k_core * (N.of_nat (size x) + 1) +
          4 * k_core * (N.of_nat (fold_right Nat.add 0%nat (map size xs)) +
            N.of_nat (length xs)))%N by ring.
      lia.
  Qed.

  Local Lemma paired_normalize_time_budget : forall xs ys budget,
    (N.of_nat (fold_right Nat.add 0%nat (map A.size xs)) <= k_core * budget)%N ->
    (N.of_nat (fold_right Nat.add 0%nat (map B.size ys)) <= k_core * budget)%N ->
    (N.of_nat (length xs) <= budget)%N ->
    (fold_right N.add 0%N (map T_normalize (combine xs ys)) <=
      8 * (k_core * k_core * budget) + 4 * (k_core * budget))%N.
  Proof.
    intros xs ys budget Ha Hb Hlength.
    pose proof (nat_bound _ _ (combine_size_bound xs ys)) as Hsize.
    rewrite Nat2N.inj_add in Hsize.
    assert (Hcombine : (N.of_nat (length (combine xs ys)) <= N.of_nat (length xs))%N).
    { apply nat_bound. rewrite length_combine. apply Nat.le_min_l. }
    eapply N.le_trans; [apply normalize_sum_time_bound|].
    replace (8 * (k_core * k_core * budget) + 4 * (k_core * budget))%N with
      (4 * k_core * (2 * (k_core * budget) + budget))%N by ring.
    apply N.mul_le_mono_l. lia.
  Qed.

  (** Product forward time separates the component clocks from list scanning. *)
  Lemma forward_time_parts : forall o xs,
    (T_forward o xs <= A.T_forward o (map fst xs) + B.T_forward o (map snd xs) +
      T_normalize (A.forward o (map fst xs), B.forward o (map snd xs)) +
      8 * N.of_nat (length xs) + 16)%N.
  Proof.
    intros o xs. pose proof (fst_map_time_bound xs) as Hfst.
    pose proof (snd_map_time_bound xs) as Hsnd.
    time_unfold T_forward. time_unfold @T_product_forward. time_unfold T_normalize.
    time_cbn. unfold t in *. lia.
  Qed.

  (** Product backward time charges assembly of the paired component outputs. *)
  Lemma backward_time_parts : forall o r xs,
    (T_backward o r xs <= A.T_backward o (fst r) (map fst xs) +
      B.T_backward o (snd r) (map snd xs) +
      fold_right N.add 0%N (map T_normalize
        (combine (A.backward o (fst r) (map fst xs))
          (B.backward o (snd r) (map snd xs)))) + 8 * N.of_nat (length xs) + 16)%N.
  Proof.
    intros o [a b] xs. cbn [fst snd].
    pose proof (fst_map_time_bound xs) as Hfst.
    pose proof (snd_map_time_bound xs) as Hsnd.
    pose proof (List.T_combine_le (A.backward o a (map fst xs))
      (B.backward o b (map snd xs))) as Hcombine.
    pose proof (normalize_map_time_bound (combine (A.backward o a (map fst xs))
      (B.backward o b (map snd xs)))) as Hmap.
    pose proof (Forall2_length (A.backward_refines o a (map fst xs))) as Hlength.
    rewrite length_map in Hlength.
    assert (Hpaired : (length (combine (A.backward o a (map fst xs))
      (B.backward o b (map snd xs))) <= length xs)%nat).
    { rewrite length_combine. eapply Nat.le_trans; [apply Nat.le_min_l|]. lia. }
    rewrite Hlength in Hcombine.
    pose proof (nat_bound _ _ Hpaired) as HpairedN.
    time_unfold T_backward. time_unfold @T_product_backward. time_cbn. time_pose.
    unfold t in *. lia.
  Qed.

  (** Product guard time charges assembly of the paired component outputs. *)
  Lemma guard_time_parts : forall g xs,
    (T_guard g xs <= A.T_guard g (map fst xs) + B.T_guard g (map snd xs) +
      fold_right N.add 0%N (map T_normalize
        (combine (A.guard g (map fst xs)) (B.guard g (map snd xs)))) +
      8 * N.of_nat (length xs) + 16)%N.
  Proof.
    intros g xs. pose proof (fst_map_time_bound xs) as Hfst.
    pose proof (snd_map_time_bound xs) as Hsnd.
    pose proof (List.T_combine_le (A.guard g (map fst xs))
      (B.guard g (map snd xs))) as Hcombine.
    pose proof (normalize_map_time_bound (combine (A.guard g (map fst xs))
      (B.guard g (map snd xs)))) as Hmap.
    pose proof (Forall2_length (A.guard_refines g (map fst xs))) as Hlength.
    rewrite length_map in Hlength.
    assert (Hpaired : (length (combine (A.guard g (map fst xs))
      (B.guard g (map snd xs))) <= length xs)%nat).
    { rewrite length_combine. eapply Nat.le_trans; [apply Nat.le_min_l|]. lia. }
    rewrite Hlength in Hcombine.
    pose proof (nat_bound _ _ Hpaired) as HpairedN.
    time_unfold T_guard. time_unfold @T_product_guard. time_cbn.
    unfold t in *. lia.
  Qed.

  Lemma T_leb_le : forall a b,
    (T_leb a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros [a b] [c d].
    set (budget := N.of_nat (size (a, b) + size (c, d) + 1)).
    assert (Hbudget : (1 <= budget)%N).
    { unfold budget. rewrite Nat2N.inj_add. lia. }
    assert (Ha0 : (A.T_is_bot a <= k_core * budget)%N).
    { eapply scale_callback; [apply A.T_is_bot_le|exact core_A|]. unfold size. cbn. lia. }
    assert (Hb0 : (B.T_is_bot b <= k_core * budget)%N).
    { eapply scale_callback; [apply B.T_is_bot_le|exact core_B|]. unfold size. cbn. lia. }
    assert (Ha1 : (A.T_leb a c <= k_core * budget)%N).
    { eapply scale_callback; [apply A.T_leb_le|exact core_A|]. unfold size. cbn. lia. }
    assert (Hb1 : (B.T_leb b d <= k_core * budget)%N).
    { eapply scale_callback; [apply B.T_leb_le|exact core_B|]. unfold size. cbn. lia. }
    pose proof (basic_budget budget) as Htotal.
    time_unfold T_leb. time_unfold @T_product_leb. time_unfold @T_product_is_bot.
    time_cbn. time_pose. lia.
  Qed.
  Lemma T_join_le : forall a b,
    (T_join a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros [a b] [c d].
    set (budget := N.of_nat (size (a, b) + size (c, d) + 1)).
    assert (Hbudget : (1 <= budget)%N).
    { unfold budget. rewrite Nat2N.inj_add. lia. }
    assert (Ha : (A.T_join a c <= k_core * budget)%N).
    { eapply scale_callback; [apply A.T_join_le|exact core_A|]. unfold size. cbn. lia. }
    assert (Hb : (B.T_join b d <= k_core * budget)%N).
    { eapply scale_callback; [apply B.T_join_le|exact core_B|]. unfold size. cbn. lia. }
    pose proof (basic_budget budget) as Htotal.
    time_unfold T_join. time_unfold @T_product_pair. time_cbn. time_pose. lia.
  Qed.
  Lemma T_meet_le : forall a b,
    (T_meet a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros [a b] [c d]. set (budget := N.of_nat (size (a, b) + size (c, d) + 1)).
    assert (Hbudget : (1 <= budget)%N).
    { unfold budget. rewrite Nat2N.inj_add. lia. }
    assert (Ha : (A.T_meet a c <= k_core * budget)%N).
    { eapply scale_callback; [apply A.T_meet_le|exact core_A|]. unfold size. cbn. lia. }
    assert (Hb : (B.T_meet b d <= k_core * budget)%N).
    { eapply scale_callback; [apply B.T_meet_le|exact core_B|]. unfold size. cbn. lia. }
    assert (Hsa : (N.of_nat (A.size (A.meet a c)) <= k_core * budget)%N).
    { eapply scale_callback; [apply A.meet_size|exact core_A|]. unfold size. cbn. lia. }
    assert (Hsb : (N.of_nat (B.size (B.meet b d)) <= k_core * budget)%N).
    { eapply scale_callback; [apply B.meet_size|exact core_B|]. unfold size. cbn. lia. }
    assert (Hraw : (N.of_nat (size (A.meet a c, B.meet b d) + 1) <=
      2 * (k_core * budget) + budget)%N).
    { unfold size. cbn [fst snd]. rewrite !Nat2N.inj_add. lia. }
    assert (Hnormal : (T_normalize (A.meet a c, B.meet b d) <=
      8 * (k_core * k_core * budget) + 4 * (k_core * budget))%N).
    { eapply N.le_trans; [apply normalize_time_bound|].
      replace (8 * (k_core * k_core * budget) + 4 * (k_core * budget))%N with
        (4 * k_core * (2 * (k_core * budget) + budget))%N by ring.
      now apply N.mul_le_mono_l. }
    pose proof (wide_budget budget) as Htotal.
    time_unfold T_meet. time_unfold @T_product_pair.
    time_cbn. time_pose. unfold product_pair. cbn [fst snd]. lia.
  Qed.
  Lemma T_is_bot_le : forall a,
    (T_is_bot a <= c_val * N.of_nat (size a + 1))%N.
  Proof.
    intros [a b]. set (budget := N.of_nat (size (a, b) + 1)).
    assert (Hbudget : (1 <= budget)%N).
    { unfold budget. rewrite Nat2N.inj_add. lia. }
    assert (Ha : (A.T_is_bot a <= k_core * budget)%N).
    { eapply scale_callback; [apply A.T_is_bot_le|exact core_A|]. unfold size. cbn. lia. }
    assert (Hb : (B.T_is_bot b <= k_core * budget)%N).
    { eapply scale_callback; [apply B.T_is_bot_le|exact core_B|]. unfold size. cbn. lia. }
    pose proof (basic_budget budget) as Htotal.
    time_unfold T_is_bot. time_unfold @T_product_is_bot. time_cbn. time_pose. lia.
  Qed.
  Lemma T_widen_le : forall p a b,
    (T_widen p a b <= c_val * N.of_nat (size a + size b + wsize p + 1))%N.
  Proof.
    intros [pa pb] [a b] [c d].
    set (budget := N.of_nat (size (a, b) + size (c, d) + wsize (pa, pb) + 1)).
    assert (Hbudget : (1 <= budget)%N).
    { unfold budget. rewrite Nat2N.inj_add. lia. }
    assert (Ha0 : (A.T_is_bot c <= k_core * budget)%N).
    { eapply scale_callback; [apply A.T_is_bot_le|exact core_A|].
      unfold size, wsize. cbn. lia. }
    assert (Hb0 : (B.T_is_bot d <= k_core * budget)%N).
    { eapply scale_callback; [apply B.T_is_bot_le|exact core_B|].
      unfold size, wsize. cbn. lia. }
    assert (Ha1 : (A.T_widen pa a c <= k_core * budget)%N).
    { eapply scale_callback; [apply A.T_widen_le|exact core_A|].
      unfold size, wsize. cbn. lia. }
    assert (Hb1 : (B.T_widen pb b d <= k_core * budget)%N).
    { eapply scale_callback; [apply B.T_widen_le|exact core_B|].
      unfold size, wsize. cbn. lia. }
    pose proof (basic_budget budget) as Htotal.
    time_unfold T_widen. time_unfold @T_product_widen. time_unfold @T_product_is_bot.
    time_cbn. time_pose. destruct (product_is_bot A.is_bot B.is_bot (c, d)); lia.
  Qed.
  Lemma T_narrow_le : forall a b,
    (T_narrow a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros [a b] [c d].
    set (budget := N.of_nat (size (a, b) + size (c, d) + 1)).
    assert (Hbudget : (1 <= budget)%N).
    { unfold budget. rewrite Nat2N.inj_add. lia. }
    assert (Ha0 : (A.T_is_bot c <= k_core * budget)%N).
    { eapply scale_callback; [apply A.T_is_bot_le|exact core_A|]. unfold size. cbn. lia. }
    assert (Hb0 : (B.T_is_bot d <= k_core * budget)%N).
    { eapply scale_callback; [apply B.T_is_bot_le|exact core_B|]. unfold size. cbn. lia. }
    assert (Ha1 : (A.T_narrow a c <= k_core * budget)%N).
    { eapply scale_callback; [apply A.T_narrow_le|exact core_A|]. unfold size. cbn. lia. }
    assert (Hb1 : (B.T_narrow b d <= k_core * budget)%N).
    { eapply scale_callback; [apply B.T_narrow_le|exact core_B|]. unfold size. cbn. lia. }
    pose proof (basic_budget budget) as Htotal.
    time_unfold T_narrow. time_unfold @T_product_narrow.
    time_unfold @T_product_is_bot. time_unfold @T_product_pair.
    time_cbn. time_pose. destruct (product_is_bot A.is_bot B.is_bot (c, d)); lia.
  Qed.
  Lemma T_forward_le : forall o xs,
    (T_forward o xs <= c_val * N.of_nat (work o xs + 1))%N.
  Proof.
    intros o xs. set (budget := N.of_nat (work o xs + 1)).
    assert (Hbudget : (1 <= budget)%N).
    { unfold budget. rewrite Nat2N.inj_add. lia. }
    assert (Hlength : (N.of_nat (length xs) <= budget)%N).
    { unfold budget, work, t. rewrite !Nat2N.inj_add. lia. }
    assert (Ha : (A.T_forward o (map fst xs) <= k_core * budget)%N).
    { eapply scale_callback; [apply A.T_forward_le|exact core_A|]. unfold work. lia. }
    assert (Hb : (B.T_forward o (map snd xs) <= k_core * budget)%N).
    { eapply scale_callback; [apply B.T_forward_le|exact core_B|]. unfold work. lia. }
    assert (Hsa : (N.of_nat (A.size (A.forward o (map fst xs))) <= k_core * budget)%N).
    { eapply scale_callback; [apply A.forward_size|exact core_A|]. unfold work. lia. }
    assert (Hsb : (N.of_nat (B.size (B.forward o (map snd xs))) <= k_core * budget)%N).
    { eapply scale_callback; [apply B.forward_size|exact core_B|]. unfold work. lia. }
    assert (Hraw : (N.of_nat (size
      (A.forward o (map fst xs), B.forward o (map snd xs)) + 1) <=
      2 * (k_core * budget) + budget)%N).
    { unfold size. cbn [fst snd]. rewrite !Nat2N.inj_add. lia. }
    assert (Hnormal : (T_normalize
      (A.forward o (map fst xs), B.forward o (map snd xs)) <=
      8 * (k_core * k_core * budget) + 4 * (k_core * budget))%N).
    { eapply N.le_trans; [apply normalize_time_bound|].
      replace (8 * (k_core * k_core * budget) + 4 * (k_core * budget))%N with
        (4 * k_core * (2 * (k_core * budget) + budget))%N by ring.
      now apply N.mul_le_mono_l. }
    pose proof (forward_time_parts o xs) as Hparts.
    pose proof (wide_budget budget) as Htotal. lia.
  Qed.
  Lemma T_backward_le : forall o r xs,
    (T_backward o r xs <= c_val * N.of_nat (work o xs + size r + 1))%N.
  Proof.
    intros o [a b] xs. set (budget := N.of_nat (work o xs + size (a, b) + 1)).
    assert (Hbudget : (1 <= budget)%N).
    { unfold budget. rewrite Nat2N.inj_add. lia. }
    assert (Hlength : (N.of_nat (length xs) <= budget)%N).
    { unfold budget, work, t. rewrite !Nat2N.inj_add. lia. }
    assert (Ha : (A.T_backward o a (map fst xs) <= k_core * budget)%N).
    { eapply scale_callback; [apply A.T_backward_le|exact core_A|].
      unfold work, size. cbn [fst snd]. lia. }
    assert (Hb : (B.T_backward o b (map snd xs) <= k_core * budget)%N).
    { eapply scale_callback; [apply B.T_backward_le|exact core_B|].
      unfold work, size. cbn [fst snd]. lia. }
    assert (Hsa : (N.of_nat (fold_right Nat.add 0%nat
      (map A.size (A.backward o a (map fst xs)))) <= k_core * budget)%N).
    { eapply scale_callback; [apply A.backward_size|exact core_A|].
      unfold work, size. cbn [fst snd]. lia. }
    assert (Hsb : (N.of_nat (fold_right Nat.add 0%nat
      (map B.size (B.backward o b (map snd xs)))) <= k_core * budget)%N).
    { eapply scale_callback; [apply B.backward_size|exact core_B|].
      unfold work, size. cbn [fst snd]. lia. }
    assert (Houtlength : (N.of_nat (length (A.backward o a (map fst xs))) <= budget)%N).
    { pose proof (Forall2_length (A.backward_refines o a (map fst xs))) as Heq.
      rewrite length_map in Heq. rewrite Heq. exact Hlength. }
    pose proof (paired_normalize_time_budget _ _ budget Hsa Hsb Houtlength) as Hnormal.
    pose proof (backward_time_parts o (a, b) xs) as Hparts. cbn [fst snd] in Hparts.
    pose proof (wide_budget budget) as Htotal. lia.
  Qed.
  Lemma T_guard_le : forall g xs,
    (T_guard g xs <= c_val * N.of_nat (gwork g xs + 1))%N.
  Proof.
    intros g xs. set (budget := N.of_nat (gwork g xs + 1)).
    assert (Hbudget : (1 <= budget)%N).
    { unfold budget. rewrite Nat2N.inj_add. lia. }
    assert (Hlength : (N.of_nat (length xs) <= budget)%N).
    { unfold budget, gwork, t. rewrite !Nat2N.inj_add. lia. }
    assert (Ha : (A.T_guard g (map fst xs) <= k_core * budget)%N).
    { eapply scale_callback; [apply A.T_guard_le|exact core_A|]. unfold gwork. lia. }
    assert (Hb : (B.T_guard g (map snd xs) <= k_core * budget)%N).
    { eapply scale_callback; [apply B.T_guard_le|exact core_B|]. unfold gwork. lia. }
    assert (Hsa : (N.of_nat (fold_right Nat.add 0%nat
      (map A.size (A.guard g (map fst xs)))) <= k_core * budget)%N).
    { eapply scale_callback; [apply A.guard_size|exact core_A|]. unfold gwork. lia. }
    assert (Hsb : (N.of_nat (fold_right Nat.add 0%nat
      (map B.size (B.guard g (map snd xs)))) <= k_core * budget)%N).
    { eapply scale_callback; [apply B.guard_size|exact core_B|]. unfold gwork. lia. }
    assert (Houtlength : (N.of_nat (length (A.guard g (map fst xs))) <= budget)%N).
    { pose proof (Forall2_length (A.guard_refines g (map fst xs))) as Heq.
      rewrite length_map in Heq. rewrite Heq. exact Hlength. }
    pose proof (paired_normalize_time_budget _ _ budget Hsa Hsb Houtlength) as Hnormal.
    pose proof (guard_time_parts g xs) as Hparts.
    pose proof (wide_budget budget) as Htotal. lia.
  Qed.
  Lemma forward_size : forall o xs,
    (N.of_nat (size (forward o xs)) <= c_val * N.of_nat (work o xs + 1))%N.
  Proof.
    intros o xs. set (budget := N.of_nat (work o xs + 1)).
    assert (Hbudget : (1 <= budget)%N).
    { unfold budget. rewrite Nat2N.inj_add. lia. }
    assert (Ha : (N.of_nat (A.size (A.forward o (map fst xs))) <= k_core * budget)%N).
    { eapply scale_callback; [apply A.forward_size|exact core_A|]. unfold work. lia. }
    assert (Hb : (N.of_nat (B.size (B.forward o (map snd xs))) <= k_core * budget)%N).
    { eapply scale_callback; [apply B.forward_size|exact core_B|]. unfold work. lia. }
    pose proof (normalize_size_bound
      (A.forward o (map fst xs), B.forward o (map snd xs))) as Hsize.
    pose proof (nat_bound _ _ Hsize) as HsizeN.
    change (N.of_nat (size (normalize
      (A.forward o (map fst xs), B.forward o (map snd xs)))) <=
      N.of_nat (A.size (A.forward o (map fst xs)) + B.size (B.forward o (map snd xs)) +
        A.size A.bot + B.size B.bot))%N in HsizeN.
    pose proof (closed_bottom_budget budget Hbudget) as Hbottom.
    pose proof (basic_budget budget) as Htotal.
    change (N.of_nat (size (normalize
      (A.forward o (map fst xs), B.forward o (map snd xs)))) <= c_val * budget)%N.
    rewrite !Nat2N.inj_add in HsizeN, Hbottom. lia.
  Qed.
  Lemma meet_size : forall a b,
    (N.of_nat (size (meet a b)) <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros [a b] [c d]. set (budget := N.of_nat (size (a, b) + size (c, d) + 1)).
    assert (Hbudget : (1 <= budget)%N).
    { unfold budget. rewrite Nat2N.inj_add. lia. }
    assert (Ha : (N.of_nat (A.size (A.meet a c)) <= k_core * budget)%N).
    { eapply scale_callback; [apply A.meet_size|exact core_A|]. unfold size. cbn. lia. }
    assert (Hb : (N.of_nat (B.size (B.meet b d)) <= k_core * budget)%N).
    { eapply scale_callback; [apply B.meet_size|exact core_B|]. unfold size. cbn. lia. }
    pose proof (normalize_size_bound (A.meet a c, B.meet b d)) as Hsize.
    pose proof (nat_bound _ _ Hsize) as HsizeN.
    change (N.of_nat (size (normalize (A.meet a c, B.meet b d))) <=
      N.of_nat (A.size (A.meet a c) + B.size (B.meet b d) +
        A.size A.bot + B.size B.bot))%N in HsizeN.
    pose proof (closed_bottom_budget budget Hbudget) as Hbottom.
    pose proof (basic_budget budget) as Htotal.
    change (N.of_nat (size (normalize (A.meet a c, B.meet b d))) <= c_val * budget)%N.
    rewrite !Nat2N.inj_add in HsizeN, Hbottom. lia.
  Qed.
  Lemma join_size : forall a b,
    (N.of_nat (size (join a b)) <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros [a b] [c d]. set (budget := N.of_nat (size (a, b) + size (c, d) + 1)).
    assert (Ha : (N.of_nat (A.size (A.join a c)) <= k_core * budget)%N).
    { eapply scale_callback; [apply A.join_size|exact core_A|]. unfold size. cbn. lia. }
    assert (Hb : (N.of_nat (B.size (B.join b d)) <= k_core * budget)%N).
    { eapply scale_callback; [apply B.join_size|exact core_B|]. unfold size. cbn. lia. }
    pose proof (basic_budget budget) as Htotal.
    unfold join, product_pair, size. cbn [fst snd]. rewrite Nat2N.inj_add. lia.
  Qed.
  Lemma widen_size : forall p a b,
    (N.of_nat (size (widen p a b)) <=
      c_val * N.of_nat (size a + size b + wsize p + 1))%N.
  Proof.
    intros [pa pb] [a b] [c d].
    set (budget := N.of_nat (size (a, b) + size (c, d) + wsize (pa, pb) + 1)).
    assert (Ha : (N.of_nat (A.size (A.widen pa a c)) <= k_core * budget)%N).
    { eapply scale_callback; [apply A.widen_size|exact core_A|].
      unfold size, wsize. cbn. lia. }
    assert (Hb : (N.of_nat (B.size (B.widen pb b d)) <= k_core * budget)%N).
    { eapply scale_callback; [apply B.widen_size|exact core_B|].
      unfold size, wsize. cbn. lia. }
    pose proof (basic_budget budget) as Htotal.
    pose proof (core_budget_dom budget) as Hdom.
    unfold widen, product_widen.
    destruct (product_is_bot A.is_bot B.is_bot (c, d)).
    - assert (Hinput : (N.of_nat (size (a, b)) <= budget)%N).
      { unfold budget. rewrite !Nat2N.inj_add. lia. }
      lia.
    - unfold size. cbn [fst snd]. rewrite Nat2N.inj_add. lia.
  Qed.
  Lemma backward_size : forall o r xs,
    (N.of_nat (fold_right Nat.add 0%nat (map size (backward o r xs))) <=
      c_val * N.of_nat (work o xs + size r + 1))%N.
  Proof.
    intros o [a b] xs. set (budget := N.of_nat (work o xs + size (a, b) + 1)).
    unfold backward, product_backward. cbn [fst snd]. apply paired_size_budget.
    - eapply scale_callback; [apply A.backward_size|exact core_A|].
      unfold work, size. cbn [fst snd]. lia.
    - eapply scale_callback; [apply B.backward_size|exact core_B|].
      unfold work, size. cbn [fst snd]. lia.
    - pose proof (Forall2_length (A.backward_refines o a (map fst xs))) as Hlength.
      rewrite length_map in Hlength. rewrite Hlength.
      unfold budget, work, t. rewrite !Nat2N.inj_add. lia.
  Qed.
  Lemma guard_size : forall g xs,
    (N.of_nat (fold_right Nat.add 0%nat (map size (guard g xs))) <=
      c_val * N.of_nat (gwork g xs + 1))%N.
  Proof.
    intros g xs. set (budget := N.of_nat (gwork g xs + 1)).
    unfold guard, product_guard. apply paired_size_budget.
    - eapply scale_callback; [apply A.guard_size|exact core_A|]. unfold gwork. lia.
    - eapply scale_callback; [apply B.guard_size|exact core_B|]. unfold gwork. lia.
    - pose proof (Forall2_length (A.guard_refines g (map fst xs))) as Hlength.
      rewrite length_map in Hlength. rewrite Hlength.
      unfold budget, gwork, t. rewrite !Nat2N.inj_add. lia.
  Qed.
  Lemma work_sizes : forall o xs,
    fold_right Nat.add 0%nat (map size xs) <= work o xs.
  Proof.
    intros o xs. rewrite sum_sizes. unfold work.
    pose proof (A.work_sizes o (map fst xs)). pose proof (B.work_sizes o (map snd xs)). lia.
  Qed.
  Lemma gwork_sizes : forall g xs,
    fold_right Nat.add 0%nat (map size xs) <= gwork g xs.
  Proof.
    intros g xs. rewrite sum_sizes. unfold gwork.
    pose proof (A.gwork_sizes g (map fst xs)). pose proof (B.gwork_sizes g (map snd xs)). lia.
  Qed.

  Lemma T_normalize_le : forall a b,
    (T_normalize (a, b) <= c_product * N.of_nat (A.size a + B.size b + 1))%N.
  Proof.
    intros a b. eapply N.le_trans; [apply normalize_time_bound|].
    unfold c_product, size. cbn [fst snd]. apply N.mul_le_mono_r. lia.
  Qed.
  Lemma T_forward_components : forall o xs,
    (T_forward o xs <= c_product *
      (N.of_nat (length xs) + A.T_forward o (map fst xs) +
       B.T_forward o (map snd xs) +
       T_normalize (A.forward o (map fst xs), B.forward o (map snd xs)) + 1))%N.
  Proof.
    intros o xs. eapply N.le_trans; [apply forward_time_parts|].
    eapply N.le_trans with (m := (16 *
      (N.of_nat (length xs) + A.T_forward o (map fst xs) +
        B.T_forward o (map snd xs) +
        T_normalize (A.forward o (map fst xs), B.forward o (map snd xs)) + 1))%N).
    - lia.
    - apply N.mul_le_mono_r. unfold c_product. pose proof (proj1 core_bounds). lia.
  Qed.
  Lemma T_backward_components : forall o r xs,
    (T_backward o r xs <= c_product *
      (N.of_nat (length xs) + A.T_backward o (fst r) (map fst xs) +
       B.T_backward o (snd r) (map snd xs) +
       fold_right N.add 0%N (map T_normalize
         (combine (A.backward o (fst r) (map fst xs))
           (B.backward o (snd r) (map snd xs)))) + 1))%N.
  Proof.
    intros o r xs. eapply N.le_trans; [apply backward_time_parts|].
    eapply N.le_trans with (m := (16 *
      (N.of_nat (length xs) + A.T_backward o (fst r) (map fst xs) +
        B.T_backward o (snd r) (map snd xs) +
        fold_right N.add 0%N (map T_normalize
          (combine (A.backward o (fst r) (map fst xs))
            (B.backward o (snd r) (map snd xs)))) + 1))%N).
    - lia.
    - apply N.mul_le_mono_r. unfold c_product. pose proof (proj1 core_bounds). lia.
  Qed.
  Lemma T_guard_components : forall g xs,
    (T_guard g xs <= c_product *
      (N.of_nat (length xs) + A.T_guard g (map fst xs) +
       B.T_guard g (map snd xs) +
       fold_right N.add 0%N (map T_normalize
         (combine (A.guard g (map fst xs)) (B.guard g (map snd xs)))) + 1))%N.
  Proof.
    intros g xs. eapply N.le_trans; [apply guard_time_parts|].
    eapply N.le_trans with (m := (16 *
      (N.of_nat (length xs) + A.T_guard g (map fst xs) +
        B.T_guard g (map snd xs) +
        fold_right N.add 0%N (map T_normalize
          (combine (A.guard g (map fst xs)) (B.guard g (map snd xs)))) + 1))%N).
    - lia.
    - apply N.mul_le_mono_r. unfold c_product. pose proof (proj1 core_bounds). lia.
  Qed.
  Lemma forward_complexity :
    T_forward o xs ∈ 𝑂(N.of_nat (work o xs)) for (o, xs).
  Proof.
    exists c_val. intros [o xs] _. cbn [fst snd].
    pose proof (T_forward_le o xs) as Htime.
    rewrite Nat2N.inj_add in Htime. time_cbn_all. exact Htime.
  Qed.
  (** Backward transfer has the published work-plus-request class. *)
  Lemma backward_complexity : (bigO (fun _ => True)
    (fun x => N.of_nat ((work (fst x) (snd (snd x)) + size (fst (snd x)))%nat))
    (fun x => T_backward (fst x) (fst (snd x)) (snd (snd x))))%N.
  Proof.
    exists c_val. intros [o [r xs]] _. cbn [fst snd].
    pose proof (T_backward_le o r xs) as Htime.
    rewrite Nat2N.inj_add in Htime. time_cbn_all. exact Htime.
  Qed.
  (** Guard transfer has the published guard-work class. *)
  Lemma guard_complexity :
    T_guard g xs ∈ 𝑂(N.of_nat ((gwork g xs)%nat)) for (g, xs).
  Proof.
    exists c_val. intros [g xs] _. cbn [fst snd].
    pose proof (T_guard_le g xs) as Htime.
    rewrite Nat2N.inj_add in Htime. time_cbn_all. exact Htime.
  Qed.

  Definition k_product_lists : N := 16%N.
  Lemma gamma_def : forall a b c,
    gamma (a, b) c <-> A.gamma a c /\ B.gamma b c.
  Proof.
    reflexivity.
  Qed.
  Lemma leb_def : forall a b,
    leb a b = orb (is_bot a) (andb (A.leb (fst a) (fst b)) (B.leb (snd a) (snd b))).
  Proof.
    reflexivity.
  Qed.
  Lemma widen_def : forall p a b,
    widen p a b = if is_bot b then a
      else (A.widen (fst p) (fst a) (fst b), B.widen (snd p) (snd a) (snd b)).
  Proof.
    reflexivity.
  Qed.
  Lemma wrank_def : forall p a b,
    wrank p (a, b) = A.wrank (fst p) a + B.wrank (snd p) b.
  Proof.
    reflexivity.
  Qed.
  Lemma size_def : forall a b, size (a, b) = A.size a + B.size b.
  Proof.
    reflexivity.
  Qed.
  Lemma is_bot_def : forall a b,
    is_bot (a, b) = orb (A.is_bot a) (B.is_bot b).
  Proof.
    reflexivity.
  Qed.
  Lemma narrow_def : forall a b,
    narrow a b = if is_bot b then b
      else (A.narrow (fst a) (fst b), B.narrow (snd a) (snd b)).
  Proof.
    reflexivity.
  Qed.
  Lemma wunits_def : forall a b, wunits (a, b) = A.wunits a + B.wunits b.
  Proof.
    reflexivity.
  Qed.
  Lemma T_leb_split : forall a b,
    (T_leb a b <= k_product_lists *
      (A.T_is_bot (fst a) + B.T_is_bot (snd a) +
       A.T_leb (fst a) (fst b) + B.T_leb (snd a) (snd b) + 1))%N.
  Proof.
    intros [a b] [c d]. unfold k_product_lists.
    time_unfold T_leb. time_unfold @T_product_leb. time_unfold @T_product_is_bot.
    time_cbn. time_pose. lia.
  Qed.
End ProductT.
