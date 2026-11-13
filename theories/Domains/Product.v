(** * Value products

    Products apply value transfers to each component independently.
    For example, a forward transfer pairs the two component results.
    Builds on: ProductSig and lattice products. *)

From Stdlib Require Import List NArith Bool Lia.
From Argent Require Import Time Std BigO.
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
  Definition c_val : N := 1%N. (* STUB *)
  Definition c_lat : N := c_val.
  (** The lattice constant pays for at least one call. *)
  Lemma c_lat_pos : (1 <= c_lat)%N.
  Proof. Admitted. (* STUB *)
  Definition c_product : N := 1%N. (* STUB *)

  Lemma T_leb_le : forall a b,
    (T_leb a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_join_le : forall a b,
    (T_join a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_meet_le : forall a b,
    (T_meet a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_is_bot_le : forall a,
    (T_is_bot a <= c_val * N.of_nat (size a + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_widen_le : forall p a b,
    (T_widen p a b <= c_val * N.of_nat (size a + size b + wsize p + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_narrow_le : forall a b,
    (T_narrow a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_forward_le : forall o xs,
    (T_forward o xs <= c_val * N.of_nat (work o xs + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_backward_le : forall o r xs,
    (T_backward o r xs <= c_val * N.of_nat (work o xs + size r + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_guard_le : forall g xs,
    (T_guard g xs <= c_val * N.of_nat (gwork g xs + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma forward_size : forall o xs,
    (N.of_nat (size (forward o xs)) <= c_val * N.of_nat (work o xs + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma meet_size : forall a b,
    (N.of_nat (size (meet a b)) <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma join_size : forall a b,
    (N.of_nat (size (join a b)) <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma widen_size : forall p a b,
    (N.of_nat (size (widen p a b)) <=
      c_val * N.of_nat (size a + size b + wsize p + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma backward_size : forall o r xs,
    (N.of_nat (fold_right Nat.add 0%nat (map size (backward o r xs))) <=
      c_val * N.of_nat (work o xs + size r + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma guard_size : forall g xs,
    (N.of_nat (fold_right Nat.add 0%nat (map size (guard g xs))) <=
      c_val * N.of_nat (gwork g xs + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma work_sizes : forall o xs,
    fold_right Nat.add 0%nat (map size xs) <= work o xs.
  Proof. Admitted. (* STUB *)
  Lemma gwork_sizes : forall g xs,
    fold_right Nat.add 0%nat (map size xs) <= gwork g xs.
  Proof. Admitted. (* STUB *)

  Lemma T_normalize_le : forall a b,
    (T_normalize (a, b) <= c_product * N.of_nat (A.size a + B.size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_forward_components : forall o xs,
    (T_forward o xs <= c_product *
      (N.of_nat (length xs) + A.T_forward o (map fst xs) +
       B.T_forward o (map snd xs) +
       T_normalize (A.forward o (map fst xs), B.forward o (map snd xs)) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_backward_components : forall o r xs,
    (T_backward o r xs <= c_product *
      (N.of_nat (length xs) + A.T_backward o (fst r) (map fst xs) +
       B.T_backward o (snd r) (map snd xs) +
       fold_right N.add 0%N (map T_normalize
         (combine (A.backward o (fst r) (map fst xs))
           (B.backward o (snd r) (map snd xs)))) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_guard_components : forall g xs,
    (T_guard g xs <= c_product *
      (N.of_nat (length xs) + A.T_guard g (map fst xs) +
       B.T_guard g (map snd xs) +
       fold_right N.add 0%N (map T_normalize
         (combine (A.guard g (map fst xs)) (B.guard g (map snd xs)))) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma forward_bigO : (bigO (fun _ => True)
    (fun ox => N.of_nat (work (fst ox) (snd ox)))
    (fun ox => T_forward (fst ox) (snd ox)))%N.
  Proof. Admitted. (* STUB *)

  Definition k_product_lists : N := 1%N. (* STUB *)
  Lemma F1_gamma : forall a b c,
    gamma (a, b) c <-> A.gamma a c /\ B.gamma b c.
  Proof.
    reflexivity.
  Qed.
  Lemma F2_leb : forall a b,
    leb a b = orb (is_bot a) (andb (A.leb (fst a) (fst b)) (B.leb (snd a) (snd b))).
  Proof.
    reflexivity.
  Qed.
  Lemma F3_widen : forall p a b,
    widen p a b = if is_bot b then a
      else (A.widen (fst p) (fst a) (fst b), B.widen (snd p) (snd a) (snd b)).
  Proof.
    reflexivity.
  Qed.
  Lemma F4_wrank : forall p a b,
    wrank p (a, b) = A.wrank (fst p) a + B.wrank (snd p) b.
  Proof.
    reflexivity.
  Qed.
  Lemma F5_size : forall a b, size (a, b) = A.size a + B.size b.
  Proof.
    reflexivity.
  Qed.
  Lemma F6_is_bot : forall a b,
    is_bot (a, b) = orb (A.is_bot a) (B.is_bot b).
  Proof.
    reflexivity.
  Qed.
  Lemma F7_narrow : forall a b,
    narrow a b = if is_bot b then b
      else (A.narrow (fst a) (fst b), B.narrow (snd a) (snd b)).
  Proof.
    reflexivity.
  Qed.
  Lemma F_wunits : forall a b, wunits (a, b) = A.wunits a + B.wunits b.
  Proof.
    reflexivity.
  Qed.
  Lemma T1_leb_components : forall a b,
    (T_leb a b <= k_product_lists *
      (A.T_is_bot (fst a) + B.T_is_bot (snd a) +
       A.T_leb (fst a) (fst b) + B.T_leb (snd a) (snd b) + 1))%N.
  Proof. Admitted. (* STUB *)
End ProductT.
