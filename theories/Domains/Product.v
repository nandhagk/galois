(** * Value products

    Products apply value transfers to each component independently.
    For example, a forward transfer pairs the two component results.
    Builds on: ProductSig and lattice products. *)

From Stdlib Require Import List.
From Galois.Lattice Require Import Product.
From Galois.Domains Require Import LangSig ValueSig ProductSig.

Module ProductCode (L : LANG_OPS) (A B : VALUE_DOMAIN_OPS L) <: PRODUCT_OPS L A B.
  Definition t := (A.t * B.t)%type.
  Definition bot : t := (A.bot, B.bot).
  Definition is_bot (x : t) := orb (A.is_bot (fst x)) (B.is_bot (snd x)).
  Definition leb (x y : t) :=
    orb (is_bot x) (andb (A.leb (fst x) (fst y)) (B.leb (snd x) (snd y))).
  Definition join (x y : t) : t := (A.join (fst x) (fst y), B.join (snd x) (snd y)).
  Definition normalize (x : t) : t :=
    if orb (A.is_bot (fst x)) (B.is_bot (snd x)) then bot else x.
  Definition top : t := (A.top, B.top).
  Definition meet (x y : t) : t :=
    normalize (A.meet (fst x) (fst y), B.meet (snd x) (snd y)).
  Definition wparam := (A.wparam * B.wparam)%type.
  Definition widen (p : wparam) (x y : t) : t :=
    if is_bot y then x
    else (A.widen (fst p) (fst x) (fst y), B.widen (snd p) (snd x) (snd y)).
  Definition narrow (x y : t) : t :=
    if is_bot y then y else (A.narrow (fst x) (fst y), B.narrow (snd x) (snd y)).
  Definition forward (o : L.op) (xs : list t) : t :=
    normalize (A.forward o (map fst xs), B.forward o (map snd xs)).
  Definition backward (o : L.op) (r : t) (xs : list t) : list t :=
    map normalize
      (combine (A.backward o (fst r) (map fst xs)) (B.backward o (snd r) (map snd xs))).
  Definition guard (g : L.guard) (xs : list t) : list t :=
    map normalize (combine (A.guard g (map fst xs)) (B.guard g (map snd xs))).
End ProductCode.

Module Product (L : LANG) (A B : VALUE_DOMAIN L) <: PRODUCT L A B.
  Include ProductCode L A B.
  Definition wrank (p : wparam) (a : t) : nat :=
    A.wrank (fst p) (fst a) + B.wrank (snd p) (snd a).
  Definition gamma (a : t) (c : L.val) : Prop := A.gamma (fst a) c /\ B.gamma (snd a) c.
  Lemma leb_refl : forall a, leb a a = true.
  Proof. Admitted.
  (** The order composes through an intermediate value. *)
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof. Admitted.
  (** Bottom is below every value. *)
  Lemma bot_least : forall a, leb bot a = true.
  Proof. Admitted.
  (** The bottom test recognizes bottom. *)
  Lemma is_bot_bot : is_bot bot = true.
  Proof. Admitted.
  (** Every recognized bottom is below every value. *)
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof. Admitted.
  (** Join is above its left operand. *)
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof. Admitted.
  (** Join is above its right operand. *)
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof. Admitted.

  Lemma top_greatest : forall a, leb a top = true.
  Proof. Admitted.

  Lemma meet_lb_l : forall a b, leb (meet a b) a = true.
  Proof. Admitted.
  (** Meet is below its right operand. *)
  Lemma meet_lb_r : forall a b, leb (meet a b) b = true.
  Proof. Admitted.

  (** Widening is above its previous value. *)
  Lemma widen_ub_l : forall p a b, leb a (widen p a b) = true.
  Proof. Admitted.
  (** Widening is above its candidate value. *)
  Lemma widen_ub_r : forall p a b, leb b (widen p a b) = true.
  Proof. Admitted.
  (** A candidate below the previous value leaves widening unchanged. *)
  Lemma widen_stable : forall p a b, leb b a = true -> widen p a b = a.
  Proof. Admitted.
  (** An unstable widening from a nonbottom strictly decreases rank. *)
  Lemma wrank_widen : forall p a b, is_bot a = false -> leb b a = false ->
    wrank p (widen p a b) < wrank p a.
  Proof. Admitted.
  (** Widening from a nonbottom does not increase rank. *)
  Lemma wrank_widen_le : forall p a b, is_bot a = false -> wrank p (widen p a b) <= wrank p a.
  Proof. Admitted.
  (** Narrowing stays between an ordered candidate and previous value. *)
  Lemma narrow_between : forall a b, leb b a = true ->
    leb b (narrow a b) = true /\ leb (narrow a b) a = true.
  Proof. Admitted.

  (** Abstract inclusion entails concrete inclusion. *)
  Lemma gamma_mono : forall a b c, leb a b = true -> gamma a c -> gamma b c.
  Proof. Admitted.
  (** Bottom describes no concrete value. *)
  Lemma gamma_bot : forall c, ~ gamma bot c.
  Proof. Admitted.
  (** Top describes every concrete value. *)
  Lemma gamma_top : forall c, gamma top c.
  Proof. Admitted.
  (** Meet retains values described by both operands. *)
  Lemma gamma_meet : forall a b c, gamma a c -> gamma b c -> gamma (meet a b) c.
  Proof. Admitted.
  (** A positive bottom test excludes every concrete value. *)
  Lemma is_bot_sound : forall a c, is_bot a = true -> ~ gamma a c.
  Proof. Admitted.
  (** Every value below a recognized bottom is recognized as bottom. *)
  Lemma is_bot_below : forall a b, leb a b = true -> is_bot b = true -> is_bot a = true.
  Proof. Admitted.
  (** Forward transfer contains every successful concrete result. *)
  Lemma forward_sound : forall o xs cs c,
    Forall2 gamma xs cs -> L.eval o cs = Some c -> gamma (forward o xs) c.
  Proof. Admitted.
  (** Backward transfer retains operands consistent with the abstract result. *)
  Lemma backward_sound : forall o r xs cs c,
    Forall2 gamma xs cs -> L.eval o cs = Some c -> gamma r c ->
    Forall2 gamma (backward o r xs) cs.
  Proof. Admitted.
  (** Backward transfer refines each operand in its original position. *)
  Lemma backward_refines : forall o r xs,
    Forall2 (fun y x => leb y x = true) (backward o r xs) xs.
  Proof. Admitted.
  (** Guard transfer retains operands satisfying the concrete guard. *)
  Lemma guard_sound : forall g xs cs,
    Forall2 gamma xs cs -> L.holds g cs -> Forall2 gamma (guard g xs) cs.
  Proof. Admitted.
  (** Guard transfer refines each operand in its original position. *)
  Lemma guard_refines : forall g xs,
    Forall2 (fun y x => leb y x = true) (guard g xs) xs.
  Proof. Admitted.
End Product.
