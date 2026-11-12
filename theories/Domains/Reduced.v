(** * Reduced value products

    Reduced products apply a fixed number of reduction rounds after transfers.
    For example, backward transfer reduces each paired result.
    Builds on: ProductSig and value products. *)

From Stdlib Require Import List Arith.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig ProductSig Product.

Module ReducedCode (L : LANG_OPS) (A B : VALUE_DOMAIN_OPS L)
    (R : REDUCER_OPS A B) (K : ROUNDS) <: REDUCED_OPS L A B R K.
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
  Definition red (x : t) : t := normalize (Nat.iter K.rounds R.reduce x).
  Definition forward (o : L.op) (xs : list t) : t :=
    red (product_forward A.is_bot B.is_bot A.bot B.bot A.forward B.forward o xs).
  Definition backward (o : L.op) (r : t) (xs : list t) : list t :=
    map red (product_backward A.is_bot B.is_bot A.bot B.bot A.backward B.backward o r xs).
  Definition guard (g : L.guard) (xs : list t) : list t :=
    map red (product_guard A.is_bot B.is_bot A.bot B.bot A.guard B.guard g xs).
End ReducedCode.

Module Reduced (L : LANG) (A B : VALUE_DOMAIN L) (R : VALUE_REDUCER L A B)
    (K : ROUNDS) <: REDUCED L A B R K.
  Include ReducedCode L A B R K.
  Definition wrank (p : wparam) (a : t) : nat :=
    A.wrank (fst p) (fst a) + B.wrank (snd p) (snd a).
  Definition gamma (a : t) (c : L.val) : Prop := A.gamma (fst a) c /\ B.gamma (snd a) c.
  Lemma leb_refl : forall a, leb a a = true.
  Proof. Admitted. (* CONVERT: slots2_laws: The variable slots_leb was not found in the current environment. *)
  (** The order composes through an intermediate value. *)
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof. Admitted. (* CONVERT: slots2_laws: The variable slots_leb was not found in the current environment. *)
  (** Bottom is below every value. *)
  Lemma bot_least : forall a, leb bot a = true.
  Proof. Admitted. (* CONVERT: slots2_laws: The reference slots_reduce was not found in the current environment. *)
  (** The bottom test recognizes bottom. *)
  Lemma is_bot_bot : is_bot bot = true.
  Proof. Admitted.
  (** Every recognized bottom is below every value. *)
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof. Admitted.
  (** Join is above its left operand. *)
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof. Admitted. (* CONVERT: slots2_laws: The reference slots_reduce was not found in the current environment. *)
  (** Join is above its right operand. *)
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof. Admitted. (* CONVERT: slots2_laws: The reference slots_reduce was not found in the current environment. *)

  Lemma top_greatest : forall a, leb a top = true.
  Proof. Admitted. (* CONVERT: slots2_top: The variable slots_leb was not found in the current environment. *)

  Lemma meet_lb_l : forall a b, leb (meet a b) a = true.
  Proof. Admitted.
  (** Meet is below its right operand. *)
  Lemma meet_lb_r : forall a b, leb (meet a b) b = true.
  Proof. Admitted.

  (** Widening is above its previous value. *)
  Lemma widen_ub_l : forall p a b, leb a (widen p a b) = true.
  Proof. Admitted. (* CONVERT: slots2_laws: The reference slots_reduce was not found in the current environment. *)
  (** Widening is above its candidate value. *)
  Lemma widen_ub_r : forall p a b, leb b (widen p a b) = true.
  Proof. Admitted. (* CONVERT: slots2_laws: The reference slots_reduce was not found in the current environment. *)
  (** A candidate below the previous value leaves widening unchanged. *)
  Lemma widen_stable : forall p a b, leb b a = true -> widen p a b = a.
  Proof. Admitted.
  (** An unstable widening from a nonbottom strictly decreases rank. *)
  Lemma wrank_widen : forall p a b, is_bot a = false -> leb b a = false ->
    wrank p (widen p a b) < wrank p a.
  Proof. Admitted. (* CONVERT: slots2_wrank: The reference slots_reduce was not found in the current environment. *)
  (** Widening from a nonbottom does not increase rank. *)
  Lemma wrank_widen_le : forall p a b, is_bot a = false -> wrank p (widen p a b) <= wrank p a.
  Proof. Admitted. (* CONVERT: slots2_wrank: The reference slots_reduce was not found in the current environment. *)
  (** Narrowing stays between an ordered candidate and previous value. *)
  Lemma narrow_between : forall a b, leb b a = true ->
    leb b (narrow a b) = true /\ leb (narrow a b) a = true.
  Proof. Admitted. (* CONVERT: slots2_laws: The variable slots_leb was not found in the current environment. *)

  (** Abstract inclusion entails concrete inclusion. *)
  Lemma gamma_mono : forall a b c, leb a b = true -> gamma a c -> gamma b c.
  Proof. Admitted. (* CONVERT: slots2_gamma_laws: The variable slots_leb was not found in the current environment. *)
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
  Proof. Admitted. (* CONVERT: product_laws: The variable product_arguments was not found in the current *)
  (** Backward transfer retains operands consistent with the abstract result. *)
  Lemma backward_sound : forall o r xs cs c,
    Forall2 gamma xs cs -> L.eval o cs = Some c -> gamma r c ->
    Forall2 gamma (backward o r xs) cs.
  Proof. Admitted. (* CONVERT: product_laws: The variable product_arguments was not found in the current *)
  (** Backward transfer refines each operand in its original position. *)
  Lemma backward_refines : forall o r xs,
    Forall2 (fun y x => leb y x = true) (backward o r xs) xs.
  Proof. Admitted.
  (** Guard transfer retains operands satisfying the concrete guard. *)
  Lemma guard_sound : forall g xs cs,
    Forall2 gamma xs cs -> L.holds g cs -> Forall2 gamma (guard g xs) cs.
  Proof. Admitted. (* CONVERT: product_laws: The variable product_arguments was not found in the current *)
  (** Guard transfer refines each operand in its original position. *)
  Lemma guard_refines : forall g xs,
    Forall2 (fun y x => leb y x = true) (guard g xs) xs.
  Proof. Admitted.
End Reduced.
