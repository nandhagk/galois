(** * Value products

    Products apply value transfers to each component independently.
    For example, a forward transfer pairs the two component results.
    Builds on: ProductSig and lattice products. *)

From Stdlib Require Import List NArith.
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
  Proof. Admitted. (* STUB *)
  (** Every recognized bottom is below every value. *)
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof. Admitted. (* STUB *)
  (** Join is above its left operand. *)
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof. Admitted. (* CONVERT: slots2_laws: The reference slots_reduce was not found in the current environment. *)
  (** Join is above its right operand. *)
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof. Admitted. (* CONVERT: slots2_laws: The reference slots_reduce was not found in the current environment. *)

  Lemma top_greatest : forall a, leb a top = true.
  Proof. Admitted. (* CONVERT: slots2_top: The variable slots_leb was not found in the current environment. *)

  Lemma meet_lb_l : forall a b, leb (meet a b) a = true.
  Proof. Admitted. (* STUB *)
  (** Meet is below its right operand. *)
  Lemma meet_lb_r : forall a b, leb (meet a b) b = true.
  Proof. Admitted. (* STUB *)

  (** Widening is above its previous value. *)
  Lemma widen_ub_l : forall p a b, leb a (widen p a b) = true.
  Proof. Admitted. (* CONVERT: slots2_laws: The reference slots_reduce was not found in the current environment. *)
  (** Widening is above its candidate value. *)
  Lemma widen_ub_r : forall p a b, leb b (widen p a b) = true.
  Proof. Admitted. (* CONVERT: slots2_laws: The reference slots_reduce was not found in the current environment. *)
  (** A candidate below the previous value leaves widening unchanged. *)
  Lemma widen_stable : forall p a b, leb b a = true -> widen p a b = a.
  Proof. Admitted. (* STUB *)
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
  Proof. Admitted. (* STUB *)
  (** A positive bottom test excludes every concrete value. *)
  Lemma is_bot_sound : forall a c, is_bot a = true -> ~ gamma a c.
  Proof. Admitted. (* STUB *)
  (** Every value below a recognized bottom is recognized as bottom. *)
  Lemma is_bot_below : forall a b, leb a b = true -> is_bot b = true -> is_bot a = true.
  Proof. Admitted. (* STUB *)
  (** Forward transfer contains every successful concrete result. *)
  Lemma forward_sound : forall o xs cs c,
    Forall2 gamma xs cs -> L.eval o cs = Some c -> gamma (forward o xs) c.
  Proof. Admitted. (* CONVERT: product_laws: The variable product_arguments was not found. *)
  (** Backward transfer retains operands consistent with the abstract result. *)
  Lemma backward_sound : forall o r xs cs c,
    Forall2 gamma xs cs -> L.eval o cs = Some c -> gamma r c ->
    Forall2 gamma (backward o r xs) cs.
  Proof. Admitted. (* CONVERT: product_laws: The variable product_arguments was not found in the current *)
  (** Backward transfer refines each operand in its original position. *)
  Lemma backward_refines : forall o r xs,
    Forall2 (fun y x => leb y x = true) (backward o r xs) xs.
  Proof. Admitted. (* STUB *)
  (** Guard transfer retains operands satisfying the concrete guard. *)
  Lemma guard_sound : forall g xs cs,
    Forall2 gamma xs cs -> L.holds g cs -> Forall2 gamma (guard g xs) cs.
  Proof. Admitted. (* CONVERT: product_laws: The variable product_arguments was not found in the current *)
  (** Guard transfer refines each operand in its original position. *)
  Lemma guard_refines : forall g xs,
    Forall2 (fun y x => leb y x = true) (guard g xs) xs.
  Proof. Admitted. (* STUB *)
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
  Proof. Admitted. (* STUB *)
  Lemma F2_leb : forall a b,
    leb a b = orb (is_bot a) (andb (A.leb (fst a) (fst b)) (B.leb (snd a) (snd b))).
  Proof. Admitted. (* STUB *)
  Lemma F3_widen : forall p a b,
    widen p a b = if is_bot b then a
      else (A.widen (fst p) (fst a) (fst b), B.widen (snd p) (snd a) (snd b)).
  Proof. Admitted. (* STUB *)
  Lemma F4_wrank : forall p a b,
    wrank p (a, b) = A.wrank (fst p) a + B.wrank (snd p) b.
  Proof. Admitted. (* STUB *)
  Lemma F5_size : forall a b, size (a, b) = A.size a + B.size b.
  Proof. Admitted. (* STUB *)
  Lemma F6_is_bot : forall a b,
    is_bot (a, b) = orb (A.is_bot a) (B.is_bot b).
  Proof. Admitted. (* STUB *)
  Lemma F7_narrow : forall a b,
    narrow a b = if is_bot b then b
      else (A.narrow (fst a) (fst b), B.narrow (snd a) (snd b)).
  Proof. Admitted. (* STUB *)
  Lemma F_wunits : forall a b, wunits (a, b) = A.wunits a + B.wunits b.
  Proof. Admitted. (* STUB *)
  Lemma T1_leb_components : forall a b,
    (T_leb a b <= k_product_lists *
      (A.T_is_bot (fst a) + B.T_is_bot (snd a) +
       A.T_leb (fst a) (fst b) + B.T_leb (snd a) (snd b) + 1))%N.
  Proof. Admitted. (* STUB *)
End ProductT.
