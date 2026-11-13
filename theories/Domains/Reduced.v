(** * Reduced value products

    Reduced products apply a fixed number of reduction rounds after transfers.
    For example, backward transfer reduces each paired result.
    Builds on: ProductSig and value products. *)

From Stdlib Require Import List Arith NArith Lia.
From Argent Require Import Time Tactics Std BigO.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig ProductSig Product.

Module Datatypes.
  TimeFun Corelib.Init.Datatypes.nat_rect.
End Datatypes.

Module Nat.
  TimeFun Nat.iter.
End Nat.

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
  Module P := Product L A B.
  Definition wrank (p : wparam) (a : t) : nat :=
    A.wrank (fst p) (fst a) + B.wrank (snd p) (snd a).
  Definition gamma (a : t) (c : L.val) : Prop := A.gamma (fst a) c /\ B.gamma (snd a) c.
  Lemma leb_refl : forall a, leb a a = true.
  Proof.
    exact P.leb_refl.
  Qed.
  (** The order composes through an intermediate value. *)
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof.
    exact P.leb_trans.
  Qed.
  (** Bottom is below every value. *)
  Lemma bot_least : forall a, leb bot a = true.
  Proof.
    exact P.bot_least.
  Qed.
  (** The bottom test recognizes bottom. *)
  Lemma is_bot_bot : is_bot bot = true.
  Proof.
    exact P.is_bot_bot.
  Qed.
  (** Every recognized bottom is below every value. *)
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof.
    exact P.is_bot_least.
  Qed.
  (** Join is above its left operand. *)
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof.
    exact P.join_ub_l.
  Qed.
  (** Join is above its right operand. *)
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof.
    exact P.join_ub_r.
  Qed.

  Lemma top_greatest : forall a, leb a top = true.
  Proof.
    exact P.top_greatest.
  Qed.

  Lemma meet_lb_l : forall a b, leb (meet a b) a = true.
  Proof.
    exact P.meet_lb_l.
  Qed.
  (** Widening is above its previous value. *)
  Lemma widen_ub_l : forall p a b, leb a (widen p a b) = true.
  Proof.
    exact P.widen_ub_l.
  Qed.
  (** Widening is above its candidate value. *)
  Lemma widen_ub_r : forall p a b, leb b (widen p a b) = true.
  Proof.
    exact P.widen_ub_r.
  Qed.
  (** A candidate below the previous value leaves widening unchanged. *)
  Lemma widen_stable : forall p a b, leb b a = true -> widen p a b = a.
  Proof.
    exact P.widen_stable.
  Qed.
  (** An unstable widening from a nonbottom strictly decreases rank. *)
  Lemma wrank_widen : forall p a b, is_bot a = false -> leb b a = false ->
    wrank p (widen p a b) < wrank p a.
  Proof.
    exact P.wrank_widen.
  Qed.
  (** Widening from a nonbottom does not increase rank. *)
  Lemma wrank_widen_le : forall p a b, is_bot a = false -> wrank p (widen p a b) <= wrank p a.
  Proof.
    exact P.wrank_widen_le.
  Qed.
  (** Narrowing stays between an ordered candidate and previous value. *)
  Lemma narrow_between : forall a b, leb b a = true ->
    leb b (narrow a b) = true /\ leb (narrow a b) a = true.
  Proof.
    exact P.narrow_between.
  Qed.

  (** Abstract inclusion entails concrete inclusion. *)
  Lemma gamma_mono : forall a b c, leb a b = true -> gamma a c -> gamma b c.
  Proof.
    exact P.gamma_mono.
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
    exact P.gamma_meet.
  Qed.
  (** A positive bottom test excludes every concrete value. *)
  Lemma is_bot_sound : forall a c, is_bot a = true -> ~ gamma a c.
  Proof.
    exact P.is_bot_sound.
  Qed.
  (** Every value below a recognized bottom is recognized as bottom. *)
  Lemma is_bot_below : forall a b, leb a b = true -> is_bot b = true -> is_bot a = true.
  Proof.
    exact P.is_bot_below.
  Qed.

  (** One reduction round preserves every value shared by the two components. *)
  Lemma step_sound : forall x c, gamma x c -> gamma (R.reduce x) c.
  Proof.
    intros [a b] c [Ha Hb]. exact (R.reduce_sound a b c Ha Hb).
  Qed.

  (** Every finite sequence of reduction rounds preserves shared concrete values. *)
  Lemma iter_sound : forall n x c, gamma x c -> gamma (Nat.iter n R.reduce x) c.
  Proof.
    intros n x c Hgamma. induction n as [|n IH].
    - exact Hgamma.
    - apply step_sound. exact IH.
  Qed.

  (** Repeated reduction descends in each original coordinate. *)
  Lemma iter_lower : forall n x,
    A.leb (fst (Nat.iter n R.reduce x)) (fst x) = true /\
    B.leb (snd (Nat.iter n R.reduce x)) (snd x) = true.
  Proof.
    intro n. induction n as [|n IH]; intros [a b].
    - split; [apply A.leb_refl|apply B.leb_refl].
    - change (A.leb (fst (R.reduce (Nat.iter n R.reduce (a, b)))) a = true /\
        B.leb (snd (R.reduce (Nat.iter n R.reduce (a, b)))) b = true).
      destruct (IH (a, b)) as [Ha Hb].
      destruct (Nat.iter n R.reduce (a, b)) as [u v] eqn:Hiter.
      destruct (R.reduce_lower u v) as [Hu Hv]. cbn [fst snd] in Ha, Hb.
      split; [eapply A.leb_trans|eapply B.leb_trans]; eassumption.
  Qed.

  (** Bottom normalization preserves the meaning of the completed reduction. *)
  Lemma red_sound : forall x c, gamma x c -> gamma (red x) c.
  Proof.
    intros x c Hgamma. unfold red. apply P.normalize_sound.
    now apply iter_sound.
  Qed.

  (** Completed reduction descends in both original coordinates. *)
  Lemma red_components_lower : forall x,
    A.leb (fst (red x)) (fst x) = true /\ B.leb (snd (red x)) (snd x) = true.
  Proof.
    intro x. unfold red.
    destruct (P.normalize_components_lower (Nat.iter K.rounds R.reduce x)) as [Hna Hnb].
    destruct (iter_lower K.rounds x) as [Ha Hb].
    split; [eapply A.leb_trans|eapply B.leb_trans]; eassumption.
  Qed.

  (** Completed reduction refines the original product. *)
  Lemma red_lower : forall x, leb (red x) x = true.
  Proof.
    intro x. destruct (red_components_lower x) as [Ha Hb].
    now apply P.components_below.
  Qed.

  (** Mapping reduction preserves the concrete value at every list position. *)
  Lemma map_red_sound : forall xs cs,
    Forall2 gamma xs cs -> Forall2 gamma (map red xs) cs.
  Proof.
    intros xs cs Hfacts. induction Hfacts as [|x c xs cs Hhead Htail IH]; cbn [map].
    - constructor.
    - constructor; [now apply red_sound|exact IH].
  Qed.

  (** Mapping reduction after a positional refinement keeps every result below its input. *)
  Lemma map_red_refines : forall ys xs,
    Forall2 (fun y x => leb y x = true) ys xs ->
    Forall2 (fun y x => leb y x = true) (map red ys) xs.
  Proof.
    intros ys xs Hbelow. induction Hbelow as [|y x ys xs Hhead Htail IH]; cbn [map].
    - constructor.
    - constructor; [|exact IH]. eapply leb_trans; [apply red_lower|exact Hhead].
  Qed.

  (** Forward transfer contains every successful concrete result. *)
  Lemma forward_sound : forall o xs cs c,
    Forall2 gamma xs cs -> L.eval o cs = Some c -> gamma (forward o xs) c.
  Proof.
    intros o xs cs c Hfacts Heval. apply red_sound.
    exact (P.forward_sound o xs cs c Hfacts Heval).
  Qed.
  (** Backward transfer retains operands consistent with the abstract result. *)
  Lemma backward_sound : forall o r xs cs c,
    Forall2 gamma xs cs -> L.eval o cs = Some c -> gamma r c ->
    Forall2 gamma (backward o r xs) cs.
  Proof.
    intros o r xs cs c Hfacts Heval Hr. apply map_red_sound.
    exact (P.backward_sound o r xs cs c Hfacts Heval Hr).
  Qed.
  (** Backward transfer refines each operand in its original position. *)
  Lemma backward_refines : forall o r xs,
    Forall2 (fun y x => leb y x = true) (backward o r xs) xs.
  Proof.
    intros o r xs. apply map_red_refines. apply P.backward_refines.
  Qed.
  (** Guard transfer retains operands satisfying the concrete guard. *)
  Lemma guard_sound : forall g xs cs,
    Forall2 gamma xs cs -> L.holds g cs -> Forall2 gamma (guard g xs) cs.
  Proof.
    intros g xs cs Hfacts Hholds. apply map_red_sound.
    exact (P.guard_sound g xs cs Hfacts Hholds).
  Qed.
  (** Guard transfer refines each operand in its original position. *)
  Lemma guard_refines : forall g xs,
    Forall2 (fun y x => leb y x = true) (guard g xs) xs.
  Proof.
    intros g xs. apply map_red_refines. apply P.guard_refines.
  Qed.
End Reduced.

Module ReducedT (L : LANG_T) (A B : VALUE_DOMAIN_T L)
    (R : VALUE_REDUCER_T L A B) (K : ROUNDS) <: REDUCED_ALL L A B R K.
  Include Reduced L A B R K.
  Module PT := ProductT L A B.

  TimeFun bot.
  TimeFun is_bot.
  TimeFun leb.
  TimeFun join.
  TimeFun normalize.
  TimeFun top.
  TimeFun meet.
  TimeFun widen.
  TimeFun narrow.
  TimeFun red.
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
  Definition k_growth : N := (R.c_reduce + 1)%N.
  Definition k_iter : N := (k_growth ^ N.of_nat K.rounds)%N.
  Definition k_rounds : N := N.of_nat (K.rounds + 1).
  Definition c_red : N := (16 * (PT.k_core + R.c_reduce + 1) * k_iter)%N.
  Definition k_red_budget : N := (c_red * k_rounds)%N.
  Definition c_val : N := (k_red_budget * (PT.c_val + 1) + PT.c_val + 16)%N.
  Definition c_lat : N := c_val.
  (** The lattice constant pays for at least one call. *)
  Lemma c_lat_pos : (1 <= c_lat)%N.
  Proof.
    unfold c_lat, c_val. lia.
  Qed.

  Local Lemma product_constant_le : (PT.c_val <= c_val)%N.
  Proof.
    unfold c_val. lia.
  Qed.

  Lemma T_leb_le : forall a b,
    (T_leb a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. eapply N.le_trans; [apply PT.T_leb_le|].
    apply N.mul_le_mono_r. exact product_constant_le.
  Qed.
  Lemma T_join_le : forall a b,
    (T_join a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. eapply N.le_trans; [apply PT.T_join_le|].
    apply N.mul_le_mono_r. exact product_constant_le.
  Qed.
  Lemma T_meet_le : forall a b,
    (T_meet a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. eapply N.le_trans; [apply PT.T_meet_le|].
    apply N.mul_le_mono_r. exact product_constant_le.
  Qed.
  Lemma T_is_bot_le : forall a,
    (T_is_bot a <= c_val * N.of_nat (size a + 1))%N.
  Proof.
    intro a. eapply N.le_trans; [apply PT.T_is_bot_le|].
    apply N.mul_le_mono_r. exact product_constant_le.
  Qed.
  Lemma T_widen_le : forall p a b,
    (T_widen p a b <= c_val * N.of_nat (size a + size b + wsize p + 1))%N.
  Proof.
    intros p a b. eapply N.le_trans; [apply PT.T_widen_le|].
    apply N.mul_le_mono_r. exact product_constant_le.
  Qed.
  Lemma T_narrow_le : forall a b,
    (T_narrow a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. eapply N.le_trans; [apply PT.T_narrow_le|].
    apply N.mul_le_mono_r. exact product_constant_le.
  Qed.
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
  Proof.
    intros a b. eapply N.le_trans; [apply PT.meet_size|].
    apply N.mul_le_mono_r. exact product_constant_le.
  Qed.
  Lemma join_size : forall a b,
    (N.of_nat (size (join a b)) <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. eapply N.le_trans; [apply PT.join_size|].
    apply N.mul_le_mono_r. exact product_constant_le.
  Qed.
  Lemma widen_size : forall p a b,
    (N.of_nat (size (widen p a b)) <=
      c_val * N.of_nat (size a + size b + wsize p + 1))%N.
  Proof.
    intros p a b. eapply N.le_trans; [apply PT.widen_size|].
    apply N.mul_le_mono_r. exact product_constant_le.
  Qed.
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
  Proof.
    exact PT.work_sizes.
  Qed.
  Lemma gwork_sizes : forall g xs,
    fold_right Nat.add 0%nat (map size xs) <= gwork g xs.
  Proof.
    exact PT.gwork_sizes.
  Qed.
  Lemma T_red_le : forall a b,
    (T_red (a, b) <= c_red * N.of_nat (K.rounds + 1) *
      N.of_nat ((A.size a + B.size b + 1)%nat))%N.
  Proof. Admitted. (* STUB *)
  Lemma forward_bigO : (bigO (fun _ => True)
    (fun ox => N.of_nat (work (fst ox) (snd ox)))
    (fun ox => T_forward (fst ox) (snd ox)))%N.
  Proof. Admitted. (* STUB *)

  Definition k_red : N := 1%N. (* STUB *)
  Lemma F1_red_eq : forall x,
    red x = let result := Nat.iter K.rounds R.reduce x in
      if orb (A.is_bot (fst result)) (B.is_bot (snd result))
      then (A.bot, B.bot) else result.
  Proof.
    reflexivity.
  Qed.
  Lemma F_is_bot : forall a b,
    is_bot (a, b) = orb (A.is_bot a) (B.is_bot b).
  Proof.
    reflexivity.
  Qed.
  Lemma F_leb : forall a b,
    leb a b = orb (is_bot a) (andb (A.leb (fst a) (fst b)) (B.leb (snd a) (snd b))).
  Proof.
    reflexivity.
  Qed.
  Lemma F_wunits : forall a b, wunits (a, b) = A.wunits a + B.wunits b.
  Proof.
    reflexivity.
  Qed.
  Lemma F2_gamma : forall a b c,
    gamma (a, b) c <-> A.gamma a c /\ B.gamma b c.
  Proof.
    reflexivity.
  Qed.
  Lemma F3_red_sound : forall x c, gamma x c -> gamma (red x) c.
  Proof.
    exact red_sound.
  Qed.
  Lemma F4_red_lower : forall a b,
    A.leb (fst (red (a, b))) a = true /\ B.leb (snd (red (a, b))) b = true.
  Proof.
    intros a b. exact (red_components_lower (a, b)).
  Qed.
  Lemma F5_widen : forall p a b,
    widen p a b = if is_bot b then a
      else (A.widen (fst p) (fst a) (fst b), B.widen (snd p) (snd a) (snd b)).
  Proof.
    reflexivity.
  Qed.
  Lemma T1_red_steps : forall x,
    (T_red x <= k_red *
      (fold_right N.add 0
        (map (fun n => R.T_reduce (Nat.iter n R.reduce x) + 1)
          (seq 0 K.rounds)) +
       A.T_is_bot (fst (Nat.iter K.rounds R.reduce x)) +
       B.T_is_bot (snd (Nat.iter K.rounds R.reduce x)) + 1))%N.
  Proof. Admitted. (* STUB *)
End ReducedT.
