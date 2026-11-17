(** * Non-relational environment code

    Environments map variables to abstract values and track unreachable states.
    For example, reading an absent binding returns the value domain's top.
    Builds on: EnvSig and the keyed map operations. *)

From Stdlib Require Import List Bool NArith Arith Lia Permutation.
From Argent Require Import Time Tactics Std BigO.
From Galois.Base Require Import KeySig MapSig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.States Require Import EnvSig.
Import List.ListNotations.

(** Variable collection prepends the leaves in their expression order. *)
Fixpoint env_vars_into {K X} (e : term K X) (acc : list X) : list X :=
  match e with
  | Leaf x => x :: acc
  | Node _ es => fold_right (fun e acc => env_vars_into e acc) acc es
  end.
TimeFun env_vars_into.

(** Variable collection traverses each expression constructor once. *)
Definition env_vars {K X} (e : term K X) : list X := env_vars_into e [].
TimeFun env_vars.

Module EnvCode (X : KEY_OPS) (M : MAP_OPS X) (L : LANG_OPS)
    (V : VALUE_DOMAIN_OPS L) <: ENV_OPS X M L V.
  Definition t := reach (M.t V.t).
  Definition wparam := V.wparam.
  Definition read (m : M.t V.t) x :=
    match M.get x m with Some a => a | None => V.top end.
  Definition bot : t := Unreached.
  Definition top : t := Reached M.empty.
  Definition is_bot (s : t) :=
    match s with Unreached => true | Reached m => M.existsb V.is_bot m end.
  Definition option_leb a b :=
    match a, b with
    | None, None | Some _, None => true
    | None, Some b => V.leb V.top b
    | Some a, Some b => V.leb a b
    end.
  Definition leb_ref (a b : t) :=
    orb (is_bot a) (andb (negb (is_bot b))
      (match a, b with
       | Reached a, Reached b => M.forall2b option_leb a b
       | _, _ => false
       end)).
  Definition leb_entry (a b : option V.t) : bool :=
    match b with
    | Some v => if V.is_bot v then false else option_leb a b
    | None => option_leb a b
    end.
  Definition leb (a b : t) :=
    match a, b with
    | Unreached, _ => true
    | Reached ma, Unreached => M.existsb V.is_bot ma
    | Reached ma, Reached mb =>
      if M.forall2b leb_entry ma mb then true else M.existsb V.is_bot ma
    end.
  Definition join_map a b :=
    M.merge (fun x y => match x, y with
      | Some a, Some b =>
        let v := V.join a b in if V.is_bot v then None else Some v
      | _, _ => None
      end) a b.
  Definition join (a b : t) :=
    match a, b with
    | Unreached, s | s, Unreached => s
    | Reached a, Reached b => Reached (join_map a b)
    end.
  Definition meet (a b : t) :=
    match a, b with
    | Reached a, Reached b => Reached (M.merge (fun x y => match x, y with
        | None, None => None
        | Some a, None => Some a
        | None, Some b => Some b
        | Some a, Some b => Some (V.meet a b)
        end) a b)
    | _, _ => Unreached
    end.
  Definition widen p (a b : t) :=
    if leb b a then a else
    match a, b with
    | Unreached, s | s, Unreached => s
    | Reached a, Reached b => Reached (M.merge (fun x y => match x, y with
        | Some a, Some b =>
          let v := V.widen p a b in if V.is_bot v then None else Some v
        | _, _ => None
        end) a b)
    end.
  Definition narrow (a b : t) :=
    if is_bot b then b else
    match a, b with
    | Unreached, _ => Unreached
    | s, Unreached => s
    | Reached a, Reached b => Reached (M.merge (fun x y => match x, y with
        | None, None => None
        | Some a, None => Some a
        | None, Some b => Some b
        | Some a, Some b => Some (V.narrow a b)
        end) a b)
    end.
  Definition root (n : ann L.op X.t V.t) := match n with ALeaf _ a | ANode _ a _ => a end.
  Fixpoint annotate (m : M.t V.t) (e : term L.op X.t) : ann L.op X.t V.t :=
    match e with
    | Leaf x => ALeaf x (read m x)
    | Node o es =>
      let ns := map (annotate m) es in ANode o (V.forward o (map root ns)) ns
    end.
  Fixpoint erase (n : ann L.op X.t V.t) : term L.op X.t :=
    match n with
    | ALeaf x _ => Leaf x
    | ANode o _ ns => Node o (map erase ns)
    end.
  Fixpoint refine_checked (q : V.t) (n : ann L.op X.t V.t) (m : M.t V.t)
      : M.t V.t * bool :=
    match n with
    | ALeaf x _ =>
      let v := V.meet (read m x) q in (M.set x v m, V.is_bot v)
    | ANode o _ ns =>
      let qs := V.backward o q (map root ns) in
      (fix go ns qs m bad :=
        match ns, qs with
        | n :: ns, q :: qs =>
          let result := refine_checked q n m in
          go ns qs (fst result) (orb bad (snd result))
        | _, _ => (m, bad)
        end) ns qs m false
    end.
  Definition refine q n m := fst (refine_checked q n m).
  Definition eval (e : term L.op X.t) (s : t) :=
    match s with Unreached => V.bot | Reached m => root (annotate m e) end.
  Definition assign x e (s : t) :=
    match s with Unreached => Unreached | Reached m => Reached (M.set x (eval e s) m) end.
  Definition havoc x (s : t) :=
    match s with Unreached => Unreached | Reached m => Reached (M.set x V.top m) end.
  Definition vars (e : term L.op X.t) : list X.t := env_vars e.
  Definition materialize (m : M.t V.t) (xs : list X.t) :=
    fold_left (fun acc x => M.set x (read acc x) acc) xs m.
  Definition assume g es (s : t) :=
    match s with
    | Unreached => Unreached
    | Reached m =>
      let ns := map (annotate m) es in
      let qs := V.guard g (map root ns) in
      let result := fold_left (fun result nq =>
        let next := refine_checked (snd nq) (fst nq) (fst result) in
        (fst next, orb (snd result) (snd next))) (combine ns qs) (m, false) in
      if snd result then Unreached else Reached (fst result)
    end.
End EnvCode.

Module Env (X : KEY) (M : MAP X) (L : LANG) (V : VALUE_DOMAIN L)
    <: ENV X M L V.
  Include EnvCode X M L V.
  Include ENV_SPEC X M L V.
  Definition wrank (p : wparam) (s : t) : nat :=
    match s with
    | Unreached => 0
    | Reached m => fold_right Nat.add 0 (map (fun c =>
        match M.find c m with Some a => V.wrank p a | None => 0 end) (M.codes m))
    end.
  Definition gamma (s : t) (st : X.t -> L.val) : Prop :=
    match s with
    | Unreached => False
    | Reached m => M.existsb V.is_bot m = false /\ forall x, V.gamma (read m x) (st x)
    end.

  Definition option_value (a : option V.t) : V.t :=
    match a with Some a => a | None => V.top end.

  (** Optional comparison is the value order with top at absent bindings. *)
  Lemma option_leb_spec : forall a b,
    option_leb a b = V.leb (option_value a) (option_value b).
  Proof.
    intros [a|] [b|]; cbn [option_leb option_value]; try reflexivity;
      symmetry; apply V.top_greatest.
  Qed.

  (** Raw map comparison reflects the value order at every encoded key. *)
  Lemma map_leb_spec : forall a b,
    M.forall2b option_leb a b = true <->
      forall p, V.leb (option_value (M.find p a)) (option_value (M.find p b)) = true.
  Proof.
    intros a b. rewrite (M.forall2b_spec V.t V.t option_leb a b eq_refl).
    split; intros H p; specialize (H p); rewrite option_leb_spec in *; exact H.
  Qed.

  (** A map is not recognized as bottom exactly when none of its bindings is. *)
  Lemma map_nonbot_spec : forall m,
    M.existsb V.is_bot m = false <->
      forall p a, M.find p m = Some a -> V.is_bot a = false.
  Proof.
    intro m. split.
    - intros Hclean p a Hfind. destruct (V.is_bot a) eqn:Hbot; [|reflexivity].
      assert (Hbad : M.existsb V.is_bot m = true).
      { apply M.existsb_spec. exists p, a. split; assumption. }
      congruence.
    - intros Hclean. destruct (M.existsb V.is_bot m) eqn:Hbad; [|reflexivity].
      apply M.existsb_spec in Hbad as [p [a [Hfind Hbot]]].
      specialize (Hclean p a Hfind). congruence.
  Qed.

  (** The fused map comparison checks the right map and the pointwise order together. *)
  Lemma map_leb_entry_spec : forall a b,
    M.forall2b leb_entry a b = true <->
      M.existsb V.is_bot b = false /\ M.forall2b option_leb a b = true.
  Proof.
    intros a b.
    rewrite (M.forall2b_spec V.t V.t leb_entry a b eq_refl).
    rewrite (M.forall2b_spec V.t V.t option_leb a b eq_refl), map_nonbot_spec.
    split.
    - intro Hentry. split.
      + intros p v Hfind. specialize (Hentry p).
        unfold leb_entry in Hentry. rewrite Hfind in Hentry.
        destruct (V.is_bot v) eqn:Hbot; [discriminate|reflexivity].
      + intro p. specialize (Hentry p). unfold leb_entry in Hentry.
        destruct (M.find p b) as [v|]; [destruct (V.is_bot v)|];
          try discriminate; exact Hentry.
    - intros [Hclean Horder] p. unfold leb_entry.
      specialize (Horder p).
      destruct (M.find p b) as [v|] eqn:Hfind.
      + rewrite (Hclean p v Hfind). exact Horder.
      + exact Horder.
  Qed.

  (** One fused comparison preserves the original environment inclusion test. *)
  Lemma leb_agree : forall a b, leb a b = leb_ref a b.
  Proof.
    intros [|a] [|b]; try reflexivity.
    - unfold leb, leb_ref, is_bot. now destruct (M.existsb V.is_bot a).
    - unfold leb, leb_ref, is_bot.
      destruct (M.forall2b leb_entry a b) eqn:Hentry.
      + apply map_leb_entry_spec in Hentry as [Hclean Horder].
        rewrite Hclean, Horder. now destruct (M.existsb V.is_bot a).
      + destruct (M.existsb V.is_bot a); [reflexivity|].
        destruct (M.existsb V.is_bot b) eqn:Hclean; cbn; [reflexivity|].
        destruct (M.forall2b option_leb a b) eqn:Horder; [|reflexivity].
        assert (Htrue : M.forall2b leb_entry a b = true).
        { apply map_leb_entry_spec. split; assumption. }
        congruence.
  Qed.

  (** The empty map has no recognized bottom binding. *)
  Lemma map_empty_nonbot : M.existsb V.is_bot (@M.empty V.t) = false.
  Proof.
    apply map_nonbot_spec. intros p a Hfind. rewrite M.find_empty in Hfind. discriminate.
  Qed.

  (** Every environment is below itself, including recognized bottom maps. *)
  Lemma leb_refl : forall a, leb a a = true.
  Proof.
    intros [|m]; [reflexivity|]. rewrite leb_agree. unfold leb_ref. cbn [is_bot].
    destruct (M.existsb V.is_bot m); cbn; [reflexivity|].
    apply map_leb_spec. intro p. apply V.leb_refl.
  Qed.
  (** The order composes through an intermediate value. *)
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof.
    intros a b c Hab Hbc. rewrite !leb_agree in *. unfold leb_ref in *.
    destruct (is_bot a) eqn:Ha; [reflexivity|]. cbn in Hab |- *.
    apply andb_true_iff in Hab as [Hb Hab]. apply negb_true_iff in Hb.
    rewrite Hb in Hbc. cbn in Hbc.
    apply andb_true_iff in Hbc as [Hc Hbc]. rewrite Hc. cbn.
    destruct a as [|a], b as [|b], c as [|c]; try discriminate.
    pose proof (proj1 (map_leb_spec a b) Hab) as Hab_point.
    pose proof (proj1 (map_leb_spec b c) Hbc) as Hbc_point.
    apply map_leb_spec. intro p. eapply V.leb_trans; [apply Hab_point|apply Hbc_point].
  Qed.
  (** Bottom is below every value. *)
  Lemma bot_least : forall a, leb bot a = true.
  Proof.
    intros [|a]; reflexivity.
  Qed.
  (** The bottom test recognizes bottom. *)
  Lemma is_bot_bot : is_bot bot = true.
  Proof.
    reflexivity.
  Qed.
  (** Every recognized bottom is below every value. *)
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof.
    intros a b Hbot. rewrite leb_agree. unfold leb_ref. now rewrite Hbot.
  Qed.

  (** Pointwise inclusion into a map without bottom bindings lifts to environments. *)
  Lemma leb_reached_intro : forall a b,
    M.existsb V.is_bot b = false ->
    (forall p, V.leb (option_value (M.find p a)) (option_value (M.find p b)) = true) ->
    leb (Reached a) (Reached b) = true.
  Proof.
    intros a b Hclean Hpoint. rewrite leb_agree. unfold leb_ref. cbn [is_bot].
    rewrite Hclean. destruct (M.existsb V.is_bot a); cbn; [reflexivity|].
    now apply map_leb_spec.
  Qed.

  (** Dropping absent and recognized bottom results preserves both upper bounds. *)
  Lemma filtered_merge_bounds : forall (f : V.t -> V.t -> V.t) a b,
    (forall x y, V.leb x (f x y) = true) ->
    (forall x y, V.leb y (f x y) = true) ->
    let m := M.merge (fun x y => match x, y with
      | Some x, Some y => if V.is_bot (f x y) then None else Some (f x y)
      | _, _ => None
      end) a b in
    M.existsb V.is_bot m = false /\
      leb (Reached a) (Reached m) = true /\ leb (Reached b) (Reached m) = true.
  Proof.
    intros f a b Hleft Hright m.
    assert (Hclean : M.existsb V.is_bot m = false).
    { apply map_nonbot_spec. intros p v Hfind. unfold m in Hfind.
      rewrite M.find_merge in Hfind by reflexivity.
      destruct (M.find p a) as [x|], (M.find p b) as [y|]; try discriminate.
      destruct (V.is_bot (f x y)) eqn:Hbot; [discriminate|].
      injection Hfind as Hvalue. subst v. exact Hbot. }
    split; [exact Hclean|]. split; apply leb_reached_intro; try exact Hclean.
    all: intro p; unfold m; rewrite M.find_merge by reflexivity.
    all: destruct (M.find p a) as [x|], (M.find p b) as [y|];
      cbn [option_value]; try apply V.top_greatest.
    all: destruct (V.is_bot (f x y)); cbn [option_value];
      first [apply V.top_greatest | apply Hleft | apply Hright].
  Qed.

  (** Join is above its left operand. *)
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof.
    intros [|a] [|b]; try apply bot_least; try apply leb_refl.
    exact (proj1 (proj2 (filtered_merge_bounds V.join a b V.join_ub_l V.join_ub_r))).
  Qed.
  (** Join is above its right operand. *)
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof.
    intros [|a] [|b]; try apply bot_least; try apply leb_refl.
    exact (proj2 (proj2 (filtered_merge_bounds V.join a b V.join_ub_l V.join_ub_r))).
  Qed.

  Lemma top_greatest : forall a, leb a top = true.
  Proof.
    intros [|m]; [reflexivity|]. rewrite leb_agree. unfold leb_ref, top. cbn [is_bot].
    rewrite map_empty_nonbot. destruct (M.existsb V.is_bot m); cbn; [reflexivity|].
    apply map_leb_spec. intro p. rewrite M.find_empty. apply V.top_greatest.
  Qed.

  (** Widening is above its previous value. *)
  Lemma widen_ub_l : forall p a b, leb a (widen p a b) = true.
  Proof.
    intros p a b. unfold widen. destruct (leb b a); [apply leb_refl|].
    destruct a as [|a], b as [|b]; try apply bot_least; try apply leb_refl.
    exact (proj1 (proj2 (filtered_merge_bounds (V.widen p) a b
      (V.widen_ub_l p) (V.widen_ub_r p)))).
  Qed.
  (** Widening is above its candidate value. *)
  Lemma widen_ub_r : forall p a b, leb b (widen p a b) = true.
  Proof.
    intros p a b. unfold widen. destruct (leb b a) eqn:Hstable; [exact Hstable|].
    destruct a as [|a], b as [|b]; try apply bot_least; try apply leb_refl.
    exact (proj2 (proj2 (filtered_merge_bounds (V.widen p) a b
      (V.widen_ub_l p) (V.widen_ub_r p)))).
  Qed.
  (** A candidate below the previous value leaves widening unchanged. *)
  Lemma widen_stable : forall p a b, leb b a = true -> widen p a b = a.
  Proof.
    intros p a b Hstable. unfold widen. now rewrite Hstable.
  Qed.
  (** Permuting bindings preserves the sum of their ranks. *)
  Lemma rank_sum_permutation : forall {A} (f : A -> nat) xs ys,
    Permutation xs ys ->
    fold_right Nat.add 0 (map f xs) = fold_right Nat.add 0 (map f ys).
  Proof.
    intros A f xs ys Hperm. induction Hperm; cbn [map fold_right]; lia.
  Qed.

  (** Filtering zero contributions leaves a rank sum unchanged. *)
  Lemma rank_sum_filter_zero : forall {A} (test : A -> bool) f xs,
    (forall x, In x xs -> test x = false -> f x = 0) ->
    fold_right Nat.add 0 (map f (filter test xs)) =
      fold_right Nat.add 0 (map f xs).
  Proof.
    intros A test f xs. induction xs as [|x xs IH]; intros Hz; cbn; [reflexivity|].
    destruct (test x) eqn:Hx; cbn.
    - rewrite IH; [reflexivity|]. intros y Hy. apply Hz. now right.
    - rewrite IH; [rewrite (Hz x (or_introl eq_refl) Hx); lia|].
      intros y Hy. apply Hz. now right.
  Qed.

  (** Pointwise rank bounds extend to sums over the same bindings. *)
  Lemma rank_sum_mono : forall {A} (f g : A -> nat) xs,
    (forall x, In x xs -> f x <= g x) ->
    fold_right Nat.add 0 (map f xs) <= fold_right Nat.add 0 (map g xs).
  Proof.
    intros A f g xs. induction xs as [|x xs IH]; intros H; cbn; [lia|].
    pose proof (H x (or_introl eq_refl)).
    assert (Htail : forall y, In y xs -> f y <= g y).
    { intros y Hy. apply H. now right. }
    specialize (IH Htail). lia.
  Qed.

  (** One strict binding decrease makes a pointwise nonincreasing sum decrease. *)
  Lemma rank_sum_strict : forall {A} (f g : A -> nat) xs,
    (forall x, In x xs -> f x <= g x) ->
    (exists x, In x xs /\ f x < g x) ->
    fold_right Nat.add 0 (map f xs) < fold_right Nat.add 0 (map g xs).
  Proof.
    intros A f g xs. induction xs as [|x xs IH]; intros H [y [Hy Hlt]];
      cbn in *; [contradiction|].
    assert (Htail : forall z, In z xs -> f z <= g z).
    { intros z Hz. apply H. now right. }
    destruct Hy as [Heq|Hy].
    - subst y. pose proof (rank_sum_mono f g xs Htail). lia.
    - specialize (IH Htail (ex_intro _ y (conj Hy Hlt))).
      pose proof (H x (or_introl eq_refl)). lia.
  Qed.

  (** A larger code list leaves the rank unchanged when added lookups are absent. *)
  Lemma rank_codes_extend : forall p (m ms : M.t V.t),
    incl (M.codes m) (M.codes ms) ->
    wrank p (Reached m) = fold_right Nat.add 0 (map (fun c =>
      match M.find c m with Some a => V.wrank p a | None => 0 end) (M.codes ms)).
  Proof.
    intros p m ms Hincl.
    set (present := fun c => match M.find c m with Some _ => true | None => false end).
    assert (Hperm : Permutation (M.codes m) (filter present (M.codes ms))).
    { apply NoDup_Permutation.
      - apply M.codes_nodup.
      - apply NoDup_filter. apply M.codes_nodup.
      - intros c. rewrite filter_In. split.
        + intros Hc. split; [now apply Hincl|]. unfold present.
          apply M.codes_spec in Hc. destruct (M.find c m); congruence.
        + intros [_ Hc]. apply M.codes_spec. unfold present in Hc.
          destruct (M.find c m); congruence. }
    unfold wrank. rewrite (rank_sum_permutation _ _ _ Hperm).
    apply rank_sum_filter_zero. intros c _ Hc. unfold present in Hc.
    destruct (M.find c m); congruence.
  Qed.

  (** The proof names the map produced by an unstable reached widening. *)
  Definition rank_widen_map p a b := M.merge (fun x y => match x, y with
    | Some a, Some b => let v := V.widen p a b in if V.is_bot v then None else Some v
    | _, _ => None end) a b.

  (** Widening a map acts on each pair of present encoded bindings. *)
  Lemma rank_widen_find : forall p a b c,
    M.find c (rank_widen_map p a b) = match M.find c a, M.find c b with
    | Some x, Some y =>
      let v := V.widen p x y in if V.is_bot v then None else Some v
    | _, _ => None end.
  Proof.
    intros p a b c. unfold rank_widen_map. apply M.find_merge. reflexivity.
  Qed.

  (** Map widening retains only codes present in the previous map. *)
  Lemma rank_widen_codes : forall p a b,
    incl (M.codes (rank_widen_map p a b)) (M.codes a).
  Proof.
    intros p a b c Hc. apply M.codes_spec in Hc. apply M.codes_spec.
    rewrite rank_widen_find in Hc. destruct (M.find c a); congruence.
  Qed.

  (** Each widening contribution is bounded by its previous binding rank. *)
  Lemma rank_widen_pointwise : forall p a b c,
    M.existsb V.is_bot a = false ->
    (match M.find c (rank_widen_map p a b) with
     | Some x => V.wrank p x | None => 0 end) <=
    (match M.find c a with Some x => V.wrank p x | None => 0 end).
  Proof.
    intros p a b c Ha. rewrite rank_widen_find.
    destruct (M.find c a) as [x|] eqn:Hx; [|lia].
    destruct (M.find c b) as [y|]; [|lia].
    cbn. destruct (V.is_bot (V.widen p x y)); cbn; [lia|].
    apply V.wrank_widen_le. exact (proj1 (map_nonbot_spec a) Ha c x Hx).
  Qed.

  (** A failed finite Boolean check exposes a failing member. *)
  Lemma rank_forallb_false : forall {A} (test : A -> bool) xs,
    forallb test xs = false -> exists x, In x xs /\ test x = false.
  Proof.
    intros A test xs. induction xs as [|x xs IH]; cbn; intros H; [discriminate|].
    destruct (test x) eqn:Hx.
    - cbn in H. destruct (IH H) as [y [Hy Hfalse]]. exists y. split; [now right|assumption].
    - exists x. split; [now left|assumption].
  Qed.

  (** Failed sparse comparison exposes an unstable binding in the previous map. *)
  Lemma rank_order_failure : forall a b,
    M.forall2b option_leb b a = false ->
    exists c x, In c (M.codes a) /\ M.find c a = Some x /\
      option_leb (M.find c b) (Some x) = false.
  Proof.
    intros a b Hbad.
    assert (Hfalse : forallb (fun c => option_leb (M.find c b) (M.find c a))
        (M.codes a) = false).
    { destruct (forallb (fun c => option_leb (M.find c b) (M.find c a))
        (M.codes a)) eqn:Hlist; [|reflexivity].
      assert (Htrue : M.forall2b option_leb b a = true).
      { apply M.forall2b_spec; [reflexivity|]. intros c.
        destruct (M.find c a) as [x|] eqn:Hx.
        - apply forallb_forall with (x := c) in Hlist.
          + now rewrite Hx in Hlist.
          + apply M.codes_spec. rewrite Hx. discriminate.
        - destruct (M.find c b); reflexivity. }
      congruence. }
    destruct (rank_forallb_false _ _ Hfalse) as [c [Hc Hfalsec]].
    destruct (M.find c a) as [x|] eqn:Hx.
    - exists c, x. auto.
    - destruct (M.find c b); discriminate.
  Qed.

  (** An unstable widening from a nonbottom strictly decreases rank. *)
  Lemma wrank_widen : forall p a b, is_bot a = false -> leb b a = false ->
    wrank p (widen p a b) < wrank p a.
  Proof.
    intros p [|a] [|b] Ha Hba; cbn [is_bot] in Ha; try discriminate.
    unfold widen. rewrite Hba.
    change (wrank p (Reached (rank_widen_map p a b)) < wrank p (Reached a)).
    rewrite (rank_codes_extend p _ a (rank_widen_codes p a b)).
    unfold wrank. apply rank_sum_strict.
    - intros c _. now apply rank_widen_pointwise.
    - assert (Horder : M.forall2b option_leb b a = false).
      { rewrite leb_agree in Hba. unfold leb_ref in Hba. cbn [is_bot] in Hba.
        rewrite Ha in Hba.
        destruct (M.existsb V.is_bot b); cbn in Hba; [discriminate|exact Hba]. }
      destruct (rank_order_failure a b Horder) as [c [x [Hc [Hx Hbad]]]].
      exists c. split; [exact Hc|]. rewrite Hx, rank_widen_find, Hx.
      pose proof (proj1 (map_nonbot_spec a) Ha c x Hx) as Hxbot.
      destruct (M.find c b) as [y|] eqn:Hy; cbn [option_leb] in Hbad.
      + pose proof (V.wrank_widen p x y Hxbot Hbad) as Hrank.
        cbn. destruct (V.is_bot (V.widen p x y)); cbn; lia.
      + pose proof (V.wrank_widen p x V.top Hxbot Hbad). lia.
  Qed.

  (** Widening from a nonbottom does not increase rank. *)
  Lemma wrank_widen_le : forall p a b, is_bot a = false ->
    wrank p (widen p a b) <= wrank p a.
  Proof.
    intros p a b Ha. destruct (leb b a) eqn:Hba.
    - unfold widen. rewrite Hba. lia.
    - apply Nat.lt_le_incl. now apply wrank_widen.
  Qed.

  (** Narrowing ordered maps without bottom bindings cannot introduce a bottom binding. *)
  Lemma narrow_map_nonbot : forall a b,
    M.existsb V.is_bot a = false -> M.existsb V.is_bot b = false ->
    M.forall2b option_leb b a = true ->
    let m := M.merge (fun x y => match x, y with
      | None, None => None
      | Some x, None => Some x
      | None, Some y => Some y
      | Some x, Some y => Some (V.narrow x y)
      end) a b in
    M.existsb V.is_bot m = false.
  Proof.
    intros a b Ha Hb Hba m. pose proof (proj1 (map_leb_spec b a) Hba) as Hpoint.
    apply map_nonbot_spec. intros p v Hfind. unfold m in Hfind.
    rewrite M.find_merge in Hfind by reflexivity. specialize (Hpoint p).
    destruct (M.find p a) as [x|] eqn:Hx, (M.find p b) as [y|] eqn:Hy;
      cbn [option_value] in Hpoint; try discriminate.
    - injection Hfind as Hvalue. subst v.
      destruct (V.is_bot (V.narrow x y)) eqn:Hbad; [|reflexivity].
      pose proof (V.is_bot_below y (V.narrow x y)
        (proj1 (V.narrow_between x y Hpoint)) Hbad) as Hybot.
      pose proof (proj1 (map_nonbot_spec b) Hb p y Hy) as Hyclean. congruence.
    - injection Hfind as Hvalue. subst v. exact (proj1 (map_nonbot_spec a) Ha p x Hx).
    - injection Hfind as Hvalue. subst v. exact (proj1 (map_nonbot_spec b) Hb p y Hy).
  Qed.

  (** Narrowing stays between an ordered candidate and previous value. *)
  Lemma narrow_between : forall a b, leb b a = true ->
    leb b (narrow a b) = true /\ leb (narrow a b) a = true.
  Proof.
    intros a b Hba. unfold narrow. destruct (is_bot b) eqn:Hb.
    - split; [apply leb_refl|exact Hba].
    - rewrite leb_agree in Hba. unfold leb_ref in Hba. rewrite Hb in Hba. cbn in Hba.
      apply andb_true_iff in Hba as [Ha Hba]. apply negb_true_iff in Ha.
      destruct a as [|a], b as [|b]; try discriminate.
      cbn [is_bot] in Ha, Hb. cbn in Hba.
      set (m := M.merge (fun x y => match x, y with
        | None, None => None
        | Some x, None => Some x
        | None, Some y => Some y
        | Some x, Some y => Some (V.narrow x y)
        end) a b).
      assert (Hm : M.existsb V.is_bot m = false) by
        exact (narrow_map_nonbot a b Ha Hb Hba).
      pose proof (proj1 (map_leb_spec b a) Hba) as Hpoint.
      change (leb (Reached b) (Reached m) = true /\ leb (Reached m) (Reached a) = true).
      split.
      + apply leb_reached_intro; [exact Hm|]. intro p. specialize (Hpoint p).
        unfold m. rewrite M.find_merge by reflexivity.
        destruct (M.find p a) as [x|], (M.find p b) as [y|];
          cbn [option_value] in *; try apply V.leb_refl; try exact Hpoint.
        exact (proj1 (V.narrow_between x y Hpoint)).
      + apply leb_reached_intro; [exact Ha|]. intro p. specialize (Hpoint p).
        unfold m. rewrite M.find_merge by reflexivity.
        destruct (M.find p a) as [x|], (M.find p b) as [y|];
          cbn [option_value] in *; try apply V.leb_refl; try apply V.top_greatest.
        exact (proj2 (V.narrow_between x y Hpoint)).
  Qed.

  (** Abstract inclusion entails inclusion of concrete environments. *)
  Lemma gamma_mono : forall a b st, leb a b = true -> gamma a st -> gamma b st.
  Proof.
    intros [|a] [|b] st Hle Hgamma; try contradiction.
    - destruct Hgamma as [Hclean Hpoint]. rewrite leb_agree in Hle.
      unfold leb_ref in Hle. cbn [is_bot] in Hle.
      rewrite Hclean in Hle. discriminate.
    - destruct Hgamma as [Hclean Hpoint]. rewrite leb_agree in Hle.
      unfold leb_ref in Hle. cbn [is_bot] in Hle.
      rewrite Hclean in Hle. cbn in Hle.
      apply andb_true_iff in Hle as [Hnonbot Horder]. apply negb_true_iff in Hnonbot.
      split; [exact Hnonbot|]. intro x.
      apply (V.gamma_mono (read a x) (read b x) (st x)); [|apply Hpoint].
      unfold read. rewrite !M.get_find.
      exact (proj1 (map_leb_spec a b) Horder (X.encode x)).
  Qed.
  (** Bottom describes no concrete environment. *)
  Lemma gamma_bot : forall st, ~ gamma bot st.
  Proof.
    intros st Hbot. exact Hbot.
  Qed.
  (** Top describes every concrete environment. *)
  Lemma gamma_top : forall st, gamma top st.
  Proof.
    intro st. split; [apply map_empty_nonbot|]. intro x.
    unfold read. rewrite M.get_empty. apply V.gamma_top.
  Qed.

  (** Successful term-list evaluation pairs each term with its own concrete result. *)
  Lemma eval_terms_rel : forall (st : X.t -> L.val) es cs,
    eval_terms L.eval st es = Some cs ->
    Forall2 (fun e c => eval_term L.eval st e = Some c) es cs.
  Proof.
    intros st es. induction es as [|e es IH]; intros cs Heval;
      cbn [eval_terms map sequence] in Heval.
    - injection Heval as Hvalues. subst cs. constructor.
    - destruct (eval_term L.eval st e) as [c|] eqn:Hvalue; [|discriminate].
      destruct (sequence (map (eval_term L.eval st) es)) as [ds|] eqn:Htail;
        [|discriminate].
      injection Heval as Hvalues. subst cs. constructor; [exact Hvalue|].
      now apply IH.
  Qed.

  (** The cached root of each annotated term covers its successful concrete result. *)
  Lemma annotate_value_sound : forall e m st c,
    (forall x, V.gamma (read m x) (st x)) ->
    eval_term L.eval st e = Some c -> V.gamma (root (annotate m e)) c.
  Proof.
    induction e as [x|o es IH]; intros m st c Hmodel Heval.
    - cbn [eval_term] in Heval. injection Heval as Hvalue. subst c. apply Hmodel.
    - cbn [eval_term] in Heval.
      destruct (sequence (map (eval_term L.eval st) es)) as [cs|] eqn:Hchildren;
        [|discriminate].
      cbn [annotate root]. apply V.forward_sound with (cs := cs); [|exact Heval].
      rewrite map_map. pose proof (eval_terms_rel st es cs Hchildren) as Hvalues.
      clear Heval Hchildren. revert IH.
      induction Hvalues as [|e value es cs Hvalue Hvalues IHvalues]; intros IH;
        cbn [map]; [constructor|].
      inversion IH as [|head Hhead tail Htail]; subst. constructor.
      + exact (Hhead m st value Hmodel Hvalue).
      + now apply IHvalues.
  Qed.

  (** Annotated operand roots cover the ordered list of concrete operand results. *)
  Lemma annotate_values_sound : forall es m st cs,
    (forall x, V.gamma (read m x) (st x)) ->
    eval_terms L.eval st es = Some cs ->
    Forall2 V.gamma (map (fun e => root (annotate m e)) es) cs.
  Proof.
    intros es m st cs Hmodel Heval. apply eval_terms_rel in Heval.
    induction Heval as [|e c es cs Hvalue Hvalues IH]; cbn [map]; constructor.
    - eapply annotate_value_sound; eassumption.
    - exact IH.
  Qed.

  (** A represented concrete value cannot be recognized as bottom. *)
  Lemma value_nonbot : forall a c, V.gamma a c -> V.is_bot a = false.
  Proof.
    intros a c Hvalue. destruct (V.is_bot a) eqn:Hbot; [|reflexivity].
    exfalso. exact (V.is_bot_sound a c Hbot Hvalue).
  Qed.

  (** Writing a nonbottom value preserves absence of recognized bottom bindings. *)
  Lemma map_set_nonbot : forall m x a,
    M.existsb V.is_bot m = false -> V.is_bot a = false ->
    M.existsb V.is_bot (M.set x a m) = false.
  Proof.
    intros m x a Hclean Ha. apply map_nonbot_spec. intros p b Hfind.
    rewrite M.find_set in Hfind. destruct (Pos.eqb p (X.encode x)).
    - injection Hfind as Hvalue. subst b. exact Ha.
    - exact (proj1 (map_nonbot_spec m) Hclean p b Hfind).
  Qed.

  (** Updating a represented binding covers the matching concrete state update. *)
  Lemma set_gamma : forall m st x a c,
    gamma (Reached m) st -> V.gamma a c ->
    gamma (Reached (M.set x a m)) (upd X.eqb st x c).
  Proof.
    intros m st x a c [Hclean Hmodel] Hvalue. split.
    - apply map_set_nonbot; [exact Hclean|]. now apply value_nonbot with (c := c).
    - intro y. unfold read, upd. destruct (X.eqb_spec y x) as [Heq|Hneq].
      + subst y. rewrite M.get_set_same. exact Hvalue.
      + rewrite M.get_set_other by exact Hneq. apply Hmodel.
  Qed.

  (** Assignment contains each successful concrete update. *)
  Lemma assign_sound : forall x e s st c,
    gamma s st -> eval_term L.eval st e = Some c ->
    gamma (assign x e s) (upd X.eqb st x c).
  Proof.
    intros x e [|m] st c Hgamma Heval; [contradiction|].
    apply set_gamma; [exact Hgamma|].
    eapply annotate_value_sound; [exact (proj2 Hgamma)|exact Heval].
  Qed.
  (** Havoc contains every concrete update of the selected variable. *)
  Lemma havoc_sound : forall x s st c,
    gamma s st -> gamma (havoc x s) (upd X.eqb st x c).
  Proof.
    intros x [|m] st c Hgamma; [contradiction|].
    apply set_gamma; [exact Hgamma|apply V.gamma_top].
  Qed.

  (** Annotation correctness records the shape and meaning of every cached subtree. *)
  Fixpoint ann_covers (st : X.t -> L.val) (n : ann L.op X.t V.t)
      (e : term L.op X.t) {struct n} : Prop :=
    (forall c, eval_term L.eval st e = Some c -> V.gamma (root n) c) /\
    match n, e with
    | ALeaf x _, Leaf y => x = y
    | ANode o _ ns, Node p es => o = p /\
      (fix children (ns : list (ann L.op X.t V.t)) (es : list (term L.op X.t)) :=
        match ns, es with
        | nil, nil => True
        | n :: ns, e :: es => ann_covers st n e /\ children ns es
        | _, _ => False
        end) ns es
    | _, _ => False
    end.

  (** Forward annotation gives correct cached facts throughout the term tree. *)
  Lemma annotate_covers : forall e m st,
    (forall x, V.gamma (read m x) (st x)) -> ann_covers st (annotate m e) e.
  Proof.
    induction e as [x|o es IH]; intros m st Hmodel; split.
    - intros c Heval. exact (annotate_value_sound (Leaf x) m st c Hmodel Heval).
    - reflexivity.
    - intros c Heval. exact (annotate_value_sound (Node o es) m st c Hmodel Heval).
    - split; [reflexivity|].
      induction IH as [|e Hhead es Htail IHtail]; cbn [map]; [constructor|].
      split; [now apply Hhead|exact IHtail].
  Qed.

  (** A correct node pairs every cached child with the corresponding source term. *)
  Lemma ann_covers_children : forall st o a ns p es,
    ann_covers st (ANode o a ns) (Node p es) ->
    o = p /\ Forall2 (ann_covers st) ns es.
  Proof.
    intros st o a ns p es [_ [Hop Hchildren]]. split; [exact Hop|].
    revert es Hchildren. induction ns as [|n ns IH]; intros [|e es] Hchildren;
      cbn in Hchildren; try contradiction; constructor.
    - exact (proj1 Hchildren).
    - apply IH. exact (proj2 Hchildren).
  Qed.

  (** Successful child evaluation attaches a concrete result to each correct cached child. *)
  Lemma ann_children_results : forall st ns es cs,
    Forall2 (ann_covers st) ns es -> eval_terms L.eval st es = Some cs ->
    Forall2 (fun n c => exists e,
      ann_covers st n e /\ eval_term L.eval st e = Some c) ns cs.
  Proof.
    intros st ns es cs Hchildren. revert cs.
    induction Hchildren as [|n e ns es Hcover Hchildren IH]; intros cs Heval;
      cbn [eval_terms map sequence] in Heval.
    - injection Heval as Hvalues. subst cs. constructor.
    - destruct (eval_term L.eval st e) as [c|] eqn:Hvalue; [|discriminate].
      destruct (sequence (map (eval_term L.eval st) es)) as [ds|] eqn:Htail;
        [|discriminate].
      injection Heval as Hvalues. subst cs. constructor.
      + exists e. split; assumption.
      + now apply IH.
  Qed.

  (** A correct cached root covers every successful result of its source term. *)
  Lemma ann_covers_root : forall st n e c,
    ann_covers st n e -> eval_term L.eval st e = Some c -> V.gamma (root n) c.
  Proof.
    intros st [x a|o a ns] e c Hcover Heval; exact (proj1 Hcover c Heval).
  Qed.

  (** Correct cached children cover the same ordered list of concrete results. *)
  Lemma ann_results_roots : forall st ns cs,
    Forall2 (fun n c => exists e,
      ann_covers st n e /\ eval_term L.eval st e = Some c) ns cs ->
    Forall2 V.gamma (map root ns) cs.
  Proof.
    intros st ns cs Hresults.
    induction Hresults as [|n c ns cs Hresult Hresults IH]; cbn [map]; constructor.
    - destruct Hresult as [e [Hcover Heval]]. eapply ann_covers_root; eassumption.
    - exact IH.
  Qed.

  (** Writing a fact about the current concrete value retains every represented variable. *)
  Lemma set_same_models : forall m st x a,
    (forall y, V.gamma (read m y) (st y)) -> V.gamma a (st x) ->
    forall y, V.gamma (read (M.set x a m) y) (st y).
  Proof.
    intros m st x a Hmodel Ha y. unfold read.
    destruct (X.eqb_spec y x) as [Heq|Hneq].
    - subst y. rewrite M.get_set_same. exact Ha.
    - rewrite M.get_set_other by exact Hneq. apply Hmodel.
  Qed.

  (** Checked refinement preserves a compatible model and never signals bottom. *)
  Lemma refine_checked_covers : forall n m st e q c,
    (forall x, V.gamma (read m x) (st x)) -> ann_covers st n e ->
    eval_term L.eval st e = Some c -> V.gamma q c ->
    (forall x, V.gamma (read (fst (refine_checked q n m)) x) (st x)) /\
      snd (refine_checked q n m) = false.
  Proof.
    induction n as [x a|o a ns IH]; intros m st e q c Hmodel Hcover Heval Hq.
    - destruct e as [y|p es]; destruct Hcover as [Hroot Hshape]; [|contradiction].
      cbn in Hshape. subst y. cbn [eval_term] in Heval.
      injection Heval as Hvalue. subst c. cbn [refine_checked fst snd].
      assert (Hmeet : V.gamma (V.meet (read m x) q) (st x)) by
        (apply V.gamma_meet; [apply Hmodel|exact Hq]).
      split; [now apply set_same_models|now apply value_nonbot with (c := st x)].
    - destruct e as [x|p es].
      { destruct Hcover as [_ Hshape]. exact (False_rect _ Hshape). }
      apply ann_covers_children in Hcover as [Hop Hchildren]. subst p.
      cbn [eval_term] in Heval.
      destruct (sequence (map (eval_term L.eval st) es)) as [cs|] eqn:Hvalues;
        [|discriminate].
      pose proof (ann_children_results st ns es cs Hchildren Hvalues) as Hresults.
      pose proof (ann_results_roots st ns cs Hresults) as Hroots.
      pose proof (V.backward_sound o q (map root ns) cs c Hroots Heval Hq) as Hrequests.
      cbn [refine_checked].
      remember (V.backward o q (map root ns)) as qs eqn:Hrequests_def.
      clear Hrequests_def Hchildren Hvalues Heval Hq Hroots.
      revert m qs Hmodel Hrequests IH.
      induction Hresults as [|n value ns cs Hresult Hresults IHresults];
        intros m qs Hmodel Hrequests IH.
      + inversion Hrequests; subst. cbn. split; [exact Hmodel|reflexivity].
      + inversion IH as [|head Hchild tail Htail]; subst.
        inversion Hrequests as [|request value' requests values' Hrequest Hrequests']; subst.
        destruct Hresult as [e [Hcover Heval]].
        destruct (Hchild m st e request value Hmodel Hcover Heval Hrequest)
          as [Hnext Hflag].
        cbn. rewrite Hflag. cbn [orb].
        exact (IHresults (fst (refine_checked request n m)) requests Hnext Hrequests' Htail).
  Qed.

  (** A clean accumulated flag means that the incoming flag was also clean. *)
  Lemma refine_children_flag_false : forall ns qs m bad,
    snd ((fix go ns qs m bad :=
      match ns, qs with
      | n :: ns, q :: qs =>
        let result := refine_checked q n m in
        go ns qs (fst result) (orb bad (snd result))
      | _, _ => (m, bad)
      end) ns qs m bad) = false -> bad = false.
  Proof.
    induction ns as [|n ns IH]; intros qs m bad Hflag; destruct qs as [|q qs];
      cbn in Hflag; try exact Hflag.
    apply IH in Hflag. now apply orb_false_iff in Hflag as [Hbad _].
  Qed.

  (** Clean child refinements preserve clean bindings across the ordered child loop. *)
  Lemma refine_children_nonbot : forall ns,
    list_all _ (fun n => forall q m,
      M.existsb V.is_bot m = false -> snd (refine_checked q n m) = false ->
      M.existsb V.is_bot (fst (refine_checked q n m)) = false) ns ->
    forall qs m bad, M.existsb V.is_bot m = false ->
    snd ((fix go ns qs m bad :=
      match ns, qs with
      | n :: ns, q :: qs =>
        let result := refine_checked q n m in
        go ns qs (fst result) (orb bad (snd result))
      | _, _ => (m, bad)
      end) ns qs m bad) = false ->
    M.existsb V.is_bot (fst ((fix go ns qs m bad :=
      match ns, qs with
      | n :: ns, q :: qs =>
        let result := refine_checked q n m in
        go ns qs (fst result) (orb bad (snd result))
      | _, _ => (m, bad)
      end) ns qs m bad)) = false.
  Proof.
    intros ns Hchildren. induction Hchildren as [|n Hn ns Hns IH];
      intros qs m bad Hclean Hflag; destruct qs as [|r qs];
      cbn in Hflag |- *; try exact Hclean.
    pose proof (refine_children_flag_false ns qs
      (fst (refine_checked r n m)) (orb bad (snd (refine_checked r n m))) Hflag)
      as Hstart.
    apply orb_false_iff in Hstart as [_ Hchild].
    apply IH; [now apply Hn|exact Hflag].
  Qed.

  (** A checked refinement with a clean flag introduces no recognized bottom binding. *)
  Lemma refine_checked_nonbot : forall q n m,
    M.existsb V.is_bot m = false -> snd (refine_checked q n m) = false ->
    M.existsb V.is_bot (fst (refine_checked q n m)) = false.
  Proof.
    intros q n. revert q. induction n as [x a|o a ns IH]; intros q m Hclean Hflag.
    - cbn [refine_checked fst snd] in Hflag |- *. now apply map_set_nonbot.
    - cbn [refine_checked] in Hflag |- *.
      eapply refine_children_nonbot; [exact IH|exact Hclean|exact Hflag].
  Qed.

  (** Pointwise descent composes through each child in the refinement loop. *)
  Lemma refine_children_lower : forall ns,
    list_all _ (fun n => forall q m x,
      V.leb (read (fst (refine_checked q n m)) x) (read m x) = true) ns ->
    forall qs m bad x,
    V.leb (read (fst ((fix go ns qs m bad :=
      match ns, qs with
      | n :: ns, q :: qs =>
        let result := refine_checked q n m in
        go ns qs (fst result) (orb bad (snd result))
      | _, _ => (m, bad)
      end) ns qs m bad)) x) (read m x) = true.
  Proof.
    intros ns Hchildren. induction Hchildren as [|n Hn ns Hns IH];
      intros qs m bad x; destruct qs as [|r qs]; cbn; try apply V.leb_refl.
    eapply V.leb_trans with (b := read (fst (refine_checked r n m)) x).
    - apply IH.
    - apply Hn.
  Qed.

  (** Every checked refinement decreases each lookup in the value order. *)
  Lemma refine_pointwise_lower : forall q n m x,
    V.leb (read (fst (refine_checked q n m)) x) (read m x) = true.
  Proof.
    intros q n. revert q. induction n as [y a|o a ns IH]; intros q m x.
    - cbn [refine_checked fst]. unfold read at 1.
      destruct (X.eqb_spec x y) as [Heq|Hneq].
      + subst x. rewrite M.get_set_same. apply V.meet_lb_l.
      + rewrite M.get_set_other by exact Hneq. apply V.leb_refl.
    - cbn [refine_checked]. apply refine_children_lower. exact IH.
  Qed.

  (** The ordered refinement fold retains compatible stores and leaves its flag clear. *)
  Lemma refine_many_covers : forall st ns qs cs,
    Forall2 (fun n c => exists e,
      ann_covers st n e /\ eval_term L.eval st e = Some c) ns cs ->
    Forall2 V.gamma qs cs -> forall m, gamma (Reached m) st ->
    let result := fold_left (fun result nq =>
      let next := refine_checked (snd nq) (fst nq) (fst result) in
      (fst next, orb (snd result) (snd next))) (combine ns qs) (m, false) in
    gamma (Reached (fst result)) st /\ snd result = false.
  Proof.
    intros st ns qs cs Hresults. revert qs.
    induction Hresults as [|n c ns cs Hresult Hresults IH];
      intros qs Hrequests m Hgamma.
    - inversion Hrequests; subst. cbn. split; [exact Hgamma|reflexivity].
    - inversion Hrequests as [|request value requests values Hrequest Hrequests']; subst.
      destruct Hresult as [e [Hcover Heval]].
      destruct (refine_checked_covers n m st e request c
        (proj2 Hgamma) Hcover Heval Hrequest) as [Hmodel Hflag].
      cbn [combine fold_left fst snd]. rewrite Hflag. cbn [orb].
      apply IH; [exact Hrequests'|]. split; [|exact Hmodel].
      apply refine_checked_nonbot; [exact (proj1 Hgamma)|exact Hflag].
  Qed.

  (** Assuming a true guard retains its concrete environment. *)
  Lemma assume_sound : forall g es s st cs,
    gamma s st -> eval_terms L.eval st es = Some cs -> L.holds g cs ->
    gamma (assume g es s) st.
  Proof.
    intros g es [|m] st cs Hgamma Heval Hholds; [contradiction|].
    set (ns := map (annotate m) es).
    set (qs := V.guard g (map root ns)).
    assert (Hcovers : Forall2 (ann_covers st) ns es).
    { unfold ns. clear Heval qs ns. induction es as [|e es IH]; cbn [map]; constructor.
      - apply annotate_covers. exact (proj2 Hgamma).
      - exact IH. }
    pose proof (ann_children_results st ns es cs Hcovers Heval) as Hresults.
    pose proof (ann_results_roots st ns cs Hresults) as Hroots.
    pose proof (V.guard_sound g (map root ns) cs Hroots Hholds) as Hrequests.
    change (Forall2 V.gamma qs cs) in Hrequests.
    destruct (refine_many_covers st ns qs cs Hresults Hrequests m Hgamma)
      as [Hmodel Hflag].
    cbn [assume]. fold ns. fold qs. cbn beta zeta in Hflag, Hmodel.
    rewrite Hflag. exact Hmodel.
  Qed.
  (** Abstract evaluation describes every successful concrete result. *)
  Lemma eval_sound : forall e s st c,
    gamma s st -> eval_term L.eval st e = Some c -> V.gamma (eval e s) c.
  Proof.
    intros e [|m] st c Hgamma Heval; [contradiction|].
    eapply annotate_value_sound; [exact (proj2 Hgamma)|exact Heval].
  Qed.

  (** Reading an absent key returns top. *)
  Lemma read_spec : forall m x,
    read m x = match M.get x m with Some a => a | None => V.top end.
  Proof.
    intros m x.
    reflexivity.
  Qed.
  (** Leaf roots expose their stored abstract value. *)
  Lemma root_leaf : forall x a, root (ALeaf x a) = a.
  Proof.
    reflexivity.
  Qed.
  (** Node roots expose their stored abstract value. *)
  Lemma root_node : forall o a ns, root (ANode o a ns) = a.
  Proof.
    reflexivity.
  Qed.
  (** Leaf annotation reads the current environment. *)
  Lemma annotate_leaf : forall m x, annotate m (Leaf x) = ALeaf x (read m x).
  Proof.
    reflexivity.
  Qed.
  (** Node annotation transfers the annotated child roots. *)
  Lemma annotate_node : forall m o es, annotate m (Node o es) =
    ANode o (V.forward o (map (fun e => root (annotate m e)) es)) (map (annotate m) es).
  Proof.
    intros m o es. cbn [annotate]. now rewrite map_map.
  Qed.
  (** Unreachable states describe no stores. *)
  Lemma gamma_unreached : forall st, ~ gamma Unreached st.
  Proof.
    intros st Hbot. exact Hbot.
  Qed.
  (** Reached maps without recognized bottoms describe stores pointwise. *)
  Lemma gamma_reached : forall m st,
    gamma (Reached m) st <->
      M.existsb V.is_bot m = false /\ forall x, V.gamma (read m x) (st x).
  Proof.
    reflexivity.
  Qed.
End Env.

Module EnvTimingHelpers (X : KEY_T) (M : MAP_T X) (L : LANG_T)
    (V : VALUE_DOMAIN_T L).
  Include Env X M L V.
  TimeFun read.
  TimeFun bot.
  TimeFun top.
  TimeFun is_bot.
  TimeFun option_leb.
  TimeFun leb_entry.
  TimeFun leb.
  TimeFun join_map.
  TimeFun join.
  TimeFun meet.
  TimeFun widen.
  TimeFun narrow.
  TimeFun root.
  TimeFun annotate.
  TimeFun erase.
  TimeFun refine_checked.
  TimeFun refine.
  TimeFun eval.
  TimeFun assign.
  TimeFun havoc.
  TimeFun vars.
  TimeFun materialize.
  TimeFun assume.
End EnvTimingHelpers.

Module EnvT (X : KEY_T) (M : MAP_T X) (L : LANG_T) (V : VALUE_DOMAIN_T L)
    <: ENV_ALL X M L V.
  Include Env X M L V.
  TimeFun read.
  TimeFun bot.
  TimeFun top.
  TimeFun is_bot.
  TimeFun option_leb.
  TimeFun leb_entry.
  TimeFun leb.
  TimeFun join_map.
  TimeFun join.
  TimeFun meet.
  TimeFun widen.
  TimeFun narrow.
  TimeFun root.
  TimeFun annotate.
  TimeFun erase.
  TimeFun refine_checked.
  TimeFun refine.
  TimeFun eval.
  TimeFun assign.
  TimeFun havoc.
  TimeFun vars.
  TimeFun materialize.
  TimeFun assume.

  Definition size (s : t) : nat :=
    match s with
    | Unreached => 0
    | Reached m => M.nodes m + fold_right Nat.add 1
      (map (fun p =>
        match M.find p m with Some a => V.size a + 1 | None => 0 end) (M.codes m))
    end.
  Definition wsize (p : wparam) : nat := V.wsize p.
  Definition wunits (s : t) : nat :=
    match s with Unreached => 0 | Reached m => length (M.codes m) end.
  Fixpoint tcost (m : M.t V.t) (e : term L.op X.t) : nat :=
    match e with
    | Leaf x => X.bits x + 1
    | Node o es =>
      fold_right Nat.add 0 (map (tcost m) es) +
        V.work o (map (fun e => root (annotate m e)) es) + 1
    end.
  Fixpoint refine_size (q : V.t) (n : ann L.op X.t V.t) (m : M.t V.t) : nat :=
    match n with
    | ALeaf x _ => Nat.max (V.size q) (V.size (read m x))
    | ANode o _ ns =>
      let qs := V.backward o q (map root ns) in
      Nat.max (V.size q)
        ((fix children ns qs m :=
          match ns, qs with
          | n :: ns, q :: qs =>
            Nat.max (refine_size q n m) (children ns qs (refine q n m))
          | _, _ => 0
          end) ns qs m)
    end.
  Definition assume_size (s : t) (g : L.guard) (es : list (term L.op X.t)) : nat :=
    match s with
    | Unreached => 0
    | Reached m =>
      let ns := map (annotate m) es in
      let qs := V.guard g (map root ns) in
      fst (fold_left (fun acc nq =>
        (Nat.max (fst acc) (refine_size (snd nq) (fst nq) (snd acc)),
          refine (snd nq) (fst nq) (snd acc))) (combine ns qs) (0, m))
    end.
  Definition assign_work (x : X.t) (e : term L.op X.t) (s : t) : nat :=
    match s with
    | Unreached => tsize e + X.bits x + 1
    | Reached m => tcost m e + size s + X.bits x + 1
    end.
  Definition havoc_work (x : X.t) (s : t) : nat := size s + X.bits x + 1.
  Definition eval_work (e : term L.op X.t) (s : t) : nat :=
    match s with Unreached => tsize e + 1 | Reached m => tcost m e + 1 end.
  Definition tcost_s (s : t) (e : term L.op X.t) : nat :=
    match s with Unreached => 0 | Reached m => tcost m e end.
  Definition rsize (s : t) (g : L.guard) (es : list (term L.op X.t)) : nat :=
    assume_size s g es.
  Definition esize (s : t) : nat := size s.
  Definition env_wf (s : t) : Prop :=
    match s with Unreached => True | Reached m => M.wf m end.
  Definition assume_work (g : L.guard) (es : list (term L.op X.t)) (s : t) : nat :=
    fold_right Nat.add 0 (map (tcost_s s) es) +
      V.gwork g (roots s es) +
      fold_right Nat.add 0 (map tsize es) * (rsize s g es + 1) + 1.
  (** Pointwise time bounds sum over a list of charged values. *)
  Lemma time_sum_bound : forall {A} (f : A -> N) (w : A -> nat) xs c,
    (forall x, In x xs -> (f x <= c * N.of_nat (w x))%N) ->
    (fold_right N.add 0 (map f xs) <=
      c * N.of_nat (fold_right Nat.add 0%nat (map w xs)))%N.
  Proof.
    intros A f w xs c. induction xs as [|x xs IH]; intro Hbound.
    - cbn. lia.
    - specialize (IH (fun y Hy => Hbound y (or_intror Hy))).
      specialize (Hbound x (or_introl eq_refl)).
      cbn [map fold_right]. rewrite Nat2N.inj_add. nia.
  Qed.

  (** Mapping adds one traversal unit per list cell and its final empty cell. *)
  Lemma time_map_sum : forall {A B} (f : A -> B) Tf (xs : list A),
    ListDef.T_map f Tf xs =
    (fold_right N.add 0 (map Tf xs) + N.of_nat (length xs) + 1)%N.
  Proof.
    intros A B f Tf xs. induction xs as [|x xs IH].
    - reflexivity.
    - cbn [map fold_right length]. unfold ListDef.T_map at 1.
      fold (@ListDef.T_map A B f Tf). rewrite IH, Nat2N.inj_succ. nia.
  Qed.

  (** Reading cached roots costs two units per annotated child. *)
  Lemma time_roots : forall ns,
    ListDef.T_map root T_root ns = (2 * N.of_nat (length ns) + 1)%N.
  Proof.
    intro ns. rewrite time_map_sum. induction ns as [|n ns IH].
    - reflexivity.
    - cbn [map fold_right length]. unfold T_root in *.
      rewrite Nat2N.inj_succ. nia.
  Qed.

  (** Every term carries a positive annotation charge. *)
  Lemma tcost_positive : forall m e, 1 <= tcost m e.
  Proof.
    intros m [x|o es]; cbn [tcost]; lia.
  Qed.

  (** Child term charges cover the length of the child list. *)
  Lemma tcost_lengths : forall m es,
    length es <= fold_right Nat.add 0%nat (map (tcost m) es).
  Proof.
    intros m es. induction es as [|e es IH]; cbn; [lia|].
    pose proof (tcost_positive m e). lia.
  Qed.

  (** Each annotation keeps three units to pay its parent traversal. *)
  Lemma annotate_time_reserve : forall m e,
    (T_annotate m e + 3 <= (M.c_map + V.c_val + 8) * N.of_nat (tcost m e))%N.
  Proof.
    intro m. induction e as [x|o es IH].
    - unfold T_annotate, T_read. cbn [tcost].
      pose proof (M.T_get_le V.t x m) as Hget. rewrite Nat2N.inj_add. cbn [N.of_nat].
      nia.
    - assert (Hkids :
        (fold_right N.add 0 (map (T_annotate m) es) +
          3 * N.of_nat (length es) <=
          (M.c_map + V.c_val + 8) *
            N.of_nat (fold_right Nat.add 0%nat (map (tcost m) es)))%N).
      { induction IH as [|e He es Hes IHes]; cbn [map fold_right length]; [lia|].
        rewrite Nat2N.inj_add, Nat2N.inj_succ. nia. }
      pose proof (V.T_forward_le o (map root (map (annotate m) es))) as Hforward.
      unfold T_annotate at 1. fold T_annotate. cbn beta zeta.
      rewrite time_map_sum, time_roots, length_map.
      cbn [tcost]. rewrite map_map in Hforward |- *.
      repeat rewrite Nat2N.inj_add in Hforward.
      repeat rewrite Nat2N.inj_add.
      change (N.of_nat 1) with 1%N in Hforward |- *.
      change (fun e : term L.op X.t => T_annotate m e) with (T_annotate m). nia.
  Qed.

  Definition c_lat : N :=
    (64 * (M.c_map + 1) * (V.c_val + 1) * (V.c_val + 1) *
      (N.of_nat (V.size V.top) + 1))%N.
  Lemma c_lat_pos : (1 <= c_lat)%N.
  Proof.
    unfold c_lat. nia.
  Qed.
  Definition env_refine_factor : N :=
    (2 * M.c_map + 2 * V.c_val * (V.c_val + 1) + 16)%N.
  Definition c_state : N :=
    (c_lat + 64 * env_refine_factor + 64 * (M.c_map + V.c_val + 8))%N.
  Definition c_env : N := c_state.

  (** The state constant covers both annotation and key operations. *)
  Lemma state_annotation_factor : (M.c_map + V.c_val + 8 <= c_state)%N.
  Proof.
    unfold c_state. nia.
  Qed.
  Create Rewrite HintDb env_time_nat.
  Local Hint Rewrite Nat2N.inj_add Nat2N.inj_mul Nat2N.inj_succ Nat2N.inj_max
    : env_time_nat.

  (** A stored value pays for its payload and its occupied map cell. *)
  Definition time_option_weight (a : option V.t) :=
    match a with Some v => V.size v + 1 | None => 0 end.
  (** The payload charge sums the occupied entries of a map. *)
  Definition time_store_size (m : M.t V.t) :=
    fold_right Nat.add 0 (map (fun c => time_option_weight (M.find c m)) (M.codes m)).

  (** A nonzero fold seed is added after the list's total charge. *)
  Lemma time_sum_seed : forall xs z,
    fold_right Nat.add z xs = fold_right Nat.add 0 xs + z.
  Proof.
    intro xs. induction xs as [|x xs IH]; intro z; cbn; [lia|rewrite IH; lia].
  Qed.

  (** Appended lists contribute the sum of their separate charges. *)
  Lemma time_sum_app : forall {A} (f : A -> nat) xs ys,
    fold_right Nat.add 0 (map f (xs ++ ys)) =
    fold_right Nat.add 0 (map f xs) + fold_right Nat.add 0 (map f ys).
  Proof.
    intros A f xs ys. rewrite map_app, fold_right_app, time_sum_seed. reflexivity.
  Qed.

  (** Pairwise charges separate into two sums and a per-entry overhead. *)
  Lemma time_sum_pair : forall {A} (f g : A -> nat) xs z,
    fold_right Nat.add 0 (map (fun x => f x + g x + z) xs) =
    fold_right Nat.add 0 (map f xs) + fold_right Nat.add 0 (map g xs) + length xs * z.
  Proof.
    intros A f g xs z. induction xs as [|x xs IH]; cbn; [lia|rewrite IH; lia].
  Qed.

  (** A duplicate-free sublist never costs more than its containing list. *)
  Lemma time_sum_incl : forall {A} (f : A -> nat) xs ys,
    NoDup xs -> incl xs ys ->
    fold_right Nat.add 0 (map f xs) <= fold_right Nat.add 0 (map f ys).
  Proof.
    intros A f xs ys Hnd. revert ys.
    induction Hnd as [|x xs Hnot Hnd IH]; intros ys Hincl; cbn [map fold_right]; [lia|].
    destruct (in_split x ys (Hincl x (or_introl eq_refl))) as [left [right Heq]].
    subst ys.
    assert (Htail : incl xs (left ++ right)).
    { intros y Hy. specialize (Hincl y (or_intror Hy)).
      apply in_app_iff in Hincl. destruct Hincl as [Hleft|[Heq|Hright]].
      - apply in_or_app. now left.
      - subst y. contradiction.
      - apply in_or_app. now right. }
    specialize (IH _ Htail). rewrite time_sum_app in IH.
    rewrite time_sum_app. cbn [map fold_right]. lia.
  Qed.

  (** Distinct lookups charge each occupied map entry at most once. *)
  Lemma time_lookup_sum : forall m xs, NoDup xs ->
    fold_right Nat.add 0 (map (fun c => time_option_weight (M.find c m)) xs) <=
    time_store_size m.
  Proof.
    intros m xs Hnd.
    set (present := fun c => match M.find c m with Some _ => true | None => false end).
    assert (Hzero : fold_right Nat.add 0
        (map (fun c => time_option_weight (M.find c m)) (filter present xs)) =
      fold_right Nat.add 0 (map (fun c => time_option_weight (M.find c m)) xs)).
    { apply rank_sum_filter_zero. intros c _ Hfalse. unfold present in Hfalse.
      destruct (M.find c m); [discriminate|reflexivity]. }
    rewrite <- Hzero. apply time_sum_incl.
    - apply NoDup_filter. exact Hnd.
    - intros c Hc. apply filter_In in Hc as [_ Hpresent]. apply M.codes_spec.
      unfold present in Hpresent. destruct (M.find c m); congruence.
  Qed.

  (** Payload charges cover the number of occupied entries. *)
  Lemma time_store_length : forall m, length (M.codes m) <= time_store_size m.
  Proof.
    intro m. unfold time_store_size.
    assert (Hbound : forall c, In c (M.codes m) -> 1 <= time_option_weight (M.find c m)).
    { intros c Hc. apply M.codes_spec in Hc.
      destruct (M.find c m); cbn [time_option_weight]; [lia|contradiction]. }
    induction (M.codes m) as [|c cs IH]; cbn [map fold_right length]; [lia|].
    pose proof (Hbound c (or_introl eq_refl)).
    specialize (IH (fun d Hd => Hbound d (or_intror Hd))). lia.
  Qed.

  (** Both code lists charge each map payload twice and the supplied per-key work. *)
  Lemma time_codes_pair_sum : forall a b w,
    fold_right Nat.add 0 (map (fun c =>
      time_option_weight (M.find c a) + time_option_weight (M.find c b) + (w + 1))
      (M.codes a ++ M.codes b)) <=
    3 * (time_store_size a + time_store_size b) +
      (length (M.codes a) + length (M.codes b)) * w.
  Proof.
    intros a b w. rewrite time_sum_pair, !time_sum_app, length_app.
    pose proof (time_lookup_sum a (M.codes b) (M.codes_nodup V.t b)) as Hleft.
    pose proof (time_lookup_sum b (M.codes a) (M.codes_nodup V.t a)) as Hright.
    pose proof (time_store_length a) as Halen.
    pose proof (time_store_length b) as Hblen.
    unfold time_store_size in *. nia.
  Qed.

  (** Environment size separates the map skeleton, its payloads, and one state cell. *)
  Lemma time_size_reached : forall m,
    size (Reached m) = M.nodes m + time_store_size m + 1.
  Proof.
    intro m. unfold size, time_store_size, time_option_weight.
    rewrite time_sum_seed. lia.
  Qed.
  (** Value callbacks may inspect top and then test a newly constructed result. *)
  Definition time_value_factor :=
    ((V.c_val + 1) * (V.c_val + 1) * (N.of_nat (V.size V.top) + 1))%N.
  (** One map unit combines skeleton traversal with the value callback factor. *)
  Definition time_map_unit := ((M.c_map + 1) * time_value_factor)%N.

  (** The value factor pays for an operation followed by a test of its result. *)
  Lemma time_factor_square : ((V.c_val + 1) * (V.c_val + 1) <= time_value_factor)%N.
  Proof.
    unfold time_value_factor. nia.
  Qed.
  (** The value factor covers comparisons against an implicit top binding. *)
  Lemma time_factor_top :
    ((V.c_val + 1) * (N.of_nat (V.size V.top) + 1) <= time_value_factor)%N.
  Proof.
    unfold time_value_factor. nia.
  Qed.
  (** A value factor pays for at least one callback entry. *)
  Lemma time_factor_positive : (1 <= time_value_factor)%N.
  Proof.
    unfold time_value_factor. nia.
  Qed.
  (** A map unit pays for at least one enclosing operation. *)
  Lemma time_map_unit_positive : (1 <= time_map_unit)%N.
  Proof.
    pose proof time_factor_positive. unfold time_map_unit. nia.
  Qed.
  (** The public lattice coefficient reserves sixty-four map units. *)
  Lemma time_c_lat_units : c_lat = (64 * time_map_unit)%N.
  Proof.
    unfold c_lat, time_map_unit, time_value_factor. ring.
  Qed.

  (** Pointwise callback bounds sum over the two input maps' occupied codes. *)
  Lemma time_callback_sum : forall a b Tf w c,
    (forall x y, (Tf x y <= c * N.of_nat
      (time_option_weight x + time_option_weight y + (w + 1)))%N) ->
    (fold_right N.add 0
      (map (fun p => Tf (M.find p a) (M.find p b)) (M.codes a ++ M.codes b)) <=
      c * N.of_nat (3 * (time_store_size a + time_store_size b) +
        (length (M.codes a) + length (M.codes b)) * w))%N.
  Proof.
    intros a b Tf w c Hcallback.
    eapply N.le_trans; [apply time_sum_bound; intros p _; apply Hcallback|].
    apply N.mul_le_mono_l. pose proof (time_codes_pair_sum a b w). lia.
  Qed.

  (** A binary map clock combines its skeleton bound and the summed callback charges. *)
  Lemma time_binary_map_bound : forall a b Tf w clock c,
    (1 <= c)%N -> Tf None None = 1%N ->
    (forall x y, (Tf x y <= c * N.of_nat
      (time_option_weight x + time_option_weight y + (w + 1)))%N) ->
    (clock <= M.c_map *
      ((Tf None None + 1) * N.of_nat (M.nodes a + M.nodes b + 1) +
      fold_right N.add 0
        (map (fun p => Tf (M.find p a) (M.find p b)) (M.codes a ++ M.codes b))))%N ->
    (clock <= 4 * (M.c_map + 1) * c * N.of_nat
      ((length (M.codes a) + length (M.codes b)) * w +
        (size (Reached a) + size (Reached b) + 1)))%N.
  Proof.
    intros a b Tf w clock c Hpos Hnone Hcallback Hclock.
    pose proof (time_callback_sum a b Tf w c Hcallback) as Hsum.
    rewrite Hnone in Hclock.
    assert (Hraw : (clock <= M.c_map *
      (2 * N.of_nat (M.nodes a + M.nodes b + 1) +
        c * N.of_nat (3 * (time_store_size a + time_store_size b) +
          (length (M.codes a) + length (M.codes b)) * w)))%N).
    { eapply N.le_trans; [exact Hclock|].
      apply N.mul_le_mono_l. apply N.add_le_mono_l. exact Hsum. }
    rewrite !time_size_reached.
    autorewrite with env_time_nat in Hraw |- *.
    change (N.succ (N.of_nat 0)) with 1%N in Hraw |- *.
    change (N.succ (N.succ (N.succ (N.of_nat 0)))) with 3%N in Hraw.
    clear Hclock Hsum Hcallback Hnone.
    nia.
  Qed.

  (** Bottom testing traverses one skeleton and tests each occupied payload. *)
  Lemma time_bot_raw : forall a,
    (T_is_bot a <= (M.c_map + 1) * (V.c_val + 1) * N.of_nat (size a + 1))%N.
  Proof.
    intros [|m].
    - change (1 <= (M.c_map + 1) * (V.c_val + 1) * 1)%N. nia.
    - pose proof (M.T_existsb_sum_le V.t V.is_bot V.T_is_bot m) as Hmap.
      assert (Hsum :
        (fold_right N.add 0 (map (fun p => match M.find p m with
          Some a => V.T_is_bot a | None => 0 end) (M.codes m)) <=
          V.c_val * N.of_nat (time_store_size m))%N).
      { apply time_sum_bound. intros p _.
        destruct (M.find p m) as [a|]; cbn [time_option_weight]; [apply V.T_is_bot_le|nia]. }
      change (1 + M.T_existsb V.is_bot V.T_is_bot m <=
        (M.c_map + 1) * (V.c_val + 1) * N.of_nat (size (Reached m) + 1))%N.
      rewrite time_size_reached. autorewrite with env_time_nat in Hmap |- *.
      change (N.succ (N.of_nat 0)) with 1%N in Hmap |- *. nia.
  Qed.

  (** Option comparison includes the cost of top when the left binding is absent. *)
  Lemma time_option_comparison : forall x y,
    (T_option_leb x y <= time_value_factor * N.of_nat
      (time_option_weight x + time_option_weight y + (0 + 1)))%N.
  Proof.
    intros [a|] [b|]; unfold T_option_leb; cbn [time_option_weight];
      pose proof time_factor_top as Htop;
      pose proof time_factor_square as Hsquare;
      pose proof time_factor_positive as Hpos.
    - pose proof (V.T_leb_le a b) as Hle.
      autorewrite with env_time_nat in Hle |- *.
      change (N.succ (N.of_nat 0)) with 1%N in Hle |- *. nia.
    - autorewrite with env_time_nat. change (N.succ (N.of_nat 0)) with 1%N. nia.
    - pose proof (V.T_leb_le V.top b) as Hle.
      autorewrite with env_time_nat in Hle |- *.
      change (N.succ (N.of_nat 0)) with 1%N in Hle |- *. nia.
    - change (1 <= time_value_factor * 1)%N. nia.
  Qed.

  (** The value factor also covers a single primitive value operation. *)
  Lemma time_factor_linear : (V.c_val + 1 <= time_value_factor)%N.
  Proof.
    pose proof time_factor_square. nia.
  Qed.

  (** A fused entry pays for a right-bottom test and one optional comparison. *)
  Lemma time_leb_entry : forall x y,
    (T_leb_entry x y <= 2 * time_value_factor * N.of_nat
      (time_option_weight x + time_option_weight y + (0 + 1)))%N.
  Proof.
    intros x y. pose proof (time_option_comparison x y) as Hcompare.
    pose proof time_factor_linear as Hfactor.
    pose proof time_factor_positive as Hpositive.
    unfold T_leb_entry. destruct y as [b|]; cbn [time_option_weight] in Hcompare |- *.
    - pose proof (V.T_is_bot_le b) as Hbot. destruct (V.is_bot b);
        autorewrite with env_time_nat in Hcompare, Hbot |- *;
        change (N.succ (N.of_nat 0)) with 1%N in Hcompare, Hbot |- *; nia.
    - autorewrite with env_time_nat in Hcompare |- *.
      change (N.succ (N.of_nat 0)) with 1%N in Hcompare |- *. nia.
  Qed.

  (** One map unit bounds environment bottom testing. *)
  Lemma time_bot_unit : forall a,
    (T_is_bot a <= time_map_unit * N.of_nat (size a + 1))%N.
  Proof.
    intro a. eapply N.le_trans; [apply time_bot_raw|].
    apply N.mul_le_mono_r. unfold time_map_unit. apply N.mul_le_mono_l.
    apply time_factor_linear.
  Qed.

  (** Comparing both maps takes four map units per combined size charge. *)
  Lemma time_forall2_raw : forall a b,
    (M.T_forall2b option_leb T_option_leb a b <=
      4 * time_map_unit * N.of_nat (size (Reached a) + size (Reached b) + 1))%N.
  Proof.
    intros a b.
    pose proof (time_binary_map_bound a b T_option_leb 0
      (M.T_forall2b option_leb T_option_leb a b) time_value_factor
      time_factor_positive eq_refl time_option_comparison
      (M.T_forall2b_sum_le V.t V.t option_leb T_option_leb a b)) as Hmap.
    rewrite Nat.mul_0_r, Nat.add_0_l in Hmap. unfold time_map_unit. nia.
  Qed.

  (** Fusing the right-bottom test into comparison takes at most eight map units. *)
  Lemma time_forall2_entry : forall a b,
    (M.T_forall2b leb_entry T_leb_entry a b <=
      8 * time_map_unit * N.of_nat (size (Reached a) + size (Reached b) + 1))%N.
  Proof.
    intros a b.
    pose proof (M.T_forall2b_sum_le V.t V.t leb_entry T_leb_entry a b) as Hmap.
    pose proof (time_callback_sum a b T_leb_entry 0 (2 * time_value_factor)%N
      time_leb_entry) as Hsum.
    change (T_leb_entry None None) with 2%N in Hmap.
    rewrite Nat.mul_0_r, Nat.add_0_r in Hsum.
    rewrite !time_size_reached.
    autorewrite with env_time_nat in Hmap, Hsum |- *.
    change (N.succ (N.of_nat 0)) with 1%N in Hmap, Hsum |- *.
    change (N.succ (N.succ (N.succ (N.of_nat 0)))) with 3%N in Hsum.
    pose proof time_factor_positive as Hpositive. unfold time_map_unit. nia.
  Qed.

  (** Inclusion retains a sixteen-unit bound for use inside widening. *)
  Lemma time_leb_raw : forall a b,
    (T_leb a b <= 16 * time_map_unit * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. pose proof (time_bot_unit a) as Ha.
    pose proof time_map_unit_positive as Hu.
    destruct a as [|a], b as [|b].
    - change (1 <= 16 * time_map_unit * 1)%N. nia.
    - change (1 <= 16 * time_map_unit * N.of_nat (0 + size (Reached b) + 1))%N.
      autorewrite with env_time_nat. change (N.succ (N.of_nat 0)) with 1%N. nia.
    - change (1 + M.T_existsb V.is_bot V.T_is_bot a <=
        16 * time_map_unit * N.of_nat (size (Reached a) + 0 + 1))%N.
      change (1 + M.T_existsb V.is_bot V.T_is_bot a <=
        time_map_unit * N.of_nat (size (Reached a) + 1))%N in Ha.
      autorewrite with env_time_nat in Ha |- *.
      change (N.succ (N.of_nat 0)) with 1%N in Ha |- *. nia.
    - pose proof (time_forall2_entry a b) as Hmaps.
      change (1 + M.T_existsb V.is_bot V.T_is_bot a <=
        time_map_unit * N.of_nat (size (Reached a) + 1))%N in Ha.
      time_unfold T_leb.
      change (fun x y : option V.t => T_leb_entry x y) with T_leb_entry.
      change (fun x : V.t => V.T_is_bot x) with V.T_is_bot.
      destruct (M.forall2b leb_entry a b);
        autorewrite with env_time_nat in Ha, Hmaps |- *;
        change (N.succ (N.of_nat 0)) with 1%N in Ha, Hmaps |- *; nia.
  Qed.

  (** An operation and a bottom test share the operation's result-size bound. *)
  Lemma time_checked_result : forall result clock n,
    (clock <= V.c_val * N.of_nat n)%N ->
    (N.of_nat (V.size result) <= V.c_val * N.of_nat n)%N ->
    (1 + (clock + V.T_is_bot result) <=
      time_value_factor * N.of_nat (n + 2))%N.
  Proof.
    intros result clock n Hclock Hsize.
    pose proof (V.T_is_bot_le result) as Hbottom.
    assert (Hbot :
      (V.T_is_bot result <= V.c_val * (V.c_val * N.of_nat n + 1))%N).
    { eapply N.le_trans; [exact Hbottom|]. apply N.mul_le_mono_l.
      rewrite Nat2N.inj_add. change (N.of_nat 1) with 1%N. lia. }
    eapply N.le_trans with
      (((V.c_val + 1) * (V.c_val + 1)) * N.of_nat (n + 2))%N.
    - rewrite Nat2N.inj_add. change (N.of_nat 2) with 2%N. nia.
    - apply N.mul_le_mono_r. apply time_factor_square.
  Qed.

  (** The join callback pays for construction and its result's bottom test. *)
  Lemma time_join_callback : forall x y,
    ((1 + match x, y with
      | Some a, Some b => V.T_join a b + V.T_is_bot (V.join a b)
      | _, _ => 0
      end) <= time_value_factor * N.of_nat
        (time_option_weight x + time_option_weight y + (0 + 1)))%N.
  Proof.
    intros [a|] [b|]; cbn [time_option_weight];
      pose proof time_factor_positive as Hpos; try nia.
    pose proof (time_checked_result (V.join a b) (V.T_join a b)
      (V.size a + V.size b + 1) (V.T_join_le a b) (V.join_size a b)) as Hbound.
    replace (V.size a + 1 + (V.size b + 1) + (0 + 1))%nat with
      (V.size a + V.size b + 1 + 2)%nat by lia. exact Hbound.
  Qed.

  (** The widening callback includes the parameter charge and its result's bottom test. *)
  Lemma time_widen_callback : forall p x y,
    ((1 + match x, y with
      | Some a, Some b => V.T_widen p a b + V.T_is_bot (V.widen p a b)
      | _, _ => 0
      end) <= time_value_factor * N.of_nat
        (time_option_weight x + time_option_weight y + (V.wsize p + 1)))%N.
  Proof.
    intros p [a|] [b|]; cbn [time_option_weight];
      pose proof time_factor_positive as Hpos; try nia.
    pose proof (time_checked_result (V.widen p a b) (V.T_widen p a b)
      (V.size a + V.size b + V.wsize p + 1)
      (V.T_widen_le p a b) (V.widen_size p a b)) as Hbound.
    replace (V.size a + 1 + (V.size b + 1) + (V.wsize p + 1))%nat with
      (V.size a + V.size b + V.wsize p + 1 + 2)%nat by lia. exact Hbound.
  Qed.

  (** Narrowing invokes its value operation only when both bindings are present. *)
  Lemma time_narrow_callback : forall x y,
    ((1 + match x, y with
      | Some a, Some b => V.T_narrow a b
      | _, _ => 0
      end) <= time_value_factor * N.of_nat
        (time_option_weight x + time_option_weight y + (0 + 1)))%N.
  Proof.
    intros [a|] [b|]; cbn [time_option_weight];
      pose proof time_factor_linear as Hfactor;
      pose proof time_factor_positive as Hpos.
    - pose proof (V.T_narrow_le a b) as Hnarrow.
      autorewrite with env_time_nat in Hnarrow |- *.
      change (N.succ (N.of_nat 0)) with 1%N in Hnarrow |- *. nia.
    - autorewrite with env_time_nat. change (N.succ (N.of_nat 0)) with 1%N. nia.
    - autorewrite with env_time_nat. change (N.succ (N.of_nat 0)) with 1%N. nia.
    - change (1 <= time_value_factor * 1)%N. nia.
  Qed.

  (** A generated merge callback uses four map units with its per-binding work. *)
  Lemma time_merge_raw : forall f Tf a b w,
    Tf None None = 1%N ->
    (forall x y, (Tf x y <= time_value_factor * N.of_nat
      (time_option_weight x + time_option_weight y + (w + 1)))%N) ->
    (M.T_merge (C := V.t) f Tf a b <= 4 * time_map_unit * N.of_nat
      ((length (M.codes a) + length (M.codes b)) * w +
        (size (Reached a) + size (Reached b) + 1)))%N.
  Proof.
    intros f Tf a b w Hnone Hcallback.
    pose proof (time_binary_map_bound a b Tf w (M.T_merge f Tf a b)
      time_value_factor time_factor_positive Hnone Hcallback
      (M.T_merge_sum_le V.t V.t V.t f Tf a b)) as Hmap.
    unfold time_map_unit. nia.
  Qed.

  (** Map join retains a reserve for the enclosing environment constructor. *)
  Lemma time_join_map_raw : forall a b,
    (T_join_map a b <=
      6 * time_map_unit * N.of_nat (size (Reached a) + size (Reached b) + 1))%N.
  Proof.
    intros a b. time_unfold T_join_map.
    eapply N.le_trans with
      (1 + 4 * time_map_unit * N.of_nat
        ((length (M.codes a) + length (M.codes b)) * 0 +
          (size (Reached a) + size (Reached b) + 1)))%N.
    - apply N.add_le_mono_l. apply time_merge_raw; [reflexivity|apply time_join_callback].
    - rewrite Nat.mul_0_r, Nat.add_0_l.
      pose proof time_map_unit_positive as Hu. autorewrite with env_time_nat.
      change (N.succ (N.of_nat 0)) with 1%N. nia.
  Qed.

  (** Joining environments uses eight map units per combined size charge. *)
  Lemma time_join_raw : forall a b,
    (T_join a b <= 8 * time_map_unit * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. pose proof time_map_unit_positive as Hu.
    assert (Hmaps :
      ((match a, b with
        | Reached ma, Reached mb => T_join_map ma mb
        | _, _ => 0
        end) <= 6 * time_map_unit * N.of_nat (size a + size b + 1))%N).
    { destruct a as [|a], b as [|b]; try apply N.le_0_l. apply time_join_map_raw. }
    time_unfold T_join. autorewrite with env_time_nat in Hmaps |- *.
    change (N.succ (N.of_nat 0)) with 1%N in Hmaps |- *. nia.
  Qed.

  (** Narrowing pays for the right bottom test and its generated merge callback. *)
  Lemma time_narrow_raw : forall a b,
    (T_narrow a b <= 8 * time_map_unit * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. pose proof time_map_unit_positive as Hu.
    pose proof (time_bot_unit b) as Hbot. time_unfold T_narrow.
    destruct (is_bot b).
    - autorewrite with env_time_nat in Hbot |- *.
      change (N.succ (N.of_nat 0)) with 1%N in Hbot |- *. nia.
    - match goal with
      | |- (1 + (_ + ?clock) <= _)%N =>
          assert (Hmerge : (clock <=
            4 * time_map_unit * N.of_nat (size a + size b + 1))%N)
      end.
      { destruct a as [|a], b as [|b]; try apply N.le_0_l.
        eapply N.le_trans.
        - apply time_merge_raw with (w := 0%nat);
            [reflexivity|apply time_narrow_callback].
        - rewrite Nat.mul_0_r, Nat.add_0_l. apply N.le_refl. }
      autorewrite with env_time_nat in Hbot, Hmerge |- *.
      change (N.succ (N.of_nat 0)) with 1%N in Hbot, Hmerge |- *. nia.
  Qed.


  (** Inclusion fits the public lattice time coefficient. *)
  Lemma T_leb_le : forall a b,
    (T_leb a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. rewrite time_c_lat_units.
    eapply N.le_trans; [apply time_leb_raw|]. apply N.mul_le_mono_r. nia.
  Qed.
  (** Join fits the public lattice time coefficient. *)
  Lemma T_join_le : forall a b,
    (T_join a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. rewrite time_c_lat_units.
    eapply N.le_trans; [apply time_join_raw|]. apply N.mul_le_mono_r. nia.
  Qed.
  (** Bottom testing fits the public lattice time coefficient. *)
  Lemma T_is_bot_le : forall a,
    (T_is_bot a <= c_lat * N.of_nat (size a + 1))%N.
  Proof.
    intro a. rewrite time_c_lat_units.
    eapply N.le_trans; [apply time_bot_unit|]. apply N.mul_le_mono_r. nia.
  Qed.
  (** Widening directly charges its generated inclusion test and merge callback. *)
  Lemma T_widen_le : forall p a b,
    (T_widen p a b <= c_lat * N.of_nat
      ((wunits a + wunits b) * wsize p + (size a + size b + wsize p + 1)))%N.
  Proof.
    intros p a b. rewrite time_c_lat_units.
    pose proof (time_leb_raw b a) as Hleb. pose proof time_map_unit_positive as Hu.
    time_unfold T_widen. destruct (leb b a).
    - autorewrite with env_time_nat in Hleb |- *.
      change (N.succ (N.of_nat 0)) with 1%N in Hleb |- *. nia.
    - match goal with
      | |- (1 + (_ + ?clock) <= _)%N =>
          assert (Hmerge : (clock <= 4 * time_map_unit * N.of_nat
            ((wunits a + wunits b) * wsize p + (size a + size b + 1)))%N)
      end.
      { destruct a as [|a], b as [|b]; try apply N.le_0_l.
        cbn [wunits wsize]. apply time_merge_raw;
          [reflexivity|apply time_widen_callback]. }
      autorewrite with env_time_nat in Hleb, Hmerge |- *.
      change (N.succ (N.of_nat 0)) with 1%N in Hleb, Hmerge |- *. nia.
  Qed.
  (** Narrowing fits the public lattice time coefficient. *)
  Lemma T_narrow_le : forall a b,
    (T_narrow a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. rewrite time_c_lat_units.
    eapply N.le_trans; [apply time_narrow_raw|]. apply N.mul_le_mono_r. nia.
  Qed.
  (** Assignment pays for annotation and one encoded-key insertion. *)
  Lemma T_assign_le : forall x e s,
    (T_assign x e s <= c_state * N.of_nat (assign_work x e s + 1))%N.
  Proof.
    intros x e [|m]; pose proof state_annotation_factor as Hfactor.
    - change (1 <= c_state * N.of_nat (tsize e + X.bits x + 1 + 1))%N.
      repeat rewrite Nat2N.inj_add. change (N.of_nat 1) with 1%N. nia.
    - change (1 + (1 + (T_annotate m e + 1) +
        M.T_set x (eval e (Reached m)) m) <=
        c_state * N.of_nat (tcost m e + size (Reached m) + X.bits x + 1 + 1))%N.
      pose proof (annotate_time_reserve m e) as Htime.
      pose proof (M.T_set_le V.t x (eval e (Reached m)) m) as Hset.
      repeat rewrite Nat2N.inj_add in Hset. repeat rewrite Nat2N.inj_add.
      change (N.of_nat 1) with 1%N in Hset |- *. nia.
  Qed.
  (** Havoc only inserts the top value at its encoded key. *)
  Lemma T_havoc_le : forall x s,
    (T_havoc x s <= c_state * N.of_nat (havoc_work x s + 1))%N.
  Proof.
    intros x [|m]; pose proof state_annotation_factor as Hfactor.
    - change (1 <= c_state * N.of_nat (X.bits x + 1 + 1))%N.
      repeat rewrite Nat2N.inj_add. change (N.of_nat 1) with 1%N. nia.
    - change (1 + M.T_set x V.top m <=
        c_state * N.of_nat (size (Reached m) + X.bits x + 1 + 1))%N.
      pose proof (M.T_set_le V.t x V.top m) as Hset.
      repeat rewrite Nat2N.inj_add in Hset. repeat rewrite Nat2N.inj_add.
      change (N.of_nat 1) with 1%N in Hset |- *. nia.
  Qed.
  (** Evaluation extracts the root of one annotation pass. *)
  Lemma T_eval_le : forall e s,
    (T_eval e s <= c_state * N.of_nat (eval_work e s + 1))%N.
  Proof.
    intros e [|m]; pose proof state_annotation_factor as Hfactor.
    - change (1 <= c_state * N.of_nat (tsize e + 1 + 1))%N.
      repeat rewrite Nat2N.inj_add. change (N.of_nat 1) with 1%N. nia.
    - change (1 + (T_annotate m e + 1) <=
        c_state * N.of_nat (tcost m e + 1 + 1))%N.
      pose proof (annotate_time_reserve m e) as Htime.
      repeat rewrite Nat2N.inj_add. change (N.of_nat 1) with 1%N. nia.
  Qed.
  Lemma T_annotate_le : forall m e,
    (T_annotate m e <= c_env * N.of_nat (tcost m e))%N.
  Proof.
    intros m e. pose proof (annotate_time_reserve m e) as Htime.
    pose proof state_annotation_factor as Hfactor. unfold c_env. nia.
  Qed.
  Lemma T_join_env_le : forall a b, env_wf a -> env_wf b ->
    (T_join a b <= c_env * N.of_nat (esize a + esize b + 1))%N.
  Proof.
    intros a b _ _. change (T_join a b <= c_env * N.of_nat (size a + size b + 1))%N.
    eapply N.le_trans; [apply T_join_le|]. apply N.mul_le_mono_r.
    unfold c_env, c_state. lia.
  Qed.

  (** Inclusion is linear in the combined environment sizes. *)
  Lemma leb_complexity : bigO (X := t * t) (fun _ => True)
    (fun ab => N.of_nat (size (fst ab) + size (snd ab)))
    (fun ab => T_leb (fst ab) (snd ab)).
  Proof.
    eapply bigO_intro with (c := c_lat). intros [a b] _.
    change (T_leb a b <= c_lat * N.of_nat (size a + size b) + c_lat)%N.
    pose proof (T_leb_le a b) as Hbound.
    rewrite Nat2N.inj_add in Hbound. nia.
  Qed.

  (** Join is linear in the combined environment sizes. *)
  Lemma join_complexity : bigO (X := t * t) (fun _ => True)
    (fun ab => N.of_nat (size (fst ab) + size (snd ab)))
    (fun ab => T_join (fst ab) (snd ab)).
  Proof.
    eapply bigO_intro with (c := c_lat). intros [a b] _.
    change (T_join a b <= c_lat * N.of_nat (size a + size b) + c_lat)%N.
    pose proof (T_join_le a b) as Hbound.
    rewrite Nat2N.inj_add in Hbound. nia.
  Qed.

  (** Widening charges environment sizes and the parameter work of each binding. *)
  Lemma widen_complexity : bigO (X := wparam * t * t) (fun _ => True)
    (fun '(p, a, b) => N.of_nat ((wunits a + wunits b) * wsize p + (size a + size b + wsize p)))
    (fun '(p, a, b) => T_widen p a b).
  Proof.
    eapply bigO_intro with (c := c_lat). intros [[p a] b] _.
    change (T_widen p a b <= c_lat * N.of_nat
      ((wunits a + wunits b) * wsize p + (size a + size b + wsize p)) + c_lat)%N.
    pose proof (T_widen_le p a b) as Hbound.
    rewrite !Nat2N.inj_add in Hbound |- *. nia.
  Qed.

  (** Assignment is linear in its annotation and insertion work. *)
  Lemma assign_complexity : bigO (X := X.t * term L.op X.t * t) (fun _ => True)
    (fun '(x, e, s) => N.of_nat (assign_work x e s))
    (fun '(x, e, s) => T_assign x e s).
  Proof.
    eapply bigO_intro with (c := c_state). intros [[x e] s] _.
    change (T_assign x e s <= c_state * N.of_nat (assign_work x e s) + c_state)%N.
    pose proof (T_assign_le x e s) as Hbound.
    rewrite Nat2N.inj_add in Hbound. nia.
  Qed.

  (** Havoc is linear in its environment and encoded-key work. *)
  Lemma havoc_complexity : bigO (X := X.t * t) (fun _ => True)
    (fun '(x, s) => N.of_nat (havoc_work x s))
    (fun '(x, s) => T_havoc x s).
  Proof.
    eapply bigO_intro with (c := c_state). intros [x s] _.
    change (T_havoc x s <= c_state * N.of_nat (havoc_work x s) + c_state)%N.
    pose proof (T_havoc_le x s) as Hbound.
    rewrite Nat2N.inj_add in Hbound. nia.
  Qed.

  (** Evaluation is linear in the work of one annotation pass. *)
  Lemma eval_complexity : bigO (X := term L.op X.t * t) (fun _ => True)
    (fun '(e, s) => N.of_nat (eval_work e s))
    (fun '(e, s) => T_eval e s).
  Proof.
    eapply bigO_intro with (c := c_state). intros [e s] _.
    change (T_eval e s <= c_state * N.of_nat (eval_work e s) + c_state)%N.
    pose proof (T_eval_le e s) as Hbound.
    rewrite Nat2N.inj_add in Hbound. nia.
  Qed.

  (** Bottom recognition is linear in the environment size. *)
  Lemma is_bot_complexity : bigO (fun _ : t => True) (fun a => N.of_nat (size a)) T_is_bot.
  Proof.
    eapply bigO_intro with (c := c_lat). intros a _.
    pose proof (T_is_bot_le a) as Hbound.
    rewrite Nat2N.inj_add in Hbound. nia.
  Qed.

  (** Narrowing is linear in the combined environment sizes. *)
  Lemma narrow_complexity : bigO (X := t * t) (fun _ => True)
    (fun ab => N.of_nat (size (fst ab) + size (snd ab)))
    (fun ab => T_narrow (fst ab) (snd ab)).
  Proof.
    eapply bigO_intro with (c := c_lat). intros [a b] _.
    change (T_narrow a b <= c_lat * N.of_nat (size a + size b) + c_lat)%N.
    pose proof (T_narrow_le a b) as Hbound.
    rewrite Nat2N.inj_add in Hbound. nia.
  Qed.

  Lemma wunits_unreached_def : wunits Unreached = 0.
  Proof.
    reflexivity.
  Qed.
  Lemma wunits_reached_def : forall m, wunits (Reached m) = length (M.codes m).
  Proof.
    reflexivity.
  Qed.
  Lemma bot_def : bot = Unreached.
  Proof.
    reflexivity.
  Qed.
  Lemma top_def : top = Reached M.empty.
  Proof.
    reflexivity.
  Qed.
  Lemma join_map_def : forall a b, join_map a b =
    M.merge (fun x y => match x, y with
      | Some a, Some b => let v := V.join a b in if V.is_bot v then None else Some v
      | _, _ => None
      end) a b.
  Proof.
    reflexivity.
  Qed.
  Lemma join_def : forall a b, join a b =
    match a, b with
    | Unreached, s | s, Unreached => s
    | Reached a, Reached b => Reached (join_map a b)
    end.
  Proof.
    reflexivity.
  Qed.
  Lemma widen_def : forall p a b, widen p a b =
    if leb b a then a else
    match a, b with
    | Unreached, s | s, Unreached => s
    | Reached a, Reached b => Reached (M.merge (fun x y => match x, y with
        | Some a, Some b => let v := V.widen p a b in if V.is_bot v then None else Some v
        | _, _ => None
        end) a b)
    end.
  Proof.
    reflexivity.
  Qed.
  Lemma narrow_def : forall a b, narrow a b =
    if is_bot b then b else
    match a, b with
    | Unreached, _ => Unreached
    | s, Unreached => s
    | Reached a, Reached b => Reached (M.merge (fun x y => match x, y with
        | None, None => None
        | Some a, None => Some a
        | None, Some b => Some b
        | Some a, Some b => Some (V.narrow a b)
        end) a b)
    end.
  Proof.
    reflexivity.
  Qed.
  Lemma eval_def : forall e s, eval e s =
    match s with Unreached => V.bot | Reached m => root (annotate m e) end.
  Proof.
    reflexivity.
  Qed.
  Lemma assign_def : forall x e s, assign x e s =
    match s with
    | Unreached => Unreached
    | Reached m => Reached (M.set x (eval e s) m)
    end.
  Proof.
    reflexivity.
  Qed.
  Lemma havoc_def : forall x s, havoc x s =
    match s with
    | Unreached => Unreached
    | Reached m => Reached (M.set x V.top m)
    end.
  Proof.
    reflexivity.
  Qed.
  Lemma refine_leaf_def : forall q x a m, refine_checked q (ALeaf x a) m =
    let v := V.meet (read m x) q in (M.set x v m, V.is_bot v).
  Proof.
    reflexivity.
  Qed.
  Lemma refine_node_def : forall q o a ns m, refine_checked q (ANode o a ns) m =
    let qs := V.backward o q (map root ns) in
    (fix children ns qs m bad :=
      match ns, qs with
      | n :: ns, q :: qs =>
        let result := refine_checked q n m in
        children ns qs (fst result) (orb bad (snd result))
      | _, _ => (m, bad)
      end) ns qs m false.
  Proof.
    reflexivity.
  Qed.
  Lemma refine_def : forall q n m,
    refine q n m = fst (refine_checked q n m).
  Proof.
    reflexivity.
  Qed.
  Lemma assume_def : forall g es s, assume g es s =
    match s with
    | Unreached => Unreached
    | Reached m =>
      let ns := map (annotate m) es in
      let qs := V.guard g (map root ns) in
      let result := fold_left (fun result nq =>
        let next := refine_checked (snd nq) (fst nq) (fst result) in
        (fst next, orb (snd result) (snd next))) (combine ns qs) (m, false) in
      if snd result then Unreached else Reached (fst result)
    end.
  Proof.
    reflexivity.
  Qed.
  Lemma rsize_def : forall s g es, rsize s g es = assume_size s g es.
  Proof.
    reflexivity.
  Qed.
  Fixpoint ann_work (n : ann L.op X.t V.t) : nat :=
    match n with
    | ALeaf x _ => X.bits x + 1
    | ANode o _ ns => fold_right Nat.add 0 (map ann_work ns) + V.work o (map root ns) + 1
    end.
  Fixpoint ann_size (n : ann L.op X.t V.t) : nat :=
    match n with
    | ALeaf _ _ => 1
    | ANode _ _ ns => S (fold_right Nat.add 0 (map ann_size ns))
    end.
  Definition k_env_refine : N := env_refine_factor.
  (** Annotation records the work of its term. *)
  Lemma ann_work_def : forall m e, ann_work (annotate m e) = tcost m e.
  Proof.
    fix IH 2. intros m [x|o es]; [reflexivity|].
    cbn [annotate ann_work tcost]. rewrite !map_map.
    assert (Hkids : map (fun e => ann_work (annotate m e)) es = map (tcost m) es).
    { induction es as [|e es IHes]; cbn; [reflexivity|].
      rewrite (IH m e), IHes. reflexivity. }
    now rewrite Hkids.
  Qed.
  (** Annotation keeps the shape of its term. *)
  Lemma ann_size_def : forall m e, ann_size (annotate m e) = tsize e.
  Proof.
    fix IH 2. intros m [x|o es]; [reflexivity|].
    cbn [annotate ann_size tsize]. rewrite map_map.
    assert (Hkids : map (fun e => ann_size (annotate m e)) es = map tsize es).
    { induction es as [|e es IHes]; cbn; [reflexivity|].
      rewrite (IH m e), IHes. reflexivity. }
    now rewrite Hkids.
  Qed.
  (** The extracted child traversal matches the local checked-refinement loop. *)
  Fixpoint refine_children (ns : list (ann L.op X.t V.t)) (qs : list V.t)
      (m : M.t V.t) (bad : bool) :=
    match ns, qs with
    | n :: ns, q :: qs =>
      let result := refine_checked q n m in
      refine_children ns qs (fst result) (orb bad (snd result))
    | _, _ => (m, bad)
    end.
  TimeFun refine_children.
  (** Child refinement records the maximum request charge along its changing map. *)
  Fixpoint refine_children_size ns qs m :=
    match ns, qs with
    | n :: ns, q :: qs => Nat.max (refine_size q n m)
      (refine_children_size ns qs (refine q n m))
    | _, _ => 0 end.

  (** Cached child work covers the traversal length. *)
  Lemma ann_work_lengths : forall ns,
    length ns <= fold_right Nat.add 0 (map ann_work ns).
  Proof.
    intro ns. induction ns as [|n ns IH]; cbn [length map fold_right]; [lia|].
    destruct n; cbn [ann_work]; lia.
  Qed.

  (** Child clocks share the largest request charge encountered along the traversal. *)
  Lemma refine_children_time_bound : forall ns,
    list_all _ (fun n => forall q m,
      (T_refine_checked q n m + 6 <= env_refine_factor *
        N.of_nat (ann_work n + ann_size n * (refine_size q n m + 1)))%N) ns ->
    forall qs m bad,
    (T_refine_children ns qs m bad + 2 * N.of_nat (length ns) <=
      env_refine_factor * N.of_nat
        (fold_right Nat.add 0%nat (map ann_work ns) +
          fold_right Nat.add 0%nat (map ann_size ns) *
            (refine_children_size ns qs m + 1)) + 1)%N.
  Proof.
    intros ns Hns. induction Hns as [|n Hn ns Hns IH]; intros qs m bad.
    - change (1 + 2 * 0 <= env_refine_factor * 0 + 1)%N. nia.
    - destruct qs as [|q qs].
      + pose proof (ann_work_lengths (n :: ns)) as Hlen.
        change (T_refine_children (n :: ns) [] m bad) with 1%N.
        cbn [refine_children_size].
        assert (HlenN : (N.of_nat (length (n :: ns)) <=
          N.of_nat (fold_right Nat.add 0%nat (map ann_work (n :: ns))))%N) by lia.
        unfold env_refine_factor. repeat rewrite Nat2N.inj_add. nia.
      + specialize (Hn q m).
        specialize (IH qs (refine q n m) (orb bad (snd (refine_checked q n m)))).
        time_unfold T_refine_children.
        unfold Datatypes.T_fst, Datatypes.T_snd, Datatypes.T_orb. cbn beta zeta.
        cbn [refine_children_size length map fold_right].
        change (fst (refine_checked q n m)) with (refine q n m).
        autorewrite with env_time_nat.
        autorewrite with env_time_nat in Hn.
        autorewrite with env_time_nat in IH.
        pose proof (N.le_max_l (N.of_nat (refine_size q n m))
          (N.of_nat (refine_children_size ns qs (refine q n m)))) as Hleft.
        pose proof (N.le_max_r (N.of_nat (refine_size q n m))
          (N.of_nat (refine_children_size ns qs (refine q n m)))) as Hright.
        change (N.of_nat 1) with 1%N in Hn, IH |- *.
        nia.
  Qed.

  (** Each checked refinement reserves six units for its parent traversal. *)
  Lemma refine_time_reserve : forall q n m,
    (T_refine_checked q n m + 6 <= env_refine_factor *
      N.of_nat (ann_work n + ann_size n * (refine_size q n m + 1)))%N.
  Proof.
    intros q n. revert q. induction n as [x a|o a ns IH]; intros q m.
    - pose proof (M.T_get_le V.t x m) as Hget.
      pose proof (M.T_set_le V.t x (V.meet (read m x) q) m) as Hset.
      pose proof (V.T_meet_le (read m x) q) as Hmeet.
      pose proof (V.T_is_bot_le (V.meet (read m x) q)) as Hbot.
      pose proof (V.meet_size (read m x) q) as Hsize.
      unfold T_refine_checked at 1. fold T_refine_checked.
      cbn [ann_work ann_size refine_size]. unfold T_read. cbn beta zeta.
      unfold env_refine_factor.
      autorewrite with env_time_nat in Hget, Hset, Hmeet, Hbot, Hsize |- *.
      pose proof (N.le_max_l (N.of_nat (V.size q))
        (N.of_nat (V.size (read m x)))) as Hleft.
      pose proof (N.le_max_r (N.of_nat (V.size q))
        (N.of_nat (V.size (read m x)))) as Hright.
      change (N.of_nat 1) with 1%N in Hget, Hset, Hmeet, Hbot, Hsize |- *.
      nia.
    - pose proof (refine_children_time_bound ns IH
        (V.backward o q (map root ns)) m false) as Hchildren.
      pose proof (V.T_backward_le o q (map root ns)) as Hback.
      change (1 + (ListDef.T_map root T_root ns + V.T_backward o q (map root ns) +
        T_refine_children ns (V.backward o q (map root ns)) m false) + 6 <=
        env_refine_factor * N.of_nat
          (ann_work (ANode o a ns) + ann_size (ANode o a ns) *
            (refine_size q (ANode o a ns) m + 1)))%N.
      rewrite time_roots.
      cbn [ann_work ann_size refine_size]. fold refine_children_size.
      autorewrite with env_time_nat.
      autorewrite with env_time_nat in Hchildren.
      autorewrite with env_time_nat in Hback.
      pose proof (N.le_max_l (N.of_nat (V.size q))
        (N.of_nat (refine_children_size ns (V.backward o q (map root ns)) m))) as Hleft.
      pose proof (N.le_max_r (N.of_nat (V.size q))
        (N.of_nat (refine_children_size ns (V.backward o q (map root ns)) m))) as Hright.
      change (N.of_nat 1) with 1%N in Hchildren, Hback |- *.
      unfold env_refine_factor in *. nia.
  Qed.

  (** Checked refinement charges cached transfers, leaf lookups and the requests it meets. *)
  Lemma T_refine_checked_le : forall q n m,
    (T_refine_checked q n m <= k_env_refine *
      N.of_nat (ann_work n + ann_size n * (refine_size q n m + 1)))%N.
  Proof.
    intros q n m. pose proof (refine_time_reserve q n m) as Htime.
    unfold k_env_refine. lia.
  Qed.
  (** One guard request refines the current map and accumulates bottom recognition. *)
  Definition assume_step (result : M.t V.t * bool) (nq : ann L.op X.t V.t * V.t) :=
    let next := refine_checked (snd nq) (fst nq) (fst result) in
    (fst next, orb (snd result) (snd next)).
  TimeFun assume_step.
  (** Sequential guard requests record their largest encountered refinement charge. *)
  Fixpoint assume_children_size (nqs : list (ann L.op X.t V.t * V.t)) m :=
    match nqs with
    | [] => 0
    | (n, q) :: nqs => Nat.max (refine_size q n m)
      (assume_children_size nqs (refine q n m))
    end.

  (** The maximum accumulator records the same peak as the recursive request traversal. *)
  Lemma assume_size_fold : forall nqs m acc,
    fst (fold_left (fun acc nq =>
      (Nat.max (fst acc) (refine_size (snd nq) (fst nq) (snd acc)),
        refine (snd nq) (fst nq) (snd acc))) nqs (acc, m)) =
    Nat.max acc (assume_children_size nqs m).
  Proof.
    intro nqs. induction nqs as [|[n q] nqs IH]; intros m acc.
    - cbn. lia.
    - cbn [fold_left fst snd assume_children_size]. rewrite IH. lia.
  Qed.

  (** Pairing requests cannot increase the charge of the original child list. *)
  Lemma combine_charge : forall (f : ann L.op X.t V.t -> nat) ns (qs : list V.t),
    fold_right Nat.add 0 (map (fun nq => f (fst nq)) (combine ns qs)) <=
    fold_right Nat.add 0 (map f ns).
  Proof.
    intros f ns. induction ns as [|n ns IH]; intros [|q qs];
      cbn [combine map fold_right fst]; try lia.
    specialize (IH qs). lia.
  Qed.

  (** Guard-request traversal pays for checked refinement and its constant callback overhead. *)
  Lemma assume_children_time_bound : forall nqs m bad,
    (List.T_fold_left assume_step T_assume_step nqs (m, bad) <=
      (env_refine_factor + 9) * N.of_nat
        (fold_right Nat.add 0%nat (map (fun nq => ann_work (fst nq)) nqs) +
          fold_right Nat.add 0%nat (map (fun nq => ann_size (fst nq)) nqs) *
            (assume_children_size nqs m + 1)) + 1)%N.
  Proof.
    intro nqs. induction nqs as [|[n q] nqs IH]; intros m bad.
    - change (1 <= (env_refine_factor + 9) * 0 + 1)%N. nia.
    - pose proof (refine_time_reserve q n m) as Hrefine.
      specialize (IH (refine q n m) (orb bad (snd (refine_checked q n m)))).
      unfold List.T_fold_left at 1. fold (@List.T_fold_left _ _ assume_step T_assume_step).
      cbn [assume_step T_assume_step fst snd map fold_right assume_children_size].
      unfold Datatypes.T_snd, Datatypes.T_fst, Datatypes.T_orb. cbn beta zeta.
      change (fst (refine_checked q n m)) with (refine q n m).
      autorewrite with env_time_nat in Hrefine, IH |- *.
      pose proof (N.le_max_l (N.of_nat (refine_size q n m))
        (N.of_nat (assume_children_size nqs (refine q n m)))) as Hleft.
      pose proof (N.le_max_r (N.of_nat (refine_size q n m))
        (N.of_nat (assume_children_size nqs (refine q n m)))) as Hright.
      assert (Hwork : (1 <= N.of_nat (ann_work n))%N).
      { destruct n; cbn [ann_work]; lia. }
      change (N.of_nat 1) with 1%N in Hrefine, IH |- *.
      change (T_assume_step (m, bad) (n, q)) with
        (1 + (3 + T_refine_checked q n m + 4))%N.
      change (assume_step (m, bad) (n, q)) with
        (refine q n m, orb bad (snd (refine_checked q n m))).
      change (N.succ (N.of_nat 0)) with 1%N in *.
      nia.
  Qed.
  (** Annotated guard children share the original terms' work and shape charges. *)
  Lemma assume_children_annotations : forall m es qs bad,
    (List.T_fold_left assume_step T_assume_step
      (combine (map (annotate m) es) qs) (m, bad) <=
      (env_refine_factor + 9) * N.of_nat
        (fold_right Nat.add 0%nat (map (tcost m) es) +
          fold_right Nat.add 0%nat (map tsize es) *
            (assume_children_size (combine (map (annotate m) es) qs) m + 1)) + 1)%N.
  Proof.
    intros m es qs bad.
    pose proof (assume_children_time_bound (combine (map (annotate m) es) qs) m bad)
      as Hfold.
    assert (Hwork : fold_right Nat.add 0
      (map (fun nq => ann_work (fst nq)) (combine (map (annotate m) es) qs)) <=
      fold_right Nat.add 0 (map (tcost m) es)).
    { eapply Nat.le_trans; [apply combine_charge|]. rewrite map_map.
      apply rank_sum_mono. intros e _. rewrite ann_work_def. lia. }
    assert (Hsize : fold_right Nat.add 0
      (map (fun nq => ann_size (fst nq)) (combine (map (annotate m) es) qs)) <=
      fold_right Nat.add 0 (map tsize es)).
    { eapply Nat.le_trans; [apply combine_charge|]. rewrite map_map.
      apply rank_sum_mono. intros e _. rewrite ann_size_def. lia. }
    autorewrite with env_time_nat in Hfold |- *.
    eapply N.le_trans; [exact Hfold|].
    apply N.add_le_mono_r. apply N.mul_le_mono_l.
    apply N.add_le_mono; [lia|]. apply N.mul_le_mono_r. lia.
  Qed.
  (** Forward, guard and refinement bounds fit the selected state coefficient. *)
  Lemma assume_time_arithmetic :
    forall (k cm cv work guard charge len annot child_time guard_time combine_time : N),
    (annot <= (cm + cv + 8) * work -> len <= work ->
      child_time <= (k + 9) * (work + charge) + 1 ->
      guard_time <= cv * (guard + 1) -> combine_time <= len + 1 ->
      1 + (annot + len + 1 + (2 * len + 1 + guard_time +
        (combine_time + child_time + 2))) <=
      (k + cm + 2 * cv + 40) * (work + guard + charge + 1))%N.
  Proof.
    intros k cm cv work guard charge len annot child_time guard_time combine_time
      Hann Hlen Hchildren Hguard Hcombine.
    assert (Htotal : (1 + (annot + len + 1 + (2 * len + 1 + guard_time +
        (combine_time + child_time + 2))) <=
      (k + cm + cv + 21) * work + cv * guard + (k + 9) * charge + cv + 7)%N) by nia.
    eapply N.le_trans; [exact Htotal|].
    clear Htotal Hann Hlen Hchildren Hguard Hcombine.
    assert (Hwork : ((k + cm + cv + 21) * work <=
      (k + cm + 2 * cv + 40) * work)%N) by (apply N.mul_le_mono_r; lia).
    assert (Hguard : (cv * guard <=
      (k + cm + 2 * cv + 40) * guard)%N) by (apply N.mul_le_mono_r; lia).
    assert (Hcharge : ((k + 9) * charge <=
      (k + cm + 2 * cv + 40) * charge)%N) by (apply N.mul_le_mono_r; lia).
    nia.
  Qed.

  (** A reached assumption pays for one cached forward pass and one refinement traversal. *)
  Lemma assume_time_reached : forall g es m,
    (T_assume g es (Reached m) <=
      (env_refine_factor + M.c_map + 2 * V.c_val + 40) * N.of_nat
      (fold_right Nat.add 0%nat (map (tcost m) es) +
        V.gwork g (roots (Reached m) es) +
        fold_right Nat.add 0%nat (map tsize es) * (rsize (Reached m) g es + 1) + 1))%N.
  Proof.
    intros g es m.
    set (ns := map (annotate m) es).
    set (qs := V.guard g (map root ns)).
    pose proof (assume_children_annotations m es qs false) as Hfold. fold ns in Hfold.
    assert (Hmap : (fold_right N.add 0 (map (T_annotate m) es) <=
      (M.c_map + V.c_val + 8) *
      N.of_nat (fold_right Nat.add 0%nat (map (tcost m) es)))%N).
    { apply time_sum_bound. intros e _. pose proof (annotate_time_reserve m e). lia. }
    pose proof (tcost_lengths m es) as Hlength.
    assert (HlengthN : (N.of_nat (length es) <=
      N.of_nat (fold_right Nat.add 0%nat (map (tcost m) es)))%N) by lia.
    pose proof (V.T_guard_le g (map root ns)) as Hguard.
    pose proof (@List.T_combine_le _ _ ns qs) as Hcombine.
    assert (Hroots : map root ns = roots (Reached m) es).
    { unfold ns, roots. rewrite map_map. reflexivity. }
    rewrite Hroots in Hguard.
    assert (Hnslen : length ns = length es) by (unfold ns; apply length_map).
    rewrite Hnslen in Hcombine.
    unfold T_assume. cbn beta iota zeta. fold ns qs.
    fold assume_step T_assume_step.
    rewrite time_map_sum, time_roots, Hnslen, Hroots.
    change (fun e : term L.op X.t => T_annotate m e) with (T_annotate m).
    unfold rsize, assume_size. fold ns qs. rewrite assume_size_fold.
    cbn [Nat.max].
    set (result := fold_left assume_step (combine ns qs) (m, false)).
    unfold Datatypes.T_snd, Datatypes.T_fst. cbn beta zeta.
    autorewrite with env_time_nat in Hfold, Hguard |- *.
    change (N.succ (N.of_nat 0)) with 1%N in Hfold, Hguard |- *.
    clear Hlength Hroots Hnslen.
    remember (N.of_nat (fold_right Nat.add 0%nat (map tsize es)) *
      (N.of_nat (assume_children_size (combine ns qs) m) + 1))%N as charge
      eqn:Hcharge in *. clear Hcharge.
    eapply N.le_trans.
    2: { eapply assume_time_arithmetic; eassumption. }
    apply N.add_le_mono_l. apply N.add_le_mono_l.
    apply N.add_le_mono_l. apply N.add_le_mono_l.
    destruct (snd result); lia.
  Qed.

  (** Reached assumptions fit the environment constant after composing their traversals. *)
  Lemma T_assume_plan_le : forall g es m,
    (T_assume g es (Reached m) <= c_env * N.of_nat
      (fold_right Nat.add 0%nat (map (tcost m) es) +
        V.gwork g (roots (Reached m) es) +
        fold_right Nat.add 0%nat (map tsize es) * (rsize (Reached m) g es + 1) + 1))%N.
  Proof.
    intros g es m. pose proof (assume_time_reached g es m) as Htime.
    eapply N.le_trans; [exact Htime|]. apply N.mul_le_mono_r.
    unfold c_env, c_state. nia.
  Qed.

  (** Assumption time is bounded for reached and unreachable environments. *)
  Lemma T_assume_env_le : forall g es s,
    (T_assume g es s <= c_env * N.of_nat
      (fold_right Nat.add 0%nat (map (tcost_s s) es) + V.gwork g (roots s es) +
       fold_right Nat.add 0%nat (map tsize es) * (rsize s g es + 1) + 1))%N.
  Proof.
    intros g es [|m].
    - change (T_assume g es Unreached) with 1%N.
      pose proof state_annotation_factor as Hfactor. unfold c_env.
      rewrite Nat2N.inj_add. change (N.of_nat 1) with 1%N. nia.
    - exact (T_assume_plan_le g es m).
  Qed.

  (** The state contract adds one unit to the stronger environment work bound. *)
  Lemma T_assume_le : forall g es s,
    (T_assume g es s <= c_state * N.of_nat (assume_work g es s + 1))%N.
  Proof.
    intros g es s. pose proof (T_assume_env_le g es s) as Htime.
    change (T_assume g es s <= c_state * N.of_nat (assume_work g es s))%N in Htime.
    eapply N.le_trans; [exact Htime|]. apply N.mul_le_mono_l.
    rewrite Nat2N.inj_add. lia.
  Qed.

  (** Assumption is linear in its annotation, guard and refinement work. *)
  Lemma assume_complexity : bigO (X := L.guard * list (term L.op X.t) * t) (fun _ => True)
    (fun '(gd, es, s) => N.of_nat (assume_work gd es s))
    (fun '(gd, es, s) => T_assume gd es s).
  Proof.
    eapply bigO_intro with (c := c_state). intros [[gd es] s] _.
    change (T_assume gd es s <= c_state * N.of_nat (assume_work gd es s) + c_state)%N.
    pose proof (T_assume_le gd es s) as Hbound.
    rewrite Nat2N.inj_add in Hbound. nia.
  Qed.

  Definition models (m : M.t V.t) (st : X.t -> L.val) : Prop :=
    forall x, V.gamma (read m x) (st x).
  Fixpoint ann_models (st : X.t -> L.val) (n : ann L.op X.t V.t)
      (e : term L.op X.t) {struct n} : Prop :=
    (forall c, eval_term L.eval st e = Some c -> V.gamma (root n) c) /\
    match n, e with
    | ALeaf x _, Leaf y => x = y
    | ANode o _ ns, Node p es => o = p /\
      (fix children (ns : list (ann L.op X.t V.t)) (es : list (term L.op X.t)) :=
        match ns, es with
        | nil, nil => True
        | n :: ns, e :: es => ann_models st n e /\ children ns es
        | _, _ => False
        end) ns es
    | _, _ => False
    end.
  Lemma annotate_sound : forall m st e c,
    models m st -> eval_term L.eval st e = Some c ->
    ann_models st (annotate m e) e /\ V.gamma (root (annotate m e)) c.
  Proof.
    intros m st e c Hmodel Heval. split.
    - change (ann_covers st (annotate m e) e). now apply annotate_covers.
    - eapply annotate_value_sound; eassumption.
  Qed.
  Lemma refine_sound : forall m st e n q c,
    models m st -> ann_models st n e -> eval_term L.eval st e = Some c ->
    V.gamma q c -> models (refine q n m) st.
  Proof.
    intros m st e n q c Hmodel Hcover Heval Hq.
    change (ann_covers st n e) in Hcover.
    exact (proj1 (refine_checked_covers n m st e q c Hmodel Hcover Heval Hq)).
  Qed.
  Lemma refine_lower : forall q n m x,
    V.leb (read (refine q n m) x) (read m x) = true.
  Proof.
    exact refine_pointwise_lower.
  Qed.
  Lemma join_models : forall a b st,
    models a st \/ models b st -> models (join_map a b) st.
  Proof.
    intros a b st [Hmodel|Hmodel] x; specialize (Hmodel x).
    all: unfold read in Hmodel |- *; unfold join_map;
      rewrite M.get_merge by reflexivity.
    all: destruct (M.get x a) as [va|], (M.get x b) as [vb|];
      cbn in Hmodel |- *; try apply V.gamma_top.
    all: destruct (V.is_bot (V.join va vb)); [apply V.gamma_top|].
    - eapply V.gamma_mono; [apply V.join_ub_l|exact Hmodel].
    - eapply V.gamma_mono; [apply V.join_ub_r|exact Hmodel].
  Qed.
  (** Injective key encoding preserves uniqueness of a key list. *)
  Lemma env_encode_nodup : forall xs,
    NoDup xs -> NoDup (map X.encode xs).
  Proof.
    intros xs Hnd. induction Hnd; cbn; constructor; [|assumption].
    intros Hin. apply in_map_iff in Hin. destruct Hin as [y [Heq Hy]].
    apply X.encode_inj in Heq. subst y. contradiction.
  Qed.

  (** Consistent map codes enumerate the encodings of their stored keys. *)
  Lemma env_codes_elements : forall (m : M.t V.t), M.wf m ->
    Permutation (M.codes m) (map (fun xa => X.encode (fst xa)) (M.elements m)).
  Proof.
    intros m Hwf. apply NoDup_Permutation.
    - apply M.codes_nodup.
    - rewrite <- map_map. apply env_encode_nodup. now apply M.elements_nodup.
    - intro code. rewrite M.codes_spec, in_map_iff. split.
      + intros Hbound. destruct (M.find code m) as [a|] eqn:Hfind; [|contradiction].
        destruct (M.wf_find V.t m code a Hwf Hfind) as [x Hcode].
        exists (x, a). split; [exact Hcode|].
        apply (proj2 (M.elements_spec V.t m x a Hwf)).
        rewrite M.get_find, Hcode. exact Hfind.
      + intros [[x a] [Hcode Hin]]. cbn in Hcode.
        rewrite <- Hcode, <- M.get_find.
        rewrite (proj1 (M.elements_spec V.t m x a Hwf) Hin). discriminate.
  Qed.

  (** Consistent maps sum stored-value measures equally by codes or by bindings. *)
  Lemma env_codes_sum : forall (m : M.t V.t) (f : V.t -> nat), M.wf m ->
    fold_right Nat.add 0 (map (fun code =>
      match M.find code m with Some a => f a | None => 0 end) (M.codes m)) =
    fold_right Nat.add 0 (map (fun xa => f (snd xa)) (M.elements m)).
  Proof.
    intros m f Hwf.
    rewrite (rank_sum_permutation _ _ _ (env_codes_elements m Hwf)), map_map.
    f_equal. apply map_ext_in. intros [x a] Hin. cbn.
    rewrite <- M.get_find, (proj1 (M.elements_spec V.t m x a Hwf) Hin). reflexivity.
  Qed.

  Lemma wrank_env : forall p m, M.wf m -> wrank p (Reached m) =
    fold_right Nat.add 0
      (map (fun kv => V.wrank p (snd kv)) (M.elements m)).
  Proof.
    intros p m Hwf. unfold wrank. now apply env_codes_sum.
  Qed.
  Lemma is_bot_env_def : forall m, is_bot (Reached m) = M.existsb V.is_bot m.
  Proof.
    reflexivity.
  Qed.
  Lemma leb_env_def : forall a b, leb a b = orb (is_bot a)
    (andb (negb (is_bot b)) (match a, b with
      | Reached ma, Reached mb => M.forall2b (fun x y =>
          V.leb (match x with Some v => v | None => V.top end)
                (match y with Some v => v | None => V.top end)) ma mb
      | _, _ => false end)).
  Proof.
    intros a b. rewrite leb_agree. unfold leb_ref.
    destruct a as [|a], b as [|b]; try reflexivity.
    assert (Hcallback : forall x y, option_leb x y =
      V.leb (match x with Some v => v | None => V.top end)
        (match y with Some v => v | None => V.top end)).
    { intros [x|] [y|]; cbn [option_leb]; try reflexivity;
      symmetry; apply V.top_greatest. }
    assert (Hiff : M.forall2b option_leb a b = true <->
      M.forall2b (fun x y =>
        V.leb (match x with Some v => v | None => V.top end)
          (match y with Some v => v | None => V.top end)) a b = true).
    { rewrite M.forall2b_spec by reflexivity.
      rewrite M.forall2b_spec by apply V.leb_refl.
      split; intros H c; [rewrite <- Hcallback|rewrite Hcallback]; apply H. }
    destruct (M.forall2b option_leb a b) eqn:Hleft;
      destruct (M.forall2b (fun x y =>
        V.leb (match x with Some v => v | None => V.top end)
          (match y with Some v => v | None => V.top end)) a b) eqn:Hright;
      try reflexivity; exfalso; intuition discriminate.
  Qed.
  Lemma tcost_leaf : forall m x, tcost m (Leaf x) = X.bits x + 1.
  Proof.
    reflexivity.
  Qed.
  Lemma tcost_node : forall m o es, tcost m (Node o es) =
    fold_right Nat.add 0 (map (tcost m) es) +
    V.work o (map (fun e => root (annotate m e)) es) + 1.
  Proof.
    reflexivity.
  Qed.
  (** Environment size agrees with its raw stored-value measure. *)
  Lemma size_def : forall s, size s = esize s.
  Proof.
    reflexivity.
  Qed.
  (** Environment widening parameters use the value-domain parameter size. *)
  Lemma wsize_def : forall p, wsize p = V.wsize p.
  Proof.
    reflexivity.
  Qed.
  (** Assignment work charges annotation and the current environment. *)
  Lemma assign_work_def : forall x e s, assign_work x e s =
    match s with
    | Unreached => tsize e + X.bits x + 1
    | Reached m => tcost m e + esize s + X.bits x + 1
    end.
  Proof.
    reflexivity.
  Qed.
  (** Havoc work charges the environment and the selected key. *)
  Lemma havoc_work_def : forall x s, havoc_work x s = esize s + X.bits x + 1.
  Proof.
    reflexivity.
  Qed.
  (** Evaluation work charges its cached forward pass. *)
  Lemma eval_work_def : forall e s, eval_work e s =
    match s with Unreached => tsize e + 1 | Reached m => tcost m e + 1 end.
  Proof.
    reflexivity.
  Qed.
  (** Assumption work charges the forward pass, guard and checked refinement. *)
  Lemma assume_work_def : forall g es s, assume_work g es s =
    fold_right Nat.add 0 (map (tcost_s s) es) + V.gwork g (roots s es) +
      fold_right Nat.add 0 (map tsize es) * (rsize s g es + 1) + 1.
  Proof.
    reflexivity.
  Qed.
End EnvT.
