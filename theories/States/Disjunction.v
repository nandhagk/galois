(** * Bounded disjunctive states

    Lists of alternatives represent a union and compact when the capacity is exceeded.
    For example, cap one joins two alternatives into one state.
    Builds on: DisjunctionSig, StateSig and the lattice interfaces. *)

From Stdlib Require Import List NArith Arith Bool Lia.
From Argent Require Import Time Tactics Std.
From Galois.Base Require Import KeySig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.States Require Import StateSig DisjunctionSig.
Import List.ListNotations.
Local Open Scope nat_scope.

Module Specif.
  TimeFun proj1_sig.
End Specif.

Module Nat.
  TimeFun Nat.pred.
End Nat.

Lemma replace_first_length {A} (is_bot : A -> bool) (f : A -> A) xs :
  length (replace_first is_bot f xs) = length xs.
Proof.
  induction xs as [|x rest IH]; simpl; auto.
  destruct (is_bot x); simpl; now rewrite ?IH.
Qed.

Module StateDisjunctionCode (X : KEY_OPS) (L : LANG_OPS) (V : VALUE_DOMAIN_OPS L)
    (S : STATE_DOMAIN_OPS X L V) (C : CAP) (P : SharedDisjunction.DISJUNCTION_OPS S C)
    <: DISJUNCTION_OPS X L V S C P.
  Definition t := P.t.
  Definition leb := P.leb.
  Definition bot := P.bot.
  Definition is_bot := P.is_bot.
  Definition join := P.join.
  Definition top := P.clip [S.top].
  Definition collapse (xs : list S.t) : S.t :=
    match xs with [] => S.bot | x :: rest => fold_left S.join rest x end.
  Fixpoint compact_tail (n : nat) (xs : list S.t) : list S.t :=
    match n, xs with
    | S m, x :: rest => x :: compact_tail m rest
    | _, _ => [collapse xs]
    end.
  Definition compact (n : nat) (xs : list S.t) : list S.t :=
    if Nat.eqb n C.k then proj1_sig (P.clip xs)
    else if Nat.leb (length xs) n then xs else compact_tail (Nat.pred n) xs.
  Definition meet (a b : t) : t :=
    P.clip (flat_map (fun x => map (S.meet x) (proj1_sig b)) (proj1_sig a)).
  Definition wparam := S.wparam.
  Definition widen (p : wparam) (a b : t) : t.
  Proof.
    destruct a as [old Hbound].
    destruct (leb b (exist _ old Hbound)) eqn:Hstable.
    - exact (exist _ old Hbound).
    - destruct (is_bot (exist _ old Hbound)) eqn:Hempty.
      + exact b.
      + destruct (forallb S.is_bot old) eqn:Hbottom.
        * exact (P.clip [S.top]).
        * refine (exist _ (replace_first S.is_bot
          (fun x => S.widen p x (collapse (x :: uncovered S.leb old (proj1_sig b)))) old) _).
          now rewrite replace_first_length.
  Defined.
  Definition narrow (a _ : t) := a.

  Definition map_bounded (f : S.t -> S.t) (d : t) : t.
  Proof.
    destruct d as [xs Hbound].
    refine (exist _ (map f xs) _).
    now rewrite length_map.
  Defined.

  Definition assign x e (d : t) := map_bounded (S.assign x e) d.
  Definition havoc x (d : t) := map_bounded (S.havoc x) d.
  Definition assume g es (d : t) := map_bounded (S.assume g es) d.
  Definition eval e (d : t) := fold_left (fun a s => V.join a (S.eval e s)) (proj1_sig d) V.bot.
End StateDisjunctionCode.

Module StateDisjunction (X : KEY) (L : LANG) (V : VALUE_DOMAIN L)
    (S : STATE_DOMAIN X L V) (C : POS_CAP) (P : SharedDisjunction.DISJUNCTION S C)
    <: DISJUNCTION X L V S C P.
  Include StateDisjunctionCode X L V S C P.
  Definition gamma (d : t) (st : X.t -> L.val) : Prop :=
    Exists (fun s => S.gamma s st) (proj1_sig d).
  Definition wrank (p : wparam) (d : t) : nat :=
    fold_right Nat.add 0 (map (S.wrank p) (proj1_sig d)) +
      if forallb S.is_bot (proj1_sig d) then 1 + S.wrank p S.top else 0.

  (** Every fold result covers its initial accumulator. *)
  Lemma fold_join_start : forall xs a, S.leb a (fold_left S.join xs a) = true.
  Proof.
    induction xs as [|x xs IH]; intro a; cbn [fold_left].
    - apply S.leb_refl.
    - eapply S.leb_trans; [apply S.join_ub_l | apply IH].
  Qed.

  (** Every member of a fold's input is below its result. *)
  Lemma fold_join_member : forall xs a x, In x xs ->
    S.leb x (fold_left S.join xs a) = true.
  Proof.
    induction xs as [|y xs IH]; intros a x Hin; cbn in Hin; [contradiction |].
    cbn [fold_left]; destruct Hin as [<- | Hin].
    - eapply S.leb_trans; [apply S.join_ub_r | apply fold_join_start].
    - apply IH; exact Hin.
  Qed.

  (** Collapse covers every raw alternative, including a singleton. *)
  Lemma collapse_upper : forall xs x, In x xs -> S.leb x (collapse xs) = true.
  Proof.
    intros [|a xs] x Hin; cbn [collapse] in *; [contradiction |].
    destruct Hin as [<- | Hin]; auto using fold_join_start, fold_join_member.
  Qed.

  (** Prefix compaction keeps each input below a returned alternative. *)
  Lemma compact_tail_covers : forall n xs x, In x xs ->
    exists y, In y (compact_tail n xs) /\ S.leb x y = true.
  Proof.
    induction n as [|n IH]; intros xs x Hin.
    - exists (collapse xs); split; [now left | now apply collapse_upper].
    - destruct xs as [|a xs]; [contradiction |].
      cbn [compact_tail]; destruct Hin as [<- | Hin].
      + exists a; split; [now left | apply S.leb_refl].
      + destruct (IH xs x Hin) as [y [Hy Hle]].
        exists y; split; [now right | exact Hle].
  Qed.

  (** A compacted suffix contributes at most one extra alternative. *)
  Lemma compact_tail_length : forall n xs, length (compact_tail n xs) <= n + 1.
  Proof.
    induction n as [|n IH]; intros [|x xs]; cbn [compact_tail length]; try lia.
    specialize (IH xs); lia.
  Qed.

  (** The raw widening equation exposes only the chosen branch's alternatives. *)
  Lemma widen_raw : forall p a b, proj1_sig (widen p a b) =
    if leb b a then proj1_sig a else
    if is_bot a then proj1_sig b else
    if forallb S.is_bot (proj1_sig a) then [S.top] else
    replace_first S.is_bot
      (fun x => S.widen p x (collapse (x :: uncovered S.leb (proj1_sig a) (proj1_sig b))))
      (proj1_sig a).
  Proof.
    intros p [xs Hbound] b; unfold widen; cbn [proj1_sig].
    destruct (leb b (exist _ xs Hbound)); [reflexivity |].
    destruct (is_bot (exist _ xs Hbound)); [reflexivity |].
    destruct (forallb S.is_bot xs); [|reflexivity].
    apply P.clip_small; cbn; exact C.k_pos.
  Qed.

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
    intro a; apply P.leb_spec; intros x Hin; exists S.top; split.
    - unfold top; rewrite P.clip_small; [now left | cbn; exact C.k_pos].
    - apply S.top_greatest.
  Qed.

  (** Replacing an alternative by an upper bound preserves raw coverage. *)
  Lemma replace_first_covers : forall f xs,
    (forall x, In x xs -> S.leb x (f x) = true) ->
    forall x, In x xs ->
    exists y, In y (replace_first S.is_bot f xs) /\ S.leb x y = true.
  Proof.
    intros f xs; induction xs as [|a xs IH]; intros Hupper x Hin; [contradiction |].
    cbn [replace_first]; destruct (S.is_bot a).
    - destruct Hin as [<- | Hin].
      + exists a; split; [now left | apply S.leb_refl].
      + destruct (IH (fun y Hy => Hupper y (or_intror Hy)) x Hin) as [y [Hy Hle]].
        exists y; split; [now right | exact Hle].
    - destruct Hin as [<- | Hin].
      + exists (f a); split; [now left | apply Hupper; now left].
      + exists x; split; [now right | apply S.leb_refl].
  Qed.

  (** A list with a nonbottom alternative contains the selected replacement. *)
  Lemma replace_first_selected : forall f xs, forallb S.is_bot xs = false ->
    exists x, In x xs /\ S.is_bot x = false /\ In (f x) (replace_first S.is_bot f xs).
  Proof.
    intros f xs; induction xs as [|a xs IH]; intro Hnonbottom; [discriminate |].
    cbn [forallb] in Hnonbottom; cbn [replace_first]; destruct (S.is_bot a) eqn:Ha.
    - cbn in Hnonbottom; destruct (IH Hnonbottom) as [x [Hin [Hx Hselected]]].
      exists x; repeat split; auto; now right.
    - exists a; repeat split; auto; now left.
  Qed.

  (** Each candidate is already covered or occurs in the uncovered list. *)
  Lemma candidate_covered_or_new : forall old new y, In y new ->
    (exists x, In x old /\ S.leb y x = true) \/ In y (uncovered S.leb old new).
  Proof.
    intros old new y Hin; destruct (existsb (S.leb y) old) eqn:Hcovered.
    - left; now apply existsb_exists.
    - right; apply filter_In; split; [exact Hin | now rewrite Hcovered].
  Qed.

  (** Widening is above its previous value. *)
  Lemma widen_ub_l : forall p a b, leb a (widen p a b) = true.
  Proof.
    intros p a b; apply P.leb_spec; intros x Hin; rewrite widen_raw.
    destruct (leb b a); [exists x; split; [exact Hin | apply S.leb_refl] |].
    destruct (is_bot a) eqn:Hempty.
    - apply P.is_bot_spec in Hempty; rewrite Hempty in Hin; contradiction.
    - destruct (forallb S.is_bot (proj1_sig a)).
      + exists S.top; split; [now left | apply S.top_greatest].
      + apply replace_first_covers; [intros; apply S.widen_ub_l | exact Hin].
  Qed.
  (** Widening is above its candidate value. *)
  Lemma widen_ub_r : forall p a b, leb b (widen p a b) = true.
  Proof.
    intros p a b; destruct (leb b a) eqn:Hstable.
    - apply P.leb_spec; intros y Hin; rewrite widen_raw, Hstable.
      exact (proj1 (P.leb_spec b a) Hstable y Hin).
    - apply P.leb_spec; intros y Hin; rewrite widen_raw, Hstable.
      destruct (is_bot a); [exists y; split; [exact Hin | apply S.leb_refl] |].
      destruct (forallb S.is_bot (proj1_sig a)) eqn:Hnonbottom.
      + exists S.top; split; [now left | apply S.top_greatest].
      + destruct (candidate_covered_or_new (proj1_sig a) (proj1_sig b) y Hin)
          as [[x [Hx Hle]] | Hnew].
        * destruct (replace_first_covers
            (fun x => S.widen p x (collapse (x :: uncovered S.leb (proj1_sig a)
              (proj1_sig b)))) (proj1_sig a)
            (fun x _ => S.widen_ub_l p x _) x Hx) as [z [Hz Hxz]].
          exists z; split; [exact Hz | eapply S.leb_trans; eassumption].
        * destruct (replace_first_selected
            (fun x => S.widen p x (collapse (x :: uncovered S.leb (proj1_sig a)
              (proj1_sig b)))) (proj1_sig a) Hnonbottom) as [x [Hx [Hbot Hselected]]].
          eexists; split; [exact Hselected |].
          eapply S.leb_trans; [|apply S.widen_ub_r].
          apply collapse_upper; now right.
  Qed.
  (** A candidate below the previous value leaves widening unchanged. *)
  Lemma widen_stable : forall p a b, leb b a = true -> widen p a b = a.
  Proof.
    intros p [xs Hbound] b Hstable; unfold widen; now rewrite Hstable.
  Qed.

  (** A failed coverage scan exhibits a candidate with no covering old alternative. *)
  Lemma uncovered_witness : forall a b, leb b a = false ->
    exists y, In y (uncovered S.leb (proj1_sig a) (proj1_sig b)).
  Proof.
    intros a b Hstrict.
    assert (Hscan : forallb (fun y => existsb (S.leb y) (proj1_sig a))
      (proj1_sig b) = false).
    { destruct (forallb (fun y => existsb (S.leb y) (proj1_sig a))
        (proj1_sig b)) eqn:Hscan; [|reflexivity].
      assert (Hcovered : leb b a = true).
      { apply P.leb_spec; intros y Hin; apply existsb_exists.
        apply forallb_forall with (x := y) in Hscan; assumption. }
      congruence. }
    revert Hscan; generalize (proj1_sig b); clear Hstrict b.
    intros ys; induction ys as [|y ys IH]; intro Hscan; [discriminate |].
    cbn [forallb] in Hscan.
    destruct (existsb (S.leb y) (proj1_sig a)) eqn:Hy.
    - cbn in Hscan; destruct (IH Hscan) as [z Hz].
      exists z; apply filter_In in Hz; apply filter_In; destruct Hz as [Hz Hbad].
      split; [now right | exact Hbad].
    - exists y; apply filter_In; split; [now left | now rewrite Hy].
  Qed.

  (** Joining an uncovered candidate cannot stay below any old alternative. *)
  Lemma collapse_strict : forall old new x,
    In x old -> (exists y, In y (uncovered S.leb old new)) ->
    S.leb (collapse (x :: uncovered S.leb old new)) x = false.
  Proof.
    intros old new x Hx [y Hy]; apply Bool.not_true_is_false; intro Hle.
    pose proof Hy as Hfilter; apply filter_In in Hfilter; destruct Hfilter as [_ Hbad].
    assert (Hcovered : existsb (S.leb y) old = true).
    { apply existsb_exists; exists x; split; [exact Hx |].
      eapply S.leb_trans; [|exact Hle].
      apply collapse_upper; now right. }
    rewrite Hcovered in Hbad; discriminate.
  Qed.

  (** A strict widening result cannot be recognized as bottom. *)
  Lemma strict_widen_nonbottom : forall p x c, S.leb c x = false ->
    S.is_bot (S.widen p x c) = false.
  Proof.
    intros p x c Hstrict; apply Bool.not_true_is_false; intro Hbottom.
    assert (Hle : S.leb c x = true).
    { eapply S.leb_trans with (b := S.widen p x c).
      - apply S.widen_ub_r.
      - apply S.is_bot_least; exact Hbottom. }
    congruence.
  Qed.

  (** Changing the selected nonbottom lowers the sum and keeps a nonbottom alternative. *)
  Lemma replace_first_rank : forall p f xs,
    forallb S.is_bot xs = false ->
    (forall x, In x xs -> S.is_bot x = false ->
      S.wrank p (f x) < S.wrank p x /\ S.is_bot (f x) = false) ->
    fold_right Nat.add 0 (map (S.wrank p) (replace_first S.is_bot f xs)) <
      fold_right Nat.add 0 (map (S.wrank p) xs) /\
    forallb S.is_bot (replace_first S.is_bot f xs) = false.
  Proof.
    intros p f xs; induction xs as [|a xs IH]; intros Hnonbottom Hstep;
      [discriminate |].
    cbn [forallb] in Hnonbottom; cbn [replace_first]; destruct (S.is_bot a) eqn:Ha.
    - cbn in Hnonbottom.
      destruct (IH Hnonbottom (fun x Hx => Hstep x (or_intror Hx))) as [Hrank Hbot].
      cbn [map fold_right forallb]; rewrite Ha, Hbot; split; [lia | reflexivity].
    - destruct (Hstep a (or_introl eq_refl) Ha) as [Hrank Hbot].
      cbn [map fold_right forallb]; rewrite Hbot; split; [lia | reflexivity].
  Qed.

  (** A strict update of a nonempty list rules out a recognized bottom top. *)
  Lemma strict_top_nonbottom : forall a b, is_bot a = false -> leb b a = false ->
    S.is_bot S.top = false.
  Proof.
    intros a b Hnonempty Hstrict; apply Bool.not_true_is_false; intro Htop.
    destruct (proj1_sig a) as [|x xs] eqn:Hxs.
    - assert (Hempty : is_bot a = true) by (apply P.is_bot_spec; exact Hxs).
      congruence.
    - assert (Hcovered : leb b a = true).
      { apply P.leb_spec; intros y Hy; exists x; split; [rewrite Hxs; now left |].
        eapply S.leb_trans; [apply S.top_greatest | now apply S.is_bot_least]. }
      congruence.
  Qed.

  (** An unstable widening from a nonbottom strictly decreases rank. *)
  (* F2-22 replaced the former twoStateDisj aligned-pair rank route with uncovered
     alternatives, and F2-30 supplies the size and widening-unit capabilities it needs. *)
  Lemma wrank_widen : forall p a b, is_bot a = false -> leb b a = false ->
    wrank p (widen p a b) < wrank p a.
  Proof.
    intros p a b Hnonempty Hstrict; unfold wrank.
    rewrite widen_raw, Hstrict, Hnonempty.
    destruct (forallb S.is_bot (proj1_sig a)) eqn:Hbottom.
    - pose proof (strict_top_nonbottom a b Hnonempty Hstrict) as Htop.
      cbn [map fold_right forallb]; rewrite Htop; cbn; lia.
    - pose proof (uncovered_witness a b Hstrict) as Huncovered.
      destruct (replace_first_rank p
        (fun x => S.widen p x (collapse (x :: uncovered S.leb (proj1_sig a)
          (proj1_sig b)))) (proj1_sig a) Hbottom) as [Hrank Hbot].
      + intros x Hx Hnotbot.
        pose proof (collapse_strict (proj1_sig a) (proj1_sig b) x Hx Huncovered) as Hgrowth.
        split; [now apply S.wrank_widen | now apply strict_widen_nonbottom].
      + rewrite Hbot; lia.
  Qed.
  (** Widening from a nonbottom does not increase rank. *)
  Lemma wrank_widen_le : forall p a b, is_bot a = false -> wrank p (widen p a b) <= wrank p a.
  Proof.
    intros p a b Hnonbottom; destruct (leb b a) eqn:Hstable.
    - rewrite widen_stable by exact Hstable; lia.
    - pose proof (wrank_widen p a b Hnonbottom Hstable); lia.
  Qed.
  (** Narrowing stays between an ordered candidate and previous value. *)
  Lemma narrow_between : forall a b, leb b a = true ->
    leb b (narrow a b) = true /\ leb (narrow a b) a = true.
  Proof.
    intros a b Hle; split; [exact Hle | apply leb_refl].
  Qed.

  (** Abstract inclusion entails inclusion of concrete environments. *)
  Lemma gamma_mono : forall a b st, leb a b = true -> gamma a st -> gamma b st.
  Proof.
    intros a b st Hle Hgamma; apply Exists_exists in Hgamma.
    destruct Hgamma as [x [Hin Hx]].
    destruct (proj1 (P.leb_spec a b) Hle x Hin) as [y [Hy Hxy]].
    apply Exists_exists; exists y; split; [exact Hy |].
    eapply S.gamma_mono; eassumption.
  Qed.
  (** Bottom describes no concrete environment. *)
  Lemma gamma_bot : forall st, ~ gamma bot st.
  Proof.
    intros st Hgamma; unfold gamma, bot in Hgamma; rewrite P.bot_raw in Hgamma.
    inversion Hgamma.
  Qed.
  (** Top describes every concrete environment. *)
  Lemma gamma_top : forall st, gamma top st.
  Proof.
    intro st; unfold gamma, top; rewrite P.clip_small.
    - constructor; apply S.gamma_top.
    - cbn; exact C.k_pos.
  Qed.
  (** Assignment contains each successful concrete update. *)
  Lemma assign_sound : forall x e s st c,
    gamma s st -> eval_term L.eval st e = Some c ->
    gamma (assign x e s) (upd X.eqb st x c).
  Proof.
    intros x e [xs Hbound] st c Hgamma Heval; apply Exists_exists in Hgamma.
    destruct Hgamma as [a [Hin Ha]].
    apply Exists_exists; exists (S.assign x e a); split.
    - apply in_map; exact Hin.
    - eapply S.assign_sound; eassumption.
  Qed.
  (** Havoc contains every concrete update of the selected variable. *)
  Lemma havoc_sound : forall x s st c,
    gamma s st -> gamma (havoc x s) (upd X.eqb st x c).
  Proof.
    intros x [xs Hbound] st c Hgamma; apply Exists_exists in Hgamma.
    destruct Hgamma as [a [Hin Ha]].
    apply Exists_exists; exists (S.havoc x a); split.
    - apply in_map; exact Hin.
    - apply S.havoc_sound; exact Ha.
  Qed.
  (** Assuming a true guard retains its concrete environment. *)
  Lemma assume_sound : forall g es s st cs,
    gamma s st -> eval_terms L.eval st es = Some cs -> L.holds g cs ->
    gamma (assume g es s) st.
  Proof.
    intros g es [xs Hbound] st cs Hgamma Heval Hholds; apply Exists_exists in Hgamma.
    destruct Hgamma as [a [Hin Ha]].
    apply Exists_exists; exists (S.assume g es a); split.
    - apply in_map; exact Hin.
    - eapply S.assume_sound; eassumption.
  Qed.
  (** Abstract evaluation describes every successful concrete result. *)
  Lemma eval_sound : forall e s st c,
    gamma s st -> eval_term L.eval st e = Some c -> V.gamma (eval e s) c.
  Proof.
    intros e [xs Hbound] st c Hgamma Heval; unfold eval; cbn [proj1_sig].
    assert (Hfold : forall ys acc, V.gamma acc c \/ Exists (fun s => S.gamma s st) ys ->
      V.gamma (fold_left (fun a s => V.join a (S.eval e s)) ys acc) c).
    { induction ys as [|a ys IH]; intros acc Hcovered; cbn [fold_left].
      - destruct Hcovered as [Hacc | Hnone]; [exact Hacc | inversion Hnone].
      - apply IH; destruct Hcovered as [Hacc | Hsome].
        + left; eapply V.gamma_mono; [apply V.join_ub_l | exact Hacc].
        + inversion Hsome as [a' rest Ha | a' rest Hrest]; subst.
          * left; eapply V.gamma_mono; [apply V.join_ub_r |].
            eapply S.eval_sound; eassumption.
          * right; exact Hrest. }
    apply Hfold; right; exact Hgamma.
  Qed.
  Lemma gamma_alternatives : forall d st,
    gamma d st <-> Exists (fun s => S.gamma s st) (proj1_sig d).
  Proof.
    reflexivity.
  Qed.
  Lemma leb_hoare : forall a b, leb a b =
    forallb (fun x => existsb (S.leb x) (proj1_sig b)) (proj1_sig a).
  Proof.
    intros a b; apply eq_true_iff_eq; rewrite P.leb_spec, forallb_forall.
    split; intros H x Hin; specialize (H x Hin); now apply existsb_exists in H.
  Qed.
  Lemma join_compact : forall a b, join a b = P.clip (proj1_sig a ++ proj1_sig b).
  Proof.
    exact P.join_clip.
  Qed.
  Lemma compact_cap : forall d, compact C.k d = proj1_sig (P.clip d).
  Proof.
    intro d; unfold compact; now rewrite Nat.eqb_refl.
  Qed.
  Lemma compact_covers : forall n d x, In x d ->
    exists y, In y (compact n d) /\ S.leb x y = true.
  Proof.
    intros n d x Hin; unfold compact; destruct (Nat.eqb n C.k).
    - apply P.clip_covers; [exact C.k_pos | exact Hin].
    - destruct (Nat.leb (length d) n).
      + exists x; split; [exact Hin | apply S.leb_refl].
      + now apply compact_tail_covers.
  Qed.
  Lemma compact_len : forall n d, length (compact n d) <= Nat.max n 1.
  Proof.
    intros n d; unfold compact; destruct (Nat.eqb n C.k) eqn:Hcap.
    - apply Nat.eqb_eq in Hcap; subst n.
      pose proof (proj2_sig (P.clip d)) as Hbound; apply Nat.leb_le in Hbound; lia.
    - destruct (Nat.leb (length d) n) eqn:Hlength.
      + apply Nat.leb_le in Hlength; lia.
      + pose proof (compact_tail_length (Nat.pred n) d); destruct n; cbn in *; lia.
  Qed.
  Lemma collapse_covers : forall xs x, In x xs -> S.leb x (collapse xs) = true.
  Proof.
    exact collapse_upper.
  Qed.
End StateDisjunction.

Module StateDisjunctionT (X : KEY_T) (L : LANG_T) (V : VALUE_DOMAIN_T L)
    (S : STATE_DOMAIN_T X L V) (JS : JOIN_SIZE S) (JU : JOIN_UNITS X L V S) (C : POS_CAP)
    (P : SharedDisjunction.DISJUNCTION_T S JS C)
    <: DISJUNCTION_ALL X L V S JS JU C P.
  Module Plain := StateDisjunction X L V S C P.
  Include Plain.
  Definition T_leb : t -> t -> N := P.T_leb.
  Definition T_join : t -> t -> N := P.T_join.
  Definition T_is_bot : t -> N := P.T_is_bot.
  TimeFun top.
  TimeFun collapse.
  TimeFun compact_tail.
  TimeFun compact.
  TimeFun widen.
  TimeFun narrow.
  TimeFun map_bounded.
  TimeFun assign.
  TimeFun havoc.
  TimeFun assume.
  TimeFun eval.
  Definition size : t -> nat := P.size.
  Definition c_lat : N := 1%N. (* STUB *)
  Definition c_state : N := 1%N. (* STUB *)
  Definition c_disjunction : N := 1%N. (* STUB *)
  Definition wsize : wparam -> nat := S.wsize.
  Definition wunits (d : t) : nat :=
    fold_right Nat.add 0%nat (map S.wunits (proj1_sig d)).
  Definition assign_work (x : X.t) (e : term L.op X.t) (d : t) : nat :=
    fold_right Nat.add 0%nat (map (fun s => S.assign_work x e s + 1) (proj1_sig d)).
  Definition havoc_work (x : X.t) (d : t) : nat :=
    fold_right Nat.add 0%nat (map (fun s => S.havoc_work x s + 1) (proj1_sig d)).
  Definition assume_work (g : L.guard) (es : list (term L.op X.t)) (d : t) : nat :=
    fold_right Nat.add 0%nat (map (fun s => S.assume_work g es s + 1) (proj1_sig d)).
  Definition eval_work (e : term L.op X.t) (d : t) : nat :=
    fold_right Nat.add 0%nat (map (fun s =>
      S.eval_work e s + V.size (S.eval e s) + 1) (proj1_sig d)).

  (** Assignment work is the component work of every alternative. *)
  Lemma assign_work_alternatives : forall x e d, assign_work x e d =
    fold_right Nat.add 0%nat (map (fun s => S.assign_work x e s + 1) (proj1_sig d)).
  Proof.
    reflexivity.
  Qed.
  (** Havoc work is the component work of every alternative. *)
  Lemma havoc_work_alternatives : forall x d, havoc_work x d =
    fold_right Nat.add 0%nat (map (fun s => S.havoc_work x s + 1) (proj1_sig d)).
  Proof.
    reflexivity.
  Qed.
  (** Assumption work is the component work of every alternative. *)
  Lemma assume_work_alternatives : forall g es d, assume_work g es d =
    fold_right Nat.add 0%nat (map (fun s => S.assume_work g es s + 1) (proj1_sig d)).
  Proof.
    reflexivity.
  Qed.
  (** Evaluation work is the component work and the value size of every alternative. *)
  Lemma eval_work_alternatives : forall e d, eval_work e d =
    fold_right Nat.add 0%nat (map (fun s =>
      S.eval_work e s + V.size (S.eval e s) + 1) (proj1_sig d)).
  Proof.
    reflexivity.
  Qed.
  Lemma c_lat_pos : (1 <= c_lat)%N.
  Proof. Admitted. (* STUB *)
  Lemma T_leb_le : forall a b,
    (T_leb a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_join_le : forall a b,
    (T_join a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_is_bot_le : forall a,
    (T_is_bot a <= c_lat * N.of_nat (size a + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_widen_le : forall p a b,
    (T_widen p a b <= c_lat * N.of_nat
      ((wunits a + wunits b) * wsize p + (size a + size b + wsize p + 1)))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_narrow_le : forall a b,
    (T_narrow a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_assign_le : forall x e s,
    (T_assign x e s <= c_state * N.of_nat (assign_work x e s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_havoc_le : forall x s,
    (T_havoc x s <= c_state * N.of_nat (havoc_work x s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_assume_le : forall g es s,
    (T_assume g es s <= c_state * N.of_nat (assume_work g es s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_eval_le : forall e s,
    (T_eval e s <= c_state * N.of_nat (eval_work e s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_assign_alternatives : forall x e d,
    (T_assign x e d <= c_disjunction *
      (fold_right N.add 0%N (map (fun s => S.T_assign x e s + 1) (proj1_sig d)) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_havoc_alternatives : forall x d,
    (T_havoc x d <= c_disjunction *
      (fold_right N.add 0%N (map (fun s => S.T_havoc x s + 1) (proj1_sig d)) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_assume_alternatives : forall g es d,
    (T_assume g es d <= c_disjunction *
      (fold_right N.add 0%N (map (fun s => S.T_assume g es s + 1) (proj1_sig d)) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma c_lat_shared : (P.c_lat <= c_lat)%N.
  Proof. Admitted. (* STUB *)
  Lemma wunits_alternatives : forall d,
    wunits d = fold_right Nat.add 0%nat (map S.wunits (proj1_sig d)).
  Proof.
    reflexivity.
  Qed.
  Lemma wsize_component : forall p, wsize p = S.wsize p.
  Proof.
    reflexivity.
  Qed.
  Lemma T_collapse_le : forall xs, length xs <= C.k + 1 ->
    (T_collapse xs <= c_disjunction * N.of_nat
      (fold_right Nat.add 0%nat (map S.size xs) + length xs + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma collapse_size : forall xs, length xs <= C.k + 1 ->
    (N.of_nat (S.size (collapse xs)) <= c_disjunction * N.of_nat
      (fold_right Nat.add 0%nat (map S.size xs) + length xs + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma collapse_wunits : forall xs, length xs <= C.k + 1 ->
    (N.of_nat (S.wunits (collapse xs)) <= c_disjunction * N.of_nat
      (fold_right Nat.add 0%nat (map S.wunits xs) + 1))%N.
  Proof. Admitted. (* STUB *)

  Definition eval_joins (e : term L.op X.t) (xs : list S.t) : N :=
    fst (fold_left (fun acc s =>
      ((fst acc + V.T_join (snd acc) (S.eval e s) + 1)%N,
       V.join (snd acc) (S.eval e s))) xs (0%N, V.bot)).
  Definition k_disjunction : N := 1%N. (* STUB *)
  Lemma F2_widen : forall p a b, proj1_sig (widen p a b) =
    if leb b a then proj1_sig a else
    if is_bot a then proj1_sig b else
    if forallb S.is_bot (proj1_sig a) then [S.top] else
    replace_first S.is_bot
      (fun x => S.widen p x (collapse (x :: uncovered S.leb (proj1_sig a) (proj1_sig b))))
      (proj1_sig a).
  Proof.
    exact widen_raw.
  Qed.
  Lemma F3_rank : forall p d, wrank p d =
    fold_right Nat.add 0%nat (map (S.wrank p) (proj1_sig d)) +
      if forallb S.is_bot (proj1_sig d) then 1 + S.wrank p S.top else 0.
  Proof.
    reflexivity.
  Qed.
  Lemma F4_assign : forall x e d,
    proj1_sig (assign x e d) = map (S.assign x e) (proj1_sig d).
  Proof.
    intros x e [xs Hbound]; reflexivity.
  Qed.
  Lemma F5_havoc : forall x d,
    proj1_sig (havoc x d) = map (S.havoc x) (proj1_sig d).
  Proof.
    intros x [xs Hbound]; reflexivity.
  Qed.
  Lemma F6_assume : forall g es d,
    proj1_sig (assume g es d) = map (S.assume g es) (proj1_sig d).
  Proof.
    intros g es [xs Hbound]; reflexivity.
  Qed.
  Lemma T1_widen : forall p a b,
    (T_widen p a b <= k_disjunction *
      (T_leb b a + T_is_bot a + P.T_clip [S.top] + N.of_nat (length (proj1_sig a) + 1) +
       fold_right N.add 0%N (map S.T_is_bot (proj1_sig a)) +
       fold_right N.add 0%N (map (fun y => fold_right N.add 0%N
         (map (fun x => S.T_leb y x + 1) (proj1_sig a))) (proj1_sig b)) +
       fold_right N.add 0%N (map (fun x =>
         let c := collapse (x :: uncovered S.leb (proj1_sig a) (proj1_sig b)) in
         T_collapse (x :: uncovered S.leb (proj1_sig a) (proj1_sig b)) + S.T_widen p x c)
         (proj1_sig a))))%N.
  Proof. Admitted. (* STUB *)
  (** Evaluation joins the values of the alternatives from bottom. *)
  Lemma F7_eval : forall e d,
    eval e d = fold_left (fun a s => V.join a (S.eval e s)) (proj1_sig d) V.bot.
  Proof.
    reflexivity.
  Qed.
  (** Evaluation charges each alternative's evaluation and the value joins. *)
  Lemma T2_eval : forall e d, (T_eval e d <= k_disjunction *
    (fold_right N.add 0%N (map (fun s => S.T_eval e s + 1) (proj1_sig d)) +
     eval_joins e (proj1_sig d) + 1))%N.
  Proof. Admitted. (* STUB *)
  (** The value joins of a capped list charge the sizes of the evaluated values. *)
  Lemma T3_eval_joins : forall e xs, length xs <= C.k ->
    (eval_joins e xs <= k_disjunction * N.of_nat (fold_right Nat.add 0%nat
      (map (fun s => (V.size (S.eval e s) + 1)%nat) xs) + 1))%N.
  Proof. Admitted. (* STUB *)
End StateDisjunctionT.

(* The landed lattice source exposed the following raw-list equations. The shared
   bounded carrier now supplies P.clip. Its laws allow different oversized-list
   covers, so the exact raw suffix equation is not implied by the reviewed P.
Theorem compact_equation {A} k (L : lattice A) xs :
  compact k L xs =
    if Nat.leb (length xs) k then xs
    else firstn (k - 1) xs ++ [join_all L (skipn (k - 1) xs)].

   The state widening grows the first nonbottom alternative using uncovered candidates.
   The landed lattice widening used a single collapse and its equation is a different claim.
Theorem widen_disjunction {A} k (L : lattice A) xs ys :
  widen (disjunction k L) xs ys =
    if disjunction_leb L ys xs then xs
    else [widen L (join_all L xs) (join_all L (xs ++ ys))].

   The old selective-join and invariant-based rank bundles used lattice_laws,
   lub_laws, concretisation_laws and widening_rank_on records, which are no longer
   the shared bounded component interface. Their original claims were:
Theorem disjunction_lub k :
  (forall a b, leb L (join L a b) a = true \/ leb L (join L a b) b = true) ->
  lub_laws (disjunction k L).
Theorem monotone_join_all {A} (L : lattice A) xs ys :
  lattice_laws L -> lub_laws L ->
  Forall2 (fun x y => leb L x y = true) xs ys ->
  leb L (join_all L xs) (join_all L ys) = true.
Theorem disjunction_gamma_laws {A C} k (L : lattice A) (G : concretisation A C) :
  concretisation_laws L G ->
  concretisation_laws (disjunction k L) (disjunction_gamma G).
Theorem disjunction_bot_empty {A C} k (L : lattice A) (G : concretisation A C) :
  bottom_empty (disjunction k L) (disjunction_gamma G).
Theorem disjunction_wrank k : widening_rank_on (disjunction k L) (Forall inv).
*)

(* The landed cost statements below refer to the removed Cost monad and raw-list
   lattice. The later timing part derives clocks for the reviewed bounded carrier.
Theorem compact_ticks k xs :
  Cost.ticks (compact_c k L xs) =
    (N.of_nat (length xs) + 1 +
      if Nat.leb (length xs) k then 0 else
        Cost.ticks (compact_tail_c (k - 1) L xs))%N.
Theorem disjunction_cost_bounded k m :
  cost_bounded_on (disjunction k L) (fun xs => Forall inv xs /\ length xs <= m)
    (((2 * N.of_nat m + 1) * (2 * N.of_nat m + 1)) * (c + 6))%N.
Theorem disjunction_cost_bigO {X} k (xs ys : X -> list A) :
  (forall x, Forall inv (xs x)) -> (forall x, Forall inv (ys x)) ->
  bigO
    (fun x => let n := (N.of_nat (length (xs x)) + N.of_nat (length (ys x)) + 1)%N in
      (n * n)%N)
    (fun x =>
      (Cost.ticks (leb_c (disjunction k L) (xs x) (ys x)) +
       Cost.ticks (join_c (disjunction k L) (xs x) (ys x)) +
       Cost.ticks (widen_c (disjunction k L) (xs x) (ys x)) +
       Cost.ticks (narrow_c (disjunction k L) (xs x) (ys x)))%N).
*)

Module StateDisjunctionClaims (X : KEY) (L : LANG) (V : VALUE_DOMAIN L)
    (S : STATE_DOMAIN X L V) (C : POS_CAP) (P : SharedDisjunction.DISJUNCTION S C).
  Include StateDisjunction X L V S C P.

  Theorem join_all_equation xs :
    collapse xs = match xs with [] => S.bot | x :: rest => fold_left S.join rest x end.
  Proof. destruct xs; reflexivity. Qed.

  Theorem disjunction_leb_equation a b : leb a b =
    forallb (fun x => existsb (S.leb x) (proj1_sig b)) (proj1_sig a).
  Proof.
    apply leb_hoare.
  Qed.

  Theorem disjunction_leb_spec a b : leb a b = true <->
    forall x, In x (proj1_sig a) ->
      exists y, In y (proj1_sig b) /\ S.leb x y = true.
Proof.
  rewrite disjunction_leb_equation, forallb_forall.
  split; intros H x Hin; specialize (H x Hin); now apply existsb_exists in H.
Qed.

  Theorem join_disjunction a b : join a b = P.clip (proj1_sig a ++ proj1_sig b).
  Proof.
    apply join_compact.
  Qed.

  Theorem disjunction_join_size a b : length (proj1_sig (join a b)) <= C.k.
  Proof.
    apply Nat.leb_le; exact (proj2_sig (join a b)).
  Qed.

  Theorem join_all_upper xs x : In x xs -> S.leb x (collapse xs) = true.
  Proof.
    apply collapse_covers.
  Qed.
End StateDisjunctionClaims.

(* The old fold equation named a charged helper whose pure value is now collapse.
Theorem fold_join_equation {A} (L : lattice A) xs a :
  Cost.value (fold_join_c L xs a) = fold_left (join L) xs a.

   The old closure statements quantified over closed_on and lattice_laws record
   bundles. The reviewed bounded state interface supplies neither such invariant
   provider nor its preservation contract for an arbitrary P.clip.
Theorem join_all_closed xs : Forall inv xs -> inv (join_all L xs).
Theorem disjunction_closed k : closed_on (disjunction k L) (Forall inv).
Theorem disjunction_laws k : lattice_laws (disjunction k L).
*)
