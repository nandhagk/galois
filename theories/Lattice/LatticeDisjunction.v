(** * Capped Hoare disjunctions

    Lists denote unions and compare by coverage of every alternative.
    For example, cap one collapses two incomparable flat values to their top.
    Builds on: CostList, LatticeCore, LatticeHeight and LatticeConcrete. *)

From Stdlib Require Import List Bool Arith NArith Lia.
From Galois.Cost Require Import CostMonad CostList CostBound CostTactics.
From Galois.Lattice Require Import LatticeCore LatticeHeight LatticeConcrete.
Import List.ListNotations Cost.Notations.
Local Open Scope nat_scope.

(** Folding charges each traversal and each component callback invocation. *)
Fixpoint fold_join_c {A} (L : lattice A) (xs : list A) (a : A) : Cost.t A :=
  match xs with
  | [] => Cost.ret a
  | x :: rest =>
    Cost.step ;; Cost.step ;;
    let* b := join_c L a x in fold_join_c L rest b
  end.

(** A nonempty list starts its fold at its first alternative. *)
Definition join_all_c {A} (L : lattice A) (xs : list A) : Cost.t A :=
  Cost.step ;;
  match xs with
  | [] => Cost.ret (bot L)
  | x :: rest => fold_join_c L rest x
  end.

(** The pure list join is the value projection of its charged fold. *)
Definition join_all {A} (L : lattice A) (xs : list A) : A :=
  Cost.value (join_all_c L xs).

(** Coverage charges both list traversals and every component comparison call. *)
Definition disjunction_leb_c {A} (L : lattice A) (xs ys : list A) : Cost.t bool :=
  forallb_c (fun x => Cost.step ;;
    existsb_c (fun y => Cost.step ;; leb_c L x y) ys) xs.

(** The pure Hoare test is the value projection of charged coverage. *)
Definition disjunction_leb {A} (L : lattice A) (xs ys : list A) : bool :=
  Cost.value (disjunction_leb_c L xs ys).

(** A charged prefix traversal rebuilds the prefix and joins the suffix once. *)
Fixpoint compact_tail_c {A} (n : nat) (L : lattice A) (xs : list A) : Cost.t (list A) :=
  Cost.step ;;
  match n, xs with
  | S m, x :: rest => Cost.map (cons x) (compact_tail_c m L rest)
  | _, _ => Cost.map (fun a => [a]) (join_all_c L xs)
  end.

(** Compaction first counts the input and retains legacy cap-zero behavior. *)
Definition compact_c {A} (k : nat) (L : lattice A) (xs : list A) : Cost.t (list A) :=
  let* n := length_c xs in
  Cost.step ;;
  if Nat.leb n k then Cost.ret xs else compact_tail_c (k - 1) L xs.

(** Pure compaction is the value projection of the charged count and prefix traversal. *)
Definition compact {A} (k : nat) (L : lattice A) (xs : list A) : list A :=
  Cost.value (compact_c k L xs).

(** Escaping widening scans coverage, joins both inputs and collapses to one value. *)
Definition disjunction {A} (k : nat) (L : lattice A) : lattice (list A) :=
  {| leb_c := disjunction_leb_c L;
     bot := [];
     join_c := fun xs ys =>
       let* zs := app_c xs ys in compact_c k L zs;
     widen_c := fun xs ys =>
       let* covered := disjunction_leb_c L ys xs in
       if covered then Cost.ret xs else
       let* zs := app_c xs ys in
       let* a := join_all_c L xs in
       let* b := join_all_c L zs in
       Cost.step ;; Cost.map (fun w => [w]) (widen_c L a b);
     narrow_c := fun xs _ => Cost.ret xs |}.

(** The fold value is the ordinary left fold of component joins. *)
Theorem fold_join_equation {A} (L : lattice A) xs a :
  Cost.value (fold_join_c L xs a) = fold_left (join L) xs a.
Proof.
  revert a; induction xs as [|x xs IH]; intro a; cbn [fold_join_c fold_left];
    cost_simpl; auto.
Qed.

(** Joining no alternatives returns bottom without calling a component join. *)
Theorem join_all_equation {A} (L : lattice A) xs :
  join_all L xs = match xs with [] => bot L | x :: rest => fold_left (join L) rest x end.
Proof.
  destruct xs; unfold join_all, join_all_c; cost_simpl; auto using fold_join_equation.
Qed.

(** Hoare comparison is universal existential component comparison. *)
Theorem disjunction_leb_equation {A} (L : lattice A) xs ys :
  disjunction_leb L xs ys = forallb (fun x => existsb (leb L x) ys) xs.
Proof.
  unfold disjunction_leb, disjunction_leb_c.
  rewrite value_forallb_c; induction xs as [|x xs IH]; cbn [forallb].
  - reflexivity.
  - rewrite Cost.value_bind, value_existsb_c, IH; reflexivity.
Qed.

Local Lemma compact_tail_equation {A} n (L : lattice A) xs :
  Cost.value (compact_tail_c n L xs) =
    firstn n xs ++ [join_all L (skipn n xs)].
Proof.
  revert xs; induction n as [|n IH]; intros [|x xs]; cbn [compact_tail_c];
    cost_simpl; cbn [firstn skipn]; try reflexivity.
  rewrite IH; reflexivity.
Qed.

(** Compaction keeps short lists and otherwise joins exactly the legacy suffix. *)
Theorem compact_equation {A} k (L : lattice A) xs :
  compact k L xs =
    if Nat.leb (length xs) k then xs
    else firstn (k - 1) xs ++ [join_all L (skipn (k - 1) xs)].
Proof.
  unfold compact, compact_c; rewrite Cost.value_bind, value_length_c.
  cost_simpl; destruct (Nat.leb (length xs) k); cost_simpl;
    auto using compact_tail_equation.
Qed.

(** Disjunction join appends then compacts. *)
Theorem join_disjunction {A} k (L : lattice A) xs ys :
  join (disjunction k L) xs ys = compact k L (xs ++ ys).
Proof.
  unfold join; cbn [disjunction join_c]; rewrite Cost.value_bind, value_app_c; reflexivity.
Qed.

(** Covered widening keeps its left list and escaping widening returns a singleton. *)
Theorem widen_disjunction {A} k (L : lattice A) xs ys :
  widen (disjunction k L) xs ys =
    if disjunction_leb L ys xs then xs
    else [widen L (join_all L xs) (join_all L (xs ++ ys))].
Proof.
  unfold widen; cbn [disjunction widen_c]; rewrite Cost.value_bind.
  fold (disjunction_leb L ys xs).
  destruct (disjunction_leb L ys xs); cost_simpl; rewrite ?value_app_c; reflexivity.
Qed.

(** Hoare coverage gives a witnessing right alternative for every left member. *)
Theorem disjunction_leb_spec {A} (L : lattice A) xs ys :
  disjunction_leb L xs ys = true <->
    forall x, In x xs -> exists y, In y ys /\ leb L x y = true.
Proof.
  rewrite disjunction_leb_equation, forallb_forall.
  split; intros H x Hin; specialize (H x Hin); now apply existsb_exists in H.
Qed.

Section Laws.
Context {A : Type} (L : lattice A) (H : lattice_laws L).

Local Lemma disjunction_refl xs : disjunction_leb L xs xs = true.
Proof.
  apply disjunction_leb_spec; intros x Hin; exists x; split;
    [exact Hin | apply (leb_refl H)].
Qed.

Local Lemma disjunction_trans xs ys zs :
  disjunction_leb L xs ys = true -> disjunction_leb L ys zs = true ->
  disjunction_leb L xs zs = true.
Proof.
  rewrite !disjunction_leb_spec; intros Hxy Hyz x Hin.
  destruct (Hxy x Hin) as [y [Hy Hle]], (Hyz y Hy) as [z [Hz Hle']].
  exists z; split; [exact Hz | eapply (leb_trans H); eassumption].
Qed.

Local Lemma fold_upper_start xs a : leb L a (fold_left (join L) xs a) = true.
Proof.
  revert a; induction xs as [|x xs IH]; intro a; cbn.
  - apply (leb_refl H).
  - eapply (leb_trans H); [apply (join_upper_l H) | apply IH].
Qed.

Local Lemma fold_upper_member xs a x : In x xs ->
  leb L x (fold_left (join L) xs a) = true.
Proof.
  revert a; induction xs as [|y xs IH]; intros a Hin; cbn in *; [contradiction |].
  destruct Hin as [<- | Hin].
  - eapply (leb_trans H); [apply (join_upper_r H) | apply fold_upper_start].
  - apply IH; exact Hin.
Qed.

(** Every input alternative is below the folded join, under weak component laws. *)
Theorem join_all_upper xs x : In x xs -> leb L x (join_all L xs) = true.
Proof.
  rewrite join_all_equation; destruct xs as [|a xs]; cbn; intro Hin; [contradiction |].
  destruct Hin as [<- | Hin]; auto using fold_upper_start, fold_upper_member.
Qed.

(** Compaction covers every original alternative even at cap zero. *)
Theorem compact_covers k xs : disjunction_leb L xs (compact k L xs) = true.
Proof.
  rewrite compact_equation; destruct (Nat.leb (length xs) k); [apply disjunction_refl |].
  apply disjunction_leb_spec; intros x Hin.
  rewrite <- (firstn_skipn (k - 1) xs) in Hin; apply in_app_iff in Hin.
  destruct Hin as [Hp | Hs].
  - exists x; split; [apply in_app_iff; auto | apply (leb_refl H)].
  - exists (join_all L (skipn (k - 1) xs)); split.
    + apply in_app_iff; right; now left.
    + apply join_all_upper; exact Hs.
Qed.

Local Lemma append_covers xs ys :
  disjunction_leb L xs (xs ++ ys) = true /\ disjunction_leb L ys (xs ++ ys) = true.
Proof.
  split; apply disjunction_leb_spec; intros x Hin; exists x; split;
    try apply (leb_refl H); apply in_app_iff; auto.
Qed.

Local Lemma collapse_covers xs ys :
  disjunction_leb L (xs ++ ys)
    [widen L (join_all L xs) (join_all L (xs ++ ys))] = true.
Proof.
  apply disjunction_leb_spec; intros x Hin.
  exists (widen L (join_all L xs) (join_all L (xs ++ ys))); split; [now left |].
  eapply (leb_trans H); [apply join_all_upper; exact Hin | apply (widen_upper_r H)].
Qed.

(** Capped Hoare disjunction satisfies weak laws without component selectivity. *)
Theorem disjunction_laws k : lattice_laws (disjunction k L).
Proof.
  constructor.
  - apply disjunction_refl.
  - apply disjunction_trans.
  - intro xs; reflexivity.
  - intros xs ys; rewrite join_disjunction.
    eapply disjunction_trans; [exact (proj1 (append_covers xs ys)) | apply compact_covers].
  - intros xs ys; rewrite join_disjunction.
    eapply disjunction_trans; [exact (proj2 (append_covers xs ys)) | apply compact_covers].
  - intros xs ys; rewrite widen_disjunction.
    destruct (disjunction_leb L ys xs); [apply disjunction_refl |].
    eapply disjunction_trans; [exact (proj1 (append_covers xs ys)) | apply collapse_covers].
  - intros xs ys; rewrite widen_disjunction.
    destruct (disjunction_leb L ys xs) eqn:Hcover; [exact Hcover |].
    eapply disjunction_trans; [exact (proj2 (append_covers xs ys)) | apply collapse_covers].
  - intros xs ys _; apply disjunction_refl.
  - intros xs ys Hcover; exact Hcover.
Qed.

Local Lemma fold_selective
    (selective : forall a b, leb L (join L a b) a = true \/ leb L (join L a b) b = true)
    xs a :
  exists z, In z (a :: xs) /\ leb L (fold_left (join L) xs a) z = true.
Proof.
  revert a; induction xs as [|x xs IH]; intro a; cbn [fold_left].
  - exists a; split; [now left | apply (leb_refl H)].
  - destruct (IH (join L a x)) as [z [[<- | Hin] Hle]].
    + destruct (selective a x) as [Ha | Hx].
      * exists a; split; [now left | eapply (leb_trans H); eassumption].
      * exists x; split; [right; now left | eapply (leb_trans H); eassumption].
    + exists z; split; [right; now right | exact Hle].
Qed.

Local Lemma compact_below k xs zs
    (selective : forall a b, leb L (join L a b) a = true \/ leb L (join L a b) b = true) :
  disjunction_leb L xs zs = true -> disjunction_leb L (compact k L xs) zs = true.
Proof.
  intro Hcover; rewrite compact_equation.
  destruct (Nat.leb (length xs) k) eqn:Hlen; [exact Hcover |].
  pose proof (proj1 (disjunction_leb_spec L xs zs) Hcover) as Hcovers.
  apply disjunction_leb_spec; intros x Hin.
  apply in_app_iff in Hin; destruct Hin as [Hp | [<- | Hnil]]; [| |contradiction].
  - apply Hcovers; rewrite <- (firstn_skipn (k - 1) xs); apply in_app_iff; now left.
  - destruct (skipn (k - 1) xs) as [|a rest] eqn:Htail.
    + pose proof (length_skipn (k - 1) xs) as Hsize.
      rewrite Htail in Hsize; cbn in Hsize; apply Nat.leb_gt in Hlen; lia.
    + rewrite join_all_equation.
      destruct (fold_selective selective rest a) as [z [Hz Hle]].
      destruct (Hcovers z) as [w [Hw Hzw]].
      * rewrite <- (firstn_skipn (k - 1) xs); apply in_app_iff; right.
        rewrite Htail; exact Hz.
      * exists w; split; [exact Hw | eapply (leb_trans H); eassumption].
Qed.

(** Selective component joins make capped joins least in the Hoare order. *)
Theorem disjunction_lub k :
  (forall a b, leb L (join L a b) a = true \/ leb L (join L a b) b = true) ->
  lub_laws (disjunction k L).
Proof.
  intro selective; constructor; intros xs ys zs Hx Hy; rewrite join_disjunction.
  apply compact_below; [exact selective |].
  apply disjunction_leb_spec; intros x Hin; apply in_app_iff in Hin.
  destruct Hin as [Hin | Hin]; [apply (proj1 (disjunction_leb_spec L xs zs) Hx) |
    apply (proj1 (disjunction_leb_spec L ys zs) Hy)]; exact Hin.
Qed.
End Laws.

Local Lemma fold_join_monotone {A} (L : lattice A)
    (H : lattice_laws L) (J : lub_laws L) xs ys :
  Forall2 (fun x y => leb L x y = true) xs ys ->
  forall a b, leb L a b = true ->
    leb L (fold_left (join L) xs a) (fold_left (join L) ys b) = true.
Proof.
  intro Hxy; induction Hxy as [|x y xs ys Hle Htail IH]; intros a b Hab; cbn [fold_left].
  - exact Hab.
  - apply IH; apply (join_monotone L); assumption.
Qed.

(** Ordered corresponding alternatives have ordered joins under component leastness. *)
Theorem monotone_join_all {A} (L : lattice A) xs ys :
  lattice_laws L -> lub_laws L ->
  Forall2 (fun x y => leb L x y = true) xs ys ->
  leb L (join_all L xs) (join_all L ys) = true.
Proof.
  intros H J Hxy; rewrite !join_all_equation.
  destruct Hxy as [|x y xs ys Hle Htail].
  - apply (leb_refl H).
  - apply (fold_join_monotone L H J); assumption.
Qed.

(** A positive cap bounds the result even when the supplied lists exceed the cap. *)
Theorem disjunction_join_size {A} k (L : lattice A) xs ys :
  1 <= k -> length (join (disjunction k L) xs ys) <= k.
Proof.
  intro Hk; rewrite join_disjunction, compact_equation.
  destruct (Nat.leb (length (xs ++ ys)) k) eqn:Hlen.
  - now apply Nat.leb_le.
  - rewrite length_app, length_firstn; cbn.
    pose proof (Nat.le_min_l (k - 1) (length (xs ++ ys))); lia.
Qed.

(** A disjunction denotes a concrete value when one alternative denotes it. *)
Definition disjunction_gamma {A C} (G : concretisation A C) : concretisation (list A) C :=
  {| gamma := fun xs c => exists x, In x xs /\ gamma G x c |}.

(** Component monotonicity transports through Hoare coverage without selectivity. *)
Theorem disjunction_gamma_laws {A C} k (L : lattice A) (G : concretisation A C) :
  concretisation_laws L G ->
  concretisation_laws (disjunction k L) (disjunction_gamma G).
Proof.
  intro HG; constructor; intros xs ys c Hcover [x [Hin Hgamma]].
  destruct (proj1 (disjunction_leb_spec L xs ys) Hcover x Hin) as [y [Hy Hle]].
  exists y; split; [exact Hy | eapply (gamma_monotone HG); eassumption].
Qed.

(** Empty disjunction has an empty meaning regardless of the component bottom. *)
Theorem disjunction_bot_empty {A C} k (L : lattice A) (G : concretisation A C) :
  bottom_empty (disjunction k L) (disjunction_gamma G).
Proof.
  constructor; intros c [x [Hin _]]; exact Hin.
Qed.

Section Invariant.
Context {A : Type} (L : lattice A) (inv : A -> Prop) (C : closed_on L inv).

Local Lemma fold_join_closed xs a :
  Forall inv xs -> inv a -> inv (fold_left (join L) xs a).
Proof.
  intro Hxs; revert a; induction Hxs as [|x xs Hx Hxs IH]; intros a Ha; cbn [fold_left].
  - exact Ha.
  - apply IH; apply (join_inv C); assumption.
Qed.

(** Joining invariant alternatives stays invariant, including the empty input. *)
Theorem join_all_closed xs : Forall inv xs -> inv (join_all L xs).
Proof.
  rewrite join_all_equation; intros Hxs; destruct Hxs as [|x xs Hx Hxs].
  - apply (bot_inv C).
  - apply fold_join_closed; assumption.
Qed.

Local Lemma compact_closed k xs : Forall inv xs -> Forall inv (compact k L xs).
Proof.
  intro Hxs; rewrite compact_equation; destruct (Nat.leb (length xs) k); [exact Hxs |].
  apply Forall_app; split.
  - apply Forall_forall; intros x Hin; apply (proj1 (Forall_forall _ _) Hxs).
    rewrite <- (firstn_skipn (k - 1) xs); apply in_app_iff; now left.
  - constructor; [apply join_all_closed | constructor].
    apply Forall_forall; intros x Hin; apply (proj1 (Forall_forall _ _) Hxs).
    rewrite <- (firstn_skipn (k - 1) xs); apply in_app_iff; now right.
Qed.

(** Component closure lifts to lists of invariant alternatives. *)
Theorem disjunction_closed k : closed_on (disjunction k L) (Forall inv).
Proof.
  constructor.
  - constructor.
  - intros xs ys Hx Hy; rewrite join_disjunction; apply compact_closed, Forall_app; auto.
  - intros xs ys Hx Hy; rewrite widen_disjunction.
    destruct (disjunction_leb L ys xs); [exact Hx |].
    constructor; [apply (widen_inv C); apply join_all_closed | constructor]; auto.
    apply Forall_app; auto.
  - intros xs ys Hx Hy _; exact Hx.
Qed.

Context (H : lattice_laws L) (W : widening_rank_on L inv).

Local Lemma singleton_coverage x ys :
  leb L (join_all L ([x] ++ ys)) x = true -> disjunction_leb L ys [x] = true.
Proof.
  intro Hjoin; apply disjunction_leb_spec; intros y Hin; exists x; split; [now left |].
  eapply (leb_trans H); [apply join_all_upper; [exact H |] | exact Hjoin].
  apply in_app_iff; right; exact Hin.
Qed.

Local Lemma collapse_rank xs ys :
  Forall inv xs -> Forall inv ys -> disjunction_leb L ys xs = false ->
  2 * wrank W (widen L (join_all L xs) (join_all L (xs ++ ys))) <
  2 * wrank W (join_all L xs) + (if Nat.eqb (length xs) 1 then 0 else 1).
Proof.
  intros Hx Hy Hescape.
  pose proof (join_all_closed xs Hx) as Ha.
  assert (Hb : inv (join_all L (xs ++ ys))).
  { apply join_all_closed, Forall_app; auto. }
  destruct (Nat.eqb (length xs) 1) eqn:Hsingle.
  - apply Nat.eqb_eq in Hsingle; destruct xs as [|x [|y xs]]; cbn in Hsingle;
      try discriminate.
    assert (Hbad : leb L (join_all L ([x] ++ ys)) x = false).
    { destruct (leb L (join_all L ([x] ++ ys)) x) eqn:Hle; [|reflexivity].
      pose proof (singleton_coverage x ys Hle); congruence. }
    rewrite join_all_equation in Ha; cbn [fold_left] in Ha.
    pose proof (widen_rank_progress W _ _ Ha Hb Hbad).
    rewrite (join_all_equation L [x]); cbn [fold_left]; lia.
  - destruct (leb L (join_all L (xs ++ ys)) (join_all L xs)) eqn:Hle.
    + pose proof (widen_rank_stable W _ _ Ha Hb Hle); lia.
    + pose proof (widen_rank_progress W _ _ Ha Hb Hle); lia.
Qed.

(** Collapse decreases twice the component credit plus a nonsingleton flag. *)
Theorem disjunction_wrank k : widening_rank_on (disjunction k L) (Forall inv).
Proof.
  set (measure := fun xs => 2 * wrank W (join_all L xs) +
    (if Nat.eqb (length xs) 1 then 0 else 1)).
  refine {| wrank := measure; wbound := 2 * wbound W + 1 |}.
  - intros xs Hxs; unfold measure.
    pose proof (wrank_bounded W _ (join_all_closed xs Hxs)).
    destruct (Nat.eqb (length xs) 1); lia.
  - intros xs ys Hx Hy Hle; rewrite widen_disjunction.
    change (disjunction_leb L ys xs = true) in Hle; rewrite Hle; lia.
  - intros xs ys Hx Hy Hescape; rewrite widen_disjunction.
    change (disjunction_leb L ys xs = false) in Hescape; rewrite Hescape.
    unfold measure; rewrite join_all_equation; cbn [fold_left length Nat.eqb].
    pose proof (collapse_rank xs ys Hx Hy Hescape); lia.
Defined.
End Invariant.

Section Costs.
Context {A : Type} (L : lattice A).

(** Fold charges retain the actual accumulator-dependent component callback cost. *)
Theorem fold_join_cost x xs a :
  Cost.ticks (fold_join_c L (x :: xs) a) =
    (2 + Cost.ticks (join_c L a x) +
      Cost.ticks (fold_join_c L xs (join L a x)))%N.
Proof.
  cbn [fold_join_c]; cost_simpl; fold (join L a x); lia.
Qed.

(** Joining lists charges a head inspection and every join in the actual tail. *)
Theorem join_all_cost xs :
  Cost.ticks (join_all_c L xs) =
    (1 + match xs with [] => 0 | x :: rest => Cost.ticks (fold_join_c L rest x) end)%N.
Proof.
  unfold join_all_c; rewrite Cost.ticks_bind, Cost.ticks_step.
  destruct xs; cbn beta iota; rewrite ?Cost.ticks_ret; reflexivity.
Qed.

(** Compact charges the length scan and the actual prefix and suffix work. *)
Theorem compact_ticks k xs :
  Cost.ticks (compact_c k L xs) =
    (N.of_nat (length xs) + 1 +
      if Nat.leb (length xs) k then 0 else
        Cost.ticks (compact_tail_c (k - 1) L xs))%N.
Proof.
  unfold compact_c; rewrite Cost.ticks_bind, ticks_length_c, value_length_c.
  cost_simpl; destruct (Nat.leb (length xs) k); cost_simpl; lia.
Qed.

(** Widening charges the coverage scan even when it returns the left input unchanged. *)
Theorem disjunction_widen_cost k xs ys :
  Cost.ticks (widen_c (disjunction k L) xs ys) =
    (Cost.ticks (disjunction_leb_c L ys xs) +
      if disjunction_leb L ys xs then 0 else
        N.of_nat (length xs) + Cost.ticks (join_all_c L xs) +
          Cost.ticks (join_all_c L (xs ++ ys)) + 1 +
          Cost.ticks (widen_c L (join_all L xs) (join_all L (xs ++ ys))))%N.
Proof.
  cbn [disjunction widen_c]; rewrite Cost.ticks_bind.
  fold (disjunction_leb L ys xs); destruct (disjunction_leb L ys xs);
    cost_simpl; rewrite ?value_app_c, ?ticks_app_c;
    fold (join_all L xs) (join_all L (xs ++ ys)); lia.
Qed.

Local Lemma exists_cost x ys :
  (Cost.ticks (existsb_c (fun y => Cost.step ;; leb_c L x y) ys) <=
    fold_right (fun y n => 2 + Cost.ticks (leb_c L x y) + n) 0 ys)%N.
Proof.
  induction ys as [|y ys IH].
  - rewrite ticks_existsb_c_nil; reflexivity.
  - rewrite ticks_existsb_c_cons; cost_simpl; cbn [fold_right].
    fold (leb L x y); destruct (leb L x y); lia.
Qed.

(** Coverage is bounded by both traversals plus all pairwise callee charges. *)
Theorem disjunction_leb_cost xs ys :
  (Cost.ticks (disjunction_leb_c L xs ys) <=
    fold_right (fun x n => 2 +
      fold_right (fun y m => 2 + Cost.ticks (leb_c L x y) + m) 0 ys + n) 0 xs)%N.
Proof.
  unfold disjunction_leb_c; induction xs as [|x xs IH].
  - rewrite ticks_forallb_c_nil; reflexivity.
  - rewrite ticks_forallb_c_cons; cost_simpl; cbn [fold_right].
    pose proof (exists_cost x ys).
    destruct (existsb (fun y => Cost.value (Cost.step ;; leb_c L x y)) ys); lia.
Qed.

Context (inv : A -> Prop) (C : closed_on L inv) (c : N)
  (K : cost_bounded_on L inv c).

Local Lemma fold_cost_bound xs a :
  Forall inv xs -> inv a ->
  (Cost.ticks (fold_join_c L xs a) <= N.of_nat (length xs) * (c + 2))%N.
Proof.
  intro Hxs; revert a; induction Hxs as [|x xs Hx Hxs IH]; intros a Ha.
  - cbn [fold_join_c]; rewrite Cost.ticks_ret; lia.
  - rewrite fold_join_cost; cbn [length]; rewrite Nat2N.inj_succ.
    specialize (IH _ (join_inv C _ _ Ha Hx)).
    destruct (K _ _ Ha Hx) as [_ [Hjoin _]]; nia.
Qed.

Local Lemma join_all_cost_bound xs : Forall inv xs ->
  (Cost.ticks (join_all_c L xs) <= 1 + N.of_nat (length xs) * (c + 2))%N.
Proof.
  intro Hxs; rewrite join_all_cost; destruct Hxs as [|x xs Hx Hxs]; cbn [length].
  - lia.
  - pose proof (fold_cost_bound xs x Hxs Hx); rewrite Nat2N.inj_succ; nia.
Qed.

Local Lemma compact_tail_cost_bound n xs : Forall inv xs ->
  (Cost.ticks (compact_tail_c n L xs) <=
    (N.of_nat (length xs) + 1) * (c + 3))%N.
Proof.
  revert xs; induction n as [|n IH]; intros xs Hxs.
  - cbn [compact_tail_c]; cost_simpl.
    pose proof (join_all_cost_bound xs Hxs); nia.
  - destruct Hxs as [|x xs Hx Hxs]; cbn [compact_tail_c]; cost_simpl.
    + pose proof (join_all_cost_bound [] (Forall_nil inv)); cbn [length] in *; nia.
    + specialize (IH xs Hxs); cbn [length]; rewrite Nat2N.inj_succ; nia.
Qed.

(** Numeric compact cost depends on the raw length and invariant component join bounds. *)
Theorem compact_cost k xs : Forall inv xs ->
  (Cost.ticks (compact_c k L xs) <= (N.of_nat (length xs) + 1) * (c + 5))%N.
Proof.
  intro Hxs; unfold compact_c; rewrite Cost.ticks_bind, value_length_c, ticks_length_c.
  cost_simpl; destruct (Nat.leb (length xs) k); cost_simpl.
  - nia.
  - pose proof (compact_tail_cost_bound (k - 1) xs Hxs); nia.
Qed.

Local Lemma coverage_cost_bound xs ys : Forall inv xs -> Forall inv ys ->
  (Cost.ticks (disjunction_leb_c L xs ys) <=
    N.of_nat (length xs) * (2 + N.of_nat (length ys) * (c + 2)))%N.
Proof.
  intros Hxs Hys; eapply N.le_trans; [apply disjunction_leb_cost |].
  assert (Hrow : forall x, inv x ->
    (fold_right (fun y m => 2 + Cost.ticks (leb_c L x y) + m) 0 ys <=
      N.of_nat (length ys) * (c + 2))%N).
  { intros x Hx; induction Hys as [|y ys Hy Hys IH]; cbn [fold_right length].
    - nia.
    - rewrite Nat2N.inj_succ; destruct (K _ _ Hx Hy) as [Hleb _]; nia. }
  induction Hxs as [|x xs Hx Hxs IH]; cbn [fold_right length].
  - nia.
  - rewrite Nat2N.inj_succ; specialize (Hrow x Hx); nia.
Qed.

(** All operations retain length-dependent costs, including widening's coverage and folds. *)
Theorem disjunction_cost k xs ys : Forall inv xs -> Forall inv ys ->
  let nx := N.of_nat (length xs) in
  let ny := N.of_nat (length ys) in
  (Cost.ticks (leb_c (disjunction k L) xs ys) <= nx * (2 + ny * (c + 2)) /\
   Cost.ticks (join_c (disjunction k L) xs ys) <= (nx + ny + 1) * (c + 6) /\
   Cost.ticks (widen_c (disjunction k L) xs ys) <=
     ny * (2 + nx * (c + 2)) + nx + 3 +
       (2 * nx + ny) * (c + 2) + c /\
   Cost.ticks (narrow_c (disjunction k L) xs ys) = 0)%N.
Proof.
  intros Hx Hy; cbn zeta; split; [apply coverage_cost_bound; assumption |].
  assert (Happ : Forall inv (xs ++ ys)) by (apply Forall_app; auto).
  pose proof (compact_cost k (xs ++ ys) Happ) as Hcompact.
  pose proof (join_all_cost_bound xs Hx) as Hfoldx.
  pose proof (join_all_cost_bound (xs ++ ys) Happ) as Hfoldxy.
  pose proof (coverage_cost_bound ys xs Hy Hx) as Hscan.
  pose proof (K _ _ (join_all_closed L inv C xs Hx)
    (join_all_closed L inv C (xs ++ ys) Happ)) as [_ [_ [Hwide _]]].
  rewrite length_app, Nat2N.inj_add in Hcompact, Hfoldxy.
  cbn [disjunction join_c widen_c narrow_c].
  rewrite !Cost.ticks_bind, !value_app_c, !ticks_app_c.
  split.
  - nia.
  - destruct (Cost.value (disjunction_leb_c L ys xs)); cost_simpl;
      rewrite ?value_app_c, ?ticks_app_c;
      fold (join_all L xs) (join_all L (xs ++ ys)); split; try reflexivity; nia.
Qed.

(** A bounded-input client gets a uniform quadratic bound with explicit invariant premises. *)
Theorem disjunction_cost_bounded k m :
  cost_bounded_on (disjunction k L) (fun xs => Forall inv xs /\ length xs <= m)
    (((2 * N.of_nat m + 1) * (2 * N.of_nat m + 1)) * (c + 6))%N.
Proof.
  intros xs ys [Hx Hnx] [Hy Hny].
  destruct (disjunction_cost k xs ys Hx Hy) as [Hl [Hj [Hw Hn]]].
  assert (Hconvert : forall n p : nat, n <= p -> (N.of_nat n <= N.of_nat p)%N).
  { intros n p Hle; induction Hle.
    - reflexivity.
    - rewrite Nat2N.inj_succ; lia. }
  pose proof (Hconvert _ _ Hnx) as Hnx'.
  pose proof (Hconvert _ _ Hny) as Hny'.
  repeat split; nia.
Qed.

(** Invariant input families have quadratic total operation cost for a fixed component bound. *)
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
Proof.
  intros Hx Hy; exists (10 * (c + 6))%N; intro x.
  destruct (disjunction_cost k (xs x) (ys x) (Hx x) (Hy x)) as [Hl [Hj [Hw Hn]]].
  cbn zeta; rewrite Hn; nia.
Qed.
End Costs.

Arguments join_all_c {A} L xs : simpl never.
Arguments disjunction_leb_c {A} L xs ys : simpl never.
Arguments compact_c {A} k L xs : simpl never.
Arguments disjunction {A} k L : simpl never.
