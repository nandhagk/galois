(** * Canonical integer interval sets

    Half-open integer ranges represent finite sets of integers.
    For example, [(0, 2)] contains zero and one but not two.
    Builds on: Stdlib and Cost. *)

From Stdlib Require Import ZArith List Bool Lia Sorting.Sorted.
From Galois.Cost Require Import CostMonad.
Import List.ListNotations.

Local Open Scope Z_scope.

Module IntervalSet.

(** A range contains its lower endpoint and excludes its upper endpoint. *)
Definition range : Type := (Z * Z)%type.

(** A set is represented by a list of ranges. *)
Definition t : Type := list range.

(** Canonical ranges are nonempty and have at least one absent integer between them. *)
Definition wf (rs : t) : Prop :=
  Forall (fun r => fst r < snd r) rs /\
  StronglySorted (fun r s => snd r < fst s) rs.

(** Membership describes the integers represented by the ranges. *)
Definition contains (rs : t) (b : Z) : Prop :=
  exists r, In r rs /\ fst r <= b < snd r.

(** The empty set has no ranges. *)
Definition empty_c : Cost.t t := Cost.ret [].
Definition empty : t := Cost.value empty_c.

(** A range contributes no integers if its endpoints are equal or reversed. *)
Definition singleton_c (r : range) : Cost.t t :=
  Cost.ret (if fst r <? snd r then [r] else []).
Definition singleton (r : range) : t := Cost.value (singleton_c r).

(** Membership charges each range inspected, including the successful range. *)
Fixpoint mem_c (rs : t) (b : Z) : Cost.t bool :=
  match rs with
  | [] => Cost.ret false
  | r :: rest =>
    Cost.bind Cost.step (fun _ =>
      if (fst r <=? b) && (b <? snd r)
      then Cost.ret true
      else mem_c rest b)
  end.
Definition mem (rs : t) (b : Z) : bool := Cost.value (mem_c rs b).

(** Emptiness charges a step when inspecting a nonempty list. *)
Definition is_empty_c (rs : t) : Cost.t bool :=
  match rs with
  | [] => Cost.ret true
  | _ :: _ => Cost.bind Cost.step (fun _ => Cost.ret false)
  end.
Definition is_empty (rs : t) : bool := Cost.value (is_empty_c rs).

(** Elements returns the canonical ranges without enumerating their integers. *)
Definition elements_c (rs : t) : Cost.t (list range) := Cost.ret rs.
Definition elements (rs : t) : list range := Cost.value (elements_c rs).

Arguments empty : simpl never.
Arguments singleton _ : simpl never.
Arguments mem _ _ : simpl never.
Arguments is_empty _ : simpl never.
Arguments elements _ : simpl never.

(** The empty set is represented by the empty list. *)
Theorem empty_equation : empty = [].
Proof.
  reflexivity.
Qed.

(** A singleton contains its range exactly when the range is nonempty. *)
Theorem singleton_equation r :
  singleton r = if fst r <? snd r then [r] else [].
Proof.
  reflexivity.
Qed.

(** Membership scans ranges until it finds one containing the integer. *)
Theorem mem_equation rs b :
  mem rs b =
  match rs with
  | [] => false
  | r :: rest => if (fst r <=? b) && (b <? snd r) then true else mem rest b
  end.
Proof.
  destruct rs as [|r rest].
  - reflexivity.
  - change (Cost.value (Cost.bind Cost.step (fun _ =>
      if (fst r <=? b) && (b <? snd r) then Cost.ret true else mem_c rest b)) =
      if (fst r <=? b) && (b <? snd r) then true else mem rest b).
    rewrite Cost.value_bind.
    destruct ((fst r <=? b) && (b <? snd r)); [apply Cost.value_ret|reflexivity].
Qed.

(** Emptiness checks whether the range list is empty. *)
Theorem is_empty_equation rs :
  is_empty rs = match rs with [] => true | _ :: _ => false end.
Proof.
  destruct rs; reflexivity.
Qed.

(** Elements returns the representation unchanged. *)
Theorem elements_equation rs : elements rs = rs.
Proof.
  reflexivity.
Qed.

(** Boolean membership agrees with the half-open range interpretation. *)
Theorem mem_spec rs b : mem rs b = true <-> contains rs b.
Proof.
  induction rs as [|r rest IH].
  - rewrite mem_equation. unfold contains. split.
    + discriminate.
    + intros [s [Hin _]]. contradiction.
  - rewrite mem_equation. unfold contains at 1. cbn [In].
    destruct ((fst r <=? b) && (b <? snd r)) eqn:Hrange.
    + apply andb_true_iff in Hrange as [Hlo Hhi].
      apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi.
      split; [intros _; exists r; intuition|intros _; reflexivity].
    + rewrite IH. unfold contains. split.
      * intros [s [Hin Hb]]. exists s. intuition.
      * intros [s [[Heq|Hin] Hb]].
        -- subst s. apply andb_false_iff in Hrange.
           destruct Hrange as [Hlo|Hhi].
           ++ apply Z.leb_gt in Hlo. lia.
           ++ apply Z.ltb_ge in Hhi. lia.
        -- exists s. intuition.
Qed.

(** The empty list satisfies the canonical invariant. *)
Theorem wf_empty : wf empty.
Proof.
  rewrite empty_equation. split; constructor.
Qed.

(** Every singleton constructor result satisfies the canonical invariant. *)
Theorem wf_singleton r : wf (singleton r).
Proof.
  rewrite singleton_equation. destruct (fst r <? snd r) eqn:Hrange.
  - apply Z.ltb_lt in Hrange. split; constructor; try constructor; assumption.
  - split; constructor.
Qed.

(** Membership of a singleton uses the half-open bounds even for reversed ranges. *)
Theorem mem_singleton r b :
  mem (singleton r) b = ((fst r <=? b) && (b <? snd r))%bool.
Proof.
  rewrite singleton_equation. destruct (fst r <? snd r) eqn:Hrange.
  - rewrite !mem_equation. destruct ((fst r <=? b) && (b <? snd r)); reflexivity.
  - rewrite mem_equation. apply Z.ltb_ge in Hrange.
    destruct (fst r <=? b) eqn:Hlo; [|reflexivity].
    apply Z.leb_le in Hlo.
    assert (Hhi : (b <? snd r) = false) by (apply Z.ltb_ge; lia).
    now rewrite Hhi.
Qed.

Local Lemma wf_cons r rs :
  wf (r :: rs) <->
  fst r < snd r /\ wf rs /\ Forall (fun s => snd r < fst s) rs.
Proof.
  unfold wf. split.
  - intros [Hpositive Hsorted]. inversion Hpositive as [|? ? Hr Hrest]; subst.
    inversion Hsorted as [|? ? Hsort Hafter]; subst. intuition.
  - intros [Hr [[Hpositive Hsorted] Hafter]]. split; constructor; assumption.
Qed.

Local Lemma contains_cons r rs b :
  contains (r :: rs) b <-> fst r <= b < snd r \/ contains rs b.
Proof.
  unfold contains. cbn. split.
  - intros [s [[Heq|Hin] Hb]]; [subst s; now left|right; now exists s].
  - intros [Hb|[s [Hin Hb]]]; [exists r|exists s]; intuition.
Qed.

Local Lemma contains_after rs low b :
  Forall (fun r => low < fst r) rs -> contains rs b -> low < b.
Proof.
  intros Hlow [r [Hin Hb]]. rewrite Forall_forall in Hlow.
  specialize (Hlow r Hin). lia.
Qed.

Local Lemma head_lower r rs b :
  wf (r :: rs) -> contains (r :: rs) b -> fst r <= b.
Proof.
  intros Hwf Hb. apply wf_cons in Hwf as [Hr [_ Hafter]].
  apply contains_cons in Hb. destruct Hb as [Hb|Hb]; [lia|].
  pose proof (contains_after rs (snd r) b Hafter Hb). lia.
Qed.

Local Lemma head_end_absent r rs :
  wf (r :: rs) -> ~ contains (r :: rs) (snd r).
Proof.
  intros Hwf Hb. apply wf_cons in Hwf as [Hr [_ Hafter]].
  apply contains_cons in Hb. destruct Hb as [Hb|Hb]; [lia|].
  pose proof (contains_after rs (snd r) (snd r) Hafter Hb). lia.
Qed.

Local Lemma heads_equal r rs s ss :
  wf (r :: rs) -> wf (s :: ss) ->
  (forall b, contains (r :: rs) b <-> contains (s :: ss) b) -> r = s.
Proof.
  destruct r as [lo hi], s as [low high].
  intros Hr Hs Hequiv.
  pose proof Hr as Hrcons. pose proof Hs as Hscons.
  apply wf_cons in Hr as [Hpositive _].
  apply wf_cons in Hs as [Hpositive2 _]. cbn in Hpositive, Hpositive2.
  assert (Hlobyte : contains ((lo, hi) :: rs) lo).
  { apply contains_cons. left. cbn. lia. }
  assert (Hlowbyte : contains ((low, high) :: ss) low).
  { apply contains_cons. left. cbn. lia. }
  apply Hequiv in Hlobyte. apply Hequiv in Hlowbyte.
  pose proof (head_lower _ _ _ Hscons Hlobyte) as Hlowlo.
  pose proof (head_lower _ _ _ Hrcons Hlowbyte) as Hlolow. cbn in Hlowlo, Hlolow.
  assert (Heq : lo = low) by lia. subst low.
  assert (Hhi : hi = high).
  { destruct (Z.lt_trichotomy hi high) as [Hlt|[Heq|Hgt]]; [|exact Heq|].
    - exfalso. apply (head_end_absent _ _ Hrcons). apply Hequiv.
      apply contains_cons. left. cbn. lia.
    - exfalso. apply (head_end_absent _ _ Hscons). apply Hequiv.
      apply contains_cons. left. cbn. lia. }
  now subst high.
Qed.

Local Lemma lists_ext xs ys :
  wf xs -> wf ys -> (forall b, contains xs b <-> contains ys b) -> xs = ys.
Proof.
  revert ys. induction xs as [|r rs IH]; intros [|s ss] Hx Hy Hequiv;
    [reflexivity| | |].
  - apply wf_cons in Hy as [Hs _]. specialize (Hequiv (fst s)).
    assert (Hmember : contains (s :: ss) (fst s)).
    { apply contains_cons. left. lia. }
    apply Hequiv in Hmember. destruct Hmember as [q [Hin _]]. contradiction.
  - apply wf_cons in Hx as [Hr _]. specialize (Hequiv (fst r)).
    assert (Hmember : contains (r :: rs) (fst r)).
    { apply contains_cons. left. lia. }
    apply Hequiv in Hmember. destruct Hmember as [q [Hin _]]. contradiction.
  - assert (Heq : r = s) by (eapply heads_equal; eassumption). subst s.
    apply wf_cons in Hx as [Hr [Hrs Hafterr]].
    apply wf_cons in Hy as [_ [Hss Hafters]]. f_equal. apply IH; try assumption.
    intro b. specialize (Hequiv b). rewrite !contains_cons in Hequiv.
    pose proof (contains_after rs (snd r) b Hafterr) as Hrb.
    pose proof (contains_after ss (snd r) b Hafters) as Hsb.
    intuition lia.
Qed.

(** Well-formed sets with the same membership have identical canonical ranges. *)
Theorem ext xs ys :
  wf xs -> wf ys -> (forall b, mem xs b = mem ys b) -> xs = ys.
Proof.
  intros Hx Hy Hequiv. apply lists_ext; try assumption.
  intro b. rewrite <- !mem_spec, Hequiv. reflexivity.
Qed.

(** * Merge and coalesce *)

Local Fixpoint merge_c (xs ys : t) {struct xs} : Cost.t t :=
  match xs with
  | [] => Cost.ret ys
  | x :: xt =>
    (fix merge_right (zs : t) : Cost.t t :=
      match zs with
      | [] => Cost.ret (x :: xt)
      | y :: yt =>
        Cost.bind Cost.step (fun _ =>
          if fst x <=? fst y
          then Cost.map (cons x) (merge_c xt zs)
          else Cost.map (cons y) (merge_right yt))
      end) ys
  end.

Local Definition merge xs ys := Cost.value (merge_c xs ys).

Local Lemma merge_equation xs ys :
  merge xs ys =
  match xs, ys with
  | [], _ => ys
  | _, [] => xs
  | x :: xt, y :: yt =>
    if fst x <=? fst y then x :: merge xt ys else y :: merge xs yt
  end.
Proof.
  destruct xs as [|x xt], ys as [|y yt]; try reflexivity.
  change (Cost.value (Cost.bind Cost.step (fun _ =>
    if fst x <=? fst y then Cost.map (cons x) (merge_c xt (y :: yt))
    else Cost.map (cons y) (merge_c (x :: xt) yt))) =
    if fst x <=? fst y then x :: merge xt (y :: yt) else y :: merge (x :: xt) yt).
  rewrite Cost.value_bind.
  destruct (fst x <=? fst y); rewrite Cost.value_map; reflexivity.
Qed.

Local Lemma merge_in xs ys r :
  In r (merge xs ys) <-> In r xs \/ In r ys.
Proof.
  revert ys. induction xs as [|x xt IH]; intros ys.
  - rewrite merge_equation. cbn. tauto.
  - induction ys as [|y yt IHr].
    + rewrite merge_equation. cbn. tauto.
    + rewrite merge_equation. destruct (fst x <=? fst y).
      * cbn. rewrite IH. cbn. tauto.
      * cbn. rewrite IHr. cbn. tauto.
Qed.

Local Lemma merge_forall (P : range -> Prop) xs ys :
  Forall P xs -> Forall P ys -> Forall P (merge xs ys).
Proof.
  intros Hx Hy. rewrite Forall_forall in Hx, Hy |- *.
  intros r Hin. apply merge_in in Hin. destruct Hin; auto.
Qed.

Local Lemma wf_order rs :
  wf rs -> StronglySorted (fun r s => fst r <= fst s) rs.
Proof.
  induction rs as [|r rs IH]; intro Hwf; [constructor|].
  apply wf_cons in Hwf as [Hr [Hrest Hafter]]. constructor.
  - now apply IH.
  - rewrite Forall_forall in Hafter |- *. intros s Hin.
    specialize (Hafter s Hin). lia.
Qed.

Local Lemma merge_order xs ys :
  StronglySorted (fun r s => fst r <= fst s) xs ->
  StronglySorted (fun r s => fst r <= fst s) ys ->
  StronglySorted (fun r s => fst r <= fst s) (merge xs ys).
Proof.
  revert ys. induction xs as [|x xt IH]; intros ys Hx Hy.
  - rewrite merge_equation. exact Hy.
  - inversion Hx as [|? ? Hxt Hxa]; subst.
    induction ys as [|y yt IHr].
    + rewrite merge_equation. exact Hx.
    + inversion Hy as [|? ? Hyt Hya]; subst. rewrite merge_equation.
      destruct (fst x <=? fst y) eqn:Hxy.
      * apply Z.leb_le in Hxy. constructor.
        -- apply IH; assumption.
        -- apply merge_forall; [exact Hxa|constructor; [exact Hxy|]].
           rewrite Forall_forall in Hya |- *. intros r Hin. specialize (Hya r Hin). lia.
      * apply Z.leb_gt in Hxy. constructor.
        -- apply IHr. exact Hyt.
        -- apply merge_forall; [|exact Hya]. constructor; [lia|].
           rewrite Forall_forall in Hxa |- *. intros r Hin. specialize (Hxa r Hin). lia.
Qed.

Local Fixpoint coalesce_from_c (r : range) (rs : t) : Cost.t t :=
  match rs with
  | [] => Cost.ret [r]
  | s :: rest =>
    Cost.bind Cost.step (fun _ =>
      if snd r <? fst s then Cost.map (cons r) (coalesce_from_c s rest)
      else coalesce_from_c (fst r, Z.max (snd r) (snd s)) rest)
  end.

Local Definition coalesce_from r rs := Cost.value (coalesce_from_c r rs).

Local Lemma coalesce_from_equation r rs :
  coalesce_from r rs =
  match rs with
  | [] => [r]
  | s :: rest =>
    if snd r <? fst s then r :: coalesce_from s rest
    else coalesce_from (fst r, Z.max (snd r) (snd s)) rest
  end.
Proof.
  destruct rs as [|s rest]; [reflexivity|].
  change (Cost.value (Cost.bind Cost.step (fun _ =>
    if snd r <? fst s then Cost.map (cons r) (coalesce_from_c s rest)
    else coalesce_from_c (fst r, Z.max (snd r) (snd s)) rest)) =
    if snd r <? fst s then r :: coalesce_from s rest
    else coalesce_from (fst r, Z.max (snd r) (snd s)) rest).
  rewrite Cost.value_bind.
  destruct (snd r <? fst s); [rewrite Cost.value_map|]; reflexivity.
Qed.

Local Definition coalesce_c (rs : t) : Cost.t t :=
  match rs with
  | [] => Cost.ret []
  | r :: rest => Cost.bind Cost.step (fun _ => coalesce_from_c r rest)
  end.

Local Definition coalesce rs := Cost.value (coalesce_c rs).

Local Lemma coalesce_equation rs :
  coalesce rs = match rs with [] => [] | r :: rest => coalesce_from r rest end.
Proof.
  destruct rs; reflexivity.
Qed.

Local Lemma coalesce_lower rs r low :
  low <= fst r -> Forall (fun s => low <= fst s) rs ->
  Forall (fun s => low <= fst s) (coalesce_from r rs).
Proof.
  revert r low. induction rs as [|s rest IH]; intros r low Hr Hrs;
    rewrite coalesce_from_equation.
  - constructor; [exact Hr|constructor].
  - inversion Hrs as [|? ? Hs Hrest]; subst.
    destruct (snd r <? fst s).
    + constructor; [exact Hr|apply IH; assumption].
    + apply IH; assumption.
Qed.

Local Lemma coalesce_wf rs r :
  fst r < snd r -> Forall (fun s => fst s < snd s) rs ->
  StronglySorted (fun s t => fst s <= fst t) rs ->
  Forall (fun s => fst r <= fst s) rs -> wf (coalesce_from r rs).
Proof.
  revert r. induction rs as [|s rest IH]; intros r Hr Hpositive Hsort Hlower;
    rewrite coalesce_from_equation.
  - apply wf_cons. repeat split; try constructor; exact Hr.
  - inversion Hpositive as [|? ? Hs Hrest]; subst.
    inversion Hsort as [|? ? Hsortrest Hafter]; subst.
    inversion Hlower as [|? ? Hrs Hlowerrest]; subst.
    destruct (snd r <? fst s) eqn:Hgap.
    + apply Z.ltb_lt in Hgap. apply wf_cons. split; [exact Hr|]. split.
      * apply IH; assumption.
      * eapply Forall_impl; [|apply (coalesce_lower rest s (fst s)); [lia|exact Hafter]].
        cbn. intros q Hq. lia.
    + apply IH; try assumption; cbn; lia.
Qed.

Local Lemma contains_nil b : ~ contains [] b.
Proof.
  intros [r [Hin _]]. contradiction.
Qed.

Local Lemma coalesce_in rs r b :
  fst r < snd r -> Forall (fun s => fst s < snd s) rs ->
  StronglySorted (fun s t => fst s <= fst t) rs ->
  Forall (fun s => fst r <= fst s) rs ->
  (contains (coalesce_from r rs) b <-> fst r <= b < snd r \/ contains rs b).
Proof.
  revert r b. induction rs as [|s rest IH]; intros r b Hr Hpositive Hsort Hlower;
    rewrite coalesce_from_equation.
  - rewrite contains_cons. split; intros H; destruct H as [H|H];
      try (now left); try (exfalso; apply (contains_nil b); exact H).
  - inversion Hpositive as [|? ? Hs Hrest]; subst.
    inversion Hsort as [|? ? Hsortrest Hafter]; subst.
    inversion Hlower as [|? ? Hrs Hlowerrest]; subst.
    destruct (snd r <? fst s) eqn:Hgap.
    + rewrite contains_cons, (IH s b Hs Hrest Hsortrest Hafter), contains_cons. tauto.
    + apply Z.ltb_ge in Hgap.
      rewrite (IH (fst r, Z.max (snd r) (snd s)) b), contains_cons;
        try assumption; cbn; try lia.
      destruct (Z.max_spec (snd r) (snd s)) as [[Hle Hmax]|[Hle Hmax]];
        rewrite Hmax; intuition lia.
Qed.

(** Union merges sorted streams and coalesces overlapping or adjacent ranges. *)
Definition union_c (xs ys : t) : Cost.t t :=
  Cost.bind (merge_c xs ys) coalesce_c.
Definition union xs ys := Cost.value (union_c xs ys).
Arguments union _ _ : simpl never.

(** Union is coalescing after the sorted merge. *)
Theorem union_equation xs ys : union xs ys = coalesce (merge xs ys).
Proof.
  reflexivity.
Qed.

(** Union preserves canonicality for canonical inputs. *)
Theorem wf_union xs ys : wf xs -> wf ys -> wf (union xs ys).
Proof.
  intros Hx Hy. rewrite union_equation.
  assert (Hpositive : Forall (fun r => fst r < snd r) (merge xs ys)).
  { apply merge_forall; [exact (proj1 Hx)|exact (proj1 Hy)]. }
  assert (Hsort : StronglySorted (fun r s => fst r <= fst s) (merge xs ys)).
  { apply merge_order; apply wf_order; assumption. }
  destruct (merge xs ys) as [|r rest]; rewrite coalesce_equation.
  - split; constructor.
  - inversion Hpositive as [|? ? Hr Hrest]; subst.
    inversion Hsort as [|? ? Hsortrest Hafter]; subst.
    exact (coalesce_wf rest r Hr Hrest Hsortrest Hafter).
Qed.

(** Union contains exactly the integers contained in either canonical input. *)
Theorem mem_union xs ys b :
  wf xs -> wf ys -> mem (union xs ys) b = (mem xs b || mem ys b)%bool.
Proof.
  intros Hx Hy. apply Bool.eq_true_iff_eq.
  rewrite orb_true_iff, !mem_spec, union_equation.
  assert (Hpositive : Forall (fun r => fst r < snd r) (merge xs ys)).
  { apply merge_forall; [exact (proj1 Hx)|exact (proj1 Hy)]. }
  assert (Hsort : StronglySorted (fun r s => fst r <= fst s) (merge xs ys)).
  { apply merge_order; apply wf_order; assumption. }
  assert (Hbytes : contains (coalesce (merge xs ys)) b <-> contains (merge xs ys) b).
  { destruct (merge xs ys) as [|r rest]; [rewrite coalesce_equation; reflexivity|].
    inversion Hpositive as [|? ? Hr Hrest]; subst.
    inversion Hsort as [|? ? Hsortrest Hafter]; subst.
    rewrite coalesce_equation, coalesce_in, contains_cons; try reflexivity; assumption. }
  rewrite Hbytes. unfold contains. setoid_rewrite merge_in. firstorder.
Qed.

(** * Subtraction *)

Local Fixpoint cut_c (lo hi : Z) (tail : t) (finish : t -> Cost.t t) (ys : t)
    : Cost.t t :=
  match ys with
  | [] => Cost.ret ((lo, hi) :: tail)
  | (m, n) :: rest =>
    Cost.bind Cost.step (fun _ =>
      if n <=? lo then cut_c lo hi tail finish rest
      else if hi <=? m then Cost.map (cons (lo, hi)) (finish ys)
      else if m <=? lo then
        if hi <=? n then finish ys else cut_c n hi tail finish rest
      else Cost.map (cons (lo, m))
        (if hi <=? n then finish ys else cut_c n hi tail finish rest))
  end.

Local Definition cut lo hi tail finish ys := Cost.value (cut_c lo hi tail finish ys).

Local Lemma cut_equation lo hi tail finish ys :
  cut lo hi tail finish ys =
  match ys with
  | [] => (lo, hi) :: tail
  | (m, n) :: rest =>
    if n <=? lo then cut lo hi tail finish rest
    else if hi <=? m then (lo, hi) :: Cost.value (finish ys)
    else if m <=? lo then
      if hi <=? n then Cost.value (finish ys) else cut n hi tail finish rest
    else (lo, m) ::
      if hi <=? n then Cost.value (finish ys) else cut n hi tail finish rest
  end.
Proof.
  destruct ys as [|[m n] rest]; [reflexivity|].
  change (Cost.value (Cost.bind Cost.step (fun _ =>
    if n <=? lo then cut_c lo hi tail finish rest
    else if hi <=? m then Cost.map (cons (lo, hi)) (finish ((m, n) :: rest))
    else if m <=? lo then
      if hi <=? n then finish ((m, n) :: rest) else cut_c n hi tail finish rest
    else Cost.map (cons (lo, m))
      (if hi <=? n then finish ((m, n) :: rest) else cut_c n hi tail finish rest))) =
    if n <=? lo then cut lo hi tail finish rest
    else if hi <=? m then (lo, hi) :: Cost.value (finish ((m, n) :: rest))
    else if m <=? lo then
      if hi <=? n then Cost.value (finish ((m, n) :: rest)) else cut n hi tail finish rest
    else (lo, m) ::
      if hi <=? n then Cost.value (finish ((m, n) :: rest)) else cut n hi tail finish rest).
  rewrite Cost.value_bind.
  destruct (n <=? lo), (hi <=? m), (m <=? lo), (hi <=? n);
    try rewrite Cost.value_map; reflexivity.
Qed.

Local Fixpoint subtract_c (xs ys : t) {struct xs} : Cost.t t :=
  match xs with
  | [] => Cost.ret []
  | (lo, hi) :: tail =>
    Cost.bind Cost.step (fun _ => cut_c lo hi tail (subtract_c tail) ys)
  end.

Local Definition subtract xs ys := Cost.value (subtract_c xs ys).

Local Lemma subtract_equation xs ys :
  subtract xs ys =
  match xs with
  | [] => []
  | (lo, hi) :: tail => cut lo hi tail (subtract_c tail) ys
  end.
Proof.
  destruct xs as [|[lo hi] tail]; reflexivity.
Qed.

Local Lemma cut_lower ys lo hi tail finish low :
  low <= lo -> Forall (fun r => low <= fst r) tail ->
  (forall zs, Forall (fun r => low <= fst r) (Cost.value (finish zs))) ->
  Forall (fun r => low <= fst r) (cut lo hi tail finish ys).
Proof.
  revert lo hi tail finish low.
  induction ys as [|[m n] rest IH]; intros lo hi tail finish low Hlo Htail Hfinish;
    rewrite cut_equation.
  - constructor; assumption.
  - destruct (n <=? lo) eqn:Hnlo; [apply IH; assumption|].
    apply Z.leb_gt in Hnlo.
    destruct (hi <=? m); [constructor; [exact Hlo|apply Hfinish]|].
    destruct (m <=? lo), (hi <=? n); try apply Hfinish;
      try (apply IH; try assumption; lia);
      constructor; try exact Hlo; try apply Hfinish;
      apply IH; try assumption; lia.
Qed.

Local Lemma subtract_lower xs ys low :
  Forall (fun r => low <= fst r) xs ->
  Forall (fun r => low <= fst r) (subtract xs ys).
Proof.
  revert ys low. induction xs as [|[lo hi] tail IH]; intros ys low Hlower.
  - rewrite subtract_equation. constructor.
  - inversion Hlower as [|? ? Hlo Htail]; subst. rewrite subtract_equation.
    apply cut_lower; try assumption. intros zs. apply IH. exact Htail.
Qed.

Local Lemma cut_wf ys lo hi tail finish :
  wf ys -> lo < hi -> wf tail -> Forall (fun r => hi < fst r) tail ->
  (forall zs, wf zs -> wf (Cost.value (finish zs))) ->
  (forall zs, Forall (fun r => hi < fst r) (Cost.value (finish zs))) ->
  wf (cut lo hi tail finish ys).
Proof.
  revert lo hi tail finish.
  induction ys as [|[m n] rest IH]; intros lo hi tail finish Hys Hlo Htail Hafter Hfinish Hlow.
  - rewrite cut_equation. apply wf_cons. intuition.
  - pose proof Hys as Hysall. apply wf_cons in Hys as [Hmn [Hrest Hysafter]].
    cbn in Hmn. rewrite cut_equation.
    destruct (n <=? lo) eqn:Hnlo; [apply IH; assumption|].
    apply Z.leb_gt in Hnlo.
    destruct (hi <=? m) eqn:Hhim.
    + apply wf_cons. split; [exact Hlo|].
      split; [apply Hfinish; exact Hysall|apply Hlow].
    + apply Z.leb_gt in Hhim. destruct (m <=? lo) eqn:Hmlo.
      * destruct (hi <=? n) eqn:Hhin; [apply Hfinish; exact Hysall|].
        apply Z.leb_gt in Hhin. apply IH; assumption.
      * apply Z.leb_gt in Hmlo. apply wf_cons. split; [cbn; lia|].
        destruct (hi <=? n) eqn:Hhin.
        -- split; [apply Hfinish; exact Hysall|].
           eapply Forall_impl; [|apply Hlow]. cbn. intros r Hr. lia.
        -- apply Z.leb_gt in Hhin. split; [apply IH; assumption|].
           assert (Hbound : Forall (fun r => n <= fst r) (cut n hi tail finish rest)).
           { apply cut_lower; [lia| |].
             - eapply Forall_impl; [|exact Hafter]. cbn. intros r Hr. lia.
             - intros zs. eapply Forall_impl; [|apply Hlow]. cbn. intros r Hr. lia. }
           eapply Forall_impl; [|exact Hbound]. cbn. intros r Hr. lia.
Qed.

Local Lemma subtract_wf xs ys : wf xs -> wf ys -> wf (subtract xs ys).
Proof.
  revert ys. induction xs as [|[lo hi] tail IH]; intros ys Hxs Hys.
  - rewrite subtract_equation. split; constructor.
  - apply wf_cons in Hxs as [Hlo [Htail Hafter]]. cbn in Hlo, Hafter.
    rewrite subtract_equation. apply cut_wf; try assumption.
    + intros zs Hzs. apply IH; assumption.
    + intros zs. assert (Hlower : Forall (fun r => hi + 1 <= fst r) tail).
      { eapply Forall_impl; [|exact Hafter]. cbn. intros r Hr. lia. }
      pose proof (subtract_lower tail zs (hi + 1) Hlower) as Hresult.
      eapply Forall_impl; [|exact Hresult]. cbn. intros r Hr. lia.
Qed.

Local Lemma cut_in ys lo hi tail finish b :
  wf ys -> lo < hi -> Forall (fun r => hi < fst r) tail ->
  (forall zs, wf zs ->
    (contains (Cost.value (finish zs)) b <-> contains tail b /\ ~ contains zs b)) ->
  (contains (cut lo hi tail finish ys) b <->
    (lo <= b < hi \/ contains tail b) /\ ~ contains ys b).
Proof.
  revert lo hi tail finish b.
  induction ys as [|[m n] rest IH]; intros lo hi tail finish b Hys Hlo Hafter Hfinish.
  - rewrite cut_equation, contains_cons. cbn [fst snd].
    pose proof (contains_nil b). tauto.
  - pose proof Hys as Hysall. apply wf_cons in Hys as [Hmn [Hrest Hlater]].
    cbn in Hmn, Hlater.
    assert (Htailbyte : contains tail b -> hi < b).
    { apply contains_after. exact Hafter. }
    assert (Hrestbyte : contains rest b -> n < b).
    { apply contains_after. exact Hlater. }
    rewrite cut_equation. destruct (n <=? lo) eqn:Hnlo.
    + apply Z.leb_le in Hnlo.
      rewrite (IH lo hi tail finish b Hrest Hlo Hafter Hfinish), contains_cons.
      cbn [fst snd]. intuition lia.
    + apply Z.leb_gt in Hnlo. destruct (hi <=? m) eqn:Hhim.
      * apply Z.leb_le in Hhim.
        rewrite (contains_cons (lo, hi) (Cost.value (finish ((m, n) :: rest))) b),
          (Hfinish _ Hysall), (contains_cons (m, n) rest b).
        cbn [fst snd]. intuition lia.
      * apply Z.leb_gt in Hhim. destruct (m <=? lo) eqn:Hmlo.
        -- apply Z.leb_le in Hmlo. destruct (hi <=? n) eqn:Hhin.
           ++ apply Z.leb_le in Hhin. rewrite (Hfinish _ Hysall), contains_cons.
              cbn [fst snd]. intuition lia.
           ++ apply Z.leb_gt in Hhin.
              rewrite (IH n hi tail finish b Hrest Hhin Hafter Hfinish), contains_cons.
              cbn [fst snd]. intuition lia.
        -- apply Z.leb_gt in Hmlo. destruct (hi <=? n) eqn:Hhin.
           ++ apply Z.leb_le in Hhin.
              rewrite (contains_cons (lo, m) (Cost.value (finish ((m, n) :: rest))) b),
                (Hfinish _ Hysall), (contains_cons (m, n) rest b).
              cbn [fst snd]. intuition lia.
           ++ apply Z.leb_gt in Hhin.
              rewrite (contains_cons (lo, m) (cut n hi tail finish rest) b),
                (IH n hi tail finish b Hrest Hhin Hafter Hfinish),
                (contains_cons (m, n) rest b). cbn [fst snd].
              destruct (Z_lt_ge_dec b m); intuition lia.
Qed.

Local Lemma subtract_in xs ys b :
  wf xs -> wf ys ->
  (contains (subtract xs ys) b <-> contains xs b /\ ~ contains ys b).
Proof.
  revert ys b. induction xs as [|[lo hi] tail IH]; intros ys b Hxs Hys.
  - rewrite subtract_equation. pose proof (contains_nil b). tauto.
  - apply wf_cons in Hxs as [Hlo [Htail Hafter]].
    cbn in Hlo, Hafter. rewrite subtract_equation, cut_in, contains_cons;
      try assumption; try reflexivity. intros zs Hzs. now apply IH.
Qed.

(** Difference removes integers represented by the right input. *)
Definition diff_c xs ys := subtract_c xs ys.
Definition diff xs ys := Cost.value (diff_c xs ys).
Arguments diff _ _ : simpl never.

(** Difference uses the costed subtraction traversal. *)
Theorem diff_equation xs ys : diff xs ys = subtract xs ys.
Proof.
  reflexivity.
Qed.

(** Difference preserves canonicality for canonical inputs. *)
Theorem wf_diff xs ys : wf xs -> wf ys -> wf (diff xs ys).
Proof.
  rewrite diff_equation. apply subtract_wf.
Qed.

(** Difference contains exactly the left integers absent from the right. *)
Theorem mem_diff xs ys b :
  wf xs -> wf ys -> mem (diff xs ys) b = (mem xs b && negb (mem ys b))%bool.
Proof.
  intros Hx Hy. apply Bool.eq_true_iff_eq.
  rewrite andb_true_iff, negb_true_iff, <- not_true_iff_false, !mem_spec, diff_equation.
  now apply subtract_in.
Qed.

(** * Derived operations *)

(** Intersection retains the left integers not removed by the first difference. *)
Definition inter_c xs ys :=
  Cost.bind (diff_c xs ys) (fun removed => diff_c xs removed).
Definition inter xs ys := Cost.value (inter_c xs ys).
Arguments inter _ _ : simpl never.

(** Intersection is the difference of the left input and its difference from the right. *)
Theorem inter_equation xs ys : inter xs ys = diff xs (diff xs ys).
Proof.
  reflexivity.
Qed.

(** Intersection preserves canonicality for canonical inputs. *)
Theorem wf_inter xs ys : wf xs -> wf ys -> wf (inter xs ys).
Proof.
  intros Hx Hy. rewrite inter_equation. apply wf_diff; [exact Hx|].
  now apply wf_diff.
Qed.

(** Intersection contains exactly the integers present in both canonical inputs. *)
Theorem mem_inter xs ys b :
  wf xs -> wf ys -> mem (inter xs ys) b = (mem xs b && mem ys b)%bool.
Proof.
  intros Hx Hy. rewrite inter_equation, !mem_diff by (try assumption; now apply wf_diff).
  destruct (mem xs b), (mem ys b); reflexivity.
Qed.

(** Adding a range unions its singleton with the set. *)
Definition add_c r xs := Cost.bind (singleton_c r) (fun one => union_c one xs).
Definition add r xs := Cost.value (add_c r xs).
Arguments add _ _ : simpl never.

(** Adding a range agrees with union of its singleton and the original set. *)
Theorem add_equation r xs : add r xs = union (singleton r) xs.
Proof.
  reflexivity.
Qed.

(** Addition preserves canonicality when the original set is canonical. *)
Theorem wf_add r xs : wf xs -> wf (add r xs).
Proof.
  intro Hx. rewrite add_equation. apply wf_union; [apply wf_singleton|exact Hx].
Qed.

(** Addition includes exactly the original integers and those in the new range. *)
Theorem mem_add r xs b :
  wf xs -> mem (add r xs) b =
    (((fst r <=? b) && (b <? snd r)) || mem xs b)%bool.
Proof.
  intro Hx. rewrite add_equation, mem_union by (try assumption; apply wf_singleton).
  now rewrite mem_singleton.
Qed.

(** Removing a range subtracts its singleton from the set. *)
Definition remove_c r xs := Cost.bind (singleton_c r) (fun one => diff_c xs one).
Definition remove r xs := Cost.value (remove_c r xs).
Arguments remove _ _ : simpl never.

(** Removing a range agrees with difference against its singleton. *)
Theorem remove_equation r xs : remove r xs = diff xs (singleton r).
Proof.
  reflexivity.
Qed.

(** Removal preserves canonicality when the original set is canonical. *)
Theorem wf_remove r xs : wf xs -> wf (remove r xs).
Proof.
  intro Hx. rewrite remove_equation. apply wf_diff; [exact Hx|apply wf_singleton].
Qed.

(** Removal excludes precisely the integers in the half-open range. *)
Theorem mem_remove r xs b :
  wf xs -> mem (remove r xs) b =
    (mem xs b && negb ((fst r <=? b) && (b <? snd r)))%bool.
Proof.
  intro Hx. rewrite remove_equation, mem_diff by (try assumption; apply wf_singleton).
  now rewrite mem_singleton.
Qed.

(** The empty set contains no integer. *)
Theorem mem_empty b : mem empty b = false.
Proof.
  rewrite empty_equation, mem_equation. reflexivity.
Qed.

(** The returned elements preserve the original well-formed representation. *)
Theorem wf_elements xs : wf xs -> wf (elements xs).
Proof.
  rewrite elements_equation. auto.
Qed.

(** The returned elements represent exactly the same integers as the set. *)
Theorem mem_elements xs b : mem (elements xs) b = mem xs b.
Proof.
  rewrite elements_equation. reflexivity.
Qed.

(** A canonical set is empty exactly when it contains no integer. *)
Theorem is_empty_spec xs :
  wf xs -> (is_empty xs = true <-> forall b, mem xs b = false).
Proof.
  intro Hwf. destruct xs as [|r rest].
  - rewrite is_empty_equation. split; [intros _ b|intros _].
    + rewrite mem_equation. reflexivity.
    + reflexivity.
  - rewrite is_empty_equation. split; [discriminate|].
    intro Hempty. specialize (Hempty (fst r)).
    assert (Hmember : mem (r :: rest) (fst r) = true).
    { apply mem_spec, contains_cons. left.
      pose proof (proj1 (wf_cons r rest) Hwf) as [Hr _]. lia. }
    rewrite Hmember in Hempty. discriminate.
Qed.

(** A canonical nonempty set has an integer member. *)
Theorem nonempty_spec xs :
  wf xs -> (is_empty xs = false <-> exists b, mem xs b = true).
Proof.
  intro Hwf. destruct xs as [|r rest].
  - rewrite is_empty_equation. split; [discriminate|].
    intros [b Hfalse]. rewrite mem_equation in Hfalse. discriminate.
  - rewrite is_empty_equation. split; [intros _|intros _; reflexivity].
    exists (fst r). apply mem_spec, contains_cons. left.
    pose proof (proj1 (wf_cons r rest) Hwf) as [Hr _]. lia.
Qed.

(** Inclusion is emptiness of the difference. *)
Definition subset_c xs ys := Cost.bind (diff_c xs ys) is_empty_c.
Definition subset xs ys := Cost.value (subset_c xs ys).
Arguments subset _ _ : simpl never.

(** Inclusion checks the difference for emptiness. *)
Theorem subset_equation xs ys : subset xs ys = is_empty (diff xs ys).
Proof.
  unfold subset, subset_c, is_empty.
  rewrite Cost.value_bind. reflexivity.
Qed.

(** Inclusion holds exactly when every left member is a right member. *)
Theorem subset_spec xs ys :
  wf xs -> wf ys ->
  (subset xs ys = true <-> forall b, mem xs b = true -> mem ys b = true).
Proof.
  intros Hx Hy. rewrite subset_equation, is_empty_spec by now apply wf_diff.
  split; intros Hsubset b; specialize (Hsubset b); rewrite mem_diff in * by assumption.
  - destruct (mem xs b), (mem ys b); cbn in *; congruence.
  - destruct (mem xs b), (mem ys b); cbn in *; intuition discriminate.
Qed.

(** Coverage includes every empty or reversed query range. *)
Definition covers_c xs r := Cost.bind (singleton_c r) (fun one => subset_c one xs).
Definition covers xs r := Cost.value (covers_c xs r).
Arguments covers _ _ : simpl never.

(** Coverage checks inclusion of the query singleton. *)
Theorem covers_equation xs r : covers xs r = subset (singleton r) xs.
Proof.
  reflexivity.
Qed.

(** Coverage means every integer in the query range belongs to the set. *)
Theorem covers_spec xs r :
  wf xs -> (covers xs r = true <-> forall b, fst r <= b < snd r -> mem xs b = true).
Proof.
  intro Hx. rewrite covers_equation, subset_spec by (try assumption; apply wf_singleton).
  setoid_rewrite mem_singleton. setoid_rewrite andb_true_iff.
  setoid_rewrite Z.leb_le. setoid_rewrite Z.ltb_lt. reflexivity.
Qed.

(** Intersection queries test whether the query and set share an integer. *)
Definition intersects_c xs r :=
  Cost.bind (singleton_c r) (fun one =>
    Cost.bind (inter_c one xs) (fun shared =>
      Cost.map negb (is_empty_c shared))).
Definition intersects xs r := Cost.value (intersects_c xs r).
Arguments intersects _ _ : simpl never.

(** Intersection queries test nonemptiness of the query intersection. *)
Theorem intersects_equation xs r :
  intersects xs r = negb (is_empty (inter (singleton r) xs)).
Proof.
  unfold intersects, intersects_c, is_empty, inter, singleton.
  rewrite !Cost.value_bind, Cost.value_map. reflexivity.
Qed.

(** An intersection query succeeds exactly when it shares an integer with the set. *)
Theorem intersects_spec xs r :
  wf xs ->
  (intersects xs r = true <-> exists b, fst r <= b < snd r /\ mem xs b = true).
Proof.
  intro Hx. rewrite intersects_equation, negb_true_iff, nonempty_spec.
  - setoid_rewrite mem_inter; try assumption; try apply wf_singleton.
    setoid_rewrite mem_singleton. repeat setoid_rewrite andb_true_iff.
    setoid_rewrite Z.leb_le. setoid_rewrite Z.ltb_lt. firstorder.
  - apply wf_inter; [apply wf_singleton|exact Hx].
Qed.

Arguments empty_c : simpl never.
Arguments singleton_c _ : simpl never.
Arguments mem_c _ _ : simpl never.
Arguments is_empty_c _ : simpl never.
Arguments elements_c _ : simpl never.
Arguments union_c _ _ : simpl never.
Arguments diff_c _ _ : simpl never.
Arguments inter_c _ _ : simpl never.
Arguments add_c _ _ : simpl never.
Arguments remove_c _ _ : simpl never.
Arguments subset_c _ _ : simpl never.
Arguments covers_c _ _ : simpl never.
Arguments intersects_c _ _ : simpl never.

End IntervalSet.
