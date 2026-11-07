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

(** Emptiness is decided from the canonical list's first constructor. *)
Definition is_empty_c (rs : t) : Cost.t bool :=
  Cost.ret (match rs with [] => true | _ :: _ => false end).
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
  - unfold mem at 1. cbn [mem_c Cost.bind Cost.step Cost.tick Cost.value].
    destruct ((fst r <=? b) && (b <? snd r)); reflexivity.
Qed.

(** Emptiness checks whether the range list is empty. *)
Theorem is_empty_equation rs :
  is_empty rs = match rs with [] => true | _ :: _ => false end.
Proof.
  reflexivity.
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

End IntervalSet.
