(** * Priority queues with a live-map reference

    The reference queue scans its live bindings to choose the least priority and code.
    For example, equal priorities pop in numeric encoded-key order.
    Builds on: BaseMap, BaseEncoding and BaseEq. *)

From Stdlib Require Import List Bool NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap.
Import List.ListNotations Cost.Notations.

Module Heap.

(** The reference queue stores only its live key-to-priority map. *)
Definition t K := Map.t K positive.

(** Queue well-formedness is the live map's canonical invariant. *)
Definition wf {K} (E : encoding K) (q : t K) := Map.wf E q.

(** Empty construction has the map's empty cost. *)
Definition empty_c {K} : Cost.t (t K) := Map.empty_c.

(** Empty queues have no live priorities. *)
Definition empty {K} : t K := Cost.value empty_c.

(** Priority lookup retains all encoding and map traversal costs. *)
Definition priority_c {K} (E : encoding K) k (q : t K) := Map.get_c E k q.

(** Priority lookup observes the live binding at the key. *)
Definition priority {K} (E : encoding K) k (q : t K) := Cost.value (priority_c E k q).

(** The reference size traverses the live map. *)
Definition size_c {K} (q : t K) := Map.size_c q.

(** Size counts live keys rather than insertion attempts. *)
Definition size {K} (q : t K) := Cost.value (size_c q).

(** Emptiness retains the map's constant-size test. *)
Definition is_empty_c {K} (q : t K) := Map.is_empty_c q.

(** Emptiness observes whether any key has a live priority. *)
Definition is_empty {K} (q : t K) := Cost.value (is_empty_c q).

(** Priority order uses numeric encoded codes to resolve equal priorities. *)
Definition before {K} (E : encoding K) p k r a :=
  (p < r)%positive \/ (p = r /\ (encode E k <= encode E a)%positive).

(** Priority ties charge both encodings and both code traversals before numeric comparison. *)
Definition beforeb_c {K} (E : encoding K) (x y : K * positive) : Cost.t bool :=
  if Pos.ltb (snd x) (snd y) then Cost.ret true
  else if Pos.eqb (snd x) (snd y) then
    Cost.step ;;
    let* cx := encode_c E (fst x) in
    Cost.step ;;
    let* cy := encode_c E (fst y) in
    Cost.tick_bits cx ;;
    Cost.tick_bits cy ;;
    Cost.ret (Pos.leb cx cy)
  else Cost.ret false.

(** The boolean order observes costed priority-and-code comparison. *)
Definition beforeb {K} (E : encoding K) x y := Cost.value (beforeb_c E x y).

Local Lemma beforeb_spec {K} (E : encoding K) (x y : K * positive) :
  beforeb E x y = true <-> before E (snd x) (fst x) (snd y) (fst y).
Proof.
  unfold beforeb, beforeb_c, before.
  destruct (Pos.ltb (snd x) (snd y)) eqn:Hlt.
  - apply Pos.ltb_lt in Hlt. cbn. intuition.
  - apply Pos.ltb_ge in Hlt.
    destruct (Pos.eqb (snd x) (snd y)) eqn:Heq.
    + apply Pos.eqb_eq in Heq. autorewrite with galois_cost.
      fold (encode E (fst x)) (encode E (fst y)).
      rewrite Pos.leb_le. intuition lia.
    + apply Pos.eqb_neq in Heq. cbn. intuition lia.
Qed.

Local Lemma before_refl {K} (E : encoding K) p k : before E p k p k.
Proof.
  right. split; [reflexivity|apply Pos.le_refl].
Qed.

Local Lemma before_trans {K} (E : encoding K) p k r a s b :
  before E p k r a -> before E r a s b -> before E p k s b.
Proof.
  unfold before. intros [Hpr|[Hpr Hka]] [Hrs|[Hrs Hab]];
    try (left; lia); right; split; lia.
Qed.

Local Lemma beforeb_false {K} (E : encoding K) (x y : K * positive) :
  beforeb E x y = false -> before E (snd y) (fst y) (snd x) (fst x).
Proof.
  intro Hfalse.
  assert (Hnot : ~ before E (snd x) (fst x) (snd y) (fst y)).
  { intro H. apply beforeb_spec in H. congruence. }
  unfold before in *. destruct (Pos.eq_dec (snd x) (snd y)); intuition lia.
Qed.

(** Selection visits every binding and retains the least priority-and-code pair. *)
Fixpoint pick_c {K} (E : encoding K) (xs : list (K * positive))
    : Cost.t (option (K * positive)) :=
  match xs with
  | [] => Cost.ret None
  | x :: rest =>
    Cost.step ;;
    let* tail := pick_c E rest in
    match tail with
    | None => Cost.ret (Some x)
    | Some y =>
      let* yes := beforeb_c E x y in Cost.ret (Some (if yes then x else y))
    end
  end.

(** Selection observes the costed live-binding scan. *)
Definition pick {K} (E : encoding K) xs := Cost.value (pick_c E xs).

Local Lemma pick_equation {K} (E : encoding K) x rest :
  pick E (x :: rest) =
  match pick E rest with
  | None => Some x
  | Some y => Some (if beforeb E x y then x else y)
  end.
Proof.
  unfold pick at 1. cbn [pick_c]. autorewrite with galois_cost.
  fold (pick E rest). destruct (pick E rest); reflexivity.
Qed.

Local Lemma pick_none {K} (E : encoding K) xs : pick E xs = None <-> xs = [].
Proof.
  destruct xs as [|x rest]; [split; reflexivity|].
  rewrite pick_equation. destruct (pick E rest); split; discriminate.
Qed.

Local Lemma pick_in {K} (E : encoding K) xs x : pick E xs = Some x -> In x xs.
Proof.
  induction xs as [|a rest IH]; [discriminate|]. rewrite pick_equation.
  destruct (pick E rest) as [b|] eqn:Hpick.
  - destruct (beforeb E a b); intro H; injection H as <-.
    + now left.
    + right. apply IH. reflexivity.
  - intro H. injection H as <-. now left.
Qed.

Local Lemma pick_min {K} (E : encoding K) xs x :
  pick E xs = Some x ->
  forall y, In y xs -> before E (snd x) (fst x) (snd y) (fst y).
Proof.
  revert x. induction xs as [|a rest IH]; intro x; [discriminate|].
  rewrite pick_equation.
  destruct (pick E rest) as [b|] eqn:Hpick.
  - destruct (beforeb E a b) eqn:Hab; intro H; injection H as <-.
    + intros y [<-|Hin]; [apply before_refl|].
      eapply before_trans; [apply beforeb_spec; exact Hab|].
      apply (IH b); [reflexivity|exact Hin].
    + intros y [<-|Hin].
      * apply beforeb_false. exact Hab.
      * apply (IH b); [reflexivity|exact Hin].
  - apply pick_none in Hpick. subst rest. intros H y [Heq|Hfalse]; [|contradiction].
    injection H as <-. subst y. apply before_refl.
Qed.

(** Push charges lookup and charges insertion only for a new or decreased priority. *)
Definition push_c {K} (E : encoding K) p k (q : t K) :=
  let* old := priority_c E k q in
  match old with
  | None => Map.set_c E k p q
  | Some r => if Pos.ltb p r then Map.set_c E k p q else Cost.ret q
  end.

(** Push observes the costed strict-decrease operation. *)
Definition push {K} (E : encoding K) p k (q : t K) := Cost.value (push_c E p k q).

(** Push retains the queue unchanged unless it inserts or strictly decreases a priority. *)
Theorem push_equation {K} (E : encoding K) p k (q : t K) :
  push E p k q =
  match priority E k q with
  | None => Map.set E k p q
  | Some r => if Pos.ltb p r then Map.set E k p q else q
  end.
Proof.
  unfold push, push_c. autorewrite with galois_cost.
  fold (priority E k q). destruct (priority E k q) as [r|]; [destruct (Pos.ltb p r)|];
    reflexivity.
Qed.

(** Pop charges enumeration, minimum selection and removal of the selected key. *)
Definition pop_c {K} (E : encoding K) (q : t K) : Cost.t (option (positive * K * t K)) :=
  let* xs := Map.elements_c q in
  let* selected := pick_c E xs in
  match selected with
  | None => Cost.ret None
  | Some (k, p) =>
    let* q' := Map.remove_c E k q in Cost.ret (Some (p, k, q'))
  end.

(** Successful pop returns the priority, key and queue with that key removed. *)
Definition pop {K} (E : encoding K) (q : t K) := Cost.value (pop_c E q).

(** Pop chooses from the live enumeration and removes exactly the chosen key. *)
Theorem pop_equation {K} (E : encoding K) (q : t K) :
  pop E q =
  match pick E (Map.elements q) with
  | None => None
  | Some (k, p) => Some (p, k, Map.remove E k q)
  end.
Proof.
  unfold pop, pop_c. autorewrite with galois_cost.
  fold (Map.elements q). fold (pick E (Map.elements q)).
  destruct (pick E (Map.elements q)) as [[k p]|]; reflexivity.
Qed.

(** Empty queues satisfy the invariant. *)
Theorem wf_empty {K} (E : encoding K) : wf E (@empty K).
Proof.
  apply Map.wf_empty.
Qed.

(** Empty queues have no live priority. *)
Theorem priority_empty {K} (E : encoding K) k : priority E k (@empty K) = None.
Proof.
  exact (Map.get_empty E k).
Qed.

(** Pushing keeps the smaller priority at its key and leaves other priorities unchanged. *)
Theorem priority_push {K} (E : encoding K) p k a (q : t K) :
  wf E q ->
  priority E a (push E p k q) =
  if eqb E a k then Some
    (match priority E k q with
    | None => p
    | Some r => Pos.min r p
    end)
  else priority E a q.
Proof.
  intro Hwf. rewrite push_equation.
  destruct (priority E k q) as [r|] eqn:Hget.
  - destruct (Pos.ltb p r) eqn:Hlt.
    + change (Map.get E a (Map.set E k p q) =
        if eqb E a k then Some (Pos.min r p) else Map.get E a q).
      rewrite Map.get_set by exact Hwf. apply Pos.ltb_lt in Hlt.
      rewrite Pos.min_r by lia. reflexivity.
    + apply Pos.ltb_ge in Hlt. rewrite Pos.min_l by lia.
      destruct (eqb E a k) eqn:Heq; [|reflexivity].
      rewrite eqb_equation in Heq. apply Pos.eqb_eq in Heq.
      change (Map.get E a q = Some r).
      rewrite Map.get_equation, Heq. exact Hget.
  - change (Map.get E a (Map.set E k p q) =
      if eqb E a k then Some p else Map.get E a q).
    rewrite Map.get_set by exact Hwf. reflexivity.
Qed.

(** Push maintains well-formedness. *)
Theorem wf_push {K} (E : encoding K) p k (q : t K) : wf E q -> wf E (push E p k q).
Proof.
  intro H. rewrite push_equation. destruct (priority E k q) as [r|];
    [destruct (Pos.ltb p r)|]; try exact H; apply Map.wf_set; exact H.
Qed.

(** Push changes the live size exactly on a previously absent key. *)
Theorem size_push {K} (E : encoding K) p k (q : t K) :
  wf E q -> size (push E p k q) =
  match priority E k q with
  | None => S (size q)
  | Some _ => size q
  end.
Proof.
  intro Hwf. rewrite push_equation. destruct (priority E k q) as [r|] eqn:Hget.
  - destruct (Pos.ltb p r); [|reflexivity].
    change (Map.size (Map.set E k p q) = Map.size q).
    rewrite Map.size_set by exact Hwf.
    change (Map.get E k q = Some r) in Hget. rewrite Hget. reflexivity.
  - change (Map.size (Map.set E k p q) = S (Map.size q)).
    rewrite Map.size_set by exact Hwf.
    change (Map.get E k q = None) in Hget. rewrite Hget. reflexivity.
Qed.

Local Lemma popped {K} (E : encoding K) (q q' : t K) p k :
  pop E q = Some (p, k, q') ->
  pick E (Map.elements q) = Some (k, p) /\ q' = Map.remove E k q.
Proof.
  rewrite pop_equation. destruct (pick E (Map.elements q)) as [[a r]|] eqn:Hpick;
    [|discriminate].
  intro H. injection H as -> -> ->. auto.
Qed.

(** A popped entry has exactly its live priority. *)
Theorem pop_priority {K} (E : encoding K) (HE : encoding_laws E) q q' p k :
  wf E q -> pop E q = Some (p, k, q') -> priority E k q = Some p.
Proof.
  intros Hwf Hpop. apply popped in Hpop as [Hpick _].
  apply (Map.elements_spec E HE k p q Hwf). exact (pick_in E _ _ Hpick).
Qed.

(** A popped pair is least by priority and then numeric encoded code among all live pairs. *)
Theorem pop_min {K} (E : encoding K) (HE : encoding_laws E) q q' p k :
  wf E q -> pop E q = Some (p, k, q') ->
  forall a r, priority E a q = Some r -> before E p k r a.
Proof.
  intros Hwf Hpop a r Hpriority. apply popped in Hpop as [Hpick _].
  apply (pick_min E _ (k, p) Hpick (a, r)).
  apply (Map.elements_spec E HE a r q Hwf). exact Hpriority.
Qed.

(** Pop clears the selected key and retains every other live priority. *)
Theorem pop_removes {K} (E : encoding K) q q' p k :
  pop E q = Some (p, k, q') ->
  forall a, priority E a q' =
    if eqb E a k then None else priority E a q.
Proof.
  intro H. apply popped in H as [_ ->]. intro a. apply Map.get_remove.
Qed.

(** Pop maintains well-formedness. *)
Theorem wf_pop {K} (E : encoding K) q q' p k :
  wf E q -> pop E q = Some (p, k, q') -> wf E q'.
Proof.
  intros Hwf Hpop. apply popped in Hpop as [_ ->]. now apply Map.wf_remove.
Qed.

(** Successful pop decreases the number of live keys by one. *)
Theorem size_pop {K} (E : encoding K) (HE : encoding_laws E) q q' p k :
  wf E q -> pop E q = Some (p, k, q') -> size q = S (size q').
Proof.
  intros Hwf Hpop. pose proof (pop_priority E HE _ _ _ _ Hwf Hpop) as Hpriority.
  apply popped in Hpop as [_ ->]. eapply Map.size_remove; eassumption.
Qed.

(** Pop returns none exactly on an empty live queue. *)
Theorem pop_none_empty {K} (E : encoding K) (HE : encoding_laws E) (q : t K) :
  wf E q -> (pop E q = None <-> is_empty q = true).
Proof.
  intro Hwf. rewrite pop_equation.
  assert (Hnone : (match pick E (Map.elements q) with
    | Some (k, p) => Some (p, k, Map.remove E k q)
    | None => None
    end = None) <-> Map.elements q = []).
  { rewrite <- (pick_none E (Map.elements q)).
    destruct (pick E (Map.elements q)) as [[k p]|]; split; congruence. }
  rewrite Hnone. change (Map.elements q = [] <-> Map.is_empty q = true).
  rewrite Map.is_empty_spec by exact Hwf. split.
  - intros Hempty k. destruct (Map.get E k q) as [p|] eqn:Hget; [|reflexivity].
    apply (Map.elements_spec E HE k p q Hwf) in Hget.
    rewrite Hempty in Hget. contradiction.
  - intro Hempty. destruct (Map.elements q) as [|[k p] rest] eqn:Hel; [reflexivity|].
    exfalso. assert (Hin : In (k, p) (Map.elements q)) by (rewrite Hel; now left).
    apply (Map.elements_spec E HE k p q Hwf) in Hin. rewrite Hempty in Hin. discriminate.
Qed.

Arguments empty_c {K} : simpl never.
Arguments empty {K} : simpl never.
Arguments priority_c {K} E k q : simpl never.
Arguments priority {K} E k q : simpl never.
Arguments size_c {K} q : simpl never.
Arguments size {K} q : simpl never.
Arguments is_empty_c {K} q : simpl never.
Arguments is_empty {K} q : simpl never.
Arguments push_c {K} E p k q : simpl never.
Arguments push {K} E p k q : simpl never.
Arguments pop_c {K} E q : simpl never.
Arguments pop {K} E q : simpl never.
Arguments beforeb_c {K} E x y : simpl never.
Arguments beforeb {K} E x y : simpl never.
Arguments pick_c {K} E xs : simpl never.
Arguments pick {K} E xs : simpl never.

End Heap.
