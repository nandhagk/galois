(** * Persistent lazy-decrease priority queues

    A binomial forest indexes a live map and retains obsolete entries after decreases.
    For example, pushing one key at priorities five and two leaves only priority two live.
    Builds on: BaseHeapBinomial, BaseMap, BaseEncoding, BaseEq and CostLoop. *)

From Stdlib Require Import List Bool NArith PArith PeanoNat Lia.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseHeapBinomial BaseHeapBinomialCost
  BaseHeapLoop.
Import List.ListNotations Cost.Notations.

Local Open Scope nat_scope.

Module Heap.

(** The queue caches live cardinality and the number of pending forest entries. *)
Record t (K : Type) : Type := Queue {
  pending : HeapBinomial.heap K;
  live : Map.t K positive;
  live_count : nat;
  pending_count : nat
}.

Arguments Queue {K}.
Arguments pending {K}.
Arguments live {K}.
Arguments live_count {K}.
Arguments pending_count {K}.

(** Forest codes agree with stored keys and cover every live encoded binding.
    Coverage is by code so preservation does not require an injective dictionary. *)
Definition wf {K} (E : encoding K) (q : t K) : Prop :=
  HeapBinomial.forest_valid (fun e => snd (fst e) = encode E (snd e)) 0 (pending q) /\
  Map.wf E (live q) /\
  (forall k p, Map.get E k (live q) = Some p ->
    exists a, In (p, encode E k, a) (HeapBinomial.entries (pending q))) /\
  live_count q = Map.size (live q) /\
  pending_count q = HeapBinomial.heap_count (pending q).

(** Empty construction retains the Map constructor's charge. *)
Definition empty_c {K} : Cost.t (t K) :=
  let* m := Map.empty_c in Cost.ret (Queue [] m 0 0).
Definition empty {K} : t K := Cost.value empty_c.

(** Priority lookup retains the encoding and Map lookup charges. *)
Definition priority_c {K} (E : encoding K) k (q : t K) := Map.get_c E k (live q).
Definition priority {K} (E : encoding K) k (q : t K) := Cost.value (priority_c E k q).

(** Size reads the maintained live cardinality. *)
Definition size_c {K} (q : t K) := Cost.ret (live_count q).
Definition size {K} (q : t K) := Cost.value (size_c q).

(** Emptiness observes the live map even for raw queues with inconsistent counters. *)
Definition is_empty_c {K} (q : t K) := Map.is_empty_c (live q).
Definition is_empty {K} (q : t K) := Cost.value (is_empty_c q).

(** Priority order uses numeric encoded codes to resolve equal priorities. *)
Definition before {K} (E : encoding K) p k r a :=
  (p < r)%positive \/ (p = r /\ (encode E k <= encode E a)%positive).

(** Priority ties retain both encodings and both code traversal charges. *)
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
Definition beforeb {K} (E : encoding K) x y := Cost.value (beforeb_c E x y).

Local Definition enqueue_c {K} (E : encoding K) p k (q : t K) n : Cost.t (t K) :=
  Cost.step ;;
  let* c := encode_c E k in
  let* h := HeapBinomial.insert_c (HeapBinomial.Tree (p, c, k) []) (pending q) in
  let* m := Map.set_c E k p (live q) in
  Cost.ret (Queue h m n (S (pending_count q))).

(** Push adds a pending entry only for a new key or a strict priority decrease. *)
Definition push_c {K} (E : encoding K) p k (q : t K) :=
  let* old := priority_c E k q in
  match old with
  | None => enqueue_c E p k q (S (live_count q))
  | Some r =>
    Cost.step ;;
    if Pos.ltb p r then enqueue_c E p k q (live_count q) else Cost.ret q
  end.
Definition push {K} (E : encoding K) p k (q : t K) := Cost.value (push_c E p k q).

Local Definition inserted {K} (E : encoding K) p k (q : t K) n :=
  Queue (HeapBinomial.insert (HeapBinomial.Tree (p, encode E k, k) []) (pending q))
    (Map.set E k p (live q)) n (S (pending_count q)).

Local Lemma push_equation {K} (E : encoding K) p k (q : t K) :
  push E p k q =
  match priority E k q with
  | None => inserted E p k q (S (live_count q))
  | Some r => if Pos.ltb p r then inserted E p k q (live_count q) else q
  end.
Proof.
  unfold push, push_c. autorewrite with galois_cost. fold (priority E k q).
  destruct (priority E k q) as [r|]; [destruct (Pos.ltb p r)|];
    unfold enqueue_c, inserted; autorewrite with galois_cost; reflexivity.
Qed.

Local Lemma push_live {K} (E : encoding K) p k (q : t K) :
  live (push E p k q) =
  match priority E k q with
  | None => Map.set E k p (live q)
  | Some r => if Pos.ltb p r then Map.set E k p (live q) else live q
  end.
Proof.
  rewrite push_equation. destruct (priority E k q) as [r|];
    [destruct (Pos.ltb p r)|]; reflexivity.
Qed.

(** A pop state contains only the shrinking forest and its pending counter. *)
Definition pop_state K := (HeapBinomial.heap K * nat)%type.

(** A step removes one minimum and stops only on an empty forest or a live entry. *)
Definition pop_step_c {K} (E : encoding K) (m : Map.t K positive) n
    (s : pop_state K) : Cost.t (pop_state K + option (positive * K * t K)) :=
  let '(h, total) := s in
  let* removed := HeapBinomial.remove_min_c h in
  match removed with
  | None => Cost.ret (inr None)
  | Some ((p, c, k), rest) =>
    let* current := Map.get_c E k m in
    match current with
    | None => Cost.ret (inl (rest, Nat.pred total))
    | Some r =>
      Cost.step ;;
      if Pos.eqb p r then
        let* m' := Map.remove_c E k m in
        Cost.ret (inr (Some (p, k, Queue rest m' (Nat.pred n) (Nat.pred total))))
      else Cost.ret (inl (rest, Nat.pred total))
    end
  end.

(** Pop uses the public binary driver to discard at most all pending stale entries. *)
Definition pop_c {K} (E : encoding K) (q : t K) : Cost.t (option (positive * K * t K)) :=
  let* fuel := HeapBinomial.sufficient_fuel_c (pending q) in
  let* result := iterate (pop_step_c E (live q) (live_count q))
    fuel (pending q, pending_count q) in
  Cost.ret (match result with inl _ => None | inr r => r end).
Definition pop {K} (E : encoding K) (q : t K) := Cost.value (pop_c E q).

(** A step observes only the minimum, its live lookup and optional removal. *)
Theorem pop_step_equation {K} (E : encoding K) m n h total :
  Cost.value (pop_step_c E m n (h, total)) =
  match HeapBinomial.remove_min h with
  | None => inr None
  | Some ((p, c, k), rest) =>
    match Map.get E k m with
    | None => inl (rest, Nat.pred total)
    | Some r =>
      if Pos.eqb p r then
        inr (Some (p, k, Queue rest (Map.remove E k m) (Nat.pred n) (Nat.pred total)))
      else inl (rest, Nat.pred total)
    end
  end.
Proof.
  unfold pop_step_c. rewrite Cost.value_bind. fold (HeapBinomial.remove_min h).
  destruct (HeapBinomial.remove_min h) as [[[[p c] k] rest]|]; [|reflexivity].
  rewrite Cost.value_bind. fold (Map.get E k m).
  destruct (Map.get E k m) as [r|]; [|reflexivity].
  autorewrite with galois_cost. destruct (Pos.eqb p r); reflexivity.
Qed.

(** * Push contracts *)

(** Empty queues satisfy all forest, Map and counter invariants. *)
Theorem wf_empty {K} (E : encoding K) : wf E (@empty K).
Proof.
  split; [exact I|]; split; [apply Map.wf_empty|]; split.
  - intros k p Hget.
    change (Map.get E k (@Map.empty K positive) = Some p) in Hget.
    rewrite Map.get_empty in Hget. discriminate.
  - split; reflexivity.
Qed.

(** Empty queues have no live priorities. *)
Theorem priority_empty {K} (E : encoding K) k : priority E k (@empty K) = None.
Proof.
  exact (Map.get_empty E k).
Qed.

(** Pushing keeps the smaller priority at its key and leaves other priorities unchanged. *)
Theorem priority_push {K} (E : encoding K) p k a (q : t K) :
  wf E q ->
  priority E a (push E p k q) =
  if eqb E a k then Some
    (match priority E k q with None => p | Some r => Pos.min r p end)
  else priority E a q.
Proof.
  intro Hwf.
  change (Map.get E a (live (push E p k q)) =
    if eqb E a k then Some
      (match priority E k q with None => p | Some r => Pos.min r p end)
    else priority E a q).
  rewrite push_live.
  destruct (priority E k q) as [r|] eqn:Hget.
  - destruct (Pos.ltb p r) eqn:Hlt.
    + change (Map.get E a (Map.set E k p (live q)) =
        if eqb E a k then Some (Pos.min r p) else Map.get E a (live q)).
      rewrite Map.get_set by exact (proj1 (proj2 Hwf)).
      apply Pos.ltb_lt in Hlt. rewrite Pos.min_r by lia. reflexivity.
    + apply Pos.ltb_ge in Hlt. rewrite Pos.min_l by lia.
      destruct (eqb E a k) eqn:Heq; [|reflexivity].
      rewrite eqb_equation in Heq. apply Pos.eqb_eq in Heq.
      change (Map.get E a (live q) = Some r).
      rewrite Map.get_equation, Heq. exact Hget.
  - change (Map.get E a (Map.set E k p (live q)) =
      if eqb E a k then Some p else Map.get E a (live q)).
    rewrite Map.get_set by exact (proj1 (proj2 Hwf)). reflexivity.
Qed.

Local Lemma wf_inserted {K} (E : encoding K) p k (q : t K) n :
  wf E q -> n = Map.size (Map.set E k p (live q)) -> wf E (inserted E p k q n).
Proof.
  intros [Hforest [Hm [Hcover [Hlive Hpending]]]] Hn.
  unfold inserted. split.
  - apply HeapBinomial.valid_insert.
    + apply HeapBinomial.Valid_zero. reflexivity.
    + exact Hforest.
  - split; [apply Map.wf_set; exact Hm|]; split.
    + intros a v Hget. cbn [live pending] in *.
      rewrite Map.get_set in Hget by exact Hm.
      destruct (eqb E a k) eqn:Heq.
      * inversion Hget; subst v. exists k. apply HeapBinomial.entries_insert.
        left. rewrite eqb_equation in Heq. apply Pos.eqb_eq in Heq.
        rewrite Heq. cbn. auto.
      * destruct (Hcover a v Hget) as [b Hin].
        exists b. apply HeapBinomial.entries_insert. right. exact Hin.
    + split; [exact Hn|]. cbn [pending_count pending].
      rewrite HeapBinomial.count_insert. cbn [HeapBinomial.tree_entries length flat_map].
      rewrite Hpending. lia.
Qed.

(** Push maintains the forest and its live-map coverage without requiring injectivity. *)
Theorem wf_push {K} (E : encoding K) p k (q : t K) : wf E q -> wf E (push E p k q).
Proof.
  intro Hwf. rewrite push_equation.
  destruct (priority E k q) as [r|] eqn:Hget.
  - destruct (Pos.ltb p r); [|exact Hwf].
    apply wf_inserted; [exact Hwf|].
    rewrite Map.size_set by exact (proj1 (proj2 Hwf)).
    change (Map.get E k (live q) = Some r) in Hget. rewrite Hget.
    exact (proj1 (proj2 (proj2 (proj2 Hwf)))).
  - apply wf_inserted; [exact Hwf|].
    rewrite Map.size_set by exact (proj1 (proj2 Hwf)).
    change (Map.get E k (live q) = None) in Hget. rewrite Hget.
    f_equal. exact (proj1 (proj2 (proj2 (proj2 Hwf)))).
Qed.

(** Push changes the live size exactly on a previously absent encoded key. *)
Theorem size_push {K} (E : encoding K) p k (q : t K) :
  wf E q -> size (push E p k q) =
  match priority E k q with None => S (size q) | Some _ => size q end.
Proof.
  intro Hwf. rewrite push_equation.
  destruct (priority E k q) as [r|]; [destruct (Pos.ltb p r)|]; reflexivity.
Qed.

(** * Forest removal invariants *)

Local Lemma wf_drop {K} (E : encoding K) h m n total e rest m' n' :
  wf E (Queue h m n total) ->
  HeapBinomial.remove_min h = Some (e, rest) ->
  Map.wf E m' ->
  (forall a v, Map.get E a m' = Some v ->
    Map.get E a m = Some v /\
    forall b, (v, encode E a, b) <> e) ->
  n' = Map.size m' ->
  wf E (Queue rest m' n' (Nat.pred total)).
Proof.
  intros [Hforest [Hm [Hcover [Hn Htotal]]]] Hremove Hm' Hlookup Hn'.
  pose proof (HeapBinomial.remove_min_correct _ h Hforest) as Hheap.
  rewrite Hremove in Hheap.
  destruct Hheap as [Hcode [Hrest [Hin [Hcount Hmin]]]].
  split; [exact Hrest|]; split; [exact Hm'|]; split.
  - intros a v Hget. destruct (Hlookup a v Hget) as [Hold Hne].
    destruct (Hcover a v Hold) as [b Hcovered].
    exists b. apply Hin in Hcovered. destruct Hcovered as [Heq|Hinrest].
    + exfalso. apply (Hne b). exact Heq.
    + exact Hinrest.
  - split; [exact Hn'|]. cbn [pending_count pending].
    change (total = HeapBinomial.heap_count h) in Htotal.
    rewrite Htotal, Hcount. reflexivity.
Qed.

Local Lemma wf_skip {K} (E : encoding K) h p c k rest m n total :
  wf E (Queue h m n total) ->
  HeapBinomial.remove_min h = Some ((p, c, k), rest) ->
  Map.get E k m <> Some p -> wf E (Queue rest m n (Nat.pred total)).
Proof.
  intros Hwf Hremove Hstale.
  apply (wf_drop E h m n total (p, c, k) rest m n); try assumption.
  - exact (proj1 (proj2 Hwf)).
  - intros a v Hget. split; [exact Hget|]. intros b Heq.
    inversion Heq; subst v c b.
    pose proof (HeapBinomial.remove_min_correct _ h (proj1 Hwf)) as Hheap.
    rewrite Hremove in Hheap. cbn in Hheap.
    destruct Hheap as [Hcode _].
    apply Hstale. rewrite Map.get_equation in Hget |- *. rewrite <- Hcode. exact Hget.
  - exact (proj1 (proj2 (proj2 (proj2 Hwf)))).
Qed.

Local Lemma wf_take {K} (E : encoding K) h p c k rest m n total :
  wf E (Queue h m n total) ->
  HeapBinomial.remove_min h = Some ((p, c, k), rest) ->
  Map.get E k m = Some p ->
  wf E (Queue rest (Map.remove E k m) (Nat.pred n) (Nat.pred total)) /\
  n = S (Nat.pred n).
Proof.
  intros Hwf Hremove Hget.
  pose proof (Map.size_remove E k p m (proj1 (proj2 Hwf)) Hget) as Hsize.
  pose proof (proj1 (proj2 (proj2 (proj2 Hwf)))) as Hn. cbn in Hn.
  split; [|lia]. apply (wf_drop E h m n total (p, c, k) rest).
  - exact Hwf.
  - exact Hremove.
  - apply Map.wf_remove. exact (proj1 (proj2 Hwf)).
  - intros a v Hlookup. rewrite Map.get_remove in Hlookup.
    destruct (eqb E a k) eqn:Heq; [discriminate|].
    split; [exact Hlookup|]. intros b Hequal.
    inversion Hequal; subst v c b.
    pose proof (HeapBinomial.remove_min_correct _ h (proj1 Hwf)) as Hheap.
    rewrite Hremove in Hheap. destruct Hheap as [Hcode _]. cbn in Hcode.
    rewrite eqb_equation, <- Hcode, Pos.eqb_refl in Heq. discriminate.
  - lia.
Qed.

Local Definition pop_result {K} (E : encoding K) m n
    (result : option (positive * K * t K)) : Prop :=
  match result with
  | None => forall k, Map.get E k m = None
  | Some (p, k, rest) =>
    Map.get E k m = Some p /\
    (forall a v, Map.get E a m = Some v -> before E p k v a) /\
    live rest = Map.remove E k m /\ n = S (size rest) /\ wf E rest
  end.

Local Lemma empty_entries_live {K} (E : encoding K) h m n total :
  wf E (Queue h m n total) -> HeapBinomial.entries h = [] ->
  forall k, Map.get E k m = None.
Proof.
  intros [_ [_ [Hcover _]]] Hempty k.
  destruct (Map.get E k m) as [p|] eqn:Hget; [|reflexivity].
  destruct (Hcover k p Hget) as [a Hin]. cbn in Hin.
  rewrite Hempty in Hin. contradiction.
Qed.

Local Definition run_result {K} (E : encoding K) m n
    (result : pop_state K + option (positive * K * t K)) :=
  pop_result E m n (match result with inl _ => None | inr r => r end).

Local Lemma pop_runs_correct {K} (E : encoding K) fuel m n :
  forall h total result, wf E (Queue h m n total) -> total <= fuel ->
  runs (pop_step_c E m n) fuel (h, total) result -> run_result E m n result.
Proof.
  induction fuel as [|fuel IH]; intros h total result Hwf Hfuel Hrun.
  - inversion Hrun; subst. change (forall k, Map.get E k m = None).
    apply (empty_entries_live E h m n total Hwf).
    pose proof (proj2 (proj2 (proj2 (proj2 Hwf)))) as Hcount.
    cbn in Hcount. unfold HeapBinomial.heap_count in Hcount.
    apply length_zero_iff_nil. lia.
  - inversion Hrun as [|budget state r Hstop|budget state next final Hnext Htail]; subst.
    + rewrite pop_step_equation in Hstop.
      pose proof (HeapBinomial.remove_min_correct _ h (proj1 Hwf)) as Hheap.
      destruct (HeapBinomial.remove_min h) as [[[[p c] k] rest]|] eqn:Hremove.
      * destruct (Map.get E k m) as [v|] eqn:Hget; [|discriminate].
        destruct (Pos.eqb p v) eqn:Heq; [|discriminate].
        inversion Hstop; subst r. apply Pos.eqb_eq in Heq; subst v.
        destruct Hheap as [Hcode [Hrest [Hin [Hcount Hmin]]]].
        destruct (wf_take E h p c k rest m n total Hwf Hremove Hget) as [Hnew Hn].
        split; [exact Hget|]; split.
        -- intros a v Hvalue.
           destruct (proj1 (proj2 (proj2 Hwf)) a v Hvalue) as [b Hcovered].
           pose proof (Hmin (v, encode E a, b) Hcovered) as Hbefore.
           unfold HeapBinomial.precedes in Hbefore. cbn in Hcode, Hbefore.
           unfold before. rewrite <- Hcode. exact Hbefore.
        -- split; [reflexivity|]. split; assumption.
      * inversion Hstop; subst r. exact (empty_entries_live E h m n total Hwf Hheap).
    + rewrite pop_step_equation in Hnext.
      pose proof (HeapBinomial.remove_min_correct _ h (proj1 Hwf)) as Hheap.
      destruct (HeapBinomial.remove_min h) as [[[[p c] k] rest]|] eqn:Hremove;
        [|discriminate].
      destruct Hheap as [Hcode [Hrest [Hin [Hcount Hmin]]]].
      assert (Htotal : total = S (HeapBinomial.heap_count rest)).
      { rewrite <- Hcount. exact (proj2 (proj2 (proj2 (proj2 Hwf)))). }
      destruct (Map.get E k m) as [v|] eqn:Hget.
      * destruct (Pos.eqb p v) eqn:Heq; [discriminate|].
        inversion Hnext; subst next. apply (IH rest (Nat.pred total)).
        -- apply (wf_skip E h p c k rest m n total Hwf Hremove).
           rewrite Hget. intro Hequal. inversion Hequal; subst v.
           rewrite Pos.eqb_refl in Heq. discriminate.
        -- lia.
        -- exact Htail.
      * inversion Hnext; subst next. apply (IH rest (Nat.pred total)).
        -- apply (wf_skip E h p c k rest m n total Hwf Hremove).
           rewrite Hget. discriminate.
        -- lia.
        -- exact Htail.
Qed.

Local Lemma pop_correct {K} (E : encoding K) (q : t K) :
  wf E q -> pop_result E (live q) (size q) (pop E q).
Proof.
  intro Hwf. unfold pop, pop_c. autorewrite with galois_cost.
  fold (HeapBinomial.sufficient_fuel (pending q)).
  apply (pop_runs_correct E (Pos.to_nat (HeapBinomial.sufficient_fuel (pending q)))
    (live q) (live_count q) (pending q) (pending_count q)).
  - exact Hwf.
  - pose proof (HeapBinomial.sufficient_fuel_capacity _ _ (proj1 Hwf)) as Hcapacity.
    pose proof (proj2 (proj2 (proj2 (proj2 Hwf)))) as Hcount. lia.
  - apply iterate_value.
Qed.

(** * Pop contracts *)

(** A popped entry has its live priority. *)
Theorem pop_priority {K} (E : encoding K) (HE : encoding_laws E) q q' p k :
  wf E q -> pop E q = Some (p, k, q') -> priority E k q = Some p.
Proof.
  intros Hwf Hpop. pose proof (pop_correct E q Hwf) as H.
  rewrite Hpop in H. exact (proj1 H).
Qed.

(** A popped pair is least by priority and then numeric code among all live pairs. *)
Theorem pop_min {K} (E : encoding K) (HE : encoding_laws E) q q' p k :
  wf E q -> pop E q = Some (p, k, q') ->
  forall a r, priority E a q = Some r -> before E p k r a.
Proof.
  intros Hwf Hpop. pose proof (pop_correct E q Hwf) as H.
  rewrite Hpop in H. exact (proj1 (proj2 H)).
Qed.

Local Lemma pop_runs_live {K} (E : encoding K) fuel m n :
  forall s result, runs (pop_step_c E m n) fuel s result ->
  match result with
  | inl _ => True
  | inr None => True
  | inr (Some (p, k, q')) => live q' = Map.remove E k m
  end.
Proof.
  intros s result Hrun. induction Hrun as [s|budget s r Hstop|budget s next final Hnext Hr IH].
  - exact I.
  - destruct s as [h total]. rewrite pop_step_equation in Hstop.
    destruct (HeapBinomial.remove_min h) as [[[[p c] k] rest]|].
    + destruct (Map.get E k m) as [v|]; [|discriminate].
      destruct (Pos.eqb p v); [|discriminate]. inversion Hstop. reflexivity.
    + inversion Hstop. exact I.
  - exact IH.
Qed.

Local Lemma pop_live {K} (E : encoding K) q q' p k :
  pop E q = Some (p, k, q') -> live q' = Map.remove E k (live q).
Proof.
  unfold pop, pop_c. autorewrite with galois_cost.
  fold (HeapBinomial.sufficient_fuel (pending q)).
  pose proof (iterate_value (pop_step_c E (live q) (live_count q))
    (HeapBinomial.sufficient_fuel (pending q)) (pending q, pending_count q)) as Hrun.
  pose proof (pop_runs_live E _ _ _ _ _ Hrun) as Hlive.
  destruct (Cost.value (iterate _ _ _)) as [s|r]; [discriminate|].
  intro H. subst r. exact Hlive.
Qed.

(** Pop clears the selected encoded key and retains every other priority, even on raw queues. *)
Theorem pop_removes {K} (E : encoding K) q q' p k :
  pop E q = Some (p, k, q') ->
  forall a, priority E a q' = if eqb E a k then None else priority E a q.
Proof.
  intros Hpop a. unfold priority, priority_c.
  change (Map.get E a (live q') = if eqb E a k then None else Map.get E a (live q)).
  rewrite (pop_live E q q' p k Hpop). apply Map.get_remove.
Qed.

(** Pop maintains the forest, live-map coverage and both counters. *)
Theorem wf_pop {K} (E : encoding K) q q' p k :
  wf E q -> pop E q = Some (p, k, q') -> wf E q'.
Proof.
  intros Hwf Hpop. pose proof (pop_correct E q Hwf) as H.
  rewrite Hpop in H. exact (proj2 (proj2 (proj2 (proj2 H)))).
Qed.

(** Successful pop decreases the number of live keys by one. *)
Theorem size_pop {K} (E : encoding K) (HE : encoding_laws E) q q' p k :
  wf E q -> pop E q = Some (p, k, q') -> size q = S (size q').
Proof.
  intros Hwf Hpop. pose proof (pop_correct E q Hwf) as H.
  rewrite Hpop in H. exact (proj1 (proj2 (proj2 (proj2 H)))).
Qed.

(** Pop fails exactly when the live map is empty. *)
Theorem pop_none_empty {K} (E : encoding K) (HE : encoding_laws E) (q : t K) :
  wf E q -> (pop E q = None <-> is_empty q = true).
Proof.
  intro Hwf. pose proof (pop_correct E q Hwf) as Hcorrect.
  change (pop E q = None <-> Map.is_empty (live q) = true).
  rewrite Map.is_empty_spec by exact (proj1 (proj2 Hwf)).
  destruct (pop E q) as [[[p k] rest]|].
  - split; [discriminate|]. intro Hempty.
    specialize (Hempty k). cbn [pop_result] in Hcorrect. destruct Hcorrect as [Hget _].
    congruence.
  - split; [intro H; exact Hcorrect|intro H; reflexivity].
Qed.

(** * Persistent accounting *)

(** Staleness counts pending entries that exceed the live cardinality. *)
Definition stale {K} (q : t K) := pending_count q - live_count q.

(** The numeric operation constant includes the binary driver's descent overhead. *)
Definition heap_k : N := 64.

(** One stale entry carries enough credit for a minimum removal and its live lookup. *)
Definition heap_w (P : nat) (w : N) : N :=
  (32 * N.of_nat (S (Nat.log2 P)) * (1 + w))%N.

(** An operation has twice the credit carried by one stale entry. *)
Definition heap_cost (P : nat) (w : N) : N :=
  (heap_k * N.of_nat (S (Nat.log2 P)) * (1 + w))%N.

(** The stale-entry weight has the same binary-logarithm form for every pending cap. *)
Theorem heap_w_equation P w :
  heap_w P w = (32 * (1 + N.log2 (N.of_nat P)) * (1 + w))%N.
Proof.
  unfold heap_w. rewrite Nat2N.inj_succ, HeapLoop.log2_nat_N. lia.
Qed.

(** The operation budget uses the named constant and the binary logarithm of the pending cap. *)
Theorem heap_cost_equation P w :
  heap_cost P w = (heap_k * (1 + N.log2 (N.of_nat P)) * (1 + w))%N.
Proof.
  unfold heap_cost. rewrite Nat2N.inj_succ, HeapLoop.log2_nat_N. lia.
Qed.

(** A fixed pending bound gives a branch-local potential for persistent operations. *)
Definition heap_potential {K} P w (q : t K) : N :=
  (N.of_nat (stale q) * heap_w P w)%N.

(** Width duties cover the finite pending entries and retain their encoder charges. *)
Definition key_budget {K} (E : encoding K) w (q : t K) : Prop :=
  forall e, In e (HeapBinomial.entries (pending q)) ->
    (Cost.ticks (encode_c E (snd e)) <= w /\
      N.pos (Pos.size (snd (fst e))) <= w)%N.

(** Push's accounting retains every reached callee, including the separately cached code. *)
Theorem push_callee_cost {K} (E : encoding K) p k (q : t K) :
  Cost.ticks (push_c E p k q) =
  (Cost.ticks (Map.get_c E k (live q)) +
    match priority E k q with
    | None =>
      1 + Cost.ticks (encode_c E k) +
      Cost.ticks (HeapBinomial.insert_c (HeapBinomial.Tree (p, encode E k, k) []) (pending q)) +
      Cost.ticks (Map.set_c E k p (live q))
    | Some r =>
      1 + if Pos.ltb p r then
        1 + Cost.ticks (encode_c E k) +
        Cost.ticks (HeapBinomial.insert_c
          (HeapBinomial.Tree (p, encode E k, k) []) (pending q)) +
        Cost.ticks (Map.set_c E k p (live q))
      else 0
    end)%N.
Proof.
  unfold push_c. rewrite Cost.ticks_bind. fold (priority E k q).
  destruct (priority E k q) as [r|].
  - autorewrite with galois_cost. destruct (Pos.ltb p r).
    + unfold enqueue_c. autorewrite with galois_cost. fold (encode E k).
      unfold priority_c. lia.
    + autorewrite with galois_cost. unfold priority_c. reflexivity.
  - unfold enqueue_c. autorewrite with galois_cost. fold (encode E k).
    unfold priority_c. lia.
Qed.

Local Lemma numeric_insert_cost {K} (E : encoding K) p k (q : t K) w :
  key_budget E w q ->
  (N.pos (Pos.size (encode E k)) <= w)%N ->
  (Cost.ticks (HeapBinomial.insert_c
      (HeapBinomial.Tree (p, encode E k, k) []) (pending q)) <=
    (N.of_nat (length (pending q)) + 1) * (2 + 2 * w))%N.
Proof.
  intros Hbudget Hkey. apply HeapBinomialCost.insert_cost.
  - intros e Hin. cbn in Hin. destruct Hin as [<-|Hfalse]; [exact Hkey|contradiction].
  - intros e Hin. exact (proj2 (Hbudget e Hin)).
Qed.

(** Push's worst-case bound includes the new key's encoder and its actual encoded width. *)
Theorem push_cost_worst {K} (E : encoding K) (laws : Map.cost_laws) p k q P w :
  wf E q -> key_budget E w q -> pending_count q < P ->
  (Cost.ticks (encode_c E k) <= w)%N ->
  (N.pos (Pos.size (encode E k)) <= w)%N ->
  (Cost.ticks (push_c E p k q) <= heap_w P w)%N.
Proof.
  intros Hwf Hbudget HP Hencode Hbits.
  pose proof (numeric_insert_cost E p k q w Hbudget Hbits) as Hinsert.
  pose proof (HeapBinomial.forest_width _ (pending q) (proj1 Hwf)) as Hwidth.
  pose proof (proj2 (proj2 (proj2 (proj2 Hwf)))) as Hcount.
  pose proof (Nat.log2_le_mono (pending_count q) P ltac:(lia)) as Hlog.
  assert (HwidthN : (N.of_nat (length (pending q)) <= N.of_nat (S (Nat.log2 P)))%N).
  { rewrite <- Hcount in Hwidth. lia. }
  rewrite push_callee_cost, Map.get_cost.
  destruct (priority E k q) as [r|]; [destruct (Pos.ltb p r)|];
    rewrite ?Map.set_cost; unfold heap_w; rewrite Nat2N.inj_succ in *; nia.
Qed.

(** A push adds at most one stale entry, independently of the queue's raw counters. *)
Theorem stale_push {K} (E : encoding K) p k (q : t K) :
  stale (push E p k q) <= S (stale q).
Proof.
  rewrite push_equation. destruct (priority E k q) as [r|].
  - destruct (Pos.ltb p r).
    + change (S (pending_count q) - live_count q <=
        S (pending_count q - live_count q)). lia.
    + unfold stale. lia.
  - change (S (pending_count q) - S (live_count q) <=
      S (pending_count q - live_count q)). lia.
Qed.

(** Push pays for both its primitive work and any newly created stale-entry credit. *)
Theorem push_cost {K} (E : encoding K) (laws : Map.cost_laws) p k q P w :
  wf E q -> key_budget E w q -> pending_count q < P ->
  (Cost.ticks (encode_c E k) <= w)%N ->
  (N.pos (Pos.size (encode E k)) <= w)%N ->
  (Cost.ticks (push_c E p k q) + heap_potential P w (push E p k q) <=
    heap_cost P w + heap_potential P w q)%N.
Proof.
  intros Hwf Hbudget HP Hencode Hbits.
  pose proof (push_cost_worst E laws p k q P w Hwf Hbudget HP Hencode Hbits).
  pose proof (stale_push E p k q).
  assert (Hstale : (N.of_nat (stale (push E p k q)) <= N.of_nat (stale q) + 1)%N)
    by lia.
  unfold heap_potential, heap_cost, heap_k, heap_w in *. nia.
Qed.

(** Live coverage bounds the live cardinality by the number of pending entries. *)
Theorem live_pending_bound {K} (E : encoding K) (HE : encoding_laws E) q :
  wf E q -> live_count q <= pending_count q.
Proof.
  intro Hwf.
  pose proof (Map.size_support_bound E HE
    (List.map (@snd (positive * positive) K) (HeapBinomial.entries (pending q)))
    (live q) (proj1 (proj2 Hwf))) as Hbound.
  assert (Hsupport : forall k p, Map.get E k (live q) = Some p ->
    In k (List.map (@snd (positive * positive) K) (HeapBinomial.entries (pending q)))).
  { intros k p Hget.
    destruct (proj1 (proj2 (proj2 Hwf)) k p Hget) as [a Hin].
    pose proof (HeapBinomial.forest_all _ _ _ (proj1 Hwf) _ Hin) as Hcode.
    cbn in Hcode. apply (encode_injective HE) in Hcode. subst a.
    apply in_map_iff. exists (p, encode E k, k). split; [reflexivity|exact Hin]. }
  specialize (Hbound Hsupport). rewrite length_map in Hbound.
  destruct Hwf as [_ [_ [_ [Hlive Hpending]]]].
  rewrite Hlive, Hpending. exact Hbound.
Qed.

(** Every pop step retains the costs of its reached Map callees and minimum removal. *)
Theorem pop_step_callee_cost {K} (E : encoding K) m n h total :
  Cost.ticks (pop_step_c E m n (h, total)) =
  (Cost.ticks (HeapBinomial.remove_min_c h) +
    match HeapBinomial.remove_min h with
    | None => 0
    | Some ((p, c, k), rest) =>
      Cost.ticks (Map.get_c E k m) +
      match Map.get E k m with
      | None => 0
      | Some r => 1 + if Pos.eqb p r then Cost.ticks (Map.remove_c E k m) else 0
      end
    end)%N.
Proof.
  unfold pop_step_c. rewrite Cost.ticks_bind. fold (HeapBinomial.remove_min h).
  destruct (HeapBinomial.remove_min h) as [[[[p c] k] rest]|];
    [|rewrite Cost.ticks_ret; reflexivity].
  rewrite Cost.ticks_bind. fold (Map.get E k m).
  destruct (Map.get E k m) as [r|]; autorewrite with galois_cost; [|lia].
  destruct (Pos.eqb p r); autorewrite with galois_cost; lia.
Qed.

Local Lemma key_budget_drop {K} (E : encoding K) w h m n total e rest :
  wf E (Queue h m n total) -> key_budget E w (Queue h m n total) ->
  HeapBinomial.remove_min h = Some (e, rest) ->
  key_budget E w (Queue rest m n (Nat.pred total)).
Proof.
  intros Hwf Hbudget Hremove a Hin.
  pose proof (HeapBinomial.remove_min_correct _ h (proj1 Hwf)) as Hheap.
  rewrite Hremove in Hheap. destruct Hheap as [_ [_ [Hentries _]]].
  apply Hbudget. apply Hentries. right. exact Hin.
Qed.

Local Lemma pop_step_numeric {K} (E : encoding K) h m n total P w :
  wf E (Queue h m n total) -> key_budget E w (Queue h m n total) -> total <= P ->
  (Cost.ticks (pop_step_c E m n (h, total)) + 2 <= heap_w P w)%N.
Proof.
  intros Hwf Hbudget HP.
  pose proof (HeapBinomialCost.remove_min_cost _ w h (proj1 Hwf)
    ltac:(intros e Hin; exact (proj2 (Hbudget e Hin)))) as Hremove.
  pose proof (proj2 (proj2 (proj2 (proj2 Hwf)))) as Hcount. cbn in Hcount.
  change (total = HeapBinomial.heap_count h) in Hcount.
  pose proof (Nat.log2_le_mono total P HP) as Hlog.
  assert (HL : (N.of_nat (S (Nat.log2 (HeapBinomial.heap_count h))) <=
    N.of_nat (S (Nat.log2 P)))%N) by (rewrite <- Hcount; lia).
  rewrite pop_step_callee_cost.
  pose proof (HeapBinomial.remove_min_correct _ h (proj1 Hwf)) as Hheap.
  destruct (HeapBinomial.remove_min h) as [[[[p c] k] rest]|] eqn:Hremoved.
  - destruct Hheap as [Hcode [_ [Hin _]]]. cbn in Hcode.
    assert (Hentry : In (p, c, k) (HeapBinomial.entries h)) by (apply Hin; left; reflexivity).
    destruct (Hbudget _ Hentry) as [Hencode Hbits]. cbn in Hencode, Hbits.
    rewrite Hcode in Hbits.
    rewrite Map.get_cost. destruct (Map.get E k m) as [r|]; [destruct (Pos.eqb p r)|];
      rewrite ?Map.remove_cost; unfold heap_w; rewrite Nat2N.inj_succ in *; nia.
  - unfold heap_w. rewrite Nat2N.inj_succ in *. nia.
Qed.

Local Definition pop_state_potential n P w {K} (s : pop_state K) : N :=
  (N.of_nat (snd s - n) * heap_w P w)%N.

(** A stopped pop retains the returned queue's potential and has zero potential on failure. *)
Definition pop_output_potential P w {K} (r : option (positive * K * t K)) : N :=
  match r with
  | None => 0%N
  | Some (_, _, q) => heap_potential P w q
  end.

Local Lemma pop_step_credit {K} (E : encoding K) (HE : encoding_laws E) m n P w :
  forall s : pop_state K,
  let '(h, total) := s in
  wf E (Queue h m n total) /\ key_budget E w (Queue h m n total) /\ total <= P ->
  match Cost.value (pop_step_c E m n s) with
  | inl s' =>
    (let '(h', total') := s' in
      wf E (Queue h' m n total') /\ key_budget E w (Queue h' m n total') /\ total' <= P) /\
    (Cost.ticks (pop_step_c E m n s) + pop_state_potential n P w s' + 2 <=
      pop_state_potential n P w s)%N
  | inr r =>
    (Cost.ticks (pop_step_c E m n s) + pop_output_potential P w r <=
      heap_w P w + pop_state_potential n P w s)%N
  end.
Proof.
  intros [h total] [Hwf [Hbudget HP]].
  pose proof (pop_step_numeric E h m n total P w Hwf Hbudget HP) as Hcost.
  rewrite pop_step_equation.
  pose proof (HeapBinomial.remove_min_correct _ h (proj1 Hwf)) as Hheap.
  destruct (HeapBinomial.remove_min h) as [[[[p c] k] rest]|] eqn:Hremove.
  - destruct Hheap as [_ [_ [_ [Hcount _]]]].
    pose proof (proj2 (proj2 (proj2 (proj2 Hwf)))) as Htotal. cbn in Htotal.
    change (total = HeapBinomial.heap_count h) in Htotal.
    assert (Hpositive : 0 < total) by lia.
    pose proof (key_budget_drop E w h m n total (p, c, k) rest Hwf Hbudget Hremove)
      as Hbudget'.
    destruct (Map.get E k m) as [v|] eqn:Hget.
    + destruct (Pos.eqb p v) eqn:Heq.
      * apply Pos.eqb_eq in Heq; subst v.
        destruct (wf_take E h p c k rest m n total Hwf Hremove Hget) as [_ Hn].
        unfold pop_output_potential, heap_potential, stale, pop_state_potential.
        cbn [pending_count live_count snd].
        assert (Hsame : Nat.pred total - Nat.pred n = total - n) by lia.
        rewrite Hsame. nia.
      * assert (Hstale : Map.get E k m <> Some p).
        { rewrite Hget. intro Hbad. inversion Hbad; subst v.
          rewrite Pos.eqb_refl in Heq. discriminate. }
        pose proof (wf_skip E h p c k rest m n total Hwf Hremove Hstale) as Hnext.
        pose proof (live_pending_bound E HE _ Hnext) as Hbound. cbn in Hbound.
        split; [split; [exact Hnext|]; split; [exact Hbudget'|lia]|].
        unfold pop_state_potential. cbn [snd].
        assert (Hdrop : (N.of_nat (total - n) = N.of_nat (Nat.pred total - n) + 1)%N)
          by lia.
        rewrite Hdrop. nia.
    + assert (Hstale : Map.get E k m <> Some p) by (rewrite Hget; discriminate).
      pose proof (wf_skip E h p c k rest m n total Hwf Hremove Hstale) as Hnext.
      pose proof (live_pending_bound E HE _ Hnext) as Hbound. cbn in Hbound.
      split; [split; [exact Hnext|]; split; [exact Hbudget'|lia]|].
      unfold pop_state_potential. cbn [snd].
      assert (Hdrop : (N.of_nat (total - n) = N.of_nat (Nat.pred total - n) + 1)%N) by lia.
      rewrite Hdrop. nia.
  - cbn [pop_output_potential]. nia.
Qed.

Local Lemma positive_size_log p :
  Pos.to_nat (Pos.size p) = S (Nat.log2 (Pos.to_nat p)).
Proof.
  induction p as [p IH|p IH|].
  - cbn [Pos.size]. rewrite Pos2Nat.inj_succ, IH, Pos2Nat.inj_xI.
    replace (S (2 * Pos.to_nat p)) with (2 * Pos.to_nat p + 1) by lia.
    rewrite Nat.log2_succ_double by apply Pos2Nat.is_pos. reflexivity.
  - cbn [Pos.size]. rewrite Pos2Nat.inj_succ, IH, Pos2Nat.inj_xO.
    rewrite Nat.log2_double by apply Pos2Nat.is_pos. reflexivity.
  - reflexivity.
Qed.

Local Lemma pop_fuel_width total P :
  total <= P ->
  (N.pos (Pos.size (Pos.of_nat (S total))) <=
    2 * N.of_nat (S (Nat.log2 P)))%N.
Proof.
  intro HP.
  pose proof (positive_size_log (Pos.of_nat (S total))) as Hsize.
  rewrite Nat2Pos.id in Hsize by lia.
  pose proof (Nat.log2_succ_le total) as Hsucc.
  pose proof (Nat.log2_le_mono total P HP) as Hlog.
  assert (HsizeN : N.pos (Pos.size (Pos.of_nat (S total))) =
    N.of_nat (S (Nat.log2 (S total)))).
  { apply N2Nat.inj. rewrite Nat2N.id. exact Hsize. }
  rewrite HsizeN. lia.
Qed.

(** Pop refunds the returned queue's potential and pays binary descent at its actual fuel width. *)
Theorem pop_cost_credit {K} (E : encoding K) (HE : encoding_laws E) q P w :
  wf E q -> key_budget E w q -> pending_count q <= P ->
  (Cost.ticks (pop_c E q) + pop_output_potential P w (pop E q) <=
    Cost.ticks (HeapBinomial.sufficient_fuel_c (pending q)) +
    heap_w P w + heap_potential P w q +
    N.pos (Pos.size (HeapBinomial.sufficient_fuel (pending q))))%N.
Proof.
  intros Hwf Hbudget HP.
  pose proof (HeapLoop.iterate_credit (pop_step_c E (live q) (live_count q))
    (fun s => let '(h, total) := s in
      wf E (Queue h (live q) (live_count q) total) /\
      key_budget E w (Queue h (live q) (live_count q) total) /\ total <= P)
    (pop_state_potential (live_count q) P w) (pop_output_potential P w) (heap_w P w)
    ltac:(intros [h total] Hlocal;
      exact (pop_step_credit E HE (live q) (live_count q) P w (h, total) Hlocal))
    (HeapBinomial.sufficient_fuel (pending q)) (pending q, pending_count q)) as Hcredit.
  assert (Hinitial :
    wf E (Queue (pending q) (live q) (live_count q) (pending_count q)) /\
    key_budget E w (Queue (pending q) (live q) (live_count q) (pending_count q)) /\
    pending_count q <= P) by (destruct q; auto).
  specialize (Hcredit Hinitial).
  unfold pop_c, pop. autorewrite with galois_cost.
  unfold pop_c. autorewrite with galois_cost.
  fold (HeapBinomial.sufficient_fuel (pending q)).
  unfold HeapLoop.potential in Hcredit.
  destruct (Cost.value (iterate _ _ _)) as [s|r].
  - cbn [pop_output_potential] in *. unfold heap_potential, stale, pop_state_potential in *.
    cbn [snd] in *. nia.
  - unfold heap_potential, stale, pop_state_potential in *. cbn [snd] in *. lia.
Qed.

(** Fuel construction and binary descent together remain logarithmic in the pending cap. *)
Theorem pop_fuel_cost {K} (E : encoding K) (q : t K) P :
  wf E q -> pending_count q <= P ->
  (Cost.ticks (HeapBinomial.sufficient_fuel_c (pending q)) +
    N.pos (Pos.size (HeapBinomial.sufficient_fuel (pending q))) <=
    3 * N.of_nat (S (Nat.log2 P)))%N.
Proof.
  intros Hwf HP.
  pose proof (HeapBinomial.forest_width _ _ (proj1 Hwf)) as Hwidth.
  pose proof (proj2 (proj2 (proj2 (proj2 Hwf)))) as Hcount.
  pose proof (Nat.log2_le_mono (pending_count q) P HP) as Hlog.
  rewrite <- Hcount in Hwidth.
  rewrite HeapBinomial.sufficient_fuel_cost, HeapBinomial.sufficient_fuel_width.
  assert (HwidthN : (N.of_nat (length (pending q)) <= N.of_nat (S (Nat.log2 P)))%N)
    by lia.
  rewrite !Nat2N.inj_succ in *. nia.
Qed.

(** Pop's amortised bound holds for every caller-chosen pending cap on every persistent branch. *)
Theorem pop_cost {K} (E : encoding K) (HE : encoding_laws E) (laws : Map.cost_laws) q P w :
  wf E q -> key_budget E w q -> pending_count q <= P ->
  (Cost.ticks (pop_c E q) + pop_output_potential P w (pop E q) <=
    heap_cost P w + heap_potential P w q)%N.
Proof.
  intros Hwf Hbudget HP.
  pose proof (pop_cost_credit E HE q P w Hwf Hbudget HP) as Hcredit.
  pose proof (pop_fuel_cost E q P Hwf HP) as Hfuel.
  unfold heap_w, heap_cost, heap_k in *. rewrite Nat2N.inj_succ in *. nia.
Qed.

(** Failure has no returned queue potential and success exposes its returned stale count. *)
Definition output_stale {K} (r : option (positive * K * t K)) : nat :=
  match r with None => 0 | Some (_, _, q) => stale q end.

Local Lemma pop_step_callee_bound {K} (E : encoding K) m n U P w g r h total :
  wf E (Queue h m n total) -> total <= P ->
  incl (HeapBinomial.entries h) U ->
  HeapBinomialCost.bounded w U ->
  (forall e, In e U -> (Cost.ticks (Map.get_c E (snd e) m) <= g /\
    Cost.ticks (Map.remove_c E (snd e) m) <= r)%N) ->
  (Cost.ticks (pop_step_c E m n (h, total)) + 2 <=
    16 * N.of_nat (S (Nat.log2 P)) * (1 + w) + g + r + 3)%N.
Proof.
  intros Hwf HP Hincl Hwidth Hcallees.
  pose proof (HeapBinomialCost.remove_min_cost _ w h (proj1 Hwf)
    ltac:(intros e Hin; apply Hwidth, Hincl, Hin)) as Hremove.
  pose proof (proj2 (proj2 (proj2 (proj2 Hwf)))) as Hcount.
  change (total = HeapBinomial.heap_count h) in Hcount.
  pose proof (Nat.log2_le_mono total P HP) as Hlog.
  assert (HL : (N.of_nat (S (Nat.log2 (HeapBinomial.heap_count h))) <=
    N.of_nat (S (Nat.log2 P)))%N) by (rewrite <- Hcount; lia).
  pose proof (HeapBinomial.remove_min_correct _ h (proj1 Hwf)) as Hheap.
  rewrite pop_step_callee_cost.
  destruct (HeapBinomial.remove_min h) as [[[[p c] k] rest]|] eqn:Hremoved.
  - destruct Hheap as [_ [_ [Hin _]]].
    assert (Hentry : In (p, c, k) U) by (apply Hincl, Hin; left; reflexivity).
    destruct (Hcallees _ Hentry) as [Hget Hdelete]. cbn [snd] in Hget, Hdelete.
    destruct (Map.get E k m) as [current|]; [destruct (Pos.eqb p current)|]; nia.
  - nia.
Qed.

(** Callee-relative pop credit covers arbitrary lookups and removals on the visited support. *)
Theorem pop_cost_callee {K} (E : encoding K) (HE : encoding_laws E) q P w g r W :
  wf E q -> pending_count q <= P ->
  HeapBinomialCost.bounded w (HeapBinomial.entries (pending q)) ->
  (forall e, In e (HeapBinomial.entries (pending q)) ->
    (Cost.ticks (Map.get_c E (snd e) (live q)) <= g /\
     Cost.ticks (Map.remove_c E (snd e) (live q)) <= r)%N) ->
  (16 * N.of_nat (S (Nat.log2 P)) * (1 + w) + g + r + 3 <= W)%N ->
  (Cost.ticks (pop_c E q) + N.of_nat (output_stale (pop E q)) * W <=
    Cost.ticks (HeapBinomial.sufficient_fuel_c (pending q)) +
    W + N.of_nat (stale q) * W +
    N.pos (Pos.size (HeapBinomial.sufficient_fuel (pending q))))%N.
Proof.
  intros Hwf HP Hwidth Hcallees HW.
  set (U := HeapBinomial.entries (pending q)).
  set (m := live q). set (n := live_count q).
  set (I := fun s : pop_state K => let '(h, total) := s in
    wf E (Queue h m n total) /\ incl (HeapBinomial.entries h) U /\ total <= P).
  set (Phi := fun s : pop_state K => (N.of_nat (snd s - n) * W)%N).
  set (Psi := fun result : option (positive * K * t K) =>
    (N.of_nat (output_stale result) * W)%N).
  assert (Hstep : forall s, I s ->
    match Cost.value (pop_step_c E m n s) with
    | inl s' => I s' /\ (Cost.ticks (pop_step_c E m n s) + Phi s' + 2 <= Phi s)%N
    | inr result => (Cost.ticks (pop_step_c E m n s) + Psi result <= W + Phi s)%N
    end).
  { intros [h total] [Hcurrent [Hincl Hcap]].
    pose proof (pop_step_callee_bound E m n U P w g r h total
      Hcurrent Hcap Hincl Hwidth Hcallees) as Hcost.
    rewrite pop_step_equation.
    pose proof (HeapBinomial.remove_min_correct _ h (proj1 Hcurrent)) as Hheap.
    destruct (HeapBinomial.remove_min h) as [[[[p c] k] rest]|] eqn:Hremove.
    - destruct Hheap as [_ [_ [Hin [Hcount _]]]].
      pose proof (proj2 (proj2 (proj2 (proj2 Hcurrent)))) as Htotal.
      change (total = HeapBinomial.heap_count h) in Htotal.
      assert (Hpositive : 0 < total) by lia.
      assert (Hincl' : incl (HeapBinomial.entries rest) U).
      { intros a Ha. apply Hincl, Hin. right. exact Ha. }
      destruct (Map.get E k m) as [v|] eqn:Hget.
      + destruct (Pos.eqb p v) eqn:Heq.
        * apply Pos.eqb_eq in Heq; subst v.
          destruct (wf_take E h p c k rest m n total Hcurrent Hremove Hget) as [_ Hn].
          unfold Phi, Psi, output_stale, stale. cbn [snd pending_count live_count].
          assert (Hsame : Nat.pred total - Nat.pred n = total - n) by lia.
          rewrite Hsame. nia.
        * assert (Hstale : Map.get E k m <> Some p).
          { rewrite Hget. intro Hbad. inversion Hbad; subst v.
            rewrite Pos.eqb_refl in Heq. discriminate. }
          pose proof (wf_skip E h p c k rest m n total Hcurrent Hremove Hstale) as Hnext.
          pose proof (live_pending_bound E HE _ Hnext) as Hbound. cbn in Hbound.
          split.
          -- split; [exact Hnext|]. split; [exact Hincl'|lia].
          -- unfold Phi. cbn [snd].
             assert (Hdrop : (N.of_nat (total - n) = N.of_nat (Nat.pred total - n) + 1)%N)
               by lia.
             rewrite Hdrop. nia.
      + assert (Hstale : Map.get E k m <> Some p) by (rewrite Hget; discriminate).
        pose proof (wf_skip E h p c k rest m n total Hcurrent Hremove Hstale) as Hnext.
        pose proof (live_pending_bound E HE _ Hnext) as Hbound. cbn in Hbound.
        split.
        * split; [exact Hnext|]. split; [exact Hincl'|lia].
        * unfold Phi. cbn [snd].
          assert (Hdrop : (N.of_nat (total - n) = N.of_nat (Nat.pred total - n) + 1)%N)
            by lia.
          rewrite Hdrop. nia.
    - change (Cost.ticks (pop_step_c E m n (h, total)) + 0 <= W + Phi (h, total))%N.
      nia. }
  assert (Hinitial : I (pending q, pending_count q)).
  { split; [destruct q; exact Hwf|]. split; [intros a Ha; exact Ha|exact HP]. }
  pose proof (HeapLoop.iterate_credit (pop_step_c E m n) I Phi Psi W Hstep
    (HeapBinomial.sufficient_fuel (pending q)) (pending q, pending_count q) Hinitial) as Hcredit.
  unfold pop, pop_c. fold m n. autorewrite with galois_cost.
  fold (HeapBinomial.sufficient_fuel (pending q)).
  unfold HeapLoop.potential in Hcredit.
  destruct (Cost.value (iterate _ _ _)) as [s|result].
  - unfold Phi, Psi, output_stale, stale in *. cbn [snd] in *.
    fold n. fold n in Hcredit. nia.
  - unfold Phi, Psi, stale in *. cbn [snd] in *.
    fold n. fold n in Hcredit. nia.
Qed.

(** Push's callee-relative inequality pays the finite new-entry credit on its current branch. *)
Theorem push_cost_callee {K} (E : encoding K) p k q W :
  (Cost.ticks (push_c E p k q) + N.of_nat (stale (push E p k q)) * W <=
    Cost.ticks (Map.get_c E k (live q)) + 2 + Cost.ticks (encode_c E k) +
    Cost.ticks (HeapBinomial.insert_c (HeapBinomial.Tree (p, encode E k, k) []) (pending q)) +
    Cost.ticks (Map.set_c E k p (live q)) + W + N.of_nat (stale q) * W)%N.
Proof.
  pose proof (stale_push E p k q) as Hstale.
  assert (HstaleN : (N.of_nat (stale (push E p k q)) <= N.of_nat (stale q) + 1)%N)
    by lia.
  rewrite push_callee_cost.
  destruct (priority E k q) as [old|]; [destruct (Pos.ltb p old)|]; nia.
Qed.

(** A trace records actual operation charges and each operation's local size and key duties. *)
Inductive operation_trace {K} (E : encoding K) P w : t K -> nat -> N -> t K -> Prop :=
  | Trace_empty q : operation_trace E P w q 0 0%N q
  | Trace_push q p k count ticks last :
      wf E q -> key_budget E w q -> pending_count q < P ->
      (Cost.ticks (encode_c E k) <= w)%N ->
      (N.pos (Pos.size (encode E k)) <= w)%N ->
      operation_trace E P w (push E p k q) count ticks last ->
      operation_trace E P w q (S count) (Cost.ticks (push_c E p k q) + ticks)%N last
  | Trace_pop q p k q' count ticks last :
      wf E q -> key_budget E w q -> pending_count q <= P ->
      pop E q = Some (p, k, q') ->
      operation_trace E P w q' count ticks last ->
      operation_trace E P w q (S count) (Cost.ticks (pop_c E q) + ticks)%N last
  | Trace_none q count ticks last :
      wf E q -> key_budget E w q -> pending_count q <= P ->
      pop E q = None ->
      operation_trace E P w empty count ticks last ->
      operation_trace E P w q (S count) (Cost.ticks (pop_c E q) + ticks)%N last.

(** Per-operation inequalities telescope along any branch and refund its final potential. *)
Theorem heap_trace_cost {K} (E : encoding K) (HE : encoding_laws E)
    (laws : Map.cost_laws) P w q count ticks last :
  operation_trace E P w q count ticks last ->
  (ticks + heap_potential P w last <=
    N.of_nat count * heap_cost P w + heap_potential P w q)%N.
Proof.
  intro Htrace.
  induction Htrace as
    [q|q p k count ticks last Hwf Hbudget HP Hencode Hbits Htail IH|
      q p k q' count ticks last Hwf Hbudget HP Hpop Htail IH|
      q count ticks last Hwf Hbudget HP Hpop Htail IH].
  - cbn [N.of_nat]. nia.
  - pose proof (push_cost E laws p k q P w Hwf Hbudget HP Hencode Hbits).
    rewrite Nat2N.inj_succ. nia.
  - pose proof (pop_cost E HE laws q P w Hwf Hbudget HP) as Hpopcost.
    rewrite Hpop in Hpopcost. cbn [pop_output_potential] in Hpopcost.
    rewrite Nat2N.inj_succ. nia.
  - pose proof (pop_cost E HE laws q P w Hwf Hbudget HP) as Hpopcost.
    rewrite Hpop in Hpopcost. cbn [pop_output_potential] in Hpopcost.
    assert (Hempty : heap_potential P w (@empty K) = 0%N) by reflexivity.
    rewrite Hempty in IH. rewrite Nat2N.inj_succ. nia.
Qed.

(** Any capped trace of at most [N] operations from empty spends at most [N] operation budgets. *)
Theorem heap_amortised {K} (E : encoding K) (HE : encoding_laws E)
    (laws : Map.cost_laws) P w count ticks last N :
  operation_trace E P w (@empty K) count ticks last -> count <= N ->
  (ticks <= N.of_nat N * heap_cost P w)%N.
Proof.
  intros Htrace Hcount.
  pose proof (heap_trace_cost E HE laws P w empty count ticks last Htrace) as Hcost.
  assert (Hempty : heap_potential P w (@empty K) = 0%N) by reflexivity.
  rewrite Hempty in Hcost.
  assert (HN : (N.of_nat count <= N.of_nat N)%N) by lia. nia.
Qed.

(** Emptiness means that every key has no live priority, including keys outside support. *)
Theorem is_empty_spec {K} (E : encoding K) (q : t K) :
  wf E q -> (is_empty q = true <-> forall k, priority E k q = None).
Proof.
  intro Hwf.
  change (Map.is_empty (live q) = true <-> forall k, Map.get E k (live q) = None).
  apply Map.is_empty_spec. exact (proj1 (proj2 Hwf)).
Qed.

(** A failed pop proves that every key is absent through the public queue observations. *)
Theorem pop_none_priority {K} (E : encoding K) (HE : encoding_laws E) (q : t K) :
  wf E q -> pop E q = None -> forall k, priority E k q = None.
Proof.
  intros Hwf Hnone.
  apply (proj1 (is_empty_spec E q Hwf)).
  apply (proj1 (pop_none_empty E HE q Hwf)). exact Hnone.
Qed.

(** An absent-key push adds one pending entry without any representation or encoding premises. *)
Theorem pending_count_push_absent {K} (E : encoding K) p k (q : t K) :
  priority E k q = None -> pending_count (push E p k q) = S (pending_count q).
Proof.
  intro Habsent. rewrite push_equation, Habsent. reflexivity.
Qed.

(** Inserting an absent key preserves the stale count even when the input counters are raw. *)
Theorem stale_push_absent {K} (E : encoding K) p k (q : t K) :
  priority E k q = None -> stale (push E p k q) = stale q.
Proof.
  intro Habsent. rewrite push_equation, Habsent. reflexivity.
Qed.

(** The empty queue starts with zero stale entries. *)
Theorem stale_empty {K} : stale (@empty K) = 0.
Proof.
  reflexivity.
Qed.

(** The empty pending support satisfies every finite key budget. *)
Theorem key_budget_empty {K} (E : encoding K) w : key_budget E w (@empty K).
Proof.
  intros e Hin. contradiction.
Qed.

(** An absent push extends the pending key budget by the new query's actual encoder and width. *)
Theorem key_budget_push_absent {K} (E : encoding K) p k (q : t K) w :
  priority E k q = None -> key_budget E w q ->
  (Cost.ticks (encode_c E k) <= w)%N ->
  (N.pos (Pos.size (encode E k)) <= w)%N ->
  key_budget E w (push E p k q).
Proof.
  intros Habsent Hbudget Hencode Hbits. rewrite push_equation, Habsent.
  intros e Hin. apply HeapBinomial.entries_insert in Hin.
  destruct Hin as [Hnew|Hold].
  - cbn [HeapBinomial.tree_entries] in Hnew.
    destruct Hnew as [Hequal|Hfalse]; [subst e; split; assumption|contradiction].
  - exact (Hbudget e Hold).
Qed.

(** Zero count-level staleness is exact counter equality on a well-formed queue. *)
Theorem stale_zero_counts {K} (E : encoding K) (HE : encoding_laws E) (q : t K) :
  wf E q -> stale q = 0 -> pending_count q = live_count q.
Proof.
  intros Hwf Hzero.
  pose proof (live_pending_bound E HE q Hwf) as Hbound.
  unfold stale in Hzero. lia.
Qed.

Local Lemma pop_step_no_stale_no_continue {K} (E : encoding K) (HE : encoding_laws E) q :
  wf E q -> stale q = 0 -> forall next,
  Cost.value (pop_step_c E (live q) (live_count q) (pending q, pending_count q)) <> inl next.
Proof.
  intros Hwf Hzero next Hnext.
  pose proof (stale_zero_counts E HE q Hwf Hzero) as Hcounts.
  rewrite pop_step_equation in Hnext.
  pose proof (HeapBinomial.remove_min_correct _ _ (proj1 Hwf)) as Hheap.
  destruct (HeapBinomial.remove_min (pending q)) as [[[[p c] k] rest]|] eqn:Hremove;
    [|discriminate].
  assert (Hstale : Map.get E k (live q) <> Some p).
  { intro Hlive. rewrite Hlive, Pos.eqb_refl in Hnext. discriminate. }
  pose proof (wf_skip E (pending q) p c k rest (live q) (live_count q) (pending_count q)
    Hwf Hremove Hstale) as Hskip.
  pose proof (live_pending_bound E HE _ Hskip) as Hbound. cbn in Hbound.
  destruct Hheap as [_ [_ [_ [Hremoved _]]]].
  pose proof (proj2 (proj2 (proj2 (proj2 Hwf)))) as Htotal. lia.
Qed.

Local Lemma pop_no_stale_first_step {K} (E : encoding K) (HE : encoding_laws E) q q' p k :
  wf E q -> stale q = 0 -> pop E q = Some (p, k, q') ->
  Cost.value (pop_step_c E (live q) (live_count q) (pending q, pending_count q)) =
    inr (Some (p, k, q')).
Proof.
  intros Hwf Hzero Hpop.
  unfold pop, pop_c in Hpop. autorewrite with galois_cost in Hpop.
  fold (HeapBinomial.sufficient_fuel (pending q)) in Hpop.
  destruct (Cost.value (iterate (pop_step_c E (live q) (live_count q))
    (HeapBinomial.sufficient_fuel (pending q)) (pending q, pending_count q)))
    as [state|result] eqn:Hiteration; [discriminate|].
  subst result.
  destruct (iterate_inr_stops (pop_step_c E (live q) (live_count q))
    (HeapBinomial.sufficient_fuel (pending q)) (pending q, pending_count q)
    (Some (p, k, q')) Hiteration) as [used [last [Hused [Hprefix Hterminal]]]].
  assert (Hlast : last = (pending q, pending_count q)).
  { inversion Hprefix as [s|budget s result Hstop|budget s next final Hnext Htail]; subst.
    - reflexivity.
    - exfalso. exact (pop_step_no_stale_no_continue E HE q Hwf Hzero _ Hnext). }
  rewrite Hlast in Hterminal. exact Hterminal.
Qed.

(** A successful no-stale pop retains zero staleness and removes exactly one pending entry. *)
Theorem pop_no_stale {K} (E : encoding K) (HE : encoding_laws E) q q' p k :
  wf E q -> stale q = 0 -> pop E q = Some (p, k, q') ->
  stale q' = 0 /\ pending_count q' + 1 = pending_count q.
Proof.
  intros Hwf Hzero Hpop.
  pose proof (stale_zero_counts E HE q Hwf Hzero) as Hcounts.
  pose proof (size_pop E HE q q' p k Hwf Hpop) as Hsize.
  change (live_count q = S (live_count q')) in Hsize.
  pose proof (pop_no_stale_first_step E HE q q' p k Hwf Hzero Hpop) as Hstep.
  rewrite pop_step_equation in Hstep.
  destruct (HeapBinomial.remove_min (pending q)) as [[[[priority code] key] rest]|];
    [|discriminate].
  destruct (Map.get E key (live q)) as [current|]; [|discriminate].
  destruct (Pos.eqb priority current); [|discriminate].
  inversion Hstep; subst q'. unfold stale. cbn [pending_count live_count].
  split; lia.
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

End Heap.
