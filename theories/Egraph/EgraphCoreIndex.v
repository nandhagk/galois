(** * Persistent parent buckets and deduplicated repair queues

    Parent buckets retain the losing root's snapshot while extending the winner's bucket.
    For example, repairing a loser can still read its parents after several later unions.
    Builds on: the public Base Map and Cost list contracts. *)

From Stdlib Require Import List PArith NArith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseMap.
Import List.ListNotations Cost.Notations.

Module EggParent.

Definition encoding := positive_encoding.
Definition t := Map.t positive (list positive).

Definition get_c (index : t) c : Cost.t (list positive) :=
  Cost.map (fun result => match result with Some xs => xs | None => [] end)
    (Map.get_c encoding c index).

Definition get index c := Cost.value (get_c index c).

(** Absent parent buckets are empty and present buckets retain their stored order. *)
Theorem get_equation index c :
  get index c = match Map.get encoding c index with Some xs => xs | None => [] end.
Proof.
  reflexivity.
Qed.

Definition add_c (index : t) c i : Cost.t t :=
  let* old := get_c index c in
  Map.set_c encoding c (i :: old) index.

Definition add index c i := Cost.value (add_c index c i).

(** Registering a node prepends one occurrence to the queried child-root bucket. *)
Theorem add_equation index c i :
  add index c i = Map.set encoding c (i :: get index c) index.
Proof.
  reflexivity.
Qed.

Definition register_c index roots i :=
  fold_left_c (fun index c => add_c index c i) roots index.

Definition register index roots i := Cost.value (register_c index roots i).

(** Registration visits the supplied child roots in order and never scans stored nodes. *)
Theorem register_equation index roots i :
  register index roots i = fold_left (fun index c => add index c i) roots index.
Proof.
  unfold register, register_c; rewrite value_fold_left_c; reflexivity.
Qed.

Definition merge_c (index : t) loser winner : Cost.t t :=
  let* losing := get_c index loser in
  let* winning := get_c index winner in
  let* combined := app_c losing winning in
  Map.set_c encoding winner combined index.

Definition merge index loser winner := Cost.value (merge_c index loser winner).

(** Merging copies the loser's bucket onto the winner and retains the historical loser bucket. *)
Theorem merge_equation index loser winner :
  merge index loser winner =
    Map.set encoding winner (get index loser ++ get index winner) index.
Proof.
  unfold merge, merge_c; rewrite !Cost.value_bind, value_app_c; reflexivity.
Qed.

Local Lemma get_set index c xs d :
  Map.wf encoding index ->
  get (Map.set encoding c xs index) d =
    if Pos.eq_dec d c then xs else get index d.
Proof.
  intro Hwf; rewrite !get_equation.
  destruct (Pos.eq_dec d c) as [->|Hne].
  - rewrite Map.get_set_same by exact Hwf; reflexivity.
  - rewrite Map.get_set_other by
      (try exact positive_encoding_laws; assumption).
    reflexivity.
Qed.

(** A bucket insertion adds only its new occurrence and preserves all previous occurrences. *)
Theorem add_in index c i d j :
  Map.wf encoding index ->
  (In j (get (add index c i) d) <-> (d = c /\ j = i) \/ In j (get index d)).
Proof.
  intro Hwf; rewrite add_equation, get_set by exact Hwf.
  destruct (Pos.eq_dec d c) as [->|Hne]; cbn; intuition congruence.
Qed.

(** A bucket insertion preserves canonical Map representation. *)
Theorem add_wf index c i :
  Map.wf encoding index -> Map.wf encoding (add index c i).
Proof.
  intro Hwf; rewrite add_equation; apply Map.wf_set; exact Hwf.
Qed.

(** Registration preserves canonical Map representation through every update. *)
Theorem register_wf roots i index :
  Map.wf encoding index -> Map.wf encoding (register index roots i).
Proof.
  rewrite register_equation; revert index.
  induction roots as [|c roots IH]; intros index Hwf; cbn [fold_left].
  - exact Hwf.
  - apply IH, add_wf; exact Hwf.
Qed.

Local Lemma register_in_fold roots i index d j :
  Map.wf encoding index ->
  (In j (get (fold_left (fun index c => add index c i) roots index) d) <->
    (j = i /\ In d roots) \/ In j (get index d)).
Proof.
  revert index; induction roots as [|c roots IH]; intros index Hwf.
  - cbn [fold_left In]; tauto.
  - cbn [fold_left]; rewrite IH by (apply add_wf; exact Hwf).
    rewrite add_in by exact Hwf; cbn [In]; intuition congruence.
Qed.

(** Registration has exactly the incidences of the supplied roots plus the old buckets. *)
Theorem register_in index roots i d j :
  Map.wf encoding index ->
  (In j (get (register index roots i) d) <->
    (j = i /\ In d roots) \/ In j (get index d)).
Proof.
  intro Hwf; rewrite register_equation; apply register_in_fold; exact Hwf.
Qed.

(** Concatenating parent buckets preserves canonical Map representation. *)
Theorem merge_wf index loser winner :
  Map.wf encoding index -> Map.wf encoding (merge index loser winner).
Proof.
  intro Hwf; rewrite merge_equation; apply Map.wf_set; exact Hwf.
Qed.

(** A merge extends only the winning bucket and preserves every old occurrence. *)
Theorem merge_in index loser winner d i :
  Map.wf encoding index ->
  (In i (get (merge index loser winner) d) <->
    In i (get index d) \/ (d = winner /\ In i (get index loser))).
Proof.
  intro Hwf; rewrite merge_equation, get_set by exact Hwf.
  destruct (Pos.eq_dec d winner) as [->|Hne].
  - rewrite in_app_iff; intuition.
  - intuition.
Qed.

(** A distinct loser bucket remains available as the deferred repair snapshot. *)
Theorem merge_loser index loser winner :
  Map.wf encoding index -> loser <> winner ->
  get (merge index loser winner) loser = get index loser.
Proof.
  intros Hwf Hne; rewrite merge_equation, get_set by exact Hwf.
  destruct (Pos.eq_dec loser winner); congruence.
Qed.

(** Parent lookup charges its encoder and the queried key bits alone. *)
Theorem get_cost index c :
  Cost.ticks (get_c index c) =
    (1 + Cost.ticks (encode_c encoding c) + N.pos (Pos.size (encode encoding c)))%N.
Proof.
  unfold get_c; rewrite Cost.ticks_map; apply Map.get_cost.
Qed.

(** Registration of one occurrence charges one bucket lookup and one persistent update. *)
Theorem add_cost index c i :
  Cost.ticks (add_c index c i) =
    (2 * (1 + Cost.ticks (encode_c encoding c) +
      N.pos (Pos.size (encode encoding c))))%N.
Proof.
  unfold add_c; rewrite Cost.ticks_bind, get_cost, Map.set_cost; lia.
Qed.

(** Registration pays one traversal tick and two trie paths for each actual child root. *)
Theorem register_cost index roots i :
  Cost.ticks (register_c index roots i) =
    fold_right (fun c total =>
      (1 + 2 * (1 + Cost.ticks (encode_c encoding c) +
        N.pos (Pos.size (encode encoding c))) + total)%N) 0%N roots.
Proof.
  unfold register_c; revert index; induction roots as [|c roots IH]; intro index.
  - reflexivity.
  - rewrite ticks_fold_left_c_cons, add_cost, IH; reflexivity.
Qed.

(** Parent concatenation pays for the copied loser list and all three trie paths. *)
Theorem merge_cost index loser winner :
  Cost.ticks (merge_c index loser winner) =
    (1 + Cost.ticks (encode_c encoding loser) + N.pos (Pos.size (encode encoding loser)) +
      2 * (1 + Cost.ticks (encode_c encoding winner) +
        N.pos (Pos.size (encode encoding winner))) +
      N.of_nat (length (get index loser)))%N.
Proof.
  unfold merge_c; rewrite !Cost.ticks_bind.
  fold (get index loser) (get index winner).
  rewrite !get_cost, ticks_app_c, Map.set_cost; lia.
Qed.

End EggParent.

Module EggPending.

Record t : Type := Queue {
  entries : list positive;
  flags : Map.t positive unit
}.

Definition empty_c : Cost.t t :=
  let* flags := Map.empty_c in
  Cost.ret (Queue [] flags).

Definition empty := Cost.value empty_c.

(** The flags enumerate exactly the queue membership and the queue contains no duplicates. *)
Record wf (q : t) : Prop := Wf {
  flags_wf : Map.wf positive_encoding (flags q);
  entries_nodup : NoDup (entries q);
  flags_agree : forall c, Map.get positive_encoding c (flags q) = Some tt <->
    In c (entries q)
}.

Definition push_c c q : Cost.t t :=
  let* old := Map.get_c positive_encoding c (flags q) in
  match old with
  | Some _ => Cost.ret q
  | None =>
    let* flags := Map.set_c positive_encoding c tt (flags q) in
    Cost.ret (Queue (c :: entries q) flags)
  end.

Definition push c q := Cost.value (push_c c q).

(** Enqueueing uses the membership flag and adds a new head only on a flag miss. *)
Theorem push_equation c q :
  push c q =
    match Map.get positive_encoding c (flags q) with
    | Some _ => q
    | None => Queue (c :: entries q) (Map.set positive_encoding c tt (flags q))
    end.
Proof.
  unfold push, push_c; rewrite Cost.value_bind.
  fold (Map.get positive_encoding c (flags q)).
  destruct (Map.get positive_encoding c (flags q)); reflexivity.
Qed.

Definition pop_c q : Cost.t (option (positive * t)) :=
  match entries q with
  | [] => Cost.ret None
  | c :: rest =>
    let* flags := Map.remove_c positive_encoding c (flags q) in
    Cost.ret (Some (c, Queue rest flags))
  end.

Definition pop q := Cost.value (pop_c q).

(** Dequeueing removes the head's flag and returns the remaining queue in its stored order. *)
Theorem pop_equation q :
  pop q =
    match entries q with
    | [] => None
    | c :: rest => Some (c, Queue rest (Map.remove positive_encoding c (flags q)))
    end.
Proof.
  destruct q as [[|c rest] flags]; reflexivity.
Qed.

(** A successful pop exposes exactly the stored head and the remaining entry list. *)
Theorem pop_entries q c rest :
  pop q = Some (c, rest) -> entries q = c :: entries rest.
Proof.
  destruct q as [[|d ds] flags]; rewrite pop_equation; [discriminate|].
  intro Hresult; injection Hresult as <- <-; reflexivity.
Qed.

(** Empty initialization establishes all queue representation duties. *)
Theorem empty_wf : wf empty.
Proof.
  constructor.
  - apply Map.wf_empty.
  - constructor.
  - intro c; change (Map.get positive_encoding c Map.empty = Some tt <-> False).
    rewrite Map.get_empty; split; [discriminate|contradiction].
Qed.

(** Enqueueing establishes the requested membership and preserves every prior membership. *)
Theorem push_in c q d :
  wf q -> (In d (entries (push c q)) <-> d = c \/ In d (entries q)).
Proof.
  intro Hwf; rewrite push_equation.
  destruct (Map.get positive_encoding c (flags q)) as [[]|] eqn:Hflag.
  - apply (proj1 (flags_agree q Hwf c)) in Hflag; intuition congruence.
  - cbn [entries In]; intuition congruence.
Qed.

(** A deduplicated push adds at most one queue entry on any raw flag table. *)
Theorem push_length c q :
  (length (entries (push c q)) <= S (length (entries q)))%nat.
Proof.
  rewrite push_equation; destruct (Map.get positive_encoding c (flags q)); cbn [entries length];
    lia.
Qed.

(** Enqueueing preserves exact membership flags and duplicate-free scheduling. *)
Theorem push_wf c q : wf q -> wf (push c q).
Proof.
  intro Hwf; rewrite push_equation.
  destruct (Map.get positive_encoding c (flags q)) as [[]|] eqn:Hflag; [exact Hwf|].
  constructor; cbn [entries flags].
  - apply Map.wf_set; exact (flags_wf q Hwf).
  - constructor; [|exact (entries_nodup q Hwf)].
    intro Hin; apply (proj2 (flags_agree q Hwf c)) in Hin; congruence.
  - intro d; destruct (Pos.eq_dec d c) as [->|Hne].
    + rewrite Map.get_set_same by exact (flags_wf q Hwf).
      cbn [In]; intuition.
    + rewrite Map.get_set_other by
        (try exact positive_encoding_laws; try exact Hne; exact (flags_wf q Hwf)).
      rewrite flags_agree by exact Hwf; cbn [In]; intuition congruence.
Qed.

(** Dequeueing preserves the exact flag-to-membership correspondence. *)
Theorem pop_wf q c rest :
  wf q -> pop q = Some (c, rest) -> wf rest.
Proof.
  intros Hwf; rewrite pop_equation.
  destruct (entries q) as [|d ds] eqn:Hentries; [discriminate|].
  intro Hresult; injection Hresult as <- <-.
  constructor; cbn [flags entries].
  - apply Map.wf_remove; exact (flags_wf q Hwf).
  - pose proof (entries_nodup q Hwf) as Hnodup.
    rewrite Hentries in Hnodup; inversion Hnodup; assumption.
  - intro key; destruct (Pos.eq_dec key d) as [->|Hne].
    + rewrite Map.get_remove_same by exact (flags_wf q Hwf).
      pose proof (entries_nodup q Hwf) as Hnodup.
      rewrite Hentries in Hnodup; inversion Hnodup as [|head tail Hnotin Htail].
      split; [discriminate|intro Hin; contradiction].
    + rewrite Map.get_remove_other by
        (try exact positive_encoding_laws; try exact Hne; exact (flags_wf q Hwf)).
      rewrite flags_agree by exact Hwf; rewrite Hentries; cbn [In]; intuition congruence.
Qed.

(** Queue pushes pay for their actual flag lookup and only perform an update on a miss. *)
Theorem push_cost c q :
  (Cost.ticks (push_c c q) <=
    2 * (1 + Cost.ticks (encode_c positive_encoding c) +
      N.pos (Pos.size (encode positive_encoding c))))%N.
Proof.
  unfold push_c; rewrite Cost.ticks_bind.
  fold (Map.get positive_encoding c (flags q)).
  destruct (Map.get positive_encoding c (flags q)) as [[]|];
    autorewrite with galois_cost; rewrite ?Map.get_cost, ?Map.set_cost; lia.
Qed.

(** A successful pop pays for the removed flag's encoder and trie path. *)
Theorem pop_cost q c rest :
  pop q = Some (c, rest) ->
  Cost.ticks (pop_c q) =
    (1 + Cost.ticks (encode_c positive_encoding c) +
      N.pos (Pos.size (encode positive_encoding c)))%N.
Proof.
  rewrite pop_equation.
  destruct q as [[|d ds] flags]; [discriminate|].
  intro Hresult; injection Hresult as <- <-.
  unfold pop_c; cbn [entries]; rewrite Cost.ticks_bind, Cost.ticks_ret, Map.remove_cost; lia.
Qed.

End EggPending.
