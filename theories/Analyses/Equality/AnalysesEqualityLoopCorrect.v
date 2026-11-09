(** * Countdown worklist correctness

    Counter changes retain dependency multiplicity and the worklist computes the finite reference.
    For example, marking a repeated operand consumes both occurrences before its user is ready.
    Builds on: AnalysesEqualityLoopWorklist and the public Base collection laws. *)

From Stdlib Require Import List Bool Arith Lia PArith NArith.
From Galois.Cost Require Import CostMonad CostList CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseIndex.
From Galois.Analyses.Equality Require Import AnalysesEqualityLoopWorklist.
Import List.ListNotations NumberingLoopWorklist.

Local Open Scope nat_scope.

Module NumberingLoopCorrect.

Section Correctness.
Context {V : Type} (E : encoding V) (HE : encoding_laws E).

(** Occurrence counts keep repeated keys rather than treating dependency lists as sets. *)
Definition hits x (xs : list V) := length (filter (fun y => eqb E y x) xs).

Local Lemma hits_cons x y xs :
  hits x (y :: xs) = (if eqb E y x then 1 else 0) + hits x xs.
Proof.
  unfold hits; cbn [filter]; destruct (eqb E y x); reflexivity.
Qed.

Local Lemma hits_app x xs ys : hits x (xs ++ ys) = hits x xs + hits x ys.
Proof.
  unfold hits; rewrite filter_app, length_app; reflexivity.
Qed.

(** A notification decrements exactly the targeted counter and preserves missing counters. *)
Theorem notify_remaining s edge query :
  Map.get E query (remaining (notify E s edge)) =
  if eqb E (snd edge) query
  then option_map Nat.pred (Map.get E query (remaining s))
  else Map.get E query (remaining s).
Proof.
  rewrite notify_equation; cbn zeta.
  destruct (eqb_spec E HE (snd edge) query) as [Heq|Hne].
  - subst query.
    destruct (Map.get E (snd edge) (remaining s)) as [[|n]|] eqn:Hget.
    + cbn [remaining option_map]; exact Hget.
    + destruct n as [|n].
      * destruct (FinSet.mem E (snd edge) (available s)); cbn [remaining];
          rewrite Map.get_set_raw, eqb_refl; reflexivity.
      * cbn [remaining]; rewrite Map.get_set_raw, eqb_refl; reflexivity.
    + cbn [remaining option_map]; exact Hget.
  - assert (Htest : eqb E query (snd edge) = false).
    { apply (eqb_false_iff E HE); congruence. }
    destruct (Map.get E (snd edge) (remaining s)) as [[|n]|] eqn:Hget; try reflexivity.
    destruct n as [|n].
    + destruct (FinSet.mem E (snd edge) (available s)); cbn [remaining];
        rewrite Map.get_set_raw, Htest; reflexivity.
    + cbn [remaining]; rewrite Map.get_set_raw, Htest; reflexivity.
Qed.

(** A user bucket subtracts its full occurrence count, including duplicate dependencies. *)
Theorem notifications_remaining uses s query :
  Map.get E query (remaining (notifications E uses s)) =
    option_map (fun n => n - hits query (map snd uses)) (Map.get E query (remaining s)).
Proof.
  unfold notifications, notifications_c; rewrite value_fold_left_c.
  change (Map.get E query (remaining (fold_left (notify E) uses s)) =
    option_map (fun n => n - hits query (map snd uses)) (Map.get E query (remaining s))).
  revert s; induction uses as [|edge rest IH]; intro s.
  - cbn [fold_left map]; unfold hits; cbn [filter length].
    destruct (Map.get E query (remaining s)); cbn [option_map]; [f_equal; lia|reflexivity].
  - cbn [fold_left map]; rewrite IH, notify_remaining, hits_cons.
    destruct (eqb E (snd edge) query),
      (Map.get E query (remaining s)) as [n|]; cbn [option_map]; try reflexivity.
    f_equal; lia.
Qed.

Local Lemma bucket_app dependency rows rest :
  filter (fun edge : V * V => eqb E (fst edge) dependency) (rows ++ rest) =
  filter (fun edge => eqb E (fst edge) dependency) rows ++
    filter (fun edge => eqb E (fst edge) dependency) rest.
Proof.
  apply filter_app.
Qed.

Local Lemma row_count dependency user owner deps :
  hits user (map snd (filter
    (fun edge : V * V => eqb E (fst edge) dependency)
    (map (fun y => (y, owner)) deps))) =
  if eqb E owner user then hits dependency deps else 0.
Proof.
  induction deps as [|y rest IH].
  - unfold hits; cbn [map filter length]; destruct (eqb E owner user); reflexivity.
  - cbn [map filter fst]; destruct (eqb E y dependency) eqn:Hy.
    + cbn [map snd]; rewrite hits_cons, IH, hits_cons, Hy.
      destruct (eqb E owner user); lia.
    + rewrite IH, hits_cons, Hy; destruct (eqb E owner user); lia.
Qed.

Local Lemma absent_row_count dependency user entries :
  ~ In user (map fst entries) ->
  hits user (map snd (filter
    (fun edge : V * V => eqb E (fst edge) dependency)
    (flat_map (fun entry => map (fun y => (y, fst entry)) (snd entry)) entries))) = 0.
Proof.
  induction entries as [|[owner deps] rest IH]; intro Habsent.
  - reflexivity.
  - cbn [flat_map fst snd]; rewrite bucket_app, map_app, hits_app, row_count.
    assert (Hdifferent : eqb E owner user = false).
    { apply (eqb_false_iff E HE); intro Heq; subst owner; apply Habsent; now left. }
    rewrite Hdifferent, IH; [reflexivity|].
    intro Hin; apply Habsent; now right.
Qed.

Local Lemma present_row_count dependency user deps entries :
  NoDup (map fst entries) -> In (user, deps) entries ->
  hits user (map snd (filter
    (fun edge : V * V => eqb E (fst edge) dependency)
    (flat_map (fun entry => map (fun y => (y, fst entry)) (snd entry)) entries))) =
    hits dependency deps.
Proof.
  induction entries as [|[owner args] rest IH]; intros Hunique Hin; [contradiction|].
  inversion Hunique as [|key keys Hfresh Hrest]; subst.
  cbn [flat_map fst snd]; rewrite bucket_app, map_app, hits_app, row_count.
  destruct Hin as [Heq|Hin].
  - injection Heq as <- <-; rewrite eqb_refl, absent_row_count by exact Hfresh; lia.
  - assert (Hdifferent : eqb E owner user = false).
    { apply (eqb_false_iff E HE); intro Heq; subst owner; apply Hfresh.
      apply in_map_iff; exists (user, deps); split; [reflexivity|exact Hin]. }
    rewrite Hdifferent, (IH Hrest Hin); lia.
Qed.

(** The prepared user bucket contains exactly the dependency occurrences of its queried user. *)
Theorem prepared_user_count universe definitions dependency user deps :
  Map.wf E definitions -> Map.get E user definitions = Some deps ->
  hits user (map snd (Index.find E dependency
    (users (prepare E universe definitions)))) = hits dependency deps.
Proof.
  intros Hwf Hget; rewrite prepare_equation; cbn [users].
  rewrite Index.find_group_by, edge_rows_value.
  apply present_row_count.
  - exact (Map.elements_nodup E definitions Hwf).
  - apply (proj2 (Map.elements_spec E HE user deps definitions Hwf)); exact Hget.
Qed.

(** Pending counts describe the unmarked dependency occurrences in one rule. *)
Definition pending s deps :=
  length (filter (fun y => negb (FinSet.mem E y (marked s))) deps).

(** Marking a fresh source removes exactly its multiplicity from each pending count. *)
Theorem pending_mark s source deps :
  FinSet.mem E source (marked s) = false ->
  pending s deps =
    length (filter (fun y => negb (FinSet.mem E y (FinSet.add E source (marked s)))) deps) +
      hits source deps.
Proof.
  intro Hfresh; unfold pending, hits; induction deps as [|y rest IH]; [reflexivity|].
  cbn [filter]; rewrite FinSet.mem_add_raw.
  destruct (eqb_spec E HE y source) as [->|Hdifferent].
  - rewrite Hfresh; cbn [orb negb length]; lia.
  - destruct (FinSet.mem E y (marked s)); cbn [orb negb length]; lia.
Qed.

(** Every stored counter counts exactly its rule's unmarked dependency occurrences. *)
Definition counters_correct (definitions : Map.t V (list V)) s : Prop :=
  forall x, Map.get E x (remaining s) =
    option_map (pending s) (Map.get E x definitions).

Local Lemma pending_empty deps :
  length (filter (fun y => negb (FinSet.mem E y FinSet.empty)) deps) = length deps.
Proof.
  induction deps as [|y rest IH]; [reflexivity|].
  cbn [filter]; rewrite FinSet.mem_empty; cbn [negb length]; lia.
Qed.

(** Counter initialization is exact for the actual prepared rules, including missing rules. *)
Theorem initial_counters universe definitions :
  counters_correct definitions (initial E (prepare E universe definitions)).
Proof.
  intro x; rewrite initial_equation, prepare_equation; cbn [remaining marked counters].
  rewrite Map.map_c_value, Map.get_map.
  destruct (Map.get E x definitions) as [deps|]; [|reflexivity].
  cbn [option_map]; rewrite value_length_c; unfold pending; cbn [marked].
  now rewrite pending_empty.
Qed.

(** A fresh pop and its full actual user bucket preserve the exact counter interpretation. *)
Theorem step_counters universe definitions s source rest :
  Map.wf E definitions -> state_wf E s -> counters_correct definitions s ->
  todo s = source :: rest -> FinSet.mem E source (marked s) = false ->
  counters_correct definitions
    (last_state (Cost.value (step_c E (prepare E universe definitions) s))).
Proof.
  intros Hdefinitions Hwf Hcounts Htodo Hfresh.
  rewrite step_equation, Htodo; cbn [last_state].
  set (base := State rest (FinSet.add E source (marked s))
    (available s) (remaining s) (S (processed s))).
  set (uses := Index.find E source (users (prepare E universe definitions))).
  assert (Hbase : state_wf E base).
  { destruct Hwf as [Hmarked [Havailable Hremaining]].
    split; [now apply FinSet.wf_add|split; assumption]. }
  pose proof (notifications_preserved E uses base Hbase) as [_ [_ [_ Hmarked]]].
  intro query; rewrite notifications_remaining.
  change (option_map (fun n => n - hits query (map snd uses))
    (Map.get E query (remaining s)) =
    option_map (pending (notifications E uses base)) (Map.get E query definitions)).
  rewrite Hcounts; destruct (Map.get E query definitions) as [deps|] eqn:Hrule;
    [|reflexivity].
  cbn [option_map]; f_equal.
  assert (Huses : hits query (map snd uses) = hits source deps).
  { unfold uses; exact (prepared_user_count universe definitions source query deps
      Hdefinitions Hrule). }
  rewrite Huses; unfold pending at 2; rewrite Hmarked.
  unfold base; cbn [marked].
  rewrite (pending_mark s source deps Hfresh); apply Nat.add_sub.
Qed.

(** Queue, marked and still-available nodes have disjoint lifecycle states and cover the universe. *)
Record lifecycle (universe : FinSet.t V) s : Prop := {
  queue_unique : NoDup (todo s);
  queue_reserved : forall x, In x (todo s) ->
    FinSet.mem E x (marked s) = false /\ FinSet.mem E x (available s) = false;
  marked_reserved : forall x, FinSet.mem E x (marked s) = true ->
    FinSet.mem E x (available s) = false;
  universe_covered : forall x, FinSet.mem E x universe = true ->
    FinSet.mem E x (marked s) = true \/ In x (todo s) \/ FinSet.mem E x (available s) = true
}.

Local Lemma removed_false available user x :
  FinSet.mem E x available = false ->
  FinSet.mem E x (FinSet.remove E user available) = false.
Proof.
  intro Hnot; rewrite FinSet.mem_remove, Hnot; destruct (eqb E x user); reflexivity.
Qed.

Local Lemma enqueue_lifecycle universe s user counts :
  lifecycle universe s -> FinSet.mem E user (available s) = true ->
  lifecycle universe
    (State (user :: todo s) (marked s) (FinSet.remove E user (available s))
      counts (processed s)).
Proof.
  intros Hlife Hfresh; destruct Hlife as [Hunique Hqueue Hmarked Hcover].
  constructor; cbn [todo marked available].
  - constructor; [|exact Hunique].
    intro Hin; destruct (Hqueue user Hin) as [_ Hnot]; congruence.
  - intros x [Heq|Hin].
    + subst x; split.
      * destruct (FinSet.mem E user (marked s)) eqn:Hdone; [|reflexivity].
        pose proof (Hmarked user Hdone); congruence.
      * rewrite FinSet.mem_remove, eqb_refl; reflexivity.
    + destruct (Hqueue x Hin) as [Hdone Hnot]; split; [exact Hdone|now apply removed_false].
  - intros x Hdone; apply removed_false; now apply Hmarked.
  - intros x Hnode; destruct (Hcover x Hnode) as [Hdone|[Hqueued|Havailable]].
    + now left.
    + right; left; now right.
    + destruct (eqb_spec E HE x user) as [->|Hdifferent].
      * right; left; now left.
      * right; right; rewrite FinSet.mem_remove, (proj2 (eqb_false_iff E HE _ _) Hdifferent).
        cbn [negb andb]; exact Havailable.
Qed.

(** Every notification preserves lifecycle separation, regardless of its counter branch. *)
Theorem notify_lifecycle universe s edge :
  lifecycle universe s -> lifecycle universe (notify E s edge).
Proof.
  intro Hlife; rewrite notify_equation; cbn zeta.
  destruct (Map.get E (snd edge) (remaining s)) as [[|[|n]]|];
    try solve [destruct Hlife; constructor; assumption].
  destruct (FinSet.mem E (snd edge) (available s)) eqn:Hfresh.
  - now apply enqueue_lifecycle.
  - destruct Hlife; constructor; assumption.
Qed.

(** Processing one complete user bucket preserves lifecycle separation. *)
Theorem notifications_lifecycle universe uses s :
  lifecycle universe s -> lifecycle universe (notifications E uses s).
Proof.
  unfold notifications, notifications_c; rewrite value_fold_left_c.
  change (lifecycle universe s -> lifecycle universe (fold_left (notify E) uses s)).
  revert s; induction uses as [|edge rest IH]; intros s Hlife; [exact Hlife|].
  cbn [fold_left]; apply IH, notify_lifecycle; exact Hlife.
Qed.

(** Popping a fresh queued value moves it to the marked set without exposing availability. *)
Theorem pop_lifecycle universe s source rest :
  lifecycle universe s -> todo s = source :: rest ->
  lifecycle universe
    (State rest (FinSet.add E source (marked s)) (available s)
      (remaining s) (S (processed s))).
Proof.
  intros [Hunique Hqueue Hmarked Hcover] Htodo; rewrite Htodo in Hunique.
  inversion Hunique as [|head tail Hfresh Hrest]; subst; constructor;
    cbn [todo marked available].
  - exact Hrest.
  - intros x Hin; destruct (Hqueue x ltac:(rewrite Htodo; now right)) as [Hdone Hnot].
    split; [|exact Hnot].
    rewrite FinSet.mem_add_raw, Hdone.
    assert (Hdifferent : eqb E x source = false).
    { apply (eqb_false_iff E HE); intro Heq; subst x; contradiction. }
    now rewrite Hdifferent.
  - intros x Hdone.
    change (FinSet.mem E x (FinSet.add E source (marked s)) = true) in Hdone.
    rewrite FinSet.mem_add_raw in Hdone; apply Bool.orb_true_iff in Hdone.
    destruct Hdone as [Heq|Hdone].
    + apply (eqb_true_iff E HE) in Heq; subst x.
      exact (proj2 (Hqueue source ltac:(rewrite Htodo; now left))).
    + now apply Hmarked.
  - intros x Hnode; destruct (Hcover x Hnode) as [Hdone|[Hin|Havailable]].
    + left; rewrite FinSet.mem_add_raw, Hdone.
      destruct (eqb E x source); reflexivity.
    + rewrite Htodo in Hin; destruct Hin as [->|Hin].
      * left; rewrite FinSet.mem_add_raw, eqb_refl; reflexivity.
      * right; left; exact Hin.
    + right; right; exact Havailable.
Qed.

Local Lemma listed_spec x xs :
  FinSet.mem E x (FinSet.of_list E xs) = true <-> In x xs.
Proof.
  rewrite FinSet.mem_of_list, existsb_exists; split.
  - intros [y [Hy Heq]]; apply (eqb_true_iff E HE) in Heq; now subst y.
  - intro Hx; exists x; split; [exact Hx|apply eqb_refl].
Qed.

(** The actual seed filter contains exactly the listed zero-counter nodes. *)
Theorem seed_spec universe definitions x :
  FinSet.wf E universe ->
  (In x (seeds (prepare E universe definitions)) <->
    FinSet.mem E x universe = true /\
    Map.get E x (counters (prepare E universe definitions)) = Some 0).
Proof.
  intro Hwf; rewrite prepare_equation; cbn [seeds counters].
  rewrite filter_In, (FinSet.elements_spec E HE x universe Hwf).
  destruct (Map.get E x (Cost.value (Map.map_c length_c definitions))) as [[|n]|];
    split; intros H; intuition discriminate.
Qed.

(** Actual initialization establishes queue uniqueness, reservations and finite-universe coverage. *)
Theorem initial_lifecycle universe definitions :
  FinSet.wf E universe ->
  lifecycle universe (initial E (prepare E universe definitions)).
Proof.
  intro Hwf; set (pr := prepare E universe definitions).
  assert (Hnodes : nodes pr = universe).
  { unfold pr; rewrite prepare_equation; reflexivity. }
  rewrite initial_equation; constructor; cbn [todo marked available].
  - unfold pr; rewrite prepare_equation; apply NoDup_filter.
    exact (FinSet.elements_nodup E universe Hwf).
  - intros x Hin; split; [apply FinSet.mem_empty|].
    rewrite Hnodes, FinSet.mem_diff by (try exact Hwf; apply FinSet.wf_of_list).
    rewrite (proj2 (listed_spec x (seeds pr)) Hin); destruct (FinSet.mem E x universe); reflexivity.
  - intros x Hdone; rewrite FinSet.mem_empty in Hdone; discriminate.
  - intros x Hnode; destruct (FinSet.mem E x (FinSet.of_list E (seeds pr))) eqn:Hseed.
    + right; left; now apply listed_spec.
    + right; right; rewrite Hnodes, FinSet.mem_diff
        by (try exact Hwf; apply FinSet.wf_of_list).
      rewrite Hnode, Hseed; reflexivity.
Qed.

(** Queued nodes always carry a present zero counter. *)
Definition queued_zero s : Prop :=
  forall x, In x (todo s) -> Map.get E x (remaining s) = Some 0.

(** A zero counter cannot retain an availability bit that would permit a later first enqueue. *)
Definition zero_unavailable s : Prop :=
  forall x, Map.get E x (remaining s) = Some 0 -> FinSet.mem E x (available s) = false.

(** Seed construction establishes both zero-counter scheduling properties internally. *)
Theorem initial_status universe definitions :
  FinSet.wf E universe ->
  queued_zero (initial E (prepare E universe definitions)) /\
    zero_unavailable (initial E (prepare E universe definitions)).
Proof.
  intro Hwf; set (pr := prepare E universe definitions).
  assert (Hnodes : nodes pr = universe).
  { unfold pr; rewrite prepare_equation; reflexivity. }
  rewrite initial_equation; split.
  - intros x Hin; exact (proj2 (proj1 (seed_spec universe definitions x Hwf) Hin)).
  - intros x Hzero; change (Map.get E x (counters pr) = Some 0) in Hzero.
    change (FinSet.mem E x (FinSet.diff (nodes pr) (FinSet.of_list E (seeds pr))) = false).
    rewrite Hnodes, FinSet.mem_diff by (try exact Hwf; apply FinSet.wf_of_list).
    destruct (FinSet.mem E x universe) eqn:Hnode; [|reflexivity].
    assert (Hseed : In x (seeds pr)).
    { apply (proj2 (seed_spec universe definitions x Hwf)); split; assumption. }
    rewrite (proj2 (listed_spec x (seeds pr)) Hseed); reflexivity.
Qed.

Local Lemma notify_unavailable s edge x :
  FinSet.mem E x (available s) = false ->
  FinSet.mem E x (available (notify E s edge)) = false.
Proof.
  intro Hnot; rewrite notify_equation; cbn zeta.
  destruct (Map.get E (snd edge) (remaining s)) as [[|[|n]]|]; try exact Hnot.
  destruct (FinSet.mem E (snd edge) (available s)); [|exact Hnot].
  now apply removed_false.
Qed.

Local Lemma notify_queue_origin s edge x :
  In x (todo (notify E s edge)) ->
  In x (todo s) \/
    (x = snd edge /\ Map.get E x (remaining (notify E s edge)) = Some 0).
Proof.
  rewrite !notify_equation; cbn zeta.
  destruct (Map.get E (snd edge) (remaining s)) as [[|[|n]]|];
    try solve [intro Hin; now left].
  destruct (FinSet.mem E (snd edge) (available s)); [|intro Hin; now left].
  intros [Hsame|Hin].
  - subst x; right; split; [reflexivity|].
    cbn [remaining]; rewrite Map.get_set_raw, eqb_refl; reflexivity.
  - now left.
Qed.

Local Lemma notify_queued_zero s edge :
  queued_zero s -> queued_zero (notify E s edge).
Proof.
  intros Hqueued x Hin; apply notify_queue_origin in Hin as [Hold|[_ Hzero]]; [|exact Hzero].
  rewrite notify_remaining, (Hqueued x Hold).
  destruct (eqb E (snd edge) x); reflexivity.
Qed.

Local Lemma notify_target_zero s edge :
  zero_unavailable s ->
  Map.get E (snd edge) (remaining (notify E s edge)) = Some 0 ->
  FinSet.mem E (snd edge) (available (notify E s edge)) = false.
Proof.
  intro Hwaiting; rewrite !notify_equation; cbn zeta.
  destruct (Map.get E (snd edge) (remaining s)) as [[|[|n]]|] eqn:Hget.
  - intros _; exact (Hwaiting _ Hget).
  - destruct (FinSet.mem E (snd edge) (available s)) eqn:Hfresh; intros _.
    + cbn [available]; rewrite FinSet.mem_remove, eqb_refl; reflexivity.
    + exact Hfresh.
  - cbn [remaining]; rewrite Map.get_set_raw, eqb_refl; discriminate.
  - cbn [remaining]; intro Hzero; rewrite Hget in Hzero; discriminate.
Qed.

Local Lemma notify_zero_unavailable s edge :
  zero_unavailable s -> zero_unavailable (notify E s edge).
Proof.
  intros Hwaiting x Hzero; destruct (eqb_spec E HE (snd edge) x) as [<-|Hdifferent].
  - now apply notify_target_zero.
  - pose proof (notify_remaining s edge x) as Hcounter.
    rewrite (proj2 (eqb_false_iff E HE _ _) Hdifferent) in Hcounter.
    apply notify_unavailable; apply Hwaiting; congruence.
Qed.

(** User notifications preserve zero-counter scheduling without scanning unrelated rules. *)
Theorem notifications_status uses s :
  queued_zero s -> zero_unavailable s ->
  queued_zero (notifications E uses s) /\ zero_unavailable (notifications E uses s).
Proof.
  unfold notifications, notifications_c; rewrite value_fold_left_c.
  change (queued_zero s -> zero_unavailable s ->
    queued_zero (fold_left (notify E) uses s) /\ zero_unavailable (fold_left (notify E) uses s)).
  revert s; induction uses as [|edge rest IH]; intros s Hqueued Hwaiting; [now split|].
  cbn [fold_left]; apply IH; [now apply notify_queued_zero|now apply notify_zero_unavailable].
Qed.

(** The finite reference is monotone in its round count. *)
Theorem reference_up definitions count x :
  reference E definitions count x = true -> reference E definitions (S count) x = true.
Proof.
  revert x; induction count as [|count IH]; intros x Htrue; [discriminate|].
  cbn [reference] in *.
  destruct (Map.get E x definitions) as [deps|]; [|discriminate].
  apply forallb_forall; intros y Hy; apply IH.
  exact (proj1 (forallb_forall _ _) Htrue y Hy).
Qed.

(** Increasing the finite-round budget preserves every recognized value. *)
Theorem reference_le definitions first last x :
  first <= last -> reference E definitions first x = true -> reference E definitions last x = true.
Proof.
  intro Hle; induction Hle as [|last Hle IH]; intro Htrue; [exact Htrue|].
  apply reference_up, IH; exact Htrue.
Qed.

Local Lemma pending_zero s deps :
  pending s deps = 0 <-> forallb (fun y => FinSet.mem E y (marked s)) deps = true.
Proof.
  unfold pending; induction deps as [|y rest IH]; [split; intros; reflexivity|].
  cbn [filter forallb]; destruct (FinSet.mem E y (marked s)); cbn [negb andb length].
  - exact IH.
  - split; discriminate.
Qed.

(** Every marked node already appears within the actual number of completed pops. *)
Definition known definitions s : Prop :=
  forall x, FinSet.mem E x (marked s) = true ->
    reference E definitions (processed s) x = true.

(** A ready queued node obtains one more finite-round rank when it is popped. *)
Theorem pop_known definitions s source rest :
  counters_correct definitions s -> queued_zero s -> known definitions s ->
  todo s = source :: rest ->
  known definitions
    (State rest (FinSet.add E source (marked s)) (available s)
      (remaining s) (S (processed s))).
Proof.
  intros Hcounts Hqueued Hknown Htodo.
  assert (Hzero : Map.get E source (remaining s) = Some 0).
  { apply Hqueued; rewrite Htodo; now left. }
  rewrite Hcounts in Hzero.
  destruct (Map.get E source definitions) as [deps|] eqn:Hrule; [|discriminate].
  injection Hzero as Hpending.
  assert (Hsource : reference E definitions (S (processed s)) source = true).
  { cbn [reference]; rewrite Hrule; apply forallb_forall; intros y Hy.
    apply Hknown; apply (proj1 (forallb_forall _ _) ((proj1 (pending_zero s deps)) Hpending) y Hy). }
  intros x Hmarked.
  change (FinSet.mem E x (FinSet.add E source (marked s)) = true) in Hmarked.
  change (reference E definitions (S (processed s)) x = true).
  rewrite FinSet.mem_add_raw in Hmarked; apply Bool.orb_true_iff in Hmarked.
  destruct Hmarked as [Heq|Hold].
  - apply (eqb_true_iff E HE) in Heq; now subst x.
  - apply reference_up; now apply Hknown.
Qed.

Local Lemma notifications_known definitions uses s :
  state_wf E s -> known definitions s -> known definitions (notifications E uses s).
Proof.
  intros Hwf Hknown.
  destruct (notifications_preserved E uses s Hwf) as [_ [_ [Hprocessed Hmarked]]].
  intros x Hx; unfold known in Hknown.
  rewrite Hprocessed; rewrite Hmarked in Hx; now apply Hknown.
Qed.

(** The semantic invariant records exact counters and scheduling, not the desired final result. *)
Definition correct universe definitions s : Prop :=
  state_wf E s /\
  lifecycle universe s /\
  counters_correct definitions s /\
  queued_zero s /\
  zero_unavailable s /\
  known definitions s.

(** All semantic invariant clauses are established by the actual preparation and initialization. *)
Theorem initial_correct universe definitions :
  FinSet.wf E universe -> Map.wf E definitions ->
  correct universe definitions (initial E (prepare E universe definitions)).
Proof.
  intros Huniverse Hdefinitions.
  destruct (initial_status universe definitions Huniverse) as [Hqueued Hwaiting].
  split; [exact (initial_wf E universe definitions Huniverse Hdefinitions)|].
  split; [now apply initial_lifecycle|split; [apply initial_counters|]].
  split; [exact Hqueued|split; [exact Hwaiting|]].
  intros x Hmarked; rewrite initial_equation in Hmarked.
  change (FinSet.mem E x FinSet.empty = true) in Hmarked.
  rewrite FinSet.mem_empty in Hmarked; discriminate.
Qed.

(** The actual runtime step preserves the complete initialized semantic invariant. *)
Theorem step_correct universe definitions s :
  Map.wf E definitions -> correct universe definitions s ->
  match Cost.value (step_c E (prepare E universe definitions) s) with
  | inl next => correct universe definitions next
  | inr final => correct universe definitions final
  end.
Proof.
  intros Hdefinitions Hcorrect; destruct (todo s) as [|source rest] eqn:Htodo.
  - rewrite step_equation, Htodo; exact Hcorrect.
  - destruct Hcorrect as [Hwf [Hlife [Hcounts [Hqueued [Hwaiting Hknown]]]]].
    assert (Hfresh : FinSet.mem E source (marked s) = false).
    { exact (proj1 (queue_reserved _ _ Hlife source ltac:(rewrite Htodo; now left))). }
    pose proof (step_counters universe definitions s source rest
      Hdefinitions Hwf Hcounts Htodo Hfresh) as Hnext_counts.
    rewrite step_equation, Htodo in Hnext_counts; cbn [last_state] in Hnext_counts.
    rewrite step_equation, Htodo.
    set (base := State rest (FinSet.add E source (marked s))
      (available s) (remaining s) (S (processed s))).
    set (uses := Index.find E source (users (prepare E universe definitions))).
    assert (Hbase_wf : state_wf E base).
    { destruct Hwf as [Hmarked [Havailable Hremaining]].
      split; [now apply FinSet.wf_add|split; assumption]. }
    assert (Hbase_queued : queued_zero base).
    { intros x Hx; apply Hqueued; rewrite Htodo; now right. }
    assert (Hbase_waiting : zero_unavailable base) by exact Hwaiting.
    destruct (notifications_preserved E uses base Hbase_wf) as [Hnext_wf _].
    destruct (notifications_status uses base Hbase_queued Hbase_waiting)
      as [Hnext_queued Hnext_waiting].
    split; [exact Hnext_wf|split].
    + apply notifications_lifecycle; exact (pop_lifecycle universe s source rest Hlife Htodo).
    + split; [exact Hnext_counts|split; [exact Hnext_queued|split; [exact Hnext_waiting|]]].
      apply notifications_known; [exact Hbase_wf|].
      exact (pop_known definitions s source rest Hcounts Hqueued Hknown Htodo).
Qed.

(** The common Cost run relation carries the initialized invariant through either outcome. *)
Theorem runs_correct universe definitions count start result :
  Map.wf E definitions ->
  runs (step_c E (prepare E universe definitions)) count start result ->
  correct universe definitions start -> correct universe definitions (last_state result).
Proof.
  intros Hdefinitions Hrun.
  induction Hrun as [s|count s final Hstop|count s next result Hnext Hrun IH]; intro Hcorrect.
  - exact Hcorrect.
  - pose proof (step_correct universe definitions s Hdefinitions Hcorrect) as Hstep.
    rewrite Hstop in Hstep; exact Hstep.
  - apply IH; pose proof (step_correct universe definitions s Hdefinitions Hcorrect) as Hstep.
    rewrite Hnext in Hstep; exact Hstep.
Qed.

(** The finite rule map contains rules only at values in the supplied node universe. *)
Definition rules_supported universe (definitions : Map.t V (list V)) : Prop :=
  forall x deps, Map.get E x definitions = Some deps -> FinSet.mem E x universe = true.

(** A terminal empty queue contains every rule whose dependencies have all been marked. *)
Theorem terminal_closed universe definitions s :
  rules_supported universe definitions -> correct universe definitions s -> todo s = [] ->
  forall x deps, Map.get E x definitions = Some deps ->
    forallb (fun y => FinSet.mem E y (marked s)) deps = true ->
    FinSet.mem E x (marked s) = true.
Proof.
  intros Hsupported [_ [Hlife [Hcounts [_ [Hwaiting _]]]]] Hempty x deps Hrule Hargs.
  assert (Hcounter : Map.get E x (remaining s) = Some 0).
  { rewrite Hcounts, Hrule; cbn [option_map]; f_equal.
    apply (proj2 (pending_zero s deps)); exact Hargs. }
  pose proof (Hwaiting x Hcounter) as Hunavailable.
  destruct (universe_covered _ _ Hlife x (Hsupported x deps Hrule))
    as [Hdone|[Hin|Havailable]]; [exact Hdone| |congruence].
  rewrite Hempty in Hin; contradiction.
Qed.

(** Any closed marked set includes every finite-round reference result. *)
Theorem reference_complete definitions s count :
  (forall x deps, Map.get E x definitions = Some deps ->
    forallb (fun y => FinSet.mem E y (marked s)) deps = true ->
    FinSet.mem E x (marked s) = true) ->
  forall x, reference E definitions count x = true -> FinSet.mem E x (marked s) = true.
Proof.
  intro Hclosed; induction count as [|count IH]; intros x Htrue; [discriminate|].
  cbn [reference] in Htrue; destruct (Map.get E x definitions) as [deps|] eqn:Hrule;
    [|discriminate].
  apply (Hclosed x deps Hrule); apply forallb_forall; intros y Hy; apply IH.
  exact (proj1 (forallb_forall _ _) Htrue y Hy).
Qed.

(** The actual solver is related to its exact finite binary-driver run. *)
Theorem solve_runs universe definitions :
  runs (step_c E (prepare E universe definitions))
    (S (length (node_order (prepare E universe definitions))))
    (initial E (prepare E universe definitions))
    (Cost.value (solve_c E universe definitions)).
Proof.
  unfold solve_c; rewrite Cost.value_bind; fold (prepare E universe definitions).
  rewrite solve_prepared_equation.
  pose proof (iterate_value (step_c E (prepare E universe definitions))
    (Pos.of_succ_nat (length (node_order (prepare E universe definitions))))
    (initial E (prepare E universe definitions))) as Hrun.
  rewrite SuccNat2Pos.id_succ in Hrun; exact Hrun.
Qed.

(** The actual countdown solver agrees with every sufficiently long finite-round reference. *)
Theorem solve_agrees universe definitions count :
  FinSet.wf E universe -> Map.wf E definitions -> rules_supported universe definitions ->
  FinSet.size universe <= count ->
  forall x,
    FinSet.mem E x (marked (last_state (Cost.value (solve_c E universe definitions)))) =
      reference E definitions count x.
Proof.
  intros Huniverse Hdefinitions Hsupported Hcount x.
  destruct (solve_finishes E HE universe definitions Huniverse Hdefinitions)
    as [final [Hresult [Hdrained [Hwf Hprocessed]]]].
  pose proof (solve_runs universe definitions) as Hrun; rewrite Hresult in Hrun.
  pose proof (runs_correct universe definitions _ _ _ Hdefinitions Hrun
    (initial_correct universe definitions Huniverse Hdefinitions)) as Hcorrect.
  change (correct universe definitions final) in Hcorrect.
  assert (Hclosed : forall x deps, Map.get E x definitions = Some deps ->
    forallb (fun y => FinSet.mem E y (marked final)) deps = true ->
    FinSet.mem E x (marked final) = true).
  { exact (terminal_closed universe definitions final Hsupported Hcorrect Hdrained). }
  destruct Hcorrect as [_ [_ [_ [_ [_ Hknown]]]]].
  rewrite Hresult; cbn [last_state].
  destruct (FinSet.mem E x (marked final)) eqn:Hmarked,
    (reference E definitions count x) eqn:Hreference; try reflexivity.
  - pose proof (reference_le definitions (processed final) count x ltac:(lia)
      (Hknown x Hmarked)) as Htrue; congruence.
  - pose proof (reference_complete definitions final count Hclosed x Hreference) as Htrue.
    congruence.
Qed.

End Correctness.

End NumberingLoopCorrect.
