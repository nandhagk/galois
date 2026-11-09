(** * Finite AND-dependency countdown worklists

    One indexed user occurrence consumes one pending dependency when its source is marked.
    For example, a repeated operand contributes two counter decrements in the same user bucket.
    Builds on: BaseIndex, BaseMap, BaseSet and CostLoop. *)

From Stdlib Require Import List Bool Arith Lia PArith NArith.
From Galois.Cost Require Import CostMonad CostList CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseIndex.
Import List.ListNotations Cost.Notations.

Local Open Scope nat_scope.

Module NumberingLoopWorklist.

Section Countdown.
Context {V : Type} (E : encoding V).

(** Missing rules are opaque and present rules require every dependency to be marked. *)
Definition rules_t := Map.t V (list V).

(** Prepared countdown data retains users with their original dependency multiplicities. *)
Record prepared : Type := Prepared {
  nodes : FinSet.t V;
  node_order : list V;
  rules : rules_t;
  users : Index.t V (V * V);
  counters : Map.t V nat;
  seeds : list V
}.

(** All queue entries are values from the prepared finite universe. *)
Record state : Type := State {
  todo : list V;
  marked : FinSet.t V;
  available : FinSet.t V;
  remaining : Map.t V nat;
  processed : nat
}.

(** Edge-row construction visits each dependency occurrence once and preserves its user. *)
Definition edge_rows_c (entries : list (V * list V)) : Cost.t (list (V * V)) :=
  fold_right_c (fun entry rest =>
    let* rows := map_c (fun dependency => Cost.ret (dependency, fst entry)) (snd entry) in
    app_c rows rest) [] entries.

(** The row observation is the ordered multiset of dependency/user pairs. *)
Theorem edge_rows_value entries :
  Cost.value (edge_rows_c entries) =
    flat_map (fun entry => map (fun dependency => (dependency, fst entry)) (snd entry)) entries.
Proof.
  unfold edge_rows_c; rewrite value_fold_right_c.
  induction entries as [|[user deps] rest IH]; [reflexivity|].
  cbn [fold_right flat_map]; autorewrite with galois_cost.
  rewrite ?value_map_c, ?value_app_c, IH; reflexivity.
Qed.

(** Preparation counts dependencies once, builds one user index and initializes zero-count seeds. *)
Definition prepare_c (universe : FinSet.t V) (definitions : rules_t) : Cost.t prepared :=
  let* order := FinSet.elements_c universe in
  let* entries := Map.elements_c definitions in
  let* rows := edge_rows_c entries in
  let* index := Index.group_by_c E (fun row => Cost.ret (fst row)) rows in
  let* counts := Map.map_c length_c definitions in
  let* ready := filter_c (fun x =>
    let* count := Map.get_c E x counts in
    Cost.ret (match count with Some 0 => true | _ => false end)) order in
  Cost.ret (Prepared universe order definitions index counts ready).

Definition prepare universe definitions := Cost.value (prepare_c universe definitions).

Definition initial_c (pr : prepared) : Cost.t state :=
  let* queued := FinSet.of_list_c E (seeds pr) in
  let* untouched := FinSet.diff_c (nodes pr) queued in
  Cost.ret (State (seeds pr) FinSet.empty untouched (counters pr) 0).

Definition initial pr := Cost.value (initial_c pr).

(** A notification enqueues a newly ready user only while its one-shot availability bit is set. *)
Definition notify_c s (edge : V * V) : Cost.t state :=
  let user := snd edge in
  let* count := Map.get_c E user (remaining s) in
  match count with
  | Some (S n) =>
    let* counts := Map.set_c E user n (remaining s) in
    match n with
    | 0 =>
      let* fresh := FinSet.mem_c E user (available s) in
      if fresh then
        let* untouched := FinSet.remove_c E user (available s) in
        Cost.ret (State (user :: todo s) (marked s) untouched counts (processed s))
      else Cost.ret (State (todo s) (marked s) (available s) counts (processed s))
    | S _ => Cost.ret (State (todo s) (marked s) (available s) counts (processed s))
    end
  | _ => Cost.ret s
  end.

Definition notify s edge := Cost.value (notify_c s edge).

Definition notifications_c uses s :=
  fold_left_c (fun s edge => Cost.step ;; notify_c s edge) uses s.

Definition notifications uses s := Cost.value (notifications_c uses s).

(** A pop marks one ready value, then processes exactly its prepared user bucket. *)
Definition step_c (pr : prepared) s : Cost.t (state + state) :=
  match todo s with
  | [] => Cost.ret (inr s)
  | x :: rest =>
    let* done := FinSet.add_c E x (marked s) in
    let* uses := Index.find_c E x (users pr) in
    let* next := notifications_c uses
      (State rest done (available s) (remaining s) (S (processed s))) in
    Cost.ret (inl next)
  end.

(** A raw solve retains exhausted state and processed-node count in the Cost driver's outcome. *)
Definition solve_prepared_c pr : Cost.t (state + state) :=
  let* start := initial_c pr in
  let* count := length_c (node_order pr) in
  iterate (step_c pr) (Pos.of_succ_nat count) start.

Definition solve_c universe definitions : Cost.t (state + state) :=
  let* pr := prepare_c universe definitions in solve_prepared_c pr.

Definition last_state (result : state + state) :=
  match result with
  | inl s => s
  | inr s => s
  end.

(** Prepared fields expose their constructor values while retaining stable users and seed order. *)
Theorem prepare_equation universe definitions :
  prepare universe definitions =
  let order := FinSet.elements universe in
  let entries := Map.elements definitions in
  let rows := Cost.value (edge_rows_c entries) in
  let index := Index.group_by E fst rows in
  let counts := Cost.value (Map.map_c length_c definitions) in
  let ready := filter (fun x =>
    match Map.get E x counts with Some 0 => true | _ => false end) order in
  Prepared universe order definitions index counts ready.
Proof.
  unfold prepare, prepare_c; rewrite !Cost.value_bind.
  rewrite Index.group_by_c_value, value_filter_c; reflexivity.
Qed.

(** Initial availability removes every seeded value before any user notification can enqueue it. *)
Theorem initial_equation pr :
  initial pr =
    State (seeds pr) FinSet.empty
      (FinSet.diff (nodes pr) (FinSet.of_list E (seeds pr))) (counters pr) 0.
Proof.
  reflexivity.
Qed.

(** Notification's equation exposes its single counter update and guarded one-shot enqueue. *)
Theorem notify_equation s edge :
  notify s edge =
  let user := snd edge in
  match Map.get E user (remaining s) with
  | Some (S n) =>
    let counts := Map.set E user n (remaining s) in
    match n with
    | 0 =>
      if FinSet.mem E user (available s)
      then State (user :: todo s) (marked s)
        (FinSet.remove E user (available s)) counts (processed s)
      else State (todo s) (marked s) (available s) counts (processed s)
    | S _ => State (todo s) (marked s) (available s) counts (processed s)
    end
  | _ => s
  end.
Proof.
  unfold notify, notify_c; rewrite Cost.value_bind; fold (Map.get E (snd edge) (remaining s)).
  destruct (Map.get E (snd edge) (remaining s)) as [[|n]|]; try reflexivity.
  autorewrite with galois_cost; fold (Map.set E (snd edge) n (remaining s)).
  destruct n; [|reflexivity].
  autorewrite with galois_cost; fold (FinSet.mem E (snd edge) (available s)).
  destruct (FinSet.mem E (snd edge) (available s)); reflexivity.
Qed.

(** A notification never changes already marked values or the number of popped nodes. *)
Theorem notify_observations s edge :
  marked (notify s edge) = marked s /\ processed (notify s edge) = processed s.
Proof.
  rewrite notify_equation; cbn zeta.
  destruct (Map.get E (snd edge) (remaining s)) as [[|[|n]]|]; try (split; reflexivity).
  destruct (FinSet.mem E (snd edge) (available s)); split; reflexivity.
Qed.

(** A notification preserves actual set and counter-map representation validity. *)
Theorem notify_wf s edge :
  FinSet.wf E (marked s) -> FinSet.wf E (available s) -> Map.wf E (remaining s) ->
  FinSet.wf E (marked (notify s edge)) /\
  FinSet.wf E (available (notify s edge)) /\ Map.wf E (remaining (notify s edge)).
Proof.
  intros Hmarked Havailable Hremaining; rewrite notify_equation; cbn zeta.
  destruct (Map.get E (snd edge) (remaining s)) as [[|[|n]]|].
  - split; [exact Hmarked|split; assumption].
  - destruct (FinSet.mem E (snd edge) (available s)); split; [exact Hmarked| |exact Hmarked|].
    + split; [now apply FinSet.wf_remove|now apply Map.wf_set].
    + split; [exact Havailable|now apply Map.wf_set].
  - split; [exact Hmarked|split; [exact Havailable|now apply Map.wf_set]].
  - split; [exact Hmarked|split; assumption].
Qed.

(** Stored set and counter maps retain their actual dictionary representation invariants. *)
Definition state_wf s : Prop :=
  FinSet.wf E (marked s) /\ FinSet.wf E (available s) /\ Map.wf E (remaining s).

Definition potential s := FinSet.size (available s) + length (todo s).

Local Lemma size_remove_present available user :
  FinSet.wf E available -> FinSet.mem E user available = true ->
  FinSet.size available = S (FinSet.size (FinSet.remove E user available)).
Proof.
  intros Hwf Hmem.
  change (Map.size available = S (Map.size (Map.remove E user available))).
  apply (Map.size_remove E user tt available Hwf).
  apply FinSet.mem_spec; exact Hmem.
Qed.

(** Every guarded enqueue spends one availability unit and adds one queue unit. *)
Theorem notify_potential s edge :
  state_wf s -> potential (notify s edge) = potential s.
Proof.
  intros [_ [Havailable _]]; rewrite notify_equation; cbn zeta.
  destruct (Map.get E (snd edge) (remaining s)) as [[|[|n]]|]; try reflexivity.
  destruct (FinSet.mem E (snd edge) (available s)) eqn:Hfresh; [|reflexivity].
  unfold potential; cbn [available todo length].
  pose proof (size_remove_present _ _ Havailable Hfresh); lia.
Qed.

(** A complete user bucket preserves validity, queue credit and the already marked set. *)
Theorem notifications_preserved uses s :
  state_wf s ->
  state_wf (notifications uses s) /\
  potential (notifications uses s) = potential s /\
  processed (notifications uses s) = processed s /\
  marked (notifications uses s) = marked s.
Proof.
  unfold notifications, notifications_c; rewrite value_fold_left_c.
  change (state_wf s ->
    state_wf (fold_left notify uses s) /\
    potential (fold_left notify uses s) = potential s /\
    processed (fold_left notify uses s) = processed s /\
    marked (fold_left notify uses s) = marked s).
  revert s; induction uses as [|edge rest IH]; intros s Hs.
  - split; [exact Hs|split; [reflexivity|split; reflexivity]].
  - cbn [fold_left].
    assert (Hnext : state_wf (notify s edge)).
    { destruct Hs as [Hmarked [Havailable Hremaining]].
      exact (notify_wf s edge Hmarked Havailable Hremaining). }
    destruct (IH _ Hnext) as [Hlast [Hpotential [Hprocessed Hmarked]]].
    destruct (notify_observations s edge) as [Hmarked' Hprocessed'].
    split; [exact Hlast|split; [rewrite Hpotential; now apply notify_potential|]].
    split; congruence.
Qed.

(** The runtime pop equation uses exactly the prepared users of the popped value. *)
Theorem step_equation pr s :
  Cost.value (step_c pr s) =
  match todo s with
  | [] => inr s
  | x :: rest =>
    inl (notifications (Index.find E x (users pr))
      (State rest (FinSet.add E x (marked s)) (available s) (remaining s) (S (processed s))))
  end.
Proof.
  unfold step_c; destruct (todo s) as [|x rest]; [reflexivity|].
  autorewrite with galois_cost; reflexivity.
Qed.

(** Every continuing runtime step strictly decreases queue credit and increments its pop counter. *)
Theorem step_progress pr s :
  state_wf s ->
  match Cost.value (step_c pr s) with
  | inl next =>
    state_wf next /\ potential next < potential s /\ processed next = S (processed s)
  | inr final => state_wf final /\ final = s
  end.
Proof.
  intro Hs; rewrite step_equation; destruct (todo s) as [|x rest] eqn:Htodo.
  - split; [exact Hs|reflexivity].
  - assert (Hpop : state_wf
      (State rest (FinSet.add E x (marked s)) (available s) (remaining s) (S (processed s)))).
    { destruct Hs as [Hmarked [Havailable Hremaining]].
      split; [now apply FinSet.wf_add|split; assumption]. }
    destruct (notifications_preserved (Index.find E x (users pr)) _ Hpop)
      as [Hnext [Hpotential [Hprocessed _]]].
    split; [exact Hnext|split; [|exact Hprocessed]].
    unfold potential in *; rewrite Htodo; cbn [todo available length] in *; lia.
Qed.

(** Exhaustion requires one strict queue-credit decrease per consumed unit of fuel. *)
Theorem exhausted_progress pr count start final :
  runs (step_c pr) count start (inl final) -> state_wf start ->
  state_wf final /\ potential final + count <= potential start.
Proof.
  intro Hrun; remember (inl final) as result eqn:Hresult.
  induction Hrun as [s|count s result Hstop|count s next result Hnext Hrun IH]; intro Hs.
  - injection Hresult as <-; split; [exact Hs|lia].
  - discriminate.
  - pose proof (step_progress pr s Hs) as Hprogress.
    rewrite Hnext in Hprogress; destruct Hprogress as [Hwf [Hless _]].
    destruct (IH Hresult Hwf) as [Hfinal Hbound]; split; [exact Hfinal|lia].
Qed.

(** The countdown solver finishes whenever its supplied fuel exceeds initialized queue credit. *)
Theorem credit_finishes pr fuel start :
  state_wf start -> potential start < Pos.to_nat fuel ->
  exists final, Cost.value (iterate (step_c pr) fuel start) = inr final.
Proof.
  intros Hwf Hfuel; pose proof (iterate_value (step_c pr) fuel start) as Hrun.
  destruct (Cost.value (iterate (step_c pr) fuel start)) as [exhausted|final] eqn:Hresult.
  - destruct (exhausted_progress pr _ _ _ Hrun Hwf) as [_ Hbound]; lia.
  - exists final; reflexivity.
Qed.

Section Laws.
Context (HE : encoding_laws E).

Local Lemma nodup_append {A} (xs ys : list A) :
  NoDup xs -> NoDup ys ->
  (forall x, In x xs -> ~ In x ys) -> NoDup (xs ++ ys).
Proof.
  intro Hxs; induction Hxs as [|x rest Hfresh Hrest IH]; intros Hys Hdisjoint.
  - exact Hys.
  - cbn [app]; constructor.
    + rewrite in_app_iff; intros [Hin|Hin].
      * exact (Hfresh Hin).
      * exact (Hdisjoint x (or_introl eq_refl) Hin).
    + apply IH; [exact Hys|intros y Hy; apply Hdisjoint; now right].
Qed.

(** Preparation establishes the actual initial set and counter-map certificates. *)
Theorem initial_wf universe definitions :
  FinSet.wf E universe -> Map.wf E definitions ->
  state_wf (initial (prepare universe definitions)).
Proof.
  intros Huniverse Hdefinitions; rewrite initial_equation, prepare_equation.
  split; [apply FinSet.wf_empty|split].
  - apply FinSet.wf_diff; [exact Huniverse|apply FinSet.wf_of_list].
  - rewrite Map.map_c_value; apply Map.wf_map; exact Hdefinitions.
Qed.

(** Initial queue credit is bounded by the finite universe, including zero-count seeds. *)
Theorem initial_potential_bound universe definitions :
  FinSet.wf E universe ->
  potential (initial (prepare universe definitions)) <=
    length (node_order (prepare universe definitions)).
Proof.
  intro Huniverse; set (pr := prepare universe definitions).
  assert (Hnodes : nodes pr = universe).
  { unfold pr; rewrite prepare_equation; reflexivity. }
  assert (Horder : node_order pr = FinSet.elements universe).
  { unfold pr; rewrite prepare_equation; reflexivity. }
  assert (Hseed_nodup : NoDup (seeds pr)).
  { unfold pr; rewrite prepare_equation; apply NoDup_filter.
    exact (FinSet.elements_nodup E universe Huniverse). }
  assert (Hseed_in : incl (seeds pr) (FinSet.elements universe)).
  { unfold pr; rewrite prepare_equation; intros x Hx; apply filter_In in Hx; tauto. }
  set (untouched := FinSet.diff universe (FinSet.of_list E (seeds pr))).
  assert (Huntouched : FinSet.wf E untouched).
  { apply FinSet.wf_diff; [exact Huniverse|apply FinSet.wf_of_list]. }
  assert (Hdisjoint : forall x, In x (FinSet.elements untouched) -> ~ In x (seeds pr)).
  { intros x Hx Hseed.
    apply (proj1 (FinSet.elements_spec E HE x untouched Huntouched)) in Hx.
    unfold untouched in Hx; rewrite FinSet.mem_diff in Hx
      by (try exact Huniverse; apply FinSet.wf_of_list).
    apply andb_true_iff in Hx as [_ Hnot]; apply negb_true_iff in Hnot.
    assert (Hmember : FinSet.mem E x (FinSet.of_list E (seeds pr)) = true).
    { rewrite FinSet.mem_of_list; apply existsb_exists; exists x.
      split; [exact Hseed|apply eqb_refl]. }
    congruence. }
  unfold potential; rewrite initial_equation; cbn [available todo].
  rewrite Hnodes, Horder; fold untouched.
  rewrite FinSet.size_elements, <- length_app.
  apply NoDup_incl_length.
  - apply nodup_append.
    + exact (FinSet.elements_nodup E untouched Huntouched).
    + exact Hseed_nodup.
    + exact Hdisjoint.
  - intros x Hx; apply in_app_iff in Hx as [Hx|Hx]; [|now apply Hseed_in].
    apply (proj2 (FinSet.elements_spec E HE x universe Huniverse)).
    apply (proj1 (FinSet.elements_spec E HE x untouched Huntouched)) in Hx.
    unfold untouched in Hx; rewrite FinSet.mem_diff in Hx
      by (try exact Huniverse; apply FinSet.wf_of_list).
    apply andb_true_iff in Hx; tauto.
Qed.

(** A run preserves stored certificates and can spend at most its starting queue credit. *)
Theorem runs_balance pr count start result :
  runs (step_c pr) count start result -> state_wf start ->
  state_wf (last_state result) /\
  processed (last_state result) + potential (last_state result) <=
    processed start + potential start.
Proof.
  intro Hrun; induction Hrun as [s|count s final Hstop|
    count s next result Hnext Hrun IH]; intro Hs.
  - split; [exact Hs|reflexivity].
  - pose proof (step_progress pr s Hs) as Hstep; rewrite Hstop in Hstep.
    destruct Hstep as [Hfinal ->]; split; [exact Hfinal|reflexivity].
  - pose proof (step_progress pr s Hs) as Hstep; rewrite Hnext in Hstep.
    destruct Hstep as [Hnext_wf [Hless Hprocessed]].
    destruct (IH Hnext_wf) as [Hfinal Hbalance]; split; [exact Hfinal|lia].
Qed.

(** Stopping is an actual empty queue, rather than exhaustion reinterpreted as closure. *)
Theorem stopped_drained pr count start final :
  runs (step_c pr) count start (inr final) -> todo final = [].
Proof.
  intro Hrun; remember (inr final) as result eqn:Hresult.
  induction Hrun as [s|count s last Hstop|count s next result Hnext Hrun IH].
  - discriminate.
  - rewrite step_equation in Hstop; destruct (todo s) as [|x rest] eqn:Htodo;
      [|discriminate].
    injection Hstop as <-; injection Hresult as <-; exact Htodo.
  - now apply IH.
Qed.

(** The raw solver equation exposes its one initialized state and exact finite-universe budget. *)
Theorem solve_prepared_equation pr :
  Cost.value (solve_prepared_c pr) =
    Cost.value (iterate (step_c pr) (Pos.of_succ_nat (length (node_order pr))) (initial pr)).
Proof.
  unfold solve_prepared_c; rewrite !Cost.value_bind, value_length_c; reflexivity.
Qed.

(** The actual prepared solve finishes and pops at most one finite-universe budget of nodes. *)
Theorem solve_finishes universe definitions :
  FinSet.wf E universe -> Map.wf E definitions ->
  exists final,
    Cost.value (solve_c universe definitions) = inr final /\
    todo final = [] /\ state_wf final /\ processed final <= FinSet.size universe.
Proof.
  intros Huniverse Hdefinitions; set (pr := prepare universe definitions).
  pose proof (initial_wf universe definitions Huniverse Hdefinitions) as Hinitial.
  pose proof (initial_potential_bound universe definitions Huniverse) as Hcredit.
  fold pr in Hinitial, Hcredit.
  destruct (credit_finishes pr (Pos.of_succ_nat (length (node_order pr))) (initial pr)
    Hinitial ltac:(rewrite SuccNat2Pos.id_succ; lia)) as [final Hfinal].
  pose proof (iterate_value (step_c pr) (Pos.of_succ_nat (length (node_order pr)))
    (initial pr)) as Hrun.
  rewrite Hfinal in Hrun.
  destruct (runs_balance pr _ _ _ Hrun Hinitial) as [Hwf Hbalance].
  exists final; split.
  - unfold solve_c; rewrite Cost.value_bind; fold pr; rewrite solve_prepared_equation.
    exact Hfinal.
  - split; [exact (stopped_drained pr _ _ _ Hrun)|split; [exact Hwf|]].
    change (state_wf final) in Hwf.
    cbn [last_state] in Hbalance.
    assert (Horder : length (node_order pr) = FinSet.size universe).
    { unfold pr; rewrite prepare_equation; symmetry; apply FinSet.size_elements. }
    assert (Hprocessed : processed (initial pr) = 0).
    { rewrite initial_equation; reflexivity. }
    rewrite Hprocessed in Hbalance; lia.
Qed.

End Laws.

(** The pure finite-round specification starts with no marked inside-body values. *)
Fixpoint reference (definitions : rules_t) (count : nat) (x : V) : bool :=
  match count with
  | 0 => false
  | S n =>
    match Map.get E x definitions with
    | None => false
    | Some dependencies => forallb (reference definitions n) dependencies
    end
  end.

End Countdown.

End NumberingLoopWorklist.
