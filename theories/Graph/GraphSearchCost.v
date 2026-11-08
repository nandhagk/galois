(** * Global search cost bounds

    Global graph credit and visitor potential bound the actual costed search.
    For example, a step that enters a child dispatches both its edge and its entry callback.
    Builds on: GraphSearch, GraphSearchExact and the costed list potential theorem. *)

From Stdlib Require Import List NArith Lia Permutation.
From Galois.Cost Require Import CostMonad CostList CostLoop CostBound.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet BaseIntern BaseIndex.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearchSpec GraphSearch
  GraphSearchInvariant GraphSearchExact.
Import List.ListNotations Cost.Notations.

Module SearchCost.
Local Open Scope N_scope.

(** Width bounds cover all valid IDs and every supplied root, including unknown root IDs. *)
Definition width_bound {V E} (p : Prepared.t V E) roots w :=
  forall v, Prepared.valid_id p v \/ In v roots ->
    (key_bits positive_encoding v <= w)%N.

Definition id_cost w := 1 + 2 * w.

Local Lemma get_cost_le {A} w v (m : Map.t positive A) :
  key_bits positive_encoding v <= w ->
    Cost.ticks (Map.get_c positive_encoding v m) <= id_cost w.
Proof.
  intro Hwidth. rewrite Map.get_cost.
  pose proof (encode_cost_bound positive_encoding_cost_laws v).
  fold (key_bits positive_encoding v). unfold id_cost. nia.
Qed.

Local Lemma set_cost_le {A} w v a (m : Map.t positive A) :
  key_bits positive_encoding v <= w ->
    Cost.ticks (Map.set_c positive_encoding v a m) <= id_cost w.
Proof.
  intro Hwidth. rewrite Map.set_cost.
  pose proof (encode_cost_bound positive_encoding_cost_laws v).
  fold (key_bits positive_encoding v). unfold id_cost. nia.
Qed.

Local Lemma mem_cost_le w v s :
  key_bits positive_encoding v <= w ->
    Cost.ticks (FinSet.mem_c positive_encoding v s) <= id_cost w.
Proof.
  intro Hwidth. rewrite FinSet.mem_cost.
  pose proof (encode_cost_bound positive_encoding_cost_laws v).
  fold (key_bits positive_encoding v). unfold id_cost. nia.
Qed.

Local Lemma add_cost_le w v s :
  key_bits positive_encoding v <= w ->
    Cost.ticks (FinSet.add_c positive_encoding v s) <= id_cost w.
Proof.
  intro Hwidth. rewrite FinSet.add_cost.
  pose proof (encode_cost_bound positive_encoding_cost_laws v).
  fold (key_bits positive_encoding v). unfold id_cost. nia.
Qed.

(** Admission charges both optional membership checks even though rejected targets emit no event. *)
Theorem admits_cost w scope v :
  key_bits positive_encoding v <= w ->
    Cost.ticks (Scope.admits_c scope v) <= 1 + 2 * id_cost w.
Proof.
  intro Hwidth. unfold Scope.admits_c. autorewrite with galois_cost.
  fold (FinSet.mem positive_encoding v (Scope.blocked scope)).
  pose proof (mem_cost_le w v (Scope.blocked scope) Hwidth) as Hblocked.
  destruct (FinSet.mem positive_encoding v (Scope.blocked scope));
    autorewrite with galois_cost; [nia|].
  destruct (Scope.within scope) as [region|]; autorewrite with galois_cost; [|nia].
  pose proof (mem_cost_le w v region Hwidth). nia.
Qed.

(** Discovery retains all selected-parent, numbering and visited-map insertion charges. *)
Theorem discover_cost {E} w v via (c : SearchRun.core E) :
  key_bits positive_encoding v <= w ->
    Cost.ticks (SearchRun.discover_c v via c) <= 1 + 3 * id_cost w.
Proof.
  intro Hwidth. unfold SearchRun.discover_c. destruct via as [edge|];
    autorewrite with galois_cost.
  - pose proof (set_cost_le w v edge (SearchRun.parents c) Hwidth).
    pose proof (set_cost_le w v (SearchRun.pre_clock c) (SearchRun.pre_index c) Hwidth).
    pose proof (add_cost_le w v (SearchRun.seen c) Hwidth). nia.
  - pose proof (set_cost_le w v (SearchRun.pre_clock c) (SearchRun.pre_index c) Hwidth).
    pose proof (add_cost_le w v (SearchRun.seen c) Hwidth). nia.
Qed.

(** Finishing charges the actual exit-number map insertion. *)
Theorem finish_cost {E} w v (c : SearchRun.core E) :
  key_bits positive_encoding v <= w ->
    Cost.ticks (SearchRun.finish_c v c) <= 1 + id_cost w.
Proof.
  intro Hwidth. unfold SearchRun.finish_c. autorewrite with galois_cost.
  pose proof (set_cost_le w v (SearchRun.post_clock c) (SearchRun.post_index c) Hwidth). nia.
Qed.

(** Current-color classification uses at most membership and three numeric-map lookups. *)
Theorem edge_kind_cost {E} w (c : SearchRun.core E) u v :
  key_bits positive_encoding u <= w -> key_bits positive_encoding v <= w ->
    Cost.ticks (SearchRun.edge_kind_c c u v) <= 4 * id_cost w.
Proof.
  intros Hu Hv.
  pose proof (mem_cost_le w v (SearchRun.seen c) Hv).
  pose proof (get_cost_le w v (SearchRun.post_index c) Hv).
  pose proof (get_cost_le w u (SearchRun.pre_index c) Hu).
  pose proof (get_cost_le w v (SearchRun.pre_index c) Hv).
  unfold SearchRun.edge_kind_c. rewrite Cost.ticks_bind.
  fold (FinSet.mem positive_encoding v (SearchRun.seen c)).
  destruct (FinSet.mem positive_encoding v (SearchRun.seen c)); [|rewrite Cost.ticks_ret; nia].
  rewrite Cost.ticks_bind. fold (Map.get positive_encoding v (SearchRun.post_index c)).
  destruct (Map.get positive_encoding v (SearchRun.post_index c));
    autorewrite with galois_cost; nia.
Qed.

(** Runtime inverse-name lookup charges the actual ID-keyed map operation. *)
Theorem name_cost {V E} (p : Prepared.t V E) w v :
  key_bits positive_encoding v <= w ->
    Cost.ticks (Prepared.name_of_c p v) <= id_cost w.
Proof.
  intro Hwidth. unfold Prepared.name_of_c. rewrite Intern.key_of_cost.
  now apply get_cost_le.
Qed.

(** Successor lookup reads the prepared map and never invokes a target callback. *)
Theorem successors_cost {V E} (p : Prepared.t V E) w v :
  key_bits positive_encoding v <= w ->
    Cost.ticks (Prepared.succ_edges_c p v) <= id_cost w.
Proof.
  intro Hwidth. unfold Prepared.succ_edges_c. rewrite Index.find_cost.
  now apply get_cost_le.
Qed.

Local Lemma edge_transition_cost {V E} (p : Prepared.t V E) w scope c u e v pending rest :
  key_bits positive_encoding u <= w -> key_bits positive_encoding v <= w ->
    Cost.ticks (SearchRun.transition_c p scope (((u, (e, v) :: pending) :: rest), c)) <=
      3 + 11 * id_cost w.
Proof.
  intros Hu Hv.
  pose proof (admits_cost w scope v Hv) as Hscope.
  pose proof (name_cost p w v Hv) as Hname.
  pose proof (edge_kind_cost w c u v Hu Hv) as Hkind.
  pose proof (discover_cost w v (Some (e, u)) c Hv) as Hdiscover.
  pose proof (successors_cost p w v Hv) as Hsuccessors.
  unfold SearchRun.transition_c. autorewrite with galois_cost.
  fold (Scope.admits scope v).
  destruct (Scope.admits scope v); autorewrite with galois_cost; [|nia].
  fold (Prepared.name_of p v).
  destruct (Prepared.name_of p v); autorewrite with galois_cost; [|nia].
  fold (SearchRun.edge_kind c u v).
  destruct (SearchRun.edge_kind c u v); autorewrite with galois_cost; nia.
Qed.

(** Primitive transition work is linear in actual ID width, including rejected occurrences. *)
Theorem transition_cost {V E} (p : Prepared.t V E) scope roots w state :
  Prepared.ready p -> width_bound p roots w ->
  SearchInvariant.sound_work p scope roots state ->
    Cost.ticks (SearchRun.transition_c p scope state) <= 3 + 11 * id_cost w.
Proof.
  intros Hready Hwidth Hsound. destruct state as [stack c].
  destruct stack as [|[u [|[e v] pending]] rest].
  - unfold SearchRun.transition_c. autorewrite with galois_cost. unfold id_cost. nia.
  - destruct (SearchInvariant.valid_frames _ _ _ _ Hsound u [] (or_introl eq_refl))
      as [_ [Hu _]].
    pose proof (finish_cost w u c (Hwidth u (or_introl Hu))) as Hfinish.
    unfold SearchRun.transition_c. autorewrite with galois_cost. nia.
  - destruct (SearchInvariant.valid_frames _ _ _ _ Hsound u ((e, v) :: pending)
      (or_introl eq_refl)) as [_ [Hu [_ Hedges]]].
    destruct (SearchInvariant.successor_arc p u e v Hready Hu
      (Hedges _ (or_introl eq_refl))) as [_ Hv].
    apply edge_transition_cost; apply Hwidth; now left.
Qed.

(** Visitor credits telescope over actual events and retain each dispatch-list traversal tick. *)
Theorem apply_events_cost {E S} (vis : Visitor.t E S) Phi kv evs s :
  Visitor.amortised vis Phi kv ->
  (Cost.ticks (SearchRun.apply_events_c vis evs s) +
    Phi (SearchRun.apply_events vis evs s) <=
    N.of_nat (length evs) * (kv + 1) + Phi s)%N.
Proof.
  intro Hamortised.
  pose proof (ticks_fold_left_c_potential
    (fun s ev => Visitor.apply_c vis ev s) (fun _ => True) Phi kv evs s) as Hfold.
  assert (Hstep : forall s ev, True -> In ev evs ->
    True /\ (Cost.ticks (Visitor.apply_c vis ev s) +
      Phi (Visitor.apply vis ev s) <= kv + Phi s)%N).
  { intros state ev _ _. split; [exact I|apply Hamortised]. }
  specialize (Hfold Hstep I).
  fold (SearchRun.apply_events_c vis evs s) in Hfold.
  rewrite SearchRun.apply_events_value in Hfold. exact Hfold.
Qed.

(** Every transition emits at most two eligible events, regardless of rejected adjacency work. *)
Theorem transition_events_bound {V E} (p : Prepared.t V E) scope w :
  (length (snd (SearchRun.transition p scope w)) <= 2)%nat.
Proof.
  destruct w as [stack c]. rewrite SearchRun.step_equation.
  destruct stack as [|[u [|[e v] pending]] rest]; [cbn; lia|cbn; lia|].
  destruct (Scope.admits scope v); [|cbn; lia].
  destruct (Prepared.name_of p v); [|cbn; lia].
  destruct (SearchRun.edge_kind c u v); cbn; lia.
Qed.

(** Each actual step spends its primitive work and at most two amortised visitor dispatches. *)
Theorem step_visitor_cost {V E S} (p : Prepared.t V E) (vis : Visitor.t E S)
    Phi kv scope w s :
  Visitor.amortised vis Phi kv ->
  (Cost.ticks (SearchRun.step_c p vis scope (w, s)) +
    Phi (snd (SearchRun.unwrap (Cost.value (SearchRun.step_c p vis scope (w, s))))) <=
    Cost.ticks (SearchRun.transition_c p scope w) + 2 * (kv + 1) + Phi s)%N.
Proof.
  intro Hamortised.
  pose proof (apply_events_cost vis Phi kv
    (snd (SearchRun.transition p scope w)) s Hamortised) as Hvisitor.
  pose proof (transition_events_bound p scope w) as Hlength.
  unfold SearchRun.step_c. rewrite Cost.ticks_bind, Cost.value_bind.
  fold (SearchRun.transition p scope w).
  destruct (SearchRun.transition p scope w) as [[w'|w'] evs];
    cbn [fst snd] in Hvisitor, Hlength |- *;
    rewrite Cost.ticks_bind, Cost.value_bind, SearchRun.apply_events_value;
    rewrite Cost.value_ret;
    cbn [SearchRun.unwrap snd]; rewrite Cost.ticks_ret, N.add_0_r.
  all: assert (HlengthN : (N.of_nat (length evs) <= 2)%N).
  all: try (destruct (length evs) as [|[|n]]; [cbn; lia|cbn; lia|];
    assert (Hn : n = 0%nat) by lia; subst n; reflexivity).
  all: nia.
Qed.

Local Lemma continue_credit {A} (I : A -> Prop) (credit : A -> N) d start
    (m : Cost.t (A + A)) next :
  (match Cost.value m with
  | inl a => I a /\ Cost.ticks m + credit a + 1 <= credit start
  | inr a => I a /\ Cost.ticks m + credit a <= credit start + d
  end) ->
  (forall a, I a ->
    match Cost.value (next a) with
    | inl b => I b /\ Cost.ticks (next a) + credit b + 1 <= credit a
    | inr b => I b /\ Cost.ticks (next a) + credit b <= credit a + d
    end) ->
  match Cost.value (continue_c m next) with
  | inl a => I a /\ 1 + Cost.ticks (continue_c m next) + credit a + 1 <= credit start
  | inr a => I a /\ 1 + Cost.ticks (continue_c m next) + credit a <= credit start + d + 1
  end.
Proof.
  intros Hfirst Hnext. rewrite value_continue_c, ticks_continue_c.
  destruct (Cost.value m) as [a|a].
  - destruct Hfirst as [Ha Hfirst]. specialize (Hnext a Ha).
    destruct (Cost.value (next a)) as [b|b]; destruct Hnext as [Hb Hnext];
      split; [exact Hb|nia|exact Hb|nia].
  - destruct Hfirst as [Ha Hfirst]. split; [exact Ha|nia].
Qed.

Local Lemma continue_plain_credit {A} (I : A -> Prop) (credit : A -> N) d start
    (m : Cost.t (A + A)) next :
  (match Cost.value m with
  | inl a => I a /\ Cost.ticks m + credit a + 1 <= credit start
  | inr a => I a /\ Cost.ticks m + credit a <= credit start + d
  end) ->
  (forall a, I a ->
    match Cost.value (next a) with
    | inl b => I b /\ Cost.ticks (next a) + credit b + 1 <= credit a
    | inr b => I b /\ Cost.ticks (next a) + credit b <= credit a + d
    end) ->
  match Cost.value (continue_c m next) with
  | inl a => I a /\ Cost.ticks (continue_c m next) + credit a + 1 <= credit start
  | inr a => I a /\ Cost.ticks (continue_c m next) + credit a <= credit start + d
  end.
Proof.
  intros Hfirst Hnext.
  pose proof (continue_credit I credit d start m next Hfirst Hnext) as Hcredit.
  destruct (Cost.value (continue_c m next)); destruct Hcredit; split; try assumption; nia.
Qed.

(** Binary descent is paid separately from the conserved graph and visitor credit. *)
Theorem iterate_credit {A} (step : A -> Cost.t (A + A)) (I : A -> Prop)
    (credit : A -> N) fuel start :
  (forall a, I a ->
    match Cost.value (step a) with
    | inl b => I b /\ Cost.ticks (step a) + credit b + 3 <= credit a
    | inr b => I b /\ Cost.ticks (step a) + credit b <= credit a + 1
    end) ->
  I start ->
  match Cost.value (iterate step fuel start) with
  | inl a => I a /\ Cost.ticks (iterate step fuel start) + credit a + 1 <= credit start
  | inr a =>
    I a /\ Cost.ticks (iterate step fuel start) + credit a <=
      credit start + (1 + N.pos (Pos.size fuel))
  end.
Proof.
  intros Hstep. revert start. induction fuel as [fuel IH|fuel IH|]; intros start HI.
  - assert (Hfirst :
      match Cost.value (Cost.step ;; step start) with
      | inl b => I b /\ Cost.ticks (Cost.step ;; step start) + credit b + 1 <= credit start
      | inr b => I b /\ Cost.ticks (Cost.step ;; step start) + credit b <=
          credit start + (1 + N.pos (Pos.size fuel))
      end).
    { specialize (Hstep start HI). autorewrite with galois_cost.
      destruct (Cost.value (step start)); destruct Hstep; split; try assumption; nia. }
    pose proof (continue_credit I credit (1 + N.pos (Pos.size fuel)) start
      (Cost.step ;; step start)
      (fun a => continue_c (iterate step fuel a) (iterate step fuel)) Hfirst
      (fun a Ha => continue_plain_credit I credit (1 + N.pos (Pos.size fuel)) a
        (iterate step fuel a) (iterate step fuel) (IH a Ha) IH))
      as Hcredit.
    cbn [iterate]. autorewrite with galois_cost.
    destruct (Cost.value (continue_c (Cost.step ;; step start)
      (fun a => continue_c (iterate step fuel a) (iterate step fuel))));
      destruct Hcredit; split; try assumption;
      change (N.pos (Pos.size (xI fuel))) with (N.succ (N.pos (Pos.size fuel))); nia.
  - pose proof (continue_credit I credit (1 + N.pos (Pos.size fuel)) start
      (iterate step fuel start) (iterate step fuel) (IH start HI) IH) as Hcredit.
    cbn [iterate]. autorewrite with galois_cost.
    destruct (Cost.value (continue_c (iterate step fuel start) (iterate step fuel)));
      destruct Hcredit; split; try assumption;
      change (N.pos (Pos.size (xO fuel))) with (N.succ (N.pos (Pos.size fuel))); nia.
  - specialize (Hstep start HI). cbn [iterate]. autorewrite with galois_cost.
    destruct (Cost.value (step start)); destruct Hstep; split; try assumption;
      cbn [Pos.size].
    all: nia.
Qed.

Definition step_k w kv := 8 + 11 * id_cost w + 2 * kv.

Definition state_credit {V E S} (p : Prepared.t V E) (Phi : S -> N) w kv
    (state : SearchRun.work E * S) :=
  step_k w kv * N.of_nat (SearchInvariant.work_measure p (fst state)) + Phi (snd state).

Definition state_invariant {V E S} (p : Prepared.t V E) scope roots
    (state : SearchRun.work E * S) :=
  SearchInvariant.representation (snd (fst state)) /\
    SearchInvariant.sound_work p scope roots (fst state).

Local Lemma stop_same {V E} (p : Prepared.t V E) scope state final evs :
  SearchRun.transition p scope state = (inr final, evs) ->
    final = state /\ evs = [] /\ fst state = [].
Proof.
  destruct state as [stack c]. rewrite SearchRun.step_equation.
  destruct stack as [|[u [|[e v] pending]] rest].
  - intro H. inversion H. auto.
  - discriminate.
  - destruct (Scope.admits scope v); [|discriminate].
    destruct (Prepared.name_of p v); [|discriminate].
    destruct (SearchRun.edge_kind c u v); discriminate.
Qed.

(** Conserved graph credit pays for primitive work while visitor credit pays arbitrary callees. *)
Theorem step_credit {V E S} (p : Prepared.t V E) (vis : Visitor.t E S)
    Phi kv scope roots w state :
  Prepared.ready p -> width_bound p roots w -> Visitor.amortised vis Phi kv ->
  state_invariant p scope roots state ->
  match Cost.value (SearchRun.step_c p vis scope state) with
  | inl next =>
    state_invariant p scope roots next /\
    Cost.ticks (SearchRun.step_c p vis scope state) + state_credit p Phi w kv next + 3 <=
      state_credit p Phi w kv state
  | inr final =>
    state_invariant p scope roots final /\
    Cost.ticks (SearchRun.step_c p vis scope state) + state_credit p Phi w kv final <=
      state_credit p Phi w kv state + 1
  end.
Proof.
  intros Hready Hwidth Hamortised. destruct state as [work s]. intros [Hrep Hsound].
  pose proof (step_visitor_cost p vis Phi kv scope work s Hamortised) as Hvisitor.
  pose proof (transition_cost p scope roots w work Hready Hwidth Hsound) as Hprimitive.
  pose proof (SearchInvariant.transition_representation p scope work Hrep) as Hrep'.
  pose proof (SearchInvariant.transition_sound p scope roots work Hready Hrep Hsound)
    as Hsound'.
  rewrite SearchRun.step_erases in Hvisitor |- *.
  destruct (SearchRun.transition p scope work) as [[next|final] evs] eqn:Htransition.
  - split; [split; assumption|].
    pose proof (SearchInvariant.transition_decreases p scope work next evs
      Hready Hrep Htransition) as Hdecrease.
    cbn [SearchRun.unwrap fst snd] in Hvisitor.
    unfold state_credit. cbn [fst snd].
    assert (HdecreaseN :
      N.of_nat (SearchInvariant.work_measure p next) + 1 <=
        N.of_nat (SearchInvariant.work_measure p work)) by lia.
    unfold step_k. nia.
  - destruct (stop_same p scope work final evs Htransition) as [-> [-> Hempty]].
    destruct work as [stack c]. cbn [fst] in Hempty. subst stack.
    cbn [SearchRun.apply_events fold_left].
    split; [split; assumption|].
    change (1 + state_credit p Phi w kv (([], c), s) <=
      state_credit p Phi w kv (([], c), s) + 1). lia.
Qed.

(** The real binary search loop telescopes graph credit and arbitrary visitor potential. *)
Theorem loop_cost {V E S} (p : Prepared.t V E) (vis : Visitor.t E S)
    Phi kv scope roots w fuel state :
  Prepared.ready p -> width_bound p roots w -> Visitor.amortised vis Phi kv ->
  state_invariant p scope roots state ->
    Cost.ticks (iterate (SearchRun.step_c p vis scope) fuel state) +
      state_credit p Phi w kv
        (SearchRun.unwrap (Cost.value (iterate (SearchRun.step_c p vis scope) fuel state))) <=
      state_credit p Phi w kv state + (1 + N.pos (Pos.size fuel)).
Proof.
  intros Hready Hwidth Hamortised HI.
  pose proof (iterate_credit (SearchRun.step_c p vis scope)
    (state_invariant p scope roots) (state_credit p Phi w kv) fuel state
    (fun st Hst => step_credit p vis Phi kv scope roots w st
      Hready Hwidth Hamortised Hst) HI) as Hcredit.
  destruct (Cost.value (iterate (SearchRun.step_c p vis scope) fuel state)) as [next|final];
    cbn [SearchRun.unwrap]; destruct Hcredit; nia.
Qed.

Definition core_credit {V E S} (p : Prepared.t V E) (Phi : S -> N) w kv
    (state : SearchRun.core E * S) :=
  step_k w kv *
    N.of_nat (SearchInvariant.white_work p (SearchInvariant.vertices p)
      (SearchRun.seen (fst state))) + Phi (snd state).

Definition root_k w kv := 4 + 8 * id_cost w + kv.

Local Lemma launch_invariant {V E S} (p : Prepared.t V E) scope roots c v name (s : S) :
  Prepared.ready p -> SearchInvariant.representation c ->
  SearchInvariant.sound_work p scope roots ([], c) ->
  In v roots -> Scope.admits scope v = true ->
  FinSet.mem positive_encoding v (SearchRun.seen c) = false ->
  Prepared.name_of p v = Some name ->
    state_invariant p scope roots
      (([(v, Prepared.succ_edges p v)], SearchRun.discover v None c), s).
Proof.
  intros Hready Hrep Hsound Hroot Hallowed Hfresh Hname.
  assert (Hvalid : Prepared.valid_id p v).
  { apply SearchInvariant.vertices_spec.
    exact (SearchInvariant.named_in_vertices p v name Hready Hname). }
  split; [now apply SearchInvariant.discover_representation|].
  apply SearchInvariant.sound_push; try assumption.
  exists v, []. split; [exact Hroot|now apply Search.scoped_nil].
Qed.

(** Launching a fresh root consumes its transferred graph credit and the actual visitor charge. *)
Theorem launch_cost {V E S} (p : Prepared.t V E) (vis : Visitor.t E S)
    Phi kv scope roots w c v name s :
  Prepared.ready p -> width_bound p roots w -> Visitor.amortised vis Phi kv ->
  SearchInvariant.representation c -> SearchInvariant.sound_work p scope roots ([], c) ->
  In v roots -> Scope.admits scope v = true ->
  FinSet.mem positive_encoding v (SearchRun.seen c) = false ->
  Prepared.name_of p v = Some name ->
  Cost.ticks (SearchRun.launch_c p vis scope c v s) +
    core_credit p Phi w kv (Cost.value (SearchRun.launch_c p vis scope c v s)) <=
    core_credit p Phi w kv (c, s) +
      (2 + 4 * id_cost w + kv + N.pos (Pos.size (Prepared.fuel p))).
Proof.
  intros Hready Hwidth Hamortised Hrep Hsound Hroot Hallowed Hfresh Hname.
  pose proof (loop_cost p vis Phi kv scope roots w (Prepared.fuel p)
    (([(v, Prepared.succ_edges p v)], SearchRun.discover v None c),
      Visitor.apply vis (Search.Enter v None) s) Hready Hwidth Hamortised
    (launch_invariant p scope roots c v name _ Hready Hrep Hsound Hroot
      Hallowed Hfresh Hname)) as Hloop.
  set (loop := iterate (SearchRun.step_c p vis scope) (Prepared.fuel p)
    (([(v, Prepared.succ_edges p v)], SearchRun.discover v None c),
      Visitor.apply vis (Search.Enter v None) s)) in *.
  pose proof (Hamortised (Search.Enter v None) s) as Hvisitor.
  pose proof (discover_cost w v None c (Hwidth v (or_intror Hroot))) as Hdiscover.
  pose proof (successors_cost p w v (Hwidth v (or_intror Hroot))) as Hsuccessors.
  unfold SearchRun.launch_c. autorewrite with galois_cost.
  fold (SearchRun.discover v None c).
  fold (Visitor.apply vis (Search.Enter v None) s).
  fold (Prepared.succ_edges p v). fold loop.
  destruct (SearchRun.unwrap (Cost.value loop)) as [[stack final] sv] eqn:Hanswer.
  cbn [fst snd]. autorewrite with galois_cost.
  unfold state_credit in Hloop. cbn [fst snd] in Hloop.
  rewrite (SearchInvariant.root_work p c v name Hready Hrep Hname Hfresh) in Hloop.
  unfold core_credit. cbn [fst snd].
  unfold SearchInvariant.work_measure in Hloop. cbn [fst snd] in Hloop.
  rewrite Nat2N.inj_add in Hloop. nia.
Qed.

(** Root checks and launch work telescope against the same global white credit. *)
Theorem root_cost {V E S} (p : Prepared.t V E) (vis : Visitor.t E S)
    Phi kv scope roots w c v s :
  Prepared.ready p -> width_bound p roots w -> Visitor.amortised vis Phi kv ->
  SearchInvariant.representation c -> SearchInvariant.sound_work p scope roots ([], c) ->
  In v roots ->
  Cost.ticks (SearchRun.root_c p vis scope (c, s) v) +
    core_credit p Phi w kv (Cost.value (SearchRun.root_c p vis scope (c, s) v)) <=
    core_credit p Phi w kv (c, s) +
      (root_k w kv + N.pos (Pos.size (Prepared.fuel p))).
Proof.
  intros Hready Hwidth Hamortised Hrep Hsound Hroot.
  pose proof (admits_cost w scope v (Hwidth v (or_intror Hroot))) as Hscope.
  pose proof (mem_cost_le w v (SearchRun.seen c) (Hwidth v (or_intror Hroot))) as Hmem.
  pose proof (name_cost p w v (Hwidth v (or_intror Hroot))) as Hname.
  unfold SearchRun.root_c. autorewrite with galois_cost.
  fold (Scope.admits scope v). destruct (Scope.admits scope v) eqn:Hallowed;
    autorewrite with galois_cost; [|unfold root_k; nia].
  fold (FinSet.mem positive_encoding v (SearchRun.seen c)).
  destruct (FinSet.mem positive_encoding v (SearchRun.seen c)) eqn:Hfresh;
    autorewrite with galois_cost; [unfold root_k; nia|].
  fold (Prepared.name_of p v).
  destruct (Prepared.name_of p v) as [name|] eqn:Hnamed;
    autorewrite with galois_cost; [|unfold root_k; nia].
  pose proof (launch_cost p vis Phi kv scope roots w c v name s
    Hready Hwidth Hamortised Hrep Hsound Hroot Hallowed Hfresh Hnamed).
  unfold root_k. nia.
Qed.

Definition core_invariant {V E S} (p : Prepared.t V E) scope roots
    (state : SearchRun.core E * S) :=
  SearchInvariant.representation (fst state) /\
    SearchInvariant.sound_work p scope roots ([], fst state).

Local Lemma root_invariant {V E S} (p : Prepared.t V E) (vis : Visitor.t E S)
    scope roots state v :
  Prepared.ready p -> core_invariant p scope roots state -> In v roots ->
    core_invariant p scope roots (Cost.value (SearchRun.root_c p vis scope state v)).
Proof.
  intros Hready. destruct state as [c s]. intros [Hrep Hsound] Hroot.
  pose proof (SearchInvariant.root_representation p scope c v Hrep) as Hrep'.
  pose proof (SearchInvariant.root_sound p scope roots c v Hready Hrep Hsound Hroot)
    as Hsound'.
  rewrite SearchRun.root_erases.
  destruct (SearchRun.reference_root p scope c v) as [final evs]. split; assumption.
Qed.

(** Root-list work and binary descent are linear in root occurrences, including repeated roots. *)
Theorem roots_cost {V E S} (p : Prepared.t V E) (vis : Visitor.t E S)
    Phi kv scope roots w c s :
  Prepared.ready p -> width_bound p roots w -> Visitor.amortised vis Phi kv ->
  core_invariant p scope roots (c, s) ->
  Cost.ticks (fold_left_c (SearchRun.root_c p vis scope) roots (c, s)) +
    core_credit p Phi w kv
      (Cost.value (fold_left_c (SearchRun.root_c p vis scope) roots (c, s))) <=
    N.of_nat (length roots) *
      (root_k w kv + N.pos (Pos.size (Prepared.fuel p)) + 1) +
      core_credit p Phi w kv (c, s).
Proof.
  intros Hready Hwidth Hamortised HI.
  apply (ticks_fold_left_c_potential (SearchRun.root_c p vis scope)
    (core_invariant p scope roots) (core_credit p Phi w kv)); [|exact HI].
  intros [c' s'] v [Hrep Hsound] Hroot. split.
  - apply root_invariant; [exact Hready|split; assumption|exact Hroot].
  - pose proof (root_cost p vis Phi kv scope roots w c' v s'
      Hready Hwidth Hamortised Hrep Hsound Hroot). nia.
Qed.

Local Lemma present_length {A B} (f : A -> option B) xs :
  (length (Prepared.present f xs) <= length xs)%nat.
Proof.
  induction xs as [|x rest IH]; [reflexivity|].
  cbn [Prepared.present]. destruct (f x); cbn [length]; lia.
Qed.

(** Search cannot discover more vertices than the prepared graph lists. *)
Theorem preorder_length {V E} (p : Prepared.t V E) scope roots :
  Prepared.ready p ->
    (length (Search.preorder (SearchRun.dfs p scope roots)) <=
      length (Graph.nodes (Prepared.graph p)))%nat.
Proof.
  intro Hready.
  destruct (SearchExact.run_representation p scope roots) as [_ [_ [_ [_ [Hnodup Hseen]]]]].
  assert (Hincl : incl (Search.preorder (SearchRun.dfs p scope roots))
    (SearchInvariant.vertices p)).
  { intros v Hv. apply SearchInvariant.vertices_spec.
    apply (proj1 (SearchExact.run_reachable p scope roots v Hready)) in Hv.
    destruct Hv as [root [es [_ Hpath]]].
    induction Hpath; assumption. }
  pose proof (NoDup_incl_length Hnodup Hincl) as Hlength.
  pose proof (present_length (Prepared.id_of p)
    (Graph.nodes (Prepared.graph p))) as Hvertices.
  unfold SearchInvariant.vertices in Hlength. lia.
Qed.

Local Lemma result_cost {E} (c : SearchRun.core E) :
  Cost.ticks (SearchRun.result_c c) =
    N.of_nat (length (Search.preorder (SearchRun.result c))) +
      N.of_nat (length (Search.postorder (SearchRun.result c))).
Proof.
  unfold SearchRun.result, SearchRun.result_c. autorewrite with galois_cost.
  cbn [Search.preorder Search.postorder]. rewrite !length_rev. lia.
Qed.

Local Lemma initial_core_invariant {V E S} (p : Prepared.t V E) scope roots (s : S) :
  core_invariant p scope roots (SearchRun.initial, s).
Proof.
  split; [apply SearchInvariant.initial_representation|]. constructor.
  - intros v Hv. change (FinSet.mem positive_encoding v FinSet.empty = true) in Hv.
    rewrite FinSet.mem_empty in Hv. discriminate.
  - intros u es Hin. contradiction.
Qed.

Local Lemma initial_credit {V E S} (p : Prepared.t V E) (Phi : S -> N) w kv s :
  Prepared.ready p ->
    core_credit p Phi w kv (SearchRun.initial, s) =
      step_k w kv *
        (N.of_nat (length (Graph.nodes (Prepared.graph p))) +
          N.of_nat (edge_count (Prepared.graph p))) + Phi s.
Proof.
  intro Hready. unfold core_credit. cbn [fst snd SearchRun.initial SearchRun.seen].
  assert (Hwhite : forall todo,
    SearchInvariant.white_work p todo FinSet.empty =
      fold_right (fun v n => SearchInvariant.vertex_work p v + n)%nat 0%nat todo).
  { induction todo as [|v rest IH]; [reflexivity|].
    cbn [SearchInvariant.white_work fold_right]. rewrite FinSet.mem_empty, IH. reflexivity. }
  rewrite Hwhite.
  fold (SearchInvariant.capacity p).
  rewrite (SearchInvariant.capacity_equation p Hready), Nat2N.inj_add. reflexivity.
Qed.

(** The explicit coefficient bound conserves global graph credit across all root occurrences. *)
Theorem search_credit_cost {V E S} (p : Prepared.t V E) (vis : Visitor.t E S)
    Phi kv scope roots w s :
  Prepared.ready p -> width_bound p roots w -> Visitor.amortised vis Phi kv ->
  Cost.ticks (SearchRun.run_c p vis scope roots s) <=
    step_k w kv *
      (N.of_nat (length (Graph.nodes (Prepared.graph p))) +
        N.of_nat (edge_count (Prepared.graph p))) +
    N.of_nat (length roots) *
      (root_k w kv + N.pos (Pos.size (Prepared.fuel p)) + 1) +
    2 * N.of_nat (length (Graph.nodes (Prepared.graph p))) + Phi s.
Proof.
  intros Hready Hwidth Hamortised.
  pose proof (roots_cost p vis Phi kv scope roots w SearchRun.initial s
    Hready Hwidth Hamortised (initial_core_invariant p scope roots s)) as Hroots.
  rewrite (initial_credit p Phi w kv s Hready) in Hroots.
  pose proof (SearchRun.run_result p vis scope roots s) as Hresult.
  pose proof (preorder_length p scope roots Hready) as Hlength.
  destruct (SearchExact.run_numbering p scope roots Hready) as [Hperm _].
  pose proof (Permutation_length Hperm) as Hpost.
  unfold SearchRun.run_c in Hresult |- *.
  set (fold_m := fold_left_c (SearchRun.root_c p vis scope) roots (SearchRun.initial, s)) in *.
  rewrite Cost.value_bind in Hresult. rewrite Cost.ticks_bind.
  fold fold_m.
  destruct (Cost.value fold_m) as [c final] eqn:Hfold.
  cbn [fst snd] in Hroots, Hresult |- *.
  autorewrite with galois_cost in Hresult |- *.
  change (SearchRun.result c = SearchRun.dfs p scope roots) in Hresult.
  rewrite result_cost, Hresult.
  unfold core_credit in Hroots. cbn [fst snd] in Hroots.
  nia.
Qed.

Definition search_k : N := 64.

(** The size term includes valid-ID/root width, all edge occurrences and binary root descent. *)
Definition search_size {V E} (p : Prepared.t V E) (roots : list positive) w kv :=
  (N.of_nat (length (Graph.nodes (Prepared.graph p))) +
    N.of_nat (edge_count (Prepared.graph p)) + N.of_nat (length roots)) *
    (1 + w + kv) + N.of_nat (length roots) * N.pos (Pos.size (Prepared.fuel p)).

(** Ready search has the linear graph/root/width bound with all visitor callee charges retained. *)
Theorem search_cost {V E S} (p : Prepared.t V E) (vis : Visitor.t E S)
    Phi kv scope roots w s :
  Prepared.ready p -> width_bound p roots w -> Visitor.amortised vis Phi kv ->
    Cost.ticks (SearchRun.run_c p vis scope roots s) <=
      search_k * search_size p roots w kv + Phi s.
Proof.
  intros Hready Hwidth Hamortised.
  pose proof (search_credit_cost p vis Phi kv scope roots w s Hready Hwidth Hamortised).
  unfold search_k, search_size, step_k, root_k, id_cost in *. nia.
Qed.

(** The explicit search bound lifts to every family satisfying the same input and visitor duties. *)
Theorem search_bigO {X V E S} (p : X -> Prepared.t V E) (vis : Visitor.t E S)
    Phi kv (scope : X -> Scope.t) roots w s :
  (forall x, Prepared.ready (p x)) -> Visitor.amortised vis Phi kv ->
  (forall x, width_bound (p x) (roots x) (w x)) ->
    bigO (fun x => search_size (p x) (roots x) (w x) kv + Phi (s x))
      (fun x => Cost.ticks (SearchRun.run_c (p x) vis (scope x) (roots x) (s x))).
Proof.
  intros Hready Hamortised Hwidth. exists search_k. intro x.
  pose proof (search_cost (p x) vis Phi kv (scope x) (roots x) (w x) (s x)
    (Hready x) (Hwidth x) Hamortised).
  unfold search_k in *. nia.
Qed.

End SearchCost.
