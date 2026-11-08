(** * Structural bounds for the reference frontier pipelines

    Explicit polynomial budgets expand all owned traversal work and retain external callbacks.
    For example, reference reachability pays the duplicate pass and every adjacency-credit query.
    Builds on: GraphWalk, the frontier consumers and public Base cost contracts. *)

From Stdlib Require Import List Bool PArith NArith Nnat Arith Lia.
From Galois.Cost Require Import CostMonad CostList CostBound.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseMapCost BaseTrieCost.
From Galois.Graph Require Import GraphModel GraphPrepared GraphPreparedCost GraphVisitor
  GraphReach GraphDomSpec GraphWalk GraphFrontierSweep GraphFrontierControl GraphFrontierEdge.
Import List.ListNotations Cost.Notations FrontierSweep.

Module FrontierCost.

Local Open Scope N_scope.

Local Lemma fuel_N n : N.pos (Pos.of_succ_nat n) = N.of_nat (S n).
Proof.
  rewrite <- (N2Nat.id (N.pos (Pos.of_succ_nat n))).
  cbn [N.to_nat]. now rewrite SuccNat2Pos.id_succ.
Qed.

Local Lemma comparisons {V E} (p : Prepared.t V E) t n m l b w a q h s
    (Hr : resources p t n m l b w a q h s) v :
  Prepared.valid_id p v ->
  forall x, Cost.ticks (Map.code_compare_c v x) <= w.
Proof.
  intros Hv x. eapply N.le_trans; [apply Map.code_compare_cost|].
  exact (width_bound Hr v Hv).
Qed.

Local Lemma set_cost_on {V E} (p : Prepared.t V E) t n m l b w a q h s
    (Hr : resources p t n m l b w a q h s) xs :
  Forall (Prepared.valid_id p) xs ->
  Cost.ticks (FinSet.of_list_c positive_encoding xs) <=
    N.of_nat (length xs) * (w + 4).
Proof.
  intro Hsupport.
  eapply N.le_trans.
  - apply (FinSet.of_list_numeric_cost Map.cost_laws_hold positive_encoding xs 1 w).
    intros i Hi. pose proof (proj1 (Forall_forall _ _) Hsupport i Hi) as Hvalid.
    split; [change (1 <= 1); reflexivity|].
    exact (width_bound Hr i Hvalid).
  - apply N.mul_le_mono; [apply N.le_refl|lia].
Qed.

(** Reference reachability has a complete polynomial structural bound. *)
Theorem reach_cost {V E} (p : Prepared.t V E) t n m l b w a q h s :
  Prepared.ready p -> resources p t n m l b w a q h s ->
  Cost.ticks (reach_c p Reach.unrestricted (Prepared.entry_ids p)) <=
    reach_work (N.of_nat n) (N.of_nat m) (N.of_nat l) w a q h.
Proof.
  intros Hready Hr.
  set (P := Prepared.valid_id p).
  set (all := Reach.universe p).
  set (next := successors_c p Reach.unrestricted all).
  set (initial := Cost.value (roots_c Reach.unrestricted all (Prepared.entry_ids p))).
  set (credit := Cost.value (credit_c next all)).
  set (fuel := Pos.of_succ_nat (credit + length initial)).
  set (kn := successor_work (N.of_nat n) (N.of_nat m) w q h).
  assert (Hcompare : forall v, P v ->
    forall x, Cost.ticks (Map.code_compare_c v x) <= w)
    by (intros v Hv x; exact (comparisons p t n m l b w a q h s Hr v Hv x)).
  assert (Hnext : forall v, P v -> Forall P (Cost.value (next v)) /\
    (length (Cost.value (next v)) <= m)%nat /\ Cost.ticks (next v) <= kn).
  { intros v Hv.
    destruct (successors_cost p t n m l b w a q h s v Hready Hr Hcompare Hv)
      as [Hcost [Hsupport Hlength]].
    exact (conj Hsupport (conj Hlength Hcost)). }
  pose proof (universe_cost p t n m l b w a q h s Hready Hr Hcompare) as Huniverse.
  destruct (roots_cost p t n m l b w a q h s Hr Hcompare)
    as [Hroots [Hinitial Hinitial_length]].
  change (Forall P initial) in Hinitial.
  change (length initial <= n)%nat in Hinitial_length.
  destruct (credit_cost next P all n m kn (universe_support p) (universe_bound Hr)
    ltac:(intros v Hv; exact (proj2 (Hnext v Hv)))) as [Hcredit Hcredit_length].
  fold credit in Hcredit_length.
  assert (Hfuel : N.pos fuel <= N.of_nat n * (N.of_nat m + 2) + 1).
  { unfold fuel. rewrite fuel_N, Nat2N.inj_succ, Nat2N.inj_add.
    assert (Hc : N.of_nat credit <= N.of_nat n * (N.of_nat m + 1)).
    { replace (N.of_nat n * (N.of_nat m + 1)) with (N.of_nat (n * (m + 1)%nat)) by
        (rewrite Nat2N.inj_mul, Nat2N.inj_add; reflexivity).
      lia. }
    nia. }
  assert (Hlists : forall v xs, P v -> (length xs <= n)%nat ->
    Cost.ticks (member_c v xs) <= N.of_nat n * (w + 1) /\
    Cost.ticks (remove_c v xs) <= N.of_nat n * (w + 1) /\
    (length (Cost.value (remove_c v xs)) <= length xs)%nat).
  { intros v xs Hv Hlength.
    pose proof (member_cost v xs w (Hcompare v Hv)) as Hmember.
    destruct (remove_cost v xs w (Hcompare v Hv)) as [Hremove Hshort].
    assert (Hscale : N.of_nat (length xs) * (w + 1) <= N.of_nat n * (w + 1)).
    { apply N.mul_le_mono; [lia|apply N.le_refl]. }
    split; [eapply N.le_trans; eassumption|].
    split; [eapply N.le_trans; eassumption|exact Hshort]. }
  pose proof (Walk.closure_cost next member_c remove_c P n m kn
    (N.of_nat n * (w + 1)) (N.of_nat n * (w + 1))
    fuel initial all Hinitial (universe_bound Hr) Hnext Hlists) as Hloop.
  destruct (Walk.closure_seen next member_c remove_c P fuel initial all Hinitial
    ltac:(intros v Hv; exact (proj1 (Hnext v Hv)))) as [Hseen Hseen_length].
  pose proof (set_cost_on p t n m l b w a q h s Hr _
    Hseen) as Hset.
  assert (HseenN : N.of_nat (length (snd
    (Cost.value (Walk.closure_c next member_c remove_c fuel initial all [])))) <=
    N.pos fuel).
  { rewrite <- (N2Nat.id (N.pos fuel)). cbn [N.to_nat]. lia. }
  assert (Hset' : Cost.ticks (FinSet.of_list_c positive_encoding
    (snd (Cost.value (Walk.closure_c next member_c remove_c fuel initial all [])))) <=
    N.pos fuel * (w + 4)).
  { eapply N.le_trans; [exact Hset|]. apply N.mul_le_mono; [exact HseenN|reflexivity]. }
  unfold reach_c. rewrite Cost.ticks_bind, universe_value.
  fold all next.
  rewrite !Cost.ticks_bind, value_length_c, Prepared.budget_cost, Prepared.budget_value.
  fold initial credit fuel.
  rewrite ticks_length_c.
  unfold reach_work. fold kn.
  assert (Hconversion : N.of_nat (credit + length initial) <= N.pos fuel).
  { unfold fuel. rewrite fuel_N. lia. }
  assert (Hloop' : Cost.ticks (Walk.closure_c next member_c remove_c fuel initial all []) <=
    (6 + kn + 2 * N.of_nat n * (w + 1) + N.of_nat m) *
      (N.of_nat n * (N.of_nat m + 2) + 1)).
  { eapply N.le_trans; [exact Hloop|]. apply N.mul_le_mono; [nia|exact Hfuel]. }
  assert (Hset'' : Cost.ticks (FinSet.of_list_c positive_encoding
    (snd (Cost.value (Walk.closure_c next member_c remove_c fuel initial all [])))) <=
    (N.of_nat n * (N.of_nat m + 2) + 1) * (w + 4)).
  { eapply N.le_trans; [exact Hset'|]. apply N.mul_le_mono; [exact Hfuel|reflexivity]. }
  assert (HinitialN : N.of_nat (length initial) <= N.of_nat n) by lia.
  assert (Hconversion' : N.of_nat (credit + length initial) <=
    N.of_nat n * (N.of_nat m + 2) + 1).
  { eapply N.le_trans; [exact Hconversion|exact Hfuel]. }
  eapply N.le_trans.
  - apply N.add_le_mono; [exact Huniverse|].
    apply N.add_le_mono; [exact Hroots|].
    apply N.add_le_mono; [exact Hcredit|].
    apply N.add_le_mono; [exact HinitialN|].
    apply N.add_le_mono; [exact Hconversion'|].
    apply N.add_le_mono; [exact Hloop'|exact Hset''].
  - clear -n m l w a q h kn. nia.
Qed.

Local Lemma budget_value t :
  Cost.value (FrontierSweep.budget_c t) = Pos.of_succ_nat (Map.size (Dom.idom t)).
Proof.
  unfold FrontierSweep.budget_c. rewrite Cost.value_bind, Prepared.budget_value.
  reflexivity.
Qed.

Local Lemma budget_cost {V E} (p : Prepared.t V E) t n m l b w a q h s
    (Hr : resources p t n m l b w a q h s) :
  Cost.ticks (FrontierSweep.budget_c t) <= scan_work s + N.of_nat b.
Proof.
  unfold FrontierSweep.budget_c. rewrite Cost.ticks_bind, Prepared.budget_cost.
  fold (Map.size (Dom.idom t)).
  pose proof (MapCost.size_cost (Dom.idom t)) as Hscan.
  pose proof (skeleton_bound Hr). pose proof (bindings_bound Hr).
  unfold scan_work.
  assert (Hscan' : Cost.ticks (Map.size_c (Dom.idom t)) <=
    TrieCost.trie_k * (1 + s)).
  { eapply N.le_trans; [exact Hscan|].
    apply N.mul_le_mono; [reflexivity|lia]. }
  lia.
Qed.

Local Lemma parent_closed {V E} (p : Prepared.t V E) t :
  Prepared.ready p -> Dom.exact p t ->
  forall i j, Prepared.valid_id p i -> Cost.value (Walk.up_c t i) = Some j ->
    Prepared.valid_id p j.
Proof.
  intros Hready Htree i j Hi Hparent.
  eapply parent_support; eassumption.
Qed.

(** A boundary cache includes its repeated map scan,
    unary fuel conversion and every set insertion. *)
Theorem ancestors_cost {V E} (p : Prepared.t V E) t n m l b w a q h s i :
  Prepared.ready p -> Dom.exact p t -> resources p t n m l b w a q h s ->
  Prepared.valid_id p i ->
  Cost.ticks (ancestors_c t i) <= ancestor_work (N.of_nat b) w s.
Proof.
  intros Hready Htree Hr Hi.
  set (fuel := Pos.of_succ_nat (Map.size (Dom.idom t))).
  assert (Hparent := parent_closed p t Hready Htree).
  assert (Hcallbacks : forall v, Prepared.valid_id p v ->
    Cost.ticks (Cost.ret false) + Cost.ticks (Walk.up_c t v) <= 2 + w).
  { intros v Hv. change (Cost.ticks (Walk.up_c t v) <= 2 + w).
    unfold Walk.up_c. now apply positive_get_cost, (width_bound Hr). }
  pose proof (Walk.until_cost_on (Walk.up_c t) (fun _ => Cost.ret false)
    (Prepared.valid_id p) (2 + w) fuel i Hi Hparent Hcallbacks) as Hwalk.
  pose proof (Walk.until_closed (Walk.up_c t) (fun _ => Cost.ret false)
    (Prepared.valid_id p) fuel i Hi Hparent) as Hsupport.
  pose proof (Walk.until_length (Walk.up_c t) (fun _ => Cost.ret false) fuel i) as Hlength.
  pose proof (set_cost_on p t n m l b w a q h s Hr _ Hsupport) as Hset.
  assert (Hfuel : N.pos fuel <= N.of_nat b + 1).
  { unfold fuel. rewrite fuel_N, Nat2N.inj_succ. pose proof (bindings_bound Hr). lia. }
  assert (HlengthN : N.of_nat (length
    (Walk.until (Walk.up_c t) (fun _ => Cost.ret false) fuel i)) <= N.pos fuel).
  { rewrite <- (N2Nat.id (N.pos fuel)). cbn [N.to_nat]. lia. }
  assert (Hset' : Cost.ticks (FinSet.of_list_c positive_encoding
    (Walk.until (Walk.up_c t) (fun _ => Cost.ret false) fuel i)) <=
      (N.of_nat b + 1) * (w + 4)).
  { eapply N.le_trans; [exact Hset|].
    apply N.mul_le_mono; [lia|reflexivity]. }
  pose proof (budget_cost p t n m l b w a q h s Hr) as Hbudget.
  unfold ancestors_c. rewrite !Cost.ticks_bind, budget_value.
  fold fuel.
  change ((Cost.ticks (FrontierSweep.budget_c t) +
    (Cost.ticks (Walk.until_c (Walk.up_c t) (fun _ => Cost.ret false) fuel i) +
      Cost.ticks (FinSet.of_list_c positive_encoding
        (Walk.until (Walk.up_c t) (fun _ => Cost.ret false) fuel i)))) <=
    ancestor_work (N.of_nat b) w s).
  unfold ancestor_work.
  assert (Hwalk' : Cost.ticks
    (Walk.until_c (Walk.up_c t) (fun _ => Cost.ret false) fuel i) <=
      (8 + w) * (N.of_nat b + 1)).
  { eapply N.le_trans; [exact Hwalk|]. apply N.mul_le_mono; [nia|exact Hfuel]. }
  nia.
Qed.

(** Source-walk cost includes the complete boundary cache and both budget conversions. *)
Theorem runner_cost {V E} (p : Prepared.t V E) t n m l b w a q h s i boundary :
  Prepared.ready p -> Dom.exact p t -> resources p t n m l b w a q h s ->
  Prepared.valid_id p i ->
  (forall j, boundary = Some j -> Prepared.valid_id p j) ->
  Cost.ticks (runner_c t i boundary) <= runner_work (N.of_nat b) w s /\
  Forall (Prepared.valid_id p) (runner t i boundary) /\
    (length (runner t i boundary) <= S b)%nat.
Proof.
  intros Hready Htree Hr Hi Hboundary.
  set (fuel := Pos.of_succ_nat (Map.size (Dom.idom t))).
  set (blocked := Cost.value (blocked_set_c t boundary)).
  set (stop := fun v => FinSet.mem_c positive_encoding v blocked).
  assert (Hparent := parent_closed p t Hready Htree).
  assert (Hcallbacks : forall v, Prepared.valid_id p v ->
    Cost.ticks (stop v) + Cost.ticks (Walk.up_c t v) <= 4 + 2 * w).
  { intros v Hv.
    pose proof (positive_mem_cost blocked v w (width_bound Hr v Hv)) as Hstop.
    pose proof (positive_get_cost (Dom.idom t) v w (width_bound Hr v Hv)) as Hup.
    unfold stop, Walk.up_c. lia. }
  pose proof (Walk.until_cost_on (Walk.up_c t) stop (Prepared.valid_id p)
    (4 + 2 * w) fuel i Hi Hparent Hcallbacks) as Hwalk.
  pose proof (Walk.until_closed (Walk.up_c t) stop (Prepared.valid_id p)
    fuel i Hi Hparent) as Hsupport.
  pose proof (Walk.until_length (Walk.up_c t) stop fuel i) as Hlength.
  assert (Hfuel : N.pos fuel <= N.of_nat b + 1).
  { unfold fuel. rewrite fuel_N, Nat2N.inj_succ. pose proof (bindings_bound Hr). lia. }
  assert (Hblocked : Cost.ticks (blocked_set_c t boundary) <= ancestor_work (N.of_nat b) w s).
  { destruct boundary as [j|]; cbn [blocked_set_c].
    - exact (ancestors_cost p t n m l b w a q h s j Hready Htree Hr
        (Hboundary j eq_refl)).
    - change (0 <= ancestor_work (N.of_nat b) w s). lia. }
  assert (Hequation : runner t i boundary = Walk.until (Walk.up_c t) stop fuel i).
  { unfold runner, runner_c. rewrite Cost.value_bind, budget_value, Cost.value_bind.
    reflexivity. }
  split.
  - unfold runner_c. rewrite !Cost.ticks_bind, budget_value. fold fuel blocked stop.
    pose proof (budget_cost p t n m l b w a q h s Hr) as Hbudget.
    assert (Hwalk' : Cost.ticks (Walk.until_c (Walk.up_c t) stop fuel i) <=
      (10 + 2 * w) * (N.of_nat b + 1)).
    { eapply N.le_trans; [exact Hwalk|]. apply N.mul_le_mono; [lia|exact Hfuel]. }
    eapply N.le_trans.
    + apply N.add_le_mono; [exact Hbudget|].
      apply N.add_le_mono; [exact Hblocked|exact Hwalk'].
    + clear -b w s. unfold runner_work, ancestor_work. nia.
  - rewrite Hequation. split; [exact Hsupport|].
    unfold fuel.
    eapply Nat.le_trans; [exact Hlength|].
    unfold fuel. rewrite SuccNat2Pos.id_succ.
    pose proof (bindings_bound Hr). lia.
Qed.

Local Lemma flat_cost {A B} (f : A -> Cost.t (list B)) (P : B -> Prop) xs k d :
  (forall x, In x xs -> Cost.ticks (f x) <= k /\
    Forall P (Cost.value (f x)) /\ (length (Cost.value (f x)) <= d)%nat) ->
  let computation := fold_right_c (fun x rest =>
    let* fresh := f x in app_c fresh rest) [] xs in
  Cost.ticks computation <= N.of_nat (length xs) * (k + N.of_nat d + 1) /\
  Forall P (Cost.value computation) /\
    (length (Cost.value computation) <= length xs * d)%nat.
Proof.
  intro Hf. cbn beta iota zeta. split.
  - eapply N.le_trans.
    + apply (fold_right_bound_on _ (k + N.of_nat d)).
      intros x rest Hx. destruct (Hf x Hx) as [Hcost [_ Hlength]].
      rewrite Cost.ticks_bind, ticks_app_c. nia.
    + apply N.mul_le_mono; [reflexivity|lia].
  - rewrite value_fold_right_c.
    induction xs as [|x rest IH]; [split; [constructor|cbn; lia]|].
    destruct (Hf x (or_introl eq_refl)) as [Hcost [Hsupport Hlength]].
    specialize (IH ltac:(intros y Hy; apply Hf; now right)).
    cbn [fold_right]. rewrite Cost.value_bind, value_app_c.
    destruct IH as [IHsupport IHlength]. split.
    + apply Forall_app. auto.
    + rewrite length_app. cbn [length]. nia.
Qed.

Local Lemma edge_cost {V E} (p : Prepared.t V E) t n m l b w a q h s seen i (e : E) j :
  Prepared.ready p -> Dom.exact p t -> resources p t n m l b w a q h s ->
  Prepared.valid_id p i -> Prepared.valid_id p j ->
  Cost.ticks (edge_events_c t seen i (e, j)) <=
    4 + 2 * w + runner_work (N.of_nat b) w s + N.of_nat (S b) /\
  Forall (fun event => Prepared.valid_id p (fst event) /\
    Prepared.valid_id p (snd (snd event)))
    (Cost.value (edge_events_c t seen i (e, j))) /\
  (length (Cost.value (edge_events_c t seen i (e, j))) <= S b)%nat.
Proof.
  intros Hready Htree Hr Hi Hj.
  pose proof (positive_mem_cost seen i w (width_bound Hr i Hi)) as Hlive.
  pose proof (positive_get_cost (Dom.idom t) j w (width_bound Hr j Hj)) as Hget.
  set (boundary := Map.get positive_encoding j (Dom.idom t)).
  destruct (runner_cost p t n m l b w a q h s i boundary Hready Htree Hr Hi
    ltac:(intros v Hv; eapply parent_support; eassumption))
    as [Hrunner [Hsupport Hlength]].
  assert (Hmap : Cost.ticks (map_c (fun d => Cost.ret (d, (e, j)))
    (runner t i boundary)) <= N.of_nat (S b)).
  { pose proof (ticks_map_c_le (fun d : positive => Cost.ret (d, (e, j)))
      0 (runner t i boundary) ltac:(intros; reflexivity)) as Hmap. nia. }
  unfold edge_events_c. rewrite Cost.ticks_bind, Cost.value_bind.
  fold (FinSet.mem positive_encoding i seen).
  destruct (FinSet.mem positive_encoding i seen).
  - rewrite !Cost.ticks_bind, !Cost.value_bind, value_map_c.
    fold boundary. fold (runner t i boundary).
    split.
    + eapply N.le_trans.
      * apply N.add_le_mono; [exact Hlive|].
        apply N.add_le_mono; [exact Hget|].
        apply N.add_le_mono; [exact Hrunner|exact Hmap].
      * clear -b w s. nia.
    + split.
      * apply Forall_forall. intros [d [label target]] Hin.
        apply in_map_iff in Hin. destruct Hin as [v [Heq Hv]].
        inversion Heq; subst d label target. cbn [fst snd].
        split; [exact (proj1 (Forall_forall _ _) Hsupport v Hv)|exact Hj].
      * rewrite length_map. exact Hlength.
  - autorewrite with galois_cost. split; [nia|].
    split; [constructor|cbn; lia].
Qed.

Local Lemma node_cost {V E} (p : Prepared.t V E) t n m l b w a q h s seen i :
  Prepared.ready p -> Dom.exact p t -> resources p t n m l b w a q h s ->
  Prepared.valid_id p i ->
  Cost.ticks (node_events_c p t seen i) <=
    q + N.of_nat m * (5 + 2 * w + runner_work (N.of_nat b) w s + 2 * N.of_nat (S b)) /\
  Forall (fun event => Prepared.valid_id p (fst event) /\
    Prepared.valid_id p (snd (snd event))) (Cost.value (node_events_c p t seen i)) /\
  (length (Cost.value (node_events_c p t seen i)) <= m * S b)%nat.
Proof.
  intros Hready Htree Hr Hi.
  pose proof (successor_support p i Hready) as Htargets.
  pose proof (flat_cost (edge_events_c t seen i)
    (fun event => Prepared.valid_id p (fst event) /\
      Prepared.valid_id p (snd (snd event))) (Prepared.succ_edges p i)
    (4 + 2 * w + runner_work (N.of_nat b) w s + N.of_nat (S b)) (S b)
    ltac:(intros [e j] Hedge; eapply edge_cost; try eassumption;
      exact (proj1 (Forall_forall _ _) Htargets (e, j) Hedge))) as Hflat.
  destruct Hflat as [Hcost [Hsupport Hlength]].
  pose proof (successor_length_bound Hr i Hi) as Hsize.
  pose proof (successor_lookup_bound Hr i Hi) as Hlookup.
  unfold node_events_c. rewrite Cost.ticks_bind, Cost.value_bind.
  fold (Prepared.succ_edges p i). split.
  - assert (Hscaled : N.of_nat (length (Prepared.succ_edges p i)) *
      (4 + 2 * w + runner_work (N.of_nat b) w s + N.of_nat (S b) + N.of_nat (S b) + 1) <=
      N.of_nat m *
      (5 + 2 * w + runner_work (N.of_nat b) w s + 2 * N.of_nat (S b))).
    { apply N.mul_le_mono; [lia|nia]. }
    lia.
  - split; [exact Hsupport|nia].
Qed.

(** Event production has a closed polynomial bound and bounded valid-ID output. *)
Theorem events_cost {V E} (p : Prepared.t V E) t n m l b w a q h s :
  Prepared.ready p -> Dom.exact p t -> resources p t n m l b w a q h s ->
  Cost.ticks (events_c p t) <=
    events_work (N.of_nat n) (N.of_nat m) (N.of_nat l) (N.of_nat b) w a q h s /\
  Forall (fun event => Prepared.valid_id p (fst event) /\
    Prepared.valid_id p (snd (snd event))) (events p t) /\
  (length (events p t) <= n * m * S b)%nat.
Proof.
  intros Hready Htree Hr.
  set (seen := Reach.set p Reach.unrestricted (Prepared.entry_ids p)).
  set (k := q + N.of_nat m *
    (5 + 2 * w + runner_work (N.of_nat b) w s + 2 * N.of_nat (S b))).
  pose proof (flat_cost (node_events_c p t seen)
    (fun event => Prepared.valid_id p (fst event) /\
      Prepared.valid_id p (snd (snd event))) (Reach.universe p) k (m * S b)%nat
    ltac:(intros i Hi; exact (node_cost p t n m l b w a q h s seen i
      Hready Htree Hr (proj1 (Reach.universe_spec p i) Hi)))) as Hflat.
  destruct Hflat as [Hflatcost [Hsupport Hlength]].
  pose proof (reach_cost p t n m l b w a q h s Hready Hr) as Hreach.
  pose proof (universe_cost p t n m l b w a q h s Hready Hr
    (comparisons p t n m l b w a q h s Hr)) as Huniverse.
  assert (Hvalue : events p t =
    Cost.value (fold_right_c (fun i rest =>
      let* fresh := node_events_c p t seen i in app_c fresh rest) [] (Reach.universe p))).
  { unfold events, events_c. rewrite Cost.value_bind, reach_value,
      Cost.value_bind, universe_value. reflexivity. }
  split.
  - unfold events_c. rewrite Cost.ticks_bind, reach_value, Cost.ticks_bind, universe_value.
    fold seen.
    assert (Hscaled : N.of_nat (length (Reach.universe p)) *
      (k + N.of_nat (m * S b) + 1) <=
      N.of_nat n * (k + N.of_nat (m * S b) + 1)).
    { apply N.mul_le_mono; [pose proof (universe_bound Hr); lia|reflexivity]. }
    eapply N.le_trans.
    + apply N.add_le_mono; [exact Hreach|].
      apply N.add_le_mono; [exact Huniverse|].
      eapply N.le_trans; [exact Hflatcost|exact Hscaled].
    + clear -n m l b w a q h s k.
      unfold events_work, k. rewrite Nat2N.inj_mul, Nat2N.inj_succ. nia.
  - rewrite Hvalue. split; [exact Hsupport|].
    pose proof (universe_bound Hr). nia.
Qed.

Local Lemma sum_work_bound {A} (f : A -> N -> N) xs k :
  (forall x acc, In x xs -> f x acc <= k + acc) ->
  fold_right f 0 xs <= N.of_nat (length xs) * k.
Proof.
  induction xs as [|x rest IH]; intro Hf; [cbn; lia|].
  cbn [fold_right length]. rewrite Nat2N.inj_succ.
  pose proof (Hf x (fold_right f 0 rest) (or_introl eq_refl)) as Hhead.
  specialize (IH ltac:(intros y acc Hy; apply Hf; now right)). nia.
Qed.

(** The actual delivered sweep has a whole-operation polynomial upper bound. *)
Theorem sweep_structural_cost {V E} (p : Prepared.t V E) t n m l b w a q h s :
  Prepared.ready p -> Dom.exact p t -> resources p t n m l b w a q h s ->
  Cost.ticks (dominance_frontier_c p t) <=
    sweep_work (N.of_nat n) (N.of_nat m) (N.of_nat l) (N.of_nat b) w a q h s.
Proof.
  intros Hready Htree Hr.
  destruct (events_cost p t n m l b w a q h s Hready Htree Hr)
    as [Hcost [Hsupport Hlength]].
  assert (Hsum : fold_right (fun event acc =>
    1 + 2 * key_charge (fst event) + key_charge (snd (snd event)) + acc)%N 0%N
      (events p t) <=
    N.of_nat (length (events p t)) * (7 + 3 * w)).
  { apply sum_work_bound. intros event acc He.
    destruct (proj1 (Forall_forall _ _) Hsupport event He) as [Hd Hx].
    pose proof (width_bound Hr _ Hd) as Hdw.
    pose proof (width_bound Hr _ Hx) as Hxw.
    clear -Hdw Hxw. unfold key_charge. nia. }
  assert (Hcount : N.of_nat (length (events p t)) <=
    N.of_nat n * N.of_nat m * (N.of_nat b + 1)).
  { clear -Hlength.
    replace (N.of_nat n * N.of_nat m * (N.of_nat b + 1)) with
      (N.of_nat (n * m * S b)%nat) by
      (rewrite !Nat2N.inj_mul, Nat2N.inj_succ; nia).
    lia. }
  rewrite frontier_cost. unfold sweep_work.
  apply N.add_le_mono; [exact Hcost|].
  eapply N.le_trans; [exact Hsum|]. apply N.mul_le_mono; [exact Hcount|reflexivity].
Qed.

(** The polynomial sweep size bounds every resource-certified family with one global constant. *)
Theorem sweep_bigO {V E X} (p : X -> Prepared.t V E) (t : X -> Dom.tree)
    (n m l b : X -> nat) (w a q h s : X -> N) :
  (forall x, Prepared.ready (p x)) ->
  (forall x, Dom.exact (p x) (t x)) ->
  (forall x, resources (p x) (t x) (n x) (m x) (l x) (b x)
    (w x) (a x) (q x) (h x) (s x)) ->
  bigO (fun x => sweep_work (N.of_nat (n x)) (N.of_nat (m x))
    (N.of_nat (l x)) (N.of_nat (b x)) (w x) (a x) (q x) (h x) (s x))
    (fun x => Cost.ticks (dominance_frontier_c (p x) (t x))).
Proof.
  intros Hready Htree Hr. exists 1. intro x.
  pose proof (sweep_structural_cost (p x) (t x) (n x) (m x) (l x) (b x)
    (w x) (a x) (q x) (h x) (s x) (Hready x) (Htree x) (Hr x)) as Hcost.
  eapply N.le_trans; [exact Hcost|].
  rewrite N.mul_1_l. apply N.le_add_l.
Qed.

Local Lemma candidate_cost {V E} (p : Prepared.t V E) t n m l b w a q h s
    seen i (e : E) j :
  Prepared.ready p -> Dom.exact p t -> resources p t n m l b w a q h s ->
  Prepared.valid_id p i -> Prepared.valid_id p j ->
  Cost.ticks (FrontierEdge.candidate_c t seen i (e, j)) <=
    ancestor_work (N.of_nat b) w s + 4 + 2 * w.
Proof.
  intros Hready Htree Hr Hi Hj.
  pose proof (positive_mem_cost seen j w (width_bound Hr j Hj)) as Hlive.
  pose proof (ancestors_cost p t n m l b w a q h s j Hready Htree Hr Hj) as Hcache.
  pose proof (positive_mem_cost (ancestors t j) i w (width_bound Hr i Hi)) as Hback.
  unfold FrontierEdge.candidate_c. cbn [snd]. rewrite Cost.ticks_bind.
  fold (FinSet.mem positive_encoding j seen).
  destruct (FinSet.mem positive_encoding j seen).
  - rewrite !Cost.ticks_bind. autorewrite with galois_cost.
    fold (ancestors t j).
    eapply N.le_trans.
    + apply N.add_le_mono; [exact Hlive|].
      apply N.add_le_mono; [exact Hcache|].
      rewrite N.add_0_r. exact Hback.
    + clear -b w s. lia.
  - autorewrite with galois_cost. clear -Hlive. lia.
Qed.

Local Lemma candidates_cost {V E} (p : Prepared.t V E) t n m l b w a q h s seen i :
  Prepared.ready p -> Dom.exact p t -> resources p t n m l b w a q h s ->
  Prepared.valid_id p i ->
  Cost.ticks (FrontierEdge.candidates_c p t seen i) <=
    q + N.of_nat m * (ancestor_work (N.of_nat b) w s + 6 + 2 * w).
Proof.
  intros Hready Htree Hr Hi.
  set (incoming := Prepared.pred_edges p i).
  set (selected := Cost.value (filter_c (FrontierEdge.candidate_c t seen i) incoming)).
  assert (Hlength : (length selected <= m)%nat).
  { unfold selected. rewrite value_filter_c.
    eapply Nat.le_trans; [apply List.filter_length_le|exact (predecessor_length_bound Hr i Hi)]. }
  assert (Hfilter : Cost.ticks (filter_c (FrontierEdge.candidate_c t seen i) incoming) <=
    N.of_nat m * (ancestor_work (N.of_nat b) w s + 5 + 2 * w)).
  { rewrite ticks_filter_c. eapply N.le_trans.
    - apply (sum_bound_on _ (ancestor_work (N.of_nat b) w s + 4 + 2 * w)).
      intros [e j] Hin.
      exact (candidate_cost p t n m l b w a q h s seen i e j Hready Htree Hr Hi
        (proj1 (Forall_forall _ _) (predecessor_support p i Hready Hi) (e, j) Hin)).
    - apply N.mul_le_mono;
        [unfold incoming; pose proof (predecessor_length_bound Hr i Hi); lia|lia]. }
  assert (Hmap : Cost.ticks (map_c (fun edge : E * positive => Cost.ret (fst edge))
    selected) <= N.of_nat m).
  { pose proof (ticks_map_c_le (fun edge : E * positive => Cost.ret (fst edge))
      0 selected ltac:(intros; reflexivity)) as Hmap. nia. }
  pose proof (predecessor_lookup_bound Hr i Hi) as Hlookup.
  unfold FrontierEdge.candidates_c. rewrite !Cost.ticks_bind. fold incoming selected.
  eapply N.le_trans.
  - apply N.add_le_mono; [exact Hlookup|].
    apply N.add_le_mono; [exact Hfilter|exact Hmap].
  - clear -m b w q s. nia.
Qed.

Local Lemma choice_cost {V E} (p : Prepared.t V E) t n m l b w a q h s entries seen i :
  Prepared.ready p -> Dom.exact p t -> resources p t n m l b w a q h s ->
  Prepared.valid_id p i ->
  Cost.ticks (FrontierEdge.choice_c p t entries seen i) <=
    2 + w + q + N.of_nat m * (ancestor_work (N.of_nat b) w s + 6 + 2 * w).
Proof.
  intros Hready Htree Hr Hi.
  pose proof (positive_mem_cost entries i w (width_bound Hr i Hi)) as Hentry.
  pose proof (candidates_cost p t n m l b w a q h s seen i Hready Htree Hr Hi) as Hcandidates.
  unfold FrontierEdge.choice_c. rewrite Cost.ticks_bind.
  fold (FinSet.mem positive_encoding i entries).
  destruct (FinSet.mem positive_encoding i entries); autorewrite with galois_cost.
  - clear -Hentry. lia.
  - destruct (Cost.value (FrontierEdge.candidates_c p t seen i)) as [|e [|f rest]];
      autorewrite with galois_cost; lia.
Qed.

(** The edge-index polynomial includes reference reachability and every incoming candidate scan. *)
Definition edge_work n m l b w a q h s :=
  (reach_work n m l w a q h + l * (w + 4) + universe_work n w a +
    n * (6 + 2 * w + q + m * (ancestor_work b w s + 6 + 2 * w)))%N.

(** The actual incoming-edge index has a whole-operation structural upper bound. *)
Theorem edge_structural_cost {V E} (p : Prepared.t V E) t n m l b w a q h s :
  Prepared.ready p -> Dom.exact p t -> resources p t n m l b w a q h s ->
  Cost.ticks (FrontierEdge.edge_dominators_c p t) <=
    edge_work (N.of_nat n) (N.of_nat m) (N.of_nat l) (N.of_nat b) w a q h s.
Proof.
  intros Hready Htree Hr.
  pose proof (reach_cost p t n m l b w a q h s Hready Hr) as Hreach.
  pose proof (universe_cost p t n m l b w a q h s Hready Hr
    (comparisons p t n m l b w a q h s Hr)) as Huniverse.
  assert (Hentries : Forall (Prepared.valid_id p) (Prepared.entry_ids p)).
  { apply Forall_forall. intros i Hi.
    apply (Prepared.entry_ids_spec p i (proj2 (proj2 Hready))) in Hi.
    destruct Hi as [v [Hv Hvi]]. exists v. split; [|exact Hvi].
    exact (entries_in (proj1 Hready) v Hv). }
  pose proof (set_cost_on p t n m l b w a q h s Hr _ Hentries) as Hset.
  assert (Hset' : Cost.ticks (FinSet.of_list_c positive_encoding (Prepared.entry_ids p)) <=
    N.of_nat l * (w + 4)).
  { eapply N.le_trans; [exact Hset|].
    apply N.mul_le_mono; [pose proof (entries_bound Hr); lia|reflexivity]. }
  assert (Hsum : fold_right (fun v acc => 2 +
      Cost.ticks (FrontierEdge.choice_c p t
        (FinSet.of_list positive_encoding (Prepared.entry_ids p))
        (Reach.set p Reach.unrestricted (Prepared.entry_ids p)) v) +
      match FrontierEdge.choice p t v with
      | None => acc
      | Some _ => key_charge v + acc
      end)%N 0 (Reach.universe p) <=
    N.of_nat n * (6 + 2 * w + q +
      N.of_nat m * (ancestor_work (N.of_nat b) w s + 6 + 2 * w))).
  { eapply N.le_trans.
    - apply (sum_work_bound _ _ (6 + 2 * w + q +
        N.of_nat m * (ancestor_work (N.of_nat b) w s + 6 + 2 * w))).
      intros v acc Hv. pose proof (proj1 (Reach.universe_spec p v) Hv) as Hvalid.
      pose proof (choice_cost p t n m l b w a q h s
        (FinSet.of_list positive_encoding (Prepared.entry_ids p))
        (Reach.set p Reach.unrestricted (Prepared.entry_ids p)) v Hready Htree Hr Hvalid)
        as Hchoice.
      pose proof (width_bound Hr v Hvalid) as Hwidth.
      clear -Hchoice Hwidth. unfold key_charge.
      destruct (FrontierEdge.choice p t v); lia.
    - apply N.mul_le_mono; [pose proof (universe_bound Hr); lia|reflexivity]. }
  rewrite FrontierEdge.edge_dominators_cost. unfold edge_work.
  apply N.add_le_mono; [|exact Hsum].
  apply N.add_le_mono; [|exact Huniverse].
  apply N.add_le_mono; [exact Hreach|exact Hset'].
Qed.

(** The edge polynomial uniformly bounds every resource-certified graph family. *)
Theorem edge_bigO {V E X} (p : X -> Prepared.t V E) (t : X -> Dom.tree)
    (n m l b : X -> nat) (w a q h s : X -> N) :
  (forall x, Prepared.ready (p x)) ->
  (forall x, Dom.exact (p x) (t x)) ->
  (forall x, resources (p x) (t x) (n x) (m x) (l x) (b x)
    (w x) (a x) (q x) (h x) (s x)) ->
  bigO (fun x => edge_work (N.of_nat (n x)) (N.of_nat (m x))
    (N.of_nat (l x)) (N.of_nat (b x)) (w x) (a x) (q x) (h x) (s x))
    (fun x => Cost.ticks (FrontierEdge.edge_dominators_c (p x) (t x))).
Proof.
  intros Hready Htree Hr. exists 1. intro x.
  eapply N.le_trans.
  - exact (edge_structural_cost (p x) (t x) (n x) (m x) (l x) (b x)
      (w x) (a x) (q x) (h x) (s x) (Hready x) (Htree x) (Hr x)).
  - rewrite N.mul_1_l. apply N.le_add_l.
Qed.

(** Control size includes every exit occurrence and the actual reversed event pipeline. *)
Definition control_work n m l b w a q h s e we :=
  (e * (3 + 2 * we) +
    (events_work n m l b w a q h s + n * m * (b + 1) * (6 + 2 * w)))%N.

(** Control dependence has a whole-operation bound including costed prepared reversal. *)
Theorem control_structural_cost {V E} (p : Prepared.t V E) exits t
    n m l b w a q h s e we :
  Prepared.ready (Prepared.reverse p exits) ->
  Dom.exact (Prepared.reverse p exits) t ->
  resources (Prepared.reverse p exits) t n m l b w a q h s ->
  (length exits <= e)%nat ->
  (forall i, In i exits -> key_bits positive_encoding i <= we) ->
  Cost.ticks (FrontierControl.control_deps_c p exits t) <=
    control_work (N.of_nat n) (N.of_nat m) (N.of_nat l) (N.of_nat b)
      w a q h s (N.of_nat e) we.
Proof.
  intros Hready Htree Hr Hexits Hwidth.
  destruct (events_cost (Prepared.reverse p exits) t n m l b w a q h s Hready Htree Hr)
    as [Hcost [Hsupport Hlength]].
  pose proof (PreparedCost.reverse_cost_bound p exits we Hwidth) as Hreverse.
  assert (Hreverse' : Cost.ticks (Prepared.reverse_c p exits) <=
    N.of_nat e * (3 + 2 * we)).
  { eapply N.le_trans; [exact Hreverse|]. apply N.mul_le_mono; [lia|reflexivity]. }
  assert (Hsum : fold_right (fun event acc => 2 * key_charge (fst event) + 2 + acc)%N
      0 (events (Prepared.reverse p exits) t) <=
    N.of_nat (length (events (Prepared.reverse p exits) t)) * (6 + 2 * w)).
  { apply sum_work_bound. intros event acc He.
    pose proof (proj1 (proj1 (Forall_forall _ _) Hsupport event He)) as Hvalid.
    pose proof (width_bound Hr _ Hvalid) as Hbit.
    clear -Hbit. unfold key_charge. nia. }
  assert (Hcount : N.of_nat (length (events (Prepared.reverse p exits) t)) <=
    N.of_nat n * N.of_nat m * (N.of_nat b + 1)).
  { clear -Hlength.
    replace (N.of_nat n * N.of_nat m * (N.of_nat b + 1)) with
      (N.of_nat (n * m * S b)%nat) by
      (rewrite !Nat2N.inj_mul, Nat2N.inj_succ; nia).
    lia. }
  rewrite FrontierControl.control_deps_cost. unfold control_work.
  apply N.add_le_mono; [exact Hreverse'|].
  apply N.add_le_mono; [exact Hcost|].
  eapply N.le_trans; [exact Hsum|].
  apply N.mul_le_mono; [exact Hcount|reflexivity].
Qed.

(** The control polynomial uniformly includes exit multiplicity and all reversed traversal work. *)
Theorem control_bigO {V E X} (p : X -> Prepared.t V E) (exits : X -> list positive)
    (t : X -> Dom.tree) (n m l b e : X -> nat) (w a q h s we : X -> N) :
  (forall x, Prepared.ready (Prepared.reverse (p x) (exits x))) ->
  (forall x, Dom.exact (Prepared.reverse (p x) (exits x)) (t x)) ->
  (forall x, resources (Prepared.reverse (p x) (exits x)) (t x)
    (n x) (m x) (l x) (b x) (w x) (a x) (q x) (h x) (s x)) ->
  (forall x, (length (exits x) <= e x)%nat) ->
  (forall x i, In i (exits x) -> key_bits positive_encoding i <= we x) ->
  bigO (fun x => control_work (N.of_nat (n x)) (N.of_nat (m x))
    (N.of_nat (l x)) (N.of_nat (b x)) (w x) (a x) (q x) (h x) (s x)
    (N.of_nat (e x)) (we x))
    (fun x => Cost.ticks (FrontierControl.control_deps_c (p x) (exits x) (t x))).
Proof.
  intros Hready Htree Hr Hexits Hwidth. exists 1. intro x.
  eapply N.le_trans.
  - exact (control_structural_cost (p x) (exits x) (t x) (n x) (m x) (l x) (b x)
      (w x) (a x) (q x) (h x) (s x) (e x) (we x) (Hready x) (Htree x) (Hr x)
      (Hexits x) (Hwidth x)).
  - rewrite N.mul_1_l. apply N.le_add_l.
Qed.

Local Lemma max_N_on {A} (f : A -> N) xs x :
  In x xs -> f x <= fold_right (fun y acc => N.max (f y) acc) 0 xs.
Proof.
  induction xs as [|y rest IH]; intro Hin; [contradiction|].
  cbn [fold_right]. destruct Hin as [<-|Hin]; [apply N.le_max_l|].
  eapply N.le_trans; [now apply IH|apply N.le_max_r].
Qed.

Local Lemma max_nat_on {A} (f : A -> nat) xs x :
  In x xs -> (f x <= fold_right (fun y acc => Nat.max (f y) acc) O xs)%nat.
Proof.
  induction xs as [|y rest IH]; intro Hin; [contradiction|].
  cbn [fold_right]. destruct Hin as [<-|Hin]; [apply Nat.le_max_l|].
  eapply Nat.le_trans; [now apply IH|apply Nat.le_max_r].
Qed.

(** Every computational graph and tree has finite structural and external-accessor budgets. *)
Theorem resources_exist {V E} (p : Prepared.t V E) t :
  exists n m l b w a q h s, resources p t n m l b w a q h s.
Proof.
  set (nodes := Graph.nodes (Prepared.graph p)).
  set (ids := Reach.universe p).
  set (n := Nat.max (length nodes) (length ids)).
  set (m := fold_right (fun i acc =>
    Nat.max (Nat.max (length (Prepared.succ_edges p i))
      (length (Prepared.pred_edges p i))) acc) O ids).
  set (w := fold_right (fun i acc => N.max (N.pos (Pos.size i)) acc) 0 ids).
  set (a := fold_right (fun v acc => N.max (Cost.ticks (Prepared.id_of_c p v)) acc) 0 nodes).
  set (q := fold_right (fun i acc =>
    N.max (N.max (Cost.ticks (Prepared.succ_edges_c p i))
      (Cost.ticks (Prepared.pred_edges_c p i))) acc) 0 ids).
  set (h := fold_right (fun i acc =>
    N.max (Cost.ticks (Scope.admits_c Reach.unrestricted i)) acc) 0 ids).
  exists n, m, (length (Prepared.entry_ids p)), (Map.size (Dom.idom t)), w, a, q, h,
    (MapCost.skeleton_nodes (Dom.idom t)).
  assert (Hids : forall i, Prepared.valid_id p i -> In i ids).
  { intros i Hi. now apply Reach.universe_spec. }
  constructor.
  - unfold n, nodes. apply Nat.le_max_l.
  - unfold n, ids. apply Nat.le_max_r.
  - lia.
  - lia.
  - reflexivity.
  - intros i Hi. exact (max_N_on _ ids i (Hids i Hi)).
  - intros v Hv. exact (max_N_on _ nodes v Hv).
  - intros i Hi. eapply N.le_trans; [apply N.le_max_l|].
    exact (max_N_on _ ids i (Hids i Hi)).
  - intros i Hi. eapply N.le_trans; [apply N.le_max_r|].
    exact (max_N_on _ ids i (Hids i Hi)).
  - intros i Hi. eapply Nat.le_trans; [apply Nat.le_max_l|].
    exact (max_nat_on _ ids i (Hids i Hi)).
  - intros i Hi. eapply Nat.le_trans; [apply Nat.le_max_r|].
    exact (max_nat_on _ ids i (Hids i Hi)).
  - intros i Hi. exact (max_N_on _ ids i (Hids i Hi)).
Qed.

End FrontierCost.
