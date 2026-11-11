(** * Primitive-derived countdown costs

    A popped source pays for its user bucket from an occurrence credit that is spent once.
    For example, two occurrences of one operand consume two credits in the same pop.
    Builds on: AnalysesEqualityLoopCorrect, BaseIndexCost, BaseMapCost and CostLoop. *)

From Stdlib Require Import List Bool Arith Lia PArith NArith.
From Galois.Cost Require Import CostMonad CostList CostLoop CostBound.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseMapCost BaseSet BaseSetCost
  BaseIndex BaseIndexCost BaseTrieCost.
From Galois.Analyses.Equality Require Import AnalysesEqualityLoopWorklist
  AnalysesEqualityLoopCorrect.
Import List.ListNotations Cost.Notations NumberingLoopWorklist NumberingLoopCorrect.

Local Open Scope nat_scope.

Module NumberingLoopCost.

Section Costs.
Context {V : Type} (E : encoding V) (HE : encoding_laws E).

(** Rows retain every dependency occurrence, including repeated operands. *)
Definition rows (definitions : Map.t V (list V)) : list (V * V) :=
  flat_map (fun entry => map (fun dependency => (dependency, fst entry)) (snd entry))
    (Map.elements definitions).

(** Primitive prices cover the finite universe and the actual dependency-source domain. *)
Definition primitive_prices universe definitions e w : Prop :=
  forall x, In x (FinSet.elements universe) \/ In x (map fst (rows definitions)) ->
    (Cost.ticks (encode_c E x) <= e)%N /\ (key_bits E x <= w)%N.

(** One map operation retains both the encoder callback and the encoded key's bit traversal. *)
Definition key_price (e w : N) : N := 1 + e + w.

(** Notification credits account for four possible map operations and both callback ticks. *)
Definition edge_price (e w : N) : N := 2 + 4 * key_price e w.

(** A pop credit pays for its two lookups or updates and the common driver's descent. *)
Definition pop_price (e w : N) : N := 3 + 2 * key_price e w.

Local Lemma node_price universe definitions e w x :
  primitive_prices universe definitions e w ->
  FinSet.wf E universe -> FinSet.mem E x universe = true ->
  (Cost.ticks (encode_c E x) <= e)%N /\ (key_bits E x <= w)%N.
Proof.
  intros Hprices Hwf Hmem; apply Hprices; left.
  now apply (FinSet.elements_spec E HE x universe Hwf).
Qed.

Local Lemma row_user universe definitions edge :
  Map.wf E definitions -> rules_supported E universe definitions ->
  In edge (rows definitions) -> FinSet.mem E (snd edge) universe = true.
Proof.
  intros Hwf Hsupport Hin; unfold rows in Hin.
  apply in_flat_map in Hin as [[user deps] [Hentry Hrow]].
  apply in_map_iff in Hrow as [dependency [<- Hdep]]; cbn [snd].
  apply (Hsupport user deps); now apply (Map.elements_spec E HE user deps definitions Hwf).
Qed.

Local Lemma prepared_bucket universe definitions x :
  Index.find E x (users (prepare E universe definitions)) =
    filter (fun edge => eqb E (fst edge) x) (rows definitions).
Proof.
  rewrite prepare_equation; cbn [users].
  rewrite Index.find_group_by, edge_rows_value; reflexivity.
Qed.

(** A notification's time depends only on the notified user's primitive key price. *)
Theorem notify_cost s edge e w :
  (Cost.ticks (encode_c E (snd edge)) <= e)%N ->
  (key_bits E (snd edge) <= w)%N ->
  (Cost.ticks (notify_c E s edge) <= 4 * key_price e w)%N.
Proof.
  intros Hencode Hwidth; unfold notify_c; rewrite Cost.ticks_bind.
  fold (Map.get E (snd edge) (remaining s)).
  pose proof (Map.get_cost E (snd edge) (remaining s)) as Hget.
  fold (key_bits E (snd edge)) in Hget.
  destruct (Map.get E (snd edge) (remaining s)) as [[|[|n]]|];
    autorewrite with galois_cost; try (unfold key_price; nia).
  - rewrite Map.set_cost; fold (key_bits E (snd edge)).
    change (Cost.ticks (Map.get_c E (snd edge) (remaining s)) +
      (1 + Cost.ticks (encode_c E (snd edge)) + key_bits E (snd edge) +
       Cost.ticks
         (let* fresh := FinSet.mem_c E (snd edge) (available s) in
          if fresh then
            let* untouched := FinSet.remove_c E (snd edge) (available s) in
            Cost.ret (State (snd edge :: todo s) (marked s) untouched
              (Map.set E (snd edge) 0%nat (remaining s)) (processed s))
          else Cost.ret (State (todo s) (marked s) (available s)
            (Map.set E (snd edge) 0%nat (remaining s)) (processed s)))) <=
      4 * key_price e w)%N.
    rewrite Cost.ticks_bind; fold (FinSet.mem E (snd edge) (available s)).
    unfold FinSet.mem_c; rewrite Map.mem_cost; fold (key_bits E (snd edge)).
    destruct (FinSet.mem E (snd edge) (available s)); autorewrite with galois_cost.
    + unfold FinSet.remove_c; rewrite Map.remove_cost; fold (key_bits E (snd edge)).
      unfold key_price; nia.
    + unfold key_price; nia.
  - rewrite Map.set_cost; fold (key_bits E (snd edge)); unfold key_price; nia.
Qed.

(** Processing one bucket charges each occurrence once, independently of its counter branch. *)
Theorem notifications_cost uses s e w :
  (forall edge, In edge uses ->
    (Cost.ticks (encode_c E (snd edge)) <= e)%N /\ (key_bits E (snd edge) <= w)%N) ->
  (Cost.ticks (notifications_c E uses s) <=
    N.of_nat (length uses) * edge_price e w)%N.
Proof.
  unfold notifications_c; revert s; induction uses as [|edge rest IH]; intros s Hprices.
  - rewrite ticks_fold_left_c_nil; reflexivity.
  - rewrite ticks_fold_left_c_cons; autorewrite with galois_cost.
    destruct (Hprices edge (or_introl eq_refl)) as [Hencode Hwidth].
    pose proof (notify_cost s edge e w Hencode Hwidth) as Hnotify.
    specialize (IH (notify E s edge) (fun a Ha => Hprices a (or_intror Ha))).
    change (1 + (1 + Cost.ticks (notify_c E s edge)) +
      Cost.ticks (fold_left_c (fun s edge => Cost.step ;; notify_c E s edge)
        rest (notify E s edge)) <=
      N.of_nat (S (length rest)) * edge_price e w)%N.
    cbn [length]; rewrite Nat2N.inj_succ; unfold edge_price in *; nia.
Qed.

(** Remaining row credit is a specification measure over the already prepared occurrence list. *)
Definition pending_rows definitions s :=
  length (filter (fun edge => negb (FinSet.mem E (fst edge) (marked s))) (rows definitions)).

(** Marking a fresh source consumes precisely the length of its prepared user bucket. *)
Theorem pending_rows_pop universe definitions s source rest :
  FinSet.mem E source (marked s) = false ->
  pending_rows definitions s =
    length (Index.find E source (users (prepare E universe definitions))) +
    pending_rows definitions
      (State rest (FinSet.add E source (marked s)) (available s)
        (remaining s) (S (processed s))).
Proof.
  intro Hfresh; rewrite prepared_bucket; unfold pending_rows; cbn [marked].
  induction (rows definitions) as [|[dependency user] rest_rows IH]; [reflexivity|].
  cbn [filter fst]; rewrite FinSet.mem_add_raw.
  destruct (eqb_spec E HE dependency source) as [->|Hdifferent].
  - rewrite Hfresh; cbn [negb orb length]; lia.
  - cbn [orb]; destruct (FinSet.mem E dependency (marked s)); cbn [negb length]; lia.
Qed.

(** Notifications preserve the remaining source-row credit because they do not mark sources. *)
Theorem pending_rows_notifications definitions uses s :
  state_wf E s -> pending_rows definitions (notifications E uses s) = pending_rows definitions s.
Proof.
  intro Hwf; destruct (notifications_preserved E uses s Hwf) as [_ [_ [_ Hmarked]]].
  unfold pending_rows; now rewrite Hmarked.
Qed.

(** The amortised credit combines one-shot queue reservations and untouched user occurrences. *)
Definition credit definitions e w s : N :=
  pop_price e w * N.of_nat (potential s) +
  edge_price e w * N.of_nat (pending_rows definitions s).

Local Lemma queued_member universe definitions s x :
  rules_supported E universe definitions ->
  correct E universe definitions s -> In x (todo s) -> FinSet.mem E x universe = true.
Proof.
  intros Hsupport [_ [_ [Hcounts [Hqueued _]]]] Hin.
  pose proof (Hqueued x Hin) as Hcounter; rewrite Hcounts in Hcounter.
  destruct (Map.get E x definitions) as [deps|] eqn:Hrule; [|discriminate].
  exact (Hsupport x deps Hrule).
Qed.

(** Each actual pop spends its complete bucket and enough queue credit for the binary driver. *)
Theorem step_credit universe definitions e w s :
  FinSet.wf E universe -> Map.wf E definitions ->
  rules_supported E universe definitions -> primitive_prices universe definitions e w ->
  correct E universe definitions s ->
  match Cost.value (step_c E (prepare E universe definitions) s) with
  | inl next =>
    correct E universe definitions next /\
    (Cost.ticks (step_c E (prepare E universe definitions) s) +
      credit definitions e w next + 2 <= credit definitions e w s)%N
  | inr _ => (Cost.ticks (step_c E (prepare E universe definitions) s) <=
      credit definitions e w s)%N
  end.
Proof.
  intros Huniverse Hdefinitions Hsupported Hprices Hcorrect.
  pose proof (step_correct E HE universe definitions s Hdefinitions Hcorrect) as Hnext.
  destruct (todo s) as [|source rest] eqn:Htodo.
  - rewrite step_equation, Htodo; unfold step_c; rewrite Htodo, Cost.ticks_ret; lia.
  - assert (Hwf : state_wf E s) by exact (proj1 Hcorrect).
    assert (Hfresh : FinSet.mem E source (marked s) = false).
    { exact (proj1 (queue_reserved E universe s (proj1 (proj2 Hcorrect)) source
        ltac:(rewrite Htodo; now left))). }
    destruct (node_price universe definitions e w source Hprices Huniverse
      (queued_member universe definitions s source Hsupported Hcorrect
        ltac:(rewrite Htodo; now left))) as [Hencode Hwidth].
    set (base := State rest (FinSet.add E source (marked s))
      (available s) (remaining s) (S (processed s))).
    set (uses := Index.find E source (users (prepare E universe definitions))).
    assert (Hbase : state_wf E base).
    { destruct Hwf as [Hm [Ha Hr]]; split; [now apply FinSet.wf_add|now split]. }
    pose proof (notifications_cost uses base e w) as Hnotifications.
    assert (Husers : forall edge, In edge uses ->
      (Cost.ticks (encode_c E (snd edge)) <= e)%N /\ (key_bits E (snd edge) <= w)%N).
    { intros edge Hin; apply (node_price universe definitions e w _ Hprices Huniverse).
      apply (row_user universe definitions edge Hdefinitions Hsupported).
      unfold uses in Hin; rewrite prepared_bucket in Hin; now apply filter_In in Hin as [Hin _]. }
    specialize (Hnotifications Husers).
    pose proof (pending_rows_pop universe definitions s source rest Hfresh) as Hrows.
    fold base uses in Hrows.
    pose proof (pending_rows_notifications definitions uses base Hbase) as Hrow_next.
    destruct (notifications_preserved E uses base Hbase) as [_ [Hpotential _]].
    assert (Hpop : potential s = S (potential base)).
    { unfold potential, base; rewrite Htodo; cbn [available todo length]; lia. }
    rewrite step_equation, Htodo in Hnext |- *; fold base uses in Hnext |- *.
    split; [exact Hnext|].
    assert (Hcost : (Cost.ticks (step_c E (prepare E universe definitions) s) <=
      2 * key_price e w + N.of_nat (length uses) * edge_price e w)%N).
    { unfold step_c; rewrite Htodo; autorewrite with galois_cost.
      change (Cost.ticks (FinSet.add_c E source (marked s)) +
        (Cost.ticks (Index.find_c E source (users (prepare E universe definitions))) +
         (Cost.ticks (notifications_c E uses base) + 0)) <=
        2 * key_price e w + N.of_nat (length uses) * edge_price e w)%N.
      unfold FinSet.add_c; rewrite Map.set_cost, Index.find_cost, Map.get_cost.
      fold (key_bits E source); unfold key_price; nia. }
    unfold credit; rewrite Hpotential, Hrow_next, Hpop, Hrows, Nat2N.inj_succ, Nat2N.inj_add.
    unfold pop_price; nia.
Qed.

(** The common driver's cost is linear in initial queue and user-occurrence credits. *)
Theorem iterate_cost universe definitions e w fuel :
  FinSet.wf E universe -> Map.wf E definitions ->
  rules_supported E universe definitions -> primitive_prices universe definitions e w ->
  (Cost.ticks (iterate (step_c E (prepare E universe definitions)) fuel
    (initial E (prepare E universe definitions))) <=
    pop_price e w * N.of_nat (FinSet.size universe) +
    edge_price e w * N.of_nat (length (rows definitions)) +
    N.pos (Pos.size fuel))%N.
Proof.
  intros Huniverse Hdefinitions Hsupported Hprices.
  pose proof (iterate_terminal_credit (step_c E (prepare E universe definitions))
    (correct E universe definitions) (credit definitions e w) (fun _ => 0%N) 0%N)
    as Hdriver.
  assert (Hstep : forall s, correct E universe definitions s ->
    match Cost.value (step_c E (prepare E universe definitions) s) with
    | inl next => correct E universe definitions next /\
      (Cost.ticks (step_c E (prepare E universe definitions) s) +
       credit definitions e w next + 2 <= credit definitions e w s)%N
    | inr _ => (Cost.ticks (step_c E (prepare E universe definitions) s) + 0 <=
      0 + credit definitions e w s)%N
    end).
  { intros s Hcorrect; pose proof
      (step_credit universe definitions e w s Huniverse Hdefinitions Hsupported Hprices Hcorrect)
      as Hlocal.
    destruct (Cost.value (step_c E (prepare E universe definitions) s)); simpl;
      [exact Hlocal|lia]. }
  specialize (Hdriver Hstep fuel _ (initial_correct E HE universe definitions Huniverse Hdefinitions)).
  pose proof (initial_potential_bound E HE universe definitions Huniverse) as Hnodes.
  assert (Horder : length (node_order (prepare E universe definitions)) = FinSet.size universe).
  { rewrite prepare_equation; cbn [node_order]; symmetry; apply FinSet.size_elements. }
  rewrite Horder in Hnodes.
  assert (Hrows : pending_rows definitions (initial E (prepare E universe definitions)) <=
    length (rows definitions)).
  { unfold pending_rows.
    generalize (rows definitions) as edges; intro edges.
    induction edges as [|edge rest IH]; [reflexivity|].
    cbn [filter length].
    destruct (FinSet.mem E (fst edge) (marked (initial E (prepare E universe definitions))));
      cbn [negb length]; lia. }
  unfold credit in Hdriver.
  destruct (Cost.value (iterate (step_c E (prepare E universe definitions)) fuel
    (initial E (prepare E universe definitions)))); nia.
Qed.

(** Dependency mass is the total list length stored in the finite rule map. *)
Definition dependency_mass (entries : list (V * list V)) : N :=
  fold_right (fun entry total => N.of_nat (length (snd entry)) + total)%N 0%N entries.

(** Row construction preserves the dependency mass exactly. *)
Theorem rows_length definitions :
  N.of_nat (length (rows definitions)) = dependency_mass (Map.elements definitions).
Proof.
  unfold rows, dependency_mass.
  induction (Map.elements definitions) as [|[user deps] rest IH]; [reflexivity|].
  cbn [flat_map fst snd fold_right]; rewrite length_app, length_map, Nat2N.inj_add, IH.
  reflexivity.
Qed.

(** Row preparation charges its entry traversal and both traversals of every dependency list. *)
Theorem edge_rows_cost entries :
  Cost.ticks (edge_rows_c entries) =
    (N.of_nat (length entries) + 2 * dependency_mass entries)%N.
Proof.
  unfold edge_rows_c; induction entries as [|[user deps] rest IH]; [reflexivity|].
  rewrite ticks_fold_right_c_cons; cbn [fst snd].
  rewrite Cost.ticks_bind, value_map_c, ticks_app_c.
  assert (Hmap : Cost.ticks (map_c (fun dependency : V => Cost.ret (dependency, user)) deps) =
    N.of_nat (length deps)).
  { rewrite ticks_map_c.
    induction deps as [|dependency tail IHdeps]; cbn [fold_right length];
      autorewrite with galois_cost; rewrite ?Nat2N.inj_succ, ?IHdeps; lia. }
  rewrite Hmap, length_map, IH.
  change (1 + (N.of_nat (length rest) + 2 * dependency_mass rest) +
    (N.of_nat (length deps) + N.of_nat (length deps)) =
    N.of_nat (S (length rest)) + 2 * (N.of_nat (length deps) + dependency_mass rest))%N.
  rewrite Nat2N.inj_succ; nia.
Qed.

(** Filtering needs callback budgets only at the finite list elements it actually visits. *)
Theorem filter_visited_cost {A} (f : A -> Cost.t bool) xs k :
  (forall x, In x xs -> (Cost.ticks (f x) <= k)%N) ->
  (Cost.ticks (filter_c f xs) <= N.of_nat (length xs) * (k + 1))%N.
Proof.
  rewrite ticks_filter_c; induction xs as [|x rest IH]; intro Hprices; [reflexivity|].
  cbn [fold_right length]; rewrite Nat2N.inj_succ.
  pose proof (Hprices x (or_introl eq_refl)) as Hhead.
  specialize (IH (fun y Hy => Hprices y (or_intror Hy))); nia.
Qed.

(** Rule support bounds the stored map size by the distinct finite universe. *)
Theorem definitions_size universe definitions :
  FinSet.wf E universe -> Map.wf E definitions -> rules_supported E universe definitions ->
  Map.size definitions <= FinSet.size universe.
Proof.
  intros Huniverse Hdefinitions Hsupport; rewrite FinSet.size_elements.
  apply (Map.size_support_bound E HE (FinSet.elements universe) definitions Hdefinitions).
  intros x deps Hget; apply (FinSet.elements_spec E HE x universe Huniverse).
  now apply (Hsupport x deps).
Qed.

Local Lemma definitions_width universe definitions e w :
  FinSet.wf E universe -> rules_supported E universe definitions ->
  primitive_prices universe definitions e w ->
  forall x deps, Map.get E x definitions = Some deps -> (key_bits E x <= w)%N.
Proof.
  intros Huniverse Hsupport Hprices x deps Hget.
  exact (proj2 (node_price universe definitions e w x Hprices Huniverse (Hsupport x deps Hget))).
Qed.

(** The preparation constant includes both physical trie traversals and list/callback overhead. *)
Definition prepare_k : N := 12 + 4 * TrieCost.trie_k.

Local Lemma length_sum entries :
  fold_right (fun entry total => Cost.ticks (length_c (snd entry)) + total)%N 0%N entries =
    dependency_mass entries.
Proof.
  unfold dependency_mass; induction entries as [|entry rest IH]; cbn [fold_right];
    rewrite ?ticks_length_c, ?IH; reflexivity.
Qed.

(** Complete countdown preparation is linear in universe size and dependency occurrences. *)
Theorem prepare_cost universe definitions e w :
  FinSet.wf E universe -> Map.wf E definitions ->
  rules_supported E universe definitions -> primitive_prices universe definitions e w ->
  (Cost.ticks (prepare_c E universe definitions) <=
    prepare_k * (1 + N.of_nat (FinSet.size universe) + N.of_nat (length (rows definitions))) *
      (1 + e + w))%N.
Proof.
  intros Huniverse Hdefinitions Hsupport Hprices.
  assert (Hwidth : forall x deps, Map.get E x definitions = Some deps ->
    (key_bits E x <= w)%N).
  { exact (definitions_width universe definitions e w Huniverse Hsupport Hprices). }
  pose proof (MapCost.elements_numeric_cost E definitions w Hdefinitions Hwidth) as Hentries.
  pose proof (MapCost.elements_numeric_cost E universe w Huniverse) as Hnodes.
  assert (Hnode_width : forall x (u : unit), Map.get E x universe = Some u ->
    (key_bits E x <= w)%N).
  { intros x [] Hget; exact (proj2 (node_price universe definitions e w x Hprices Huniverse
      (proj2 (FinSet.mem_spec E x universe) Hget))). }
  specialize (Hnodes Hnode_width).
  pose proof (definitions_size universe definitions Huniverse Hdefinitions Hsupport) as Hsize.
  pose proof (edge_rows_cost (Map.elements definitions)) as Hrows.
  rewrite <- rows_length, <- Map.size_elements in Hrows.
  set (edges := Cost.value (edge_rows_c (Map.elements definitions))).
  assert (Hedges : edges = rows definitions) by (unfold edges; apply edge_rows_value).
  pose proof (IndexCost.group_by_cost Map.cost_laws_hold E HE
    (fun edge : V * V => Cost.ret (fst edge)) edges e w 0%N) as Hindex.
  assert (Hedge_prices : forall edge, In edge edges ->
    (Cost.ticks (Cost.ret (fst edge)) <= 0)%N /\
    (Cost.ticks (encode_c E (Cost.value (Cost.ret (fst edge)))) <= e)%N /\
    (key_bits E (Cost.value (Cost.ret (fst edge))) <= w)%N).
  { intros edge Hin; split; [reflexivity|]; apply Hprices; right.
    apply in_map_iff; exists edge; split; [reflexivity|now rewrite <- Hedges]. }
  specialize (Hindex Hedge_prices); rewrite Hedges in Hindex.
  pose proof (MapCost.map_numeric_cost E length_c definitions w Hdefinitions Hwidth) as Hcounts.
  assert (Hsum : fold_right (fun entry total =>
    Cost.ticks (length_c (snd entry)) + total)%N 0%N (Map.elements definitions) =
    N.of_nat (length (rows definitions))).
  { rewrite rows_length; apply length_sum. }
  rewrite Hsum in Hcounts.
  set (counts := Cost.value (Map.map_c length_c definitions)).
  pose proof (filter_visited_cost (fun x =>
    let* count := Map.get_c E x counts in
    Cost.ret (match count with Some 0%nat => true | _ => false end))
    (FinSet.elements universe) (key_price e w)) as Hseeds.
  assert (Hseed_prices : forall x, In x (FinSet.elements universe) ->
    (Cost.ticks
      (let* count := Map.get_c E x counts in
       Cost.ret (match count with Some 0%nat => true | _ => false end)) <= key_price e w)%N).
  { intros x Hin; autorewrite with galois_cost; rewrite Map.get_cost; fold (key_bits E x).
    destruct (Hprices x (or_introl Hin)) as [Hencode Hbits]; unfold key_price; nia. }
  specialize (Hseeds Hseed_prices).
  rewrite <- FinSet.size_elements in Hseeds.
  unfold prepare_c; rewrite !Cost.ticks_bind.
  change (Cost.ticks (FinSet.elements_c universe) + (Cost.ticks (Map.elements_c definitions) +
    (Cost.ticks (edge_rows_c (Map.elements definitions)) +
    (Cost.ticks (Index.group_by_c E (fun edge => Cost.ret (fst edge)) edges) +
    (Cost.ticks (Map.map_c length_c definitions) +
    (Cost.ticks (filter_c (fun x =>
      let* count := Map.get_c E x counts in
      Cost.ret (match count with Some 0%nat => true | _ => false end))
      (FinSet.elements universe)) + 0))))) <=
    prepare_k * (1 + N.of_nat (FinSet.size universe) + N.of_nat (length (rows definitions))) *
      (1 + e + w))%N.
  rewrite FinSet.elements_cost_equation, Hedges.
  rewrite FinSet.size_backend in *.
  unfold prepare_k, key_price in *; nia.
Qed.

Local Lemma prepared_seeds universe definitions :
  incl (seeds (prepare E universe definitions)) (FinSet.elements universe) /\
  length (seeds (prepare E universe definitions)) <= FinSet.size universe.
Proof.
  rewrite prepare_equation; cbn [seeds]; split.
  - intros x Hin; now apply filter_In in Hin as [Hin _].
  - rewrite FinSet.size_elements.
    generalize (FinSet.elements universe) as order; intro order.
    induction order as [|x rest IH]; [reflexivity|].
    cbn [filter length].
    destruct (Map.get E x (Cost.value (Map.map_c length_c definitions))) as [[|n]|];
      cbn [length]; lia.
Qed.

(** Initialization retains seed construction and the full candidate-set difference traversal. *)
Theorem initial_cost universe definitions e w :
  FinSet.wf E universe -> primitive_prices universe definitions e w ->
  (Cost.ticks (initial_c E (prepare E universe definitions)) <=
    (4 + TrieCost.trie_k) * (1 + N.of_nat (FinSet.size universe)) * (1 + e + w))%N.
Proof.
  intros Huniverse Hprices; set (pr := prepare E universe definitions).
  destruct (prepared_seeds universe definitions) as [Hin Hlength]; fold pr in Hin, Hlength.
  pose proof (FinSet.of_list_numeric_cost Map.cost_laws_hold E (seeds pr) e w
    (fun x Hx => Hprices x (or_introl (Hin x Hx)))) as Hseeds.
  assert (Hnodes : nodes pr = universe).
  { unfold pr; rewrite prepare_equation; reflexivity. }
  pose proof (FinSetCost.diff_numeric_cost E universe (FinSet.of_list E (seeds pr)) w
    Huniverse) as Hdiff.
  specialize (Hdiff (fun x Hx =>
    proj2 (node_price universe definitions e w x Hprices Huniverse Hx))).
  unfold initial_c; rewrite !Cost.ticks_bind; fold (FinSet.of_list E (seeds pr)).
  rewrite Hnodes; autorewrite with galois_cost; nia.
Qed.

Local Lemma positive_bits p : (N.pos (Pos.size p) <= N.pos p)%N.
Proof.
  induction p as [p IH|p IH|]; [| |reflexivity].
  - change (N.succ (N.pos (Pos.size p)) <= 1 + 2 * N.pos p)%N; nia.
  - change (N.succ (N.pos (Pos.size p)) <= 2 * N.pos p)%N; nia.
Qed.

Local Lemma successor_bits n :
  (N.pos (Pos.size (Pos.of_succ_nat n)) <= N.of_nat (S n))%N.
Proof.
  pose proof (positive_bits (Pos.of_succ_nat n)) as Hbits.
  assert (Hvalue : N.pos (Pos.of_succ_nat n) = N.of_nat (S n)).
  { apply N2Nat.inj; rewrite Nat2N.id; change (Pos.to_nat (Pos.of_succ_nat n) = S n).
    apply SuccNat2Pos.id_succ. }
  now rewrite <- Hvalue.
Qed.

(** The complete kernel constant covers preparation, initialization, binary descent and all pops. *)
Definition kernel_k : N := 64 + 8 * TrieCost.trie_k.

Local Lemma kernel_sum n d e w bits :
  (bits <= 1 + n)%N ->
  (prepare_k * (1 + n + d) * (1 + e + w) +
    ((4 + TrieCost.trie_k) * (1 + n) * (1 + e + w) +
    (n + (pop_price e w * n + edge_price e w * d + bits))) <=
    kernel_k * (1 + n + d) * (1 + e + w))%N.
Proof.
  intro Hbits; unfold kernel_k, prepare_k, pop_price, edge_price, key_price; nia.
Qed.

(** The same countdown driver used by correctness has a full linear primitive-resource bound. *)
Theorem solve_cost universe definitions e w :
  FinSet.wf E universe -> Map.wf E definitions ->
  rules_supported E universe definitions -> primitive_prices universe definitions e w ->
  (Cost.ticks (solve_c E universe definitions) <=
    kernel_k * (1 + N.of_nat (FinSet.size universe) + N.of_nat (length (rows definitions))) *
      (1 + e + w))%N.
Proof.
  intros Huniverse Hdefinitions Hsupport Hprices; set (pr := prepare E universe definitions).
  pose proof (prepare_cost universe definitions e w Huniverse Hdefinitions Hsupport Hprices)
    as Hprepare.
  pose proof (initial_cost universe definitions e w Huniverse Hprices) as Hinitial.
  pose proof (iterate_cost universe definitions e w
    (Pos.of_succ_nat (length (node_order pr))) Huniverse Hdefinitions Hsupport Hprices) as Hrun.
  fold pr in Hinitial, Hrun.
  assert (Horder : length (node_order pr) = FinSet.size universe).
  { unfold pr; rewrite prepare_equation; symmetry; apply FinSet.size_elements. }
  pose proof (successor_bits (length (node_order pr))) as Hbits.
  rewrite Horder in Hbits.
  unfold solve_c; rewrite Cost.ticks_bind; fold pr.
  unfold solve_prepared_c; rewrite !Cost.ticks_bind, value_length_c, ticks_length_c.
  change (Cost.ticks (prepare_c E universe definitions) +
    (Cost.ticks (initial_c E pr) + (N.of_nat (length (node_order pr)) +
      Cost.ticks (iterate (step_c E pr) (Pos.of_succ_nat (length (node_order pr)))
        (initial E pr)))) <=
    kernel_k * (1 + N.of_nat (FinSet.size universe) + N.of_nat (length (rows definitions))) *
      (1 + e + w))%N.
  rewrite Horder in *.
  eapply N.le_trans.
  - apply N.add_le_mono; [exact Hprepare|].
    apply N.add_le_mono; [exact Hinitial|].
    apply N.add_le_mono_l; exact Hrun.
  - apply kernel_sum; rewrite Nat2N.inj_succ in Hbits; lia.
Qed.

(** A prepared solve inherits the complete kernel bound while retaining all initialization work. *)
Theorem solve_prepared_cost universe definitions e w :
  FinSet.wf E universe -> Map.wf E definitions ->
  rules_supported E universe definitions -> primitive_prices universe definitions e w ->
  (Cost.ticks (solve_prepared_c E (prepare E universe definitions)) <=
    kernel_k * (1 + N.of_nat (FinSet.size universe) + N.of_nat (length (rows definitions))) *
      (1 + e + w))%N.
Proof.
  intros Huniverse Hdefinitions Hsupport Hprices.
  pose proof (solve_cost universe definitions e w Huniverse Hdefinitions Hsupport Hprices) as Hcost.
  unfold solve_c in Hcost; rewrite Cost.ticks_bind in Hcost; exact (N.le_trans _ _ _
    (N.le_add_l _ _) Hcost).
Qed.

(** Varying finite instances retain their own sizes, encoder budgets and actual key widths. *)
Theorem solve_bigO {X} (universes : X -> FinSet.t V) (definitions : X -> Map.t V (list V))
    (encoder width : X -> N) :
  (forall x, FinSet.wf E (universes x)) ->
  (forall x, Map.wf E (definitions x)) ->
  (forall x, rules_supported E (universes x) (definitions x)) ->
  (forall x, primitive_prices (universes x) (definitions x) (encoder x) (width x)) ->
  bigO (fun x =>
    ((1 + N.of_nat (FinSet.size (universes x)) +
      N.of_nat (length (rows (definitions x)))) * (1 + encoder x + width x))%N)
    (fun x => Cost.ticks (solve_c E (universes x) (definitions x))).
Proof.
  intros Huniverse Hdefinitions Hsupport Hprices; exists kernel_k; intro x.
  pose proof (solve_cost (universes x) (definitions x) (encoder x) (width x)
    (Huniverse x) (Hdefinitions x) (Hsupport x) (Hprices x)) as Hcost; nia.
Qed.

End Costs.

End NumberingLoopCost.
