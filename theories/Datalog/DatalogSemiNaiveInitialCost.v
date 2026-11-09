(** * Complete setup costs for a semi-naive stratum

    Setup charges source classification, nonrecursive firing, seed storage and every prepared job.
    For example, a rule that emits no facts still pays its literal and preparation inventories.
    Builds on: DatalogSemiNaiveCandidateCost and the complete prepared-firing contract. *)

From Stdlib Require Import List Bool PeanoNat NArith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet BaseTrieCost.
From Galois.Lattice Require Import LatticeSet.
From Galois.Datalog Require Import DatalogSyntax DatalogStratify DatalogRelation DatalogFire
  DatalogCost DatalogJoin DatalogJoinPrepareCost DatalogJoinPreparedFire DatalogSemiNaive
  DatalogSemiNaiveSyntax DatalogSemiNaiveIndex DatalogSemiNaiveCost DatalogSemiNaiveBudget
  DatalogSemiNaiveCandidateCost DatalogSemiNaiveTrace.
Import List.ListNotations Cost.Notations SemiNaive SemiNaiveSyntax SemiNaiveIndex
  SemiNaiveCost SemiNaiveBudget SemiNaiveCandidateCost SemiNaiveTrace.
Local Open Scope N_scope.

Module SemiNaiveInitialCost.

Lemma fold_price {A B} (f : A -> B -> Cost.t B) xs init price :
  (forall x acc, In x xs -> Cost.ticks (f x acc) <= price x) ->
  Cost.ticks (fold_right_c f init xs) <= sum (fun x => 1 + price x) xs.
Proof.
  induction xs as [|x xs IH]; intro Hprice; [change (0 <= 0); lia |].
  rewrite ticks_fold_right_c_cons.
  pose proof (Hprice x (Cost.value (fold_right_c f init xs)) (or_introl eq_refl)).
  specialize (IH (fun y acc Hy => Hprice y acc (or_intror Hy))).
  unfold sum at 1; cbn [fold_right]; fold (sum (fun y => 1 + price y) xs); lia.
Qed.

Lemma pivots_length {P} (st : stratification P) k position ls :
  (length (Cost.value (pivots_from_c st k position ls)) <= length ls)%nat.
Proof.
  revert position; induction ls as [|[atom | atom] rest IH]; intro position;
    rewrite pivots_from_equation; cbn [length]; [lia | |].
  - destruct (Nat.eqb (level st (pred atom)) k); cbn [length];
      specialize (IH (S position)); lia.
  - specialize (IH position); lia.
Qed.

Lemma ret_map_cost {A B} (f : A -> B) xs :
  Cost.ticks (map_c (fun x => Cost.ret (f x)) xs) = N.of_nat (length xs).
Proof.
  rewrite ticks_map_c; induction xs as [|x xs IH]; cbn [fold_right length]; [reflexivity |].
  rewrite Cost.ticks_ret, Nat2N.inj_succ; lia.
Qed.

Lemma pivots_cost {P} (st : stratification P) k position ls l :
  (forall atom, In (LPos atom) ls -> Cost.ticks (level_c st (pred atom)) <= l) ->
  Cost.ticks (pivots_from_c st k position ls) <= N.of_nat (length ls) * (2 + l).
Proof.
  revert position; induction ls as [|[atom | atom] rest IH]; intros position Hlevel;
    [change (0 <= 0); lia | |].
  - cbn [pivots_from_c]; repeat rewrite Cost.ticks_bind.
    rewrite !Cost.ticks_step, Cost.ticks_ret.
    pose proof (Hlevel atom (or_introl eq_refl)).
    specialize (IH (S position) (fun x Hx => Hlevel x (or_intror Hx))).
    cbn [length]; rewrite Nat2N.inj_succ; nia.
  - cbn [pivots_from_c]; rewrite Cost.ticks_bind, Cost.ticks_step.
    specialize (IH position (fun x Hx => Hlevel x (or_intror Hx))).
    cbn [length]; rewrite Nat2N.inj_succ; nia.
Qed.

(** Source classification pays every rule and literal occurrence, including unselected rules. *)
Definition classification_charge {P} (rs : list (rule P)) b :=
  sum (fun r => 2 + level_bound b + N.of_nat (length (body r)) * (4 + level_bound b)) rs.

Lemma classify_one_cost {P} (st : stratification P) k r acc b :
  Cost.ticks (level_c st (pred (head r))) <= level_bound b ->
  (forall atom, In (LPos atom) (body r) ->
    Cost.ticks (level_c st (pred atom)) <= level_bound b) ->
  Cost.ticks (classify_one_c st k r acc) <=
    1 + level_bound b + N.of_nat (length (body r)) * (4 + level_bound b).
Proof.
  intros Hhead Hbody.
  pose proof (pivots_cost st k 0 (body r) _ Hbody) as Hpivots.
  pose proof (nat_N_le _ _ (pivots_length st k 0 (body r))) as Hlength.
  unfold classify_one_c; repeat rewrite Cost.ticks_bind; rewrite Cost.ticks_step.
  fold (level st (pred (head r))); destruct (Nat.eqb (level st (pred (head r))) k);
    [|rewrite Cost.ticks_ret; nia].
  rewrite Cost.ticks_bind.
  fold (@pivots P st k r).
  destruct (pivots st k r) as [|position rest] eqn:Hpositions.
  - rewrite Cost.ticks_ret; nia.
  - repeat rewrite Cost.ticks_bind; rewrite ticks_app_c, value_map_c, length_map.
    rewrite Cost.ticks_ret.
    assert (Hmap : Cost.ticks (map_c (fun i => Cost.ret (r, i)) (position :: rest)) =
      N.of_nat (length (position :: rest))).
    { apply ret_map_cost. }
    rewrite Hmap; fold (@pivots P st k r) in Hlength.
    rewrite Hpositions in Hlength; nia.
Qed.

(** Classification derives its full scan price from primitive level callbacks. *)
Theorem classify_cost {P} (st : stratification P) k rs b :
  (forall r, In r rs ->
    Cost.ticks (level_c st (pred (head r))) <= level_bound b /\
    forall atom, In (LPos atom) (body r) ->
      Cost.ticks (level_c st (pred atom)) <= level_bound b) ->
  Cost.ticks (classify_c st k rs) <= classification_charge rs b.
Proof.
  intro Hlevel; unfold classify_c.
  eapply N.le_trans; [apply (fold_price _ _ _ (fun r =>
    1 + level_bound b + N.of_nat (length (body r)) * (4 + level_bound b))) |].
  - intros r acc Hr; apply classify_one_cost; apply Hlevel, Hr.
  - clear Hlevel; unfold classification_charge, sum.
    induction rs as [|r rs IH]; cbn [fold_right]; lia.
Qed.

Lemma tag_body_cost {P} pivot position (ls : list (literal P)) :
  Cost.ticks (tag_body_from_c pivot position ls) = N.of_nat (length ls).
Proof.
  revert position; induction ls as [|[atom | atom] rest IH]; intro position;
    cbn [tag_body_from_c length]; autorewrite with galois_cost; [reflexivity | |];
    rewrite IH, Nat2N.inj_succ; lia.
Qed.

Lemma tagged_length {P} pivot position (ls : list (literal P)) :
  length (tagged_body pivot position ls) = length ls.
Proof.
  revert position; induction ls as [|[atom | atom] rest IH]; intro position;
    rewrite tagged_body_equation; cbn [length]; rewrite ?IH; reflexivity.
Qed.

(** A prepared job pays tagging, positive collection and all indexed preparation work. *)
Definition prepare_job_charge {P} b (spec : rule P * nat) :=
  2 * N.of_nat (length (body (fst spec))) +
  N.of_nat (length (positive_atoms (body (tag_rule (fst spec) (snd spec))))) *
    JoinPrepareCost.prepare_unit_cost (args_bound b) (variables_bound b)
      (rows_bound b) (environment_charge b) (tuple_width b) (tuple_encode b) (tuple_width b).

Lemma prepare_job_cost {P} (prog : program P) st lower k acc b spec :
  preparation_data [] (positive_atoms (body (tag_rule (fst spec) (snd spec))))
    (tagged_c prog st k lower acc acc) b ->
  (forall atom, In atom (positive_atoms (body (tag_rule (fst spec) (snd spec)))) ->
    input prog st lower b (fst (pred atom))) ->
  Cost.ticks (prepare_job_c prog (tagged_c prog st k lower acc acc) spec) <=
    prepare_job_charge b spec.
Proof.
  intros Hdata Hinput.
  pose proof (JoinPrepareCost.join_prepare_cost (tag_program prog) _
    (tagged_c prog st k lower acc acc) _ _ _ _ _ _ _
    (preparation_lift _ _ _ b (environment_charge b) Hdata
      (fun atom Ha => tagged_cost prog st lower b k acc acc (pred atom) (Hinput atom Ha))))
    as Hprepare.
  unfold prepare_job_c; repeat rewrite Cost.ticks_bind; rewrite Cost.ticks_ret.
  change (Cost.ticks (tag_rule_c (fst spec) (snd spec)) +
    (Cost.ticks (positive_atoms_c (body (tag_rule (fst spec) (snd spec)))) +
    (Cost.ticks (Join.prepare_c (tag_program prog)
      (positive_atoms (body (tag_rule (fst spec) (snd spec))))
      (tagged_c prog st k lower acc acc)) + 0)) <= prepare_job_charge b spec).
  unfold tag_rule_c; rewrite Cost.ticks_bind, Cost.ticks_ret, tag_body_cost.
  assert (Hlength : length (body (tag_rule (fst spec) (snd spec))) =
    length (body (fst spec))).
  { rewrite tag_rule_equation; cbn [body]; apply tagged_length. }
  rewrite PreparedFire.positive_atoms_cost, Hlength.
  unfold prepare_job_charge; lia.
Qed.

(** This observation names the plan actually prepared for a nonrecursive seed rule. *)
Definition seed_plan {P} (prog : program P) lower r :=
  Join.prepare prog (positive_atoms (body r)) lower.

(** Seed data duties cover preparation, firing and primitive lower-environment callbacks. *)
Definition seed_data {P} (prog : program P) st lower b r :=
  preparation_data [] (positive_atoms (body r)) lower b /\
  firing_data r lower (seed_plan prog lower r) b /\
  forall atom, In atom (positive_atoms (body r)) \/ In (LNeg atom) (body r) ->
    input prog st lower b (pred atom).

(** The seed price retains the complete source preparation and firing pipeline. *)
Definition seed_fire_charge {P} (prog : program P) lower b r :=
  PreparedFire.pipeline_work prog r lower (args_bound b) (variables_bound b) (binding_bound b)
    (rows_bound b) (component_bound b) (lower_bound b)
    (tuple_width b) (tuple_encode b) (tuple_width b).

Lemma seed_fire_cost {P} (prog : program P) st lower b r :
  seed_data prog st lower b r ->
  Cost.ticks (PreparedFire.fire_c prog r lower) <= seed_fire_charge prog lower b r.
Proof.
  intros [Hprepare [Hfire Hinputs]]; apply PreparedFire.fire_cost.
  - apply preparation_lift; [exact Hprepare |].
    intros atom Ha; exact (proj1 (proj2 (Hinputs atom (or_introl Ha)))).
  - apply firing_lift; [exact Hfire |].
    intros atom Ha; exact (proj1 (proj2 (Hinputs atom (or_intror Ha)))).
Qed.

(** Seed collection pays each classified nonrecursive rule and all of its emitted occurrences. *)
Definition seed_collection_charge {P} (prog : program P) st lower k b :=
  sum (collection_charge (fun r => PreparedFire.fire_c prog r lower)
    (seed_fire_charge prog lower b) (tuple_width b))
    (fst (classify st k (rules prog))).

Lemma seed_rules_cost {P} (prog : program P) st lower k b :
  (forall r, In r (fst (classify st k (rules prog))) -> seed_data prog st lower b r) ->
  Cost.ticks (seed_rules_c prog (fst (classify st k (rules prog))) lower) <=
    seed_collection_charge prog st lower k b.
Proof.
  intro Hdata; unfold seed_rules_c, seed_collection_charge; apply collection_cost.
  - intros r Hr; apply (seed_fire_cost prog st lower b r (Hdata r Hr)).
  - intros r row Hr Hrow; apply (proj2 (firing_keys r lower (seed_plan prog lower r) b row
      (proj1 (proj2 (Hdata r Hr))) Hrow)).
Qed.

(** These observations name actual seed storage without defining another evaluator. *)
Definition known {P} (prog : program P) facts st lower k :=
  FinSet.of_list (ground_encoding prog) (seed_atoms prog facts st lower k).

(** The seed predicate index is the actual index passed to every initial job preparation. *)
Definition indexed {P} (prog : program P) facts st lower k :=
  add_atoms prog (FinSet.elements (known prog facts st lower k)) Map.empty.

(** Setup duties concern primitive source callbacks, emitted keys and actual preparation data. *)
Definition initial_data {P} (prog : program P) facts st lower k b :=
  (forall r, In r (rules prog) ->
    Cost.ticks (level_c st (pred (head r))) <= level_bound b /\
    forall atom, In (LPos atom) (body r) ->
      Cost.ticks (level_c st (pred atom)) <= level_bound b) /\
  (forall f, In f facts -> Cost.ticks (level_c st (fst f)) <= level_bound b) /\
  (forall r, In r (fst (classify st k (rules prog))) -> seed_data prog st lower b r) /\
  (forall f, In f (seed_atoms prog facts st lower k) ->
    key_budget (ground_encoding prog) (ground_encode b) (ground_width b) f /\
    key_budget (penc prog) (predicate_encode b) (predicate_width b) (fst f) /\
    key_budget tuple_encoding (tuple_encode b) (tuple_width b) (snd f)) /\
  forall spec, In spec (snd (classify st k (rules prog))) ->
    preparation_data [] (positive_atoms (body (tag_rule (fst spec) (snd spec))))
      (tagged_c prog st k lower (indexed prog facts st lower k)
        (indexed prog facts st lower k)) b /\
    forall atom, In atom (positive_atoms (body (tag_rule (fst spec) (snd spec)))) ->
      input prog st lower b (fst (pred atom)).

(** Setup retains source scans, emitted seed occurrences, seed storage and every prepared job. *)
Definition initial_charge {P} (prog : program P) facts st lower k b :=
  let count := N.of_nat (FinSet.size (known prog facts st lower k)) in
  classification_charge (rules prog) b +
  N.of_nat (length facts) * (2 + level_bound b) +
  seed_collection_charge prog st lower k b + N.of_nat (length facts) +
  N.of_nat (length (seed_atoms prog facts st lower k)) *
    (3 + ground_encode b + ground_width b) +
  (TrieCost.trie_k * (1 + count * ground_width b) + count) +
  count * add_atoms_unit_cost (predicate_encode b) (predicate_width b)
    (tuple_encode b) (tuple_width b) +
  sum (fun spec => 1 + prepare_job_charge b spec) (snd (classify st k (rules prog))).

Lemma seed_storage_cost {P} (prog : program P) facts st lower k b :
  encoding_laws (penc prog) ->
  (forall f, In f (seed_atoms prog facts st lower k) ->
    key_budget (ground_encoding prog) (ground_encode b) (ground_width b) f /\
    key_budget (penc prog) (predicate_encode b) (predicate_width b) (fst f) /\
    key_budget tuple_encoding (tuple_encode b) (tuple_width b) (snd f)) ->
  Cost.ticks (FinSet.of_list_c (ground_encoding prog) (seed_atoms prog facts st lower k)) <=
    N.of_nat (length (seed_atoms prog facts st lower k)) *
      (3 + ground_encode b + ground_width b) /\
  Cost.ticks (FinSet.elements_c (known prog facts st lower k)) <=
    TrieCost.trie_k * (1 +
      N.of_nat (FinSet.size (known prog facts st lower k)) * ground_width b) +
      N.of_nat (FinSet.size (known prog facts st lower k)) /\
  Cost.ticks (add_atoms_c prog (FinSet.elements (known prog facts st lower k)) Map.empty) <=
    N.of_nat (FinSet.size (known prog facts st lower k)) *
      add_atoms_unit_cost (predicate_encode b) (predicate_width b) (tuple_encode b) (tuple_width b).
Proof.
  intros HE Hkeys.
  assert (Hstored : forall f, FinSet.mem (ground_encoding prog) f
    (known prog facts st lower k) = true ->
    key_bits (ground_encoding prog) f <= ground_width b /\
    key_budget (penc prog) (predicate_encode b) (predicate_width b) (fst f) /\
    key_budget tuple_encoding (tuple_encode b) (tuple_width b) (snd f)).
  { intros f Hf; apply (mem_of_list _ (ground_encoding_laws prog HE)) in Hf.
    destruct (Hkeys f Hf) as [[_ Hwidth] Hrest]; auto. }
  split.
  - apply (FinSet.of_list_numeric_cost Map.cost_laws_hold (ground_encoding prog)
      (seed_atoms prog facts st lower k) _ _ (fun f Hf => proj1 (Hkeys f Hf))).
  - split.
    + apply (batch_elements_cost prog (known prog facts st lower k) _
        (FinSet.wf_of_list _ _) (fun f Hf => proj1 (Hstored f Hf))).
    + rewrite FinSet.size_elements; apply add_atoms_cost; intros f Hf.
      apply (FinSet.elements_spec _ (ground_encoding_laws prog HE) _ _
        (FinSet.wf_of_list _ _)) in Hf; exact (proj2 (Hstored f Hf)).
Qed.

Lemma fact_filter_cost {P} (facts : list (ground_atom P)) st k l :
  (forall f, In f facts -> Cost.ticks (level_c st (fst f)) <= l) ->
  Cost.ticks (filter_c (fun f =>
    Cost.step ;; let* lev := level_c st (fst f) in Cost.ret (Nat.eqb lev k)) facts) <=
      N.of_nat (length facts) * (2 + l).
Proof.
  intro Hfacts; rewrite ticks_filter_c; replace (2 + l) with ((1 + l) + 1) by lia.
  apply traversal_bound_on; intros f Hf.
  repeat rewrite Cost.ticks_bind; rewrite Cost.ticks_step, Cost.ticks_ret.
  pose proof (Hfacts f Hf); lia.
Qed.

(** Actual initialization has a complete numerical setup bound from independent primitive duties. *)
Theorem initial_cost {P} (prog : program P) facts st lower k b :
  encoding_laws (penc prog) -> initial_data prog facts st lower k b ->
  Cost.ticks (initial_c prog facts st lower k) <= initial_charge prog facts st lower k b.
Proof.
  intros HE [Hclassification [Hfacts [Hseeds [Hkeys Hjobs]]]].
  pose proof (classify_cost st k (rules prog) b Hclassification) as Hclassify.
  pose proof (seed_rules_cost prog st lower k b Hseeds) as Hseed.
  set (selected := filter (fun f => Nat.eqb (level st (fst f)) k) facts).
  pose proof (fact_filter_cost facts st k (level_bound b) Hfacts) as Hfilter.
  pose proof (nat_N_le _ _ (filter_length_bound
    (fun f => Nat.eqb (level st (fst f)) k) facts)) as Hselected.
  destruct (seed_storage_cost prog facts st lower k b HE Hkeys)
    as [Hbuild [Helements Hstore]].
  assert (Hprepare : Cost.ticks (map_c (prepare_job_c prog
    (tagged_c prog st k lower (indexed prog facts st lower k)
      (indexed prog facts st lower k))) (snd (classify st k (rules prog)))) <=
    sum (fun spec => 1 + prepare_job_charge b spec) (snd (classify st k (rules prog)))).
  { unfold map_c; apply fold_price; intros spec acc Hspec.
    rewrite Cost.ticks_map; apply prepare_job_cost; apply Hjobs, Hspec. }
  unfold initial_c; repeat rewrite Cost.ticks_bind; rewrite Cost.ticks_ret.
  fold (@classify P st k (rules prog)).
  rewrite value_filter_c, value_app_c.
  fold selected.
  rewrite ticks_app_c.
  fold (@seed_atoms P prog facts st lower k).
  fold (@known P prog facts st lower k).
  fold (@FinSet.elements (ground_atom P) (known prog facts st lower k)).
  fold (@indexed P prog facts st lower k).
  fold selected in Hselected.
  eapply N.le_trans.
  - apply N.add_le_mono; [exact Hclassify |].
    apply N.add_le_mono; [exact Hfilter |].
    apply N.add_le_mono; [exact Hseed |].
    apply N.add_le_mono; [exact Hselected |].
    apply N.add_le_mono; [exact Hbuild |].
    apply N.add_le_mono; [exact Helements |].
    apply N.add_le_mono; [exact Hstore |].
    apply N.add_le_mono; [exact Hprepare | exact (N.le_refl 0)].
  - unfold initial_charge; cbn zeta.
    repeat rewrite N.add_assoc; rewrite N.add_0_r; apply N.le_refl.
Qed.

End SemiNaiveInitialCost.
Import SemiNaiveInitialCost.
