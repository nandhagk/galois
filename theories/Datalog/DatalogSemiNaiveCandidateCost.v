(** * Full candidate-generation costs

    Candidate generation charges each cached firing, output traversal and ground-set insertion.
    For example, duplicate heads from different pivots incur costs before set deduplication.
    Builds on: DatalogSemiNaiveBudget and the public Join and FinSet numerical contracts. *)

From Stdlib Require Import List Bool PeanoNat NArith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet BaseTrieCost.
From Galois.Lattice Require Import LatticeSet.
From Galois.Datalog Require Import DatalogSyntax DatalogStratify DatalogRelation DatalogCost
  DatalogJoin DatalogJoinFireCost DatalogJoinPrepareCost DatalogSemiNaive
  DatalogSemiNaiveIndex DatalogSemiNaiveBudget DatalogSemiNaiveCost DatalogSemiNaiveTrace.
Import List.ListNotations Cost.Notations SemiNaive SemiNaiveIndex SemiNaiveBudget
  SemiNaiveCost SemiNaiveTrace.
Local Open Scope N_scope.

Module SemiNaiveCandidateCost.

(** Collection rows retain all per-item output occurrences before ground-set construction. *)
Definition collection_rows {A P} (fire : A -> Cost.t relation) (target : A -> P) xs :=
  flat_map (fun x => map (fun row => (target x, row))
    (FinSet.elements (set_raw (Cost.value (fire x))))) xs.

Lemma collection_equation {A P} (fire : A -> Cost.t relation) (target : A -> P) xs :
  Cost.value (fold_right_c (fun x acc =>
    let* rel := fire x in
    let* rows := FinSet.elements_c (set_raw rel) in
    let* here := map_c (fun row => Cost.ret (target x, row)) rows in
    app_c here acc) [] xs) = collection_rows fire target xs.
Proof.
  rewrite value_fold_right_c; induction xs as [|x xs IH]; [reflexivity |].
  cbn [fold_right collection_rows flat_map]; repeat rewrite Cost.value_bind.
  rewrite value_map_c, value_app_c, IH; reflexivity.
Qed.

(** This price retains enumeration, pair construction, append and the fold visit. *)
Definition collection_charge {A} (fire : A -> Cost.t relation) price wt x :=
  let count := N.of_nat (FinSet.size (set_raw (Cost.value (fire x)))) in
  price x + TrieCost.trie_k * (1 + count * wt) + 3 * count + 1.

Lemma collection_cost {A P} (fire : A -> Cost.t relation) (target : A -> P) xs price wt :
  (forall x, In x xs -> Cost.ticks (fire x) <= price x) ->
  (forall x row, In x xs -> member row (Cost.value (fire x)) = true ->
    key_bits tuple_encoding row <= wt) ->
  Cost.ticks (fold_right_c (fun x acc =>
    let* rel := fire x in
    let* rows := FinSet.elements_c (set_raw rel) in
    let* here := map_c (fun row => Cost.ret (target x, row)) rows in
    app_c here acc) [] xs) <= sum (collection_charge fire price wt) xs.
Proof.
  induction xs as [|x xs IH]; intros Hfire Hwidth; [change (0 <= 0); lia |].
  rewrite ticks_fold_right_c_cons.
  specialize (IH (fun y Hy => Hfire y (or_intror Hy))
    (fun y row Hy => Hwidth y row (or_intror Hy))).
  pose proof (Hfire x (or_introl eq_refl)) as Hx.
  pose proof (JoinPrepareCost.relation_elements_cost (Cost.value (fire x)) wt
    (fun row => Hwidth x row (or_introl eq_refl))) as Helements.
  repeat rewrite Cost.ticks_bind; rewrite ticks_app_c, value_map_c, length_map.
  fold (@FinSet.elements tuple (set_raw (Cost.value (fire x)))).
  assert (Hmap : Cost.ticks (map_c (fun row => Cost.ret (target x, row))
    (FinSet.elements (set_raw (Cost.value (fire x))))) =
      N.of_nat (FinSet.size (set_raw (Cost.value (fire x))))).
  { rewrite ticks_map_c, FinSet.size_elements.
    induction (FinSet.elements (set_raw (Cost.value (fire x)))) as [|row rest IHrest];
      cbn [fold_right length]; [reflexivity |].
    rewrite Cost.ticks_ret, Nat2N.inj_succ; lia. }
  rewrite Hmap, <- FinSet.size_elements.
  unfold sum at 1; cbn [fold_right]; fold (sum (collection_charge fire price wt) xs).
  unfold collection_charge at 1; cbn zeta; lia.
Qed.

Lemma collection_length {A P} (fire : A -> Cost.t relation) (target : A -> P) xs :
  N.of_nat (length (collection_rows fire target xs)) =
    sum (fun x => N.of_nat (FinSet.size (set_raw (Cost.value (fire x))))) xs.
Proof.
  induction xs as [|x xs IH]; [reflexivity |].
  cbn [collection_rows flat_map]; rewrite length_app, length_map, Nat2N.inj_add.
  rewrite <- FinSet.size_elements.
  fold (@collection_rows A P fire target xs); rewrite IH; reflexivity.
Qed.

(** Job data duties concern actual probes, bindings, primitive inputs and emitted ground keys. *)
Definition candidate_data {P} (prog : program P) st lower k s b : Prop :=
  forall j, In j (jobs s) ->
    firing_data (tagged_rule j)
      (tagged_c prog st k lower (accumulated_index s) (frontier_index s)) (plan j) b /\
    (forall atom, In (LNeg atom) (body (tagged_rule j)) ->
      input prog st lower b (fst (pred atom))) /\
    forall row, member row (Join.fire (tagged_rule j)
      (tagged_c prog st k lower (accumulated_index s) (frontier_index s)) (plan j)) = true ->
      key_budget (ground_encoding prog) (ground_encode b) (ground_width b)
        (pred (head (source_rule j)), row).

(** This observation names the firing called by the source candidate loop. *)
Definition job_fire {P} (prog : program P) st lower k s j :=
  Join.fire_c (tagged_rule j)
    (tagged_c prog st k lower (accumulated_index s) (frontier_index s)) (plan j).

(** A job's price retains actual Join work and the full literal and primitive coefficient. *)
Definition firing_charge {P} b (j : job P) :=
  (Join.work (plan j) + 1) * JoinFireCost.fire_unit_cost
    (length (body (tagged_rule j))) (args_bound b) (binding_bound b)
    (component_bound b) (environment_charge b) (tuple_encode b) (tuple_width b).

(** The candidate domain retains actual firing work and all output-construction occurrences. *)
Definition candidates_charge {P} (prog : program P) st lower k s b :=
  sum (collection_charge (job_fire prog st lower k s) (firing_charge b) (tuple_width b))
    (jobs s) +
  sum (fun j => N.of_nat (FinSet.size (set_raw (Cost.value
    (job_fire prog st lower k s j))))) (jobs s) *
    (3 + ground_encode b + ground_width b).

(** Actual candidate generation has a complete primitive numerical bound for arbitrary states. *)
Theorem candidates_cost {P} (prog : program P) st lower k s b :
  candidate_data prog st lower k s b ->
  Cost.ticks (candidates_c prog st lower k s) <= candidates_charge prog st lower k s b.
Proof.
  intro Hdata.
  set (fire := job_fire prog st lower k s).
  set (target := fun j : job P => pred (head (source_rule j))).
  assert (Hfire : forall j, In j (jobs s) -> Cost.ticks (fire j) <= firing_charge b j).
  { intros j Hj; destruct (Hdata j Hj) as [Hf [Hi _]].
    exact (JoinFireCost.join_fire_cost (tagged_rule j)
      (tagged_c prog st k lower (accumulated_index s) (frontier_index s)) (plan j)
      (args_bound b) (binding_bound b) (component_bound b) (environment_charge b)
      (tuple_encode b) (tuple_width b)
      (firing_lift (tagged_rule j) _ (plan j) b (environment_charge b) Hf
        (fun atom Ha => tagged_cost prog st lower b k _ _ (pred atom) (Hi atom Ha)))). }
  assert (Hwidth : forall j row, In j (jobs s) ->
    member row (Cost.value (fire j)) = true -> key_bits tuple_encoding row <= tuple_width b).
  { intros j row Hj Hrow.
    exact (proj2 (firing_keys _ _ _ b row (proj1 (Hdata j Hj)) Hrow)). }
  pose proof (collection_cost fire target (jobs s) _ _ Hfire Hwidth) as Hcollect.
  assert (Hkeys : forall f, In f (collection_rows fire target (jobs s)) ->
    key_budget (ground_encoding prog) (ground_encode b) (ground_width b) f).
  { intros f Hf; apply in_flat_map in Hf as [j [Hj Hf]].
    apply in_map_iff in Hf as [row [<- Hrow]].
    apply (proj2 (proj2 (Hdata j Hj))).
    apply (FinSet.elements_spec tuple_encoding tuple_encoding_laws);
      [exact (proj2_sig (Cost.value (fire j))) | exact Hrow]. }
  pose proof (FinSet.of_list_numeric_cost Map.cost_laws_hold (ground_encoding prog)
    (collection_rows fire target (jobs s)) _ _ Hkeys) as Hbuild.
  unfold candidates_c; rewrite Cost.ticks_bind.
  fold fire; fold target.
  rewrite (collection_equation fire target).
  rewrite collection_length in Hbuild; unfold candidates_charge; fold fire.
  apply N.add_le_mono; [exact Hcollect | exact Hbuild].
Qed.

(** Ground-key width of actual candidates follows from primitive emitted-key duties. *)
Theorem candidates_width {P} (prog : program P) st lower k s b :
  encoding_laws (penc prog) -> candidate_data prog st lower k s b ->
  forall f, FinSet.mem (ground_encoding prog) f (candidates prog st lower k s) = true ->
    key_bits (ground_encoding prog) f <= ground_width b.
Proof.
  intros HE Hdata f Hf; rewrite candidates_equation in Hf.
  apply (mem_of_list (ground_encoding prog) (ground_encoding_laws prog HE)) in Hf.
  apply in_flat_map in Hf as [j [Hj Hrow]].
  apply in_map_iff in Hrow as [row [<- Hrow]].
  apply (FinSet.elements_spec tuple_encoding tuple_encoding_laws _ _
    (proj2_sig (Cost.value (job_fire prog st lower k s j)))) in Hrow.
  exact (proj2 (proj2 (proj2 (Hdata j Hj)) row Hrow)).
Qed.

Lemma construction_size {A} (E : encoding A) (HE : encoding_laws E) xs :
  (FinSet.size (FinSet.of_list E xs) <= length xs)%nat.
Proof.
  rewrite FinSet.size_elements; apply NoDup_incl_length.
  - apply (FinSet.elements_nodup E), FinSet.wf_of_list.
  - intros x Hx; apply (FinSet.elements_spec E HE _ _ (FinSet.wf_of_list E xs)) in Hx.
    apply (mem_of_list E HE), Hx.
Qed.

(** Candidate cardinality is bounded by actual Join work before any ground-set deduplication. *)
Theorem candidates_work_bound {P} (prog : program P) st lower k s :
  encoding_laws (penc prog) ->
  N.of_nat (FinSet.size (candidates prog st lower k s)) <=
    sum (fun j => Join.work (plan j) + 1) (jobs s).
Proof.
  intro HE.
  assert (Hsize : (FinSet.size (candidates prog st lower k s) <=
    length (collection_rows (job_fire prog st lower k s)
      (fun j => pred (head (source_rule j))) (jobs s)))%nat).
  { rewrite candidates_equation; apply construction_size, (ground_encoding_laws prog HE). }
  apply nat_N_le in Hsize; rewrite collection_length in Hsize.
  eapply N.le_trans; [exact Hsize |].
  apply sum_bound; intros j Hj; apply firing_size.
Qed.

End SemiNaiveCandidateCost.
Import SemiNaiveCandidateCost.
