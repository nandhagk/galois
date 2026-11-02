(** * Concrete input budgets for phi production

    Bounds follow the actual rows and changing maps, with callback work charged at its input.
    For example, resolution of a later node uses the representative table returned by the first.
    Builds on: AnalysesAuditMemoryPhiInputBudget and the component source adequacy leaves. *)

From Stdlib Require Import List Bool PArith PeanoNat Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditMap CollectionsAuditMapAdequacy CollectionsAuditFinSet
  CollectionsAuditFinSetAdequacy CollectionsAuditPrimitive CollectionsAuditPrimitiveAdequacy
  CollectionsAuditEncoding CollectionsAuditEncoderBudget CollectionsAuditEncoderBudgetAdequacy.
From Galois.Graph Require Import GraphCore GraphPrepare GraphScc GraphAuditBase
  GraphAuditBaseAdequacy GraphAuditDfs GraphAuditDfsAdequacy GraphAuditScc GraphAuditSccAdequacy.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryFrontier
  AnalysesAuditMemoryEncoding
  AnalysesAuditMemoryInputBudget AnalysesAuditMemoryInputBudgetAdequacy
  AnalysesAuditMemoryDistinctAdequacy AnalysesAuditMemoryIndex AnalysesAuditMemoryIndexAdequacy
  AnalysesAuditMemorySharedBudget AnalysesAuditMemorySharedBudgetAdequacy
  AnalysesAuditMemoryPhiState AnalysesAuditMemoryPhiRows AnalysesAuditMemoryPhiRowsAdequacy
  AnalysesAuditMemoryPhiResolve
  AnalysesAuditMemoryPhiResolveAdequacy AnalysesAuditMemoryPhiProducer
  AnalysesAuditMemoryPhiProducerAdequacy AnalysesAuditMemoryPhiInputBudget.
Import List.ListNotations.

(** * Concrete primitive calls *)

Lemma audit_phi_get_input_bound K V CE (enc : K -> positive * list CE) work budget key
    (input : Map.t K V) :
  (forall k, work (snd (enc k)) <= budget k) ->
  audit_map_source_work work (snd (audit_map_get enc key input)) <=
    audit_phi_get_input_budget enc budget key.
Proof.
  intro Hbudget.
  pose proof (audit_map_get_source_work_bound K V CE enc work key input) as Hget.
  specialize (Hbudget key).
  unfold audit_phi_get_input_budget; lia.
Qed.

Lemma audit_phi_set_input_bound K V CE (enc : K -> positive * list CE) work budget key value
    (input : Map.t K V) :
  (forall k, work (snd (enc k)) <= budget k) ->
  audit_map_source_work work (snd (audit_map_set enc key value input)) <=
    audit_phi_set_input_budget enc budget key.
Proof.
  intro Hbudget.
  pose proof (audit_map_set_source_work_bound K V CE enc work key value input) as Hset.
  specialize (Hbudget key).
  unfold audit_phi_set_input_budget; lia.
Qed.

Lemma audit_phi_mem_input_bound K CE (enc : K -> positive * list CE) work budget key input :
  (forall k, work (snd (enc k)) <= budget k) ->
  audit_finset_source_work work (snd (audit_finset_mem enc key input)) <=
    6 + budget key + 5 * Pos.size_nat (fst (enc key)).
Proof.
  intro Hbudget.
  pose proof (audit_memory_distinct_mem_bound K CE enc work key input) as Hmem.
  specialize (Hbudget key); lia.
Qed.

Lemma audit_phi_add_input_bound K CE (enc : K -> positive * list CE) work budget key input :
  (forall k, work (snd (enc k)) <= budget k) ->
  audit_finset_source_work work (snd (audit_finset_add enc key input)) <=
    audit_phi_set_input_budget enc budget key.
Proof.
  intro Hbudget.
  pose proof (audit_memory_distinct_add_bound K CE enc work key input) as Hadd.
  specialize (Hbudget key).
  unfold audit_phi_set_input_budget; lia.
Qed.

Lemma audit_phi_distinct_input_bound K CE (enc : K -> positive * list CE) work budget keys :
  (forall k, work (snd (enc k)) <= budget k) ->
  forall seen, audit_phi_distinct_work work (snd (audit_phi_distinct_from enc seen keys)) <=
    audit_memory_distinct_input_budget enc budget keys.
Proof.
  intro Hbudget.
  induction keys as [|key rest IH]; intro seen.
  - reflexivity.
  - cbn [audit_phi_distinct_from audit_memory_distinct_input_budget].
    pose proof (audit_phi_mem_input_bound K CE enc work budget key seen Hbudget) as Hmem.
    destruct (audit_finset_mem enc key seen) as [found probes].
    cbn [snd] in Hmem.
    destruct found.
    + specialize (IH seen).
      destruct (audit_phi_distinct_from enc seen rest) as [output events].
      cbn [snd app audit_phi_distinct_work] in IH |- *; lia.
    + pose proof (audit_phi_add_input_bound K CE enc work budget key seen Hbudget) as Hadd.
      destruct (audit_finset_add enc key seen) as [next adds].
      specialize (IH next).
      destruct (audit_phi_distinct_from enc next rest) as [output events].
      cbn [snd app audit_phi_distinct_work] in Hadd, IH |- *.
      unfold audit_phi_set_input_budget in Hadd; lia.
Qed.

(** * Input row construction *)

Lemma audit_phi_rows_primitive_work_app N E CN CE PE OE node_work edge_work pred_work operand_work
    (left right : list (audit_phi_row_event N E CN CE PE OE)) :
  audit_phi_rows_primitive_work node_work edge_work pred_work operand_work (left ++ right) =
    audit_phi_rows_primitive_work node_work edge_work pred_work operand_work left +
      audit_phi_rows_primitive_work node_work edge_work pred_work operand_work right.
Proof.
  induction left as [|event rest IH].
  - reflexivity.
  - destruct event; cbn [app audit_phi_rows_primitive_work]; rewrite IH; lia.
Qed.

Lemma audit_phi_operand_input_bound N E CN CE PE OE
    (operand : N -> option E -> option (memory_version N E) * list OE)
    node_work edge_work pred_work operand_work operand_budget n keys :
  (forall n key, operand_work (snd (operand n key)) <= operand_budget n key) ->
  let events := snd (@audit_phi_row_operands N E CN CE PE OE operand n keys) in
  2 * length events + audit_phi_rows_primitive_work node_work edge_work pred_work operand_work
    events <= audit_phi_operand_input_budget operand_budget n keys.
Proof.
  intro Hbudget.
  induction keys as [|key rest IH].
  - reflexivity.
  - cbn [audit_phi_row_operands audit_phi_operand_input_budget].
    specialize (Hbudget n key) as Hhead.
    destruct (operand n key) as [result calls].
    destruct (@audit_phi_row_operands N E CN CE PE OE operand n rest) as [tail events].
    cbn [snd length audit_phi_rows_primitive_work] in Hhead, IH |- *; lia.
Qed.

Lemma audit_phi_input_row_input_bound N E CN CE PE OE (edge_enc : E -> positive * list CE)
    (pred : N -> list E * list PE)
    (operand : N -> option E -> option (memory_version N E) * list OE)
    node_work edge_work pred_work operand_work edge_budget pred_budget operand_budget n :
  (forall e, edge_work (snd (edge_enc e)) <= edge_budget e) ->
  (forall n, pred_work (snd (pred n)) <= pred_budget n) ->
  (forall n key, operand_work (snd (operand n key)) <= operand_budget n key) ->
  let edges := fst (pred n) in
  let keys := None :: map Some edges in
  let distinct := fst (audit_phi_distinct_from (audit_option_encode edge_enc) FinSet.empty keys) in
  let events := snd (@audit_phi_input_row N E CN CE PE OE edge_enc pred operand n) in
  2 * length events + audit_phi_rows_primitive_work node_work edge_work pred_work operand_work
    events <=
    2 + length edges + pred_budget n +
    2 + audit_memory_distinct_input_budget (audit_option_encode edge_enc)
      (audit_option_input_budget edge_budget) keys +
    audit_phi_operand_input_budget operand_budget n distinct.
Proof.
  intros Hedge Hpred Hoperand.
  destruct audit_sum_option_input_bound as [Hoption _].
  unfold audit_phi_input_row.
  specialize (Hpred n).
  destruct (pred n) as [edges pred_events].
  pose proof (audit_phi_distinct_input_bound (option E) _ (audit_option_encode edge_enc)
    (audit_option_events_work edge_work) (audit_option_input_budget edge_budget)
    (None :: map Some edges) (fun key => Hoption E CE edge_enc edge_work edge_budget key Hedge)
    FinSet.empty) as Hdistinct.
  destruct (audit_phi_distinct_from (audit_option_encode edge_enc) FinSet.empty
    (None :: map Some edges)) as [distinct distinct_events] eqn:Hdistinct_call.
  pose proof (audit_phi_operand_input_bound N E CN CE PE OE operand node_work edge_work pred_work
    operand_work operand_budget n distinct Hoperand) as Hoperands.
  destruct (@audit_phi_row_operands N E CN CE PE OE operand n distinct) as [row operand_events].
  cbn [fst snd app length audit_phi_rows_primitive_work] in Hpred, Hdistinct, Hoperands |- *.
  rewrite Hdistinct_call; cbn [fst].
  lia.
Qed.

Lemma audit_phi_rows_input_bound N E CN CE PE OE (node_enc : N -> positive * list CN)
    (edge_enc : E -> positive * list CE) (pred : N -> list E * list PE)
    (operand : N -> option E -> option (memory_version N E) * list OE)
    node_work edge_work pred_work operand_work node_budget edge_budget pred_budget operand_budget
    nodes :
  (forall n, node_work (snd (node_enc n)) <= node_budget n) ->
  (forall e, edge_work (snd (edge_enc e)) <= edge_budget e) ->
  (forall n, pred_work (snd (pred n)) <= pred_budget n) ->
  (forall n key, operand_work (snd (operand n key)) <= operand_budget n key) ->
  audit_phi_rows_source_work node_work edge_work pred_work operand_work
    (snd (audit_phi_input_rows node_enc edge_enc pred operand nodes)) <=
    audit_phi_rows_input_budget node_enc edge_enc pred node_budget edge_budget pred_budget
      operand_budget nodes.
Proof.
  intros Hnode Hedge Hpred Hoperand.
  induction nodes as [|n rest IH].
  - reflexivity.
  - cbn [audit_phi_input_rows audit_phi_rows_input_budget].
    pose proof (audit_phi_input_row_input_bound N E CN CE PE OE edge_enc pred operand node_work
      edge_work pred_work operand_work edge_budget pred_budget operand_budget n Hedge Hpred
      Hoperand) as Hrow.
    destruct (audit_phi_input_rows node_enc edge_enc pred operand rest) as [tail tail_events].
    destruct (@audit_phi_input_row N E CN CE PE OE edge_enc pred operand n) as [row row_events].
    pose proof (audit_phi_set_input_bound N _ CN node_enc node_work node_budget n row tail Hnode)
      as Hset.
    destruct (audit_map_set node_enc n row tail) as [output stores].
    unfold audit_phi_rows_source_work in IH |- *.
    cbn [snd] in IH, Hrow, Hset |- *.
    rewrite !length_app, !audit_phi_rows_primitive_work_app.
    cbn [length audit_phi_rows_primitive_work]; lia.
Qed.

(** * Dependency rows *)

Lemma audit_phi_dependency_entries_input_bound N E CN node_work n row :
  audit_phi_dependency_row_work node_work
    (snd (@audit_phi_dependency_row_entries N E CN n row)) <= 2 + 4 * length row.
Proof.
  induction row as [|[key v] rest IH].
  - reflexivity.
  - cbn [audit_phi_dependency_row_entries].
    destruct (@audit_phi_dependency_row_entries N E CN n rest) as [tail events].
    cbn [snd] in IH.
    destruct v; cbn [snd app audit_phi_dependency_row_work length]; lia.
Qed.

Lemma audit_phi_dependency_row_input_bound N E CN (node_enc : N -> positive * list CN)
    node_work node_budget inputs n :
  (forall node, node_work (snd (node_enc node)) <= node_budget node) ->
  audit_phi_dependency_row_work node_work (snd (@audit_phi_dependency_row N E CN node_enc inputs
    n)) <= audit_phi_dependency_row_input_budget node_enc node_budget inputs n.
Proof.
  intro Hnode.
  unfold audit_phi_dependency_row, audit_phi_dependency_row_input_budget.
  pose proof (audit_phi_get_input_bound N _ CN node_enc node_work node_budget n inputs Hnode)
    as Hget.
  destruct (audit_map_get node_enc n inputs) as [found calls].
  pose proof (audit_phi_dependency_entries_input_bound N E CN node_work n
    (match found with
    | Some row =>
      row
    | None =>
      []
    end)) as Hentries.
  destruct (@audit_phi_dependency_row_entries N E CN n
    (match found with
    | Some row =>
      row
    | None =>
      []
    end)) as [edges events].
  cbn [fst snd audit_phi_dependency_row_work] in Hget, Hentries |- *; lia.
Qed.

Lemma audit_phi_dependency_rows_input_bound N E CN (node_enc : N -> positive * list CN)
    node_work node_budget mg inputs :
  (forall node, node_work (snd (node_enc node)) <= node_budget node) ->
  audit_phi_dependency_rows_work node_work
    (snd (@audit_phi_dependency_rows_counted N E CN node_enc mg inputs)) <=
    audit_memory_index_input_budget node_enc node_budget
      (audit_phi_dependency_row_input_budget node_enc node_budget inputs) (memory_phis mg).
Proof.
  intro Hnode.
  eapply Nat.le_trans.
  - apply audit_memory_result_index_work_bound.
  - apply audit_memory_index_budget_input; [exact Hnode|].
    intro n; apply audit_phi_dependency_row_input_bound; exact Hnode.
Qed.

(** * Cycle scans and persistent marking *)

Lemma audit_phi_cycle_work_app N E CN node_work
    (left right : list (audit_phi_cycle_event N E CN)) :
  audit_phi_cycle_source_work node_work (left ++ right) =
    audit_phi_cycle_source_work node_work left + audit_phi_cycle_source_work node_work right.
Proof.
  induction left as [|event rest IH].
  - reflexivity.
  - destruct event; cbn [app audit_phi_cycle_source_work]; rewrite IH; lia.
Qed.

Lemma audit_phi_self_edges_input_bound N E CN (node_enc : N -> positive * list CN)
    node_work node_budget (dep : Graph.t N (phi_dependency_edge N E)) n edges :
  (forall node, node_work (snd (node_enc node)) <= node_budget node) ->
  audit_phi_cycle_source_work node_work (snd (audit_phi_cycle_self_edges node_enc dep n edges)) <=
    audit_phi_self_edges_input_budget node_enc node_budget dep n edges.
Proof.
  intro Hnode.
  induction edges as [|edge rest IH].
  - reflexivity.
  - cbn [audit_phi_cycle_self_edges audit_phi_self_edges_input_budget].
    specialize (Hnode (Graph.target dep edge)) as Htarget; specialize (Hnode n) as Hself.
    destruct (node_enc (Graph.target dep edge)) as [target_code target_body].
    destruct (node_enc n) as [node_code node_body].
    pose proof (audit_positive_eqb_source_bound target_code node_code) as Hcompare.
    destruct (audit_positive_eqb target_code node_code) as [same comparisons].
    destruct (audit_phi_cycle_self_edges node_enc dep n rest) as [later events].
    cbn [fst snd app audit_phi_cycle_source_work] in Htarget, Hself, Hcompare, IH |- *.
    lia.
Qed.

Lemma audit_phi_component_input_bound N E CN (EN : encoding N)
    (node_enc : N -> positive * list CN) node_work node_budget
    (dep : Graph.t N (phi_dependency_edge N E)) (p : prepared EN dep) component :
  (forall node, node_work (snd (node_enc node)) <= node_budget node) ->
  audit_phi_cycle_source_work node_work
    (snd (audit_phi_component_cyclic_counted EN node_enc dep p component)) <=
    audit_phi_component_input_budget EN node_enc node_budget dep p component.
Proof.
  intro Hnode.
  destruct component as [|n [|next rest]]; try reflexivity.
  unfold audit_phi_component_cyclic_counted, audit_phi_component_input_budget.
  pose proof (audit_phi_get_input_bound N _ CN node_enc node_work node_budget n (out_index p)
    Hnode) as Hget.
  destruct (audit_map_get node_enc n (out_index p)) as [found calls].
  pose proof (audit_phi_self_edges_input_bound N E CN node_enc node_work node_budget dep n
    (match found with
    | Some edges =>
      edges
    | None =>
      []
    end) Hnode) as Hedges.
  destruct (audit_phi_cycle_self_edges node_enc dep n
    (match found with
    | Some edges =>
      edges
    | None =>
      []
    end)) as [cyclic events].
  cbn [fst snd app audit_phi_cycle_source_work] in Hget, Hedges |- *; lia.
Qed.

Lemma audit_phi_mark_input_bound N E CN (node_enc : N -> positive * list CN)
    node_work node_budget nodes :
  (forall node, node_work (snd (node_enc node)) <= node_budget node) ->
  forall marked, audit_phi_cycle_source_work node_work
    (snd (@audit_phi_cycle_mark_nodes N E CN node_enc nodes marked)) <=
    audit_phi_mark_input_budget node_enc node_budget nodes.
Proof.
  intro Hnode.
  induction nodes as [|n rest IH]; intro marked.
  - reflexivity.
  - cbn [audit_phi_cycle_mark_nodes audit_phi_mark_input_budget].
    pose proof (audit_phi_add_input_bound N CN node_enc node_work node_budget n marked Hnode)
      as Hadd.
    destruct (audit_finset_add node_enc n marked) as [next calls].
    specialize (IH next).
    destruct (@audit_phi_cycle_mark_nodes N E CN node_enc rest next).
    cbn [snd audit_phi_cycle_source_work] in Hadd, IH |- *; lia.
Qed.

Lemma audit_phi_cycles_from_input_bound N E CN (EN : encoding N)
    (node_enc : N -> positive * list CN) node_work node_budget
    (dep : Graph.t N (phi_dependency_edge N E)) (p : prepared EN dep) components :
  (forall node, node_work (snd (node_enc node)) <= node_budget node) ->
  forall marked, audit_phi_cycle_source_work node_work
    (snd (audit_phi_cycle_flags_from EN node_enc dep p components marked)) <=
    audit_phi_cycles_input_budget EN node_enc node_budget dep p components.
Proof.
  intro Hnode.
  induction components as [|component rest IH]; intro marked.
  - reflexivity.
  - cbn [audit_phi_cycle_flags_from audit_phi_cycles_input_budget].
    pose proof (audit_phi_component_input_bound N E CN EN node_enc node_work node_budget dep p
      component Hnode) as Hcomponent.
    destruct (audit_phi_component_cyclic_counted EN node_enc dep p component) as [cyclic events].
    cbn [fst snd] in Hcomponent |- *.
    destruct cyclic.
    + pose proof (audit_phi_mark_input_bound N E CN node_enc node_work node_budget component
        Hnode marked) as Hmark.
      destruct (@audit_phi_cycle_mark_nodes N E CN node_enc component marked) as [next marks].
      specialize (IH next).
      destruct (audit_phi_cycle_flags_from EN node_enc dep p rest next).
      cbn [snd] in Hmark, IH |- *.
      rewrite !audit_phi_cycle_work_app; lia.
    + specialize (IH marked).
      destruct (audit_phi_cycle_flags_from EN node_enc dep p rest marked).
      cbn [snd app] in IH |- *.
      rewrite audit_phi_cycle_work_app; lia.
Qed.

(** * Resolution at actual intermediate maps *)

Lemma audit_phi_rep_input_bound N E CN CV (version_enc : memory_version N E -> positive * list CV)
    version_work version_budget reps v :
  (forall input, version_work (snd (version_enc input)) <= version_budget input) ->
  audit_phi_resolve_source_work (fun _ : list CN => 0) version_work
    (snd (@audit_phi_rep N E CN CV version_enc reps v)) <=
    audit_phi_rep_input_budget version_enc version_budget v.
Proof.
  intro Hversion.
  unfold audit_phi_rep, audit_phi_rep_input_budget.
  pose proof (audit_phi_get_input_bound _ _ CV version_enc version_work version_budget v reps
    Hversion) as Hget.
  destruct (audit_map_get version_enc v reps).
  unfold audit_phi_resolve_source_work.
  cbn [snd length audit_phi_resolve_primitive_work] in Hget |- *; lia.
Qed.

Lemma audit_phi_rep_node_work_irrelevant N E CN CV node_work version_work
    (version_enc : memory_version N E -> positive * list CV) reps v :
  audit_phi_resolve_source_work node_work version_work
    (snd (@audit_phi_rep N E CN CV version_enc reps v)) =
  audit_phi_resolve_source_work (fun _ : list CN => 0) version_work
    (snd (@audit_phi_rep N E CN CV version_enc reps v)).
Proof.
  unfold audit_phi_rep; destruct (audit_map_get version_enc v reps); reflexivity.
Qed.

Lemma audit_phi_compare_input_bound N E CN CV node_work version_work
    (version_enc : memory_version N E -> positive * list CV) version_budget left right :
  (forall v, version_work (snd (version_enc v)) <= version_budget v) ->
  audit_phi_resolve_source_work node_work version_work
    (snd (@audit_phi_compare N E CN CV version_enc left right)) <=
    audit_phi_compare_input_budget version_enc version_budget left right.
Proof.
  intro Hversion.
  unfold audit_phi_compare, audit_phi_compare_input_budget.
  specialize (Hversion left) as Hleft; specialize (Hversion right) as Hright.
  destruct (version_enc left) as [left_code left_body].
  destruct (version_enc right) as [right_code right_body].
  pose proof (audit_positive_eqb_source_bound left_code right_code) as Hcompare.
  destruct (audit_positive_eqb left_code right_code).
  unfold audit_phi_resolve_source_work.
  cbn [fst snd length audit_phi_resolve_primitive_work] in Hleft, Hright, Hcompare |- *; lia.
Qed.

Lemma audit_phi_forall_source_work N E CN CV node_work version_work row
    (events : list (audit_phi_resolve_event N E CN CV)) :
  audit_phi_resolve_source_work node_work version_work (AuditPhiForall row :: events) =
    2 + audit_phi_resolve_source_work node_work version_work events.
Proof.
  unfold audit_phi_resolve_source_work.
  cbn [length audit_phi_resolve_primitive_work]; lia.
Qed.

Lemma audit_phi_all_same_input_bound N E CN CV node_work version_work
    (version_enc : memory_version N E -> positive * list CV) version_budget reps candidate row :
  (forall v, version_work (snd (version_enc v)) <= version_budget v) ->
  audit_phi_resolve_source_work node_work version_work
    (snd (@audit_phi_all_same N E CN CV version_enc reps candidate row)) <=
    audit_phi_all_same_input_budget version_enc version_budget reps candidate row.
Proof.
  intro Hversion.
  induction row as [|[key v] rest IH].
  - reflexivity.
  - cbn [audit_phi_all_same audit_phi_all_same_input_budget].
    pose proof (audit_phi_rep_input_bound N E CN CV version_enc version_work version_budget reps v
      Hversion) as Hrep.
    rewrite <- (audit_phi_rep_node_work_irrelevant N E CN CV node_work version_work version_enc
      reps v) in Hrep.
    destruct (@audit_phi_rep N E CN CV version_enc reps v) as [representative re] eqn:Hrep_call.
    pose proof (audit_phi_compare_input_bound N E CN CV node_work version_work version_enc
      version_budget candidate representative Hversion) as Hcompare.
    destruct (@audit_phi_compare N E CN CV version_enc candidate representative) as [same ce].
    destruct (@audit_phi_all_same N E CN CV version_enc reps candidate rest) as [later tail].
    cbn [snd] in Hrep, Hcompare, IH |- *.
    rewrite audit_phi_forall_source_work, !audit_phi_resolve_source_work_app.
    assert (Hrep_value : fst (@audit_phi_rep N E unit CV version_enc reps v) = representative).
    { unfold audit_phi_rep in Hrep_call |- *.
      destruct (audit_map_get version_enc v reps); inversion Hrep_call; reflexivity. }
    rewrite Hrep_value; lia.
Qed.

Lemma audit_phi_resolve_step_input_bound N E CN CV (EN : encoding N)
    (node_enc : N -> positive * list CN)
    (version_enc : memory_version N E -> positive * list CV)
    node_work version_work node_budget version_budget index reps n :
  (forall node, node_work (snd (node_enc node)) <= node_budget node) ->
  (forall v, version_work (snd (version_enc v)) <= version_budget v) ->
  audit_phi_resolve_source_work node_work version_work
    (snd (audit_phi_resolve_step EN node_enc version_enc index reps n)) <=
    audit_phi_resolve_step_input_budget EN node_enc version_enc node_budget version_budget
      index reps n.
Proof.
  intros Hnode Hversion.
  unfold audit_phi_resolve_step, audit_phi_resolve_step_input_budget.
  pose proof (audit_phi_mem_input_bound N CN node_enc node_work node_budget n
    (phi_index_cycles index) Hnode) as Hcycle.
  destruct (audit_finset_mem node_enc n (phi_index_cycles index)) as [cyclic ce].
  cbn [fst snd] in Hcycle |- *.
  destruct cyclic.
  - unfold audit_phi_resolve_source_work.
    cbn [snd length audit_phi_resolve_primitive_work]; lia.
  - pose proof (audit_phi_get_input_bound N _ CN node_enc node_work node_budget n
      (phi_index_inputs index) Hnode) as Hrow.
    destruct (audit_map_get node_enc n (phi_index_inputs index)) as [row ie].
    cbn [fst snd] in Hrow |- *.
    destruct row as [[|[key v] rest]|]; try (unfold audit_phi_resolve_source_work;
      cbn [snd length audit_phi_resolve_primitive_work]; lia).
    pose proof (audit_phi_rep_input_bound N E CN CV version_enc version_work version_budget reps v
      Hversion) as Hrep.
    rewrite <- (audit_phi_rep_node_work_irrelevant N E CN CV node_work version_work version_enc
      reps v) in Hrep.
    destruct (@audit_phi_rep N E CN CV version_enc reps v) as [candidate re].
    pose proof (audit_phi_compare_input_bound N E CN CV node_work version_work version_enc
      version_budget candidate (MemoryPhi n) Hversion) as Hself.
    destruct (@audit_phi_compare N E CN CV version_enc candidate (MemoryPhi n)) as [self se]
      eqn:Hself_call.
    pose proof (audit_phi_all_same_input_bound N E CN CV node_work version_work version_enc
      version_budget reps candidate rest Hversion) as Hsame.
    destruct (@audit_phi_all_same N E CN CV version_enc reps candidate rest) as [same ae]
      eqn:Hsame_call.
    cbn [fst snd] in Hrep, Hself, Hsame |- *.
    rewrite Hself_call, Hsame_call; cbn [fst].
    destruct (andb (negb self) same).
    + pose proof (audit_phi_set_input_bound _ _ CV version_enc version_work version_budget
        (MemoryPhi n) candidate reps Hversion) as Hwrite.
      destruct (audit_map_set version_enc (MemoryPhi n) candidate reps) as [output we].
      unfold audit_phi_resolve_source_work in Hrep, Hself, Hsame |- *.
      cbn [snd] in Hwrite |- *.
      rewrite !length_app, !audit_phi_resolve_primitive_work_app.
      cbn [length audit_phi_resolve_primitive_work]; lia.
    + unfold audit_phi_resolve_source_work in Hrep, Hself, Hsame |- *.
      cbn [snd].
      rewrite !length_app, !audit_phi_resolve_primitive_work_app.
      cbn [length audit_phi_resolve_primitive_work]; lia.
Qed.

Lemma audit_phi_resolve_pass_input_bound N E CN CV (EN : encoding N)
    (node_enc : N -> positive * list CN)
    (version_enc : memory_version N E -> positive * list CV)
    node_work version_work node_budget version_budget index nodes :
  (forall node, node_work (snd (node_enc node)) <= node_budget node) ->
  (forall v, version_work (snd (version_enc v)) <= version_budget v) ->
  forall reps, audit_phi_resolve_source_work node_work version_work
    (snd (audit_phi_resolve_all EN node_enc version_enc index nodes reps)) <=
    audit_phi_resolve_pass_input_budget EN node_enc version_enc node_budget version_budget
      index nodes reps.
Proof.
  intros Hnode Hversion.
  induction nodes as [|n rest IH]; intro reps.
  - reflexivity.
  - cbn [audit_phi_resolve_all audit_phi_resolve_pass_input_budget].
    pose proof (audit_phi_resolve_step_input_bound N E CN CV EN node_enc version_enc node_work
      version_work node_budget version_budget index reps n Hnode Hversion) as Hstep.
    destruct (audit_phi_resolve_step EN node_enc version_enc index reps n) as [next events].
    specialize (IH next).
    destruct (audit_phi_resolve_all EN node_enc version_enc index rest next).
    cbn [fst snd] in Hstep, IH |- *.
    rewrite audit_phi_resolve_source_work_app; lia.
Qed.

(** * Stable output construction *)

Lemma audit_phi_output_work_app N E CN CV node_work version_work
    (left right : list (audit_phi_output_event N E CN CV)) :
  audit_phi_output_source_work node_work version_work (left ++ right) =
    audit_phi_output_source_work node_work version_work left +
      audit_phi_output_source_work node_work version_work right.
Proof.
  induction left as [|event rest IH].
  - reflexivity.
  - destruct event; cbn [app audit_phi_output_source_work]; rewrite IH; lia.
Qed.

Lemma audit_phi_output_keep_input_bound N E CN CV (EN : encoding N) (EE : encoding E)
    (node_enc : N -> positive * list CN)
    (version_enc : memory_version N E -> positive * list CV)
    node_work version_work version_budget reps nodes :
  (forall v, version_work (snd (version_enc v)) <= version_budget v) ->
  audit_phi_output_source_work node_work version_work
    (snd (audit_phi_output_keep_phis EN EE node_enc version_enc reps nodes)) <=
    audit_phi_output_keep_input_budget version_enc version_budget reps nodes.
Proof.
  intro Hversion.
  induction nodes as [|n rest IH].
  - reflexivity.
  - cbn [audit_phi_output_keep_phis audit_phi_output_keep_input_budget].
    pose proof (audit_phi_get_input_bound _ _ CV version_enc version_work version_budget
      (MemoryPhi n) reps Hversion) as Hget.
    destruct (audit_map_get version_enc (MemoryPhi n) reps) as [found reads].
    set (representative :=
      match found with
      | Some v =>
        v
      | None =>
        MemoryPhi n
      end).
    specialize (Hversion (MemoryPhi n)) as Hleft; specialize (Hversion representative) as Hright.
    destruct (version_enc (MemoryPhi n)) as [left_code left_body].
    destruct (version_enc representative) as [right_code right_body] eqn:Hright_call.
    pose proof (audit_positive_eqb_source_bound left_code right_code) as Hcompare.
    destruct (audit_positive_eqb left_code right_code) as [same comparisons].
    destruct (audit_phi_output_keep_phis EN EE node_enc version_enc reps rest).
    cbn [fst snd app audit_phi_output_source_work] in Hget, Hleft, Hright, Hcompare, IH |- *.
    fold representative.
    rewrite Hright_call; cbn [fst].
    lia.
Qed.

Lemma audit_phi_filter_nodes_input_bound N E CN CV (node_enc : N -> positive * list CN)
    node_work version_work node_budget kept nodes :
  (forall node, node_work (snd (node_enc node)) <= node_budget node) ->
  audit_phi_output_source_work node_work version_work
    (snd (@audit_phi_output_filter_nodes N E CN CV node_enc kept nodes)) <=
    audit_phi_filter_nodes_input_budget node_enc node_budget nodes.
Proof.
  intro Hnode.
  induction nodes as [|n rest IH].
  - reflexivity.
  - cbn [audit_phi_output_filter_nodes audit_phi_filter_nodes_input_budget].
    pose proof (audit_phi_mem_input_bound N CN node_enc node_work node_budget n kept Hnode) as Hmem.
    destruct (audit_finset_mem node_enc n kept) as [found calls].
    destruct (@audit_phi_output_filter_nodes N E CN CV node_enc kept rest).
    cbn [snd audit_phi_output_source_work] in Hmem, IH |- *; lia.
Qed.

Lemma audit_phi_filter_versions_input_bound N E CN CV (node_enc : N -> positive * list CN)
    (version_enc : memory_version N E -> positive * list CV)
    node_work version_work node_budget kept versions :
  (forall node, node_work (snd (node_enc node)) <= node_budget node) ->
  audit_phi_output_source_work node_work version_work
    (snd (audit_phi_output_filter_versions node_enc version_enc kept versions)) <=
    audit_phi_filter_versions_input_budget node_enc node_budget versions.
Proof.
  intro Hnode.
  induction versions as [|v rest IH].
  - reflexivity.
  - destruct v as [|n|e i]; cbn [audit_phi_output_filter_versions
      audit_phi_filter_versions_input_budget].
    + destruct (audit_phi_output_filter_versions node_enc version_enc kept rest).
      cbn [snd app audit_phi_output_source_work] in IH |- *; lia.
    + pose proof (audit_phi_mem_input_bound N CN node_enc node_work node_budget n kept Hnode)
        as Hmem.
      destruct (audit_finset_mem node_enc n kept) as [found calls].
      destruct (audit_phi_output_filter_versions node_enc version_enc kept rest).
      cbn [snd app audit_phi_output_source_work] in Hmem, IH |- *; lia.
    + destruct (audit_phi_output_filter_versions node_enc version_enc kept rest).
      cbn [snd app audit_phi_output_source_work] in IH |- *; lia.
Qed.

Lemma audit_phi_set_build_budget K CE (enc : K -> positive * list CE) work budget keys :
  (forall key, work (snd (enc key)) <= budget key) ->
  audit_finset_of_list_budget enc work keys <= audit_memory_distinct_input_budget enc budget keys.
Proof.
  intro Hbudget.
  induction keys as [|key rest IH].
  - reflexivity.
  - cbn [audit_finset_of_list_budget audit_memory_distinct_input_budget].
    specialize (Hbudget key); lia.
Qed.

Lemma audit_phi_output_input_bound N E CN CV (EN : encoding N) (EE : encoding E)
    (node_enc : N -> positive * list CN)
    (version_enc : memory_version N E -> positive * list CV)
    node_work version_work node_budget version_budget old reps :
  (forall node, node_work (snd (node_enc node)) <= node_budget node) ->
  (forall v, version_work (snd (version_enc v)) <= version_budget v) ->
  audit_phi_output_source_work node_work version_work
    (snd (audit_phi_producer_output_counted EN EE node_enc version_enc old reps)) <=
    audit_phi_output_input_budget EN EE node_enc version_enc node_budget version_budget old reps.
Proof.
  intros Hnode Hversion.
  unfold audit_phi_producer_output_counted, audit_phi_output_input_budget.
  pose proof (audit_phi_output_keep_input_bound N E CN CV EN EE node_enc version_enc node_work
    version_work version_budget reps (memory_phis old) Hversion) as Hkeep.
  destruct (audit_phi_output_keep_phis EN EE node_enc version_enc reps (memory_phis old))
    as [kept keeps].
  pose proof (audit_finset_of_list_source_bound N CN node_enc node_work kept) as Hset.
  pose proof (audit_phi_set_build_budget N CN node_enc node_work node_budget kept Hnode)
    as Hset_input.
  destruct (audit_finset_of_list node_enc kept) as [kept_set sets].
  pose proof (audit_phi_filter_nodes_input_bound N E CN CV node_enc node_work version_work
    node_budget kept_set (memory_phis old) Hnode) as Hphis.
  destruct (@audit_phi_output_filter_nodes N E CN CV node_enc kept_set (memory_phis old))
    as [phis phi_events].
  pose proof (audit_phi_filter_versions_input_bound N E CN CV node_enc version_enc node_work
    version_work node_budget kept_set (memory_versions old) Hnode) as Hversions.
  destruct (audit_phi_output_filter_versions node_enc version_enc kept_set (memory_versions old))
    as [versions version_events].
  cbn [fst snd] in Hkeep, Hset, Hphis, Hversions |- *.
  rewrite !audit_phi_output_work_app; cbn [app audit_phi_output_source_work].
  lia.
Qed.

(** * Concrete callback work in graph preparation *)

Lemma audit_phi_prepare_get_bodies V E B (cb : audit_prepare_callback_model V E B) weight
    bound key (input : Map.t V (list E)) :
  fold_right (fun event total => weight event + total) 0
    (snd (audit_prepare_encode_model cb key)) <= bound ->
  Forall (fun event => audit_prepare_source_body_event_work weight event <= bound)
    (map PrepareSourceMap (snd (audit_map_get (audit_prepare_encode_model cb) key input))).
Proof.
  intro Hbody; unfold audit_map_get.
  destruct (audit_prepare_encode_model cb key) as [code body].
  destruct (CollectionsAuditTrie.audit_map_code_get code input).
  cbn [snd map audit_prepare_source_body_event_work] in Hbody |- *.
  constructor; [exact Hbody|constructor].
Qed.

Lemma audit_phi_prepare_set_bodies V E B (cb : audit_prepare_callback_model V E B) weight
    bound key value (input : Map.t V (list E)) :
  fold_right (fun event total => weight event + total) 0
    (snd (audit_prepare_encode_model cb key)) <= bound ->
  Forall (fun event => audit_prepare_source_body_event_work weight event <= bound)
    (map PrepareSourceMap (snd (audit_map_set (audit_prepare_encode_model cb) key value input))).
Proof.
  intro Hbody; unfold audit_map_set.
  destruct (audit_prepare_encode_model cb key) as [code body].
  destruct (CollectionsAuditTrie.audit_trie_set code (key, value) input).
  cbn [snd map audit_prepare_source_body_event_work] in Hbody |- *.
  constructor; [exact Hbody|constructor].
Qed.

Lemma audit_phi_prepare_out_bodies V E B (cb : audit_prepare_callback_model V E B) weight bound
    nodes :
  (forall n, In n nodes -> fold_right (fun event total => weight event + total) 0
    (snd (audit_prepare_out_model cb n)) <= bound) ->
  (forall n, In n nodes -> fold_right (fun event total => weight event + total) 0
    (snd (audit_prepare_encode_model cb n)) <= bound) ->
  forall input, Forall (fun event => audit_prepare_source_body_event_work weight event <= bound)
    (snd (audit_prepare_source_out cb nodes input)).
Proof.
  induction nodes as [|n rest IH]; intros Hout Hencode input.
  - cbn [audit_prepare_source_out snd]; constructor; [cbn; lia|constructor].
  - cbn [audit_prepare_source_out].
    specialize (IH (fun x Hin => Hout x (or_intror Hin))
      (fun x Hin => Hencode x (or_intror Hin)) input).
    destruct (audit_prepare_source_out cb rest input) as [middle tail].
    specialize (Hout n (or_introl eq_refl)).
    destruct (audit_prepare_out_model cb n) as [outgoing body].
    pose proof (audit_phi_prepare_set_bodies V E B cb weight bound n outgoing middle
      (Hencode n (or_introl eq_refl))) as Hset.
    destruct (audit_map_set (audit_prepare_encode_model cb) n outgoing middle) as [next calls].
    cbn [snd] in Hout, Hset, IH |- *.
    constructor; [cbn; lia|].
    apply Forall_app; split; [exact IH|].
    constructor; [exact Hout|exact Hset].
Qed.

Lemma audit_phi_prepare_edges_bodies V E B (cb : audit_prepare_callback_model V E B) weight bound
    edges :
  (forall edge, In edge edges -> fold_right (fun event total => weight event + total) 0
    (snd (audit_prepare_target_model cb edge)) <= bound) ->
  (forall edge, In edge edges -> fold_right (fun event total => weight event + total) 0
    (snd (audit_prepare_encode_model cb (fst (audit_prepare_target_model cb edge)))) <= bound) ->
  forall input, Forall (fun event => audit_prepare_source_body_event_work weight event <= bound)
    (snd (audit_prepare_source_edges cb edges input)).
Proof.
  induction edges as [|edge rest IH]; intros Htarget Hencode input.
  - cbn [audit_prepare_source_edges snd]; constructor; [cbn; lia|constructor].
  - cbn [audit_prepare_source_edges].
    specialize (IH (fun e Hin => Htarget e (or_intror Hin))
      (fun e Hin => Hencode e (or_intror Hin)) input).
    destruct (audit_prepare_source_edges cb rest input) as [middle tail].
    specialize (Htarget edge (or_introl eq_refl)).
    specialize (Hencode edge (or_introl eq_refl)).
    destruct (audit_prepare_target_model cb edge) as [target body].
    cbn [fst snd] in Htarget, Hencode.
    pose proof (audit_phi_prepare_get_bodies V E B cb weight bound target middle Hencode) as Hget.
    destruct (audit_map_get (audit_prepare_encode_model cb) target middle) as [found reads].
    pose proof (audit_phi_prepare_set_bodies V E B cb weight bound target
      (edge ::
        match found with
        | Some row =>
          row
        | None =>
          []
        end) middle Hencode) as Hset.
    destruct (audit_map_set (audit_prepare_encode_model cb) target
      (edge ::
        match found with
        | Some row =>
          row
        | None =>
          []
        end) middle) as [next writes].
    cbn [snd] in Hget, Hset, IH |- *.
    constructor; [cbn; lia|].
    apply Forall_app; split; [exact IH|].
    constructor; [exact Htarget|constructor; [exact Htarget|]].
    apply Forall_app; split; [exact Hget|].
    constructor; [destruct found; cbn; lia|exact Hset].
Qed.

Lemma audit_phi_prepare_in_bodies V E B (cb : audit_prepare_callback_model V E B) weight bound
    nodes :
  (forall n, In n nodes -> fold_right (fun event total => weight event + total) 0
    (snd (audit_prepare_out_model cb n)) <= bound) ->
  (forall n edge, In n nodes -> In edge (fst (audit_prepare_out_model cb n)) ->
    fold_right (fun event total => weight event + total) 0
      (snd (audit_prepare_target_model cb edge)) <= bound) ->
  (forall n edge, In n nodes -> In edge (fst (audit_prepare_out_model cb n)) ->
    fold_right (fun event total => weight event + total) 0
      (snd (audit_prepare_encode_model cb (fst (audit_prepare_target_model cb edge)))) <= bound) ->
  forall input, Forall (fun event => audit_prepare_source_body_event_work weight event <= bound)
    (snd (audit_prepare_source_in cb nodes input)).
Proof.
  induction nodes as [|n rest IH]; intros Hout Htarget Hencode input.
  - cbn [audit_prepare_source_in snd]; constructor; [cbn; lia|constructor].
  - cbn [audit_prepare_source_in].
    specialize (IH (fun x Hin => Hout x (or_intror Hin))
      (fun x e Hin He => Htarget x e (or_intror Hin) He)
      (fun x e Hin He => Hencode x e (or_intror Hin) He) input).
    destruct (audit_prepare_source_in cb rest input) as [middle tail].
    specialize (Hout n (or_introl eq_refl)).
    specialize (Htarget n); specialize (Hencode n).
    destruct (audit_prepare_out_model cb n) as [outgoing body].
    cbn [fst snd] in Hout, Htarget, Hencode.
    pose proof (audit_phi_prepare_edges_bodies V E B cb weight bound outgoing
      (fun e He => Htarget e (or_introl eq_refl) He)
      (fun e He => Hencode e (or_introl eq_refl) He) middle) as Hedges.
    destruct (audit_prepare_source_edges cb outgoing middle) as [next events].
    cbn [snd] in IH, Hedges |- *.
    constructor; [cbn; lia|].
    apply Forall_app; split; [exact IH|].
    constructor; [exact Hout|exact Hedges].
Qed.

Lemma audit_phi_prepare_count_bodies V E B (cb : audit_prepare_callback_model V E B) weight bound
    nodes :
  (forall n, In n nodes -> fold_right (fun event total => weight event + total) 0
    (snd (audit_prepare_out_model cb n)) <= bound) ->
  Forall (fun event => audit_prepare_source_body_event_work weight event <= bound)
    (snd (audit_prepare_source_edge_count cb nodes)).
Proof.
  induction nodes as [|n rest IH]; intro Hout.
  - cbn [audit_prepare_source_edge_count snd]; constructor; [cbn; lia|constructor].
  - cbn [audit_prepare_source_edge_count].
    specialize (IH (fun x Hin => Hout x (or_intror Hin))).
    destruct (audit_prepare_source_edge_count cb rest) as [count tail].
    specialize (Hout n (or_introl eq_refl)).
    destruct (audit_prepare_out_model cb n) as [outgoing body].
    cbn [snd] in Hout, IH |- *.
    constructor; [cbn; lia|].
    apply Forall_app; split; [exact IH|].
    constructor; [exact Hout|constructor; [cbn; lia|constructor]].
Qed.

Lemma audit_phi_prepare_body_sum V E B weight bound
    (events : list (audit_prepare_source_event V E B)) :
  Forall (fun event => audit_prepare_source_body_event_work weight event <= bound) events ->
  audit_prepare_source_body_work weight events <= length events * bound.
Proof.
  intro Hbound; induction Hbound as [|event rest Hhead Hrest IH].
  - reflexivity.
  - unfold audit_prepare_source_body_work in *; cbn [fold_right length] in *; lia.
Qed.

Lemma audit_phi_prepare_source_input_bound V E B (EV : encoding V) (g : Graph.t V E)
    (cb : audit_prepare_callback_model V E B) weight bound :
  audit_prepare_callbacks_erase EV g cb ->
  (forall n, In n (Graph.nodes g) -> fold_right (fun event total => weight event + total) 0
    (snd (audit_prepare_out_model cb n)) <= bound) ->
  (forall n, In n (Graph.nodes g) -> fold_right (fun event total => weight event + total) 0
    (snd (audit_prepare_encode_model cb n)) <= bound) ->
  (forall n edge, In n (Graph.nodes g) -> In edge (Graph.out g n) ->
    fold_right (fun event total => weight event + total) 0
      (snd (audit_prepare_target_model cb edge)) <= bound) ->
  (forall n edge, In n (Graph.nodes g) -> In edge (Graph.out g n) ->
    fold_right (fun event total => weight event + total) 0
      (snd (audit_prepare_encode_model cb (fst (audit_prepare_target_model cb edge)))) <= bound) ->
  audit_prepare_source_work weight (snd (audit_prepare_source_counted EV g cb)) <=
    audit_prepare_source_budget EV g + audit_graph_prepare_full_event_bound g * bound.
Proof.
  intros Hcallbacks Hout Hencode Htarget Htarget_encode.
  pose proof (audit_prepare_source_correct V E B EV g cb weight Hcallbacks) as Hsource.
  assert (Hbody : Forall (fun event => audit_prepare_source_body_event_work weight event <= bound)
    (snd (audit_prepare_source_counted EV g cb))).
  { unfold audit_prepare_source_counted.
    pose proof (audit_phi_prepare_out_bodies V E B cb weight bound (Graph.nodes g) Hout Hencode
      Map.empty) as Hout_run.
    destruct (audit_prepare_source_out cb (Graph.nodes g) Map.empty) as [outgoing out_events].
    assert (Hin_targets : forall n edge, In n (Graph.nodes g) ->
      In edge (fst (audit_prepare_out_model cb n)) ->
      fold_right (fun event total => weight event + total) 0
        (snd (audit_prepare_target_model cb edge)) <= bound).
    { intros n edge Hn He; apply (Htarget n edge Hn).
      rewrite (proj1 Hcallbacks n) in He; exact He. }
    assert (Hin_encode : forall n edge, In n (Graph.nodes g) ->
      In edge (fst (audit_prepare_out_model cb n)) ->
      fold_right (fun event total => weight event + total) 0
        (snd (audit_prepare_encode_model cb (fst (audit_prepare_target_model cb edge)))) <= bound).
    { intros n edge Hn He; apply (Htarget_encode n edge Hn).
      rewrite (proj1 Hcallbacks n) in He; exact He. }
    pose proof (audit_phi_prepare_in_bodies V E B cb weight bound (Graph.nodes g) Hout Hin_targets
      Hin_encode Map.empty) as Hin_run.
    destruct (audit_prepare_source_in cb (Graph.nodes g) Map.empty) as [incoming in_events].
    pose proof (audit_phi_prepare_count_bodies V E B cb weight bound (Graph.nodes g) Hout)
      as Hcount_run.
    destruct (audit_prepare_source_edge_count cb (Graph.nodes g)) as [count count_events].
    cbn [snd] in Hout_run, Hin_run, Hcount_run |- *.
    apply Forall_app; split; [exact Hout_run|].
    apply Forall_app; split; [exact Hin_run|].
    constructor; [cbn; lia|].
    apply Forall_app; split; [exact Hcount_run|].
    constructor; [cbn; lia|constructor]. }
  pose proof (audit_phi_prepare_body_sum V E B weight bound _ Hbody) as Hsum.
  destruct (audit_prepare_source_counted EV g cb) as [result events].
  destruct Hsource as [_ [Hlength Hwork]].
  cbn [snd] in Hsum |- *; nia.
Qed.

(** * Original-input envelopes for graph callbacks *)

Lemma audit_phi_graph_node_envelope N E CN (node_enc : N -> positive * list CN) node_budget
    (dep : Graph.t N (phi_dependency_edge N E)) nodes n :
  In n nodes ->
  node_budget n <= audit_phi_graph_callback_envelope node_enc node_budget dep nodes /\
    audit_phi_get_input_budget node_enc node_budget n <=
      audit_phi_graph_callback_envelope node_enc node_budget dep nodes.
Proof.
  induction nodes as [|node rest IH]; intro Hin; [contradiction|].
  cbn [audit_phi_graph_callback_envelope].
  destruct Hin as [->|Hin].
  - split; lia.
  - specialize (IH Hin); destruct IH; split; lia.
Qed.

Lemma audit_phi_graph_target_sum N E (node_budget : N -> nat)
    (edges : list (phi_dependency_edge N E)) edge :
  In edge edges -> node_budget (dependency_target edge) <=
    audit_phi_graph_targets_input_budget node_budget edges.
Proof.
  induction edges as [|first rest IH]; intro Hin; [contradiction|].
  cbn [audit_phi_graph_targets_input_budget].
  destruct Hin as [->|Hin]; [lia|specialize (IH Hin); lia].
Qed.

Lemma audit_phi_graph_target_envelope N E CN (node_enc : N -> positive * list CN) node_budget
    (dep : Graph.t N (phi_dependency_edge N E)) nodes n edge :
  In n nodes -> In edge (Graph.out dep n) ->
  node_budget (dependency_target edge) <=
    audit_phi_graph_callback_envelope node_enc node_budget dep nodes.
Proof.
  induction nodes as [|node rest IH]; intros Hin Hedge; [contradiction|].
  cbn [audit_phi_graph_callback_envelope].
  destruct Hin as [->|Hin].
  - pose proof (audit_phi_graph_target_sum N E node_budget (Graph.out dep n) edge Hedge); lia.
  - specialize (IH Hin Hedge); lia.
Qed.

Lemma audit_phi_graph_prepare_input_bound N E CN (EN : encoding N)
    (node_enc : N -> positive * list CN) node_work node_budget
    (dep : Graph.t N (phi_dependency_edge N E)) rows :
  (forall n, fst (node_enc n) = encode EN n) ->
  (forall n, node_work (snd (node_enc n)) <= node_budget n) ->
  (forall n, index_edges EN rows n = Graph.out dep n) ->
  (forall edge, Graph.target dep edge = dependency_target edge) ->
  audit_prepare_source_work (audit_phi_graph_callback_work node_work)
    (snd (audit_prepare_source_counted EN dep (audit_phi_prepare_callbacks node_enc rows dep))) <=
  audit_prepare_source_budget EN dep + audit_graph_prepare_full_event_bound dep *
    audit_phi_graph_callback_envelope node_enc node_budget dep (Graph.nodes dep).
Proof.
  intros Hencode Hnode Hrows Htarget.
  apply audit_phi_prepare_source_input_bound.
  - apply audit_phi_prepare_callbacks_erases; assumption.
  - intros n Hin.
    unfold audit_phi_prepare_callbacks; cbn [audit_prepare_out_model].
    pose proof (audit_phi_get_input_bound N _ CN node_enc node_work node_budget n rows Hnode)
      as Hget.
    pose proof (audit_phi_graph_node_envelope N E CN node_enc node_budget dep (Graph.nodes dep)
      n Hin) as [_ Henvelope].
    destruct (audit_map_get node_enc n rows).
    cbn [snd fold_right audit_phi_graph_callback_work] in Hget |- *; lia.
  - intros n Hin.
    unfold audit_phi_prepare_callbacks; cbn [audit_prepare_encode_model].
    specialize (Hnode n).
    pose proof (audit_phi_graph_node_envelope N E CN node_enc node_budget dep (Graph.nodes dep)
      n Hin) as [Henvelope _].
    destruct (node_enc n); cbn [snd fold_right audit_phi_graph_callback_work] in Hnode |- *; lia.
  - intros n edge Hin Hedge; cbn; lia.
  - intros n edge Hin Hedge.
    unfold audit_phi_prepare_callbacks.
    cbn [audit_prepare_encode_model audit_prepare_target_model fst].
    specialize (Hnode (Graph.target dep edge)).
    pose proof (audit_phi_graph_target_envelope N E CN node_enc node_budget dep (Graph.nodes dep)
      n edge Hin Hedge) as Henvelope.
    rewrite <- (Htarget edge) in Henvelope.
    destruct (node_enc (Graph.target dep edge)).
    cbn [snd fold_right audit_phi_graph_callback_work] in Hnode |- *; lia.
Qed.

Lemma audit_phi_prepared_out_row N E (EN : encoding N) (dep : Graph.t N E) n edges :
  In (n, edges) (Map.elements (out_index (prepare EN dep))) ->
  In n (Graph.nodes dep) /\ edges = Graph.out dep n.
Proof.
  intro Hin.
  assert (Hmap : Map.wf EN (out_index (prepare EN dep))).
  { unfold prepare; cbn [out_index].
    induction (Graph.nodes dep) as [|node rest IH].
    - apply Map.wf_empty.
    - apply Map.wf_set; exact IH. }
  pose proof (Map.elements_sound EN n edges _ Hmap Hin) as Hget.
  change (Map.get EN n (AnalysesMemoryFrontier.memory_result_index EN (Graph.out dep)
    (Graph.nodes dep)) = Some edges) in Hget.
  assert (Hnode : In n (Graph.nodes dep)).
  { apply (proj1 (AnalysesMemoryFrontier.memory_result_index_domain EN (Graph.out dep)
      (Graph.nodes dep) n)); eexists; exact Hget. }
  split; [exact Hnode|].
  pose proof (AnalysesMemoryFrontier.memory_result_index_at EN (Graph.out dep) (Graph.nodes dep)
    n Hnode) as Hrow.
  rewrite Hget in Hrow; now inversion Hrow.
Qed.

Lemma audit_phi_scc_vertex_envelope N E CN (EN : encoding N)
    (node_enc : N -> positive * list CN) node_budget
    (dep : Graph.t N (phi_dependency_edge N E)) vertex :
  (forall edge, Graph.target dep edge = dependency_target edge) ->
  In vertex (Graph.nodes dep ++ map (Graph.target dep)
    (flat_map snd (Map.elements (out_index (prepare EN dep))))) ->
  node_budget vertex <=
    audit_phi_graph_callback_envelope node_enc node_budget dep (Graph.nodes dep).
Proof.
  intros Htarget Hin.
  apply in_app_iff in Hin; destruct Hin as [Hnode|Htarget_member].
  - exact (proj1 (audit_phi_graph_node_envelope N E CN node_enc node_budget dep (Graph.nodes dep)
      vertex Hnode)).
  - apply in_map_iff in Htarget_member; destruct Htarget_member as [edge [<- Hedge]].
    apply in_flat_map in Hedge; destruct Hedge as [[n edges] [Hrow Hedge]].
    destruct (audit_phi_prepared_out_row N _ EN dep n edges Hrow) as [Hnode Hedges].
    cbn [snd] in Hedge.
    rewrite Hedges in Hedge; rewrite Htarget.
    eapply audit_phi_graph_target_envelope; eassumption.
Qed.

(** * SCC callback captures at their actual operands *)

Lemma audit_phi_scc_event_body_shape V E B vertices
    (item : audit_tarjan_nested_event V E (audit_graph_callback_capture V E B)) :
  audit_scc_source_event_wellformed item -> audit_tarjan_event_keys vertices (fst item) ->
  length (snd item) <= 2 /\
  forall capture, In capture (snd item) ->
  match capture with
  | AuditGraphEncodeCapture _ _ _ vertex _ _ =>
    In vertex vertices
  | AuditGraphTargetCapture _ _ _ _ _ _ =>
    True
  end.
Proof.
  destruct item as [event body]; intros Hshape Hkeys.
  destruct event;
    try match goal with
    | helper : audit_thelper_event _ _ |- _ =>
      destruct helper
    end.
  all: cbn [audit_scc_source_event_wellformed audit_tarjan_event_keys audit_tarjan_helper_keys
    fst snd] in Hshape, Hkeys.
  all: repeat match type of Hshape with
  | ex _ =>
    destruct Hshape as [? Hshape]
  end.
  all: subst body.
  all: split; [cbn; lia|].
  all: intros capture Hin; cbn in Hin; intuition subst; cbn; tauto.
Qed.

Lemma audit_phi_scc_capture_input_bound N E CN (node_enc : N -> positive * list CN)
    node_work node_budget (dep : Graph.t N (phi_dependency_edge N E)) bound vertices capture :
  (forall n, node_work (snd (node_enc n)) <= node_budget n) ->
  (forall n, In n vertices -> node_budget n <= bound) ->
  audit_dfs_capture_receipt (audit_phi_scc_callbacks node_enc dep) capture ->
  (match capture with
  | AuditGraphEncodeCapture _ _ _ vertex _ _ =>
    In vertex vertices
  | AuditGraphTargetCapture _ _ _ _ _ _ =>
    True
  end) ->
  audit_graph_capture_work (audit_phi_graph_callback_work node_work) capture <= bound.
Proof.
  intros Hnode Henvelope Hreceipt Hin.
  destruct capture as [edge target body|vertex code body].
  - unfold audit_dfs_capture_receipt, audit_phi_scc_callbacks in Hreceipt.
    cbn [audit_dfs_target_model] in Hreceipt; inversion Hreceipt; subst body.
    cbn [audit_graph_capture_work fold_right]; lia.
  - unfold audit_dfs_capture_receipt, audit_phi_scc_callbacks in Hreceipt.
    cbn [audit_dfs_encode_model] in Hreceipt.
    specialize (Hnode vertex); specialize (Henvelope vertex Hin).
    destruct (node_enc vertex) as [actual_code actual_body].
    inversion Hreceipt; subst body.
    cbn [snd audit_graph_capture_work fold_right audit_phi_graph_callback_work] in Hnode |- *; lia.
Qed.

Lemma audit_phi_scc_event_body_input_bound N E CN (node_enc : N -> positive * list CN)
    node_work node_budget (dep : Graph.t N (phi_dependency_edge N E)) bound vertices item :
  (forall n, node_work (snd (node_enc n)) <= node_budget n) ->
  (forall n, In n vertices -> node_budget n <= bound) ->
  audit_scc_source_event_wellformed item -> audit_tarjan_event_keys vertices (fst item) ->
  audit_tarjan_event_bodies
    (audit_dfs_capture_receipt (audit_phi_scc_callbacks node_enc dep)) item ->
  fold_right (fun capture total =>
    audit_graph_capture_work (audit_phi_graph_callback_work node_work) capture + total)
    0 (snd item) <= 2 * bound.
Proof.
  intros Hnode Henvelope Hshape Hkeys Hreceipts.
  destruct (audit_phi_scc_event_body_shape N _ _ vertices item Hshape Hkeys) as [Hlength Hmembers].
  assert (Hsum : fold_right (fun capture total =>
    audit_graph_capture_work (audit_phi_graph_callback_work node_work) capture + total) 0
    (snd item) <= length (snd item) * bound).
  { unfold audit_tarjan_event_bodies in Hreceipts.
    clear Hlength.
    induction Hreceipts as [|capture rest Hcapture Hrest IH].
    - reflexivity.
    - cbn [fold_right length].
      pose proof (audit_phi_scc_capture_input_bound N E CN node_enc node_work node_budget dep bound
        vertices capture Hnode Henvelope Hcapture (Hmembers capture (or_introl eq_refl))) as Hhead.
      specialize (IH (fun c Hin => Hmembers c (or_intror Hin))).
      lia. }
  nia.
Qed.

Lemma audit_phi_scc_source_input_bound N E CN (EN : encoding N)
    (node_enc : N -> positive * list CN) node_work node_budget
    (dep : Graph.t N (phi_dependency_edge N E)) :
  (forall n, fst (node_enc n) = encode EN n) ->
  (forall n, node_work (snd (node_enc n)) <= node_budget n) ->
  (forall edge, Graph.target dep edge = dependency_target edge) ->
  audit_scc_source_work (audit_phi_graph_callback_work node_work)
    (snd (audit_scc_source_counted (prepare EN dep) (audit_phi_scc_callbacks node_enc dep)
      (Graph.nodes dep))) <=
  audit_scc_source_budget EN dep (prepare EN dep) (Graph.nodes dep) +
    2 * audit_tarjan_input_event_bound (prepare EN dep) (Graph.nodes dep) *
      audit_phi_graph_callback_envelope node_enc node_budget dep (Graph.nodes dep).
Proof.
  intros Hencode Hnode Htarget.
  pose proof (audit_phi_scc_callbacks_erases N E CN EN node_enc dep Hencode) as Hcallbacks.
  pose proof (audit_scc_source_correct N _ _ EN dep (prepare EN dep)
    (audit_phi_scc_callbacks node_enc dep) (audit_phi_graph_callback_work node_work)
    (Graph.nodes dep) Hcallbacks) as Hsource.
  pose proof (audit_scc_source_receipts (prepare EN dep) (audit_phi_scc_callbacks node_enc dep)
    (Graph.nodes dep)) as Hreceipts.
  pose proof (audit_scc_counted_keys (prepare EN dep) (Graph.nodes dep)) as Hkeys.
  pose proof (audit_scc_source_erases (prepare EN dep) (audit_phi_scc_callbacks node_enc dep)
    (Graph.nodes dep) Hcallbacks) as Herase.
  rewrite <- Herase in Hkeys; cbn [snd] in Hkeys.
  destruct (audit_scc_source_counted (prepare EN dep) (audit_phi_scc_callbacks node_enc dep)
    (Graph.nodes dep)) as [result events].
  destruct Hsource as [_ [Hshape [Hcount Hwork]]].
  cbn [fst snd] in Hkeys, Hreceipts |- *.
  set (bound := audit_phi_graph_callback_envelope node_enc node_budget dep (Graph.nodes dep)).
  assert (Hbody : audit_scc_source_body_work (audit_phi_graph_callback_work node_work) events <=
    2 * length events * bound).
  { assert (Hevents : Forall (fun item => fold_right (fun capture total =>
      audit_graph_capture_work (audit_phi_graph_callback_work node_work) capture + total) 0
      (snd item) <= 2 * bound) events).
    { apply Forall_forall; intros item Hin.
      eapply audit_phi_scc_event_body_input_bound; [exact Hnode| | | |].
      - intros n Hn; apply (audit_phi_scc_vertex_envelope N E CN EN node_enc node_budget dep n
          Htarget Hn).
      - exact (proj1 (Forall_forall _ _) Hshape item Hin).
      - apply (proj1 (Forall_forall _ _) Hkeys (fst item)); apply in_map; exact Hin.
      - exact (proj1 (Forall_forall _ _) Hreceipts item Hin). }
    clear Hshape Hkeys Hreceipts Hcount Hwork Herase.
    induction Hevents as [|event rest Hhead Hrest IH].
    - reflexivity.
    - unfold audit_scc_source_body_work in *; cbn [fold_right length] in *; nia. }
  nia.
Qed.

(** * Whole producer composition *)

Lemma audit_phi_dependency_graph_input_bound N E CN (EN : encoding N)
    (node_enc : N -> positive * list CN) node_work node_budget mg inputs :
  (forall n, fst (node_enc n) = encode EN n) ->
  (forall n, node_work (snd (node_enc n)) <= node_budget n) ->
  let '(dep, rows, events) := @audit_phi_dependency_graph_counted N E CN EN node_enc mg inputs in
  (forall n, index_edges EN rows n = Graph.out dep n) /\
  (forall edge, Graph.target dep edge = dependency_target edge) /\
  audit_phi_dependency_rows_work node_work events <=
    audit_memory_index_input_budget node_enc node_budget
      (audit_phi_dependency_row_input_budget node_enc node_budget inputs) (memory_phis mg).
Proof.
  intros Hencode Hnode.
  pose proof (audit_phi_dependency_graph_erases N E CN EN node_enc mg inputs Hencode) as Hshape.
  pose proof (audit_phi_dependency_rows_input_bound N E CN node_enc node_work node_budget mg
    inputs Hnode) as Hwork.
  unfold audit_phi_dependency_graph_counted in *.
  destruct (audit_phi_dependency_rows_counted node_enc mg inputs) as [rows events].
  cbn [fst snd] in Hwork, Hshape |- *.
  destruct Hshape as [_ Hrows].
  split; [rewrite Hrows; reflexivity|].
  split; [reflexivity|exact Hwork].
Qed.

Lemma audit_phi_resolution_output_input_bound N E CN CV (EN : encoding N) (EE : encoding E)
    (node_enc : N -> positive * list CN)
    (version_enc : memory_version N E -> positive * list CV)
    node_work version_work node_budget version_budget mg index order :
  (forall n, node_work (snd (node_enc n)) <= node_budget n) ->
  (forall v, version_work (snd (version_enc v)) <= version_budget v) ->
  let '(reps, resolution) := audit_phi_resolve_all EN node_enc version_enc index order Map.empty in
  let '(_, output) := audit_phi_producer_output_counted EN EE node_enc version_enc mg reps in
  audit_phi_resolve_source_work node_work version_work resolution +
    audit_phi_output_source_work node_work version_work output <=
  audit_phi_resolve_pass_input_budget EN node_enc version_enc node_budget version_budget
    index order Map.empty +
    audit_phi_output_input_budget EN EE node_enc version_enc node_budget version_budget mg reps.
Proof.
  intros Hnode Hversion.
  pose proof (audit_phi_resolve_pass_input_bound N E CN CV EN node_enc version_enc node_work
    version_work node_budget version_budget index order Hnode Hversion Map.empty) as Hresolve.
  destruct (audit_phi_resolve_all EN node_enc version_enc index order Map.empty) as [reps events].
  pose proof (audit_phi_output_input_bound N E CN CV EN EE node_enc version_enc node_work
    version_work node_budget version_budget mg reps Hnode Hversion) as Houtput.
  destruct (audit_phi_producer_output_counted EN EE node_enc version_enc mg reps).
  cbn [fst snd] in Hresolve, Houtput |- *; lia.
Qed.

Lemma audit_phi_prepared_dependency_input_bound N E CN (EN : encoding N)
    (node_enc : N -> positive * list CN) node_work node_budget mg inputs :
  (forall n, fst (node_enc n) = encode EN n) ->
  (forall n, node_work (snd (node_enc n)) <= node_budget n) ->
  let '(dep, rows, dependency_events) :=
    @audit_phi_dependency_graph_counted N E CN EN node_enc mg inputs in
  let '(prep, preparation) := audit_prepare_source_counted EN dep
    (audit_phi_prepare_callbacks node_enc rows dep) in
  prep = prepare EN dep /\
  (forall edge, Graph.target dep edge = dependency_target edge) /\
  audit_phi_dependency_rows_work node_work dependency_events <=
    audit_memory_index_input_budget node_enc node_budget
      (audit_phi_dependency_row_input_budget node_enc node_budget inputs) (memory_phis mg) /\
  audit_prepare_source_work (audit_phi_graph_callback_work node_work) preparation <=
    audit_prepare_source_budget EN dep + audit_graph_prepare_full_event_bound dep *
      audit_phi_graph_callback_envelope node_enc node_budget dep (Graph.nodes dep).
Proof.
  intros Hencode Hnode.
  pose proof (audit_phi_dependency_graph_input_bound N E CN EN node_enc node_work node_budget mg
    inputs Hencode Hnode) as Hdependency.
  destruct (audit_phi_dependency_graph_counted EN node_enc mg inputs) as [[dep rows] events].
  destruct Hdependency as [Hrows [Htarget Hdependency]].
  pose proof (audit_phi_graph_prepare_input_bound N E CN EN node_enc node_work node_budget dep
    rows Hencode Hnode Hrows Htarget) as Hprepare.
  pose proof (audit_prepare_source_correct N _ _ EN dep
    (audit_phi_prepare_callbacks node_enc rows dep) (audit_phi_graph_callback_work node_work)
    (audit_phi_prepare_callbacks_erases N E CN EN node_enc dep rows Hencode Hrows)) as Hprep.
  destruct (audit_prepare_source_counted EN dep (audit_phi_prepare_callbacks node_enc rows dep)).
  destruct Hprep as [Hprep _].
  split; [exact Hprep|].
  split; [exact Htarget|].
  split; [exact Hdependency|exact Hprepare].
Qed.

(** Concrete phase bounds compose through the producer's exact persistent intermediate states. *)
Theorem audit_phi_producer_whole_input_bound : audit_phi_producer_whole_input_bound_statement.
Proof.
  intros N E T CN CE PE OE EN EE node_enc edge_enc pred operand node_work edge_work pred_work
    operand_work node_budget edge_budget pred_budget operand_budget g effects mg
    Hencode Hnode Hedge Hpred Hoperand.
  set (version_enc := audit_memory_version_encode node_enc edge_enc).
  set (version_budget :=
    audit_memory_version_input_budget node_enc edge_enc node_budget edge_budget).
  assert (Hversion : forall v, audit_memory_version_work node_work edge_work
    (snd (version_enc v)) <= version_budget v).
  { intro v; apply audit_memory_version_input_bound; assumption. }
  unfold audit_phi_produce, audit_phi_producer_input_budget.
  fold version_enc version_budget.
  pose proof (audit_phi_rows_input_bound N E CN CE PE OE node_enc edge_enc pred operand node_work
    edge_work pred_work operand_work node_budget edge_budget pred_budget operand_budget
    (memory_phis mg) Hnode Hedge Hpred Hoperand) as Hrows.
  destruct (audit_phi_input_rows node_enc edge_enc pred operand (memory_phis mg))
    as [inputs row_events].
  pose proof (audit_phi_prepared_dependency_input_bound N E CN EN node_enc node_work node_budget
    mg inputs Hencode Hnode) as Hsetup.
  destruct (audit_phi_dependency_graph_counted EN node_enc mg inputs) as [[dep rows] dep_events]
    eqn:Hdep_run.
  destruct (audit_prepare_source_counted EN dep (audit_phi_prepare_callbacks node_enc rows dep))
    as [prep prep_events] eqn:Hprep_run.
  destruct Hsetup as [Hprep [Htarget [Hdependency Hprepare]]].
  subst prep.
  pose proof (audit_phi_scc_source_input_bound N E CN EN node_enc node_work node_budget dep
    Hencode Hnode Htarget) as Hscc.
  destruct (audit_scc_source_counted (prepare EN dep) (audit_phi_scc_callbacks node_enc dep)
    (Graph.nodes dep)) as [result scc_events] eqn:Hscc_run.
  pose proof (audit_phi_cycles_from_input_bound N E CN EN node_enc node_work node_budget dep
    (prepare EN dep) (components result) Hnode FinSet.empty) as Hcycles.
  unfold audit_phi_cycle_flags_counted.
  destruct (audit_phi_cycle_flags_from EN node_enc dep (prepare EN dep) (components result)
    FinSet.empty) as [cycles cycle_events] eqn:Hcycles_run.
  pose proof (audit_phi_resolution_output_input_bound N E CN _ EN EE node_enc version_enc node_work
    (audit_memory_version_work node_work edge_work) node_budget version_budget
    mg (PhiDependencyIndex inputs dep (prepare EN dep) result cycles) (concat (components result))
    Hnode Hversion) as Htail.
  destruct (audit_phi_resolve_all EN node_enc version_enc
    (PhiDependencyIndex inputs dep (prepare EN dep) result cycles) (concat (components result))
    Map.empty) as [reps resolve_events] eqn:Hresolve_run.
  destruct (audit_phi_producer_output_counted EN EE node_enc version_enc mg reps)
    as [output output_events].
  cbn [fst snd].
  unfold audit_phi_producer_work.
  cbn [audit_phi_producer_work audit_phi_run_rows audit_phi_run_dependency_rows audit_phi_run_order
    audit_phi_run_index phi_index_scc audit_phi_run_graph_preparation audit_phi_run_scc_events
    audit_phi_run_cycle_events audit_phi_run_resolution audit_phi_run_output_events fst snd] in *.
  rewrite Hdep_run; cbn [fst snd].
  rewrite Hprep_run; cbn [fst snd].
  rewrite Hscc_run; cbn [fst snd].
  rewrite Hcycles_run; cbn [fst snd].
  rewrite Hresolve_run; cbn [fst snd].
  lia.
Qed.
