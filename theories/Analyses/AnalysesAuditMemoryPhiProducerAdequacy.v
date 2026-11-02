(** * Phi producer phase adequacy

    The counted phases preserve cycle flags, stable output filters and ordered resolution.
    For example, a singleton cycle scans all successor edges before its flag is returned.
    Builds on: AnalysesAuditMemoryPhiProducer and row, graph and resolution adequacy. *)

From Stdlib Require Import List Bool PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditMap CollectionsAuditMapAdequacy CollectionsAuditFinSet
  CollectionsAuditFinSetAdequacy CollectionsAuditPrimitive CollectionsAuditPrimitiveAdequacy.
From Galois.Graph Require Import GraphCore GraphPrepare GraphScc GraphAuditBase
  GraphAuditBaseAdequacy GraphAuditDfs GraphAuditScc GraphAuditSccAdequacy.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryFlow AnalysesMemoryFrontier
  AnalysesAuditMemoryPhiState AnalysesAuditMemoryPhiRows AnalysesAuditMemoryPhiRowsAdequacy
  AnalysesAuditMemoryPhiProducer AnalysesAuditMemoryPhiResolve
  AnalysesAuditMemoryPhiResolveAdequacy AnalysesAuditMemoryIndex AnalysesAuditMemoryIndexAdequacy.
Import List.ListNotations.

(** * Cycle flags *)

Lemma audit_phi_cycle_self_edges_erases N E CN (EN : encoding N)
    (node_enc : N -> positive * list CN) (dep : Graph.t N (phi_dependency_edge N E)) n edges :
  (forall x, fst (node_enc x) = encode EN x) ->
  fst (audit_phi_cycle_self_edges node_enc dep n edges) =
    existsb (fun edge => Pos.eqb (encode EN (Graph.target dep edge)) (encode EN n)) edges.
Proof.
  intro Henc.
  induction edges as [|edge rest IH].
  - reflexivity.
  - cbn [audit_phi_cycle_self_edges existsb].
    specialize (Henc (Graph.target dep edge)) as Htarget; specialize (Henc n) as Hnode.
    destruct (node_enc (Graph.target dep edge)) as [target_code target_body].
    destruct (node_enc n) as [node_code node_body].
    pose proof (audit_positive_eqb_erases target_code node_code) as Heq.
    destruct (audit_positive_eqb target_code node_code) as [same comparisons].
    destruct (audit_phi_cycle_self_edges node_enc dep n rest) as [later tail].
    cbn [fst] in Htarget, Hnode, Heq, IH |- *.
    now rewrite Heq, Htarget, Hnode, IH.
Qed.

Lemma audit_phi_component_cyclic_erases N E CN (EN : encoding N)
    (node_enc : N -> positive * list CN) (dep : Graph.t N (phi_dependency_edge N E))
    (prepared_dep : prepared EN dep) component :
  (forall x, fst (node_enc x) = encode EN x) ->
  fst (audit_phi_component_cyclic_counted EN node_enc dep prepared_dep component) =
    phi_component_cyclic EN dep prepared_dep component.
Proof.
  intro Henc.
  destruct component as [|n [|next rest]]; try reflexivity.
  unfold audit_phi_component_cyclic_counted, phi_component_cyclic, succ_edges, index_edges.
  pose proof (audit_map_get_erases N _ CN node_enc EN n (out_index prepared_dep) (Henc n)) as Hget.
  destruct (audit_map_get node_enc n (out_index prepared_dep)) as [found calls].
  cbn [fst] in Hget |- *.
  rewrite <- Hget.
  pose proof (audit_phi_cycle_self_edges_erases N E CN EN node_enc dep n
    (match found with
    | Some edges =>
      edges
    | None =>
      []
    end) Henc) as Hedges.
  destruct (audit_phi_cycle_self_edges node_enc dep n
    (match found with
    | Some edges =>
      edges
    | None =>
      []
    end)); exact Hedges.
Qed.

Lemma audit_phi_cycle_mark_erases N E CN (EN : encoding N)
    (node_enc : N -> positive * list CN) nodes :
  (forall x, fst (node_enc x) = encode EN x) ->
  forall marked, fst (@audit_phi_cycle_mark_nodes N E CN node_enc nodes marked) =
    fold_left (fun flags n => FinSet.add EN n flags) nodes marked.
Proof.
  intros Henc.
  induction nodes as [|n rest IH]; intro marked.
  - reflexivity.
  - cbn [audit_phi_cycle_mark_nodes fold_left].
    pose proof (audit_finset_add_erases N CN node_enc EN n marked (Henc n)) as Hadd.
    destruct (audit_finset_add node_enc n marked) as [next calls].
    specialize (IH next).
    destruct (@audit_phi_cycle_mark_nodes N E CN node_enc rest next).
    cbn [fst] in Hadd, IH |- *; now rewrite IH, Hadd.
Qed.

Lemma audit_phi_cycle_flags_from_erases N E CN (EN : encoding N)
    (node_enc : N -> positive * list CN) (dep : Graph.t N (phi_dependency_edge N E))
    (prepared_dep : prepared EN dep) components :
  (forall x, fst (node_enc x) = encode EN x) ->
  forall marked, fst (audit_phi_cycle_flags_from EN node_enc dep prepared_dep components marked) =
    fold_left (fun flags component =>
      if phi_component_cyclic EN dep prepared_dep component then
        fold_left (fun flags n => FinSet.add EN n flags) component flags
      else flags) components marked.
Proof.
  intro Henc.
  induction components as [|component rest IH]; intro marked.
  - reflexivity.
  - cbn [audit_phi_cycle_flags_from fold_left].
    pose proof (audit_phi_component_cyclic_erases N E CN EN node_enc dep prepared_dep component
      Henc) as Hcyclic.
    destruct (audit_phi_component_cyclic_counted EN node_enc dep prepared_dep component)
      as [cyclic cycle_events].
    cbn [fst] in Hcyclic; rewrite <- Hcyclic.
    destruct cyclic.
    + pose proof (audit_phi_cycle_mark_erases N E CN EN node_enc component Henc marked) as Hmark.
      destruct (@audit_phi_cycle_mark_nodes N E CN node_enc component marked) as [next events].
      specialize (IH next).
      destruct (audit_phi_cycle_flags_from EN node_enc dep prepared_dep rest next).
      cbn [fst] in Hmark, IH |- *; now rewrite IH, Hmark.
    + specialize (IH marked).
      destruct (audit_phi_cycle_flags_from EN node_enc dep prepared_dep rest marked).
      exact IH.
Qed.

(** Counted cycle classification and marking preserve the fixed plain flag set. *)
Theorem audit_phi_cycle_flags_erases : audit_phi_cycle_flags_erases_statement.
Proof.
  intros N E CN EN node_enc dep prepared_dep result Henc.
  apply audit_phi_cycle_flags_from_erases; exact Henc.
Qed.

(** * Output filters *)

Lemma audit_phi_output_keep_erases N E CN CV (EN : encoding N) (EE : encoding E)
    (node_enc : N -> positive * list CN)
    (version_enc : memory_version N E -> positive * list CV) reps nodes :
  (forall v, fst (version_enc v) = encode (memory_version_encoding EN EE) v) ->
  fst (audit_phi_output_keep_phis EN EE node_enc version_enc reps nodes) =
    filter (fun n => Pos.eqb (encode (memory_version_encoding EN EE) (MemoryPhi n))
      (encode (memory_version_encoding EN EE) (audit_phi_producer_rep EN EE reps (MemoryPhi n))))
      nodes.
Proof.
  intro Henc.
  induction nodes as [|n rest IH].
  - reflexivity.
  - cbn [audit_phi_output_keep_phis filter].
    pose proof (audit_map_get_erases _ _ CV version_enc (memory_version_encoding EN EE)
      (MemoryPhi n) reps (Henc (MemoryPhi n))) as Hget.
    destruct (audit_map_get version_enc (MemoryPhi n) reps) as [found reads].
    set (representative :=
      match found with
      | Some v =>
        v
      | None =>
        MemoryPhi n
      end).
    specialize (Henc (MemoryPhi n)) as Hleft; specialize (Henc representative) as Hright.
    destruct (version_enc (MemoryPhi n)) as [left_code left_body].
    destruct (version_enc representative) as [right_code right_body].
    pose proof (audit_positive_eqb_erases left_code right_code) as Hsame.
    destruct (audit_positive_eqb left_code right_code) as [same comparisons].
    destruct (audit_phi_output_keep_phis EN EE node_enc version_enc reps rest) as [kept events].
    cbn [fst] in Hget, Hleft, Hright, Hsame, IH |- *.
    unfold audit_phi_producer_rep.
    rewrite <- Hget.
    fold representative.
    rewrite <- Hleft, <- Hright, <- Hsame, IH.
    reflexivity.
Qed.

Lemma audit_phi_output_filter_nodes_erases N E CN CV (EN : encoding N)
    (node_enc : N -> positive * list CN) kept nodes :
  (forall n, fst (node_enc n) = encode EN n) ->
  fst (@audit_phi_output_filter_nodes N E CN CV node_enc kept nodes) =
    filter (fun n => FinSet.mem EN n kept) nodes.
Proof.
  intro Henc.
  induction nodes as [|n rest IH].
  - reflexivity.
  - cbn [audit_phi_output_filter_nodes filter].
    pose proof (audit_finset_mem_erases N CN node_enc EN n kept (Henc n)) as Hmem.
    destruct (audit_finset_mem node_enc n kept) as [found calls].
    destruct (@audit_phi_output_filter_nodes N E CN CV node_enc kept rest).
    cbn [fst] in Hmem, IH |- *; now rewrite Hmem, IH.
Qed.

Lemma audit_phi_output_filter_versions_erases N E CN CV (EN : encoding N)
    (node_enc : N -> positive * list CN)
    (version_enc : memory_version N E -> positive * list CV) kept versions :
  (forall n, fst (node_enc n) = encode EN n) ->
  fst (audit_phi_output_filter_versions node_enc version_enc kept versions) =
    filter (fun v =>
      match v with
      | MemoryPhi n =>
        FinSet.mem EN n kept
      | _ =>
        true
      end) versions.
Proof.
  intro Henc.
  induction versions as [|v rest IH].
  - reflexivity.
  - destruct v as [|n|e i]; cbn [audit_phi_output_filter_versions filter].
    + destruct (audit_phi_output_filter_versions node_enc version_enc kept rest).
      cbn [fst] in IH |- *; now rewrite IH.
    + pose proof (audit_finset_mem_erases N CN node_enc EN n kept (Henc n)) as Hmem.
      destruct (audit_finset_mem node_enc n kept) as [found calls].
      destruct (audit_phi_output_filter_versions node_enc version_enc kept rest).
      cbn [fst] in Hmem, IH |- *; now rewrite Hmem, IH.
    + destruct (audit_phi_output_filter_versions node_enc version_enc kept rest).
      cbn [fst] in IH |- *; now rewrite IH.
Qed.

(** Counted output construction returns the same complete memory graph, including closures. *)
Theorem audit_phi_output_counted_erases : audit_phi_output_counted_erases_statement.
Proof.
  intros N E CN CV EN EE node_enc version_enc old reps Hnode Hversion.
  unfold audit_phi_producer_output_counted, audit_phi_producer_output.
  pose proof (audit_phi_output_keep_erases N E CN CV EN EE node_enc version_enc reps
    (memory_phis old) Hversion) as Hkeep.
  destruct (audit_phi_output_keep_phis EN EE node_enc version_enc reps (memory_phis old))
    as [kept keep_events].
  pose proof (audit_finset_of_list_erases N CN node_enc EN kept (fun n _ => Hnode n)) as Hset.
  destruct (audit_finset_of_list node_enc kept) as [kept_set set_events].
  pose proof (audit_phi_output_filter_nodes_erases N E CN CV EN node_enc kept_set
    (memory_phis old) Hnode) as Hphis.
  destruct (@audit_phi_output_filter_nodes N E CN CV node_enc kept_set (memory_phis old))
    as [phis phi_events].
  pose proof (audit_phi_output_filter_versions_erases N E CN CV EN node_enc version_enc kept_set
    (memory_versions old) Hnode) as Hversions.
  destruct (audit_phi_output_filter_versions node_enc version_enc kept_set (memory_versions old))
    as [versions version_events].
  cbn [fst] in Hkeep, Hset, Hphis, Hversions |- *.
  now rewrite Hphis, Hversions, Hset, Hkeep.
Qed.

Lemma audit_phi_kept_set_stable N (EN : encoding N) (keep : N -> bool) nodes n :
  let kept := filter keep nodes in
  FinSet.mem EN n (FinSet.of_list EN
    (filter (fun node => FinSet.mem EN node (FinSet.of_list EN kept)) nodes)) =
    FinSet.mem EN n (FinSet.of_list EN kept).
Proof.
  cbn zeta.
  apply eq_true_iff_eq.
  rewrite !FinSet.of_list_spec, filter_In.
  split.
  - intros [_ Hmem]; now apply FinSet.of_list_spec in Hmem.
  - intro Hin; split.
    + apply filter_In in Hin; exact (proj1 Hin).
    + now apply FinSet.of_list_spec.
Qed.

(** Output inventories use the same stable retained-phi membership as their field construction. *)
Theorem audit_phi_producer_output_shape : audit_phi_producer_output_shape_statement.
Proof.
  intros N E EN EE old reps.
  unfold audit_phi_producer_output; cbn [memory_phis memory_versions memory_in memory_out
    memory_before memory_operand].
  split; [reflexivity|].
  split.
  - apply filter_ext.
    intros [|n|e i]; try reflexivity.
    symmetry; apply audit_phi_kept_set_stable.
  - split; [reflexivity|].
    split; [reflexivity|].
    split; [reflexivity|].
    intros n key.
    rewrite audit_phi_kept_set_stable.
    reflexivity.
Qed.

(** * Actual ordered producer phases *)

Lemma audit_phi_dependency_entries_erases N E CN n row :
  fst (@audit_phi_dependency_row_entries N E CN n row) =
    flat_map (fun kv =>
      match snd kv with
      | MemoryPhi target =>
        [PhiDependencyEdgeData n (fst kv) target]
      | _ =>
        []
      end) row.
Proof.
  induction row as [|[key v] rest IH].
  - reflexivity.
  - cbn [audit_phi_dependency_row_entries flat_map fst snd].
    destruct (@audit_phi_dependency_row_entries N E CN n rest).
    cbn [fst] in IH |- *.
    destruct v; cbn; now rewrite IH.
Qed.

Lemma audit_phi_dependency_row_erases N E CN (EN : encoding N)
    (node_enc : N -> positive * list CN) inputs n :
  (forall node, fst (node_enc node) = encode EN node) ->
  fst (@audit_phi_dependency_row N E CN node_enc inputs n) =
    flat_map (fun kv =>
      match snd kv with
      | MemoryPhi target =>
        [PhiDependencyEdgeData n (fst kv) target]
      | _ =>
        []
      end) (index_edges EN inputs n).
Proof.
  intro Hnode.
  unfold audit_phi_dependency_row, index_edges.
  pose proof (audit_map_get_erases N _ CN node_enc EN n inputs (Hnode n)) as Hget.
  destruct (audit_map_get node_enc n inputs) as [found calls].
  cbn [fst] in Hget; rewrite <- Hget.
  pose proof (audit_phi_dependency_entries_erases N E CN n
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
    end)); exact Hentries.
Qed.

Lemma audit_phi_dependency_graph_erases N E CN (EN : encoding N)
    (node_enc : N -> positive * list CN) mg inputs :
  (forall node, fst (node_enc node) = encode EN node) ->
  let '(dep, rows, events) := @audit_phi_dependency_graph_counted N E CN EN node_enc mg inputs in
  dep = phi_dependency_graph_from_inputs EN mg inputs /\
    rows = phi_dependency_rows_from_inputs EN mg inputs.
Proof.
  intro Hnode.
  unfold audit_phi_dependency_graph_counted, audit_phi_dependency_rows_counted.
  pose proof (audit_memory_result_index_erases N _ CN _ node_enc EN
    (audit_phi_dependency_row node_enc inputs)
    (fun n => flat_map (fun kv =>
      match snd kv with
      | MemoryPhi target =>
        [PhiDependencyEdgeData n (fst kv) target]
      | _ =>
        []
      end) (index_edges EN inputs n)) (memory_phis mg)
    (fun n _ => Hnode n) (fun n _ => audit_phi_dependency_row_erases N E CN EN node_enc inputs
      n Hnode)) as Hrows.
  destruct (audit_memory_result_index node_enc (audit_phi_dependency_row node_enc inputs)
    (memory_phis mg)) as [rows events].
  cbn [fst] in Hrows |- *.
  change (rows = phi_dependency_rows_from_inputs EN mg inputs) in Hrows.
  rewrite Hrows; split; reflexivity.
Qed.

Lemma audit_phi_prepare_callbacks_erases N E CN (EN : encoding N)
    (node_enc : N -> positive * list CN) (dep : Graph.t N (phi_dependency_edge N E)) rows :
  (forall node, fst (node_enc node) = encode EN node) ->
  (forall node, index_edges EN rows node = Graph.out dep node) ->
  audit_prepare_callbacks_erase EN dep (audit_phi_prepare_callbacks node_enc rows dep).
Proof.
  intros Hnode Hrows.
  split.
  - intro n.
    unfold audit_phi_prepare_callbacks; cbn [audit_prepare_out_model].
    pose proof (audit_map_get_erases N _ CN node_enc EN n rows (Hnode n)) as Hget.
    destruct (audit_map_get node_enc n rows); cbn [fst] in Hget |- *.
    rewrite Hget; apply Hrows.
  - split; [reflexivity|].
    intro n.
    unfold audit_phi_prepare_callbacks; cbn [audit_prepare_encode_model].
    specialize (Hnode n).
    destruct (node_enc n); exact Hnode.
Qed.

Lemma audit_phi_scc_callbacks_erases N E CN (EN : encoding N)
    (node_enc : N -> positive * list CN) (dep : Graph.t N (phi_dependency_edge N E)) :
  (forall node, fst (node_enc node) = encode EN node) ->
  audit_dfs_callbacks_erase EN dep (audit_phi_scc_callbacks node_enc dep).
Proof.
  intro Hnode.
  split; [reflexivity|].
  intro n.
  unfold audit_phi_scc_callbacks; cbn [audit_dfs_encode_model].
  specialize (Hnode n).
  destruct (node_enc n); exact Hnode.
Qed.

Lemma audit_phi_producer_index_erases N E T CN CE PE OE CV (EN : encoding N) (EE : encoding E)
    (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
    (pred : N -> list E * list PE)
    (operand : N -> option E -> option (memory_version N E) * list OE)
    (version_enc : memory_version N E -> positive * list CV) g
    (effects : E -> list (ViewsMemoryEffects.memory_effect T)) mg :
  (forall n, fst (node_enc n) = encode EN n) ->
  (forall e, fst (edge_enc e) = encode EE e) ->
  (forall n, fst (pred n) = pred_edges (prepare EN g) n) ->
  (forall n key, fst (operand n key) = memory_operand mg n key) ->
  audit_phi_run_index EN (audit_phi_produce EN EE node_enc edge_enc pred operand version_enc
    g effects mg) = phi_prepare_dependencies EN EE g effects mg.
Proof.
  intros Hnode Hedge Hpred Hoperand.
  unfold audit_phi_produce.
  pose proof (audit_phi_input_rows_erases N E T CN CE PE OE EN EE g effects mg node_enc edge_enc
    pred operand Hnode Hedge Hpred Hoperand) as Hinputs.
  destruct (audit_phi_input_rows node_enc edge_enc pred operand (memory_phis mg))
    as [inputs row_events]; cbn [fst] in Hinputs.
  pose proof (audit_phi_dependency_graph_erases N E CN EN node_enc mg inputs Hnode) as Hdeps.
  destruct (audit_phi_dependency_graph_counted EN node_enc mg inputs) as [[dep rows] deps].
  destruct Hdeps as [Hdep Hrows].
  assert (Hcallbacks : audit_prepare_callbacks_erase EN dep
    (audit_phi_prepare_callbacks node_enc rows dep)).
  { apply audit_phi_prepare_callbacks_erases; [exact Hnode|].
    intro n; rewrite Hrows, Hdep; reflexivity. }
  pose proof (audit_prepare_source_correct N _ _ EN dep
    (audit_phi_prepare_callbacks node_enc rows dep) (fun _ => 0) Hcallbacks) as Hprepare.
  destruct (audit_prepare_source_counted EN dep (audit_phi_prepare_callbacks node_enc rows dep))
    as [prep preparation].
  destruct Hprepare as [Hprep _].
  pose proof (audit_scc_source_correct N _ _ EN dep prep (audit_phi_scc_callbacks node_enc dep)
    (fun _ => 0) (Graph.nodes dep) (audit_phi_scc_callbacks_erases N E CN EN node_enc dep Hnode))
    as Hcomponents.
  destruct (audit_scc_source_counted prep (audit_phi_scc_callbacks node_enc dep) (Graph.nodes dep))
    as [result scc_events].
  destruct Hcomponents as [Hresult _].
  pose proof (audit_phi_cycle_flags_erases N E CN EN node_enc dep prep result Hnode) as Hcycles.
  destruct (audit_phi_cycle_flags_counted EN node_enc dep prep result) as [cycles cycle_events].
  destruct (audit_phi_resolve_all EN node_enc version_enc
    (PhiDependencyIndex inputs dep prep result cycles) (concat (components result)) Map.empty)
    as [reps resolution].
  destruct (audit_phi_producer_output_counted EN EE node_enc version_enc mg reps).
  cbn [fst] in Hcycles |- *.
  subst cycles result prep rows dep inputs.
  reflexivity.
Qed.

(** The captured index uses the same input rows, dependency graph, preparation, SCCs and flags. *)
Theorem audit_phi_producer_index_source : audit_phi_producer_index_source_statement.
Proof.
  intros N E T CN CE PE OE CV EN EE node_enc edge_enc pred operand version_enc g effects mg
    Hnode Hedge Hpred Hoperand Hversion.
  cbn zeta.
  rewrite (audit_phi_producer_index_erases N E T CN CE PE OE CV EN EE node_enc edge_enc pred
    operand version_enc g effects mg Hnode Hedge Hpred Hoperand).
  split; [reflexivity|].
  split; [reflexivity|].
  split; reflexivity.
Qed.

Lemma audit_phi_producer_value_shape N E T CN CE PE OE CV (EN : encoding N) (EE : encoding E)
    (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
    (pred : N -> list E * list PE)
    (operand : N -> option E -> option (memory_version N E) * list OE)
    (version_enc : memory_version N E -> positive * list CV) g
    (effects : E -> list (ViewsMemoryEffects.memory_effect T)) mg :
  let run := audit_phi_produce EN EE node_enc edge_enc pred operand version_enc g effects mg in
  audit_phi_run_order EN run = concat (components (phi_index_scc (audit_phi_run_index EN run))) /\
  audit_phi_run_representatives EN run = fst (audit_phi_resolve_all EN node_enc version_enc
    (audit_phi_run_index EN run) (audit_phi_run_order EN run) Map.empty) /\
  audit_phi_run_output EN run = fst (audit_phi_producer_output_counted EN EE node_enc version_enc
    mg (audit_phi_run_representatives EN run)).
Proof.
  unfold audit_phi_produce.
  destruct (audit_phi_input_rows node_enc edge_enc pred operand (memory_phis mg))
    as [inputs rows].
  destruct (audit_phi_dependency_graph_counted EN node_enc mg inputs) as [[dep indexed] deps].
  destruct (audit_prepare_source_counted EN dep (audit_phi_prepare_callbacks node_enc indexed dep))
    as [prep preparation].
  destruct (audit_scc_source_counted prep (audit_phi_scc_callbacks node_enc dep) (Graph.nodes dep))
    as [result scc_events].
  destruct (audit_phi_cycle_flags_counted EN node_enc dep prep result) as [cycles cycle_events].
  destruct (audit_phi_resolve_all EN node_enc version_enc
    (PhiDependencyIndex inputs dep prep result cycles) (concat (components result)) Map.empty)
    as [reps resolution] eqn:Hresolution.
  destruct (audit_phi_producer_output_counted EN EE node_enc version_enc mg reps)
    as [output output_events] eqn:Houtput.
  cbn [audit_phi_run_index audit_phi_run_order audit_phi_run_representatives audit_phi_run_output
    phi_index_scc].
  rewrite Hresolution, Houtput.
  split; [reflexivity|].
  split; reflexivity.
Qed.

(** The producer's returned representative map follows the actual complete resolution trace. *)
Theorem audit_phi_producer_resolution : audit_phi_producer_resolution_statement.
Proof.
  intros N E T CN CE PE OE CV EN EE node_enc edge_enc pred operand version_enc g effects mg
    Hnode Hversion.
  unfold audit_phi_produce.
  destruct (audit_phi_input_rows node_enc edge_enc pred operand (memory_phis mg))
    as [inputs rows].
  destruct (audit_phi_dependency_graph_counted EN node_enc mg inputs) as [[dep indexed] deps].
  destruct (audit_prepare_source_counted EN dep (audit_phi_prepare_callbacks node_enc indexed dep))
    as [prep preparation].
  destruct (audit_scc_source_counted prep (audit_phi_scc_callbacks node_enc dep) (Graph.nodes dep))
    as [result scc_events].
  destruct (audit_phi_cycle_flags_counted EN node_enc dep prep result) as [cycles cycle_events].
  set (index := PhiDependencyIndex inputs dep prep result cycles).
  pose proof (audit_phi_resolve_all_refines N E CN CV EN EE index node_enc version_enc
    (concat (components result)) Map.empty Hnode Hversion) as Htrace.
  destruct (audit_phi_resolve_all EN node_enc version_enc index (concat (components result))
    Map.empty) as [reps resolution].
  destruct (audit_phi_producer_output_counted EN EE node_enc version_enc mg reps).
  exact Htrace.
Qed.

(** The actual producer retains exactly its five preparation phase receipts. *)
Theorem audit_phi_producer_phase_counts : audit_phi_producer_phase_counts_statement.
Proof.
  intros N E T CN CE PE OE CV EN EE node_enc edge_enc pred operand version_enc g effects mg.
  unfold audit_phi_produce.
  destruct (audit_phi_input_rows node_enc edge_enc pred operand (memory_phis mg))
    as [inputs rows].
  destruct (audit_phi_dependency_graph_counted EN node_enc mg inputs) as [[dep indexed] deps].
  destruct (audit_prepare_source_counted EN dep (audit_phi_prepare_callbacks node_enc indexed dep))
    as [prep preparation].
  destruct (audit_scc_source_counted prep (audit_phi_scc_callbacks node_enc dep) (Graph.nodes dep))
    as [result scc_events].
  destruct (audit_phi_cycle_flags_counted EN node_enc dep prep result) as [cycles cycle_events].
  destruct (audit_phi_resolve_all EN node_enc version_enc
    (PhiDependencyIndex inputs dep prep result cycles) (concat (components result)) Map.empty)
    as [reps resolution].
  destruct (audit_phi_producer_output_counted EN EE node_enc version_enc mg reps).
  reflexivity.
Qed.
