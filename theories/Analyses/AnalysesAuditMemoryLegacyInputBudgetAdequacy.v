(** * Adequacy of legacy checker input budgets

    Input budgets bound the original callback bodies and intermediate indexed rows.
    For example, each repeated target is still charged during adjacency construction.
    Builds on: legacy CFG and shared memory budget adequacy. *)

From Stdlib Require Import List PArith Arith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditFinSet CollectionsAuditMap CollectionsAuditMapAdequacy CollectionsAuditPrimitive
  CollectionsAuditPrimitiveAdequacy.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphAuditBase
  GraphAuditBaseAdequacy GraphAuditDfs
  GraphAuditDfsAdequacy.
From Galois.Domains Require Import DomainsFootprint.
From Galois.Analyses Require Import AnalysesAuditMemoryDistinct AnalysesAuditMemoryDistinctAdequacy
  AnalysesAuditMemoryIndex AnalysesAuditMemorySharedBudget AnalysesAuditMemorySharedBudgetAdequacy
  AnalysesAuditMemoryLegacyCfg AnalysesAuditMemoryLegacyCfgAdequacy
  AnalysesMemoryLegacy AnalysesAuditMemoryLegacyChecker AnalysesAuditMemoryLegacySuccessor
  AnalysesAuditMemoryLegacyOverlap AnalysesAuditMemoryLegacySlice
  AnalysesAuditMemoryLegacySliceAdequacy AnalysesAuditMemoryGraphCallbacks
  AnalysesAuditMemoryWalkIndex AnalysesAuditMemoryWalkIndexAdequacy
  AnalysesAuditMemoryLegacySliceFull AnalysesAuditMemoryLegacySliceFullAdequacy
  AnalysesAuditMemoryLegacyNoClobber AnalysesAuditMemoryLegacyNoClobberAdequacy
  AnalysesAuditMemoryLegacyInputBudget.
Import List.ListNotations.

(** * Normalized adjacency input budget *)

(** Row work distributes over consecutive event sequences. *)
Lemma audit_legacy_cfg_row_work_app N E CN OE TE node_work out_work target_work
    (left right : list (audit_legacy_cfg_event N E CN OE TE)) :
    audit_legacy_cfg_row_work node_work out_work target_work (left ++ right) =
      audit_legacy_cfg_row_work node_work out_work target_work left +
      audit_legacy_cfg_row_work node_work out_work target_work right.
Proof.
  induction left as [|event rest IH].
  - reflexivity.
  - destruct event; cbn; rewrite IH; lia.
Qed.

(** Target callbacks fit their per-edge input budget. *)
Lemma audit_legacy_targets_input_bound N E CN OE TE (target : E -> N * list TE)
    node_work out_work target_work target_budget node edges :
    (forall e, target_work (snd (target e)) <= target_budget e) ->
    audit_legacy_cfg_row_work node_work out_work target_work
      (snd (@audit_legacy_cfg_targets N E CN OE TE target node edges)) <=
    audit_legacy_targets_input_budget target target_budget edges.
Proof.
  intro Hwork; induction edges as [|edge rest IH].
  - reflexivity.
  - cbn [audit_legacy_cfg_targets audit_legacy_targets_input_budget].
    specialize (Hwork edge) as Hedge.
    destruct (target edge) as [result calls].
    destruct (audit_legacy_cfg_targets target node rest) as [tail events]; cbn in *; lia.
Qed.

(** Pair construction costs two units for its terminal frame and four per target. *)
Lemma audit_legacy_cfg_pairs_work N E CN OE TE node_work out_work target_work node targets :
    audit_legacy_cfg_row_work node_work out_work target_work
      (snd (@audit_legacy_cfg_pairs N E CN OE TE node targets)) = 2 + 4 * length targets.
Proof.
  induction targets as [|target rest IH].
  - reflexivity.
  - cbn [audit_legacy_cfg_pairs].
    destruct (audit_legacy_cfg_pairs node rest) as [tail events]; cbn in *; lia.
Qed.

(** Stable distinctness never returns more elements than it receives. *)
Lemma audit_legacy_distinct_length N CN (enc : N -> positive * list CN) seen keys :
    length (fst (audit_memory_distinct_from enc seen keys)) <= length keys.
Proof.
  revert seen; induction keys as [|key rest IH]; intro seen.
  - reflexivity.
  - cbn [audit_memory_distinct_from].
    destruct (audit_finset_mem enc key seen) as [found probes].
    destruct found.
    + specialize (IH seen).
      destruct (audit_memory_distinct_from enc seen rest); cbn in *; lia.
    + destruct (audit_finset_add enc key seen) as [next adds].
      specialize (IH next).
      destruct (audit_memory_distinct_from enc next rest); cbn in *; lia.
Qed.

(** A normalized row is bounded by target, distinctness and pair-construction input costs. *)
Lemma audit_legacy_cfg_row_input_bound N E CN OE TE (EN : encoding N)
    (node_enc : N -> positive * list CN) (out : N -> list E * list OE)
    (target : E -> N * list TE) node_work out_work target_work node_budget out_budget
    target_budget node :
    (forall n, node_work (snd (node_enc n)) <= node_budget n) ->
    (forall n, out_work (snd (out n)) <= out_budget n) ->
    (forall e, target_work (snd (target e)) <= target_budget e) ->
    audit_legacy_cfg_row_work node_work out_work target_work
      (snd (audit_legacy_cfg_row EN node_enc out target node)) <=
      audit_legacy_cfg_row_input_budget node_enc out target node_budget out_budget
        target_budget node.
Proof.
  intros Hnode Hout Htarget.
  pose proof (Hout node) as Hout_work.
  pose proof (audit_legacy_targets_input_bound N E CN OE TE target node_work out_work target_work
    target_budget node (fst (out node)) Htarget) as Htarget_work.
  pose proof (audit_legacy_cfg_targets_erases N E CN OE TE target node (fst (out node)))
    as Htargets.
  unfold audit_legacy_cfg_row, audit_legacy_cfg_row_input_budget.
  destruct (out node) as [edges out_calls]; cbn in *.
  destruct (audit_legacy_cfg_targets target node edges) as [targets target_events]; cbn in *.
  pose proof (audit_memory_distinct_source_bound N CN node_enc node_work FinSet.empty targets)
    as Hdistinct_work.
  pose proof (audit_memory_distinct_budget_input N CN node_enc node_work node_budget targets Hnode)
    as Hdistinct_budget.
  pose proof (audit_legacy_distinct_length N CN node_enc FinSet.empty targets) as Hlength.
  unfold audit_memory_distinct in *.
  destruct (audit_memory_distinct_from node_enc FinSet.empty targets) as [distinct distinct_events];
    cbn in *.
  pose proof (audit_legacy_cfg_pairs_work N E CN OE TE node_work out_work target_work node distinct)
    as Hpair_work.
  destruct (audit_legacy_cfg_pairs node distinct) as [pairs pair_events]; cbn in *.
  rewrite !audit_legacy_cfg_row_work_app; cbn [audit_legacy_cfg_row_work].
  rewrite Htargets, length_map in Hlength.
  rewrite Htargets in Hdistinct_work, Hdistinct_budget.
  rewrite length_map.
  lia.
Qed.

(** Callback budgets bound construction of every indexed adjacency row. *)
Theorem audit_legacy_cfg_whole_input_bound : audit_legacy_cfg_whole_input_bound_statement.
Proof.
  intros N E CN OE TE EN node_enc out target node_work out_work target_work node_budget out_budget
    target_budget g Hnode Hout Htarget.
  pose proof (audit_legacy_cfg_source_bound N E CN OE TE EN node_enc out target g
    node_work out_work target_work) as Hsource.
  pose proof (audit_memory_index_budget_input N (list (N * N)) CN
    (audit_legacy_cfg_event N E CN OE TE) node_enc (audit_legacy_cfg_row EN node_enc out target)
    node_work (audit_legacy_cfg_row_work node_work out_work target_work) node_budget
    (audit_legacy_cfg_row_input_budget node_enc out target node_budget out_budget target_budget)
    (Graph.nodes g) Hnode
    (fun n => audit_legacy_cfg_row_input_bound N E CN OE TE EN node_enc out target node_work
      out_work target_work node_budget out_budget target_budget n Hnode Hout Htarget)) as Hbudget.
  unfold audit_legacy_cfg_input_budget; lia.
Qed.

(** * DFS callback input budget *)

(** The sum of vertex charges bounds the charge of each listed occurrence. *)
Lemma audit_legacy_sum_vertex_member N (budget : N -> nat) nodes node :
    In node nodes -> budget node <= audit_legacy_sum_vertex_budget budget nodes.
Proof.
  induction nodes as [|head rest IH]; cbn.
  - contradiction.
  - intros [Heq|Hin].
    + subst head; lia.
    + specialize (IH Hin); lia.
Qed.

(** An encoder capture pays at most the budget of its actual node. *)
Lemma audit_legacy_dfs_encode_body_bound N E CN (node_enc : N -> positive * list CN)
    (g : Graph.t N E) node_work node_budget node code body :
    (forall n, node_work (snd (node_enc n)) <= node_budget n) ->
    audit_dfs_capture_receipt (audit_legacy_dfs_callbacks node_enc g)
      (AuditGraphEncodeCapture N E (list CN) node code body) ->
    audit_graph_capture_work node_work (AuditGraphEncodeCapture N E (list CN) node code body) <=
      node_budget node.
Proof.
  intros Hbudget Hreceipt.
  cbn [audit_dfs_capture_receipt audit_legacy_dfs_callbacks] in Hreceipt.
  change ((let '(actual, trace) := node_enc node in (actual, [trace])) = (code, body))
    in Hreceipt.
  specialize (Hbudget node).
  destruct (node_enc node) as [actual trace]; cbn in Hbudget, Hreceipt.
  inversion Hreceipt; subst; cbn [snd audit_graph_capture_work fold_right].
  lia.
Qed.

(** One encoder capture is bounded by the sum over an envelope containing its node. *)
Lemma audit_legacy_dfs_encoded_event_bound N E CN (node_enc : N -> positive * list CN)
    (g : Graph.t N E) node_work node_budget vertices node code trace :
    (forall n, node_work (snd (node_enc n)) <= node_budget n) ->
    In node vertices ->
    audit_dfs_capture_receipt (audit_legacy_dfs_callbacks node_enc g)
      (AuditGraphEncodeCapture N E (list CN) node code trace) ->
    fold_right (fun capture k => audit_graph_capture_work node_work capture + k) 0
      [AuditGraphEncodeCapture N E (list CN) node code trace] <=
      1 + audit_legacy_sum_vertex_budget node_budget vertices.
Proof.
  intros Hbudget Hmember Hreceipt.
  pose proof (audit_legacy_dfs_encode_body_bound N E CN node_enc g node_work node_budget
    node code trace Hbudget Hreceipt) as Hbody.
  pose proof (audit_legacy_sum_vertex_member N node_budget vertices node Hmember) as Hnode.
  cbn [fold_right]; lia.
Qed.

(** A captured DFS event charges at most one node budget within its vertex envelope. *)
Lemma audit_legacy_dfs_event_body_bound N E CN (node_enc : N -> positive * list CN)
    (g : Graph.t N E) node_work node_budget vertices
    (item : audit_dfs_nested_event N E (audit_graph_callback_capture N E (list CN))) :
    (forall n, node_work (snd (node_enc n)) <= node_budget n) ->
    audit_dfs_source_event_wellformed item ->
    audit_dfs_event_receipts (audit_legacy_dfs_callbacks node_enc g) item ->
    audit_dfs_full_event_keys vertices (fst item) ->
    fold_right (fun capture k => audit_graph_capture_work node_work capture + k) 0 (snd item) <=
      1 + audit_legacy_sum_vertex_budget node_budget vertices.
Proof.
  intros Hbudget Hshape Hreceipts Hkeys.
  destruct item as [event body].
  destruct event as [site|edge value|node set found|node index found|node via before after|
    node before after|detail|pre post];
    cbn [audit_dfs_source_event_wellformed audit_dfs_full_event_keys fst snd] in Hshape, Hkeys.
  - subst body; cbn; lia.
  - destruct Hshape as [trace Hshape]; subst body.
    inversion Hreceipts as [|capture rest Hreceipt Htail]; subst.
    change ((Graph.target g edge, @nil (list CN)) = (value, trace)) in Hreceipt.
    inversion Hreceipt; subst; cbn [snd audit_graph_capture_work fold_right]; lia.
  - destruct Hshape as [code [trace Hshape]]; subst body.
    inversion Hreceipts as [|capture rest Hreceipt Htail]; subst.
    apply (audit_legacy_dfs_encoded_event_bound N E CN node_enc g node_work node_budget
      vertices node code trace Hbudget Hkeys Hreceipt).
  - destruct Hshape as [code [trace Hshape]]; subst body.
    inversion Hreceipts as [|capture rest Hreceipt Htail]; subst.
    apply (audit_legacy_dfs_encoded_event_bound N E CN node_enc g node_work node_budget
      vertices node code trace Hbudget Hkeys Hreceipt).
  - subst body; cbn; lia.
  - subst body; cbn; lia.
  - destruct detail as [node edge index|node number index|node set|before after];
      cbn [audit_dfs_source_event_wellformed audit_dfs_full_event_keys] in Hshape, Hkeys.
    + destruct Hshape as [code [trace Hshape]]; subst body.
      inversion Hreceipts as [|capture rest Hreceipt Htail]; subst.
      apply (audit_legacy_dfs_encoded_event_bound N E CN node_enc g node_work node_budget
        vertices node code trace Hbudget Hkeys Hreceipt).
    + destruct Hshape as [code [trace Hshape]]; subst body.
      inversion Hreceipts as [|capture rest Hreceipt Htail]; subst.
      apply (audit_legacy_dfs_encoded_event_bound N E CN node_enc g node_work node_budget
        vertices node code trace Hbudget Hkeys Hreceipt).
    + destruct Hshape as [code [trace Hshape]]; subst body.
      inversion Hreceipts as [|capture rest Hreceipt Htail]; subst.
      apply (audit_legacy_dfs_encoded_event_bound N E CN node_enc g node_work node_budget
        vertices node code trace Hbudget Hkeys Hreceipt).
    + subst body; cbn; lia.
  - subst body; cbn; lia.
Qed.

(** Enlarging a vertex envelope preserves each full DFS event's key condition. *)
Lemma audit_legacy_dfs_event_keys_mono N E (small large : list N) (event : audit_dfs_full_call N E)
    :
    incl small large -> audit_dfs_full_event_keys small event ->
      audit_dfs_full_event_keys large event.
Proof.
  intros Hincl Hkeys; destruct event as [site|edge value|node set found|node index found|
    node via before after|node before after|detail|pre post];
    cbn [audit_dfs_full_event_keys] in *; try exact I;
    try (apply Hincl; exact Hkeys).
  destruct detail; cbn [audit_dfs_full_event_keys] in *; auto.
Qed.

(** Both the result and callback bodies of a DFS fit the original vertex budget. *)
Lemma audit_legacy_dfs_input_bound N E CN (EN : encoding N) (g : Graph.t N E)
    (p : prepared EN g) (node_enc : N -> positive * list CN) node_work node_budget roots :
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall n, node_work (snd (node_enc n)) <= node_budget n) ->
    audit_dfs_source_work node_work
      (snd (audit_dfs_source_counted p (audit_legacy_dfs_callbacks node_enc g)
        FinSet.empty roots)) <=
      audit_legacy_dfs_input_budget EN g p node_budget roots.
Proof.
  intros Hnode Hbudget.
  set (cb := audit_legacy_dfs_callbacks node_enc g).
  assert (Hcallbacks : audit_dfs_callbacks_erase EN g cb).
  { unfold cb; apply audit_legacy_dfs_callbacks_erases; exact Hnode. }
  pose proof (audit_dfs_source_correct N E (list CN) EN g p cb node_work FinSet.empty roots
    Hcallbacks) as Hsource.
  pose proof (audit_dfs_source_erases p cb FinSet.empty roots Hcallbacks) as Herases.
  pose proof (audit_dfs_full_counted_keys p FinSet.empty roots) as Hkeys.
  pose proof (audit_dfs_source_receipts p cb FinSet.empty roots) as Hreceipts.
  destruct (audit_dfs_source_counted p cb FinSet.empty roots) as [result events] eqn:Hdfs;
    cbn in Hsource, Herases, Hreceipts.
  destruct Hsource as [_ [Hshape [Hcount Hwork]]].
  rewrite <- Herases in Hkeys; cbn in Hkeys; apply Forall_map in Hkeys.
  set (vertices := audit_legacy_dfs_vertices g (out_index p) roots).
  assert (Hincl : incl
      (roots ++ map (Graph.target g) (flat_map snd (Map.elements (out_index p)))) vertices).
  { unfold vertices, audit_legacy_dfs_vertices.
    intros node Hin; apply in_app_iff in Hin as [Hroot|Htarget]; apply in_app_iff.
    - left; exact Hroot.
    - right; apply in_app_iff; right; exact Htarget. }
  assert (Hbody : audit_dfs_source_body_work node_work events <=
      length events * (1 + audit_legacy_sum_vertex_budget node_budget vertices)).
  { unfold audit_dfs_source_body_work.
    clear Hwork Hcount Herases Hdfs result.
    induction events as [|item rest IH].
    - cbn; lia.
    - inversion Hshape as [|? ? Hitem Hshape_tail]; subst.
      inversion Hreceipts as [|? ? Hreceipt Hreceipt_tail]; subst.
      inversion Hkeys as [|? ? Hkey Hkeys_tail]; subst.
      specialize (IH Hshape_tail Hkeys_tail Hreceipt_tail).
      pose proof (audit_legacy_dfs_event_keys_mono N E _ vertices (fst item) Hincl Hkey)
        as Henvelope.
      pose proof (audit_legacy_dfs_event_body_bound N E CN node_enc g node_work node_budget vertices
        item Hbudget Hitem Hreceipt Henvelope) as Hitem_bound.
      cbn [fold_right length Nat.mul]; lia. }
  unfold audit_legacy_dfs_input_budget; fold vertices.
  change (audit_dfs_source_work node_work events <= audit_dfs_source_budget EN g p roots +
    audit_dfs_source_body_work node_work events) in Hwork.
  eapply Nat.le_trans; [exact Hwork|].
  apply Nat.add_le_mono_l.
  eapply Nat.le_trans; [exact Hbody|].
  apply Nat.mul_le_mono_r; exact Hcount.
Qed.

(** * Slice input budgets *)

(** Site callback budgets bound one row of footprint comparisons. *)
Lemma audit_legacy_overlap_inner_input_bound T CT (site_enc : T -> positive * list CT)
    site_work site_budget left right :
    (forall t, site_work (snd (site_enc t)) <= site_budget t) ->
    audit_legacy_overlap_inner_budget site_enc site_work left right <=
      audit_legacy_overlap_row_input_budget site_enc site_budget left right.
Proof.
  intro Hsite; induction right as [|item rest IH].
  - reflexivity.
  - cbn [audit_legacy_overlap_inner_budget audit_legacy_overlap_row_input_budget].
    pose proof (Hsite (DomainsFootprint.fp_site left)) as Hleft.
    pose proof (Hsite (DomainsFootprint.fp_site item)) as Hitem.
    lia.
Qed.

(** Site budgets bound all footprint comparisons in their original order. *)
Lemma audit_legacy_overlap_input_bound T CT (site_enc : T -> positive * list CT)
    site_work site_budget left right :
    (forall t, site_work (snd (site_enc t)) <= site_budget t) ->
    audit_legacy_overlap_budget site_enc site_work left right <=
      audit_legacy_overlap_input_budget site_enc site_budget left right.
Proof.
  intro Hsite; induction left as [|item rest IH].
  - reflexivity.
  - cbn [audit_legacy_overlap_budget audit_legacy_overlap_input_budget].
    pose proof (audit_legacy_overlap_inner_input_bound T CT site_enc site_work site_budget item
      right Hsite) as Hinner; lia.
Qed.

(** The membership and map observers make the same decision on the same encoded key. *)
Lemma audit_legacy_mem_is_map N CN (enc : N -> positive * list CN) node set :
    fst (audit_finset_mem enc node set) =
      match fst (audit_map_get enc node set) with
      | Some _ => true
      | None => false
      end.
Proof.
  unfold audit_finset_mem, audit_map_get.
  destruct (enc node) as [code events].
  destruct (CollectionsAuditTrie.audit_map_code_get code set) as [found calls].
  destruct found; reflexivity.
Qed.

(** Node and site budgets bound every membership and selected write in the same scan. *)
Lemma audit_legacy_slice_nodes_input_bound N T CN CT W (node_enc : N -> positive * list CN)
    (site_enc : T -> positive * list CT) (writes : N -> list (footprint T) * list W)
    node_work site_work writes_work node_budget site_budget writes_budget read forward backward
    nodes :
    (forall n, node_work (snd (node_enc n)) <= node_budget n) ->
    (forall t, site_work (snd (site_enc t)) <= site_budget t) ->
    (forall n, writes_work (snd (writes n)) <= writes_budget n) ->
    audit_legacy_slice_budget node_enc site_enc writes node_work site_work writes_work
      read forward backward nodes <=
    audit_legacy_slice_nodes_input_budget node_enc site_enc writes node_budget site_budget
      writes_budget read forward backward nodes.
Proof.
  intros Hnode Hsite Hwrites; induction nodes as [|node rest IH].
  - reflexivity.
  - cbn [audit_legacy_slice_budget audit_legacy_slice_nodes_input_budget].
    pose proof (audit_memory_distinct_mem_bound N CN node_enc node_work node forward) as Hforward.
    pose proof (audit_memory_distinct_mem_bound N CN node_enc node_work node backward) as Hbackward.
    pose proof (audit_legacy_mem_is_map N CN node_enc node forward) as Hforward_map.
    pose proof (audit_legacy_mem_is_map N CN node_enc node backward) as Hbackward_map.
    pose proof (Hnode node) as Hnode_work.
    pose proof (Hwrites node) as Hwrite.
    pose proof (audit_legacy_overlap_input_bound T CT site_enc site_work site_budget
      (fst (writes node)) read Hsite) as Hoverlap.
    destruct (audit_finset_mem node_enc node forward) as [f fe].
    destruct (audit_finset_mem node_enc node backward) as [b be]; cbn in *.
    rewrite <- Hforward_map, <- Hbackward_map.
    unfold audit_walk_predecessor_input_budget.
    destruct (andb f b); cbn; lia.
Qed.

(** Two DFS walks and the selected node checks fit the full-slice input budget. *)
Lemma audit_legacy_slice_full_input_bound N E T CN CT W (EN : encoding N) (ET : encoding T)
    (node_enc : N -> positive * list CN) (site_enc : T -> positive * list CT)
    (g : Graph.t N E) (p : prepared EN g)
    (writes : N -> list (footprint T) * list W)
    node_work site_work writes_work node_budget site_budget writes_budget read roots load :
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall n, node_work (snd (node_enc n)) <= node_budget n) ->
    (forall t, site_work (snd (site_enc t)) <= site_budget t) ->
    (forall n, writes_work (snd (writes n)) <= writes_budget n) ->
    audit_legacy_slice_full_source_work EN node_work site_work writes_work
      (snd (audit_legacy_slice_full EN ET node_enc site_enc g p writes read roots load)) <=
    audit_legacy_slice_full_input_budget EN node_enc site_enc g p writes node_budget site_budget
      writes_budget read roots load.
Proof.
  intros Hnode Hnode_work Hsite Hwrites.
  pose proof (audit_legacy_dfs_input_bound N E CN EN g p node_enc node_work node_budget roots
    Hnode Hnode_work) as Hforward_work.
  pose proof (audit_legacy_dfs_input_bound N E CN EN (reverse_graph p [load])
    (prepared_reverse p [load]) node_enc node_work node_budget [load] Hnode Hnode_work)
    as Hbackward_work.
  pose proof (audit_legacy_reached_erases N E CN EN node_enc g p roots Hnode) as Hforward.
  pose proof (audit_legacy_reached_erases N E CN EN node_enc (reverse_graph p [load])
    (prepared_reverse p [load]) [load] Hnode) as Hbackward.
  unfold audit_legacy_slice_full, audit_legacy_slice_full_input_budget.
  unfold audit_legacy_reached_counted in Hforward, Hbackward |- *.
  destruct (audit_dfs_source_counted p (audit_legacy_dfs_callbacks node_enc g) FinSet.empty roots)
    as [fresult fevents].
  destruct (audit_dfs_source_counted (prepared_reverse p [load])
    (audit_legacy_dfs_callbacks node_enc (reverse_graph p [load])) FinSet.empty [load])
    as [bresult bevents].
  cbn [fst snd] in Hforward, Hbackward, Hforward_work, Hbackward_work.
  pose proof (audit_legacy_slice_nodes_source_bound N T CN CT W node_enc site_enc writes
    node_work site_work writes_work read (visited fresult) (visited bresult) (Graph.nodes g))
    as Hscan.
  pose proof (audit_legacy_slice_nodes_input_bound N T CN CT W node_enc site_enc writes node_work
    site_work writes_work node_budget site_budget writes_budget read (visited fresult)
    (visited bresult) (Graph.nodes g) Hnode_work Hsite Hwrites) as Hscan_budget.
  destruct (audit_legacy_slice_nodes node_enc site_enc writes read
    (visited fresult) (visited bresult)
    (Graph.nodes g)) as [answer events]; cbn [fst snd] in Hscan |- *.
  unfold audit_legacy_slice_full_source_work; cbn [audit_legacy_slice_forward_dfs
    audit_legacy_slice_reverse_dfs audit_legacy_slice_node_checks].
  rewrite <- Hforward, <- Hbackward.
  lia.
Qed.

(** * Pair and checker input budgets *)

(** The selected pair branch charges its actual probes, callbacks and full slice. *)
Lemma audit_legacy_pair_input_bound F N E T CN CF CT CS CR CW
    (EN : encoding N) (EF : encoding F) (ET : encoding T)
    (node_enc : N -> positive * list CN) (function_enc : F -> positive * list CF)
    (site_enc : T -> positive * list CT) (successors : N -> list N * list CS)
    (reads : N -> list (footprint T) * list CR) (writes : N -> list (footprint T) * list CW)
    node_work function_work site_work successor_work read_work write_work node_budget
    function_budget site_budget successor_budget read_budget write_budget
    (g : Graph.t N E) (p : prepared EN g) reached load definition function :
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall n, node_work (snd (node_enc n)) <= node_budget n) ->
    (forall f, function_work (snd (function_enc f)) <= function_budget f) ->
    (forall t, site_work (snd (site_enc t)) <= site_budget t) ->
    (forall n, successor_work (snd (successors n)) <= successor_budget n) ->
    (forall n, read_work (snd (reads n)) <= read_budget n) ->
    (forall n, write_work (snd (writes n)) <= write_budget n) ->
    audit_legacy_pair_source_work EN node_work function_work site_work successor_work read_work
      write_work (snd (audit_legacy_pair_check_full EN EF ET node_enc function_enc site_enc
        successors reads writes g p reached load definition function)) <=
    audit_legacy_pair_input_budget EN node_enc function_enc site_enc successors reads writes
      node_budget function_budget site_budget successor_budget read_budget write_budget g p
      load definition function.
Proof.
  intros Hnode Hnode_work Hfunction Hsite Hsucc Hread Hwrite.
  pose proof (audit_memory_distinct_mem_bound N CN node_enc node_work load reached) as Hload.
  pose proof (Hnode_work load) as Hload_work.
  destruct (audit_finset_mem node_enc load reached) as [load_ok load_calls] eqn:Hload_call;
    cbn [snd] in Hload.
  destruct definition as [owner node|owner].
  - pose proof (audit_memory_distinct_mem_bound N CN node_enc node_work node reached) as Hdef.
    pose proof (Hnode_work node) as Hdef_work.
    pose proof (Hfunction owner) as Howner_work.
    pose proof (Hfunction function) as Hfunction_work.
    pose proof (audit_positive_eqb_source_bound (fst (function_enc owner))
      (fst (function_enc function))) as Hequal.
    pose proof (Hread load) as Hread_work.
    pose proof (Hsucc node) as Hsucc_work.
    pose proof (audit_legacy_slice_full_input_bound N E T CN CT CW EN ET node_enc site_enc g p
      writes node_work site_work write_work node_budget site_budget write_budget (fst (reads load))
      (fst (successors node)) load Hnode Hnode_work Hsite Hwrite) as Hslice.
    unfold audit_legacy_pair_check_full, audit_legacy_pair_input_budget.
    rewrite Hload_call.
    destruct (function_enc owner) as [owner_code owner_body].
    destruct (function_enc function) as [function_code function_body].
    destruct (audit_positive_eqb owner_code function_code) as [same eq_events] eqn:Hequal_call.
    destruct (audit_finset_mem node_enc node reached) as [def_ok def_calls] eqn:Hdef_call.
    destruct (reads load) as [read read_calls].
    destruct (successors node) as [roots succ_calls].
    destruct (audit_legacy_slice_full EN ET node_enc site_enc g p writes read roots load)
      as [answer slice_events] eqn:Hslice_call.
    cbn [fst snd] in Hdef, Howner_work, Hfunction_work, Hequal, Hread_work, Hsucc_work, Hslice.
    rewrite Hequal_call in Hequal; cbn [snd] in Hequal.
    rewrite Hslice_call in Hslice; cbn [snd] in Hslice.
    unfold audit_legacy_pair_source_work.
    cbn [snd fst audit_legacy_pair_primitive_work length].
    unfold audit_walk_predecessor_input_budget.
    lia.
  - pose proof (Hfunction owner) as Howner_work.
    pose proof (Hfunction function) as Hfunction_work.
    pose proof (audit_positive_eqb_source_bound (fst (function_enc owner))
      (fst (function_enc function))) as Hequal.
    pose proof (Hread load) as Hread_work.
    pose proof (audit_legacy_slice_full_input_bound N E T CN CT CW EN ET node_enc site_enc g p
      writes node_work site_work write_work node_budget site_budget write_budget (fst (reads load))
      (Graph.entries g) load Hnode Hnode_work Hsite Hwrite) as Hslice.
    unfold audit_legacy_pair_check_full, audit_legacy_pair_input_budget.
    rewrite Hload_call.
    destruct (function_enc owner) as [owner_code owner_body].
    destruct (function_enc function) as [function_code function_body].
    destruct (audit_positive_eqb owner_code function_code) as [same eq_events] eqn:Hequal_call.
    destruct (reads load) as [read read_calls].
    destruct (audit_legacy_slice_full EN ET node_enc site_enc g p writes read
      (Graph.entries g) load)
      as [answer slice_events] eqn:Hslice_call.
    cbn [fst snd] in Howner_work, Hfunction_work, Hequal, Hread_work, Hslice.
    rewrite Hequal_call in Hequal; cbn [snd] in Hequal.
    rewrite Hslice_call in Hslice; cbn [snd] in Hslice.
    unfold audit_legacy_pair_source_work.
    cbn [snd fst audit_legacy_pair_primitive_work length].
    unfold audit_walk_predecessor_input_budget; lia.
Qed.

(** Each mapped successor edge contributes two fixed source frames. *)
Lemma audit_legacy_successor_map_work N E CN (g : Graph.t N E) node_work edges :
    audit_legacy_successor_source_work node_work
      (snd (@audit_legacy_successor_map N E CN g edges)) = 4 * length edges.
Proof.
  induction edges as [|edge rest IH].
  - reflexivity.
  - cbn [audit_legacy_successor_map].
    destruct (audit_legacy_successor_map g rest) as [targets events]; cbn in *; lia.
Qed.

(** Indexed successor enumeration is bounded by its actual map lookup and stored row. *)
Lemma audit_legacy_successors_input_bound N E CN (EN : encoding N)
    (node_enc : N -> positive * list CN) node_work node_budget (g : Graph.t N E)
    (p : prepared EN g) node :
    node_work (snd (node_enc node)) <= node_budget node ->
    audit_legacy_successor_source_work node_work
      (snd (audit_legacy_successors_counted EN node_enc g p node)) <=
    audit_legacy_successors_input_budget node_enc node_budget (out_index p) node.
Proof.
  intro Hnode.
  pose proof (audit_map_get_source_work_bound N (list E) CN node_enc node_work node (out_index p))
    as Hlookup.
  unfold audit_legacy_successors_counted, audit_legacy_successors_input_budget.
  destruct (audit_map_get node_enc node (out_index p)) as [found calls] eqn:Hcall; cbn [fst snd]
    in Hlookup |- *.
  destruct found as [edges|].
  - pose proof (audit_legacy_successor_map_work N E CN g node_work edges) as Hmap.
    destruct (audit_legacy_successor_map g edges) as [targets events]; cbn [snd] in Hmap |- *.
    cbn [audit_legacy_successor_source_work].
    unfold audit_walk_predecessor_input_budget; lia.
  - cbn [audit_legacy_successor_map audit_legacy_successor_source_work length].
    unfold audit_walk_predecessor_input_budget.
    cbn [snd audit_legacy_successor_source_work].
    lia.
Qed.

(** Every candidate and missing definition contributes its bounded actual checker body. *)
Lemma audit_legacy_check_nodes_input_bound F N E T CN CF CT CS CR CW CD
    (EN : encoding N) (EF : encoding F) (ET : encoding T)
    (node_enc : N -> positive * list CN) (function_enc : F -> positive * list CF)
    (site_enc : T -> positive * list CT) (successors : N -> list N * list CS)
    (reads : N -> list (footprint T) * list CR) (writes : N -> list (footprint T) * list CW)
    (definitions : N -> option (mem_node F N) * list CD)
    node_work function_work site_work successor_work read_work write_work definition_work
    node_budget
    function_budget site_budget successor_budget read_budget write_budget definition_budget
    (g : Graph.t N E) (p : prepared EN g) reached function nodes :
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall n, node_work (snd (node_enc n)) <= node_budget n) ->
    (forall f, function_work (snd (function_enc f)) <= function_budget f) ->
    (forall t, site_work (snd (site_enc t)) <= site_budget t) ->
    (forall n, successor_work (snd (successors n)) <= successor_budget n) ->
    (forall n, read_work (snd (reads n)) <= read_budget n) ->
    (forall n, write_work (snd (writes n)) <= write_budget n) ->
    (forall n, definition_work (snd (definitions n)) <= definition_budget n) ->
    audit_legacy_checker_source_work EN node_work function_work site_work successor_work read_work
      write_work definition_work (snd (audit_legacy_check_nodes EN EF ET node_enc function_enc
        site_enc successors reads writes g p reached definitions function nodes)) <=
    audit_legacy_check_nodes_input_budget EN node_enc function_enc site_enc successors reads writes
      definitions node_budget function_budget site_budget successor_budget read_budget write_budget
      definition_budget g p function nodes.
Proof.
  intros Hnode Hnode_work Hfunction Hsite Hsucc Hread Hwrite Hdefinition.
  induction nodes as [|node rest IH].
  - reflexivity.
  - cbn [audit_legacy_check_nodes audit_legacy_check_nodes_input_budget].
    pose proof (Hdefinition node) as Hcall.
    destruct (definitions node) as [candidate calls] eqn:Hdefinition_call; cbn [fst snd] in *.
    destruct candidate as [definition|].
    + pose proof (audit_legacy_pair_input_bound F N E T CN CF CT CS CR CW EN EF ET node_enc
        function_enc site_enc successors reads writes node_work function_work site_work
        successor_work read_work write_work node_budget function_budget site_budget successor_budget
        read_budget write_budget g p reached node definition function Hnode Hnode_work Hfunction
        Hsite Hsucc Hread Hwrite) as Hpair.
      destruct (audit_legacy_pair_check_full EN EF ET node_enc function_enc site_enc
        successors reads writes g p reached node definition function) as [answer pair_events].
      destruct (audit_legacy_check_nodes EN EF ET node_enc function_enc site_enc successors reads
        writes g p reached definitions function rest) as [tail events]; cbn [fst snd] in *.
      cbn [audit_legacy_checker_source_work]; lia.
    + destruct (audit_legacy_check_nodes EN EF ET node_enc function_enc site_enc successors reads
        writes g p reached definitions function rest) as [tail events]; cbn [fst snd] in *.
      cbn [audit_legacy_checker_source_work]; lia.
Qed.

(** The normalized graph preparation charges its indexed row reads and pair projections. *)
Lemma audit_legacy_prepare_input_bound N CN (EN : encoding N)
    (node_enc : N -> positive * list CN) node_work node_budget
    (rows : Map.t N (list (N * N))) entries nodes :
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall n, node_work (snd (node_enc n)) <= node_budget n) ->
    let cfg := Graph.Make entries nodes (index_edges EN rows) fst snd in
    audit_prepare_source_work
      (audit_snapshot_graph_body_work node_work (audit_map_source_work node_work) (@length unit))
      (snd (audit_prepare_source_counted EN cfg (audit_legacy_prepare_callbacks node_enc rows))) <=
    audit_prepare_source_budget EN cfg + audit_graph_prepare_full_event_bound cfg *
      audit_snapshot_graph_input_budget (audit_walk_predecessors node_enc rows)
        (fun edge : N * N => (snd edge, @nil unit)) node_budget
        (audit_walk_predecessor_input_budget node_enc node_budget) (fun _ => 1) (Graph.nodes cfg).
Proof.
  intros Hnode Hnode_work cfg.
  set (out_model := audit_walk_predecessors node_enc rows).
  set (target_model := fun edge : N * N => (snd edge, @nil unit)).
  set (out_budget' := audit_walk_predecessor_input_budget node_enc node_budget).
  assert (Hout_model : forall n, fst (out_model n) = Graph.out cfg n).
  { intro n; unfold out_model, cfg; cbn [Graph.out].
    apply audit_walk_predecessors_erases; apply Hnode. }
  assert (Htarget_model : forall e, fst (target_model e) = Graph.target cfg e).
  { intro e; reflexivity. }
  assert (Hout_budget : forall n, audit_map_source_work node_work (snd (out_model n)) <=
      out_budget' n).
  { intro n; unfold out_model, out_budget'.
    apply audit_walk_predecessors_work_bound; apply Hnode_work. }
  assert (Htarget_budget : forall e, length (snd (target_model e)) <= 1).
  { intro e; unfold target_model; cbn; lia. }
  pose proof (audit_walk_prepare_source_bound N (N * N)%type CN
    (audit_map_event N (list (N * N)) CN) unit EN cfg node_enc out_model target_model node_work
    (audit_map_source_work node_work) (@length unit) node_budget out_budget' (fun _ => 1)
    Hnode Hout_model Htarget_model Hnode_work Hout_budget Htarget_budget) as Hwork.
  exact Hwork.
Qed.

(** The entire checker is bounded by its input-derived setup and candidate budgets. *)
Theorem audit_legacy_no_clobber_whole_input_bound :
    audit_legacy_no_clobber_whole_input_bound_statement.
Proof.
  intros F N E T CN CF CT OE TE CR CW CD EN EF ET node_enc function_enc site_enc out target
    reads writes definitions node_work function_work site_work out_work target_work read_work
    write_work definition_work node_budget function_budget site_budget out_budget target_budget
    read_budget write_budget definition_budget g function Hnode Hnode_work Hfunction Hsite Hout
    Htarget Hread Hwrite Hdefinition.
  pose proof (audit_legacy_cfg_whole_input_bound N E CN OE TE EN node_enc out target node_work
    out_work target_work node_budget out_budget target_budget g Hnode_work Hout Htarget) as Hcfg.
  unfold audit_legacy_no_clobber_counted, audit_legacy_no_clobber_input_budget.
  destruct (audit_legacy_cfg_rows EN node_enc out target (Graph.nodes g))
    as [rows cfg_events] eqn:Hrows.
  set (cfg := Graph.Make (Graph.entries g) (Graph.nodes g) (index_edges EN rows) fst snd).
  pose proof (audit_legacy_prepare_input_bound N CN EN node_enc node_work node_budget rows
    (Graph.entries g) (Graph.nodes g) Hnode Hnode_work) as Hprepare_work.
  cbn zeta in Hprepare_work; fold cfg in Hprepare_work.
  assert (Hcallbacks : audit_prepare_callbacks_erase EN cfg
      (audit_legacy_prepare_callbacks node_enc rows)).
  { unfold cfg; apply audit_legacy_prepare_callbacks_erases; exact Hnode. }
  pose proof (audit_prepare_source_correct N (N * N)%type _ EN cfg
    (audit_legacy_prepare_callbacks node_enc rows) (fun _ => 0) Hcallbacks) as Hprepare.
  destruct (audit_prepare_source_counted EN cfg (audit_legacy_prepare_callbacks node_enc rows))
    as [prep prep_events] eqn:Hprepare_call; cbn [fst snd] in Hprepare, Hprepare_work.
  destruct Hprepare as [Hprep _]; subst prep.
  pose proof (audit_legacy_dfs_input_bound N (N * N)%type CN EN cfg (prepare EN cfg) node_enc
    node_work node_budget (Graph.entries cfg) Hnode Hnode_work) as Hdfs_work.
  destruct (audit_dfs_source_counted (prepare EN cfg) (audit_legacy_dfs_callbacks node_enc cfg)
    FinSet.empty (Graph.entries cfg)) as [result dfs_events]; cbn [snd] in Hdfs_work |- *.
  pose proof (audit_legacy_check_nodes_input_bound F N (N * N)%type T CN CF CT
    (audit_legacy_successor_event N (N * N) CN) CR CW CD EN EF ET node_enc function_enc site_enc
    (audit_legacy_successors_counted EN node_enc cfg (prepare EN cfg)) reads writes definitions
    node_work function_work site_work (audit_legacy_successor_source_work node_work) read_work
    write_work definition_work node_budget function_budget site_budget
    (audit_legacy_successors_input_budget node_enc node_budget (out_index (prepare EN cfg)))
    read_budget write_budget definition_budget cfg (prepare EN cfg) (visited result) function
    (Graph.nodes g) Hnode Hnode_work Hfunction Hsite
    (fun n => audit_legacy_successors_input_bound N (N * N)%type CN EN node_enc node_work
      node_budget cfg (prepare EN cfg) n (Hnode_work n)) Hread Hwrite Hdefinition) as Hcheck.
  destruct (audit_legacy_check_nodes EN EF ET node_enc function_enc site_enc
    (audit_legacy_successors_counted EN node_enc cfg (prepare EN cfg)) reads writes cfg
    (prepare EN cfg) (visited result) definitions function (Graph.nodes g)) as [answer events].
  cbn [snd] in Hcheck |- *.
  unfold audit_legacy_no_clobber_source_work; cbn [audit_legacy_check_cfg_events
    audit_legacy_check_prepare_events audit_legacy_check_reached_events
    audit_legacy_check_nodes_events].
  unfold audit_legacy_cfg_counted in Hcfg.
  rewrite Hrows in Hcfg; cbn [snd] in Hcfg.
  cbn [fst snd] in |- *.
  fold cfg.
  lia.
Qed.
