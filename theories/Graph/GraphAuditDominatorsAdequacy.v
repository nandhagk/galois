(** * Dominator source adequacy

    Connects the counted dominator construction to its source operations.
    For example, the LT backend retains the virtual search and parent erasure traces.
    Builds on: GraphAuditDominators and its prerequisite adequacy proofs. *)

From Stdlib Require Import List Bool PArith Arith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsAuditCost CollectionsAuditPrimitive CollectionsAuditMap
  CollectionsAuditTrie CollectionsAuditMapAdequacy CollectionsAuditElements
  CollectionsAuditElementsAdequacy.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphDominance
  GraphSemiDominators GraphLengauerTarjan GraphDominators GraphAuditBase GraphAuditDfs
  GraphAuditVirtual GraphAuditSemiDominators GraphAuditLengauerTarjan GraphAuditDominators
  GraphAuditBaseAdequacy
  GraphAuditDfsAdequacy GraphAuditVirtualAdequacy GraphAuditSemiDominatorsAdequacy
  GraphAuditLengauerTarjanAdequacy.
Import List.ListNotations.

(** * Backend erasure *)

(** The counted LT backend retains a run returning the ordinary immediate dominators. *)
Theorem audit_lt_backend_erasure : audit_lt_backend_erasure_statement.
Proof.
  intros V E EV g p.
  destruct (audit_virtual_callbacks_correct V E EV g) as [Hprepare [Hdfs _]].
  pose proof (audit_graph_prepare_nested_correct _ _ _ (virtual_encoding EV)
    (virtual_graph EV g) (audit_virtual_prepare_callbacks EV g) Hprepare) as Hprepared.
  pose proof (audit_virtual_search_correct V E EV g p) as Hsearch.
  unfold audit_virtual_search_counted, audit_virtual_search_with_prepared in Hsearch.
  unfold audit_lt_backend_run, audit_virtual_search_with_prepared.
  destruct (audit_graph_prepare_nested_counted (virtual_encoding EV) (virtual_graph EV g)
    (audit_virtual_prepare_callbacks EV g)) as [vp prepare_events] eqn:Hprep.
  cbn [fst snd] in Hprepared; destruct Hprepared as [Hprepared _].
  change (vp = virtual_prepared p) in Hprepared; subst vp.
  destruct (audit_dfs_nested_counted (virtual_prepared p) (audit_virtual_dfs_callbacks EV g)
    FinSet.empty [inr tt]) as [search dfs_events] eqn:Hdfs_run.
  cbn [fst snd] in Hsearch; subst search.
  destruct (audit_semi_compute_correct _ _ (virtual_encoding EV) (virtual_graph EV g)
    (virtual_prepared p) (virtual_dfs p)) as [state [semi_events [Hsemi [Hstate _]]]].
  subst state.
  destruct (audit_lt_compute_correct _ _ (virtual_encoding EV) (virtual_graph EV g)
    (virtual_dfs p) (SemiState.result (semi_compute (virtual_prepared p) (virtual_dfs p))))
    as [parents [lt_events [Hlt [Hparents _]]]].
  subst parents.
  pose proof (audit_erase_virtual_correct V EV
    (lt_compute (virtual_encoding EV) (virtual_graph EV g) (virtual_dfs p)
      (SemiState.result (semi_compute (virtual_prepared p) (virtual_dfs p))))) as Herase.
  destruct (audit_erase_virtual_counted EV
    (lt_compute (virtual_encoding EV) (virtual_graph EV g) (virtual_dfs p)
      (SemiState.result (semi_compute (virtual_prepared p) (virtual_dfs p)))))
    as [result erase_events] eqn:Herase_run.
  cbn [fst snd] in Herase; destruct Herase as [Herase _].
  exists result, (AuditLtBackendTrace prepare_events dfs_events semi_events lt_events erase_events).
  split.
  - exists (semi_compute (virtual_prepared p) (virtual_dfs p)), semi_events,
      (lt_compute (virtual_encoding EV) (virtual_graph EV g) (virtual_dfs p)
        (SemiState.result (semi_compute (virtual_prepared p) (virtual_dfs p)))), lt_events.
    split; [exact Hsemi|].
    split; [exact Hlt|].
    rewrite Herase_run; split; reflexivity.
  - unfold simple_lt_idom; exact Herase.
Qed.

(** * Forest construction *)

(** Tail-first child indexing erases to the original child map. *)
Lemma audit_dom_children_erases {V E} (EV : encoding V) rows :
  fst (@audit_dom_children_counted V E EV rows) = dom_children EV rows.
Proof.
  induction rows as [|[v u] rest IH].
  - reflexivity.
  - cbn [audit_dom_children_counted dom_children].
    destruct (audit_dom_children_counted EV rest) as [children events].
    cbn [fst] in IH; subst children.
    unfold index_edges; destruct (Map.get EV u (dom_children EV rest)); reflexivity.
Qed.

(** The counted roots are exactly the parentless live vertices in source order. *)
Lemma audit_dom_roots_erases {V E} (EV : encoding V) parents live :
  fst (@audit_dom_roots_counted V E EV parents live) =
    filter (fun v => negb (Map.mem EV v parents)) live.
Proof.
  induction live as [|v rest IH].
  - reflexivity.
  - cbn [audit_dom_roots_counted filter].
    destruct (Map.get EV v parents) eqn:Hget;
      destruct (audit_dom_roots_counted EV parents rest) as [roots events];
      cbn [fst] in IH; unfold Map.mem; rewrite Hget; cbn; now rewrite IH.
Qed.

(** The source child traversal erases each actual map call. *)
Lemma audit_dom_source_children_erases {V E B} (EV : encoding V) enc rows :
  (forall v, fst (enc v) = encode EV v) ->
  fst (@audit_dom_source_children V E B enc rows) = dom_children EV rows.
Proof.
  intro Hencode; induction rows as [|[v u] rest IH].
  - reflexivity.
  - cbn [audit_dom_source_children dom_children].
    destruct (audit_dom_source_children enc rest) as [children events].
    cbn [fst] in IH; subst children.
    pose proof (audit_map_get_erases V (list V) B enc EV u (dom_children EV rest)
      (Hencode u)) as Hget.
    destruct (audit_map_get enc u (dom_children EV rest)) as [found reads].
    cbn [fst] in Hget; subst found.
    pose proof (audit_map_set_erases V (list V) B enc EV u
      (v :: index_edges EV (dom_children EV rest) u) (dom_children EV rest) (Hencode u)) as Hset.
    unfold index_edges in Hset |- *.
    destruct (Map.get EV u (dom_children EV rest)) as [row|].
    + destruct (audit_map_set enc u (v :: row) (dom_children EV rest)); exact Hset.
    + destruct (audit_map_set enc u [v] (dom_children EV rest)); exact Hset.
Qed.

(** The source root traversal preserves the parentless live vertices. *)
Lemma audit_dom_source_roots_erases {V E B} (EV : encoding V) enc parents live :
  (forall v, fst (enc v) = encode EV v) ->
  fst (@audit_dom_source_roots V E B enc parents live) =
    filter (fun v => negb (Map.mem EV v parents)) live.
Proof.
  intro Hencode; induction live as [|v rest IH].
  - reflexivity.
  - cbn [audit_dom_source_roots filter].
    pose proof (audit_map_get_erases V V B enc EV v parents (Hencode v)) as Hget.
    destruct (audit_map_get enc v parents) as [found reads].
    cbn [fst] in Hget; subst found.
    destruct (audit_dom_source_roots enc parents rest) as [roots events].
    cbn [fst] in IH; unfold Map.mem; destruct (Map.get EV v parents); cbn; now rewrite IH.
Qed.

(** Child indexing emits three calls for each binding and one terminal case. *)
Lemma audit_dom_children_count {V E} (EV : encoding V) rows :
  length (snd (@audit_dom_children_counted V E EV rows)) = 1 + 3 * length rows.
Proof.
  induction rows as [|[v u] rest IH].
  - reflexivity.
  - cbn [audit_dom_children_counted].
    destruct (audit_dom_children_counted EV rest) as [children events].
    cbn [snd] in IH; destruct (Map.get EV u children); cbn [snd length]; rewrite length_app;
      cbn; lia.
Qed.

(** Root selection emits a case and lookup for each live vertex. *)
Lemma audit_dom_roots_count {V E} (EV : encoding V) parents live :
  length (snd (@audit_dom_roots_counted V E EV parents live)) = 1 + 2 * length live.
Proof.
  induction live as [|v rest IH].
  - reflexivity.
  - cbn [audit_dom_roots_counted].
    destruct (audit_dom_roots_counted EV parents rest) as [roots events].
    cbn [snd] in IH |- *; destruct (Map.get EV v parents); cbn; lia.
Qed.

(** The source forest callback returns the indexed children using its actual encoder. *)
Lemma audit_dom_source_out_erases {V B} (EV : encoding V) enc children v :
  (forall x, fst (enc x) = encode EV x) ->
  fst (@audit_dom_source_out V B enc children v) = index_edges EV children v.
Proof.
  intro Hencode.
  pose proof (audit_map_get_erases V (list V) B enc EV v children (Hencode v)) as Hget.
  unfold audit_dom_source_out, index_edges.
  destruct (audit_map_get enc v children) as [found events].
  cbn [fst] in Hget; subst found; destruct (Map.get EV v children); reflexivity.
Qed.

(** The source encoder wrapper returns the same code while preserving its body. *)
Lemma audit_dom_source_encode_erases {V B} (EV : encoding V) enc v :
  (forall x, fst (enc x) = encode EV x) ->
  fst (@audit_dom_source_encode V B enc v) = encode EV v.
Proof.
  intro Hencode; specialize (Hencode v).
  unfold audit_dom_source_encode; destruct (enc v); exact Hencode.
Qed.

(** Source forest preparation and search return the ordinary forest search. *)
Lemma audit_dom_search_source_erases {V E B} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) parents (cb : audit_dfs_callback_model V E B) :
  audit_dfs_callbacks_erase EV g cb ->
  audit_dom_source_result (audit_dom_search_source_counted p parents cb) = dom_search p parents.
Proof.
  intro Hcallbacks.
  destruct Hcallbacks as [Htarget Hencode].
  pose proof (audit_dfs_source_result_and_count p cb FinSet.empty (Graph.entries g)
    (conj Htarget Hencode)) as [Hsearch _].
  pose proof (audit_map_elements_erases V V parents) as Hrows.
  pose proof (audit_dom_source_children_erases (E := E) EV (audit_dfs_encode_model cb)
    (Map.elements parents) Hencode) as Hchildren.
  pose proof (audit_dom_source_roots_erases (E := E) EV (audit_dfs_encode_model cb) parents
    (preorder (dfs p FinSet.empty (Graph.entries g))) Hencode) as Hroots.
  unfold audit_dom_search_source_counted.
  destruct (audit_dfs_source_counted p cb FinSet.empty (Graph.entries g))
    as [search search_events].
  cbn [fst] in Hsearch; subst search.
  destruct (audit_map_elements parents) as [rows element_events].
  cbn [fst] in Hrows; subst rows.
  destruct (audit_dom_source_children (audit_dfs_encode_model cb) (Map.elements parents))
    as [children child_events].
  cbn [fst] in Hchildren; subst children.
  destruct (audit_dom_source_roots (audit_dfs_encode_model cb) parents
    (preorder (dfs p FinSet.empty (Graph.entries g)))) as [roots root_events].
  cbn [fst] in Hroots; subst roots.
  set (forest := dom_forest p parents).
  change (audit_dom_source_result
    (let prepare_cb := AuditPrepareCallbackModel V V (audit_dom_source_body V B)
      (audit_dom_source_out (audit_dfs_encode_model cb) (dom_children EV (Map.elements parents)))
      audit_dom_source_target (audit_dom_source_encode (audit_dfs_encode_model cb)) in
     let dfs_cb := AuditDfsCallbackModel V V (audit_dom_source_body V B) audit_dom_source_target
      (audit_dom_source_encode (audit_dfs_encode_model cb)) in
     let '(fp, prepare_events) := audit_prepare_source_counted EV forest prepare_cb in
     let '(result, dfs_events) := audit_dfs_source_counted fp dfs_cb FinSet.empty
      (Graph.entries forest) in
     AuditDomSourceReceipt forest fp result
       (map DomSourceInitialDfs search_events ++ map DomSourceElements element_events ++
        child_events ++ root_events ++ map DomSourcePrepare prepare_events ++
        map DomSourceDfs dfs_events)) = dom_search p parents).
  set (prepare_cb := AuditPrepareCallbackModel V V (audit_dom_source_body V B)
    (audit_dom_source_out (audit_dfs_encode_model cb) (dom_children EV (Map.elements parents)))
    audit_dom_source_target (audit_dom_source_encode (audit_dfs_encode_model cb))).
  set (dfs_cb := AuditDfsCallbackModel V V (audit_dom_source_body V B) audit_dom_source_target
    (audit_dom_source_encode (audit_dfs_encode_model cb))).
  assert (Hprepare : audit_prepare_callbacks_erase EV forest prepare_cb).
  { unfold audit_prepare_callbacks_erase, prepare_cb; cbn [audit_prepare_out_model
      audit_prepare_target_model audit_prepare_encode_model].
    split.
    - intro v; unfold forest, dom_forest; cbn [Graph.out].
      apply audit_dom_source_out_erases; exact Hencode.
    - split.
      + intro v; reflexivity.
      + intro v; apply audit_dom_source_encode_erases; exact Hencode. }
  assert (Hdfs : audit_dfs_callbacks_erase EV forest dfs_cb).
  { unfold audit_dfs_callbacks_erase, dfs_cb; cbn [audit_dfs_target_model audit_dfs_encode_model].
    split.
    - intro v; reflexivity.
    - intro v; apply audit_dom_source_encode_erases; exact Hencode. }
  cbn zeta.
  fold prepare_cb dfs_cb.
  pose proof (audit_prepare_source_correct V V (audit_dom_source_body V B) EV forest prepare_cb
    (fun _ => 0) Hprepare) as Hprepared.
  destruct (audit_prepare_source_counted EV forest prepare_cb) as [fp prepare_events] eqn:Hprep_run.
  cbn [fst snd] in Hprepared; destruct Hprepared as [Hprepared _]; subst fp.
  pose proof (audit_dfs_source_result_and_count (prepare EV forest) dfs_cb FinSet.empty
    (Graph.entries forest) Hdfs) as [Hresult _].
  destruct (audit_dfs_source_counted (prepare EV forest) dfs_cb FinSet.empty
    (Graph.entries forest)) as [result dfs_events] eqn:Hforest_run.
  cbn [fst] in Hresult; cbn [audit_dom_source_result].
  unfold dom_search; fold forest; exact Hresult.
Qed.

(** The counted forest callbacks return the exact source operations. *)
Lemma audit_dom_prepare_callbacks_erases {V} (EV : encoding V) roots live parents children :
  let forest := Graph.Make roots live (fun v => index_edges EV children v)
    (fun v => match Map.get EV v parents with
      | Some u => u
      | None => v
      end) (fun v => v) in
  audit_prepare_callbacks_erase EV forest (audit_dom_prepare_callbacks EV children).
Proof.
  cbn [audit_prepare_callbacks_erase audit_dom_prepare_callbacks audit_prepare_out_model
    audit_prepare_target_model audit_prepare_encode_model audit_dom_out_counted
    audit_dom_target_counted audit_dom_encode_counted Graph.out Graph.target].
  split.
  - intro v; unfold index_edges; destruct (Map.get EV v children); reflexivity.
  - split; intros v; reflexivity.
Qed.

(** The counted forest DFS callbacks return the exact target and encoding. *)
Lemma audit_dom_dfs_callbacks_erases {V} (EV : encoding V) roots live parents children :
  let forest := Graph.Make roots live (fun v => index_edges EV children v)
    (fun v => match Map.get EV v parents with
      | Some u => u
      | None => v
      end) (fun v => v) in
  audit_dfs_callbacks_erase EV forest (audit_dom_dfs_callbacks EV).
Proof.
  cbn [audit_dfs_callbacks_erase audit_dom_dfs_callbacks audit_dfs_target_model
    audit_dfs_encode_model audit_dom_target_counted audit_dom_encode_counted Graph.target].
  split; intros v; reflexivity.
Qed.

(** The counted dominator tree returns the ordinary forest numbering. *)
Lemma audit_dom_tree_counted_erases {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) parents :
  fst (audit_dom_tree_counted p parents) = dom_tree_of p parents.
Proof.
  pose proof (audit_dfs_full_counted_erases p FinSet.empty (Graph.entries g)) as Hsearch.
  pose proof (audit_dom_children_erases (E := E) EV (Map.elements parents)) as Hchildren.
  pose proof (audit_dom_roots_erases (E := E) EV parents
    (preorder (dfs p FinSet.empty (Graph.entries g)))) as Hroots.
  unfold audit_dom_tree_counted.
  destruct (audit_dfs_full_counted p FinSet.empty (Graph.entries g)) as [search initial_events].
  cbn [fst] in Hsearch; subst search.
  destruct (audit_dom_children_counted EV (Map.elements parents)) as [children child_events].
  cbn [fst] in Hchildren; subst children.
  destruct (audit_dom_roots_counted EV parents (preorder (dfs p FinSet.empty (Graph.entries g))))
    as [roots root_events].
  cbn [fst] in Hroots; subst roots.
  set (forest := dom_forest p parents).
  change (fst
    (let '(fp, prep_events) := audit_graph_prepare_nested_counted EV forest
       (audit_dom_prepare_callbacks EV (dom_children EV (Map.elements parents))) in
     let '(result, dfs_events) := audit_dfs_nested_counted fp (audit_dom_dfs_callbacks EV)
       FinSet.empty (Graph.entries forest) in
     (DomTree parents (pre_num result) (post_num result),
      map AuditDomInitialDfs initial_events ++ [AuditDomElements parents (Map.elements parents)] ++
      child_events ++ root_events ++ map AuditDomPrepare prep_events ++ map AuditDomDfs
        dfs_events ++
      [AuditDomOutput (length (preorder (dfs p FinSet.empty (Graph.entries g))))])) =
    dom_tree_of p parents).
  assert (Hprepare : audit_prepare_callbacks_erase EV forest
    (audit_dom_prepare_callbacks EV (dom_children EV (Map.elements parents)))).
  { unfold forest, dom_forest; apply audit_dom_prepare_callbacks_erases. }
  assert (Hdfs : audit_dfs_callbacks_erase EV forest (audit_dom_dfs_callbacks EV)).
  { unfold forest, dom_forest; apply audit_dom_dfs_callbacks_erases. }
  pose proof (audit_graph_prepare_nested_correct V V (audit_dom_body V) EV forest
    (audit_dom_prepare_callbacks EV (dom_children EV (Map.elements parents))) Hprepare) as
      Hprepared.
  destruct (audit_graph_prepare_nested_counted EV forest
    (audit_dom_prepare_callbacks EV (dom_children EV (Map.elements parents)))) as [fp prep_events].
  cbn [fst snd] in Hprepared; destruct Hprepared as [Hprepared _]; subst fp.
  pose proof (audit_dfs_nested_correct V V (audit_dom_body V) EV forest (prepare EV forest)
    (audit_dom_dfs_callbacks EV) FinSet.empty (Graph.entries forest) Hdfs) as Hresult.
  destruct (audit_dfs_nested_counted (prepare EV forest) (audit_dom_dfs_callbacks EV)
    FinSet.empty (Graph.entries forest)) as [result dfs_events].
  cbn [fst snd] in Hresult; destruct Hresult as [Hsame _].
  unfold dom_tree_of, dom_search; fold forest; cbn [fst]; now rewrite Hsame.
Qed.

(** Each indexed child row contains at most one entry per input binding. *)
Lemma audit_dom_children_row_length {V} (EV : encoding V) rows u :
  length (index_edges EV (dom_children EV rows) u) <= length rows.
Proof.
  induction rows as [|[v parent] rest IH].
  - unfold dom_children, index_edges; rewrite Map.get_empty; reflexivity.
  - cbn [dom_children].
    destruct (dfs_eq_dec EV u parent) as [Heq|Hne].
    + subst parent; unfold index_edges at 1; rewrite Map.get_set_same; cbn; lia.
    + unfold index_edges at 1; rewrite Map.get_set_other by exact Hne.
      change (length (index_edges EV (dom_children EV rest) u) <= S (length rest)); lia.
Qed.

(** The forest's total outgoing edges are bounded by vertices times parent bindings. *)
Lemma audit_dom_forest_edges_bound {V} (EV : encoding V) live rows :
  length (flat_map (index_edges EV (dom_children EV rows)) live) <= length live * length rows.
Proof.
  induction live as [|v rest IH].
  - reflexivity.
  - cbn [flat_map length]; rewrite length_app.
    pose proof (audit_dom_children_row_length EV rows v); nia.
Qed.

(** Initial DFS cannot discover more vertices than its roots and fuel permit. *)
Lemma audit_dom_live_length {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) :
  length (preorder (dfs p FinSet.empty (Graph.entries g))) <=
    length (Graph.entries g) * S (Pos.to_nat (fuel p)).
Proof.
  pose proof (audit_dfs_roots_clock_bound p FinSet.empty (Graph.entries g) dfs_initial)
    as [Hclock _].
  assert (Hinitial : audit_dfs_list_clock_invariant (@dfs_initial V E)).
  { unfold audit_dfs_list_clock_invariant, dfs_initial; cbn; lia. }
  pose proof (audit_dfs_roots_list_clock p FinSet.empty (Graph.entries g) dfs_initial Hinitial)
    as [Hlength _].
  unfold dfs; cbn [preorder]; rewrite <- rev_alt, length_rev.
  cbn [dfs_initial] in Hclock; cbn in Hclock; lia.
Qed.

(** The two node measures count the same trie constructors. *)
Lemma audit_dom_nodes_ne_agree {A} (node : Trie.ne A) :
  audit_elements_nodes node = audit_erase_nodes_ne node.
Proof.
  induction node; cbn [audit_elements_nodes audit_erase_nodes_ne]; congruence.
Qed.

(** Enumeration emits at most one parent binding per input trie node. *)
Lemma audit_dom_parent_rows_bound {V} (parents : Map.t V V) :
  length (Map.elements parents) <= audit_erase_nodes parents.
Proof.
  pose proof (audit_map_elements_erases V V parents) as Herase.
  pose proof (audit_map_elements_quantitative V V parents) as [Hlength _].
  rewrite Herase in Hlength.
  destruct parents as [|node]; cbn [audit_trie_nodes audit_erase_nodes] in *.
  - exact Hlength.
  - rewrite <- audit_dom_nodes_ne_agree; exact Hlength.
Qed.

(** A generated forest's edge count uses only its live vertices and parent rows. *)
Lemma audit_dom_forest_edge_count {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) parents :
  edge_count (dom_forest p parents) <=
    length (preorder (dfs p FinSet.empty (Graph.entries g))) * length (Map.elements parents).
Proof.
  unfold edge_count, dom_forest; cbn [Graph.nodes Graph.out].
  generalize (preorder (dfs p FinSet.empty (Graph.entries g))) as live.
  intro live; induction live as [|v rest IH].
  - reflexivity.
  - cbn [fold_right length].
    pose proof (audit_dom_children_row_length EV (Map.elements parents) v); nia.
Qed.

(** Forest roots are a filtered subset of the original search's live vertices. *)
Lemma audit_dom_forest_roots_length {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) parents :
  length (Graph.entries (dom_forest p parents)) <=
    length (preorder (dfs p FinSet.empty (Graph.entries g))).
Proof.
  unfold dom_forest; cbn [Graph.entries].
  apply filter_length_le.
Qed.

(** The counted tree trace is bounded by the input DFS, forest size and parent rows. *)
Lemma audit_dom_tree_count_components {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) parents :
  let live := length (preorder (dfs p FinSet.empty (Graph.entries g))) in
  let rows := length (Map.elements parents) in
  length (snd (audit_dom_tree_counted p parents)) <=
    audit_dfs_full_input_event_bound p (Graph.entries g) + 1 + (1 + 3 * rows) +
    (1 + 2 * live) + (8 + 12 * live + 8 * (live * rows)) +
    (3 + live * (40 * (3 + 2 * live + live * rows))) + 1.
Proof.
  pose proof (audit_dfs_full_counted_correct V E EV g p FinSet.empty (Graph.entries g)) as Hfirst.
  pose proof (audit_dom_children_erases (E := E) EV (Map.elements parents)) as Hchildren.
  pose proof (audit_dom_children_count (E := E) EV (Map.elements parents)) as Hchild_count.
  pose proof (audit_dom_roots_erases (E := E) EV parents
    (preorder (dfs p FinSet.empty (Graph.entries g)))) as Hroots.
  pose proof (audit_dom_roots_count (E := E) EV parents
    (preorder (dfs p FinSet.empty (Graph.entries g)))) as Hroot_count.
  pose proof (audit_dom_forest_edge_count EV g p parents) as Hedges.
  pose proof (audit_dom_forest_roots_length EV g p parents) as Hroot_length.
  unfold audit_dom_tree_counted.
  destruct (audit_dfs_full_counted p FinSet.empty (Graph.entries g)) as [search first_events].
  cbn [fst snd] in Hfirst; destruct Hfirst as [Hsearch [Hfirst_count _]]; subst search.
  destruct (audit_dom_children_counted EV (Map.elements parents)) as [children child_events].
  cbn [fst snd] in Hchildren, Hchild_count; subst children.
  destruct (audit_dom_roots_counted EV parents (preorder (dfs p FinSet.empty (Graph.entries g))))
    as [roots root_events].
  cbn [fst snd] in Hroots, Hroot_count; subst roots.
  set (forest := dom_forest p parents) in *.
  change (length (snd
    (let '(fp, prep_events) := audit_graph_prepare_nested_counted EV forest
       (audit_dom_prepare_callbacks EV (dom_children EV (Map.elements parents))) in
     let '(result, dfs_events) := audit_dfs_nested_counted fp (audit_dom_dfs_callbacks EV)
       FinSet.empty (Graph.entries forest) in
     (DomTree parents (pre_num result) (post_num result),
      map AuditDomInitialDfs first_events ++ [AuditDomElements parents (Map.elements parents)] ++
      child_events ++ root_events ++ map AuditDomPrepare prep_events ++ map AuditDomDfs
        dfs_events ++
      [AuditDomOutput (length (Graph.nodes forest))]))) <=
    audit_dfs_full_input_event_bound p (Graph.entries g) + 1 +
    (1 + 3 * length (Map.elements parents)) +
    (1 + 2 * length (preorder (dfs p FinSet.empty (Graph.entries g)))) +
    (8 + 12 * length (preorder (dfs p FinSet.empty (Graph.entries g))) +
      8 * (length (preorder (dfs p FinSet.empty (Graph.entries g))) *
        length (Map.elements parents))) +
    (3 + length (preorder (dfs p FinSet.empty (Graph.entries g))) *
      (40 * (3 + 2 * length (preorder (dfs p FinSet.empty (Graph.entries g))) +
        length (preorder (dfs p FinSet.empty (Graph.entries g))) *
          length (Map.elements parents)))) + 1).
  assert (Hprepare : audit_prepare_callbacks_erase EV forest
    (audit_dom_prepare_callbacks EV (dom_children EV (Map.elements parents)))).
  { unfold forest, dom_forest; apply audit_dom_prepare_callbacks_erases. }
  assert (Hdfs : audit_dfs_callbacks_erase EV forest (audit_dom_dfs_callbacks EV)).
  { unfold forest, dom_forest; apply audit_dom_dfs_callbacks_erases. }
  pose proof (audit_graph_prepare_nested_correct V V (audit_dom_body V) EV forest
    (audit_dom_prepare_callbacks EV (dom_children EV (Map.elements parents))) Hprepare) as
      Hprepared.
  destruct (audit_graph_prepare_nested_counted EV forest
    (audit_dom_prepare_callbacks EV (dom_children EV (Map.elements parents)))) as [fp prep_events].
  cbn [fst snd] in Hprepared; destruct Hprepared as [Hprepared [_ [Hprep_count _]]]; subst fp.
  pose proof (audit_dfs_nested_correct V V (audit_dom_body V) EV forest (prepare EV forest)
    (audit_dom_dfs_callbacks EV) FinSet.empty (Graph.entries forest) Hdfs) as Hsecond.
  destruct (audit_dfs_nested_counted (prepare EV forest) (audit_dom_dfs_callbacks EV)
    FinSet.empty (Graph.entries forest)) as [result dfs_events].
  cbn [fst snd] in Hsecond; destruct Hsecond as [_ [_ [Hsecond_count _]]].
  unfold audit_graph_prepare_full_event_bound in Hprep_count.
  unfold audit_dfs_full_input_event_bound in Hsecond_count.
  assert (Hnodes : length (Graph.nodes forest) =
    length (preorder (dfs p FinSet.empty (Graph.entries g)))) by reflexivity.
  assert (Hfuel : Pos.to_nat (fuel (prepare EV forest)) =
    2 * length (Graph.nodes forest) + edge_count forest + 2).
  { cbn [prepare fuel]; rewrite SuccNat2Pos.id_succ; lia. }
  rewrite Hnodes in Hprep_count, Hfuel.
  rewrite Hfuel in Hsecond_count.
  cbn [snd length]; repeat rewrite length_app; repeat rewrite length_map; cbn [length].
  nia.
Qed.

(** The same tree trace fits the stated original-input event bound. *)
Lemma audit_dom_tree_count_bound {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) parents :
  length (snd (audit_dom_tree_counted p parents)) <= audit_dom_input_event_bound p parents.
Proof.
  pose proof (audit_dom_tree_count_components EV g p parents) as Hcount.
  cbn zeta in Hcount.
  pose proof (audit_dom_live_length EV g p) as Hlive.
  pose proof (audit_dom_parent_rows_bound parents) as Hrows.
  set (live := length (preorder (dfs p FinSet.empty (Graph.entries g)))) in *.
  set (rows := length (Map.elements parents)) in *.
  set (q := S (audit_dom_input_scale p parents)) in *.
  assert (Hlive_q : live <= q).
  { unfold q, audit_dom_input_scale; lia. }
  assert (Hrows_q : rows <= q).
  { unfold q, audit_dom_input_scale; lia. }
  assert (Hq : 1 <= q) by (unfold q; lia).
  assert (Hproduct : live * rows <= q * q).
  { apply Nat.mul_le_mono; assumption. }
  assert (Hsecond : live * (40 * (3 + 2 * live + live * rows)) <=
    q * (40 * (3 + 2 * q + q * q))).
  { apply Nat.mul_le_mono; [exact Hlive_q|].
    apply Nat.mul_le_mono_l; lia. }
  assert (Hfirst : audit_dfs_full_input_event_bound p (Graph.entries g) <= 3 + 40 * q).
  { unfold audit_dfs_full_input_event_bound, q, audit_dom_input_scale; nia. }
  assert (Hsquare : q <= q * q) by nia.
  assert (Hcube : q * q <= q * q * q) by nia.
  assert (Hfour : q * q * q <= q * q * q * q) by nia.
  assert (Hlarge :
    3 + 40 * q + 1 + (1 + 3 * q) + (1 + 2 * q) + (8 + 12 * q + 8 * (q * q)) +
      (3 + q * (40 * (3 + 2 * q + q * q))) + 1 <= 1024 * (q * q * q * q)) by nia.
  assert (Hpower : q * q * q * q <= Nat.pow q 8).
  { cbn [Nat.pow]; nia. }
  unfold audit_dom_input_event_bound; fold q.
  nia.
Qed.

(** A child-map read charges its actual encoder body and encoded key width. *)
Lemma audit_dom_source_child_get_work {V E B} (enc : V -> positive * list B)
    (weight : B -> nat) key (input : Map.t V (list V)) :
  let events := snd (audit_map_get enc key input) in
  audit_dom_source_work weight (map (@DomSourceChild V E B) events) <=
    69 + 5 * Pos.size_nat (fst (enc key)) +
    audit_dom_source_external_work weight (map (@DomSourceChild V E B) events).
Proof.
  pose proof (audit_map_get_source_work_bound V (list V) B enc
    (fun body => fold_right (fun item n => weight item + n) 0 body) key input) as Hwork.
  unfold audit_map_get in Hwork |- *.
  destruct (enc key) as [code body].
  destruct (audit_map_code_get code input) as [result trace].
  cbn [fst snd map audit_dom_source_work audit_dom_source_external_work
    audit_dom_source_event_work audit_dom_source_event_external audit_map_source_work] in *.
  unfold audit_dom_source_work, audit_dom_source_external_work;
    cbn [fold_right audit_dom_source_event_work audit_dom_source_event_external
      audit_map_source_work].
  unfold audit_dom_source_event_work; cbn [audit_map_source_work].
  lia.
Qed.

(** A child-map write charges its actual encoder body and encoded key width. *)
Lemma audit_dom_source_child_set_work {V E B} (enc : V -> positive * list B)
    (weight : B -> nat) key value (input : Map.t V (list V)) :
  let events := snd (audit_map_set enc key value input) in
  audit_dom_source_work weight (map (@DomSourceChild V E B) events) <=
    66 + 16 * Pos.size_nat (fst (enc key)) +
    audit_dom_source_external_work weight (map (@DomSourceChild V E B) events).
Proof.
  pose proof (audit_map_set_source_work_bound V (list V) B enc
    (fun body => fold_right (fun item n => weight item + n) 0 body) key value input) as Hwork.
  unfold audit_map_set in Hwork |- *.
  destruct (enc key) as [code body].
  destruct (audit_trie_set code (key, value) input) as [result trace].
  cbn [fst snd map audit_dom_source_work audit_dom_source_external_work
    audit_dom_source_event_work audit_dom_source_event_external audit_map_source_work] in *.
  unfold audit_dom_source_work, audit_dom_source_external_work;
    cbn [fold_right audit_dom_source_event_work audit_dom_source_event_external
      audit_map_source_work].
  unfold audit_dom_source_event_work; cbn [audit_map_source_work].
  lia.
Qed.

(** A parent lookup charges its actual encoder body and encoded key width. *)
Lemma audit_dom_source_parent_get_work {V E B} (enc : V -> positive * list B)
    (weight : B -> nat) key (input : Map.t V V) :
  let events := snd (audit_map_get enc key input) in
  audit_dom_source_work weight (map (@DomSourceParent V E B) events) <=
    69 + 5 * Pos.size_nat (fst (enc key)) +
    audit_dom_source_external_work weight (map (@DomSourceParent V E B) events).
Proof.
  pose proof (audit_map_get_source_work_bound V V B enc
    (fun body => fold_right (fun item n => weight item + n) 0 body) key input) as Hwork.
  unfold audit_map_get in Hwork |- *.
  destruct (enc key) as [code body].
  destruct (audit_map_code_get code input) as [result trace].
  cbn [fst snd map audit_dom_source_work audit_dom_source_external_work
    audit_dom_source_event_work audit_dom_source_event_external audit_map_source_work] in *.
  unfold audit_dom_source_work, audit_dom_source_external_work;
    cbn [fold_right audit_dom_source_event_work audit_dom_source_event_external
      audit_map_source_work].
  unfold audit_dom_source_event_work; cbn [audit_map_source_work].
  lia.
Qed.

(** Concatenated source traces add their model work. *)
Lemma audit_dom_source_work_app {V E B} (weight : B -> nat)
    (left right : list (audit_dom_source_event V E B)) :
  audit_dom_source_work weight (left ++ right) =
    audit_dom_source_work weight left + audit_dom_source_work weight right.
Proof.
  unfold audit_dom_source_work; induction left as [|event rest IH]; cbn [List.app
    List.fold_right]; lia.
Qed.

(** Concatenated source traces add their actual external callback work. *)
Lemma audit_dom_source_external_app {V E B} (weight : B -> nat)
    (left right : list (audit_dom_source_event V E B)) :
  audit_dom_source_external_work weight (left ++ right) =
    audit_dom_source_external_work weight left + audit_dom_source_external_work weight right.
Proof.
  unfold audit_dom_source_external_work; induction left as [|event rest IH]; cbn [List.app
    List.fold_right]; lia.
Qed.

(** Root traversal work retains each read body and pays for its encoded width. *)
Lemma audit_dom_source_roots_work {V E B} (EV : encoding V) enc (weight : B -> nat)
    parents live width :
  (forall v, fst (enc v) = encode EV v) ->
  (forall v, In v live -> Pos.size_nat (encode EV v) <= width) ->
  let events := snd (@audit_dom_source_roots V E B enc parents live) in
  audit_dom_source_work weight events <=
    64 + length live * (133 + 5 * width) + audit_dom_source_external_work weight events.
Proof.
  intros Hencode; induction live as [|v rest IH]; intro Hwidth.
  - cbn [audit_dom_source_roots snd].
    unfold audit_dom_source_work, audit_dom_source_external_work.
    cbn [fold_right]; unfold audit_dom_source_event_work, audit_dom_source_event_external; lia.
  - pose proof (audit_dom_source_parent_get_work (E := E) enc weight v parents) as Hget.
    destruct (audit_map_get enc v parents) as [found reads] eqn:Hread.
    cbn [snd] in Hget.
    specialize (IH (fun x Hin => Hwidth x (or_intror Hin))).
    destruct (audit_dom_source_roots enc parents rest) as [roots events] eqn:Hrun.
    cbn [snd] in IH.
    pose proof (Hencode v) as Hcode; pose proof (Hwidth v (or_introl eq_refl)) as Hkey.
    destruct (enc v) as [code body] eqn:Henc; cbn [fst] in Hcode; subst code.
    cbn [fst] in Hget.
    cbn [audit_dom_source_roots]; rewrite Hread, Hrun; destruct found;
      change (64 + audit_dom_source_work weight (map DomSourceParent reads ++ events) <=
        64 + S (length rest) * (133 + 5 * width) +
          audit_dom_source_external_work weight (map DomSourceParent reads ++ events));
      rewrite audit_dom_source_work_app, audit_dom_source_external_app; nia.
Qed.

(** Child traversal work retains both map call bodies at each input binding. *)
Lemma audit_dom_source_children_work {V E B} (EV : encoding V) enc (weight : B -> nat)
    rows width :
  (forall v, fst (enc v) = encode EV v) ->
  (forall v u, In (v, u) rows -> Pos.size_nat (encode EV u) <= width) ->
  let events := snd (@audit_dom_source_children V E B enc rows) in
  audit_dom_source_work weight events <=
    64 + length rows * (199 + 21 * width) + audit_dom_source_external_work weight events.
Proof.
  intros Hencode; induction rows as [|[v u] rest IH]; intro Hwidth.
  - cbn [audit_dom_source_children snd].
    unfold audit_dom_source_work, audit_dom_source_external_work.
    cbn [fold_right]; unfold audit_dom_source_event_work, audit_dom_source_event_external; lia.
  - specialize (IH (fun x y Hin => Hwidth x y (or_intror Hin))).
    destruct (audit_dom_source_children enc rest) as [children events] eqn:Hrun.
    cbn [snd] in IH.
    pose proof (audit_dom_source_child_get_work (E := E) enc weight u children) as Hget.
    destruct (audit_map_get enc u children) as [found reads] eqn:Hread.
    cbn [snd] in Hget.
    pose proof (audit_dom_source_child_set_work (E := E) enc weight u
      (v :: match found with
       | Some row => row
       | None => []
       end) children) as Hset.
    destruct (audit_map_set enc u (v :: match found with
      | Some row => row
      | None => []
      end) children) as [next writes] eqn:Hwrite.
    cbn [snd] in Hset.
    pose proof (Hencode u) as Hcode; pose proof (Hwidth v u (or_introl eq_refl)) as Hkey.
    destruct (enc u) as [code body]; cbn [fst] in Hcode; subst code.
    cbn [fst] in Hget, Hset.
    cbn [audit_dom_source_children]; rewrite Hrun, Hread, Hwrite.
    change (64 + audit_dom_source_work weight (events ++ map DomSourceChild reads ++
      map DomSourceChild writes) <= 64 + S (length rest) * (199 + 21 * width) +
      audit_dom_source_external_work weight (events ++ map DomSourceChild reads ++
        map DomSourceChild writes)).
    repeat rewrite audit_dom_source_work_app; repeat rewrite audit_dom_source_external_app; nia.
Qed.

(** The forest out callback charges its internal lookup and actual encoder body. *)
Lemma audit_dom_source_out_work {V B} (enc : V -> positive * list B) (weight : B -> nat)
    children v :
  let body := snd (audit_dom_source_out enc children v) in
  fold_right (fun event n => audit_dom_source_body_work weight event + n) 0 body <=
    133 + 5 * Pos.size_nat (fst (enc v)) +
    fold_right (fun event n => audit_dom_source_body_external weight event + n) 0 body.
Proof.
  pose proof (audit_map_get_source_work_bound V (list V) B enc
    (fun body => fold_right (fun item n => weight item + n) 0 body) v children) as Hwork.
  unfold audit_dom_source_out, audit_map_get in *.
  destruct (enc v) as [code body].
  destruct (audit_map_code_get code children) as [found trace].
  cbn [fst snd map audit_map_source_work] in Hwork |- *.
  unfold audit_dom_source_body_work, audit_dom_source_body_external.
  cbn [fold_right audit_map_source_work]; lia.
Qed.

(** The forest encode callback preserves and charges its exact body. *)
Lemma audit_dom_source_encode_work {V B} (enc : V -> positive * list B) (weight : B -> nat) v :
  let body := snd (audit_dom_source_encode enc v) in
  fold_right (fun event n => audit_dom_source_body_work weight event + n) 0 body =
    64 + fold_right (fun event n => audit_dom_source_body_external weight event + n) 0 body.
Proof.
  unfold audit_dom_source_encode; destruct (enc v); reflexivity.
Qed.

(** One source DFS step preserves both stack provenance and discovered-vertex provenance. *)
Lemma audit_dom_dfs_step_vertices {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked vertices work :
  let edges := flat_map snd (Map.elements (out_index p)) in
  (forall edge, In edge edges -> In (Graph.target g edge) vertices) ->
  audit_dfs_stack_keys vertices edges (fst work) ->
  Forall (fun v => In v vertices) (DfsState.pre (snd work)) ->
  audit_dfs_stack_keys vertices edges (fst (dfs_step p blocked work)) /\
  Forall (fun v => In v vertices) (DfsState.pre (snd (dfs_step p blocked work))).
Proof.
  intros edges Hall Hstack Hpre; subst edges.
  pose proof (audit_dfs_step_keys p blocked vertices work Hall Hstack) as [_ Hnext].
  pose proof (audit_dfs_step_erases p blocked work) as Herase.
  rewrite Herase in Hnext; split; [exact Hnext|].
  destruct work as [stack st], stack as [|[v outgoing] rest].
  - exact Hpre.
  - inversion Hstack as [|frame tail Hframe Hrest]; subst frame tail.
    destruct Hframe as [Hv Hedge].
    destruct outgoing as [|edge outgoing].
    + exact Hpre.
    + cbn [dfs_step].
      destruct (FinSet.mem EV (Graph.target g edge) blocked ||
        FinSet.mem EV (Graph.target g edge) (DfsState.seen st)).
      * exact Hpre.
      * cbn [dfs_discover]; constructor; [apply Hall, Hedge; left; reflexivity|exact Hpre].
Qed.

(** A binary DFS run keeps every discovered vertex in its input-derived envelope. *)
Lemma audit_dom_dfs_run_vertices {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked vertices fuel work :
  let edges := flat_map snd (Map.elements (out_index p)) in
  (forall edge, In edge edges -> In (Graph.target g edge) vertices) ->
  audit_dfs_stack_keys vertices edges (fst work) ->
  Forall (fun v => In v vertices) (DfsState.pre (snd work)) ->
  audit_dfs_stack_keys vertices edges (fst (dfs_run p blocked fuel work)) /\
  Forall (fun v => In v vertices) (DfsState.pre (snd (dfs_run p blocked fuel work))).
Proof.
  intros edges Hall Hstack Hpre; subst edges.
  rewrite (dfs_run_agrees EV g p blocked fuel work).
  induction fuel using Pos.peano_ind.
  - cbn; apply audit_dom_dfs_step_vertices; assumption.
  - rewrite Pos.iter_succ.
    apply audit_dom_dfs_step_vertices; [exact Hall|exact (proj1 IHfuel)|exact (proj2 IHfuel)].
Qed.

(** Searching one root preserves discovered-vertex provenance. *)
Lemma audit_dom_dfs_root_vertices {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked vertices st root :
  (forall edge, In edge (flat_map snd (Map.elements (out_index p))) ->
    In (Graph.target g edge) vertices) ->
  In root vertices -> Forall (fun v => In v vertices) (DfsState.pre st) ->
  Forall (fun v => In v vertices) (DfsState.pre (dfs_root p blocked st root)).
Proof.
  intros Hall Hroot Hpre; unfold dfs_root.
  destruct (FinSet.mem EV root blocked || FinSet.mem EV root (DfsState.seen st)).
  - exact Hpre.
  - assert (Hstack : audit_dfs_stack_keys vertices (flat_map snd (Map.elements (out_index p)))
      [(root, succ_edges p root)]).
    { constructor; [|constructor]. cbn; split; [exact Hroot|].
      unfold succ_edges, index_edges.
      destruct (Map.get EV root (out_index p)) as [outgoing|] eqn:Hget.
      - now apply (audit_dfs_outgoing_edges p root outgoing Hget).
      - intros edge Hfalse; contradiction. }
    assert (Hinitial : Forall (fun v => In v vertices)
      (DfsState.pre (dfs_discover EV root None st))).
    { cbn [dfs_discover]; constructor; assumption. }
    exact (proj2 (audit_dom_dfs_run_vertices p blocked vertices (fuel p)
      ([(root, succ_edges p root)], dfs_discover EV root None st) Hall Hstack Hinitial)).
Qed.

(** All roots preserve the same discovered-vertex envelope. *)
Lemma audit_dom_dfs_roots_vertices {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked vertices roots st :
  (forall edge, In edge (flat_map snd (Map.elements (out_index p))) ->
    In (Graph.target g edge) vertices) ->
  incl roots vertices -> Forall (fun v => In v vertices) (DfsState.pre st) ->
  Forall (fun v => In v vertices)
    (DfsState.pre (fold_left (dfs_root p blocked) roots st)).
Proof.
  intros Hall; revert st; induction roots as [|root rest IH]; intros st Hroots Hpre.
  - exact Hpre.
  - cbn [fold_left]; apply IH.
    + intros v Hin; apply Hroots; right; exact Hin.
    + apply audit_dom_dfs_root_vertices; [exact Hall|apply Hroots; left; reflexivity|exact Hpre].
Qed.

(** Every discovered vertex is a root or the target of an indexed edge. *)
Lemma audit_dom_live_envelope {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) :
  incl (preorder (dfs p FinSet.empty (Graph.entries g)))
    (Graph.entries g ++ map (Graph.target g) (flat_map snd (Map.elements (out_index p)))).
Proof.
  set (vertices := Graph.entries g ++
    map (Graph.target g) (flat_map snd (Map.elements (out_index p)))).
  assert (Hall : forall edge, In edge (flat_map snd (Map.elements (out_index p))) ->
    In (Graph.target g edge) vertices).
  { intros edge Hin; unfold vertices; apply in_or_app; right; now apply in_map. }
  assert (Hroots : incl (Graph.entries g) vertices).
  { intros v Hin; unfold vertices; apply in_or_app; now left. }
  pose proof (audit_dom_dfs_roots_vertices p FinSet.empty vertices (Graph.entries g) dfs_initial
    Hall Hroots (Forall_nil _)) as Hpre.
  intros v Hin; unfold dfs in Hin; cbn [preorder] in Hin; rewrite <- rev_alt, in_rev,
    rev_involutive in Hin.
  apply Forall_forall with (x := v) in Hpre; [exact Hpre|exact Hin].
Qed.

(** Live vertices have encoded width bounded by the original full DFS input. *)
Lemma audit_dom_live_width {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) v :
  In v (preorder (dfs p FinSet.empty (Graph.entries g))) ->
  audit_key_bits_weight (encode EV v) <= audit_dfs_full_input_width EV g p (Graph.entries g).
Proof.
  intro Hin; apply audit_dfs_envelope_width.
  now apply (audit_dom_live_envelope EV g p).
Qed.

(** Every parent binding's key and value are covered by the input width. *)
Lemma audit_dom_parent_width {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) parents v u :
  In (v, u) (Map.elements parents) ->
  Pos.size_nat (encode EV v) <= audit_dom_input_width EV g p parents /\
  Pos.size_nat (encode EV u) <= audit_dom_input_width EV g p parents.
Proof.
  intro Hin; unfold audit_dom_input_width, audit_key_bits_weight.
  split.
  - eapply Nat.le_trans; [|apply Nat.le_max_r].
    apply (audit_dfs_width_member (fun x => Pos.size_nat (encode EV x))); apply in_or_app; left;
      apply in_map_iff.
    exists (v, u); split; [reflexivity|exact Hin].
  - eapply Nat.le_trans; [|apply Nat.le_max_r].
    apply (audit_dfs_width_member (fun x => Pos.size_nat (encode EV x))); apply in_or_app;
      right; apply in_map_iff.
    exists (v, u); split; [reflexivity|exact Hin].
Qed.

(** Every live vertex is covered by the same original-input width. *)
Lemma audit_dom_live_input_width {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) parents v :
  In v (preorder (dfs p FinSet.empty (Graph.entries g))) ->
  Pos.size_nat (encode EV v) <= audit_dom_input_width EV g p parents.
Proof.
  intro Hin; pose proof (audit_dom_live_width EV g p v Hin) as Hwidth.
  unfold audit_dom_input_width; eapply Nat.le_trans; [exact Hwidth|apply Nat.le_max_l].
Qed.

(** A maximum fold remains bounded when every selected value and its base are bounded. *)
Lemma audit_dom_max_fold_bound {A} (width : A -> nat) values base bound :
  base <= bound -> (forall x, In x values -> width x <= bound) ->
  fold_right (fun x n => Nat.max (width x) n) base values <= bound.
Proof.
  intros Hbase; induction values as [|v rest IH]; intro Hwidth.
  - exact Hbase.
  - cbn [fold_right]; apply Nat.max_lub.
    + apply Hwidth; left; reflexivity.
    + apply IH; intros x Hin; apply Hwidth; now right.
Qed.

(** Preparing the forest uses only widths already present in the original inputs. *)
Lemma audit_dom_forest_prepare_width {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) parents :
  audit_graph_prepare_input_width EV (dom_forest p parents) <=
    audit_dom_input_width EV g p parents.
Proof.
  unfold audit_graph_prepare_input_width, dom_forest; cbn [Graph.nodes Graph.out Graph.target].
  set (live := preorder (dfs p FinSet.empty (Graph.entries g))).
  assert (Hlive : forall v, In v live ->
    audit_key_bits_weight (encode EV v) <= audit_dom_input_width EV g p parents).
  { intros v Hin; apply audit_dom_live_input_width; exact Hin. }
  assert (Hedge : forall u v, In v (index_edges EV (dom_children EV (Map.elements parents)) u) ->
    audit_key_bits_weight (encode EV v) <= audit_dom_input_width EV g p parents).
  { intros u v Hin; apply dom_children_in in Hin.
    exact (proj1 (audit_dom_parent_width EV g p parents v u Hin)). }
  induction live as [|v rest IH].
  - cbn; lia.
  - cbn [fold_right]; apply Nat.max_lub.
    + apply Hlive; left; reflexivity.
    + apply audit_dom_max_fold_bound.
      * apply IH; intros x Hin; apply Hlive; now right.
      * intros edge Hin; now apply (Hedge v edge).
Qed.

(** Each forest DFS capture charges its one internal wrapper and its actual external body. *)
Lemma audit_dom_dfs_capture_work {V B} (enc : V -> positive * list B) (weight : B -> nat)
    capture :
  audit_dfs_capture_receipt
    (AuditDfsCallbackModel V V (audit_dom_source_body V B) audit_dom_source_target
      (audit_dom_source_encode enc)) capture ->
  audit_graph_capture_work (audit_dom_source_body_work weight) capture <=
    64 + audit_graph_capture_work (audit_dom_source_body_external weight) capture.
Proof.
  intro Hreceipt; destruct capture as [edge value body|vertex code body];
    cbn [audit_dfs_capture_receipt audit_dfs_target_model audit_dfs_encode_model] in Hreceipt.
  - unfold audit_dom_source_target in Hreceipt; inversion Hreceipt; subst body.
    unfold audit_graph_capture_work, audit_dom_source_body_work, audit_dom_source_body_external;
      cbn; lia.
  - pose proof (audit_dom_source_encode_work enc weight vertex) as Hbody.
    rewrite Hreceipt in Hbody; cbn [snd audit_graph_capture_work] in *; lia.
Qed.

(** A well-formed forest DFS event retains at most one charged wrapper. *)
Lemma audit_dom_dfs_event_work {V B} (enc : V -> positive * list B) (weight : B -> nat) item :
  audit_dfs_source_event_wellformed item ->
  audit_dfs_event_receipts
    (AuditDfsCallbackModel V V (audit_dom_source_body V B) audit_dom_source_target
      (audit_dom_source_encode enc)) item ->
  fold_right (fun capture n => audit_graph_capture_work (audit_dom_source_body_work weight)
    capture + n) 0 (snd item) <=
  64 + fold_right (fun capture n => audit_graph_capture_work (audit_dom_source_body_external weight)
    capture + n) 0 (snd item).
Proof.
  intros Hshape Hreceipts.
  pose proof (audit_virtual_dfs_capture_count V V (audit_dom_source_body V B) item Hshape) as
    Hcount.
  unfold audit_dfs_event_receipts in Hreceipts.
  destruct (snd item) as [|capture rest].
  - cbn; lia.
  - destruct rest as [|next rest]; cbn in Hcount; [|lia].
    inversion Hreceipts as [|? ? Hreceipt Htail].
    pose proof (audit_dom_dfs_capture_work enc weight capture Hreceipt); cbn; lia.
Qed.

(** Forest DFS callback work is bounded on the same captured events. *)
Lemma audit_dom_dfs_body_work {V B} (enc : V -> positive * list B) (weight : B -> nat) events :
  Forall audit_dfs_source_event_wellformed events ->
  Forall (audit_dfs_event_receipts
    (AuditDfsCallbackModel V V (audit_dom_source_body V B) audit_dom_source_target
      (audit_dom_source_encode enc))) events ->
  audit_dfs_source_body_work (audit_dom_source_body_work weight) events <=
    64 * length events + audit_dfs_source_body_work (audit_dom_source_body_external weight) events.
Proof.
  intros Hshape Hreceipts; induction Hshape as [|item rest Hitem Htail IH].
  - reflexivity.
  - inversion Hreceipts as [|? ? Hreceipt Hrest]; subst.
    specialize (IH Hrest).
    pose proof (audit_dom_dfs_event_work enc weight item Hitem Hreceipt) as Hbound.
    change (fold_right (fun capture n => audit_graph_capture_work (audit_dom_source_body_work
      weight)
      capture + n) 0 (snd item) + audit_dfs_source_body_work (audit_dom_source_body_work weight)
      rest <= 64 * length (item :: rest) +
      (fold_right (fun capture n => audit_graph_capture_work (audit_dom_source_body_external weight)
        capture + n) 0 (snd item) +
      audit_dfs_source_body_work (audit_dom_source_body_external weight) rest)).
    cbn [length]; lia.
Qed.

(** Each forest preparation callback charges its own internal work and external body. *)
Lemma audit_dom_prepare_event_work {V B} (EV : encoding V) (g : Graph.t V V)
    (enc : V -> positive * list B) (weight : B -> nat) children item :
  (forall v, fst (enc v) = encode EV v) ->
  audit_source_receipt
    (AuditPrepareCallbackModel V V (audit_dom_source_body V B)
      (audit_dom_source_out enc children) audit_dom_source_target (audit_dom_source_encode enc))
        item ->
  audit_prepare_out_in_nodes V V (audit_dom_source_body V B) (Graph.nodes g) item ->
  audit_prepare_source_body_event_work (audit_dom_source_body_work weight) item <=
    133 + 5 * audit_graph_prepare_input_width EV g +
    audit_prepare_source_body_event_work (audit_dom_source_body_external weight) item.
Proof.
  intros Hencode Hreceipt Hnode.
  destruct item as [site|v outgoing body|edge target body|map_event|amount|nodes edges fuel];
    cbn [audit_source_receipt audit_prepare_out_in_nodes audit_prepare_out_model
      audit_prepare_target_model audit_prepare_encode_model audit_prepare_source_body_event_work]
      in *; try lia.
  - pose proof (audit_dom_source_out_work enc weight children v) as Hout.
    rewrite Hreceipt in Hout; cbn [snd] in Hout.
    pose proof (Hencode v) as Hcode.
    pose proof (audit_input_width_node V V EV g v Hnode) as Hwidth.
    unfold audit_key_bits_weight in Hwidth.
    destruct (enc v) as [code encoded_body]; cbn [fst] in Hcode, Hout; subst code; lia.
  - unfold audit_dom_source_target in Hreceipt; inversion Hreceipt; subst body.
    unfold audit_dom_source_body_work, audit_dom_source_body_external; cbn; lia.
  - destruct map_event as [key code input output body trace|key value code input output body trace|
      key code input output body trace]; cbn [audit_source_receipt audit_prepare_encode_model
        audit_prepare_source_body_event_work] in *;
      pose proof (audit_dom_source_encode_work enc weight key) as Hbody;
      rewrite Hreceipt in Hbody; cbn [snd] in Hbody; lia.
Qed.

(** The complete forest preparation trace retains all actual external bodies. *)
Lemma audit_dom_prepare_body_work {V B} (EV : encoding V) (g : Graph.t V V)
    (enc : V -> positive * list B) (weight : B -> nat) children events :
  (forall v, fst (enc v) = encode EV v) ->
  Forall (audit_source_receipt
    (AuditPrepareCallbackModel V V (audit_dom_source_body V B)
      (audit_dom_source_out enc children) audit_dom_source_target (audit_dom_source_encode enc)))
    events ->
  Forall (audit_prepare_out_in_nodes V V (audit_dom_source_body V B) (Graph.nodes g)) events ->
  audit_prepare_source_body_work (audit_dom_source_body_work weight) events <=
    length events * (133 + 5 * audit_graph_prepare_input_width EV g) +
    audit_prepare_source_body_work (audit_dom_source_body_external weight) events.
Proof.
  intros Hencode Hreceipts Hnodes; induction Hreceipts as [|item rest Hreceipt Htail IH].
  - reflexivity.
  - inversion Hnodes as [|? ? Hnode Hrest]; subst.
    specialize (IH Hrest).
    pose proof (audit_dom_prepare_event_work EV g enc weight children item Hencode Hreceipt Hnode)
      as Hbound.
    change (audit_prepare_source_body_event_work (audit_dom_source_body_work weight) item +
      audit_prepare_source_body_work (audit_dom_source_body_work weight) rest <=
      length (item :: rest) * (133 + 5 * audit_graph_prepare_input_width EV g) +
      (audit_prepare_source_body_event_work (audit_dom_source_body_external weight) item +
       audit_prepare_source_body_work (audit_dom_source_body_external weight) rest)).
    cbn [length]; nia.
Qed.

(** Appending one trie branch adds one bit to the accumulated path bound. *)
Lemma audit_dom_path_child_bound (path : positive -> positive) depth :
  (forall p, Pos.size_nat (path p) <= depth + Pos.size_nat p) ->
  (forall p, Pos.size_nat (path (xO p)) <= S depth + Pos.size_nat p) /\
  (forall p, Pos.size_nat (path (xI p)) <= S depth + Pos.size_nat p).
Proof.
  intro Hpath; split; intro p.
  - specialize (Hpath (xO p)); cbn [Pos.size_nat] in Hpath; lia.
  - specialize (Hpath (xI p)); cbn [Pos.size_nat] in Hpath; lia.
Qed.

(** Enumeration's position bits are bounded by trie nodes and incoming path depth. *)
Lemma audit_dom_elements_bits_bound {A} (node : Trie.ne A) :
  forall path depth,
    (forall p, Pos.size_nat (path p) <= depth + Pos.size_nat p) ->
    audit_elements_bits path node <= audit_elements_nodes node * (depth + audit_elements_nodes
      node).
Proof.
  induction node as [r IHr|value|value r IHr|l IHl|l IHl r IHr|
    l IHl value|l IHl value r IHr]; intros path depth Hpath;
    cbn [audit_elements_bits audit_elements_nodes].
  - destruct (audit_dom_path_child_bound path depth Hpath) as [_ Hr].
    specialize (IHr (fun p => path (xI p)) (S depth) Hr); nia.
  - specialize (Hpath xH); cbn [Pos.size_nat] in Hpath; lia.
  - destruct (audit_dom_path_child_bound path depth Hpath) as [_ Hr].
    specialize (IHr (fun p => path (xI p)) (S depth) Hr).
    specialize (Hpath xH); cbn [Pos.size_nat] in Hpath; nia.
  - destruct (audit_dom_path_child_bound path depth Hpath) as [Hl _].
    specialize (IHl (fun p => path (xO p)) (S depth) Hl); nia.
  - destruct (audit_dom_path_child_bound path depth Hpath) as [Hl Hr].
    specialize (IHl (fun p => path (xO p)) (S depth) Hl).
    specialize (IHr (fun p => path (xI p)) (S depth) Hr); nia.
  - destruct (audit_dom_path_child_bound path depth Hpath) as [Hl _].
    specialize (IHl (fun p => path (xO p)) (S depth) Hl).
    specialize (Hpath xH); cbn [Pos.size_nat] in Hpath; nia.
  - destruct (audit_dom_path_child_bound path depth Hpath) as [Hl Hr].
    specialize (IHl (fun p => path (xO p)) (S depth) Hl).
    specialize (IHr (fun p => path (xI p)) (S depth) Hr).
    specialize (Hpath xH); cbn [Pos.size_nat] in Hpath; nia.
Qed.

(** Enumerating a trie emits at most a quadratic number of position bits. *)
Lemma audit_dom_trie_output_bits_bound {A} (input : Trie.t A) :
  audit_trie_output_bits input <= audit_trie_nodes input * audit_trie_nodes input.
Proof.
  destruct input as [|node].
  - reflexivity.
  - cbn [audit_trie_output_bits audit_trie_nodes].
    pose proof (audit_dom_elements_bits_bound node (fun p => p) 0) as Hbound.
    cbn in Hbound; apply Hbound; intro p; lia.
Qed.

(** Initial DFS events retain the same work and add one wrapper per event. *)
Lemma audit_dom_initial_events_work {V E B} (weight : B -> nat) events :
  audit_dom_source_work weight (map (@DomSourceInitialDfs V E B) events) =
    64 * length events + audit_dfs_source_work weight events /\
  audit_dom_source_external_work weight (map (@DomSourceInitialDfs V E B) events) =
    audit_dfs_source_body_work weight events.
Proof.
  induction events as [|event rest IH].
  - split; reflexivity.
  - destruct IH as [Hwork Hbody]; split.
    + change (64 + audit_dfs_source_event_work weight event +
        audit_dom_source_work weight (map DomSourceInitialDfs rest) =
        64 * S (length rest) +
          (audit_dfs_source_event_work weight event + audit_dfs_source_work weight rest)).
      rewrite Hwork; lia.
    + change (audit_dfs_source_body_work weight [event] +
        audit_dom_source_external_work weight (map DomSourceInitialDfs rest) =
        audit_dfs_source_body_work weight (event :: rest)).
      rewrite Hbody; unfold audit_dfs_source_body_work; cbn [fold_right]; lia.
Qed.

(** Map enumeration events retain their full source-frame work. *)
Lemma audit_dom_element_events_work {V E B} (weight : B -> nat) events :
  audit_dom_source_work weight (map (@DomSourceElements V E B) events) =
    64 * length events + audit_elements_work events /\
  audit_dom_source_external_work weight (map (@DomSourceElements V E B) events) = 0.
Proof.
  induction events as [|event rest IH].
  - split; reflexivity.
  - destruct IH as [Hwork Hbody]; split.
    + change (64 + audit_elements_frame_work event +
        audit_dom_source_work weight (map (@DomSourceElements V E B) rest) =
        64 * S (length rest) + (audit_elements_frame_work event + audit_elements_work rest)).
      rewrite Hwork; lia.
    + change (audit_dom_source_external_work weight (map (@DomSourceElements V E B) rest) = 0).
      exact Hbody.
Qed.

(** Forest preparation events retain their work and their captured external bodies. *)
Lemma audit_dom_prepare_events_work {V E B} (weight : B -> nat) events :
  audit_dom_source_work weight (map (@DomSourcePrepare V E B) events) =
    64 * length events + audit_prepare_source_work (audit_dom_source_body_work weight) events /\
  audit_dom_source_external_work weight (map (@DomSourcePrepare V E B) events) =
    audit_prepare_source_body_work (audit_dom_source_body_external weight) events.
Proof.
  induction events as [|event rest IH].
  - split; reflexivity.
  - destruct IH as [Hwork Hbody]; split.
    + change (64 + audit_prepare_source_event_work (audit_dom_source_body_work weight) event +
        audit_dom_source_work weight (map (@DomSourcePrepare V E B) rest) = 64 * S (length rest) +
        (audit_prepare_source_event_work (audit_dom_source_body_work weight) event +
          audit_prepare_source_work (audit_dom_source_body_work weight) rest)).
      rewrite Hwork; lia.
    + change (audit_prepare_source_body_work (audit_dom_source_body_external weight) [event] +
        audit_dom_source_external_work weight (map (@DomSourcePrepare V E B) rest) =
        audit_prepare_source_body_work (audit_dom_source_body_external weight) (event :: rest)).
      rewrite Hbody; unfold audit_prepare_source_body_work; cbn [fold_right]; lia.
Qed.

(** Forest DFS events retain their work and their captured external bodies. *)
Lemma audit_dom_dfs_events_work {V E B} (weight : B -> nat) events :
  audit_dom_source_work weight (map (@DomSourceDfs V E B) events) =
    64 * length events + audit_dfs_source_work (audit_dom_source_body_work weight) events /\
  audit_dom_source_external_work weight (map (@DomSourceDfs V E B) events) =
    audit_dfs_source_body_work (audit_dom_source_body_external weight) events.
Proof.
  induction events as [|event rest IH].
  - split; reflexivity.
  - destruct IH as [Hwork Hbody]; split.
    + change (64 + audit_dfs_source_event_work (audit_dom_source_body_work weight) event +
        audit_dom_source_work weight (map (@DomSourceDfs V E B) rest) = 64 * S (length rest) +
        (audit_dfs_source_event_work (audit_dom_source_body_work weight) event +
          audit_dfs_source_work (audit_dom_source_body_work weight) rest)).
      rewrite Hwork; lia.
    + change (audit_dfs_source_body_work (audit_dom_source_body_external weight) [event] +
        audit_dom_source_external_work weight (map (@DomSourceDfs V E B) rest) =
        audit_dfs_source_body_work (audit_dom_source_body_external weight) (event :: rest)).
      rewrite Hbody; unfold audit_dfs_source_body_work; cbn [fold_right]; lia.
Qed.

(** The DFS source budget also pays two fixed wrapper frames per event. *)
Lemma audit_dom_dfs_source_slack {V E B} {EV} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (weight : B -> nat) blocked roots :
  audit_dfs_callbacks_erase EV g cb ->
  let events := snd (audit_dfs_source_counted p cb blocked roots) in
  128 * length events + audit_dfs_source_work weight events <=
    audit_dfs_source_budget EV g p roots + audit_dfs_source_body_work weight events.
Proof.
  intro Hcallbacks.
  pose proof (audit_dfs_source_result_and_count p cb blocked roots Hcallbacks) as [_ Hcount].
  pose proof (audit_dfs_source_event_work_bound p cb weight blocked roots Hcallbacks) as Hwork.
  destruct (audit_dfs_source_counted p cb blocked roots) as [result events].
  cbn [fst snd] in Hcount, Hwork |- *.
  cbn zeta in Hwork.
  unfold audit_dfs_source_budget.
  set (count := length events) in *.
  set (bound := audit_dfs_full_input_event_bound p roots) in *.
  set (output_bound := 2 * (2 + length roots * S (Pos.to_nat (fuel p)))) in *.
  set (width := Nat.max (audit_dfs_full_input_width EV g p roots)
    (Pos.size_nat (Pos.of_succ_nat (S (length roots) * S (Pos.to_nat (fuel p)))))) in *.
  assert (Houtput : output_bound <= 2 * bound).
  { unfold output_bound, bound, audit_dfs_full_input_event_bound; nia. }
  assert (Hlinear : count * (512 + 64 * width) <= bound * (512 + 64 * width)).
  { apply Nat.mul_le_mono_r; exact Hcount. }
  assert (Hextra : count * (2 * output_bound) + 128 * count <= 132 * S bound * S bound).
  { assert (Hfirst : count * (2 * output_bound) <= 4 * S bound * S bound).
    { replace (4 * S bound * S bound) with (S bound * (4 * S bound)) by nia.
      apply Nat.mul_le_mono; lia. }
    assert (Hsecond : 128 * count <= 128 * S bound * S bound) by nia.
    nia. }
  rewrite Nat.mul_add_distr_l in Hwork; nia.
Qed.

(** The polynomial reserve covers enumeration, indexing and preparation wrappers. *)
Lemma audit_dom_source_reserve_arithmetic size width nodes live prep_count :
  1 <= size -> nodes <= size -> live <= size -> prep_count <= 8 + 20 * size ->
  65 * (17 * nodes + nodes * nodes + 4) +
    (64 + nodes * (199 + 21 * width)) + (64 + live * (133 + 5 * width)) +
    prep_count * (197 + 5 * width) <=
      (1024 * 1024)%nat * Nat.pow size 8 * S width * S width.
Proof.
  intros Hsize Hnodes Hlive Hprep.
  set (w := S width).
  set (reserve := size * size * (w * w)).
  assert (Hw : 1 <= w) by (unfold w; lia).
  assert (Hsize2 : size <= size * size) by nia.
  assert (Hw2 : 1 <= w * w) by nia.
  assert (Hwidth2 : width <= w * w) by (unfold w in *; nia).
  assert (Hsmall : size <= reserve).
  { unfold reserve; replace size with (size * 1) at 1 by lia.
    apply Nat.mul_le_mono; assumption. }
  assert (Hone : 1 <= reserve) by lia.
  assert (Hnodes_square : nodes * nodes <= reserve).
  { unfold reserve; replace (nodes * nodes) with ((nodes * nodes) * 1) at 1 by lia.
    apply Nat.mul_le_mono; [apply Nat.mul_le_mono; lia|exact Hw2]. }
  assert (Hnodes_width : nodes * width <= reserve).
  { unfold reserve; apply Nat.mul_le_mono; lia. }
  assert (Hlive_width : live * width <= reserve).
  { unfold reserve; apply Nat.mul_le_mono; lia. }
  assert (Hprep_size : prep_count <= 28 * reserve) by nia.
  assert (Hwidth : width <= reserve).
  { unfold reserve; replace width with (1 * width) at 1 by lia.
    apply Nat.mul_le_mono; lia. }
  assert (Hsize_width : size * width <= reserve).
  { unfold reserve; apply Nat.mul_le_mono; assumption. }
  assert (Hprep_width : prep_count * width <= 28 * reserve).
  { assert (Hproduct : prep_count * width <= (8 + 20 * size) * width)
      by (apply Nat.mul_le_mono_r; exact Hprep).
    nia. }
  assert (Hlocal :
    65 * (17 * nodes + nodes * nodes + 4) +
      (64 + nodes * (199 + 21 * width)) + (64 + live * (133 + 5 * width)) +
      prep_count * (197 + 5 * width) <= (8 * 1024)%nat * reserve).
  { clear - Hnodes Hlive Hsmall Hone Hnodes_square Hnodes_width Hlive_width Hprep_size Hprep_width.
    nia. }
  assert (Hpower : size * size <= Nat.pow size 8).
  { replace (size * size) with (Nat.pow size 2) by (cbn [Nat.pow]; lia).
    apply Nat.pow_le_mono_r; lia. }
  assert (Hscale : reserve <= Nat.pow size 8 * w * w).
  { unfold reserve; replace (size * size * (w * w)) with (size * size * w * w) by nia.
    apply Nat.mul_le_mono_r, Nat.mul_le_mono_r; exact Hpower. }
  fold w.
  replace ((1024 * 1024)%nat * Nat.pow size 8 * w * w) with
    ((1024 * 1024)%nat * (Nat.pow size 8 * w * w)) by nia.
  eapply Nat.le_trans; [exact Hlocal|].
  apply Nat.mul_le_mono; [lia|exact Hscale].
Qed.

(** Forest preparation callbacks erase to the forest's graph operations. *)
Lemma audit_dom_source_prepare_callbacks {V E B} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) parents enc :
  (forall v, fst (enc v) = encode EV v) ->
  audit_prepare_callbacks_erase EV (dom_forest p parents)
    (AuditPrepareCallbackModel V V (audit_dom_source_body V B)
      (audit_dom_source_out enc (dom_children EV (Map.elements parents))) audit_dom_source_target
      (audit_dom_source_encode enc)).
Proof.
  intro Hencode; unfold audit_prepare_callbacks_erase; cbn [audit_prepare_out_model
    audit_prepare_target_model audit_prepare_encode_model].
  split.
  - intro v; unfold dom_forest; cbn [Graph.out]; apply audit_dom_source_out_erases; exact Hencode.
  - split.
    + intro v; reflexivity.
    + intro v; apply audit_dom_source_encode_erases; exact Hencode.
Qed.

(** Forest DFS callbacks erase to the forest's target and encoding. *)
Lemma audit_dom_source_dfs_callbacks {V E B} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) parents enc :
  (forall v, fst (enc v) = encode EV v) ->
  audit_dfs_callbacks_erase EV (dom_forest p parents)
    (AuditDfsCallbackModel V V (audit_dom_source_body V B) audit_dom_source_target
      (audit_dom_source_encode enc)).
Proof.
  intro Hencode; unfold audit_dfs_callbacks_erase; cbn [audit_dfs_target_model
    audit_dfs_encode_model].
  split.
  - intro v; reflexivity.
  - intro v; apply audit_dom_source_encode_erases; exact Hencode.
Qed.

(** A parent binding's value width is included in the receipt's row-width fold. *)
Lemma audit_dom_parent_row_width {V} (EV : encoding V) parents v u :
  In (v, u) (Map.elements parents) ->
  Pos.size_nat (encode EV u) <=
    fold_right Nat.max 0 (map (fun row => Nat.max (Pos.size_nat (encode EV (fst row)))
      (Pos.size_nat (encode EV (snd row)))) (Map.elements parents)).
Proof.
  intro Hin; eapply Nat.le_trans with
    (m := Nat.max (Pos.size_nat (encode EV v)) (Pos.size_nat (encode EV u)));
    [apply Nat.le_max_r|].
  apply (audit_dfs_width_member (fun row => Nat.max (Pos.size_nat (encode EV (fst row)))
    (Pos.size_nat (encode EV (snd row)))) (Map.elements parents) (v, u)); exact Hin.
Qed.

(** Child and root index traces retain their actual external bodies and fit input widths. *)
Lemma audit_dom_index_trace_bounds {V E B} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) parents enc (weight : B -> nat) width child_events root_events :
  (forall v, fst (enc v) = encode EV v) ->
  audit_dfs_full_input_width EV g p (Graph.entries g) <= width ->
  fold_right Nat.max 0 (map (fun row => Nat.max (Pos.size_nat (encode EV (fst row)))
    (Pos.size_nat (encode EV (snd row)))) (Map.elements parents)) <= width ->
  snd (@audit_dom_source_children V E B enc (Map.elements parents)) = child_events ->
  snd (@audit_dom_source_roots V E B enc parents
    (preorder (dfs p FinSet.empty (Graph.entries g)))) = root_events ->
  audit_dom_source_work weight child_events <=
    64 + audit_trie_nodes parents * (199 + 21 * width) +
      audit_dom_source_external_work weight child_events /\
  audit_dom_source_work weight root_events <=
    64 + length (preorder (dfs p FinSet.empty (Graph.entries g))) * (133 + 5 * width) +
      audit_dom_source_external_work weight root_events.
Proof.
  intros Henc Hdfs Hrows Hchild Hroot.
  assert (Hrow_width : forall v u, In (v, u) (Map.elements parents) ->
    Pos.size_nat (encode EV u) <= width).
  { intros v u Hin; pose proof (audit_dom_parent_row_width EV parents v u Hin). lia. }
  assert (Hlive_width : forall v, In v (preorder (dfs p FinSet.empty (Graph.entries g))) ->
    Pos.size_nat (encode EV v) <= width).
  { intros v Hin; pose proof (audit_dom_live_width EV g p v Hin).
    unfold audit_key_bits_weight in *. lia. }
  pose proof (audit_dom_source_children_work (E := E) EV enc weight (Map.elements parents) width
    Henc Hrow_width) as Hchild_work.
  pose proof (audit_dom_source_roots_work (E := E) EV enc weight parents
    (preorder (dfs p FinSet.empty (Graph.entries g))) width Henc Hlive_width) as Hroot_work.
  cbn zeta in Hchild_work, Hroot_work; rewrite Hchild in Hchild_work; rewrite Hroot in Hroot_work.
  assert (Hparent_count : length (Map.elements parents) <= audit_trie_nodes parents).
  { pose proof (audit_map_elements_quantitative V V parents) as [Hbound _].
    pose proof (audit_map_elements_erases V V parents) as Hrow.
    rewrite Hrow in Hbound; exact Hbound. }
  assert (Hmul : length (Map.elements parents) * (199 + 21 * width) <=
    audit_trie_nodes parents * (199 + 21 * width)).
  { apply Nat.mul_le_mono_r; exact Hparent_count. }
  split; lia.
Qed.

(** Trie enumeration frames fit the same node-derived scalar envelope. *)
Lemma audit_dom_source_elements_bound {V} (parents : Map.t V V) element_events :
  snd (audit_map_elements parents) = element_events ->
  64 * length element_events + audit_elements_work element_events <=
    65 * (17 * audit_trie_nodes parents + audit_trie_nodes parents * audit_trie_nodes parents + 4).
Proof.
  intro Helement.
  pose proof (audit_map_elements_quantitative V V parents) as [_ Hwork].
  rewrite Helement in Hwork.
  pose proof (audit_dom_trie_output_bits_bound parents) as Hbits.
  pose proof (audit_erase_elements_count _ element_events) as Hcount.
  nia.
Qed.

(** Forest preparation work includes each captured body and its width charge. *)
Lemma audit_dom_source_prepare_bound {V B} (EV : encoding V) (forest : Graph.t V V)
    (weight : B -> nat) (prep_events : list (audit_prepare_source_event V V
      (audit_dom_source_body V B))) width :
  audit_graph_prepare_input_width EV forest <= width ->
  audit_prepare_source_work (audit_dom_source_body_work weight) prep_events <=
    audit_prepare_source_budget EV forest +
      audit_prepare_source_body_work (audit_dom_source_body_work weight) prep_events ->
  audit_prepare_source_body_work (audit_dom_source_body_work weight) prep_events <=
    length prep_events * (133 + 5 * audit_graph_prepare_input_width EV forest) +
      audit_prepare_source_body_work (audit_dom_source_body_external weight) prep_events ->
  64 * length prep_events +
    audit_prepare_source_work (audit_dom_source_body_work weight) prep_events <=
    audit_prepare_source_budget EV forest + length prep_events * (197 + 5 * width) +
      audit_prepare_source_body_work (audit_dom_source_body_external weight) prep_events.
Proof.
  intros Hwidth Hwork Hbody.
  assert (Hmul : length prep_events * (133 + 5 * audit_graph_prepare_input_width EV forest) <=
    length prep_events * (133 + 5 * width)) by (apply Nat.mul_le_mono_l; lia).
  clear - Hmul Hbody Hwork; nia.
Qed.

(** Same-run source stages compose within the explicit numerical reserve. *)
Lemma audit_dom_source_stages {V E B} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) parents enc (weight : B -> nat)
    first_events element_events child_events root_events prep_events dfs_events :
  (forall v, fst (enc v) = encode EV v) ->
  snd (audit_map_elements parents) = element_events ->
  snd (@audit_dom_source_children V E B enc (Map.elements parents)) = child_events ->
  snd (@audit_dom_source_roots V E B enc parents
    (preorder (dfs p FinSet.empty (Graph.entries g)))) = root_events ->
  let forest := dom_forest p parents in
  128 * length first_events + audit_dfs_source_work weight first_events <=
    audit_dfs_source_budget EV g p (Graph.entries g) + audit_dfs_source_body_work weight
      first_events ->
  length prep_events <= audit_graph_prepare_full_event_bound forest ->
  audit_prepare_source_work (audit_dom_source_body_work weight) prep_events <=
    audit_prepare_source_budget EV forest +
      audit_prepare_source_body_work (audit_dom_source_body_work weight) prep_events ->
  audit_prepare_source_body_work (audit_dom_source_body_work weight) prep_events <=
    length prep_events * (133 + 5 * audit_graph_prepare_input_width EV forest) +
      audit_prepare_source_body_work (audit_dom_source_body_external weight) prep_events ->
  128 * length dfs_events + audit_dfs_source_work (audit_dom_source_body_work weight) dfs_events <=
    audit_dfs_source_budget EV forest (prepare EV forest) (Graph.entries forest) +
      audit_dfs_source_body_work (audit_dom_source_body_work weight) dfs_events ->
  audit_dfs_source_body_work (audit_dom_source_body_work weight) dfs_events <=
    64 * length dfs_events + audit_dfs_source_body_work (audit_dom_source_body_external weight)
      dfs_events ->
  let size := S (audit_trie_nodes parents + length (Graph.nodes forest) +
    length (Graph.entries forest) + Pos.to_nat (fuel p) + Pos.to_nat (fuel (prepare EV forest))) in
  let width := audit_dfs_full_input_width EV g p (Graph.entries g) +
    audit_graph_prepare_input_width EV forest +
    audit_dfs_full_input_width EV forest (prepare EV forest) (Graph.entries forest) +
    fold_right Nat.max 0 (map (fun row => Nat.max (Pos.size_nat (encode EV (fst row)))
      (Pos.size_nat (encode EV (snd row)))) (Map.elements parents)) in
  let events := map DomSourceInitialDfs first_events ++ map DomSourceElements element_events ++
    child_events ++ root_events ++ map DomSourcePrepare prep_events ++ map DomSourceDfs
      dfs_events in
  audit_dom_source_work weight events <= audit_dfs_source_budget EV g p (Graph.entries g) +
    audit_prepare_source_budget EV forest +
    audit_dfs_source_budget EV forest (prepare EV forest) (Graph.entries forest) +
    (1024 * 1024)%nat * Nat.pow size 8 * S width * S width +
    audit_dom_source_external_work weight events.
Proof.
  intros Henc Helement Hchild Hroot forest Hfirst_work Hprep_count Hprep_work Hprep_body
    Hforest_work Hforest_body size width events.
  pose proof (audit_dom_source_elements_bound parents element_events Helement) as Helem_bound.
  assert (Hdfs_width : audit_dfs_full_input_width EV g p (Graph.entries g) <= width)
    by (unfold width; lia).
  assert (Hrows_width : fold_right Nat.max 0 (map (fun row =>
    Nat.max (Pos.size_nat (encode EV (fst row))) (Pos.size_nat (encode EV (snd row))))
    (Map.elements parents)) <= width) by (unfold width; lia).
  destruct (audit_dom_index_trace_bounds EV g p parents enc weight width child_events root_events
    Henc Hdfs_width Hrows_width Hchild Hroot) as [Hchild_bound Hroot_work].
  assert (Hsize : 1 <= size) by (unfold size; lia).
  assert (Hnodes : audit_trie_nodes parents <= size) by (unfold size; lia).
  assert (Hlive : length (preorder (dfs p FinSet.empty (Graph.entries g))) <= size).
  { unfold size, forest, dom_forest; cbn [Graph.nodes]; lia. }
  assert (Hfuel : Pos.to_nat (fuel (prepare EV forest)) =
    2 * length (Graph.nodes forest) + edge_count forest + 2).
  { cbn [prepare fuel]; rewrite SuccNat2Pos.id_succ; lia. }
  assert (Hprep_size : length prep_events <= 8 + 20 * size).
  { unfold audit_graph_prepare_full_event_bound in Hprep_count; unfold size; lia. }
  assert (Hprep_width : audit_graph_prepare_input_width EV forest <= width) by (unfold width; lia).
  pose proof (audit_dom_source_reserve_arithmetic size width (audit_trie_nodes parents)
    (length (preorder (dfs p FinSet.empty (Graph.entries g)))) (length prep_events)
    Hsize Hnodes Hlive Hprep_size) as Hreserve.
  unfold events; repeat rewrite audit_dom_source_work_app; repeat rewrite
    audit_dom_source_external_app.
  rewrite (proj1 (audit_dom_initial_events_work weight first_events)),
    (proj2 (audit_dom_initial_events_work weight first_events)),
    (proj1 (audit_dom_element_events_work (E := E) weight element_events)),
    (proj2 (audit_dom_element_events_work (E := E) weight element_events)),
    (proj1 (audit_dom_prepare_events_work (E := E) weight prep_events)),
    (proj2 (audit_dom_prepare_events_work (E := E) weight prep_events)),
    (proj1 (audit_dom_dfs_events_work (E := E) weight dfs_events)),
    (proj2 (audit_dom_dfs_events_work (E := E) weight dfs_events)).
  pose proof (audit_dom_source_prepare_bound EV forest weight prep_events width
    Hprep_width Hprep_work Hprep_body) as Hprep_bound.
  lia.
Qed.

(** The captured forest preparation and DFS supply the stage-composition bounds. *)
Lemma audit_dom_source_forest_tail {V E B} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) parents (cb : audit_dfs_callback_model V E B) (weight : B -> nat)
    first_events element_events child_events root_events :
  audit_dfs_callbacks_erase EV g cb ->
  128 * length first_events + audit_dfs_source_work weight first_events <=
    audit_dfs_source_budget EV g p (Graph.entries g) + audit_dfs_source_body_work weight
      first_events ->
  snd (audit_map_elements parents) = element_events ->
  snd (@audit_dom_source_children V E B (audit_dfs_encode_model cb) (Map.elements parents)) =
    child_events ->
  snd (@audit_dom_source_roots V E B (audit_dfs_encode_model cb) parents
    (preorder (dfs p FinSet.empty (Graph.entries g)))) = root_events ->
  let forest := dom_forest p parents in
  let enc := audit_dfs_encode_model cb in
  let prepare_cb := AuditPrepareCallbackModel V V (audit_dom_source_body V B)
    (audit_dom_source_out enc (dom_children EV (Map.elements parents))) audit_dom_source_target
    (audit_dom_source_encode enc) in
  let dfs_cb := AuditDfsCallbackModel V V (audit_dom_source_body V B) audit_dom_source_target
    (audit_dom_source_encode enc) in
  let receipt :=
    (let '(fp, prep_events) := audit_prepare_source_counted EV forest prepare_cb in
      let '(result, dfs_events) := audit_dfs_source_counted fp dfs_cb FinSet.empty
        (Graph.entries forest) in
      AuditDomSourceReceipt forest fp result
        (map DomSourceInitialDfs first_events ++ map DomSourceElements element_events ++
        child_events ++ root_events ++ map DomSourcePrepare prep_events ++
        map DomSourceDfs dfs_events)) in
  audit_dom_source_work weight (audit_dom_source_events receipt) <=
    audit_dom_search_source_budget EV g p parents receipt +
    audit_dom_source_external_work weight (audit_dom_source_events receipt).
Proof.
  intros [_ Hencode] Hfirst_work Helement Hchild Hroot.
  set (forest := dom_forest p parents).
  set (enc := audit_dfs_encode_model cb).
  set (prepare_cb := AuditPrepareCallbackModel V V (audit_dom_source_body V B)
    (audit_dom_source_out enc (dom_children EV (Map.elements parents))) audit_dom_source_target
    (audit_dom_source_encode enc)).
  set (dfs_cb := AuditDfsCallbackModel V V (audit_dom_source_body V B) audit_dom_source_target
    (audit_dom_source_encode enc)).
  assert (Hprepare : audit_prepare_callbacks_erase EV forest prepare_cb).
  { unfold forest, prepare_cb, enc; apply audit_dom_source_prepare_callbacks; exact Hencode. }
  assert (Hdfs : audit_dfs_callbacks_erase EV forest dfs_cb).
  { unfold forest, dfs_cb, enc; apply audit_dom_source_dfs_callbacks; exact Hencode. }
  pose proof (audit_prepare_source_with_receipts V V (audit_dom_source_body V B) EV forest
    prepare_cb (audit_dom_source_body_work weight) Hprepare) as Hprepare_run.
  pose proof (audit_prepare_source_out_in_nodes V V (audit_dom_source_body V B) EV forest
    prepare_cb) as Hprepare_nodes.
  cbn zeta; fold forest enc prepare_cb dfs_cb.
  destruct (audit_prepare_source_counted EV forest prepare_cb) as [fp prep_events].
  cbn [fst snd] in Hprepare_run, Hprepare_nodes.
  destruct Hprepare_run as [Hprepared [Hprep_count [Hprep_work Hprep_receipts]]]; subst fp.
  pose proof (audit_dom_prepare_body_work EV forest enc weight
    (dom_children EV (Map.elements parents)) prep_events Hencode Hprep_receipts Hprepare_nodes)
    as Hprep_body.
  pose proof (audit_dom_dfs_source_slack (prepare EV forest) dfs_cb (audit_dom_source_body_work
    weight) FinSet.empty (Graph.entries forest) Hdfs) as Hforest_work.
  pose proof (audit_dfs_source_events_wellformed (prepare EV forest) dfs_cb FinSet.empty
    (Graph.entries forest)) as Hshape.
  pose proof (audit_dfs_source_receipts (prepare EV forest) dfs_cb FinSet.empty
    (Graph.entries forest)) as Hreceipts.
  destruct (audit_dfs_source_counted (prepare EV forest) dfs_cb FinSet.empty (Graph.entries forest))
    as [result dfs_events].
  cbn [fst snd] in Hforest_work, Hshape, Hreceipts.
  pose proof (audit_dom_dfs_body_work enc weight dfs_events Hshape Hreceipts) as Hforest_body.
  cbn [audit_dom_source_events audit_dom_source_forest audit_dom_source_index
    audit_dom_search_source_budget].
  unfold audit_dom_search_source_budget; cbn [audit_dom_source_forest audit_dom_source_index].
  eapply (audit_dom_source_stages EV g p parents enc weight first_events element_events
    child_events root_events prep_events dfs_events); eassumption.
Qed.

(** Source dominator search pays for all retained callbacks and source operations. *)
Theorem audit_dom_search_source_correct : audit_dom_search_source_statement.
Proof.
  intros V E B EV g p parents cb weight Hcallbacks.
  split; [apply audit_dom_search_source_erases; exact Hcallbacks|].
  pose proof (audit_dfs_source_result_and_count p cb FinSet.empty (Graph.entries g) Hcallbacks)
    as [Hsearch _].
  pose proof (audit_dom_dfs_source_slack p cb weight FinSet.empty (Graph.entries g) Hcallbacks)
    as Hfirst_work.
  pose proof (audit_map_elements_erases V V parents) as Hrows.
  destruct Hcallbacks as [Htarget Hencode].
  pose proof (audit_dom_source_children_erases (E := E) EV (audit_dfs_encode_model cb)
    (Map.elements parents) Hencode) as Hchildren.
  pose proof (audit_dom_source_roots_erases (E := E) EV (audit_dfs_encode_model cb) parents
    (preorder (dfs p FinSet.empty (Graph.entries g))) Hencode) as Hroots.
  unfold audit_dom_search_source_counted.
  destruct (audit_dfs_source_counted p cb FinSet.empty (Graph.entries g))
    as [search first_events] eqn:Hfirst_run.
  cbn [fst snd] in Hsearch, Hfirst_work; subst search.
  destruct (audit_map_elements parents) as [rows element_events] eqn:Helements_run.
  cbn [fst] in Hrows; subst rows.
  destruct (audit_dom_source_children (audit_dfs_encode_model cb) (Map.elements parents))
    as [children child_events] eqn:Hchildren_run.
  cbn [fst] in Hchildren; subst children.
  destruct (audit_dom_source_roots (audit_dfs_encode_model cb) parents
    (preorder (dfs p FinSet.empty (Graph.entries g)))) as [roots root_events] eqn:Hroots_run.
  cbn [fst] in Hroots; subst roots.
  assert (Helement : snd (audit_map_elements parents) = element_events)
    by (rewrite Helements_run; reflexivity).
  assert (Hchild : snd (audit_dom_source_children (E := E) (audit_dfs_encode_model cb)
    (Map.elements parents)) = child_events) by (rewrite Hchildren_run; reflexivity).
  assert (Hroot : snd (audit_dom_source_roots (E := E) (audit_dfs_encode_model cb) parents
    (preorder (dfs p FinSet.empty (Graph.entries g)))) = root_events)
    by (rewrite Hroots_run; reflexivity).
  eapply (audit_dom_source_forest_tail EV g p parents cb weight first_events element_events
    child_events root_events); try eassumption. split; assumption.
Qed.

(** One virtual source receipt and its own LT run produce the default dominator tree. *)
Lemma audit_default_dom_run_erases {V E B} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (cb : audit_virtual_base_callbacks V E B) (source : E -> V * list B) :
  audit_virtual_base_callbacks_erase EV g cb ->
  (forall edge, fst (source edge) = Graph.source g edge) ->
  exists vp search prepare_events dfs_events semi_state semi_events virtual_parents lt_events
    parents erase_events receipt result,
    audit_virtual_source_search EV g cb = (vp, (search, (prepare_events, dfs_events))) /\
    audit_semi_producer_nested_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
      vp search semi_state semi_events /\
    audit_lt_nested_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
      search (SemiState.result semi_state) virtual_parents lt_events /\
    audit_erase_virtual_nested (audit_virtual_base_encode cb) virtual_parents =
      (parents, erase_events) /\
    receipt = audit_dom_search_source_counted p parents
      (AuditDfsCallbackModel V E B (audit_virtual_base_target cb) (audit_virtual_base_encode cb)) /\
    result = DomTree parents (pre_num (audit_dom_source_result receipt))
      (post_num (audit_dom_source_result receipt)) /\
    result = dominator_tree p.
Proof.
  intros Hcallbacks Hsource.
  pose proof (audit_virtual_source_search_holds V E B EV g p cb (fun _ => 0) Hcallbacks) as Hsearch.
  pose proof (audit_virtual_full_source_correct V E B EV g source Hsource) as Hsource_full.
  destruct Hcallbacks as [Hout [Htarget Hbase]].
  assert (Hencode : forall v,
    fst (audit_virtual_full_encode cb v) = encode (virtual_encoding EV) v).
  { intros [v|[]]; cbn [audit_virtual_full_encode virtual_encoding].
    - specialize (Hbase v); destruct (audit_virtual_base_encode cb v); cbn in *; now rewrite Hbase.
    - reflexivity. }
  destruct (audit_virtual_source_search EV g cb) as [vp [search [prepare_events dfs_events]]]
    eqn:Hsearch_run.
  cbn [fst snd] in Hsearch; destruct Hsearch as [Hvp [Hresult _]].
  subst vp search.
  destruct (audit_semi_producer_nested_erasure _ _ _ (virtual_encoding EV) (virtual_graph EV g)
    (virtual_prepared p) (virtual_dfs p) (audit_virtual_full_encode cb)
    (audit_virtual_full_source source) Hencode Hsource_full) as [state [semi_events [Hsemi
      Hstate]]].
  subst state.
  destruct (audit_lt_nested_erasure _ _ _ (virtual_encoding EV) (virtual_graph EV g) (virtual_dfs p)
    (SemiState.result (semi_compute (virtual_prepared p) (virtual_dfs p)))
    (audit_virtual_full_encode cb) (audit_virtual_full_source source) Hencode Hsource_full)
    as [virtual_parents [lt_events [Hlt Hparents]]].
  subst virtual_parents.
  pose proof (audit_erase_nested_correct V B EV (audit_virtual_base_encode cb) (fun _ => 0)
    (lt_compute (virtual_encoding EV) (virtual_graph EV g) (virtual_dfs p)
      (SemiState.result (semi_compute (virtual_prepared p) (virtual_dfs p)))) Hbase) as Herase.
  destruct (audit_erase_virtual_nested (audit_virtual_base_encode cb)
    (lt_compute (virtual_encoding EV) (virtual_graph EV g) (virtual_dfs p)
      (SemiState.result (semi_compute (virtual_prepared p) (virtual_dfs p)))))
    as [parents erase_events] eqn:Herase_run.
  cbn [fst snd] in Herase; destruct Herase as [Hparents _].
  assert (Hdom_callbacks : audit_dfs_callbacks_erase EV g
    (AuditDfsCallbackModel V E B (audit_virtual_base_target cb) (audit_virtual_base_encode cb)))
    by (split; assumption).
  pose proof (audit_dom_search_source_erases EV g p parents _ Hdom_callbacks) as Hforest.
  exists (virtual_prepared p), (virtual_dfs p), prepare_events, dfs_events,
    (semi_compute (virtual_prepared p) (virtual_dfs p)), semi_events,
    (lt_compute (virtual_encoding EV) (virtual_graph EV g) (virtual_dfs p)
      (SemiState.result (semi_compute (virtual_prepared p) (virtual_dfs p)))), lt_events,
    parents, erase_events, (audit_dom_search_source_counted p parents
      (AuditDfsCallbackModel V E B (audit_virtual_base_target cb) (audit_virtual_base_encode cb))),
    (DomTree parents (pre_num (dom_search p parents)) (post_num (dom_search p parents))).
  repeat split; try assumption; try reflexivity.
  - now rewrite Hforest.
  - unfold dominator_tree, dominator_tree_with.
    change (DomTree parents (pre_num (dom_search p parents)) (post_num (dom_search p parents)) =
      dom_tree_of p (erase_virtual_parents EV
        (lt_compute (virtual_encoding EV) (virtual_graph EV g) (virtual_dfs p)
          (SemiState.result (semi_compute (virtual_prepared p) (virtual_dfs p)))))).
    rewrite <- Hparents; reflexivity.
Qed.

(** The prepared outgoing fold stores only rows belonging to its node list. *)
Lemma audit_dom_prepare_out_lookup {V E} (EV : encoding V) (g : Graph.t V E) nodes key row :
  Map.get EV key (fold_right (fun v m => Map.set EV v (Graph.out g v) m) Map.empty nodes) =
    Some row ->
  In key nodes /\ row = Graph.out g key.
Proof.
  induction nodes as [|v rest IH]; cbn [fold_right].
  - rewrite Map.get_empty; discriminate.
  - destruct (dfs_eq_dec EV key v) as [Heq|Hne].
    + subst v; rewrite Map.get_set_same; intro Hrow; inversion Hrow; split; [now left|reflexivity].
    + rewrite Map.get_set_other by exact Hne; intro Hget.
      destruct (IH Hget) as [Hin Hrow]; split; [now right|exact Hrow].
Qed.

(** Every stored prepared outgoing row comes from an actual graph node. *)
Lemma audit_dom_prepare_out_row {V E} (EV : encoding V) (g : Graph.t V E) key row :
  In (key, row) (Map.elements (out_index (prepare EV g))) ->
  In key (Graph.nodes g) /\ row = Graph.out g key.
Proof.
  intro Hin; cbn [prepare out_index] in Hin |- *.
  assert (Hwf : Map.wf EV
    (fold_right (fun v m => Map.set EV v (Graph.out g v) m) Map.empty (Graph.nodes g))).
  { clear Hin; induction (Graph.nodes g) as [|v rest IH]; cbn [fold_right].
    - apply Map.wf_empty.
    - apply Map.wf_set; exact IH. }
  apply (audit_dom_prepare_out_lookup EV g (Graph.nodes g) key row).
  apply Map.elements_sound; assumption.
Qed.

(** For prepared graphs, DFS operand widths come from graph nodes, edges and roots. *)
Lemma audit_dom_prepared_dfs_width {V E} (EV : encoding V) (g : Graph.t V E) roots :
  incl roots (Graph.nodes g) ->
  audit_dfs_full_input_width EV g (prepare EV g) roots <= audit_graph_prepare_input_width EV g.
Proof.
  intro Hroots; unfold audit_dfs_full_input_width.
  apply audit_dom_max_fold_bound; [lia|].
  intros code Hin; apply in_map_iff in Hin; destruct Hin as [v [Heq Hin]]; subst code.
  apply in_app_iff in Hin; destruct Hin as [Hroot|Hin].
  - apply audit_input_width_node; now apply Hroots.
  - apply in_app_iff in Hin; destruct Hin as [Hnode|Hin].
    + now apply audit_input_width_node.
    + apply in_app_iff in Hin; destruct Hin as [Hkey|Htarget].
      * apply in_map_iff in Hkey; destruct Hkey as [[key row] [Heq Hrow]]; cbn in Heq; subst key.
        destruct (audit_dom_prepare_out_row EV g v row Hrow) as [Hnode _].
        now apply audit_input_width_node.
      * apply in_flat_map in Htarget; destruct Htarget as [[key row] [Hrow Htarget]].
        apply in_map_iff in Htarget; destruct Htarget as [edge [Heq Hedge]]; subst v.
        destruct (audit_dom_prepare_out_row EV g key row Hrow) as [Hnode Hrow_eq].
        subst row; eapply audit_input_width_edge; eassumption.
Qed.

(** Forest DFS widths are bounded by the original graph and parent-map widths. *)
Lemma audit_dom_forest_dfs_width {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) parents :
  audit_dfs_full_input_width EV (dom_forest p parents) (prepare EV (dom_forest p parents))
    (Graph.entries (dom_forest p parents)) <= audit_dom_input_width EV g p parents.
Proof.
  eapply Nat.le_trans; [apply audit_dom_prepared_dfs_width|apply audit_dom_forest_prepare_width].
  intros v Hin; unfold dom_forest in *; cbn [Graph.entries Graph.nodes] in *.
  apply filter_In in Hin; exact (proj1 Hin).
Qed.

(** An individual nested preparation event stays within its body-work bound. *)
Definition audit_dom_prepare_body_bounded {V E} (EV : encoding V) bound
    (event : audit_prepare_nested_event V E (audit_dom_body V)) : Prop :=
  fold_right (fun item n => audit_dom_body_work EV item + n) 0 (snd event) <= bound.

(** Incoming-edge preparation bounds target and encoder bodies for the actual edges. *)
Lemma audit_dom_prepare_edges_body {V} (EV : encoding V) (g : Graph.t V V) children
    edges width :
  (forall edge, Graph.target g edge = edge) ->
  (forall edge, In edge edges -> audit_key_bits_weight (encode EV (Graph.target g edge)) <=
    width) ->
  forall initial, Forall (audit_dom_prepare_body_bounded EV (66 + 2 * width))
    (snd (audit_prepare_nested_edges g (audit_dom_prepare_callbacks EV children) edges initial)).
Proof.
  intros Htarget Hwidth; induction edges as [|edge rest IH]; intro initial.
  - repeat constructor; unfold audit_dom_prepare_body_bounded; cbn; lia.
  - cbn [audit_prepare_nested_edges].
    specialize (IH (fun e Hin => Hwidth e (or_intror Hin)) initial).
    destruct (audit_prepare_nested_edges g (audit_dom_prepare_callbacks EV children) rest initial)
      as [middle events].
    cbn [audit_dom_prepare_callbacks audit_prepare_target_model audit_prepare_encode_model
      audit_dom_target_counted audit_dom_encode_counted] in *.
    destruct (Map.code_get (encode EV edge) middle) as [row|] eqn:Hget;
      cbn [snd] in IH |- *; constructor;
      try (unfold audit_dom_prepare_body_bounded; cbn; lia).
    all: apply Forall_app; split; [exact IH|].
    all: specialize (Hwidth edge (or_introl eq_refl)); rewrite Htarget in Hwidth.
    all: repeat (constructor; [unfold audit_dom_prepare_body_bounded, audit_dom_body_work,
      audit_encoding_weight; cbn; lia|]); constructor.
Qed.

(** Outgoing-index preparation prices reads and encodes at their actual node. *)
Lemma audit_dom_prepare_out_body {V} (EV : encoding V) (g : Graph.t V V) children nodes width :
  (forall v, In v nodes -> audit_key_bits_weight (encode EV v) <= width) ->
  forall initial, Forall (audit_dom_prepare_body_bounded EV (66 + 2 * width))
    (snd (audit_prepare_nested_out g (audit_dom_prepare_callbacks EV children) nodes initial)).
Proof.
  intro Hwidth; induction nodes as [|v rest IH]; intro initial.
  - repeat constructor; unfold audit_dom_prepare_body_bounded; cbn; lia.
  - cbn [audit_prepare_nested_out].
    specialize (IH (fun x Hin => Hwidth x (or_intror Hin)) initial).
    destruct (audit_prepare_nested_out g (audit_dom_prepare_callbacks EV children) rest initial)
      as [middle events].
    cbn [audit_dom_prepare_callbacks audit_prepare_out_model audit_prepare_encode_model
      audit_dom_out_counted audit_dom_encode_counted] in *.
    destruct (Map.get EV v children) as [row|] eqn:Hget; cbn [snd] in IH |- *.
    all: constructor; [unfold audit_dom_prepare_body_bounded; cbn; lia|].
    all: apply Forall_app; split; [exact IH|].
    all: specialize (Hwidth v (or_introl eq_refl)).
    all: repeat (constructor; [unfold audit_dom_prepare_body_bounded, audit_dom_body_work,
      audit_encoding_weight, audit_get_weight; cbn; lia|]); constructor.
Qed.

(** Incoming-index preparation prices its out and edge callback bodies. *)
Lemma audit_dom_prepare_in_body {V} (EV : encoding V) (g : Graph.t V V) children nodes width :
  (forall v, Graph.out g v = index_edges EV children v) ->
  (forall edge, Graph.target g edge = edge) ->
  (forall v, In v nodes -> audit_key_bits_weight (encode EV v) <= width) ->
  (forall v edge, In v nodes -> In edge (Graph.out g v) ->
    audit_key_bits_weight (encode EV edge) <= width) ->
  forall initial, Forall (audit_dom_prepare_body_bounded EV (66 + 2 * width))
    (snd (audit_prepare_nested_in g (audit_dom_prepare_callbacks EV children) nodes initial)).
Proof.
  intros Hout Htarget Hwidth Hedge; induction nodes as [|v rest IH]; intro initial.
  - repeat constructor; unfold audit_dom_prepare_body_bounded; cbn; lia.
  - cbn [audit_prepare_nested_in].
    specialize (IH (fun x Hin => Hwidth x (or_intror Hin))
      (fun x edge Hin => Hedge x edge (or_intror Hin)) initial).
    destruct (audit_prepare_nested_in g (audit_dom_prepare_callbacks EV children) rest initial)
      as [middle events].
    pose proof (audit_dom_prepare_edges_body EV g children (Graph.out g v) width Htarget) as Hedges.
    assert (Hedge_width : forall edge, In edge (Graph.out g v) ->
      audit_key_bits_weight (encode EV (Graph.target g edge)) <= width).
    { intros edge Hin; rewrite Htarget; exact (Hedge v edge (or_introl eq_refl) Hin). }
    specialize (Hedges Hedge_width middle).
    destruct (audit_prepare_nested_edges g (audit_dom_prepare_callbacks EV children)
      (Graph.out g v) middle) as [result edge_events] eqn:Hrun.
    specialize (Hwidth v (or_introl eq_refl)).
    cbn [snd] in IH, Hedges.
    cbn [audit_dom_prepare_callbacks audit_prepare_out_model audit_dom_out_counted].
    unfold index_edges in Hout; rewrite <- Hout; rewrite Hrun; cbn [snd].
    constructor; [unfold audit_dom_prepare_body_bounded; cbn; lia|].
    repeat rewrite Forall_app; repeat split; try assumption.
    constructor; [|constructor].
    unfold audit_dom_prepare_body_bounded, audit_dom_body_work, audit_encoding_weight,
      audit_get_weight; cbn; lia.
Qed.

(** Edge counting prices the same outgoing callback at each listed node. *)
Lemma audit_dom_prepare_count_body {V} (EV : encoding V) (g : Graph.t V V) children nodes width :
  (forall v, In v nodes -> audit_key_bits_weight (encode EV v) <= width) ->
  Forall (audit_dom_prepare_body_bounded EV (66 + 2 * width))
    (snd (audit_prepare_nested_edge_count g (audit_dom_prepare_callbacks EV children) nodes)).
Proof.
  intro Hwidth; induction nodes as [|v rest IH].
  - repeat constructor; unfold audit_dom_prepare_body_bounded; cbn; lia.
  - cbn [audit_prepare_nested_edge_count].
    specialize (IH (fun x Hin => Hwidth x (or_intror Hin))).
    destruct (audit_prepare_nested_edge_count g (audit_dom_prepare_callbacks EV children) rest)
      as [count events].
    cbn [audit_dom_prepare_callbacks audit_prepare_out_model audit_dom_out_counted] in *.
    destruct (Map.get EV v children); cbn [snd] in IH |- *.
    all: constructor; [unfold audit_dom_prepare_body_bounded; cbn; lia|].
    all: apply Forall_app; split; [exact IH|].
    all: specialize (Hwidth v (or_introl eq_refl)).
    all: repeat (constructor; [unfold audit_dom_prepare_body_bounded, audit_dom_body_work,
      audit_encoding_weight, audit_get_weight; cbn; lia|]); constructor.
Qed.

(** Every nested forest-preparation body is priced by its graph input width. *)
Lemma audit_dom_prepare_bodies {V} (EV : encoding V) (g : Graph.t V V) children :
  (forall v, Graph.out g v = index_edges EV children v) ->
  (forall edge, Graph.target g edge = edge) ->
  Forall (audit_dom_prepare_body_bounded EV (66 + 2 * audit_graph_prepare_input_width EV g))
    (snd (audit_graph_prepare_nested_counted EV g (audit_dom_prepare_callbacks EV children))).
Proof.
  intros Hout Htarget; set (width := audit_graph_prepare_input_width EV g).
  assert (Hnodes : forall v, In v (Graph.nodes g) ->
    audit_key_bits_weight (encode EV v) <= width).
  { intros v Hin; apply audit_input_width_node; exact Hin. }
  assert (Hedges : forall v edge, In v (Graph.nodes g) -> In edge (Graph.out g v) ->
    audit_key_bits_weight (encode EV edge) <= width).
  { intros v edge Hin Hedge; rewrite <- (Htarget edge).
    eapply audit_input_width_edge; eassumption. }
  pose proof (audit_dom_prepare_out_body EV g children (Graph.nodes g) width Hnodes Map.empty)
    as Hout_events.
  pose proof (audit_dom_prepare_in_body EV g children (Graph.nodes g) width Hout Htarget Hnodes
    Hedges Map.empty) as Hin_events.
  pose proof (audit_dom_prepare_count_body EV g children (Graph.nodes g) width Hnodes) as Hcount.
  unfold audit_graph_prepare_nested_counted.
  destruct (audit_prepare_nested_out g (audit_dom_prepare_callbacks EV children)
    (Graph.nodes g) Map.empty) as [out out_events].
  destruct (audit_prepare_nested_in g (audit_dom_prepare_callbacks EV children)
    (Graph.nodes g) Map.empty) as [incoming in_events].
  destruct (audit_prepare_nested_edge_count g (audit_dom_prepare_callbacks EV children)
    (Graph.nodes g)) as [edges edge_events].
  cbn [snd] in Hout_events, Hin_events, Hcount |- *; fold width.
  repeat rewrite Forall_app; repeat split; try assumption;
    repeat constructor; unfold audit_dom_prepare_body_bounded; cbn; lia.
Qed.

(** The complete forest-preparation body sum is bounded by the event count. *)
Lemma audit_dom_prepare_body_sum {V} (EV : encoding V) (g : Graph.t V V)
    (events : list (audit_prepare_nested_event V V (audit_dom_body V))) :
  Forall (audit_dom_prepare_body_bounded EV (66 + 2 * audit_graph_prepare_input_width EV g))
    events ->
  audit_prepare_nested_body_work (audit_dom_body_work EV) events <=
    length events * (66 + 2 * audit_graph_prepare_input_width EV g).
Proof.
  intro Hbounded; induction Hbounded as [|[event body] rest Hbody Htail IH].
  - reflexivity.
  - unfold audit_dom_prepare_body_bounded in Hbody; cbn [snd] in Hbody.
    change (fold_right (fun item n => audit_dom_body_work EV item + n) 0 body +
      audit_prepare_nested_body_work (audit_dom_body_work EV) rest <=
      length ((event, body) :: rest) * (66 + 2 * audit_graph_prepare_input_width EV g)).
    cbn [length]; rewrite Nat.mul_succ_l, Nat.add_comm; apply Nat.add_le_mono; assumption.
Qed.

(** A nested forest DFS event prices its actual target or encoded vertex. *)
Lemma audit_dom_dfs_model_event {V} (EV : encoding V) item width :
  audit_virtual_dfs_model_receipt V V (audit_dom_body V) (audit_dom_dfs_callbacks EV) item ->
  audit_dfs_full_event_width EV (fst item) <= width ->
  fold_right (fun body n => audit_dom_body_work EV body + n) 0 (snd item) <= 65 + width.
Proof.
  intros Hreceipt Hwidth; destruct item as [event body].
  destruct event as [site|edge target|v input found|v input found|v via before after|
      v before after|detail|pre post];
    cbn [audit_virtual_dfs_model_receipt audit_dom_dfs_callbacks audit_dfs_target_model
      audit_dfs_encode_model audit_dom_target_counted audit_dom_encode_counted
      audit_dfs_full_event_width fst snd] in Hreceipt, Hwidth |- *;
    try (subst body; cbn [fold_right]; lia).
  - inversion Hreceipt; subst body; unfold audit_dom_body_work; cbn; lia.
  - subst body; unfold audit_dom_body_work, audit_encoding_weight; cbn; lia.
  - subst body; unfold audit_dom_body_work, audit_encoding_weight; cbn; lia.
  - destruct detail; cbn [audit_virtual_dfs_model_receipt audit_dom_dfs_callbacks
      audit_dfs_encode_model audit_dom_encode_counted audit_dfs_full_event_width] in Hreceipt,
        Hwidth;
      try (subst body; cbn [fold_right]; lia);
      subst body; unfold audit_dom_body_work, audit_encoding_weight; cbn; lia.
Qed.

(** The forest DFS body sum is bounded by the full-event operand width. *)
Lemma audit_dom_dfs_model_sum {V} (EV : encoding V) (g : Graph.t V V)
    (p : prepared EV g) roots :
  audit_dfs_callbacks_erase EV g (audit_dom_dfs_callbacks EV) ->
  let events := snd (audit_dfs_nested_counted p (audit_dom_dfs_callbacks EV) FinSet.empty roots) in
  audit_dfs_nested_body_work (audit_dom_body_work EV) events <=
    length events * (65 + audit_dfs_full_input_width EV g p roots).
Proof.
  intro Hcallbacks.
  pose proof (audit_virtual_dfs_nested_receipts _ _ _ p (audit_dom_dfs_callbacks EV)
    FinSet.empty roots) as Hreceipts.
  pose proof (audit_dfs_nested_correct _ _ _ EV g p (audit_dom_dfs_callbacks EV)
    FinSet.empty roots Hcallbacks) as Hnested.
  pose proof (audit_dfs_full_counted_event_width p FinSet.empty roots) as Hwidth.
  destruct (audit_dfs_nested_counted p (audit_dom_dfs_callbacks EV) FinSet.empty roots)
    as [result events].
  cbn [fst snd] in Hreceipts, Hnested |- *; destruct Hnested as [_ [Htrace _]].
  rewrite <- Htrace in Hwidth; apply Forall_map in Hwidth.
  clear Htrace.
  induction Hreceipts as [|[event body] rest Hreceipt Htail IH].
  - reflexivity.
  - inversion Hwidth as [|? ? Hwidth_one Hwidth_tail]; subst.
    specialize (IH Hwidth_tail).
    pose proof (audit_dom_dfs_model_event EV (event, body)
      (audit_dfs_full_input_width EV g p roots) Hreceipt Hwidth_one) as Hbound.
    change (fold_right (fun item n => audit_dom_body_work EV item + n) 0 body +
      audit_dfs_nested_body_work (audit_dom_body_work EV) rest <=
      length ((event, body) :: rest) * (65 + audit_dfs_full_input_width EV g p roots)).
    cbn [length]; rewrite Nat.mul_succ_l, Nat.add_comm; apply Nat.add_le_mono; assumption.
Qed.

(** Sum the selected event prices in a counted dominator trace. *)
Definition audit_dom_event_sum {V E} (EV : encoding V) (events : list (audit_dom_call V E)) : nat :=
  fold_right (fun event n => audit_dom_event_work EV event + n) 0 events.

(** Event prices add over concatenated traces. *)
Lemma audit_dom_event_sum_app {V E} (EV : encoding V) (left right : list (audit_dom_call V E)) :
  audit_dom_event_sum EV (left ++ right) = audit_dom_event_sum EV left + audit_dom_event_sum EV
    right.
Proof.
  unfold audit_dom_event_sum; induction left as [|event rest IH]; cbn [List.app
    List.fold_right]; lia.
Qed.

(** Tail-first child construction prices each actual parent key. *)
Lemma audit_dom_children_work {V E} (EV : encoding V) rows width :
  (forall v u, In (v, u) rows -> audit_key_bits_weight (encode EV u) <= width) ->
  audit_dom_event_sum EV (snd (@audit_dom_children_counted V E EV rows)) <=
    (1 + 3 * length rows) * (66 + 3 * width).
Proof.
  induction rows as [|[v u] rest IH]; intro Hwidth.
  - cbn [audit_dom_children_counted snd]; unfold audit_dom_event_sum, audit_dom_event_work;
      cbn [fold_right]; lia.
  - specialize (IH (fun x y Hin => Hwidth x y (or_intror Hin))).
    destruct (audit_dom_children_counted EV rest) as [children events] eqn:Hrun.
    cbn [snd] in IH.
    specialize (Hwidth v u (or_introl eq_refl)).
    cbn [audit_dom_children_counted]; rewrite Hrun; cbn [snd];
    destruct (Map.get EV u children) as [row|].
    + change (64 + audit_dom_event_sum EV
        (events ++ [AuditDomChildRead u children (Some row);
          AuditDomChildSet u (v :: row) children]) <=
        (1 + 3 * S (length rest)) * (66 + 3 * width)).
      rewrite audit_dom_event_sum_app; unfold audit_dom_event_sum at 2; cbn [fold_right].
      unfold audit_dom_event_work, audit_encoding_weight, audit_get_weight, audit_set_weight;
        cbn; nia.
    + change (64 + audit_dom_event_sum EV
        (events ++ [AuditDomChildRead u children None; AuditDomChildSet u [v] children]) <=
        (1 + 3 * S (length rest)) * (66 + 3 * width)).
      rewrite audit_dom_event_sum_app; unfold audit_dom_event_sum at 2; cbn [fold_right].
      unfold audit_dom_event_work, audit_encoding_weight, audit_get_weight, audit_set_weight;
        cbn; nia.
Qed.

(** Root selection prices each actual live-vertex lookup. *)
Lemma audit_dom_roots_work {V E} (EV : encoding V) parents live width :
  (forall v, In v live -> audit_key_bits_weight (encode EV v) <= width) ->
  audit_dom_event_sum EV (snd (@audit_dom_roots_counted V E EV parents live)) <=
    (1 + 2 * length live) * (66 + 3 * width).
Proof.
  induction live as [|v rest IH]; intro Hwidth.
  - cbn [audit_dom_roots_counted snd]; unfold audit_dom_event_sum, audit_dom_event_work;
      cbn [fold_right]; lia.
  - specialize (IH (fun x Hin => Hwidth x (or_intror Hin))).
    destruct (audit_dom_roots_counted EV parents rest) as [roots events] eqn:Hrun.
    cbn [snd] in IH; specialize (Hwidth v (or_introl eq_refl)).
    cbn [audit_dom_roots_counted]; rewrite Hrun; cbn [snd]; destruct (Map.get EV v parents);
      unfold audit_dom_event_sum at 1; cbn [fold_right]; fold (audit_dom_event_sum EV events);
      unfold audit_dom_event_work, audit_encoding_weight, audit_get_weight; cbn; nia.
Qed.

(** Wrapping initial DFS events preserves their prices and adds one fixed frame each. *)
Lemma audit_dom_initial_model_sum {V E} (EV : encoding V) events :
  audit_dom_event_sum EV (map (@AuditDomInitialDfs V E) events) =
    64 * length events + fold_right (fun event n => audit_dfs_full_model_event EV event + n) 0
      events.
Proof.
  induction events as [|event rest IH]; [reflexivity|].
  change (64 + audit_dfs_full_model_event EV event +
    audit_dom_event_sum EV (map AuditDomInitialDfs rest) = 64 * S (length rest) +
      (audit_dfs_full_model_event EV event +
        fold_right (fun item n => audit_dfs_full_model_event EV item + n) 0 rest)).
  rewrite IH; lia.
Qed.

(** Wrapping preparation retains both the outer event price and callback body. *)
Lemma audit_dom_prepare_model_sum {V E} (EV : encoding V)
    (events : list (audit_prepare_nested_event V V (audit_dom_body V))) :
  audit_dom_event_sum EV (map (@AuditDomPrepare V E) events) =
    64 * length events +
    fold_right (fun event n => audit_graph_full_event_work (fst event) + n) 0 events +
    audit_prepare_nested_body_work (audit_dom_body_work EV) events.
Proof.
  induction events as [|[event body] rest IH]; [reflexivity|].
  change (64 + (audit_graph_full_event_work event +
    fold_right (fun item n => audit_dom_body_work EV item + n) 0 body) +
    audit_dom_event_sum EV (map (@AuditDomPrepare V E) rest) =
    64 * S (length rest) +
      (audit_graph_full_event_work event +
        fold_right (fun item n => audit_graph_full_event_work (fst item) + n) 0 rest) +
      (fold_right (fun item n => audit_dom_body_work EV item + n) 0 body +
        audit_prepare_nested_body_work (audit_dom_body_work EV) rest)).
  rewrite IH; lia.
Qed.

(** Wrapping forest DFS retains both the outer event price and callback body. *)
Lemma audit_dom_dfs_model_events {V E} (EV : encoding V)
    (events : list (audit_dfs_nested_event V V (audit_dom_body V))) :
  audit_dom_event_sum EV (map (@AuditDomDfs V E) events) =
    64 * length events +
    fold_right (fun event n => audit_dfs_full_model_event EV (fst event) + n) 0 events +
    audit_dfs_nested_body_work (audit_dom_body_work EV) events.
Proof.
  induction events as [|[event body] rest IH]; [reflexivity|].
  change (64 + (audit_dfs_full_model_event EV event +
    fold_right (fun item n => audit_dom_body_work EV item + n) 0 body) +
    audit_dom_event_sum EV (map (@AuditDomDfs V E) rest) =
    64 * S (length rest) +
      (audit_dfs_full_model_event EV event +
        fold_right (fun item n => audit_dfs_full_model_event EV (fst item) + n) 0 rest) +
      (fold_right (fun item n => audit_dom_body_work EV item + n) 0 body +
        audit_dfs_nested_body_work (audit_dom_body_work EV) rest)).
  rewrite IH; lia.
Qed.

(** The input event envelope covers the forest's node, edge and DFS ceilings. *)
Lemma audit_dom_resource_arithmetic input nodes live rows roots edges forest_fuel :
  live <= input -> rows <= nodes -> roots <= live -> edges <= live * rows ->
  forest_fuel = 2 * live + edges + 2 ->
  let q := S (1 + input + nodes) in
  let bound := 1024 * Nat.pow q 8 in
  2 + input <= bound /\ 3 + 40 * input <= bound /\
  8 + 12 * live + 8 * edges <= bound /\
  2 + roots * S forest_fuel <= bound /\ 3 + 40 * (roots * S forest_fuel) <= bound /\
  2 * live + edges + 1 <= bound /\ live <= bound /\ rows <= bound /\ nodes <= bound.
Proof.
  intros Hlive Hrows Hroots Hedges Hfuel q bound.
  assert (Hq : 1 <= q) by (unfold q; lia).
  assert (Hinput : input <= q) by (unfold q; lia).
  assert (Hlive_q : live <= q) by (unfold q; lia).
  assert (Hrows_q : rows <= q) by (unfold q; lia).
  assert (Hedges_q : edges <= q * q).
  { assert (Hmul : live * rows <= q * q) by (apply Nat.mul_le_mono; assumption); lia. }
  assert (Hroots_q : roots <= q) by lia.
  assert (Hfuel_q : S forest_fuel <= 3 + 2 * q + q * q) by lia.
  assert (Hrun : roots * S forest_fuel <= q * (3 + 2 * q + q * q)).
  { apply Nat.mul_le_mono; assumption. }
  assert (Hpow : q * q * q <= Nat.pow q 8).
  { replace (q * q * q) with (Nat.pow q 3) by (cbn [Nat.pow]; nia).
    apply Nat.pow_le_mono_r; lia. }
  assert (Hsq : q * q <= q * q * q) by nia.
  assert (Hlin : q <= q * q * q) by nia.
  assert (Hone : 1 <= q * q * q) by nia.
  unfold bound; repeat split; nia.
Qed.

(** The original-input cubic budget covers the combined counted model components. *)
Lemma audit_dom_model_arithmetic count width :
  1024 * S count * S count +
    2 * count * (204 + 12 * width + 2 * count) +
    (128 * S count * S count + count * (128 + 3 * width) +
      64 * S count * S count + count * width) +
    64 * count + count * (66 + 2 * width) + count * (65 + width) +
    (2 + 5 * count) * (66 + 3 * width) +
    (64 + 64 * Nat.pow (S count) 3) + (65 + count) <=
    (128 * 64)%nat * Nat.pow (S count) 3 * Nat.pow (S width) 2.
Proof.
  set (x := S count); set (y := S width).
  set (reserve := Nat.pow x 3 * Nat.pow y 2).
  assert (Hx : 1 <= x) by (unfold x; lia).
  assert (Hy : 1 <= y) by (unfold y; lia).
  assert (Hcube : x * x <= Nat.pow x 3).
  { cbn [Nat.pow]; nia. }
  assert (Hy2 : 1 <= Nat.pow y 2).
  { pose proof (Nat.pow_nonzero y 2 ltac:(lia)); lia. }
  assert (Hcube_reserve : Nat.pow x 3 <= reserve).
  { unfold reserve; replace (Nat.pow x 3) with (Nat.pow x 3 * 1) at 1 by lia.
    apply Nat.mul_le_mono_l; exact Hy2. }
  assert (Hsquare_reserve : x * x <= reserve) by lia.
  assert (Hlinear : x <= reserve) by nia.
  assert (Hone : 1 <= reserve) by lia.
  assert (Hprod : count * width <= reserve).
  { assert (Hxy : count * width <= x * y) by (apply Nat.mul_le_mono; unfold x, y; lia).
    assert (Hxy2 : x * y <= (x * x) * (y * y)).
    { apply Nat.mul_le_mono; nia. }
    assert (Htarget : (x * x) * (y * y) <= reserve).
    { unfold reserve; cbn [Nat.pow]; apply Nat.mul_le_mono; nia. }
    lia. }
  assert (Hcount_square : count * count <= reserve).
  { assert (Hbound : count * count <= x * x) by (apply Nat.mul_le_mono; unfold x; lia); lia. }
  assert (Hcount : count <= reserve) by (unfold x in *; lia).
  assert (Hwidth : width <= reserve).
  { assert (Hwidth_prod : width <= x * y) by (unfold x, y; nia).
    assert (Hxy2 : x * y <= (x * x) * (y * y)) by (apply Nat.mul_le_mono; nia).
    assert (Htarget : (x * x) * (y * y) <= reserve).
    { unfold reserve; cbn [Nat.pow]; apply Nat.mul_le_mono; nia. }
    lia. }
  fold x y reserve.
  clear - Hcube_reserve Hsquare_reserve Hlinear Hone Hprod Hcount_square Hcount Hwidth.
  nia.
Qed.

(** The original tree-event bound covers all forest preparation and search ceilings. *)
Lemma audit_dom_forest_resources {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) parents :
  let forest := dom_forest p parents in
  let bound := audit_dom_input_event_bound p parents in
  2 + length (Graph.entries g) * S (Pos.to_nat (fuel p)) <= bound /\
  audit_dfs_full_input_event_bound p (Graph.entries g) <= bound /\
  audit_graph_prepare_full_event_bound forest <= bound /\
  2 + length (Graph.entries forest) * S (Pos.to_nat (fuel (prepare EV forest))) <= bound /\
  audit_dfs_full_input_event_bound (prepare EV forest) (Graph.entries forest) <= bound /\
  2 * length (Graph.nodes forest) + edge_count forest + 1 <= bound /\
  length (Graph.nodes forest) <= bound /\ length (Map.elements parents) <= bound /\
  audit_erase_nodes parents <= bound.
Proof.
  pose proof (audit_dom_live_length EV g p) as Hlive.
  pose proof (audit_dom_parent_rows_bound parents) as Hrows.
  pose proof (audit_dom_forest_roots_length EV g p parents) as Hroots.
  pose proof (audit_dom_forest_edge_count EV g p parents) as Hedges.
  assert (Hfuel : Pos.to_nat (fuel (prepare EV (dom_forest p parents))) =
    2 * length (preorder (dfs p FinSet.empty (Graph.entries g))) +
      edge_count (dom_forest p parents) + 2).
  { cbn [prepare fuel]; rewrite SuccNat2Pos.id_succ.
    unfold dom_forest; cbn [Graph.nodes]; lia. }
  pose proof (audit_dom_resource_arithmetic
    (length (Graph.entries g) * S (Pos.to_nat (fuel p))) (audit_erase_nodes parents)
    (length (preorder (dfs p FinSet.empty (Graph.entries g)))) (length (Map.elements parents))
    (length (Graph.entries (dom_forest p parents))) (edge_count (dom_forest p parents))
    (Pos.to_nat (fuel (prepare EV (dom_forest p parents)))) Hlive Hrows Hroots Hedges Hfuel)
    as Hbound.
  cbn zeta in Hbound |- *.
  unfold audit_dom_input_event_bound, audit_dom_input_scale, audit_graph_prepare_full_event_bound,
    audit_dfs_full_input_event_bound.
  unfold dom_forest at 2 3 4; cbn [Graph.nodes].
  destruct Hbound as [Ha [Hb [Hc [Hd [He [Hf [Hh [Hi Hj]]]]]]]].
  repeat split; try assumption; nia.
Qed.

(** Summing a projection is the same as summing after mapping it. *)
Lemma audit_dom_fold_map {A B} (cost : A -> nat) (project : B -> A) items :
  fold_right (fun item n => cost item + n) 0 (map project items) =
    fold_right (fun item n => cost (project item) + n) 0 items.
Proof.
  induction items as [|item rest IH]; cbn [map fold_right]; [reflexivity|now rewrite IH].
Qed.

(** Original and forest DFS widths and clock codes fit the tree input width. *)
Lemma audit_dom_tree_widths {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) parents :
  let forest := dom_forest p parents in
  let bound := audit_dom_input_event_bound p parents in
  let width := Nat.max (audit_dom_input_width EV g p parents)
    (audit_key_bits_weight (Pos.of_succ_nat (S bound))) in
  audit_dfs_full_input_width EV g p (Graph.entries g) <= width /\
  audit_dfs_full_input_width EV forest (prepare EV forest) (Graph.entries forest) <= width /\
  audit_graph_prepare_input_width EV forest <= width /\
  (forall n, n <= bound -> Pos.size_nat (Pos.of_succ_nat n) <= width).
Proof.
  cbn zeta. repeat split.
  - unfold audit_dom_input_width; eapply Nat.le_trans; [apply Nat.le_max_l|apply Nat.le_max_l].
  - eapply Nat.le_trans; [apply audit_dom_forest_dfs_width|apply Nat.le_max_l].
  - eapply Nat.le_trans; [apply audit_dom_forest_prepare_width|apply Nat.le_max_l].
  - intros n Hn; eapply Nat.le_trans; [|apply Nat.le_max_r].
    unfold audit_key_bits_weight; apply audit_dfs_clock_width.
    rewrite SuccNat2Pos.id_succ; lia.
Qed.

(** One DFS model trace fits the common count, width and clock bounds. *)
Lemma audit_dom_dfs_model_scalar count bound input_width clock_width clock width work :
  count <= bound -> input_width <= width -> clock_width <= width -> clock <= bound ->
  work <= count * (140 + 12 * Nat.max input_width clock_width + 2 * clock) ->
  64 * count + work <= bound * (204 + 12 * width + 2 * bound).
Proof.
  intros Hcount Hinput Hclock_width Hclock Hwork.
  assert (Hmax : Nat.max input_width clock_width <= width) by (apply Nat.max_lub; assumption).
  assert (Hmul : count * (140 + 12 * Nat.max input_width clock_width + 2 * clock) <=
    bound * (140 + 12 * width + 2 * bound)) by (apply Nat.mul_le_mono; lia).
  clear - Hwork Hcount Hmul; nia.
Qed.

(** The actual forest preparation trace fits the common scalar budget. *)
Lemma audit_dom_prepare_model_bound {V} (EV : encoding V) (forest : Graph.t V V)
    (prep_events : list (audit_prepare_nested_event V V (audit_dom_body V))) bound width :
  audit_graph_prepare_full_work (map fst prep_events) <= audit_graph_prepare_full_budget EV
    forest ->
  audit_graph_prepare_full_event_bound forest <= bound ->
  2 * length (Graph.nodes forest) + edge_count forest + 1 <= bound ->
  audit_graph_prepare_input_width EV forest <= width ->
  audit_key_bits_weight (Pos.of_succ_nat
    (2 * length (Graph.nodes forest) + edge_count forest + 1)) <= width ->
  fold_right (fun event n => audit_graph_full_event_work (fst event) + n) 0 prep_events <=
    128 * S bound * S bound + bound * (128 + 3 * width) +
      64 * S bound * S bound + bound * width.
Proof.
  intros Hwork Hcount Hamount Hwidth Hbits.
  unfold audit_graph_prepare_full_work in Hwork; rewrite audit_dom_fold_map in Hwork.
  unfold audit_graph_prepare_full_budget in Hwork; cbn zeta in Hwork.
  set (pc := audit_graph_prepare_full_event_bound forest) in *.
  set (amount := 2 * length (Graph.nodes forest) + edge_count forest + 1) in *.
  set (pw := audit_graph_prepare_input_width EV forest) in *.
  assert (Hquad1 : 128 * S pc * S pc <= 128 * S bound * S bound).
  { apply Nat.mul_le_mono; [apply Nat.mul_le_mono_l|]; lia. }
  assert (Hquad2 : 64 * S amount * S amount <= 64 * S bound * S bound).
  { apply Nat.mul_le_mono; [apply Nat.mul_le_mono_l|]; lia. }
  assert (Hlinear1 : pc * (128 + 3 * pw) <= bound * (128 + 3 * width)).
  { apply Nat.mul_le_mono; lia. }
  assert (Hlinear2 : amount * audit_key_bits_weight (Pos.of_succ_nat amount) <= bound * width).
  { apply Nat.mul_le_mono; assumption. }
  clear - Hwork Hquad1 Hquad2 Hlinear1 Hlinear2; lia.
Qed.

(** Bounded same-run stage traces compose into the tree model-work budget. *)
Lemma audit_dom_tree_trace_bound {V E} (EV : encoding V) parents nodes bound width
    (first_events : list (audit_dfs_full_call V E))
    (child_events root_events : list (audit_dom_call V E))
    (prep_events : list (audit_prepare_nested_event V V (audit_dom_body V)))
    (dfs_events : list (audit_dfs_nested_event V V (audit_dom_body V))) :
  let events := map AuditDomInitialDfs first_events ++
    [AuditDomElements parents (Map.elements parents)] ++ child_events ++ root_events ++
    map AuditDomPrepare prep_events ++ map AuditDomDfs dfs_events ++ [AuditDomOutput nodes] in
  length events <= bound -> length prep_events <= bound -> nodes <= bound ->
  audit_erase_nodes parents <= bound ->
  audit_dom_event_sum EV child_events <= (1 + 3 * bound) * (66 + 3 * width) ->
  audit_dom_event_sum EV root_events <= (1 + 2 * bound) * (66 + 3 * width) ->
  audit_prepare_nested_body_work (audit_dom_body_work EV) prep_events <= bound * (66 + 2 * width) ->
  audit_dfs_nested_body_work (audit_dom_body_work EV) dfs_events <= bound * (65 + width) ->
  64 * length first_events +
    fold_right (fun event n => audit_dfs_full_model_event EV event + n) 0 first_events <=
      bound * (204 + 12 * width + 2 * bound) ->
  64 * length dfs_events +
    fold_right (fun event n => audit_dfs_full_model_event EV (fst event) + n) 0 dfs_events <=
      bound * (204 + 12 * width + 2 * bound) ->
  fold_right (fun event n => audit_graph_full_event_work (fst event) + n) 0 prep_events <=
    128 * S bound * S bound + bound * (128 + 3 * width) +
      64 * S bound * S bound + bound * width ->
  audit_dom_model_work EV events <=
    (128 * 64)%nat * Nat.pow (S bound) 3 * Nat.pow (S width) 2.
Proof.
  intros events Hcount Hprep_actual Hlive Hnodes Hchild_bound Hroot_bound Hprep_body_bound
    Hdfs_body_bound Hfirst_bound Hdfs_bound Hprep_full.
  assert (Helements : 64 * Nat.pow (S (audit_erase_nodes parents)) 3 <=
    64 * Nat.pow (S bound) 3).
  { apply Nat.mul_le_mono_l, Nat.pow_le_mono_l; lia. }
  assert (Hquad : 1024 * S (length events) * S (length events) <=
    1024 * S bound * S bound).
  { apply Nat.mul_le_mono; [apply Nat.mul_le_mono_l|]; lia. }
  assert (Hprep_wrap : 64 * length prep_events <= 64 * bound)
    by (apply Nat.mul_le_mono_l; exact Hprep_actual).
  change (1024 * S (length events) * S (length events) + audit_dom_event_sum EV events <=
    (128 * 64)%nat * Nat.pow (S bound) 3 * Nat.pow (S width) 2).
  unfold events in *.
  repeat rewrite audit_dom_event_sum_app.
  rewrite audit_dom_initial_model_sum, audit_dom_prepare_model_sum, audit_dom_dfs_model_events.
  cbn [audit_dom_event_sum fold_right audit_dom_event_work].
  cbv beta iota zeta delta [audit_dom_event_work].
  assert (Hdfs_both : (64 * length first_events +
    fold_right (fun event n => audit_dfs_full_model_event EV event + n) 0 first_events) +
    (64 * length dfs_events +
    fold_right (fun event n => audit_dfs_full_model_event EV (fst event) + n) 0 dfs_events) <=
    2 * bound * (204 + 12 * width + 2 * bound)).
  { clear - Hfirst_bound Hdfs_bound; nia. }
  assert (Hchildren_both : audit_dom_event_sum EV child_events + audit_dom_event_sum EV
    root_events <=
    (2 + 5 * bound) * (66 + 3 * width)).
  { clear - Hchild_bound Hroot_bound; nia. }
  pose proof (audit_dom_model_arithmetic bound width) as Harithmetic.
  eapply Nat.le_trans; [|exact Harithmetic].
  clear - Hquad Hprep_wrap Hdfs_both Hprep_full Hprep_body_bound Hdfs_body_bound
    Hchildren_both Hlive Helements. lia.
Qed.

(** Forest preparation and DFS preserve the actual traces and their stage bounds. *)
Lemma audit_dom_tree_forest_stages {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) parents
    (prep_events : list (audit_prepare_nested_event V V (audit_dom_body V)))
    (dfs_events : list (audit_dfs_nested_event V V (audit_dom_body V))) result :
  let forest := dom_forest p parents in
  audit_graph_prepare_nested_counted EV forest
    (audit_dom_prepare_callbacks EV (dom_children EV (Map.elements parents))) =
      (prepare EV forest, prep_events) ->
  audit_dfs_nested_counted (prepare EV forest) (audit_dom_dfs_callbacks EV) FinSet.empty
    (Graph.entries forest) = (result, dfs_events) ->
  audit_graph_prepare_full_work (map fst prep_events) <= audit_graph_prepare_full_budget EV
    forest /\
  audit_prepare_nested_body_work (audit_dom_body_work EV) prep_events <=
    length prep_events * (66 + 2 * audit_graph_prepare_input_width EV forest) /\
  fold_right (fun event n => audit_dfs_full_model_event EV (fst event) + n) 0 dfs_events <=
    length dfs_events * (140 + 12 *
      Nat.max (audit_dfs_full_input_width EV forest (prepare EV forest) (Graph.entries forest))
        (Pos.size_nat (Pos.of_succ_nat
          (2 + length (Graph.entries forest) * S (Pos.to_nat (fuel (prepare EV forest)))))) +
      2 * (2 + length (Graph.entries forest) * S (Pos.to_nat (fuel (prepare EV forest))))) /\
  audit_dfs_nested_body_work (audit_dom_body_work EV) dfs_events <=
    length dfs_events * (65 + audit_dfs_full_input_width EV forest (prepare EV forest)
      (Graph.entries forest)).
Proof.
  intros forest Hprep_run Hdfs_run.
  assert (Hprepare : audit_prepare_callbacks_erase EV forest
    (audit_dom_prepare_callbacks EV (dom_children EV (Map.elements parents)))).
  { unfold forest, dom_forest; apply audit_dom_prepare_callbacks_erases. }
  assert (Hdfs : audit_dfs_callbacks_erase EV forest (audit_dom_dfs_callbacks EV)).
  { unfold forest, dom_forest; apply audit_dom_dfs_callbacks_erases. }
  pose proof (audit_graph_prepare_nested_correct V V (audit_dom_body V) EV forest
    (audit_dom_prepare_callbacks EV (dom_children EV (Map.elements parents))) Hprepare) as
      Hprepared.
  pose proof (audit_dom_prepare_bodies EV forest (dom_children EV (Map.elements parents))
    ltac:(intro v; reflexivity) ltac:(intro v; reflexivity)) as Hbodies.
  rewrite Hprep_run in Hprepared, Hbodies; cbn [fst snd] in Hprepared, Hbodies.
  destruct Hprepared as [_ [_ [_ Hprep_work]]].
  pose proof (audit_dom_prepare_body_sum EV forest prep_events Hbodies) as Hprep_body.
  pose proof (audit_dfs_nested_correct V V (audit_dom_body V) EV forest (prepare EV forest)
    (audit_dom_dfs_callbacks EV) FinSet.empty (Graph.entries forest) Hdfs) as Hsecond.
  pose proof (audit_dom_dfs_model_sum EV forest (prepare EV forest) (Graph.entries forest) Hdfs)
    as Hdfs_body.
  pose proof (audit_dfs_full_event_work_bound (prepare EV forest) FinSet.empty
    (Graph.entries forest)) as Hsecond_sum.
  rewrite Hdfs_run in Hsecond, Hdfs_body; cbn [fst snd] in Hsecond, Hdfs_body.
  destruct Hsecond as [_ [Htrace _]].
  cbn zeta in Hsecond_sum; rewrite <- Htrace in Hsecond_sum; rewrite audit_dom_fold_map in
    Hsecond_sum.
  rewrite length_map in Hsecond_sum. repeat split; assumption.
Qed.

(** Actual child and root traces fit the bounded parent and live-key widths. *)
Lemma audit_dom_tree_index_costs {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) parents (child_events root_events : list (audit_dom_call V E)) :
  snd (audit_dom_children_counted (E := E) EV (Map.elements parents)) = child_events ->
  snd (audit_dom_roots_counted (E := E) EV parents
    (preorder (dfs p FinSet.empty (Graph.entries g)))) = root_events ->
  let bound := audit_dom_input_event_bound p parents in
  let width := Nat.max (audit_dom_input_width EV g p parents)
    (audit_key_bits_weight (Pos.of_succ_nat (S bound))) in
  audit_dom_event_sum EV child_events <= (1 + 3 * bound) * (66 + 3 * width) /\
  audit_dom_event_sum EV root_events <= (1 + 2 * bound) * (66 + 3 * width).
Proof.
  intros Hchild Hroot bound width.
  pose proof (audit_dom_forest_resources EV g p parents) as Hresources.
  cbn zeta in Hresources; fold bound in Hresources.
  destruct Hresources as [_ [_ [_ [_ [_ [_ [Hlive [Hrows _]]]]]]]].
  assert (Hchild_keys : forall v u, In (v, u) (Map.elements parents) ->
    audit_key_bits_weight (encode EV u) <= width).
  { intros v u Hin; pose proof (proj2 (audit_dom_parent_width EV g p parents v u Hin)) as Hkey.
    unfold audit_key_bits_weight in *; eapply Nat.le_trans; [exact Hkey|unfold width; apply
      Nat.le_max_l]. }
  assert (Hlive_keys : forall v, In v (preorder (dfs p FinSet.empty (Graph.entries g))) ->
    audit_key_bits_weight (encode EV v) <= width).
  { intros v Hin; pose proof (audit_dom_live_input_width EV g p parents v Hin) as Hkey.
    unfold audit_key_bits_weight in *; eapply Nat.le_trans; [exact Hkey|unfold width; apply
      Nat.le_max_l]. }
  pose proof (audit_dom_children_work (E := E) EV (Map.elements parents) width Hchild_keys) as Hcw.
  pose proof (audit_dom_roots_work (E := E) EV parents
    (preorder (dfs p FinSet.empty (Graph.entries g))) width Hlive_keys) as Hrw.
  cbn zeta in Hcw, Hrw; rewrite Hchild in Hcw; rewrite Hroot in Hrw.
  split.
  - eapply Nat.le_trans; [exact Hcw|apply Nat.mul_le_mono_r; lia].
  - eapply Nat.le_trans; [exact Hrw|apply Nat.mul_le_mono_r].
    unfold dom_forest in Hlive; cbn [Graph.nodes] in Hlive; lia.
Qed.

(** The counted tree stages share graph, clock and event ceilings. *)
Lemma audit_dom_tree_stages {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) parents first_events child_events root_events prep_events dfs_events
      result :
  audit_dfs_full_counted p FinSet.empty (Graph.entries g) =
    (dfs p FinSet.empty (Graph.entries g), first_events) ->
  snd (audit_dom_children_counted (E := E) EV (Map.elements parents)) = child_events ->
  snd (audit_dom_roots_counted (E := E) EV parents
    (preorder (dfs p FinSet.empty (Graph.entries g)))) = root_events ->
  let forest := dom_forest p parents in
  audit_graph_prepare_nested_counted EV forest
    (audit_dom_prepare_callbacks EV (dom_children EV (Map.elements parents))) =
      (prepare EV forest, prep_events) ->
  audit_dfs_nested_counted (prepare EV forest) (audit_dom_dfs_callbacks EV) FinSet.empty
    (Graph.entries forest) = (result, dfs_events) ->
  let events := map AuditDomInitialDfs first_events ++
    [AuditDomElements parents (Map.elements parents)] ++ child_events ++ root_events ++
    map AuditDomPrepare prep_events ++ map AuditDomDfs dfs_events ++
    [AuditDomOutput (length (Graph.nodes forest))] in
  length events <= audit_dom_input_event_bound p parents ->
  audit_dom_model_work EV events <= audit_dom_input_budget EV g p parents.
Proof.
  intros Hfirst_run Hchild Hroot forest Hprep_run Hdfs_run events Hcount.
  set (bound := audit_dom_input_event_bound p parents) in *.
  set (width := Nat.max (audit_dom_input_width EV g p parents)
    (audit_key_bits_weight (Pos.of_succ_nat (S bound)))).
  pose proof (audit_dom_forest_resources EV g p parents) as Hresources.
  cbn zeta in Hresources; fold forest bound in Hresources.
  destruct Hresources as [Hfirst_ceiling [_ [Hprep_limit [Hdfs_ceiling
    [_ [Hamount [Hlive [_ Hnodes]]]]]]]].
  pose proof (audit_dom_tree_widths EV g p parents) as
    [Horig_width [Hforest_width [Hprep_width Hclock]]].
  cbn zeta in Horig_width, Hforest_width, Hprep_width, Hclock.
  fold forest bound width in Horig_width, Hforest_width, Hprep_width, Hclock.
  pose proof (audit_dfs_full_event_work_bound p FinSet.empty (Graph.entries g)) as Hfirst_sum.
  rewrite Hfirst_run in Hfirst_sum; cbn [fst snd] in Hfirst_sum.
  destruct (audit_dom_tree_forest_stages EV g p parents prep_events dfs_events result
    Hprep_run Hdfs_run) as [Hprep_work [Hprep_body [Hsecond_sum Hdfs_body]]].
  fold forest in Hprep_work, Hprep_body, Hsecond_sum, Hdfs_body.
  pose proof (audit_dom_tree_index_costs EV g p parents child_events root_events Hchild Hroot)
    as [Hchild_bound Hroot_bound].
  cbn zeta in Hchild_bound, Hroot_bound; fold bound width in Hchild_bound, Hroot_bound.
  assert (Hlengths : length first_events +
    (1 + (length child_events + (length root_events + (length prep_events +
      (length dfs_events + 1))))) <= bound).
  { unfold events in Hcount; repeat rewrite length_app in Hcount;
      repeat rewrite length_map in Hcount; cbn [length] in Hcount; exact Hcount. }
  assert (Hfirst_actual : length first_events <= bound) by lia.
  assert (Hprep_actual : length prep_events <= bound) by lia.
  assert (Hdfs_actual : length dfs_events <= bound) by lia.
  assert (Horig_clock : Pos.size_nat (Pos.of_succ_nat
    (2 + length (Graph.entries g) * S (Pos.to_nat (fuel p)))) <= width) by (apply Hclock; lia).
  assert (Hforest_clock : Pos.size_nat (Pos.of_succ_nat
    (2 + length (Graph.entries forest) * S (Pos.to_nat (fuel (prepare EV forest))))) <= width)
    by (apply Hclock; lia).
  cbn zeta in Hfirst_sum, Hsecond_sum.
  pose proof (audit_dom_dfs_model_scalar (length first_events) bound
    (audit_dfs_full_input_width EV g p (Graph.entries g))
    (Pos.size_nat (Pos.of_succ_nat (2 + length (Graph.entries g) * S (Pos.to_nat (fuel p)))))
    (2 + length (Graph.entries g) * S (Pos.to_nat (fuel p))) width _
    Hfirst_actual Horig_width Horig_clock Hfirst_ceiling Hfirst_sum) as Hfirst_bound.
  pose proof (audit_dom_dfs_model_scalar (length dfs_events) bound
    (audit_dfs_full_input_width EV forest (prepare EV forest) (Graph.entries forest))
    (Pos.size_nat (Pos.of_succ_nat
      (2 + length (Graph.entries forest) * S (Pos.to_nat (fuel (prepare EV forest))))))
    (2 + length (Graph.entries forest) * S (Pos.to_nat (fuel (prepare EV forest)))) width _
    Hdfs_actual Hforest_width Hforest_clock Hdfs_ceiling Hsecond_sum) as Hdfs_bound.
  assert (Hamount_clock : audit_key_bits_weight (Pos.of_succ_nat
    (2 * length (Graph.nodes forest) + edge_count forest + 1)) <= width).
  { unfold audit_key_bits_weight; apply Hclock; exact Hamount. }
  pose proof (audit_dom_prepare_model_bound EV forest prep_events bound width
    Hprep_work Hprep_limit Hamount Hprep_width Hamount_clock) as Hprep_full.
  assert (Hprep_body_bound : audit_prepare_nested_body_work (audit_dom_body_work EV) prep_events <=
    bound * (66 + 2 * width)).
  { eapply Nat.le_trans; [exact Hprep_body|apply Nat.mul_le_mono; lia]. }
  assert (Hdfs_body_bound : audit_dfs_nested_body_work (audit_dom_body_work EV) dfs_events <=
    bound * (65 + width)).
  { eapply Nat.le_trans; [exact Hdfs_body|apply Nat.mul_le_mono; lia]. }
  unfold audit_dom_input_budget; fold bound width.
  unfold events in Hcount |- *.
  eapply (audit_dom_tree_trace_bound EV parents (length (Graph.nodes forest)) bound width
    first_events child_events root_events prep_events dfs_events); eassumption.
Qed.

(** The actual prepared forest stages satisfy the tree-work accounting. *)
Lemma audit_dom_tree_forest_tail {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) parents first_events child_events root_events :
  audit_dfs_full_counted p FinSet.empty (Graph.entries g) =
    (dfs p FinSet.empty (Graph.entries g), first_events) ->
  snd (audit_dom_children_counted (E := E) EV (Map.elements parents)) = child_events ->
  snd (audit_dom_roots_counted (E := E) EV parents
    (preorder (dfs p FinSet.empty (Graph.entries g)))) = root_events ->
  let forest := dom_forest p parents in
  let produced :=
    (let '(fp, prep_events) := audit_graph_prepare_nested_counted EV forest
        (audit_dom_prepare_callbacks EV (dom_children EV (Map.elements parents))) in
      let '(result, dfs_events) := audit_dfs_nested_counted fp (audit_dom_dfs_callbacks EV)
        FinSet.empty (Graph.entries forest) in
      (DomTree parents (pre_num result) (post_num result),
      map AuditDomInitialDfs first_events ++ [AuditDomElements parents (Map.elements parents)] ++
      child_events ++ root_events ++ map AuditDomPrepare prep_events ++ map AuditDomDfs
        dfs_events ++ [AuditDomOutput (length (Graph.nodes forest))])) in
  length (snd produced) <= audit_dom_input_event_bound p parents ->
  audit_dom_model_work EV (snd produced) <= audit_dom_input_budget EV g p parents.
Proof.
  intros Hfirst Hchild Hroot forest produced Hcount.
  assert (Hprepare : audit_prepare_callbacks_erase EV forest
    (audit_dom_prepare_callbacks EV (dom_children EV (Map.elements parents)))).
  { unfold forest, dom_forest; apply audit_dom_prepare_callbacks_erases. }
  pose proof (audit_graph_prepare_nested_correct V V (audit_dom_body V) EV forest
    (audit_dom_prepare_callbacks EV (dom_children EV (Map.elements parents))) Hprepare) as
      Hprepared.
  unfold produced in Hcount |- *.
  destruct (audit_graph_prepare_nested_counted EV forest
    (audit_dom_prepare_callbacks EV (dom_children EV (Map.elements parents)))) as [fp prep_events]
    eqn:Hprep_run.
  cbn [fst snd] in Hprepared; destruct Hprepared as [Hprepared _]; subst fp.
  destruct (audit_dfs_nested_counted (prepare EV forest) (audit_dom_dfs_callbacks EV)
    FinSet.empty (Graph.entries forest)) as [result dfs_events] eqn:Hdfs_run.
  cbn [snd] in Hcount |- *.
  eapply (audit_dom_tree_stages EV g p parents first_events child_events root_events prep_events
    dfs_events result); eassumption.
Qed.

(** The selected tree model work fits the original input budget. *)
Lemma audit_dom_tree_work_bound {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) parents :
  audit_dom_model_work EV (snd (audit_dom_tree_counted p parents)) <=
    audit_dom_input_budget EV g p parents.
Proof.
  pose proof (audit_dom_tree_count_bound EV g p parents) as Hcount.
  pose proof (audit_dfs_full_counted_correct V E EV g p FinSet.empty (Graph.entries g)) as Hfirst.
  pose proof (audit_dom_children_erases (E := E) EV (Map.elements parents)) as Hchildren.
  pose proof (audit_dom_roots_erases (E := E) EV parents
    (preorder (dfs p FinSet.empty (Graph.entries g)))) as Hroots.
  unfold audit_dom_tree_counted in Hcount |- *.
  destruct (audit_dfs_full_counted p FinSet.empty (Graph.entries g)) as [search first_events]
    eqn:Hfirst_run.
  cbn [fst snd] in Hfirst; destruct Hfirst as [Hsearch _]; subst search.
  destruct (audit_dom_children_counted EV (Map.elements parents)) as [children child_events]
    eqn:Hchildren_run.
  cbn [fst] in Hchildren; subst children.
  destruct (audit_dom_roots_counted EV parents (preorder (dfs p FinSet.empty (Graph.entries g))))
    as [roots root_events] eqn:Hroots_run.
  cbn [fst] in Hroots; subst roots.
  assert (Hchild : snd (audit_dom_children_counted (E := E) EV (Map.elements parents)) =
    child_events) by (rewrite Hchildren_run; reflexivity).
  assert (Hroot : snd (audit_dom_roots_counted (E := E) EV parents
    (preorder (dfs p FinSet.empty (Graph.entries g)))) = root_events)
    by (rewrite Hroots_run; reflexivity).
  eapply (audit_dom_tree_forest_tail EV g p parents first_events child_events root_events);
    eassumption.
Qed.

(** Counted tree construction erases and meets its input-derived event and work bounds. *)
Theorem audit_dom_tree_counted_correct : audit_dom_tree_counted_statement.
Proof.
  intros V E EV g p parents.
  pose proof (audit_dom_tree_counted_erases EV g p parents) as Herase.
  pose proof (audit_dom_tree_count_bound EV g p parents) as Hcount.
  pose proof (audit_dom_tree_work_bound EV g p parents) as Hwork.
  destruct (audit_dom_tree_counted p parents) as [result events].
  cbn [fst snd] in Herase, Hcount, Hwork |- *; repeat split; assumption.
Qed.

(** Callback-body sums distribute over two prices on the same captured events. *)
Lemma audit_dom_body_fold_add {A} (first second : A -> nat) events :
  fold_right (fun event n => (first event + second event) + n) 0 events =
    fold_right (fun event n => first event + n) 0 events +
    fold_right (fun event n => second event + n) 0 events.
Proof.
  induction events as [|event rest IH]; cbn [fold_right]; lia.
Qed.

(** Nested compression body work distributes over the two captured callback prices. *)
Lemma audit_dom_semi_body_event_add {V B} (first second : B -> nat)
    (event : audit_semi_nested_event V B) :
  audit_semi_nested_body_event_work (fun item => first item + second item) event =
    audit_semi_nested_body_event_work first event + audit_semi_nested_body_event_work second event.
Proof.
  destruct event as [site|vertex_map|rank_map|a b result trace];
    cbn [audit_semi_nested_body_event_work]; try lia;
    destruct vertex_map || destruct rank_map;
    cbn [audit_semi_nested_body_event_work]; rewrite audit_dom_body_fold_add; reflexivity.
Qed.

(** One semidominator producer event preserves both components of each recorded callback price. *)
Lemma audit_dom_producer_body_event_add {V E B} (first second : B -> nat)
    (event : audit_semi_producer_nested_event V E B) :
  audit_semi_producer_nested_body_event_work (fun item => first item + second item) event =
    audit_semi_producer_nested_body_event_work first event +
      audit_semi_producer_nested_body_event_work second event.
Proof.
  destruct event as [site|edge vertex body|inner|tree|pred|size];
    cbn [audit_semi_producer_nested_body_event_work]; try lia.
  - apply audit_dom_body_fold_add.
  - apply audit_dom_semi_body_event_add.
  - destruct tree; cbn [audit_semi_producer_nested_body_event_work];
      apply audit_dom_body_fold_add.
  - destruct pred; cbn [audit_semi_producer_nested_body_event_work];
      apply audit_dom_body_fold_add.
Qed.

(** A semidominator producer trace distributes both prices without replaying callbacks. *)
Lemma audit_dom_producer_body_add {V E B} (first second : B -> nat)
    (events : list (audit_semi_producer_nested_event V E B)) :
  audit_semi_producer_nested_body_work (fun item => first item + second item) events =
    audit_semi_producer_nested_body_work first events + audit_semi_producer_nested_body_work second
      events.
Proof.
  unfold audit_semi_producer_nested_body_work.
  induction events as [|event rest IH]; cbn [fold_right]; [reflexivity|].
  rewrite audit_dom_producer_body_event_add, IH; lia.
Qed.

(** One LT event preserves both components of each recorded callback price. *)
Lemma audit_dom_lt_body_event_add {V E B} (first second : B -> nat)
    (event : audit_lt_nested_event V E B) :
  audit_lt_nested_body_event_work (fun item => first item + second item) event =
    audit_lt_nested_body_event_work first event + audit_lt_nested_body_event_work second event.
Proof.
  destruct event as [site|semi|producer|bucket|tree|edge vertex source_body|vertex code encode_body|
    a b result trace|size]; cbn [audit_lt_nested_body_event_work]; try lia.
  - apply audit_dom_semi_body_event_add.
  - apply audit_dom_producer_body_event_add.
  - destruct bucket; cbn [audit_lt_nested_body_event_work]; apply audit_dom_body_fold_add.
  - destruct tree; cbn [audit_lt_nested_body_event_work]; apply audit_dom_body_fold_add.
  - apply audit_dom_body_fold_add.
  - apply audit_dom_body_fold_add.
Qed.

(** An LT trace distributes both prices over its actual recorded bodies. *)
Lemma audit_dom_lt_body_add {V E B} (first second : B -> nat)
    (events : list (audit_lt_nested_event V E B)) :
  audit_lt_nested_body_work (fun item => first item + second item) events =
    audit_lt_nested_body_work first events + audit_lt_nested_body_work second events.
Proof.
  unfold audit_lt_nested_body_work.
  induction events as [|event rest IH]; cbn [fold_right]; [reflexivity|].
  rewrite audit_dom_lt_body_event_add, IH; lia.
Qed.

(** The captured stages compose once their internal work fits the virtual input reserve. *)
Lemma audit_dom_captured_stage_bound {V E B} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (cb : audit_virtual_base_callbacks V E B) (source : E -> V * list B)
    (weight : B -> nat) vp search prepare_events dfs_events semi_state semi_events
    virtual_parents lt_events parents erase_events receipt :
  audit_virtual_base_callbacks_erase EV g cb ->
  (forall edge, fst (source edge) = Graph.source g edge) ->
  audit_virtual_source_search EV g cb = (vp, (search, (prepare_events, dfs_events))) ->
  audit_semi_producer_nested_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
    vp search semi_state semi_events ->
  audit_lt_nested_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
    search (SemiState.result semi_state) virtual_parents lt_events ->
  audit_erase_virtual_nested (audit_virtual_base_encode cb) virtual_parents =
    (parents, erase_events) ->
  receipt = audit_dom_search_source_counted p parents
    (AuditDfsCallbackModel V E B (audit_virtual_base_target cb) (audit_virtual_base_encode cb)) ->
  audit_virtual_source_search_budget EV g +
    audit_semi_producer_input_budget (virtual_encoding EV) (virtual_graph EV g) vp search +
    audit_lt_nested_input_budget (virtual_encoding EV) (virtual_graph EV g) search
      (SemiState.result semi_state) +
    audit_erase_nested_budget EV virtual_parents +
    audit_semi_producer_nested_body_work audit_virtual_full_internal_event_work semi_events +
    audit_lt_nested_body_work audit_virtual_full_internal_event_work lt_events <=
    audit_virtual_lt_input_budget EV g ->
  audit_prepare_source_work
    (fun event => audit_virtual_full_internal_event_work event +
      audit_virtual_full_body_event_work weight event) prepare_events +
    audit_dfs_source_work
      (fun event => audit_virtual_full_internal_event_work event +
        audit_virtual_full_body_event_work weight event) dfs_events +
    audit_virtual_semi_stage_work weight semi_events + audit_virtual_lt_stage_work weight lt_events
      +
    audit_erase_nested_work weight erase_events +
    audit_dom_source_work weight (audit_dom_source_events receipt) <=
  audit_virtual_lt_input_budget EV g + audit_dom_search_source_budget EV g p parents receipt +
    audit_prepare_source_body_work (audit_virtual_full_body_event_work weight) prepare_events +
    audit_dfs_source_body_work (audit_virtual_full_body_event_work weight) dfs_events +
    audit_virtual_semi_external_work weight semi_events + audit_virtual_lt_external_work weight
      lt_events + audit_erase_nested_body_work weight erase_events +
    audit_dom_source_external_work weight (audit_dom_source_events receipt).
Proof.
  intros Hcallbacks Hsource Hsearch Hsemi Hlt Herase Hreceipt Hreserve.
  pose proof (audit_virtual_source_search_holds V E B EV g p cb weight Hcallbacks) as Hvirtual.
  rewrite Hsearch in Hvirtual.
  cbv beta iota zeta in Hvirtual.
  destruct Hvirtual as [_ [_ Hvirtual]].
  assert (Hfull_encode : forall v,
    fst (audit_virtual_full_encode cb v) = encode (virtual_encoding EV) v).
  { destruct Hcallbacks as [_ [_ Hencode]].
    intros [v|[]]; cbn [audit_virtual_full_encode virtual_encoding].
    - specialize (Hencode v); destruct (audit_virtual_base_encode cb v);
      cbn [fst] in Hencode |- *; now rewrite Hencode.
    - reflexivity. }
  pose proof (audit_virtual_full_source_correct V E B EV g source Hsource) as Hfull_source.
  pose proof (audit_semi_producer_nested_bound _ _ _ (virtual_encoding EV) (virtual_graph EV g)
    vp search (audit_virtual_full_encode cb) (audit_virtual_full_source source)
    (fun event => audit_virtual_full_internal_event_work event +
      audit_virtual_full_body_event_work weight event) semi_state semi_events
    Hfull_encode Hfull_source Hsemi) as [_ Hsemi_work].
  pose proof (audit_lt_nested_bound _ _ _ (virtual_encoding EV) (virtual_graph EV g)
    search (SemiState.result semi_state) (audit_virtual_full_encode cb)
    (audit_virtual_full_source source)
    (fun event => audit_virtual_full_internal_event_work event +
      audit_virtual_full_body_event_work weight event) virtual_parents lt_events
    Hfull_encode Hfull_source Hlt) as [_ Hlt_work].
  destruct Hcallbacks as [_ [Htarget Hencode]].
  pose proof (audit_erase_nested_correct V B EV (audit_virtual_base_encode cb) weight
    virtual_parents
    Hencode) as Herase_work.
  rewrite Herase in Herase_work; cbn [fst snd] in Herase_work; destruct Herase_work as [_
    Herase_work].
  assert (Hdom_cb : audit_dfs_callbacks_erase EV g
    (AuditDfsCallbackModel V E B (audit_virtual_base_target cb) (audit_virtual_base_encode cb)))
    by (split; assumption).
  pose proof (audit_dom_search_source_correct V E B EV g p parents
    (AuditDfsCallbackModel V E B (audit_virtual_base_target cb) (audit_virtual_base_encode cb))
    weight Hdom_cb) as [_ Hdom_work].
  rewrite <- Hreceipt in Hdom_work.
  rewrite audit_dom_producer_body_add in Hsemi_work.
  rewrite audit_dom_lt_body_add in Hlt_work.
  unfold audit_virtual_semi_stage_work, audit_virtual_lt_stage_work,
    audit_virtual_semi_external_work, audit_virtual_lt_external_work.
  lia.
Qed.

(** A bound on the actual virtual-stage reserve yields the full shared-run contract. *)
Lemma audit_dom_single_run_from_reserve :
  (forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (cb : audit_virtual_base_callbacks V E B) (source : E -> V * list B)
    vp search prepare_events dfs_events semi_state semi_events virtual_parents lt_events
    parents erase_events receipt,
    audit_virtual_base_callbacks_erase EV g cb ->
    (forall edge, fst (source edge) = Graph.source g edge) ->
    audit_virtual_source_search EV g cb = (vp, (search, (prepare_events, dfs_events))) ->
    audit_semi_producer_nested_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
      vp search semi_state semi_events ->
    audit_lt_nested_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
      search (SemiState.result semi_state) virtual_parents lt_events ->
    audit_erase_virtual_nested (audit_virtual_base_encode cb) virtual_parents =
      (parents, erase_events) ->
    receipt = audit_dom_search_source_counted p parents
      (AuditDfsCallbackModel V E B (audit_virtual_base_target cb) (audit_virtual_base_encode cb)) ->
    audit_virtual_source_search_budget EV g +
      audit_semi_producer_input_budget (virtual_encoding EV) (virtual_graph EV g) vp search +
      audit_lt_nested_input_budget (virtual_encoding EV) (virtual_graph EV g) search
        (SemiState.result semi_state) + audit_erase_nested_budget EV virtual_parents +
      audit_semi_producer_nested_body_work audit_virtual_full_internal_event_work semi_events +
      audit_lt_nested_body_work audit_virtual_full_internal_event_work lt_events <=
      audit_virtual_lt_input_budget EV g) ->
  audit_default_dom_single_run_statement.
Proof.
  intro Hreserve.
  intros V E B EV g p cb source weight Hcallbacks Hsource.
  destruct (audit_default_dom_run_erases EV g p cb source Hcallbacks Hsource)
    as (vp & search & prepare_events & dfs_events & semi_state & semi_events & virtual_parents &
      lt_events & parents & erase_events & receipt & result & Hsearch & Hsemi & Hlt & Herase &
      Hreceipt & Hresult & Hdom).
  exists vp, search, prepare_events, dfs_events, semi_state, semi_events, virtual_parents,
    lt_events,
    parents, erase_events, receipt, result.
  repeat split; try assumption.
  eapply audit_dom_captured_stage_bound; try eassumption.
  eapply Hreserve; eassumption.
Qed.

(** A lifted encoder call uses at most two fixed-cost virtual wrapper events. *)
Lemma audit_dom_virtual_encode_internal_bound V E B (cb : audit_virtual_base_callbacks V E B) v :
  fold_right (fun event n => audit_virtual_full_internal_event_work event + n) 0
    (snd (audit_virtual_full_encode cb v)) <= 128.
Proof.
  destruct v as [vertex|[]]; cbn [audit_virtual_full_encode].
  - destruct (audit_virtual_base_encode cb vertex); cbn [snd List.fold_right
      audit_virtual_full_internal_event_work].
    unfold audit_virtual_full_internal_event_work; lia.
  - cbn [snd List.fold_right audit_virtual_full_internal_event_work];
    unfold audit_virtual_full_internal_event_work; lia.
Qed.

(** A lifted source call uses at most two fixed-cost virtual wrapper events. *)
Lemma audit_dom_virtual_source_internal_bound V E B (source : E -> V * list B) edge :
  fold_right (fun event n => audit_virtual_full_internal_event_work event + n) 0
    (snd (audit_virtual_full_source source edge)) <= 128.
Proof.
  destruct edge as [edge|vertex]; cbn [audit_virtual_full_source].
  - destruct (source edge); cbn [snd List.fold_right audit_virtual_full_internal_event_work];
    unfold audit_virtual_full_internal_event_work; lia.
  - cbn [snd List.fold_right audit_virtual_full_internal_event_work];
    unfold audit_virtual_full_internal_event_work; lia.
Qed.

(** Map events expose the exact lifted encoder body and its fixed wrapper cost. *)
Definition audit_dom_virtual_map_internal {V E B A}
    (event : audit_map_event (V + unit) A (audit_virtual_full_call V E B)) : Prop :=
  match event with
  | AuditMapGet _ _ _ _ body _
  | AuditMapSet _ _ _ _ _ body _
  | AuditMapRemove _ _ _ _ body _ =>
      fold_right (fun item n => audit_virtual_full_internal_event_work item + n) 0 body <= 128
  end.

(** Actual lifted map reads, writes and removals retain that bounded encoder body. *)
Lemma audit_dom_virtual_map_internal_bound V E B A (cb : audit_virtual_base_callbacks V E B)
    vertex (input : Map.t (V + unit) A) value :
  Forall audit_dom_virtual_map_internal
    (snd (audit_map_get (audit_virtual_full_encode cb) vertex input)) /\
  Forall audit_dom_virtual_map_internal
    (snd (audit_map_set (audit_virtual_full_encode cb) vertex value input)) /\
  Forall audit_dom_virtual_map_internal
    (snd (audit_map_remove (audit_virtual_full_encode cb) vertex input)).
Proof.
  pose proof (audit_dom_virtual_encode_internal_bound V E B cb vertex) as Hbody.
  unfold audit_map_get, audit_map_set, audit_map_remove.
  destruct (audit_virtual_full_encode cb vertex) as [code body].
  destruct (audit_map_code_get code input) as [found reads].
  destruct (audit_trie_set code (vertex, value) input) as [updated writes].
  destruct (audit_trie_remove code input) as [removed removals].
  cbn [snd] in Hbody |- *.
  split.
  - constructor; [exact Hbody|constructor].
  - split.
    + constructor; [exact Hbody|constructor].
    + constructor; [exact Hbody|constructor].
Qed.

(** A lifted map lookup has bounded wrapper work even for an empty value type. *)
Lemma audit_dom_virtual_map_get_internal V E B A (cb : audit_virtual_base_callbacks V E B)
    vertex (input : Map.t (V + unit) A) :
  Forall audit_dom_virtual_map_internal
    (snd (audit_map_get (audit_virtual_full_encode cb) vertex input)).
Proof.
  pose proof (audit_dom_virtual_encode_internal_bound V E B cb vertex) as Hbody.
  unfold audit_map_get.
  destruct (audit_virtual_full_encode cb vertex) as [code body].
  destruct (audit_map_code_get code input) as [found reads].
  cbn [snd] in Hbody |- *; constructor; [exact Hbody|constructor].
Qed.

(** A semidominator event has bounded fixed-cost virtual callback work. *)
Definition audit_dom_semi_internal {V E B}
    (event : audit_semi_nested_event (V + unit) (audit_virtual_full_call V E B)) : Prop :=
  audit_semi_nested_body_event_work audit_virtual_full_internal_event_work event <= 128.

(** A vertex-map event retains its bounded virtual encoder body. *)
Lemma audit_dom_semi_vertex_map_internal V E B
    (events : list (audit_map_event (V + unit) (V + unit) (audit_virtual_full_call V E B))) :
  Forall audit_dom_virtual_map_internal events ->
  Forall audit_dom_semi_internal (map SemiNestedVertexMap events).
Proof.
  intro Hbody; apply Forall_map; eapply Forall_impl; [|exact Hbody].
  intros item Hitem; destruct item; exact Hitem.
Qed.

(** A rank-map event retains its bounded virtual encoder body. *)
Lemma audit_dom_semi_rank_map_internal V E B
    (events : list (audit_map_event (V + unit) positive (audit_virtual_full_call V E B))) :
  Forall audit_dom_virtual_map_internal events ->
  Forall audit_dom_semi_internal (map SemiNestedRankMap events).
Proof.
  intro Hbody; apply Forall_map; eapply Forall_impl; [|exact Hbody].
  intros item Hitem; destruct item; exact Hitem.
Qed.

(** A rank lookup retains the bounded virtual encoder wrapper. *)
Lemma audit_dom_semi_rank_internal V E B (cb : audit_virtual_base_callbacks V E B)
    (r : dfs_result (V + unit) (E + V)) vertex :
  Forall audit_dom_semi_internal
    (snd (audit_semi_nested_rank (audit_virtual_full_encode cb) r vertex)).
Proof.
  unfold audit_semi_nested_rank.
  pose proof (proj1 (audit_dom_virtual_map_internal_bound V E B positive cb vertex
    (pre_num r) 1%positive)) as Hget.
  destruct (audit_map_get (audit_virtual_full_encode cb) vertex (pre_num r)) as [found events].
  cbn [snd] in Hget |- *; now apply audit_dom_semi_rank_map_internal.
Qed.

(** A label lookup retains the bounded virtual encoder wrapper. *)
Lemma audit_dom_semi_label_internal V E B (cb : audit_virtual_base_callbacks V E B)
    (state : SemiLinks.t (V + unit)) vertex :
  Forall audit_dom_semi_internal
    (snd (audit_semi_nested_label (audit_virtual_full_encode cb) state vertex)).
Proof.
  unfold audit_semi_nested_label.
  pose proof (proj1 (audit_dom_virtual_map_internal_bound V E B (V + unit) cb vertex
    (SemiLinks.labels state) vertex)) as Hget.
  destruct (audit_map_get (audit_virtual_full_encode cb) vertex (SemiLinks.labels state))
    as [found events].
  cbn [snd] in Hget |- *; now apply audit_dom_semi_vertex_map_internal.
Qed.

(** A score lookup preserves both bounded virtual callback bodies. *)
Lemma audit_dom_semi_score_internal V E B (cb : audit_virtual_base_callbacks V E B)
    (r : dfs_result (V + unit) (E + V)) semis vertex :
  Forall audit_dom_semi_internal
    (snd (audit_semi_nested_score (audit_virtual_full_encode cb) r semis vertex)).
Proof.
  unfold audit_semi_nested_score.
  pose proof (proj1 (audit_dom_virtual_map_internal_bound V E B (V + unit) cb vertex
    semis vertex)) as Hget.
  destruct (audit_map_get (audit_virtual_full_encode cb) vertex semis) as [found events].
  cbn [snd] in Hget.
  pose proof (audit_dom_semi_rank_internal V E B cb r
    (match found with Some x => x | None => vertex end)) as Hrank.
  destruct (audit_semi_nested_rank (audit_virtual_full_encode cb) r
    (match found with Some x => x | None => vertex end)) as [score rank_events].
  cbn [snd] in Hrank |- *; apply Forall_app; split;
    [now apply audit_dom_semi_vertex_map_internal|exact Hrank].
Qed.

(** Both shortcut writes preserve the bounded virtual encoder wrapper. *)
Lemma audit_dom_semi_shortcut_internal V E B (cb : audit_virtual_base_callbacks V E B)
    (state : SemiLinks.t (V + unit)) vertex root best :
  Forall audit_dom_semi_internal
    (snd (audit_semi_nested_shortcut_set (audit_virtual_full_encode cb) state vertex root best)).
Proof.
  unfold audit_semi_nested_shortcut_set.
  pose proof (proj1 (proj2 (audit_dom_virtual_map_internal_bound V E B (V + unit) cb
    vertex (SemiLinks.shortcut state) root))) as Hfirst.
  pose proof (proj1 (proj2 (audit_dom_virtual_map_internal_bound V E B (V + unit) cb
    vertex (SemiLinks.labels state) best))) as Hsecond.
  destruct (audit_map_set (audit_virtual_full_encode cb) vertex root (SemiLinks.shortcut state))
    as [shortcuts first].
  destruct (audit_map_set (audit_virtual_full_encode cb) vertex best (SemiLinks.labels state))
    as [labels second].
  cbn [snd] in Hfirst, Hsecond |- *; apply Forall_app; split;
    apply audit_dom_semi_vertex_map_internal; assumption.
Qed.

(** A real compression run retains fixed-cost virtual callback bodies at every step. *)
Lemma audit_dom_semi_compress_internal V E B (cb : audit_virtual_base_callbacks V E B)
    (r : dfs_result (V + unit) (E + V)) semis state vertex result events :
  audit_semi_nested_compress_run (audit_virtual_full_encode cb) r semis state vertex result events
    ->
  Forall audit_dom_semi_internal events.
Proof.
  intro Hrun.
  assert (Hget : forall key input output trace,
    audit_map_get (audit_virtual_full_encode cb) key input = (output, trace) ->
    Forall audit_dom_semi_internal (map SemiNestedVertexMap trace)).
  { intros key input output trace Hcall.
    pose proof (audit_dom_virtual_map_get_internal V E B (V + unit) cb key input) as Hbody.
    rewrite Hcall in Hbody; cbn [snd] in Hbody; now apply audit_dom_semi_vertex_map_internal. }
  assert (Hrank : forall v number trace,
    audit_semi_nested_rank (audit_virtual_full_encode cb) r v = (number, trace) ->
    Forall audit_dom_semi_internal trace).
  { intros v number trace Hcall; pose proof (audit_dom_semi_rank_internal V E B cb r v) as Hbody.
    rewrite Hcall in Hbody; exact Hbody. }
  assert (Hlabel : forall st v result trace,
    audit_semi_nested_label (audit_virtual_full_encode cb) st v = (result, trace) ->
    Forall audit_dom_semi_internal trace).
  { intros st v label trace Hcall; pose proof (audit_dom_semi_label_internal V E B cb st v) as
    Hbody.
    rewrite Hcall in Hbody; exact Hbody. }
  assert (Hscore : forall v score trace,
    audit_semi_nested_score (audit_virtual_full_encode cb) r semis v = (score, trace) ->
    Forall audit_dom_semi_internal trace).
  { intros v score trace Hcall; pose proof (audit_dom_semi_score_internal V E B cb r semis v)
      as Hbody.
    rewrite Hcall in Hbody; exact Hbody. }
  assert (Hset : forall st v root best output trace,
    audit_semi_nested_shortcut_set (audit_virtual_full_encode cb) st v root best = (output, trace)
      ->
    Forall audit_dom_semi_internal trace).
  { intros st v root best output trace Hcall.
    pose proof (audit_dom_semi_shortcut_internal V E B cb st v root best) as Hbody.
    rewrite Hcall in Hbody; exact Hbody. }
  induction Hrun; repeat rewrite Forall_app; repeat split;
    try solve [eauto using Hget, Hrank, Hlabel, Hscore, Hset];
    repeat constructor; unfold audit_dom_semi_internal; cbn [audit_semi_nested_body_event_work];
      lia.
Qed.

(** Each producer event carries at most the fixed virtual source or encoder wrapper cost. *)
Definition audit_dom_producer_internal {V E B}
    (event : audit_semi_producer_nested_event (V + unit) (E + V) (audit_virtual_full_call V E B))
    : Prop :=
  audit_semi_producer_nested_body_event_work audit_virtual_full_internal_event_work event <= 128.

(** An inner compression event keeps the same virtual callback bound. *)
Lemma audit_dom_producer_inner_internal V E B
    (events : list (audit_semi_nested_event (V + unit) (audit_virtual_full_call V E B))) :
  Forall audit_dom_semi_internal events ->
  Forall audit_dom_producer_internal (map (SemiProducerInner (E := E + V)) events).
Proof.
  intro Hbody; apply Forall_map; exact Hbody.
Qed.

(** Tree-map and predecessor-map wrappers retain the bound of the actual map event. *)
Lemma audit_dom_producer_tree_map_internal V E B
    (events : list (audit_map_event (V + unit) (E + V) (audit_virtual_full_call V E B))) :
  Forall audit_dom_virtual_map_internal events ->
  Forall audit_dom_producer_internal (map SemiProducerTreeMap events).
Proof.
  intro Hbody; apply Forall_map; eapply Forall_impl; [|exact Hbody].
  intros item Hitem; destruct item; exact Hitem.
Qed.

Lemma audit_dom_producer_pred_map_internal V E B
    (events : list (audit_map_event (V + unit) (list (E + V)) (audit_virtual_full_call V E B))) :
  Forall audit_dom_virtual_map_internal events ->
  Forall audit_dom_producer_internal (map SemiProducerPredMap events).
Proof.
  intro Hbody; apply Forall_map; eapply Forall_impl; [|exact Hbody].
  intros item Hitem; destruct item; exact Hitem.
Qed.

(** Each link update retains the bounded virtual encoder wrapper. *)
Lemma audit_dom_producer_link_internal V E B (cb : audit_virtual_base_callbacks V E B)
    (state : SemiLinks.t (V + unit)) vertex parent :
  Forall audit_dom_producer_internal
    (snd (audit_semi_producer_link (E := E + V) (audit_virtual_full_encode cb) state vertex
      parent)).
Proof.
  unfold audit_semi_producer_link.
  pose proof (proj1 (proj2 (audit_dom_virtual_map_internal_bound V E B (V + unit) cb
    vertex (SemiLinks.original state) parent))) as Hfirst.
  pose proof (proj1 (proj2 (audit_dom_virtual_map_internal_bound V E B (V + unit) cb
    vertex (SemiLinks.shortcut state) parent))) as Hsecond.
  pose proof (proj1 (proj2 (audit_dom_virtual_map_internal_bound V E B (V + unit) cb
    vertex (SemiLinks.labels state) vertex))) as Hthird.
  destruct (audit_map_set (audit_virtual_full_encode cb) vertex parent (SemiLinks.original state))
    as [original first].
  destruct (audit_map_set (audit_virtual_full_encode cb) vertex parent (SemiLinks.shortcut state))
    as [shortcut second].
  destruct (audit_map_set (audit_virtual_full_encode cb) vertex vertex (SemiLinks.labels state))
    as [labels third].
  cbn [snd] in Hfirst, Hsecond, Hthird |- *.
  rewrite <- map_map.
  apply audit_dom_producer_inner_internal, audit_dom_semi_vertex_map_internal.
  repeat rewrite Forall_app; repeat split; assumption.
Qed.

(** A producer's inner vertex map retains its bounded encoder wrapper. *)
Lemma audit_dom_producer_vertex_map_internal V E B
    (events : list (audit_map_event (V + unit) (V + unit) (audit_virtual_full_call V E B))) :
  Forall audit_dom_virtual_map_internal events ->
  Forall audit_dom_producer_internal
    (map (fun item => SemiProducerInner (E := E + V) (SemiNestedVertexMap item)) events).
Proof.
  intro Hbody; rewrite <- map_map.
  apply audit_dom_producer_inner_internal, audit_dom_semi_vertex_map_internal; exact Hbody.
Qed.

(** A producer's inner rank map retains its bounded encoder wrapper. *)
Lemma audit_dom_producer_rank_map_internal V E B
    (events : list (audit_map_event (V + unit) positive (audit_virtual_full_call V E B))) :
  Forall audit_dom_virtual_map_internal events ->
  Forall audit_dom_producer_internal
    (map (fun item => SemiProducerInner (E := E + V) (SemiNestedRankMap item)) events).
Proof.
  intro Hbody; rewrite <- map_map.
  apply audit_dom_producer_inner_internal, audit_dom_semi_rank_map_internal; exact Hbody.
Qed.

(** A predecessor step retains bounded virtual callback work for its actual operations. *)
Lemma audit_dom_producer_pred_internal V E B (cb : audit_virtual_base_callbacks V E B)
    (source : E -> V * list B) (r : dfs_result (V + unit) (E + V)) semis initial edge result
    events :
  audit_semi_producer_pred_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
    r semis initial edge result events -> Forall audit_dom_producer_internal events.
Proof.
  intro Hrun.
  assert (Hsource : forall e v body, audit_virtual_full_source source e = (v, body) ->
    fold_right (fun item n => audit_virtual_full_internal_event_work item + n) 0 body <= 128).
  { intros e v body Hcall; pose proof (audit_dom_virtual_source_internal_bound V E B source e) as
    Hbody.
    rewrite Hcall in Hbody; exact Hbody. }
  assert (Hrank_get : forall key input result trace,
    audit_map_get (audit_virtual_full_encode cb) key input = (result, trace) ->
    Forall audit_dom_producer_internal
      (map (fun item => SemiProducerInner (E := E + V) (SemiNestedRankMap item)) trace)).
  { intros key input found trace Hcall.
    pose proof (audit_dom_virtual_map_get_internal V E B positive cb key input) as Hbody.
    rewrite Hcall in Hbody; cbn [snd] in Hbody; now apply audit_dom_producer_rank_map_internal. }
  assert (Hvertex_get : forall key input result trace,
    audit_map_get (audit_virtual_full_encode cb) key input = (result, trace) ->
    Forall audit_dom_producer_internal
      (map (fun item => SemiProducerInner (E := E + V) (SemiNestedVertexMap item)) trace)).
  { intros key input found trace Hcall.
    pose proof (audit_dom_virtual_map_get_internal V E B (V + unit) cb key input) as Hbody.
    rewrite Hcall in Hbody; cbn [snd] in Hbody; now apply audit_dom_producer_vertex_map_internal. }
  assert (Hrank : forall v number trace,
    audit_semi_nested_rank (audit_virtual_full_encode cb) r v = (number, trace) ->
    Forall audit_dom_producer_internal (map (SemiProducerInner (E := E + V)) trace)).
  { intros v number trace Hcall; pose proof (audit_dom_semi_rank_internal V E B cb r v) as Hbody.
    rewrite Hcall in Hbody; cbn [snd] in Hbody; now apply audit_dom_producer_inner_internal. }
  assert (Hinner : forall st v after trace,
    audit_semi_nested_compress_run (audit_virtual_full_encode cb) r semis st v after trace ->
    Forall audit_dom_producer_internal (map (SemiProducerInner (E := E + V)) trace)).
  { intros st v after trace Hcall; apply audit_dom_producer_inner_internal;
      eapply audit_dom_semi_compress_internal; exact Hcall. }
  destruct Hrun; repeat rewrite Forall_app; repeat split;
    try solve [eauto using Hrank_get, Hvertex_get, Hrank, Hinner].
  all: repeat match goal with
    | |- Forall _ (_ :: _) => constructor;
        [unfold audit_dom_producer_internal;
          cbn [audit_semi_producer_nested_body_event_work audit_semi_nested_body_event_work];
          eauto using Hsource; lia|]
    end; constructor.
Qed.

(** A predecessor traversal sums the actual fixed-cost callback wrappers. *)
Lemma audit_dom_producer_preds_internal V E B (cb : audit_virtual_base_callbacks V E B)
    (source : E -> V * list B) (r : dfs_result (V + unit) (E + V)) semis edges initial result
    events :
  audit_semi_producer_preds_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
    r semis edges initial result events -> Forall audit_dom_producer_internal events.
Proof.
  intro Hrun; induction Hrun.
  - repeat constructor; unfold audit_dom_producer_internal; cbn
    [audit_semi_producer_nested_body_event_work]; lia.
  - constructor; [unfold audit_dom_producer_internal; cbn
    [audit_semi_producer_nested_body_event_work]; lia|].
    apply Forall_app; split; [eapply audit_dom_producer_pred_internal; eassumption|assumption].
Qed.

(** One producer settlement retains bounded virtual callback wrappers. *)
Lemma audit_dom_producer_settle_internal V E B (cb : audit_virtual_base_callbacks V E B)
    (source : E -> V * list B) (EV : encoding (V + unit))
    (g : Graph.t (V + unit) (E + V)) (p : prepared EV g)
    (r : dfs_result (V + unit) (E + V)) state vertex result events :
  audit_semi_producer_settle_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
    p r state vertex result events -> Forall audit_dom_producer_internal events.
Proof.
  intro Hrun.
  assert (Htree : forall key input output trace,
    audit_map_get (audit_virtual_full_encode cb) key input = (output, trace) ->
    Forall audit_dom_producer_internal (map SemiProducerTreeMap trace)).
  { intros key input output trace Hcall.
    pose proof (audit_dom_virtual_map_get_internal V E B (E + V) cb key input) as Hbody.
    rewrite Hcall in Hbody; cbn [snd] in Hbody; now apply audit_dom_producer_tree_map_internal. }
  assert (Hpred : forall key input output trace,
    audit_map_get (audit_virtual_full_encode cb) key input = (output, trace) ->
    Forall audit_dom_producer_internal (map SemiProducerPredMap trace)).
  { intros key input output trace Hcall.
    pose proof (audit_dom_virtual_map_get_internal V E B (list (E + V)) cb key input) as Hbody.
    rewrite Hcall in Hbody; cbn [snd] in Hbody; now apply audit_dom_producer_pred_map_internal. }
  assert (Hset : forall key value input output trace,
    audit_map_set (audit_virtual_full_encode cb) key value input = (output, trace) ->
    Forall audit_dom_producer_internal
      (map (fun item => SemiProducerInner (E := E + V) (SemiNestedVertexMap item)) trace)).
  { intros key value input output trace Hcall.
    pose proof (proj1 (proj2 (audit_dom_virtual_map_internal_bound V E B (V + unit) cb key input
      value))) as Hbody.
    rewrite Hcall in Hbody; cbn [snd] in Hbody; now apply audit_dom_producer_vertex_map_internal. }
  assert (Hsource : forall edge parent body,
    audit_virtual_full_source source edge = (parent, body) ->
    fold_right (fun item n => audit_virtual_full_internal_event_work item + n) 0 body <= 128).
  { intros edge parent body Hcall.
    pose proof (audit_dom_virtual_source_internal_bound V E B source edge) as Hbody.
    rewrite Hcall in Hbody; exact Hbody. }
  assert (Hlink : forall st v parent output trace,
    audit_semi_producer_link (E := E + V) (audit_virtual_full_encode cb) st v parent =
      (output, trace) -> Forall audit_dom_producer_internal trace).
  { intros st v parent output trace Hcall.
    pose proof (audit_dom_producer_link_internal V E B cb st v parent) as Hbody.
    rewrite Hcall in Hbody; exact Hbody. }
  destruct Hrun; repeat rewrite Forall_app; repeat split;
    try solve [eauto using Htree, Hpred, Hset, Hlink, audit_dom_producer_preds_internal].
  all: repeat match goal with
    | |- Forall _ (_ :: _) => constructor;
        [unfold audit_dom_producer_internal; cbn [audit_semi_producer_nested_body_event_work];
          eauto using Hsource; lia|]
    end; constructor.
Qed.

(** The settlement traversal retains bounded virtual callback wrappers. *)
Lemma audit_dom_producer_settles_internal V E B (cb : audit_virtual_base_callbacks V E B)
    (source : E -> V * list B) (EV : encoding (V + unit))
    (g : Graph.t (V + unit) (E + V)) (p : prepared EV g)
    (r : dfs_result (V + unit) (E + V)) vertices state result events :
  audit_semi_producer_settles_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
    p r vertices state result events -> Forall audit_dom_producer_internal events.
Proof.
  intro Hrun; induction Hrun.
  - constructor; [unfold audit_dom_producer_internal;
      cbn [audit_semi_producer_nested_body_event_work]; lia|constructor].
  - constructor; [unfold audit_dom_producer_internal;
      cbn [audit_semi_producer_nested_body_event_work]; lia|].
    apply Forall_app; split; [eapply audit_dom_producer_settle_internal; eassumption|assumption].
Qed.

(** A real producer run spends at most 128 on each internal virtual callback body. *)
Lemma audit_dom_producer_run_internal V E B (cb : audit_virtual_base_callbacks V E B)
    (source : E -> V * list B) (EV : encoding (V + unit))
    (g : Graph.t (V + unit) (E + V)) (p : prepared EV g)
    (r : dfs_result (V + unit) (E + V)) result events :
  audit_semi_producer_nested_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
    p r result events ->
  audit_semi_producer_nested_body_work audit_virtual_full_internal_event_work events <=
    128 * length events.
Proof.
  intros [inner [Hrun ->]].
  pose proof (audit_dom_producer_settles_internal V E B cb source EV g p r _ _ _ _ Hrun) as Hbody.
  assert (Hsum : audit_semi_producer_nested_body_work audit_virtual_full_internal_event_work inner
    <=
    128 * length inner).
  { clear Hrun; induction Hbody as [|event rest Hitem Htail IH].
    - reflexivity.
    - unfold audit_semi_producer_nested_body_work in *; cbn [fold_right length].
      unfold audit_dom_producer_internal in Hitem; lia. }
  change (audit_semi_producer_nested_body_work audit_virtual_full_internal_event_work inner <=
    128 * S (length inner)).
  lia.
Qed.

(** An LT event has bounded fixed-cost virtual callback work. *)
Definition audit_dom_lt_internal {V E B}
    (event : audit_lt_nested_event (V + unit) (E + V) (audit_virtual_full_call V E B)) : Prop :=
  audit_lt_nested_body_event_work audit_virtual_full_internal_event_work event <= 128.

(** Inner semidominator and producer events keep their original wrapper bound. *)
Lemma audit_dom_lt_semi_internal V E B
    (events : list (audit_semi_nested_event (V + unit) (audit_virtual_full_call V E B))) :
  Forall audit_dom_semi_internal events ->
  Forall audit_dom_lt_internal (map (LtNestedSemi (E := E + V)) events).
Proof.
  intro Hbody; apply Forall_map; exact Hbody.
Qed.

Lemma audit_dom_lt_producer_internal V E B
    (events : list (audit_semi_producer_nested_event (V + unit) (E + V)
      (audit_virtual_full_call V E B))) :
  Forall audit_dom_producer_internal events ->
  Forall audit_dom_lt_internal (map LtNestedProducer events).
Proof.
  intro Hbody; apply Forall_map; exact Hbody.
Qed.

(** Bucket and tree map events retain the bounded virtual encoder body. *)
Lemma audit_dom_lt_bucket_map_internal V E B
    (events : list (audit_map_event (V + unit) (list (V + unit)) (audit_virtual_full_call V E B))) :
  Forall audit_dom_virtual_map_internal events ->
  Forall audit_dom_lt_internal (map (LtNestedBucket (E := E + V)) events).
Proof.
  intro Hbody; apply Forall_map; eapply Forall_impl; [|exact Hbody].
  intros item Hitem; destruct item; exact Hitem.
Qed.

Lemma audit_dom_lt_tree_map_internal V E B
    (events : list (audit_map_event (V + unit) (E + V) (audit_virtual_full_call V E B))) :
  Forall audit_dom_virtual_map_internal events -> Forall audit_dom_lt_internal (map LtNestedTree
    events).
Proof.
  intro Hbody; apply Forall_map; eapply Forall_impl; [|exact Hbody].
  intros item Hitem; destruct item; exact Hitem.
Qed.

Lemma audit_dom_lt_vertex_map_internal V E B
    (events : list (audit_map_event (V + unit) (V + unit) (audit_virtual_full_call V E B))) :
  Forall audit_dom_virtual_map_internal events ->
  Forall audit_dom_lt_internal
    (map (fun item => LtNestedSemi (E := E + V) (SemiNestedVertexMap item)) events).
Proof.
  intro Hbody; rewrite <- map_map.
  apply audit_dom_lt_semi_internal, audit_dom_semi_vertex_map_internal; exact Hbody.
Qed.

(** Bucket construction uses only bounded virtual encoder wrappers. *)
Lemma audit_dom_lt_buckets_internal V E B (cb : audit_virtual_base_callbacks V E B)
    semis vertices buckets :
  Forall audit_dom_lt_internal
    (snd (audit_lt_nested_buckets (E := E + V) (audit_virtual_full_encode cb)
      semis vertices buckets)).
Proof.
  revert buckets; induction vertices as [|v rest IH]; intro buckets.
  - constructor; [unfold audit_dom_lt_internal; cbn [audit_lt_nested_body_event_work];
    lia|constructor].
  - cbn [audit_lt_nested_buckets].
    pose proof (audit_dom_virtual_map_get_internal V E B (V + unit) cb v semis) as Hget.
    destruct (audit_map_get (audit_virtual_full_encode cb) v semis) as [found get_events].
    cbn [snd] in Hget; destruct found as [parent|].
    + pose proof (audit_dom_virtual_map_get_internal V E B (list (V + unit)) cb parent buckets)
        as Hbucket.
      destruct (audit_map_get (audit_virtual_full_encode cb) parent buckets) as [old bucket_events].
      cbn [snd] in Hbucket.
      pose proof (proj1 (proj2 (audit_dom_virtual_map_internal_bound V E B (list (V + unit)) cb
        parent buckets (v :: match old with Some xs => xs | None => [] end)))) as Hset.
      destruct (audit_map_set (audit_virtual_full_encode cb) parent
        (v :: match old with Some xs => xs | None => [] end) buckets) as [next set_events].
      cbn [snd] in Hset; specialize (IH next).
      destruct (audit_lt_nested_buckets (E := E + V) (audit_virtual_full_encode cb) semis rest next)
        as [result later].
      cbn [snd] in IH |- *; constructor;
        [unfold audit_dom_lt_internal; cbn [audit_lt_nested_body_event_work]; lia|].
      apply Forall_app; split; [now apply audit_dom_lt_vertex_map_internal|].
      constructor; [unfold audit_dom_lt_internal; cbn [audit_lt_nested_body_event_work]; lia|].
      repeat rewrite Forall_app; repeat split; try assumption;
        now apply audit_dom_lt_bucket_map_internal.
    + specialize (IH buckets).
      destruct (audit_lt_nested_buckets (E := E + V) (audit_virtual_full_encode cb) semis rest
        buckets) as [result later].
      cbn [snd] in IH |- *; constructor;
        [unfold audit_dom_lt_internal; cbn [audit_lt_nested_body_event_work]; lia|].
      apply Forall_app; split; [now apply audit_dom_lt_vertex_map_internal|].
      constructor; [unfold audit_dom_lt_internal; cbn [audit_lt_nested_body_event_work]; lia|exact
        IH].
Qed.

(** A bucket member retains bounded internal callback bodies. *)
Lemma audit_dom_lt_member_internal V E B (cb : audit_virtual_base_callbacks V E B)
    (r : dfs_result (V + unit) (E + V)) semis s initial vertex result events :
  audit_lt_nested_member_run (audit_virtual_full_encode cb) r semis s initial vertex result events
    ->
  Forall audit_dom_lt_internal events.
Proof.
  intro Hrun.
  assert (Hset : forall key value input output trace,
    audit_map_set (audit_virtual_full_encode cb) key value input = (output, trace) ->
    Forall audit_dom_lt_internal
      (map (fun item => LtNestedSemi (E := E + V) (SemiNestedVertexMap item)) trace)).
  { intros key value input output trace Hcall.
    pose proof (proj1 (proj2 (audit_dom_virtual_map_internal_bound V E B (V + unit) cb key input
      value))) as Hbody.
    rewrite Hcall in Hbody; cbn [snd] in Hbody; now apply audit_dom_lt_vertex_map_internal. }
  assert (Hrank : forall v number trace,
    audit_semi_nested_rank (audit_virtual_full_encode cb) r v = (number, trace) ->
    Forall audit_dom_lt_internal (map (LtNestedSemi (E := E + V)) trace)).
  { intros v number trace Hcall; pose proof (audit_dom_semi_rank_internal V E B cb r v) as Hbody.
    rewrite Hcall in Hbody; cbn [snd] in Hbody; now apply audit_dom_lt_semi_internal. }
  assert (Hscore : forall v score trace,
    audit_semi_nested_score (audit_virtual_full_encode cb) r semis v = (score, trace) ->
    Forall audit_dom_lt_internal (map (LtNestedSemi (E := E + V)) trace)).
  { intros v score trace Hcall; pose proof (audit_dom_semi_score_internal V E B cb r semis v) as
    Hbody.
    rewrite Hcall in Hbody; cbn [snd] in Hbody; now apply audit_dom_lt_semi_internal. }
  assert (Hinner : forall st v after trace,
    audit_semi_nested_compress_run (audit_virtual_full_encode cb) r semis st v after trace ->
    Forall audit_dom_lt_internal (map (LtNestedSemi (E := E + V)) trace)).
  { intros st v after trace Hcall; apply audit_dom_lt_semi_internal;
      eapply audit_dom_semi_compress_internal; exact Hcall. }
  destruct Hrun; repeat rewrite Forall_app; repeat split;
    try solve [eauto using Hset, Hrank, Hscore, Hinner].
  all: repeat match goal with
    | |- Forall _ (_ :: _) => constructor;
        [unfold audit_dom_lt_internal;
          cbn [audit_lt_nested_body_event_work audit_semi_nested_body_event_work]; lia|]
    end; constructor.
Qed.

(** The member traversal retains bounded internal callback bodies. *)
Lemma audit_dom_lt_members_internal V E B (cb : audit_virtual_base_callbacks V E B)
    (r : dfs_result (V + unit) (E + V)) semis s vertices initial result events :
  audit_lt_nested_members_run (audit_virtual_full_encode cb) r semis s vertices initial result
    events -> Forall audit_dom_lt_internal events.
Proof.
  intro Hrun; induction Hrun.
  - constructor; [unfold audit_dom_lt_internal; cbn [audit_lt_nested_body_event_work];
    lia|constructor].
  - constructor; [unfold audit_dom_lt_internal; cbn [audit_lt_nested_body_event_work]; lia|].
    apply Forall_app; split; [eapply audit_dom_lt_member_internal; eassumption|assumption].
Qed.

(** One reverse LT step retains bounded internal callback bodies. *)
Lemma audit_dom_lt_reverse_internal V E B (cb : audit_virtual_base_callbacks V E B)
    (source : E -> V * list B) (r : dfs_result (V + unit) (E + V)) semis buckets initial vertex
    result events :
  audit_lt_nested_reverse_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
    r semis buckets initial vertex result events -> Forall audit_dom_lt_internal events.
Proof.
  intro Hrun.
  assert (Hbucket : forall key input output trace,
    audit_map_get (audit_virtual_full_encode cb) key input = (output, trace) ->
    Forall audit_dom_lt_internal (map (LtNestedBucket (E := E + V)) trace)).
  { intros key input output trace Hcall.
    pose proof (audit_dom_virtual_map_get_internal V E B (list (V + unit)) cb key input) as Hbody.
    rewrite Hcall in Hbody; cbn [snd] in Hbody; now apply audit_dom_lt_bucket_map_internal. }
  assert (Htree : forall key input output trace,
    audit_map_get (audit_virtual_full_encode cb) key input = (output, trace) ->
    Forall audit_dom_lt_internal (map LtNestedTree trace)).
  { intros key input output trace Hcall.
    pose proof (audit_dom_virtual_map_get_internal V E B (E + V) cb key input) as Hbody.
    rewrite Hcall in Hbody; cbn [snd] in Hbody; now apply audit_dom_lt_tree_map_internal. }
  assert (Hsource : forall edge parent body,
    audit_virtual_full_source source edge = (parent, body) ->
    fold_right (fun item n => audit_virtual_full_internal_event_work item + n) 0 body <= 128).
  { intros edge parent body Hcall.
    pose proof (audit_dom_virtual_source_internal_bound V E B source edge) as Hbody.
    rewrite Hcall in Hbody; exact Hbody. }
  assert (Hlink : forall st v parent output trace,
    audit_semi_producer_link (E := E + V) (audit_virtual_full_encode cb) st v parent =
      (output, trace) -> Forall audit_dom_lt_internal (map LtNestedProducer trace)).
  { intros st v parent output trace Hcall.
    pose proof (audit_dom_producer_link_internal V E B cb st v parent) as Hbody.
    rewrite Hcall in Hbody; cbn [snd] in Hbody; now apply audit_dom_lt_producer_internal. }
  destruct Hrun; repeat rewrite Forall_app; repeat split;
    try solve [eauto using Hbucket, Htree, Hlink, audit_dom_lt_members_internal].
  all: repeat match goal with
    | |- Forall _ (_ :: _) => constructor;
        [unfold audit_dom_lt_internal; cbn [audit_lt_nested_body_event_work];
          eauto using Hsource; lia|]
    end; constructor.
Qed.

(** The reverse traversal retains bounded internal callback bodies. *)
Lemma audit_dom_lt_reverse_fold_internal V E B (cb : audit_virtual_base_callbacks V E B)
    (source : E -> V * list B) (r : dfs_result (V + unit) (E + V)) semis buckets vertices initial
    result events :
  audit_lt_nested_reverse_fold_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
    r semis buckets vertices initial result events -> Forall audit_dom_lt_internal events.
Proof.
  intro Hrun; induction Hrun.
  - constructor; [unfold audit_dom_lt_internal; cbn [audit_lt_nested_body_event_work];
    lia|constructor].
  - constructor; [unfold audit_dom_lt_internal; cbn [audit_lt_nested_body_event_work]; lia|].
    apply Forall_app; split; [eapply audit_dom_lt_reverse_internal; eassumption|assumption].
Qed.

(** One correction step preserves the bounded virtual encoder bodies. *)
Lemma audit_dom_lt_correct_internal V E B (cb : audit_virtual_base_callbacks V E B)
    semis provisional corrected vertex :
  Forall audit_dom_lt_internal
    (snd (audit_lt_nested_correct (E := E + V) (audit_virtual_full_encode cb)
      semis provisional corrected vertex)).
Proof.
  assert (Hget : forall key input output trace,
    audit_map_get (audit_virtual_full_encode cb) key input = (output, trace) ->
    Forall audit_dom_lt_internal
      (map (fun item => LtNestedSemi (E := E + V) (SemiNestedVertexMap item)) trace)).
  { intros key input output trace Hcall.
    pose proof (audit_dom_virtual_map_get_internal V E B (V + unit) cb key input) as Hbody.
    rewrite Hcall in Hbody; cbn [snd] in Hbody; now apply audit_dom_lt_vertex_map_internal. }
  assert (Hset : forall key value input output trace,
    audit_map_set (audit_virtual_full_encode cb) key value input = (output, trace) ->
    Forall audit_dom_lt_internal
      (map (fun item => LtNestedSemi (E := E + V) (SemiNestedVertexMap item)) trace)).
  { intros key value input output trace Hcall.
    pose proof (proj1 (proj2 (audit_dom_virtual_map_internal_bound V E B (V + unit) cb key input
      value))) as Hbody.
    rewrite Hcall in Hbody; cbn [snd] in Hbody; now apply audit_dom_lt_vertex_map_internal. }
  assert (Hencode : forall key code body, audit_virtual_full_encode cb key = (code, body) ->
    fold_right (fun item n => audit_virtual_full_internal_event_work item + n) 0 body <= 128).
  { intros key code body Hcall.
    pose proof (audit_dom_virtual_encode_internal_bound V E B cb key) as Hbody.
    rewrite Hcall in Hbody; exact Hbody. }
  unfold audit_lt_nested_correct.
  destruct (audit_map_get (audit_virtual_full_encode cb) vertex provisional)
    as [found first] eqn:Hfirst.
  destruct found as [u|].
  - destruct (audit_virtual_full_encode cb u) as [a a_body] eqn:Ha.
    destruct (audit_map_get (audit_virtual_full_encode cb) vertex semis)
      as [found value_events] eqn:Hvalue.
    set (value := match found with Some x => x | None => vertex end).
    destruct (audit_virtual_full_encode cb value) as [b b_body] eqn:Hb.
    destruct (audit_positive_eqb a b) as [equal equal_events].
    destruct equal.
    + destruct (audit_map_set (audit_virtual_full_encode cb) vertex u corrected)
        as [result set_events] eqn:Hwrite.
      cbn [snd]; repeat rewrite Forall_app; repeat split; try solve [eauto using Hget, Hset].
      all: repeat match goal with
        | |- Forall _ (_ :: _) => constructor;
            [unfold audit_dom_lt_internal; cbn [audit_lt_nested_body_event_work];
              eauto using Hencode; lia|]
        end; constructor.
    + destruct (audit_map_get (audit_virtual_full_encode cb) u corrected)
        as [found_parent parent_events] eqn:Hparent.
      set (parent := match found_parent with Some x => x | None => u end).
      destruct (audit_map_set (audit_virtual_full_encode cb) vertex parent corrected)
        as [result set_events] eqn:Hwrite.
      cbn [snd]; repeat rewrite Forall_app; repeat split; try solve [eauto using Hget, Hset].
      all: repeat match goal with
        | |- Forall _ (_ :: _) => constructor;
            [unfold audit_dom_lt_internal; cbn [audit_lt_nested_body_event_work];
              eauto using Hencode; lia|]
        end; constructor.
  - cbn [snd]; apply Forall_app; split; [eauto using Hget|].
    constructor; [unfold audit_dom_lt_internal; cbn [audit_lt_nested_body_event_work];
      lia|constructor].
Qed.

(** The correction fold preserves bounded internal callback bodies. *)
Lemma audit_dom_lt_correct_fold_internal V E B (cb : audit_virtual_base_callbacks V E B)
    semis provisional vertices corrected :
  Forall audit_dom_lt_internal
    (snd (audit_lt_nested_correct_fold (E := E + V) (audit_virtual_full_encode cb)
      semis provisional vertices corrected)).
Proof.
  revert corrected; induction vertices as [|v rest IH]; intro corrected.
  - constructor; [unfold audit_dom_lt_internal; cbn [audit_lt_nested_body_event_work];
    lia|constructor].
  - cbn [audit_lt_nested_correct_fold].
    pose proof (audit_dom_lt_correct_internal V E B cb semis provisional corrected v) as Hhere.
    destruct (audit_lt_nested_correct (E := E + V) (audit_virtual_full_encode cb)
      semis provisional corrected v) as [middle here].
    cbn [snd] in Hhere; specialize (IH middle).
    destruct (audit_lt_nested_correct_fold (E := E + V) (audit_virtual_full_encode cb)
      semis provisional rest middle) as [result later].
    cbn [snd] in IH |- *; constructor;
      [unfold audit_dom_lt_internal; cbn [audit_lt_nested_body_event_work]; lia|].
    apply Forall_app; split; assumption.
Qed.

(** A real LT run spends at most 128 on each internal virtual callback body. *)
Lemma audit_dom_lt_run_internal V E B (cb : audit_virtual_base_callbacks V E B)
    (source : E -> V * list B) (r : dfs_result (V + unit) (E + V)) semis result events :
  audit_lt_nested_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
    r semis result events ->
  audit_lt_nested_body_work audit_virtual_full_internal_event_work events <= 128 * length events.
Proof.
  unfold audit_lt_nested_run.
  pose proof (audit_dom_lt_buckets_internal V E B cb semis (preorder r) Map.empty) as Hbuckets.
  destruct (audit_lt_nested_buckets (E := E + V) (audit_virtual_full_encode cb)
    semis (preorder r) Map.empty) as [buckets bucket_events].
  cbn [snd] in Hbuckets.
  intros [settled [reverse_events [Hreverse Hcorrection]]].
  pose proof (audit_dom_lt_correct_fold_internal V E B cb semis (LtState.parents settled)
    (preorder r) Map.empty) as Hcorrect.
  destruct (audit_lt_nested_correct_fold (E := E + V) (audit_virtual_full_encode cb)
    semis (LtState.parents settled) (preorder r) Map.empty) as [output correction_events].
  cbn [snd] in Hcorrect; destruct Hcorrection as [_ ->].
  assert (Hbody : Forall audit_dom_lt_internal
    (bucket_events ++ [LtNestedOutput (length (preorder r))] ++ reverse_events ++
      correction_events)).
  { repeat rewrite Forall_app; repeat split; try assumption.
    - constructor; [unfold audit_dom_lt_internal; cbn [audit_lt_nested_body_event_work];
      lia|constructor].
    - eapply audit_dom_lt_reverse_fold_internal; exact Hreverse. }
  clear Hreverse Hbuckets Hcorrect.
  induction Hbody as [|event rest Hitem Htail IH].
  - reflexivity.
  - unfold audit_lt_nested_body_work in *; cbn [fold_right length].
    unfold audit_dom_lt_internal in Hitem; lia.
Qed.

(** Event ceilings turn the two actual wrapper-work sums into input-derived terms. *)
Lemma audit_dom_virtual_reserve_from_limits {V E B} (EV : encoding V) (g : Graph.t V E)
    (cb : audit_virtual_base_callbacks V E B) (source : E -> V * list B)
    (vp : prepared (virtual_encoding EV) (virtual_graph EV g))
    (search : dfs_result (V + unit) (E + V)) semi_state semi_events virtual_parents lt_events :
  audit_virtual_base_callbacks_erase EV g cb ->
  (forall edge, fst (source edge) = Graph.source g edge) ->
  audit_semi_producer_nested_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
    vp search semi_state semi_events ->
  audit_lt_nested_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
    search (SemiState.result semi_state) virtual_parents lt_events ->
  audit_virtual_source_search_budget EV g +
    audit_semi_producer_input_budget (virtual_encoding EV) (virtual_graph EV g) vp search +
    audit_lt_nested_input_budget (virtual_encoding EV) (virtual_graph EV g) search
      (SemiState.result semi_state) + audit_erase_nested_budget EV virtual_parents +
    128 * audit_semi_producer_event_bound vp search +
    128 * audit_lt_nested_input_event_bound search <= audit_virtual_lt_input_budget EV g ->
  audit_virtual_source_search_budget EV g +
    audit_semi_producer_input_budget (virtual_encoding EV) (virtual_graph EV g) vp search +
    audit_lt_nested_input_budget (virtual_encoding EV) (virtual_graph EV g) search
      (SemiState.result semi_state) + audit_erase_nested_budget EV virtual_parents +
    audit_semi_producer_nested_body_work audit_virtual_full_internal_event_work semi_events +
    audit_lt_nested_body_work audit_virtual_full_internal_event_work lt_events <=
      audit_virtual_lt_input_budget EV g.
Proof.
  intros Hcallbacks Hsource Hsemi Hlt Hreserve.
  assert (Hencode : forall v,
    fst (audit_virtual_full_encode cb v) = encode (virtual_encoding EV) v).
  { destruct Hcallbacks as [_ [_ Hbase]].
    intros [v|[]]; cbn [audit_virtual_full_encode virtual_encoding].
    - specialize (Hbase v); destruct (audit_virtual_base_encode cb v);
        cbn [fst] in Hbase |- *; now rewrite Hbase.
    - reflexivity. }
  pose proof (audit_virtual_full_source_correct V E B EV g source Hsource) as Hfull_source.
  pose proof (audit_semi_producer_nested_bound _ _ _ (virtual_encoding EV) (virtual_graph EV g)
    vp search (audit_virtual_full_encode cb) (audit_virtual_full_source source) (fun _ => 0)
    semi_state semi_events Hencode Hfull_source Hsemi) as [Hsemi_count _].
  pose proof (audit_lt_nested_bound _ _ _ (virtual_encoding EV) (virtual_graph EV g)
    search (SemiState.result semi_state) (audit_virtual_full_encode cb)
    (audit_virtual_full_source source) (fun _ => 0) virtual_parents lt_events Hencode Hfull_source
    Hlt) as [Hlt_count _].
  pose proof (audit_dom_producer_run_internal V E B cb source (virtual_encoding EV)
    (virtual_graph EV g) vp search semi_state semi_events Hsemi) as Hsemi_body.
  pose proof (audit_dom_lt_run_internal V E B cb source search (SemiState.result semi_state)
    virtual_parents lt_events Hlt) as Hlt_body.
  clear - Hreserve Hsemi_count Hlt_count Hsemi_body Hlt_body; lia.
Qed.
Lemma audit_dom_flat_map_length {A B} (f : A -> list B) xs :
  length (flat_map f xs) = fold_right (fun x n => length (f x) + n) 0 xs.
Proof.
  induction xs as [|x rest IH]; cbn [flat_map length fold_right]; [reflexivity|].
  rewrite length_app, IH; reflexivity.
Qed.

Lemma audit_dom_virtual_node_count {V E} (EV : encoding V) (g : Graph.t V E) :
  length (Graph.nodes (virtual_graph EV g)) = S (length (Graph.nodes g)).
Proof.
  cbn [virtual_graph Graph.nodes]; rewrite length_app, length_map; cbn; lia.
Qed.

Lemma audit_dom_virtual_edge_count {V E} (EV : encoding V) (g : Graph.t V E) :
  edge_count (virtual_graph EV g) <= edge_count g + length (Graph.entries g).
Proof.
  unfold edge_count; cbn [virtual_graph Graph.nodes Graph.out].
  rewrite fold_right_app; cbn [fold_right]; rewrite length_map.
  assert (Hentries : length (virtual_entries EV g) <= length (Graph.entries g)).
  { unfold virtual_entries; apply audit_virtual_entries_length. }
  generalize (Graph.nodes g); intro nodes; induction nodes as [|node rest IH]; cbn [map fold_right];
    [lia|rewrite length_map; lia].
Qed.

Lemma audit_dom_original_edge_count {V E} (g : Graph.t V E) :
  edge_count g = length (flat_map (Graph.out g) (Graph.nodes g)).
Proof.
  unfold edge_count; symmetry; apply audit_dom_flat_map_length.
Qed.

Lemma audit_dom_virtual_support_width {V E} (EV : encoding V) (g : Graph.t V E) v :
  In v (audit_virtual_lt_input_support g) ->
  Pos.size_nat (encode EV v) <= audit_virtual_lt_input_width EV g.
Proof.
  unfold audit_virtual_lt_input_width; apply (audit_dfs_width_member (fun x => Pos.size_nat (encode
    EV x))).
Qed.

Lemma audit_dom_virtual_node_width {V E} (EV : encoding V) (g : Graph.t V E) v :
  In v (Graph.nodes (virtual_graph EV g)) ->
  Pos.size_nat (encode (virtual_encoding EV) v) <= 2 + audit_virtual_lt_input_width EV g.
Proof.
  intros Hin; destruct v as [v|[]].
  - cbn [virtual_graph Graph.nodes] in Hin.
    apply in_app_iff in Hin; destruct Hin as [Hin|Hin]; [|cbn in Hin; intuition discriminate].
    apply in_map_iff in Hin; destruct Hin as [node [Heq Hnode]]; inversion Heq; subst node.
    assert (Hwidth : Pos.size_nat (encode EV v) <= audit_virtual_lt_input_width EV g).
    { apply audit_dom_virtual_support_width; unfold audit_virtual_lt_input_support.
      apply in_or_app; now left. }
    cbn [virtual_encoding sum_encoding encode Pos.size_nat]; lia.
  - cbn [virtual_encoding sum_encoding unit_encoding encode Pos.size_nat].
    unfold audit_virtual_lt_input_width, audit_virtual_lt_input_support.
    destruct (Graph.nodes g) as [|node nodes]; cbn [map fold_right]; lia.
Qed.

Lemma audit_dom_virtual_target_width {V E} (EV : encoding V) (g : Graph.t V E) v edge :
  In v (Graph.nodes (virtual_graph EV g)) -> In edge (Graph.out (virtual_graph EV g) v) ->
  Pos.size_nat (encode (virtual_encoding EV) (Graph.target (virtual_graph EV g) edge)) <=
    2 + audit_virtual_lt_input_width EV g.
Proof.
  intros Hnode Hedge; destruct v as [v|[]].
  - cbn [virtual_graph Graph.nodes] in Hnode.
    apply in_app_iff in Hnode; destruct Hnode as [Hnode|Hnode];
      [|cbn in Hnode; intuition discriminate].
    apply in_map_iff in Hnode; destruct Hnode as [node [Heq Hnode]]; inversion Heq; subst node.
    cbn [virtual_graph Graph.out] in Hedge; apply in_map_iff in Hedge.
    destruct Hedge as [e [Hedge_eq Hedge]]; subst edge.
    assert (Hwidth : Pos.size_nat (encode EV (Graph.target g e)) <= audit_virtual_lt_input_width EV
      g).
    { apply audit_dom_virtual_support_width; unfold audit_virtual_lt_input_support.
      apply in_or_app; right; apply in_or_app; right; apply in_or_app; right;
      apply in_map; apply in_flat_map; exists v; auto. }
    cbn [virtual_graph Graph.target virtual_encoding sum_encoding encode Pos.size_nat]; lia.
  - cbn [virtual_graph Graph.out] in Hedge; apply in_map_iff in Hedge.
    destruct Hedge as [entry [Heq Hentry]]; subst edge.
    apply (proj1 (proj2 (virtual_entries_exact EV g) entry)) in Hentry.
    assert (Hwidth : Pos.size_nat (encode EV entry) <= audit_virtual_lt_input_width EV g).
    { apply audit_dom_virtual_support_width; unfold audit_virtual_lt_input_support.
      apply in_or_app; right; apply in_or_app; now left. }
    cbn [virtual_graph Graph.target virtual_encoding sum_encoding encode Pos.size_nat]; lia.
Qed.

Lemma audit_dom_virtual_prepare_width {V E} (EV : encoding V) (g : Graph.t V E) :
  audit_graph_prepare_input_width (virtual_encoding EV) (virtual_graph EV g) <=
    2 + audit_virtual_lt_input_width EV g.
Proof.
  set (vg := virtual_graph EV g).
  set (width := 2 + audit_virtual_lt_input_width EV g).
  assert (Hnode : forall v, In v (Graph.nodes vg) ->
    audit_key_bits_weight (encode (virtual_encoding EV) v) <= width).
  { unfold vg, width, audit_key_bits_weight; intros v Hin; now apply audit_dom_virtual_node_width. }
  assert (Hedge : forall v edge, In v (Graph.nodes vg) -> In edge (Graph.out vg v) ->
    audit_key_bits_weight (encode (virtual_encoding EV) (Graph.target vg edge)) <= width).
  { unfold vg, width, audit_key_bits_weight; intros v edge Hv Hedge;
      eapply audit_dom_virtual_target_width; eassumption. }
  unfold audit_graph_prepare_input_width; fold vg.
  remember (Graph.nodes vg) as nodes eqn:Hnodes.
  clear Hnodes.
  revert Hnode Hedge; induction nodes as [|v rest IH]; intros Hnode Hedge; cbn [fold_right]; [lia|].
  apply Nat.max_lub.
  - apply Hnode; now left.
  - apply audit_dom_max_fold_bound.
    + apply IH.
      * intros x Hin; apply Hnode; now right.
      * intros x edge Hin; apply Hedge; now right.
    + intros edge Hin; apply Hedge with (v := v); [now left|exact Hin].
Qed.

Lemma audit_dom_virtual_search_width {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) :
  audit_dfs_full_input_width (virtual_encoding EV) (virtual_graph EV g)
    (virtual_prepared p) [inr tt] <= 2 + audit_virtual_lt_input_width EV g.
Proof.
  eapply Nat.le_trans; [|apply audit_dom_virtual_prepare_width].
  unfold virtual_prepared; apply audit_dom_prepared_dfs_width.
  intros v Hin; cbn [List.In] in Hin; destruct Hin as [Heq|[]]; subst v.
  cbn [virtual_graph Graph.nodes]; apply in_or_app; right; now left.
Qed.

Lemma audit_dom_virtual_sizes {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) :
  let scale := audit_virtual_lt_input_scale EV g in
  length (Graph.nodes (virtual_graph EV g)) <= scale /\
  edge_count (virtual_graph EV g) <= scale /\
  audit_graph_prepare_input_width (virtual_encoding EV) (virtual_graph EV g) <= scale /\
  audit_dfs_full_input_width (virtual_encoding EV) (virtual_graph EV g) (virtual_prepared p)
    [inr tt] <= scale /\
  Pos.to_nat (fuel (virtual_prepared p)) <= 3 * scale.
Proof.
  pose proof (audit_dom_virtual_node_count EV g) as Hnodes.
  pose proof (audit_dom_virtual_edge_count EV g) as Hedges.
  pose proof (audit_dom_original_edge_count g) as Hcount.
  pose proof (audit_dom_virtual_prepare_width EV g) as Hwidth.
  pose proof (audit_dom_virtual_search_width EV g p) as Hdfs.
  assert (Hfuel : Pos.to_nat (fuel (virtual_prepared p)) =
    2 * length (Graph.nodes (virtual_graph EV g)) + edge_count (virtual_graph EV g) + 2).
  { cbn [virtual_prepared prepare fuel]; rewrite SuccNat2Pos.id_succ; lia. }
  unfold audit_virtual_lt_input_scale; cbn zeta.
  rewrite Hcount in Hedges; repeat split; lia.
Qed.

(** * Trie size and encoded output bounds *)

Lemma audit_dom_elements_bits_lower {A} (node : Trie.ne A) :
  forall path depth,
    (forall p, depth + Pos.size_nat p <= Pos.size_nat (path p)) ->
    audit_elements_nodes node + depth <= audit_elements_bits path node.
Proof.
  induction node as [r IHr|value|value r IHr|l IHl|l IHl r IHr|
    l IHl value|l IHl value r IHr]; intros path depth Hpath;
    cbn [audit_elements_bits audit_elements_nodes].
  - specialize (IHr (fun p => path (xI p)) (S depth)).
    assert (Hchild : forall p, S depth + Pos.size_nat p <= Pos.size_nat (path (xI p))).
    { intro p; specialize (Hpath (xI p)); cbn [Pos.size_nat] in Hpath; lia. }
    specialize (IHr Hchild); lia.
  - specialize (Hpath xH); cbn [Pos.size_nat] in Hpath; lia.
  - specialize (IHr (fun p => path (xI p)) (S depth)).
    assert (Hchild : forall p, S depth + Pos.size_nat p <= Pos.size_nat (path (xI p))).
    { intro p; specialize (Hpath (xI p)); cbn [Pos.size_nat] in Hpath; lia. }
    specialize (IHr Hchild); lia.
  - specialize (IHl (fun p => path (xO p)) (S depth)).
    assert (Hchild : forall p, S depth + Pos.size_nat p <= Pos.size_nat (path (xO p))).
    { intro p; specialize (Hpath (xO p)); cbn [Pos.size_nat] in Hpath; lia. }
    specialize (IHl Hchild); lia.
  - specialize (IHl (fun p => path (xO p)) (S depth)).
    specialize (IHr (fun p => path (xI p)) (S depth)).
    assert (Hl : forall p, S depth + Pos.size_nat p <= Pos.size_nat (path (xO p))).
    { intro p; specialize (Hpath (xO p)); cbn [Pos.size_nat] in Hpath; lia. }
    assert (Hr : forall p, S depth + Pos.size_nat p <= Pos.size_nat (path (xI p))).
    { intro p; specialize (Hpath (xI p)); cbn [Pos.size_nat] in Hpath; lia. }
    specialize (IHl Hl); specialize (IHr Hr); lia.
  - specialize (IHl (fun p => path (xO p)) (S depth)).
    assert (Hchild : forall p, S depth + Pos.size_nat p <= Pos.size_nat (path (xO p))).
    { intro p; specialize (Hpath (xO p)); cbn [Pos.size_nat] in Hpath; lia. }
    specialize (IHl Hchild); lia.
  - specialize (IHl (fun p => path (xO p)) (S depth)).
    specialize (IHr (fun p => path (xI p)) (S depth)).
    assert (Hl : forall p, S depth + Pos.size_nat p <= Pos.size_nat (path (xO p))).
    { intro p; specialize (Hpath (xO p)); cbn [Pos.size_nat] in Hpath; lia. }
    assert (Hr : forall p, S depth + Pos.size_nat p <= Pos.size_nat (path (xI p))).
    { intro p; specialize (Hpath (xI p)); cbn [Pos.size_nat] in Hpath; lia. }
    specialize (IHl Hl); specialize (IHr Hr); lia.
Qed.

Lemma audit_dom_nodes_le_output_bits {A} (input : Trie.t A) :
  audit_trie_nodes input <= audit_trie_output_bits input.
Proof.
  destruct input as [|node]; [reflexivity|].
  cbn [audit_trie_nodes audit_trie_output_bits].
  pose proof (audit_dom_elements_bits_lower node (fun p => p) 0) as Hbound.
  specialize (Hbound (fun p => Nat.le_refl _)); lia.
Qed.

Lemma audit_dom_bits_fold_map {A B} (cost : A -> nat) (f : B -> A) items :
  fold_right (fun x n => cost x + n) 0 (map f items) =
    fold_right (fun x n => cost (f x) + n) 0 items.
Proof.
  induction items as [|item rest IH]; cbn [map fold_right]; [reflexivity|].
  now rewrite IH.
Qed.

Lemma audit_dom_fold_plus {A} (cost : A -> nat) xs ys :
  fold_right (fun x n => cost x + n) 0 (xs ++ ys) =
    fold_right (fun x n => cost x + n) 0 xs + fold_right (fun x n => cost x + n) 0 ys.
Proof.
  induction xs as [|x rest IH]; cbn [app fold_right]; lia.
Qed.

Lemma audit_dom_elements_bits_entries {A} (node : Trie.ne A) : forall path,
  audit_elements_bits path node =
    fold_right (fun row n => Pos.size_nat (path (fst row)) + n) 0 (Trie.entries_ne node).
Proof.
  induction node as [r IHr|value|value r IHr|l IHl|l IHl r IHr|
    l IHl value|l IHl value r IHr]; intro path;
    cbn [audit_elements_bits Trie.entries_ne fold_right];
    repeat rewrite audit_dom_fold_plus; repeat rewrite audit_dom_bits_fold_map;
    cbn [Trie.lift fst fold_right]; repeat rewrite audit_dom_bits_fold_map;
    cbn [Trie.lift fst fold_right];
    try (rewrite <- (IHl (fun p => path (xO p))));
    try (rewrite <- (IHr (fun p => path (xI p)))); lia.
Qed.

Lemma audit_dom_trie_bits_elements {A} (input : Trie.t A) :
  audit_trie_output_bits input =
    fold_right (fun row n => Pos.size_nat (fst row) + n) 0 (Trie.elements input).
Proof.
  rewrite Trie.elements_entries. destruct input as [|node];
    cbn [audit_trie_output_bits Trie.entries fold_right].
  - reflexivity.
  - exact (audit_dom_elements_bits_entries node (fun p => p)).
Qed.

Lemma audit_dom_bits_bounded {K V} (E : encoding K) (m : Map.t K V) width :
  Map.wf E m ->
  (forall k v, In (k, v) (Map.elements m) -> Pos.size_nat (encode E k) <= width) ->
  audit_trie_output_bits m <= length (Map.elements m) * width.
Proof.
  intros Hwf Hwidth. rewrite audit_dom_trie_bits_elements.
  unfold Map.elements. rewrite length_map.
  remember (Trie.elements m) as entries eqn:Hentries.
  assert (Hall : forall p k v, In (p, (k, v)) entries -> Pos.size_nat p <= width).
  { intros p k v Hin. subst entries.
    assert (Hget : Trie.get p m = Some (k, v)) by (apply Trie.elements_sound; exact Hin).
    rewrite <- (Hwf p k v Hget). apply (Hwidth k v).
    apply in_map_iff. exists (p, (k, v)). split; [reflexivity|exact Hin]. }
  clear Hwf Hwidth Hentries. induction entries as [|[p [k v]] rest IH];
    cbn [fold_right length]; [lia|].
  assert (Hone : Pos.size_nat p <= width) by (apply (Hall p k v); now left).
  assert (Hrest : forall p k v, In (p, (k, v)) rest -> Pos.size_nat p <= width).
  { intros p' k' v' Hin. apply (Hall p' k' v'). now right. }
  specialize (IH Hrest). cbn [fst]. rewrite Nat.mul_succ_l. lia.
Qed.

(** * DFS numbering and predecessor bounds *)

Definition audit_dom_dfs_number_inv {V E} (EV : encoding V) (st : DfsState.t V E) :=
  dfs_numbering EV (DfsState.pre st) (DfsState.pre_index st) (DfsState.pre_clock st) /\
  forall v, FinSet.mem EV v (DfsState.seen st) = true <-> In v (DfsState.pre st).

Lemma audit_dom_dfs_number_discover {V E} (EV : encoding V) v via (st : DfsState.t V E) :
  audit_dom_dfs_number_inv EV st -> FinSet.mem EV v (DfsState.seen st) = false ->
  audit_dom_dfs_number_inv EV (dfs_discover EV v via st).
Proof.
  intros [Hnum Hseen] Hfresh. split; cbn [dfs_discover DfsState.pre DfsState.pre_index
    DfsState.pre_clock DfsState.seen].
  - constructor; [exact Hnum|]. intro Hin. apply Hseen in Hin. congruence.
  - intro w. rewrite FinSet.mem_add, Hseen. cbn. intuition congruence.
Qed.

Lemma audit_dom_dfs_number_step {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) blocked work :
  audit_dom_dfs_number_inv EV (snd work) -> audit_dom_dfs_number_inv EV (snd (dfs_step p blocked
    work)).
Proof.
  destruct work as [stack st]; destruct stack as [|[v edges] rest]; cbn [dfs_step snd];
    intro Hinv; [exact Hinv|].
  destruct edges as [|edge edges]; cbn [dfs_step snd].
  - exact Hinv.
  - destruct (FinSet.mem EV (Graph.target g edge) blocked ||
      FinSet.mem EV (Graph.target g edge) (DfsState.seen st)) eqn:Hmem; [exact Hinv|].
    apply Bool.orb_false_iff in Hmem as [_ Hfresh]. now apply audit_dom_dfs_number_discover.
Qed.

Lemma audit_dom_dfs_number_run {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) blocked n work :
  audit_dom_dfs_number_inv EV (snd work) -> audit_dom_dfs_number_inv EV (snd (dfs_run p blocked n
    work)).
Proof.
  revert work; induction n as [n IH|n IH|]; intros [stack st] Hinv;
    destruct stack as [|frame rest]; cbn [dfs_run fst snd]; try exact Hinv.
  - apply audit_dom_dfs_number_step. apply IH. apply IH. exact Hinv.
  - apply IH. apply IH. exact Hinv.
  - now apply audit_dom_dfs_number_step.
Qed.

Lemma audit_dom_dfs_number_root {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) blocked st v :
  audit_dom_dfs_number_inv EV st -> audit_dom_dfs_number_inv EV (dfs_root p blocked st v).
Proof.
  intro Hinv. unfold dfs_root.
  destruct (FinSet.mem EV v blocked || FinSet.mem EV v (DfsState.seen st)) eqn:Hmem;
    [exact Hinv|].
  apply Bool.orb_false_iff in Hmem as [_ Hfresh]. apply audit_dom_dfs_number_run.
  cbn [snd]. now apply audit_dom_dfs_number_discover.
Qed.

Lemma audit_dom_dfs_number_roots {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) blocked roots st :
  audit_dom_dfs_number_inv EV st ->
  audit_dom_dfs_number_inv EV (fold_left (dfs_root p blocked) roots st).
Proof.
  revert st; induction roots as [|v rest IH]; intros st Hinv; cbn [fold_left]; [exact Hinv|].
  apply IH, audit_dom_dfs_number_root, Hinv.
Qed.

Lemma audit_dom_dfs_number_wf {V} (EV : encoding V) xs m next :
  dfs_numbering EV xs m next -> Map.wf EV m.
Proof.
  intro Hnum. induction Hnum; [apply Map.wf_empty|now apply Map.wf_set].
Qed.

Lemma audit_dom_dfs_initial_inv {V E} (EV : encoding V) :
  audit_dom_dfs_number_inv EV (@dfs_initial V E).
Proof.
  split; cbn [dfs_initial DfsState.pre DfsState.pre_index DfsState.pre_clock DfsState.seen].
  - constructor.
  - intro v. rewrite FinSet.mem_empty. cbn. split; [discriminate|contradiction].
Qed.

Lemma audit_dom_dfs_rank_bound {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) blocked roots :
  audit_semi_producer_input_rank (dfs p blocked roots) <=
    S (length (preorder (dfs p blocked roots))).
Proof.
  pose proof (audit_dom_dfs_number_roots EV g p blocked roots dfs_initial
    (audit_dom_dfs_initial_inv EV)) as [Hnum _].
  set (st := fold_left (dfs_root p blocked) roots dfs_initial) in *.
  pose proof (audit_dom_dfs_number_wf EV _ _ _ Hnum) as Hwf.
  assert (Hrow : forall v n, In (v, n) (Map.elements (DfsState.pre_index st)) ->
    Pos.to_nat n <= S (length (DfsState.pre st))).
  { intros v n Hin. apply (Map.elements_sound EV) in Hin; [|exact Hwf].
    pose proof (dfs_numbering_bound EV _ _ _ Hnum v n Hin) as Hlt.
    apply Pos2Nat.inj_lt in Hlt. rewrite (dfs_numbering_size EV _ _ _ Hnum) in Hlt. lia. }
  unfold dfs. fold st. cbn [pre_num preorder]. rewrite <- rev_alt, length_rev.
  unfold audit_semi_producer_input_rank. cbn [pre_num].
  remember (Map.elements (DfsState.pre_index st)) as rows eqn:Hrows.
  assert (Hall : forall v n, In (v, n) rows -> Pos.to_nat n <= S (length (DfsState.pre st))).
  { subst rows; exact Hrow. }
  clear Hrows Hrow Hwf Hnum. induction rows as [|[v n] rest IH]; cbn [map fold_right]; [lia|].
  apply Nat.max_lub.
  - apply (Hall v n); now left.
  - apply IH. intros v' n' Hin. apply (Hall v' n'); now right.
Qed.

Lemma audit_dom_dfs_predecessor_bound {V E} (EV : encoding V) (g : Graph.t V E) r :
  audit_semi_producer_input_edges (prepare EV g) r <=
    length (preorder r) * edge_count g.
Proof.
  unfold audit_semi_producer_input_edges.
  assert (Hpred : forall v, length (pred_edges (prepare EV g) v) <= edge_count g).
  { intro v. rewrite prepare_pred, audit_dom_original_edge_count. apply filter_length_le. }
  induction (preorder r) as [|v rest IH]; cbn [fold_right length]; [lia|].
  rewrite Nat.mul_succ_l. specialize (Hpred v). lia.
Qed.

(** * Virtual search event bounds *)

Lemma audit_dom_virtual_search_counts {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) :
  let scale := audit_virtual_lt_input_scale EV g in
  length (preorder (virtual_dfs p)) <= 1 + 3 * scale /\
  audit_semi_producer_input_rank (virtual_dfs p) <= 2 + 3 * scale /\
  audit_semi_producer_input_edges (virtual_prepared p) (virtual_dfs p) <=
    (1 + 3 * scale) * scale.
Proof.
  pose proof (audit_dom_virtual_sizes EV g p) as [_ [Hedges [_ [_ Hfuel]]]].
  pose proof (audit_dom_live_length (virtual_encoding EV) (virtual_graph EV g)
    (virtual_prepared p)) as Hlive.
  change (length (preorder (virtual_dfs p)) <= 1 * S (Pos.to_nat (fuel (virtual_prepared p))))
    in Hlive.
  pose proof (audit_dom_dfs_rank_bound (virtual_encoding EV) (virtual_graph EV g)
    (virtual_prepared p) FinSet.empty [inr tt]) as Hrank.
  change (audit_semi_producer_input_rank (virtual_dfs p) <=
    S (length (preorder (virtual_dfs p)))) in Hrank.
  pose proof (audit_dom_dfs_predecessor_bound (virtual_encoding EV) (virtual_graph EV g)
    (virtual_dfs p)) as Hpred.
  change (audit_semi_producer_input_edges (virtual_prepared p) (virtual_dfs p) <=
    length (preorder (virtual_dfs p)) * edge_count (virtual_graph EV g)) in Hpred.
  cbn zeta in *. repeat split; try lia.
  eapply Nat.le_trans; [exact Hpred|]. apply Nat.mul_le_mono; lia.
Qed.

Lemma audit_dom_virtual_event_counts {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) :
  let scale := audit_virtual_lt_input_scale EV g in
  audit_semi_producer_event_bound (virtual_prepared p) (virtual_dfs p) <=
    100 * (2 + 3 * scale) * (1 + (1 + 3 * scale) * scale) * (3 + 3 * scale) /\
  audit_lt_nested_input_event_bound (virtual_dfs p) <=
    200 * (2 + 3 * scale) * (2 + 3 * scale) * (3 + 3 * scale).
Proof.
  pose proof (audit_dom_virtual_search_counts EV g p) as [Hlive [Hrank Hpred]].
  cbn zeta in *. split.
  - unfold audit_semi_producer_event_bound.
    repeat apply Nat.mul_le_mono; lia.
  - unfold audit_lt_nested_input_event_bound.
    repeat apply Nat.mul_le_mono; lia.
Qed.
Lemma audit_dom_dfs_numbered_vertex {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) blocked roots v n :
  In (v, n) (Map.elements (pre_num (dfs p blocked roots))) ->
  In v (preorder (dfs p blocked roots)) /\
  Pos.to_nat n <= S (length (preorder (dfs p blocked roots))).
Proof.
  pose proof (audit_dom_dfs_number_roots EV g p blocked roots dfs_initial
    (audit_dom_dfs_initial_inv EV)) as [Hnum _].
  set (st := fold_left (dfs_root p blocked) roots dfs_initial) in *.
  pose proof (audit_dom_dfs_number_wf EV _ _ _ Hnum) as Hwf.
  unfold dfs. fold st. cbn [pre_num preorder]. rewrite <- rev_alt, length_rev.
  intro Hin. apply (Map.elements_sound EV) in Hin; [|exact Hwf].
  split.
  - rewrite <- in_rev. apply (proj1 (dfs_numbering_domain EV _ _ _ Hnum v)). eauto.
  - pose proof (dfs_numbering_bound EV _ _ _ Hnum v n Hin) as Hlt.
    apply Pos2Nat.inj_lt in Hlt. rewrite (dfs_numbering_size EV _ _ _ Hnum) in Hlt. lia.
Qed.

(** * Parent map size and erasure bounds *)

Lemma audit_dom_lt_fold_unwritten {V} (EV : encoding V) semis provisional order m k :
  ~ In k order ->
  Map.get EV k (fold_left (lt_correct_step EV semis provisional) order m) = Map.get EV k m.
Proof.
  revert m; induction order as [|v rest IH]; intros m Hnot; [reflexivity|].
  cbn [fold_left]. rewrite IH by (intro Hin; apply Hnot; now right).
  unfold lt_correct_step. destruct (Map.get EV v provisional); [|reflexivity].
  rewrite Map.get_set_other; [reflexivity|]. intro Heq; subst k. apply Hnot; now left.
Qed.

Lemma audit_dom_lt_parent_key {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) semis k v :
  In (k, v) (Map.elements (lt_compute EV g r semis)) -> In k (preorder r).
Proof.
  intro Hin. pose proof (lt_compute_wf EV g r semis) as Hwf.
  apply (Map.elements_sound EV) in Hin; [|exact Hwf].
  destruct (in_dec (dfs_eq_dec EV) k (preorder r)) as [Hyes|Hno]; [exact Hyes|].
  unfold lt_compute in Hin. rewrite audit_dom_lt_fold_unwritten, Map.get_empty in Hin;
    [discriminate|exact Hno].
Qed.

Lemma audit_dom_lt_parent_count {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) semis :
  length (Map.elements (lt_compute EV g r semis)) <= length (preorder r).
Proof.
  pose proof (Map.elements_nodup EV (lt_compute EV g r semis)
    (lt_compute_wf EV g r semis)) as Hnodup.
  assert (Hin : incl (map fst (Map.elements (lt_compute EV g r semis))) (preorder r)).
  { intros k Hkey. apply in_map_iff in Hkey as [[key value] [Heq Hrow]].
    cbn in Heq; subst key. eapply audit_dom_lt_parent_key; exact Hrow. }
  pose proof (NoDup_incl_length Hnodup Hin) as Hlen. now rewrite length_map in Hlen.
Qed.

Lemma audit_dom_virtual_parent_trie_bound {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) semis :
  let scale := audit_virtual_lt_input_scale EV g in
  let parents := lt_compute (virtual_encoding EV) (virtual_graph EV g) (virtual_dfs p) semis in
  audit_trie_nodes parents <= (1 + 3 * scale) * scale /\
  audit_trie_output_bits parents <= (1 + 3 * scale) * scale.
Proof.
  pose proof (audit_dom_virtual_sizes EV g p) as [_ [_ [_ [Hdfs Hfuel]]]].
  pose proof (audit_dom_live_length (virtual_encoding EV) (virtual_graph EV g)
    (virtual_prepared p)) as Hlive.
  change (length (preorder (virtual_dfs p)) <= 1 * S (Pos.to_nat (fuel (virtual_prepared p))))
    in Hlive.
  set (parents := lt_compute (virtual_encoding EV) (virtual_graph EV g) (virtual_dfs p) semis).
  pose proof (audit_dom_lt_parent_count (virtual_encoding EV) (virtual_graph EV g) (virtual_dfs p)
    semis)
    as Hcount. fold parents in Hcount.
  assert (Hwidth : forall k v, In (k, v) (Map.elements parents) ->
    Pos.size_nat (encode (virtual_encoding EV) k) <= audit_virtual_lt_input_scale EV g).
  { intros k v Hrow.
    assert (Hin : In k (preorder (virtual_dfs p))).
    { eapply audit_dom_lt_parent_key; exact Hrow. }
    pose proof (audit_dom_live_width (virtual_encoding EV) (virtual_graph EV g)
      (virtual_prepared p) k) as Hkey.
    change (In k (preorder (virtual_dfs p)) ->
      Pos.size_nat (encode (virtual_encoding EV) k) <=
        audit_dfs_full_input_width (virtual_encoding EV) (virtual_graph EV g)
          (virtual_prepared p) [inr tt]) in Hkey.
    specialize (Hkey Hin). cbn zeta in Hdfs. lia. }
  pose proof (audit_dom_bits_bounded (virtual_encoding EV) parents
    (audit_virtual_lt_input_scale EV g) (lt_compute_wf (virtual_encoding EV)
      (virtual_graph EV g) (virtual_dfs p) semis) Hwidth) as Hbits.
  pose proof (audit_dom_nodes_le_output_bits parents) as Hnodes.
  cbn zeta in *. split; eapply Nat.le_trans; [exact Hnodes| |exact Hbits|].
  - eapply Nat.le_trans; [exact Hbits|]. apply Nat.mul_le_mono_r. lia.
  - apply Nat.mul_le_mono_r. lia.
Qed.

Lemma audit_dom_virtual_parent_erase_width {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) semis :
  audit_erase_nested_width EV
    (lt_compute (virtual_encoding EV) (virtual_graph EV g) (virtual_dfs p) semis) <=
      audit_virtual_lt_input_scale EV g.
Proof.
  pose proof (audit_dom_virtual_sizes EV g p) as [_ [_ [_ [Hdfs _]]]].
  set (parents := lt_compute (virtual_encoding EV) (virtual_graph EV g) (virtual_dfs p) semis).
  assert (Hwidth : forall k v, In (k, v) (Map.elements parents) ->
    Pos.size_nat (encode (virtual_encoding EV) k) <= audit_virtual_lt_input_scale EV g).
  { intros k v Hrow.
    assert (Hin : In k (preorder (virtual_dfs p))).
    { eapply audit_dom_lt_parent_key; exact Hrow. }
    pose proof (audit_dom_live_width (virtual_encoding EV) (virtual_graph EV g)
      (virtual_prepared p) k) as Hkey.
    change (In k (preorder (virtual_dfs p)) ->
      Pos.size_nat (encode (virtual_encoding EV) k) <=
        audit_dfs_full_input_width (virtual_encoding EV) (virtual_graph EV g)
          (virtual_prepared p) [inr tt]) in Hkey.
    specialize (Hkey Hin). cbn zeta in Hdfs. lia. }
  change (audit_erase_nested_width EV parents <= audit_virtual_lt_input_scale EV g).
  unfold audit_erase_nested_width.
  remember (Map.elements parents) as rows eqn:Hrows.
  assert (Hall : forall k v, In (k, v) rows ->
    Pos.size_nat (encode (virtual_encoding EV) k) <= audit_virtual_lt_input_scale EV g).
  { subst rows; exact Hwidth. }
  clear Hrows Hwidth Hdfs. induction rows as [|[[k|[]] value] rest IH]; cbn [fold_right fst];
    [lia| |].
  - apply Nat.max_lub.
    + specialize (Hall (inl k) value (or_introl eq_refl)).
      cbn [virtual_encoding sum_encoding encode Pos.size_nat] in Hall. lia.
    + apply IH. intros key val Hin. apply (Hall key val). now right.
  - apply IH. intros key val Hin. apply (Hall key val). now right.
Qed.

Lemma audit_dom_virtual_parent_erase_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) semis :
  let scale := audit_virtual_lt_input_scale EV g in
  let bound := (1 + 3 * scale) * scale in
  let parents := lt_compute (virtual_encoding EV) (virtual_graph EV g) (virtual_dfs p) semis in
  audit_erase_nested_budget EV parents <=
    1024 * S bound * S bound + 128 * bound + 128 * S bound * S scale.
Proof.
  pose proof (audit_dom_virtual_parent_trie_bound EV g p semis) as [Hnodes Hbits].
  pose proof (audit_dom_virtual_parent_erase_width EV g p semis) as Hwidth.
  cbn zeta in *; unfold audit_erase_nested_budget.
  apply Nat.add_le_mono.
  - apply Nat.add_le_mono.
    + apply Nat.mul_le_mono; [apply Nat.mul_le_mono_l|]; lia.
    + apply Nat.mul_le_mono_l. exact Hbits.
  - apply Nat.mul_le_mono.
    + apply Nat.mul_le_mono_l. lia.
    + lia.
Qed.

(** * Prepared predecessor provenance *)

Lemma audit_dom_in_index_flat {V E} (EV : encoding V) (g : Graph.t V E) nodes m :
  fold_right (fun v acc => fold_right (index_edge EV g) acc (Graph.out g v)) m nodes =
    fold_right (index_edge EV g) m (flat_map (Graph.out g) nodes).
Proof.
  induction nodes as [|v rest IH]; cbn [flat_map fold_right]; [reflexivity|].
  rewrite fold_right_app, IH. reflexivity.
Qed.

Lemma audit_dom_in_index_invariant {V E} (EV : encoding V) (g : Graph.t V E) edges :
  forall m, Map.wf EV m -> (forall v, Map.get EV v m <> Some []) ->
  let result := fold_right (index_edge EV g) m edges in
  Map.wf EV result /\ (forall v, Map.get EV v result <> Some []).
Proof.
  induction edges as [|edge rest IH]; intros m Hwf Hnon; cbn [fold_right].
  - split; assumption.
  - destruct (IH m Hwf Hnon) as [Hwf' Hnon'].
    split.
    + unfold index_edge. now apply Map.wf_set.
    + intro v. unfold index_edge.
      destruct (dfs_eq_dec EV v (Graph.target g edge)) as [Heq|Hne].
      * subst v. rewrite Map.get_set_same. discriminate.
      * rewrite Map.get_set_other by exact Hne. apply Hnon'.
Qed.

Lemma audit_dom_in_index_row {V E} (EV : encoding V) (g : Graph.t V E) key row :
  In (key, row) (Map.elements (in_index (prepare EV g))) ->
  exists edge, In edge (flat_map (Graph.out g) (Graph.nodes g)) /\
    Graph.target g edge = key /\ incl row (flat_map (Graph.out g) (Graph.nodes g)).
Proof.
  cbn [prepare in_index]. rewrite audit_dom_in_index_flat.
  set (edges := flat_map (Graph.out g) (Graph.nodes g)).
  destruct (audit_dom_in_index_invariant EV g edges Map.empty (Map.wf_empty EV)
    (fun v => ltac:(rewrite Map.get_empty; discriminate))) as [Hwf Hnon].
  intro Hin. apply (Map.elements_sound EV) in Hin; [|exact Hwf].
  assert (Hrow : row <> []) by (intro Heq; subst row; apply (Hnon key); exact Hin).
  assert (Hindex : index_edges EV (fold_right (index_edge EV g) Map.empty edges) key = row).
  { unfold index_edges. now rewrite Hin. }
  rewrite index_edge_fold in Hindex. unfold index_edges in Hindex.
  rewrite Map.get_empty, app_nil_r in Hindex.
  assert (Hfirst : exists edge, In edge row).
  { destruct row as [|edge rest]; [contradiction|]. exists edge; now left. }
  destruct Hfirst as [edge Hedge]. rewrite <- Hindex in Hedge. apply filter_In in Hedge as [HinE
    Hkey].
  exists edge. split; [exact HinE|]. split.
  - apply Pos.eqb_eq in Hkey. now apply (encode_injective EV) in Hkey.
  - intros e He. rewrite <- Hindex in He. now apply filter_In in He as [He _].
Qed.

Lemma audit_dom_virtual_source_width {V E} (EV : encoding V) (g : Graph.t V E) v edge :
  In v (Graph.nodes (virtual_graph EV g)) -> In edge (Graph.out (virtual_graph EV g) v) ->
  Pos.size_nat (encode (virtual_encoding EV) (Graph.source (virtual_graph EV g) edge)) <=
    2 + audit_virtual_lt_input_width EV g.
Proof.
  intros Hnode Hedge; destruct v as [v|[]].
  - cbn [virtual_graph Graph.nodes] in Hnode.
    apply in_app_iff in Hnode; destruct Hnode as [Hnode|Hnode];
      [|cbn in Hnode; intuition discriminate].
    apply in_map_iff in Hnode; destruct Hnode as [node [Heq Hnode]]; inversion Heq; subst node.
    cbn [virtual_graph Graph.out] in Hedge; apply in_map_iff in Hedge.
    destruct Hedge as [e [Hedge_eq Hedge]]; subst edge.
    assert (Hwidth : Pos.size_nat (encode EV (Graph.source g e)) <= audit_virtual_lt_input_width EV
      g).
    { apply audit_dom_virtual_support_width; unfold audit_virtual_lt_input_support.
      apply in_or_app; right; apply in_or_app; right; apply in_or_app; left;
      apply in_map; apply in_flat_map; exists v; auto. }
    cbn [virtual_graph Graph.source virtual_encoding sum_encoding encode Pos.size_nat]; lia.
  - cbn [virtual_graph Graph.out] in Hedge; apply in_map_iff in Hedge.
    destruct Hedge as [entry [Heq Hentry]]; subst edge.
    cbn [virtual_graph Graph.source virtual_encoding sum_encoding unit_encoding encode
      Pos.size_nat]. lia.
Qed.

Lemma audit_dom_virtual_in_index_width {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) key row :
  In (key, row) (Map.elements (in_index (virtual_prepared p))) ->
  Pos.size_nat (encode (virtual_encoding EV) key) <= audit_virtual_lt_input_scale EV g /\
  (forall edge, In edge row ->
    Pos.size_nat (encode (virtual_encoding EV) (Graph.source (virtual_graph EV g) edge)) <=
      audit_virtual_lt_input_scale EV g).
Proof.
  intro Hrow. change (In (key, row) (Map.elements (in_index (prepare (virtual_encoding EV)
    (virtual_graph EV g))))) in Hrow.
  destruct (audit_dom_in_index_row (virtual_encoding EV) (virtual_graph EV g) key row Hrow)
    as [edge [Hedge [Htarget Hrow_edges]]].
  assert (Hscale : 2 + audit_virtual_lt_input_width EV g <= audit_virtual_lt_input_scale EV g).
  { unfold audit_virtual_lt_input_scale; lia. }
  split.
  - apply in_flat_map in Hedge as [v [Hv Hedge]]. rewrite <- Htarget.
    pose proof (audit_dom_virtual_target_width EV g v edge Hv Hedge). lia.
  - intros e Hin. apply Hrow_edges, in_flat_map in Hin as [v [Hv He]].
    pose proof (audit_dom_virtual_source_width EV g v e Hv He). lia.
Qed.

(** The captured search supplies the event and parent-erasure bounds of its source run. *)
Lemma audit_dom_captured_virtual_reserves {V E B} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (cb : audit_virtual_base_callbacks V E B) vp search prep_events dfs_events
    semis :
  audit_virtual_base_callbacks_erase EV g cb ->
  audit_virtual_source_search EV g cb = (vp, (search, (prep_events, dfs_events))) ->
  let scale := audit_virtual_lt_input_scale EV g in
  let bound := (1 + 3 * scale) * scale in
  audit_semi_producer_event_bound vp search <=
    100 * (2 + 3 * scale) * (1 + (1 + 3 * scale) * scale) * (3 + 3 * scale) /\
  audit_lt_nested_input_event_bound search <=
    200 * (2 + 3 * scale) * (2 + 3 * scale) * (3 + 3 * scale) /\
  audit_erase_nested_budget EV (lt_compute (virtual_encoding EV) (virtual_graph EV g) search semis)
    <=
    1024 * S bound * S bound + 128 * bound + 128 * S bound * S scale.
Proof.
  intros Hcallbacks Hsearch.
  pose proof (audit_virtual_source_search_holds V E B EV g p cb (fun _ => 0) Hcallbacks) as Herase.
  rewrite Hsearch in Herase. cbv beta iota zeta in Herase.
  destruct Herase as [Hprep [Hdfs _]]. subst vp search.
  pose proof (audit_dom_virtual_event_counts EV g p) as [Hsemi Hlt].
  pose proof (audit_dom_virtual_parent_erase_budget EV g p semis) as Herasure.
  cbn zeta in *. repeat split; assumption.
Qed.

(** * Operational support of DFS tree edges *)

(** A parent map records only discovered keys and edges supplied by its prepared index. *)
Definition audit_dom_dfs_tree_inv {V E} (EV : encoding V) (edges : list E)
    (st : DfsState.t V E) : Prop :=
  Map.wf EV (DfsState.parent st) /\
  forall key edge, Map.get EV key (DfsState.parent st) = Some edge ->
    In key (DfsState.pre st) /\ In edge edges.

(** Discovering a vertex preserves existing provenance and records only its supplied edge. *)
Lemma audit_dom_dfs_tree_discover {V E} (EV : encoding V) edges v via
    (st : DfsState.t V E) :
  audit_dom_dfs_tree_inv EV edges st ->
  (forall edge, via = Some edge -> In edge edges) ->
  audit_dom_dfs_tree_inv EV edges (dfs_discover EV v via st).
Proof.
  intros [Hwf Hrows] Hvia; destruct via as [edge|];
    unfold audit_dom_dfs_tree_inv;
    cbn [dfs_discover DfsState.parent DfsState.pre].
  - split; [now apply Map.wf_set|].
    intros key found Hget; destruct (dfs_eq_dec EV key v) as [Heq|Hne].
    + subst key; rewrite Map.get_set_same in Hget; inversion Hget; subst found.
      split; [now left|apply Hvia; reflexivity].
    + rewrite Map.get_set_other in Hget by exact Hne.
      destruct (Hrows key found Hget) as [Hkey Hedge]; split; [now right|exact Hedge].
  - split; [exact Hwf|].
    intros key found Hget; destruct (Hrows key found Hget) as [Hkey Hedge].
    split; [now right|exact Hedge].
Qed.

(** One DFS step retains indexed stack edges and tree provenance. *)
Lemma audit_dom_dfs_tree_step {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked vertices work :
  let edges := flat_map snd (Map.elements (out_index p)) in
  (forall edge, In edge edges -> In (Graph.target g edge) vertices) ->
  audit_dfs_stack_keys vertices edges (fst work) ->
  audit_dom_dfs_tree_inv EV edges (snd work) ->
  audit_dfs_stack_keys vertices edges (fst (dfs_step p blocked work)) /\
  audit_dom_dfs_tree_inv EV edges (snd (dfs_step p blocked work)).
Proof.
  intros edges Hall Hstack Htree.
  pose proof (audit_dfs_step_keys p blocked vertices work Hall Hstack) as [_ Hnext].
  rewrite (audit_dfs_step_erases p blocked work) in Hnext.
  split; [exact Hnext|].
  destruct work as [stack st], stack as [|[v outgoing] rest]; [exact Htree|].
  inversion Hstack as [|frame tail Hframe Hrest]; subst frame tail.
  destruct Hframe as [_ Hedge]; destruct outgoing as [|edge outgoing].
  - exact Htree.
  - cbn [dfs_step snd].
    destruct (FinSet.mem EV (Graph.target g edge) blocked ||
      FinSet.mem EV (Graph.target g edge) (DfsState.seen st)); [exact Htree|].
    apply audit_dom_dfs_tree_discover; [exact Htree|].
    intros found Heq; inversion Heq; subst found; apply Hedge; now left.
Qed.

(** Binary DFS iteration preserves tree provenance at every fuel value. *)
Lemma audit_dom_dfs_tree_run {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked vertices n work :
  let edges := flat_map snd (Map.elements (out_index p)) in
  (forall edge, In edge edges -> In (Graph.target g edge) vertices) ->
  audit_dfs_stack_keys vertices edges (fst work) ->
  audit_dom_dfs_tree_inv EV edges (snd work) ->
  audit_dfs_stack_keys vertices edges (fst (dfs_run p blocked n work)) /\
  audit_dom_dfs_tree_inv EV edges (snd (dfs_run p blocked n work)).
Proof.
  intros edges Hall Hstack Htree; subst edges.
  rewrite (dfs_run_agrees EV g p blocked n work).
  induction n using Pos.peano_ind.
  - now apply audit_dom_dfs_tree_step.
  - rewrite Pos.iter_succ.
    apply audit_dom_dfs_tree_step; [exact Hall|exact (proj1 IHn)|exact (proj2 IHn)].
Qed.

(** Starting or skipping a root preserves tree provenance. *)
Lemma audit_dom_dfs_tree_root {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked vertices st root :
  (forall edge, In edge (flat_map snd (Map.elements (out_index p))) ->
    In (Graph.target g edge) vertices) ->
  In root vertices ->
  audit_dom_dfs_tree_inv EV (flat_map snd (Map.elements (out_index p))) st ->
  audit_dom_dfs_tree_inv EV (flat_map snd (Map.elements (out_index p)))
    (dfs_root p blocked st root).
Proof.
  intros Hall Hroot Htree; unfold dfs_root.
  destruct (FinSet.mem EV root blocked || FinSet.mem EV root (DfsState.seen st));
    [exact Htree|].
  assert (Hstack : audit_dfs_stack_keys vertices
    (flat_map snd (Map.elements (out_index p))) [(root, succ_edges p root)]).
  { constructor; [|constructor]; split; [exact Hroot|].
    unfold succ_edges, index_edges.
    destruct (Map.get EV root (out_index p)) as [row|] eqn:Hget.
    - now apply (audit_dfs_outgoing_edges p root row Hget).
    - intros edge Hfalse; contradiction. }
  assert (Hinitial : audit_dom_dfs_tree_inv EV
    (flat_map snd (Map.elements (out_index p))) (dfs_discover EV root None st)).
  { apply audit_dom_dfs_tree_discover; [exact Htree|].
    intros edge Hfalse; discriminate. }
  exact (proj2 (audit_dom_dfs_tree_run p blocked vertices (fuel p)
    ([(root, succ_edges p root)], dfs_discover EV root None st) Hall Hstack Hinitial)).
Qed.

(** Every stored DFS tree edge has a discovered key and an indexed-edge origin. *)
Lemma audit_dom_dfs_tree_row {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) blocked roots key edge :
  In (key, edge) (Map.elements (tree_edge (dfs p blocked roots))) ->
  In key (preorder (dfs p blocked roots)) /\
  In edge (flat_map snd (Map.elements (out_index p))).
Proof.
  set (edges := flat_map snd (Map.elements (out_index p))).
  set (vertices := roots ++ map (Graph.target g) edges).
  assert (Hall : forall e, In e edges -> In (Graph.target g e) vertices).
  { intros e Hin; apply in_or_app; right; now apply in_map. }
  assert (Hroots : incl roots vertices).
  { intros v Hin; apply in_or_app; now left. }
  assert (Hinitial : audit_dom_dfs_tree_inv EV edges (@dfs_initial V E)).
  { split; [apply Map.wf_empty|].
    intros v e Hget; change (Map.get EV v Map.empty = Some e) in Hget.
    rewrite Map.get_empty in Hget; discriminate. }
  clearbody vertices.
  assert (Hfinal : audit_dom_dfs_tree_inv EV edges
    (fold_left (dfs_root p blocked) roots dfs_initial)).
  { revert Hroots Hinitial; generalize (@dfs_initial V E) as st.
    induction roots as [|root rest IH]; intros st Hroots Hstate;
      cbn [fold_left]; [exact Hstate|].
    apply IH.
    - intros v Hin; apply Hroots; now right.
    - eapply audit_dom_dfs_tree_root; [exact Hall|apply Hroots; now left|exact Hstate]. }
  destruct Hfinal as [Hwf Hrows].
  unfold dfs; cbn [tree_edge preorder]; rewrite <- rev_alt.
  intro Hin; apply (Map.elements_sound EV) in Hin; [|exact Hwf].
  destruct (Hrows key edge Hin) as [Hkey Hedge].
  split; [exact (proj1 (in_rev _ key) Hkey)|exact Hedge].
Qed.

(** A prepared outgoing edge occurs in a row enumerated by the original graph. *)
Lemma audit_dom_prepared_edge_origin {V E} (EV : encoding V) (g : Graph.t V E) edge :
  In edge (flat_map snd (Map.elements (out_index (prepare EV g)))) ->
  In edge (flat_map (Graph.out g) (Graph.nodes g)).
Proof.
  intro Hin; apply in_flat_map in Hin as [[key row] [Hrow Hedge]].
  cbn [snd] in Hedge.
  destruct (audit_dom_prepare_out_row EV g key row Hrow) as [Hkey ->].
  apply in_flat_map; exists key; auto.
Qed.

(** The virtual search's live vertices fit the original virtual input scale. *)
Lemma audit_dom_virtual_live_width {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) v :
  In v (preorder (virtual_dfs p)) ->
  Pos.size_nat (encode (virtual_encoding EV) v) <= audit_virtual_lt_input_scale EV g.
Proof.
  intro Hin.
  pose proof (audit_dom_live_width (virtual_encoding EV) (virtual_graph EV g)
    (virtual_prepared p) v Hin) as Hwidth.
  pose proof (audit_dom_virtual_sizes EV g p) as [_ [_ [_ [Hsearch _]]]].
  exact (Nat.le_trans _ _ _ Hwidth Hsearch).
Qed.

(** Virtual tree keys and the sources of their actual edges fit original support. *)
Lemma audit_dom_virtual_tree_width {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) key edge :
  In (key, edge) (Map.elements (tree_edge (virtual_dfs p))) ->
  Pos.size_nat (encode (virtual_encoding EV) key) <= audit_virtual_lt_input_scale EV g /\
  Pos.size_nat (encode (virtual_encoding EV) (Graph.source (virtual_graph EV g) edge)) <=
    audit_virtual_lt_input_scale EV g.
Proof.
  intro Hrow.
  destruct (audit_dom_dfs_tree_row (virtual_encoding EV) (virtual_graph EV g)
    (virtual_prepared p) FinSet.empty [inr tt] key edge Hrow) as [Hkey Hedge].
  split; [exact (audit_dom_virtual_live_width EV g p key Hkey)|].
  apply audit_dom_prepared_edge_origin in Hedge.
  apply in_flat_map in Hedge as [vertex [Hvertex Hedge]].
  pose proof (audit_dom_virtual_source_width EV g vertex edge Hvertex Hedge) as Hwidth.
  unfold audit_virtual_lt_input_scale; lia.
Qed.

(** Each actual producer vertex has an original-input bounded code. *)
Lemma audit_dom_virtual_producer_vertex_width {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) v :
  audit_semi_producer_vertex _ _ (virtual_encoding EV) (virtual_graph EV g)
    (virtual_prepared p) (virtual_dfs p) v ->
  Pos.size_nat (encode (virtual_encoding EV) v) <= audit_virtual_lt_input_scale EV g.
Proof.
  unfold audit_semi_producer_vertex; intro Hin.
  apply in_app_iff in Hin as [Hin|Hin];
    [exact (audit_dom_virtual_live_width EV g p v Hin)|].
  apply in_app_iff in Hin as [Hin|Hin].
  - apply in_map_iff in Hin as [[key rank] [Heq Hrow]]; cbn in Heq; subst key.
    destruct (audit_dom_dfs_numbered_vertex (virtual_encoding EV) (virtual_graph EV g)
      (virtual_prepared p) FinSet.empty [inr tt] v rank Hrow) as [Hlive _].
    exact (audit_dom_virtual_live_width EV g p v Hlive).
  - apply in_app_iff in Hin as [Hin|Hin].
    + apply in_map_iff in Hin as [[key edge] [Heq Hrow]]; cbn in Heq; subst key.
      exact (proj1 (audit_dom_virtual_tree_width EV g p v edge Hrow)).
    + apply in_app_iff in Hin as [Hin|Hin].
      * apply in_map_iff in Hin as [[key row] [Heq Hrow]]; cbn in Heq; subst key.
        exact (proj1 (audit_dom_virtual_in_index_width EV g p v row Hrow)).
      * apply in_map_iff in Hin as [edge [Heq Hedge]]; subst v.
        apply in_app_iff in Hedge as [Hedge|Hedge].
        -- apply in_flat_map in Hedge as [[key row] [Hrow Hedge]]; cbn in Hedge.
           exact (proj2 (audit_dom_virtual_in_index_width EV g p key row Hrow) edge Hedge).
        -- apply in_map_iff in Hedge as [[key found] [Heq Hrow]]; cbn in Heq; subst found.
           exact (proj2 (audit_dom_virtual_tree_width EV g p key edge Hrow)).
Qed.

(** A positive's binary width never exceeds its numeric value. *)
Lemma audit_dom_positive_width value : Pos.size_nat value <= Pos.to_nat value.
Proof.
  induction value as [value IH|value IH|]; cbn [Pos.size_nat Pos.to_nat]; lia.
Qed.

(** Every actual discovery rank fits four times the virtual input scale. *)
Lemma audit_dom_virtual_rank_width {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) key rank :
  In (key, rank) (Map.elements (pre_num (virtual_dfs p))) ->
  Pos.size_nat rank <= 4 * audit_virtual_lt_input_scale EV g.
Proof.
  intro Hrow.
  destruct (audit_dom_dfs_numbered_vertex (virtual_encoding EV) (virtual_graph EV g)
    (virtual_prepared p) FinSet.empty [inr tt] key rank Hrow) as [_ Hrank].
  change (Pos.to_nat rank <= S (length (preorder (virtual_dfs p)))) in Hrank.
  pose proof (audit_dom_virtual_search_counts EV g p) as [Hlive _].
  pose proof (audit_dom_positive_width rank) as Hwidth.
  assert (Hscale : 4 <= audit_virtual_lt_input_scale EV g).
  { unfold audit_virtual_lt_input_scale; lia. }
  cbn zeta in Hlive; lia.
Qed.

(** The generated producer's key and rank widths fit a concrete original-input bound. *)
Lemma audit_dom_virtual_producer_width {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) :
  audit_semi_producer_input_width (virtual_encoding EV) (virtual_graph EV g)
    (virtual_prepared p) (virtual_dfs p) <= 4 * audit_virtual_lt_input_scale EV g.
Proof.
  unfold audit_semi_producer_input_width; apply Nat.max_lub; apply audit_semi_max_le.
  - intros v Hin.
    pose proof (audit_dom_virtual_producer_vertex_width EV g p v Hin); lia.
  - intros [key rank] Hrow; cbn [snd].
    now apply (audit_dom_virtual_rank_width EV g p key rank).
Qed.

(** The actual semidominator result retains both key and value provenance. *)
Lemma audit_dom_semi_result_envelope {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) r :
  audit_semi_map_envelope _ EV (audit_semi_producer_vertex _ _ EV g p r)
    (SemiState.result (semi_compute p r)).
Proof.
  destruct (audit_semi_settles_erases _ _ EV g p r (rev (preorder r))
    (SemiState.Make Map.empty semi_links_empty)) as [events Hrun].
  assert (Hinitial : audit_semi_state_envelope _ EV (audit_semi_producer_vertex _ _ EV g p r)
    (SemiState.Make Map.empty semi_links_empty)).
  { split; [apply audit_semi_map_envelope_empty|apply audit_semi_links_envelope_empty]. }
  assert (Hvertices : forall v, In v (rev (preorder r)) ->
    audit_semi_producer_vertex _ _ EV g p r v).
  { intros v Hin; apply in_rev in Hin; unfold audit_semi_producer_vertex.
    apply in_or_app; now left. }
  destruct (audit_semi_settles_in_producer _ _ EV g p r _ _ _ _ Hrun Hinitial Hvertices)
    as [[Hresult _] _].
  exact Hresult.
Qed.

(** Actual LT input vertices inherit the generated producer's original support. *)
Lemma audit_dom_virtual_lt_vertex_width {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) v :
  audit_lt_input_vertex _ _ (virtual_graph EV g) (virtual_dfs p)
    (SemiState.result (semi_compute (virtual_prepared p) (virtual_dfs p))) v ->
  Pos.size_nat (encode (virtual_encoding EV) v) <= audit_virtual_lt_input_scale EV g.
Proof.
  unfold audit_lt_input_vertex; intro Hin.
  apply in_app_iff in Hin as [Hin|Hin];
    [exact (audit_dom_virtual_live_width EV g p v Hin)|].
  apply in_app_iff in Hin as [Hin|Hin].
  - apply in_map_iff in Hin as [[key value] [Heq Hrow]]; cbn in Heq; subst key.
    destruct (audit_semi_map_envelope_elements _ _ _ _ v value
      (audit_dom_semi_result_envelope (virtual_encoding EV) (virtual_graph EV g)
        (virtual_prepared p) (virtual_dfs p)) Hrow) as [Hv _].
    exact (audit_dom_virtual_producer_vertex_width EV g p v Hv).
  - apply in_app_iff in Hin as [Hin|Hin].
    + apply in_map_iff in Hin as [[key value] [Heq Hrow]]; cbn in Heq; subst value.
      destruct (audit_semi_map_envelope_elements _ _ _ _ key v
        (audit_dom_semi_result_envelope (virtual_encoding EV) (virtual_graph EV g)
          (virtual_prepared p) (virtual_dfs p)) Hrow) as [_ Hv].
      exact (audit_dom_virtual_producer_vertex_width EV g p v Hv).
    + apply in_app_iff in Hin as [Hin|Hin].
      * apply in_map_iff in Hin as [[key edge] [Heq Hrow]]; cbn in Heq; subst key.
        exact (proj1 (audit_dom_virtual_tree_width EV g p v edge Hrow)).
      * apply in_app_iff in Hin as [Hin|Hin].
        -- apply in_map_iff in Hin as [edge [Heq Hedge]]; subst v.
           apply in_map_iff in Hedge as [[key found] [Heq Hrow]]; cbn in Heq; subst found.
           exact (proj2 (audit_dom_virtual_tree_width EV g p key edge Hrow)).
        -- apply in_map_iff in Hin as [[key rank] [Heq Hrow]]; cbn in Heq; subst key.
           destruct (audit_dom_dfs_numbered_vertex (virtual_encoding EV) (virtual_graph EV g)
             (virtual_prepared p) FinSet.empty [inr tt] v rank Hrow) as [Hv _].
           exact (audit_dom_virtual_live_width EV g p v Hv).
Qed.

(** The actual LT input has bounded vertex and numeric rank widths. *)
Lemma audit_dom_virtual_lt_width {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) :
  audit_lt_nested_input_width (virtual_encoding EV) (virtual_graph EV g) (virtual_dfs p)
    (SemiState.result (semi_compute (virtual_prepared p) (virtual_dfs p))) <=
    4 * audit_virtual_lt_input_scale EV g.
Proof.
  unfold audit_lt_nested_input_width; apply Nat.max_lub; apply audit_semi_max_le.
  - intros v Hin; pose proof (audit_dom_virtual_lt_vertex_width EV g p v Hin); lia.
  - intros [key rank] Hrow; cbn [snd].
    now apply (audit_dom_virtual_rank_width EV g p key rank).
Qed.

(** Every nested LT result retains the operational input envelope, including parent values. *)
Lemma audit_dom_lt_nested_result_envelope {V E B} (EV : encoding V) (g : Graph.t V E)
    enc source (r : dfs_result V E) semis result events :
  (forall x, fst (enc x) = encode EV x) ->
  (forall edge, fst (source edge) = Graph.source g edge) ->
  audit_lt_nested_run (B := B) enc source r semis result events ->
  audit_semi_map_envelope _ EV (audit_lt_input_vertex _ _ g r semis) result.
Proof.
  intros Hencode Hsource Hrun.
  assert (Horder : Forall (audit_lt_input_vertex _ _ g r semis) (preorder r)).
  { apply Forall_forall; intros v Hin; now apply audit_lt_preorder_vertex. }
  pose proof (audit_lt_nested_buckets_erases V E B EV enc semis (preorder r)
    Map.empty Hencode) as Hbuckets.
  unfold audit_lt_nested_run in Hrun.
  destruct (audit_lt_nested_buckets enc semis (preorder r) Map.empty)
    as [buckets bucket_events]; cbn in Hbuckets, Hrun.
  destruct Hrun as [settled [reverse_events [Hreverse Hrun]]].
  assert (Hinitial : audit_lt_state_envelope _ _ EV g r semis
    (LtState.Make semi_links_empty Map.empty)).
  { split; cbn; [apply audit_semi_links_envelope_empty|apply audit_semi_map_envelope_empty]. }
  assert (Hreverse_order : Forall (audit_lt_input_vertex _ _ g r semis)
    (rev (preorder r))).
  { apply Forall_forall; intros v Hin; apply audit_lt_preorder_vertex; now apply in_rev. }
  destruct (audit_lt_nested_reverse_fold_safe _ _ _ EV g enc source (fun _ => 0) r semis
    buckets (rev (preorder r)) (LtState.Make semi_links_empty Map.empty) settled reverse_events
    Hencode Hsource Hbuckets Hinitial Hreverse_order Hreverse) as [[_ Hprovisional] _].
  destruct (audit_lt_nested_correct_fold_safe _ _ _ EV g enc (fun _ => 0) r semis
    (LtState.parents settled) (preorder r) Map.empty Hencode Hprovisional
    (audit_semi_map_envelope_empty _ EV _) Horder) as [Hresult _].
  destruct (audit_lt_nested_correct_fold enc semis (LtState.parents settled) (preorder r)
    Map.empty) as [output correction]; cbn in Hresult, Hrun.
  destruct Hrun as [Heq _]; now subst result.
Qed.

(** The ordinary LT output has the same operational key and value envelope. *)
Lemma audit_dom_lt_result_envelope {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) semis :
  audit_semi_map_envelope _ EV (audit_lt_input_vertex _ _ g r semis)
    (lt_compute EV g r semis).
Proof.
  destruct (audit_lt_nested_erasure V E unit EV g r semis
    (fun v => (encode EV v, [])) (fun edge => (Graph.source g edge, []))
    (fun _ => eq_refl) (fun _ => eq_refl)) as [result [events [Hrun ->]]].
  eapply audit_dom_lt_nested_result_envelope; [| |exact Hrun]; intros; reflexivity.
Qed.

(** Actual virtual LT parent values, as well as keys, have original-input bounded codes. *)
Lemma audit_dom_virtual_parent_value_width {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) key value :
  In (key, value) (Map.elements
    (lt_compute (virtual_encoding EV) (virtual_graph EV g) (virtual_dfs p)
      (SemiState.result (semi_compute (virtual_prepared p) (virtual_dfs p))))) ->
  Pos.size_nat (encode (virtual_encoding EV) key) <= audit_virtual_lt_input_scale EV g /\
  Pos.size_nat (encode (virtual_encoding EV) value) <= audit_virtual_lt_input_scale EV g.
Proof.
  intro Hrow.
  destruct (audit_semi_map_envelope_elements _ _ _ _ key value
    (audit_dom_lt_result_envelope (virtual_encoding EV) (virtual_graph EV g)
      (virtual_dfs p) (SemiState.result (semi_compute (virtual_prepared p) (virtual_dfs p))))
    Hrow) as [Hkey Hvalue].
  split.
  - exact (audit_dom_virtual_lt_vertex_width EV g p key Hkey).
  - exact (audit_dom_virtual_lt_vertex_width EV g p value Hvalue).
Qed.

(** * Scalar reserves for the generated virtual run *)

(** Generated producer and LT event counts satisfy explicit low-degree ceilings. *)
Lemma audit_dom_virtual_coarse_counts {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) :
  let scale := audit_virtual_lt_input_scale EV g in
  audit_semi_producer_event_bound (virtual_prepared p) (virtual_dfs p) <=
    (64 * 100)%nat * Nat.pow scale 4 /\
  audit_lt_nested_input_event_bound (virtual_dfs p) <= (128 * 100)%nat * Nat.pow scale 3.
Proof.
  pose proof (audit_dom_virtual_event_counts EV g p) as [Hsemi Hlt].
  set (scale := audit_virtual_lt_input_scale EV g) in *.
  assert (Hscale : 4 <= scale) by (unfold scale, audit_virtual_lt_input_scale; lia).
  cbn zeta in Hsemi, Hlt |- *.
  assert (Hrank : 2 + 3 * scale <= 4 * scale) by lia.
  assert (Hnext : 3 + 3 * scale <= 4 * scale) by lia.
  assert (Hedges : 1 + (1 + 3 * scale) * scale <= 4 * scale * scale) by nia.
  split.
  - eapply Nat.le_trans; [exact Hsemi|].
    eapply Nat.le_trans with (m := 100 * (4 * scale) * (4 * scale * scale) * (4 * scale)).
    + repeat apply Nat.mul_le_mono; lia.
    + cbn [Nat.pow]; nia.
  - eapply Nat.le_trans; [exact Hlt|].
    eapply Nat.le_trans with (m := 200 * (4 * scale) * (4 * scale) * (4 * scale)).
    + repeat apply Nat.mul_le_mono; lia.
    + cbn [Nat.pow]; nia.
Qed.

(** Event and width scalars bound a stage without expanding any execution receipt. *)
Lemma audit_dom_stage_budget_scalar scale count width :
  4 <= scale -> count <= 32 * Nat.pow scale 8 -> width <= 4 * scale ->
  512 * S count * S count + count * (512 + 64 * width) <=
    (1024 * 1024)%nat * Nat.pow scale 16.
Proof.
  intros Hscale Hcount Hwidth.
  set (q := Nat.pow scale 4).
  assert (Hq : 256 <= q).
  { change (Nat.pow 4 4 <= Nat.pow scale 4); now apply Nat.pow_le_mono_l. }
  assert (Hscale_q : scale <= q).
  { unfold q; replace scale with (Nat.pow scale 1) at 1 by (cbn; lia).
    apply Nat.pow_le_mono_r; lia. }
  assert (Hpow8 : Nat.pow scale 8 = q * q).
  { unfold q; rewrite <- Nat.pow_add_r; reflexivity. }
  assert (Hpow16 : Nat.pow scale 16 = q * q * q * q).
  { unfold q; repeat rewrite <- Nat.pow_add_r; reflexivity. }
  rewrite Hpow8 in Hcount; rewrite Hpow16.
  assert (Hsucc : S count <= 33 * (q * q)) by nia.
  assert (Hsquare : S count * S count <= (33 * (q * q)) * (33 * (q * q))).
  { apply Nat.mul_le_mono; exact Hsucc. }
  assert (Hlinear : count * (512 + 64 * width) <=
    (32 * (q * q)) * (512 + 256 * q)).
  { apply Nat.mul_le_mono; lia. }
  clear Hcount Hsucc Hwidth Hscale_q Hscale Hpow8 Hpow16.
  nia.
Qed.

(** The two generated event ceilings fit the common scalar reserve. *)
Lemma audit_dom_virtual_scalar_counts {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) :
  let scale := audit_virtual_lt_input_scale EV g in
  audit_semi_producer_event_bound (virtual_prepared p) (virtual_dfs p) <=
    32 * Nat.pow scale 8 /\
  audit_lt_nested_input_event_bound (virtual_dfs p) <= 32 * Nat.pow scale 8.
Proof.
  pose proof (audit_dom_virtual_coarse_counts EV g p) as [Hsemi Hlt].
  set (scale := audit_virtual_lt_input_scale EV g) in *.
  assert (Hscale : 4 <= scale) by (unfold scale, audit_virtual_lt_input_scale; lia).
  set (q := Nat.pow scale 4).
  set (r := Nat.pow scale 3).
  assert (Hq : 256 <= q).
  { change (Nat.pow 4 4 <= Nat.pow scale 4); now apply Nat.pow_le_mono_l. }
  assert (Hqr : 4 * r <= q).
  { unfold q, r; cbn [Nat.pow]; nia. }
  assert (Hpow : Nat.pow scale 8 = q * q).
  { unfold q; rewrite <- Nat.pow_add_r; reflexivity. }
  cbn zeta in Hsemi, Hlt |- *; fold q in Hsemi; fold r in Hlt; rewrite Hpow.
  split; nia.
Qed.

(** The concrete producer and LT input budgets fit separate polynomial reserves. *)
Lemma audit_dom_virtual_stage_budgets {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) :
  let reserve := (1024 * 1024)%nat * Nat.pow (audit_virtual_lt_input_scale EV g) 16 in
  audit_semi_producer_input_budget (virtual_encoding EV) (virtual_graph EV g)
    (virtual_prepared p) (virtual_dfs p) <= reserve /\
  audit_lt_nested_input_budget (virtual_encoding EV) (virtual_graph EV g) (virtual_dfs p)
    (SemiState.result (semi_compute (virtual_prepared p) (virtual_dfs p))) <= reserve.
Proof.
  pose proof (audit_dom_virtual_scalar_counts EV g p) as [Hsemi Hlt].
  pose proof (audit_dom_virtual_producer_width EV g p) as Hproducer.
  pose proof (audit_dom_virtual_lt_width EV g p) as Hwidth.
  assert (Hscale : 4 <= audit_virtual_lt_input_scale EV g).
  { unfold audit_virtual_lt_input_scale; lia. }
  cbn zeta in *; unfold audit_semi_producer_input_budget, audit_lt_nested_input_budget.
  split; apply audit_dom_stage_budget_scalar; assumption.
Qed.

(** Small preparation and DFS stages fit a sixth-power reserve using only their scalars. *)
Lemma audit_dom_small_stage_scalar scale count width amount bits :
  4 <= scale -> count <= 200 * scale -> width <= 8 * scale ->
  amount <= 4 * scale -> bits <= 5 * scale ->
  1024 * S count * S count + count * (512 + 64 * width) +
    64 * S amount * S amount + amount * bits <= (1024 * 1024)%nat * Nat.pow scale 6.
Proof.
  intros Hscale Hcount Hwidth Hamount Hbits.
  assert (Hsucc : S count <= 201 * scale) by lia.
  assert (Hsquare : S count * S count <= (201 * scale) * (201 * scale)).
  { apply Nat.mul_le_mono; exact Hsucc. }
  assert (Hlinear : count * (512 + 64 * width) <=
    (200 * scale) * (640 * scale)).
  { apply Nat.mul_le_mono; lia. }
  assert (Hamount_succ : S amount <= 5 * scale) by lia.
  assert (Hamount_square : S amount * S amount <= (5 * scale) * (5 * scale)).
  { apply Nat.mul_le_mono; exact Hamount_succ. }
  assert (Hlast : amount * bits <= (4 * scale) * (5 * scale)).
  { apply Nat.mul_le_mono; assumption. }
  assert (Htotal : 1024 * S count * S count + count * (512 + 64 * width) +
    64 * S amount * S amount + amount * bits <= (1024 * 1024)%nat * (64 * (scale * scale))).
  { nia. }
  assert (Hfour : 256 <= Nat.pow scale 4).
  { change (Nat.pow 4 4 <= Nat.pow scale 4); now apply Nat.pow_le_mono_l. }
  assert (Hpower : 64 * (scale * scale) <= Nat.pow scale 6).
  { replace (Nat.pow scale 6) with (Nat.pow scale 2 * Nat.pow scale 4)
      by (rewrite <- Nat.pow_add_r; reflexivity).
    replace (Nat.pow scale 2) with (scale * scale) by (cbn; lia).
    nia. }
  eapply Nat.le_trans; [exact Htotal|].
  apply Nat.mul_le_mono_l; exact Hpower.
Qed.

(** Virtual callback wrappers fit a sixth-power reserve from graph-size scalars. *)
Lemma audit_dom_virtual_wrapper_scalar scale entries width size prep_count dfs_count :
  4 <= scale -> entries <= scale -> width <= scale -> size <= scale ->
  prep_count <= 22 * scale -> dfs_count <= 200 * scale ->
  (prep_count + dfs_count) *
    (8 * S entries * (1024 + 128 * S width + size)) <= (1024 * 1024)%nat * Nat.pow scale 6.
Proof.
  intros Hscale Hentries Hwidth Hsize Hprep Hdfs.
  assert (Hcount : prep_count + dfs_count <= 222 * scale) by lia.
  assert (Hbody : 8 * S entries * (1024 + 128 * S width + size) <=
    (8 * 1026)%nat * (scale * scale)).
  { assert (Hentry : S entries <= 2 * scale) by lia.
    assert (Hterm : 1024 + 128 * S width + size <= 513 * scale) by lia.
    assert (Hproduct : S entries * (1024 + 128 * S width + size) <=
      (2 * scale) * (513 * scale)).
    { apply Nat.mul_le_mono; assumption. }
    nia. }
  assert (Hproduct : (prep_count + dfs_count) *
    (8 * S entries * (1024 + 128 * S width + size)) <=
      (222 * scale) * ((8 * 1026)%nat * (scale * scale))).
  { apply Nat.mul_le_mono; assumption. }
  assert (Hthree : 64 <= Nat.pow scale 3).
  { change (Nat.pow 4 3 <= Nat.pow scale 3); now apply Nat.pow_le_mono_l. }
  replace (Nat.pow scale 6) with (Nat.pow scale 3 * Nat.pow scale 3)
    by (rewrite <- Nat.pow_add_r; reflexivity).
  set (cube := Nat.pow scale 3) in *.
  assert (Hcube : cube = scale * scale * scale) by (unfold cube; cbn [Nat.pow]; ring).
  assert (Htotal : (prep_count + dfs_count) *
    (8 * S entries * (1024 + 128 * S width + size)) <=
      (1024 * 1024)%nat * (2 * cube)).
  { clear - Hproduct Hcube; nia. }
  clear - Htotal Hthree; nia.
Qed.

(** A bounded source-stage count and width suffice for the small-stage reserve. *)
Lemma audit_dom_source_budget_from_width scale count width :
  4 <= scale -> count <= 200 * scale -> width <= 8 * scale ->
  1024 * S count * S count + count * (512 + 64 * width) <=
    (1024 * 1024)%nat * Nat.pow scale 6.
Proof.
  intros Hscale Hcount Hwidth.
  eapply Nat.le_trans with (m := 1024 * S count * S count +
    count * (512 + 64 * width) + 64 * S 0 * S 0 + 0 * 0).
  - lia.
  - apply audit_dom_small_stage_scalar; lia.
Qed.

(** The full-event stage budget is below its source-stage scalar envelope. *)
Lemma audit_dom_full_budget_from_width scale count width :
  4 <= scale -> count <= 200 * scale -> width <= 8 * scale ->
  512 * S count * S count + count * (140 + 12 * width) <=
    (1024 * 1024)%nat * Nat.pow scale 6.
Proof.
  intros Hscale Hcount Hwidth.
  eapply Nat.le_trans; [|apply audit_dom_source_budget_from_width; eassumption].
  clear; nia.
Qed.

(** Both preparation budgets follow from the generated graph's size and key width. *)
Lemma audit_dom_prepare_stage_budgets {V E} (EV : encoding V) (g : Graph.t V E) scale :
  4 <= scale -> length (Graph.nodes g) <= scale -> edge_count g <= scale ->
  audit_graph_prepare_input_width EV g <= scale ->
  audit_prepare_source_budget EV g <= (1024 * 1024)%nat * Nat.pow scale 6 /\
  audit_graph_prepare_full_budget EV g <= (1024 * 1024)%nat * Nat.pow scale 6.
Proof.
  intros Hscale Hnodes Hedges Hwidth.
  set (count := audit_graph_prepare_full_event_bound g).
  set (amount := 2 * length (Graph.nodes g) + edge_count g + 1).
  assert (Hcount : count <= 22 * scale).
  { unfold count, audit_graph_prepare_full_event_bound; lia. }
  assert (Hamount : amount <= 4 * scale) by (unfold amount; lia).
  assert (Hbits : Pos.size_nat (Pos.of_succ_nat amount) <= 5 * scale).
  { pose proof (audit_dom_positive_width (Pos.of_succ_nat amount)) as Hvalue.
    rewrite SuccNat2Pos.id_succ in Hvalue; lia. }
  split.
  - unfold audit_prepare_source_budget; fold count amount.
    apply audit_dom_small_stage_scalar; lia.
  - unfold audit_graph_prepare_full_budget; fold count amount.
    eapply Nat.le_trans; [|apply audit_dom_small_stage_scalar with
      (count := count) (width := audit_graph_prepare_input_width EV g)
      (amount := amount) (bits := Pos.size_nat (Pos.of_succ_nat amount)); try lia].
    unfold audit_key_bits_weight; clear; nia.
Qed.

(** Both one-root DFS budgets follow from its actual input width and binary fuel. *)
Lemma audit_dom_dfs_stage_budgets {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) root scale :
  4 <= scale -> Pos.to_nat (fuel p) <= 3 * scale ->
  audit_dfs_full_input_width EV g p [root] <= scale ->
  audit_dfs_source_budget EV g p [root] <= (1024 * 1024)%nat * Nat.pow scale 6 /\
  audit_dfs_full_input_budget EV g p [root] <= (1024 * 1024)%nat * Nat.pow scale 6.
Proof.
  intros Hscale Hfuel Hwidth.
  assert (Hcount : audit_dfs_full_input_event_bound p [root] <= 200 * scale).
  { change (3 + 1 * (40 * S (Pos.to_nat (fuel p))) <= 200 * scale); lia. }
  assert (Hsource_clock : Pos.size_nat
    (Pos.of_succ_nat (S (length [root]) * S (Pos.to_nat (fuel p)))) <= 8 * scale).
  { eapply Nat.le_trans; [apply audit_dom_positive_width|].
    rewrite SuccNat2Pos.id_succ.
    change (S (2 * S (Pos.to_nat (fuel p))) <= 8 * scale); lia. }
  assert (Hfull_clock : audit_key_bits_weight
    (Pos.of_succ_nat (2 + length [root] * S (Pos.to_nat (fuel p)))) <= 8 * scale).
  { unfold audit_key_bits_weight.
    eapply Nat.le_trans; [apply audit_dom_positive_width|].
    rewrite SuccNat2Pos.id_succ.
    change (S (2 + 1 * S (Pos.to_nat (fuel p))) <= 8 * scale); lia. }
  split.
  - unfold audit_dfs_source_budget; apply audit_dom_source_budget_from_width;
      [exact Hscale|exact Hcount|].
    apply Nat.max_lub; [lia|exact Hsource_clock].
  - unfold audit_dfs_full_input_budget; apply audit_dom_full_budget_from_width;
      [exact Hscale|exact Hcount|].
    apply Nat.max_lub; [lia|exact Hfull_clock].
Qed.

(** Actual virtual callback wrappers fit a reserve derived from the original graph. *)
Lemma audit_dom_virtual_wrapper_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) :
  let vg := virtual_graph EV g in let enc := virtual_encoding EV in
  let vp := virtual_prepared p in let scale := audit_virtual_lt_input_scale EV g in
  (audit_graph_prepare_full_event_bound vg + audit_dfs_full_input_event_bound vp [inr tt]) *
    (8 * S (length (Graph.entries g)) *
      (1024 + 128 * S (Nat.max (audit_graph_prepare_input_width enc vg)
        (audit_dfs_full_input_width enc vg vp [inr tt])) +
        (1 + length (Graph.nodes g) + length (Graph.entries g) + edge_count g))) <=
    (1024 * 1024)%nat * Nat.pow scale 6.
Proof.
  pose proof (audit_dom_virtual_sizes EV g p) as [Hnodes [Hedges [Hwidth [Hdfs Hfuel]]]].
  set (scale := audit_virtual_lt_input_scale EV g) in *.
  assert (Hscale : 4 <= scale) by (unfold scale, audit_virtual_lt_input_scale; lia).
  cbn zeta in Hnodes, Hedges, Hwidth, Hdfs, Hfuel |- *; fold scale.
  assert (Hentries : length (Graph.entries g) <= scale).
  { unfold scale, audit_virtual_lt_input_scale; lia. }
  assert (Hsize : 1 + length (Graph.nodes g) + length (Graph.entries g) + edge_count g <= scale).
  { rewrite audit_dom_original_edge_count; unfold scale, audit_virtual_lt_input_scale; lia. }
  apply audit_dom_virtual_wrapper_scalar; try assumption.
  - apply Nat.max_lub; assumption.
  - unfold audit_graph_prepare_full_event_bound; lia.
  - change (3 + 1 * (40 * S (Pos.to_nat (fuel (virtual_prepared p)))) <= 200 * scale).
    lia.
Qed.

(** The entire virtual preparation/search budget is bounded by the original input scale. *)
Lemma audit_dom_virtual_source_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) :
  audit_virtual_source_search_budget EV g <=
    (1024 * 1024)%nat * Nat.pow (audit_virtual_lt_input_scale EV g) 8.
Proof.
  pose proof (audit_dom_virtual_sizes EV g p) as [Hnodes [Hedges [Hwidth [Hdfs Hfuel]]]].
  set (scale := audit_virtual_lt_input_scale EV g) in *.
  assert (Hscale : 4 <= scale) by (unfold scale, audit_virtual_lt_input_scale; lia).
  cbn zeta in Hnodes, Hedges, Hwidth, Hdfs, Hfuel.
  destruct (audit_dom_prepare_stage_budgets (virtual_encoding EV) (virtual_graph EV g)
    scale Hscale Hnodes Hedges Hwidth) as [Hprepare_source Hprepare_full].
  destruct (audit_dom_dfs_stage_budgets (virtual_encoding EV) (virtual_graph EV g)
    (virtual_prepared p) (inr tt) scale Hscale Hfuel Hdfs) as [Hsearch_source Hsearch_full].
  pose proof (audit_dom_virtual_wrapper_budget EV g p) as Hwrapper.
  cbn zeta in Hwrapper; fold scale in Hwrapper.
  set (reserve := (1024 * 1024)%nat * Nat.pow scale 6) in *.
  assert (Hsum : audit_virtual_source_search_budget EV g <= 5 * reserve).
  { unfold audit_virtual_source_search_budget, audit_virtual_full_search_input_budget.
    cbv beta iota zeta; fold (virtual_prepared p).
    lia. }
  eapply Nat.le_trans; [exact Hsum|].
  unfold reserve; fold scale.
  replace (Nat.pow scale 8) with (Nat.pow scale 6 * Nat.pow scale 2)
    by (rewrite <- Nat.pow_add_r; reflexivity).
  assert (Htwo : 5 <= Nat.pow scale 2) by (cbn [Nat.pow]; nia).
  nia.
Qed.

(** Erasing the generated parent map fits the same polynomial stage reserve. *)
Lemma audit_dom_virtual_erasure_reserve {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) semis :
  audit_erase_nested_budget EV
    (lt_compute (virtual_encoding EV) (virtual_graph EV g) (virtual_dfs p) semis) <=
    (1024 * 1024)%nat * Nat.pow (audit_virtual_lt_input_scale EV g) 16.
Proof.
  pose proof (audit_dom_virtual_parent_erase_budget EV g p semis) as Hbudget.
  set (scale := audit_virtual_lt_input_scale EV g) in *.
  assert (Hscale : 4 <= scale) by (unfold scale, audit_virtual_lt_input_scale; lia).
  set (q := Nat.pow scale 4).
  assert (Hq : 256 <= q).
  { change (Nat.pow 4 4 <= Nat.pow scale 4); now apply Nat.pow_le_mono_l. }
  assert (Hscale_q : scale <= q).
  { unfold q; replace scale with (Nat.pow scale 1) at 1 by (cbn; lia).
    apply Nat.pow_le_mono_r; lia. }
  assert (Hbound : (1 + 3 * scale) * scale <= q).
  { unfold q; cbn [Nat.pow]; nia. }
  assert (Hsquare : S ((1 + 3 * scale) * scale) * S ((1 + 3 * scale) * scale) <=
    (2 * q) * (2 * q)).
  { apply Nat.mul_le_mono; lia. }
  assert (Hproduct : S ((1 + 3 * scale) * scale) * S scale <= (2 * q) * (2 * q)).
  { apply Nat.mul_le_mono; lia. }
  assert (Hpow : Nat.pow scale 16 = q * q * q * q).
  { unfold q; repeat rewrite <- Nat.pow_add_r; reflexivity. }
  cbn zeta in Hbudget; rewrite Hpow; nia.
Qed.

(** Six separate stage reserves fit the published fortieth-power original-input budget. *)
Lemma audit_dom_six_reserves scale :
  4 <= scale -> 6 * ((1024 * 1024)%nat * Nat.pow scale 16) <= (1024 * 1024)%nat * Nat.pow scale 40.
Proof.
  intro Hscale.
  assert (Htwo : 6 <= Nat.pow scale 2) by (cbn [Nat.pow]; nia).
  assert (Hmono : Nat.pow scale 18 <= Nat.pow scale 40).
  { apply Nat.pow_le_mono_r; lia. }
  assert (Hproduct : 6 * Nat.pow scale 16 <= Nat.pow scale 18).
  { replace (Nat.pow scale 18) with (Nat.pow scale 16 * Nat.pow scale 2)
      by (rewrite <- Nat.pow_add_r; reflexivity).
    nia. }
  nia.
Qed.

(** The original input bounds every internal stage of its concrete virtual LT execution. *)
Lemma audit_dom_virtual_concrete_reserve {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) :
  let vp := virtual_prepared p in
  let search := virtual_dfs p in
  let semis := SemiState.result (semi_compute vp search) in
  audit_virtual_source_search_budget EV g +
    audit_semi_producer_input_budget (virtual_encoding EV) (virtual_graph EV g) vp search +
    audit_lt_nested_input_budget (virtual_encoding EV) (virtual_graph EV g) search semis +
    audit_erase_nested_budget EV
      (lt_compute (virtual_encoding EV) (virtual_graph EV g) search semis) +
    128 * audit_semi_producer_event_bound vp search +
    128 * audit_lt_nested_input_event_bound search <= audit_virtual_lt_input_budget EV g.
Proof.
  pose proof (audit_dom_virtual_source_budget EV g p) as Hsource.
  pose proof (audit_dom_virtual_stage_budgets EV g p) as [Hsemi Hlt].
  pose proof (audit_dom_virtual_erasure_reserve EV g p
    (SemiState.result (semi_compute (virtual_prepared p) (virtual_dfs p)))) as Herase.
  pose proof (audit_dom_virtual_scalar_counts EV g p) as [Hsemi_count Hlt_count].
  set (scale := audit_virtual_lt_input_scale EV g) in *.
  assert (Hscale : 4 <= scale) by (unfold scale, audit_virtual_lt_input_scale; lia).
  assert (Hmono : Nat.pow scale 8 <= Nat.pow scale 16).
  { apply Nat.pow_le_mono_r; lia. }
  set (reserve := (1024 * 1024)%nat * Nat.pow scale 16) in *.
  assert (Hsource_reserve : audit_virtual_source_search_budget EV g <= reserve).
  { unfold reserve; nia. }
  assert (Hsemi_internal : 128 * audit_semi_producer_event_bound
    (virtual_prepared p) (virtual_dfs p) <= reserve).
  { cbn zeta in Hsemi_count; unfold reserve; nia. }
  assert (Hlt_internal : 128 * audit_lt_nested_input_event_bound (virtual_dfs p) <= reserve).
  { cbn zeta in Hlt_count; unfold reserve; nia. }
  pose proof (audit_dom_six_reserves scale Hscale) as Hsum.
  cbn zeta in Hsemi, Hlt |- *.
  unfold audit_virtual_lt_input_budget; fold scale; fold reserve in Hsum.
  lia.
Qed.

(** Lifted virtual encoders return exactly the generated virtual key encoding. *)
Lemma audit_dom_virtual_full_encode_erases {V E B} (EV : encoding V) (g : Graph.t V E)
    (cb : audit_virtual_base_callbacks V E B) :
  audit_virtual_base_callbacks_erase EV g cb ->
  forall v, fst (audit_virtual_full_encode cb v) = encode (virtual_encoding EV) v.
Proof.
  intros [_ [_ Hbase]] [v|[]]; cbn [audit_virtual_full_encode virtual_encoding].
  - specialize (Hbase v); destruct (audit_virtual_base_encode cb v);
      cbn [fst] in Hbase |- *; now rewrite Hbase.
  - reflexivity.
Qed.

(** The captured virtual run's state is the ordinary producer state without callback replay. *)
Lemma audit_dom_virtual_captured_states {V E B} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (cb : audit_virtual_base_callbacks V E B) source
    semi_state semi_events virtual_parents lt_events :
  audit_virtual_base_callbacks_erase EV g cb ->
  (forall edge, fst (source edge) = Graph.source g edge) ->
  audit_semi_producer_nested_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
    (virtual_prepared p) (virtual_dfs p) semi_state semi_events ->
  audit_lt_nested_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
    (virtual_dfs p) (SemiState.result semi_state) virtual_parents lt_events ->
  semi_state = semi_compute (virtual_prepared p) (virtual_dfs p) /\
  virtual_parents = lt_compute (virtual_encoding EV) (virtual_graph EV g) (virtual_dfs p)
    (SemiState.result semi_state).
Proof.
  intros Hcallbacks Hsource Hsemi Hlt.
  pose proof (audit_dom_virtual_full_encode_erases EV g cb Hcallbacks) as Hencode.
  pose proof (audit_virtual_full_source_correct _ _ _ EV g source Hsource) as Hfull_source.
  destruct (audit_semi_producer_nested_erasure _ _ _ (virtual_encoding EV) (virtual_graph EV g)
    (virtual_prepared p) (virtual_dfs p) (audit_virtual_full_encode cb)
    (audit_virtual_full_source source) Hencode Hfull_source) as [state [events [Hrun Hstate]]].
  destruct (audit_semi_producer_nested_unique _ _ _ (virtual_encoding EV) (virtual_graph EV g)
    (virtual_prepared p) (virtual_dfs p) (audit_virtual_full_encode cb)
    (audit_virtual_full_source source) _ _ _ _ Hsemi Hrun) as [Heq _].
  split; [now rewrite Heq|].
  destruct (audit_lt_nested_erasure _ _ _ (virtual_encoding EV) (virtual_graph EV g)
    (virtual_dfs p) (SemiState.result semi_state) (audit_virtual_full_encode cb)
    (audit_virtual_full_source source) Hencode Hfull_source) as [parents [trace [Hrun_lt
      Hparents]]].
  destruct (audit_lt_nested_unique _ _ _ (audit_virtual_full_encode cb)
    (audit_virtual_full_source source) (virtual_dfs p) (SemiState.result semi_state)
    _ _ _ _ Hlt Hrun_lt) as [Heq_lt _].
  now rewrite Heq_lt.
Qed.

(** The default dominator run satisfies its exact source-work contract on the captured execution. *)
Theorem audit_default_dom_single_run_holds : audit_default_dom_single_run_statement.
Proof.
  apply audit_dom_single_run_from_reserve.
  intros V E B EV g p cb source vp search prepare_events dfs_events semi_state semi_events
    virtual_parents lt_events parents erase_events receipt Hcallbacks Hsource Hsearch Hsemi Hlt
    Herase Hreceipt.
  pose proof (audit_virtual_source_search_holds _ _ _ EV g p cb (fun _ => 0) Hcallbacks)
    as Hsearch_erases.
  rewrite Hsearch in Hsearch_erases; cbn [fst snd] in Hsearch_erases.
  destruct Hsearch_erases as [Hvp [Hdfs _]]; subst vp search.
  eapply audit_dom_virtual_reserve_from_limits; try eassumption.
  destruct (audit_dom_virtual_captured_states EV g p cb source semi_state semi_events
    virtual_parents lt_events Hcallbacks Hsource Hsemi Hlt) as [Hstate Hparents].
  subst semi_state; rewrite Hparents.
  exact (audit_dom_virtual_concrete_reserve EV g p).
Qed.
