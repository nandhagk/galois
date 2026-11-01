(** * Adequacy of indexed memory walks

    Preparation builds every listed version row before the search uses the index.
    For example, a missing predecessor row supplies the empty incoming list.
    Builds on: memory table, raw successor, graph preparation and map adequacy. *)

From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsAuditMap
  CollectionsAuditTrie CollectionsAuditMapAdequacy.
From Galois.Graph Require Import GraphCore GraphPrepare GraphAuditBase GraphAuditBaseAdequacy.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryFrontier AnalysesMemoryWalk
  AnalysesAuditMemoryRawNext AnalysesAuditMemoryEffects AnalysesAuditMemoryDisjoint
  AnalysesAuditMemoryEffectsAdequacy AnalysesAuditMemoryDisjointAdequacy
  AnalysesAuditMemoryGraphCallbacks AnalysesAuditMemoryEncoding
  AnalysesAuditMemoryEncodingAdequacy AnalysesAuditMemoryTable
  AnalysesAuditMemoryTableAdequacy AnalysesAuditMemoryIndex
  AnalysesAuditMemoryIndexAdequacy AnalysesAuditMemoryInputBudget
  AnalysesAuditMemoryInputBudgetAdequacy AnalysesAuditMemorySharedBudget
  AnalysesAuditMemorySharedBudgetAdequacy AnalysesAuditMemoryWalkIndex.
Import List.ListNotations.

(** * Adjacency erasure *)

(** Counted operand enumeration retains the original order and missing entries. *)
Lemma audit_walk_operands_erases N E T CE SE IE OE BE
    (operand : N -> option E -> option (memory_version N E) * list OE)
    (mg : memory_graph N E) node keys :
  (forall n key, fst (operand n key) = memory_operand mg n key) ->
  fst (@audit_memory_operands N E T CE SE IE OE BE operand node keys) =
    memory_walk_operands mg node keys.
Proof.
  intro Hoperand.
  unfold memory_walk_operands.
  induction keys as [|key rest IH]; cbn [audit_memory_operands flat_map]; [reflexivity|].
  pose proof (Hoperand node key) as Hkey.
  destruct (operand node key) as [value calls]; cbn in Hkey.
  destruct (@audit_memory_operands N E T CE SE IE OE BE operand node rest) as [tail events];
    cbn in IH.
  rewrite <- Hkey, <- IH.
  destruct value; reflexivity.
Qed.

(** Preparation callbacks return the graph and encoding values required by the graph proof. *)
Lemma audit_walk_callbacks_erases N E CN OE TE (EN : encoding N) (g : Graph.t N E)
    (node_enc : N -> positive * list CN) (out : N -> list E * list OE)
    (target : E -> N * list TE) :
  (forall n, fst (node_enc n) = encode EN n) ->
  (forall n, fst (out n) = Graph.out g n) ->
  (forall e, fst (target e) = Graph.target g e) ->
  audit_prepare_callbacks_erase EN g (audit_snapshot_graph_callbacks node_enc out target).
Proof.
  intros Hnode Hout Htarget.
  unfold audit_prepare_callbacks_erase, audit_snapshot_graph_callbacks; cbn.
  split; [|split].
  - intro n; specialize (Hout n); destruct (out n); exact Hout.
  - intro e; specialize (Htarget e); destruct (target e); exact Htarget.
  - intro n; specialize (Hnode n); destruct (node_enc n); exact Hnode.
Qed.

(** A counted predecessor lookup returns the prepared graph's incoming row. *)
Lemma audit_walk_predecessors_erases N E CN (EN : encoding N)
    (node_enc : N -> positive * list CN) (rows : Map.t N (list E)) node :
  fst (node_enc node) = encode EN node ->
  fst (audit_walk_predecessors node_enc rows node) = index_edges EN rows node.
Proof.
  intro Henc.
  pose proof (audit_map_get_erases N (list E) CN node_enc EN node rows Henc) as Hget.
  unfold audit_walk_predecessors, index_edges.
  destruct (audit_map_get node_enc node rows) as [found calls]; cbn in Hget.
  rewrite <- Hget; destruct found; reflexivity.
Qed.

(** Raw successor erasure uses the same effect, predecessor and memory callbacks. *)
Lemma audit_walk_raw_next_erases N E T CE SE IE OE BE (EE : encoding E) (ET : encoding T)
    (edge_enc : E -> positive * list CE) (site_enc : T -> positive * list SE)
    table (incoming : N -> list E * list IE)
    (operand : N -> option E -> option (memory_version N E) * list OE)
    (before : E -> nat -> option (memory_version N E) * list BE) mg q v :
  (forall e, fst (edge_enc e) = encode EE e) ->
  (forall t, fst (site_enc t) = encode ET t) ->
  (forall n key, fst (operand n key) = memory_operand mg n key) ->
  (forall e i, fst (before e i) = memory_before mg e i) ->
  fst (audit_memory_raw_next edge_enc site_enc table incoming operand before q v) =
    memory_walk_raw_next EE ET table (fun n => fst (incoming n)) mg q v.
Proof.
  intros Hedge Hsite Hoperand Hbefore.
  destruct v as [|node|edge index]; cbn [audit_memory_raw_next memory_walk_raw_next];
    [reflexivity| |].
  - destruct (incoming node) as [edges events] eqn:Hin.
    pose proof (audit_walk_operands_erases N E T CE SE IE OE BE operand mg node
      (map Some edges) Hoperand) as Htail.
    pose proof (Hoperand node None) as Hkey.
    destruct (operand node None) as [value calls] eqn:Hcall; cbn in Hkey.
    destruct (@audit_memory_operands N E T CE SE IE OE BE operand node (map Some edges))
      as [tail tail_calls] eqn:Htailcall; cbn in Htail.
    unfold memory_walk_operands in *; cbn in *.
    rewrite Hcall, Htailcall; cbn.
    rewrite <- Hkey, <- Htail; destruct value; reflexivity.
  - pose proof (audit_memory_effect_get_erases E T CE edge_enc EE table edge index (Hedge edge))
      as Heffect.
    destruct (audit_memory_effect_get edge_enc table edge index) as [effect calls]; cbn in Heffect.
    rewrite <- Heffect.
    destruct effect as [effect|]; [|destruct (memory_before mg edge index); reflexivity].
    pose proof (Hbefore edge index) as Hprevious.
    destruct (before edge index) as [previous events]; cbn in Hprevious.
    rewrite <- Hprevious.
    destruct previous as [previous|]; [|reflexivity].
    pose proof (audit_memory_scopes_disjoint_erases T SE site_enc ET (effect_writes effect) q Hsite)
      as Hdisjoint.
    destruct (audit_memory_scopes_disjoint site_enc (effect_writes effect) q) as [disjoint events'];
      cbn in Hdisjoint.
    rewrite <- Hdisjoint; reflexivity.
Qed.

(** Materialized rows agree with the original adjacency index, including duplicate keys. *)
Theorem audit_memory_walk_index_erases : audit_memory_walk_index_erases_statement.
Proof.
  intros N E T CN CE SE OE TE FE PE BE EN EE ET node_enc edge_enc site_enc out target effects
    operand before g original mg scope Hnode Hedge Hsite Hout Htarget Heffects Hoperand Hbefore.
  pose proof (audit_memory_effect_table_erases N E T CE OE FE EE g edge_enc out effects original
    Hedge Hout Heffects) as Htable.
  pose proof (audit_walk_callbacks_erases N E CN OE TE EN g node_enc out target Hnode Hout Htarget)
    as Hcallbacks.
  pose proof (audit_prepare_source_correct N E (audit_snapshot_graph_body CN OE TE) EN g
    (audit_snapshot_graph_callbacks node_enc out target) (fun _ => 0) Hcallbacks) as Hprepare.
  unfold audit_memory_walk_index_counted, memory_walk_index.
  destruct (audit_memory_effect_table edge_enc out effects (Graph.nodes g)) as [table table_events];
    cbn in Htable.
  destruct (audit_prepare_source_counted EN g (audit_snapshot_graph_callbacks node_enc out target))
    as [base prepare_events]; cbn in Hprepare.
  destruct Hprepare as [Hbase _].
  cbn [audit_walk_index_value].
  pose proof (audit_memory_result_index_erases (memory_version N E) (list (memory_version N E))
    (audit_memory_version_event N E CN CE) (audit_walk_raw_event N E T CN CE SE PE BE)
    (audit_memory_version_encode node_enc edge_enc) (memory_frontier_version_encoding EN EE)
    (audit_memory_raw_next edge_enc site_enc table
      (audit_walk_predecessors node_enc (in_index base)) operand before scope)
    (memory_walk_raw_next EE ET (memory_walk_effect_table EE g original)
      (pred_edges (prepare EN g)) mg scope) (memory_versions mg)) as Hindex.
  assert (Hcodes : forall version, In version (memory_versions mg) ->
    fst (audit_memory_version_encode node_enc edge_enc version) =
      encode (memory_frontier_version_encoding EN EE) version).
  { intros version Hin.
    pose proof (audit_memory_version_encode_erases N E CN CE EN EE node_enc edge_enc version
      Hnode Hedge) as Hencode.
    exact Hencode. }
  assert (Hvalues : forall version, In version (memory_versions mg) ->
    fst (audit_memory_raw_next edge_enc site_enc table
      (audit_walk_predecessors node_enc (in_index base)) operand before scope version) =
    memory_walk_raw_next EE ET (memory_walk_effect_table EE g original)
      (pred_edges (prepare EN g)) mg scope version).
  { intros version Hin.
    pose proof (audit_walk_raw_next_erases N E T CE SE (audit_map_event N (list E) CN) PE BE
      EE ET edge_enc site_enc table (audit_walk_predecessors node_enc (in_index base))
      operand before mg scope version Hedge Hsite Hoperand Hbefore) as Hraw.
    rewrite Hraw, Htable, Hbase.
    destruct version as [|node|edge index]; cbn [memory_walk_raw_next]; try reflexivity.
    unfold pred_edges.
    rewrite (audit_walk_predecessors_erases N E CN EN node_enc (in_index (prepare EN g)) node
      (Hnode node)).
    reflexivity. }
  specialize (Hindex Hcodes Hvalues).
  destruct (audit_memory_result_index (audit_memory_version_encode node_enc edge_enc)
    (audit_memory_raw_next edge_enc site_enc table
      (audit_walk_predecessors node_enc (in_index base)) operand before scope) (memory_versions mg))
    as [index index_events] eqn:Hindexrun.
  cbn [audit_walk_index_value].
  change (fst (index, index_events) =
    memory_result_index (memory_frontier_version_encoding EN EE)
      (memory_walk_raw_next EE ET (memory_walk_effect_table EE g original)
        (pred_edges (prepare EN g)) mg scope) (memory_versions mg)).
  rewrite <- Hindexrun; exact Hindex.
Qed.

(** * Preparation and whole-input work *)

(** A counted lookup's single map event is charged to its actual key. *)
Lemma audit_walk_prepare_get_budget N E B (enc : N -> positive * list B) key rows
    node_budget out_budget target_budget limit :
  node_budget key <= limit ->
  Forall (fun event => audit_prepare_source_event_budget node_budget out_budget target_budget event
    <= limit) (map (@PrepareSourceMap N E B) (snd (audit_map_get enc key rows))).
Proof.
  intro Hkey.
  unfold audit_map_get.
  destruct (enc key) as [code events].
  destruct (audit_map_code_get code rows) as [found trace].
  cbn [snd map audit_prepare_source_event_budget].
  constructor; [exact Hkey|constructor].
Qed.

(** A counted insertion's single map event is charged to its actual key. *)
Lemma audit_walk_prepare_set_budget N E B (enc : N -> positive * list B) key value rows
    node_budget out_budget target_budget limit :
  node_budget key <= limit ->
  Forall (fun event => audit_prepare_source_event_budget node_budget out_budget target_budget event
    <= limit) (map (@PrepareSourceMap N E B) (snd (audit_map_set enc key value rows))).
Proof.
  intro Hkey.
  unfold audit_map_set.
  destruct (enc key) as [code events].
  destruct (audit_trie_set code (key, value) rows) as [updated trace].
  cbn [snd map audit_prepare_source_event_budget].
  constructor; [exact Hkey|constructor].
Qed.

(** Every outgoing-index event is charged to a node from the supplied list. *)
Lemma audit_walk_prepare_out_budget N E B (cb : audit_prepare_callback_model N E B)
    nodes initial node_budget out_budget target_budget limit :
  (forall node, In node nodes -> node_budget node <= limit /\ out_budget node <= limit) ->
  Forall (fun event => audit_prepare_source_event_budget node_budget out_budget target_budget event
    <= limit) (snd (audit_prepare_source_out cb nodes initial)).
Proof.
  intro Hnodes; induction nodes as [|node rest IH]; cbn [audit_prepare_source_out].
  - repeat constructor; cbn; lia.
  - specialize (IH (fun n Hin => Hnodes n (or_intror Hin))).
    destruct (audit_prepare_source_out cb rest initial) as [middle events] eqn:Hrest.
    cbn in IH.
    destruct (audit_prepare_out_model cb node) as [out body] eqn:Hout.
    pose proof (audit_walk_prepare_set_budget N E B (audit_prepare_encode_model cb) node out middle
      node_budget out_budget target_budget limit (proj1 (Hnodes node (or_introl eq_refl)))) as Hmap.
    destruct (audit_map_set (audit_prepare_encode_model cb) node out middle) as [result writes].
    cbn [snd] in Hmap |- *.
    constructor; [cbn; lia|].
    apply Forall_app; split; [exact IH|].
    constructor; [cbn; exact (proj2 (Hnodes node (or_introl eq_refl)))|exact Hmap].
Qed.

(** Each incoming-index event is charged to its actual edge or returned target. *)
Lemma audit_walk_prepare_edges_budget N E B (cb : audit_prepare_callback_model N E B)
    edges initial node_budget out_budget target_budget limit :
  (forall edge, In edge edges -> target_budget edge <= limit /\
    node_budget (fst (audit_prepare_target_model cb edge)) <= limit) ->
  Forall (fun event => audit_prepare_source_event_budget node_budget out_budget target_budget event
    <= limit) (snd (audit_prepare_source_edges cb edges initial)).
Proof.
  intro Hedges; induction edges as [|edge rest IH]; cbn [audit_prepare_source_edges].
  - repeat constructor; cbn; lia.
  - specialize (IH (fun e Hin => Hedges e (or_intror Hin))).
    destruct (audit_prepare_source_edges cb rest initial) as [middle events] eqn:Hrest.
    cbn in IH.
    pose proof (Hedges edge (or_introl eq_refl)) as [Hedge Hnode].
    destruct (audit_prepare_target_model cb edge) as [target body] eqn:Htarget; cbn in Hnode.
    pose proof (audit_walk_prepare_get_budget N E B (audit_prepare_encode_model cb) target middle
      node_budget out_budget target_budget limit Hnode) as Hread.
    destruct (audit_map_get (audit_prepare_encode_model cb) target middle) as [found reads].
    cbn in Hread.
    pose proof (audit_walk_prepare_set_budget N E B (audit_prepare_encode_model cb) target
      (edge ::
        match found with
        Some xs => xs
        | None => []
        end) middle
      node_budget out_budget target_budget limit Hnode) as Hwrite.
    destruct (audit_map_set (audit_prepare_encode_model cb) target
      (edge ::
        match found with
        Some xs => xs
        | None => []
        end) middle) as [result writes].
    cbn [snd] in Hwrite |- *.
    constructor; [cbn; lia|].
    repeat rewrite Forall_app; repeat split; try exact IH; try exact Hread; try exact Hwrite;
      repeat constructor; cbn; lia.
Qed.

(** Incoming construction charges every output and edge at its actual supplied input. *)
Lemma audit_walk_prepare_in_budget N E B (cb : audit_prepare_callback_model N E B)
    nodes initial node_budget out_budget target_budget limit :
  (forall node, In node nodes -> out_budget node <= limit) ->
  (forall node edge, In node nodes -> In edge (fst (audit_prepare_out_model cb node)) ->
    target_budget edge <= limit /\
    node_budget (fst (audit_prepare_target_model cb edge)) <= limit) ->
  Forall (fun event => audit_prepare_source_event_budget node_budget out_budget target_budget event
    <= limit) (snd (audit_prepare_source_in cb nodes initial)).
Proof.
  intros Hnodes Hedges; induction nodes as [|node rest IH]; cbn [audit_prepare_source_in].
  - repeat constructor; cbn; lia.
  - specialize (IH (fun n Hin => Hnodes n (or_intror Hin))
      (fun n e Hin Hedge => Hedges n e (or_intror Hin) Hedge)).
    destruct (audit_prepare_source_in cb rest initial) as [middle events] eqn:Hrest; cbn in IH.
    pose proof (Hnodes node (or_introl eq_refl)) as Hnode.
    pose proof (Hedges node) as Hedge.
    destruct (audit_prepare_out_model cb node) as [out body] eqn:Hout; cbn in Hedge.
    pose proof (audit_walk_prepare_edges_budget N E B cb out middle node_budget out_budget
      target_budget limit (fun edge Hin => Hedge edge (or_introl eq_refl) Hin)) as Hnext.
    destruct (audit_prepare_source_edges cb out middle) as [result calls]; cbn in Hnext.
    cbn [snd].
    constructor; [cbn; lia|].
    repeat rewrite Forall_app; repeat split; try exact IH; try exact Hnext.
    repeat constructor; cbn; lia.
Qed.

(** The final edge-count pass charges only output callbacks for listed nodes. *)
Lemma audit_walk_prepare_count_budget N E B (cb : audit_prepare_callback_model N E B)
    nodes node_budget out_budget target_budget limit :
  (forall node, In node nodes -> out_budget node <= limit) ->
  Forall (fun event => audit_prepare_source_event_budget node_budget out_budget target_budget event
    <= limit) (snd (audit_prepare_source_edge_count cb nodes)).
Proof.
  intro Hnodes; induction nodes as [|node rest IH]; cbn [audit_prepare_source_edge_count].
  - repeat constructor; cbn; lia.
  - specialize (IH (fun n Hin => Hnodes n (or_intror Hin))).
    destruct (audit_prepare_source_edge_count cb rest) as [count events]; cbn in IH.
    destruct (audit_prepare_out_model cb node) as [out body].
    cbn [snd]; constructor; [cbn; lia|].
    apply Forall_app; split; [exact IH|].
    repeat constructor; cbn; try lia; apply Hnodes; now left.
Qed.

(** A target occurrence contributes both its callback and returned-node budgets. *)
Lemma audit_walk_target_budget_member N E TE (target : E -> N * list TE)
    node_budget target_budget edges edge :
  In edge edges ->
  target_budget edge + node_budget (fst (target edge)) <=
    audit_snapshot_target_input_budget target node_budget target_budget edges.
Proof.
  induction edges as [|head rest IH]; cbn; [contradiction|].
  intros [Heq|Hin].
  - subst head; lia.
  - specialize (IH Hin); lia.
Qed.

(** Each listed node's own budgets occur in the graph input envelope. *)
Lemma audit_walk_node_budget_member N E OE TE (out : N -> list E * list OE)
    (target : E -> N * list TE) node_budget out_budget target_budget nodes node :
  In node nodes ->
  node_budget node + out_budget node <=
    audit_snapshot_graph_input_budget out target node_budget out_budget target_budget nodes.
Proof.
  induction nodes as [|head rest IH]; cbn; [contradiction|].
  intros [Heq|Hin].
  - subst head; lia.
  - specialize (IH Hin); lia.
Qed.

(** Every outgoing edge occurrence contributes its target and returned-node budgets. *)
Lemma audit_walk_edge_budget_member N E OE TE (out : N -> list E * list OE)
    (target : E -> N * list TE) node_budget out_budget target_budget nodes node edge :
  In node nodes -> In edge (fst (out node)) ->
  target_budget edge + node_budget (fst (target edge)) <=
    audit_snapshot_graph_input_budget out target node_budget out_budget target_budget nodes.
Proof.
  induction nodes as [|head rest IH]; cbn; [contradiction|].
  intros [Heq|Hin] Hedge.
  - subst head.
    pose proof (audit_walk_target_budget_member N E TE target node_budget target_budget
      (fst (out node)) edge Hedge); lia.
  - specialize (IH Hin Hedge); lia.
Qed.

(** The graph envelope bounds every callback budget on the actual preparation trace. *)
Lemma audit_walk_prepare_events_budget N E CN OE TE (EN : encoding N) (g : Graph.t N E)
    (node_enc : N -> positive * list CN) (out : N -> list E * list OE)
    (target : E -> N * list TE) node_budget out_budget target_budget :
  let cb := audit_snapshot_graph_callbacks node_enc out target in
  let limit := audit_snapshot_graph_input_budget out target node_budget out_budget target_budget
    (Graph.nodes g) in
  Forall (fun event => audit_prepare_source_event_budget node_budget out_budget target_budget event
    <= limit) (snd (audit_prepare_source_counted EN g cb)).
Proof.
  cbn zeta.
  set (cb := audit_snapshot_graph_callbacks node_enc out target).
  set (limit := audit_snapshot_graph_input_budget out target node_budget out_budget target_budget
    (Graph.nodes g)).
  assert (Hnodes : forall node, In node (Graph.nodes g) ->
    node_budget node <= limit /\ out_budget node <= limit).
  { intros node Hin.
    pose proof (audit_walk_node_budget_member N E OE TE out target node_budget out_budget
      target_budget (Graph.nodes g) node Hin); unfold limit; lia. }
  assert (Hedges : forall node edge, In node (Graph.nodes g) ->
    In edge (fst (audit_prepare_out_model cb node)) ->
    target_budget edge <= limit /\ node_budget (fst (audit_prepare_target_model cb edge)) <= limit).
  { intros node edge Hin Hedge.
    unfold cb, audit_snapshot_graph_callbacks in Hedge |- *; cbn in Hedge |- *.
    destruct (out node) as [edges body] eqn:Hout; cbn in Hedge.
    destruct (target edge) as [destination target_body] eqn:Htarget; cbn.
    pose proof (audit_walk_edge_budget_member N E OE TE out target node_budget out_budget
      target_budget (Graph.nodes g) node edge Hin) as Hbound.
    rewrite Hout in Hbound; cbn in Hbound; specialize (Hbound Hedge).
    rewrite Htarget in Hbound; cbn in Hbound; unfold limit; lia. }
  pose proof (audit_walk_prepare_out_budget N E _ cb (Graph.nodes g) Map.empty node_budget
    out_budget target_budget limit Hnodes) as Hout.
  pose proof (audit_walk_prepare_in_budget N E _ cb (Graph.nodes g) Map.empty node_budget
    out_budget target_budget limit (fun n Hin => proj2 (Hnodes n Hin)) Hedges) as Hin.
  pose proof (audit_walk_prepare_count_budget N E _ cb (Graph.nodes g) node_budget out_budget
    target_budget limit (fun n Hin => proj2 (Hnodes n Hin))) as Hcount.
  unfold audit_prepare_source_counted.
  destruct (audit_prepare_source_out cb (Graph.nodes g) Map.empty) as [out_rows out_events].
  destruct (audit_prepare_source_in cb (Graph.nodes g) Map.empty) as [in_rows in_events].
  destruct (audit_prepare_source_edge_count cb (Graph.nodes g)) as [count count_events].
  cbn [snd] in Hout, Hin, Hcount |- *.
  repeat rewrite Forall_app; repeat split; try assumption; repeat constructor; cbn; lia.
Qed.

(** A list of bounded event budgets is bounded by its length times the common envelope. *)
Lemma audit_walk_prepare_budget_sum N E B node_budget out_budget target_budget limit
    (events : list (audit_prepare_source_event N E B)) :
  Forall (fun event => audit_prepare_source_event_budget node_budget out_budget target_budget event
    <= limit) events ->
  fold_right (fun event total =>
    audit_prepare_source_event_budget node_budget out_budget target_budget event + total)
    0 events <=
  length events * limit.
Proof.
  intro Hbound; induction Hbound as [|event rest Hhead Hrest IH]; cbn; nia.
Qed.

(** Graph preparation charges only the bodies returned by its actual external calls. *)
Lemma audit_walk_prepare_source_bound N E CN OE TE (EN : encoding N) (g : Graph.t N E)
    (node_enc : N -> positive * list CN) (out : N -> list E * list OE)
    (target : E -> N * list TE) node_work out_work target_work node_budget out_budget
    target_budget :
  (forall n, fst (node_enc n) = encode EN n) ->
  (forall n, fst (out n) = Graph.out g n) ->
  (forall e, fst (target e) = Graph.target g e) ->
  (forall n, node_work (snd (node_enc n)) <= node_budget n) ->
  (forall n, out_work (snd (out n)) <= out_budget n) ->
  (forall e, target_work (snd (target e)) <= target_budget e) ->
  audit_prepare_source_work (audit_snapshot_graph_body_work node_work out_work target_work)
    (snd (audit_prepare_source_counted EN g
      (audit_snapshot_graph_callbacks node_enc out target))) <=
  audit_prepare_source_budget EN g + audit_graph_prepare_full_event_bound g *
    audit_snapshot_graph_input_budget out target node_budget out_budget target_budget
      (Graph.nodes g).
Proof.
  intros Hnode Hout Htarget Hnodework Houtwork Htargetwork.
  set (cb := audit_snapshot_graph_callbacks node_enc out target).
  set (weight := audit_snapshot_graph_body_work node_work out_work target_work).
  assert (Hcallbacks : audit_prepare_callbacks_erase EN g cb).
  { unfold cb; apply audit_walk_callbacks_erases; assumption. }
  assert (Hnode_adapter : audit_graph_external_callback_adapter (audit_prepare_encode_model cb)
    weight (fun _ _ _ _ => True) node_budget).
  { constructor; intros n code body Hcall.
    unfold cb, audit_snapshot_graph_callbacks in Hcall; cbn in Hcall.
    specialize (Hnodework n).
    destruct (node_enc n) as [actual events]; cbn in Hnodework, Hcall.
    inversion Hcall; subst; unfold weight; cbn [fold_right audit_snapshot_graph_body_work];
      split; [exact I|lia]. }
  assert (Hout_adapter : audit_graph_external_callback_adapter (audit_prepare_out_model cb)
    weight (fun _ _ _ _ => True) out_budget).
  { constructor; intros n edges body Hcall.
    unfold cb, audit_snapshot_graph_callbacks in Hcall; cbn in Hcall.
    specialize (Houtwork n).
    destruct (out n) as [actual events]; cbn in Houtwork, Hcall.
    inversion Hcall; subst; unfold weight; cbn [fold_right audit_snapshot_graph_body_work];
      split; [exact I|lia]. }
  assert (Htarget_adapter : audit_graph_external_callback_adapter (audit_prepare_target_model cb)
    weight (fun _ _ _ _ => True) target_budget).
  { constructor; intros e node body Hcall.
    unfold cb, audit_snapshot_graph_callbacks in Hcall; cbn in Hcall.
    specialize (Htargetwork e).
    destruct (target e) as [actual events]; cbn in Htargetwork, Hcall.
    inversion Hcall; subst; unfold weight; cbn [fold_right audit_snapshot_graph_body_work];
      split; [exact I|lia]. }
  pose proof (audit_prepare_source_with_receipts N E _ EN g cb weight Hcallbacks) as Hrun.
  pose proof (audit_walk_prepare_events_budget N E CN OE TE EN g node_enc out target node_budget
    out_budget target_budget) as Hevents.
  change (Forall (fun event =>
    audit_prepare_source_event_budget node_budget out_budget target_budget event <=
    audit_snapshot_graph_input_budget out target node_budget out_budget target_budget
      (Graph.nodes g))
    (snd (audit_prepare_source_counted EN g cb))) in Hevents.
  destruct (audit_prepare_source_counted EN g cb) as [result events] eqn:Hprepare.
  cbn [snd] in Hrun, Hevents |- *.
  destruct Hrun as [_ [Hlength [Hwork Hreceipts]]].
  pose proof (audit_source_receipts_body_bound N E _ cb weight
    (fun _ _ _ _ => True) (fun _ _ _ _ => True) (fun _ _ _ _ => True)
    node_budget out_budget target_budget events Hnode_adapter Hout_adapter Htarget_adapter
    Hreceipts)
    as Hbody.
  pose proof (audit_walk_prepare_budget_sum N E _ node_budget out_budget target_budget
    (audit_snapshot_graph_input_budget out target node_budget out_budget target_budget
      (Graph.nodes g))
    events Hevents) as Hsum.
  nia.
Qed.

(** A predecessor read pays for the concrete encoded-node map lookup. *)
Lemma audit_walk_predecessors_work_bound N E CN (node_enc : N -> positive * list CN)
    node_work node_budget (rows : Map.t N (list E)) node :
  node_work (snd (node_enc node)) <= node_budget node ->
  audit_map_source_work node_work (snd (audit_walk_predecessors node_enc rows node)) <=
    audit_walk_predecessor_input_budget node_enc node_budget node.
Proof.
  intro Hnode.
  pose proof (audit_map_get_source_work_bound N (list E) CN node_enc node_work node rows) as Hread.
  unfold audit_walk_predecessors, audit_walk_predecessor_input_budget.
  destruct (audit_map_get node_enc node rows) as [found calls]; cbn [snd] in Hread |- *.
  lia.
Qed.

(** Adjacency construction is bounded using only its external input budgets. *)
Theorem audit_memory_walk_index_whole_input_bound :
  audit_memory_walk_index_whole_input_bound_statement.
Proof.
  intros N E T CN CE SE OE TE FE PE BE EN node_enc edge_enc site_enc out target effects operand
    before node_work edge_work site_work out_work target_work effect_work operand_work before_work
    node_budget edge_budget site_budget out_budget target_budget effect_budget operand_budget
    before_budget g mg scope Hnode Hout Htarget Hnodework Hedgework Hsitework Houtwork Htargetwork
    Heffectwork Hoperandwork Hbeforework.
  pose proof (audit_memory_table_whole_input_bound N E T CE OE FE edge_enc out effects edge_work
    out_work effect_work edge_budget out_budget effect_budget (Graph.nodes g) Hedgework Houtwork
    Heffectwork) as Htable.
  pose proof (audit_walk_prepare_source_bound N E CN OE TE EN g node_enc out target node_work
    out_work target_work node_budget out_budget target_budget Hnode Hout Htarget Hnodework Houtwork
    Htargetwork) as Hprepare.
  set (enc := audit_memory_version_encode node_enc edge_enc).
  set (key_work := @audit_memory_version_work N E CN CE node_work edge_work).
  set (key_budget := audit_memory_version_input_budget node_enc edge_enc node_budget edge_budget).
  set (table := fst (audit_memory_effect_table edge_enc out effects (Graph.nodes g))).
  set (base := fst (audit_prepare_source_counted EN g
    (audit_snapshot_graph_callbacks node_enc out target))).
  set (incoming := audit_walk_predecessors node_enc (in_index base)).
  set (incoming_budget := audit_walk_predecessor_input_budget node_enc node_budget).
  set (value := audit_memory_raw_next edge_enc site_enc table incoming operand before scope).
  set (value_work := @audit_raw_next_source_work N E T CE SE (audit_map_event N (list E) CN) PE BE
    edge_work site_work (audit_map_source_work node_work) operand_work before_work).
  set (value_budget := @audit_raw_next_input_budget N E T CE SE (audit_map_event N (list E) CN)
    PE BE edge_enc site_enc table incoming before edge_budget site_budget incoming_budget
    operand_budget before_budget scope).
  assert (Hkey : forall v, key_work (snd (enc v)) <= key_budget v).
  { intro v; unfold key_work, enc, key_budget.
    apply audit_memory_version_input_bound; assumption. }
  assert (Hincoming : forall n, audit_map_source_work node_work (snd (incoming n)) <=
    incoming_budget n).
  { intro n; unfold incoming, incoming_budget.
    apply audit_walk_predecessors_work_bound, Hnodework. }
  assert (Hvalue : forall v, value_work (snd (value v)) <= value_budget v).
  { intro v; unfold value_work, value, value_budget.
    apply audit_raw_next_whole_input_bound; assumption. }
  pose proof (audit_memory_result_index_work_bound (memory_version N E) (list (memory_version N E))
    _ _ enc value key_work value_work (memory_versions mg)) as Hindex.
  pose proof (audit_memory_index_budget_input (memory_version N E) (list (memory_version N E)) _ _
    enc value key_work value_work key_budget value_budget (memory_versions mg) Hkey Hvalue)
    as Hbudget.
  unfold audit_memory_walk_index_counted, audit_memory_walk_index_source_work,
    audit_memory_walk_index_input_budget.
  destruct (audit_memory_effect_table edge_enc out effects (Graph.nodes g)) as [actual_table te]
    eqn:Htable_run.
  destruct (audit_prepare_source_counted EN g (audit_snapshot_graph_callbacks node_enc out target))
    as [actual_base pe] eqn:Hprepare_run.
  destruct (audit_memory_result_index enc value (memory_versions mg)) as [rows ie] eqn:Hindex_run.
  cbn [snd] in Htable, Hprepare, Hindex.
  cbn [audit_walk_index_table audit_walk_index_prepare audit_walk_index_rows fst].
  unfold enc, value, incoming, table, base in Hindex_run; cbn [fst] in Hindex_run.
  rewrite Hindex_run; cbn [audit_walk_index_table audit_walk_index_prepare audit_walk_index_rows].
  unfold enc, value, incoming, table, base, key_work, value_work, key_budget, value_budget,
    incoming_budget in Hindex, Hbudget; cbn [fst] in Hindex, Hbudget.
  unfold table, incoming, base in Hbudget; cbn [fst] in Hbudget.
  lia.
Qed.
