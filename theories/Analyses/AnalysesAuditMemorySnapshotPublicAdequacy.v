(** * Public saved snapshot semantics

    Saved queries preserve their full memo invariant and interpret epoch reuse by observations.
    For example, matching epochs reuse the saved graph while equal observations transport traces.
    Builds on: concrete memo query semantics and complete snapshot source adequacy. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Graph Require Import GraphCore.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryWalk
  AnalysesAuditMemoryState AnalysesAuditMemoryStateAdequacy AnalysesAuditMemoryMemoExecute
  AnalysesAuditMemoryMemoExecuteAdequacy AnalysesAuditMemoryMemoSnapshot
  AnalysesAuditMemoryMemoSnapshotSource AnalysesAuditMemoryMemoSnapshotSourceAdequacy
  AnalysesAuditMemorySnapshotPublic.
Import List.ListNotations.

(** * Plain public operations *)

(** Complete source refresh and plain refresh select the same exact saved cache on both branches. *)
Theorem audit_snapshot_refresh_plain_erases : audit_snapshot_refresh_plain_erases_statement.
Proof.
  intros N E T Epoch CE CN OE FE TE EN EE EEpoch epoch_enc node_enc edge_enc out target effects
    old current Hepoch Hnode Hedge Hout Htarget Heffects.
  unfold audit_snapshot_refresh_compute, epoch_matches.
  rewrite <- (Hepoch (snapshot_epoch (audit_cache_snapshot old))),
    <- (Hepoch (snapshot_epoch current)).
  destruct (Pos.eqb (fst (epoch_enc (snapshot_epoch (audit_cache_snapshot old))))
    (fst (epoch_enc (snapshot_epoch current)))) eqn:Hmatch.
  - apply audit_snapshot_refresh_source_hit; exact Hmatch.
  - apply (audit_snapshot_refresh_source_miss N E T Epoch CE CN OE FE TE EN EE
      epoch_enc node_enc edge_enc out target effects old current Hmatch
      Hnode Hedge Hout Htarget Heffects).
Qed.

(** A refresh hit retains validity and a miss reconstructs the valid empty initial memo. *)
Theorem audit_snapshot_refresh_semantic_valid : audit_snapshot_refresh_semantic_valid_statement.
Proof.
  intros N E T Epoch EN EE ET EEpoch old current Hvalid.
  unfold audit_snapshot_refresh_compute.
  destruct (epoch_matches EEpoch (snapshot_epoch (audit_cache_snapshot old)) (snapshot_epoch
    current));
    [exact Hvalid|].
  apply (AnalysesAuditMemoryStateAdequacy.memo_initial N E T EN EE ET
    (snapshot_graph current) (snapshot_effects current) (snapshot_memory current)).
Qed.

(** A valid saved query preserves its full completed-entry semantics and exact saved indexes. *)
Theorem audit_snapshot_query_semantic_valid : audit_snapshot_query_semantic_valid_statement.
Proof.
  intros N E T Epoch EN EE ET cache scope start fuel; cbn zeta; intros Hvalid Hwf Hstart.
  pose proof (proj1 (audit_memory_memo_query_correct N E T EN EE ET
    (snapshot_graph (audit_cache_snapshot cache)) (snapshot_effects (audit_cache_snapshot cache))
    (snapshot_memory (audit_cache_snapshot cache)) (audit_snapshot_saved_state EN cache)
    scope start fuel Hvalid Hwf Hstart)) as Hfinal.
  unfold audit_snapshot_query, audit_memory_memo_query.
  cbn zeta; split; [exact Hfinal|repeat split; reflexivity].
Qed.

(** Every saved terminal or cyclic trace intersects the exact saved-query roots. *)
Theorem audit_snapshot_query_coverage : audit_snapshot_query_coverage_statement.
Proof.
  intros N E T Epoch EN EE ET cache scope start fuel; cbn zeta; intros Hvalid Hwf Hstart.
  pose proof (proj2 (audit_memory_memo_query_correct N E T EN EE ET
    (snapshot_graph (audit_cache_snapshot cache)) (snapshot_effects (audit_cache_snapshot cache))
    (snapshot_memory (audit_cache_snapshot cache)) (audit_snapshot_saved_state EN cache)
    scope start fuel Hvalid Hwf Hstart)) as [_ [_ Hcoverage]].
  exact Hcoverage.
Qed.

(** A complete saved query contains exactly the saved snapshot's reachable terminal roots. *)
Theorem audit_snapshot_query_complete : audit_snapshot_query_complete_statement.
Proof.
  intros N E T Epoch EN EE ET cache scope start fuel; cbn zeta; intros Hvalid Hwf Hstart.
  cbn zeta; intro Hcomplete.
  pose proof (proj2 (audit_memory_memo_query_correct N E T EN EE ET
    (snapshot_graph (audit_cache_snapshot cache)) (snapshot_effects (audit_cache_snapshot cache))
    (snapshot_memory (audit_cache_snapshot cache)) (audit_snapshot_saved_state EN cache)
    scope start fuel Hvalid Hwf Hstart)) as [_ [Hresult Hcoverage]].
  exact (proj2 (Hresult Hcomplete)).
Qed.

(** * Pointwise observation transport *)

(** Graph observation equality is symmetric without identifying callback functions. *)
Lemma audit_snapshot_graph_observations_sym N E (g h : Graph.t N E) :
  graph_observations_equal g h -> graph_observations_equal h g.
Proof.
  intros [Hentries [Hnodes [Hout Hends]]].
  split; [symmetry; exact Hentries|]; split; [symmetry; exact Hnodes|]; split.
  - intro node; symmetry; apply Hout.
  - intro edge; destruct (Hends edge) as [Hsource Htarget]; split; symmetry; assumption.
Qed.

(** Memory observation equality is symmetric at every queried node, edge and occurrence. *)
Lemma audit_snapshot_memory_observations_sym N E (old current : memory_graph N E) :
  memory_observations_equal old current -> memory_observations_equal current old.
Proof.
  intros [Hphis [Hversions [Hin [Hbefore [Hout Hoperand]]]]].
  split; [symmetry; exact Hphis|]; split; [symmetry; exact Hversions|].
  split; [intro node; symmetry; apply Hin|].
  split; [intros edge index; symmetry; apply Hbefore|].
  split; [intro edge; symmetry; apply Hout|].
  intros node key; symmetry; apply Hoperand.
Qed.

(** Equal graph observations transport each actual reachability derivation. *)
Lemma audit_snapshot_reachable_transport N E (g h : Graph.t N E) :
  graph_observations_equal g h -> forall node, reachable g node -> reachable h node.
Proof.
  intros [Hentries [Hnodes [Hout Hends]]] node Hreach.
  induction Hreach as [node Hin|edge Hreach IH Hedge].
  - constructor; rewrite <- Hentries; exact Hin.
  - rewrite (proj2 (Hends edge)); apply reachable_step.
    + rewrite <- (proj1 (Hends edge)); exact IH.
    + rewrite <- (proj1 (Hends edge)), <- Hout; exact Hedge.
Qed.

(** Equal graph observations preserve reachability in both directions. *)
Lemma audit_snapshot_reachable_agrees N E (g h : Graph.t N E) :
  graph_observations_equal g h -> forall node, reachable g node <-> reachable h node.
Proof.
  intros Hgraph node; split.
  - apply audit_snapshot_reachable_transport; exact Hgraph.
  - apply audit_snapshot_reachable_transport; apply audit_snapshot_graph_observations_sym; exact
    Hgraph.
Qed.

(** Equal graph observations preserve all graph well-formedness fields pointwise. *)
Lemma audit_snapshot_graph_wf_transport N E (g h : Graph.t N E) :
  graph_observations_equal g h -> graph_wf g -> graph_wf h.
Proof.
  intros [Hentries [Hnodes [Hout Hends]]] Hwf; constructor.
  - rewrite <- Hnodes; exact (nodes_nodup Hwf).
  - intros node Hin; rewrite <- Hnodes; apply (entries_in Hwf).
    rewrite Hentries; exact Hin.
  - intros node edge Hin; rewrite <- (proj1 (Hends edge)).
    apply (out_source Hwf); rewrite Hout; exact Hin.
  - intros node edge Hnode Hedge; rewrite <- Hnodes, <- (proj2 (Hends edge)).
    apply (out_target_in Hwf node edge); [rewrite Hnodes|rewrite Hout]; assumption.
Qed.

(** An occurrence keeps the same edge, index and effect under pointwise snapshot observations. *)
Lemma audit_snapshot_occurrence_agrees N E T (g h : Graph.t N E)
    (effects effects' : E -> list (memory_effect T)) :
  graph_observations_equal g h -> (forall edge, effects edge = effects' edge) ->
  forall edge index effect,
    memory_occurrence g effects edge index effect <-> memory_occurrence h effects' edge index
      effect.
Proof.
  intros Hgraph Heffects edge index effect.
  destruct Hgraph as [Hentries [Hnodes [Hout Hends]]].
  unfold memory_occurrence.
  rewrite (proj1 (Hends edge)), Hout, Heffects.
  rewrite (audit_snapshot_reachable_agrees N E g h
    (conj Hentries (conj Hnodes (conj Hout Hends))) (Graph.source h edge)); tauto.
Qed.

(** Valid versions retain their identical live, phi or edge-occurrence witnesses. *)
Lemma audit_snapshot_valid_version_agrees N E T (g h : Graph.t N E)
    (effects effects' : E -> list (memory_effect T)) (memory memory' : memory_graph N E) :
  graph_observations_equal g h -> (forall edge, effects edge = effects' edge) ->
  memory_observations_equal memory memory' -> forall version,
  memory_valid_version g effects memory version <-> memory_valid_version h effects' memory' version.
Proof.
  intros Hgraph Heffects [Hphis Hmemory] [|node|edge index]; cbn [memory_valid_version].
  - tauto.
  - unfold memory_phi_at; rewrite Hphis, (audit_snapshot_reachable_agrees N E g h Hgraph node);
    tauto.
  - split; intros [effect [Hoc Hdef]]; exists effect; split; [|exact Hdef| |exact Hdef].
    + apply (audit_snapshot_occurrence_agrees N E T g h effects effects' Hgraph Heffects); exact
      Hoc.
    + apply (audit_snapshot_occurrence_agrees N E T g h effects effects' Hgraph Heffects); exact
      Hoc.
Qed.

(** Arrival observations retain the actual phi operand and node input. *)
Lemma audit_snapshot_arrival_agrees N E (memory memory' : memory_graph N E) :
  memory_observations_equal memory memory' -> forall node key version,
  memory_arrival memory node key version <-> memory_arrival memory' node key version.
Proof.
  intros [Hphis [Hversions [Hin [Hbefore [Hout Hoperand]]]]] node key version.
  unfold memory_arrival, memory_phi_at; rewrite Hphis, Hin, Hoperand; tauto.
Qed.

(** Equal before lookups transport the complete ordered flow through an edge's effect list. *)
Lemma audit_snapshot_edge_flow_transport N E T (memory memory' : memory_graph N E) :
  memory_observations_equal memory memory' -> forall edge index effects input output,
  @memory_edge_flow N E T memory edge index effects input output ->
  memory_edge_flow memory' edge index effects input output.
Proof.
  intros [Hphis [Hversions [Hin [Hbefore [Hout Hoperand]]]]] edge index effects input output Hflow.
  induction Hflow as [index version|index effect rest version last Hlookup Hflow IH].
  - constructor.
  - constructor; [rewrite <- Hbefore; exact Hlookup|exact IH].
Qed.

(** Edge flow and arrival retain the same effect sequence and actual endpoint observations. *)
Lemma audit_snapshot_memory_edges_transport N E T (g h : Graph.t N E)
    (effects effects' : E -> list (memory_effect T)) (memory memory' : memory_graph N E) :
  graph_observations_equal g h -> (forall edge, effects edge = effects' edge) ->
  memory_observations_equal memory memory' -> memory_graph_wf g effects memory ->
  (forall edge, In edge (Graph.out h (Graph.source h edge)) -> reachable h (Graph.source h edge) ->
    memory_edge_flow memory' edge 0 (effects' edge) (memory_in memory' (Graph.source h edge))
      (memory_out memory' edge)) /\
  (forall edge, In edge (Graph.out h (Graph.source h edge)) -> reachable h (Graph.source h edge) ->
    memory_arrival memory' (Graph.target h edge) (Some edge) (memory_out memory' edge)).
Proof.
  intros Hgraph Heffects Hmemory Hwf.
  pose proof (audit_snapshot_graph_observations_sym N E g h Hgraph) as Hgraph'.
  destruct Hgraph as [Hentries [Hnodes [Hout Hends]]].
  destruct Hmemory as [Hphis [Hversions [Hin [Hbefore [Hmemout Hoperand]]]]].
  assert (Hmemory : memory_observations_equal memory memory')
    by exact (conj Hphis (conj Hversions (conj Hin (conj Hbefore (conj Hmemout Hoperand))))).
  split; intros edge Hedge Hreach.
  - rewrite <- Heffects, <- Hin, <- Hmemout, <- (proj1 (Hends edge)).
    apply (audit_snapshot_edge_flow_transport N E T memory memory' Hmemory).
    apply (memory_edges_flow Hwf).
    + rewrite Hout, (proj1 (Hends edge)); exact Hedge.
    + apply (audit_snapshot_reachable_transport N E h g Hgraph').
      rewrite (proj1 (Hends edge)); exact Hreach.
  - rewrite <- Hmemout, <- (proj2 (Hends edge)).
    apply (audit_snapshot_arrival_agrees N E memory memory' Hmemory).
    apply (memory_edges_arrive Hwf).
    + rewrite Hout, (proj1 (Hends edge)); exact Hedge.
    + apply (audit_snapshot_reachable_transport N E h g Hgraph').
      rewrite (proj1 (Hends edge)); exact Hreach.
Qed.

(** All local memory-graph laws transport through pointwise graph and memory observations. *)
Lemma audit_snapshot_memory_wf_transport N E T (g h : Graph.t N E)
    (effects effects' : E -> list (memory_effect T)) (memory memory' : memory_graph N E) :
  graph_observations_equal g h -> (forall edge, effects edge = effects' edge) ->
  memory_observations_equal memory memory' ->
  memory_graph_wf g effects memory -> memory_graph_wf h effects' memory'.
Proof.
  intros Hgraph Heffects Hmemory Hwf.
  pose proof (audit_snapshot_memory_edges_transport N E T g h effects effects' memory memory'
    Hgraph Heffects Hmemory Hwf) as [Hflow Harrival].
  pose proof (audit_snapshot_graph_observations_sym N E g h Hgraph) as Hgraph'.
  pose proof (audit_snapshot_memory_observations_sym N E memory memory' Hmemory) as Hmemory'.
  destruct Hgraph as [Hentries [Hnodes [Hout Hends]]].
  destruct Hmemory as [Hphis [Hversions [Hin [Hbefore [Hmemout Hoperand]]]]].
  assert (Hgraph : graph_observations_equal g h)
    by exact (conj Hentries (conj Hnodes (conj Hout Hends))).
  assert (Hmemory : memory_observations_equal memory memory')
    by exact (conj Hphis (conj Hversions (conj Hin (conj Hbefore (conj Hmemout Hoperand))))).
  constructor.
  - apply (audit_snapshot_graph_wf_transport N E g h Hgraph); exact (memory_cfg_wf Hwf).
  - rewrite <- Hphis; exact (memory_phis_nodup Hwf).
  - intros node Hphi; apply (audit_snapshot_reachable_transport N E g h Hgraph).
    apply (memory_phi_reachable Hwf); unfold memory_phi_at in *; rewrite Hphis; exact Hphi.
  - rewrite <- Hversions; exact (memory_versions_nodup Hwf).
  - intro version; rewrite <- Hversions, (memory_versions_exact Hwf).
    apply audit_snapshot_valid_version_agrees; assumption.
  - intros node Hentry; apply (audit_snapshot_arrival_agrees N E memory memory' Hmemory).
    apply (memory_entries_arrive Hwf); rewrite Hentries; exact Hentry.
  - exact Hflow.
  - exact Harrival.
  - intros node Hreach; rewrite <- Hin.
    apply (audit_snapshot_valid_version_agrees N E T g h effects effects' memory memory'
      Hgraph Heffects Hmemory).
    apply (memory_in_valid Hwf); apply (audit_snapshot_reachable_transport N E h g Hgraph'); exact
      Hreach.
  - intros edge Hedge Hreach; rewrite <- Hmemout.
    apply (audit_snapshot_valid_version_agrees N E T g h effects effects' memory memory'
      Hgraph Heffects Hmemory).
    apply (memory_out_valid Hwf).
    + rewrite Hout, (proj1 (Hends edge)); exact Hedge.
    + apply (audit_snapshot_reachable_transport N E h g Hgraph').
      rewrite (proj1 (Hends edge)); exact Hreach.
  - intros edge index; rewrite <- Hbefore, (memory_before_domain Hwf).
    split; intros [effect Hoc]; exists effect.
    + apply (audit_snapshot_occurrence_agrees N E T g h effects effects' Hgraph Heffects); exact
      Hoc.
    + apply (audit_snapshot_occurrence_agrees N E T g h effects effects' Hgraph Heffects); exact
      Hoc.
  - intros node key; rewrite <- Hoperand, (memory_operand_domain Hwf).
    unfold memory_phi_at; rewrite Hphis.
    destruct key as [edge|]; [|rewrite Hentries; tauto].
    rewrite (proj1 (Hends edge)), Hout, (proj2 (Hends edge)).
    rewrite (audit_snapshot_reachable_agrees N E g h Hgraph (Graph.source h edge)); tauto.
Qed.

(** Equal effects and memory observations transport each exact backward transition. *)
Lemma audit_snapshot_next_agrees N E T (ET : encoding T)
    (effects effects' : E -> list (memory_effect T)) (memory memory' : memory_graph N E) :
  (forall edge, effects edge = effects' edge) -> memory_observations_equal memory memory' ->
  forall scope start next,
  memory_walk_next ET effects memory scope start next <->
  memory_walk_next ET effects' memory' scope start next.
Proof.
  intros Heffects [Hphis [Hversions [Hin [Hbefore [Hout Hoperand]]]]] scope start next; split;
    intro Hstep; destruct Hstep as [edge index effect previous Hnth Hdef Hclear Hprevious|
      node key previous Hget].
  - eapply memory_walk_skip_def; try eassumption; [rewrite <- Heffects|rewrite <- Hbefore];
    assumption.
  - eapply memory_walk_phi; rewrite <- Hoperand; exact Hget.
  - eapply memory_walk_skip_def; try eassumption; [rewrite Heffects|rewrite Hbefore]; assumption.
  - eapply memory_walk_phi; rewrite Hoperand; exact Hget.
Qed.

(** Pointwise observation transport preserves the complete trace list, including repeated versions.
    *)
Lemma audit_snapshot_trace_agrees N E T (ET : encoding T)
    (effects effects' : E -> list (memory_effect T)) (memory memory' : memory_graph N E) :
  (forall edge, effects edge = effects' edge) -> memory_observations_equal memory memory' ->
  forall scope start trace,
  memory_walk_trace ET effects memory scope start trace <->
  memory_walk_trace ET effects' memory' scope start trace.
Proof.
  intros Heffects Hmemory scope start trace; split; intro Htrace;
    induction Htrace as [v|v w rest Hstep Htrace IH].
  - constructor.
  - econstructor; [apply (audit_snapshot_next_agrees N E T ET effects effects' memory memory'
      Heffects Hmemory); exact Hstep|exact IH].
  - constructor.
  - econstructor; [apply (audit_snapshot_next_agrees N E T ET effects effects' memory memory'
      Heffects Hmemory); exact Hstep|exact IH].
Qed.

(** Terminality depends only on the transported exact successor relation. *)
Lemma audit_snapshot_terminal_agrees N E T (ET : encoding T)
    (effects effects' : E -> list (memory_effect T)) (memory memory' : memory_graph N E) :
  (forall edge, effects edge = effects' edge) -> memory_observations_equal memory memory' ->
  forall scope version,
  memory_walk_terminal ET effects memory scope version <->
  memory_walk_terminal ET effects' memory' scope version.
Proof.
  intros Heffects Hmemory scope version; split; intros Hterminal next Hstep; apply (Hterminal next);
    apply (audit_snapshot_next_agrees N E T ET effects effects' memory memory' Heffects Hmemory);
    exact Hstep.
Qed.

(** * Epoch interpretation *)

(** Matching injective epoch codes activate exactly the stated snapshot-domain observation law. *)
Lemma audit_snapshot_epoch_observations N E T Epoch (EEpoch : encoding Epoch)
    (domain : memo_snapshot N E T Epoch -> Prop) old current :
  memo_epoch_laws domain -> domain old -> domain current ->
  epoch_matches EEpoch (snapshot_epoch old) (snapshot_epoch current) = true ->
  graph_observations_equal (snapshot_graph old) (snapshot_graph current) /\
  (forall edge, snapshot_effects old edge = snapshot_effects current edge) /\
  memory_observations_equal (snapshot_memory old) (snapshot_memory current).
Proof.
  intros Hlaws Hold Hcurrent Hmatch.
  apply (epoch_equal_observations domain Hlaws old current Hold Hcurrent).
  apply (encode_injective EEpoch); apply Pos.eqb_eq; exact Hmatch.
Qed.

(** Current well-formedness and valid starts transport back to the saved snapshot pointwise. *)
Lemma audit_snapshot_saved_domain N E T Epoch (old current : memo_snapshot N E T Epoch) start :
  graph_observations_equal (snapshot_graph old) (snapshot_graph current) ->
  (forall edge, snapshot_effects old edge = snapshot_effects current edge) ->
  memory_observations_equal (snapshot_memory old) (snapshot_memory current) ->
  memory_graph_wf (snapshot_graph current) (snapshot_effects current) (snapshot_memory current) ->
  memory_valid_version (snapshot_graph current) (snapshot_effects current) (snapshot_memory current)
    start ->
  memory_graph_wf (snapshot_graph old) (snapshot_effects old) (snapshot_memory old) /\
  memory_valid_version (snapshot_graph old) (snapshot_effects old) (snapshot_memory old) start.
Proof.
  intros Hgraph Heffects Hmemory Hwf Hvalid; split.
  - apply (audit_snapshot_memory_wf_transport N E T (snapshot_graph current) (snapshot_graph old)
      (snapshot_effects current) (snapshot_effects old) (snapshot_memory current) (snapshot_memory
        old)).
    + apply audit_snapshot_graph_observations_sym; exact Hgraph.
    + intro edge; symmetry; apply Heffects.
    + apply audit_snapshot_memory_observations_sym; exact Hmemory.
    + exact Hwf.
  - apply (audit_snapshot_valid_version_agrees N E T (snapshot_graph old) (snapshot_graph current)
      (snapshot_effects old) (snapshot_effects current) (snapshot_memory old) (snapshot_memory
        current)
      Hgraph Heffects Hmemory); exact Hvalid.
Qed.

(** Epoch-equivalent current traces intersect the actual saved-query roots with no extra premise. *)
Theorem audit_snapshot_query_current_coverage : audit_snapshot_query_current_coverage_statement.
Proof.
  intros N E T Epoch EN EE ET EEpoch domain cache current scope start fuel
    Hlaws Hold Hcurrent Hmatch Hvalid Hwf Hstart trace last Htrace Hlast Hend.
  destruct (audit_snapshot_epoch_observations N E T Epoch EEpoch domain
    (audit_cache_snapshot cache) current Hlaws Hold Hcurrent Hmatch) as [Hgraph [Heffects Hmemory]].
  destruct (audit_snapshot_saved_domain N E T Epoch (audit_cache_snapshot cache) current start
    Hgraph Heffects Hmemory Hwf Hstart) as [Hsavedwf Hsavedstart].
  apply (audit_snapshot_query_coverage N E T Epoch EN EE ET cache scope start fuel
    Hvalid Hsavedwf Hsavedstart trace last).
  - apply (audit_snapshot_trace_agrees N E T ET _ _ _ _ Heffects Hmemory); exact Htrace.
  - exact Hlast.
  - destruct Hend as [Hterminal|Hrepeat]; [left|right; exact Hrepeat].
    apply (audit_snapshot_terminal_agrees N E T ET _ _ _ _ Heffects Hmemory); exact Hterminal.
Qed.

(** Complete saved roots denote exactly current terminals and traces under the original epoch laws.
    *)
Theorem audit_snapshot_query_current_complete : audit_snapshot_query_current_complete_statement.
Proof.
  intros N E T Epoch EN EE ET EEpoch domain cache current scope start fuel
    Hlaws Hold Hcurrent Hmatch Hvalid Hwf Hstart.
  cbn zeta; intros Hcomplete version.
  destruct (audit_snapshot_epoch_observations N E T Epoch EEpoch domain
    (audit_cache_snapshot cache) current Hlaws Hold Hcurrent Hmatch) as [Hgraph [Heffects Hmemory]].
  destruct (audit_snapshot_saved_domain N E T Epoch (audit_cache_snapshot cache) current start
    Hgraph Heffects Hmemory Hwf Hstart) as [Hsavedwf Hsavedstart].
  rewrite (audit_snapshot_query_complete N E T Epoch EN EE ET cache scope start fuel
    Hvalid Hsavedwf Hsavedstart Hcomplete version).
  rewrite (audit_snapshot_terminal_agrees N E T ET _ _ _ _ Heffects Hmemory scope version).
  split; intros [Hterminal [trace [Htrace Hlast]]]; split; [exact Hterminal| |exact Hterminal|];
    exists trace; split; [|exact Hlast| |exact Hlast].
  - apply (audit_snapshot_trace_agrees N E T ET _ _ _ _ Heffects Hmemory); exact Htrace.
  - apply (audit_snapshot_trace_agrees N E T ET _ _ _ _ Heffects Hmemory); exact Htrace.
Qed.
