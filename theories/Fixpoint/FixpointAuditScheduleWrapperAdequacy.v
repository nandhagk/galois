(** * Adequacy of indexed reverse postorder preparation

    The counted dependency graph retains the index and callback results used by scheduling.
    For example, a reader bucket supplies the targets of its outgoing edges.
    Builds on: FixpointAuditScheduleWrapper, indexed preparation and graph adequacy. *)

From Stdlib Require Import List PArith Lia PeanoNat Permutation.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditTrie CollectionsAuditMap CollectionsAuditFinSet CollectionsAuditElements
  CollectionsAuditEncoding CollectionsAuditCompare
  CollectionsAuditTrieAdequacy CollectionsAuditFinSetAdequacy CollectionsAuditElementsAdequacy.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphAuditBase GraphAuditDfs
  GraphAuditBaseAdequacy GraphAuditDfsAdequacy.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointWorklist FixpointSchedule
  FixpointAuditIndex FixpointAuditIndexAdequacy FixpointAuditSchedule
  FixpointAuditScheduleAdequacy FixpointAuditScheduleWrapper.
Import List.ListNotations.

(** * Dependency graph erasure *)

Lemma fx_dep_distinct_erases X C B (EX : encoding X) (cb : fx_index_external_model X C B) input :
  (forall x, fst (fxi_encode cb x) = encode EX x) ->
  fst (fxi_distinct_counted cb input) = distinct_unknowns EX input.
Proof.
  intro Hencode.
  pose proof (audit_finset_of_list_erases X B (fxi_encode cb) EX input
    (fun x _ => Hencode x)) as Hset.
  unfold fxi_distinct_counted.
  destruct (audit_finset_of_list (fxi_encode cb) input) as [set events]; cbn in Hset; subst set.
  pose proof (audit_finset_elements_erases X (FinSet.of_list EX input)) as Helements.
  destruct (audit_finset_elements (FinSet.of_list EX input)) as [output element_events]; cbn in
    Helements.
  unfold distinct_unknowns; exact Helements.
Qed.

Lemma fx_dep_unknowns_erases X C A B (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B) cs :
  fx_index_external_erases EX S SS cb ->
  fst (fx_dep_unknowns_input cb cs) =
    flat_map (fun c => System.target S c :: deps SS c ++ side_targets SS c) cs.
Proof.
  intros [_ [Htarget [Hsides Hdeps]]].
  induction cs as [|c rest IH].
  - reflexivity.
  - cbn [fx_dep_unknowns_input flat_map].
    specialize (Htarget c) as Ht; specialize (Hsides c) as Hs; specialize (Hdeps c) as Hd.
    destruct (fxi_target cb c) as [target tb]; cbn in Ht; subst target.
    destruct (fxi_deps cb c) as [reads db]; cbn in Hd; subst reads.
    destruct (fxi_sides cb c) as [sides sb]; cbn in Hs; subst sides.
    destruct (fx_dep_unknowns_input cb rest) as [tail events]; cbn in IH |- *.
    rewrite IH, app_assoc; reflexivity.
Qed.

Lemma fx_dep_outputs_erases X C A B (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B) cs :
  fx_index_external_erases EX S SS cb ->
  fst (fx_dep_outputs_input cb cs) =
    flat_map (fun c => System.target S c :: side_targets SS c) cs.
Proof.
  intros [_ [Htarget [Hsides _]]].
  induction cs as [|c rest IH].
  - reflexivity.
  - cbn [fx_dep_outputs_input flat_map].
    specialize (Htarget c) as Ht; specialize (Hsides c) as Hs.
    destruct (fxi_target cb c) as [target tb]; cbn in Ht; subst target.
    destruct (fxi_sides cb c) as [sides sb]; cbn in Hs; subst sides.
    destruct (fx_dep_outputs_input cb rest) as [tail events]; cbn in IH |- *.
    now rewrite IH.
Qed.

(** Counted dependency preparation returns the original graph and index. *)
Theorem fx_dep_build_erasure_correct : fx_dep_build_erasure_statement.
Proof.
  intros X C A B EX S SS cb Herase.
  pose proof (fx_dep_unknowns_erases X C A B EX S SS cb (System.constraints S) Herase) as Hinput.
  pose proof (fx_index_nested_erasure X C A B EX S SS cb Herase) as Hindex.
  unfold fx_dep_graph_build, dependency_graph, unknowns.
  destruct (fx_dep_unknowns_input cb (System.constraints S)) as [input input_events]; cbn in Hinput.
  subst input.
  pose proof (fx_dep_distinct_erases X C B EX cb
    (flat_map (fun c => System.target S c :: deps SS c ++ side_targets SS c)
      (System.constraints S)) (proj1 Herase)) as Hdistinct.
  destruct (fxi_distinct_counted cb (flat_map
    (fun c => System.target S c :: deps SS c ++ side_targets SS c) (System.constraints S)))
    as [vertices distinct_events]; cbn in Hdistinct; subst vertices.
  destruct (fx_index_nested_counted S cb) as [ix index_events]; cbn in Hindex; subst ix.
  split; reflexivity.
Qed.

(** Counted outgoing edges use the original reader bucket and distinct targets. *)
Theorem fx_dep_out_erasure_correct : fx_dep_out_erasure_statement.
Proof.
  intros X C A B EX S SS cb ix y Herase.
  pose proof (proj1 Herase y) as Hencode.
  pose proof (audit_map_code_get_erases X (list C) (fst (fxi_encode cb y)) (readers ix)) as Hget.
  unfold fx_dep_out, readers_of.
  destruct (fxi_encode cb y) as [code body]; cbn in Hencode, Hget; subst code.
  destruct (audit_map_code_get (encode EX y) (readers ix)) as [raw trie]; cbn in Hget.
  pose proof (fx_dep_outputs_erases X C A B EX S SS cb
    (match raw with
      | Some cs => cs
      | None => []
      end) Herase) as Houtputs.
  destruct (fx_dep_outputs_input cb (match raw with
      | Some cs => cs
      | None => []
      end))
    as [values events]; cbn in Houtputs; subst values.
  pose proof (fx_dep_distinct_erases X C B EX cb
    (flat_map (fun c => System.target S c :: side_targets SS c)
      (match raw with
      | Some cs => cs
      | None => []
      end)) (proj1 Herase)) as Hdistinct.
  destruct (fxi_distinct_counted cb
    (flat_map (fun c => System.target S c :: side_targets SS c)
      (match raw with
      | Some cs => cs
      | None => []
      end))) as [distinct distinct_events].
  cbn in Hdistinct |- *; rewrite Hdistinct, Hget; reflexivity.
Qed.

(** * Scheduler composition *)

Lemma fx_dep_encoder_erases X C A B (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B) :
  fx_index_external_erases EX S SS cb ->
  forall x, fst (fx_dep_encoder cb x) = encode EX x.
Proof.
  intros Herase x; specialize (proj1 Herase x) as Hencode.
  unfold fx_dep_encoder; destruct (fxi_encode cb x); exact Hencode.
Qed.

Lemma fx_dep_prepare_erases X C A B (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B) :
  fx_index_external_erases EX S SS cb ->
  audit_prepare_callbacks_erase EX (dependency_graph EX S SS)
    (fx_dep_prepare_cb cb (index_system EX S SS)).
Proof.
  intro Herase; unfold audit_prepare_callbacks_erase, fx_dep_prepare_cb; cbn.
  split.
  - intro x; apply fx_dep_out_erasure_correct; exact Herase.
  - split; [reflexivity |].
    apply (fx_dep_encoder_erases X C A B EX S SS cb Herase).
Qed.

Lemma fx_dep_dfs_erases X C A B (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B) :
  fx_index_external_erases EX S SS cb ->
  audit_dfs_callbacks_erase EX (dependency_graph EX S SS) (fx_dep_dfs_cb cb).
Proof.
  intro Herase; unfold audit_dfs_callbacks_erase, fx_dep_dfs_cb; cbn.
  split; [reflexivity |].
  apply (fx_dep_encoder_erases X C A B EX S SS cb Herase).
Qed.

Lemma fx_dep_retreat_erases X C A B (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B) :
  fx_index_external_erases EX S SS cb ->
  audit_rpo_graph_callbacks_erase EX (dependency_graph EX S SS)
    (fx_dep_rpo_cb cb (index_system EX S SS)).
Proof.
  intro Herase; unfold audit_rpo_graph_callbacks_erase, fx_dep_rpo_cb; cbn.
  split; [apply (fx_dep_encoder_erases X C A B EX S SS cb Herase) |].
  split.
  - intro x; apply fx_dep_out_erasure_correct; exact Herase.
  - split; reflexivity.
Qed.

Lemma fx_rpo_run_erases X C A B (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B) :
  fx_index_external_erases EX S SS cb ->
  let result := fx_rpo_scheduler_counted EX S SS cb in
  let g := dependency_graph EX S SS in
  let p := prepare EX g in
  let search := dfs p FinSet.empty (Graph.entries g) in
  fx_rpo_positions result = schedule_positions EX (rpo search) 1 /\
  fx_rpo_heads result = schedule_retreats EX g search /\
  fx_rpo_reverse_input result = postorder search /\
  fx_rpo_reverse_output result = rpo search /\
  audit_graph_reverse_fast_run (fx_rpo_reverse_input result) []
    (fx_rpo_reverse_output result) (fx_rpo_reverse_work result) /\
  fx_rpo_reverse_work result = audit_graph_reverse_fast_work (length (postorder search)).
Proof.
  intro Herase.
  pose proof (fx_dep_build_erasure_correct X C A B EX S SS cb Herase) as Hbuild.
  unfold fx_rpo_scheduler_counted in *.
  destruct (fx_dep_graph_build EX S SS cb) as [[g ix] build] eqn:Hbuild_call.
  cbn [fst snd] in Hbuild; destruct Hbuild as [Hg Hix]; subst g ix.
  pose proof (audit_prepare_source_correct X (X * X)%type (fx_dep_event X C B) EX
    (dependency_graph EX S SS) (fx_dep_prepare_cb cb (index_system EX S SS)) (fun _ => 0)
    (fx_dep_prepare_erases X C A B EX S SS cb Herase)) as Hprepare.
  destruct (audit_prepare_source_counted EX (dependency_graph EX S SS)
    (fx_dep_prepare_cb cb (index_system EX S SS))) as [p prepare_events] eqn:Hprepare_call.
  cbn [fst snd] in Hprepare; destruct Hprepare as [Hp _]; subst p.
  pose proof (audit_dfs_source_correct X (X * X)%type (fx_dep_event X C B) EX
    (dependency_graph EX S SS) (prepare EX (dependency_graph EX S SS)) (fx_dep_dfs_cb cb)
    (fun _ => 0) FinSet.empty (Graph.entries (dependency_graph EX S SS))
    (fx_dep_dfs_erases X C A B EX S SS cb Herase)) as Hdfs.
  destruct (audit_dfs_source_counted (prepare EX (dependency_graph EX S SS))
    (fx_dep_dfs_cb cb) FinSet.empty (Graph.entries (dependency_graph EX S SS)))
    as [search dfs_events] eqn:Hdfs_call.
  cbn [fst snd] in Hdfs; destruct Hdfs as [Hsearch _]; subst search.
  pose proof (audit_graph_reverse_fast_counted_holds X
    (postorder (dfs (prepare EX (dependency_graph EX S SS)) FinSet.empty
      (Graph.entries (dependency_graph EX S SS)))) []) as Hreverse.
  destruct (audit_graph_reverse_fast_counted
    (postorder (dfs (prepare EX (dependency_graph EX S SS)) FinSet.empty
      (Graph.entries (dependency_graph EX S SS)))) []) as [order work] eqn:Hreverse_call.
  cbn [fst snd] in Hreverse; destruct Hreverse as [Hrun [Horder [_ Hwork]]].
  change (order = rpo (dfs (prepare EX (dependency_graph EX S SS)) FinSet.empty
    (Graph.entries (dependency_graph EX S SS)))) in Horder; subst order.
  pose proof (audit_rpo_schedule_positions_erases X (fx_dep_event X C B) EX
    (fx_dep_encoder cb)
    (rpo (dfs (prepare EX (dependency_graph EX S SS)) FinSet.empty
      (Graph.entries (dependency_graph EX S SS)))) 1%positive
    (fx_dep_encoder_erases X C A B EX S SS cb Herase)) as Hpositions.
  destruct (audit_rpo_schedule_positions (fx_dep_encoder cb)
    (rpo (dfs (prepare EX (dependency_graph EX S SS)) FinSet.empty
      (Graph.entries (dependency_graph EX S SS)))) 1) as [positions position_events].
  cbn [fst snd] in Hpositions; subst positions.
  pose proof (audit_rpo_schedule_retreats_erases X (X * X)%type (fx_dep_event X C B) EX
    (dependency_graph EX S SS)
    (dfs (prepare EX (dependency_graph EX S SS)) FinSet.empty
      (Graph.entries (dependency_graph EX S SS)))
    (fx_dep_rpo_cb cb (index_system EX S SS))
    (fx_dep_retreat_erases X C A B EX S SS cb Herase)) as Hheads.
  destruct (audit_rpo_schedule_retreats (fx_dep_rpo_cb cb (index_system EX S SS))
    (dependency_graph EX S SS)
    (dfs (prepare EX (dependency_graph EX S SS)) FinSet.empty
      (Graph.entries (dependency_graph EX S SS)))) as [heads retreat_events].
  cbn [fst snd] in Hheads; cbn [fx_rpo_positions fx_rpo_heads fx_rpo_reverse_input
    fx_rpo_reverse_output fx_rpo_reverse_work]; subst heads; repeat split; assumption ||
    reflexivity.
Qed.

(** The recorded reversal is the source RPO reversal and has exact linear work. *)
Theorem fx_rpo_fast_reverse_correct : fx_rpo_fast_reverse_statement.
Proof.
  intros X C A B EX S SS cb Herase.
  destruct (fx_rpo_run_erases X C A B EX S SS cb Herase) as [_ [_ Hreverse]].
  exact Hreverse.
Qed.

(** The counted scheduler returns the source priority and widening observations. *)
Theorem fx_rpo_scheduler_erasure_correct : fx_rpo_scheduler_erasure_statement.
Proof.
  intros X C A B EX S SS cb Herase; cbn zeta; intro x.
  pose proof (fx_rpo_run_erases X C A B EX S SS cb Herase) as [Hpositions [Hheads _]].
  pose proof (audit_rpo_schedule_callbacks_erases X (fx_dep_event X C B) EX
    (fx_dep_encoder cb) (fx_rpo_positions (fx_rpo_scheduler_counted EX S SS cb))
    (fx_rpo_heads (fx_rpo_scheduler_counted EX S SS cb)) x
    (fx_dep_encoder_erases X C A B EX S SS cb Herase)) as Hcallbacks.
  change (fst (audit_rpo_schedule_priority (fx_dep_encoder cb)
    (fx_rpo_positions (fx_rpo_scheduler_counted EX S SS cb)) x) =
      schedule_priority EX (schedule_positions EX
        (rpo (dfs (prepare EX (dependency_graph EX S SS)) FinSet.empty
          (Graph.entries (dependency_graph EX S SS)))) 1) x /\
    fst (audit_rpo_schedule_widening (fx_dep_encoder cb)
      (fx_rpo_heads (fx_rpo_scheduler_counted EX S SS cb)) x) =
      FinSet.mem EX x (schedule_retreats EX (dependency_graph EX S SS)
        (dfs (prepare EX (dependency_graph EX S SS)) FinSet.empty
          (Graph.entries (dependency_graph EX S SS))))).
  rewrite <- Hpositions, <- Hheads; exact Hcallbacks.
Qed.

(** * Dependency-output work *)

Lemma fx_dep_work_app X C B (ib : fx_index_external_budget X C B) left right :
  fx_dep_events_work ib (left ++ right) =
    fx_dep_events_work ib left + fx_dep_events_work ib right.
Proof.
  induction left as [|event rest IH].
  - reflexivity.
  - change (fx_dep_event_work ib event + fx_dep_events_work ib (rest ++ right) =
      (fx_dep_event_work ib event + fx_dep_events_work ib rest) + fx_dep_events_work ib right).
    rewrite IH; lia.
Qed.

Lemma fx_dep_index_work X C B (ib : fx_index_external_budget X C B) events :
  fx_dep_events_work ib (map FxDepIndexEvent events) =
    16 * length events + fx_index_adapter_work ib events.
Proof.
  induction events as [|event rest IH].
  - reflexivity.
  - change (fx_dep_event_work ib (FxDepIndexEvent event) +
      fx_dep_events_work ib (map FxDepIndexEvent rest) =
      16 * S (length rest) + (fxi_event_work ib event + fx_index_adapter_work ib rest)).
    unfold fx_dep_event_work; rewrite IH; lia.
Qed.

Lemma fx_dep_outputs_work X C A B (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B)
    (ib : fx_index_external_budget X C B) cs :
  fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
  fx_dep_events_work ib (snd (fx_dep_outputs_input cb cs)) <=
    128 * (1 + length cs +
      length (flat_map (fun c => System.target S c :: side_targets SS c) cs)) +
    fx_dep_callback_budget ib cs.
Proof.
  intros [_ [Htarget [Hsides _]]] [_ [_ [Htbound [Hsbound _]]]].
  induction cs as [|c rest IH].
  - unfold fx_dep_events_work, fx_dep_event_work; cbn [fx_dep_outputs_input snd fold_right
      fx_dep_callback_budget flat_map length fxi_event_work]; lia.
  - cbn [fx_dep_outputs_input flat_map fx_dep_callback_budget].
    specialize (Htarget c) as Ht; specialize (Hsides c) as Hs.
    specialize (Htbound c) as Htb; specialize (Hsbound c) as Hsb.
    destruct (fxi_target cb c) as [target tb]; cbn [fst snd] in Ht, Htb; subst target.
    destruct (fxi_sides cb c) as [sides sb]; cbn [fst snd] in Hs, Hsb; subst sides.
    destruct (fx_dep_outputs_input cb rest) as [tail events]; cbn [snd] in IH |- *.
    change (16 + ((19 + fxi_body_work ib tb) + ((19 + fxi_body_work ib sb) +
      fx_dep_events_work ib (events ++ [FxDepListWork (1 + length (side_targets SS c))]))) <=
      128 * (1 + length (c :: rest) +
        length (System.target S c :: side_targets SS c ++
          flat_map (fun c => System.target S c :: side_targets SS c) rest)) +
      (fxi_target_bound ib c + fxi_deps_bound ib c + fxi_sides_bound ib c +
        fx_dep_callback_budget ib rest)).
    rewrite fx_dep_work_app; cbn [length]; rewrite length_app.
    unfold fx_dep_events_work at 2; cbn [fold_right fx_dep_event_work length].
    unfold fx_dep_event_work; cbn; lia.
Qed.

Lemma fx_dep_distinct_length X (EX : encoding X) input :
  length (distinct_unknowns EX input) <= length input.
Proof.
  apply NoDup_incl_length.
  - apply distinct_unknowns_nodup.
  - intros x Hin; apply distinct_unknowns_spec in Hin; exact Hin.
Qed.

Lemma fx_dep_distinct_event_count X C B (cb : fx_index_external_model X C B) input :
  length (snd (fxi_distinct_counted cb input)) = 2.
Proof.
  unfold fxi_distinct_counted.
  destruct (audit_finset_of_list (fxi_encode cb) input) as [set build].
  destruct (audit_finset_elements set) as [output elements].
  reflexivity.
Qed.

(** A dependency output query charges its reader lookup, callbacks and distinct traversal. *)
Theorem fx_dep_out_bound_correct : fx_dep_out_bound_statement.
Proof.
  intros X C A B EX S SS cb ib ix y Herase Hbounded.
  destruct Herase as [Hencode [Htarget [Hsides Hdeps]]].
  destruct Hbounded as [Hweight [Hencbound [Htbound [Hsbound Hdbound]]]].
  assert (Herase : fx_index_external_erases EX S SS cb)
    by (repeat split; assumption).
  assert (Hbounded : fx_index_external_bounded cb ib)
    by (repeat split; assumption).
  pose proof (fxi_read_adequate X C B EX cb ib y (readers ix) (Hencode y) (Hencbound y))
    as Hread.
  pose proof (fx_dep_outputs_work X C A B EX S SS cb ib (readers_of EX ix y) Herase Hbounded)
    as Houtputs_work.
  pose proof (fx_dep_outputs_erases X C A B EX S SS cb (readers_of EX ix y) Herase)
    as Houtputs_result.
  unfold fx_dep_out.
  destruct (fxi_encode cb y) as [code body] eqn:Hencode_call.
  destruct (audit_map_code_get code (readers ix)) as [raw trie] eqn:Hread_call.
  cbn [fst snd] in Hread; destruct Hread as [Hcode [Hraw [Hbody Htrie]]]; subst code.
  assert (Hreaders : (match raw with
      | Some found => found
      | None => []
      end) = readers_of EX ix y).
  { unfold readers_of, index_get; rewrite <- Hraw; destruct raw; reflexivity. }
  rewrite Hreaders.
  destruct (fx_dep_outputs_input cb (readers_of EX ix y)) as [values bodies]
    eqn:Houtputs_call.
  cbn [fst snd] in Houtputs_result, Houtputs_work; subst values.
  set (values := fx_dep_out_values_native EX S SS ix y).
  fold (fx_dep_out_values_native EX S SS ix y); fold values.
  change (fx_dep_events_work ib bodies <=
    128 * (1 + length (readers_of EX ix y) + length values) +
      fx_dep_callback_budget ib (readers_of EX ix y)) in Houtputs_work.
  pose proof (fxi_distinct_adequate X C B EX cb ib values Hencode Hencbound) as Hdistinct.
  pose proof (fx_dep_distinct_event_count X C B cb values) as Hcount.
  destruct (fxi_distinct_counted cb values) as [distinct distinct_events] eqn:Hdistinct_call.
  cbn [fst snd] in Hdistinct, Hcount; destruct Hdistinct as [Hresult Hdistinct_work].
  subst distinct.
  pose proof (fx_dep_distinct_length X EX values) as Hlength.
  unfold fx_dep_out_budget; fold values.
  cbn [snd].
  change (16 + ((16 + (8 + fxi_body_work ib body +
    audit_trie_get_trace_source_work trie)) +
    fx_dep_events_work ib (bodies ++ map FxDepIndexEvent distinct_events ++
      [FxDepListWork (length (distinct_unknowns EX values)); FxDepCase 3])) <=
    1024 * (1 + length (readers_of EX ix y) + length values) +
      fx_dep_callback_budget ib (readers_of EX ix y) +
      32 * Pos.size_nat (encode EX y) + fxi_encode_bound ib y +
      fxi_distinct_input_budget EX ib values).
  repeat rewrite fx_dep_work_app; rewrite fx_dep_index_work, Hcount.
  change (16 + ((16 + (8 + fxi_body_work ib body + audit_trie_get_trace_source_work trie)) +
    (fx_dep_events_work ib bodies +
      ((16 * 2 + fx_index_adapter_work ib distinct_events) +
        ((17 + length (distinct_unknowns EX values)) + 16)))) <=
    1024 * (1 + length (readers_of EX ix y) + length values) +
      fx_dep_callback_budget ib (readers_of EX ix y) +
      32 * Pos.size_nat (encode EX y) + fxi_encode_bound ib y +
      fxi_distinct_input_budget EX ib values).
  lia.
Qed.

(** * Dependency construction work *)

Lemma fx_dep_unknowns_work X C A B (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B)
    (ib : fx_index_external_budget X C B) cs :
  fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
  fx_dep_events_work ib (snd (fx_dep_unknowns_input cb cs)) <=
    128 * (1 + length cs +
      length (flat_map (fun c => System.target S c :: deps SS c ++ side_targets SS c) cs)) +
    fx_dep_callback_budget ib cs.
Proof.
  intros [_ [Htarget [Hsides Hdeps]]] [_ [_ [Htbound [Hsbound Hdbound]]]].
  induction cs as [|c rest IH].
  - change (16 <= 128 * (1 + 0 + 0) + 0); lia.
  - cbn [fx_dep_unknowns_input flat_map fx_dep_callback_budget].
    specialize (Htarget c) as Ht; specialize (Hsides c) as Hs; specialize (Hdeps c) as Hd.
    specialize (Htbound c) as Htb; specialize (Hsbound c) as Hsb; specialize (Hdbound c) as Hdb.
    destruct (fxi_target cb c) as [target tb]; cbn [fst snd] in Ht, Htb; subst target.
    destruct (fxi_deps cb c) as [deps db]; cbn [fst snd] in Hd, Hdb; subst deps.
    destruct (fxi_sides cb c) as [sides sb]; cbn [fst snd] in Hs, Hsb; subst sides.
    destruct (fx_dep_unknowns_input cb rest) as [tail events]; cbn [snd] in IH |- *.
    change (16 + ((19 + fxi_body_work ib tb) + ((19 + fxi_body_work ib db) +
      ((19 + fxi_body_work ib sb) + ((17 + length (deps SS c)) +
      fx_dep_events_work ib (events ++
        [FxDepListWork (1 + length (deps SS c) + length (side_targets SS c))]))))) <=
      128 * (1 + length (c :: rest) +
        length (System.target S c :: (deps SS c ++ side_targets SS c) ++
          flat_map (fun c => System.target S c :: deps SS c ++ side_targets SS c) rest)) +
      (fxi_target_bound ib c + fxi_deps_bound ib c + fxi_sides_bound ib c +
        fx_dep_callback_budget ib rest)).
    rewrite fx_dep_work_app; cbn [length]; repeat rewrite length_app.
    unfold fx_dep_events_work at 2; cbn [fold_right].
    unfold fx_dep_event_work; cbn [fxi_event_work].
    lia.
Qed.

Lemma fx_dep_push_event_count X C B (cb : fx_index_external_model X C B) c keys :
  forall input, length (snd (fxi_push_many cb c keys input)) = 1 + 4 * length keys.
Proof.
  induction keys as [|key rest IH]; intro input.
  - reflexivity.
  - cbn [fxi_push_many].
    specialize (IH input).
    destruct (fxi_push_many cb c rest input) as [before events]; cbn [snd] in IH.
    destruct (fxi_encode cb key) as [read_code read_body].
    destruct (audit_map_code_get read_code before) as [raw read_events].
    destruct (audit_trie_set read_code (key,
      c :: match raw with
      | Some values => values
      | None => []
      end) before)
      as [after write_events].
    cbn [snd length]; rewrite length_app; cbn [length]; lia.
Qed.

Lemma fx_dep_index_event_count X C A B (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B) cs :
  fx_index_external_erases EX S SS cb ->
  length (snd (fxi_fold cb cs)) <=
    20 * (1 + length cs +
      length (flat_map (fun c => System.target S c :: deps SS c ++ side_targets SS c) cs)).
Proof.
  intro Herase; destruct Herase as [Hencode [Htarget [Hsides Hdeps]]].
  induction cs as [|c rest IH].
  - change (1 <= 20 * (1 + 0 + 0)); lia.
  - cbn [fxi_fold flat_map].
    destruct (fxi_fold cb rest) as [ix tail] eqn:Hfold; cbn [snd] in IH.
    specialize (Htarget c) as Ht; specialize (Hsides c) as Hs; specialize (Hdeps c) as Hd.
    destruct (fxi_target cb c) as [target tb]; cbn [fst] in Ht; subst target.
    destruct (fxi_sides cb c) as [sides sb]; cbn [fst] in Hs; subst sides.
    pose proof (fx_dep_distinct_erases X C B EX cb (System.target S c :: side_targets SS c)
      Hencode) as Houtputs.
    pose proof (fx_dep_distinct_event_count X C B cb (System.target S c :: side_targets SS c))
      as Houtput_count.
    destruct (fxi_distinct_counted cb (System.target S c :: side_targets SS c))
      as [outputs output_events] eqn:Houtputs_call; cbn [fst snd] in Houtputs, Houtput_count.
    subst outputs.
    pose proof (fx_dep_distinct_length X EX (System.target S c :: side_targets SS c))
      as Houtput_length.
    pose proof (fx_dep_push_event_count X C B cb c
      (distinct_unknowns EX (System.target S c :: side_targets SS c)) (contributors ix))
      as Hcontrib_count.
    destruct (fxi_push_many cb c
      (distinct_unknowns EX (System.target S c :: side_targets SS c)) (contributors ix))
      as [contrib contrib_events]; cbn [snd] in Hcontrib_count.
    destruct (fxi_deps cb c) as [reads db]; cbn [fst] in Hd; subst reads.
    pose proof (fx_dep_distinct_erases X C B EX cb (deps SS c) Hencode) as Hreads.
    pose proof (fx_dep_distinct_event_count X C B cb (deps SS c)) as Hread_count.
    destruct (fxi_distinct_counted cb (deps SS c)) as [reads read_events] eqn:Hreads_call;
      cbn [fst snd] in Hreads, Hread_count; subst reads.
    pose proof (fx_dep_distinct_length X EX (deps SS c)) as Hread_length.
    pose proof (fx_dep_push_event_count X C B cb c (distinct_unknowns EX (deps SS c)) (readers ix))
      as Hreader_count.
    destruct (fxi_push_many cb c (distinct_unknowns EX (deps SS c)) (readers ix))
      as [reader reader_events]; cbn [snd] in Hreader_count.
    cbn [snd length]; repeat rewrite length_app; cbn [length] in *.
    repeat rewrite length_app; lia.
Qed.

(** Dependency construction charges its enumeration, distinct traversal and counted index. *)
Theorem fx_dep_build_bound_correct : fx_dep_build_bound_statement.
Proof.
  intros X C A B EX S SS cb ib Herase Hbounded.
  pose proof (fx_dep_unknowns_erases X C A B EX S SS cb (System.constraints S) Herase)
    as Hinput.
  pose proof (fx_dep_unknowns_work X C A B EX S SS cb ib (System.constraints S) Herase Hbounded)
    as Hinput_work.
  pose proof (fx_index_nested_input_bound X C A B EX S SS cb ib Herase Hbounded) as Hindex.
  pose proof (fx_dep_index_event_count X C A B EX S SS cb (System.constraints S) Herase)
    as Hindex_count.
  unfold fx_dep_graph_build.
  destruct (fx_dep_unknowns_input cb (System.constraints S)) as [input input_events]
    eqn:Hinput_call; cbn [fst snd] in Hinput, Hinput_work; subst input.
  fold (fx_dep_unknowns_native S SS).
  pose proof (fxi_distinct_adequate X C B EX cb ib (fx_dep_unknowns_native S SS)
    (proj1 Herase) (proj1 (proj2 Hbounded))) as Hdistinct.
  pose proof (fx_dep_distinct_event_count X C B cb (fx_dep_unknowns_native S SS)) as
    Hdistinct_count.
  destruct (fxi_distinct_counted cb (fx_dep_unknowns_native S SS)) as [vertices distinct_events];
    cbn [fst snd] in Hdistinct, Hdistinct_count; destruct Hdistinct as [_ Hdistinct_work].
  destruct (fx_index_nested_counted S cb) as [ix index_events] eqn:Hindex_call.
  cbn [fst snd] in Hindex; destruct Hindex as [_ Hindex_work].
  unfold fx_index_nested_counted in Hindex_call.
  rewrite Hindex_call in Hindex_count; cbn [snd] in Hindex_count.
  unfold fx_dep_build_budget; fold (fx_dep_unknowns_native S SS).
  cbn [snd]; repeat rewrite fx_dep_work_app; repeat rewrite fx_dep_index_work.
  rewrite Hdistinct_count.
  change (fx_dep_events_work ib input_events +
    ((16 * 2 + fx_index_adapter_work ib distinct_events) +
    (16 * length index_events + fx_index_adapter_work ib index_events)) <=
    1024 * (1 + length (System.constraints S) + length (fx_dep_unknowns_native S SS)) +
      fx_dep_callback_budget ib (System.constraints S) +
      fxi_distinct_input_budget EX ib (fx_dep_unknowns_native S SS) +
      fx_index_nested_input_budget EX S SS ib).
  fold (fx_dep_unknowns_native S SS) in Hinput_work, Hindex_count.
  lia.
Qed.

(** * Scheduler receipt count *)

(** Every preparation, DFS, position and retreat receipt fits the input-derived count limit. *)
Theorem fx_rpo_receipt_count_correct : fx_rpo_receipt_count_statement.
Proof.
  intros X C A B EX S SS cb Herase.
  pose proof (fx_dep_build_erasure_correct X C A B EX S SS cb Herase) as Hbuild.
  unfold fx_rpo_scheduler_counted in *.
  destruct (fx_dep_graph_build EX S SS cb) as [[g ix] build] eqn:Hbuild_call.
  cbn [fst snd] in Hbuild; destruct Hbuild as [Hg Hix]; subst g ix.
  pose proof (audit_prepare_source_correct X (X * X)%type (fx_dep_event X C B) EX
    (dependency_graph EX S SS) (fx_dep_prepare_cb cb (index_system EX S SS)) (fun _ => 0)
    (fx_dep_prepare_erases X C A B EX S SS cb Herase)) as Hprepare.
  destruct (audit_prepare_source_counted EX (dependency_graph EX S SS)
    (fx_dep_prepare_cb cb (index_system EX S SS))) as [p prepare_events] eqn:Hprepare_call.
  cbn [fst snd] in Hprepare; destruct Hprepare as [Hp [Hprepare_count _]]; subst p.
  pose proof (audit_dfs_source_correct X (X * X)%type (fx_dep_event X C B) EX
    (dependency_graph EX S SS) (prepare EX (dependency_graph EX S SS)) (fx_dep_dfs_cb cb)
    (fun _ => 0) FinSet.empty (Graph.entries (dependency_graph EX S SS))
    (fx_dep_dfs_erases X C A B EX S SS cb Herase)) as Hdfs.
  destruct (audit_dfs_source_counted (prepare EX (dependency_graph EX S SS))
    (fx_dep_dfs_cb cb) FinSet.empty (Graph.entries (dependency_graph EX S SS)))
    as [search dfs_events] eqn:Hdfs_call.
  cbn [fst snd] in Hdfs; destruct Hdfs as [Hsearch [_ [Hdfs_count _]]]; subst search.
  pose proof (audit_graph_reverse_fast_counted_holds X
    (postorder (dfs (prepare EX (dependency_graph EX S SS)) FinSet.empty
      (Graph.entries (dependency_graph EX S SS)))) []) as Hreverse.
  destruct (audit_graph_reverse_fast_counted
    (postorder (dfs (prepare EX (dependency_graph EX S SS)) FinSet.empty
      (Graph.entries (dependency_graph EX S SS)))) []) as [order work].
  cbn [fst snd] in Hreverse; destruct Hreverse as [_ [Horder _]].
  change (order = rpo (dfs (prepare EX (dependency_graph EX S SS)) FinSet.empty
    (Graph.entries (dependency_graph EX S SS)))) in Horder; subst order.
  pose proof (audit_rpo_positions_count X (fx_dep_event X C B) (fx_dep_encoder cb)
    (rpo (dfs (prepare EX (dependency_graph EX S SS)) FinSet.empty
      (Graph.entries (dependency_graph EX S SS)))) 1) as Hposition_count.
  destruct (audit_rpo_schedule_positions (fx_dep_encoder cb)
    (rpo (dfs (prepare EX (dependency_graph EX S SS)) FinSet.empty
      (Graph.entries (dependency_graph EX S SS)))) 1) as [positions position_events].
  cbn [snd] in Hposition_count.
  pose proof (audit_rpo_retreats_bound_correct X (X * X)%type (fx_dep_event X C B) EX
    (dependency_graph EX S SS)
    (dfs (prepare EX (dependency_graph EX S SS)) FinSet.empty
      (Graph.entries (dependency_graph EX S SS))) (fx_dep_rpo_cb cb (index_system EX S SS))
    (fun _ => 0) (fx_dep_retreat_erases X C A B EX S SS cb Herase)) as Hretreat.
  destruct (audit_rpo_schedule_retreats (fx_dep_rpo_cb cb (index_system EX S SS))
    (dependency_graph EX S SS)
    (dfs (prepare EX (dependency_graph EX S SS)) FinSet.empty
      (Graph.entries (dependency_graph EX S SS)))) as [heads retreat_events].
  cbn [fst snd] in Hretreat; destruct Hretreat as [_ Hretreat_work].
  rewrite audit_rpo_graph_zero_body in Hretreat_work.
  pose proof (audit_rpo_graph_length_work X (X * X)%type (fx_dep_event X C B)
    (fun _ => 0) retreat_events) as Hretreat_count.
  assert (Horder_length : length (rpo (dfs (prepare EX (dependency_graph EX S SS)) FinSet.empty
    (Graph.entries (dependency_graph EX S SS)))) =
    length (postorder (dfs (prepare EX (dependency_graph EX S SS)) FinSet.empty
      (Graph.entries (dependency_graph EX S SS))))).
  { unfold rpo; rewrite <- rev_alt, length_rev; reflexivity. }
  rewrite Horder_length in Hposition_count.
  unfold fx_rpo_receipt_count_limit.
  cbn [fx_rpo_prepare_events fx_rpo_dfs_events fx_rpo_position_events fx_rpo_retreat_events].
  lia.
Qed.

(** * Index callback source receipts *)

Lemma fx_dep_set_fold_source X C B (cb : fx_index_external_model X C B)
    (source : fx_index_external_source X C B) keys :
  fx_dep_source_laws cb source ->
  forall input, fxi_set_external_adequacy source (snd (audit_finset_fold (fxi_encode cb) keys
    input)).
Proof.
  intro Hlaws; destruct Hlaws as [Hencode _].
  induction keys as [|key rest IH]; intro input.
  - cbn [audit_finset_fold snd fxi_set_external_adequacy]; constructor; [exact I | constructor].
  - cbn [audit_finset_fold].
    specialize (Hencode key) as Hcall.
    unfold audit_finset_add.
    destruct (fxi_encode cb key) as [code body] eqn:Hencode_call; cbn in Hcall.
    destruct (audit_trie_set code (key, tt) input) as [next trace].
    specialize (IH next).
    destruct (audit_finset_fold (fxi_encode cb) rest next) as [output events]; cbn [snd] in IH |- *.
    unfold fxi_set_external_adequacy in *; constructor; [exact I |].
    constructor; [exact Hcall | exact IH].
Qed.

Lemma fx_dep_distinct_source X C B (cb : fx_index_external_model X C B)
    (source : fx_index_external_source X C B) input :
  fx_dep_source_laws cb source ->
  fx_index_external_trace_adequacy source (snd (fxi_distinct_counted cb input)).
Proof.
  intro Hlaws.
  pose proof (fx_dep_set_fold_source X C B cb source input Hlaws FinSet.empty) as Hbuild.
  unfold fxi_distinct_counted, audit_finset_of_list.
  destruct (audit_finset_fold (fxi_encode cb) input FinSet.empty) as [set build]; cbn [snd] in
    Hbuild.
  destruct (audit_finset_elements set) as [output events].
  cbn [snd fx_index_external_trace_adequacy]; constructor; [exact Hbuild |].
  constructor; [exact I | constructor].
Qed.

Lemma fx_dep_push_source X C B (cb : fx_index_external_model X C B)
    (source : fx_index_external_source X C B) c keys :
  fx_dep_source_laws cb source ->
  forall input, fx_index_external_trace_adequacy source (snd (fxi_push_many cb c keys input)).
Proof.
  intro Hlaws; destruct Hlaws as [Hencode Hrest].
  induction keys as [|key rest IH]; intro input.
  - cbn [fxi_push_many snd fx_index_external_trace_adequacy]; constructor; [exact I | constructor].
  - cbn [fxi_push_many].
    specialize (IH input).
    destruct (fxi_push_many cb c rest input) as [before events]; cbn [snd] in IH.
    specialize (Hencode key) as Hcall.
    destruct (fxi_encode cb key) as [code body]; cbn in Hcall.
    destruct (audit_map_code_get code before) as [raw read_events].
    destruct (audit_trie_set code (key, c ::
      match raw with
      | Some values => values
      | None => []
      end) before) as [after write_events].
    cbn [snd fx_index_external_trace_adequacy]; constructor; [exact I |].
    unfold fx_index_external_trace_adequacy in IH.
    apply Forall_app; split; [exact IH |].
    constructor; [exact Hcall |].
    constructor; [exact I |].
    constructor; [exact Hcall | constructor].
Qed.

Lemma fx_dep_fold_source X C B (cb : fx_index_external_model X C B)
    (source : fx_index_external_source X C B) cs :
  fx_dep_source_laws cb source -> fx_index_external_trace_adequacy source (snd (fxi_fold cb cs)).
Proof.
  intro Hlaws; destruct Hlaws as [Hencode [Htarget [Hsides Hdeps]]].
  assert (Hlaws : fx_dep_source_laws cb source) by (repeat split; assumption).
  induction cs as [|c rest IH].
  - cbn [fxi_fold snd fx_index_external_trace_adequacy]; constructor; [exact I | constructor].
  - cbn [fxi_fold].
    destruct (fxi_fold cb rest) as [ix tail]; cbn [snd] in IH.
    specialize (Htarget c) as Ht; specialize (Hsides c) as Hs; specialize (Hdeps c) as Hd.
    destruct (fxi_target cb c) as [target tb]; cbn in Ht.
    destruct (fxi_sides cb c) as [sides sb]; cbn in Hs.
    pose proof (fx_dep_distinct_source X C B cb source (target :: sides) Hlaws) as Houtputs.
    destruct (fxi_distinct_counted cb (target :: sides)) as [outputs output_events];
      cbn [snd] in Houtputs.
    pose proof (fx_dep_push_source X C B cb source c outputs Hlaws (contributors ix)) as Hcontrib.
    destruct (fxi_push_many cb c outputs (contributors ix)) as [contrib contrib_events];
      cbn [snd] in Hcontrib.
    destruct (fxi_deps cb c) as [reads db]; cbn in Hd.
    pose proof (fx_dep_distinct_source X C B cb source reads Hlaws) as Hreads.
    destruct (fxi_distinct_counted cb reads) as [distinct read_events]; cbn [snd] in Hreads.
    pose proof (fx_dep_push_source X C B cb source c distinct Hlaws (readers ix)) as Hreader.
    destruct (fxi_push_many cb c distinct (readers ix)) as [reader reader_events];
      cbn [snd] in Hreader |- *.
    unfold fx_index_external_trace_adequacy in *; constructor; [exact I |].
    repeat rewrite Forall_app; repeat split; try assumption.
    + constructor; [exact Ht | constructor; [exact Hs | constructor]].
    + constructor; [exact Hd | apply Forall_app; split; assumption].
Qed.

Lemma fx_dep_nested_source X C B (source : fx_index_external_source X C B) events :
  fx_index_external_trace_adequacy source events ->
  fx_dep_body_source source (map FxDepIndexEvent events).
Proof.
  unfold fx_index_external_trace_adequacy, fx_dep_body_source.
  intro Hsource; induction Hsource as [|event rest Hhead Hrest IH].
  - constructor.
  - cbn [map]; constructor; [|exact IH].
    cbn [fx_dep_event_source fx_index_external_trace_adequacy];
      constructor; [exact Hhead | constructor].
Qed.

Lemma fx_dep_unknowns_source X C B (cb : fx_index_external_model X C B)
    (source : fx_index_external_source X C B) cs :
  fx_dep_source_laws cb source -> fx_dep_body_source source (snd (fx_dep_unknowns_input cb cs)).
Proof.
  intro Hlaws; destruct Hlaws as [Hencode [Htarget [Hsides Hdeps]]].
  induction cs as [|c rest IH].
  - cbn [fx_dep_unknowns_input snd fx_dep_body_source fx_dep_event_source];
      constructor; [exact I | constructor].
  - cbn [fx_dep_unknowns_input].
    specialize (Htarget c) as Ht; specialize (Hsides c) as Hs; specialize (Hdeps c) as Hd.
    destruct (fxi_target cb c) as [target tb]; cbn in Ht.
    destruct (fxi_deps cb c) as [deps db]; cbn in Hd.
    destruct (fxi_sides cb c) as [sides sb]; cbn in Hs.
    destruct (fx_dep_unknowns_input cb rest) as [tail events]; cbn [snd] in IH |- *.
    unfold fx_dep_body_source in *.
    constructor; [exact I |].
    constructor; [cbn [fx_dep_event_source fx_index_external_trace_adequacy];
      constructor; [exact Ht | constructor] |].
    constructor; [cbn [fx_dep_event_source fx_index_external_trace_adequacy];
      constructor; [exact Hd | constructor] |].
    constructor; [cbn [fx_dep_event_source fx_index_external_trace_adequacy];
      constructor; [exact Hs | constructor] |].
    constructor; [exact I |].
    apply Forall_app; split; [exact IH | constructor; [exact I | constructor]].
Qed.

Lemma fx_dep_outputs_source X C B (cb : fx_index_external_model X C B)
    (source : fx_index_external_source X C B) cs :
  fx_dep_source_laws cb source -> fx_dep_body_source source (snd (fx_dep_outputs_input cb cs)).
Proof.
  intro Hlaws; destruct Hlaws as [Hencode [Htarget [Hsides Hdeps]]].
  induction cs as [|c rest IH].
  - cbn [fx_dep_outputs_input snd fx_dep_body_source fx_dep_event_source];
      constructor; [exact I | constructor].
  - cbn [fx_dep_outputs_input].
    specialize (Htarget c) as Ht; specialize (Hsides c) as Hs.
    destruct (fxi_target cb c) as [target tb]; cbn in Ht.
    destruct (fxi_sides cb c) as [sides sb]; cbn in Hs.
    destruct (fx_dep_outputs_input cb rest) as [tail events]; cbn [snd] in IH |- *.
    unfold fx_dep_body_source in *.
    constructor; [exact I |].
    constructor; [cbn [fx_dep_event_source fx_index_external_trace_adequacy];
      constructor; [exact Ht | constructor] |].
    constructor; [cbn [fx_dep_event_source fx_index_external_trace_adequacy];
      constructor; [exact Hs | constructor] |].
    apply Forall_app; split; [exact IH | constructor; [exact I | constructor]].
Qed.

Lemma fx_dep_out_source X C B (cb : fx_index_external_model X C B)
    (source : fx_index_external_source X C B) ix y :
  fx_dep_source_laws cb source -> fx_dep_body_source source (snd (fx_dep_out cb ix y)).
Proof.
  intro Hlaws; pose proof (proj1 Hlaws y) as Hencode.
  unfold fx_dep_out.
  destruct (fxi_encode cb y) as [code body]; cbn in Hencode.
  destruct (audit_map_code_get code (readers ix)) as [raw trie].
  pose proof (fx_dep_outputs_source X C B cb source
    (match raw with
      | Some found => found
      | None => []
      end) Hlaws) as Houtputs.
  destruct (fx_dep_outputs_input cb (match raw with
      | Some found => found
      | None => []
      end))
    as [values events]; cbn [snd] in Houtputs.
  pose proof (fx_dep_distinct_source X C B cb source values Hlaws) as Hdistinct.
  destruct (fxi_distinct_counted cb values) as [distinct distinct_events]; cbn [snd] in Hdistinct.
  pose proof (fx_dep_nested_source X C B source distinct_events Hdistinct) as Hnested.
  cbn [snd]; unfold fx_dep_body_source in *; constructor; [exact I |].
  constructor; [cbn [fx_dep_event_source fx_index_external_trace_adequacy];
    constructor; [exact Hencode | constructor] |].
  repeat rewrite Forall_app; repeat split; try assumption.
  constructor; [exact I | constructor; [exact I | constructor]].
Qed.

Lemma fx_dep_build_source X C A B (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B)
    (source : fx_index_external_source X C B) :
  fx_dep_source_laws cb source ->
  let '(_, _, events) := fx_dep_graph_build EX S SS cb in fx_dep_body_source source events.
Proof.
  intro Hlaws.
  pose proof (fx_dep_unknowns_source X C B cb source (System.constraints S) Hlaws) as Hinput.
  pose proof (fx_dep_fold_source X C B cb source (System.constraints S) Hlaws) as Hindex.
  unfold fx_dep_graph_build, fx_index_nested_counted.
  destruct (fx_dep_unknowns_input cb (System.constraints S)) as [input input_events];
    cbn [snd] in Hinput.
  pose proof (fx_dep_distinct_source X C B cb source input Hlaws) as Hdistinct.
  destruct (fxi_distinct_counted cb input) as [vertices distinct_events]; cbn [snd] in Hdistinct.
  destruct (fxi_fold cb (System.constraints S)) as [ix index_events]; cbn [snd] in Hindex |- *.
  pose proof (fx_dep_nested_source X C B source distinct_events Hdistinct) as Hdistinct_body.
  pose proof (fx_dep_nested_source X C B source index_events Hindex) as Hindex_body.
  unfold fx_dep_body_source in *; repeat rewrite Forall_app; repeat split; assumption.
Qed.

(** * Preparation callback source receipts *)

Lemma fx_dep_encoder_source X C B (cb : fx_index_external_model X C B)
    (source : fx_index_external_source X C B) x :
  fx_dep_source_laws cb source -> fx_dep_body_source source (snd (fx_dep_encoder cb x)).
Proof.
  intro Hlaws; pose proof (proj1 Hlaws x) as Hencode.
  unfold fx_dep_encoder; destruct (fxi_encode cb x) as [code body]; cbn in Hencode |- *.
  unfold fx_dep_body_source; constructor; [exact Hencode | constructor].
Qed.

Lemma fx_dep_prepare_get_source X C B (cb : fx_index_external_model X C B)
    (source : fx_index_external_source X C B) key (input : Map.t X (list (X * X))) :
  fx_dep_source_laws cb source ->
  Forall (fx_dep_prepare_source source)
    (map PrepareSourceMap (snd (audit_map_get (fx_dep_encoder cb) key input))).
Proof.
  intro Hlaws; pose proof (fx_dep_encoder_source X C B cb source key Hlaws) as Hbody.
  unfold audit_map_get; destruct (fx_dep_encoder cb key) as [code body]; cbn [snd] in Hbody.
  destruct (audit_map_code_get code input) as [output trace].
  cbn [snd map]; constructor; [exact Hbody | constructor].
Qed.

Lemma fx_dep_prepare_set_source X C B (cb : fx_index_external_model X C B)
    (source : fx_index_external_source X C B) key value (input : Map.t X (list (X * X))) :
  fx_dep_source_laws cb source ->
  Forall (fx_dep_prepare_source source)
    (map PrepareSourceMap (snd (audit_map_set (fx_dep_encoder cb) key value input))).
Proof.
  intro Hlaws; pose proof (fx_dep_encoder_source X C B cb source key Hlaws) as Hbody.
  unfold audit_map_set; destruct (fx_dep_encoder cb key) as [code body]; cbn [snd] in Hbody.
  destruct (audit_trie_set code (key, value) input) as [output trace].
  cbn [snd map]; constructor; [exact Hbody | constructor].
Qed.

Lemma fx_dep_prepare_out_source X C B (cb : fx_index_external_model X C B)
    (source : fx_index_external_source X C B) ix vertices :
  fx_dep_source_laws cb source -> forall initial,
  Forall (fx_dep_prepare_source source)
    (snd (audit_prepare_source_out (fx_dep_prepare_cb cb ix) vertices initial)).
Proof.
  intro Hlaws; induction vertices as [|v rest IH]; intro initial.
  - cbn [audit_prepare_source_out snd]; constructor; [exact I | constructor].
  - cbn [audit_prepare_source_out fx_dep_prepare_cb audit_prepare_out_model
    audit_prepare_encode_model].
    specialize (IH initial).
    destruct (audit_prepare_source_out (fx_dep_prepare_cb cb ix) rest initial) as [middle events];
      cbn [snd] in IH.
    pose proof (fx_dep_out_source X C B cb source ix v Hlaws) as Hout.
    destruct (fx_dep_out cb ix v) as [outgoing body] eqn:Hout_call; cbn [snd] in Hout.
    pose proof (fx_dep_prepare_set_source X C B cb source v outgoing middle Hlaws) as Hset.
    destruct (audit_map_set (fx_dep_encoder cb) v outgoing middle) as [result writes];
      cbn [snd] in Hset |- *.
    constructor; [exact I |].
    repeat rewrite Forall_app; repeat split; try assumption.
    constructor; [exact Hout | constructor].
Qed.

Lemma fx_dep_prepare_edges_source X C B (cb : fx_index_external_model X C B)
    (source : fx_index_external_source X C B) ix edges :
  fx_dep_source_laws cb source -> forall initial,
  Forall (fx_dep_prepare_source source)
    (snd (audit_prepare_source_edges (fx_dep_prepare_cb cb ix) edges initial)).
Proof.
  intro Hlaws; induction edges as [|edge rest IH]; intro initial.
  - cbn [audit_prepare_source_edges snd]; constructor; [exact I | constructor].
  - cbn [audit_prepare_source_edges fx_dep_prepare_cb audit_prepare_target_model
    audit_prepare_encode_model].
    specialize (IH initial).
    destruct (audit_prepare_source_edges (fx_dep_prepare_cb cb ix) rest initial)
      as [middle events]; cbn [snd] in IH.
    pose proof (fx_dep_prepare_get_source X C B cb source (snd edge) middle Hlaws) as Hget.
    destruct (audit_map_get (fx_dep_encoder cb) (snd edge) middle) as [found reads];
      cbn [snd] in Hget.
    pose proof (fx_dep_prepare_set_source X C B cb source (snd edge)
      (edge :: match found with
      | Some xs => xs
      | None => []
      end) middle Hlaws) as Hset.
    destruct (audit_map_set (fx_dep_encoder cb) (snd edge)
      (edge :: match found with
      | Some xs => xs
      | None => []
      end) middle) as [next writes];
      cbn [snd] in Hset |- *.
    constructor; [exact I |].
    repeat rewrite Forall_app; repeat split; try assumption.
    + constructor; [constructor; [exact I | constructor] |].
      constructor; [constructor; [exact I | constructor] | constructor].
    + constructor; [exact I | constructor].
Qed.

Lemma fx_dep_prepare_in_source X C B (cb : fx_index_external_model X C B)
    (source : fx_index_external_source X C B) ix vertices :
  fx_dep_source_laws cb source -> forall initial,
  Forall (fx_dep_prepare_source source)
    (snd (audit_prepare_source_in (fx_dep_prepare_cb cb ix) vertices initial)).
Proof.
  intro Hlaws; induction vertices as [|v rest IH]; intro initial.
  - cbn [audit_prepare_source_in snd]; constructor; [exact I | constructor].
  - cbn [audit_prepare_source_in fx_dep_prepare_cb audit_prepare_out_model].
    specialize (IH initial).
    destruct (audit_prepare_source_in (fx_dep_prepare_cb cb ix) rest initial) as [middle events];
      cbn [snd] in IH.
    pose proof (fx_dep_out_source X C B cb source ix v Hlaws) as Hout.
    destruct (fx_dep_out cb ix v) as [outgoing body]; cbn [snd] in Hout.
    pose proof (fx_dep_prepare_edges_source X C B cb source ix outgoing Hlaws middle) as Hedges.
    destruct (audit_prepare_source_edges (fx_dep_prepare_cb cb ix) outgoing middle)
      as [result edges]; cbn [snd] in Hedges |- *.
    constructor; [exact I |].
    repeat rewrite Forall_app; repeat split; try assumption.
    constructor; [exact Hout | constructor].
Qed.

Lemma fx_dep_prepare_count_source X C B (cb : fx_index_external_model X C B)
    (source : fx_index_external_source X C B) ix vertices :
  fx_dep_source_laws cb source ->
  Forall (fx_dep_prepare_source source)
    (snd (audit_prepare_source_edge_count (fx_dep_prepare_cb cb ix) vertices)).
Proof.
  intro Hlaws; induction vertices as [|v rest IH].
  - cbn [audit_prepare_source_edge_count snd]; constructor; [exact I | constructor].
  - cbn [audit_prepare_source_edge_count fx_dep_prepare_cb audit_prepare_out_model].
    destruct (audit_prepare_source_edge_count (fx_dep_prepare_cb cb ix) rest) as [count events];
      cbn [snd] in IH.
    pose proof (fx_dep_out_source X C B cb source ix v Hlaws) as Hout.
    destruct (fx_dep_out cb ix v) as [outgoing body]; cbn [snd] in Hout |- *.
    constructor; [exact I |].
    apply Forall_app; split; [exact IH |].
    constructor; [exact Hout | constructor; [exact I | constructor]].
Qed.

Lemma fx_dep_prepare_source_all X C B (EX : encoding X) (g : Graph.t X (X * X))
    (cb : fx_index_external_model X C B) (source : fx_index_external_source X C B) ix :
  fx_dep_source_laws cb source ->
  Forall (fx_dep_prepare_source source)
    (snd (audit_prepare_source_counted EX g (fx_dep_prepare_cb cb ix))).
Proof.
  intro Hlaws.
  pose proof (fx_dep_prepare_out_source X C B cb source ix (Graph.nodes g) Hlaws Map.empty) as Hout.
  pose proof (fx_dep_prepare_in_source X C B cb source ix (Graph.nodes g) Hlaws Map.empty) as Hin.
  pose proof (fx_dep_prepare_count_source X C B cb source ix (Graph.nodes g) Hlaws) as Hcount.
  unfold audit_prepare_source_counted.
  destruct (audit_prepare_source_out (fx_dep_prepare_cb cb ix) (Graph.nodes g) Map.empty)
    as [out out_events]; cbn [snd] in Hout.
  destruct (audit_prepare_source_in (fx_dep_prepare_cb cb ix) (Graph.nodes g) Map.empty)
    as [incoming in_events]; cbn [snd] in Hin.
  destruct (audit_prepare_source_edge_count (fx_dep_prepare_cb cb ix) (Graph.nodes g))
    as [count count_events]; cbn [snd] in Hcount |- *.
  repeat rewrite Forall_app; repeat split; try assumption; repeat constructor.
Qed.

(** * Scheduler callback source receipts *)

Lemma fx_dep_dfs_source_all X C B (EX : encoding X) (g : Graph.t X (X * X))
    (p : prepared EX g) (cb : fx_index_external_model X C B)
    (source : fx_index_external_source X C B) blocked roots :
  fx_dep_source_laws cb source ->
  Forall (fx_dep_dfs_source source) (snd (audit_dfs_source_counted p (fx_dep_dfs_cb cb)
    blocked roots)).
Proof.
  intro Hlaws.
  pose proof (audit_dfs_source_receipts p (fx_dep_dfs_cb cb) blocked roots) as Hreceipts.
  eapply Forall_impl; [|exact Hreceipts].
  intros [event captures] Hitem; unfold audit_dfs_event_receipts in Hitem; cbn [snd] in Hitem.
  unfold fx_dep_dfs_source; cbn [snd].
  eapply Forall_impl; [|exact Hitem].
  intros capture Hcapture; destruct capture as [edge target body | v code body];
    cbn [audit_dfs_capture_receipt fx_dep_dfs_cb audit_dfs_target_model
      audit_dfs_encode_model] in Hcapture |- *.
  - inversion Hcapture; subst body; unfold fx_dep_body_source; constructor; [exact I | constructor].
  - pose proof (fx_dep_encoder_source X C B cb source v Hlaws) as Hbody.
    rewrite Hcapture in Hbody; exact Hbody.
Qed.

Lemma fx_dep_positions_source_all X C B (cb : fx_index_external_model X C B)
    (source : fx_index_external_source X C B) vertices :
  fx_dep_source_laws cb source -> forall next,
  Forall (fx_dep_positions_source source)
    (snd (audit_rpo_schedule_positions (fx_dep_encoder cb) vertices next)).
Proof.
  intro Hlaws; induction vertices as [|v rest IH]; intro next.
  - cbn [audit_rpo_schedule_positions snd]; constructor; [exact I | constructor].
  - cbn [audit_rpo_schedule_positions].
    destruct (audit_positive_succ next) as [next' successor_events].
    specialize (IH next').
    destruct (audit_rpo_schedule_positions (fx_dep_encoder cb) rest next') as [middle events];
      cbn [snd] in IH.
    pose proof (fx_dep_encoder_source X C B cb source v Hlaws) as Hbody.
    unfold audit_map_set; destruct (fx_dep_encoder cb v) as [code body]; cbn [snd] in Hbody.
    destruct (audit_trie_set code (v, next) middle) as [output trace].
    cbn [snd map app]; constructor; [exact I | constructor; [exact I |]].
    apply Forall_app; split; [exact IH |].
    constructor; [exact Hbody | constructor].
Qed.

Lemma fx_dep_retreat_event_source X C B (cb : fx_index_external_model X C B)
    (source : fx_index_external_source X C B) ix event :
  fx_dep_source_laws cb source -> audit_rpo_graph_receipt (fx_dep_rpo_cb cb ix) event ->
  fx_dep_retreat_source source event.
Proof.
  intros Hlaws Hreceipt.
  destruct event as [site | v output body | edge output body | edge output body | item | item |
    left right result trace]; cbn [audit_rpo_graph_receipt fx_dep_rpo_cb audit_rpo_graph_encode]
      in Hreceipt;
    cbn [fx_dep_retreat_source].
  - exact I.
  - change (fx_dep_out cb ix v = (output, body)) in Hreceipt.
    pose proof (fx_dep_out_source X C B cb source ix v Hlaws) as Hbody.
    rewrite Hreceipt in Hbody; exact Hbody.
  - inversion Hreceipt; subst body; unfold fx_dep_body_source; constructor; [exact I | constructor].
  - inversion Hreceipt; subst body; unfold fx_dep_body_source; constructor; [exact I | constructor].
  - destruct item; cbn [audit_rpo_graph_receipt fx_dep_rpo_cb audit_rpo_graph_encode] in Hreceipt;
      cbn [fx_dep_map_source];
      match goal with
      | Hcall : fx_dep_encoder cb ?key = (?code, ?body) |- _ =>
        pose proof (fx_dep_encoder_source X C B cb source key Hlaws) as Hbody;
        rewrite Hcall in Hbody; exact Hbody
      end.
  - destruct item; cbn [audit_rpo_graph_receipt fx_dep_rpo_cb audit_rpo_graph_encode] in Hreceipt;
      cbn [fx_dep_set_source]; try exact I;
      match goal with
      | Hcall : fx_dep_encoder cb ?key = (?code, ?body) |- _ =>
        pose proof (fx_dep_encoder_source X C B cb source key Hlaws) as Hbody;
        rewrite Hcall in Hbody; exact Hbody
      end.
  - exact I.
Qed.

Lemma fx_dep_retreat_source_all X C B (cb : fx_index_external_model X C B)
    (source : fx_index_external_source X C B) ix (g : Graph.t X (X * X)) (r : dfs_result X (X *
      X)) :
  fx_dep_source_laws cb source ->
  Forall (fx_dep_retreat_source source) (snd (audit_rpo_schedule_retreats (fx_dep_rpo_cb cb ix) g
    r)).
Proof.
  intro Hlaws; pose proof (audit_rpo_retreat_receipts X (X * X)%type (fx_dep_event X C B)
    (fx_dep_rpo_cb cb ix) g r) as Hreceipts.
  eapply Forall_impl; [|exact Hreceipts].
  intros event Hreceipt; exact (fx_dep_retreat_event_source X C B cb source ix event Hlaws
    Hreceipt).
Qed.

(** The same scheduler execution retains source evidence for all nested callback bodies. *)
Theorem fx_rpo_scheduler_source_correct : fx_rpo_scheduler_source_statement.
Proof.
  intros X C A B EX S SS cb source Hlaws.
  pose proof (fx_dep_build_source X C A B EX S SS cb source Hlaws) as Hbuild.
  unfold fx_rpo_scheduler_counted.
  destruct (fx_dep_graph_build EX S SS cb) as [[g ix] build]; cbn [fst snd] in Hbuild.
  pose proof (fx_dep_prepare_source_all X C B EX g cb source ix Hlaws) as Hprepare.
  destruct (audit_prepare_source_counted EX g (fx_dep_prepare_cb cb ix)) as [p prepare_events];
    cbn [snd] in Hprepare.
  pose proof (fx_dep_dfs_source_all X C B EX g p cb source FinSet.empty (Graph.entries g) Hlaws)
    as Hdfs.
  destruct (audit_dfs_source_counted p (fx_dep_dfs_cb cb) FinSet.empty (Graph.entries g))
    as [search dfs_events]; cbn [snd] in Hdfs.
  destruct (audit_graph_reverse_fast_counted (postorder search) []) as [order work].
  pose proof (fx_dep_positions_source_all X C B cb source order Hlaws 1) as Hpositions.
  destruct (audit_rpo_schedule_positions (fx_dep_encoder cb) order 1) as [positions
    position_events];
    cbn [snd] in Hpositions.
  pose proof (fx_dep_retreat_source_all X C B cb source ix g search Hlaws) as Hretreats.
  destruct (audit_rpo_schedule_retreats (fx_dep_rpo_cb cb ix) g search) as [heads retreat_events];
    cbn [snd] in Hretreats |- *.
  repeat split; assumption.
Qed.

(** * Callback input envelope *)

Lemma fx_dep_max_member X (f : X -> nat) values x :
  In x values -> f x <= fold_right (fun x n => Nat.max n (f x)) 0 values.
Proof.
  induction values as [|value rest IH]; intro Hin.
  - contradiction.
  - cbn [fold_right] in *; destruct Hin as [Heq | Hin].
    + subst value; apply Nat.le_max_r.
    + eapply Nat.le_trans; [apply IH; exact Hin | apply Nat.le_max_l].
Qed.

Lemma fx_rpo_node_budget X C A B (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ib : fx_index_external_budget X C B) x :
  In x (Graph.nodes (dependency_graph EX S SS)) ->
  fx_dep_out_budget EX S SS (index_system EX S SS) ib x + fxi_encode_bound ib x + 64 <=
    fx_rpo_callback_max EX S SS ib.
Proof.
  intro Hin; unfold fx_rpo_callback_max.
  pose proof (fx_dep_max_member X
    (fun x => fx_dep_out_budget EX S SS (index_system EX S SS) ib x + fxi_encode_bound ib x)
    (Graph.nodes (dependency_graph EX S SS) ++ Graph.entries (dependency_graph EX S SS) ++
      map fst (flat_map (Graph.out (dependency_graph EX S SS))
        (Graph.nodes (dependency_graph EX S SS))) ++
      map snd (flat_map (Graph.out (dependency_graph EX S SS))
        (Graph.nodes (dependency_graph EX S SS)))) x) as Hmax.
  assert (Hscope : In x (Graph.nodes (dependency_graph EX S SS) ++
    Graph.entries (dependency_graph EX S SS) ++
    map fst (flat_map (Graph.out (dependency_graph EX S SS))
      (Graph.nodes (dependency_graph EX S SS))) ++
    map snd (flat_map (Graph.out (dependency_graph EX S SS))
      (Graph.nodes (dependency_graph EX S SS))))).
  { apply in_or_app; now left. }
  specialize (Hmax Hscope); cbv beta in Hmax; lia.
Qed.

Lemma fx_rpo_order_nodes X C A (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) x :
  In x (rpo (dfs (prepare EX (dependency_graph EX S SS)) FinSet.empty
    (Graph.entries (dependency_graph EX S SS)))) ->
  In x (Graph.nodes (dependency_graph EX S SS)).
Proof.
  intro Hin; set (g := dependency_graph EX S SS).
  set (p := prepare EX g).
  pose proof (dependency_graph_ready EX S SS) as Hready; fold g p in Hready.
  pose proof (proj1 Hready) as Hwf.
  pose proof (dfs_exact EX g p x (Graph.entries g) FinSet.empty Hready (entries_in Hwf)) as Hdfs.
  destruct Hdfs as [_ [_ [Hperm Hpre]]].
  fold g p in Hin; unfold rpo in Hin; rewrite <- rev_alt in Hin; apply in_rev in Hin.
  apply (Permutation_in x (Permutation_sym Hperm)) in Hin.
  apply Hpre in Hin; apply (reachable_dfs EX g p x Hready) in Hin.
  exact (reachable_in_nodes g x Hwf Hin).
Qed.

Lemma fx_rpo_max_floor X C A B (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ib : fx_index_external_budget X C B) :
  64 <= fx_rpo_callback_max EX S SS ib.
Proof.
  unfold fx_rpo_callback_max; lia.
Qed.

Lemma fx_dep_encoder_work X C B (cb : fx_index_external_model X C B)
    (ib : fx_index_external_budget X C B) x :
  fx_index_external_bounded cb ib ->
  fx_dep_events_work ib (snd (fx_dep_encoder cb x)) <= 16 + fxi_encode_bound ib x.
Proof.
  intro Hbounded; pose proof (proj1 (proj2 Hbounded) x) as Hbody.
  unfold fx_dep_encoder; destruct (fxi_encode cb x) as [code body]; cbn [snd] in Hbody |- *.
  change (16 + fxi_body_work ib body + 0 <= 16 + fxi_encode_bound ib x); lia.
Qed.

Lemma fx_dep_node_encoder_work X C A B (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B)
    (ib : fx_index_external_budget X C B) x :
  fx_index_external_bounded cb ib -> In x (Graph.nodes (dependency_graph EX S SS)) ->
  fx_dep_events_work ib (snd (fx_dep_encoder cb x)) <= fx_rpo_callback_max EX S SS ib.
Proof.
  intros Hbounded Hin.
  pose proof (fx_dep_encoder_work X C B cb ib x Hbounded) as Hwork.
  pose proof (fx_rpo_node_budget X C A B EX S SS ib x Hin) as Hbudget; lia.
Qed.

Lemma fx_dep_node_out_work X C A B (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B)
    (ib : fx_index_external_budget X C B) x :
  fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
  In x (Graph.nodes (dependency_graph EX S SS)) ->
  fx_dep_events_work ib (snd (fx_dep_out cb (index_system EX S SS) x)) <=
    fx_rpo_callback_max EX S SS ib.
Proof.
  intros Herase Hbounded Hin.
  pose proof (fx_dep_out_bound_correct X C A B EX S SS cb ib (index_system EX S SS) x
    Herase Hbounded) as Hwork.
  pose proof (fx_rpo_node_budget X C A B EX S SS ib x Hin) as Hbudget; lia.
Qed.

Lemma fx_dep_prepared_out_wf X E (EX : encoding X) (g : Graph.t X E) :
  Map.wf EX (out_index (prepare EX g)).
Proof.
  unfold prepare; cbn [out_index].
  induction (Graph.nodes g) as [|v rest IH].
  - apply Map.wf_empty.
  - apply Map.wf_set; exact IH.
Qed.

Lemma fx_dep_prepared_targets_nodes X E (EX : encoding X) (g : Graph.t X E) edge :
  ready EX g (prepare EX g) ->
  In edge (flat_map snd (Map.elements (out_index (prepare EX g)))) ->
  In (Graph.target g edge) (Graph.nodes g).
Proof.
  intros Hready Hin; apply in_flat_map in Hin; destruct Hin as [[key row] [Hrow Hedge]].
  cbn [snd] in Hedge.
  pose proof (Map.elements_sound EX key row (out_index (prepare EX g))
    (fx_dep_prepared_out_wf X E EX g) Hrow) as Hget.
  pose proof (prepare_succ EX g (Graph.nodes g) key) as Hsucc.
  change (index_edges EX (out_index (prepare EX g)) key =
    if existsb (fun u => Pos.eqb (encode EX u) (encode EX key)) (Graph.nodes g)
    then Graph.out g key else []) in Hsucc.
  unfold index_edges in Hsucc; rewrite Hget in Hsucc.
  destruct (existsb (fun u => Pos.eqb (encode EX u) (encode EX key)) (Graph.nodes g))
    eqn:Hfind.
  - apply existsb_exists in Hfind; destruct Hfind as [v [Hv Heq]].
    apply Pos.eqb_eq in Heq; apply (encode_injective EX) in Heq; subst v.
    eapply out_target_in; [exact (proj1 Hready) | exact Hv |].
    rewrite <- Hsucc; exact Hedge.
  - rewrite Hsucc in Hedge; contradiction.
Qed.

Lemma fx_dep_dfs_event_work X C A B (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B)
    (ib : fx_index_external_budget X C B) item :
  fx_index_external_bounded cb ib ->
  audit_dfs_source_event_wellformed item ->
  audit_dfs_event_receipts (fx_dep_dfs_cb cb) item ->
  audit_dfs_full_event_keys (Graph.nodes (dependency_graph EX S SS)) (fst item) ->
  fold_right (fun capture n => audit_graph_capture_work (fx_dep_event_work ib) capture + n)
    0 (snd item) <= fx_rpo_callback_max EX S SS ib.
Proof.
  intros Hbounded Hshape Hreceipts Hkeys.
  pose proof (fx_rpo_max_floor X C A B EX S SS ib) as Hfloor.
  destruct item as [event captures].
  destruct event as [site | edge target | v set result | v index result | v via before after |
    v before after | detail | pre post];
    cbn [fst snd audit_dfs_source_event_wellformed audit_dfs_full_event_keys] in *.
  - subst captures; cbn; lia.
  - destruct Hshape as [body Hshape]; subst captures.
    inversion Hreceipts as [|capture rest Hreceipt Htail]; subst capture rest.
    cbn [audit_dfs_capture_receipt fx_dep_dfs_cb audit_dfs_target_model] in Hreceipt.
    inversion Hreceipt; subst body.
    change (16 + 0 <= fx_rpo_callback_max EX S SS ib); lia.
  - destruct Hshape as [code [body Hshape]]; subst captures.
    inversion Hreceipts as [|capture rest Hreceipt Htail]; subst capture rest.
    cbn [audit_dfs_capture_receipt fx_dep_dfs_cb audit_dfs_encode_model] in Hreceipt.
    pose proof (fx_dep_node_encoder_work X C A B EX S SS cb ib v Hbounded Hkeys) as Hwork.
    rewrite Hreceipt in Hwork; cbn [snd] in Hwork;
    change (fx_dep_events_work ib body + 0 <= fx_rpo_callback_max EX S SS ib); lia.
  - destruct Hshape as [code [body Hshape]]; subst captures.
    inversion Hreceipts as [|capture rest Hreceipt Htail]; subst capture rest.
    cbn [audit_dfs_capture_receipt fx_dep_dfs_cb audit_dfs_encode_model] in Hreceipt.
    pose proof (fx_dep_node_encoder_work X C A B EX S SS cb ib v Hbounded Hkeys) as Hwork.
    rewrite Hreceipt in Hwork; cbn [snd] in Hwork;
    change (fx_dep_events_work ib body + 0 <= fx_rpo_callback_max EX S SS ib); lia.
  - subst captures; cbn; lia.
  - subst captures; cbn; lia.
  - destruct detail as [v edge input | v number input | v input | before after];
      cbn [audit_dfs_source_event_wellformed audit_dfs_full_event_keys] in *.
    + destruct Hshape as [code [body Hshape]]; subst captures.
      inversion Hreceipts as [|capture rest Hreceipt Htail]; subst capture rest.
      cbn [audit_dfs_capture_receipt fx_dep_dfs_cb audit_dfs_encode_model] in Hreceipt.
      pose proof (fx_dep_node_encoder_work X C A B EX S SS cb ib v Hbounded Hkeys) as Hwork.
      rewrite Hreceipt in Hwork; cbn [snd] in Hwork;
      change (fx_dep_events_work ib body + 0 <= fx_rpo_callback_max EX S SS ib); lia.
    + destruct Hshape as [code [body Hshape]]; subst captures.
      inversion Hreceipts as [|capture rest Hreceipt Htail]; subst capture rest.
      cbn [audit_dfs_capture_receipt fx_dep_dfs_cb audit_dfs_encode_model] in Hreceipt.
      pose proof (fx_dep_node_encoder_work X C A B EX S SS cb ib v Hbounded Hkeys) as Hwork.
      rewrite Hreceipt in Hwork; cbn [snd] in Hwork;
      change (fx_dep_events_work ib body + 0 <= fx_rpo_callback_max EX S SS ib); lia.
    + destruct Hshape as [code [body Hshape]]; subst captures.
      inversion Hreceipts as [|capture rest Hreceipt Htail]; subst capture rest.
      cbn [audit_dfs_capture_receipt fx_dep_dfs_cb audit_dfs_encode_model] in Hreceipt.
      pose proof (fx_dep_node_encoder_work X C A B EX S SS cb ib v Hbounded Hkeys) as Hwork.
      rewrite Hreceipt in Hwork; cbn [snd] in Hwork;
      change (fx_dep_events_work ib body + 0 <= fx_rpo_callback_max EX S SS ib); lia.
    + subst captures; cbn; lia.
  - subst captures; cbn; lia.
Qed.

Lemma fx_dep_dfs_keys_incl X E vertices nodes (event : audit_dfs_full_call X E) :
  incl vertices nodes -> audit_dfs_full_event_keys vertices event ->
  audit_dfs_full_event_keys nodes event.
Proof.
  intros Hincl Hkeys; destruct event as [site | edge target | v set result | v index result |
    v via before after | v before after | detail | pre post];
    cbn [audit_dfs_full_event_keys] in *; try exact I; try (apply Hincl; exact Hkeys).
  destruct detail; cbn [audit_dfs_full_event_keys] in *; try exact I; apply Hincl; exact Hkeys.
Qed.

Lemma fx_dep_dfs_body_sum X C B (ib : fx_index_external_budget X C B)
    (events : list (audit_dfs_nested_event X (X * X)
      (audit_graph_callback_capture X (X * X) (fx_dep_event X C B)))) maximum :
  Forall (fun item =>
    fold_right (fun capture n => audit_graph_capture_work (fx_dep_event_work ib) capture + n)
      0 (snd item) <= maximum) events ->
  audit_dfs_source_body_work (fx_dep_event_work ib) events <= length events * maximum.
Proof.
  intro Hbounds; induction Hbounds as [|item rest Hitem Hrest IH].
  - reflexivity.
  - change (fold_right (fun capture n =>
      audit_graph_capture_work (fx_dep_event_work ib) capture + n) 0 (snd item) +
      audit_dfs_source_body_work (fx_dep_event_work ib) rest <= S (length rest) * maximum).
    rewrite Nat.mul_succ_l, Nat.add_comm; apply Nat.add_le_mono; assumption.
Qed.

Lemma fx_dep_dfs_body_bound X C A B (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B)
    (ib : fx_index_external_budget X C B) :
  fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
  let g := dependency_graph EX S SS in let p := prepare EX g in
  let events := snd (audit_dfs_source_counted p (fx_dep_dfs_cb cb) FinSet.empty (Graph.entries g))
    in
  audit_dfs_source_body_work (fx_dep_event_work ib) events <=
    length events * fx_rpo_callback_max EX S SS ib.
Proof.
  intros Herase Hbounded; cbn zeta.
  set (g := dependency_graph EX S SS); set (p := prepare EX g).
  pose proof (dependency_graph_ready EX S SS) as Hready; fold g p in Hready.
  pose proof (fx_dep_dfs_erases X C A B EX S SS cb Herase) as Hcallbacks; fold g in Hcallbacks.
  pose proof (audit_dfs_source_correct X (X * X)%type (fx_dep_event X C B) EX g p
    (fx_dep_dfs_cb cb) (fx_dep_event_work ib) FinSet.empty (Graph.entries g) Hcallbacks) as Hsource.
  pose proof (audit_dfs_source_receipts p (fx_dep_dfs_cb cb) FinSet.empty (Graph.entries g))
    as Hreceipts.
  pose proof (audit_dfs_source_erases p (fx_dep_dfs_cb cb) FinSet.empty (Graph.entries g)
    Hcallbacks)
    as Herases.
  pose proof (audit_dfs_full_counted_keys p FinSet.empty (Graph.entries g)) as Hkeys.
  destruct (audit_dfs_source_counted p (fx_dep_dfs_cb cb) FinSet.empty (Graph.entries g))
    as [search events] eqn:Hsource_call; cbn [fst snd] in Hsource, Hreceipts, Herases |- *.
  destruct Hsource as [_ [Hshape _]].
  destruct (audit_dfs_full_counted p FinSet.empty (Graph.entries g)) as [original full_events];
    cbn [fst snd] in Hkeys, Herases.
  inversion Herases as [[Hresult Htrace]].
  subst full_events.
  assert (Hincl : incl (Graph.entries g ++ map (Graph.target g)
    (flat_map snd (Map.elements (out_index p)))) (Graph.nodes g)).
  { intros x Hin; apply in_app_iff in Hin; destruct Hin as [Hin | Hin].
    - exact (entries_in (proj1 Hready) x Hin).
    - apply in_map_iff in Hin; destruct Hin as [edge [Heq Hedge]]; subst x.
      unfold p in Hedge; apply (fx_dep_prepared_targets_nodes X (X * X)%type EX g edge Hready
        Hedge). }
  assert (Hbounds : Forall (fun item =>
    fold_right (fun capture n => audit_graph_capture_work (fx_dep_event_work ib) capture + n)
      0 (snd item) <= fx_rpo_callback_max EX S SS ib) events).
  { apply Forall_forall; intros item Hin.
    apply Forall_forall with (x := item) in Hshape; [|exact Hin].
    apply Forall_forall with (x := item) in Hreceipts; [|exact Hin].
    assert (Hkey : audit_dfs_full_event_keys (Graph.nodes g) (fst item)).
    { apply (fx_dep_dfs_keys_incl X (X * X)%type _ _ (fst item) Hincl).
      apply Forall_forall with (x := fst item) in Hkeys; [exact Hkeys |].
      apply in_map; exact Hin. }
    eapply fx_dep_dfs_event_work; [exact Hbounded | exact Hshape | exact Hreceipts | exact Hkey]. }
  apply fx_dep_dfs_body_sum; exact Hbounds.
Qed.

Lemma fx_dep_positions_body_bound X C A B (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B)
    (ib : fx_index_external_budget X C B) vertices :
  fx_index_external_bounded cb ib ->
  Forall (fun v => In v (Graph.nodes (dependency_graph EX S SS))) vertices ->
  forall next,
  let events := snd (audit_rpo_schedule_positions (fx_dep_encoder cb) vertices next) in
  audit_rpo_schedule_body_work (fx_dep_event_work ib) events <=
    length events * fx_rpo_callback_max EX S SS ib.
Proof.
  intros Hbounded Hnodes; induction Hnodes as [|v rest Hv Hrest IH]; intro next.
  - change (0 <= 1 * fx_rpo_callback_max EX S SS ib); lia.
  - cbn [audit_rpo_schedule_positions].
    destruct (audit_positive_succ next) as [next' successor_events].
    specialize (IH next').
    destruct (audit_rpo_schedule_positions (fx_dep_encoder cb) rest next') as [middle events];
      cbn [snd] in IH.
    pose proof (fx_dep_node_encoder_work X C A B EX S SS cb ib v Hbounded Hv) as Hbody.
    unfold audit_map_set.
    destruct (fx_dep_encoder cb v) as [code body]; cbn [snd] in Hbody.
    destruct (audit_trie_set code (v, next) middle) as [output trace].
    cbn [snd map app].
    change (audit_rpo_schedule_body_work (fx_dep_event_work ib)
      (events ++ [RpoScheduleMap (AuditMapSet v next code middle output body trace)]) <=
      length (RpoScheduleCase 1 :: RpoScheduleNext next next' successor_events ::
        events ++ [RpoScheduleMap (AuditMapSet v next code middle output body trace)]) *
        fx_rpo_callback_max EX S SS ib).
    rewrite audit_rpo_schedule_body_app; cbn [length]; rewrite length_app; cbn [length].
    change (audit_rpo_schedule_body_work (fx_dep_event_work ib) events +
      (fx_dep_events_work ib body + 0) <=
      Datatypes.S (Datatypes.S (length events + 1)) * fx_rpo_callback_max EX S SS ib).
    nia.
Qed.

Definition fx_dep_retreat_scope {X C B} (nodes : list X)
    (event : audit_rpo_graph_event X (X * X) (fx_dep_event X C B)) : Prop :=
  match event with
  | RpoGraphOut v _ _ => In v nodes
  | RpoGraphRank (AuditMapGet key _ _ _ _ _)
  | RpoGraphRank (AuditMapSet key _ _ _ _ _ _)
  | RpoGraphRank (AuditMapRemove key _ _ _ _ _)
  | RpoGraphSet (AuditSetMem key _ _ _ _ _)
  | RpoGraphSet (AuditSetAdd key _ _ _ _ _)
  | RpoGraphSet (AuditSetRemove key _ _ _ _ _) => In key nodes
  | _ => True
  end.

Lemma fx_dep_rank_scope X C B (cb : fx_index_external_model X C B) nodes key input :
  In key nodes -> Forall (fx_dep_retreat_scope nodes)
    (map RpoGraphRank (snd (audit_map_get (fx_dep_encoder cb) key input))).
Proof.
  intro Hin; unfold audit_map_get.
  destruct (fx_dep_encoder cb key) as [code body].
  destruct (audit_map_code_get code input) as [output trace].
  cbn [snd map]; constructor; [exact Hin | constructor].
Qed.

Lemma fx_dep_ancestor_scope X C B (cb : fx_index_external_model X C B)
    (r : dfs_result X (X * X)) nodes u v :
  In u nodes -> In v nodes -> Forall (fx_dep_retreat_scope nodes)
    (snd (audit_rpo_graph_ancestor (fx_dep_encoder cb) r u v)).
Proof.
  intros Hu Hv.
  pose proof (fx_dep_rank_scope X C B cb nodes u (pre_num r) Hu) as Hfirst.
  unfold audit_rpo_graph_ancestor.
  destruct (audit_map_get (fx_dep_encoder cb) u (pre_num r)) as [[a|] ea];
    cbn [snd] in Hfirst |- *; [|exact Hfirst].
  pose proof (fx_dep_rank_scope X C B cb nodes v (pre_num r) Hv) as Hsecond.
  destruct (audit_map_get (fx_dep_encoder cb) v (pre_num r)) as [[b|] eb];
    cbn [snd] in Hsecond |- *.
  2: { rewrite map_app; apply Forall_app; split; assumption. }
  pose proof (fx_dep_rank_scope X C B cb nodes u (post_num r) Hu) as Hthird.
  destruct (audit_map_get (fx_dep_encoder cb) u (post_num r)) as [[c|] ec];
    cbn [snd] in Hthird |- *.
  2: { repeat rewrite map_app; repeat rewrite Forall_app; repeat split; assumption. }
  pose proof (fx_dep_rank_scope X C B cb nodes v (post_num r) Hv) as Hfourth.
  destruct (audit_map_get (fx_dep_encoder cb) v (post_num r)) as [[d|] ed];
    cbn [snd] in Hfourth |- *.
  2: { repeat rewrite map_app; repeat rewrite Forall_app; repeat split; assumption. }
  destruct (audit_positive_leb a b) as [first ef].
  destruct (audit_positive_leb d c) as [second es].
  cbn [snd]; repeat rewrite map_app; repeat rewrite Forall_app.
  repeat split; try assumption; constructor; [exact I | constructor; [exact I | constructor]].
Qed.

Lemma fx_dep_filter_scope X C B (cb : fx_index_external_model X C B) ix
    (r : dfs_result X (X * X)) nodes edges :
  Forall (fun e => In (fst e) nodes /\ In (snd e) nodes) edges ->
  Forall (fx_dep_retreat_scope nodes) (snd (audit_rpo_graph_filter (fx_dep_rpo_cb cb ix) r edges)).
Proof.
  intro Hnodes; induction Hnodes as [|edge rest [Hsource Htarget] Hrest IH].
  - cbn [audit_rpo_graph_filter snd]; constructor; [exact I | constructor].
  - cbn [audit_rpo_graph_filter fx_dep_rpo_cb audit_rpo_graph_target audit_rpo_graph_source
      audit_rpo_graph_encode].
    pose proof (fx_dep_ancestor_scope X C B cb r nodes (snd edge) (fst edge) Htarget Hsource)
      as Hancestor.
    destruct (audit_rpo_graph_ancestor (fx_dep_encoder cb) r (snd edge) (fst edge))
      as [keep checks]; cbn [snd] in Hancestor.
    destruct (audit_rpo_graph_filter (fx_dep_rpo_cb cb ix) r rest) as [later events];
      cbn [snd] in IH |- *.
    constructor; [exact I | constructor; [exact I | constructor; [exact I |]]].
    apply Forall_app; split; assumption.
Qed.

Lemma fx_dep_targets_scope X C B (cb : fx_index_external_model X C B) ix nodes edges :
  Forall (fx_dep_retreat_scope nodes) (snd (audit_rpo_graph_targets (fx_dep_rpo_cb cb ix) edges)).
Proof.
  induction edges as [|edge rest IH].
  - cbn [audit_rpo_graph_targets snd]; constructor; [exact I | constructor].
  - cbn [audit_rpo_graph_targets fx_dep_rpo_cb audit_rpo_graph_target].
    destruct (audit_rpo_graph_targets (fx_dep_rpo_cb cb ix) rest) as [later events];
      cbn [snd] in IH |- *.
    constructor; [exact I | constructor; [exact I | exact IH]].
Qed.

Lemma fx_dep_collect_scope X C A B (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B) (r : dfs_result X (X * X))
    vertices :
  fx_index_external_erases EX S SS cb ->
  Forall (fun v => In v (Graph.nodes (dependency_graph EX S SS))) vertices ->
  Forall (fx_dep_retreat_scope (Graph.nodes (dependency_graph EX S SS)))
    (snd (audit_rpo_graph_collect (fx_dep_rpo_cb cb (index_system EX S SS)) r vertices)).
Proof.
  intros Herase Hvertices.
  pose proof (proj1 (dependency_graph_ready EX S SS)) as Hwf.
  induction Hvertices as [|v rest Hv Hrest IH].
  - cbn [audit_rpo_graph_collect snd]; constructor; [exact I | constructor].
  - cbn [audit_rpo_graph_collect fx_dep_rpo_cb audit_rpo_graph_out].
    pose proof (fx_dep_out_erasure_correct X C A B EX S SS cb (index_system EX S SS) v Herase)
      as Hout.
    destruct (fx_dep_out cb (index_system EX S SS) v) as [outgoing body]; cbn [fst] in Hout.
    change (outgoing = Graph.out (dependency_graph EX S SS) v) in Hout; subst outgoing.
    assert (Hedges : Forall (fun e => In (fst e) (Graph.nodes (dependency_graph EX S SS)) /\
      In (snd e) (Graph.nodes (dependency_graph EX S SS)))
      (Graph.out (dependency_graph EX S SS) v)).
    { apply Forall_forall; intros e He; split.
      - change (In (Graph.source (dependency_graph EX S SS) e)
          (Graph.nodes (dependency_graph EX S SS))).
        rewrite (out_source Hwf v e He); exact Hv.
      - change (In (Graph.target (dependency_graph EX S SS) e)
          (Graph.nodes (dependency_graph EX S SS))).
        exact (out_target_in Hwf v e Hv He). }
    pose proof (fx_dep_filter_scope X C B cb (index_system EX S SS) r
      (Graph.nodes (dependency_graph EX S SS)) (Graph.out (dependency_graph EX S SS) v) Hedges)
      as Hfilter.
    destruct (audit_rpo_graph_filter (fx_dep_rpo_cb cb (index_system EX S SS)) r
      (Graph.out (dependency_graph EX S SS) v)) as [retreats checks]; cbn [snd] in Hfilter.
    pose proof (fx_dep_targets_scope X C B cb (index_system EX S SS)
      (Graph.nodes (dependency_graph EX S SS)) retreats) as Htargets.
    destruct (audit_rpo_graph_targets (fx_dep_rpo_cb cb (index_system EX S SS)) retreats)
      as [targets target_events]; cbn [snd] in Htargets.
    destruct (audit_rpo_graph_collect (fx_dep_rpo_cb cb (index_system EX S SS)) r rest)
      as [later events]; cbn [snd] in IH |- *.
    constructor; [exact I | constructor; [exact Hv |]].
    repeat rewrite Forall_app; repeat split; assumption.
Qed.

Lemma fx_dep_add_scope X C B (cb : fx_index_external_model X C B) nodes vertices :
  Forall (fun v => In v nodes) vertices -> forall heads,
  Forall (fx_dep_retreat_scope nodes) (snd (audit_rpo_graph_add_all (fx_dep_encoder cb) vertices
    heads)).
Proof.
  intro Hvertices; induction Hvertices as [|v rest Hv Hrest IH]; intro heads.
  - cbn [audit_rpo_graph_add_all snd]; constructor; [exact I | constructor].
  - cbn [audit_rpo_graph_add_all].
    unfold audit_finset_add.
    destruct (fx_dep_encoder cb v) as [code body].
    destruct (audit_trie_set code (v, tt) heads) as [next trace].
    specialize (IH next).
    destruct (audit_rpo_graph_add_all (fx_dep_encoder cb) rest next) as [result later];
      cbn [snd] in IH |- *.
    constructor; [exact I | constructor; [exact Hv | exact IH]].
Qed.

Lemma fx_dep_collected_nodes X C A B (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B) (r : dfs_result X (X * X)) :
  fx_index_external_erases EX S SS cb ->
  Forall (fun v => In v (Graph.nodes (dependency_graph EX S SS)))
    (fst (audit_rpo_graph_collect (fx_dep_rpo_cb cb (index_system EX S SS)) r
      (Graph.nodes (dependency_graph EX S SS)))).
Proof.
  intro Herase.
  pose proof (fx_dep_retreat_erases X C A B EX S SS cb Herase) as Hcallbacks.
  rewrite (audit_rpo_graph_collect_erases X (X * X)%type (fx_dep_event X C B) EX
    (dependency_graph EX S SS) (fx_dep_rpo_cb cb (index_system EX S SS)) r
    (Graph.nodes (dependency_graph EX S SS)) Hcallbacks).
  apply Forall_forall; intros v Hin; apply in_flat_map in Hin; destruct Hin as [u [Hu Hin]].
  apply in_map_iff in Hin; destruct Hin as [edge [Heq Hedge]]; subst v.
  apply filter_In in Hedge; destruct Hedge as [Hedge _].
  pose proof (proj1 (dependency_graph_ready EX S SS)) as Hwf.
  exact (out_target_in Hwf u edge Hu Hedge).
Qed.

Lemma fx_dep_retreat_scope_all X C A B (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B) (r : dfs_result X (X * X)) :
  fx_index_external_erases EX S SS cb ->
  Forall (fx_dep_retreat_scope (Graph.nodes (dependency_graph EX S SS)))
    (snd (audit_rpo_schedule_retreats (fx_dep_rpo_cb cb (index_system EX S SS))
      (dependency_graph EX S SS) r)).
Proof.
  intro Herase.
  assert (Hnodes : Forall (fun v => In v (Graph.nodes (dependency_graph EX S SS)))
    (Graph.nodes (dependency_graph EX S SS))).
  { apply Forall_forall; intros v Hin; exact Hin. }
  pose proof (fx_dep_collect_scope X C A B EX S SS cb r
    (Graph.nodes (dependency_graph EX S SS)) Herase Hnodes) as Hcollect.
  pose proof (fx_dep_collected_nodes X C A B EX S SS cb r Herase) as Hcollected.
  unfold audit_rpo_schedule_retreats.
  destruct (audit_rpo_graph_collect (fx_dep_rpo_cb cb (index_system EX S SS)) r
    (Graph.nodes (dependency_graph EX S SS))) as [vertices events];
      cbn [fst snd] in Hcollect, Hcollected.
  pose proof (fx_dep_add_scope X C B cb (Graph.nodes (dependency_graph EX S SS)) vertices
    Hcollected FinSet.empty) as Hadd.
  cbn [fx_dep_rpo_cb audit_rpo_graph_encode].
  destruct (audit_rpo_graph_add_all (fx_dep_encoder cb) vertices FinSet.empty)
    as [result adds]; cbn [snd] in Hadd |- *.
  apply Forall_app; split; assumption.
Qed.

Lemma fx_dep_retreat_event_work X C A B (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B)
    (ib : fx_index_external_budget X C B) event :
  fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
  audit_rpo_graph_receipt (fx_dep_rpo_cb cb (index_system EX S SS)) event ->
  fx_dep_retreat_scope (Graph.nodes (dependency_graph EX S SS)) event ->
  audit_rpo_graph_event_body (fx_dep_event_work ib) event <= fx_rpo_callback_max EX S SS ib.
Proof.
  intros Herase Hbounded Hreceipt Hscope.
  pose proof (fx_rpo_max_floor X C A B EX S SS ib) as Hfloor.
  destruct event as [site | v output body | edge output body | edge output body | item | item |
    left right result trace]; cbn [audit_rpo_graph_receipt fx_dep_rpo_cb audit_rpo_graph_encode]
      in Hreceipt; cbn [fx_dep_retreat_scope audit_rpo_graph_event_body] in Hscope |- *.
  - lia.
  - change (fx_dep_out cb (index_system EX S SS) v = (output, body)) in Hreceipt.
    pose proof (fx_dep_node_out_work X C A B EX S SS cb ib v Herase Hbounded Hscope) as Hwork.
    rewrite Hreceipt in Hwork; exact Hwork.
  - inversion Hreceipt; subst body; change (16 + 0 <= fx_rpo_callback_max EX S SS ib); lia.
  - inversion Hreceipt; subst body; change (16 + 0 <= fx_rpo_callback_max EX S SS ib); lia.
  - destruct item; cbn [audit_rpo_graph_receipt fx_dep_rpo_cb audit_rpo_graph_encode] in Hreceipt;
      cbn [fx_dep_retreat_scope audit_rpo_graph_event_body] in Hscope |- *;
      match goal with
      | Hcall : fx_dep_encoder cb ?key = (?code, ?body), Hnode : In ?key _ |- _ =>
        pose proof (fx_dep_node_encoder_work X C A B EX S SS cb ib key Hbounded Hnode) as Hwork;
        rewrite Hcall in Hwork; exact Hwork
      end.
  - destruct item; cbn [audit_rpo_graph_receipt fx_dep_rpo_cb audit_rpo_graph_encode] in Hreceipt;
      cbn [fx_dep_retreat_scope audit_rpo_graph_event_body] in Hscope |- *; try lia;
      match goal with
      | Hcall : fx_dep_encoder cb ?key = (?code, ?body), Hnode : In ?key _ |- _ =>
        pose proof (fx_dep_node_encoder_work X C A B EX S SS cb ib key Hbounded Hnode) as Hwork;
        rewrite Hcall in Hwork; exact Hwork
      end.
  - lia.
Qed.

Lemma fx_dep_retreat_body_bound X C A B (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B)
    (ib : fx_index_external_budget X C B) (r : dfs_result X (X * X)) :
  fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
  let events := snd (audit_rpo_schedule_retreats (fx_dep_rpo_cb cb (index_system EX S SS))
    (dependency_graph EX S SS) r) in
  audit_rpo_graph_body_work (fx_dep_event_work ib) events <=
    length events * fx_rpo_callback_max EX S SS ib.
Proof.
  intros Herase Hbounded; cbn zeta.
  pose proof (audit_rpo_retreat_receipts X (X * X)%type (fx_dep_event X C B)
    (fx_dep_rpo_cb cb (index_system EX S SS)) (dependency_graph EX S SS) r) as Hreceipts.
  pose proof (fx_dep_retreat_scope_all X C A B EX S SS cb r Herase) as Hscope.
  set (events := snd (audit_rpo_schedule_retreats (fx_dep_rpo_cb cb (index_system EX S SS))
    (dependency_graph EX S SS) r)) in *.
  assert (Hbounds : Forall (fun event => audit_rpo_graph_event_body (fx_dep_event_work ib) event <=
    fx_rpo_callback_max EX S SS ib) events).
  { apply Forall_forall; intros event Hin.
    apply Forall_forall with (x := event) in Hreceipts; [|exact Hin].
    apply Forall_forall with (x := event) in Hscope; [|exact Hin].
    exact (fx_dep_retreat_event_work X C A B EX S SS cb ib event Herase Hbounded Hreceipts
      Hscope). }
  clear Hreceipts Hscope.
  induction Hbounds as [|event rest Hbody Hrest IH].
  - reflexivity.
  - change (audit_rpo_graph_event_body (fx_dep_event_work ib) event +
      audit_rpo_graph_body_work (fx_dep_event_work ib) rest <=
      Datatypes.S (length rest) * fx_rpo_callback_max EX S SS ib).
    rewrite Nat.mul_succ_l, Nat.add_comm; apply Nat.add_le_mono; assumption.
Qed.

(** * Preparation callback input envelope *)

Definition fx_dep_prepare_scope {X C B} (nodes : list X)
    (event : audit_prepare_source_event X (X * X) (fx_dep_event X C B)) : Prop :=
  match event with
  | PrepareSourceOut v _ _ => In v nodes
  | PrepareSourceMap (AuditMapGet key _ _ _ _ _)
  | PrepareSourceMap (AuditMapSet key _ _ _ _ _ _)
  | PrepareSourceMap (AuditMapRemove key _ _ _ _ _) => In key nodes
  | _ => True
  end.

Lemma fx_dep_prepare_get_scope X C B (cb : fx_index_external_model X C B) nodes key input :
  In key nodes -> Forall (fx_dep_prepare_scope nodes)
    (map PrepareSourceMap (snd (audit_map_get (fx_dep_encoder cb) key input))).
Proof.
  intro Hin; unfold audit_map_get.
  destruct (fx_dep_encoder cb key) as [code body].
  destruct (audit_map_code_get code input) as [output trace].
  cbn [snd map]; constructor; [exact Hin | constructor].
Qed.

Lemma fx_dep_prepare_set_scope X C B (cb : fx_index_external_model X C B) nodes key value input :
  In key nodes -> Forall (fx_dep_prepare_scope nodes)
    (map PrepareSourceMap (snd (audit_map_set (fx_dep_encoder cb) key value input))).
Proof.
  intro Hin; unfold audit_map_set.
  destruct (fx_dep_encoder cb key) as [code body].
  destruct (audit_trie_set code (key, value) input) as [output trace].
  cbn [snd map]; constructor; [exact Hin | constructor].
Qed.

Lemma fx_dep_prepare_out_scope X C B (cb : fx_index_external_model X C B) ix nodes vertices :
  Forall (fun v => In v nodes) vertices -> forall initial,
  Forall (fx_dep_prepare_scope nodes)
    (snd (audit_prepare_source_out (fx_dep_prepare_cb cb ix) vertices initial)).
Proof.
  intro Hnodes; induction Hnodes as [|v rest Hv Hrest IH]; intro initial.
  - cbn [audit_prepare_source_out snd]; constructor; [exact I | constructor].
  - cbn [audit_prepare_source_out fx_dep_prepare_cb audit_prepare_out_model
    audit_prepare_encode_model].
    specialize (IH initial).
    destruct (audit_prepare_source_out (fx_dep_prepare_cb cb ix) rest initial) as [middle events];
      cbn [snd] in IH.
    destruct (fx_dep_out cb ix v) as [outgoing body].
    pose proof (fx_dep_prepare_set_scope X C B cb nodes v outgoing middle Hv) as Hset.
    destruct (audit_map_set (fx_dep_encoder cb) v outgoing middle) as [result writes];
      cbn [snd] in Hset |- *.
    constructor; [exact I |].
    repeat rewrite Forall_app; repeat split; try assumption.
    constructor; [exact Hv | constructor].
Qed.

Lemma fx_dep_prepare_edges_scope X C B (cb : fx_index_external_model X C B) ix nodes edges :
  Forall (fun e => In (snd e) nodes) edges -> forall initial,
  Forall (fx_dep_prepare_scope nodes)
    (snd (audit_prepare_source_edges (fx_dep_prepare_cb cb ix) edges initial)).
Proof.
  intro Hnodes; induction Hnodes as [|edge rest Hedge Hrest IH]; intro initial.
  - cbn [audit_prepare_source_edges snd]; constructor; [exact I | constructor].
  - cbn [audit_prepare_source_edges fx_dep_prepare_cb audit_prepare_target_model
      audit_prepare_encode_model].
    specialize (IH initial).
    destruct (audit_prepare_source_edges (fx_dep_prepare_cb cb ix) rest initial)
      as [middle events]; cbn [snd] in IH.
    pose proof (fx_dep_prepare_get_scope X C B cb nodes (snd edge) middle Hedge) as Hget.
    destruct (audit_map_get (fx_dep_encoder cb) (snd edge) middle) as [found reads];
      cbn [snd] in Hget.
    pose proof (fx_dep_prepare_set_scope X C B cb nodes (snd edge)
      (edge :: match found with
      | Some xs => xs
      | None => []
      end) middle Hedge) as Hset.
    destruct (audit_map_set (fx_dep_encoder cb) (snd edge)
      (edge :: match found with
      | Some xs => xs
      | None => []
      end) middle) as [next writes];
      cbn [snd] in Hset |- *.
    constructor; [exact I |].
    repeat rewrite Forall_app; repeat split; try assumption; repeat constructor.
Qed.

Lemma fx_dep_prepare_in_scope X C A B (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B) vertices :
  fx_index_external_erases EX S SS cb ->
  Forall (fun v => In v (Graph.nodes (dependency_graph EX S SS))) vertices -> forall initial,
  Forall (fx_dep_prepare_scope (Graph.nodes (dependency_graph EX S SS)))
    (snd (audit_prepare_source_in (fx_dep_prepare_cb cb (index_system EX S SS)) vertices initial)).
Proof.
  intros Herase Hnodes; pose proof (proj1 (dependency_graph_ready EX S SS)) as Hwf.
  induction Hnodes as [|v rest Hv Hrest IH]; intro initial.
  - cbn [audit_prepare_source_in snd]; constructor; [exact I | constructor].
  - cbn [audit_prepare_source_in fx_dep_prepare_cb audit_prepare_out_model].
    specialize (IH initial).
    destruct (audit_prepare_source_in (fx_dep_prepare_cb cb (index_system EX S SS)) rest initial)
      as [middle events]; cbn [snd] in IH.
    pose proof (fx_dep_out_erasure_correct X C A B EX S SS cb (index_system EX S SS) v Herase)
      as Hout.
    destruct (fx_dep_out cb (index_system EX S SS) v) as [outgoing body]; cbn [fst] in Hout.
    change (outgoing = Graph.out (dependency_graph EX S SS) v) in Hout; subst outgoing.
    assert (Hedges : Forall (fun e => In (snd e) (Graph.nodes (dependency_graph EX S SS)))
      (Graph.out (dependency_graph EX S SS) v)).
    { apply Forall_forall; intros e He.
      change (In (Graph.target (dependency_graph EX S SS) e)
        (Graph.nodes (dependency_graph EX S SS))).
      exact (out_target_in Hwf v e Hv He). }
    pose proof (fx_dep_prepare_edges_scope X C B cb (index_system EX S SS)
      (Graph.nodes (dependency_graph EX S SS)) (Graph.out (dependency_graph EX S SS) v)
      Hedges middle) as Hedges_scope.
    destruct (audit_prepare_source_edges (fx_dep_prepare_cb cb (index_system EX S SS))
      (Graph.out (dependency_graph EX S SS) v) middle) as [result edges];
      cbn [snd] in Hedges_scope |- *.
    constructor; [exact I |].
    repeat rewrite Forall_app; repeat split; try assumption.
    constructor; [exact Hv | constructor].
Qed.

Lemma fx_dep_prepare_count_scope X C B (cb : fx_index_external_model X C B) ix nodes vertices :
  Forall (fun v => In v nodes) vertices ->
  Forall (fx_dep_prepare_scope nodes)
    (snd (audit_prepare_source_edge_count (fx_dep_prepare_cb cb ix) vertices)).
Proof.
  intro Hnodes; induction Hnodes as [|v rest Hv Hrest IH].
  - cbn [audit_prepare_source_edge_count snd]; constructor; [exact I | constructor].
  - cbn [audit_prepare_source_edge_count fx_dep_prepare_cb audit_prepare_out_model].
    destruct (audit_prepare_source_edge_count (fx_dep_prepare_cb cb ix) rest) as [count events];
      cbn [snd] in IH.
    destruct (fx_dep_out cb ix v) as [outgoing body]; cbn [snd] in *.
    constructor; [exact I |].
    apply Forall_app; split; [exact IH |].
    constructor; [exact Hv | constructor; [exact I | constructor]].
Qed.

Lemma fx_dep_prepare_scope_all X C A B (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B) :
  fx_index_external_erases EX S SS cb ->
  Forall (fx_dep_prepare_scope (Graph.nodes (dependency_graph EX S SS)))
    (snd (audit_prepare_source_counted EX (dependency_graph EX S SS)
      (fx_dep_prepare_cb cb (index_system EX S SS)))).
Proof.
  intro Herase.
  assert (Hnodes : Forall (fun v => In v (Graph.nodes (dependency_graph EX S SS)))
    (Graph.nodes (dependency_graph EX S SS))).
  { apply Forall_forall; intros v Hin; exact Hin. }
  pose proof (fx_dep_prepare_out_scope X C B cb (index_system EX S SS)
    (Graph.nodes (dependency_graph EX S SS)) (Graph.nodes (dependency_graph EX S SS))
    Hnodes Map.empty) as Hout.
  pose proof (fx_dep_prepare_in_scope X C A B EX S SS cb (Graph.nodes (dependency_graph EX S SS))
    Herase Hnodes Map.empty) as Hin.
  pose proof (fx_dep_prepare_count_scope X C B cb (index_system EX S SS)
    (Graph.nodes (dependency_graph EX S SS)) (Graph.nodes (dependency_graph EX S SS)) Hnodes)
    as Hcount.
  unfold audit_prepare_source_counted.
  destruct (audit_prepare_source_out (fx_dep_prepare_cb cb (index_system EX S SS))
    (Graph.nodes (dependency_graph EX S SS)) Map.empty) as [out out_events]; cbn [snd] in Hout.
  destruct (audit_prepare_source_in (fx_dep_prepare_cb cb (index_system EX S SS))
    (Graph.nodes (dependency_graph EX S SS)) Map.empty) as [incoming in_events]; cbn [snd] in Hin.
  destruct (audit_prepare_source_edge_count (fx_dep_prepare_cb cb (index_system EX S SS))
    (Graph.nodes (dependency_graph EX S SS))) as [count count_events]; cbn [snd] in Hcount |- *.
  repeat rewrite Forall_app; repeat split; try assumption; repeat constructor.
Qed.

Lemma fx_dep_prepare_event_work X C A B (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B)
    (ib : fx_index_external_budget X C B) event :
  fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
  audit_source_receipt (fx_dep_prepare_cb cb (index_system EX S SS)) event ->
  fx_dep_prepare_scope (Graph.nodes (dependency_graph EX S SS)) event ->
  audit_prepare_source_body_event_work (fx_dep_event_work ib) event <=
    fx_rpo_callback_max EX S SS ib.
Proof.
  intros Herase Hbounded Hreceipt Hscope.
  pose proof (fx_rpo_max_floor X C A B EX S SS ib) as Hfloor.
  destruct event as [site | v outgoing body | edge target body | item | amount | nodes edges fuel];
    cbn [audit_source_receipt fx_dep_prepare_cb audit_prepare_out_model audit_prepare_target_model
      audit_prepare_encode_model] in Hreceipt;
    cbn [fx_dep_prepare_scope audit_prepare_source_body_event_work] in Hscope |- *.
  - lia.
  - pose proof (fx_dep_node_out_work X C A B EX S SS cb ib v Herase Hbounded Hscope) as Hwork.
    rewrite Hreceipt in Hwork; exact Hwork.
  - inversion Hreceipt; subst body; change (16 + 0 <= fx_rpo_callback_max EX S SS ib); lia.
  - destruct item; cbn [audit_source_receipt fx_dep_prepare_cb audit_prepare_encode_model] in
    Hreceipt;
      cbn [fx_dep_prepare_scope audit_prepare_source_body_event_work] in Hscope |- *;
      match goal with
      | Hcall : fx_dep_encoder cb ?key = (?code, ?body), Hnode : In ?key _ |- _ =>
        pose proof (fx_dep_node_encoder_work X C A B EX S SS cb ib key Hbounded Hnode) as Hwork;
        rewrite Hcall in Hwork; exact Hwork
      end.
  - lia.
  - lia.
Qed.

Lemma fx_dep_prepare_body_bound X C A B (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B)
    (ib : fx_index_external_budget X C B) :
  fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb ib ->
  let events := snd (audit_prepare_source_counted EX (dependency_graph EX S SS)
    (fx_dep_prepare_cb cb (index_system EX S SS))) in
  audit_prepare_source_body_work (fx_dep_event_work ib) events <=
    length events * fx_rpo_callback_max EX S SS ib.
Proof.
  intros Herase Hbounded; cbn zeta.
  pose proof (audit_prepare_source_with_receipts X (X * X)%type (fx_dep_event X C B) EX
    (dependency_graph EX S SS) (fx_dep_prepare_cb cb (index_system EX S SS))
    (fx_dep_event_work ib) (fx_dep_prepare_erases X C A B EX S SS cb Herase)) as Hrun.
  pose proof (fx_dep_prepare_scope_all X C A B EX S SS cb Herase) as Hscope.
  destruct (audit_prepare_source_counted EX (dependency_graph EX S SS)
    (fx_dep_prepare_cb cb (index_system EX S SS))) as [prepared events];
    cbn [fst snd] in Hrun, Hscope |- *.
  destruct Hrun as [_ [_ [_ Hreceipts]]].
  assert (Hbounds : Forall (fun event =>
    audit_prepare_source_body_event_work (fx_dep_event_work ib) event <=
      fx_rpo_callback_max EX S SS ib) events).
  { apply Forall_forall; intros event Hin.
    apply Forall_forall with (x := event) in Hreceipts; [|exact Hin].
    apply Forall_forall with (x := event) in Hscope; [|exact Hin].
    exact (fx_dep_prepare_event_work X C A B EX S SS cb ib event Herase Hbounded Hreceipts
      Hscope). }
  clear Hreceipts Hscope.
  induction Hbounds as [|event rest Hbody Hrest IH].
  - reflexivity.
  - change (audit_prepare_source_body_event_work (fx_dep_event_work ib) event +
      audit_prepare_source_body_work (fx_dep_event_work ib) rest <=
      Datatypes.S (length rest) * fx_rpo_callback_max EX S SS ib).
    rewrite Nat.mul_succ_l, Nat.add_comm; apply Nat.add_le_mono; assumption.
Qed.

(** Scheduler preparation charges the same execution within its input-derived budget. *)
Theorem fx_rpo_scheduler_input_bound_correct : fx_rpo_scheduler_input_bound_statement.
Proof.
  intros X C A B EX S SS cb ib Herase Hbounded.
  pose proof (fx_dep_build_erasure_correct X C A B EX S SS cb Herase) as Hbuild.
  pose proof (fx_dep_build_bound_correct X C A B EX S SS cb ib Herase Hbounded) as Hbuild_work.
  pose proof (fx_rpo_receipt_count_correct X C A B EX S SS cb Herase) as Hcount.
  unfold fx_rpo_scheduler_counted in Hcount |- *.
  destruct (fx_dep_graph_build EX S SS cb) as [[g ix] build] eqn:Hbuild_call.
  cbn [fst snd] in Hbuild, Hbuild_work; destruct Hbuild as [Hg Hix]; subst g ix.
  pose proof (audit_prepare_source_correct X (X * X)%type (fx_dep_event X C B) EX
    (dependency_graph EX S SS) (fx_dep_prepare_cb cb (index_system EX S SS))
    (fx_dep_event_work ib) (fx_dep_prepare_erases X C A B EX S SS cb Herase)) as Hprepare.
  pose proof (fx_dep_prepare_body_bound X C A B EX S SS cb ib Herase Hbounded) as Hprepare_body.
  destruct (audit_prepare_source_counted EX (dependency_graph EX S SS)
    (fx_dep_prepare_cb cb (index_system EX S SS))) as [p prepare_events] eqn:Hprepare_call.
  cbn [fst snd] in Hprepare, Hprepare_body; destruct Hprepare as [Hp [_ Hprepare_work]]; subst p.
  pose proof (audit_dfs_source_correct X (X * X)%type (fx_dep_event X C B) EX
    (dependency_graph EX S SS) (prepare EX (dependency_graph EX S SS)) (fx_dep_dfs_cb cb)
    (fx_dep_event_work ib) FinSet.empty (Graph.entries (dependency_graph EX S SS))
    (fx_dep_dfs_erases X C A B EX S SS cb Herase)) as Hdfs.
  pose proof (fx_dep_dfs_body_bound X C A B EX S SS cb ib Herase Hbounded) as Hdfs_body.
  destruct (audit_dfs_source_counted (prepare EX (dependency_graph EX S SS))
    (fx_dep_dfs_cb cb) FinSet.empty (Graph.entries (dependency_graph EX S SS)))
    as [search dfs_events] eqn:Hdfs_call.
  cbn zeta in Hdfs_body; rewrite Hdfs_call in Hdfs_body.
  cbn [fst snd] in Hdfs, Hdfs_body; destruct Hdfs as [Hsearch [_ [_ Hdfs_work]]]; subst search.
  pose proof (audit_graph_reverse_fast_counted_holds X
    (postorder (dfs (prepare EX (dependency_graph EX S SS)) FinSet.empty
      (Graph.entries (dependency_graph EX S SS)))) []) as Hreverse.
  destruct (audit_graph_reverse_fast_counted
    (postorder (dfs (prepare EX (dependency_graph EX S SS)) FinSet.empty
      (Graph.entries (dependency_graph EX S SS)))) []) as [order work] eqn:Hreverse_call.
  cbn [fst snd] in Hreverse; destruct Hreverse as [_ [Horder [_ Hreverse_work]]].
  change (order = rpo (dfs (prepare EX (dependency_graph EX S SS)) FinSet.empty
    (Graph.entries (dependency_graph EX S SS)))) in Horder; subst order.
  assert (Hnodes : Forall (fun v => In v (Graph.nodes (dependency_graph EX S SS)))
    (rpo (dfs (prepare EX (dependency_graph EX S SS)) FinSet.empty
      (Graph.entries (dependency_graph EX S SS))))).
  { apply Forall_forall; intros v Hin; exact (fx_rpo_order_nodes X C A EX S SS v Hin). }
  pose proof (audit_rpo_positions_bound_correct X (fx_dep_event X C B) EX (fx_dep_encoder cb)
    (fx_dep_event_work ib) (rpo (dfs (prepare EX (dependency_graph EX S SS)) FinSet.empty
      (Graph.entries (dependency_graph EX S SS)))) 1%positive
    (fx_dep_encoder_erases X C A B EX S SS cb Herase)) as Hpositions.
  pose proof (fx_dep_positions_body_bound X C A B EX S SS cb ib _ Hbounded Hnodes 1%positive) as
    Hposition_body.
  destruct (audit_rpo_schedule_positions (fx_dep_encoder cb)
    (rpo (dfs (prepare EX (dependency_graph EX S SS)) FinSet.empty
      (Graph.entries (dependency_graph EX S SS)))) 1) as [positions position_events]
    eqn:Hposition_call.
  cbn [fst snd] in Hpositions, Hposition_body; destruct Hpositions as [_ Hposition_work].
  pose proof (audit_rpo_retreats_bound_correct X (X * X)%type (fx_dep_event X C B) EX
    (dependency_graph EX S SS)
    (dfs (prepare EX (dependency_graph EX S SS)) FinSet.empty
      (Graph.entries (dependency_graph EX S SS))) (fx_dep_rpo_cb cb (index_system EX S SS))
    (fx_dep_event_work ib) (fx_dep_retreat_erases X C A B EX S SS cb Herase)) as Hretreat.
  pose proof (fx_dep_retreat_body_bound X C A B EX S SS cb ib
    (dfs (prepare EX (dependency_graph EX S SS)) FinSet.empty
      (Graph.entries (dependency_graph EX S SS))) Herase Hbounded) as Hretreat_body.
  destruct (audit_rpo_schedule_retreats (fx_dep_rpo_cb cb (index_system EX S SS))
    (dependency_graph EX S SS)
    (dfs (prepare EX (dependency_graph EX S SS)) FinSet.empty
      (Graph.entries (dependency_graph EX S SS)))) as [heads retreat_events] eqn:Hretreat_call.
  cbn [fst snd] in Hretreat, Hretreat_body; destruct Hretreat as [_ Hretreat_work].
  cbn [fx_rpo_prepare_events fx_rpo_dfs_events fx_rpo_position_events fx_rpo_retreat_events]
    in Hcount.
  unfold fx_rpo_scheduler_work, fx_rpo_scheduler_budget.
  cbn [fx_rpo_build_events fx_rpo_reverse_work fx_rpo_prepare_events fx_rpo_dfs_events
    fx_rpo_position_events fx_rpo_retreat_events].
  set (maximum := fx_rpo_callback_max EX S SS ib) in *.
  set (limit := fx_rpo_receipt_count_limit EX S SS) in *.
  assert (Hproduct : (length prepare_events + length dfs_events + length position_events +
    length retreat_events) * maximum <= limit * maximum).
  { apply Nat.mul_le_mono_r; exact Hcount. }
  nia.
Qed.
