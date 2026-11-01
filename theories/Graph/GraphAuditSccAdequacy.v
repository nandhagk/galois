(** * Strongly connected component audit adequacy

    Relates the counted Tarjan traversal and its source receipts to graph operations.
    For example, the reversal contract covers the component list returned by traversal.
    Builds on: GraphAuditScc, GraphAuditDfsAdequacy, GraphAuditBaseAdequacy,
    CollectionsAuditTrieAdequacy, CollectionsAuditCompareAdequacy,
    CollectionsAuditPrimitiveAdequacy and CollectionsAuditEncodingAdequacy. *)

From Stdlib Require Import List PArith Arith ZArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditCost CollectionsAuditCompare CollectionsAuditCompareAdequacy CollectionsAuditTrie
  CollectionsAuditTrieAdequacy CollectionsAuditPrimitiveAdequacy CollectionsAuditEncodingAdequacy.
From Galois.Graph Require Import GraphCore GraphPrepare GraphScc GraphAuditBase GraphAuditDfs
  GraphAuditScc GraphAuditBaseAdequacy GraphAuditDfsAdequacy.
Import List.ListNotations.

(** * Reversal and positive minimum *)

(** Both reversal implementations have the stated run and work guarantees. *)
Theorem audit_scc_reverse_run_holds : audit_scc_reverse_run_statement.
Proof.
  repeat split.
  - exact audit_graph_reverse_run_holds.
  - exact audit_graph_reverse_fast_run_holds.
  - exact audit_graph_reverse_fast_counted_holds.
Qed.

(** The counted positive minimum returns the standard minimum within the comparison bound. *)
Theorem audit_scc_min_source_model_holds : audit_scc_min_source_model_statement.
Proof.
  intros left right.
  pose proof (audit_positive_compare_cont Eq left right) as Hcompare.
  unfold audit_scc_min_source_model, CollectionsAuditCompare.audit_positive_compare.
  destruct (CollectionsAuditCompare.audit_positive_compare_cont Eq left right)
    as [order events] eqn:Hrun.
  cbn in Hcompare |- *.
  destruct Hcompare as [Horder Hbound].
  split.
  - unfold Pos.min, Pos.compare; rewrite <- Horder; destruct order; reflexivity.
  - exact Hbound.
Qed.

(** * Tarjan helper erasure *)

(** Popping the counted stack returns the same members and persistent maps as the source. *)
Lemma audit_tarjan_pop_erases {V E} (EV : encoding V) root i xs links owners :
    fst (@audit_tarjan_pop_counted V E EV root i xs links owners) =
      tarjan_pop EV root i xs links owners.
Proof.
  revert links owners; induction xs as [|v rest IH]; intros links owners.
  - reflexivity.
  - cbn [audit_tarjan_pop_counted tarjan_pop].
    destruct (Pos.eqb (encode EV v) (encode EV root)) eqn:Hequal; [reflexivity|].
    specialize (IH (Map.remove EV v links) (Map.set EV v i owners)).
    destruct (audit_tarjan_pop_counted EV root i rest
      (Map.remove EV v links) (Map.set EV v i owners))
      as [[[[members tail] links'] owners'] events].
    cbn in IH; rewrite <- IH; reflexivity.
Qed.

(** Counted lowering returns the same updated lowlink state as the source helper. *)
Lemma audit_tarjan_lower_erases :
    forall V E (EV : encoding V) v n (st : tarjan_state V E),
      fst (audit_tarjan_lower_counted EV v n st) = tarjan_lower EV v n st.
Proof.
  intros V E EV v n st; unfold audit_tarjan_lower_counted, tarjan_lower.
  destruct (Map.get EV v (low st)); reflexivity.
Qed.

(** Counted emission returns the source component and persistent maps after the same pop. *)
Lemma audit_tarjan_emit_erases :
    forall V E (EV : encoding V) root (st : tarjan_state V E),
      fst (audit_tarjan_emit_counted EV root st) = tarjan_emit EV root st.
Proof.
  intros V E EV root st.
  unfold audit_tarjan_emit_counted, tarjan_emit, tarjan_next_id.
  destruct (component_ids (emitted st)) as [|previous rest] eqn:Hids;
    pose proof (@audit_tarjan_pop_erases V E EV root
      (match component_ids (emitted st) with
       | [] => 1%positive
       | previous :: _ => Pos.succ previous
       end) (pending st) (low st) (comp_of (emitted st))) as Hpop;
    rewrite Hids in Hpop.
  all: cbn in Hpop |- *;
    destruct (audit_tarjan_pop_counted EV root _ _ _ _)
      as [[[[members tail] links] owners] events];
    cbn in Hpop; rewrite <- Hpop; reflexivity.
Qed.

(** Counted helper results agree with the five source Tarjan operations. *)
Theorem audit_tarjan_helpers_erasure : audit_tarjan_helpers_erasure_statement.
Proof.
  unfold audit_tarjan_helpers_erasure_statement.
  pose proof audit_tarjan_lower_erases as Hlower.
  pose proof audit_tarjan_emit_erases as Hemit.
  split; [|split; [|split; [|split]]].
  - intros V E EV g p v st.
    unfold audit_tarjan_discover_counted, tarjan_discover, succ_edges, index_edges.
    destruct (Map.get EV v (out_index p)); reflexivity.
  - exact Hlower.
  - intros V E; apply (@audit_tarjan_pop_erases V E).
  - exact Hemit.
  - intros V E EV v rest st; unfold audit_tarjan_close_counted, tarjan_close.
    destruct (Map.get EV v (low st)) as [l|] eqn:Hlow;
      destruct (Map.get EV v (disc st)) as [d|] eqn:Hdisc; try reflexivity.
    destruct (Pos.eqb l d) eqn:Hequal.
    + pose proof (Hemit V E EV v
        (TarjanState rest (disc st) (low st) (pending st) (clock st) (emitted st))) as Hresult.
      destruct (audit_tarjan_emit_counted EV v
        (TarjanState rest (disc st) (low st) (pending st) (clock st) (emitted st)));
        exact Hresult.
    + destruct rest as [|parent rest]; [reflexivity|].
      pose proof (Hlower V E EV (frame_node parent) l
        (TarjanState (parent :: rest) (disc st) (low st) (pending st) (clock st)
          (emitted st))) as Hresult.
      destruct (audit_tarjan_lower_counted EV (frame_node parent) l
        (TarjanState (parent :: rest) (disc st) (low st) (pending st) (clock st)
          (emitted st))); exact Hresult.
Qed.

(** A counted pop emits at most five events per inspected stack entry and one final event. *)
Lemma audit_tarjan_pop_event_bound {V E} (EV : encoding V) root i xs links owners :
    length (snd (@audit_tarjan_pop_counted V E EV root i xs links owners)) <=
      1 + 5 * length xs.
Proof.
  revert links owners; induction xs as [|v rest IH]; intros links owners.
  - reflexivity.
  - cbn [audit_tarjan_pop_counted].
    destruct (Pos.eqb (encode EV v) (encode EV root)) eqn:Hequal.
    + cbn; lia.
    + specialize (IH (Map.remove EV v links) (Map.set EV v i owners)).
      destruct (audit_tarjan_pop_counted EV root i rest
        (Map.remove EV v links) (Map.set EV v i owners))
      as [[[[members tail] links'] owners'] events].
      cbn in IH |- *; lia.
Qed.

(** Each helper trace is bounded by the stack length at that helper's input. *)
Theorem audit_tarjan_helpers_event_bound : audit_tarjan_helpers_event_bound_statement.
Proof.
  unfold audit_tarjan_helpers_event_bound_statement.
  assert (Hlower : forall V E (EV : encoding V) v n (st : tarjan_state V E),
    length (snd (audit_tarjan_lower_counted EV v n st)) <= 4).
  { intros V E EV v n st; unfold audit_tarjan_lower_counted.
    destruct (Map.get EV v (low st)); cbn; lia. }
  assert (Hemit : forall V E (EV : encoding V) root (st : tarjan_state V E),
    length (snd (audit_tarjan_emit_counted EV root st)) <= 4 + 5 * length (pending st)).
  { intros V E EV root st; unfold audit_tarjan_emit_counted.
    destruct (component_ids (emitted st)) as [|previous rest] eqn:Hids;
      pose proof (@audit_tarjan_pop_event_bound V E EV root
        (match component_ids (emitted st) with
         | [] => 1%positive
         | previous :: _ => Pos.succ previous
         end) (pending st) (low st) (comp_of (emitted st))) as Hpop;
      rewrite Hids in Hpop; cbn in Hpop |- *;
      destruct (audit_tarjan_pop_counted EV root _ _ _ _)
        as [[[[members tail] links] owners] events];
      cbn in Hpop |- *; rewrite length_app; cbn; lia. }
  split; [|split; [|split; [|split]]].
  - intros V E EV g p v st; unfold audit_tarjan_discover_counted.
    destruct (Map.get EV v (out_index p)); reflexivity.
  - exact Hlower.
  - intros V E; apply (@audit_tarjan_pop_event_bound V E).
  - exact Hemit.
  - intros V E EV v rest st; unfold audit_tarjan_close_counted.
    destruct (Map.get EV v (low st)) as [l|] eqn:Hlow;
      destruct (Map.get EV v (disc st)) as [d|] eqn:Hdisc; cbn; try lia.
    destruct (Pos.eqb l d) eqn:Hequal.
    + pose proof (Hemit V E EV v
        (TarjanState rest (disc st) (low st) (pending st) (clock st) (emitted st))) as Hbound.
      destruct (audit_tarjan_emit_counted EV v
        (TarjanState rest (disc st) (low st) (pending st) (clock st) (emitted st)));
        cbn in Hbound |- *; lia.
    + destruct rest as [|parent rest]; [cbn; lia|].
      pose proof (Hlower V E EV (frame_node parent) l
        (TarjanState (parent :: rest) (disc st) (low st) (pending st) (clock st)
          (emitted st))) as Hbound.
      destruct (audit_tarjan_lower_counted EV (frame_node parent) l
        (TarjanState (parent :: rest) (disc st) (low st) (pending st) (clock st)
          (emitted st))); cbn in Hbound |- *; lia.
Qed.

(** * Counted traversal erasure *)

(** One counted transition returns the same next state as the source transition. *)
Lemma audit_tarjan_step_erases {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) region st :
    fst (audit_tarjan_step_counted p region st) = tarjan_step p region st.
Proof.
  destruct audit_tarjan_helpers_erasure as [Hdiscover [Hlower [_ [_ Hclose]]]].
  unfold audit_tarjan_step_counted, tarjan_step.
  destruct (frames st) as [|[v edges] rest] eqn:Hframes; [reflexivity|].
  destruct edges as [|edge edges].
  - pose proof (Hclose V E EV v rest st) as Hresult.
    destruct (audit_tarjan_close_counted EV v rest st); exact Hresult.
  - destruct (FinSet.mem EV (Graph.target g edge) region) eqn:Hinside; [|reflexivity].
    destruct (Map.get EV (Graph.target g edge) (disc st)) as [d|] eqn:Hdisc.
    + destruct (Map.get EV (Graph.target g edge) (low st)) as [onstack|] eqn:Hlow;
        [|reflexivity].
      pose proof (Hlower V E EV v d
        (TarjanState (TarjanFrame v edges :: rest) (disc st) (low st)
          (pending st) (clock st) (emitted st))) as Hresult.
      destruct (audit_tarjan_lower_counted EV v d
        (TarjanState (TarjanFrame v edges :: rest) (disc st) (low st)
          (pending st) (clock st) (emitted st))); exact Hresult.
    + pose proof (Hdiscover V E EV g p (Graph.target g edge)
        (TarjanState (TarjanFrame v edges :: rest) (disc st) (low st)
          (pending st) (clock st) (emitted st))) as Hresult.
      destruct (audit_tarjan_discover_counted p (Graph.target g edge)
        (TarjanState (TarjanFrame v edges :: rest) (disc st) (low st)
          (pending st) (clock st) (emitted st))); exact Hresult.
Qed.

(** Binary counted execution preserves the final state returned by source fuel execution. *)
Lemma audit_tarjan_run_erases {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) region fuel st :
    fst (audit_tarjan_run_counted p region fuel st) = tarjan_run p region fuel st.
Proof.
  revert st; induction fuel as [fuel IH|fuel IH|];
    intros [frames disc low pending clock emitted]; destruct frames as [|frame rest];
    try reflexivity.
  - change (fst (let '(middle, first) := audit_tarjan_run_counted p region fuel
        (TarjanState (frame :: rest) disc low pending clock emitted) in
      let '(last, second) := audit_tarjan_run_counted p region fuel middle in
      let '(result, steps) := audit_tarjan_step_counted p region last in
      (result, AuditTarjanCase 9 :: first ++ second ++ steps)) =
      tarjan_step p region (tarjan_run p region fuel (tarjan_run p region fuel
        (TarjanState (frame :: rest) disc low pending clock emitted)))).
    pose proof (IH (TarjanState (frame :: rest) disc low pending clock emitted)) as Hfirst.
    destruct (audit_tarjan_run_counted p region fuel
      (TarjanState (frame :: rest) disc low pending clock emitted)) as [middle first].
    cbn in Hfirst |- *.
    pose proof (IH middle) as Hsecond.
    destruct (audit_tarjan_run_counted p region fuel middle) as [last second].
    cbn in Hsecond |- *.
    pose proof (audit_tarjan_step_erases p region last) as Hstep.
    destruct (audit_tarjan_step_counted p region last) as [result steps].
    cbn in Hstep |- *; now rewrite <- Hfirst, <- Hsecond, <- Hstep.
  - change (fst (let '(middle, first) := audit_tarjan_run_counted p region fuel
        (TarjanState (frame :: rest) disc low pending clock emitted) in
      let '(result, second) := audit_tarjan_run_counted p region fuel middle in
      (result, AuditTarjanCase 8 :: first ++ second)) =
      tarjan_run p region fuel (tarjan_run p region fuel
        (TarjanState (frame :: rest) disc low pending clock emitted))).
    pose proof (IH (TarjanState (frame :: rest) disc low pending clock emitted)) as Hfirst.
    destruct (audit_tarjan_run_counted p region fuel
      (TarjanState (frame :: rest) disc low pending clock emitted)) as [middle first].
    cbn in Hfirst |- *.
    pose proof (IH middle) as Hsecond.
    destruct (audit_tarjan_run_counted p region fuel middle) as [result second].
    cbn in Hsecond |- *; now rewrite <- Hfirst, <- Hsecond.
  - change (fst (let '(result, events) := audit_tarjan_step_counted p region
        (TarjanState (frame :: rest) disc low pending clock emitted) in
      (result, AuditTarjanCase 7 :: events)) =
      tarjan_step p region (TarjanState (frame :: rest) disc low pending clock emitted)).
    pose proof (audit_tarjan_step_erases p region
      (TarjanState (frame :: rest) disc low pending clock emitted)) as Hstep.
    destruct (audit_tarjan_step_counted p region
      (TarjanState (frame :: rest) disc low pending clock emitted)); exact Hstep.
Qed.

(** Counted root processing returns the source state for a fresh or previously seen root. *)
Lemma audit_tarjan_root_erases {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) region st v :
    fst (audit_tarjan_root_counted p region st v) = tarjan_root p region st v.
Proof.
  unfold audit_tarjan_root_counted, tarjan_root.
  destruct (Map.get EV v (disc st)) as [number|] eqn:Hfound; [reflexivity|].
  pose proof (proj1 audit_tarjan_helpers_erasure V E EV g p v st) as Hdiscover.
  destruct (audit_tarjan_discover_counted p v st) as [next detail]; cbn in Hdiscover |- *.
  pose proof (audit_tarjan_run_erases p region (fuel p) next) as Hrun.
  destruct (audit_tarjan_run_counted p region (fuel p) next) as [result events].
  cbn in Hrun |- *; now rewrite <- Hdiscover, <- Hrun.
Qed.

(** The counted root list visits roots in the source fold's order. *)
Lemma audit_tarjan_roots_erase {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) region roots st :
    fst (audit_tarjan_roots_counted p region roots st) =
      fold_left (tarjan_root p region) roots st.
Proof.
  revert st; induction roots as [|root rest IH]; intro st; [reflexivity|].
  cbn [audit_tarjan_roots_counted fold_left].
  pose proof (audit_tarjan_root_erases p region st root) as Hroot.
  destruct (audit_tarjan_root_counted p region st root) as [next here]; cbn in Hroot |- *.
  pose proof (IH next) as Hrest.
  destruct (audit_tarjan_roots_counted p region rest next) as [result events].
  cbn in Hrest |- *; now rewrite <- Hroot, <- Hrest.
Qed.

(** Region setup builds the same set as the corresponding left fold. *)
Lemma audit_tarjan_region_erases {V E} (EV : encoding V) region set :
    fst (@audit_tarjan_region_counted V E EV region set) =
      fold_left (fun acc v => FinSet.add EV v acc) region set.
Proof.
  revert set; induction region as [|v rest IH]; intro set; [reflexivity|].
  cbn [audit_tarjan_region_counted fold_left].
  pose proof (IH (FinSet.add EV v set)) as Hrest.
  destruct (audit_tarjan_region_counted EV rest (FinSet.add EV v set)) as [result events].
  exact Hrest.
Qed.

(** Erasing the counted traversal yields the SCC result for the original region. *)
Lemma audit_scc_counted_erases {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) region :
    fst (audit_scc_within_counted p region) = scc_within p region.
Proof.
  unfold audit_scc_within_counted, scc_within, FinSet.of_list.
  pose proof (@audit_tarjan_region_erases V E EV region FinSet.empty) as Hregion.
  destruct (audit_tarjan_region_counted EV region FinSet.empty) as [keep setup].
  cbn in Hregion |- *; rewrite <- Hregion.
  pose proof (audit_tarjan_roots_erase p keep region tarjan_initial) as Hroots.
  destruct (audit_tarjan_roots_counted p keep region tarjan_initial) as [st events].
  cbn in Hroots |- *; now rewrite <- Hroots.
Qed.

(** * Correspondence of captured primitive calls *)

(** Every primitive event in a counted pop uses the comparison results actually captured. *)
Lemma audit_tarjan_pop_primitives {V E B} (cb : audit_dfs_callback_model V E B)
    root i xs links owners :
    Forall audit_scc_source_event_primitive
      (snd (audit_tarjan_nested_pop (audit_graph_capture_callbacks cb) root i xs links owners)).
Proof.
  revert links owners; induction xs as [|v rest IH]; intros links owners.
  - cbn [audit_tarjan_nested_pop audit_scc_source_event_primitive]; repeat constructor.
  - cbn [audit_tarjan_nested_pop].
    unfold audit_tarjan_nested_remove, audit_tarjan_nested_set, audit_graph_capture_callbacks.
    cbn.
    cbn [audit_tarjan_nested_remove audit_tarjan_nested_set
      audit_graph_capture_callbacks].
    destruct (audit_dfs_encode_model cb v) as [vcode vbody] eqn:Hv.
    destruct (audit_dfs_encode_model cb root) as [rcode rbody] eqn:Hroot.
    cbn.
    pose proof (audit_positive_eqb_erases vcode rcode) as Hequal.
    destruct (Pos.eqb vcode rcode) eqn:Hbranch.
    + cbn [audit_scc_source_event_primitive audit_scc_source_codes].
      repeat constructor; exact Hequal.
    + specialize (IH (CollectionsTrie.Trie.remove vcode links)
        (CollectionsTrie.Trie.set vcode (v, i) owners)).
      fold (audit_graph_capture_callbacks cb).
      destruct (audit_tarjan_nested_pop (audit_graph_capture_callbacks cb) root i rest
        (CollectionsTrie.Trie.remove vcode links)
        (CollectionsTrie.Trie.set vcode (v, i) owners))
        as [[[[members tail] links'] owners'] events].
      cbn in IH |- *; cbn [audit_scc_source_event_primitive audit_scc_source_codes].
      repeat constructor; try exact Hequal; exact IH.
Qed.

(** Discovery records its actual clock successor as a primitive event. *)
Lemma audit_tarjan_discover_primitives {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) v st :
    Forall audit_scc_source_event_primitive
      (snd (audit_tarjan_nested_discover p (audit_graph_capture_callbacks cb) v st)).
Proof.
  unfold audit_tarjan_nested_discover.
  destruct (audit_tarjan_nested_get (audit_graph_capture_callbacks cb) v (out_index p)).
  destruct (audit_tarjan_nested_set (audit_graph_capture_callbacks cb) v (clock st) (disc st)).
  destruct (audit_tarjan_nested_set (audit_graph_capture_callbacks cb) v (clock st) (low st)).
  cbn [audit_scc_source_event_primitive]; repeat constructor; apply audit_positive_succ_erases.
Qed.

(** Lowering records the positive minimum computed from the looked-up lowlink. *)
Lemma audit_tarjan_lower_primitives {V E B} (cb : audit_dfs_callback_model V E B) v n st :
    Forall audit_scc_source_event_primitive
      (snd (audit_tarjan_nested_lower (audit_graph_capture_callbacks cb) v n st)).
Proof.
  unfold audit_tarjan_nested_lower.
  destruct (audit_tarjan_nested_get (audit_graph_capture_callbacks cb) v (low st))
    as [[old|] body]; cbn.
  - destruct (audit_tarjan_nested_set (audit_graph_capture_callbacks cb) v (Pos.min old n)
      (low st)); cbn [audit_scc_source_event_primitive].
    pose proof (audit_scc_min_source_model_holds old n) as Hmin.
    destruct (audit_scc_min_source_model old n ) eqn:Hminrun; cbn in Hmin |- *.
    repeat (constructor; cbn [audit_scc_source_event_primitive];
      try exact I; try (rewrite Hminrun; exact (proj1 Hmin))).
  - cbn [audit_scc_source_event_primitive]; repeat constructor.
Qed.

(** Component emission preserves primitive correspondence through the actual pop. *)
Lemma audit_tarjan_emit_primitives {V E B} (cb : audit_dfs_callback_model V E B) root st :
    Forall audit_scc_source_event_primitive
      (snd (audit_tarjan_nested_emit (audit_graph_capture_callbacks cb) root st)).
Proof.
  unfold audit_tarjan_nested_emit.
  destruct (component_ids (emitted st)) as [|previous rest] eqn:Hids;
    pose proof (audit_tarjan_pop_primitives cb root
      (match component_ids (emitted st) with
       | [] => 1%positive
       | previous :: _ => Pos.succ previous
       end) (pending st) (low st) (comp_of (emitted st))) as Hpop;
    rewrite Hids in Hpop; cbn in Hpop |- *;
    destruct (audit_tarjan_nested_pop (audit_graph_capture_callbacks cb) root _ _ _ _)
      as [[[[members tail] links] owners] events]; cbn in Hpop |- *.
  - constructor; [exact I|].
    apply Forall_app; split; [exact Hpop|repeat constructor].
  - constructor; [exact I|]. constructor; [apply audit_positive_succ_erases|].
    apply Forall_app; split; [exact Hpop|repeat constructor].
Qed.

(** Closing a frame records its lowlink comparison and the chosen helper's primitive events. *)
Lemma audit_tarjan_close_primitives {V E B} (cb : audit_dfs_callback_model V E B) v rest st :
    Forall audit_scc_source_event_primitive
      (snd (audit_tarjan_nested_close (audit_graph_capture_callbacks cb) v rest st)).
Proof.
  unfold audit_tarjan_nested_close.
  destruct (audit_tarjan_nested_get (audit_graph_capture_callbacks cb) v (low st))
    as [[lo|] low_body]; cbn.
  2: { repeat constructor. }
  destruct (audit_tarjan_nested_get (audit_graph_capture_callbacks cb) v (disc st))
    as [[di|] disc_body]; cbn.
  2: { repeat constructor. }
  pose proof (audit_positive_eqb_erases lo di) as Hequal.
  destruct (Pos.eqb lo di) eqn:Hcompare.
  - pose proof (audit_tarjan_emit_primitives cb v
      (TarjanState rest (disc st) (low st) (pending st) (clock st) (emitted st))) as Hemit.
    destruct (audit_tarjan_nested_emit (audit_graph_capture_callbacks cb) v
      (TarjanState rest (disc st) (low st) (pending st) (clock st) (emitted st)))
      as [next events]; cbn in Hemit |- *.
    repeat (constructor; cbn [audit_scc_source_event_primitive]; try exact I; try exact Hequal).
    exact Hemit.
  - destruct rest as [|parent rest].
    + repeat (constructor; cbn [audit_scc_source_event_primitive]; try exact I; try exact Hequal).
    + pose proof (audit_tarjan_lower_primitives cb (frame_node parent) lo
        (TarjanState (parent :: rest) (disc st) (low st) (pending st) (clock st)
          (emitted st))) as Hlower.
      destruct (audit_tarjan_nested_lower (audit_graph_capture_callbacks cb) (frame_node parent) lo
        (TarjanState (parent :: rest) (disc st) (low st) (pending st) (clock st)
          (emitted st))) as [next events]; cbn in Hlower |- *.
      repeat (constructor; cbn [audit_scc_source_event_primitive]; try exact I; try exact Hequal).
      exact Hlower.
Qed.

(** Each nested transition preserves primitive correspondence in its emitted trace. *)
Lemma audit_tarjan_step_primitives {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) region st :
    Forall audit_scc_source_event_primitive
      (snd (audit_tarjan_nested_step p (audit_graph_capture_callbacks cb) region st)).
Proof.
  unfold audit_tarjan_nested_step.
  destruct (frames st) as [|[v edges] rest] eqn:Hframes; [repeat constructor|].
  destruct edges as [|edge edges].
  - pose proof (audit_tarjan_close_primitives cb v rest st) as Hclose.
    destruct (audit_tarjan_nested_close (audit_graph_capture_callbacks cb) v rest st)
      as [next detail]; cbn in Hclose |- *.
    constructor; [exact I|]. apply Forall_app; split; [exact Hclose|repeat constructor].
  - destruct (audit_dfs_target_model (audit_graph_capture_callbacks cb) edge) as [target
    target_body].
    destruct (audit_tarjan_nested_get (audit_graph_capture_callbacks cb) target region)
      as [[member|] member_body]; cbn.
    2: { repeat constructor. }
    destruct (audit_tarjan_nested_get (audit_graph_capture_callbacks cb) target (disc st))
      as [[d|] disc_body]; cbn.
    + destruct (audit_tarjan_nested_get (audit_graph_capture_callbacks cb) target (low st))
        as [[onstack|] low_body]; cbn.
      2: { repeat constructor. }
      pose proof (audit_tarjan_lower_primitives cb v d
        (TarjanState (TarjanFrame v edges :: rest) (disc st) (low st)
          (pending st) (clock st) (emitted st))) as Hlower.
      destruct (audit_tarjan_nested_lower (audit_graph_capture_callbacks cb) v d
        (TarjanState (TarjanFrame v edges :: rest) (disc st) (low st)
          (pending st) (clock st) (emitted st))) as [next detail]; cbn in Hlower |- *.
      repeat constructor; apply Forall_app; split; [exact Hlower|repeat constructor].
    + pose proof (audit_tarjan_discover_primitives p cb target
        (TarjanState (TarjanFrame v edges :: rest) (disc st) (low st)
          (pending st) (clock st) (emitted st))) as Hdiscover.
      destruct (audit_tarjan_nested_discover p (audit_graph_capture_callbacks cb) target
        (TarjanState (TarjanFrame v edges :: rest) (disc st) (low st)
          (pending st) (clock st) (emitted st))) as [next detail]; cbn in Hdiscover |- *.
      repeat constructor; apply Forall_app; split; [exact Hdiscover|repeat constructor].
Qed.

(** Nested binary fuel preserves any event property held by steps and administrative cases. *)
Lemma audit_tarjan_nested_run_events {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) region
    (P : audit_tarjan_nested_event V E B -> Prop) fuel st :
    (forall state, Forall P (snd (audit_tarjan_nested_step p cb region state))) ->
    (forall site, P (AuditTarjanCase site, [])) ->
    Forall P (snd (audit_tarjan_nested_run p cb region fuel st)).
Proof.
  intros Hstep Hcase; revert st; induction fuel as [fuel IH|fuel IH|];
    intros [frames disc low stack clock emitted]; destruct frames as [|frame rest];
    try (constructor; [apply Hcase|constructor]).
  - change (Forall P (snd (let '(middle, first) := audit_tarjan_nested_run p cb region fuel
        (TarjanState (frame :: rest) disc low stack clock emitted) in
      let '(last, second) := audit_tarjan_nested_run p cb region fuel middle in
      let '(result, steps) := audit_tarjan_nested_step p cb region last in
      (result, (AuditTarjanCase 9, []) :: first ++ second ++ steps)))).
    pose proof (IH (TarjanState (frame :: rest) disc low stack clock emitted)) as Hfirst.
    destruct (audit_tarjan_nested_run p cb region fuel
      (TarjanState (frame :: rest) disc low stack clock emitted)) as [middle first].
    cbn in Hfirst |- *; pose proof (IH middle) as Hsecond.
    destruct (audit_tarjan_nested_run p cb region fuel middle) as [last second].
    cbn in Hsecond |- *; specialize (Hstep last) as Hlast.
    destruct (audit_tarjan_nested_step p cb region last) as [result steps]; cbn in Hlast |- *.
    constructor; [apply Hcase|]. apply Forall_app; split; [exact Hfirst|].
    apply Forall_app; split; assumption.
  - change (Forall P (snd (let '(middle, first) := audit_tarjan_nested_run p cb region fuel
        (TarjanState (frame :: rest) disc low stack clock emitted) in
      let '(result, second) := audit_tarjan_nested_run p cb region fuel middle in
      (result, (AuditTarjanCase 8, []) :: first ++ second)))).
    pose proof (IH (TarjanState (frame :: rest) disc low stack clock emitted)) as Hfirst.
    destruct (audit_tarjan_nested_run p cb region fuel
      (TarjanState (frame :: rest) disc low stack clock emitted)) as [middle first].
    cbn in Hfirst |- *; pose proof (IH middle) as Hsecond.
    destruct (audit_tarjan_nested_run p cb region fuel middle) as [result second].
    cbn in Hsecond |- *; constructor; [apply Hcase|]. apply Forall_app; split; assumption.
  - change (Forall P (snd (let '(result, events) := audit_tarjan_nested_step p cb region
        (TarjanState (frame :: rest) disc low stack clock emitted) in
      (result, (AuditTarjanCase 7, []) :: events)))).
    specialize (Hstep (TarjanState (frame :: rest) disc low stack clock emitted)) as Hlast.
    destruct (audit_tarjan_nested_step p cb region
      (TarjanState (frame :: rest) disc low stack clock emitted)) as [result events].
    cbn in Hlast |- *; constructor; [apply Hcase|exact Hlast].
Qed.

(** Both halves of a binary-fuel run retain primitive correspondence. *)
Lemma audit_tarjan_run_primitives {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) region fuel st :
    Forall audit_scc_source_event_primitive
      (snd (audit_tarjan_nested_run p (audit_graph_capture_callbacks cb) region fuel st)).
Proof.
  apply audit_tarjan_nested_run_events.
  - apply audit_tarjan_step_primitives.
  - intros site; exact I.
Qed.

(** A nested root preserves correspondence across discovery and the ensuing run. *)
Lemma audit_tarjan_root_primitives {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) region st v :
    Forall audit_scc_source_event_primitive
      (snd (audit_tarjan_nested_root p (audit_graph_capture_callbacks cb) region st v)).
Proof.
  unfold audit_tarjan_nested_root.
  destruct (audit_tarjan_nested_get (audit_graph_capture_callbacks cb) v (disc st))
    as [[number|] body]; cbn; [repeat constructor|].
  pose proof (audit_tarjan_discover_primitives p cb v st) as Hdiscover.
  destruct (audit_tarjan_nested_discover p (audit_graph_capture_callbacks cb) v st)
    as [next detail]; cbn in Hdiscover |- *.
  pose proof (audit_tarjan_run_primitives p cb region (fuel p) next) as Hrun.
  destruct (audit_tarjan_nested_run p (audit_graph_capture_callbacks cb) region (fuel p) next)
    as [result events]; cbn in Hrun |- *.
  repeat constructor; apply Forall_app; split; [exact Hdiscover|].
  constructor; [exact I|exact Hrun].
Qed.

(** Root traversal preserves primitive correspondence across every returned state. *)
Lemma audit_tarjan_roots_primitives {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) region roots st :
    Forall audit_scc_source_event_primitive
      (snd (audit_tarjan_nested_roots p (audit_graph_capture_callbacks cb) region roots st)).
Proof.
  revert st; induction roots as [|root rest IH]; intro st; cbn [audit_tarjan_nested_roots].
  - repeat constructor.
  - pose proof (audit_tarjan_root_primitives p cb region st root) as Hroot.
    destruct (audit_tarjan_nested_root p (audit_graph_capture_callbacks cb) region st root)
      as [next here]; cbn in Hroot |- *.
    pose proof (IH next) as Hrest.
    destruct (audit_tarjan_nested_roots p (audit_graph_capture_callbacks cb) region rest next)
      as [result later]; cbn in Hrest |- *.
    constructor; [exact I|]. apply Forall_app; split; assumption.
Qed.

(** Region setup contains no positive arithmetic primitive events. *)
Lemma audit_tarjan_region_primitives {V E B} (cb : audit_dfs_callback_model V E B) region set :
    Forall audit_scc_source_event_primitive
      (snd (audit_tarjan_nested_region (audit_graph_capture_callbacks cb) region set)).
Proof.
  revert set; induction region as [|v rest IH]; intro set; cbn [audit_tarjan_nested_region].
  - repeat constructor.
  - destruct (audit_tarjan_nested_set (audit_graph_capture_callbacks cb) v tt set) as [next body].
    pose proof (IH next) as Hrest.
    destruct (audit_tarjan_nested_region (audit_graph_capture_callbacks cb) rest next)
      as [result events]; cbn in Hrest |- *.
    constructor; [exact I|exact Hrest].
Qed.

(** Every source SCC primitive event agrees with its captured operands and result. *)
Theorem audit_scc_source_primitive_correspondence_holds :
    audit_scc_source_primitive_correspondence_statement.
Proof.
  intros V E B EV g p cb region Hcallbacks.
  unfold audit_scc_source_counted.
  pose proof (audit_tarjan_region_primitives cb region FinSet.empty) as Hsetup.
  destruct (audit_tarjan_nested_region (audit_graph_capture_callbacks cb) region FinSet.empty)
    as [keep setup]; cbn in Hsetup |- *.
  pose proof (audit_tarjan_roots_primitives p cb keep region tarjan_initial) as Hroots.
  destruct (audit_tarjan_nested_roots p (audit_graph_capture_callbacks cb) keep region
    tarjan_initial)
    as [st events]; cbn in Hroots |- *.
  apply Forall_app; split; [exact Hsetup|].
  apply Forall_app; split; [exact Hroots|repeat constructor].
Qed.

(** SCC primitive dependencies include the collection, arithmetic and reversal guarantees. *)
Theorem audit_scc_source_primitives_correct : audit_scc_source_library_obligations.
Proof.
  unfold audit_scc_source_library_obligations.
  split; [exact audit_trie_get_trace_adequate|].
  split; [exact audit_trie_update_trace_adequate|].
  split; [exact audit_trie_get_source_work_bound|].
  split; [exact audit_trie_update_source_work_bound|].
  split; [exact audit_positive_eqb_erases|].
  split; [exact audit_positive_eqb_source_bound|].
  split; [exact audit_positive_compare_cont|].
  split; [exact audit_positive_compare|].
  split; [exact audit_positive_succ_run_total|].
  split; [exact audit_positive_succ_run_correct|].
  split; [exact audit_scc_min_source_model_holds|].
  split; [exact audit_scc_source_primitive_correspondence_holds|].
  exact audit_scc_reverse_run_holds.
Qed.

(** * Nested traversal erasure *)

(** An erasing encoder makes nested discovery preserve the counted helper's result and trace. *)
Lemma audit_tarjan_nested_discover_erases {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) v st :
    audit_dfs_callbacks_erase EV g cb ->
    (fst (audit_tarjan_nested_discover p cb v st),
      map fst (snd (audit_tarjan_nested_discover p cb v st))) =
      let '(next, details) := audit_tarjan_discover_counted p v st in
      (next, map AuditTarjanHelper details).
Proof.
  intros [_ Hencode].
  specialize (Hencode v).
  destruct (audit_dfs_encode_model cb v) as [code body] eqn:Hcode; cbn in Hencode; subst code.
  unfold audit_tarjan_nested_discover, audit_tarjan_nested_get, audit_tarjan_nested_set,
    audit_tarjan_discover_counted.
  rewrite Hcode; reflexivity.
Qed.

(** An erasing encoder makes nested lowering preserve its counted helper result and trace. *)
Lemma audit_tarjan_nested_lower_erases {V E B} (EV : encoding V) (g : Graph.t V E)
    (cb : audit_dfs_callback_model V E B) v n st :
    audit_dfs_callbacks_erase EV g cb ->
    (fst (audit_tarjan_nested_lower cb v n st), map fst (snd (audit_tarjan_nested_lower cb v n
      st))) =
      let '(next, details) := audit_tarjan_lower_counted EV v n st in
      (next, map AuditTarjanHelper details).
Proof.
  intros [_ Hencode].
  specialize (Hencode v).
  destruct (audit_dfs_encode_model cb v) as [code body] eqn:Hcode; cbn in Hencode; subst code.
  unfold audit_tarjan_nested_lower, audit_tarjan_nested_get, audit_tarjan_nested_set,
    audit_tarjan_lower_counted.
  rewrite Hcode; change (Map.code_get (encode EV v) (low st)) with (Map.get EV v (low st)).
  destruct (Map.get EV v (low st)); reflexivity.
Qed.

(** Nested pop retains each counted map operation and comparison in order. *)
Lemma audit_tarjan_nested_pop_erases {V E B} (EV : encoding V) (g : Graph.t V E)
    (cb : audit_dfs_callback_model V E B) root i xs links owners :
    audit_dfs_callbacks_erase EV g cb ->
    (fst (audit_tarjan_nested_pop cb root i xs links owners),
      map fst (snd (audit_tarjan_nested_pop cb root i xs links owners))) =
      let '(answer, details) := @audit_tarjan_pop_counted V E EV root i xs links owners in
      (answer, map AuditTarjanHelper details).
Proof.
  intros Hcallbacks; destruct Hcallbacks as [_ Hencode].
  revert links owners; induction xs as [|v rest IH]; intros links owners; [reflexivity|].
  specialize (Hencode v) as Hv; specialize (Hencode root) as Hroot.
  destruct (audit_dfs_encode_model cb v) as [vcode vbody] eqn:Hvcall; cbn in Hv; subst vcode.
  destruct (audit_dfs_encode_model cb root) as [rcode rbody] eqn:Hrootcall;
    cbn in Hroot; subst rcode.
  cbn [audit_tarjan_nested_pop audit_tarjan_pop_counted].
  unfold audit_tarjan_nested_remove, audit_tarjan_nested_set; rewrite Hvcall, Hrootcall; cbn.
  destruct (Pos.eqb (encode EV v) (encode EV root)) eqn:Hequal; [reflexivity|].
  change (CollectionsTrie.Trie.remove (encode EV v) links) with (Map.remove EV v links).
  change (CollectionsTrie.Trie.set (encode EV v) (v, i) owners) with (Map.set EV v i owners).
  pose proof (IH (Map.remove EV v links) (Map.set EV v i owners)) as Hrest.
  destruct (audit_tarjan_nested_pop cb root i rest (Map.remove EV v links) (Map.set EV v i owners))
    as [[[[members tail] links'] owners'] events].
  destruct (@audit_tarjan_pop_counted V E EV root i rest
    (Map.remove EV v links) (Map.set EV v i owners)) as [answer details].
  cbn in Hrest |- *; destruct answer as [[[members' tail'] links''] owners''].
  assert (Htrace : map fst events = map AuditTarjanHelper details)
    by (inversion Hrest; reflexivity).
  inversion Hrest; subst; cbn; now rewrite Htrace.
Qed.

(** Nested emission retains the counted pop, result maps, and ordered helper trace. *)
Lemma audit_tarjan_nested_emit_erases {V E B} (EV : encoding V) (g : Graph.t V E)
    (cb : audit_dfs_callback_model V E B) root st :
    audit_dfs_callbacks_erase EV g cb ->
    (fst (audit_tarjan_nested_emit cb root st), map fst (snd (audit_tarjan_nested_emit cb root
      st))) =
      let '(next, details) := audit_tarjan_emit_counted EV root st in
      (next, map AuditTarjanHelper details).
Proof.
  intro Hcallbacks.
  unfold audit_tarjan_nested_emit, audit_tarjan_emit_counted.
  destruct (component_ids (emitted st)) as [|previous rest] eqn:Hids;
    pose proof (audit_tarjan_nested_pop_erases EV g cb root
      (match component_ids (emitted st) with
       | [] => 1%positive
       | previous :: _ => Pos.succ previous
       end) (pending st) (low st) (comp_of (emitted st)) Hcallbacks) as Hpop;
    rewrite Hids in Hpop; cbn in Hpop |- *;
    destruct (audit_tarjan_nested_pop cb root _ _ _ _) as [[[[members tail] links] owners] events];
    destruct (audit_tarjan_pop_counted EV root _ _ _ _)
      as [[[[members' tail'] links'] owners'] details];
    cbn in Hpop |- *;
    assert (Htrace : map fst events = map AuditTarjanHelper details)
      by (inversion Hpop; reflexivity);
    inversion Hpop; subst; rewrite !map_app; cbn; now rewrite <- Htrace.
Qed.

(** Nested closing matches all counted lookup, comparison, emission, and lowering events. *)
Lemma audit_tarjan_nested_close_erases {V E B} (EV : encoding V) (g : Graph.t V E)
    (cb : audit_dfs_callback_model V E B) v rest st :
    audit_dfs_callbacks_erase EV g cb ->
    (fst (audit_tarjan_nested_close cb v rest st),
      map fst (snd (audit_tarjan_nested_close cb v rest st))) =
      let '(next, details) := audit_tarjan_close_counted EV v rest st in
      (next, map AuditTarjanHelper details).
Proof.
  intro Hcallbacks; pose proof Hcallbacks as [_ Hencode].
  specialize (Hencode v).
  destruct (audit_dfs_encode_model cb v) as [code body] eqn:Hcode; cbn in Hencode; subst code.
  unfold audit_tarjan_nested_close, audit_tarjan_nested_get, audit_tarjan_close_counted.
  rewrite Hcode; change (Map.code_get (encode EV v) (low st)) with (Map.get EV v (low st)).
  change (Map.code_get (encode EV v) (disc st)) with (Map.get EV v (disc st)).
  destruct (Map.get EV v (low st)) as [lo|] eqn:Hlow; [|reflexivity].
  destruct (Map.get EV v (disc st)) as [di|] eqn:Hdisc; [|reflexivity].
  destruct (Pos.eqb lo di) eqn:Hcompare.
  - pose proof (audit_tarjan_nested_emit_erases EV g cb v
      (TarjanState rest (disc st) (low st) (pending st) (clock st) (emitted st)) Hcallbacks)
      as Hemit.
    destruct (audit_tarjan_nested_emit cb v
      (TarjanState rest (disc st) (low st) (pending st) (clock st) (emitted st)))
      as [next events].
    destruct (audit_tarjan_emit_counted EV v
      (TarjanState rest (disc st) (low st) (pending st) (clock st) (emitted st)))
      as [next' details] eqn:Hcount.
    cbn in Hemit |- *.
    assert (Htrace : map fst events = map AuditTarjanHelper details)
      by (inversion Hemit; reflexivity).
    inversion Hemit; subst; cbn; reflexivity.
  - destruct rest as [|parent rest]; [reflexivity|].
    pose proof (audit_tarjan_nested_lower_erases EV g cb (frame_node parent) lo
      (TarjanState (parent :: rest) (disc st) (low st) (pending st) (clock st) (emitted st))
      Hcallbacks) as Hlower.
    destruct (audit_tarjan_nested_lower cb (frame_node parent) lo
      (TarjanState (parent :: rest) (disc st) (low st) (pending st) (clock st) (emitted st)))
      as [next events].
    destruct (audit_tarjan_lower_counted EV (frame_node parent) lo
      (TarjanState (parent :: rest) (disc st) (low st) (pending st) (clock st) (emitted st)))
      as [next' details] eqn:Hcount.
    cbn in Hlower |- *.
    assert (Htrace : map fst events = map AuditTarjanHelper details)
      by (inversion Hlower; reflexivity).
    inversion Hlower; subst; cbn; reflexivity.
Qed.

(** Discovery erasure extends to the enclosing event that records its returned state. *)
Lemma audit_tarjan_nested_discover_event_erases {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) v st :
    audit_dfs_callbacks_erase EV g cb ->
    let '(next, events) := audit_tarjan_nested_discover p cb v st in
    let '(counted, details) := audit_tarjan_discover_counted p v st in
    (next, map fst events ++ [AuditTarjanDiscover v st next]) =
      (counted, map AuditTarjanHelper details ++ [AuditTarjanDiscover v st counted]).
Proof.
  intro Hcallbacks.
  pose proof (audit_tarjan_nested_discover_erases p cb v st Hcallbacks) as Hdiscover.
  destruct (audit_tarjan_nested_discover p cb v st) as [next events].
  destruct (audit_tarjan_discover_counted p v st) as [counted details].
  cbn in Hdiscover |- *; inversion Hdiscover; subst; reflexivity.
Qed.

(** Lowering erasure extends to the enclosing event that records its returned state. *)
Lemma audit_tarjan_nested_lower_event_erases {V E B} (EV : encoding V) (g : Graph.t V E)
    (cb : audit_dfs_callback_model V E B) v n st :
    audit_dfs_callbacks_erase EV g cb ->
    let '(next, events) := audit_tarjan_nested_lower cb v n st in
    let '(counted, details) := audit_tarjan_lower_counted EV v n st in
    (next, map fst events ++ [AuditTarjanLower v n st next]) =
      (counted, map AuditTarjanHelper details ++ [AuditTarjanLower v n st counted]).
Proof.
  intro Hcallbacks.
  pose proof (audit_tarjan_nested_lower_erases EV g cb v n st Hcallbacks) as Hlower.
  destruct (audit_tarjan_nested_lower cb v n st) as [next events].
  destruct (audit_tarjan_lower_counted EV v n st) as [counted details].
  cbn in Hlower |- *; inversion Hlower; subst; reflexivity.
Qed.

(** An edge transition retains the counted target, lookups, and selected helper trace. *)
Lemma audit_tarjan_nested_edge_erases {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) region st v edge edges rest :
    audit_dfs_callbacks_erase EV g cb ->
    frames st = TarjanFrame v (edge :: edges) :: rest ->
    (fst (audit_tarjan_nested_step p cb region st),
      map fst (snd (audit_tarjan_nested_step p cb region st))) =
      audit_tarjan_step_counted p region st.
Proof.
  intros Hcallbacks Hframes.
  unfold audit_tarjan_nested_step, audit_tarjan_step_counted; rewrite Hframes.
  pose proof Hcallbacks as [Htarget Hencode].
  specialize (Htarget edge).
  destruct (audit_dfs_target_model cb edge) as [target target_body] eqn:Htargetcall.
  cbn in Htarget; subst target.
  specialize (Hencode (Graph.target g edge)) as Hcode.
  destruct (audit_dfs_encode_model cb (Graph.target g edge)) as [code body] eqn:Hcodecall.
  cbn in Hcode; subst code.
  unfold audit_tarjan_nested_get; rewrite Hcodecall.
  change (Map.code_get (encode EV (Graph.target g edge)) region) with
    (Map.get EV (Graph.target g edge) region).
  change (Map.code_get (encode EV (Graph.target g edge)) (disc st)) with
    (Map.get EV (Graph.target g edge) (disc st)).
  change (Map.code_get (encode EV (Graph.target g edge)) (low st)) with
    (Map.get EV (Graph.target g edge) (low st)).
  unfold FinSet.mem, Map.mem.
  destruct (Map.get EV (Graph.target g edge) region) as [member|] eqn:Hmember;
    cbn; [|reflexivity].
  destruct (Map.get EV (Graph.target g edge) (disc st)) as [d|] eqn:Hdisc.
  - destruct (Map.get EV (Graph.target g edge) (low st)) as [onstack|] eqn:Hlow;
      cbn; [|reflexivity].
    pose proof (audit_tarjan_nested_lower_event_erases EV g cb v d
      (TarjanState (TarjanFrame v edges :: rest) (disc st) (low st)
        (pending st) (clock st) (emitted st)) Hcallbacks) as Hlower.
    destruct (audit_tarjan_nested_lower cb v d
      (TarjanState (TarjanFrame v edges :: rest) (disc st) (low st)
        (pending st) (clock st) (emitted st))) as [next events].
    destruct (audit_tarjan_lower_counted EV v d
      (TarjanState (TarjanFrame v edges :: rest) (disc st) (low st)
        (pending st) (clock st) (emitted st))) as [next' details] eqn:Hcount.
    cbn in Hlower |- *.
    inversion Hlower; subst; rewrite map_app; cbn; repeat f_equal; assumption.
  - pose proof (audit_tarjan_nested_discover_event_erases p cb (Graph.target g edge)
      (TarjanState (TarjanFrame v edges :: rest) (disc st) (low st)
        (pending st) (clock st) (emitted st)) Hcallbacks) as Hdiscover.
    destruct (audit_tarjan_nested_discover p cb (Graph.target g edge)
      (TarjanState (TarjanFrame v edges :: rest) (disc st) (low st)
        (pending st) (clock st) (emitted st))) as [next events].
    destruct (audit_tarjan_discover_counted p (Graph.target g edge)
      (TarjanState (TarjanFrame v edges :: rest) (disc st) (low st)
        (pending st) (clock st) (emitted st))) as [counted details] eqn:Hcount.
    cbn in Hdiscover |- *.
    cbn [audit_tarjan_discover_counted] in Hcount; inversion Hcount; subst.
    cbn in Hdiscover |- *; inversion Hdiscover; subst.
    rewrite map_app; cbn; repeat f_equal; assumption.
Qed.

(** A nested transition preserves the counted transition's state and ordered event trace. *)
Lemma audit_tarjan_nested_step_erases {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) region st :
    audit_dfs_callbacks_erase EV g cb ->
    (fst (audit_tarjan_nested_step p cb region st),
      map fst (snd (audit_tarjan_nested_step p cb region st))) =
      audit_tarjan_step_counted p region st.
Proof.
  intro Hcallbacks.
  unfold audit_tarjan_nested_step, audit_tarjan_step_counted.
  destruct (frames st) as [|[v edges] rest] eqn:Hframes; [reflexivity|].
  destruct edges as [|edge edges].
  - pose proof (audit_tarjan_nested_close_erases EV g cb v rest st Hcallbacks) as Hclose.
    destruct (audit_tarjan_nested_close cb v rest st) as [next events].
    destruct (audit_tarjan_close_counted EV v rest st) as [next' details] eqn:Hcount.
    cbn in Hclose |- *.
    assert (Htrace : map fst events = map AuditTarjanHelper details)
      by (inversion Hclose; reflexivity).
    inversion Hclose; subst; rewrite map_app; cbn; reflexivity.
  - pose proof (audit_tarjan_nested_edge_erases p cb region st v edge edges rest
      Hcallbacks Hframes) as Hedge.
    unfold audit_tarjan_nested_step, audit_tarjan_step_counted in Hedge.
    rewrite Hframes in Hedge; exact Hedge.
Qed.

(** The odd nested fuel branch preserves the counted state and event order. *)
Lemma audit_tarjan_nested_run_erases_odd {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) region fuel
    (frame : tarjan_frame V E) rest (disc low : Map.t V positive) pending clock emitted :
    audit_dfs_callbacks_erase EV g cb ->
    (forall state, (fst (audit_tarjan_nested_run p cb region fuel state),
      map fst (snd (audit_tarjan_nested_run p cb region fuel state))) =
      audit_tarjan_run_counted p region fuel state) ->
    (fst (audit_tarjan_nested_run p cb region (xI fuel)
      (TarjanState (frame :: rest) disc low pending clock emitted)),
      map fst (snd (audit_tarjan_nested_run p cb region (xI fuel)
        (TarjanState (frame :: rest) disc low pending clock emitted)))) =
      audit_tarjan_run_counted p region (xI fuel)
        (TarjanState (frame :: rest) disc low pending clock emitted).
Proof.
  intros Hcallbacks IH.
  change ((fst (let '(middle, first) := audit_tarjan_nested_run p cb region fuel
        (TarjanState (frame :: rest) disc low pending clock emitted) in
      let '(last, second) := audit_tarjan_nested_run p cb region fuel middle in
      let '(result, steps) := audit_tarjan_nested_step p cb region last in
      (result, (AuditTarjanCase 9, []) :: first ++ second ++ steps)),
    map fst (snd (let '(middle, first) := audit_tarjan_nested_run p cb region fuel
        (TarjanState (frame :: rest) disc low pending clock emitted) in
      let '(last, second) := audit_tarjan_nested_run p cb region fuel middle in
      let '(result, steps) := audit_tarjan_nested_step p cb region last in
      (result, (AuditTarjanCase 9, []) :: first ++ second ++ steps)))) =
    let '(middle, first) := audit_tarjan_run_counted p region fuel
      (TarjanState (frame :: rest) disc low pending clock emitted) in
    let '(last, second) := audit_tarjan_run_counted p region fuel middle in
    let '(result, steps) := audit_tarjan_step_counted p region last in
    (result, AuditTarjanCase 9 :: first ++ second ++ steps)).
  pose proof (IH (TarjanState (frame :: rest) disc low pending clock emitted)) as Hfirst.
  destruct (audit_tarjan_nested_run p cb region fuel
    (TarjanState (frame :: rest) disc low pending clock emitted)) as [middle first].
  destruct (audit_tarjan_run_counted p region fuel
    (TarjanState (frame :: rest) disc low pending clock emitted)) as [middle' first'].
  cbn in Hfirst |- *; inversion Hfirst; subst middle' first'.
  pose proof (IH middle) as Hsecond.
  destruct (audit_tarjan_nested_run p cb region fuel middle) as [last second].
  destruct (audit_tarjan_run_counted p region fuel middle) as [last' second'].
  cbn in Hsecond |- *; inversion Hsecond; subst last' second'.
  pose proof (audit_tarjan_nested_step_erases p cb region last Hcallbacks) as Hstep.
  destruct (audit_tarjan_nested_step p cb region last) as [result steps].
  destruct (audit_tarjan_step_counted p region last) as [result' steps'].
  cbn in Hstep |- *; inversion Hstep; subst result' steps'.
  now rewrite !map_app.
Qed.

(** The even nested fuel branch preserves the counted state and event order. *)
Lemma audit_tarjan_nested_run_erases_even {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) region fuel
    (frame : tarjan_frame V E) rest (disc low : Map.t V positive) pending clock emitted :
    audit_dfs_callbacks_erase EV g cb ->
    (forall state, (fst (audit_tarjan_nested_run p cb region fuel state),
      map fst (snd (audit_tarjan_nested_run p cb region fuel state))) =
      audit_tarjan_run_counted p region fuel state) ->
    (fst (audit_tarjan_nested_run p cb region (xO fuel)
      (TarjanState (frame :: rest) disc low pending clock emitted)),
      map fst (snd (audit_tarjan_nested_run p cb region (xO fuel)
        (TarjanState (frame :: rest) disc low pending clock emitted)))) =
      audit_tarjan_run_counted p region (xO fuel)
        (TarjanState (frame :: rest) disc low pending clock emitted).
Proof.
  intros Hcallbacks IH.
  change ((fst (let '(middle, first) := audit_tarjan_nested_run p cb region fuel
        (TarjanState (frame :: rest) disc low pending clock emitted) in
      let '(result, second) := audit_tarjan_nested_run p cb region fuel middle in
      (result, (AuditTarjanCase 8, []) :: first ++ second)),
    map fst (snd (let '(middle, first) := audit_tarjan_nested_run p cb region fuel
        (TarjanState (frame :: rest) disc low pending clock emitted) in
      let '(result, second) := audit_tarjan_nested_run p cb region fuel middle in
      (result, (AuditTarjanCase 8, []) :: first ++ second)))) =
    let '(middle, first) := audit_tarjan_run_counted p region fuel
      (TarjanState (frame :: rest) disc low pending clock emitted) in
    let '(result, second) := audit_tarjan_run_counted p region fuel middle in
    (result, AuditTarjanCase 8 :: first ++ second)).
  pose proof (IH (TarjanState (frame :: rest) disc low pending clock emitted)) as Hfirst.
  destruct (audit_tarjan_nested_run p cb region fuel
    (TarjanState (frame :: rest) disc low pending clock emitted)) as [middle first].
  destruct (audit_tarjan_run_counted p region fuel
    (TarjanState (frame :: rest) disc low pending clock emitted)) as [middle' first'].
  cbn in Hfirst |- *; inversion Hfirst; subst middle' first'.
  pose proof (IH middle) as Hsecond.
  destruct (audit_tarjan_nested_run p cb region fuel middle) as [result second].
  destruct (audit_tarjan_run_counted p region fuel middle) as [result' second'].
  cbn in Hsecond |- *; inversion Hsecond; subst result' second'.
  now rewrite map_app.
Qed.

(** Nested binary-fuel execution returns the counted state and event sequence. *)
Lemma audit_tarjan_nested_run_erases {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) region fuel st :
    audit_dfs_callbacks_erase EV g cb ->
    (fst (audit_tarjan_nested_run p cb region fuel st),
      map fst (snd (audit_tarjan_nested_run p cb region fuel st))) =
      audit_tarjan_run_counted p region fuel st.
Proof.
  intro Hcallbacks; revert st; induction fuel as [fuel IH|fuel IH|];
    intros [frames disc low pending clock emitted]; destruct frames as [|frame rest];
    try reflexivity.
  - apply audit_tarjan_nested_run_erases_odd; assumption.
  - apply audit_tarjan_nested_run_erases_even; assumption.
  - change ((fst (let '(result, events) := audit_tarjan_nested_step p cb region
          (TarjanState (frame :: rest) disc low pending clock emitted) in
        (result, (AuditTarjanCase 7, []) :: events)),
      map fst (snd (let '(result, events) := audit_tarjan_nested_step p cb region
          (TarjanState (frame :: rest) disc low pending clock emitted) in
        (result, (AuditTarjanCase 7, []) :: events)))) =
      let '(result, events) := audit_tarjan_step_counted p region
        (TarjanState (frame :: rest) disc low pending clock emitted) in
      (result, AuditTarjanCase 7 :: events)).
    pose proof (audit_tarjan_nested_step_erases p cb region
      (TarjanState (frame :: rest) disc low pending clock emitted) Hcallbacks) as Hstep.
    destruct (audit_tarjan_nested_step p cb region
      (TarjanState (frame :: rest) disc low pending clock emitted)) as [result events].
    destruct (audit_tarjan_step_counted p region
      (TarjanState (frame :: rest) disc low pending clock emitted)) as [result' events'].
    cbn in Hstep |- *; inversion Hstep; reflexivity.
Qed.

(** Nested root processing preserves the counted state and event sequence. *)
Lemma audit_tarjan_nested_root_erases {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) region st v :
    audit_dfs_callbacks_erase EV g cb ->
    (fst (audit_tarjan_nested_root p cb region st v),
      map fst (snd (audit_tarjan_nested_root p cb region st v))) =
      audit_tarjan_root_counted p region st v.
Proof.
  intro Hcallbacks; pose proof Hcallbacks as [_ Hencode].
  specialize (Hencode v).
  destruct (audit_dfs_encode_model cb v) as [code body] eqn:Hcode; cbn in Hencode; subst code.
  unfold audit_tarjan_nested_root, audit_tarjan_root_counted, audit_tarjan_nested_get.
  rewrite Hcode; change (Map.code_get (encode EV v) (disc st)) with (Map.get EV v (disc st)).
  destruct (Map.get EV v (disc st)) as [number|] eqn:Hfound; [reflexivity|].
  pose proof (audit_tarjan_nested_discover_erases p cb v st Hcallbacks) as Hdiscover.
  destruct (audit_tarjan_nested_discover p cb v st) as [next details].
  destruct (audit_tarjan_discover_counted p v st) as [next' details'] eqn:Hcount.
  cbn in Hdiscover |- *; inversion Hdiscover; subst next'.
  pose proof (audit_tarjan_nested_run_erases p cb region (fuel p) next Hcallbacks) as Hrun.
  destruct (audit_tarjan_nested_run p cb region (fuel p) next) as [result events].
  destruct (audit_tarjan_run_counted p region (fuel p) next) as [result' events'].
  cbn in Hrun |- *; inversion Hrun; subst result' events'.
  rewrite !map_app; cbn; reflexivity.
Qed.

(** Nested root-list traversal keeps the same states and ordered events as counted traversal. *)
Lemma audit_tarjan_nested_roots_erase {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) region roots st :
    audit_dfs_callbacks_erase EV g cb ->
    (fst (audit_tarjan_nested_roots p cb region roots st),
      map fst (snd (audit_tarjan_nested_roots p cb region roots st))) =
      audit_tarjan_roots_counted p region roots st.
Proof.
  intro Hcallbacks; revert st; induction roots as [|root rest IH]; intro st; [reflexivity|].
  cbn [audit_tarjan_nested_roots audit_tarjan_roots_counted].
  pose proof (audit_tarjan_nested_root_erases p cb region st root Hcallbacks) as Hroot.
  destruct (audit_tarjan_nested_root p cb region st root) as [next here].
  destruct (audit_tarjan_root_counted p region st root) as [next' here'].
  cbn in Hroot |- *; inversion Hroot; subst next' here'.
  pose proof (IH next) as Hrest.
  destruct (audit_tarjan_nested_roots p cb region rest next) as [result later].
  destruct (audit_tarjan_roots_counted p region rest next) as [result' later'].
  cbn in Hrest |- *; inversion Hrest; subst result' later'.
  now rewrite map_app.
Qed.

(** Nested region setup keeps the counted set and the same sequence of set operations. *)
Lemma audit_tarjan_nested_region_erases {V E B} (EV : encoding V) (g : Graph.t V E)
    (cb : audit_dfs_callback_model V E B) region set :
    audit_dfs_callbacks_erase EV g cb ->
    (fst (audit_tarjan_nested_region cb region set),
      map fst (snd (audit_tarjan_nested_region cb region set))) =
      @audit_tarjan_region_counted V E EV region set.
Proof.
  intros [_ Hencode]; revert set; induction region as [|v rest IH]; intro set; [reflexivity|].
  specialize (Hencode v) as Hvalue.
  destruct (audit_dfs_encode_model cb v) as [code body] eqn:Hcall; cbn in Hvalue; subst code.
  cbn [audit_tarjan_nested_region audit_tarjan_region_counted].
  unfold audit_tarjan_nested_set; rewrite Hcall.
  change (CollectionsTrie.Trie.set (encode EV v) (v, tt) set) with (FinSet.add EV v set).
  pose proof (IH (FinSet.add EV v set)) as Hrest.
  destruct (audit_tarjan_nested_region cb rest (FinSet.add EV v set)) as [result events].
  destruct (audit_tarjan_region_counted EV rest (FinSet.add EV v set)) as [result' events'].
  cbn in Hrest |- *; inversion Hrest; reflexivity.
Qed.

(** Nested SCC traversal erases to the counted result and its original event sequence. *)
Lemma audit_scc_nested_erases {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) region :
    audit_dfs_callbacks_erase EV g cb ->
    (fst (audit_scc_within_nested_counted p cb region),
      map fst (snd (audit_scc_within_nested_counted p cb region))) =
      audit_scc_within_counted p region.
Proof.
  intro Hcallbacks; unfold audit_scc_within_nested_counted, audit_scc_within_counted.
  pose proof (audit_tarjan_nested_region_erases EV g cb region FinSet.empty Hcallbacks) as Hsetup.
  destruct (audit_tarjan_nested_region cb region FinSet.empty) as [keep setup].
  destruct (audit_tarjan_region_counted EV region FinSet.empty) as [keep' setup'].
  cbn in Hsetup |- *; inversion Hsetup; subst keep' setup'.
  pose proof (audit_tarjan_nested_roots_erase p cb keep region tarjan_initial Hcallbacks) as Hroots.
  destruct (audit_tarjan_nested_roots p cb keep region tarjan_initial) as [st events].
  destruct (audit_tarjan_roots_counted p keep region tarjan_initial) as [st' events'].
  cbn in Hroots |- *; inversion Hroots; subst st' events'.
  now rewrite !map_app.
Qed.

(** The counted SCC contract transfers to nested execution through its exact trace erasure. *)
Lemma audit_scc_nested_from_counted :
    audit_scc_within_counted_statement -> audit_scc_within_nested_statement.
Proof.
  intros Hcounted V E B EV g p cb region Hcallbacks.
  pose proof (audit_scc_nested_erases p cb region Hcallbacks) as Herase.
  pose proof (Hcounted V E EV g p region) as Hbound.
  destruct (audit_scc_within_nested_counted p cb region) as [result events].
  destruct (audit_scc_within_counted p region) as [counted trace].
  cbn in Herase, Hbound |- *; inversion Herase; subst counted trace.
  destruct Hbound as [Hresult [Hlength Hwork]].
  rewrite length_map in Hlength.
  split; [exact Hresult|]. split; [reflexivity|]. split; assumption.
Qed.

(** A nested internal-work bound gives the total bound for the very same callback bodies. *)
Lemma audit_scc_nested_total_from_nested :
    audit_scc_within_nested_statement -> audit_scc_within_nested_total_statement.
Proof.
  intros Hnested V E B EV g p cb weight region Hcallbacks.
  pose proof (Hnested V E B EV g p cb region Hcallbacks) as Hbound.
  destruct (audit_scc_within_nested_counted p cb region) as [result events].
  destruct Hbound as [_ [_ [_ Hwork]]].
  unfold audit_tarjan_nested_total_work; apply Nat.add_le_mono_r; exact Hwork.
Qed.

(** * Pending-stack bounds *)

(** The stack remaining after a component pop is no longer than its input. *)
Lemma audit_tarjan_pop_tail_bound {V} (EV : encoding V) root i xs links owners :
    let '(_, tail, _, _) := tarjan_pop EV root i xs links owners in
    length tail <= length xs.
Proof.
  pose proof (tarjan_pop_split EV root i xs links owners) as Hsplit.
  destruct (tarjan_pop EV root i xs links owners) as [[[members tail] links'] owners'].
  cbn in Hsplit |- *; destruct Hsplit as [Hxs _]; rewrite Hxs, length_app; lia.
Qed.

(** Component emission never increases the pending stack. *)
Lemma audit_tarjan_emit_pending_bound {V E} (EV : encoding V) root (st : tarjan_state V E) :
    length (pending (tarjan_emit EV root st)) <= length (pending st).
Proof.
  unfold tarjan_emit.
  pose proof (audit_tarjan_pop_tail_bound EV root (tarjan_next_id (emitted st))
    (pending st) (low st) (comp_of (emitted st))) as Hpop.
  destruct (tarjan_pop EV root (tarjan_next_id (emitted st))
    (pending st) (low st) (comp_of (emitted st))) as [[[members tail] links] owners].
  exact Hpop.
Qed.

(** Closing a frame never increases the pending stack. *)
Lemma audit_tarjan_close_pending_bound {V E} (EV : encoding V) v rest (st : tarjan_state V E) :
    length (pending (tarjan_close EV v rest st)) <= length (pending st).
Proof.
  unfold tarjan_close.
  destruct (Map.get EV v (low st)) as [lo|] eqn:Hlow;
    destruct (Map.get EV v (disc st)) as [di|] eqn:Hdisc; cbn; try lia.
  destruct (Pos.eqb lo di) eqn:Hequal.
  - pose proof (audit_tarjan_emit_pending_bound EV v
      (TarjanState rest (disc st) (low st) (pending st) (clock st) (emitted st))) as Hbound.
    exact Hbound.
  - destruct rest as [|parent rest]; [cbn; lia|].
    unfold tarjan_lower; cbn [low]; destruct (Map.get EV (frame_node parent) (low st)); cbn; lia.
Qed.

(** A source Tarjan step can push at most one new pending vertex. *)
Lemma audit_tarjan_step_pending_bound {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) region st :
    length (pending (tarjan_step p region st)) <= S (length (pending st)).
Proof.
  unfold tarjan_step.
  destruct (frames st) as [|[v edges] rest] eqn:Hframes; [lia|].
  destruct edges as [|edge edges].
  - pose proof (audit_tarjan_close_pending_bound EV v rest st); lia.
  - destruct (FinSet.mem EV (Graph.target g edge) region) eqn:Hinside; cbn; [|lia].
    destruct (Map.get EV (Graph.target g edge) (disc st)) as [d|] eqn:Hdisc.
    + destruct (Map.get EV (Graph.target g edge) (low st)) as [onstack|] eqn:Hlow; cbn; [|lia].
      unfold tarjan_lower; cbn; destruct (Map.get EV v (low st)); cbn; lia.
    + change (S (length (pending st)) <= S (length (pending st))); reflexivity.
Qed.

(** A counted step's returned state can add at most one pending vertex. *)
Lemma audit_tarjan_counted_step_pending_bound {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) region st :
    length (pending (fst (audit_tarjan_step_counted p region st))) <= S (length (pending st)).
Proof.
  rewrite audit_tarjan_step_erases; apply audit_tarjan_step_pending_bound.
Qed.

(** A counted step emits fixed overhead plus at most five events per pending vertex. *)
Lemma audit_tarjan_step_event_bound {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) region st :
    length (snd (audit_tarjan_step_counted p region st)) <= 12 + 5 * length (pending st).
Proof.
  destruct audit_tarjan_helpers_event_bound as [Hdiscover [Hlower [_ [_ Hclose]]]].
  unfold audit_tarjan_step_counted.
  destruct (frames st) as [|[v edges] rest] eqn:Hframes; [cbn; lia|].
  destruct edges as [|edge edges].
  - pose proof (Hclose V E EV v rest st) as Hbound.
    destruct (audit_tarjan_close_counted EV v rest st) as [next details]; cbn in Hbound |- *.
    rewrite length_app, length_map; cbn; lia.
  - destruct (FinSet.mem EV (Graph.target g edge) region) eqn:Hinside; [|cbn; lia].
    destruct (Map.get EV (Graph.target g edge) (disc st)) as [d|] eqn:Hdisc.
    + destruct (Map.get EV (Graph.target g edge) (low st)) as [onstack|] eqn:Hlow; [|cbn; lia].
      pose proof (Hlower V E EV v d
        (TarjanState (TarjanFrame v edges :: rest) (disc st) (low st)
          (pending st) (clock st) (emitted st))) as Hbound.
      destruct (audit_tarjan_lower_counted EV v d
        (TarjanState (TarjanFrame v edges :: rest) (disc st) (low st)
          (pending st) (clock st) (emitted st))) as [next details]; cbn in Hbound |- *.
      rewrite length_app, length_map; cbn; lia.
    + pose proof (Hdiscover V E EV g p (Graph.target g edge)
        (TarjanState (TarjanFrame v edges :: rest) (disc st) (low st)
          (pending st) (clock st) (emitted st))) as Hbound.
      destruct (audit_tarjan_discover_counted p (Graph.target g edge)
        (TarjanState (TarjanFrame v edges :: rest) (disc st) (low st)
          (pending st) (clock st) (emitted st))) as [next details]; cbn in Hbound |- *.
      rewrite length_app, length_map; cbn; lia.
Qed.

(** The odd binary-fuel branch composes pending-stack and event-size bounds. *)
Lemma audit_tarjan_run_size_odd {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) region fuel (frame : tarjan_frame V E) rest
    (disc low : Map.t V positive) stack clock emitted :
    (forall state, let '(result, events) := audit_tarjan_run_counted p region fuel state in
      length (pending result) <= length (pending state) + Pos.to_nat fuel /\
      length events <= 2 * Pos.to_nat fuel *
        (12 + 5 * (length (pending state) + Pos.to_nat fuel))) ->
    let '(result, events) := audit_tarjan_run_counted p region (xI fuel)
      (TarjanState (frame :: rest) disc low stack clock emitted) in
    length (pending result) <= length stack + Pos.to_nat (xI fuel) /\
    length events <= 2 * Pos.to_nat (xI fuel) *
      (12 + 5 * (length stack + Pos.to_nat (xI fuel))).
Proof.
  intro IH.
  change (let '(result, events) :=
    let '(middle, first) := audit_tarjan_run_counted p region fuel
      (TarjanState (frame :: rest) disc low stack clock emitted) in
    let '(last, second) := audit_tarjan_run_counted p region fuel middle in
    let '(result, steps) := audit_tarjan_step_counted p region last in
    (result, AuditTarjanCase 9 :: first ++ second ++ steps) in
    length (pending result) <= length stack + Pos.to_nat (xI fuel) /\
    length events <= 2 * Pos.to_nat (xI fuel) *
      (12 + 5 * (length stack + Pos.to_nat (xI fuel)))).
  pose proof (IH (TarjanState (frame :: rest) disc low stack clock emitted)) as Hfirst.
  destruct (audit_tarjan_run_counted p region fuel
    (TarjanState (frame :: rest) disc low stack clock emitted)) as [middle first].
  cbn in Hfirst |- *; destruct Hfirst as [Hmiddle Hfirst].
  pose proof (IH middle) as Hsecond.
  destruct (audit_tarjan_run_counted p region fuel middle) as [last second].
  cbn in Hsecond |- *; destruct Hsecond as [Hlast Hsecond].
  pose proof (audit_tarjan_step_event_bound p region last) as Hstep.
  pose proof (audit_tarjan_counted_step_pending_bound p region last) as Hpending.
  destruct (audit_tarjan_step_counted p region last) as [result steps].
  cbn in Hstep, Hpending |- *; rewrite !length_app; cbn.
  rewrite Pos2Nat.inj_xI; pose proof (Pos2Nat.is_pos fuel); split; nia.
Qed.

(** The even binary-fuel branch composes pending-stack and event-size bounds. *)
Lemma audit_tarjan_run_size_even {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) region fuel (frame : tarjan_frame V E) rest
    (disc low : Map.t V positive) stack clock emitted :
    (forall state, let '(result, events) := audit_tarjan_run_counted p region fuel state in
      length (pending result) <= length (pending state) + Pos.to_nat fuel /\
      length events <= 2 * Pos.to_nat fuel *
        (12 + 5 * (length (pending state) + Pos.to_nat fuel))) ->
    let '(result, events) := audit_tarjan_run_counted p region (xO fuel)
      (TarjanState (frame :: rest) disc low stack clock emitted) in
    length (pending result) <= length stack + Pos.to_nat (xO fuel) /\
    length events <= 2 * Pos.to_nat (xO fuel) *
      (12 + 5 * (length stack + Pos.to_nat (xO fuel))).
Proof.
  intro IH.
  change (let '(result, events) :=
    let '(middle, first) := audit_tarjan_run_counted p region fuel
      (TarjanState (frame :: rest) disc low stack clock emitted) in
    let '(result, second) := audit_tarjan_run_counted p region fuel middle in
    (result, AuditTarjanCase 8 :: first ++ second) in
    length (pending result) <= length stack + Pos.to_nat (xO fuel) /\
    length events <= 2 * Pos.to_nat (xO fuel) *
      (12 + 5 * (length stack + Pos.to_nat (xO fuel)))).
  pose proof (IH (TarjanState (frame :: rest) disc low stack clock emitted)) as Hfirst.
  destruct (audit_tarjan_run_counted p region fuel
    (TarjanState (frame :: rest) disc low stack clock emitted)) as [middle first].
  cbn in Hfirst |- *; destruct Hfirst as [Hmiddle Hfirst].
  pose proof (IH middle) as Hsecond.
  destruct (audit_tarjan_run_counted p region fuel middle) as [result second].
  cbn in Hsecond |- *; destruct Hsecond as [Hresult Hsecond].
  rewrite length_app; cbn; rewrite Pos2Nat.inj_xO; pose proof (Pos2Nat.is_pos fuel); split; nia.
Qed.

(** A binary-fuel run bounds its returned pending stack and all events by its input and fuel. *)
Lemma audit_tarjan_run_size_bound {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) region fuel st :
    let '(result, events) := audit_tarjan_run_counted p region fuel st in
    length (pending result) <= length (pending st) + Pos.to_nat fuel /\
    length events <= 2 * Pos.to_nat fuel * (12 + 5 * (length (pending st) + Pos.to_nat fuel)).
Proof.
  revert st; induction fuel as [fuel IH|fuel IH|];
    intros [frames disc low stack clock emitted]; destruct frames as [|frame rest].
  - cbn [audit_tarjan_run_counted]; pose proof (Pos2Nat.is_pos (xI fuel)); cbn; nia.
  - apply audit_tarjan_run_size_odd; exact IH.
  - cbn [audit_tarjan_run_counted]; pose proof (Pos2Nat.is_pos (xO fuel)); cbn; nia.
  - apply audit_tarjan_run_size_even; exact IH.
  - cbn [audit_tarjan_run_counted]; cbn; lia.
  - change (let '(result, events) :=
      let '(result, steps) := audit_tarjan_step_counted p region
        (TarjanState (frame :: rest) disc low stack clock emitted) in
      (result, AuditTarjanCase 7 :: steps) in
      length (pending result) <= length stack + Pos.to_nat xH /\
      length events <= 2 * Pos.to_nat xH * (12 + 5 * (length stack + Pos.to_nat xH))).
    pose proof (audit_tarjan_step_event_bound p region
      (TarjanState (frame :: rest) disc low stack clock emitted)) as Hstep.
    pose proof (audit_tarjan_counted_step_pending_bound p region
      (TarjanState (frame :: rest) disc low stack clock emitted)) as Hpending.
    destruct (audit_tarjan_step_counted p region
      (TarjanState (frame :: rest) disc low stack clock emitted)) as [result steps].
    cbn in Hstep, Hpending |- *; split; lia.
Qed.

(** One root adds at most one discovery plus its fuel allowance and emits a bounded trace. *)
Lemma audit_tarjan_root_size_bound {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) region st v :
    let '(result, events) := audit_tarjan_root_counted p region st v in
    length (pending result) <= length (pending st) + S (Pos.to_nat (fuel p)) /\
    length events <= 7 + 2 * Pos.to_nat (fuel p) *
      (12 + 5 * (S (length (pending st)) + Pos.to_nat (fuel p))).
Proof.
  unfold audit_tarjan_root_counted.
  destruct (Map.get EV v (disc st)) as [number|] eqn:Hfound; [cbn; lia|].
  pose proof (proj1 audit_tarjan_helpers_erasure V E EV g p v st) as Hdiscover.
  pose proof (proj1 audit_tarjan_helpers_event_bound V E EV g p v st) as Hdetails.
  destruct (audit_tarjan_discover_counted p v st) as [next details] eqn:Hrun.
  cbn in Hdiscover, Hdetails; subst next.
  pose proof (audit_tarjan_run_size_bound p region (fuel p) (tarjan_discover p v st)) as Hrunbound.
  destruct (audit_tarjan_run_counted p region (fuel p) (tarjan_discover p v st))
    as [result events].
  cbn [tarjan_discover pending] in Hrunbound.
  destruct Hrunbound as [Hpending Hevents].
  cbn [length] in Hpending, Hevents.
  change (length (pending result) <= length (pending st) + S (Pos.to_nat (fuel p)) /\
    length ([AuditTarjanGet v (disc st) None; AuditTarjanCase 11] ++
      map AuditTarjanHelper details ++ [AuditTarjanDiscover v st (tarjan_discover p v st)] ++
      events) <= 7 + 2 * Pos.to_nat (fuel p) *
      (12 + 5 * (S (length (pending st)) + Pos.to_nat (fuel p)))).
  rewrite !length_app, length_map; cbn [length]; split; nia.
Qed.

(** A fixed ceiling covers each root's pending stack and all events across the remaining roots. *)
Lemma audit_tarjan_roots_size_bound {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) region roots st ceiling :
    length (pending st) + length roots * S (Pos.to_nat (fuel p)) <= ceiling ->
    let '(result, events) := audit_tarjan_roots_counted p region roots st in
    length (pending result) <= ceiling /\
    length events <= 1 + length roots * (12 + 2 * Pos.to_nat (fuel p)) * (12 + 6 * ceiling).
Proof.
  revert st; induction roots as [|root rest IH]; intros st Hceiling.
  - cbn [audit_tarjan_roots_counted]; cbn in Hceiling |- *; split; lia.
  - cbn [audit_tarjan_roots_counted].
    pose proof (audit_tarjan_root_size_bound p region st root) as Hroot.
    destruct (audit_tarjan_root_counted p region st root) as [next here].
    cbn in Hroot |- *; destruct Hroot as [Hpending Hhere].
    assert (Hnext : length (pending next) + length rest * S (Pos.to_nat (fuel p)) <= ceiling).
    { cbn in Hceiling; nia. }
    pose proof (IH next Hnext) as Hrest.
    destruct (audit_tarjan_roots_counted p region rest next) as [result later].
    cbn in Hrest |- *; destruct Hrest as [Hresult Hlater].
    rewrite length_app; cbn; split; [exact Hresult|].
    cbn in Hceiling; nia.
Qed.

(** Region setup's trace length is one more than the number of input vertices. *)
Lemma audit_tarjan_region_event_count {V E} (EV : encoding V) region set :
    length (snd (@audit_tarjan_region_counted V E EV region set)) = S (length region).
Proof.
  revert set; induction region as [|v rest IH]; intro set; [reflexivity|].
  cbn [audit_tarjan_region_counted].
  specialize (IH (FinSet.add EV v set)).
  destruct (audit_tarjan_region_counted EV rest (FinSet.add EV v set)) as [result events].
  cbn in IH |- *; now rewrite IH.
Qed.

(** The full counted SCC trace fits the public event bound computed from region and fuel. *)
Lemma audit_scc_counted_event_bound {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) region :
    length (snd (audit_scc_within_counted p region)) <= audit_tarjan_input_event_bound p region.
Proof.
  unfold audit_scc_within_counted, audit_tarjan_input_event_bound.
  pose proof (@audit_tarjan_region_event_count V E EV region FinSet.empty) as Hsetup.
  destruct (audit_tarjan_region_counted EV region FinSet.empty) as [keep setup].
  cbn in Hsetup |- *.
  pose proof (audit_tarjan_roots_size_bound p keep region tarjan_initial
    (length region * S (Pos.to_nat (fuel p)))) as Hroots.
  cbn [tarjan_initial pending] in Hroots.
  specialize (Hroots (Nat.le_refl _)).
  destruct (audit_tarjan_roots_counted p keep region tarjan_initial) as [st events].
  cbn in Hroots |- *; destruct Hroots as [_ Hbound].
  rewrite !length_app; cbn; nia.
Qed.

(** Captured source traversal has the same result and projected events as counted traversal. *)
Lemma audit_scc_source_erases {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) region :
    audit_dfs_callbacks_erase EV g cb ->
    (fst (audit_scc_source_counted p cb region),
      map fst (snd (audit_scc_source_counted p cb region))) =
      audit_scc_within_counted p region.
Proof.
  intro Hcallbacks.
  pose proof (audit_graph_capture_callbacks_erases_holds V E B EV g cb Hcallbacks) as Hcaptured.
  pose proof (audit_scc_nested_erases p (audit_graph_capture_callbacks cb) region Hcaptured)
    as Hnested.
  unfold audit_scc_source_counted, audit_scc_within_nested_counted in *.
  destruct (audit_tarjan_nested_region (audit_graph_capture_callbacks cb) region FinSet.empty)
    as [keep setup].
  destruct (audit_tarjan_nested_roots p (audit_graph_capture_callbacks cb) keep region
    tarjan_initial)
    as [st events].
  exact Hnested.
Qed.

(** The captured source execution returns SCCs and obeys the original region's event bound. *)
Lemma audit_scc_source_result_and_count {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) region :
    audit_dfs_callbacks_erase EV g cb ->
    let '(result, events) := audit_scc_source_counted p cb region in
    result = scc_within p region /\ length events <= audit_tarjan_input_event_bound p region.
Proof.
  intro Hcallbacks.
  pose proof (audit_scc_source_erases p cb region Hcallbacks) as Herase.
  pose proof (audit_scc_counted_erases EV g p region) as Hresult.
  pose proof (audit_scc_counted_event_bound p region) as Hbound.
  destruct (audit_scc_source_counted p cb region) as [result events].
  destruct (audit_scc_within_counted p region) as [counted trace].
  cbn in Herase, Hresult, Hbound |- *; inversion Herase; subst counted trace.
  rewrite length_map in Hbound; split; [reflexivity|exact Hbound].
Qed.

(** * Callback receipts *)

(** Every body attached to an event satisfies the selected callback-body property. *)
Definition audit_tarjan_event_bodies {V E B} (P : B -> Prop)
    (item : audit_tarjan_nested_event V E B) : Prop := Forall P (snd item).

(** Nested lookup retains a callback body satisfying the encoder's body property. *)
Lemma audit_tarjan_nested_get_body {V E B A} (cb : audit_dfs_callback_model V E B)
    (P : B -> Prop) v (m : Map.t V A) :
    Forall P (snd (audit_dfs_encode_model cb v)) ->
    Forall P (snd (audit_tarjan_nested_get cb v m)).
Proof.
  unfold audit_tarjan_nested_get; destruct (audit_dfs_encode_model cb v); auto.
Qed.

(** Nested insertion retains a callback body satisfying the encoder's body property. *)
Lemma audit_tarjan_nested_set_body {V E B A} (cb : audit_dfs_callback_model V E B)
    (P : B -> Prop) v (value : A) (m : Map.t V A) :
    Forall P (snd (audit_dfs_encode_model cb v)) ->
    Forall P (snd (audit_tarjan_nested_set cb v value m)).
Proof.
  unfold audit_tarjan_nested_set; destruct (audit_dfs_encode_model cb v); auto.
Qed.

(** Nested removal retains a callback body satisfying the encoder's body property. *)
Lemma audit_tarjan_nested_remove_body {V E B A} (cb : audit_dfs_callback_model V E B)
    (P : B -> Prop) v (m : Map.t V A) :
    Forall P (snd (audit_dfs_encode_model cb v)) ->
    Forall P (snd (audit_tarjan_nested_remove cb v m)).
Proof.
  unfold audit_tarjan_nested_remove; destruct (audit_dfs_encode_model cb v); auto.
Qed.

(** Every discovery event retains an encoder body satisfying the same callback property. *)
Lemma audit_tarjan_discover_bodies {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (P : B -> Prop) v st :
    (forall x, Forall P (snd (audit_dfs_encode_model cb x))) ->
    Forall (audit_tarjan_event_bodies P) (snd (audit_tarjan_nested_discover p cb v st)).
Proof.
  intro Hencode; unfold audit_tarjan_nested_discover.
  pose proof (audit_tarjan_nested_get_body cb P v (out_index p) (Hencode v)) as Hget.
  destruct (audit_tarjan_nested_get cb v (out_index p)) as [adjacent get_body].
  pose proof (audit_tarjan_nested_set_body cb P v (clock st) (disc st) (Hencode v)) as Hdisc.
  destruct (audit_tarjan_nested_set cb v (clock st) (disc st)) as [disc' disc_body].
  pose proof (audit_tarjan_nested_set_body cb P v (clock st) (low st) (Hencode v)) as Hlow.
  destruct (audit_tarjan_nested_set cb v (clock st) (low st)) as [low' low_body].
  cbn in Hget, Hdisc, Hlow |- *.
  unfold audit_tarjan_event_bodies; cbn; repeat constructor; assumption.
Qed.

(** Every lowering event retains the lookup and update bodies from its encoder calls. *)
Lemma audit_tarjan_lower_bodies {V E B} (cb : audit_dfs_callback_model V E B) (P : B -> Prop)
    v n st :
    (forall x, Forall P (snd (audit_dfs_encode_model cb x))) ->
    Forall (audit_tarjan_event_bodies P) (snd (audit_tarjan_nested_lower cb v n st)).
Proof.
  intro Hencode; unfold audit_tarjan_nested_lower.
  pose proof (audit_tarjan_nested_get_body cb P v (low st) (Hencode v)) as Hget.
  destruct (audit_tarjan_nested_get cb v (low st)) as [[old|] body]; cbn in Hget |- *.
  - pose proof (audit_tarjan_nested_set_body cb P v (Pos.min old n) (low st) (Hencode v)) as Hset.
    destruct (audit_tarjan_nested_set cb v (Pos.min old n) (low st)) as [next set_body].
    cbn in Hset |- *; unfold audit_tarjan_event_bodies; cbn; repeat constructor; assumption.
  - unfold audit_tarjan_event_bodies; cbn; repeat constructor; assumption.
Qed.

(** A nested pop retains the bodies from its own updates and two-key comparisons. *)
Lemma audit_tarjan_pop_bodies {V E B} (cb : audit_dfs_callback_model V E B) (P : B -> Prop)
    root i xs links owners :
    (forall x, Forall P (snd (audit_dfs_encode_model cb x))) ->
    Forall (audit_tarjan_event_bodies P) (snd (audit_tarjan_nested_pop cb root i xs links owners)).
Proof.
  intro Hencode; revert links owners; induction xs as [|v rest IH]; intros links owners.
  - cbn [audit_tarjan_nested_pop audit_tarjan_event_bodies]; repeat constructor.
  - cbn [audit_tarjan_nested_pop].
    pose proof (audit_tarjan_nested_remove_body cb P v links (Hencode v)) as Hremove.
    destruct (audit_tarjan_nested_remove cb v links) as [links' remove_body].
    pose proof (audit_tarjan_nested_set_body cb P v i owners (Hencode v)) as Hset.
    destruct (audit_tarjan_nested_set cb v i owners) as [owners' set_body].
    specialize (Hencode v) as Hv; specialize (Hencode root) as Hroot.
    destruct (audit_dfs_encode_model cb v) as [vcode vbody].
    destruct (audit_dfs_encode_model cb root) as [rcode rbody].
    cbn in Hremove, Hset, Hv, Hroot |- *.
    assert (Hboth : Forall P (vbody ++ rbody)) by (apply Forall_app; split; assumption).
    destruct (Pos.eqb vcode rcode) eqn:Hequal.
    + unfold audit_tarjan_event_bodies; cbn; repeat (constructor; try assumption).
    + pose proof (IH links' owners') as Hrest.
      destruct (audit_tarjan_nested_pop cb root i rest links' owners')
        as [[[[members tail] final_links] final_owners] events].
      cbn in Hrest |- *; unfold audit_tarjan_event_bodies in *; cbn in *.
      repeat (constructor; try assumption).
Qed.

(** Component emission carries its pop's callback bodies unchanged. *)
Lemma audit_tarjan_emit_bodies {V E B} (cb : audit_dfs_callback_model V E B) (P : B -> Prop)
    root st :
    (forall x, Forall P (snd (audit_dfs_encode_model cb x))) ->
    Forall (audit_tarjan_event_bodies P) (snd (audit_tarjan_nested_emit cb root st)).
Proof.
  intro Hencode; unfold audit_tarjan_nested_emit.
  destruct (component_ids (emitted st)) as [|previous rest] eqn:Hids;
    pose proof (audit_tarjan_pop_bodies cb P root
      (match component_ids (emitted st) with
       | [] => 1%positive
       | previous :: _ => Pos.succ previous
       end) (pending st) (low st) (comp_of (emitted st)) Hencode) as Hpop;
    rewrite Hids in Hpop; cbn in Hpop |- *;
    destruct (audit_tarjan_nested_pop cb root _ _ _ _) as [[[[members tail] links] owners] events];
    cbn in Hpop |- *.
  - constructor; [constructor|]. apply Forall_app; split; [exact Hpop|repeat constructor].
  - constructor; [constructor|]. constructor; [constructor|].
    apply Forall_app; split; [exact Hpop|repeat constructor].
Qed.

(** Closing a frame keeps every body from its lookups and the chosen nested helper. *)
Lemma audit_tarjan_close_bodies {V E B} (cb : audit_dfs_callback_model V E B) (P : B -> Prop)
    v rest st :
    (forall x, Forall P (snd (audit_dfs_encode_model cb x))) ->
    Forall (audit_tarjan_event_bodies P) (snd (audit_tarjan_nested_close cb v rest st)).
Proof.
  intro Hencode; unfold audit_tarjan_nested_close.
  pose proof (audit_tarjan_nested_get_body cb P v (low st) (Hencode v)) as Hlow.
  destruct (audit_tarjan_nested_get cb v (low st)) as [[lo|] low_body]; cbn in Hlow |- *.
  2: { unfold audit_tarjan_event_bodies; cbn; repeat (constructor; try assumption). }
  pose proof (audit_tarjan_nested_get_body cb P v (disc st) (Hencode v)) as Hdisc.
  destruct (audit_tarjan_nested_get cb v (disc st)) as [[di|] disc_body]; cbn in Hdisc |- *.
  2: { unfold audit_tarjan_event_bodies; cbn; repeat (constructor; try assumption). }
  destruct (Pos.eqb lo di) eqn:Hequal.
  - pose proof (audit_tarjan_emit_bodies cb P v
      (TarjanState rest (disc st) (low st) (pending st) (clock st) (emitted st)) Hencode) as Hemit.
    destruct (audit_tarjan_nested_emit cb v
      (TarjanState rest (disc st) (low st) (pending st) (clock st) (emitted st))) as [next events].
    cbn in Hemit |- *; unfold audit_tarjan_event_bodies in *; cbn in *.
    repeat (constructor; try assumption).
  - destruct rest as [|parent rest].
    + unfold audit_tarjan_event_bodies; cbn; repeat (constructor; try assumption).
    + pose proof (audit_tarjan_lower_bodies cb P (frame_node parent) lo
        (TarjanState (parent :: rest) (disc st) (low st) (pending st) (clock st) (emitted st))
        Hencode) as Hlower.
      destruct (audit_tarjan_nested_lower cb (frame_node parent) lo
        (TarjanState (parent :: rest) (disc st) (low st) (pending st) (clock st) (emitted st)))
        as [next events].
      cbn in Hlower |- *; unfold audit_tarjan_event_bodies in *; cbn in *.
      repeat (constructor; try assumption).
Qed.

(** A nested step keeps the body property for its target, lookups, and chosen helper. *)
Lemma audit_tarjan_step_bodies {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (P : B -> Prop) region st :
    (forall x, Forall P (snd (audit_dfs_encode_model cb x))) ->
    (forall e, Forall P (snd (audit_dfs_target_model cb e))) ->
    Forall (audit_tarjan_event_bodies P) (snd (audit_tarjan_nested_step p cb region st)).
Proof.
  intros Hencode Htarget; unfold audit_tarjan_nested_step.
  destruct (frames st) as [|[v edges] rest] eqn:Hframes; [repeat constructor|].
  destruct edges as [|edge edges].
  - pose proof (audit_tarjan_close_bodies cb P v rest st Hencode) as Hclose.
    destruct (audit_tarjan_nested_close cb v rest st) as [next events]; cbn in Hclose |- *.
    constructor; [constructor|]. apply Forall_app; split; [exact Hclose|repeat constructor].
  - pose proof (Htarget edge) as Htarget_body.
    destruct (audit_dfs_target_model cb edge) as [target target_body]; cbn in Htarget_body |- *.
    pose proof (audit_tarjan_nested_get_body cb P target region (Hencode target)) as Hmember.
    destruct (audit_tarjan_nested_get cb target region) as [[member|] member_body];
      cbn in Hmember |- *.
    2: { unfold audit_tarjan_event_bodies; cbn; repeat (constructor; try assumption). }
    pose proof (audit_tarjan_nested_get_body cb P target (disc st) (Hencode target)) as Hdisc.
    destruct (audit_tarjan_nested_get cb target (disc st)) as [[d|] disc_body]; cbn in Hdisc |- *.
    + pose proof (audit_tarjan_nested_get_body cb P target (low st) (Hencode target)) as Hlow.
      destruct (audit_tarjan_nested_get cb target (low st)) as [[onstack|] low_body];
        cbn in Hlow |- *.
      2: { unfold audit_tarjan_event_bodies; cbn; repeat (constructor; try assumption). }
      pose proof (audit_tarjan_lower_bodies cb P v d
        (TarjanState (TarjanFrame v edges :: rest) (disc st) (low st)
          (pending st) (clock st) (emitted st)) Hencode) as Hlower.
      destruct (audit_tarjan_nested_lower cb v d
        (TarjanState (TarjanFrame v edges :: rest) (disc st) (low st)
          (pending st) (clock st) (emitted st))) as [next details]; cbn in Hlower |- *.
      unfold audit_tarjan_event_bodies in *; cbn in *.
      repeat (constructor; try assumption).
      apply Forall_app; split; [exact Hlower|repeat constructor].
    + pose proof (audit_tarjan_discover_bodies p cb P target
        (TarjanState (TarjanFrame v edges :: rest) (disc st) (low st)
          (pending st) (clock st) (emitted st)) Hencode) as Hdiscover.
      destruct (audit_tarjan_nested_discover p cb target
        (TarjanState (TarjanFrame v edges :: rest) (disc st) (low st)
          (pending st) (clock st) (emitted st))) as [next details]; cbn in Hdiscover |- *.
      unfold audit_tarjan_event_bodies in *; cbn in *.
      repeat (constructor; try assumption).
      apply Forall_app; split; [exact Hdiscover|repeat constructor].
Qed.

(** Both halves of a nested binary-fuel run preserve every callback body property. *)
Lemma audit_tarjan_run_bodies {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (P : B -> Prop) region fuel st :
    (forall x, Forall P (snd (audit_dfs_encode_model cb x))) ->
    (forall e, Forall P (snd (audit_dfs_target_model cb e))) ->
    Forall (audit_tarjan_event_bodies P) (snd (audit_tarjan_nested_run p cb region fuel st)).
Proof.
  intros Hencode Htarget.
  apply audit_tarjan_nested_run_events.
  - intro state; apply audit_tarjan_step_bodies; assumption.
  - intros site; constructor.
Qed.

(** A root retains the body property through its lookup, discovery, and binary-fuel run. *)
Lemma audit_tarjan_root_bodies {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (P : B -> Prop) region st v :
    (forall x, Forall P (snd (audit_dfs_encode_model cb x))) ->
    (forall e, Forall P (snd (audit_dfs_target_model cb e))) ->
    Forall (audit_tarjan_event_bodies P) (snd (audit_tarjan_nested_root p cb region st v)).
Proof.
  intros Hencode Htarget; unfold audit_tarjan_nested_root.
  pose proof (audit_tarjan_nested_get_body cb P v (disc st) (Hencode v)) as Hget.
  destruct (audit_tarjan_nested_get cb v (disc st)) as [[number|] body]; cbn in Hget |- *.
  - unfold audit_tarjan_event_bodies; cbn; repeat (constructor; try assumption).
  - pose proof (audit_tarjan_discover_bodies p cb P v st Hencode) as Hdiscover.
    destruct (audit_tarjan_nested_discover p cb v st) as [next details]; cbn in Hdiscover |- *.
    pose proof (audit_tarjan_run_bodies p cb P region (fuel p) next Hencode Htarget) as Hrun.
    destruct (audit_tarjan_nested_run p cb region (fuel p) next) as [result events];
      cbn in Hrun |- *.
    constructor; [exact Hget|]. constructor; [constructor|].
    apply Forall_app; split; [exact Hdiscover|]. constructor; [constructor|exact Hrun].
Qed.

(** Root-list traversal retains the property of each actual callback body. *)
Lemma audit_tarjan_roots_bodies {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (P : B -> Prop) region roots st :
    (forall x, Forall P (snd (audit_dfs_encode_model cb x))) ->
    (forall e, Forall P (snd (audit_dfs_target_model cb e))) ->
    Forall (audit_tarjan_event_bodies P) (snd (audit_tarjan_nested_roots p cb region roots st)).
Proof.
  intros Hencode Htarget; revert st; induction roots as [|root rest IH]; intro st;
    cbn [audit_tarjan_nested_roots].
  - repeat constructor.
  - pose proof (audit_tarjan_root_bodies p cb P region st root Hencode Htarget) as Hroot.
    destruct (audit_tarjan_nested_root p cb region st root) as [next here]; cbn in Hroot |- *.
    pose proof (IH next) as Hrest.
    destruct (audit_tarjan_nested_roots p cb region rest next) as [result later]; cbn in Hrest |- *.
    constructor; [constructor|]. apply Forall_app; split; assumption.
Qed.

(** Region setup retains each actual encoder callback body. *)
Lemma audit_tarjan_region_bodies {V E B} (cb : audit_dfs_callback_model V E B) (P : B -> Prop)
    region set :
    (forall x, Forall P (snd (audit_dfs_encode_model cb x))) ->
    Forall (audit_tarjan_event_bodies P) (snd (audit_tarjan_nested_region cb region set)).
Proof.
  intro Hencode; revert set; induction region as [|v rest IH]; intro set;
    cbn [audit_tarjan_nested_region].
  - repeat constructor.
  - pose proof (audit_tarjan_nested_set_body cb P v tt set (Hencode v)) as Hset.
    destruct (audit_tarjan_nested_set cb v tt set) as [next body]; cbn in Hset |- *.
    pose proof (IH next) as Hrest.
    destruct (audit_tarjan_nested_region cb rest next) as [result events]; cbn in Hrest |- *.
    constructor; [exact Hset|exact Hrest].
Qed.

(** Every captured SCC callback body is the receipt of the callback that produced it. *)
Lemma audit_scc_source_receipts {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) region :
    Forall (audit_tarjan_event_bodies (audit_dfs_capture_receipt cb))
      (snd (audit_scc_source_counted p cb region)).
Proof.
  assert (Hencode : forall x, Forall (audit_dfs_capture_receipt cb)
    (snd (audit_dfs_encode_model (audit_graph_capture_callbacks cb) x))).
  { intro x; unfold audit_graph_capture_callbacks; cbn.
    destruct (audit_dfs_encode_model cb x) as [code body] eqn:Hcall.
    cbn; constructor; [exact Hcall|constructor]. }
  assert (Htarget : forall e, Forall (audit_dfs_capture_receipt cb)
    (snd (audit_dfs_target_model (audit_graph_capture_callbacks cb) e))).
  { intro e; unfold audit_graph_capture_callbacks; cbn.
    destruct (audit_dfs_target_model cb e) as [value body] eqn:Hcall.
    cbn; constructor; [exact Hcall|constructor]. }
  unfold audit_scc_source_counted.
  pose proof (audit_tarjan_region_bodies (audit_graph_capture_callbacks cb)
    (audit_dfs_capture_receipt cb) region FinSet.empty Hencode) as Hsetup.
  destruct (audit_tarjan_nested_region (audit_graph_capture_callbacks cb) region FinSet.empty)
    as [keep setup]; cbn in Hsetup |- *.
  pose proof (audit_tarjan_roots_bodies p (audit_graph_capture_callbacks cb)
    (audit_dfs_capture_receipt cb) keep region tarjan_initial Hencode Htarget) as Hroots.
  destruct (audit_tarjan_nested_roots p (audit_graph_capture_callbacks cb) keep region
    tarjan_initial)
    as [st events]; cbn in Hroots |- *.
  apply Forall_app; split; [exact Hsetup|].
  apply Forall_app; split; [exact Hroots|repeat constructor].
Qed.

(** Exact callback receipts bound captured body work by the matching external budgets. *)
Lemma audit_scc_source_bodies_bound {V E B} (cb : audit_dfs_callback_model V E B)
    (weight : B -> nat) encode_source target_source encode_budget target_budget events :
    audit_graph_external_callback_adapter (audit_dfs_encode_model cb) weight encode_source
      encode_budget ->
    audit_graph_external_callback_adapter (audit_dfs_target_model cb) weight target_source
      target_budget ->
    Forall (audit_tarjan_event_bodies (audit_dfs_capture_receipt cb)) events ->
    audit_scc_source_body_work weight events <=
      audit_scc_source_external_budget encode_budget target_budget events.
Proof.
  intros Hencode Htarget Hreceipts.
  induction Hreceipts as [|[event body] events Hbody Htail IH].
  - reflexivity.
  - unfold audit_tarjan_event_bodies in Hbody; cbn in Hbody.
    change (fold_right (fun capture n => audit_graph_capture_work weight capture + n) 0 body +
      audit_scc_source_body_work weight events <=
      fold_right (fun capture n => audit_scc_capture_budget encode_budget target_budget capture + n)
        0 body + audit_scc_source_external_budget encode_budget target_budget events).
    assert (Hbody_bound :
      fold_right (fun capture n => audit_graph_capture_work weight capture + n) 0 body <=
      fold_right (fun capture n => audit_scc_capture_budget encode_budget target_budget capture + n)
        0 body).
    { clear IH Htail events event.
      induction Hbody as [|capture body Hcapture Hrest IHbody]; cbn; [lia|].
      pose proof (audit_dfs_capture_body_bound cb weight encode_source target_source encode_budget
        target_budget capture Hencode Htarget Hcapture) as Hbound.
      destruct capture; cbn [audit_scc_capture_budget audit_dfs_capture_budget] in *; lia. }
    lia.
Qed.

(** The source work contract transfers to external budgets using receipts from that same run. *)
Lemma audit_scc_source_adapted_from_source :
    audit_scc_source_statement -> audit_scc_source_adapted_statement.
Proof.
  intros Hsource V E B EV g p cb weight region encode_source target_source encode_budget
    target_budget Hcallbacks Hencode Htarget.
  pose proof (Hsource V E B EV g p cb weight region Hcallbacks) as Hwork.
  pose proof (audit_scc_source_receipts p cb region) as Hreceipts.
  destruct (audit_scc_source_counted p cb region) as [result events].
  destruct Hwork as [Hresult [_ [_ Hbound]]].
  pose proof (audit_scc_source_bodies_bound cb weight encode_source target_source encode_budget
    target_budget events Hencode Htarget Hreceipts) as Hbody.
  split; [exact Hresult|].
  eapply Nat.le_trans; [exact Hbound|].
  apply Nat.add_le_mono_l; exact Hbody.
Qed.

(** * Source capture shapes *)

(** Discovery associates each map event with the encoder call on the discovered vertex. *)
Lemma audit_tarjan_discover_wellformed {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) v st :
    Forall audit_scc_source_event_wellformed
      (snd (audit_tarjan_nested_discover p (audit_graph_capture_callbacks cb) v st)).
Proof.
  unfold audit_tarjan_nested_discover, audit_tarjan_nested_get, audit_tarjan_nested_set,
    audit_graph_capture_callbacks; cbn.
  destruct (audit_dfs_encode_model cb v) as [code body]; cbn.
  repeat (constructor; cbn [audit_scc_source_event_wellformed]; eauto).
Qed.

(** Lowering associates its lookup and update with the encoder call on that vertex. *)
Lemma audit_tarjan_lower_wellformed {V E B} (cb : audit_dfs_callback_model V E B) v n st :
    Forall audit_scc_source_event_wellformed
      (snd (audit_tarjan_nested_lower (audit_graph_capture_callbacks cb) v n st)).
Proof.
  unfold audit_tarjan_nested_lower, audit_tarjan_nested_get, audit_tarjan_nested_set,
    audit_graph_capture_callbacks; cbn.
  destruct (audit_dfs_encode_model cb v) as [code body]; cbn.
  destruct (Map.code_get code (low st)); cbn.
  all: repeat (constructor; cbn [audit_scc_source_event_wellformed]; eauto).
Qed.

(** Popping associates each removal, insertion, and comparison with its actual encoder operands. *)
Lemma audit_tarjan_pop_wellformed {V E B} (cb : audit_dfs_callback_model V E B) root i xs
    links owners :
    Forall audit_scc_source_event_wellformed
      (snd (audit_tarjan_nested_pop (audit_graph_capture_callbacks cb) root i xs links owners)).
Proof.
  revert links owners; induction xs as [|v rest IH]; intros links owners.
  - cbn [audit_tarjan_nested_pop]; repeat constructor.
  - cbn [audit_tarjan_nested_pop].
    unfold audit_tarjan_nested_remove, audit_tarjan_nested_set, audit_graph_capture_callbacks; cbn.
    destruct (audit_dfs_encode_model cb v) as [vcode vbody].
    destruct (audit_dfs_encode_model cb root) as [rcode rbody]; cbn.
    destruct (Pos.eqb vcode rcode) eqn:Hequal.
    + repeat (constructor; cbn [audit_scc_source_event_wellformed]; eauto).
    + fold (audit_graph_capture_callbacks cb).
      pose proof (IH (CollectionsTrie.Trie.remove vcode links)
        (CollectionsTrie.Trie.set vcode (v, i) owners)) as Hrest.
      destruct (audit_tarjan_nested_pop (audit_graph_capture_callbacks cb) root i rest
        (CollectionsTrie.Trie.remove vcode links)
        (CollectionsTrie.Trie.set vcode (v, i) owners))
        as [[[[members tail] links'] owners'] events]; cbn in Hrest |- *.
      repeat (constructor; cbn [audit_scc_source_event_wellformed]; eauto).
Qed.

(** Emission preserves the capture shapes of its actual pop and empty administrative events. *)
Lemma audit_tarjan_emit_wellformed {V E B} (cb : audit_dfs_callback_model V E B) root st :
    Forall audit_scc_source_event_wellformed
      (snd (audit_tarjan_nested_emit (audit_graph_capture_callbacks cb) root st)).
Proof.
  unfold audit_tarjan_nested_emit.
  destruct (component_ids (emitted st)) as [|previous rest] eqn:Hids;
    pose proof (audit_tarjan_pop_wellformed cb root
      (match component_ids (emitted st) with
       | [] => 1%positive
       | previous :: _ => Pos.succ previous
       end) (pending st) (low st) (comp_of (emitted st))) as Hpop;
    rewrite Hids in Hpop; cbn in Hpop |- *;
    destruct (audit_tarjan_nested_pop (audit_graph_capture_callbacks cb) root _ _ _ _)
      as [[[[members tail] links] owners] events]; cbn in Hpop |- *.
  - constructor; [reflexivity|]. apply Forall_app; split; [exact Hpop|repeat constructor].
  - constructor; [reflexivity|]. constructor; [reflexivity|].
    apply Forall_app; split; [exact Hpop|repeat constructor].
Qed.

(** Closing associates both lookups and its chosen helper with their actual captures. *)
Lemma audit_tarjan_close_wellformed {V E B} (cb : audit_dfs_callback_model V E B) v rest st :
    Forall audit_scc_source_event_wellformed
      (snd (audit_tarjan_nested_close (audit_graph_capture_callbacks cb) v rest st)).
Proof.
  unfold audit_tarjan_nested_close, audit_tarjan_nested_get, audit_graph_capture_callbacks; cbn.
  destruct (audit_dfs_encode_model cb v) as [code body]; cbn.
  destruct (Map.code_get code (low st)) as [lo|] eqn:Hlow; cbn.
  2: { repeat (constructor; cbn [audit_scc_source_event_wellformed]; eauto). }
  destruct (Map.code_get code (disc st)) as [di|] eqn:Hdisc; cbn.
  2: { repeat (constructor; cbn [audit_scc_source_event_wellformed]; eauto). }
  fold (audit_graph_capture_callbacks cb).
  destruct (Pos.eqb lo di) eqn:Hequal.
  - pose proof (audit_tarjan_emit_wellformed cb v
      (TarjanState rest (disc st) (low st) (pending st) (clock st) (emitted st))) as Hemit.
    destruct (audit_tarjan_nested_emit (audit_graph_capture_callbacks cb) v
      (TarjanState rest (disc st) (low st) (pending st) (clock st) (emitted st)))
      as [next events]; cbn in Hemit |- *.
    repeat (constructor; cbn [audit_scc_source_event_wellformed]; eauto).
  - destruct rest as [|parent rest].
    + repeat (constructor; cbn [audit_scc_source_event_wellformed]; eauto).
    + pose proof (audit_tarjan_lower_wellformed cb (frame_node parent) lo
        (TarjanState (parent :: rest) (disc st) (low st) (pending st) (clock st) (emitted st)))
        as Hlower.
      destruct (audit_tarjan_nested_lower (audit_graph_capture_callbacks cb) (frame_node parent) lo
        (TarjanState (parent :: rest) (disc st) (low st) (pending st) (clock st) (emitted st)))
        as [next events]; cbn in Hlower |- *.
      repeat (constructor; cbn [audit_scc_source_event_wellformed]; eauto).
Qed.

(** Every nested source step records the target and key captures required by its events. *)
Lemma audit_tarjan_step_wellformed {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) region st :
    Forall audit_scc_source_event_wellformed
      (snd (audit_tarjan_nested_step p (audit_graph_capture_callbacks cb) region st)).
Proof.
  unfold audit_tarjan_nested_step.
  destruct (frames st) as [|[v edges] rest] eqn:Hframes; [repeat constructor|].
  destruct edges as [|edge edges].
  - pose proof (audit_tarjan_close_wellformed cb v rest st) as Hclose.
    destruct (audit_tarjan_nested_close (audit_graph_capture_callbacks cb) v rest st)
      as [next events]; cbn in Hclose |- *.
    constructor; [reflexivity|]. apply Forall_app; split; [exact Hclose|repeat constructor].
  - unfold audit_graph_capture_callbacks; cbn.
    destruct (audit_dfs_target_model cb edge) as [target target_body]; cbn.
    unfold audit_tarjan_nested_get; cbn.
    destruct (audit_dfs_encode_model cb target) as [code body]; cbn.
    destruct (Map.code_get code region) as [member|] eqn:Hmember; cbn.
    2: { repeat (constructor; cbn [audit_scc_source_event_wellformed]; eauto). }
    destruct (Map.code_get code (disc st)) as [d|] eqn:Hdisc; cbn.
    + destruct (Map.code_get code (low st)) as [onstack|] eqn:Hlow; cbn.
      2: { repeat (constructor; cbn [audit_scc_source_event_wellformed]; eauto). }
      fold (audit_graph_capture_callbacks cb).
      pose proof (audit_tarjan_lower_wellformed cb v d
        (TarjanState (TarjanFrame v edges :: rest) (disc st) (low st)
          (pending st) (clock st) (emitted st))) as Hlower.
      destruct (audit_tarjan_nested_lower (audit_graph_capture_callbacks cb) v d
        (TarjanState (TarjanFrame v edges :: rest) (disc st) (low st)
          (pending st) (clock st) (emitted st))) as [next details]; cbn in Hlower |- *.
      repeat (constructor; cbn [audit_scc_source_event_wellformed]; eauto).
      apply Forall_app; split; [exact Hlower|repeat constructor].
    + fold (audit_graph_capture_callbacks cb).
      pose proof (audit_tarjan_discover_wellformed p cb target
        (TarjanState (TarjanFrame v edges :: rest) (disc st) (low st)
          (pending st) (clock st) (emitted st))) as Hdiscover.
      destruct (audit_tarjan_nested_discover p (audit_graph_capture_callbacks cb) target
        (TarjanState (TarjanFrame v edges :: rest) (disc st) (low st)
          (pending st) (clock st) (emitted st))) as [next details]; cbn in Hdiscover |- *.
      repeat (constructor; cbn [audit_scc_source_event_wellformed]; eauto).
      apply Forall_app; split; [exact Hdiscover|repeat constructor].
Qed.

(** Both halves of a nested run preserve event-specific capture shapes. *)
Lemma audit_tarjan_run_wellformed {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) region fuel st :
    Forall audit_scc_source_event_wellformed
      (snd (audit_tarjan_nested_run p (audit_graph_capture_callbacks cb) region fuel st)).
Proof.
  apply audit_tarjan_nested_run_events.
  - apply audit_tarjan_step_wellformed.
  - intros site; reflexivity.
Qed.

(** A source root records the lookup and the captures of discovery and its run. *)
Lemma audit_tarjan_root_wellformed {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) region st v :
    Forall audit_scc_source_event_wellformed
      (snd (audit_tarjan_nested_root p (audit_graph_capture_callbacks cb) region st v)).
Proof.
  unfold audit_tarjan_nested_root, audit_tarjan_nested_get, audit_graph_capture_callbacks; cbn.
  destruct (audit_dfs_encode_model cb v) as [code body]; cbn.
  destruct (Map.code_get code (disc st)) as [number|] eqn:Hfound; cbn.
  - repeat (constructor; cbn [audit_scc_source_event_wellformed]; eauto).
  - fold (audit_graph_capture_callbacks cb).
    pose proof (audit_tarjan_discover_wellformed p cb v st) as Hdiscover.
    destruct (audit_tarjan_nested_discover p (audit_graph_capture_callbacks cb) v st)
      as [next details]; cbn in Hdiscover |- *.
    pose proof (audit_tarjan_run_wellformed p cb region (fuel p) next) as Hrun.
    destruct (audit_tarjan_nested_run p (audit_graph_capture_callbacks cb) region (fuel p) next)
      as [result events]; cbn in Hrun |- *.
    constructor; [cbn; eauto|]. constructor; [reflexivity|].
    apply Forall_app; split; [exact Hdiscover|]. constructor; [reflexivity|exact Hrun].
Qed.

(** Root traversal preserves capture shapes across every returned intermediate state. *)
Lemma audit_tarjan_roots_wellformed {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) region roots st :
    Forall audit_scc_source_event_wellformed
      (snd (audit_tarjan_nested_roots p (audit_graph_capture_callbacks cb) region roots st)).
Proof.
  revert st; induction roots as [|root rest IH]; intro st; cbn [audit_tarjan_nested_roots].
  - repeat constructor.
  - pose proof (audit_tarjan_root_wellformed p cb region st root) as Hroot.
    destruct (audit_tarjan_nested_root p (audit_graph_capture_callbacks cb) region st root)
      as [next here]; cbn in Hroot |- *.
    pose proof (IH next) as Hrest.
    destruct (audit_tarjan_nested_roots p (audit_graph_capture_callbacks cb) region rest next)
      as [result later]; cbn in Hrest |- *.
    constructor; [reflexivity|]. apply Forall_app; split; assumption.
Qed.

(** Every region-set event carries the encoder capture for its inserted vertex. *)
Lemma audit_tarjan_region_wellformed {V E B} (cb : audit_dfs_callback_model V E B) region set :
    Forall audit_scc_source_event_wellformed
      (snd (audit_tarjan_nested_region (audit_graph_capture_callbacks cb) region set)).
Proof.
  revert set; induction region as [|v rest IH]; intro set; cbn [audit_tarjan_nested_region].
  - repeat constructor.
  - unfold audit_tarjan_nested_set, audit_graph_capture_callbacks; cbn.
    destruct (audit_dfs_encode_model cb v) as [code body]; cbn.
    fold (audit_graph_capture_callbacks cb).
    pose proof (IH (CollectionsTrie.Trie.set code (v, tt) set)) as Hrest.
    destruct (audit_tarjan_nested_region (audit_graph_capture_callbacks cb) rest
      (CollectionsTrie.Trie.set code (v, tt) set)) as [result events]; cbn in Hrest |- *.
    constructor; [cbn; eauto|exact Hrest].
Qed.

(** Every source SCC event has the shape required for its captured operands. *)
Lemma audit_scc_source_events_wellformed {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) region :
    Forall audit_scc_source_event_wellformed (snd (audit_scc_source_counted p cb region)).
Proof.
  unfold audit_scc_source_counted.
  pose proof (audit_tarjan_region_wellformed cb region FinSet.empty) as Hsetup.
  destruct (audit_tarjan_nested_region (audit_graph_capture_callbacks cb) region FinSet.empty)
    as [keep setup]; cbn in Hsetup |- *.
  pose proof (audit_tarjan_roots_wellformed p cb keep region tarjan_initial) as Hroots.
  destruct (audit_tarjan_nested_roots p (audit_graph_capture_callbacks cb) keep region
    tarjan_initial)
    as [st events]; cbn in Hroots |- *.
  apply Forall_app; split; [exact Hsetup|].
  apply Forall_app; split; [exact Hroots|repeat constructor].
Qed.

(** * Original-input key envelope *)

(** Each frame's vertex is allowed and its outgoing edges come from the prepared index. *)
Definition audit_tarjan_frame_keys {V E} (vertices : list V) (edges : list E)
    (frame : tarjan_frame V E) : Prop :=
  In (frame_node frame) vertices /\ incl (frame_edges frame) edges.

(** Open frames and pending vertices use keys from the original-input envelope. *)
Definition audit_tarjan_state_keys {V E} (vertices : list V) (edges : list E)
    (st : tarjan_state V E) : Prop :=
  Forall (audit_tarjan_frame_keys vertices edges) (frames st) /\
  Forall (fun v => In v vertices) (pending st).

(** A helper event's encoded operands are vertices in the original-input envelope. *)
Definition audit_tarjan_helper_keys {V E} (vertices : list V) (event : audit_thelper_event V E) :
    Prop :=
  match event with
  | THGet v _ _
  | THGetEdges v _ _
  | THSet v _ _
  | THRemove v _ => In v vertices
  | THCompare v root _ => In v vertices /\ In root vertices
  | _ => True
  end.

(** A traversal event's encoded operands are vertices in the original-input envelope. *)
Definition audit_tarjan_event_keys {V E} (vertices : list V) (event : audit_tarjan_call V E) :
    Prop :=
  match event with
  | AuditTarjanMember v _ _
  | AuditTarjanGet v _ _
  | AuditTarjanSet v _ => In v vertices
  | AuditTarjanHelper helper => audit_tarjan_helper_keys vertices helper
  | _ => True
  end.

(** A counted pop preserves permitted keys in both returned lists and its helper events. *)
Lemma audit_tarjan_pop_keys {V E} (EV : encoding V) vertices root i xs links owners :
    In root vertices -> Forall (fun v => In v vertices) xs ->
    let '(answer, events) := @audit_tarjan_pop_counted V E EV root i xs links owners in
    let '(members, tail, _, _) := answer in
    Forall (fun v => In v vertices) members /\ Forall (fun v => In v vertices) tail /\
    Forall (audit_tarjan_helper_keys vertices) events.
Proof.
  intros Hroot Hxs; revert links owners; induction Hxs as [|v rest Hv Hrest IH];
    intros links owners; cbn [audit_tarjan_pop_counted].
  - repeat constructor.
  - destruct (Pos.eqb (encode EV v) (encode EV root)) eqn:Hequal; cbn.
    + repeat (constructor; cbn [audit_tarjan_helper_keys]; auto).
    + pose proof (IH (Map.remove EV v links) (Map.set EV v i owners)) as Hpop.
      destruct (audit_tarjan_pop_counted EV root i rest (Map.remove EV v links)
        (Map.set EV v i owners)) as [[[[members tail] links'] owners'] events].
      cbn in Hpop |- *; destruct Hpop as [Hmembers [Htail Hevents]].
      split; [constructor; assumption|]. split; [exact Htail|].
      repeat (constructor; cbn [audit_tarjan_helper_keys]; auto).
Qed.

(** Counted discovery retains the input envelope for its pushed frame and helper keys. *)
Lemma audit_tarjan_discover_keys {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) vertices v st :
    In v vertices ->
    audit_tarjan_state_keys vertices (flat_map snd (Map.elements (out_index p))) st ->
    let '(next, events) := audit_tarjan_discover_counted p v st in
    audit_tarjan_state_keys vertices (flat_map snd (Map.elements (out_index p))) next /\
    Forall (audit_tarjan_helper_keys vertices) events.
Proof.
  intros Hv [Hframes Hpending]; unfold audit_tarjan_discover_counted.
  destruct (Map.get EV v (out_index p)) as [outgoing|] eqn:Hout; cbn.
  - split.
    + unfold audit_tarjan_state_keys; cbn; split.
      * constructor; [|exact Hframes]. unfold audit_tarjan_frame_keys; cbn; split; [exact Hv|].
        now apply (audit_dfs_outgoing_edges p v outgoing Hout).
      * constructor; assumption.
    + repeat (constructor; cbn [audit_tarjan_helper_keys]; auto).
  - split.
    + unfold audit_tarjan_state_keys; cbn; split.
      * constructor; [|exact Hframes]. unfold audit_tarjan_frame_keys; cbn; split; [exact Hv|].
        intros edge Hfalse; contradiction.
      * constructor; assumption.
    + repeat (constructor; cbn [audit_tarjan_helper_keys]; auto).
Qed.

(** Lowering preserves frames and pending keys while recording only its supplied vertex. *)
Lemma audit_tarjan_lower_keys {V E} (EV : encoding V) vertices edges v n (st : tarjan_state V E) :
    In v vertices -> audit_tarjan_state_keys vertices edges st ->
    let '(next, events) := audit_tarjan_lower_counted EV v n st in
    audit_tarjan_state_keys vertices edges next /\ Forall (audit_tarjan_helper_keys vertices)
      events.
Proof.
  intros Hv Hstate; unfold audit_tarjan_lower_counted.
  destruct (Map.get EV v (low st)); cbn.
  - split; [exact Hstate|]. repeat (constructor; cbn [audit_tarjan_helper_keys]; auto).
  - split; [exact Hstate|]. repeat (constructor; cbn [audit_tarjan_helper_keys]; auto).
Qed.

(** Emission preserves permitted pending keys and records helper keys drawn from them. *)
Lemma audit_tarjan_emit_keys {V E} (EV : encoding V) vertices edges root (st : tarjan_state V E) :
    In root vertices -> audit_tarjan_state_keys vertices edges st ->
    let '(next, events) := audit_tarjan_emit_counted EV root st in
    audit_tarjan_state_keys vertices edges next /\ Forall (audit_tarjan_helper_keys vertices)
      events.
Proof.
  intros Hroot [Hframes Hpending]; unfold audit_tarjan_emit_counted.
  destruct (component_ids (emitted st)) as [|previous rest] eqn:Hids;
    pose proof (@audit_tarjan_pop_keys V E EV vertices root
      (match component_ids (emitted st) with
       | [] => 1%positive
       | previous :: _ => Pos.succ previous
       end) (pending st) (low st) (comp_of (emitted st)) Hroot Hpending) as Hpop;
    rewrite Hids in Hpop; cbn in Hpop |- *;
    destruct (audit_tarjan_pop_counted EV root _ _ _ _) as [[[[members tail] links] owners] events];
    cbn in Hpop |- *; destruct Hpop as [Hmembers [Htail Hevents]]; split.
  - split; assumption.
  - constructor; [exact I|]. apply Forall_app; split; [exact Hevents|repeat constructor].
  - split; assumption.
  - constructor; [exact I|]. constructor; [exact I|].
    apply Forall_app; split; [exact Hevents|repeat constructor].
Qed.

(** Closing a frame keeps the remaining permitted frames and records only permitted keys. *)
Lemma audit_tarjan_close_keys {V E} (EV : encoding V) vertices edges v rest
    (st : tarjan_state V E) :
    In v vertices -> Forall (audit_tarjan_frame_keys vertices edges) rest ->
    Forall (fun x => In x vertices) (pending st) ->
    let '(next, events) := audit_tarjan_close_counted EV v rest st in
    audit_tarjan_state_keys vertices edges next /\ Forall (audit_tarjan_helper_keys vertices)
      events.
Proof.
  intros Hv Hframes Hpending.
  set (closed := TarjanState rest (disc st) (low st) (pending st) (clock st) (emitted st)).
  assert (Hclosed : audit_tarjan_state_keys vertices edges closed) by (split; assumption).
  unfold audit_tarjan_close_counted; fold closed.
  destruct (Map.get EV v (low st)) as [lo|] eqn:Hlow; cbn.
  2: { split; [exact Hclosed|]. repeat (constructor; cbn [audit_tarjan_helper_keys]; auto). }
  destruct (Map.get EV v (disc st)) as [di|] eqn:Hdisc; cbn.
  2: { split; [exact Hclosed|]. repeat (constructor; cbn [audit_tarjan_helper_keys]; auto). }
  destruct (Pos.eqb lo di) eqn:Hequal.
  - pose proof (audit_tarjan_emit_keys EV vertices edges v closed Hv Hclosed) as Hemit.
    destruct (audit_tarjan_emit_counted EV v closed) as [next events]; cbn in Hemit |- *.
    destruct Hemit as [Hnext Hevents]; split; [exact Hnext|].
    repeat (constructor; cbn [audit_tarjan_helper_keys]; auto).
  - destruct rest as [|parent rest].
    + split; [exact Hclosed|]. repeat (constructor; cbn [audit_tarjan_helper_keys]; auto).
    + inversion Hframes as [|? ? Hparent Hrest]; subst.
      destruct Hparent as [Hparent _].
      pose proof (audit_tarjan_lower_keys EV vertices edges (frame_node parent) lo closed Hparent
        Hclosed) as Hlower.
      destruct (audit_tarjan_lower_counted EV (frame_node parent) lo closed) as [next events].
      cbn in Hlower |- *; destruct Hlower as [Hnext Hevents]; split; [exact Hnext|].
      repeat (constructor; cbn [audit_tarjan_helper_keys]; auto).
Qed.

(** Wrapping helper events preserves their original-input key property. *)
Lemma audit_tarjan_helper_events_keys {V E} vertices (events : list (audit_thelper_event V E)) :
    Forall (audit_tarjan_helper_keys vertices) events ->
    Forall (audit_tarjan_event_keys vertices) (map AuditTarjanHelper events).
Proof.
  induction 1 as [|event events Hkey Htail IH]; cbn; constructor; auto.
Qed.

(** One counted step preserves the input key envelope for its state and emitted events. *)
Lemma audit_tarjan_step_keys {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) region vertices st :
    (forall edge, In edge (flat_map snd (Map.elements (out_index p))) ->
      In (Graph.target g edge) vertices) ->
    audit_tarjan_state_keys vertices (flat_map snd (Map.elements (out_index p))) st ->
    let '(next, events) := audit_tarjan_step_counted p region st in
    audit_tarjan_state_keys vertices (flat_map snd (Map.elements (out_index p))) next /\
    Forall (audit_tarjan_event_keys vertices) events.
Proof.
  intros Hall [Hframes Hpending]; unfold audit_tarjan_step_counted.
  destruct (frames st) as [|[v outgoing] rest] eqn:Hframes_eq.
  - split; [split; [rewrite Hframes_eq; constructor|exact Hpending]|repeat constructor].
  - inversion Hframes as [|frame tail Hframe Hrest]; subst.
    cbn [audit_tarjan_frame_keys frame_node frame_edges] in Hframe.
    destruct Hframe as [Hv Hedges]; destruct outgoing as [|edge outgoing].
    + pose proof (audit_tarjan_close_keys EV vertices (flat_map snd (Map.elements (out_index p)))
        v rest st Hv Hrest Hpending) as Hclose.
      destruct (audit_tarjan_close_counted EV v rest st) as [next details]; cbn in Hclose |- *.
      destruct Hclose as [Hnext Hdetail]; split; [exact Hnext|].
      constructor; [exact I|]. apply Forall_app; split.
      * now apply audit_tarjan_helper_events_keys.
      * repeat constructor.
    + assert (Htarget : In (Graph.target g edge) vertices).
      { apply Hall, Hedges; left; reflexivity. }
      assert (Htail : incl outgoing (flat_map snd (Map.elements (out_index p)))).
      { intros e Hin; apply Hedges; right; exact Hin. }
      set (advanced := TarjanState (TarjanFrame v outgoing :: rest) (disc st) (low st)
        (pending st) (clock st) (emitted st)).
      assert (Hadvanced : audit_tarjan_state_keys vertices
        (flat_map snd (Map.elements (out_index p))) advanced).
      { split; [|exact Hpending]. constructor; [|exact Hrest]. split; assumption. }
      fold advanced.
      destruct (FinSet.mem EV (Graph.target g edge) region) eqn:Hinside; [|].
      2: { split; [exact Hadvanced|]. repeat (constructor; cbn [audit_tarjan_event_keys]; auto). }
      destruct (Map.get EV (Graph.target g edge) (disc st)) as [d|] eqn:Hdisc.
      * destruct (Map.get EV (Graph.target g edge) (low st)) as [onstack|] eqn:Hlow.
        2: { split; [exact Hadvanced|]. repeat (constructor; cbn [audit_tarjan_event_keys]; auto). }
        pose proof (audit_tarjan_lower_keys EV vertices (flat_map snd (Map.elements (out_index p)))
          v d advanced Hv Hadvanced) as Hlower.
        destruct (audit_tarjan_lower_counted EV v d advanced) as [next details].
        cbn in Hlower |- *; destruct Hlower as [Hnext Hdetail]; split; [exact Hnext|].
        repeat (constructor; cbn [audit_tarjan_event_keys]; auto).
        apply Forall_app; split; [now apply audit_tarjan_helper_events_keys|repeat constructor].
      * pose proof (audit_tarjan_discover_keys p vertices (Graph.target g edge) advanced
          Htarget Hadvanced) as Hdiscover.
        destruct (audit_tarjan_discover_counted p (Graph.target g edge) advanced) as [next details].
        cbn in Hdiscover |- *; destruct Hdiscover as [Hnext Hdetail]; split; [exact Hnext|].
        repeat (constructor; cbn [audit_tarjan_event_keys]; auto).
        apply Forall_app; split; [now apply audit_tarjan_helper_events_keys|repeat constructor].
Qed.

(** Binary counted fuel preserves any step invariant and its associated event property. *)
Lemma audit_tarjan_counted_run_invariant {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) region (P : tarjan_state V E -> Prop) (Q : audit_tarjan_call V E -> Prop)
    fuel st :
    (forall state, P state -> let '(next, events) := audit_tarjan_step_counted p region state in
      P next /\ Forall Q events) ->
    (forall site, Q (AuditTarjanCase site)) -> P st ->
    let '(next, events) := audit_tarjan_run_counted p region fuel st in P next /\ Forall Q events.
Proof.
  intros Hstep Hcase; revert st; induction fuel as [fuel IH|fuel IH|];
    intros [frames disc low stack clock emitted] Hstate; destruct frames as [|frame rest];
    try (split; [exact Hstate|constructor; [apply Hcase|constructor]]).
  - change (let '(next, events) :=
      let '(middle, first) := audit_tarjan_run_counted p region fuel
        (TarjanState (frame :: rest) disc low stack clock emitted) in
      let '(last, second) := audit_tarjan_run_counted p region fuel middle in
      let '(result, steps) := audit_tarjan_step_counted p region last in
      (result, AuditTarjanCase 9 :: first ++ second ++ steps) in P next /\ Forall Q events).
    pose proof (IH (TarjanState (frame :: rest) disc low stack clock emitted) Hstate) as Hfirst.
    destruct (audit_tarjan_run_counted p region fuel
      (TarjanState (frame :: rest) disc low stack clock emitted)) as [middle first].
    cbn in Hfirst |- *; destruct Hfirst as [Hmiddle Hfirst].
    pose proof (IH middle Hmiddle) as Hsecond.
    destruct (audit_tarjan_run_counted p region fuel middle) as [last second].
    cbn in Hsecond |- *; destruct Hsecond as [Hlast Hsecond].
    pose proof (Hstep last Hlast) as Hfinal.
    destruct (audit_tarjan_step_counted p region last) as [result steps]; cbn in Hfinal |- *.
    destruct Hfinal as [Hresult Hsteps]; split; [exact Hresult|].
    constructor; [apply Hcase|]. apply Forall_app; split; [exact Hfirst|].
    apply Forall_app; split; assumption.
  - change (let '(next, events) :=
      let '(middle, first) := audit_tarjan_run_counted p region fuel
        (TarjanState (frame :: rest) disc low stack clock emitted) in
      let '(result, second) := audit_tarjan_run_counted p region fuel middle in
      (result, AuditTarjanCase 8 :: first ++ second) in P next /\ Forall Q events).
    pose proof (IH (TarjanState (frame :: rest) disc low stack clock emitted) Hstate) as Hfirst.
    destruct (audit_tarjan_run_counted p region fuel
      (TarjanState (frame :: rest) disc low stack clock emitted)) as [middle first].
    cbn in Hfirst |- *; destruct Hfirst as [Hmiddle Hfirst].
    pose proof (IH middle Hmiddle) as Hsecond.
    destruct (audit_tarjan_run_counted p region fuel middle) as [result second].
    cbn in Hsecond |- *; destruct Hsecond as [Hresult Hsecond]; split; [exact Hresult|].
    constructor; [apply Hcase|]. apply Forall_app; split; assumption.
  - change (let '(next, events) :=
      let '(result, steps) := audit_tarjan_step_counted p region
        (TarjanState (frame :: rest) disc low stack clock emitted) in
      (result, AuditTarjanCase 7 :: steps) in P next /\ Forall Q events).
    pose proof (Hstep (TarjanState (frame :: rest) disc low stack clock emitted) Hstate) as Hfinal.
    destruct (audit_tarjan_step_counted p region
      (TarjanState (frame :: rest) disc low stack clock emitted)) as [result steps].
    cbn in Hfinal |- *; destruct Hfinal as [Hresult Hsteps]; split; [exact Hresult|].
    constructor; [apply Hcase|exact Hsteps].
Qed.

(** Binary-fuel traversal preserves the same key envelope through both actual intermediate
  states. *)
Lemma audit_tarjan_run_keys {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) region vertices fuel st :
    (forall edge, In edge (flat_map snd (Map.elements (out_index p))) ->
      In (Graph.target g edge) vertices) ->
    audit_tarjan_state_keys vertices (flat_map snd (Map.elements (out_index p))) st ->
    let '(next, events) := audit_tarjan_run_counted p region fuel st in
    audit_tarjan_state_keys vertices (flat_map snd (Map.elements (out_index p))) next /\
    Forall (audit_tarjan_event_keys vertices) events.
Proof.
  intros Hall Hstate; eapply audit_tarjan_counted_run_invariant.
  - intros state Hkeys; now apply audit_tarjan_step_keys.
  - intro site; exact I.
  - exact Hstate.
Qed.

(** A counted root preserves the envelope when the root belongs to it. *)
Lemma audit_tarjan_root_keys {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) region vertices st v :
    (forall edge, In edge (flat_map snd (Map.elements (out_index p))) ->
      In (Graph.target g edge) vertices) ->
    In v vertices -> audit_tarjan_state_keys vertices (flat_map snd (Map.elements (out_index p)))
      st ->
    let '(next, events) := audit_tarjan_root_counted p region st v in
    audit_tarjan_state_keys vertices (flat_map snd (Map.elements (out_index p))) next /\
    Forall (audit_tarjan_event_keys vertices) events.
Proof.
  intros Hall Hv Hstate; unfold audit_tarjan_root_counted.
  destruct (Map.get EV v (disc st)) as [number|] eqn:Hfound.
  - cbn; split; [exact Hstate|]. repeat (constructor; cbn [audit_tarjan_event_keys]; auto).
  - change (let '(result, events) :=
      let '(next, details) := audit_tarjan_discover_counted p v st in
      let '(result, events) := audit_tarjan_run_counted p region (fuel p) next in
      (result, [AuditTarjanGet v (disc st) None; AuditTarjanCase 11] ++
        map AuditTarjanHelper details ++ [AuditTarjanDiscover v st next] ++ events) in
      audit_tarjan_state_keys vertices (flat_map snd (Map.elements (out_index p))) result /\
      Forall (audit_tarjan_event_keys vertices) events).

    pose proof (audit_tarjan_discover_keys p vertices v st Hv Hstate) as Hdiscover.
    destruct (audit_tarjan_discover_counted p v st) as [next details]; cbn in Hdiscover |- *.
    destruct Hdiscover as [Hnext Hdetail].
    pose proof (audit_tarjan_run_keys p region vertices (fuel p) next Hall Hnext) as Hrun.
    destruct (audit_tarjan_run_counted p region (fuel p) next) as [result events]; cbn in Hrun |- *.
    destruct Hrun as [Hresult Hevents]; split; [exact Hresult|].
    constructor; [exact Hv|]. constructor; [exact I|].
    apply Forall_app; split; [now apply audit_tarjan_helper_events_keys|].
    constructor; [exact I|exact Hevents].
Qed.

(** A list of roots drawn from the envelope preserves it for all states and events. *)
Lemma audit_tarjan_roots_keys {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) region vertices roots st :
    (forall edge, In edge (flat_map snd (Map.elements (out_index p))) ->
      In (Graph.target g edge) vertices) ->
    incl roots vertices ->
    audit_tarjan_state_keys vertices (flat_map snd (Map.elements (out_index p))) st ->
    let '(next, events) := audit_tarjan_roots_counted p region roots st in
    audit_tarjan_state_keys vertices (flat_map snd (Map.elements (out_index p))) next /\
    Forall (audit_tarjan_event_keys vertices) events.
Proof.
  intros Hall Hroots; revert st; induction roots as [|root rest IH]; intros st Hstate;
    cbn [audit_tarjan_roots_counted].
  - split; [exact Hstate|repeat constructor].
  - pose proof (audit_tarjan_root_keys p region vertices st root Hall (Hroots root (or_introl
    eq_refl))
      Hstate) as Hroot.
    destruct (audit_tarjan_root_counted p region st root) as [next here]; cbn in Hroot |- *.
    destruct Hroot as [Hnext Hhere].
    assert (Hrest : incl rest vertices) by (intros v Hin; apply Hroots; right; exact Hin).
    pose proof (IH Hrest next Hnext) as Hlater.
    destruct (audit_tarjan_roots_counted p region rest next) as [result later]; cbn in Hlater |- *.
    destruct Hlater as [Hresult Hevents]; split; [exact Hresult|].
    constructor; [exact I|]. apply Forall_app; split; assumption.
Qed.

(** Region-set events use only the vertices listed in the region. *)
Lemma audit_tarjan_region_keys {V E} (EV : encoding V) vertices region set :
    incl region vertices ->
    Forall (audit_tarjan_event_keys vertices) (snd (@audit_tarjan_region_counted V E EV region
      set)).
Proof.
  intro Hregion; revert set; induction region as [|v rest IH]; intro set;
    cbn [audit_tarjan_region_counted].
  - repeat constructor.
  - pose proof (IH (fun x Hx => Hregion x (or_intror Hx)) (FinSet.add EV v set)) as Hrest.
    destruct (audit_tarjan_region_counted EV rest (FinSet.add EV v set)) as [result events].
    cbn in Hrest |- *; constructor; [apply Hregion; left; reflexivity|exact Hrest].
Qed.

(** Counted SCC event keys come from region roots or targets of the actual prepared index. *)
Lemma audit_scc_counted_keys {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) region :
    let vertices := region ++ map (Graph.target g) (flat_map snd (Map.elements (out_index p))) in
    Forall (audit_tarjan_event_keys vertices) (snd (audit_scc_within_counted p region)).
Proof.
  intros vertices; unfold audit_scc_within_counted.
  assert (Hall : forall edge, In edge (flat_map snd (Map.elements (out_index p))) ->
    In (Graph.target g edge) vertices).
  { intros edge Hin; subst vertices; apply in_or_app; right; now apply in_map. }
  assert (Hregion : incl region vertices).
  { intros v Hin; subst vertices; apply in_or_app; left; exact Hin. }
  pose proof (@audit_tarjan_region_keys V E EV vertices region FinSet.empty Hregion) as Hsetup.
  destruct (audit_tarjan_region_counted EV region FinSet.empty) as [keep setup]; cbn in Hsetup |- *.
  assert (Hinitial : audit_tarjan_state_keys vertices (flat_map snd (Map.elements (out_index p)))
    tarjan_initial) by (split; constructor).
  pose proof (audit_tarjan_roots_keys p keep vertices region tarjan_initial Hall Hregion Hinitial)
    as Hroots.
  destruct (audit_tarjan_roots_counted p keep region tarjan_initial) as [st events];
    cbn in Hroots |- *; destruct Hroots as [_ Hevents].
  apply Forall_app; split; [exact Hsetup|]. apply Forall_app; split; [exact Hevents|repeat
    constructor].
Qed.

(** * Numeric envelopes *)

(** Every successful lookup in a positive-valued map is bounded by the same ceiling. *)
Definition audit_tarjan_map_numbers {V} (EV : encoding V) (ceiling : nat)
    (m : Map.t V positive) : Prop :=
  forall v n, Map.get EV v m = Some n -> Pos.to_nat n <= ceiling.

(** A bounded insertion preserves the map's lookup-value ceiling. *)
Lemma audit_tarjan_map_numbers_set {V} (EV : encoding V) ceiling key value m :
    Pos.to_nat value <= ceiling -> audit_tarjan_map_numbers EV ceiling m ->
    audit_tarjan_map_numbers EV ceiling (Map.set EV key value m).
Proof.
  intros Hvalue Hmap v n Hget.
  destruct (Pos.eq_dec (encode EV v) (encode EV key)) as [Hequal|Hdistinct].
  - apply (encode_injective EV) in Hequal; subst v.
    rewrite Map.get_set_same in Hget; inversion Hget; subst n; exact Hvalue.
  - assert (Hne : v <> key) by (intro Heq; subst v; contradiction).
    rewrite Map.get_set_other in Hget by exact Hne; now apply (Hmap v n).
Qed.

(** Removal cannot introduce an out-of-range value into a positive-valued map. *)
Lemma audit_tarjan_map_numbers_remove {V} (EV : encoding V) ceiling key m :
    audit_tarjan_map_numbers EV ceiling m ->
    audit_tarjan_map_numbers EV ceiling (Map.remove EV key m).
Proof.
  intros Hmap v n Hget.
  destruct (Pos.eq_dec (encode EV v) (encode EV key)) as [Hequal|Hdistinct].
  - apply (encode_injective EV) in Hequal; subst v.
    rewrite Map.get_remove_same in Hget; discriminate.
  - assert (Hne : v <> key) by (intro Heq; subst v; contradiction).
    rewrite Map.get_remove_other in Hget by exact Hne; now apply (Hmap v n).
Qed.

(** The clock, successful lowlink and discovery lookups, and component IDs fit a ceiling. *)
Definition audit_tarjan_state_numbers {V E} (EV : encoding V) (ceiling : nat)
    (st : tarjan_state V E) : Prop :=
  Pos.to_nat (clock st) <= ceiling /\ audit_tarjan_map_numbers EV ceiling (disc st) /\
  audit_tarjan_map_numbers EV ceiling (low st) /\
  Forall (fun i => Pos.to_nat i <= ceiling) (component_ids (emitted st)).

(** Numeric bounds remain valid when the ceiling increases. *)
Lemma audit_tarjan_state_numbers_mono {V E} (EV : encoding V) small large (st : tarjan_state V E) :
    small <= large -> audit_tarjan_state_numbers EV small st ->
    audit_tarjan_state_numbers EV large st.
Proof.
  intros Hle [Hclock [Hdisc [Hlow Hids]]].
  split; [lia|]. split.
  - intros v n Hget; specialize (Hdisc v n Hget); lia.
  - split.
    + intros v n Hget; specialize (Hlow v n Hget); lia.
    + induction Hids as [|id ids Hbound Htail IH]; constructor; [lia|exact IH].
Qed.

(** Every positive operand in a helper event is at most the selected numeric ceiling. *)
Definition audit_tarjan_helper_numbers {V E} (ceiling : nat) (event : audit_thelper_event V E) :
    Prop :=
  match event with
  | THGet _ _ (Some n)
  | THSet _ n _
  | THTrieSet n _ _ => Pos.to_nat n <= ceiling
  | THPosCompare a b _
  | THMin a b _
  | THSucc a b =>
    Pos.to_nat a <= ceiling /\ Pos.to_nat b <= ceiling
  | _ => True
  end.

(** Each traversal helper event keeps its recorded numeric operands within the ceiling. *)
Definition audit_tarjan_event_numbers {V E} (ceiling : nat) (event : audit_tarjan_call V E) :
    Prop :=
  match event with
  | AuditTarjanHelper helper => audit_tarjan_helper_numbers ceiling helper
  | _ => True
  end.

(** Popping removes lowlinks without increasing their values and records only its bounded ID. *)
Lemma audit_tarjan_pop_numbers {V E} (EV : encoding V) ceiling root i xs links owners :
    Pos.to_nat i <= ceiling -> audit_tarjan_map_numbers EV ceiling links ->
    let '(answer, events) := @audit_tarjan_pop_counted V E EV root i xs links owners in
    let '(_, _, links', _) := answer in
    audit_tarjan_map_numbers EV ceiling links' /\ Forall (audit_tarjan_helper_numbers ceiling)
      events.
Proof.
  intros Hid Hlinks; revert links owners Hlinks; induction xs as [|v rest IH];
    intros links owners Hlinks; cbn [audit_tarjan_pop_counted].
  - split; [exact Hlinks|repeat constructor].
  - pose proof (audit_tarjan_map_numbers_remove EV ceiling v links Hlinks) as Hremoved.
    destruct (Pos.eqb (encode EV v) (encode EV root)) eqn:Hequal; cbn.
    + split; [exact Hremoved|]. repeat (constructor; cbn [audit_tarjan_helper_numbers]; auto).
    + pose proof (IH (Map.remove EV v links) (Map.set EV v i owners) Hremoved) as Hpop.
      destruct (audit_tarjan_pop_counted EV root i rest (Map.remove EV v links)
        (Map.set EV v i owners)) as [[[[members tail] links'] owners'] events].
      cbn in Hpop |- *; destruct Hpop as [Hlinks' Hevents].
      split; [exact Hlinks'|]. repeat (constructor; cbn [audit_tarjan_helper_numbers]; auto).
Qed.

(** Increasing the numeric ceiling preserves every map lookup bound. *)
Lemma audit_tarjan_map_numbers_mono {V} (EV : encoding V) small large m :
    small <= large -> audit_tarjan_map_numbers EV small m -> audit_tarjan_map_numbers EV large m.
Proof.
  intros Hle Hmap v n Hget; specialize (Hmap v n Hget); lia.
Qed.

(** Discovery advances its clock once and keeps all recorded numbers within the new ceiling. *)
Lemma audit_tarjan_discover_numbers {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) ceiling v st :
    audit_tarjan_state_numbers EV ceiling st ->
    let '(next, events) := audit_tarjan_discover_counted p v st in
    audit_tarjan_state_numbers EV (S ceiling) next /\
    Forall (audit_tarjan_helper_numbers (S ceiling)) events.
Proof.
  intros [Hclock [Hdisc [Hlow Hids]]].
  assert (Hdisc' : audit_tarjan_map_numbers EV (S ceiling) (disc st)).
  { eapply (audit_tarjan_map_numbers_mono EV ceiling (S ceiling)); [lia|exact Hdisc]. }
  assert (Hlow' : audit_tarjan_map_numbers EV (S ceiling) (low st)).
  { eapply (audit_tarjan_map_numbers_mono EV ceiling (S ceiling)); [lia|exact Hlow]. }
  assert (Hids' : Forall (fun i => Pos.to_nat i <= S ceiling) (component_ids (emitted st))).
  { induction Hids as [|id ids Hid Hrest IH]; constructor; [lia|exact IH]. }
  assert (Hnew : forall outgoing, audit_tarjan_state_numbers EV (S ceiling)
    (TarjanState (TarjanFrame v outgoing :: frames st)
      (Map.set EV v (clock st) (disc st)) (Map.set EV v (clock st) (low st))
      (v :: pending st) (Pos.succ (clock st)) (emitted st))).
  { intro outgoing; unfold audit_tarjan_state_numbers; cbn.
    split; [rewrite Pos2Nat.inj_succ; lia|].
    split; [apply audit_tarjan_map_numbers_set; [lia|exact Hdisc']|].
    split; [apply audit_tarjan_map_numbers_set; [lia|exact Hlow']|exact Hids']. }
  unfold audit_tarjan_discover_counted; destruct (Map.get EV v (out_index p)); cbn; split;
    [apply Hnew| |apply Hnew|].
  all: constructor; [exact I|]; constructor; [cbn; lia|]; constructor; [cbn; lia|];
    constructor; [cbn; rewrite Pos2Nat.inj_succ; lia|constructor].
Qed.

(** Lowering preserves the ceiling when its new candidate is already bounded. *)
Lemma audit_tarjan_lower_numbers {V E} (EV : encoding V) ceiling v n (st : tarjan_state V E) :
    Pos.to_nat n <= ceiling -> audit_tarjan_state_numbers EV ceiling st ->
    let '(next, events) := audit_tarjan_lower_counted EV v n st in
    audit_tarjan_state_numbers EV ceiling next /\
    Forall (audit_tarjan_helper_numbers ceiling) events.
Proof.
  intros Hn Hstate; destruct Hstate as [Hclock [Hdisc [Hlow Hids]]].
  unfold audit_tarjan_lower_counted.
  destruct (Map.get EV v (low st)) as [old|] eqn:Hget; cbn.
  - assert (Hold : Pos.to_nat old <= ceiling) by (now apply (Hlow v old)).
    assert (Hmin : Pos.to_nat (Pos.min old n) <= ceiling).
    { pose proof (Pos.le_min_l old n) as Hle; apply Pos2Nat.inj_le in Hle; lia. }
    split.
    + split; [exact Hclock|]. split; [exact Hdisc|]. split; [|exact Hids].
      now apply audit_tarjan_map_numbers_set.
    + repeat (constructor; cbn [audit_tarjan_helper_numbers]; auto).
  - split.
    + split; [exact Hclock|]. split; [exact Hdisc|]. split; assumption.
    + repeat (constructor; cbn [audit_tarjan_helper_numbers]; auto).
Qed.

(** The next component identifier is at most one greater than the previous ID ceiling. *)
Lemma audit_tarjan_next_id_bound {V} (r : scc_result V) ceiling :
    Forall (fun i => Pos.to_nat i <= ceiling) (component_ids r) ->
    Pos.to_nat (tarjan_next_id r) <= S ceiling.
Proof.
  intro Hids; unfold tarjan_next_id.
  destruct (component_ids r) as [|previous rest] eqn:Hids_eq; [cbn; lia|].
  inversion Hids as [|? ? Hprevious Hrest]; subst.
  rewrite Pos2Nat.inj_succ; lia.
Qed.

(** Emission increments the component-ID ceiling at most once and preserves bounded lowlinks. *)
Lemma audit_tarjan_emit_numbers {V E} (EV : encoding V) ceiling root (st : tarjan_state V E) :
    audit_tarjan_state_numbers EV ceiling st ->
    let '(next, events) := audit_tarjan_emit_counted EV root st in
    audit_tarjan_state_numbers EV (S ceiling) next /\
    Forall (audit_tarjan_helper_numbers (S ceiling)) events.
Proof.
  intro Hstate.
  pose proof (audit_tarjan_state_numbers_mono EV ceiling (S ceiling) st ltac:(lia) Hstate) as Hwide.
  destruct Hwide as [Hclock [Hdisc [Hlow Hids]]].
  destruct Hstate as [_ [_ [_ Hids_old]]].
  pose proof (audit_tarjan_next_id_bound (emitted st) ceiling Hids_old) as Hid.
  unfold audit_tarjan_emit_counted.
  destruct (component_ids (emitted st)) as [|previous rest] eqn:Hids_eq.
  - unfold tarjan_next_id in Hid; rewrite Hids_eq in Hid.
    pose proof (@audit_tarjan_pop_numbers V E EV (S ceiling) root 1%positive
      (pending st) (low st) (comp_of (emitted st)) Hid Hlow) as Hpop.
    destruct (audit_tarjan_pop_counted EV root 1%positive (pending st) (low st) (comp_of (emitted
      st)))
      as [[[[members tail] links] owners] events]; cbn in Hpop |- *.
    destruct Hpop as [Hlinks Hevents]; split.
    + split; [exact Hclock|]. split; [exact Hdisc|]. split; [exact Hlinks|].
      constructor; [exact Hid|exact Hids].
    + constructor; [exact I|]. apply Forall_app; split; [exact Hevents|].
      constructor; [exact Hid|constructor].
  - unfold tarjan_next_id in Hid; rewrite Hids_eq in Hid.
    inversion Hids_old as [|? ? Hprevious Hrest]; subst.
    pose proof (@audit_tarjan_pop_numbers V E EV (S ceiling) root (Pos.succ previous)
      (pending st) (low st) (comp_of (emitted st)) Hid Hlow) as Hpop.
    destruct (audit_tarjan_pop_counted EV root (Pos.succ previous) (pending st) (low st)
      (comp_of (emitted st))) as [[[[members tail] links] owners] events]; cbn in Hpop |- *.
    destruct Hpop as [Hlinks Hevents]; split.
    + split; [exact Hclock|]. split; [exact Hdisc|]. split; [exact Hlinks|].
      constructor; [exact Hid|exact Hids].
    + constructor; [exact I|]. constructor; [split; [lia|exact Hid]|].
      apply Forall_app; split; [exact Hevents|]. constructor; [exact Hid|constructor].
Qed.

(** Closing a frame preserves bounded numeric state and charges at most one ID increment. *)
Lemma audit_tarjan_close_numbers {V E} (EV : encoding V) ceiling v rest (st : tarjan_state V E) :
    audit_tarjan_state_numbers EV ceiling st ->
    let '(next, events) := audit_tarjan_close_counted EV v rest st in
    audit_tarjan_state_numbers EV (S ceiling) next /\
    Forall (audit_tarjan_helper_numbers (S ceiling)) events.
Proof.
  intro Hstate.
  pose proof (audit_tarjan_state_numbers_mono EV ceiling (S ceiling) st ltac:(lia) Hstate) as Hwide.
  destruct Hstate as [Hclock [Hdisc [Hlow Hids]]].
  set (closed := TarjanState rest (disc st) (low st) (pending st) (clock st) (emitted st)).
  assert (Hclosed : audit_tarjan_state_numbers EV ceiling closed).
  { unfold closed, audit_tarjan_state_numbers; cbn; split; [exact Hclock|].
    split; [exact Hdisc|]. split; assumption. }
  assert (Hclosed_wide : audit_tarjan_state_numbers EV (S ceiling) closed).
  { unfold closed; exact Hwide. }
  unfold audit_tarjan_close_counted; fold closed.
  destruct (Map.get EV v (low st)) as [lo|] eqn:Hlow_get; cbn.
  2: { split; [exact Hclosed_wide|repeat constructor]. }
  assert (Hlo : Pos.to_nat lo <= ceiling) by (now apply (Hlow v lo)).
  destruct (Map.get EV v (disc st)) as [di|] eqn:Hdisc_get; cbn.
  2: { split; [exact Hclosed_wide|].
       repeat (constructor; cbn [audit_tarjan_helper_numbers]; try lia). }
  assert (Hdi : Pos.to_nat di <= ceiling) by (now apply (Hdisc v di)).
  destruct (Pos.eqb lo di) eqn:Hequal.
  - pose proof (audit_tarjan_emit_numbers EV ceiling v closed Hclosed) as Hemit.
    destruct (audit_tarjan_emit_counted EV v closed) as [next events]; cbn in Hemit |- *.
    destruct Hemit as [Hnext Hevents]; split; [exact Hnext|].
    repeat (constructor; cbn [audit_tarjan_helper_numbers]; try lia; try assumption).
  - destruct rest as [|parent rest].
    + split; [exact Hclosed_wide|].
      repeat (constructor; cbn [audit_tarjan_helper_numbers]; try lia).
    + pose proof (audit_tarjan_lower_numbers EV (S ceiling) (frame_node parent) lo closed
        ltac:(lia) Hclosed_wide) as Hlower.
      destruct (audit_tarjan_lower_counted EV (frame_node parent) lo closed) as [next events].
      cbn in Hlower |- *; destruct Hlower as [Hnext Hevents]; split; [exact Hnext|].
      repeat (constructor; cbn [audit_tarjan_helper_numbers]; try lia; try assumption).
Qed.

(** Wrapping helper events preserves their numeric ceiling. *)
Lemma audit_tarjan_helper_events_numbers {V E} ceiling (events : list (audit_thelper_event V E)) :
    Forall (audit_tarjan_helper_numbers ceiling) events ->
    Forall (audit_tarjan_event_numbers ceiling) (map AuditTarjanHelper events).
Proof.
  induction 1 as [|event events Hnumber Htail IH]; cbn; constructor; auto.
Qed.

(** A counted step increases the numeric ceiling by at most one. *)
Lemma audit_tarjan_step_numbers {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) region ceiling st :
    audit_tarjan_state_numbers EV ceiling st ->
    let '(next, events) := audit_tarjan_step_counted p region st in
    audit_tarjan_state_numbers EV (S ceiling) next /\
    Forall (audit_tarjan_event_numbers (S ceiling)) events.
Proof.
  intro Hstate.
  pose proof (audit_tarjan_state_numbers_mono EV ceiling (S ceiling) st ltac:(lia) Hstate) as Hwide.
  destruct Hstate as [Hclock [Hdisc [Hlow Hids]]].
  unfold audit_tarjan_step_counted.
  destruct (frames st) as [|[v outgoing] rest] eqn:Hframes; [split; [exact Hwide|repeat
    constructor]|].
  destruct outgoing as [|edge outgoing].
  - pose proof (audit_tarjan_close_numbers EV ceiling v rest st
      (conj Hclock (conj Hdisc (conj Hlow Hids)))) as Hclose.
    destruct (audit_tarjan_close_counted EV v rest st) as [next details]; cbn in Hclose |- *.
    destruct Hclose as [Hnext Hdetail]; split; [exact Hnext|].
    constructor; [exact I|]. apply Forall_app; split.
    + now apply audit_tarjan_helper_events_numbers.
    + repeat constructor.
  - set (advanced := TarjanState (TarjanFrame v outgoing :: rest) (disc st) (low st)
      (pending st) (clock st) (emitted st)).
    assert (Hadvanced : audit_tarjan_state_numbers EV ceiling advanced).
    { unfold advanced, audit_tarjan_state_numbers; cbn; split; [exact Hclock|].
      split; [exact Hdisc|]. split; assumption. }
    assert (Hadvanced_wide : audit_tarjan_state_numbers EV (S ceiling) advanced).
    { unfold advanced; exact Hwide. }
    fold advanced.
    destruct (FinSet.mem EV (Graph.target g edge) region) eqn:Hinside.
    2: { split; [exact Hadvanced_wide|repeat constructor]. }
    destruct (Map.get EV (Graph.target g edge) (disc st)) as [d|] eqn:Hdisc_get.
    + destruct (Map.get EV (Graph.target g edge) (low st)) as [onstack|] eqn:Hlow_get.
      2: { split; [exact Hadvanced_wide|repeat constructor]. }
      assert (Hd : Pos.to_nat d <= S ceiling) by (specialize (Hdisc _ _ Hdisc_get); lia).
      pose proof (audit_tarjan_lower_numbers EV (S ceiling) v d advanced Hd Hadvanced_wide) as
        Hlower.
      destruct (audit_tarjan_lower_counted EV v d advanced) as [next details]; cbn in Hlower |- *.
      destruct Hlower as [Hnext Hdetail]; split; [exact Hnext|].
      repeat constructor; apply Forall_app; split;
        [now apply audit_tarjan_helper_events_numbers|repeat constructor].
    + pose proof (audit_tarjan_discover_numbers p ceiling (Graph.target g edge) advanced Hadvanced)
        as Hdiscover.
      destruct (audit_tarjan_discover_counted p (Graph.target g edge) advanced) as [next details].
      cbn in Hdiscover |- *; destruct Hdiscover as [Hnext Hdetail]; split; [exact Hnext|].
      repeat constructor; apply Forall_app; split;
        [now apply audit_tarjan_helper_events_numbers|repeat constructor].
Qed.

(** Raising the ceiling preserves a helper event's numeric bounds. *)
Lemma audit_tarjan_helper_numbers_mono {V E} small large (event : audit_thelper_event V E) :
    small <= large -> audit_tarjan_helper_numbers small event ->
    audit_tarjan_helper_numbers large event.
Proof.
  intros Hle Hnumber.
  destruct event as [site|key m [n|]|key m result|key value m|key m|a b result|
    a b result|a b result|a b|key members m];
    cbn [audit_tarjan_helper_numbers] in *; try exact I; try lia;
    destruct Hnumber; split; lia.
Qed.

(** Raising the ceiling preserves every numeric event bound in a trace. *)
Lemma audit_tarjan_events_numbers_mono {V E} small large (events : list (audit_tarjan_call V E)) :
    small <= large -> Forall (audit_tarjan_event_numbers small) events ->
    Forall (audit_tarjan_event_numbers large) events.
Proof.
  intros Hle Hevents; induction Hevents as [|event events Hnumber Htail IH]; constructor; [|exact
    IH].
  destruct event; cbn [audit_tarjan_event_numbers] in *; try exact I.
  eapply audit_tarjan_helper_numbers_mono; eauto.
Qed.

(** Two consecutive fuel runs compose their numeric ceilings and retain both event traces. *)
Lemma audit_tarjan_two_runs_numbers {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) region fuel ceiling st :
    (forall bound state, audit_tarjan_state_numbers EV bound state ->
      let '(next, events) := audit_tarjan_run_counted p region fuel state in
      audit_tarjan_state_numbers EV (bound + Pos.to_nat fuel) next /\
      Forall (audit_tarjan_event_numbers (bound + Pos.to_nat fuel)) events) ->
    audit_tarjan_state_numbers EV ceiling st ->
    let '(middle, first) := audit_tarjan_run_counted p region fuel st in
    let '(last, second) := audit_tarjan_run_counted p region fuel middle in
    audit_tarjan_state_numbers EV (ceiling + Pos.to_nat fuel + Pos.to_nat fuel) last /\
    Forall (audit_tarjan_event_numbers (ceiling + Pos.to_nat fuel + Pos.to_nat fuel))
      (first ++ second).
Proof.
  intros Hrun Hstate.
  pose proof (Hrun ceiling st Hstate) as Hfirst.
  destruct (audit_tarjan_run_counted p region fuel st) as [middle first]; cbn in Hfirst |- *.
  destruct Hfirst as [Hmiddle Hfirst].
  pose proof (Hrun (ceiling + Pos.to_nat fuel) middle Hmiddle) as Hsecond.
  destruct (audit_tarjan_run_counted p region fuel middle) as [last second]; cbn in Hsecond |- *.
  destruct Hsecond as [Hlast Hsecond]; split; [exact Hlast|].
  apply Forall_app; split.
  - eapply (audit_tarjan_events_numbers_mono (ceiling + Pos.to_nat fuel)); [lia|exact Hfirst].
  - exact Hsecond.
Qed.

(** An odd binary run composes two numeric-bounded runs and one step. *)
Lemma audit_tarjan_run_numbers_odd {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) region fuel ceiling (frame : tarjan_frame V E) rest
    (disc low : Map.t V positive) stack clock emitted :
    (forall bound state, audit_tarjan_state_numbers EV bound state ->
      let '(next, events) := audit_tarjan_run_counted p region fuel state in
      audit_tarjan_state_numbers EV (bound + Pos.to_nat fuel) next /\
      Forall (audit_tarjan_event_numbers (bound + Pos.to_nat fuel)) events) ->
    audit_tarjan_state_numbers EV ceiling
      (TarjanState (frame :: rest) disc low stack clock emitted) ->
    let '(next, events) := audit_tarjan_run_counted p region (xI fuel)
      (TarjanState (frame :: rest) disc low stack clock emitted) in
    audit_tarjan_state_numbers EV (ceiling + Pos.to_nat (xI fuel)) next /\
    Forall (audit_tarjan_event_numbers (ceiling + Pos.to_nat (xI fuel))) events.
Proof.
  intros IH Hstate.
  change (let '(next, events) :=
    let '(middle, first) := audit_tarjan_run_counted p region fuel
      (TarjanState (frame :: rest) disc low stack clock emitted) in
    let '(last, second) := audit_tarjan_run_counted p region fuel middle in
    let '(result, steps) := audit_tarjan_step_counted p region last in
    (result, AuditTarjanCase 9 :: first ++ second ++ steps) in
    audit_tarjan_state_numbers EV (ceiling + Pos.to_nat (xI fuel)) next /\
    Forall (audit_tarjan_event_numbers (ceiling + Pos.to_nat (xI fuel))) events).
  pose proof (audit_tarjan_two_runs_numbers p region fuel ceiling
    (TarjanState (frame :: rest) disc low stack clock emitted) IH Hstate) as Hboth.
  destruct (audit_tarjan_run_counted p region fuel
    (TarjanState (frame :: rest) disc low stack clock emitted)) as [middle first].
  destruct (audit_tarjan_run_counted p region fuel middle) as [last second]; cbn in Hboth |- *.
  destruct Hboth as [Hlast Hboth].
  pose proof (audit_tarjan_step_numbers p region (ceiling + Pos.to_nat fuel + Pos.to_nat fuel)
    last Hlast) as Hstep.
  destruct (audit_tarjan_step_counted p region last) as [result steps]; cbn in Hstep |- *.
  destruct Hstep as [Hresult Hsteps]; rewrite Pos2Nat.inj_xI; split.
  - eapply (audit_tarjan_state_numbers_mono EV (S (ceiling + Pos.to_nat fuel + Pos.to_nat fuel)));
      [lia|exact Hresult].
  - constructor; [exact I|]. rewrite app_assoc. apply Forall_app; split.
    + eapply (audit_tarjan_events_numbers_mono (ceiling + Pos.to_nat fuel + Pos.to_nat fuel));
          [lia|exact Hboth].
    + eapply (audit_tarjan_events_numbers_mono (S (ceiling + Pos.to_nat fuel + Pos.to_nat fuel)));
          [lia|exact Hsteps].
Qed.

(** An even binary run composes two numeric-bounded runs. *)
Lemma audit_tarjan_run_numbers_even {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) region fuel ceiling (frame : tarjan_frame V E) rest
    (disc low : Map.t V positive) stack clock emitted :
    (forall bound state, audit_tarjan_state_numbers EV bound state ->
      let '(next, events) := audit_tarjan_run_counted p region fuel state in
      audit_tarjan_state_numbers EV (bound + Pos.to_nat fuel) next /\
      Forall (audit_tarjan_event_numbers (bound + Pos.to_nat fuel)) events) ->
    audit_tarjan_state_numbers EV ceiling
      (TarjanState (frame :: rest) disc low stack clock emitted) ->
    let '(next, events) := audit_tarjan_run_counted p region (xO fuel)
      (TarjanState (frame :: rest) disc low stack clock emitted) in
    audit_tarjan_state_numbers EV (ceiling + Pos.to_nat (xO fuel)) next /\
    Forall (audit_tarjan_event_numbers (ceiling + Pos.to_nat (xO fuel))) events.
Proof.
  intros IH Hstate.
  change (let '(next, events) :=
    let '(middle, first) := audit_tarjan_run_counted p region fuel
      (TarjanState (frame :: rest) disc low stack clock emitted) in
    let '(result, second) := audit_tarjan_run_counted p region fuel middle in
    (result, AuditTarjanCase 8 :: first ++ second) in
    audit_tarjan_state_numbers EV (ceiling + Pos.to_nat (xO fuel)) next /\
    Forall (audit_tarjan_event_numbers (ceiling + Pos.to_nat (xO fuel))) events).
  pose proof (audit_tarjan_two_runs_numbers p region fuel ceiling
    (TarjanState (frame :: rest) disc low stack clock emitted) IH Hstate) as Hboth.
  destruct (audit_tarjan_run_counted p region fuel
    (TarjanState (frame :: rest) disc low stack clock emitted)) as [middle first].
  destruct (audit_tarjan_run_counted p region fuel middle) as [result second]; cbn in Hboth |- *.
  destruct Hboth as [Hresult Hboth]; rewrite Pos2Nat.inj_xO; split.
  - eapply (audit_tarjan_state_numbers_mono EV (ceiling + Pos.to_nat fuel + Pos.to_nat fuel));
      [lia|exact Hresult].
  - constructor; [exact I|].
    eapply (audit_tarjan_events_numbers_mono (ceiling + Pos.to_nat fuel + Pos.to_nat fuel));
      [lia|exact Hboth].
Qed.

(** A binary-fuel run bounds each intermediate numeric value by input ceiling plus fuel. *)
Lemma audit_tarjan_run_numbers {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) region fuel ceiling st :
    audit_tarjan_state_numbers EV ceiling st ->
    let '(next, events) := audit_tarjan_run_counted p region fuel st in
    audit_tarjan_state_numbers EV (ceiling + Pos.to_nat fuel) next /\
    Forall (audit_tarjan_event_numbers (ceiling + Pos.to_nat fuel)) events.
Proof.
  revert ceiling st; induction fuel as [fuel IH|fuel IH|];
    intros ceiling [frames disc low stack clock emitted] Hstate; destruct frames as [|frame rest].
  - cbn [audit_tarjan_run_counted]; split.
    + eapply (audit_tarjan_state_numbers_mono EV ceiling); [lia|exact Hstate].
    + repeat constructor.
  - eapply audit_tarjan_run_numbers_odd; [exact IH|exact Hstate].
  - cbn [audit_tarjan_run_counted]; split.
    + eapply (audit_tarjan_state_numbers_mono EV ceiling); [lia|exact Hstate].
    + repeat constructor.
  - eapply audit_tarjan_run_numbers_even; [exact IH|exact Hstate].
  - cbn [audit_tarjan_run_counted]; split.
    + eapply (audit_tarjan_state_numbers_mono EV ceiling); [lia|exact Hstate].
    + repeat constructor.
  - change (let '(next, events) :=
      let '(result, steps) := audit_tarjan_step_counted p region
        (TarjanState (frame :: rest) disc low stack clock emitted) in
      (result, AuditTarjanCase 7 :: steps) in
      audit_tarjan_state_numbers EV (ceiling + Pos.to_nat xH) next /\
      Forall (audit_tarjan_event_numbers (ceiling + Pos.to_nat xH)) events).
    pose proof (audit_tarjan_step_numbers p region ceiling
      (TarjanState (frame :: rest) disc low stack clock emitted) Hstate) as Hstep.
    destruct (audit_tarjan_step_counted p region
      (TarjanState (frame :: rest) disc low stack clock emitted)) as [result steps].
    cbn in Hstep |- *; destruct Hstep as [Hresult Hsteps].
    replace (ceiling + Pos.to_nat xH) with (S ceiling) by (cbn; lia); split; [exact Hresult|].
    constructor; [exact I|exact Hsteps].
Qed.

(** Processing one root grows the numeric ceiling by at most one plus the supplied fuel. *)
Lemma audit_tarjan_root_numbers {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) region ceiling st v :
    audit_tarjan_state_numbers EV ceiling st ->
    let '(next, events) := audit_tarjan_root_counted p region st v in
    audit_tarjan_state_numbers EV (ceiling + S (Pos.to_nat (fuel p))) next /\
    Forall (audit_tarjan_event_numbers (ceiling + S (Pos.to_nat (fuel p)))) events.
Proof.
  intro Hstate; unfold audit_tarjan_root_counted.
  destruct (Map.get EV v (disc st)) as [number|] eqn:Hfound.
  - cbn; split; [eapply (audit_tarjan_state_numbers_mono EV ceiling); [lia|exact Hstate]|].
    repeat constructor.
  - change (let '(result, events) :=
      let '(next, details) := audit_tarjan_discover_counted p v st in
      let '(result, events) := audit_tarjan_run_counted p region (fuel p) next in
      (result, [AuditTarjanGet v (disc st) None; AuditTarjanCase 11] ++
        map AuditTarjanHelper details ++ [AuditTarjanDiscover v st next] ++ events) in
      audit_tarjan_state_numbers EV (ceiling + S (Pos.to_nat (fuel p))) result /\
      Forall (audit_tarjan_event_numbers (ceiling + S (Pos.to_nat (fuel p)))) events).
    pose proof (audit_tarjan_discover_numbers p ceiling v st Hstate) as Hdiscover.
    destruct (audit_tarjan_discover_counted p v st) as [next details]; cbn in Hdiscover |- *.
    destruct Hdiscover as [Hnext Hdetail].
    pose proof (audit_tarjan_run_numbers p region (fuel p) (S ceiling) next Hnext) as Hrun.
    destruct (audit_tarjan_run_counted p region (fuel p) next) as [result events]; cbn in Hrun |- *.
    destruct Hrun as [Hresult Hevents]; split.
    + eapply (audit_tarjan_state_numbers_mono EV (S ceiling + Pos.to_nat (fuel p))); [lia|exact
      Hresult].
    + constructor; [exact I|]. constructor; [exact I|]. apply Forall_app; split.
      * apply audit_tarjan_helper_events_numbers.
        eapply Forall_impl; [|exact Hdetail].
        intros event Hnumber; eapply (audit_tarjan_helper_numbers_mono (S ceiling)); [lia|exact
          Hnumber].
      * constructor; [exact I|].
        eapply (audit_tarjan_events_numbers_mono (S ceiling + Pos.to_nat (fuel p))); [lia|exact
          Hevents].
Qed.

(** Root-list traversal bounds all numeric events by its initial ceiling and total fuel
  allowance. *)
Lemma audit_tarjan_roots_numbers {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) region roots ceiling st :
    audit_tarjan_state_numbers EV ceiling st ->
    let '(next, events) := audit_tarjan_roots_counted p region roots st in
    audit_tarjan_state_numbers EV (ceiling + length roots * S (Pos.to_nat (fuel p))) next /\
    Forall (audit_tarjan_event_numbers (ceiling + length roots * S (Pos.to_nat (fuel p)))) events.
Proof.
  revert ceiling st; induction roots as [|root rest IH]; intros ceiling st Hstate;
    cbn [audit_tarjan_roots_counted].
  - rewrite Nat.add_0_r; split; [exact Hstate|repeat constructor].
  - pose proof (audit_tarjan_root_numbers p region ceiling st root Hstate) as Hroot.
    destruct (audit_tarjan_root_counted p region st root) as [next here]; cbn in Hroot |- *.
    destruct Hroot as [Hnext Hhere].
    pose proof (IH (ceiling + S (Pos.to_nat (fuel p))) next Hnext) as Hrest.
    destruct (audit_tarjan_roots_counted p region rest next) as [result later]; cbn in Hrest |- *.
    destruct Hrest as [Hresult Hlater]; split.
    + eapply (audit_tarjan_state_numbers_mono EV
        (ceiling + S (Pos.to_nat (fuel p)) + length rest * S (Pos.to_nat (fuel p)))); [lia|exact
          Hresult].
    + constructor; [exact I|]. apply Forall_app; split.
      * eapply (audit_tarjan_events_numbers_mono (ceiling + S (Pos.to_nat (fuel p)))); [lia|exact
        Hhere].
      * eapply (audit_tarjan_events_numbers_mono
          (ceiling + S (Pos.to_nat (fuel p)) + length rest * S (Pos.to_nat (fuel p))));
            [lia|exact Hlater].
Qed.

(** Initial Tarjan state contains no indexed numbers and starts its clock at one. *)
Lemma audit_tarjan_initial_numbers {V E} (EV : encoding V) :
    audit_tarjan_state_numbers EV 1 (@tarjan_initial V E).
Proof.
  unfold audit_tarjan_state_numbers, tarjan_initial; cbn; split; [lia|].
  split; [|split].
  - intros v n Hget; rewrite Map.get_empty in Hget; discriminate.
  - intros v n Hget; rewrite Map.get_empty in Hget; discriminate.
  - constructor.
Qed.

(** Every counted SCC numeric operand fits the region-and-fuel input ceiling. *)
Lemma audit_scc_counted_numbers {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) region :
    Forall (audit_tarjan_event_numbers (2 + length region * S (Pos.to_nat (fuel p))))
      (snd (audit_scc_within_counted p region)).
Proof.
  unfold audit_scc_within_counted.
  assert (Hsetup : Forall (audit_tarjan_event_numbers (2 + length region * S (Pos.to_nat (fuel p))))
    (snd (@audit_tarjan_region_counted V E EV region FinSet.empty))).
  { generalize (@FinSet.empty V); induction region as [|v rest IH]; intro set;
      cbn [audit_tarjan_region_counted]; [repeat constructor|].
    specialize (IH (FinSet.add EV v set)).
    destruct (audit_tarjan_region_counted EV rest (FinSet.add EV v set)) as [result events].
    cbn in IH |- *; constructor; [exact I|].
    eapply (audit_tarjan_events_numbers_mono (2 + length rest * S (Pos.to_nat (fuel p))));
      [cbn; nia|exact IH]. }
  destruct (audit_tarjan_region_counted EV region FinSet.empty) as [keep setup]; cbn in Hsetup |- *.
  pose proof (audit_tarjan_roots_numbers p keep region 1 tarjan_initial
    (audit_tarjan_initial_numbers EV))
    as Hroots.
  destruct (audit_tarjan_roots_counted p keep region tarjan_initial) as [st events]; cbn in
    Hroots |- *.
  destruct Hroots as [_ Hevents]; apply Forall_app; split; [exact Hsetup|].
  apply Forall_app; split.
  - eapply (audit_tarjan_events_numbers_mono (1 + length region * S (Pos.to_nat (fuel p))));
      [lia|exact Hevents].
  - repeat constructor.
Qed.

(** * Output-list size *)

(** The two reversed output lists grow together when a component is emitted. *)
Definition audit_tarjan_output_size {V E} (st : tarjan_state V E) : nat :=
  length (components (emitted st)) + length (component_ids (emitted st)).

(** An emission adds exactly one component and one identifier. *)
Lemma audit_tarjan_emit_output_size {V E} (EV : encoding V) root (st : tarjan_state V E) :
    audit_tarjan_output_size (tarjan_emit EV root st) = S (S (audit_tarjan_output_size st)).
Proof.
  unfold tarjan_emit, audit_tarjan_output_size.
  destruct (tarjan_pop EV root (tarjan_next_id (emitted st))
    (pending st) (low st) (comp_of (emitted st))) as [[[members tail] links] owners].
  cbn; lia.
Qed.

(** Closing a frame grows the two output lists by at most one entry each. *)
Lemma audit_tarjan_close_output_size {V E} (EV : encoding V) v rest (st : tarjan_state V E) :
    audit_tarjan_output_size (tarjan_close EV v rest st) <= S (S (audit_tarjan_output_size st)).
Proof.
  unfold tarjan_close.
  destruct (Map.get EV v (low st)) as [lo|] eqn:Hlow;
    destruct (Map.get EV v (disc st)) as [di|] eqn:Hdisc; cbn; try (unfold
      audit_tarjan_output_size; cbn; lia).
  destruct (Pos.eqb lo di) eqn:Hequal.
  - rewrite audit_tarjan_emit_output_size; unfold audit_tarjan_output_size; cbn; lia.
  - destruct rest as [|parent rest]; [unfold audit_tarjan_output_size; cbn; lia|].
    unfold tarjan_lower; cbn [low]; destruct (Map.get EV (frame_node parent) (low st));
      unfold audit_tarjan_output_size; cbn; lia.
Qed.

(** A source transition adds at most one component and one identifier. *)
Lemma audit_tarjan_step_output_size {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) region st :
    audit_tarjan_output_size (tarjan_step p region st) <= S (S (audit_tarjan_output_size st)).
Proof.
  unfold tarjan_step.
  destruct (frames st) as [|[v edges] rest] eqn:Hframes; [lia|].
  destruct edges as [|edge edges].
  - pose proof (audit_tarjan_close_output_size EV v rest st); lia.
  - destruct (FinSet.mem EV (Graph.target g edge) region) eqn:Hinside; cbn.
    2: { unfold audit_tarjan_output_size; cbn; lia. }
    destruct (Map.get EV (Graph.target g edge) (disc st)) as [d|] eqn:Hdisc.
    + destruct (Map.get EV (Graph.target g edge) (low st)) as [onstack|] eqn:Hlow; cbn.
      * unfold tarjan_lower; cbn [low]; destruct (Map.get EV v (low st));
          unfold audit_tarjan_output_size; cbn; lia.
      * unfold audit_tarjan_output_size; cbn; lia.
    + change (audit_tarjan_output_size st <= S (S (audit_tarjan_output_size st))); lia.
Qed.

(** A counted step's returned persistent state adds at most two output-list entries. *)
Lemma audit_tarjan_counted_step_output_size {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) region st :
    audit_tarjan_output_size (fst (audit_tarjan_step_counted p region st)) <=
      S (S (audit_tarjan_output_size st)).
Proof.
  rewrite audit_tarjan_step_erases; apply audit_tarjan_step_output_size.
Qed.

(** Binary source fuel bounds the growth of both output lists across the actual run. *)
Lemma audit_tarjan_run_output_size {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) region fuel st :
    audit_tarjan_output_size (tarjan_run p region fuel st) <=
      audit_tarjan_output_size st + 2 * Pos.to_nat fuel.
Proof.
  revert st; induction fuel as [fuel IH|fuel IH|];
    intros [frames disc low stack clock emitted]; destruct frames as [|frame rest].
  - cbn [tarjan_run]; apply Nat.le_add_r.
  - change (audit_tarjan_output_size (tarjan_step p region (tarjan_run p region fuel
        (tarjan_run p region fuel (TarjanState (frame :: rest) disc low stack clock emitted)))) <=
      audit_tarjan_output_size (TarjanState (frame :: rest) disc low stack clock emitted) +
        2 * Pos.to_nat (xI fuel)).
    pose proof (IH (TarjanState (frame :: rest) disc low stack clock emitted)) as Hfirst.
    pose proof (IH (tarjan_run p region fuel
      (TarjanState (frame :: rest) disc low stack clock emitted))) as Hsecond.
    pose proof (audit_tarjan_step_output_size p region (tarjan_run p region fuel
      (tarjan_run p region fuel (TarjanState (frame :: rest) disc low stack clock emitted)))) as
        Hstep.
    rewrite Pos2Nat.inj_xI; nia.
  - cbn [tarjan_run]; apply Nat.le_add_r.
  - change (audit_tarjan_output_size (tarjan_run p region fuel
        (tarjan_run p region fuel (TarjanState (frame :: rest) disc low stack clock emitted))) <=
      audit_tarjan_output_size (TarjanState (frame :: rest) disc low stack clock emitted) +
        2 * Pos.to_nat (xO fuel)).
    pose proof (IH (TarjanState (frame :: rest) disc low stack clock emitted)) as Hfirst.
    pose proof (IH (tarjan_run p region fuel
      (TarjanState (frame :: rest) disc low stack clock emitted))) as Hsecond.
    rewrite Pos2Nat.inj_xO; nia.
  - cbn [tarjan_run]; apply Nat.le_add_r.
  - change (audit_tarjan_output_size (tarjan_step p region
        (TarjanState (frame :: rest) disc low stack clock emitted)) <=
      audit_tarjan_output_size (TarjanState (frame :: rest) disc low stack clock emitted) +
        2 * Pos.to_nat xH).
    pose proof (audit_tarjan_step_output_size p region
      (TarjanState (frame :: rest) disc low stack clock emitted)); cbn [Pos.to_nat]; lia.
Qed.

(** A source root adds no more output entries than its binary-fuel run can emit. *)
Lemma audit_tarjan_root_output_size {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) region st v :
    audit_tarjan_output_size (tarjan_root p region st v) <=
      audit_tarjan_output_size st + 2 * Pos.to_nat (fuel p).
Proof.
  unfold tarjan_root; destruct (Map.get EV v (disc st)) as [number|] eqn:Hfound; [lia|].
  pose proof (audit_tarjan_run_output_size p region (fuel p) (tarjan_discover p v st)) as Hrun.
  assert (Hsize : audit_tarjan_output_size (tarjan_discover p v st) =
    audit_tarjan_output_size st) by reflexivity.
  rewrite Hsize in Hrun.
  exact Hrun.
Qed.

(** Folding over roots grows the two output lists by at most twice their total fuel. *)
Lemma audit_tarjan_roots_output_size {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) region roots st :
    audit_tarjan_output_size (fold_left (tarjan_root p region) roots st) <=
      audit_tarjan_output_size st + 2 * length roots * Pos.to_nat (fuel p).
Proof.
  revert st; induction roots as [|root rest IH]; intro st; [cbn; lia|].
  cbn [fold_left length].
  pose proof (audit_tarjan_root_output_size p region st root) as Hroot.
  pose proof (IH (tarjan_root p region st root)) as Hrest; nia.
Qed.

(** The final counted state has at most two output entries per supplied root and fuel step. *)
Lemma audit_tarjan_counted_final_output {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) region roots :
    audit_tarjan_output_size (fst (audit_tarjan_roots_counted p region roots tarjan_initial)) <=
      2 * length roots * Pos.to_nat (fuel p).
Proof.
  rewrite audit_tarjan_roots_erase.
  pose proof (audit_tarjan_roots_output_size p region roots tarjan_initial) as Hsize.
  assert (Hinitial : audit_tarjan_output_size (@tarjan_initial V E) = 0) by reflexivity.
  rewrite Hinitial in Hsize; cbn in Hsize.
  exact Hsize.
Qed.

(** A traversal event is internal when it is not the final output-reversal receipt. *)
Definition audit_tarjan_internal_event {V E} (event : audit_tarjan_call V E) : Prop :=
  match event with
  | AuditTarjanOutput _ _ => False
  | _ => True
  end.

(** Wrapped helper events are internal, regardless of their numeric or key operands. *)
Lemma audit_tarjan_helper_events_internal {V E} (events : list (audit_thelper_event V E)) :
    Forall audit_tarjan_internal_event (map AuditTarjanHelper events).
Proof.
  induction events as [|event events IH]; cbn; [constructor|].
  constructor; [exact I|exact IH].
Qed.

(** A counted transition never emits the final output-reversal event. *)
Lemma audit_tarjan_step_internal {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) region st :
    Forall audit_tarjan_internal_event (snd (audit_tarjan_step_counted p region st)).
Proof.
  unfold audit_tarjan_step_counted.
  destruct (frames st) as [|[v edges] rest] eqn:Hframes; [repeat constructor|].
  destruct edges as [|edge edges].
  - destruct (audit_tarjan_close_counted EV v rest st) as [next details]; cbn.
    constructor; [exact I|]. apply Forall_app; split.
    + apply audit_tarjan_helper_events_internal.
    + repeat constructor.
  - destruct (FinSet.mem EV (Graph.target g edge) region) eqn:Hinside; [|repeat constructor].
    destruct (Map.get EV (Graph.target g edge) (disc st)) as [d|] eqn:Hdisc.
    + destruct (Map.get EV (Graph.target g edge) (low st)) as [onstack|] eqn:Hlow;
        [|repeat constructor].
      destruct (audit_tarjan_lower_counted EV v d
        (TarjanState (TarjanFrame v edges :: rest) (disc st) (low st)
          (pending st) (clock st) (emitted st))) as [next details]; cbn.
      repeat constructor; apply Forall_app; split;
        [apply audit_tarjan_helper_events_internal|repeat constructor].
    + destruct (audit_tarjan_discover_counted p (Graph.target g edge)
        (TarjanState (TarjanFrame v edges :: rest) (disc st) (low st)
          (pending st) (clock st) (emitted st))) as [next details]; cbn.
      repeat constructor; apply Forall_app; split;
        [apply audit_tarjan_helper_events_internal|repeat constructor].
Qed.

(** A binary-fuel run emits only internal events. *)
Lemma audit_tarjan_run_internal {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) region fuel st :
    Forall audit_tarjan_internal_event (snd (audit_tarjan_run_counted p region fuel st)).
Proof.
  pose proof (audit_tarjan_counted_run_invariant p region (fun _ => True)
    audit_tarjan_internal_event fuel st) as Hrun.
  assert (Hstep : forall state, True ->
    let '(next, events) := audit_tarjan_step_counted p region state in
    True /\ Forall audit_tarjan_internal_event events).
  { intros state _; pose proof (audit_tarjan_step_internal p region state) as Hinternal.
    destruct (audit_tarjan_step_counted p region state); cbn in Hinternal |- *; auto. }
  specialize (Hrun Hstep (fun _ => I) I).
  destruct (audit_tarjan_run_counted p region fuel st); exact (proj2 Hrun).
Qed.

(** A root's discovery and fuel run emit only internal events. *)
Lemma audit_tarjan_root_internal {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) region st v :
    Forall audit_tarjan_internal_event (snd (audit_tarjan_root_counted p region st v)).
Proof.
  unfold audit_tarjan_root_counted.
  destruct (Map.get EV v (disc st)) as [number|] eqn:Hfound; [repeat constructor|].
  change (Forall audit_tarjan_internal_event
    (snd (let '(next, details) := audit_tarjan_discover_counted p v st in
      let '(result, events) := audit_tarjan_run_counted p region (fuel p) next in
      (result, [AuditTarjanGet v (disc st) None; AuditTarjanCase 11] ++
        map AuditTarjanHelper details ++ [AuditTarjanDiscover v st next] ++ events)))).
  destruct (audit_tarjan_discover_counted p v st) as [next details].
  pose proof (audit_tarjan_run_internal p region (fuel p) next) as Hrun.
  destruct (audit_tarjan_run_counted p region (fuel p) next) as [result events]; cbn in Hrun |- *.
  constructor; [exact I|]. constructor; [exact I|]. apply Forall_app; split.
  - apply audit_tarjan_helper_events_internal.
  - constructor; [exact I|exact Hrun].
Qed.

(** Root-list traversal emits only internal events. *)
Lemma audit_tarjan_roots_internal {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) region roots st :
    Forall audit_tarjan_internal_event (snd (audit_tarjan_roots_counted p region roots st)).
Proof.
  revert st; induction roots as [|root rest IH]; intro st; cbn [audit_tarjan_roots_counted].
  - repeat constructor.
  - pose proof (audit_tarjan_root_internal p region st root) as Hroot.
    destruct (audit_tarjan_root_counted p region st root) as [next here]; cbn in Hroot |- *.
    pose proof (IH next) as Hrest.
    destruct (audit_tarjan_roots_counted p region rest next) as [result later]; cbn in Hrest |- *.
    constructor; [exact I|]. apply Forall_app; split; assumption.
Qed.

(** Region construction emits only set and administrative events. *)
Lemma audit_tarjan_region_internal {V E} (EV : encoding V) region set :
    Forall audit_tarjan_internal_event (snd (@audit_tarjan_region_counted V E EV region set)).
Proof.
  revert set; induction region as [|v rest IH]; intro set; cbn [audit_tarjan_region_counted].
  - repeat constructor.
  - pose proof (IH (FinSet.add EV v set)) as Hrest.
    destruct (audit_tarjan_region_counted EV rest (FinSet.add EV v set)) as [result events].
    cbn in Hrest |- *; constructor; [exact I|exact Hrest].
Qed.

(** * Counted model work *)

(** One helper's key and numeric envelopes bound its concrete model work. *)
Lemma audit_tarjan_helper_work_bound {V E} (EV : encoding V) vertices ceiling width
    (event : audit_thelper_event V E) :
    (forall v, In v vertices -> audit_key_bits_weight (encode EV v) <= width) ->
    (forall n, Pos.to_nat n <= ceiling -> Pos.size_nat n <= width) ->
    audit_tarjan_helper_keys vertices event -> audit_tarjan_helper_numbers ceiling event ->
    audit_thelper_event_work EV event <= 70 + 12 * width.
Proof.
  intros Hkeys Hnumbers Hkey Hnumber.
  destruct event as [site|v m [number|]|v m result|v number m|v m|a b result|
    a b result|a b result|a b|key members m];
    cbn [audit_tarjan_helper_keys audit_tarjan_helper_numbers] in Hkey, Hnumber;
    unfold audit_thelper_event_work, audit_encoding_weight, audit_get_weight, audit_set_weight,
      audit_remove_weight, audit_binary_weight, audit_key_bits_weight;
    try rewrite !audit_dfs_positive_z_bits; try (cbn [audit_z_bits]); try lia.
  - specialize (Hkeys v Hkey); unfold audit_key_bits_weight in Hkeys; lia.
  - specialize (Hkeys v Hkey); unfold audit_key_bits_weight in Hkeys; lia.
  - specialize (Hkeys v Hkey); unfold audit_key_bits_weight in Hkeys; lia.
  - specialize (Hkeys v Hkey); unfold audit_key_bits_weight in Hkeys; lia.
  - specialize (Hkeys v Hkey); unfold audit_key_bits_weight in Hkeys; lia.
  - destruct Hkey as [Ha Hb]; specialize (Hkeys a Ha) as Hwidth_a;
      specialize (Hkeys b Hb) as Hwidth_b; unfold audit_key_bits_weight in *; lia.
  - destruct Hnumber as [Ha Hb]; specialize (Hnumbers a Ha) as Hwidth_a; specialize (Hnumbers b
    Hb) as Hwidth_b; lia.
  - destruct Hnumber as [Ha Hb]; specialize (Hnumbers a Ha) as Hwidth_a; specialize (Hnumbers b
    Hb) as Hwidth_b; lia.
  - destruct Hnumber as [Ha Hb]; specialize (Hnumbers a Ha); cbn [Pos.size_nat]; lia.
  - specialize (Hnumbers key Hnumber); lia.
Qed.

(** Each internal event fits the common key and numeric width envelope. *)
Lemma audit_tarjan_internal_event_work_bound {V E} (EV : encoding V) vertices ceiling width
    (event : audit_tarjan_call V E) :
    (forall v, In v vertices -> audit_key_bits_weight (encode EV v) <= width) ->
    (forall n, Pos.to_nat n <= ceiling -> Pos.size_nat n <= width) ->
    audit_tarjan_event_keys vertices event -> audit_tarjan_event_numbers ceiling event ->
    audit_tarjan_internal_event event -> audit_tarjan_event_work EV event <= 140 + 12 * width.
Proof.
  intros Hkeys Hnumbers Hkey Hnumber Hinternal.
  destruct event as [site|edge target|v set result|v map result|v before after|v n before after|
    v rest before after|helper|v set|a b];
    cbn [audit_tarjan_event_keys audit_tarjan_event_numbers audit_tarjan_internal_event] in *;
    unfold audit_tarjan_event_work, audit_encoding_weight, audit_get_weight, audit_set_weight,
      audit_key_bits_weight; try contradiction; try lia.
  - specialize (Hkeys v Hkey); unfold audit_key_bits_weight in Hkeys; lia.
  - specialize (Hkeys v Hkey); unfold audit_key_bits_weight in Hkeys; lia.
  - pose proof (audit_tarjan_helper_work_bound EV vertices ceiling width helper Hkeys Hnumbers
      Hkey Hnumber); lia.
  - specialize (Hkeys v Hkey); unfold audit_key_bits_weight in Hkeys; lia.
Qed.

(** Summing internal event work retains the same single original-input width bound. *)
Lemma audit_tarjan_internal_work_bound {V E} (EV : encoding V) vertices ceiling width
    (events : list (audit_tarjan_call V E)) :
    (forall v, In v vertices -> audit_key_bits_weight (encode EV v) <= width) ->
    (forall n, Pos.to_nat n <= ceiling -> Pos.size_nat n <= width) ->
    Forall (audit_tarjan_event_keys vertices) events ->
    Forall (audit_tarjan_event_numbers ceiling) events -> Forall audit_tarjan_internal_event
      events ->
    fold_right (fun event n => audit_tarjan_event_work EV event + n) 0 events <=
      length events * (140 + 12 * width).
Proof.
  intros Hkeys Hnumbers Hkey_events Hnum_events Hinternal.
  induction events as [|event rest IH]; [reflexivity|].
  inversion Hkey_events as [|? ? Hkey Hkeys_rest]; subst.
  inversion Hnum_events as [|? ? Hnumber Hnumbers_rest]; subst.
  inversion Hinternal as [|? ? Hcase Hinternal_rest]; subst.
  specialize (IH Hkeys_rest Hnumbers_rest Hinternal_rest).
  pose proof (audit_tarjan_internal_event_work_bound EV vertices ceiling width event Hkeys Hnumbers
    Hkey Hnumber Hcase) as Hwork.
  cbn [fold_right length]; nia.
Qed.

(** Event-work sums distribute over the two consecutive portions of a trace. *)
Lemma audit_tarjan_work_sum_app {V E} (EV : encoding V)
    (left right : list (audit_tarjan_call V E)) :
    fold_right (fun event n => audit_tarjan_event_work EV event + n) 0 (left ++ right) =
    fold_right (fun event n => audit_tarjan_event_work EV event + n) 0 left +
    fold_right (fun event n => audit_tarjan_event_work EV event + n) 0 right.
Proof.
  induction left as [|event rest IH]; [reflexivity|].
  change (audit_tarjan_event_work EV event +
    fold_right (fun item n => audit_tarjan_event_work EV item + n) 0 (rest ++ right) =
    (audit_tarjan_event_work EV event +
      fold_right (fun item n => audit_tarjan_event_work EV item + n) 0 rest) +
    fold_right (fun item n => audit_tarjan_event_work EV item + n) 0 right).
  rewrite IH; lia.
Qed.

(** The input width bounds each region vertex, indexed target, and number below the ceiling. *)
Lemma audit_tarjan_input_width_bounds {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) region ceiling :
    (forall v, In v (region ++ map (Graph.target g)
      (flat_map snd (Map.elements (out_index p)))) ->
      audit_key_bits_weight (encode EV v) <=
        Nat.max (audit_dfs_input_width EV g p region) (Pos.size_nat (Pos.of_succ_nat ceiling))) /\
    (forall n, Pos.to_nat n <= ceiling -> Pos.size_nat n <=
      Nat.max (audit_dfs_input_width EV g p region) (Pos.size_nat (Pos.of_succ_nat ceiling))).
Proof.
  split.
  - intros v Hin; eapply Nat.le_trans; [now apply (audit_dfs_envelope_width EV g p region v)|].
    apply Nat.le_max_l.
  - intros n Hn; eapply Nat.le_trans with (m := Pos.size_nat (Pos.of_succ_nat ceiling)).
    + now apply audit_dfs_clock_width.
    + apply Nat.le_max_r.
Qed.

(** The actual counted work sum is bounded by input width plus the final output-list size. *)
Lemma audit_scc_counted_work_sum {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) region :
    let events := snd (audit_scc_within_counted p region) in
    let width := Nat.max (audit_dfs_input_width EV g p region)
      (Pos.size_nat (Pos.of_succ_nat (2 + length region * S (Pos.to_nat (fuel p))))) in
    fold_right (fun event n => audit_tarjan_event_work EV event + n) 0 events <=
      length events * (140 + 12 * width) + 2 * length region * Pos.to_nat (fuel p).
Proof.
  set (vertices := region ++ map (Graph.target g) (flat_map snd (Map.elements (out_index p)))).
  set (ceiling := 2 + length region * S (Pos.to_nat (fuel p))).
  set (width := Nat.max (audit_dfs_input_width EV g p region)
    (Pos.size_nat (Pos.of_succ_nat ceiling))).
  pose proof (audit_tarjan_input_width_bounds EV g p region ceiling) as [Hkeys Hnumbers].
  fold vertices width in Hkeys; fold width in Hnumbers.
  pose proof (audit_scc_counted_keys p region) as Hkey_events.
  fold vertices in Hkey_events.
  pose proof (audit_scc_counted_numbers p region) as Hnum_events.
  fold ceiling in Hnum_events.
  unfold audit_scc_within_counted in Hkey_events, Hnum_events |- *.
  pose proof (@audit_tarjan_region_internal V E EV region FinSet.empty) as Hsetup_internal.
  destruct (audit_tarjan_region_counted EV region FinSet.empty) as [keep setup].
  cbn in Hsetup_internal, Hkey_events, Hnum_events |- *.
  pose proof (audit_tarjan_roots_internal p keep region tarjan_initial) as Hroots_internal.
  pose proof (audit_tarjan_counted_final_output p keep region) as Houtput.
  destruct (audit_tarjan_roots_counted p keep region tarjan_initial) as [st calls].
  cbn in Hroots_internal, Houtput, Hkey_events, Hnum_events |- *.
  assert (Hinternal : Forall audit_tarjan_internal_event (setup ++ calls))
    by (apply Forall_app; split; assumption).
  assert (Hprefix_keys : Forall (audit_tarjan_event_keys vertices) (setup ++ calls)).
  { rewrite app_assoc in Hkey_events; apply Forall_app in Hkey_events; tauto. }
  assert (Hprefix_numbers : Forall (audit_tarjan_event_numbers ceiling) (setup ++ calls)).
  { rewrite app_assoc in Hnum_events; apply Forall_app in Hnum_events; tauto. }
  pose proof (audit_tarjan_internal_work_bound EV vertices ceiling width (setup ++ calls)
    Hkeys Hnumbers Hprefix_keys Hprefix_numbers Hinternal) as Hsum.
  rewrite !app_assoc.
  change (fold_right (fun event n => audit_tarjan_event_work EV event + n) 0
    ((setup ++ calls) ++ [AuditTarjanOutput (length (components (emitted st)))
      (length (component_ids (emitted st)))]) <=
    length ((setup ++ calls) ++ [AuditTarjanOutput (length (components (emitted st)))
      (length (component_ids (emitted st)))]) * (140 + 12 * width) +
      2 * length region * Pos.to_nat (fuel p)).
  rewrite audit_tarjan_work_sum_app, length_app.
  change (fold_right (fun event n => audit_tarjan_event_work EV event + n) 0 (setup ++ calls) +
    ((64 + (length (components (emitted st)) + length (component_ids (emitted st)))) + 0) <=
    (length (setup ++ calls) + 1) * (140 + 12 * width) +
      2 * length region * Pos.to_nat (fuel p)).
  unfold audit_tarjan_output_size in Houtput; nia.
Qed.

(** Counted SCC execution returns the source result within its original-input event and work
    bounds. *)
Theorem audit_scc_within_counted_correct : audit_scc_within_counted_statement.
Proof.
  intros V E EV g p region.
  pose proof (audit_scc_counted_erases EV g p region) as Herase.
  pose proof (audit_scc_counted_event_bound p region) as Hcount.
  pose proof (audit_scc_counted_work_sum p region) as Hsum.
  set (bound := audit_tarjan_input_event_bound p region).
  set (width := Nat.max (audit_dfs_input_width EV g p region)
    (Pos.size_nat (Pos.of_succ_nat (2 + length region * S (Pos.to_nat (fuel p)))))).
  assert (Hsteps : length region * Pos.to_nat (fuel p) <= bound).
  { unfold bound, audit_tarjan_input_event_bound.
    set (r := length region); set (f := Pos.to_nat (fuel p)).
    assert (Htail : r * f <= 12 + 6 * S (r * S f)) by nia.
    eapply Nat.le_trans; [exact Htail|].
    replace (12 + 6 * S (r * S f)) with (1 * (12 + 6 * S (r * S f))) at 1 by lia.
    apply Nat.mul_le_mono_r; nia. }
  destruct (audit_scc_within_counted p region) as [result events].
  change (result = scc_within p region) in Herase.
  change (length events <= bound) in Hcount.
  change (fold_right (fun event n => audit_tarjan_event_work EV event + n) 0 events <=
    length events * (140 + 12 * width) + 2 * length region * Pos.to_nat (fuel p)) in Hsum.
  split; [exact Herase|]. split; [exact Hcount|].
  unfold audit_tarjan_model_work, audit_tarjan_input_budget; fold bound width.
  change (64 * S (length events) * S (length events) +
    fold_right (fun event n => audit_tarjan_event_work EV event + n) 0 events <=
    128 * S bound * S bound + bound * (140 + 12 * width)).
  nia.
Qed.

(** Nested SCC traversal keeps the counted result, trace, and original-input bounds. *)
Theorem audit_scc_within_nested_holds : audit_scc_within_nested_statement.
Proof.
  apply audit_scc_nested_from_counted; exact audit_scc_within_counted_correct.
Qed.

(** Nested SCC total work adds the work of exactly the recorded callback bodies. *)
Theorem audit_scc_within_nested_total_holds : audit_scc_within_nested_total_statement.
Proof.
  apply audit_scc_nested_total_from_nested; exact audit_scc_within_nested_holds.
Qed.

(** * Source event work *)

(** Key-bearing source events use the encoder results captured at their actual call sites. *)
Definition audit_scc_source_code_matches {V E B} (EV : encoding V)
    (item : audit_tarjan_nested_event V E (audit_graph_callback_capture V E B)) : Prop :=
  let '(event, body) := item in
  match event with
  | AuditTarjanMember v _ _
  | AuditTarjanGet v _ _
  | AuditTarjanSet v _
  | AuditTarjanHelper (THGet v _ _)
  | AuditTarjanHelper (THGetEdges v _ _)
  | AuditTarjanHelper (THSet v _ _)
  | AuditTarjanHelper (THRemove v _) =>
    audit_dfs_source_code body = encode EV v
  | AuditTarjanHelper (THCompare a b _) =>
    audit_scc_source_codes body = (encode EV a, encode EV b)
  | _ => True
  end.

(** Well-formed same-call receipts identify each source event's captured encoder operands. *)
Lemma audit_scc_source_event_code {V E B} (EV : encoding V) (g : Graph.t V E)
    (cb : audit_dfs_callback_model V E B) item :
    audit_dfs_callbacks_erase EV g cb -> audit_scc_source_event_wellformed item ->
    audit_tarjan_event_bodies (audit_dfs_capture_receipt cb) item ->
    audit_scc_source_code_matches EV item.
Proof.
  intros Hcallbacks Hshape Hreceipts; destruct item as [event body].
  destruct event as [site|edge target|v set result|v m result|v before after|v n before after|
    v rest before after|helper|v set|a b];
    cbn [audit_scc_source_code_matches audit_scc_source_event_wellformed] in *; try exact I.
  all: try (destruct helper as [site|v m result|v m result|v n m|v m|a b result|
    a b result|a b result|a b|key members m];
    cbn [audit_scc_source_code_matches audit_scc_source_event_wellformed] in *; try exact I).
  all: try (destruct Hshape as [code [trace Hbody]]; subst body;
    cbn [audit_tarjan_event_bodies] in Hreceipts;
    inversion Hreceipts as [|? ? Hreceipt ?]; cbn [audit_dfs_source_code];
    eapply audit_dfs_receipt_code; eauto).
  destruct Hshape as [ac [bc [trace_a [trace_b Hbody]]]]; subst body.
  cbn [audit_tarjan_event_bodies] in Hreceipts.
  inversion Hreceipts as [|? ? Hleft Htail]; subst.
  inversion Htail as [|? ? Hright Hnil]; subst.
  cbn [audit_scc_source_codes]; f_equal; eapply audit_dfs_receipt_code; eauto.
Qed.

(** One source helper's trie and arithmetic work fits the original key and numeric widths. *)
Lemma audit_scc_source_helper_work_bound {V E B} (EV : encoding V) vertices ceiling width
    (helper : audit_thelper_event V E) (body : list (audit_graph_callback_capture V E B)) :
    (forall v, In v vertices -> audit_key_bits_weight (encode EV v) <= width) ->
    (forall n, Pos.to_nat n <= ceiling -> Pos.size_nat n <= width) ->
    audit_tarjan_helper_keys vertices helper -> audit_tarjan_helper_numbers ceiling helper ->
    audit_scc_source_code_matches EV (AuditTarjanHelper helper, body) ->
    audit_scc_source_helper_work body helper <= 40 + 32 * width.
Proof.
  intros Hkeys Hnumbers Hkey Hnumber Hcode.
  destruct helper as [site|v m result|v m result|v value m|v m|a b result|
    a b result|a b result|a b|key members m];
    cbn [audit_tarjan_helper_keys audit_tarjan_helper_numbers audit_scc_source_code_matches] in *;
    unfold audit_scc_source_helper_work; try lia.
  - rewrite Hcode; pose proof (audit_trie_get_source_work_bound _ (encode EV v) m) as Hget.
    specialize (Hkeys v Hkey); unfold audit_key_bits_weight in Hkeys; lia.
  - rewrite Hcode; pose proof (audit_trie_get_source_work_bound _ (encode EV v) m) as Hget.
    specialize (Hkeys v Hkey); unfold audit_key_bits_weight in Hkeys; lia.
  - rewrite Hcode; pose proof (audit_trie_update_source_work_bound _ (encode EV v) (Some (v,
    value)) m)
      as Hset. specialize (Hkeys v Hkey); unfold audit_key_bits_weight in Hkeys; lia.
  - rewrite Hcode; pose proof (audit_trie_update_source_work_bound _ (encode EV v) None m) as
    Hremove.
    specialize (Hkeys v Hkey); unfold audit_key_bits_weight in Hkeys; lia.
  - rewrite Hcode; destruct Hkey as [Ha Hb].
    specialize (Hkeys a Ha) as Hwidth_a; unfold audit_key_bits_weight in Hwidth_a.
    pose proof (Nat.le_min_l (Pos.size_nat (encode EV a)) (Pos.size_nat (encode EV b))); lia.
  - destruct Hnumber as [Ha Hb]; specialize (Hnumbers a Ha) as Hwidth_a.
    pose proof (Nat.le_min_l (Pos.size_nat a) (Pos.size_nat b)); lia.
  - destruct Hnumber as [Ha Hb]; specialize (Hnumbers a Ha) as Hwidth_a.
    pose proof (Nat.le_min_l (Pos.size_nat a) (Pos.size_nat b)); lia.
  - destruct Hnumber as [Ha Hb]; specialize (Hnumbers a Ha); lia.
  - pose proof (audit_trie_update_source_work_bound _ key (Some members) m) as Hset.
    specialize (Hnumbers key Hnumber); lia.
Qed.

(** The output event records both list sizes; internal events have zero output size. *)
Definition audit_tarjan_event_output {V E} (event : audit_tarjan_call V E) : nat :=
  match event with
  | AuditTarjanOutput components identifiers => components + identifiers
  | _ => 0
  end.

(** A source event's work includes its captured callback bodies and bounded concrete operations. *)
Lemma audit_scc_source_event_work_bound {V E B} (EV : encoding V) (weight : B -> nat)
    vertices ceiling width
    (item : audit_tarjan_nested_event V E (audit_graph_callback_capture V E B)) :
    (forall v, In v vertices -> audit_key_bits_weight (encode EV v) <= width) ->
    (forall n, Pos.to_nat n <= ceiling -> Pos.size_nat n <= width) ->
    audit_tarjan_event_keys vertices (fst item) -> audit_tarjan_event_numbers ceiling (fst item) ->
    audit_scc_source_code_matches EV item ->
    audit_scc_source_event_work weight item <=
      512 + 64 * width + 2 * audit_tarjan_event_output (fst item) +
      audit_scc_source_body_work weight [item].
Proof.
  intros Hkeys Hnumbers Hkey Hnumber Hcode; destruct item as [event body].
  destruct event as [site|edge target|v set result|v m result|v before after|v n before after|
    v rest before after|helper|v set|a b];
    cbn [audit_tarjan_event_keys audit_tarjan_event_numbers audit_scc_source_code_matches] in *;
    unfold audit_scc_source_event_work, audit_scc_source_body_work, audit_tarjan_event_output;
    cbn; try lia.
  - rewrite Hcode; pose proof (audit_trie_get_source_work_bound _ (encode EV v) set) as Hget.
    specialize (Hkeys v Hkey); unfold audit_key_bits_weight in Hkeys; lia.
  - rewrite Hcode; pose proof (audit_trie_get_source_work_bound _ (encode EV v) m) as Hget.
    specialize (Hkeys v Hkey); unfold audit_key_bits_weight in Hkeys; lia.
  - pose proof (audit_scc_source_helper_work_bound EV vertices ceiling width helper body Hkeys
      Hnumbers Hkey Hnumber Hcode) as Hhelper; lia.
  - rewrite Hcode; pose proof (audit_trie_update_source_work_bound _ (encode EV v) (Some (v, tt))
    set)
      as Hset. specialize (Hkeys v Hkey); unfold audit_key_bits_weight in Hkeys; lia.
Qed.

(** Every counted SCC output receipt is bounded by the actual root-and-fuel allowance. *)
Lemma audit_scc_counted_event_output {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) region :
    Forall (fun event => audit_tarjan_event_output event <=
      2 * length region * Pos.to_nat (fuel p)) (snd (audit_scc_within_counted p region)).
Proof.
  unfold audit_scc_within_counted.
  pose proof (@audit_tarjan_region_internal V E EV region FinSet.empty) as Hsetup.
  destruct (audit_tarjan_region_counted EV region FinSet.empty) as [keep setup]; cbn in Hsetup |- *.
  pose proof (audit_tarjan_roots_internal p keep region tarjan_initial) as Hroots.
  pose proof (audit_tarjan_counted_final_output p keep region) as Houtput.
  destruct (audit_tarjan_roots_counted p keep region tarjan_initial) as [st calls];
    cbn in Hroots, Houtput |- *.
  assert (Hinternal : Forall audit_tarjan_internal_event (setup ++ calls))
    by (apply Forall_app; split; assumption).
  rewrite app_assoc; apply Forall_app; split.
  - induction Hinternal as [|event events Hcase Htail IH]; [constructor|].
    constructor; [|exact IH].
    destruct event; cbn [audit_tarjan_internal_event audit_tarjan_event_output] in *;
      try contradiction; lia.
  - constructor; [|constructor]. cbn [audit_tarjan_event_output].
    unfold audit_tarjan_output_size in Houtput; exact Houtput.
Qed.

(** Every captured SCC key event retains the encoder result from its own callback. *)
Lemma audit_scc_source_codes {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) region :
    audit_dfs_callbacks_erase EV g cb ->
    Forall (audit_scc_source_code_matches EV) (snd (audit_scc_source_counted p cb region)).
Proof.
  intro Hcallbacks.
  pose proof (audit_scc_source_events_wellformed p cb region) as Hshape.
  pose proof (audit_scc_source_receipts p cb region) as Hreceipts.
  apply Forall_forall; intros item Hin.
  eapply audit_scc_source_event_code; [exact Hcallbacks| |].
  - apply Forall_forall with (x := item) in Hshape; assumption.
  - apply Forall_forall with (x := item) in Hreceipts; assumption.
Qed.

(** Source event work sums against the actual captured callbacks and the same input envelopes. *)
Lemma audit_scc_source_work_sum {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (weight : B -> nat) region :
    audit_dfs_callbacks_erase EV g cb ->
    let events := snd (audit_scc_source_counted p cb region) in
    let width := Nat.max (audit_dfs_input_width EV g p region)
      (Pos.size_nat (Pos.of_succ_nat (2 + length region * S (Pos.to_nat (fuel p))))) in
    audit_scc_source_work weight events <=
      length events * (512 + 64 * width + 4 * length region * Pos.to_nat (fuel p)) +
      audit_scc_source_body_work weight events.
Proof.
  intro Hcallbacks.
  set (vertices := region ++ map (Graph.target g) (flat_map snd (Map.elements (out_index p)))).
  set (ceiling := 2 + length region * S (Pos.to_nat (fuel p))).
  set (width := Nat.max (audit_dfs_input_width EV g p region)
    (Pos.size_nat (Pos.of_succ_nat ceiling))).
  assert (Hkeys : forall v, In v vertices -> audit_key_bits_weight (encode EV v) <= width).
  { intros v Hin; unfold width; eapply Nat.le_trans.
    - apply (audit_dfs_envelope_width EV g p region v); exact Hin.
    - apply Nat.le_max_l. }
  assert (Hnumbers : forall n, Pos.to_nat n <= ceiling -> Pos.size_nat n <= width).
  { intros n Hn; unfold width; eapply Nat.le_trans with
      (m := Pos.size_nat (Pos.of_succ_nat ceiling)); [now apply audit_dfs_clock_width|apply
        Nat.le_max_r]. }
  pose proof (audit_scc_source_erases p cb region Hcallbacks) as Herase.
  pose proof (audit_scc_source_codes p cb region Hcallbacks) as Hcodes.
  pose proof (audit_scc_counted_keys p region) as Hkey_events; fold vertices in Hkey_events.
  pose proof (audit_scc_counted_numbers p region) as Hnum_events; fold ceiling in Hnum_events.
  pose proof (audit_scc_counted_event_output p region) as Houtput.
  destruct (audit_scc_source_counted p cb region) as [result events].
  cbn in Herase, Hcodes.
  rewrite <- Herase in Hkey_events, Hnum_events, Houtput; cbn in Hkey_events, Hnum_events, Houtput.
  apply Forall_map in Hkey_events, Hnum_events, Houtput.
  change (audit_scc_source_work weight events <=
    length events * (512 + 64 * width + 4 * length region * Pos.to_nat (fuel p)) +
    audit_scc_source_body_work weight events).
  clear Herase.
  induction events as [|item events IH].
  - cbn [audit_scc_source_work audit_scc_source_body_work]; reflexivity.
  - inversion Hkey_events as [|? ? Hkey Hkeys_rest].
    inversion Hnum_events as [|? ? Hnumber Hnumbers_rest].
    inversion Houtput as [|? ? Hout Houtput_rest].
    inversion Hcodes as [|? ? Hcode Hcodes_rest].
    specialize (IH Hcodes_rest Hkeys_rest Hnumbers_rest Houtput_rest).
    pose proof (audit_scc_source_event_work_bound EV weight vertices ceiling width item
      Hkeys Hnumbers Hkey Hnumber Hcode) as Hevent.
    unfold audit_scc_source_work, audit_scc_source_body_work in *; cbn [fold_right length] in *.
    rewrite Nat.mul_succ_l; nia.
Qed.

(** The public event bound dominates the original region-and-fuel transition allowance. *)
Lemma audit_tarjan_input_steps_bound {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) region :
    length region * Pos.to_nat (fuel p) <= audit_tarjan_input_event_bound p region.
Proof.
  unfold audit_tarjan_input_event_bound.
  set (r := length region); set (f := Pos.to_nat (fuel p)).
  assert (Htail : r * f <= 12 + 6 * S (r * S f)) by nia.
  eapply Nat.le_trans; [exact Htail|].
  replace (12 + 6 * S (r * S f)) with (1 * (12 + 6 * S (r * S f))) at 1 by lia.
  apply Nat.mul_le_mono_r; nia.
Qed.

(** Captured SCC execution returns the source result within its input-derived concrete work
  bound. *)
Theorem audit_scc_source_correct : audit_scc_source_statement.
Proof.
  intros V E B EV g p cb weight region Hcallbacks.
  pose proof (audit_scc_source_result_and_count p cb region Hcallbacks) as Hresult_count.
  pose proof (audit_scc_source_events_wellformed p cb region) as Hshape.
  pose proof (audit_scc_source_work_sum p cb weight region Hcallbacks) as Hsum.
  pose proof (audit_tarjan_input_steps_bound p region) as Hsteps.
  set (bound := audit_tarjan_input_event_bound p region).
  set (width := Nat.max (audit_dfs_input_width EV g p region)
    (Pos.size_nat (Pos.of_succ_nat (2 + length region * S (Pos.to_nat (fuel p)))))).
  destruct (audit_scc_source_counted p cb region) as [result events].
  change (result = scc_within p region /\ length events <= bound) in Hresult_count.
  change (Forall audit_scc_source_event_wellformed events) in Hshape.
  change (audit_scc_source_work weight events <=
    length events * (512 + 64 * width + 4 * length region * Pos.to_nat (fuel p)) +
    audit_scc_source_body_work weight events) in Hsum.
  fold bound in Hsteps; destruct Hresult_count as [Hresult Hcount].
  split; [exact Hresult|]. split; [exact Hshape|]. split; [exact Hcount|].
  unfold audit_scc_source_budget; fold bound width.
  change (audit_scc_source_work weight events <=
    1024 * S bound * S bound + bound * (512 + 64 * width) +
    audit_scc_source_body_work weight events).
  nia.
Qed.

(** Same-run callback receipts transfer the source work bound to caller-supplied budgets. *)
Theorem audit_scc_source_adapted_correct : audit_scc_source_adapted_statement.
Proof.
  apply audit_scc_source_adapted_from_source; exact audit_scc_source_correct.
Qed.

(** The SCC source contract combines concrete work, primitive adequacy, and external budgets. *)
Theorem audit_scc_source_contract_correct : audit_scc_source_contract_statement.
Proof.
  split; [exact audit_scc_source_correct|].
  split; [exact audit_scc_source_primitives_correct|exact audit_scc_source_adapted_correct].
Qed.
