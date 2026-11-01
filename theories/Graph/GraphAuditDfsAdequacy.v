(** * Depth-first search audit adequacy

    Relates the counted DFS operations and callback captures to their source operations.
    For example, a captured encoder retains its original returned code.
    Builds on: GraphAuditDfs and GraphDfs. *)

From Stdlib Require Import List Bool PArith Arith ZArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsAuditCost
  CollectionsAuditEncodingAdequacy CollectionsAuditTrie CollectionsAuditTrieAdequacy.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphAuditDfs GraphAuditBase
  GraphAuditBaseAdequacy.
Import List.ListNotations.

(** * Helper and callback erasure *)

(** Counted discovery returns its source-helper result with at most four events, and finishing
    returns its source-helper result with exactly two events. *)
Theorem audit_dfs_helpers_correct : audit_dfs_helpers_statement.
Proof.
  unfold audit_dfs_helpers_statement.
  split.
  - intros V E EV v [edge|] st;
      cbn [audit_dfs_discover_counted dfs_discover]; split; cbn; try reflexivity; lia.
  - intros V E EV v st.
    cbn [audit_dfs_finish_counted dfs_finish]; auto.
Qed.

(** Capturing erasing target and encoder callbacks preserves their returned-value agreement. *)
Theorem audit_graph_capture_callbacks_erases_holds :
    audit_graph_capture_callbacks_erases_statement.
Proof.
  unfold audit_graph_capture_callbacks_erases_statement, audit_dfs_callbacks_erase.
  intros V E B EV g cb [Htarget Hencode]; split.
  - intro edge; specialize (Htarget edge).
    unfold audit_graph_capture_callbacks; cbn.
    destruct (audit_dfs_target_model cb edge); exact Htarget.
  - intro vertex; specialize (Hencode vertex).
    unfold audit_graph_capture_callbacks; cbn.
    destruct (audit_dfs_encode_model cb vertex); exact Hencode.
Qed.

(** * Successor events *)

(** Each discovery clock records the successor of its input clock. *)
Lemma audit_dfs_discover_successors {V E B}
    (cb : audit_dfs_callback_model V E (audit_graph_callback_capture V E B)) v via st :
    Forall audit_dfs_source_successor_event (snd (audit_dfs_nested_discover cb v via st)).
Proof.
  unfold audit_dfs_nested_discover.
  destruct via as [edge|];
    repeat match goal with
    | |- context [audit_dfs_nested_set ?cb ?v ?x ?m] =>
      destruct (audit_dfs_nested_set cb v x m)
    end;
    cbn; repeat constructor; apply audit_positive_succ_erases.
Qed.

(** Each finish clock records the successor of its input clock. *)
Lemma audit_dfs_finish_successors {V E B}
    (cb : audit_dfs_callback_model V E (audit_graph_callback_capture V E B)) v st :
    Forall audit_dfs_source_successor_event (snd (audit_dfs_nested_finish cb v st)).
Proof.
  unfold audit_dfs_nested_finish.
  destruct (audit_dfs_nested_set cb v (DfsState.post_clock st) (DfsState.post_index st)).
  cbn; repeat constructor; apply audit_positive_succ_erases.
Qed.

(** A DFS step propagates the successor property through its helper trace. *)
Lemma audit_dfs_step_successors {V E B} {EV} {g : Graph.t V E}
    (p : prepared EV g)
    (cb : audit_dfs_callback_model V E (audit_graph_callback_capture V E B)) blocked work :
    Forall audit_dfs_source_successor_event (snd (audit_dfs_nested_step p cb blocked work)).
Proof.
  destruct work as [stack st], stack as [|[v edges] rest]; cbn [audit_dfs_nested_step].
  - repeat constructor.
  - destruct edges as [|edge edges].
    + pose proof (audit_dfs_finish_successors cb v st) as Hfinish.
      destruct (audit_dfs_nested_finish cb v st) as [next events]; cbn in Hfinish |- *.
      constructor; [exact I|]. apply Forall_app; split; [exact Hfinish|repeat constructor].
    + destruct (audit_dfs_target_model cb edge) as [target target_body].
      destruct (audit_dfs_nested_get cb target blocked) as [blocked_value blocked_body].
      destruct (audit_dfs_nested_get cb target (DfsState.seen st)) as [seen_value seen_body].
      destruct blocked_value, seen_value; cbn.
      all: try (repeat constructor; fail).
      destruct (audit_dfs_nested_get cb target (out_index p)) as [outgoing outgoing_body].
      pose proof (audit_dfs_discover_successors cb target (Some edge) st) as Hdiscover.
      destruct (audit_dfs_nested_discover cb target (Some edge) st) as [next events].
      cbn in Hdiscover |- *.
      repeat constructor; apply Forall_app; split; [exact Hdiscover|repeat constructor].
Qed.

(** Both halves of a binary-fuel run and its optional last step preserve clock correspondence. *)
Lemma audit_dfs_run_successors {V E B} {EV} {g : Graph.t V E}
    (p : prepared EV g)
    (cb : audit_dfs_callback_model V E (audit_graph_callback_capture V E B)) blocked fuel work :
    Forall audit_dfs_source_successor_event
      (snd (audit_dfs_nested_run p cb blocked fuel work)).
Proof.
  revert work; induction fuel as [fuel IH|fuel IH|]; intro work;
    destruct work as [stack st], stack as [|frame stack]; cbn [audit_dfs_nested_run].
  - repeat constructor.
  - cbn [audit_dfs_nested_run fst].
    specialize (IH (frame :: stack, st)) as Hfirst.
    destruct (audit_dfs_nested_run p cb blocked fuel (frame :: stack, st))
      as [middle first] eqn:Hfirst_run; cbn in Hfirst |- *.
    specialize (IH middle) as Hsecond.
    destruct (audit_dfs_nested_run p cb blocked fuel middle) as [last second] eqn:Hsecond_run;
      cbn in Hsecond |- *.
    pose proof (audit_dfs_step_successors p cb blocked last) as Hstep.
    destruct (audit_dfs_nested_step p cb blocked last) as [result events] eqn:Hstep_run;
      cbn in Hstep |- *.
    change (Forall audit_dfs_source_successor_event
      (snd (let '(middle, first) := audit_dfs_nested_run p cb blocked fuel (frame :: stack, st) in
        let '(last, second) := audit_dfs_nested_run p cb blocked fuel middle in
        let '(result, events) := audit_dfs_nested_step p cb blocked last in
        (result, (AuditDfsFullCase 7, []) :: first ++ second ++ events)))).
    rewrite Hfirst_run, Hsecond_run, Hstep_run; cbn.
    constructor; [exact I|]. apply Forall_app; split; [exact Hfirst|].
    apply Forall_app; split; assumption.
  - repeat constructor.
  - cbn [audit_dfs_nested_run fst].
    specialize (IH (frame :: stack, st)) as Hfirst.
    destruct (audit_dfs_nested_run p cb blocked fuel (frame :: stack, st))
      as [middle first] eqn:Hfirst_run; cbn in Hfirst |- *.
    specialize (IH middle) as Hsecond.
    destruct (audit_dfs_nested_run p cb blocked fuel middle) as [result second] eqn:Hsecond_run;
      cbn in Hsecond |- *.
    change (Forall audit_dfs_source_successor_event
      (snd (let '(middle, first) := audit_dfs_nested_run p cb blocked fuel (frame :: stack, st) in
        let '(result, second) := audit_dfs_nested_run p cb blocked fuel middle in
        (result, (AuditDfsFullCase 6, []) :: first ++ second)))).
    rewrite Hfirst_run, Hsecond_run; cbn.
    constructor; [exact I|]. apply Forall_app; split; assumption.
  - repeat constructor.
  - cbn [audit_dfs_nested_run fst].
    pose proof (audit_dfs_step_successors p cb blocked (frame :: stack, st)) as Hstep.
    destruct (audit_dfs_nested_step p cb blocked (frame :: stack, st))
      as [result events] eqn:Hstep_run.
    cbn in Hstep.
    change (Forall audit_dfs_source_successor_event
      (snd (let '(result, events) := audit_dfs_nested_step p cb blocked (frame :: stack, st) in
        (result, (AuditDfsFullCase 5, []) :: events)))).
    rewrite Hstep_run; cbn; constructor; [exact I|exact Hstep].
Qed.

(** A root's discovery and binary-fuel run preserve clock correspondence. *)
Lemma audit_dfs_root_successors {V E B} {EV} {g : Graph.t V E}
    (p : prepared EV g)
    (cb : audit_dfs_callback_model V E (audit_graph_callback_capture V E B)) blocked st v :
    Forall audit_dfs_source_successor_event (snd (audit_dfs_nested_root p cb blocked st v)).
Proof.
  unfold audit_dfs_nested_root.
  destruct (audit_dfs_nested_get cb v blocked) as [blocked_value blocked_body].
  destruct (audit_dfs_nested_get cb v (DfsState.seen st)) as [seen_value seen_body].
  destruct blocked_value, seen_value; cbn.
  all: try (repeat constructor; fail).
  destruct (audit_dfs_nested_get cb v (out_index p)) as [outgoing outgoing_body].
  pose proof (audit_dfs_discover_successors cb v None st) as Hdiscover.
  destruct (audit_dfs_nested_discover cb v None st)
    as [discovered details] eqn:Hdiscover_run; cbn in Hdiscover |- *.
  pose proof (audit_dfs_run_successors p cb blocked (fuel p)
    ([(v,
      match outgoing with
      | Some xs => xs
      | None => []
      end)], discovered)) as Hrun.
  destruct (audit_dfs_nested_run p cb blocked (fuel p)
    ([(v,
      match outgoing with
      | Some xs => xs
      | None => []
      end)], discovered)) as [result events] eqn:Hrun_eq.
  cbn in Hrun |- *.
  change (Forall audit_dfs_source_successor_event
    (snd (let '(discovered, details) := audit_dfs_nested_discover cb v None st in
      let '(result, events) := audit_dfs_nested_run p cb blocked (fuel p)
        ([(v,
          match outgoing with
          | Some xs => xs
          | None => []
          end)], discovered) in
      (snd result, [(AuditDfsFullMember v blocked false, blocked_body);
        (AuditDfsFullMember v (DfsState.seen st) false, seen_body); (AuditDfsFullCase 9, []);
        (AuditDfsFullSuccessors v (out_index p) outgoing, outgoing_body)] ++ details ++
        [(AuditDfsFullDiscover v None st discovered, [])] ++ events)))).
  rewrite Hdiscover_run, Hrun_eq; cbn.
  repeat constructor; apply Forall_app; split; [exact Hdiscover|].
  constructor; [exact I|exact Hrun].
Qed.

(** The fold over roots preserves clock correspondence in every emitted event. *)
Lemma audit_dfs_roots_successors {V E B} {EV} {g : Graph.t V E}
    (p : prepared EV g)
    (cb : audit_dfs_callback_model V E (audit_graph_callback_capture V E B)) blocked roots st :
    Forall audit_dfs_source_successor_event (snd (audit_dfs_nested_roots p cb blocked roots st)).
Proof.
  revert st; induction roots as [|root roots IH]; intro st; cbn [audit_dfs_nested_roots].
  - repeat constructor.
  - pose proof (audit_dfs_root_successors p cb blocked st root) as Hroot.
    destruct (audit_dfs_nested_root p cb blocked st root) as [next here] eqn:Hroot_run.
    cbn in Hroot.
    specialize (IH next).
    destruct (audit_dfs_nested_roots p cb blocked roots next) as [result later] eqn:Hroots_run.
    cbn in IH.
    constructor; [exact I|]. apply Forall_app; split; assumption.
Qed.

(** With erasing callbacks, every captured DFS clock event agrees with positive successor. *)
Theorem audit_dfs_source_successor_correspondence_holds :
    audit_dfs_source_successor_correspondence_statement.
Proof.
  unfold audit_dfs_source_successor_correspondence_statement.
  intros V E B EV g p cb blocked roots Hcallbacks.
  unfold audit_dfs_source_counted.
  pose proof (audit_dfs_roots_successors p (audit_graph_capture_callbacks cb) blocked roots
    dfs_initial) as Hroots.
  destruct (audit_dfs_nested_roots p (audit_graph_capture_callbacks cb) blocked roots dfs_initial)
    as [st events]; cbn in Hroots |- *.
  apply Forall_app; split; [exact Hroots|repeat constructor].
Qed.

(** * Counted traversal erasure *)

(** Erasing one counted transition yields the actual DFS step. *)
Lemma audit_dfs_step_erases {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked work :
    fst (audit_dfs_step_counted p blocked work) = dfs_step p blocked work.
Proof.
  destruct work as [stack st], stack as [|[v edges] rest]; cbn [audit_dfs_step_counted dfs_step].
  - reflexivity.
  - destruct edges as [|edge edges]; [reflexivity|].
    destruct (FinSet.mem EV (Graph.target g edge) blocked ||
      FinSet.mem EV (Graph.target g edge) (DfsState.seen st)); [reflexivity|].
    unfold succ_edges; reflexivity.
Qed.

(** The counted binary traversal erases to the source traversal at every intermediate worklist. *)
Lemma audit_dfs_run_erases {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked fuel work :
    fst (audit_dfs_run_counted p blocked fuel work) = dfs_run p blocked fuel work.
Proof.
  revert work; induction fuel as [fuel IH|fuel IH|]; intros [stack st];
    destruct stack as [|frame stack]; [reflexivity| |reflexivity| |reflexivity|].
  - change (fst (let '(middle, first) :=
        audit_dfs_run_counted p blocked fuel (frame :: stack, st) in
      let '(last, second) := audit_dfs_run_counted p blocked fuel middle in
      let '(result, events) := audit_dfs_step_counted p blocked last in
      (result, AuditDfsCase 7 :: first ++ second ++ events)) =
        dfs_step p blocked (dfs_run p blocked fuel
        (dfs_run p blocked fuel (frame :: stack, st)))).
    pose proof (IH (frame :: stack, st)) as Hfirst.
    destruct (audit_dfs_run_counted p blocked fuel (frame :: stack, st))
      as [middle first]; cbn in Hfirst |- *.
    pose proof (IH middle) as Hsecond.
    destruct (audit_dfs_run_counted p blocked fuel middle) as [last second]; cbn in Hsecond |- *.
    pose proof (audit_dfs_step_erases p blocked last) as Hstep.
    destruct (audit_dfs_step_counted p blocked last) as [result events]; cbn in Hstep |- *.
    cbn [dfs_run fst]; now rewrite <- Hfirst, <- Hsecond, <- Hstep.
  - change (fst (let '(middle, first) :=
        audit_dfs_run_counted p blocked fuel (frame :: stack, st) in
      let '(result, second) := audit_dfs_run_counted p blocked fuel middle in
      (result, AuditDfsCase 6 :: first ++ second)) = dfs_run p blocked fuel
        (dfs_run p blocked fuel (frame :: stack, st))).
    pose proof (IH (frame :: stack, st)) as Hfirst.
    destruct (audit_dfs_run_counted p blocked fuel (frame :: stack, st))
      as [middle first]; cbn in Hfirst |- *.
    pose proof (IH middle) as Hsecond.
    destruct (audit_dfs_run_counted p blocked fuel middle) as [result events]; cbn in Hsecond |- *.
    cbn [dfs_run fst]; now rewrite <- Hfirst, <- Hsecond.
  - change (fst (let '(result, events) :=
      audit_dfs_step_counted p blocked (frame :: stack, st) in
      (result, AuditDfsCase 5 :: events)) = dfs_step p blocked (frame :: stack, st)).
    pose proof (audit_dfs_step_erases p blocked (frame :: stack, st)) as Hstep.
    destruct (audit_dfs_step_counted p blocked (frame :: stack, st)) as [result events].
    cbn [dfs_run fst] in Hstep |- *; exact Hstep.
Qed.

(** A counted root returns the state produced by the corresponding source root. *)
Lemma audit_dfs_root_erases {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked st v :
    fst (audit_dfs_root_counted p blocked st v) = dfs_root p blocked st v.
Proof.
  unfold audit_dfs_root_counted, dfs_root.
  destruct (FinSet.mem EV v blocked || FinSet.mem EV v (DfsState.seen st)); [reflexivity|].
  unfold succ_edges, index_edges.
  pose proof (audit_dfs_run_erases p blocked (fuel p)
    ([(v,
      match Map.get EV v (out_index p) with
      | Some xs => xs
      | None => []
      end)],
      dfs_discover EV v None st)) as Hrun.
  destruct (audit_dfs_run_counted p blocked (fuel p)
    ([(v,
      match Map.get EV v (out_index p) with
      | Some xs => xs
      | None => []
      end)],
      dfs_discover EV v None st)) as [result events]; cbn in Hrun |- *.
  now rewrite <- Hrun.
Qed.

(** Counted root processing returns the source fold's final state. *)
Lemma audit_dfs_roots_erase {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked roots st :
    fst (audit_dfs_roots_counted p blocked roots st) = fold_left (dfs_root p blocked) roots st.
Proof.
  revert st; induction roots as [|root roots IH]; intro st; cbn [audit_dfs_roots_counted fold_left].
  - reflexivity.
  - pose proof (audit_dfs_root_erases p blocked st root) as Hroot.
    destruct (audit_dfs_root_counted p blocked st root) as [next here]; cbn in Hroot |- *.
    rewrite <- Hroot; specialize (IH next).
    destruct (audit_dfs_roots_counted p blocked roots next); exact IH.
Qed.

(** Erasing the counted receipt yields the source DFS result, including output order. *)
Lemma audit_dfs_counted_erases {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked roots :
    fst (audit_dfs_counted p blocked roots) = dfs p blocked roots.
Proof.
  unfold audit_dfs_counted, dfs.
  pose proof (audit_dfs_roots_erase p blocked roots dfs_initial) as Hroots.
  destruct (audit_dfs_roots_counted p blocked roots dfs_initial) as [st events]; cbn in Hroots |- *.
  rewrite <- Hroots, <- !rev_alt; reflexivity.
Qed.

(** A counted transition emits no more than six events. *)
Lemma audit_dfs_step_count_bound {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked work :
    length (snd (audit_dfs_step_counted p blocked work)) <= 6.
Proof.
  destruct work as [stack st], stack as [|[v edges] rest]; cbn [audit_dfs_step_counted].
  - cbn; lia.
  - destruct edges as [|edge edges]; cbn; [lia|].
    destruct (FinSet.mem EV (Graph.target g edge) blocked ||
      FinSet.mem EV (Graph.target g edge) (DfsState.seen st)); cbn; lia.
Qed.

(** Binary fuel bounds all events emitted by a counted DFS run. *)
Lemma audit_dfs_run_count_bound {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked fuel work :
    length (snd (audit_dfs_run_counted p blocked fuel work)) <= 10 * Pos.to_nat fuel - 1.
Proof.
  revert work; induction fuel as [fuel IH|fuel IH|]; intros [stack st];
    destruct stack as [|frame stack].
  - cbn [audit_dfs_run_counted]; cbn; lia.
  - change (length (snd (let '(middle, first) :=
        audit_dfs_run_counted p blocked fuel (frame :: stack, st) in
      let '(last, second) := audit_dfs_run_counted p blocked fuel middle in
      let '(result, events) := audit_dfs_step_counted p blocked last in
      (result, AuditDfsCase 7 :: first ++ second ++ events))) <= 10 * Pos.to_nat (xI fuel) - 1).
    pose proof (IH (frame :: stack, st)) as Hfirst.
    destruct (audit_dfs_run_counted p blocked fuel (frame :: stack, st))
      as [middle first]; cbn in Hfirst |- *.
    pose proof (IH middle) as Hsecond.
    destruct (audit_dfs_run_counted p blocked fuel middle) as [last second]; cbn in Hsecond |- *.
    pose proof (audit_dfs_step_count_bound p blocked last) as Hstep.
    destruct (audit_dfs_step_counted p blocked last) as [result events]; cbn in Hstep |- *.
    rewrite !length_app; cbn; rewrite Pos2Nat.inj_xI; pose proof (Pos2Nat.is_pos fuel); lia.
  - cbn [audit_dfs_run_counted]; cbn; lia.
  - change (length (snd (let '(middle, first) :=
        audit_dfs_run_counted p blocked fuel (frame :: stack, st) in
      let '(result, second) := audit_dfs_run_counted p blocked fuel middle in
      (result, AuditDfsCase 6 :: first ++ second))) <= 10 * Pos.to_nat (xO fuel) - 1).
    pose proof (IH (frame :: stack, st)) as Hfirst.
    destruct (audit_dfs_run_counted p blocked fuel (frame :: stack, st))
      as [middle first]; cbn in Hfirst |- *.
    pose proof (IH middle) as Hsecond.
    destruct (audit_dfs_run_counted p blocked fuel middle) as [result second]; cbn in Hsecond |- *.
    rewrite length_app; cbn; rewrite Pos2Nat.inj_xO; pose proof (Pos2Nat.is_pos fuel); lia.
  - cbn [audit_dfs_run_counted]; cbn; lia.
  - change (length (snd (let '(result, events) :=
        audit_dfs_step_counted p blocked (frame :: stack, st) in
      (result, AuditDfsCase 5 :: events))) <= 10 * Pos.to_nat xH - 1).
    pose proof (audit_dfs_step_count_bound p blocked (frame :: stack, st)) as Hstep.
    destruct (audit_dfs_step_counted p blocked (frame :: stack, st)); cbn in Hstep |- *; lia.
Qed.

(** A root emits its membership checks and, if fresh, one fuel-bounded traversal. *)
Lemma audit_dfs_root_count_bound {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked st v :
    length (snd (audit_dfs_root_counted p blocked st v)) <= 10 * Pos.to_nat (fuel p) + 5.
Proof.
  unfold audit_dfs_root_counted.
  destruct (FinSet.mem EV v blocked || FinSet.mem EV v (DfsState.seen st)); cbn.
  - lia.
  - pose proof (audit_dfs_run_count_bound p blocked (fuel p)
      ([(v,
        match Map.get EV v (out_index p) with
        | Some xs => xs
        | None => []
        end)],
        dfs_discover EV v None st)) as Hrun.
    destruct (audit_dfs_run_counted p blocked (fuel p)
      ([(v,
        match Map.get EV v (out_index p) with
        | Some xs => xs
        | None => []
        end)],
        dfs_discover EV v None st)) as [result events]; cbn in Hrun |- *; lia.
Qed.

(** The root fold's trace length is bounded by its number of roots and prepared fuel. *)
Lemma audit_dfs_roots_count_bound {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked roots st :
    length (snd (audit_dfs_roots_counted p blocked roots st)) <=
      1 + length roots * (10 * Pos.to_nat (fuel p) + 6).
Proof.
  revert st; induction roots as [|root roots IH]; intro st; cbn [audit_dfs_roots_counted].
  - cbn; lia.
  - pose proof (audit_dfs_root_count_bound p blocked st root) as Hroot.
    destruct (audit_dfs_root_counted p blocked st root) as [next here]; cbn in Hroot |- *.
    specialize (IH next).
    destruct (audit_dfs_roots_counted p blocked roots next) as [result later]; cbn in IH |- *.
    rewrite length_app; cbn; nia.
Qed.

(** The complete counted receipt meets the public original-input event bound. *)
Lemma audit_dfs_counted_event_bound {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked roots :
    length (snd (audit_dfs_counted p blocked roots)) <= audit_dfs_input_event_bound p roots.
Proof.
  unfold audit_dfs_counted, audit_dfs_input_event_bound.
  pose proof (audit_dfs_roots_count_bound p blocked roots dfs_initial) as Hroots.
  destruct (audit_dfs_roots_counted p blocked roots dfs_initial) as [st events]; cbn in Hroots |- *.
  nia.
Qed.

(** A full step emits at most ten events, including discovery and finish details. *)
Lemma audit_dfs_full_step_count_bound {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked work :
    length (snd (audit_dfs_full_step_counted p blocked work)) <= 10.
Proof.
  destruct work as [stack st], stack as [|[v edges] rest]; cbn [audit_dfs_full_step_counted].
  - cbn; lia.
  - destruct edges as [|edge edges].
    + cbn [audit_dfs_finish_counted]; cbn; lia.
    + destruct (FinSet.mem EV (Graph.target g edge) blocked ||
        FinSet.mem EV (Graph.target g edge) (DfsState.seen st)); cbn.
      * lia.
      * cbn [audit_dfs_discover_counted]; cbn; lia.
Qed.

(** Binary fuel bounds all events emitted by a full DFS run. *)
Lemma audit_dfs_full_run_count_bound {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked fuel work :
    length (snd (audit_dfs_full_run_counted p blocked fuel work)) <= 14 * Pos.to_nat fuel - 1.
Proof.
  revert work; induction fuel as [fuel IH|fuel IH|]; intros [stack st];
    destruct stack as [|frame stack].
  - cbn [audit_dfs_full_run_counted]; cbn; lia.
  - change (length (snd (let '(middle, first) :=
        audit_dfs_full_run_counted p blocked fuel (frame :: stack, st) in
      let '(last, second) := audit_dfs_full_run_counted p blocked fuel middle in
      let '(result, events) := audit_dfs_full_step_counted p blocked last in
      (result, AuditDfsFullCase 7 :: first ++ second ++ events))) <= 14 * Pos.to_nat (xI fuel) - 1).
    pose proof (IH (frame :: stack, st)) as Hfirst.
    destruct (audit_dfs_full_run_counted p blocked fuel (frame :: stack, st))
      as [middle first]; cbn in Hfirst |- *.
    pose proof (IH middle) as Hsecond.
    destruct (audit_dfs_full_run_counted p blocked fuel middle) as [last second];
      cbn in Hsecond |- *.
    pose proof (audit_dfs_full_step_count_bound p blocked last) as Hstep.
    destruct (audit_dfs_full_step_counted p blocked last) as [result events]; cbn in Hstep |- *.
    rewrite !length_app; cbn; rewrite Pos2Nat.inj_xI; pose proof (Pos2Nat.is_pos fuel); lia.
  - cbn [audit_dfs_full_run_counted]; cbn; lia.
  - change (length (snd (let '(middle, first) :=
        audit_dfs_full_run_counted p blocked fuel (frame :: stack, st) in
      let '(result, second) := audit_dfs_full_run_counted p blocked fuel middle in
      (result, AuditDfsFullCase 6 :: first ++ second))) <= 14 * Pos.to_nat (xO fuel) - 1).
    pose proof (IH (frame :: stack, st)) as Hfirst.
    destruct (audit_dfs_full_run_counted p blocked fuel (frame :: stack, st))
      as [middle first]; cbn in Hfirst |- *.
    pose proof (IH middle) as Hsecond.
    destruct (audit_dfs_full_run_counted p blocked fuel middle) as [result second];
      cbn in Hsecond |- *.
    rewrite length_app; cbn; rewrite Pos2Nat.inj_xO; pose proof (Pos2Nat.is_pos fuel); lia.
  - cbn [audit_dfs_full_run_counted]; cbn; lia.
  - change (length (snd (let '(result, events) :=
        audit_dfs_full_step_counted p blocked (frame :: stack, st) in
      (result, AuditDfsFullCase 5 :: events))) <= 14 * Pos.to_nat xH - 1).
    pose proof (audit_dfs_full_step_count_bound p blocked (frame :: stack, st)) as Hstep.
    destruct (audit_dfs_full_step_counted p blocked (frame :: stack, st)); cbn in Hstep |- *; lia.
Qed.

(** One full root emits a bounded prefix and at most one binary-fuel run. *)
Lemma audit_dfs_full_root_count_bound {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked st v :
    length (snd (audit_dfs_full_root_counted p blocked st v)) <= 14 * Pos.to_nat (fuel p) + 10.
Proof.
  unfold audit_dfs_full_root_counted.
  destruct (FinSet.mem EV v blocked || FinSet.mem EV v (DfsState.seen st)); cbn.
  - lia.
  - cbn [audit_dfs_discover_counted].
    pose proof (audit_dfs_full_run_count_bound p blocked (fuel p)
      ([(v, index_edges EV (out_index p) v)], dfs_discover EV v None st)) as Hrun.
    unfold index_edges, dfs_discover in Hrun.
    destruct (audit_dfs_full_run_counted p blocked (fuel p)
      ([(v, index_edges EV (out_index p) v)], dfs_discover EV v None st))
      as [result events] eqn:Hrun_eq.
    unfold index_edges, dfs_discover in Hrun_eq.
    rewrite Hrun_eq in Hrun; cbn in Hrun.
    rewrite Hrun_eq; cbn; lia.
Qed.

(** The full root fold's trace length is bounded by roots and prepared fuel. *)
Lemma audit_dfs_full_roots_count_bound {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked roots st :
    length (snd (audit_dfs_full_roots_counted p blocked roots st)) <=
      1 + length roots * (14 * Pos.to_nat (fuel p) + 11).
Proof.
  revert st; induction roots as [|root roots IH]; intro st; cbn [audit_dfs_full_roots_counted].
  - cbn; lia.
  - pose proof (audit_dfs_full_root_count_bound p blocked st root) as Hroot.
    destruct (audit_dfs_full_root_counted p blocked st root) as [next here]; cbn in Hroot |- *.
    specialize (IH next).
    destruct (audit_dfs_full_roots_counted p blocked roots next) as [result later]; cbn in IH |- *.
    rewrite length_app; cbn; nia.
Qed.

(** Full DFS's output event and traversal meet the original-input event bound. *)
Lemma audit_dfs_full_counted_event_bound {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked roots :
    length (snd (audit_dfs_full_counted p blocked roots)) <=
      audit_dfs_full_input_event_bound p roots.
Proof.
  unfold audit_dfs_full_counted, audit_dfs_full_input_event_bound.
  pose proof (audit_dfs_full_roots_count_bound p blocked roots dfs_initial) as Hroots.
  destruct (audit_dfs_full_roots_counted p blocked roots dfs_initial) as [st events].
  cbn in Hroots |- *; rewrite length_app; cbn; nia.
Qed.

(** A full counted transition returns the original DFS step's worklist and state. *)
Lemma audit_dfs_full_step_erases {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked work :
    fst (audit_dfs_full_step_counted p blocked work) = dfs_step p blocked work.
Proof.
  destruct work as [stack st], stack as [|[v edges] rest];
    cbn [audit_dfs_full_step_counted dfs_step].
  - reflexivity.
  - destruct edges as [|edge edges].
    + cbn [audit_dfs_finish_counted dfs_finish]; reflexivity.
    + destruct (FinSet.mem EV (Graph.target g edge) blocked ||
        FinSet.mem EV (Graph.target g edge) (DfsState.seen st)); [reflexivity|].
      cbn [audit_dfs_discover_counted dfs_discover]; unfold succ_edges; reflexivity.
Qed.

(** The full binary traversal erases to the source traversal at every intermediate worklist. *)
Lemma audit_dfs_full_run_erases {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked fuel work :
    fst (audit_dfs_full_run_counted p blocked fuel work) = dfs_run p blocked fuel work.
Proof.
  revert work; induction fuel as [fuel IH|fuel IH|]; intros [stack st];
    destruct stack as [|frame stack]; [reflexivity| |reflexivity| |reflexivity|].
  - change (fst (let '(middle, first) :=
        audit_dfs_full_run_counted p blocked fuel (frame :: stack, st) in
      let '(last, second) := audit_dfs_full_run_counted p blocked fuel middle in
      let '(result, events) := audit_dfs_full_step_counted p blocked last in
      (result, AuditDfsFullCase 7 :: first ++ second ++ events)) =
        dfs_step p blocked (dfs_run p blocked fuel
        (dfs_run p blocked fuel (frame :: stack, st)))).
    pose proof (IH (frame :: stack, st)) as Hfirst.
    destruct (audit_dfs_full_run_counted p blocked fuel (frame :: stack, st))
      as [middle first]; cbn in Hfirst |- *.
    pose proof (IH middle) as Hsecond.
    destruct (audit_dfs_full_run_counted p blocked fuel middle) as [last second];
      cbn in Hsecond |- *.
    pose proof (audit_dfs_full_step_erases p blocked last) as Hstep.
    destruct (audit_dfs_full_step_counted p blocked last) as [result events]; cbn in Hstep |- *.
    cbn [dfs_run fst]; now rewrite <- Hfirst, <- Hsecond, <- Hstep.
  - change (fst (let '(middle, first) :=
        audit_dfs_full_run_counted p blocked fuel (frame :: stack, st) in
      let '(result, second) := audit_dfs_full_run_counted p blocked fuel middle in
      (result, AuditDfsFullCase 6 :: first ++ second)) = dfs_run p blocked fuel
        (dfs_run p blocked fuel (frame :: stack, st))).
    pose proof (IH (frame :: stack, st)) as Hfirst.
    destruct (audit_dfs_full_run_counted p blocked fuel (frame :: stack, st))
      as [middle first]; cbn in Hfirst |- *.
    pose proof (IH middle) as Hsecond.
    destruct (audit_dfs_full_run_counted p blocked fuel middle) as [result events];
      cbn in Hsecond |- *.
    cbn [dfs_run fst]; now rewrite <- Hfirst, <- Hsecond.
  - change (fst (let '(result, events) :=
      audit_dfs_full_step_counted p blocked (frame :: stack, st) in
      (result, AuditDfsFullCase 5 :: events)) = dfs_step p blocked (frame :: stack, st)).
    pose proof (audit_dfs_full_step_erases p blocked (frame :: stack, st)) as Hstep.
    destruct (audit_dfs_full_step_counted p blocked (frame :: stack, st)) as [result events].
    cbn [dfs_run fst] in Hstep |- *; exact Hstep.
Qed.

(** Full counted root processing returns the source root's state. *)
Lemma audit_dfs_full_root_erases {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked st v :
    fst (audit_dfs_full_root_counted p blocked st v) = dfs_root p blocked st v.
Proof.
  unfold audit_dfs_full_root_counted, dfs_root.
  destruct (FinSet.mem EV v blocked || FinSet.mem EV v (DfsState.seen st)); [reflexivity|].
  unfold succ_edges, index_edges.
  cbn [audit_dfs_discover_counted].
  pose proof (audit_dfs_full_run_erases p blocked (fuel p)
    ([(v, index_edges EV (out_index p) v)], dfs_discover EV v None st)) as Hrun.
  destruct (audit_dfs_full_run_counted p blocked (fuel p)
    ([(v, index_edges EV (out_index p) v)], dfs_discover EV v None st))
    as [result events] eqn:Hrun_eq.
  unfold index_edges, dfs_discover in Hrun_eq, Hrun.
  cbn in Hrun.
  rewrite Hrun_eq.
  change (snd result = snd (dfs_run p blocked (fuel p)
    ([(v, index_edges EV (out_index p) v)], dfs_discover EV v None st))).
  unfold index_edges, dfs_discover; now rewrite <- Hrun.
Qed.

(** Full counted root processing returns the source fold's final state. *)
Lemma audit_dfs_full_roots_erase {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked roots st :
    fst (audit_dfs_full_roots_counted p blocked roots st) = fold_left (dfs_root p blocked) roots st.
Proof.
  revert st; induction roots as [|root roots IH]; intro st;
    cbn [audit_dfs_full_roots_counted fold_left].
  - reflexivity.
  - pose proof (audit_dfs_full_root_erases p blocked st root) as Hroot.
    destruct (audit_dfs_full_root_counted p blocked st root) as [next here]; cbn in Hroot |- *.
    rewrite <- Hroot; specialize (IH next).
    destruct (audit_dfs_full_roots_counted p blocked roots next); exact IH.
Qed.

(** Full counted DFS retains the source result, including its output ordering. *)
Lemma audit_dfs_full_counted_erases {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked roots :
    fst (audit_dfs_full_counted p blocked roots) = dfs p blocked roots.
Proof.
  unfold audit_dfs_full_counted, dfs.
  pose proof (audit_dfs_full_roots_erase p blocked roots dfs_initial) as Hroots.
  destruct (audit_dfs_full_roots_counted p blocked roots dfs_initial) as [st events].
  cbn in Hroots |- *; rewrite <- Hroots, <- !rev_alt; reflexivity.
Qed.

(** * Nested callback erasure *)

(** An erasing encoder makes nested discovery match every full discovery detail. *)
Lemma audit_dfs_nested_discover_erases {V E B} (EV : encoding V) (g : Graph.t V E)
    (cb : audit_dfs_callback_model V E B) v via st :
    audit_dfs_callbacks_erase EV g cb ->
    (fst (audit_dfs_nested_discover cb v via st),
      map fst (snd (audit_dfs_nested_discover cb v via st))) =
      let '(next, details) := audit_dfs_discover_counted EV v via st in
      (next, map AuditDfsFullDetail details).
Proof.
  intros [_ Hencode].
  specialize (Hencode v).
  destruct (audit_dfs_encode_model cb v) as [code body] eqn:Hcode; cbn in Hencode; subst code.
  destruct via as [edge|];
    unfold audit_dfs_nested_discover, audit_dfs_nested_set, audit_dfs_discover_counted;
    rewrite Hcode; reflexivity.
Qed.

(** An erasing encoder makes nested finishing match every full finish detail. *)
Lemma audit_dfs_nested_finish_erases {V E B} (EV : encoding V) (g : Graph.t V E)
    (cb : audit_dfs_callback_model V E B) v st :
    audit_dfs_callbacks_erase EV g cb ->
    (fst (audit_dfs_nested_finish cb v st),
      map fst (snd (audit_dfs_nested_finish cb v st))) =
      let '(next, details) := audit_dfs_finish_counted EV v st in
      (next, map AuditDfsFullDetail details).
Proof.
  intros [_ Hencode].
  specialize (Hencode v).
  destruct (audit_dfs_encode_model cb v) as [code body] eqn:Hcode; cbn in Hencode; subst code.
  unfold audit_dfs_nested_finish, audit_dfs_nested_set, audit_dfs_finish_counted.
  rewrite Hcode; reflexivity.
Qed.

(** With erasing callbacks, a nested step retains the full result and ordered events. *)
Lemma audit_dfs_nested_step_erases {V E B} {EV} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) blocked work :
    audit_dfs_callbacks_erase EV g cb ->
    (fst (audit_dfs_nested_step p cb blocked work),
      map fst (snd (audit_dfs_nested_step p cb blocked work))) =
      audit_dfs_full_step_counted p blocked work.
Proof.
  intro Hcallbacks.
  destruct work as [stack st], stack as [|[v edges] rest]; cbn [audit_dfs_nested_step
    audit_dfs_full_step_counted].
  - reflexivity.
  - destruct edges as [|edge edges].
    + pose proof (audit_dfs_nested_finish_erases EV g cb v st Hcallbacks) as Hfinish.
      destruct (audit_dfs_nested_finish cb v st) as [next details] eqn:Hnested.
      destruct (audit_dfs_finish_counted EV v st) as [next' details'] eqn:Hfull.
      cbn in Hfinish |- *; inversion Hfinish; subst next'.
      rewrite map_app; cbn.
      reflexivity.
    + pose proof Hcallbacks as [Htarget Hencode].
      specialize (Htarget edge).
      destruct (audit_dfs_target_model cb edge) as [target target_body] eqn:Hcall.
      cbn in Htarget; subst target.
      specialize (Hencode (Graph.target g edge)) as Hcode.
      destruct (audit_dfs_encode_model cb (Graph.target g edge)) as [code body] eqn:Hcallcode.
      cbn in Hcode; subst code.
      unfold audit_dfs_nested_get; rewrite Hcallcode.
      change (Map.code_get (encode EV (Graph.target g edge)) blocked) with
        (Map.get EV (Graph.target g edge) blocked).
      change (Map.code_get (encode EV (Graph.target g edge)) (DfsState.seen st)) with
        (Map.get EV (Graph.target g edge) (DfsState.seen st)).
      unfold FinSet.mem, Map.mem.
      destruct (Map.get EV (Graph.target g edge) blocked),
        (Map.get EV (Graph.target g edge) (DfsState.seen st)); cbn; try reflexivity.
      change (Map.code_get (encode EV (Graph.target g edge)) (out_index p)) with
        (Map.get EV (Graph.target g edge) (out_index p)).
      pose proof (audit_dfs_nested_discover_erases EV g cb (Graph.target g edge) (Some edge) st
        (Hcallbacks)) as Hdiscover.
      destruct (audit_dfs_nested_discover cb (Graph.target g edge) (Some edge) st)
        as [next details] eqn:Hnested.
      destruct (audit_dfs_discover_counted EV (Graph.target g edge) (Some edge) st)
        as [next' details'] eqn:Hfull.
      cbn in Hdiscover |- *.
      assert (Hdetails : map fst details = map AuditDfsFullDetail details')
        by (inversion Hdiscover; reflexivity).
      inversion Hdiscover; subst next'.
      cbn [audit_dfs_discover_counted] in Hfull.
      inversion Hfull; subst next details'.
      cbn in Hdetails; rewrite map_app; cbn.
      repeat f_equal; try reflexivity.
      apply (f_equal (fun xs => xs ++
        [AuditDfsFullDiscover (Graph.target g edge) (Some edge) st
          (dfs_discover EV (Graph.target g edge) (Some edge) st)])) in Hdetails.
      exact Hdetails.
Qed.

(** With erasing callbacks, a nested binary run retains the full result and event order. *)
Lemma audit_dfs_nested_run_erases {V E B} {EV} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) blocked fuel work :
    audit_dfs_callbacks_erase EV g cb ->
    (fst (audit_dfs_nested_run p cb blocked fuel work),
      map fst (snd (audit_dfs_nested_run p cb blocked fuel work))) =
      audit_dfs_full_run_counted p blocked fuel work.
Proof.
  intro Hcallbacks; revert work.
  induction fuel as [fuel IH|fuel IH|]; intros [stack st]; destruct stack as [|frame stack].
  - reflexivity.
  - change ((fst (let '(middle, first) :=
        audit_dfs_nested_run p cb blocked fuel (frame :: stack, st) in
        let '(last, second) := audit_dfs_nested_run p cb blocked fuel middle in
        let '(result, events) := audit_dfs_nested_step p cb blocked last in
        (result, (AuditDfsFullCase 7, []) :: first ++ second ++ events)),
      map fst (snd (let '(middle, first) :=
        audit_dfs_nested_run p cb blocked fuel (frame :: stack, st) in
        let '(last, second) := audit_dfs_nested_run p cb blocked fuel middle in
        let '(result, events) := audit_dfs_nested_step p cb blocked last in
        (result, (AuditDfsFullCase 7, []) :: first ++ second ++ events)))) =
      let '(middle, first) := audit_dfs_full_run_counted p blocked fuel (frame :: stack, st) in
      let '(last, second) := audit_dfs_full_run_counted p blocked fuel middle in
      let '(result, events) := audit_dfs_full_step_counted p blocked last in
      (result, AuditDfsFullCase 7 :: first ++ second ++ events)).
    pose proof (IH (frame :: stack, st)) as Hfirst.
    destruct (audit_dfs_nested_run p cb blocked fuel (frame :: stack, st))
      as [middle first]; cbn in Hfirst |- *.
    rewrite <- Hfirst; cbn.
    pose proof (IH middle) as Hsecond.
    destruct (audit_dfs_nested_run p cb blocked fuel middle) as [last second]; cbn in Hsecond |- *.
    rewrite <- Hsecond; cbn.
    pose proof (audit_dfs_nested_step_erases p cb blocked last Hcallbacks) as Hstep.
    destruct (audit_dfs_nested_step p cb blocked last) as [result events]; cbn in Hstep |- *.
    rewrite <- Hstep; cbn; rewrite !map_app; reflexivity.
  - reflexivity.
  - change ((fst (let '(middle, first) :=
        audit_dfs_nested_run p cb blocked fuel (frame :: stack, st) in
        let '(result, second) := audit_dfs_nested_run p cb blocked fuel middle in
        (result, (AuditDfsFullCase 6, []) :: first ++ second)),
      map fst (snd (let '(middle, first) :=
        audit_dfs_nested_run p cb blocked fuel (frame :: stack, st) in
        let '(result, second) := audit_dfs_nested_run p cb blocked fuel middle in
        (result, (AuditDfsFullCase 6, []) :: first ++ second)))) =
      let '(middle, first) := audit_dfs_full_run_counted p blocked fuel (frame :: stack, st) in
      let '(result, second) := audit_dfs_full_run_counted p blocked fuel middle in
      (result, AuditDfsFullCase 6 :: first ++ second)).
    pose proof (IH (frame :: stack, st)) as Hfirst.
    destruct (audit_dfs_nested_run p cb blocked fuel (frame :: stack, st))
      as [middle first]; cbn in Hfirst |- *.
    rewrite <- Hfirst; cbn.
    pose proof (IH middle) as Hsecond.
    destruct (audit_dfs_nested_run p cb blocked fuel middle) as [result second];
      cbn in Hsecond |- *.
    rewrite <- Hsecond; cbn; rewrite map_app; reflexivity.
  - reflexivity.
  - change ((fst (let '(result, events) :=
        audit_dfs_nested_step p cb blocked (frame :: stack, st) in
        (result, (AuditDfsFullCase 5, []) :: events)),
      map fst (snd (let '(result, events) :=
        audit_dfs_nested_step p cb blocked (frame :: stack, st) in
        (result, (AuditDfsFullCase 5, []) :: events)))) =
      let '(result, events) := audit_dfs_full_step_counted p blocked (frame :: stack, st) in
      (result, AuditDfsFullCase 5 :: events)).
    pose proof (audit_dfs_nested_step_erases p cb blocked (frame :: stack, st) Hcallbacks) as Hstep.
    destruct (audit_dfs_nested_step p cb blocked (frame :: stack, st)) as [result events].
    cbn in Hstep |- *; rewrite <- Hstep; reflexivity.
Qed.

(** With erasing callbacks, a nested root preserves the full root's state and event order. *)
Lemma audit_dfs_nested_root_erases {V E B} {EV} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) blocked st v :
    audit_dfs_callbacks_erase EV g cb ->
    (fst (audit_dfs_nested_root p cb blocked st v),
      map fst (snd (audit_dfs_nested_root p cb blocked st v))) =
      audit_dfs_full_root_counted p blocked st v.
Proof.
  intro Hcallbacks.
  pose proof Hcallbacks as [_ Hencode].
  specialize (Hencode v) as Hcode.
  destruct (audit_dfs_encode_model cb v) as [code body] eqn:Hcall.
  cbn in Hcode; subst code.
  unfold audit_dfs_nested_root, audit_dfs_full_root_counted, audit_dfs_nested_get.
  rewrite Hcall.
  change (Map.code_get (encode EV v) blocked) with (Map.get EV v blocked).
  change (Map.code_get (encode EV v) (DfsState.seen st)) with (Map.get EV v (DfsState.seen st)).
  unfold FinSet.mem, Map.mem.
  destruct (Map.get EV v blocked), (Map.get EV v (DfsState.seen st)); cbn; try reflexivity.
  change (Map.code_get (encode EV v) (out_index p)) with (Map.get EV v (out_index p)).
  pose proof (audit_dfs_nested_discover_erases EV g cb v None st Hcallbacks) as Hdiscover.
  destruct (audit_dfs_nested_discover cb v None st) as [next details] eqn:Hnested.
  destruct (audit_dfs_discover_counted EV v None st) as [next' details'] eqn:Hfull.
  cbn in Hdiscover |- *.
  assert (Hdetails : map fst details = map AuditDfsFullDetail details')
    by (inversion Hdiscover; reflexivity).
  inversion Hdiscover; subst next'.
  cbn [audit_dfs_discover_counted] in Hfull.
  inversion Hfull; subst next details'; cbn in Hdetails.
  pose proof (audit_dfs_nested_run_erases p cb blocked (fuel p)
    ([(v, index_edges EV (out_index p) v)], dfs_discover EV v None st) Hcallbacks) as Hrun.
  unfold index_edges in Hrun.
  destruct (audit_dfs_nested_run p cb blocked (fuel p)
    ([(v, index_edges EV (out_index p) v)], dfs_discover EV v None st))
    as [result events] eqn:Hrun_eq.
  unfold index_edges in Hrun_eq; rewrite Hrun_eq in Hrun; cbn in Hrun |- *.
  unfold dfs_discover in Hrun.
  rewrite <- Hrun; cbn; cbn.
  cbn [audit_dfs_nested_discover]; cbn in Hnested.
  rewrite Hnested.
  unfold dfs_discover in Hrun_eq; rewrite Hrun_eq.
  cbn; rewrite !map_app; cbn; repeat f_equal; try reflexivity.
  apply (f_equal (fun xs => xs ++
    AuditDfsFullDiscover v None st (dfs_discover EV v None st) :: map fst events)) in Hdetails.
  exact Hdetails.
Qed.

(** With erasing callbacks, nested roots preserve the full fold's state and event order. *)
Lemma audit_dfs_nested_roots_erase {V E B} {EV} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) blocked roots st :
    audit_dfs_callbacks_erase EV g cb ->
    (fst (audit_dfs_nested_roots p cb blocked roots st),
      map fst (snd (audit_dfs_nested_roots p cb blocked roots st))) =
      audit_dfs_full_roots_counted p blocked roots st.
Proof.
  intro Hcallbacks; revert st; induction roots as [|root roots IH]; intro st.
  - reflexivity.
  - cbn [audit_dfs_nested_roots audit_dfs_full_roots_counted].
    pose proof (audit_dfs_nested_root_erases p cb blocked st root Hcallbacks) as Hroot.
    destruct (audit_dfs_nested_root p cb blocked st root) as [next here]; cbn in Hroot |- *.
    rewrite <- Hroot; cbn.
    specialize (IH next).
    destruct (audit_dfs_nested_roots p cb blocked roots next) as [result later]; cbn in IH |- *.
    rewrite <- IH; cbn; rewrite map_app; reflexivity.
Qed.

(** With erasing callbacks, nested counted DFS has the full result and event sequence. *)
Lemma audit_dfs_nested_counted_erases {V E B} {EV} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) blocked roots :
    audit_dfs_callbacks_erase EV g cb ->
    (fst (audit_dfs_nested_counted p cb blocked roots),
      map fst (snd (audit_dfs_nested_counted p cb blocked roots))) =
      audit_dfs_full_counted p blocked roots.
Proof.
  intro Hcallbacks; unfold audit_dfs_nested_counted, audit_dfs_full_counted.
  pose proof (audit_dfs_nested_roots_erase p cb blocked roots dfs_initial Hcallbacks) as Hroots.
  destruct (audit_dfs_nested_roots p cb blocked roots dfs_initial) as [st events].
  cbn in Hroots |- *; rewrite <- Hroots; cbn; rewrite map_app; reflexivity.
Qed.

(** With erasing callbacks, captured source DFS has the full result and event sequence. *)
Lemma audit_dfs_source_erases {V E B} {EV} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) blocked roots :
    audit_dfs_callbacks_erase EV g cb ->
    (fst (audit_dfs_source_counted p cb blocked roots),
      map fst (snd (audit_dfs_source_counted p cb blocked roots))) =
      audit_dfs_full_counted p blocked roots.
Proof.
  intro Hcallbacks.
  pose proof (audit_graph_capture_callbacks_erases_holds V E B EV g cb Hcallbacks) as Hcapture.
  pose proof (audit_dfs_nested_counted_erases p (audit_graph_capture_callbacks cb) blocked roots
    Hcapture) as Hnested.
  unfold audit_dfs_nested_counted, audit_dfs_source_counted in *.
  destruct (audit_dfs_nested_roots p (audit_graph_capture_callbacks cb) blocked roots dfs_initial)
    as [st events]; cbn in Hnested |- *.
  rewrite <- !rev_alt; exact Hnested.
Qed.

(** With erasing callbacks, captured DFS returns the source result and meets the event bound. *)
Lemma audit_dfs_source_result_and_count {V E B} {EV} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) blocked roots :
    audit_dfs_callbacks_erase EV g cb ->
    fst (audit_dfs_source_counted p cb blocked roots) = dfs p blocked roots /\
    length (snd (audit_dfs_source_counted p cb blocked roots)) <=
      audit_dfs_full_input_event_bound p roots.
Proof.
  intro Hcallbacks.
  pose proof (audit_dfs_source_erases p cb blocked roots Hcallbacks) as Herase.
  pose proof (audit_dfs_full_counted_erases p blocked roots) as Hresult.
  pose proof (audit_dfs_full_counted_event_bound p blocked roots) as Hcount.
  destruct (audit_dfs_source_counted p cb blocked roots) as [result events]; cbn in Herase |- *.
  rewrite <- Herase in Hresult, Hcount; cbn in Hresult, Hcount.
  rewrite length_map in Hcount; auto.
Qed.

(** * Captured event shape *)

(** Discovery pairs each map update with the encoder capture for that same vertex. *)
Lemma audit_dfs_source_discover_wellformed {V E B} (cb : audit_dfs_callback_model V E B)
    v via st :
    Forall audit_dfs_source_event_wellformed
      (snd (audit_dfs_nested_discover (audit_graph_capture_callbacks cb) v via st)).
Proof.
  unfold audit_dfs_nested_discover, audit_dfs_nested_set, audit_graph_capture_callbacks; cbn.
  destruct (audit_dfs_encode_model cb v) as [code trace].
  destruct via; cbn; repeat constructor; cbn [audit_dfs_source_event_wellformed]; eauto.
Qed.

(** Finishing pairs its number-map update with the encoder capture for that vertex. *)
Lemma audit_dfs_source_finish_wellformed {V E B} (cb : audit_dfs_callback_model V E B) v st :
    Forall audit_dfs_source_event_wellformed
      (snd (audit_dfs_nested_finish (audit_graph_capture_callbacks cb) v st)).
Proof.
  unfold audit_dfs_nested_finish, audit_dfs_nested_set, audit_graph_capture_callbacks; cbn.
  destruct (audit_dfs_encode_model cb v) as [code trace].
  cbn; repeat constructor; cbn [audit_dfs_source_event_wellformed]; eauto.
Qed.

(** Every captured step attaches the matching target or encoder call to its event. *)
Lemma audit_dfs_source_step_wellformed {V E B} {EV} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) blocked work :
    Forall audit_dfs_source_event_wellformed
      (snd (audit_dfs_nested_step p (audit_graph_capture_callbacks cb) blocked work)).
Proof.
  destruct work as [stack st], stack as [|[v edges] rest]; cbn [audit_dfs_nested_step].
  - repeat constructor; reflexivity.
  - destruct edges as [|edge edges].
    + pose proof (audit_dfs_source_finish_wellformed cb v st) as Hfinish.
      destruct (audit_dfs_nested_finish (audit_graph_capture_callbacks cb) v st)
        as [next details] eqn:Hdiscover_run.
      cbn in Hfinish |- *; constructor; [reflexivity|].
      apply Forall_app; split; [exact Hfinish|repeat constructor; reflexivity].
    + unfold audit_graph_capture_callbacks at 1; cbn.
      destruct (audit_dfs_target_model cb edge) as [target target_body].
      unfold audit_dfs_nested_get, audit_graph_capture_callbacks; cbn.
      destruct (audit_dfs_encode_model cb target) as [code body].
      destruct (Map.code_get code blocked), (Map.code_get code (DfsState.seen st)); cbn;
        try (repeat constructor; cbn [audit_dfs_source_event_wellformed]; eauto; fail).
      pose proof (audit_dfs_source_discover_wellformed cb target (Some edge) st) as Hdiscover.
      destruct (audit_dfs_nested_discover (audit_graph_capture_callbacks cb) target (Some edge) st)
        as [next details] eqn:Hdiscover_run.
      cbn in Hdiscover |- *.
      fold (audit_graph_capture_callbacks cb).
      rewrite Hdiscover_run; cbn.
      repeat constructor; cbn [audit_dfs_source_event_wellformed]; eauto.
      apply Forall_app; split; [exact Hdiscover|repeat constructor; reflexivity].
Qed.

(** Both halves of a captured binary-fuel run preserve event well-formedness. *)
Lemma audit_dfs_source_run_wellformed {V E B} {EV} {g : Graph.t V E}
    (p : prepared EV g)
    (cb : audit_dfs_callback_model V E B) blocked fuel work :
    Forall audit_dfs_source_event_wellformed
      (snd (audit_dfs_nested_run p (audit_graph_capture_callbacks cb) blocked fuel work)).
Proof.
  set (captured := audit_graph_capture_callbacks cb).
  revert work; induction fuel as [fuel IH|fuel IH|]; intro work;
    destruct work as [stack st], stack as [|frame stack]; cbn [audit_dfs_nested_run].
  - repeat constructor.
  - cbn [audit_dfs_nested_run fst].
    specialize (IH (frame :: stack, st)) as Hfirst.
    destruct (audit_dfs_nested_run p captured blocked fuel (frame :: stack, st))
      as [middle first] eqn:Hfirst_run; cbn in Hfirst |- *.
    specialize (IH middle) as Hsecond.
    destruct (audit_dfs_nested_run p captured blocked fuel middle) as [last second] eqn:Hsecond_run;
      cbn in Hsecond |- *.
    pose proof (audit_dfs_source_step_wellformed p cb blocked last) as Hstep.
    fold captured in Hstep.
    destruct (audit_dfs_nested_step p captured blocked last) as [result events] eqn:Hstep_run;
      cbn in Hstep |- *.
    change (Forall audit_dfs_source_event_wellformed
      (snd (let '(middle, first) :=
        audit_dfs_nested_run p captured blocked fuel (frame :: stack, st) in
        let '(last, second) := audit_dfs_nested_run p captured blocked fuel middle in
        let '(result, events) := audit_dfs_nested_step p captured blocked last in
        (result, (AuditDfsFullCase 7, []) :: first ++ second ++ events)))).
    rewrite Hfirst_run, Hsecond_run, Hstep_run; cbn.
    constructor; [reflexivity|]. apply Forall_app; split; [exact Hfirst|].
    apply Forall_app; split; assumption.
  - repeat constructor.
  - cbn [audit_dfs_nested_run fst].
    specialize (IH (frame :: stack, st)) as Hfirst.
    destruct (audit_dfs_nested_run p captured blocked fuel (frame :: stack, st))
      as [middle first] eqn:Hfirst_run; cbn in Hfirst |- *.
    specialize (IH middle) as Hsecond.
    destruct (audit_dfs_nested_run p captured blocked fuel middle)
      as [result second] eqn:Hsecond_run;
      cbn in Hsecond |- *.
    change (Forall audit_dfs_source_event_wellformed
      (snd (let '(middle, first) :=
        audit_dfs_nested_run p captured blocked fuel (frame :: stack, st) in
        let '(result, second) := audit_dfs_nested_run p captured blocked fuel middle in
        (result, (AuditDfsFullCase 6, []) :: first ++ second)))).
    rewrite Hfirst_run, Hsecond_run; cbn.
    constructor; [reflexivity|]. apply Forall_app; split; assumption.
  - repeat constructor.
  - cbn [audit_dfs_nested_run fst].
    pose proof (audit_dfs_source_step_wellformed p cb blocked (frame :: stack, st)) as Hstep.
    fold captured in Hstep.
    destruct (audit_dfs_nested_step p captured blocked (frame :: stack, st))
      as [result events] eqn:Hstep_run.
    cbn in Hstep.
    change (Forall audit_dfs_source_event_wellformed
      (snd (let '(result, events) :=
        audit_dfs_nested_step p captured blocked (frame :: stack, st) in
        (result, (AuditDfsFullCase 5, []) :: events)))).
    rewrite Hstep_run; cbn; constructor; [reflexivity|exact Hstep].
Qed.

(** Root membership and discovery events carry their actual encoder captures. *)
Lemma audit_dfs_source_root_wellformed {V E B} {EV} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) blocked st v :
    Forall audit_dfs_source_event_wellformed
      (snd (audit_dfs_nested_root p (audit_graph_capture_callbacks cb) blocked st v)).
Proof.
  unfold audit_dfs_nested_root, audit_dfs_nested_get, audit_graph_capture_callbacks; cbn.
  destruct (audit_dfs_encode_model cb v) as [code body].
  destruct (Map.code_get code blocked), (Map.code_get code (DfsState.seen st)); cbn;
    try (repeat constructor; cbn [audit_dfs_source_event_wellformed]; eauto; fail).
  pose proof (audit_dfs_source_discover_wellformed cb v None st) as Hdiscover.
  destruct (audit_dfs_nested_discover (audit_graph_capture_callbacks cb) v None st)
    as [next details] eqn:Hdiscover_run.
  cbn in Hdiscover.
  pose proof (audit_dfs_source_run_wellformed p cb blocked (fuel p)
    ([(v,
      match Map.code_get code (out_index p) with
      | Some xs => xs
      | None => []
      end)], next)) as Hrun.
  destruct (audit_dfs_nested_run p (audit_graph_capture_callbacks cb) blocked (fuel p)
    ([(v,
      match Map.code_get code (out_index p) with
      | Some xs => xs
      | None => []
      end)], next)) as [result events] eqn:Hrun_eq.
  cbn in Hrun.
  fold (audit_graph_capture_callbacks cb).
  cbn [audit_dfs_nested_discover]; cbn.
  cbn [audit_dfs_nested_discover] in Hdiscover_run; cbn in Hdiscover_run.
  rewrite Hdiscover_run, Hrun_eq; cbn.
  repeat constructor; cbn [audit_dfs_source_event_wellformed]; eauto.
  apply Forall_app; split; [exact Hdiscover|].
  constructor; [reflexivity|exact Hrun].
Qed.

(** The fold over roots preserves captured-event well-formedness. *)
Lemma audit_dfs_source_roots_wellformed {V E B} {EV} {g : Graph.t V E}
    (p : prepared EV g)
    (cb : audit_dfs_callback_model V E B) blocked roots st :
    Forall audit_dfs_source_event_wellformed
      (snd (audit_dfs_nested_roots p (audit_graph_capture_callbacks cb) blocked roots st)).
Proof.
  set (captured := audit_graph_capture_callbacks cb).
  revert st; induction roots as [|root roots IH]; intro st; cbn [audit_dfs_nested_roots].
  - repeat constructor.
  - pose proof (audit_dfs_source_root_wellformed p cb blocked st root) as Hroot.
    fold captured in Hroot.
    destruct (audit_dfs_nested_root p captured blocked st root) as [next here] eqn:Hroot_run.
    cbn in Hroot.
    specialize (IH next).
    destruct (audit_dfs_nested_roots p captured blocked roots next)
      as [result later] eqn:Hroots_run.
    cbn in IH.
    constructor; [reflexivity|]. apply Forall_app; split; assumption.
Qed.

(** Every source DFS event contains the callback capture required by its event kind. *)
Lemma audit_dfs_source_events_wellformed {V E B} {EV} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) blocked roots :
    Forall audit_dfs_source_event_wellformed (snd (audit_dfs_source_counted p cb blocked roots)).
Proof.
  unfold audit_dfs_source_counted.
  pose proof (audit_dfs_source_roots_wellformed p cb blocked roots dfs_initial) as Hroots.
  destruct (audit_dfs_nested_roots p (audit_graph_capture_callbacks cb) blocked roots dfs_initial)
    as [st events]; cbn in Hroots |- *.
  apply Forall_app; split; [exact Hroots|repeat constructor; reflexivity].
Qed.

(** * Input key widths *)

(** A member contributes its width to the maximum over a mapped list. *)
Lemma audit_dfs_width_member {A} (width : A -> nat) xs value :
    In value xs -> width value <= fold_right Nat.max 0 (map width xs).
Proof.
  induction xs as [|head tail IH]; cbn; [contradiction|].
  intros [Heq|Hin].
  - subst head; apply Nat.le_max_l.
  - eapply Nat.le_trans; [apply IH; exact Hin|apply Nat.le_max_r].
Qed.

(** Every root's encoded width occurs in the original DFS input-width envelope. *)
Lemma audit_dfs_input_width_root {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) roots v :
    In v roots -> audit_key_bits_weight (encode EV v) <= audit_dfs_input_width EV g p roots.
Proof.
  intro Hin; unfold audit_dfs_input_width.
  apply (audit_dfs_width_member (fun node => audit_key_bits_weight (encode EV node))).
  apply in_or_app; left; exact Hin.
Qed.

(** A position lookup's returned value occurs in map enumeration, even for a malformed map. *)
Lemma audit_dfs_get_row {V A} (EV : encoding V) (m : Map.t V A) v value :
    Map.get EV v m = Some value -> exists key, In (key, value) (Map.elements m).
Proof.
  unfold Map.get, Map.code_get, Map.elements.
  destruct (Trie.get (encode EV v) m) as [[key stored]|] eqn:Hget; cbn; [|discriminate].
  intro Heq; inversion Heq; subst stored.
  exists key; apply in_map_iff; exists (encode EV v, (key, value)); split; [reflexivity|].
  now apply Trie.elements_complete.
Qed.

(** Every actual indexed successor target lies within the original input-width envelope. *)
Lemma audit_dfs_input_width_target {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) roots v edges edge :
    Map.get EV v (out_index p) = Some edges -> In edge edges ->
    audit_key_bits_weight (encode EV (Graph.target g edge)) <= audit_dfs_input_width EV g p roots.
Proof.
  intros Hget Hedge.
  destruct (audit_dfs_get_row EV (out_index p) v edges Hget) as [key Hrow].
  unfold audit_dfs_input_width; apply (audit_dfs_width_member (fun node => audit_key_bits_weight
    (encode EV node))).
  repeat (apply in_or_app; right).
  apply in_flat_map; exists (key, edges); split; [exact Hrow|].
  apply in_map; exact Hedge.
Qed.

(** A DFS transition advances each clock by at most one. *)
Lemma audit_dfs_step_clock_bound {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked work :
    Pos.to_nat (DfsState.pre_clock (snd (dfs_step p blocked work))) <=
      S (Pos.to_nat (DfsState.pre_clock (snd work))) /\
    Pos.to_nat (DfsState.post_clock (snd (dfs_step p blocked work))) <=
      S (Pos.to_nat (DfsState.post_clock (snd work))).
Proof.
  destruct work as [stack st], stack as [|[v edges] rest]; cbn [dfs_step].
  - cbn; lia.
  - destruct edges as [|edge edges].
    + cbn [dfs_finish]; cbn; rewrite Pos2Nat.inj_succ; lia.
    + destruct (FinSet.mem EV (Graph.target g edge) blocked ||
        FinSet.mem EV (Graph.target g edge) (DfsState.seen st)); cbn [dfs_discover]; cbn;
        try rewrite Pos2Nat.inj_succ; lia.
Qed.

(** Binary traversal fuel bounds the increase of both source DFS clocks. *)
Lemma audit_dfs_run_clock_bound {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked fuel work :
    Pos.to_nat (DfsState.pre_clock (snd (dfs_run p blocked fuel work))) <=
      Pos.to_nat (DfsState.pre_clock (snd work)) + Pos.to_nat fuel /\
    Pos.to_nat (DfsState.post_clock (snd (dfs_run p blocked fuel work))) <=
      Pos.to_nat (DfsState.post_clock (snd work)) + Pos.to_nat fuel.
Proof.
  revert work; induction fuel as [fuel IH|fuel IH|]; intros [stack st];
    destruct stack as [|frame stack].
  - cbn [dfs_run]; cbn; lia.
  - change (Pos.to_nat (DfsState.pre_clock
        (snd (dfs_step p blocked (dfs_run p blocked fuel
          (dfs_run p blocked fuel (frame :: stack, st)))))) <= Pos.to_nat (DfsState.pre_clock st)
            + Pos.to_nat (xI fuel) /\
      Pos.to_nat (DfsState.post_clock
        (snd (dfs_step p blocked (dfs_run p blocked fuel
          (dfs_run p blocked fuel (frame :: stack, st)))))) <= Pos.to_nat (DfsState.post_clock st)
            + Pos.to_nat (xI fuel)).
    pose proof (IH (frame :: stack, st)) as [Hfirst_pre Hfirst_post].
    pose proof (IH (dfs_run p blocked fuel (frame :: stack, st))) as [Hsecond_pre Hsecond_post].
    pose proof (audit_dfs_step_clock_bound p blocked
      (dfs_run p blocked fuel (dfs_run p blocked fuel (frame :: stack, st)))) as [Hstep_pre
        Hstep_post].
    cbn in Hfirst_pre, Hfirst_post; rewrite Pos2Nat.inj_xI; lia.
  - cbn [dfs_run]; cbn; lia.
  - change (Pos.to_nat (DfsState.pre_clock
        (snd (dfs_run p blocked fuel (dfs_run p blocked fuel (frame :: stack, st))))) <=
          Pos.to_nat (DfsState.pre_clock st) + Pos.to_nat (xO fuel) /\
      Pos.to_nat (DfsState.post_clock
        (snd (dfs_run p blocked fuel (dfs_run p blocked fuel (frame :: stack, st))))) <=
          Pos.to_nat (DfsState.post_clock st) + Pos.to_nat (xO fuel)).
    pose proof (IH (frame :: stack, st)) as [Hfirst_pre Hfirst_post].
    pose proof (IH (dfs_run p blocked fuel (frame :: stack, st))) as [Hsecond_pre Hsecond_post].
    cbn in Hfirst_pre, Hfirst_post; rewrite Pos2Nat.inj_xO; lia.
  - cbn [dfs_run]; cbn; lia.
  - cbn [dfs_run fst].
    pose proof (audit_dfs_step_clock_bound p blocked (frame :: stack, st)) as Hstep.
    cbn in Hstep; cbn; lia.
Qed.

(** One root advances either clock by no more than discovery plus its prepared fuel. *)
Lemma audit_dfs_root_clock_bound {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked st v :
    Pos.to_nat (DfsState.pre_clock (dfs_root p blocked st v)) <=
      Pos.to_nat (DfsState.pre_clock st) + S (Pos.to_nat (fuel p)) /\
    Pos.to_nat (DfsState.post_clock (dfs_root p blocked st v)) <=
      Pos.to_nat (DfsState.post_clock st) + S (Pos.to_nat (fuel p)).
Proof.
  unfold dfs_root.
  destruct (FinSet.mem EV v blocked || FinSet.mem EV v (DfsState.seen st)); [lia|].
  pose proof (audit_dfs_run_clock_bound p blocked (fuel p)
    ([(v, succ_edges p v)], dfs_discover EV v None st)) as [Hpre Hpost].
  cbn [dfs_discover] in Hpre, Hpost; cbn in Hpre, Hpost.
  rewrite Pos2Nat.inj_succ in Hpre; lia.
Qed.

(** The root fold increases either clock by at most discovery plus fuel per root. *)
Lemma audit_dfs_roots_clock_bound {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked roots st :
    Pos.to_nat (DfsState.pre_clock (fold_left (dfs_root p blocked) roots st)) <=
      Pos.to_nat (DfsState.pre_clock st) + length roots * S (Pos.to_nat (fuel p)) /\
    Pos.to_nat (DfsState.post_clock (fold_left (dfs_root p blocked) roots st)) <=
      Pos.to_nat (DfsState.post_clock st) + length roots * S (Pos.to_nat (fuel p)).
Proof.
  revert st; induction roots as [|root roots IH]; intro st; cbn [fold_left length].
  - lia.
  - pose proof (audit_dfs_root_clock_bound p blocked st root) as [Hroot_pre Hroot_post].
    pose proof (IH (dfs_root p blocked st root)) as [Hrest_pre Hrest_post]; nia.
Qed.

(** A DFS transition never decreases either clock. *)
Lemma audit_dfs_step_clock_monotone {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked work :
    Pos.to_nat (DfsState.pre_clock (snd work)) <=
      Pos.to_nat (DfsState.pre_clock (snd (dfs_step p blocked work))) /\
    Pos.to_nat (DfsState.post_clock (snd work)) <=
      Pos.to_nat (DfsState.post_clock (snd (dfs_step p blocked work))).
Proof.
  destruct work as [stack st], stack as [|[v edges] rest]; cbn [dfs_step].
  - cbn; lia.
  - destruct edges as [|edge edges].
    + cbn [dfs_finish]; cbn; rewrite Pos2Nat.inj_succ; lia.
    + destruct (FinSet.mem EV (Graph.target g edge) blocked ||
        FinSet.mem EV (Graph.target g edge) (DfsState.seen st)); cbn [dfs_discover]; cbn;
        try rewrite Pos2Nat.inj_succ; lia.
Qed.

(** The source binary run preserves the lower bound on both clocks. *)
Lemma audit_dfs_run_clock_monotone {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked fuel work :
    Pos.to_nat (DfsState.pre_clock (snd work)) <=
      Pos.to_nat (DfsState.pre_clock (snd (dfs_run p blocked fuel work))) /\
    Pos.to_nat (DfsState.post_clock (snd work)) <=
      Pos.to_nat (DfsState.post_clock (snd (dfs_run p blocked fuel work))).
Proof.
  revert work; induction fuel as [fuel IH|fuel IH|]; intros [stack st];
    destruct stack as [|frame stack].
  - cbn [dfs_run]; cbn; lia.
  - change (Pos.to_nat (DfsState.pre_clock st) <= Pos.to_nat (DfsState.pre_clock
        (snd (dfs_step p blocked (dfs_run p blocked fuel
          (dfs_run p blocked fuel (frame :: stack, st)))))) /\
      Pos.to_nat (DfsState.post_clock st) <= Pos.to_nat (DfsState.post_clock
        (snd (dfs_step p blocked (dfs_run p blocked fuel
          (dfs_run p blocked fuel (frame :: stack, st))))))).
    pose proof (IH (frame :: stack, st)) as [Hfirst_pre Hfirst_post].
    pose proof (IH (dfs_run p blocked fuel (frame :: stack, st))) as [Hsecond_pre Hsecond_post].
    pose proof (audit_dfs_step_clock_monotone p blocked
      (dfs_run p blocked fuel (dfs_run p blocked fuel (frame :: stack, st)))) as [Hstep_pre
        Hstep_post].
    cbn in Hfirst_pre, Hfirst_post; lia.
  - cbn [dfs_run]; cbn; lia.
  - change (Pos.to_nat (DfsState.pre_clock st) <= Pos.to_nat (DfsState.pre_clock
        (snd (dfs_run p blocked fuel (dfs_run p blocked fuel (frame :: stack, st))))) /\
      Pos.to_nat (DfsState.post_clock st) <= Pos.to_nat (DfsState.post_clock
        (snd (dfs_run p blocked fuel (dfs_run p blocked fuel (frame :: stack, st)))))).
    pose proof (IH (frame :: stack, st)) as [Hfirst_pre Hfirst_post].
    pose proof (IH (dfs_run p blocked fuel (frame :: stack, st))) as [Hsecond_pre Hsecond_post].
    cbn in Hfirst_pre, Hfirst_post; lia.
  - cbn [dfs_run]; cbn; lia.
  - cbn [dfs_run fst].
    pose proof (audit_dfs_step_clock_monotone p blocked (frame :: stack, st)) as Hstep.
    cbn in Hstep; exact Hstep.
Qed.

(** * Counted event bounds *)

(** The clock charged by a counted event, or zero when the event has no clock charge. *)
Definition audit_dfs_event_clock {V E} (event : audit_dfs_call V E) : nat :=
  match event with
  | AuditDfsDiscover _ _ before _ => Pos.to_nat (DfsState.pre_clock before)
  | AuditDfsFinish _ before _ => Pos.to_nat (DfsState.post_clock before)
  | _ => 0
  end.

(** A counted step only charges clocks present in its input state. *)
Lemma audit_dfs_step_event_clock {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked work :
    Forall (fun event => audit_dfs_event_clock event <=
      Nat.max (Pos.to_nat (DfsState.pre_clock (snd work)))
        (Pos.to_nat (DfsState.post_clock (snd work))))
      (snd (audit_dfs_step_counted p blocked work)).
Proof.
  destruct work as [stack st], stack as [|[v edges] rest]; cbn [audit_dfs_step_counted].
  - repeat constructor; cbn [audit_dfs_event_clock]; lia.
  - destruct edges as [|edge edges].
    + repeat constructor; cbn [audit_dfs_event_clock]; try lia; apply Nat.le_max_r.
    + destruct (FinSet.mem EV (Graph.target g edge) blocked ||
        FinSet.mem EV (Graph.target g edge) (DfsState.seen st)); cbn;
        repeat constructor; cbn [audit_dfs_event_clock]; try lia; apply Nat.le_max_l.
Qed.

(** The maximum source clock increases by at most the binary run's fuel. *)
Lemma audit_dfs_run_max_clock_bound {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked fuel work :
    Nat.max (Pos.to_nat (DfsState.pre_clock (snd (dfs_run p blocked fuel work))))
      (Pos.to_nat (DfsState.post_clock (snd (dfs_run p blocked fuel work)))) <=
    Nat.max (Pos.to_nat (DfsState.pre_clock (snd work)))
      (Pos.to_nat (DfsState.post_clock (snd work))) + Pos.to_nat fuel.
Proof.
  pose proof (audit_dfs_run_clock_bound p blocked fuel work) as [Hpre Hpost].
  apply Nat.max_lub; pose proof (Nat.le_max_l (Pos.to_nat (DfsState.pre_clock (snd work)))
    (Pos.to_nat (DfsState.post_clock (snd work)))) as Hleft;
    pose proof (Nat.le_max_r (Pos.to_nat (DfsState.pre_clock (snd work)))
      (Pos.to_nat (DfsState.post_clock (snd work)))) as Hright; lia.
Qed.

(** Every clock charged by a binary counted run is bounded by its input clocks and fuel. *)
Lemma audit_dfs_run_event_clock {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked fuel work :
    Forall (fun event => audit_dfs_event_clock event <=
      Nat.max (Pos.to_nat (DfsState.pre_clock (snd work)))
        (Pos.to_nat (DfsState.post_clock (snd work))) + Pos.to_nat fuel)
      (snd (audit_dfs_run_counted p blocked fuel work)).
Proof.
  revert work; induction fuel as [fuel IH|fuel IH|]; intros [stack st];
    destruct stack as [|frame stack].
  - cbn [audit_dfs_run_counted]; repeat constructor; cbn [audit_dfs_event_clock]; lia.
  - change (Forall (fun event => audit_dfs_event_clock event <=
      Nat.max (Pos.to_nat (DfsState.pre_clock st)) (Pos.to_nat (DfsState.post_clock st)) +
        Pos.to_nat (xI fuel)) (snd (let '(middle, first) :=
        audit_dfs_run_counted p blocked fuel (frame :: stack, st) in
      let '(last, second) := audit_dfs_run_counted p blocked fuel middle in
      let '(result, events) := audit_dfs_step_counted p blocked last in
      (result, AuditDfsCase 7 :: first ++ second ++ events)))).
    pose proof (IH (frame :: stack, st)) as Hfirst.
    pose proof (audit_dfs_run_max_clock_bound p blocked fuel (frame :: stack, st)) as Hmax1.
    pose proof (audit_dfs_run_erases p blocked fuel (frame :: stack, st)) as Herase1.
    destruct (audit_dfs_run_counted p blocked fuel (frame :: stack, st)) as [middle first].
    cbn in Hfirst, Herase1 |- *; rewrite <- Herase1 in Hmax1.
    pose proof (IH middle) as Hsecond.
    pose proof (audit_dfs_run_max_clock_bound p blocked fuel middle) as Hmax2.
    pose proof (audit_dfs_run_erases p blocked fuel middle) as Herase2.
    destruct (audit_dfs_run_counted p blocked fuel middle) as [last second].
    cbn in Hsecond, Herase2 |- *; rewrite <- Herase2 in Hmax2.
    pose proof (audit_dfs_step_event_clock p blocked last) as Hstep.
    destruct (audit_dfs_step_counted p blocked last) as [result events]; cbn in Hstep |- *.
    constructor; [cbn [audit_dfs_event_clock]; lia|].
    rewrite !Forall_app; rewrite Pos2Nat.inj_xI.
    split; [|split].
    all: eapply Forall_impl; [|eassumption].
    all: intros event Hbound; cbn in Hbound, Hmax1, Hmax2; lia.
  - cbn [audit_dfs_run_counted]; repeat constructor; cbn [audit_dfs_event_clock]; lia.
  - change (Forall (fun event => audit_dfs_event_clock event <=
      Nat.max (Pos.to_nat (DfsState.pre_clock st)) (Pos.to_nat (DfsState.post_clock st)) +
        Pos.to_nat (xO fuel)) (snd (let '(middle, first) :=
        audit_dfs_run_counted p blocked fuel (frame :: stack, st) in
      let '(result, second) := audit_dfs_run_counted p blocked fuel middle in
      (result, AuditDfsCase 6 :: first ++ second)))).
    pose proof (IH (frame :: stack, st)) as Hfirst.
    pose proof (audit_dfs_run_max_clock_bound p blocked fuel (frame :: stack, st)) as Hmax.
    pose proof (audit_dfs_run_erases p blocked fuel (frame :: stack, st)) as Herase.
    destruct (audit_dfs_run_counted p blocked fuel (frame :: stack, st)) as [middle first].
    cbn in Hfirst, Herase |- *; rewrite <- Herase in Hmax.
    pose proof (IH middle) as Hsecond.
    destruct (audit_dfs_run_counted p blocked fuel middle) as [result second]; cbn in Hsecond |- *.
    constructor; [cbn [audit_dfs_event_clock]; lia|].
    rewrite Forall_app; rewrite Pos2Nat.inj_xO.
    split.
    all: eapply Forall_impl; [|eassumption].
    all: intros event Hbound; cbn in Hbound, Hmax; lia.
  - cbn [audit_dfs_run_counted]; repeat constructor; cbn [audit_dfs_event_clock]; lia.
  - change (Forall (fun event => audit_dfs_event_clock event <=
      Nat.max (Pos.to_nat (DfsState.pre_clock st)) (Pos.to_nat (DfsState.post_clock st)) +
        Pos.to_nat xH) (snd (let '(result, events) :=
        audit_dfs_step_counted p blocked (frame :: stack, st) in
      (result, AuditDfsCase 5 :: events)))).
    pose proof (audit_dfs_step_event_clock p blocked (frame :: stack, st)) as Hstep.
    destruct (audit_dfs_step_counted p blocked (frame :: stack, st)); cbn in Hstep |- *.
    constructor; [cbn [audit_dfs_event_clock]; lia|].
    eapply Forall_impl; [|exact Hstep]; intros event Hbound; cbn in *; lia.
Qed.

(** A root's counted events charge at most its starting maximum clock plus discovery and fuel. *)
Lemma audit_dfs_root_event_clock {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked st v :
    Forall (fun event => audit_dfs_event_clock event <=
      Nat.max (Pos.to_nat (DfsState.pre_clock st)) (Pos.to_nat (DfsState.post_clock st)) +
        S (Pos.to_nat (fuel p))) (snd (audit_dfs_root_counted p blocked st v)).
Proof.
  unfold audit_dfs_root_counted.
  destruct (FinSet.mem EV v blocked || FinSet.mem EV v (DfsState.seen st)); cbn.
  - repeat constructor; cbn [audit_dfs_event_clock]; lia.
  - pose proof (audit_dfs_run_event_clock p blocked (fuel p)
      ([(v, index_edges EV (out_index p) v)], dfs_discover EV v None st)) as Hrun.
    unfold index_edges in Hrun.
    destruct (audit_dfs_run_counted p blocked (fuel p)
      ([(v, index_edges EV (out_index p) v)], dfs_discover EV v None st))
      as [result events] eqn:Hrun_eq.
    unfold index_edges in Hrun_eq; rewrite Hrun_eq in Hrun; cbn in Hrun.
    rewrite Hrun_eq; cbn.
    repeat constructor; cbn [audit_dfs_event_clock]; try lia.
    eapply Forall_impl; [|exact Hrun].
    intros event Hbound; cbn [dfs_discover] in Hbound; cbn in Hbound.
    rewrite Pos2Nat.inj_succ in Hbound.
    assert (Hmax : Nat.max (S (Pos.to_nat (DfsState.pre_clock st)))
      (Pos.to_nat (DfsState.post_clock st)) <=
      S (Nat.max (Pos.to_nat (DfsState.pre_clock st)) (Pos.to_nat (DfsState.post_clock st)))).
    { apply Nat.max_lub; pose proof (Nat.le_max_l (Pos.to_nat (DfsState.pre_clock st))
        (Pos.to_nat (DfsState.post_clock st)));
        pose proof (Nat.le_max_r (Pos.to_nat (DfsState.pre_clock st))
        (Pos.to_nat (DfsState.post_clock st))); lia. }
    lia.
Qed.

(** Root events charge clocks bounded by the initial clocks and the remaining root budget. *)
Lemma audit_dfs_roots_event_clock {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked roots st :
    Forall (fun event => audit_dfs_event_clock event <=
      Nat.max (Pos.to_nat (DfsState.pre_clock st)) (Pos.to_nat (DfsState.post_clock st)) +
        length roots * S (Pos.to_nat (fuel p)))
      (snd (audit_dfs_roots_counted p blocked roots st)).
Proof.
  revert st; induction roots as [|root roots IH]; intro st; cbn [audit_dfs_roots_counted length].
  - repeat constructor; cbn [audit_dfs_event_clock]; lia.
  - pose proof (audit_dfs_root_event_clock p blocked st root) as Hroot.
    pose proof (audit_dfs_root_clock_bound p blocked st root) as [Hpre Hpost].
    pose proof (audit_dfs_root_erases p blocked st root) as Herase.
    destruct (audit_dfs_root_counted p blocked st root) as [next here]; cbn in Hroot, Herase |- *.
    rewrite <- Herase in Hpre, Hpost.
    specialize (IH next).
    destruct (audit_dfs_roots_counted p blocked roots next) as [result later]; cbn in IH |- *.
    constructor; [cbn [audit_dfs_event_clock]; lia|].
    apply Forall_app; split.
    + eapply Forall_impl; [|exact Hroot].
      intros event Hbound; cbn in Hbound; nia.
    + eapply Forall_impl; [|exact IH].
      intros event Hbound; cbn in Hbound.
      assert (Hmax : Nat.max (Pos.to_nat (DfsState.pre_clock next))
        (Pos.to_nat (DfsState.post_clock next)) <=
        Nat.max (Pos.to_nat (DfsState.pre_clock st)) (Pos.to_nat (DfsState.post_clock st)) +
          S (Pos.to_nat (fuel p))).
      { apply Nat.max_lub; pose proof (Nat.le_max_l (Pos.to_nat (DfsState.pre_clock st))
          (Pos.to_nat (DfsState.post_clock st)));
          pose proof (Nat.le_max_r (Pos.to_nat (DfsState.pre_clock st))
          (Pos.to_nat (DfsState.post_clock st))); lia. }
      nia.
Qed.

(** A frame retains a permitted vertex and only edges drawn from the prepared index. *)
Definition audit_dfs_stack_keys {V E} (vertices : list V) (edges : list E)
    (stack : dfs_stack V E) : Prop :=
  Forall (fun frame => In (fst frame) vertices /\ incl (snd frame) edges) stack.

(** A counted event's vertex operands must belong to the input-derived vertex envelope. *)
Definition audit_dfs_event_keys {V E} (vertices : list V) (event : audit_dfs_call V E) : Prop :=
  match event with
  | AuditDfsTarget _ vertex
  | AuditDfsMember vertex _ _
  | AuditDfsSuccessors vertex _ _
  | AuditDfsDiscover vertex _ _ _
  | AuditDfsFinish vertex _ _ => In vertex vertices
  | AuditDfsCase _ => True
  end.

(** A returned adjacency row contains only edges enumerated in the prepared index. *)
Lemma audit_dfs_outgoing_edges {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) v outgoing :
    Map.get EV v (out_index p) = Some outgoing ->
    incl outgoing (flat_map snd (Map.elements (out_index p))).
Proof.
  intros Hget edge Hedge.
  destruct (audit_dfs_get_row EV (out_index p) v outgoing Hget) as [key Hrow].
  apply in_flat_map; exists (key, outgoing); auto.
Qed.

(** One counted step preserves stack provenance and emits only vertices in the envelope. *)
Lemma audit_dfs_step_keys {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked vertices work :
    let edges := flat_map snd (Map.elements (out_index p)) in
    (forall edge, In edge edges -> In (Graph.target g edge) vertices) ->
    audit_dfs_stack_keys vertices edges (fst work) ->
    Forall (audit_dfs_event_keys vertices) (snd (audit_dfs_step_counted p blocked work)) /\
    audit_dfs_stack_keys vertices edges (fst (fst (audit_dfs_step_counted p blocked work))).
Proof.
  intros edges Hall Hstack; subst edges; unfold audit_dfs_stack_keys in *.
  destruct work as [stack st], stack as [|[v outgoing] rest]; cbn [audit_dfs_step_counted] in *.
  - split; constructor; [exact I|constructor].
  - cbn in Hstack.
    inversion Hstack as [|frame tail Hframe Hrest]; subst frame tail.
    cbn in Hframe; destruct Hframe as [Hv Hedges].
    destruct outgoing as [|edge outgoing].
    + split.
      * repeat constructor; cbn [audit_dfs_event_keys]; assumption.
      * exact Hrest.
    + assert (Htarget : In (Graph.target g edge) vertices).
      { apply Hall, Hedges; left; reflexivity. }
      assert (Htail : incl outgoing (flat_map snd (Map.elements (out_index p)))).
      { intros x Hin; apply Hedges; right; exact Hin. }
      destruct (FinSet.mem EV (Graph.target g edge) blocked ||
        FinSet.mem EV (Graph.target g edge) (DfsState.seen st)); cbn.
      * split.
        -- repeat constructor; cbn [audit_dfs_event_keys]; auto.
        -- constructor; [cbn; auto|exact Hrest].
      * destruct (Map.get EV (Graph.target g edge) (out_index p)) as [next_edges|] eqn:Hget; cbn.
        -- split.
           ++ repeat constructor; cbn [audit_dfs_event_keys]; auto.
           ++ constructor.
              ** cbn; split; [exact Htarget|]. now apply (audit_dfs_outgoing_edges p _ _ Hget).
              ** constructor; [cbn; auto|exact Hrest].
        -- split.
           ++ repeat constructor; cbn [audit_dfs_event_keys]; auto.
           ++ constructor; [cbn; split; [exact Htarget|intros x Hfalse; contradiction]|].
              constructor; [cbn; auto|exact Hrest].
Qed.

(** Binary counted traversal preserves stack provenance and its events' key envelope. *)
Lemma audit_dfs_run_keys {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked vertices fuel work :
    let edges := flat_map snd (Map.elements (out_index p)) in
    (forall edge, In edge edges -> In (Graph.target g edge) vertices) ->
    audit_dfs_stack_keys vertices edges (fst work) ->
    Forall (audit_dfs_event_keys vertices) (snd (audit_dfs_run_counted p blocked fuel work)) /\
    audit_dfs_stack_keys vertices edges (fst (fst (audit_dfs_run_counted p blocked fuel work))).
Proof.
  intros edges Hall; subst edges; revert work.
  induction fuel as [fuel IH|fuel IH|]; intros [stack st] Hstack; destruct stack as [|frame stack].
  - cbn [audit_dfs_run_counted]; split; [repeat constructor|exact Hstack].
  - change (Forall (audit_dfs_event_keys vertices)
      (snd (let '(middle, first) := audit_dfs_run_counted p blocked fuel (frame :: stack, st) in
        let '(last, second) := audit_dfs_run_counted p blocked fuel middle in
        let '(result, events) := audit_dfs_step_counted p blocked last in
        (result, AuditDfsCase 7 :: first ++ second ++ events))) /\
      audit_dfs_stack_keys vertices (flat_map snd (Map.elements (out_index p)))
      (fst (fst (let '(middle, first) :=
          audit_dfs_run_counted p blocked fuel (frame :: stack, st) in
        let '(last, second) := audit_dfs_run_counted p blocked fuel middle in
        let '(result, events) := audit_dfs_step_counted p blocked last in
        (result, AuditDfsCase 7 :: first ++ second ++ events))))).
    pose proof (IH (frame :: stack, st) Hstack) as [Hfirst Hmiddle].
    destruct (audit_dfs_run_counted p blocked fuel (frame :: stack, st)) as [middle first].
    cbn in Hfirst, Hmiddle |- *.
    pose proof (IH middle Hmiddle) as [Hsecond Hlast].
    destruct (audit_dfs_run_counted p blocked fuel middle) as [last second].
    cbn in Hsecond, Hlast |- *.
    pose proof (audit_dfs_step_keys p blocked vertices last Hall Hlast) as [Hstep Hresult].
    destruct (audit_dfs_step_counted p blocked last) as [result events]; cbn in Hstep, Hresult |- *.
    split; [constructor; [exact I|rewrite !Forall_app; auto]|exact Hresult].
  - cbn [audit_dfs_run_counted]; split; [repeat constructor|exact Hstack].
  - change (Forall (audit_dfs_event_keys vertices)
      (snd (let '(middle, first) := audit_dfs_run_counted p blocked fuel (frame :: stack, st) in
        let '(result, second) := audit_dfs_run_counted p blocked fuel middle in
        (result, AuditDfsCase 6 :: first ++ second))) /\
      audit_dfs_stack_keys vertices (flat_map snd (Map.elements (out_index p)))
      (fst (fst (let '(middle, first) :=
          audit_dfs_run_counted p blocked fuel (frame :: stack, st) in
        let '(result, second) := audit_dfs_run_counted p blocked fuel middle in
        (result, AuditDfsCase 6 :: first ++ second))))).
    pose proof (IH (frame :: stack, st) Hstack) as [Hfirst Hmiddle].
    destruct (audit_dfs_run_counted p blocked fuel (frame :: stack, st)) as [middle first].
    cbn in Hfirst, Hmiddle |- *.
    pose proof (IH middle Hmiddle) as [Hsecond Hresult].
    destruct (audit_dfs_run_counted p blocked fuel middle) as [result second].
    cbn in Hsecond, Hresult |- *.
    split; [constructor; [exact I|rewrite Forall_app; auto]|exact Hresult].
  - cbn [audit_dfs_run_counted]; split; [repeat constructor|exact Hstack].
  - change (Forall (audit_dfs_event_keys vertices)
      (snd (let '(result, events) := audit_dfs_step_counted p blocked (frame :: stack, st) in
        (result, AuditDfsCase 5 :: events))) /\
      audit_dfs_stack_keys vertices (flat_map snd (Map.elements (out_index p)))
      (fst (fst (let '(result, events) := audit_dfs_step_counted p blocked (frame :: stack, st) in
        (result, AuditDfsCase 5 :: events))))).
    pose proof (audit_dfs_step_keys p blocked vertices (frame :: stack, st) Hall Hstack)
      as [Hstep Hresult].
    destruct (audit_dfs_step_counted p blocked (frame :: stack, st)); cbn in Hstep, Hresult |- *.
    split; [constructor; [exact I|exact Hstep]|exact Hresult].
Qed.

(** A root in the envelope emits only envelope vertices. *)
Lemma audit_dfs_root_keys {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked vertices st v :
    (forall edge, In edge (flat_map snd (Map.elements (out_index p))) ->
      In (Graph.target g edge) vertices) ->
    In v vertices ->
    Forall (audit_dfs_event_keys vertices) (snd (audit_dfs_root_counted p blocked st v)).
Proof.
  intros Hall Hv; unfold audit_dfs_root_counted.
  destruct (FinSet.mem EV v blocked || FinSet.mem EV v (DfsState.seen st)); cbn.
  - repeat constructor; cbn [audit_dfs_event_keys]; auto.
  - destruct (Map.get EV v (out_index p)) as [outgoing|] eqn:Hget.
    + assert (Hstack : audit_dfs_stack_keys vertices (flat_map snd (Map.elements (out_index p)))
        [(v, outgoing)]).
      { constructor; [cbn; split; [exact Hv|now apply (audit_dfs_outgoing_edges p _ _ Hget)]|].
        constructor. }
      pose proof (audit_dfs_run_keys p blocked vertices (fuel p)
        ([(v, outgoing)], dfs_discover EV v None st) Hall Hstack) as [Hrun _].
      destruct (audit_dfs_run_counted p blocked (fuel p)
        ([(v, outgoing)], dfs_discover EV v None st)); cbn in Hrun |- *.
      repeat constructor; cbn [audit_dfs_event_keys]; auto.
    + assert (Hstack : audit_dfs_stack_keys vertices (flat_map snd (Map.elements (out_index p)))
        [(v, [])]).
      { constructor; [cbn; split; [exact Hv|intros x Hfalse; contradiction]|constructor]. }
      pose proof (audit_dfs_run_keys p blocked vertices (fuel p)
        ([(v, [])], dfs_discover EV v None st) Hall Hstack) as [Hrun _].
      destruct (audit_dfs_run_counted p blocked (fuel p)
        ([(v, [])], dfs_discover EV v None st)); cbn in Hrun |- *.
      repeat constructor; cbn [audit_dfs_event_keys]; auto.
Qed.

(** Processing roots in the envelope emits only vertices in that envelope. *)
Lemma audit_dfs_roots_keys {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked vertices roots st :
    (forall edge, In edge (flat_map snd (Map.elements (out_index p))) ->
      In (Graph.target g edge) vertices) ->
    incl roots vertices ->
    Forall (audit_dfs_event_keys vertices) (snd (audit_dfs_roots_counted p blocked roots st)).
Proof.
  intros Hall; revert st; induction roots as [|root roots IH]; intros st Hroots.
  - cbn [audit_dfs_roots_counted]; repeat constructor.
  - cbn [audit_dfs_roots_counted].
    pose proof (audit_dfs_root_keys p blocked vertices st root Hall (Hroots root (or_introl
      eq_refl)))
      as Hroot.
    destruct (audit_dfs_root_counted p blocked st root) as [next here]; cbn in Hroot |- *.
    specialize (IH next ltac:(intros v Hv; apply Hroots; right; exact Hv)).
    destruct (audit_dfs_roots_counted p blocked roots next) as [result later]; cbn in IH |- *.
    constructor; [exact I|]. apply Forall_app; split; assumption.
Qed.

(** Every counted event vertex is either a root or a target of an indexed edge. *)
Lemma audit_dfs_counted_keys {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked roots :
    let vertices := roots ++ map (Graph.target g) (flat_map snd (Map.elements (out_index p))) in
    Forall (audit_dfs_event_keys vertices) (snd (audit_dfs_counted p blocked roots)).
Proof.
  intro vertices; subst vertices; unfold audit_dfs_counted.
  pose proof (audit_dfs_roots_keys p blocked
    (roots ++ map (Graph.target g) (flat_map snd (Map.elements (out_index p)))) roots dfs_initial)
    as Hroots.
  assert (Hall : forall edge, In edge (flat_map snd (Map.elements (out_index p))) ->
      In (Graph.target g edge)
        (roots ++ map (Graph.target g) (flat_map snd (Map.elements (out_index p)))))
    by (intros edge Hin; apply in_or_app; right; now apply in_map).
  assert (Hincl : incl roots
    (roots ++ map (Graph.target g) (flat_map snd (Map.elements (out_index p)))))
    by (intros v Hin; apply in_or_app; now left).
  specialize (Hroots Hall Hincl).
  destruct (audit_dfs_roots_counted p blocked roots dfs_initial) as [st events]; exact Hroots.
Qed.

(** The encoded width of a counted event vertex, or zero when no vertex appears. *)
Definition audit_dfs_event_width {V E} (EV : encoding V) (event : audit_dfs_call V E) : nat :=
  match event with
  | AuditDfsTarget _ vertex
  | AuditDfsMember vertex _ _
  | AuditDfsSuccessors vertex _ _
  | AuditDfsDiscover vertex _ _ _
  | AuditDfsFinish vertex _ _ => audit_key_bits_weight (encode EV vertex)
  | AuditDfsCase _ => 0
  end.

(** An envelope vertex has an encoded width bounded by the original DFS input. *)
Lemma audit_dfs_envelope_width {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) roots v :
    In v (roots ++ map (Graph.target g) (flat_map snd (Map.elements (out_index p)))) ->
    audit_key_bits_weight (encode EV v) <= audit_dfs_input_width EV g p roots.
Proof.
  rewrite in_app_iff; intros [Hroot|Htarget].
  - now apply audit_dfs_input_width_root.
  - apply in_map_iff in Htarget; destruct Htarget as [edge [Heq Hedge]]; subst v.
    apply in_flat_map in Hedge; destruct Hedge as [[key edges] [Hrow Hedge]]; cbn in Hedge.
    unfold audit_dfs_input_width.
    apply (audit_dfs_width_member (fun node => audit_key_bits_weight (encode EV node))).
    repeat (apply in_or_app; right).
    apply in_flat_map; exists (key, edges); split; [exact Hrow|].
    now apply in_map.
Qed.

(** Every counted event's encoded key width is bounded by the original input. *)
Lemma audit_dfs_counted_event_width {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked roots :
    Forall (fun event => audit_dfs_event_width EV event <= audit_dfs_input_width EV g p roots)
      (snd (audit_dfs_counted p blocked roots)).
Proof.
  pose proof (audit_dfs_counted_keys p blocked roots) as Hkeys.
  eapply Forall_impl; [|exact Hkeys].
  intros event Hin; destruct event; cbn [audit_dfs_event_keys audit_dfs_event_width] in *;
    try lia; now apply audit_dfs_envelope_width.
Qed.

(** Positive bit size has the same value in its binary and unary representations. *)
Lemma audit_dfs_positive_size_nat p : Pos.to_nat (Pos.size p) = Pos.size_nat p.
Proof.
  induction p as [p IH|p IH|]; cbn [Pos.size Pos.size_nat];
    try rewrite Pos2Nat.inj_succ; lia.
Qed.

(** The binary-work model's positive operand width is the positive bit size. *)
Lemma audit_dfs_positive_z_bits p : audit_z_bits (Z.pos p) = Pos.size_nat p.
Proof.
  unfold audit_z_bits; destruct p as [p|p|]; cbn [Z.abs Z.log2 Pos.size_nat Z.to_nat];
    try rewrite audit_dfs_positive_size_nat; reflexivity.
Qed.

(** A positive value no larger than a natural ceiling fits the ceiling's positive bit width. *)
Lemma audit_dfs_clock_width p ceiling :
    Pos.to_nat p <= ceiling -> Pos.size_nat p <= Pos.size_nat (Pos.of_succ_nat ceiling).
Proof.
  intro Hbound.
  apply Pos.size_nat_monotone.
  apply Pos2Nat.inj_lt.
  rewrite SuccNat2Pos.id_succ; lia.
Qed.

(** Every counted clock operand fits the original root-and-fuel numeric ceiling. *)
Lemma audit_dfs_counted_event_clock {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked roots :
    Forall (fun event => audit_dfs_event_clock event <= 2 + length roots * S (Pos.to_nat (fuel p)))
      (snd (audit_dfs_counted p blocked roots)).
Proof.
  unfold audit_dfs_counted.
  pose proof (audit_dfs_roots_event_clock p blocked roots dfs_initial) as Hroots.
  destruct (audit_dfs_roots_counted p blocked roots dfs_initial) as [st events]; cbn in Hroots |- *.
  eapply Forall_impl; [|exact Hroots].
  intros event Hbound; cbn [dfs_initial] in Hbound; cbn in Hbound; lia.
Qed.

(** Key and clock envelopes bound one counted event's model work. *)
Lemma audit_dfs_model_event_bound {V E} (EV : encoding V) (event : audit_dfs_call V E)
    key_width clock_ceiling :
    audit_dfs_event_width EV event <= key_width ->
    audit_dfs_event_clock event <= clock_ceiling ->
    audit_dfs_model_event EV event <=
      80 + 12 * Nat.max key_width (Pos.size_nat (Pos.of_succ_nat clock_ceiling)).
Proof.
  remember (Nat.max key_width (Pos.size_nat (Pos.of_succ_nat clock_ceiling))) as limit eqn:Hlimit.
  assert (Hkeymax : key_width <= limit) by (rewrite Hlimit; apply Nat.le_max_l).
  assert (Hclockmax : Pos.size_nat (Pos.of_succ_nat clock_ceiling) <= limit)
    by (rewrite Hlimit; apply Nat.le_max_r).
  intros Hkey Hclock.
  destruct event as [site|edge target|v set result|v index result|v via before after|v before
    after];
    cbn [audit_dfs_event_width audit_dfs_event_clock] in Hkey, Hclock;
    unfold audit_key_bits_weight in Hkey;
    unfold audit_dfs_model_event, audit_get_weight, audit_set_weight, audit_encoding_weight,
      audit_binary_weight, audit_key_bits_weight;
    cbn; try lia.
  - pose proof (audit_dfs_clock_width (DfsState.pre_clock before) clock_ceiling Hclock) as Hsize.
    unfold audit_set_weight, audit_encoding_weight, audit_key_bits_weight, audit_z_bits.
    destruct via; destruct (DfsState.pre_clock before) as [bits|bits|] eqn:Hpre;
      cbn [Z.abs Z.log2 Z.to_nat Pos.size_nat] in *;
      try rewrite audit_dfs_positive_size_nat in *; lia.
  - pose proof (audit_dfs_clock_width (DfsState.post_clock before) clock_ceiling Hclock) as Hsize.
    unfold audit_set_weight, audit_encoding_weight, audit_key_bits_weight, audit_z_bits.
    destruct (DfsState.post_clock before) as [bits|bits|] eqn:Hpost;
      cbn [Z.abs Z.log2 Z.to_nat Pos.size_nat] in *;
      try rewrite audit_dfs_positive_size_nat in *; lia.
Qed.

(** Summed counted event work is bounded by the common per-event input envelope. *)
Lemma audit_dfs_counted_event_work_bound {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked roots :
    let events := snd (audit_dfs_counted p blocked roots) in
    let width := Nat.max (audit_dfs_input_width EV g p roots)
      (Pos.size_nat (Pos.of_succ_nat (2 + length roots * S (Pos.to_nat (fuel p))))) in
    fold_right (fun event n => audit_dfs_model_event EV event + n) 0 events <=
      length events * (80 + 12 * width).
Proof.
  pose proof (audit_dfs_counted_event_width p blocked roots) as Hwidth.
  pose proof (audit_dfs_counted_event_clock p blocked roots) as Hclock.
  destruct (audit_dfs_counted p blocked roots) as [result events]; cbn in Hwidth, Hclock.
  change (fold_right (fun event n => audit_dfs_model_event EV event + n) 0 events <=
    length events * (80 + 12 * Nat.max (audit_dfs_input_width EV g p roots)
      (Pos.size_nat (Pos.of_succ_nat (2 + length roots * S (Pos.to_nat (fuel p))))))).
  remember (Nat.max (audit_dfs_input_width EV g p roots)
    (Pos.size_nat (Pos.of_succ_nat (2 + length roots * S (Pos.to_nat (fuel p))))))
    as width eqn:Hwidth_eq.
  induction events as [|event events IH].
  - cbn; lia.
  - change (audit_dfs_model_event EV event +
      fold_right (fun item n => audit_dfs_model_event EV item + n) 0 events <=
      S (length events) * (80 + 12 * width)).
    inversion Hwidth as [|? ? Hkey Hwidths].
    inversion Hclock as [|? ? Htime Hclocks].
    specialize (IH Hwidths Hclocks).
    pose proof (audit_dfs_model_event_bound EV event (audit_dfs_input_width EV g p roots)
      (2 + length roots * S (Pos.to_nat (fuel p))) Hkey Htime) as Hevent.
    rewrite <- Hwidth_eq in Hevent.
    change (fold_right (fun item n => audit_dfs_model_event EV item + n) 0 events <=
      length events * (80 + 12 * width)) in IH.
    rewrite Nat.mul_succ_l; lia.
Qed.

(** Counted DFS returns the source result with original-input event and model-work bounds. *)
Theorem audit_dfs_counted_correct : audit_dfs_counted_statement.
Proof.
  intros V E EV g p blocked roots.
  pose proof (audit_dfs_counted_erases p blocked roots) as Herase.
  pose proof (audit_dfs_counted_event_bound p blocked roots) as Hcount.
  pose proof (audit_dfs_counted_event_work_bound p blocked roots) as Hwork.
  destruct (audit_dfs_counted p blocked roots) as [result events].
  cbn in Herase, Hcount, Hwork.
  change (length events <= audit_dfs_input_event_bound p roots) in Hcount.
  change (fold_right (fun event n => audit_dfs_model_event EV event + n) 0 events <=
    length events * (80 + 12 * Nat.max (audit_dfs_input_width EV g p roots)
      (Pos.size_nat (Pos.of_succ_nat (2 + length roots * S (Pos.to_nat (fuel p))))))) in Hwork.
  split; [exact Herase|]; split; [exact Hcount|].
  unfold audit_dfs_model_work, audit_dfs_input_budget.
  change (256 * S (length events) * S (length events) +
    fold_right (fun event n => audit_dfs_model_event EV event + n) 0 events <=
    256 * S (audit_dfs_input_event_bound p roots) * S (audit_dfs_input_event_bound p roots) +
    audit_dfs_input_event_bound p roots * (80 + 12 *
      Nat.max (audit_dfs_input_width EV g p roots)
        (Pos.size_nat (Pos.of_succ_nat (2 + length roots * S (Pos.to_nat (fuel p))))))).
  assert (Hquad : 256 * S (length events) * S (length events) <=
    256 * S (audit_dfs_input_event_bound p roots) * S (audit_dfs_input_event_bound p roots)).
  { apply Nat.mul_le_mono; [apply Nat.mul_le_mono_l|]; lia. }
  assert (Hlinear : length events * (80 + 12 *
      Nat.max (audit_dfs_input_width EV g p roots)
        (Pos.size_nat (Pos.of_succ_nat (2 + length roots * S (Pos.to_nat (fuel p)))))) <=
    audit_dfs_input_event_bound p roots * (80 + 12 *
      Nat.max (audit_dfs_input_width EV g p roots)
        (Pos.size_nat (Pos.of_succ_nat (2 + length roots * S (Pos.to_nat (fuel p))))))).
  { apply Nat.mul_le_mono_r; exact Hcount. }
  lia.
Qed.

(** * Full event bounds *)

(** Full detail events retain the same vertex envelope as their enclosing DFS operation. *)
Definition audit_dfs_full_event_keys {V E} (vertices : list V)
    (event : audit_dfs_full_call V E) : Prop :=
  match event with
  | AuditDfsFullTarget _ v
  | AuditDfsFullMember v _ _
  | AuditDfsFullSuccessors v _ _
  | AuditDfsFullDiscover v _ _ _
  | AuditDfsFullFinish v _ _ => In v vertices
  | AuditDfsFullDetail detail =>
    match detail with
    | AuditDfsParentSet v _ _
    | AuditDfsNumSet v _ _
    | AuditDfsSeenAdd v _ => In v vertices
    | AuditDfsClock _ _ => True
    end
  | _ => True
  end.

(** One full counted step preserves stack provenance and emits only vertices in the envelope. *)
Lemma audit_dfs_full_step_keys {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked vertices work :
    let edges := flat_map snd (Map.elements (out_index p)) in
    (forall edge, In edge edges -> In (Graph.target g edge) vertices) ->
    audit_dfs_stack_keys vertices edges (fst work) ->
    Forall (audit_dfs_full_event_keys vertices) (snd (audit_dfs_full_step_counted p blocked work))
      /\
    audit_dfs_stack_keys vertices edges (fst (fst (audit_dfs_full_step_counted p blocked work))).
Proof.
  intros edges Hall Hstack; subst edges; unfold audit_dfs_stack_keys in *.
  destruct work as [stack st], stack as [|[v outgoing] rest]; cbn [audit_dfs_full_step_counted] in
    *.
  - split; constructor; [exact I|constructor].
  - cbn in Hstack.
    inversion Hstack as [|frame tail Hframe Hrest]; subst frame tail.
    cbn in Hframe; destruct Hframe as [Hv Hedges].
    destruct outgoing as [|edge outgoing].
    + split.
      * repeat constructor; cbn [audit_dfs_full_event_keys]; assumption.
      * exact Hrest.
    + assert (Htarget : In (Graph.target g edge) vertices).
      { apply Hall, Hedges; left; reflexivity. }
      assert (Htail : incl outgoing (flat_map snd (Map.elements (out_index p)))).
      { intros x Hin; apply Hedges; right; exact Hin. }
      destruct (FinSet.mem EV (Graph.target g edge) blocked ||
        FinSet.mem EV (Graph.target g edge) (DfsState.seen st)); cbn.
      * split.
        -- repeat constructor; cbn [audit_dfs_full_event_keys]; auto.
        -- constructor; [cbn; auto|exact Hrest].
      * destruct (Map.get EV (Graph.target g edge) (out_index p)) as [next_edges|] eqn:Hget; cbn.
        -- split.
           ++ repeat constructor; cbn [audit_dfs_full_event_keys]; auto.
           ++ constructor.
              ** cbn; split; [exact Htarget|]. now apply (audit_dfs_outgoing_edges p _ _ Hget).
              ** constructor; [cbn; auto|exact Hrest].
        -- split.
           ++ repeat constructor; cbn [audit_dfs_full_event_keys]; auto.
           ++ constructor; [cbn; split; [exact Htarget|intros x Hfalse; contradiction]|].
              constructor; [cbn; auto|exact Hrest].
Qed.

(** Binary full traversal preserves stack provenance and its events' key envelope. *)
Lemma audit_dfs_full_run_keys {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked vertices fuel work :
    let edges := flat_map snd (Map.elements (out_index p)) in
    (forall edge, In edge edges -> In (Graph.target g edge) vertices) ->
    audit_dfs_stack_keys vertices edges (fst work) ->
    Forall (audit_dfs_full_event_keys vertices) (snd (audit_dfs_full_run_counted p blocked fuel
      work)) /\
    audit_dfs_stack_keys vertices edges (fst (fst (audit_dfs_full_run_counted p blocked fuel
      work))).
Proof.
  intros edges Hall; subst edges; revert work.
  induction fuel as [fuel IH|fuel IH|]; intros [stack st] Hstack; destruct stack as [|frame stack].
  - cbn [audit_dfs_full_run_counted]; split; [repeat constructor|exact Hstack].
  - change (Forall (audit_dfs_full_event_keys vertices)
      (snd (let '(middle, first) := audit_dfs_full_run_counted p blocked fuel (frame :: stack, st)
        in
        let '(last, second) := audit_dfs_full_run_counted p blocked fuel middle in
        let '(result, events) := audit_dfs_full_step_counted p blocked last in
        (result, AuditDfsFullCase 7 :: first ++ second ++ events))) /\
      audit_dfs_stack_keys vertices (flat_map snd (Map.elements (out_index p)))
      (fst (fst (let '(middle, first) :=
          audit_dfs_full_run_counted p blocked fuel (frame :: stack, st) in
        let '(last, second) := audit_dfs_full_run_counted p blocked fuel middle in
        let '(result, events) := audit_dfs_full_step_counted p blocked last in
        (result, AuditDfsFullCase 7 :: first ++ second ++ events))))).
    pose proof (IH (frame :: stack, st) Hstack) as [Hfirst Hmiddle].
    destruct (audit_dfs_full_run_counted p blocked fuel (frame :: stack, st)) as [middle first].
    cbn in Hfirst, Hmiddle |- *.
    pose proof (IH middle Hmiddle) as [Hsecond Hlast].
    destruct (audit_dfs_full_run_counted p blocked fuel middle) as [last second].
    cbn in Hsecond, Hlast |- *.
    pose proof (audit_dfs_full_step_keys p blocked vertices last Hall Hlast) as [Hstep Hresult].
    destruct (audit_dfs_full_step_counted p blocked last) as [result events]; cbn in Hstep,
      Hresult |- *.
    split; [constructor; [exact I|rewrite !Forall_app; auto]|exact Hresult].
  - cbn [audit_dfs_full_run_counted]; split; [repeat constructor|exact Hstack].
  - change (Forall (audit_dfs_full_event_keys vertices)
      (snd (let '(middle, first) := audit_dfs_full_run_counted p blocked fuel (frame :: stack, st)
        in
        let '(result, second) := audit_dfs_full_run_counted p blocked fuel middle in
        (result, AuditDfsFullCase 6 :: first ++ second))) /\
      audit_dfs_stack_keys vertices (flat_map snd (Map.elements (out_index p)))
      (fst (fst (let '(middle, first) :=
          audit_dfs_full_run_counted p blocked fuel (frame :: stack, st) in
        let '(result, second) := audit_dfs_full_run_counted p blocked fuel middle in
        (result, AuditDfsFullCase 6 :: first ++ second))))).
    pose proof (IH (frame :: stack, st) Hstack) as [Hfirst Hmiddle].
    destruct (audit_dfs_full_run_counted p blocked fuel (frame :: stack, st)) as [middle first].
    cbn in Hfirst, Hmiddle |- *.
    pose proof (IH middle Hmiddle) as [Hsecond Hresult].
    destruct (audit_dfs_full_run_counted p blocked fuel middle) as [result second].
    cbn in Hsecond, Hresult |- *.
    split; [constructor; [exact I|rewrite Forall_app; auto]|exact Hresult].
  - cbn [audit_dfs_full_run_counted]; split; [repeat constructor|exact Hstack].
  - change (Forall (audit_dfs_full_event_keys vertices)
      (snd (let '(result, events) := audit_dfs_full_step_counted p blocked (frame :: stack, st) in
        (result, AuditDfsFullCase 5 :: events))) /\
      audit_dfs_stack_keys vertices (flat_map snd (Map.elements (out_index p)))
      (fst (fst (let '(result, events) := audit_dfs_full_step_counted p blocked (frame :: stack,
        st) in
        (result, AuditDfsFullCase 5 :: events))))).
    pose proof (audit_dfs_full_step_keys p blocked vertices (frame :: stack, st) Hall Hstack)
      as [Hstep Hresult].
    destruct (audit_dfs_full_step_counted p blocked (frame :: stack, st)); cbn in Hstep, Hresult
      |- *.
    split; [constructor; [exact I|exact Hstep]|exact Hresult].
Qed.

(** A full counted root in the envelope emits only envelope vertices. *)
Lemma audit_dfs_full_root_keys {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked vertices st v :
    (forall edge, In edge (flat_map snd (Map.elements (out_index p))) ->
      In (Graph.target g edge) vertices) ->
    In v vertices ->
    Forall (audit_dfs_full_event_keys vertices) (snd (audit_dfs_full_root_counted p blocked st v)).
Proof.
  intros Hall Hv; unfold audit_dfs_full_root_counted.
  destruct (FinSet.mem EV v blocked || FinSet.mem EV v (DfsState.seen st)); cbn.
  - repeat constructor; cbn [audit_dfs_full_event_keys]; auto.
  - destruct (Map.get EV v (out_index p)) as [outgoing|] eqn:Hget.
    + cbn [audit_dfs_discover_counted].
      assert (Hstack : audit_dfs_stack_keys vertices (flat_map snd (Map.elements (out_index p)))
        [(v, outgoing)]).
      { constructor; [cbn; split; [exact Hv|now apply (audit_dfs_outgoing_edges p _ _ Hget)]|].
        constructor. }
      pose proof (audit_dfs_full_run_keys p blocked vertices (fuel p)
        ([(v, outgoing)], dfs_discover EV v None st) Hall Hstack) as [Hrun _].
      destruct (audit_dfs_full_run_counted p blocked (fuel p)
        ([(v, outgoing)], dfs_discover EV v None st)) eqn:Hrun_eq; cbn in Hrun |- *.
      unfold dfs_discover in Hrun_eq; rewrite Hrun_eq; cbn.
      repeat constructor; cbn [audit_dfs_full_event_keys]; auto.
    + cbn [audit_dfs_discover_counted].
      assert (Hstack : audit_dfs_stack_keys vertices (flat_map snd (Map.elements (out_index p)))
        [(v, [])]).
      { constructor; [cbn; split; [exact Hv|intros x Hfalse; contradiction]|constructor]. }
      pose proof (audit_dfs_full_run_keys p blocked vertices (fuel p)
        ([(v, [])], dfs_discover EV v None st) Hall Hstack) as [Hrun _].
      destruct (audit_dfs_full_run_counted p blocked (fuel p)
        ([(v, [])], dfs_discover EV v None st)) eqn:Hrun_eq; cbn in Hrun |- *.
      unfold dfs_discover in Hrun_eq; rewrite Hrun_eq; cbn.
      repeat constructor; cbn [audit_dfs_full_event_keys]; auto.
Qed.

(** Processing full counted roots in the envelope emits only vertices in that envelope. *)
Lemma audit_dfs_full_roots_keys {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked vertices roots st :
    (forall edge, In edge (flat_map snd (Map.elements (out_index p))) ->
      In (Graph.target g edge) vertices) ->
    incl roots vertices ->
    Forall (audit_dfs_full_event_keys vertices) (snd (audit_dfs_full_roots_counted p blocked roots
      st)).
Proof.
  intros Hall; revert st; induction roots as [|root roots IH]; intros st Hroots.
  - cbn [audit_dfs_full_roots_counted]; repeat constructor.
  - cbn [audit_dfs_full_roots_counted].
    pose proof (audit_dfs_full_root_keys p blocked vertices st root Hall (Hroots root (or_introl
      eq_refl)))
      as Hroot.
    destruct (audit_dfs_full_root_counted p blocked st root) as [next here]; cbn in Hroot |- *.
    specialize (IH next ltac:(intros v Hv; apply Hroots; right; exact Hv)).
    destruct (audit_dfs_full_roots_counted p blocked roots next) as [result later]; cbn in IH |- *.
    constructor; [exact I|]. apply Forall_app; split; assumption.
Qed.

(** Every full counted event vertex is either a root or a target of an indexed edge. *)
Lemma audit_dfs_full_counted_keys {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked roots :
    let vertices := roots ++ map (Graph.target g) (flat_map snd (Map.elements (out_index p))) in
    Forall (audit_dfs_full_event_keys vertices) (snd (audit_dfs_full_counted p blocked roots)).
Proof.
  intro vertices; subst vertices; unfold audit_dfs_full_counted.
  pose proof (audit_dfs_full_roots_keys p blocked
    (roots ++ map (Graph.target g) (flat_map snd (Map.elements (out_index p)))) roots dfs_initial)
    as Hroots.
  assert (Hall : forall edge, In edge (flat_map snd (Map.elements (out_index p))) ->
      In (Graph.target g edge)
        (roots ++ map (Graph.target g) (flat_map snd (Map.elements (out_index p)))))
    by (intros edge Hin; apply in_or_app; right; now apply in_map).
  assert (Hincl : incl roots
    (roots ++ map (Graph.target g) (flat_map snd (Map.elements (out_index p)))))
    by (intros v Hin; apply in_or_app; now left).
  specialize (Hroots Hall Hincl).
  destruct (audit_dfs_full_roots_counted p blocked roots dfs_initial) as [st events].
  cbn in Hroots |- *; apply Forall_app; split; [exact Hroots|repeat constructor].
Qed.

(** The encoded width of a full event vertex, or zero when no vertex appears. *)
Definition audit_dfs_full_event_width {V E} (EV : encoding V)
    (event : audit_dfs_full_call V E) : nat :=
  match event with
  | AuditDfsFullTarget _ v
  | AuditDfsFullMember v _ _
  | AuditDfsFullSuccessors v _ _
  | AuditDfsFullDiscover v _ _ _
  | AuditDfsFullFinish v _ _ => audit_key_bits_weight (encode EV v)
  | AuditDfsFullDetail detail =>
    match detail with
    | AuditDfsParentSet v _ _
    | AuditDfsNumSet v _ _
    | AuditDfsSeenAdd v _ => audit_key_bits_weight (encode EV v)
    | AuditDfsClock _ _ => 0
    end
  | _ => 0
  end.

(** Full-event encoded vertex widths are bounded by the original graph input. *)
Lemma audit_dfs_full_counted_event_width {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked roots :
    Forall (fun event => audit_dfs_full_event_width EV event <= audit_dfs_full_input_width EV g p
      roots)
      (snd (audit_dfs_full_counted p blocked roots)).
Proof.
  pose proof (audit_dfs_full_counted_keys p blocked roots) as Hkeys.
  eapply Forall_impl; [|exact Hkeys].
  intros event Hin; destruct event; cbn [audit_dfs_full_event_keys audit_dfs_full_event_width] in *;
    try lia; try (apply audit_dfs_envelope_width; exact Hin).
  destruct detail; cbn [audit_dfs_full_event_keys audit_dfs_full_event_width] in *;
    try lia; now apply audit_dfs_envelope_width.
Qed.

(** Full clock detail events expose the positive value passed to successor. *)
Definition audit_dfs_full_event_clock {V E} (event : audit_dfs_full_call V E) : nat :=
  match event with
  | AuditDfsFullDetail (AuditDfsClock before _) => Pos.to_nat before
  | _ => 0
  end.

(** A full step's clock details use only clocks in the input state. *)
Lemma audit_dfs_full_step_event_clock {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked work :
    Forall (fun event => audit_dfs_full_event_clock event <=
      Nat.max (Pos.to_nat (DfsState.pre_clock (snd work)))
        (Pos.to_nat (DfsState.post_clock (snd work))))
      (snd (audit_dfs_full_step_counted p blocked work)).
Proof.
  destruct work as [stack st], stack as [|[v edges] rest]; cbn [audit_dfs_full_step_counted].
  - repeat constructor; cbn [audit_dfs_full_event_clock]; lia.
  - destruct edges as [|edge edges].
    + cbn [audit_dfs_finish_counted]; cbn; repeat constructor;
        cbn [audit_dfs_full_event_clock]; try lia; apply Nat.le_max_r.
    + destruct (FinSet.mem EV (Graph.target g edge) blocked ||
        FinSet.mem EV (Graph.target g edge) (DfsState.seen st)); cbn.
      * repeat constructor; cbn [audit_dfs_full_event_clock]; lia.
      * cbn [audit_dfs_discover_counted]; cbn; repeat constructor;
          cbn [audit_dfs_full_event_clock]; try lia; apply Nat.le_max_l.
Qed.

(** Every clock charged by a binary full counted run is bounded by its input clocks and fuel. *)
Lemma audit_dfs_full_run_event_clock {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked fuel work :
    Forall (fun event => audit_dfs_full_event_clock event <=
      Nat.max (Pos.to_nat (DfsState.pre_clock (snd work)))
        (Pos.to_nat (DfsState.post_clock (snd work))) + Pos.to_nat fuel)
      (snd (audit_dfs_full_run_counted p blocked fuel work)).
Proof.
  revert work; induction fuel as [fuel IH|fuel IH|]; intros [stack st];
    destruct stack as [|frame stack].
  - cbn [audit_dfs_full_run_counted]; repeat constructor; cbn [audit_dfs_full_event_clock]; lia.
  - change (Forall (fun event => audit_dfs_full_event_clock event <=
      Nat.max (Pos.to_nat (DfsState.pre_clock st)) (Pos.to_nat (DfsState.post_clock st)) +
        Pos.to_nat (xI fuel)) (snd (let '(middle, first) :=
        audit_dfs_full_run_counted p blocked fuel (frame :: stack, st) in
      let '(last, second) := audit_dfs_full_run_counted p blocked fuel middle in
      let '(result, events) := audit_dfs_full_step_counted p blocked last in
      (result, AuditDfsFullCase 7 :: first ++ second ++ events)))).
    pose proof (IH (frame :: stack, st)) as Hfirst.
    pose proof (audit_dfs_run_max_clock_bound p blocked fuel (frame :: stack, st)) as Hmax1.
    pose proof (audit_dfs_full_run_erases p blocked fuel (frame :: stack, st)) as Herase1.
    destruct (audit_dfs_full_run_counted p blocked fuel (frame :: stack, st)) as [middle first].
    cbn in Hfirst, Herase1 |- *; rewrite <- Herase1 in Hmax1.
    pose proof (IH middle) as Hsecond.
    pose proof (audit_dfs_run_max_clock_bound p blocked fuel middle) as Hmax2.
    pose proof (audit_dfs_full_run_erases p blocked fuel middle) as Herase2.
    destruct (audit_dfs_full_run_counted p blocked fuel middle) as [last second].
    cbn in Hsecond, Herase2 |- *; rewrite <- Herase2 in Hmax2.
    pose proof (audit_dfs_full_step_event_clock p blocked last) as Hstep.
    destruct (audit_dfs_full_step_counted p blocked last) as [result events]; cbn in Hstep |- *.
    constructor; [cbn [audit_dfs_full_event_clock]; lia|].
    rewrite !Forall_app; rewrite Pos2Nat.inj_xI.
    split; [|split].
    all: eapply Forall_impl; [|eassumption].
    all: intros event Hbound; cbn in Hbound, Hmax1, Hmax2; lia.
  - cbn [audit_dfs_full_run_counted]; repeat constructor; cbn [audit_dfs_full_event_clock]; lia.
  - change (Forall (fun event => audit_dfs_full_event_clock event <=
      Nat.max (Pos.to_nat (DfsState.pre_clock st)) (Pos.to_nat (DfsState.post_clock st)) +
        Pos.to_nat (xO fuel)) (snd (let '(middle, first) :=
        audit_dfs_full_run_counted p blocked fuel (frame :: stack, st) in
      let '(result, second) := audit_dfs_full_run_counted p blocked fuel middle in
      (result, AuditDfsFullCase 6 :: first ++ second)))).
    pose proof (IH (frame :: stack, st)) as Hfirst.
    pose proof (audit_dfs_run_max_clock_bound p blocked fuel (frame :: stack, st)) as Hmax.
    pose proof (audit_dfs_full_run_erases p blocked fuel (frame :: stack, st)) as Herase.
    destruct (audit_dfs_full_run_counted p blocked fuel (frame :: stack, st)) as [middle first].
    cbn in Hfirst, Herase |- *; rewrite <- Herase in Hmax.
    pose proof (IH middle) as Hsecond.
    destruct (audit_dfs_full_run_counted p blocked fuel middle) as [result second]; cbn in Hsecond
      |- *.
    constructor; [cbn [audit_dfs_full_event_clock]; lia|].
    rewrite Forall_app; rewrite Pos2Nat.inj_xO.
    split.
    all: eapply Forall_impl; [|eassumption].
    all: intros event Hbound; cbn in Hbound, Hmax; lia.
  - cbn [audit_dfs_full_run_counted]; repeat constructor; cbn [audit_dfs_full_event_clock]; lia.
  - change (Forall (fun event => audit_dfs_full_event_clock event <=
      Nat.max (Pos.to_nat (DfsState.pre_clock st)) (Pos.to_nat (DfsState.post_clock st)) +
        Pos.to_nat xH) (snd (let '(result, events) :=
        audit_dfs_full_step_counted p blocked (frame :: stack, st) in
      (result, AuditDfsFullCase 5 :: events)))).
    pose proof (audit_dfs_full_step_event_clock p blocked (frame :: stack, st)) as Hstep.
    destruct (audit_dfs_full_step_counted p blocked (frame :: stack, st)); cbn in Hstep |- *.
    constructor; [cbn [audit_dfs_full_event_clock]; lia|].
    eapply Forall_impl; [|exact Hstep]; intros event Hbound; cbn in *; lia.
Qed.

(** A root's full counted events charge at most its starting maximum clock plus discovery and
  fuel. *)
Lemma audit_dfs_full_root_event_clock {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked st v :
    Forall (fun event => audit_dfs_full_event_clock event <=
      Nat.max (Pos.to_nat (DfsState.pre_clock st)) (Pos.to_nat (DfsState.post_clock st)) +
        S (Pos.to_nat (fuel p))) (snd (audit_dfs_full_root_counted p blocked st v)).
Proof.
  unfold audit_dfs_full_root_counted.
  destruct (FinSet.mem EV v blocked || FinSet.mem EV v (DfsState.seen st)); cbn.
  - repeat constructor; cbn [audit_dfs_full_event_clock]; lia.
  - pose proof (audit_dfs_full_run_event_clock p blocked (fuel p)
      ([(v, index_edges EV (out_index p) v)], dfs_discover EV v None st)) as Hrun.
    unfold index_edges in Hrun.
    destruct (audit_dfs_full_run_counted p blocked (fuel p)
      ([(v, index_edges EV (out_index p) v)], dfs_discover EV v None st))
      as [result events] eqn:Hrun_eq.
    unfold index_edges in Hrun_eq; rewrite Hrun_eq in Hrun; cbn in Hrun.
    cbn [audit_dfs_discover_counted].
    unfold dfs_discover in Hrun_eq; rewrite Hrun_eq; cbn.
    repeat constructor; cbn [audit_dfs_full_event_clock]; try lia.
    eapply Forall_impl; [|exact Hrun].
    intros event Hbound; cbn [dfs_discover] in Hbound; cbn in Hbound.
    rewrite Pos2Nat.inj_succ in Hbound.
    assert (Hmax : Nat.max (S (Pos.to_nat (DfsState.pre_clock st)))
      (Pos.to_nat (DfsState.post_clock st)) <=
      S (Nat.max (Pos.to_nat (DfsState.pre_clock st)) (Pos.to_nat (DfsState.post_clock st)))).
    { apply Nat.max_lub; pose proof (Nat.le_max_l (Pos.to_nat (DfsState.pre_clock st))
        (Pos.to_nat (DfsState.post_clock st)));
        pose proof (Nat.le_max_r (Pos.to_nat (DfsState.pre_clock st))
        (Pos.to_nat (DfsState.post_clock st))); lia. }
    lia.
Qed.

(** Full root events charge clocks bounded by the initial clocks and the remaining root budget. *)
Lemma audit_dfs_full_roots_event_clock {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked roots st :
    Forall (fun event => audit_dfs_full_event_clock event <=
      Nat.max (Pos.to_nat (DfsState.pre_clock st)) (Pos.to_nat (DfsState.post_clock st)) +
        length roots * S (Pos.to_nat (fuel p)))
      (snd (audit_dfs_full_roots_counted p blocked roots st)).
Proof.
  revert st; induction roots as [|root roots IH]; intro st; cbn [audit_dfs_full_roots_counted
    length].
  - repeat constructor; cbn [audit_dfs_full_event_clock]; lia.
  - pose proof (audit_dfs_full_root_event_clock p blocked st root) as Hroot.
    pose proof (audit_dfs_root_clock_bound p blocked st root) as [Hpre Hpost].
    pose proof (audit_dfs_full_root_erases p blocked st root) as Herase.
    destruct (audit_dfs_full_root_counted p blocked st root) as [next here]; cbn in Hroot, Herase
      |- *.
    rewrite <- Herase in Hpre, Hpost.
    specialize (IH next).
    destruct (audit_dfs_full_roots_counted p blocked roots next) as [result later]; cbn in IH |- *.
    constructor; [cbn [audit_dfs_full_event_clock]; lia|].
    apply Forall_app; split.
    + eapply Forall_impl; [|exact Hroot].
      intros event Hbound; cbn in Hbound; nia.
    + eapply Forall_impl; [|exact IH].
      intros event Hbound; cbn in Hbound.
      assert (Hmax : Nat.max (Pos.to_nat (DfsState.pre_clock next))
        (Pos.to_nat (DfsState.post_clock next)) <=
        Nat.max (Pos.to_nat (DfsState.pre_clock st)) (Pos.to_nat (DfsState.post_clock st)) +
          S (Pos.to_nat (fuel p))).
      { apply Nat.max_lub; pose proof (Nat.le_max_l (Pos.to_nat (DfsState.pre_clock st))
          (Pos.to_nat (DfsState.post_clock st)));
          pose proof (Nat.le_max_r (Pos.to_nat (DfsState.pre_clock st))
          (Pos.to_nat (DfsState.post_clock st))); lia. }
      nia.
Qed.

(** Every full clock detail fits the original root-and-fuel numeric ceiling. *)
Lemma audit_dfs_full_counted_event_clock {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked roots :
    Forall (fun event => audit_dfs_full_event_clock event <=
      2 + length roots * S (Pos.to_nat (fuel p))) (snd (audit_dfs_full_counted p blocked roots)).
Proof.
  unfold audit_dfs_full_counted.
  pose proof (audit_dfs_full_roots_event_clock p blocked roots dfs_initial) as Hroots.
  destruct (audit_dfs_full_roots_counted p blocked roots dfs_initial) as [st events].
  cbn in Hroots |- *; apply Forall_app; split.
  - eapply Forall_impl; [|exact Hroots].
    intros event Hbound; cbn [dfs_initial] in Hbound; cbn in Hbound; lia.
  - repeat constructor; cbn [audit_dfs_full_event_clock]; lia.
Qed.

(** DFS list lengths remain strictly below the clocks used to number those lists. *)
Definition audit_dfs_list_clock_invariant {V E} (st : DfsState.t V E) : Prop :=
  length (DfsState.pre st) < Pos.to_nat (DfsState.pre_clock st) /\
  length (DfsState.post st) < Pos.to_nat (DfsState.post_clock st).

(** A source DFS step preserves the list-length and clock invariant. *)
Lemma audit_dfs_step_list_clock {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked work :
    audit_dfs_list_clock_invariant (snd work) ->
    audit_dfs_list_clock_invariant (snd (dfs_step p blocked work)).
Proof.
  destruct work as [stack st], stack as [|[v edges] rest]; cbn [dfs_step]; intro Hinv.
  - exact Hinv.
  - destruct edges as [|edge edges].
    + unfold audit_dfs_list_clock_invariant in *; cbn [dfs_finish] in *; cbn in *.
      rewrite Pos2Nat.inj_succ; lia.
    + destruct (FinSet.mem EV (Graph.target g edge) blocked ||
        FinSet.mem EV (Graph.target g edge) (DfsState.seen st)); [exact Hinv|].
      unfold audit_dfs_list_clock_invariant in *; cbn [dfs_discover] in *; cbn in *.
      rewrite Pos2Nat.inj_succ; lia.
Qed.

(** Every binary source run preserves the list-length and clock invariant. *)
Lemma audit_dfs_run_list_clock {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked fuel work :
    audit_dfs_list_clock_invariant (snd work) ->
    audit_dfs_list_clock_invariant (snd (dfs_run p blocked fuel work)).
Proof.
  revert work; induction fuel as [fuel IH|fuel IH|]; intros [stack st] Hinv;
    destruct stack as [|frame stack]; cbn [dfs_run fst]; try exact Hinv.
  - apply audit_dfs_step_list_clock, IH, IH; exact Hinv.
  - apply IH, IH; exact Hinv.
  - apply audit_dfs_step_list_clock; exact Hinv.
Qed.

(** Each root preserves the invariant between output lengths and numbering clocks. *)
Lemma audit_dfs_root_list_clock {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked st v :
    audit_dfs_list_clock_invariant st -> audit_dfs_list_clock_invariant (dfs_root p blocked st v).
Proof.
  intro Hinv; unfold dfs_root.
  destruct (FinSet.mem EV v blocked || FinSet.mem EV v (DfsState.seen st)); [exact Hinv|].
  apply audit_dfs_run_list_clock.
  unfold audit_dfs_list_clock_invariant in *; cbn [dfs_discover] in *; cbn in *.
  rewrite Pos2Nat.inj_succ; lia.
Qed.

(** The source fold maintains the list-length and numbering-clock invariant. *)
Lemma audit_dfs_roots_list_clock {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked roots st :
    audit_dfs_list_clock_invariant st ->
    audit_dfs_list_clock_invariant (fold_left (dfs_root p blocked) roots st).
Proof.
  revert st; induction roots as [|root roots IH]; intros st Hinv; cbn [fold_left].
  - exact Hinv.
  - apply IH, audit_dfs_root_list_clock; exact Hinv.
Qed.

(** The output event carries both actual output-list lengths. *)
Definition audit_dfs_full_event_output {V E} (event : audit_dfs_full_call V E) : nat :=
  match event with
  | AuditDfsFullOutput pre post => pre + post
  | _ => 0
  end.

(** Every event from a full DFS step contributes zero to the output-length measure. *)
Lemma audit_dfs_full_step_output_zero {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked work :
    Forall (fun event => audit_dfs_full_event_output event = 0)
      (snd (audit_dfs_full_step_counted p blocked work)).
Proof.
  destruct work as [stack st], stack as [|[v edges] rest]; cbn [audit_dfs_full_step_counted].
  - repeat constructor.
  - destruct edges as [|edge edges].
    + cbn [audit_dfs_finish_counted]; cbn; repeat constructor.
    + destruct (FinSet.mem EV (Graph.target g edge) blocked ||
        FinSet.mem EV (Graph.target g edge) (DfsState.seen st)); cbn.
      * repeat constructor.
      * cbn [audit_dfs_discover_counted]; cbn; repeat constructor.
Qed.

(** Every event from a binary full DFS run contributes zero to the output-length measure. *)
Lemma audit_dfs_full_run_output_zero {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked fuel work :
    Forall (fun event => audit_dfs_full_event_output event = 0)
      (snd (audit_dfs_full_run_counted p blocked fuel work)).
Proof.
  revert work; induction fuel as [fuel IH|fuel IH|]; intros [stack st];
    destruct stack as [|frame stack].
  - repeat constructor.
  - change (Forall (fun event => audit_dfs_full_event_output event = 0)
      (snd (let '(middle, first) := audit_dfs_full_run_counted p blocked fuel (frame :: stack, st)
        in
        let '(last, second) := audit_dfs_full_run_counted p blocked fuel middle in
        let '(result, events) := audit_dfs_full_step_counted p blocked last in
        (result, AuditDfsFullCase 7 :: first ++ second ++ events)))).
    pose proof (IH (frame :: stack, st)) as Hfirst.
    destruct (audit_dfs_full_run_counted p blocked fuel (frame :: stack, st)) as [middle first].
    cbn in Hfirst |- *.
    pose proof (IH middle) as Hsecond.
    destruct (audit_dfs_full_run_counted p blocked fuel middle) as [last second]; cbn in Hsecond
      |- *.
    pose proof (audit_dfs_full_step_output_zero p blocked last) as Hstep.
    destruct (audit_dfs_full_step_counted p blocked last) as [result events]; cbn in Hstep |- *.
    constructor; [reflexivity|]. rewrite !Forall_app; auto.
  - repeat constructor.
  - change (Forall (fun event => audit_dfs_full_event_output event = 0)
      (snd (let '(middle, first) := audit_dfs_full_run_counted p blocked fuel (frame :: stack, st)
        in
        let '(result, second) := audit_dfs_full_run_counted p blocked fuel middle in
        (result, AuditDfsFullCase 6 :: first ++ second)))).
    pose proof (IH (frame :: stack, st)) as Hfirst.
    destruct (audit_dfs_full_run_counted p blocked fuel (frame :: stack, st)) as [middle first].
    cbn in Hfirst |- *.
    pose proof (IH middle) as Hsecond.
    destruct (audit_dfs_full_run_counted p blocked fuel middle) as [result events]; cbn in Hsecond
      |- *.
    constructor; [reflexivity|]. apply Forall_app; auto.
  - repeat constructor.
  - change (Forall (fun event => audit_dfs_full_event_output event = 0)
      (snd (let '(result, events) := audit_dfs_full_step_counted p blocked (frame :: stack, st) in
        (result, AuditDfsFullCase 5 :: events)))).
    pose proof (audit_dfs_full_step_output_zero p blocked (frame :: stack, st)) as Hstep.
    destruct (audit_dfs_full_step_counted p blocked (frame :: stack, st)); cbn in Hstep |- *.
    constructor; [reflexivity|exact Hstep].
Qed.

(** Every event from a full root contributes zero to the output-length measure. *)
Lemma audit_dfs_full_root_output_zero {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked st v :
    Forall (fun event => audit_dfs_full_event_output event = 0)
      (snd (audit_dfs_full_root_counted p blocked st v)).
Proof.
  unfold audit_dfs_full_root_counted.
  destruct (FinSet.mem EV v blocked || FinSet.mem EV v (DfsState.seen st)); cbn.
  - repeat constructor.
  - cbn [audit_dfs_discover_counted].
    pose proof (audit_dfs_full_run_output_zero p blocked (fuel p)
      ([(v, index_edges EV (out_index p) v)], dfs_discover EV v None st)) as Hrun.
    destruct (audit_dfs_full_run_counted p blocked (fuel p)
      ([(v, index_edges EV (out_index p) v)], dfs_discover EV v None st))
      as [result events] eqn:Hrun_eq.
    cbn in Hrun; unfold index_edges, dfs_discover in Hrun_eq.
    rewrite Hrun_eq; cbn; repeat constructor; exact Hrun.
Qed.

(** Every event from the full root fold contributes zero to the output-length measure. *)
Lemma audit_dfs_full_roots_output_zero {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked roots st :
    Forall (fun event => audit_dfs_full_event_output event = 0)
      (snd (audit_dfs_full_roots_counted p blocked roots st)).
Proof.
  revert st; induction roots as [|root roots IH]; intro st; cbn [audit_dfs_full_roots_counted].
  - repeat constructor.
  - pose proof (audit_dfs_full_root_output_zero p blocked st root) as Hroot.
    destruct (audit_dfs_full_root_counted p blocked st root) as [next here]; cbn in Hroot |- *.
    specialize (IH next).
    destruct (audit_dfs_full_roots_counted p blocked roots next) as [result later]; cbn in IH |- *.
    constructor; [reflexivity|]. apply Forall_app; split; assumption.
Qed.

(** The full receipt's output event is bounded by the original root-and-fuel ceiling. *)
Lemma audit_dfs_full_counted_event_output {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked roots :
    Forall (fun event => audit_dfs_full_event_output event <=
      2 * (2 + length roots * S (Pos.to_nat (fuel p))))
      (snd (audit_dfs_full_counted p blocked roots)).
Proof.
  unfold audit_dfs_full_counted.
  pose proof (audit_dfs_full_roots_output_zero p blocked roots dfs_initial) as Hzero.
  pose proof (audit_dfs_full_roots_erase p blocked roots dfs_initial) as Herase.
  pose proof (audit_dfs_roots_clock_bound p blocked roots dfs_initial) as [Hpre Hpost].
  assert (Hinit : audit_dfs_list_clock_invariant (@dfs_initial V E)).
  { unfold audit_dfs_list_clock_invariant, dfs_initial; cbn; lia. }
  pose proof (audit_dfs_roots_list_clock p blocked roots dfs_initial Hinit) as Hlength.
  destruct (audit_dfs_full_roots_counted p blocked roots dfs_initial) as [st events].
  cbn in Hzero, Herase |- *; rewrite <- Herase in Hpre, Hpost, Hlength.
  unfold audit_dfs_list_clock_invariant in Hlength; cbn [dfs_initial] in Hpre, Hpost.
  apply Forall_app; split.
  - eapply Forall_impl; [|exact Hzero]. intros event Houtput; cbn in Houtput; lia.
  - constructor; [cbn [audit_dfs_full_event_output]; cbn [dfs_initial] in Hpre, Hpost; cbn in
    Hpre, Hpost; lia|constructor].
Qed.

(** Full event work is bounded by its key and clock widths and its actual output length. *)
Lemma audit_dfs_full_model_event_bound {V E} (EV : encoding V)
    (event : audit_dfs_full_call V E) key_width clock_ceiling :
    audit_dfs_full_event_width EV event <= key_width ->
    audit_dfs_full_event_clock event <= clock_ceiling ->
    audit_dfs_full_model_event EV event <=
      140 + 12 * Nat.max key_width (Pos.size_nat (Pos.of_succ_nat clock_ceiling)) +
        audit_dfs_full_event_output event.
Proof.
  remember (Nat.max key_width (Pos.size_nat (Pos.of_succ_nat clock_ceiling))) as limit eqn:Hlimit.
  assert (Hkeymax : key_width <= limit) by (rewrite Hlimit; apply Nat.le_max_l).
  assert (Hclockmax : Pos.size_nat (Pos.of_succ_nat clock_ceiling) <= limit)
    by (rewrite Hlimit; apply Nat.le_max_r).
  intros Hkey Hclock.
  destruct event as [site|edge target|v set result|v index result|v via before after|
      v before after|detail|pre post];
    cbn [audit_dfs_full_event_width audit_dfs_full_event_clock] in Hkey, Hclock;
    unfold audit_key_bits_weight in Hkey;
    unfold audit_dfs_full_model_event, audit_dfs_full_event_output, audit_get_weight,
      audit_set_weight, audit_encoding_weight, audit_key_bits_weight; cbn; try lia.
  destruct detail as [v edge input|v number input|v input|before after];
    cbn [audit_dfs_full_event_width audit_dfs_full_event_clock] in Hkey, Hclock;
    unfold audit_key_bits_weight in Hkey;
    unfold audit_dfs_detail_work, audit_set_weight, audit_encoding_weight, audit_binary_weight,
      audit_key_bits_weight; cbn; try lia.
  pose proof (audit_dfs_clock_width before clock_ceiling Hclock) as Hsize.
  unfold audit_z_bits.
  destruct before as [bits|bits|]; cbn [Z.abs Z.log2 Z.to_nat Pos.size_nat] in *;
    try rewrite audit_dfs_positive_size_nat in *; lia.
Qed.

(** Summed full-event work uses the input width and the actual bounded output length. *)
Lemma audit_dfs_full_event_work_bound {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked roots :
    let events := snd (audit_dfs_full_counted p blocked roots) in
    let ceiling := 2 + length roots * S (Pos.to_nat (fuel p)) in
    let width := Nat.max (audit_dfs_full_input_width EV g p roots)
      (Pos.size_nat (Pos.of_succ_nat ceiling)) in
    fold_right (fun event n => audit_dfs_full_model_event EV event + n) 0 events <=
      length events * (140 + 12 * width + 2 * ceiling).
Proof.
  pose proof (audit_dfs_full_counted_event_width p blocked roots) as Hwidth.
  pose proof (audit_dfs_full_counted_event_clock p blocked roots) as Hclock.
  pose proof (audit_dfs_full_counted_event_output p blocked roots) as Houtput.
  destruct (audit_dfs_full_counted p blocked roots) as [result events]; cbn in Hwidth, Hclock,
    Houtput.
  change (fold_right (fun event n => audit_dfs_full_model_event EV event + n) 0 events <=
    length events * (140 + 12 * Nat.max (audit_dfs_full_input_width EV g p roots)
      (Pos.size_nat (Pos.of_succ_nat (2 + length roots * S (Pos.to_nat (fuel p))))) +
      2 * (2 + length roots * S (Pos.to_nat (fuel p))))).
  remember (2 + length roots * S (Pos.to_nat (fuel p))) as ceiling eqn:Hceiling.
  remember (Nat.max (audit_dfs_full_input_width EV g p roots)
    (Pos.size_nat (Pos.of_succ_nat ceiling))) as width eqn:Hwidth_eq.
  induction events as [|event events IH].
  - cbn; lia.
  - change (audit_dfs_full_model_event EV event +
      fold_right (fun item n => audit_dfs_full_model_event EV item + n) 0 events <=
      S (length events) * (140 + 12 * width + 2 * ceiling)).
    inversion Hwidth as [|? ? Hkey Hwidths].
    inversion Hclock as [|? ? Htime Hclocks].
    inversion Houtput as [|? ? Hout Houtputs].
    specialize (IH Hwidths Hclocks Houtputs).
    change (audit_dfs_full_event_clock event <=
      2 + length roots * S (Pos.to_nat (fuel p))) in Htime.
    change (audit_dfs_full_event_output event <=
      2 * (2 + length roots * S (Pos.to_nat (fuel p)))) in Hout.
    rewrite <- Hceiling in Htime, Hout.
    pose proof (audit_dfs_full_model_event_bound EV event (audit_dfs_full_input_width EV g p roots)
      ceiling Hkey Htime) as Hevent.
    rewrite <- Hwidth_eq in Hevent.
    change (fold_right (fun item n => audit_dfs_full_model_event EV item + n) 0 events <=
      length events * (140 + 12 * width + 2 * ceiling)) in IH.
    cbn in Hout; rewrite Nat.mul_succ_l; lia.
Qed.

(** Full counted DFS returns the source result with its input-derived count and work bounds. *)
Theorem audit_dfs_full_counted_correct : audit_dfs_full_counted_statement.
Proof.
  intros V E EV g p blocked roots.
  pose proof (audit_dfs_full_counted_erases p blocked roots) as Herase.
  pose proof (audit_dfs_full_counted_event_bound p blocked roots) as Hcount.
  pose proof (audit_dfs_full_event_work_bound p blocked roots) as Hwork.
  destruct (audit_dfs_full_counted p blocked roots) as [result events].
  cbn in Herase, Hcount, Hwork.
  change (length events <= audit_dfs_full_input_event_bound p roots) in Hcount.
  change (fold_right (fun event n => audit_dfs_full_model_event EV event + n) 0 events <=
    length events * (140 + 12 * Nat.max (audit_dfs_full_input_width EV g p roots)
      (Pos.size_nat (Pos.of_succ_nat (2 + length roots * S (Pos.to_nat (fuel p))))) +
      2 * (2 + length roots * S (Pos.to_nat (fuel p))))) in Hwork.
  split; [exact Herase|]; split; [exact Hcount|].
  unfold audit_dfs_full_model_work, audit_dfs_full_input_budget.
  change (256 * S (length events) * S (length events) +
    fold_right (fun event n => audit_dfs_full_model_event EV event + n) 0 events <=
    512 * S (audit_dfs_full_input_event_bound p roots) *
      S (audit_dfs_full_input_event_bound p roots) +
    audit_dfs_full_input_event_bound p roots * (140 + 12 *
      Nat.max (audit_dfs_full_input_width EV g p roots)
        (Pos.size_nat (Pos.of_succ_nat (2 + length roots * S (Pos.to_nat (fuel p))))))).
  set (count := length events) in *.
  set (bound := audit_dfs_full_input_event_bound p roots) in *.
  set (ceiling := 2 + length roots * S (Pos.to_nat (fuel p))) in *.
  set (width := Nat.max (audit_dfs_full_input_width EV g p roots)
    (Pos.size_nat (Pos.of_succ_nat ceiling))) in *.
  assert (Hceiling : ceiling <= bound).
  { unfold ceiling, bound, audit_dfs_full_input_event_bound; nia. }
  assert (Hquad : 256 * S count * S count <= 256 * S bound * S bound).
  { apply Nat.mul_le_mono; [apply Nat.mul_le_mono_l|]; lia. }
  assert (Hlinear : count * (140 + 12 * width) <= bound * (140 + 12 * width)).
  { apply Nat.mul_le_mono_r; exact Hcount. }
  assert (Hextra : count * (2 * ceiling) <= 2 * S bound * S bound).
  { replace (2 * S bound * S bound) with (S bound * (2 * S bound)) by nia.
    apply Nat.mul_le_mono; lia. }
  rewrite Nat.mul_add_distr_l in Hwork.
  assert (Hroom : 256 * S bound * S bound + 2 * S bound * S bound <=
    512 * S bound * S bound) by nia.
  lia.
Qed.

(** Erasing callbacks preserve the source DFS result, full events, and input-derived bounds. *)
Theorem audit_dfs_nested_correct : audit_dfs_nested_statement.
Proof.
  intros V E B EV g p cb blocked roots Hcallbacks.
  pose proof (audit_dfs_nested_counted_erases p cb blocked roots Hcallbacks) as Herase.
  pose proof (audit_dfs_full_counted_correct V E EV g p blocked roots) as Hfull.
  destruct (audit_dfs_nested_counted p cb blocked roots) as [result events].
  destruct (audit_dfs_full_counted p blocked roots) as [result' full_events].
  cbn in Herase, Hfull |- *; inversion Herase; subst result' full_events.
  destruct Hfull as [Hresult [Hcount Hwork]].
  rewrite length_map in Hcount; auto.
Qed.

(** * Callback receipts and source work *)

(** A callback capture records the exact return value and body of its original call. *)
Definition audit_dfs_capture_receipt {V E B} (cb : audit_dfs_callback_model V E B)
    (capture : audit_graph_callback_capture V E B) : Prop :=
  match capture with
  | AuditGraphTargetCapture _ _ _ edge value body => audit_dfs_target_model cb edge = (value, body)
  | AuditGraphEncodeCapture _ _ _ vertex code body => audit_dfs_encode_model cb vertex = (code,
    body)
  end.

(** Every callback capture attached to an event is a receipt of that callback. *)
Definition audit_dfs_event_receipts {V E B} (cb : audit_dfs_callback_model V E B)
    (event : audit_dfs_nested_event V E (audit_graph_callback_capture V E B)) : Prop :=
  Forall (audit_dfs_capture_receipt cb) (snd event).

(** Discovery retains the exact encoder return and body for every nested update. *)
Lemma audit_dfs_discover_receipts {V E B} (cb : audit_dfs_callback_model V E B) v via st :
    Forall (audit_dfs_event_receipts cb)
      (snd (audit_dfs_nested_discover (audit_graph_capture_callbacks cb) v via st)).
Proof.
  unfold audit_dfs_nested_discover, audit_dfs_nested_set, audit_graph_capture_callbacks; cbn.
  destruct (audit_dfs_encode_model cb v) as [code body] eqn:Hcall.
  destruct via; cbn; repeat constructor; cbn [audit_dfs_event_receipts audit_dfs_capture_receipt];
    repeat constructor; exact Hcall.
Qed.

(** Finishing retains the exact encoder return and body for its nested update. *)
Lemma audit_dfs_finish_receipts {V E B} (cb : audit_dfs_callback_model V E B) v st :
    Forall (audit_dfs_event_receipts cb)
      (snd (audit_dfs_nested_finish (audit_graph_capture_callbacks cb) v st)).
Proof.
  unfold audit_dfs_nested_finish, audit_dfs_nested_set, audit_graph_capture_callbacks; cbn.
  destruct (audit_dfs_encode_model cb v) as [code body] eqn:Hcall.
  cbn; repeat constructor; cbn [audit_dfs_event_receipts audit_dfs_capture_receipt];
    repeat constructor; exact Hcall.
Qed.

(** A source step attaches receipts from its actual target and encoder callbacks. *)
Lemma audit_dfs_step_receipts {V E B} {EV} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) blocked work :
    Forall (audit_dfs_event_receipts cb)
      (snd (audit_dfs_nested_step p (audit_graph_capture_callbacks cb) blocked work)).
Proof.
  destruct work as [stack st], stack as [|[v edges] rest]; cbn [audit_dfs_nested_step].
  - repeat constructor.
  - destruct edges as [|edge edges].
    + pose proof (audit_dfs_finish_receipts cb v st) as Hfinish.
      destruct (audit_dfs_nested_finish (audit_graph_capture_callbacks cb) v st) as [next details].
      cbn in Hfinish |- *; constructor; [constructor|].
      apply Forall_app; split; [exact Hfinish|repeat constructor].
    + unfold audit_graph_capture_callbacks at 1; cbn.
      destruct (audit_dfs_target_model cb edge) as [target target_body] eqn:Htarget.
      unfold audit_dfs_nested_get, audit_graph_capture_callbacks; cbn.
      destruct (audit_dfs_encode_model cb target) as [code body] eqn:Hencode.
      destruct (Map.code_get code blocked), (Map.code_get code (DfsState.seen st)); cbn;
        try (repeat constructor; cbn [audit_dfs_event_receipts audit_dfs_capture_receipt];
          repeat constructor; eauto; fail).
      pose proof (audit_dfs_discover_receipts cb target (Some edge) st) as Hdiscover.
      destruct (audit_dfs_nested_discover (audit_graph_capture_callbacks cb) target (Some edge) st)
        as [next details] eqn:Hdiscover_run.
      fold (audit_graph_capture_callbacks cb).
      rewrite Hdiscover_run; cbn.
      repeat constructor; cbn [audit_dfs_event_receipts audit_dfs_capture_receipt];
        try (repeat constructor; eauto).
      apply Forall_app; split; [exact Hdiscover|repeat constructor].
Qed.

(** Both halves of a captured binary-fuel run preserve same-call receipts. *)
Lemma audit_dfs_run_receipts {V E B} {EV} {g : Graph.t V E}
    (p : prepared EV g)
    (cb : audit_dfs_callback_model V E B) blocked fuel work :
    Forall (audit_dfs_event_receipts cb)
      (snd (audit_dfs_nested_run p (audit_graph_capture_callbacks cb) blocked fuel work)).
Proof.
  set (captured := audit_graph_capture_callbacks cb).
  revert work; induction fuel as [fuel IH|fuel IH|]; intro work;
    destruct work as [stack st], stack as [|frame stack]; cbn [audit_dfs_nested_run].
  - repeat constructor.
  - cbn [audit_dfs_nested_run fst].
    specialize (IH (frame :: stack, st)) as Hfirst.
    destruct (audit_dfs_nested_run p captured blocked fuel (frame :: stack, st))
      as [middle first] eqn:Hfirst_run; cbn in Hfirst |- *.
    specialize (IH middle) as Hsecond.
    destruct (audit_dfs_nested_run p captured blocked fuel middle) as [last second] eqn:Hsecond_run;
      cbn in Hsecond |- *.
    pose proof (audit_dfs_step_receipts p cb blocked last) as Hstep.
    fold captured in Hstep.
    destruct (audit_dfs_nested_step p captured blocked last) as [result events] eqn:Hstep_run;
      cbn in Hstep |- *.
    change (Forall (audit_dfs_event_receipts cb)
      (snd (let '(middle, first) :=
        audit_dfs_nested_run p captured blocked fuel (frame :: stack, st) in
        let '(last, second) := audit_dfs_nested_run p captured blocked fuel middle in
        let '(result, events) := audit_dfs_nested_step p captured blocked last in
        (result, (AuditDfsFullCase 7, []) :: first ++ second ++ events)))).
    rewrite Hfirst_run, Hsecond_run, Hstep_run; cbn.
    constructor; [constructor|]. apply Forall_app; split; [exact Hfirst|].
    apply Forall_app; split; assumption.
  - repeat constructor.
  - cbn [audit_dfs_nested_run fst].
    specialize (IH (frame :: stack, st)) as Hfirst.
    destruct (audit_dfs_nested_run p captured blocked fuel (frame :: stack, st))
      as [middle first] eqn:Hfirst_run; cbn in Hfirst |- *.
    specialize (IH middle) as Hsecond.
    destruct (audit_dfs_nested_run p captured blocked fuel middle)
      as [result second] eqn:Hsecond_run;
      cbn in Hsecond |- *.
    change (Forall (audit_dfs_event_receipts cb)
      (snd (let '(middle, first) :=
        audit_dfs_nested_run p captured blocked fuel (frame :: stack, st) in
        let '(result, second) := audit_dfs_nested_run p captured blocked fuel middle in
        (result, (AuditDfsFullCase 6, []) :: first ++ second)))).
    rewrite Hfirst_run, Hsecond_run; cbn.
    constructor; [constructor|]. apply Forall_app; split; assumption.
  - repeat constructor.
  - cbn [audit_dfs_nested_run fst].
    pose proof (audit_dfs_step_receipts p cb blocked (frame :: stack, st)) as Hstep.
    fold captured in Hstep.
    destruct (audit_dfs_nested_step p captured blocked (frame :: stack, st))
      as [result events] eqn:Hstep_run.
    cbn in Hstep.
    change (Forall (audit_dfs_event_receipts cb)
      (snd (let '(result, events) :=
        audit_dfs_nested_step p captured blocked (frame :: stack, st) in
        (result, (AuditDfsFullCase 5, []) :: events)))).
    rewrite Hstep_run; cbn; constructor; [constructor|exact Hstep].
Qed.

(** A source root retains the exact encoder returns for its membership and discovery calls. *)
Lemma audit_dfs_root_receipts {V E B} {EV} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) blocked st v :
    Forall (audit_dfs_event_receipts cb)
      (snd (audit_dfs_nested_root p (audit_graph_capture_callbacks cb) blocked st v)).
Proof.
  unfold audit_dfs_nested_root, audit_dfs_nested_get, audit_graph_capture_callbacks; cbn.
  destruct (audit_dfs_encode_model cb v) as [code body] eqn:Hencode.
  destruct (Map.code_get code blocked), (Map.code_get code (DfsState.seen st)); cbn;
    try (repeat constructor; cbn [audit_dfs_event_receipts audit_dfs_capture_receipt];
      repeat constructor; eauto; fail).
  pose proof (audit_dfs_discover_receipts cb v None st) as Hdiscover.
  destruct (audit_dfs_nested_discover (audit_graph_capture_callbacks cb) v None st)
    as [next details] eqn:Hdiscover_run.
  cbn in Hdiscover.
  pose proof (audit_dfs_run_receipts p cb blocked (fuel p)
    ([(v,
      match Map.code_get code (out_index p) with
      | Some xs => xs
      | None => []
      end)], next)) as Hrun.
  destruct (audit_dfs_nested_run p (audit_graph_capture_callbacks cb) blocked (fuel p)
    ([(v,
      match Map.code_get code (out_index p) with
      | Some xs => xs
      | None => []
      end)], next)) as [result events] eqn:Hrun_eq.
  cbn in Hrun.
  fold (audit_graph_capture_callbacks cb).
  cbn [audit_dfs_nested_discover]; cbn.
  cbn [audit_dfs_nested_discover] in Hdiscover_run; cbn in Hdiscover_run.
  rewrite Hdiscover_run, Hrun_eq; cbn.
  repeat constructor; cbn [audit_dfs_event_receipts audit_dfs_capture_receipt];
    try (repeat constructor; eauto).
  apply Forall_app; split; [exact Hdiscover|].
  constructor; [constructor|exact Hrun].
Qed.

(** The fold over roots preserves same-call callback receipts. *)
Lemma audit_dfs_roots_receipts {V E B} {EV} {g : Graph.t V E}
    (p : prepared EV g)
    (cb : audit_dfs_callback_model V E B) blocked roots st :
    Forall (audit_dfs_event_receipts cb)
      (snd (audit_dfs_nested_roots p (audit_graph_capture_callbacks cb) blocked roots st)).
Proof.
  set (captured := audit_graph_capture_callbacks cb).
  revert st; induction roots as [|root roots IH]; intro st; cbn [audit_dfs_nested_roots].
  - repeat constructor.
  - pose proof (audit_dfs_root_receipts p cb blocked st root) as Hroot.
    fold captured in Hroot.
    destruct (audit_dfs_nested_root p captured blocked st root) as [next here] eqn:Hroot_run.
    cbn in Hroot.
    specialize (IH next).
    destruct (audit_dfs_nested_roots p captured blocked roots next)
      as [result later] eqn:Hroots_run.
    cbn in IH.
    constructor; [constructor|]. apply Forall_app; split; assumption.
Qed.

(** Every source DFS capture is the return of the callback call that produced it. *)
Lemma audit_dfs_source_receipts {V E B} {EV} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) blocked roots :
    Forall (audit_dfs_event_receipts cb) (snd (audit_dfs_source_counted p cb blocked roots)).
Proof.
  unfold audit_dfs_source_counted.
  pose proof (audit_dfs_roots_receipts p cb blocked roots dfs_initial) as Hroots.
  destruct (audit_dfs_nested_roots p (audit_graph_capture_callbacks cb) blocked roots dfs_initial)
    as [st events]; cbn in Hroots |- *.
  apply Forall_app; split; [exact Hroots|repeat constructor].
Qed.

(** Source clock details fit the source budget's root-and-fuel ceiling. *)
Lemma audit_dfs_full_event_source_clock {V E} {EV} {g : Graph.t V E}
    (p : prepared EV g) blocked roots :
    Forall (fun event => audit_dfs_full_event_clock event <=
      S (length roots) * S (Pos.to_nat (fuel p))) (snd (audit_dfs_full_counted p blocked roots)).
Proof.
  unfold audit_dfs_full_counted.
  pose proof (audit_dfs_full_roots_event_clock p blocked roots dfs_initial) as Hroots.
  destruct (audit_dfs_full_roots_counted p blocked roots dfs_initial) as [st events].
  cbn in Hroots |- *; apply Forall_app; split.
  - eapply Forall_impl; [|exact Hroots].
    intros event Hbound; cbn [dfs_initial] in Hbound; cbn in Hbound.
    pose proof (Pos2Nat.is_pos (fuel p)); nia.
  - repeat constructor; cbn [audit_dfs_full_event_clock]; lia.
Qed.

(** An encoder capture in a same-call receipt has the code required by callback erasure. *)
Lemma audit_dfs_receipt_code {V E B} (EV : encoding V) (g : Graph.t V E)
    (cb : audit_dfs_callback_model V E B) v code body :
    audit_dfs_callbacks_erase EV g cb ->
    audit_dfs_capture_receipt cb (AuditGraphEncodeCapture V E B v code body) ->
    code = encode EV v.
Proof.
  intros [_ Hencode] Hreceipt.
  specialize (Hencode v); cbn [audit_dfs_capture_receipt] in Hreceipt.
  rewrite Hreceipt in Hencode; exact Hencode.
Qed.

(** A key-bearing source event uses the encoding of the vertex in that same event. *)
Definition audit_dfs_source_code_matches {V E B} (EV : encoding V)
    (item : audit_dfs_nested_event V E (audit_graph_callback_capture V E B)) : Prop :=
  let '(event, body) := item in
  match event with
  | AuditDfsFullMember v _ _
  | AuditDfsFullSuccessors v _ _ => audit_dfs_source_code body = encode EV v
  | AuditDfsFullDetail (AuditDfsParentSet v _ _)
  | AuditDfsFullDetail (AuditDfsNumSet v _ _)
  | AuditDfsFullDetail (AuditDfsSeenAdd v _) => audit_dfs_source_code body = encode EV v
  | _ => True
  end.

(** Well-formed same-call captures and erasing callbacks identify every key-event code. *)
Lemma audit_dfs_source_event_code {V E B} (EV : encoding V) (g : Graph.t V E)
    (cb : audit_dfs_callback_model V E B) item :
    audit_dfs_callbacks_erase EV g cb -> audit_dfs_source_event_wellformed item ->
    audit_dfs_event_receipts cb item -> audit_dfs_source_code_matches EV item.
Proof.
  intros Hcallbacks Hshape Hreceipts; destruct item as [event body].
  destruct event as [site|edge target|v set result|v index result|v via before after|
      v before after|detail|pre post];
    cbn [audit_dfs_source_code_matches audit_dfs_source_event_wellformed] in *; try exact I.
  all: try (destruct detail as [v edge input|v number input|v input|before after];
    cbn [audit_dfs_source_code_matches audit_dfs_source_event_wellformed] in *; try exact I).
  all: destruct Hshape as [code [trace Hbody]]; subst body;
    cbn [audit_dfs_event_receipts] in Hreceipts; inversion Hreceipts as [|? ? Hreceipt ?];
    cbn [audit_dfs_source_code]; eapply audit_dfs_receipt_code; eauto.
Qed.

(** Captured source-event work uses its actual callback bodies and bounded primitive operands. *)
Lemma audit_dfs_source_event_bound {V E B} (EV : encoding V) (weight : B -> nat)
    (item : audit_dfs_nested_event V E (audit_graph_callback_capture V E B)) key_width ceiling :
    audit_dfs_source_code_matches EV item ->
    audit_dfs_full_event_width EV (fst item) <= key_width ->
    audit_dfs_full_event_clock (fst item) <= ceiling ->
    audit_dfs_source_event_work weight item <=
      512 + 64 * Nat.max key_width (Pos.size_nat (Pos.of_succ_nat ceiling)) +
      2 * audit_dfs_full_event_output (fst item) + audit_dfs_source_body_work weight [item].
Proof.
  remember (Nat.max key_width (Pos.size_nat (Pos.of_succ_nat ceiling))) as width eqn:Hwidth.
  assert (Hkeymax : key_width <= width) by (rewrite Hwidth; apply Nat.le_max_l).
  assert (Hclockmax : Pos.size_nat (Pos.of_succ_nat ceiling) <= width)
    by (rewrite Hwidth; apply Nat.le_max_r).
  intros Hcode Hkey Hclock; destruct item as [event body].
  destruct event as [site|edge target|v set result|v index result|v via before after|
      v before after|detail|pre post];
    cbn [audit_dfs_source_code_matches audit_dfs_full_event_width audit_dfs_full_event_clock] in *;
    unfold audit_key_bits_weight in Hkey;
    unfold audit_dfs_source_event_work, audit_dfs_source_body_work, audit_dfs_full_event_output;
      cbn;
    try lia.
  - rewrite Hcode.
    pose proof (audit_trie_get_source_work_bound _ (encode EV v) set) as Hget.
    change (64 + fold_right (fun item n => audit_graph_capture_work weight item + n) 0 body +
      (5 + audit_trie_get_source_work (encode EV v) set) <=
      512 + 64 * width + 0 +
      (fold_right (fun item n => audit_graph_capture_work weight item + n) 0 body + 0)).
    change (Pos.size_nat (encode EV v) <= key_width) in Hkey.
    lia.
  - rewrite Hcode.
    pose proof (audit_trie_get_source_work_bound _ (encode EV v) index) as Hget.
    change (Pos.size_nat (encode EV v) <= key_width) in Hkey.
    change (64 + fold_right (fun item n => audit_graph_capture_work weight item + n) 0 body +
      (5 + audit_trie_get_source_work (encode EV v) index) <=
      512 + 64 * width + 0 +
      (fold_right (fun item n => audit_graph_capture_work weight item + n) 0 body + 0)); lia.
  - destruct detail as [v edge input|v number input|v input|before after];
      cbn [audit_dfs_source_code_matches audit_dfs_full_event_width audit_dfs_full_event_clock] in
        *;
      unfold audit_key_bits_weight in Hkey; cbn.
    + rewrite Hcode.
      pose proof (audit_trie_update_source_work_bound _ (encode EV v) (Some (v, edge)) input) as
        Hset.
      change (Pos.size_nat (encode EV v) <= key_width) in Hkey.
      change (64 + fold_right (fun item n => audit_graph_capture_work weight item + n) 0 body +
        (2 + audit_trie_update_source_work (encode EV v) (Some (v, edge)) input) <=
        512 + 64 * width + 0 +
        (fold_right (fun item n => audit_graph_capture_work weight item + n) 0 body + 0)); lia.
    + rewrite Hcode.
      pose proof (audit_trie_update_source_work_bound _ (encode EV v) (Some (v, number)) input) as
        Hset.
      change (Pos.size_nat (encode EV v) <= key_width) in Hkey.
      change (64 + fold_right (fun item n => audit_graph_capture_work weight item + n) 0 body +
        (2 + audit_trie_update_source_work (encode EV v) (Some (v, number)) input) <=
        512 + 64 * width + 0 +
        (fold_right (fun item n => audit_graph_capture_work weight item + n) 0 body + 0)); lia.
    + rewrite Hcode.
      pose proof (audit_trie_update_source_work_bound _ (encode EV v) (Some (v, tt)) input) as Hset.
      change (Pos.size_nat (encode EV v) <= key_width) in Hkey.
      change (64 + fold_right (fun item n => audit_graph_capture_work weight item + n) 0 body +
        (2 + audit_trie_update_source_work (encode EV v) (Some (v, tt)) input) <=
        512 + 64 * width + 0 +
        (fold_right (fun item n => audit_graph_capture_work weight item + n) 0 body + 0)); lia.
    + pose proof (audit_dfs_clock_width before ceiling Hclock); lia.
Qed.

(** Source event work sums under the same captured callback bodies and input envelopes. *)
Lemma audit_dfs_source_event_work_bound {V E B} {EV} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (weight : B -> nat) blocked roots :
    audit_dfs_callbacks_erase EV g cb ->
    let events := snd (audit_dfs_source_counted p cb blocked roots) in
    let ceiling := S (length roots) * S (Pos.to_nat (fuel p)) in
    let output_bound := 2 * (2 + length roots * S (Pos.to_nat (fuel p))) in
    let width := Nat.max (audit_dfs_full_input_width EV g p roots)
      (Pos.size_nat (Pos.of_succ_nat ceiling)) in
    audit_dfs_source_work weight events <=
      length events * (512 + 64 * width + 2 * output_bound) +
      audit_dfs_source_body_work weight events.
Proof.
  intro Hcallbacks.
  pose proof (audit_dfs_source_erases p cb blocked roots Hcallbacks) as Herase.
  pose proof (audit_dfs_source_events_wellformed p cb blocked roots) as Hshape.
  pose proof (audit_dfs_source_receipts p cb blocked roots) as Hreceipts.
  pose proof (audit_dfs_full_counted_event_width p blocked roots) as Hwidth.
  pose proof (audit_dfs_full_event_source_clock p blocked roots) as Hclock.
  pose proof (audit_dfs_full_counted_event_output p blocked roots) as Houtput.
  destruct (audit_dfs_source_counted p cb blocked roots) as [result events].
  cbn in Herase, Hshape, Hreceipts.
  rewrite <- Herase in Hwidth, Hclock, Houtput; cbn in Hwidth, Hclock, Houtput.
  apply Forall_map in Hwidth, Hclock, Houtput.
  assert (Hcodes : Forall (audit_dfs_source_code_matches EV) events).
  { apply Forall_forall; intros item Hin.
    eapply audit_dfs_source_event_code; [exact Hcallbacks| |].
    - apply Forall_forall with (x := item) in Hshape; assumption.
    - apply Forall_forall with (x := item) in Hreceipts; assumption. }
  change (audit_dfs_source_work weight events <=
    length events * (512 + 64 * Nat.max (audit_dfs_full_input_width EV g p roots)
      (Pos.size_nat (Pos.of_succ_nat (S (length roots) * S (Pos.to_nat (fuel p))))) +
      2 * (2 * (2 + length roots * S (Pos.to_nat (fuel p))))) +
    audit_dfs_source_body_work weight events).
  remember (S (length roots) * S (Pos.to_nat (fuel p))) as ceiling eqn:Hceiling.
  remember (2 * (2 + length roots * S (Pos.to_nat (fuel p)))) as output_bound eqn:Houtput_bound.
  remember (Nat.max (audit_dfs_full_input_width EV g p roots)
    (Pos.size_nat (Pos.of_succ_nat ceiling))) as width eqn:Hwidth_eq.
  clear Herase Hshape Hreceipts.
  induction events as [|item events IH].
  - cbn [audit_dfs_source_work audit_dfs_source_body_work]; cbn; lia.
  - inversion Hcodes as [|? ? Hcode Hcodes_tail].
    inversion Hwidth as [|? ? Hkey Hwidth_tail].
    inversion Hclock as [|? ? Htime Hclock_tail].
    inversion Houtput as [|? ? Hout Houtput_tail].
    specialize (IH Hwidth_tail Hclock_tail Houtput_tail Hcodes_tail).
    change (audit_dfs_full_event_clock (fst item) <=
      S (length roots) * S (Pos.to_nat (fuel p))) in Htime.
    change (audit_dfs_full_event_output (fst item) <=
      2 * (2 + length roots * S (Pos.to_nat (fuel p)))) in Hout.
    rewrite <- Hceiling in Htime; rewrite <- Houtput_bound in Hout.
    pose proof (audit_dfs_source_event_bound EV weight item
      (audit_dfs_full_input_width EV g p roots) ceiling Hcode Hkey Htime) as Hevent.
    rewrite <- Hwidth_eq in Hevent.
    unfold audit_dfs_source_work, audit_dfs_source_body_work in *; cbn [fold_right length] in *.
    rewrite Nat.mul_succ_l; lia.
Qed.

(** Erasing callbacks yield source DFS, well-formed captures and its input-derived work bound. *)
Theorem audit_dfs_source_correct : audit_dfs_source_statement.
Proof.
  intros V E B EV g p cb weight blocked roots Hcallbacks.
  pose proof (audit_dfs_source_result_and_count p cb blocked roots Hcallbacks) as [Hresult Hcount].
  pose proof (audit_dfs_source_events_wellformed p cb blocked roots) as Hshape.
  pose proof (audit_dfs_source_event_work_bound p cb weight blocked roots Hcallbacks) as Hwork.
  destruct (audit_dfs_source_counted p cb blocked roots) as [result events].
  cbn in Hresult, Hcount, Hshape, Hwork.
  change (length events <= audit_dfs_full_input_event_bound p roots) in Hcount.
  change (audit_dfs_source_work weight events <=
    length events * (512 + 64 * Nat.max (audit_dfs_full_input_width EV g p roots)
      (Pos.size_nat (Pos.of_succ_nat (S (length roots) * S (Pos.to_nat (fuel p))))) +
      2 * (2 * (2 + length roots * S (Pos.to_nat (fuel p))))) +
    audit_dfs_source_body_work weight events) in Hwork.
  split; [exact Hresult|]; split; [exact Hshape|]; split; [exact Hcount|].
  unfold audit_dfs_source_budget.
  change (audit_dfs_source_work weight events <=
    1024 * S (audit_dfs_full_input_event_bound p roots) *
      S (audit_dfs_full_input_event_bound p roots) +
    audit_dfs_full_input_event_bound p roots * (512 + 64 *
      Nat.max (audit_dfs_full_input_width EV g p roots)
        (Pos.size_nat (Pos.of_succ_nat (S (length roots) * S (Pos.to_nat (fuel p)))))) +
    audit_dfs_source_body_work weight events).
  set (count := length events) in *.
  set (bound := audit_dfs_full_input_event_bound p roots) in *.
  set (output_bound := 2 * (2 + length roots * S (Pos.to_nat (fuel p)))) in *.
  set (width := Nat.max (audit_dfs_full_input_width EV g p roots)
    (Pos.size_nat (Pos.of_succ_nat (S (length roots) * S (Pos.to_nat (fuel p)))))) in *.
  assert (Houtput : output_bound <= 2 * bound).
  { unfold output_bound, bound, audit_dfs_full_input_event_bound; nia. }
  assert (Hlinear : count * (512 + 64 * width) <= bound * (512 + 64 * width)).
  { apply Nat.mul_le_mono_r; exact Hcount. }
  assert (Hextra : count * (2 * output_bound) <= 4 * S bound * S bound).
  { replace (4 * S bound * S bound) with (S bound * (4 * S bound)) by nia.
    apply Nat.mul_le_mono; lia. }
  assert (Hroom : 4 * S bound * S bound <= 1024 * S bound * S bound) by nia.
  rewrite Nat.mul_add_distr_l in Hwork; lia.
Qed.

(** * External callback adaptation *)

(** A same-call capture's callback body is bounded by the budget for its actual argument. *)
Lemma audit_dfs_capture_body_bound {V E B} (cb : audit_dfs_callback_model V E B)
    (weight : B -> nat) encode_source target_source encode_budget target_budget capture :
    audit_graph_external_callback_adapter (audit_dfs_encode_model cb) weight encode_source
      encode_budget ->
    audit_graph_external_callback_adapter (audit_dfs_target_model cb) weight target_source
      target_budget ->
    audit_dfs_capture_receipt cb capture ->
    audit_graph_capture_work weight capture <=
      audit_dfs_capture_budget encode_budget target_budget capture.
Proof.
  intros Hencode Htarget Hreceipt; destruct capture as [edge value body|v code body];
    cbn [audit_dfs_capture_receipt audit_graph_capture_work audit_dfs_capture_budget] in *.
  - destruct (audit_graph_external_callback_source _ _ _ _ Htarget edge value body Hreceipt)
      as [_ Hbound]; exact Hbound.
  - destruct (audit_graph_external_callback_source _ _ _ _ Hencode v code body Hreceipt)
      as [_ Hbound]; exact Hbound.
Qed.

(** Same-call receipts bound all external callback bodies in the recorded event sequence. *)
Lemma audit_dfs_source_bodies_bound {V E B} (cb : audit_dfs_callback_model V E B)
    (weight : B -> nat) encode_source target_source encode_budget target_budget events :
    audit_graph_external_callback_adapter (audit_dfs_encode_model cb) weight encode_source
      encode_budget ->
    audit_graph_external_callback_adapter (audit_dfs_target_model cb) weight target_source
      target_budget ->
    Forall (audit_dfs_event_receipts cb) events ->
    audit_dfs_source_body_work weight events <=
      audit_dfs_source_external_budget encode_budget target_budget events.
Proof.
  intros Hencode Htarget Hreceipts.
  induction Hreceipts as [|[event body] events Hbody Htail IH].
  - reflexivity.
  - unfold audit_dfs_event_receipts in Hbody; cbn in Hbody.
    change (fold_right (fun capture n => audit_graph_capture_work weight capture + n) 0 body +
      audit_dfs_source_body_work weight events <=
      fold_right (fun capture n => audit_dfs_capture_budget encode_budget target_budget capture + n)
        0 body + audit_dfs_source_external_budget encode_budget target_budget events).
    assert (Hbody_bound :
      fold_right (fun capture n => audit_graph_capture_work weight capture + n) 0 body <=
      fold_right (fun capture n => audit_dfs_capture_budget encode_budget target_budget capture + n)
        0 body).
    { clear IH Htail events event.
      induction Hbody as [|capture body Hcapture Hrest IHbody]; cbn; [lia|].
      pose proof (audit_dfs_capture_body_bound cb weight encode_source target_source encode_budget
        target_budget capture Hencode Htarget Hcapture); lia. }
    lia.
Qed.

(** With erasing callbacks and adapter laws, DFS returns its source result within external
    budgets. *)
Theorem audit_dfs_source_adapted_holds : audit_dfs_source_adapted_statement.
Proof.
  intros V E B EV g p cb weight blocked roots encode_source target_source encode_budget
    target_budget Hcallbacks Hencode Htarget.
  pose proof (audit_dfs_source_correct V E B EV g p cb weight blocked roots Hcallbacks) as Hsource.
  pose proof (audit_dfs_source_receipts p cb blocked roots) as Hreceipts.
  destruct (audit_dfs_source_counted p cb blocked roots) as [result events].
  cbn in Hsource, Hreceipts |- *.
  destruct Hsource as [Hresult [_ [_ Hwork]]].
  pose proof (audit_dfs_source_bodies_bound cb weight encode_source target_source encode_budget
    target_budget events Hencode Htarget Hreceipts) as Hbody.
  split; [exact Hresult|].
  change (audit_dfs_source_work weight events <= audit_dfs_source_budget EV g p roots +
    audit_dfs_source_external_budget encode_budget target_budget events).
  change (audit_dfs_source_work weight events <= audit_dfs_source_budget EV g p roots +
    audit_dfs_source_body_work weight events) in Hwork.
  eapply Nat.le_trans; [exact Hwork|].
  apply Nat.add_le_mono_l; exact Hbody.
Qed.

(** Source and adapted DFS bounds compose with reverse, successor and trie source obligations. *)
Theorem audit_dfs_source_contract_holds : audit_dfs_source_contract_statement.
Proof.
  unfold audit_dfs_source_contract_statement, audit_dfs_source_reverse_obligations,
    audit_dfs_source_successor_obligations.
  split; [exact audit_dfs_source_correct|].
  split; [exact audit_dfs_source_adapted_holds|].
  split.
  - split; [exact audit_graph_reverse_run_holds|].
    split; [exact audit_graph_reverse_fast_run_holds|exact audit_graph_reverse_fast_counted_holds].
  - split.
    + split; [exact audit_positive_succ_run_total|].
      split; [exact audit_positive_succ_run_correct|exact
        audit_dfs_source_successor_correspondence_holds].
    + split; [exact audit_trie_get_trace_adequate|].
      split; [exact audit_trie_update_trace_adequate|].
      split; [exact audit_trie_get_source_work_bound|exact audit_trie_update_source_work_bound].
Qed.
