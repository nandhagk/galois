(** * Adequacy of reverse postorder scheduling

    Counted scheduler traversals preserve the underlying scheduler observations.
    For example, assigning one vertex a position records the same map entry.
    Builds on: FixpointAuditSchedule, graph DFS and collection adequacy. *)

From Stdlib Require Import List PArith Lia PeanoNat.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditMap CollectionsAuditFinSet CollectionsAuditEncoding CollectionsAuditCompare
  CollectionsAuditMapAdequacy CollectionsAuditFinSetAdequacy CollectionsAuditEncodingAdequacy
  CollectionsAuditCompareAdequacy CollectionsAuditTrie CollectionsAuditTrieAdequacy.
From Galois.Graph Require Import GraphCore GraphDfs GraphAuditBase GraphAuditDfsAdequacy.
From Galois.Fixpoint Require Import FixpointSchedule FixpointAuditSchedule.
Import List.ListNotations.

(** * Position and query erasure *)

(** Counted position assignments return the original position map. *)
Theorem audit_rpo_schedule_positions_erases : audit_rpo_schedule_positions_statement.
Proof.
  intros V B EV enc vertices; induction vertices as [|v rest IH]; intros next Henc.
  - reflexivity.
  - cbn [audit_rpo_schedule_positions schedule_positions].
    pose proof (audit_positive_succ_erases next) as Hsucc.
    destruct (audit_positive_succ next) as [next' successor_events] eqn:Hnext.
    cbn in Hsucc; subst next'.
    specialize (IH (Pos.succ next) Henc).
    destruct (audit_rpo_schedule_positions enc rest (Pos.succ next)) as [middle events]
      eqn:Hmiddle.
    cbn in IH; subst middle.
    pose proof (audit_map_set_erases V positive B enc EV v next
      (schedule_positions EV rest (Pos.succ next)) (Henc v)) as Hset.
    destruct (audit_map_set enc v next (schedule_positions EV rest (Pos.succ next)))
      as [result writes]; exact Hset.
Qed.

(** * Retreat traversal erasure *)

Lemma audit_rpo_graph_ancestor_erases V E B (EV : encoding V)
    (enc : V -> positive * list B) (r : dfs_result V E) u v :
  (forall x, fst (enc x) = encode EV x) ->
  fst (audit_rpo_graph_ancestor enc r u v) = ancestor_b EV r u v.
Proof.
  intro Henc.
  pose proof (audit_map_get_erases V positive B enc EV u (pre_num r) (Henc u)) as Hpreu.
  pose proof (audit_map_get_erases V positive B enc EV v (pre_num r) (Henc v)) as Hprev.
  pose proof (audit_map_get_erases V positive B enc EV u (post_num r) (Henc u)) as Hpostu.
  pose proof (audit_map_get_erases V positive B enc EV v (post_num r) (Henc v)) as Hpostv.
  unfold audit_rpo_graph_ancestor, ancestor_b.
  destruct (audit_map_get enc u (pre_num r)) as [[a|] ea]; cbn in Hpreu |- *;
    rewrite <- Hpreu; [|reflexivity].
  destruct (audit_map_get enc v (pre_num r)) as [[b|] eb]; cbn in Hprev |- *;
    rewrite <- Hprev; [|reflexivity].
  destruct (audit_map_get enc u (post_num r)) as [[c|] ec]; cbn in Hpostu |- *;
    rewrite <- Hpostu; [|reflexivity].
  destruct (audit_map_get enc v (post_num r)) as [[d|] ed]; cbn in Hpostv |- *;
    rewrite <- Hpostv; [|reflexivity].
  pose proof (audit_positive_order a b) as [_ [Hab _]].
  pose proof (audit_positive_order d c) as [_ [Hdc _]].
  destruct (audit_positive_leb a b) as [first ef]; cbn in Hab |- *.
  destruct (audit_positive_leb d c) as [second es]; cbn in Hdc |- *.
  now rewrite Hab, Hdc.
Qed.

Lemma audit_rpo_graph_filter_erases V E B (EV : encoding V) (g : Graph.t V E)
    (cb : audit_rpo_graph_callbacks V E B) (r : dfs_result V E) edges :
  audit_rpo_graph_callbacks_erase EV g cb ->
  fst (audit_rpo_graph_filter cb r edges) =
    filter (fun e => ancestor_b EV r (Graph.target g e) (Graph.source g e)) edges.
Proof.
  intros [Henc [Hout [Hsource Htarget]]].
  induction edges as [|edge rest IH].
  - reflexivity.
  - cbn [audit_rpo_graph_filter filter].
    specialize (Htarget edge); specialize (Hsource edge).
    destruct (audit_rpo_graph_target cb edge) as [target tb]; cbn in Htarget; subst target.
    destruct (audit_rpo_graph_source cb edge) as [source sb]; cbn in Hsource; subst source.
    pose proof (audit_rpo_graph_ancestor_erases V E B EV (audit_rpo_graph_encode cb) r
      (Graph.target g edge) (Graph.source g edge) Henc) as Hancestor.
    destruct (audit_rpo_graph_ancestor (audit_rpo_graph_encode cb) r
      (Graph.target g edge) (Graph.source g edge)) as [keep checks]; cbn in Hancestor.
    destruct (audit_rpo_graph_filter cb r rest) as [later events]; cbn in IH |- *.
    now rewrite Hancestor, IH.
Qed.

Lemma audit_rpo_graph_targets_erases V E B (g : Graph.t V E)
    (cb : audit_rpo_graph_callbacks V E B) edges :
  (forall e, fst (audit_rpo_graph_target cb e) = Graph.target g e) ->
  fst (audit_rpo_graph_targets cb edges) = map (Graph.target g) edges.
Proof.
  intro Htarget; induction edges as [|edge rest IH].
  - reflexivity.
  - cbn [audit_rpo_graph_targets map].
    specialize (Htarget edge) as Hcall.
    destruct (audit_rpo_graph_target cb edge) as [target body]; cbn in Hcall; subst target.
    destruct (audit_rpo_graph_targets cb rest) as [later events]; cbn in IH |- *.
    now rewrite IH.
Qed.

Lemma audit_rpo_graph_collect_erases V E B (EV : encoding V) (g : Graph.t V E)
    (cb : audit_rpo_graph_callbacks V E B) (r : dfs_result V E) vertices :
  audit_rpo_graph_callbacks_erase EV g cb ->
  fst (audit_rpo_graph_collect cb r vertices) =
    flat_map (fun y => map (Graph.target g)
      (filter (fun e => ancestor_b EV r (Graph.target g e) (Graph.source g e))
        (Graph.out g y))) vertices.
Proof.
  intro Hcallbacks; destruct Hcallbacks as [Henc [Hout [Hsource Htarget]]].
  assert (Hcallbacks : audit_rpo_graph_callbacks_erase EV g cb)
    by (repeat split; assumption).
  induction vertices as [|v rest IH].
  - reflexivity.
  - cbn [audit_rpo_graph_collect flat_map].
    specialize (Hout v) as Hcall.
    destruct (audit_rpo_graph_out cb v) as [outgoing body]; cbn in Hcall; subst outgoing.
    pose proof (audit_rpo_graph_filter_erases V E B EV g cb r (Graph.out g v) Hcallbacks)
      as Hfilter.
    destruct (audit_rpo_graph_filter cb r (Graph.out g v)) as [retreats checks]; cbn in Hfilter.
    pose proof (audit_rpo_graph_targets_erases V E B g cb retreats Htarget) as Htargets.
    destruct (audit_rpo_graph_targets cb retreats) as [targets target_events]; cbn in Htargets.
    destruct (audit_rpo_graph_collect cb r rest) as [later events]; cbn in IH |- *.
    now rewrite Htargets, Hfilter, IH.
Qed.

Lemma audit_rpo_graph_add_all_erases V E B (EV : encoding V)
    (enc : V -> positive * list B) vertices heads :
  (forall x, fst (enc x) = encode EV x) ->
  fst (@audit_rpo_graph_add_all V E B enc vertices heads) =
    fold_left (fun set x => FinSet.add EV x set) vertices heads.
Proof.
  intro Henc; revert heads; induction vertices as [|v rest IH]; intro heads.
  - reflexivity.
  - cbn [audit_rpo_graph_add_all fold_left].
    pose proof (audit_finset_add_erases V B enc EV v heads (Henc v)) as Hadd.
    destruct (audit_finset_add enc v heads) as [next events]; cbn in Hadd.
    specialize (IH next).
    destruct (audit_rpo_graph_add_all enc rest next) as [result later]; cbn in IH |- *.
    now rewrite IH, Hadd.
Qed.

(** Counted retreat detection returns the source scheduler's set of heads. *)
Theorem audit_rpo_schedule_retreats_erases : audit_rpo_schedule_retreats_statement.
Proof.
  intros V E B EV g r cb Hcallbacks.
  pose proof (audit_rpo_graph_collect_erases V E B EV g cb r (Graph.nodes g) Hcallbacks)
    as Hcollect.
  unfold audit_rpo_schedule_retreats, schedule_retreats, FinSet.of_list.
  destruct (audit_rpo_graph_collect cb r (Graph.nodes g)) as [vertices events]; cbn in Hcollect.
  pose proof (audit_rpo_graph_add_all_erases V E B EV (audit_rpo_graph_encode cb)
    vertices FinSet.empty (proj1 Hcallbacks)) as Hadd.
  destruct (audit_rpo_graph_add_all (audit_rpo_graph_encode cb) vertices FinSet.empty)
    as [result adds]; cbn in Hadd |- *.
  now rewrite Hadd, Hcollect.
Qed.

(** Counted priority and widening queries return the original observations. *)
Theorem audit_rpo_schedule_callbacks_erases : audit_rpo_schedule_callbacks_statement.
Proof.
  intros V B EV enc positions heads v Henc.
  pose proof (audit_map_get_erases V positive B enc EV v positions (Henc v)) as Hget.
  pose proof (audit_finset_mem_erases V B enc EV v heads (Henc v)) as Hmem.
  unfold audit_rpo_schedule_priority, schedule_priority, audit_rpo_schedule_widening.
  destruct (audit_map_get enc v positions) as [found reads]; cbn in Hget |- *.
  destruct (audit_finset_mem enc v heads) as [member events]; cbn in Hmem |- *.
  rewrite Hget, Hmem; split; reflexivity.
Qed.

(** Both counted queries include their actual encoding and trie traversal costs. *)
Theorem audit_rpo_schedule_query_bound_correct : audit_rpo_schedule_query_bound_statement.
Proof.
  intros V B EV enc weight positions heads v Henc.
  pose proof (audit_rpo_schedule_callbacks_erases V B EV enc positions heads v Henc) as Herase.
  pose proof (audit_map_get_source_work_bound V positive B enc
    (fun es => fold_right (fun item n => weight item + n) 0 es) v positions) as Hmap.
  pose proof (audit_trie_get_source_work_bound (V * unit)%type (fst (enc v)) heads) as Hset.
  pose proof (audit_trie_get_trace_adequate (V * unit)%type (fst (enc v)) heads) as Htrace.
  unfold audit_rpo_schedule_priority, audit_rpo_schedule_widening in *.
  unfold audit_finset_mem in *.
  destruct (enc v) as [code body] eqn:Hcall; cbn in Hset, Htrace, Henc.
  specialize (Henc v); rewrite Hcall in Henc; cbn in Henc; subst code.
  unfold audit_map_code_get in *.
  destruct (audit_trie_get (encode EV v) heads) as [found set_events] eqn:Hget.
  cbn in Htrace.
  destruct (audit_map_get enc v positions) as [priority map_events] eqn:Hmap_call.
  cbn [fst snd] in Herase, Hmap, Hset |- *.
  destruct Herase as [Hpriority Hwiden].
  split; [exact Hpriority |].
  split; [exact Hwiden |].
  unfold audit_map_get in Hmap_call.
  rewrite Hcall in Hmap_call.
  unfold audit_map_code_get in Hmap_call.
  destruct (audit_trie_get (encode EV v) positions) as [raw map_trace] eqn:Hraw.
  inversion Hmap_call; subst priority map_events; clear Hmap_call.
  unfold audit_rpo_schedule_work, audit_rpo_schedule_body_work in *.
  unfold audit_rpo_schedule_event_work; destruct raw, found;
    cbn [map fold_right audit_rpo_schedule_event_work audit_rpo_schedule_event_body
      audit_map_source_work audit_finset_source_work option_map] in *; lia.
Qed.

(** * Position traversal work *)

Lemma audit_rpo_schedule_work_app V B (weight : B -> nat)
    (left right : list (audit_rpo_schedule_event V B)) :
  audit_rpo_schedule_work weight (left ++ right) =
    audit_rpo_schedule_work weight left + audit_rpo_schedule_work weight right.
Proof.
  induction left as [|event rest IH].
  - reflexivity.
  - change (audit_rpo_schedule_event_work weight event +
      audit_rpo_schedule_work weight (rest ++ right) =
      (audit_rpo_schedule_event_work weight event + audit_rpo_schedule_work weight rest) +
      audit_rpo_schedule_work weight right).
    rewrite IH; lia.
Qed.

Lemma audit_rpo_schedule_body_app V B (weight : B -> nat)
    (left right : list (audit_rpo_schedule_event V B)) :
  audit_rpo_schedule_body_work weight (left ++ right) =
    audit_rpo_schedule_body_work weight left + audit_rpo_schedule_body_work weight right.
Proof.
  induction left as [|event rest IH].
  - reflexivity.
  - change (audit_rpo_schedule_event_body weight event +
      audit_rpo_schedule_body_work weight (rest ++ right) =
      (audit_rpo_schedule_event_body weight event + audit_rpo_schedule_body_work weight rest) +
      audit_rpo_schedule_body_work weight right).
    rewrite IH; lia.
Qed.

Lemma audit_rpo_succ_width p : Pos.size_nat (Pos.succ p) <= S (Pos.size_nat p).
Proof.
  induction p as [p IH | p IH |]; cbn [Pos.succ Pos.size_nat] in *; lia.
Qed.

Lemma audit_rpo_positions_work V B (EV : encoding V) (enc : V -> positive * list B)
    (weight : B -> nat) vertices width :
  (forall v, fst (enc v) = encode EV v) ->
  Forall (fun v => Pos.size_nat (encode EV v) <= width) vertices ->
  forall next,
    audit_rpo_schedule_work weight (snd (audit_rpo_schedule_positions enc vertices next)) <=
      256 * S (length vertices) * (128 + 32 * width + Pos.size_nat next + length vertices) +
      audit_rpo_schedule_body_work weight (snd (audit_rpo_schedule_positions enc vertices next)).
Proof.
  intros Hencode Hwidth; induction Hwidth as [|v rest Hv Hrest IH]; intro next.
  - change (64 <= 256 * 1 * (128 + 32 * width + Pos.size_nat next + 0) + 0); lia.
  - pose proof (audit_positive_succ_erases next) as Hsucc.
    pose proof (audit_positive_succ_count next) as Hcount.
    pose proof (audit_rpo_succ_width next) as Hnext.
    specialize (IH (Pos.succ next)).
    cbn [audit_rpo_schedule_positions].
    destruct (audit_positive_succ next) as [next' successor_events]; cbn [fst snd] in Hsucc, Hcount.
    subst next'.
    destruct (audit_rpo_schedule_positions enc rest (Pos.succ next)) as [middle events].
    cbn [snd] in IH.
    pose proof (audit_map_set_source_work_bound V positive B enc
      (fun es => fold_right (fun item n => weight item + n) 0 es) v next middle) as Hmap.
    unfold audit_map_set in *.
    specialize (Hencode v) as Hcode.
    destruct (enc v) as [code body]; cbn [fst snd] in Hcode, Hmap; subst code.
    destruct (audit_trie_set (encode EV v) (v, next) middle) as [output trace].
    cbn [snd audit_map_source_work] in Hmap.
    cbn [snd map app].
    change (64 + (64 + 2 * length successor_events +
      audit_rpo_schedule_work weight (events ++
        [RpoScheduleMap (AuditMapSet v next (encode EV v) middle output body trace)])) <=
      256 * S (length (v :: rest)) *
        (128 + 32 * width + Pos.size_nat next + length (v :: rest)) +
      audit_rpo_schedule_body_work weight (events ++
        [RpoScheduleMap (AuditMapSet v next (encode EV v) middle output body trace)])).
    rewrite audit_rpo_schedule_work_app, audit_rpo_schedule_body_app.
    cbn [length].
    unfold audit_rpo_schedule_work, audit_rpo_schedule_body_work in *.
    cbn [fold_right audit_rpo_schedule_event_work audit_rpo_schedule_event_body
      audit_map_source_work] in *.
    unfold audit_rpo_schedule_event_work in *; cbn [audit_map_source_work] in *; nia.
Qed.

Lemma audit_rpo_max_member n values :
  In n values -> n <= fold_right Nat.max 0 values.
Proof.
  induction values as [|value rest IH]; intro Hin.
  - contradiction.
  - cbn [fold_right] in *; destruct Hin as [Heq | Hin].
    + subst value; apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact Hin | apply Nat.le_max_r].
Qed.

(** Position construction returns the original map within its input-derived work budget. *)
Theorem audit_rpo_positions_bound_correct : audit_rpo_positions_bound_statement.
Proof.
  intros V B EV enc weight vertices next Hencode.
  set (width := fold_right Nat.max 0 (map (fun v => Pos.size_nat (encode EV v)) vertices)).
  assert (Hwidth : Forall (fun v => Pos.size_nat (encode EV v) <= width) vertices).
  { apply Forall_forall; intros v Hin; unfold width; apply audit_rpo_max_member.
    apply in_map_iff; exists v; split; [reflexivity | exact Hin]. }
  pose proof (audit_rpo_positions_work V B EV enc weight vertices width Hencode Hwidth next)
    as Hwork.
  pose proof (audit_rpo_schedule_positions_erases V B EV enc vertices next Hencode) as Hresult.
  unfold audit_rpo_positions_budget; fold width.
  destruct (audit_rpo_schedule_positions enc vertices next) as [result events].
  cbn [fst snd] in Hwork, Hresult |- *; split; assumption.
Qed.

Lemma audit_rpo_schedule_budget_app V B (budget : V -> nat)
    (left right : list (audit_rpo_schedule_event V B)) :
  fold_right (fun event n => audit_rpo_schedule_event_budget budget event + n) 0 (left ++ right) =
  fold_right (fun event n => audit_rpo_schedule_event_budget budget event + n) 0 left +
  fold_right (fun event n => audit_rpo_schedule_event_budget budget event + n) 0 right.
Proof.
  induction left as [|event rest IH].
  - reflexivity.
  - cbn [app fold_right]; rewrite IH; lia.
Qed.

Lemma audit_rpo_positions_body_adapted V B (enc : V -> positive * list B)
    (weight : B -> nat) source budget vertices :
  audit_graph_external_callback_adapter enc weight source budget ->
  forall next,
    audit_rpo_schedule_body_work weight (snd (audit_rpo_schedule_positions enc vertices next)) <=
    fold_right (fun event n => audit_rpo_schedule_event_budget budget event + n) 0
      (snd (audit_rpo_schedule_positions enc vertices next)).
Proof.
  intro Hadapter; induction vertices as [|v rest IH]; intro next.
  - reflexivity.
  - cbn [audit_rpo_schedule_positions].
    destruct (audit_positive_succ next) as [next' successor_events].
    specialize (IH next').
    destruct (audit_rpo_schedule_positions enc rest next') as [middle events].
    cbn [snd] in IH.
    unfold audit_map_set.
    destruct (enc v) as [code body] eqn:Hcall.
    pose proof (audit_graph_external_callback_source _ _ _ _ Hadapter v code body Hcall) as [_
      Hbody].
    destruct (audit_trie_set code (v, next) middle) as [output trace].
    cbn [snd map app].
    change (audit_rpo_schedule_body_work weight
      (events ++ [RpoScheduleMap (AuditMapSet v next code middle output body trace)]) <=
      fold_right (fun event n => audit_rpo_schedule_event_budget budget event + n) 0
        (events ++ [RpoScheduleMap (AuditMapSet v next code middle output body trace)])).
    rewrite audit_rpo_schedule_body_app, audit_rpo_schedule_budget_app.
    unfold audit_rpo_schedule_body_work at 2.
    cbn [fold_right audit_rpo_schedule_event_body audit_rpo_schedule_event_budget].
    lia.
Qed.

(** The position bound charges the actual encoder bodies to their individual budgets. *)
Theorem audit_rpo_positions_adapted_correct : audit_rpo_positions_adapted_statement.
Proof.
  intros V B EV enc weight source budget vertices next Hencode Hadapter.
  pose proof (audit_rpo_positions_bound_correct V B EV enc weight vertices next Hencode) as Hbound.
  pose proof (audit_rpo_positions_body_adapted V B enc weight source budget vertices Hadapter next)
    as Hbody.
  destruct (audit_rpo_schedule_positions enc vertices next) as [result events].
  cbn [fst snd] in Hbound, Hbody |- *; destruct Hbound as [Hresult Hwork].
  split; [exact Hresult | lia].
Qed.

(** * Retreat traversal work *)

Lemma audit_rpo_graph_work_app V E B (weight : B -> nat)
    (left right : list (audit_rpo_graph_event V E B)) :
  audit_rpo_graph_work weight (left ++ right) =
    audit_rpo_graph_work weight left + audit_rpo_graph_work weight right /\
  audit_rpo_graph_body_work weight (left ++ right) =
    audit_rpo_graph_body_work weight left + audit_rpo_graph_body_work weight right.
Proof.
  induction left as [|event rest [IHwork IHbody]].
  - split; reflexivity.
  - unfold audit_rpo_graph_work, audit_rpo_graph_body_work in *.
    cbn [app fold_right] in *; rewrite IHwork, IHbody; split; lia.
Qed.

Lemma audit_rpo_graph_work_concat V E B (weight : B -> nat)
    (left right : list (audit_rpo_graph_event V E B)) :
  audit_rpo_graph_work weight (left ++ right) =
    audit_rpo_graph_work weight left + audit_rpo_graph_work weight right.
Proof.
  exact (proj1 (audit_rpo_graph_work_app V E B weight left right)).
Qed.

Lemma audit_rpo_graph_body_concat V E B (weight : B -> nat)
    (left right : list (audit_rpo_graph_event V E B)) :
  audit_rpo_graph_body_work weight (left ++ right) =
    audit_rpo_graph_body_work weight left + audit_rpo_graph_body_work weight right.
Proof.
  exact (proj2 (audit_rpo_graph_work_app V E B weight left right)).
Qed.

Lemma audit_rpo_graph_get_work V E B (enc : V -> positive * list B) (weight : B -> nat)
    key (input : Map.t V positive) :
  let events := map (@RpoGraphRank V E B) (snd (audit_map_get enc key input)) in
  audit_rpo_graph_work weight events <= 69 + 5 * Pos.size_nat (fst (enc key)) +
    audit_rpo_graph_body_work weight events.
Proof.
  pose proof (audit_map_get_source_work_bound V positive B enc
    (fun body => fold_right (fun item n => weight item + n) 0 body) key input) as Hbound.
  unfold audit_map_get in *.
  destruct (enc key) as [code body].
  destruct (audit_map_code_get code input) as [found trie_events].
  cbn [fst snd map fold_right audit_map_source_work audit_rpo_graph_work
    audit_rpo_graph_body_work audit_rpo_graph_event_body] in *.
  unfold audit_rpo_graph_event_work; cbn [audit_map_source_work].
  lia.
Qed.

Lemma audit_rpo_graph_add_work V E B (enc : V -> positive * list B) (weight : B -> nat)
    key (input : FinSet.t V) :
  let events := map (@RpoGraphSet V E B) (snd (audit_finset_add enc key input)) in
  audit_rpo_graph_work weight events <= 66 + 16 * Pos.size_nat (fst (enc key)) +
    audit_rpo_graph_body_work weight events.
Proof.
  pose proof (audit_trie_update_source_work_bound (V * unit)%type (fst (enc key))
    (Some (key, tt)) input) as Hbound.
  pose proof (audit_trie_update_trace_adequate (V * unit)%type (fst (enc key))
    (Some (key, tt)) input) as Htrace.
  unfold audit_finset_add, audit_trie_set in *.
  destruct (enc key) as [code body]; cbn [fst] in Hbound, Htrace.
  destruct (audit_trie_update code (Some (key, tt)) input) as [output trie_events].
  cbn [fst snd] in Htrace |- *.
  unfold audit_rpo_graph_work, audit_rpo_graph_body_work, audit_rpo_graph_event_work.
  cbn [map fold_right audit_rpo_graph_event_body audit_finset_source_work].
  lia.
Qed.

Lemma audit_rpo_ancestor_work V E B (EV : encoding V) (enc : V -> positive * list B)
    (weight : B -> nat) (r : dfs_result V E) u v width :
  (forall x, fst (enc x) = encode EV x) ->
  Pos.size_nat (encode EV u) <= width -> Pos.size_nat (encode EV v) <= width ->
  (forall x n, Map.get EV x (pre_num r) = Some n -> Pos.size_nat n <= width) ->
  (forall x n, Map.get EV x (post_num r) = Some n -> Pos.size_nat n <= width) ->
  audit_rpo_graph_work weight (snd (audit_rpo_graph_ancestor enc r u v)) <=
    1024 + 128 * width + audit_rpo_graph_body_work weight (snd (audit_rpo_graph_ancestor enc r u
      v)).
Proof.
  intros Henc Hu Hv Hpre Hpost.
  pose proof (audit_rpo_graph_get_work V E B enc weight u (pre_num r)) as Hfirst.
  pose proof (audit_map_get_erases V positive B enc EV u (pre_num r) (Henc u)) as Herase_first.
  unfold audit_rpo_graph_ancestor.
  destruct (audit_map_get enc u (pre_num r)) as [[a|] ea] eqn:Hfirst_call;
    cbn [fst snd] in Hfirst, Herase_first |- *; rewrite Henc in Hfirst.
  - pose proof (Hpre u a (eq_sym Herase_first)) as Ha.
    pose proof (audit_rpo_graph_get_work V E B enc weight v (pre_num r)) as Hsecond.
    destruct (audit_map_get enc v (pre_num r)) as [[b|] eb] eqn:Hsecond_call;
      cbn [fst snd] in Hsecond |- *; rewrite Henc in Hsecond.
    + pose proof (audit_rpo_graph_get_work V E B enc weight u (post_num r)) as Hthird.
      destruct (audit_map_get enc u (post_num r)) as [[c|] ec] eqn:Hthird_call;
        cbn [fst snd] in Hthird |- *; rewrite Henc in Hthird.
      * pose proof (audit_rpo_graph_get_work V E B enc weight v (post_num r)) as Hfourth.
        pose proof (audit_map_get_erases V positive B enc EV v (post_num r) (Henc v))
          as Herase_fourth.
        destruct (audit_map_get enc v (post_num r)) as [[d|] ed] eqn:Hfourth_call;
          cbn [fst snd] in Hfourth, Herase_fourth |- *; rewrite Henc in Hfourth.
        -- pose proof (Hpost v d (eq_sym Herase_fourth)) as Hd.
           pose proof (audit_positive_order a b) as [_ [_ [_ Hab]]].
           pose proof (audit_positive_order d c) as [_ [_ [_ Hdc]]].
           destruct (audit_positive_leb a b) as [first ef]; cbn [snd] in Hab |- *.
           destruct (audit_positive_leb d c) as [second es]; cbn [snd] in Hdc |- *.
           repeat rewrite map_app.
           repeat rewrite audit_rpo_graph_work_concat.
           repeat rewrite audit_rpo_graph_body_concat.
           unfold audit_rpo_graph_work at 5; unfold audit_rpo_graph_body_work at 5.
           cbn [fold_right audit_rpo_graph_event_work audit_rpo_graph_event_body].
           unfold audit_rpo_graph_event_work; cbn [audit_rpo_graph_event_body].
           pose proof (Nat.le_min_l (Pos.size_nat a) (Pos.size_nat b)).
           pose proof (Nat.le_min_l (Pos.size_nat d) (Pos.size_nat c)).
           lia.
        -- repeat rewrite map_app; repeat rewrite audit_rpo_graph_work_concat;
             repeat rewrite audit_rpo_graph_body_concat; lia.
      * repeat rewrite map_app; repeat rewrite audit_rpo_graph_work_concat;
          repeat rewrite audit_rpo_graph_body_concat; lia.
    + repeat rewrite map_app; repeat rewrite audit_rpo_graph_work_concat;
        repeat rewrite audit_rpo_graph_body_concat; lia.
  - lia.
Qed.

Lemma audit_rpo_filter_work V E B (EV : encoding V) (g : Graph.t V E)
    (cb : audit_rpo_graph_callbacks V E B) (weight : B -> nat) (r : dfs_result V E) edges width :
  audit_rpo_graph_callbacks_erase EV g cb ->
  Forall (fun e => Pos.size_nat (encode EV (Graph.target g e)) <= width /\
    Pos.size_nat (encode EV (Graph.source g e)) <= width) edges ->
  (forall x n, Map.get EV x (pre_num r) = Some n -> Pos.size_nat n <= width) ->
  (forall x n, Map.get EV x (post_num r) = Some n -> Pos.size_nat n <= width) ->
  audit_rpo_graph_work weight (snd (audit_rpo_graph_filter cb r edges)) <=
    64 + (2048 + 256 * width) * length edges +
    audit_rpo_graph_body_work weight (snd (audit_rpo_graph_filter cb r edges)).
Proof.
  intros Hcallbacks Hwidth Hpre Hpost.
  destruct Hcallbacks as [Henc [Hout [Hsource Htarget]]].
  induction Hwidth as [|edge rest [Htwidth Hswidth] Hrest IH].
  - change (64 <= 64 + (2048 + 256 * width) * 0 + 0); lia.
  - cbn [audit_rpo_graph_filter].
    specialize (Htarget edge) as Ht; specialize (Hsource edge) as Hs.
    destruct (audit_rpo_graph_target cb edge) as [target tb]; cbn [fst] in Ht; subst target.
    destruct (audit_rpo_graph_source cb edge) as [source sb]; cbn [fst] in Hs; subst source.
    pose proof (audit_rpo_ancestor_work V E B EV (audit_rpo_graph_encode cb) weight r
      (Graph.target g edge) (Graph.source g edge) width Henc Htwidth Hswidth Hpre Hpost)
      as Hancestor.
    destruct (audit_rpo_graph_ancestor (audit_rpo_graph_encode cb) r
      (Graph.target g edge) (Graph.source g edge)) as [keep checks]; cbn [snd] in Hancestor.
    destruct (audit_rpo_graph_filter cb r rest) as [later events]; cbn [snd] in IH |- *.
    change (64 + ((64 + fold_right (fun item n => weight item + n) 0 tb) +
      ((64 + fold_right (fun item n => weight item + n) 0 sb) +
        audit_rpo_graph_work weight (checks ++ events))) <=
      64 + (2048 + 256 * width) * length (edge :: rest) +
      (fold_right (fun item n => weight item + n) 0 tb +
        (fold_right (fun item n => weight item + n) 0 sb +
          audit_rpo_graph_body_work weight (checks ++ events)))).
    rewrite audit_rpo_graph_work_concat, audit_rpo_graph_body_concat; cbn [length]; nia.
Qed.

Lemma audit_rpo_targets_work V E B (cb : audit_rpo_graph_callbacks V E B)
    (weight : B -> nat) edges :
  audit_rpo_graph_work weight (snd (audit_rpo_graph_targets cb edges)) <=
    64 + 128 * length edges +
    audit_rpo_graph_body_work weight (snd (audit_rpo_graph_targets cb edges)).
Proof.
  induction edges as [|edge rest IH].
  - change (64 <= 64 + 128 * 0 + 0); lia.
  - cbn [audit_rpo_graph_targets].
    destruct (audit_rpo_graph_target cb edge) as [target body].
    destruct (audit_rpo_graph_targets cb rest) as [later events]; cbn [snd] in IH |- *.
    change (64 + ((64 + fold_right (fun item n => weight item + n) 0 body) +
      audit_rpo_graph_work weight events) <= 64 + 128 * length (edge :: rest) +
      (fold_right (fun item n => weight item + n) 0 body +
        audit_rpo_graph_body_work weight events)).
    cbn [length]; lia.
Qed.

Lemma audit_rpo_filter_length V E B (cb : audit_rpo_graph_callbacks V E B)
    (r : dfs_result V E) edges :
  length (fst (audit_rpo_graph_filter cb r edges)) <= length edges.
Proof.
  induction edges as [|edge rest IH].
  - reflexivity.
  - cbn [audit_rpo_graph_filter].
    destruct (audit_rpo_graph_target cb edge) as [target tb].
    destruct (audit_rpo_graph_source cb edge) as [source sb].
    destruct (audit_rpo_graph_ancestor (audit_rpo_graph_encode cb) r target source)
      as [keep checks].
    destruct (audit_rpo_graph_filter cb r rest) as [later events]; cbn [fst] in IH |- *.
    destruct keep; cbn [length]; lia.
Qed.

Lemma audit_rpo_collect_work V E B (EV : encoding V) (g : Graph.t V E)
    (cb : audit_rpo_graph_callbacks V E B) (weight : B -> nat) (r : dfs_result V E)
    vertices width :
  audit_rpo_graph_callbacks_erase EV g cb ->
  (forall x n, Map.get EV x (pre_num r) = Some n -> Pos.size_nat n <= width) ->
  (forall x n, Map.get EV x (post_num r) = Some n -> Pos.size_nat n <= width) ->
  Forall (fun e => Pos.size_nat (encode EV (Graph.target g e)) <= width /\
    Pos.size_nat (encode EV (Graph.source g e)) <= width) (flat_map (Graph.out g) vertices) ->
  audit_rpo_graph_work weight (snd (audit_rpo_graph_collect cb r vertices)) <=
    64 + 256 * length vertices + (4096 + 512 * width) *
      length (flat_map (Graph.out g) vertices) +
    audit_rpo_graph_body_work weight (snd (audit_rpo_graph_collect cb r vertices)).
Proof.
  intros Hcallbacks Hpre Hpost; induction vertices as [|v rest IH]; intro Hwidth.
  - change (64 <= 64 + 256 * 0 + (4096 + 512 * width) * 0 + 0); lia.
  - cbn [flat_map] in Hwidth; apply Forall_app in Hwidth; destruct Hwidth as [Houtwidth Hrest].
    specialize (IH Hrest).
    pose proof (proj1 (proj2 Hcallbacks) v) as Hout.
    cbn [audit_rpo_graph_collect].
    destruct (audit_rpo_graph_out cb v) as [outgoing body]; cbn [fst] in Hout; subst outgoing.
    pose proof (audit_rpo_filter_work V E B EV g cb weight r (Graph.out g v) width
      Hcallbacks Houtwidth Hpre Hpost) as Hfilter.
    pose proof (audit_rpo_filter_length V E B cb r (Graph.out g v)) as Hlength.
    destruct (audit_rpo_graph_filter cb r (Graph.out g v)) as [retreats checks];
      cbn [fst snd] in Hfilter, Hlength.
    pose proof (audit_rpo_targets_work V E B cb weight retreats) as Htargets.
    destruct (audit_rpo_graph_targets cb retreats) as [targets target_events]; cbn [snd] in
      Htargets.
    destruct (audit_rpo_graph_collect cb r rest) as [later events]; cbn [snd] in IH |- *.
    change (64 + ((64 + fold_right (fun item n => weight item + n) 0 body) +
      audit_rpo_graph_work weight (checks ++ target_events ++ events)) <=
      64 + 256 * length (v :: rest) + (4096 + 512 * width) *
        length (Graph.out g v ++ flat_map (Graph.out g) rest) +
      (fold_right (fun item n => weight item + n) 0 body +
        audit_rpo_graph_body_work weight (checks ++ target_events ++ events))).
    repeat rewrite audit_rpo_graph_work_concat; repeat rewrite audit_rpo_graph_body_concat.
    rewrite length_app; cbn [length]; nia.
Qed.

Lemma audit_rpo_add_all_work V E B (EV : encoding V) (enc : V -> positive * list B)
    (weight : B -> nat) vertices width :
  (forall v, fst (enc v) = encode EV v) ->
  Forall (fun v => Pos.size_nat (encode EV v) <= width) vertices ->
  forall heads,
    audit_rpo_graph_work weight (snd (@audit_rpo_graph_add_all V E B enc vertices heads)) <=
      64 + (256 + 32 * width) * length vertices +
      audit_rpo_graph_body_work weight (snd (@audit_rpo_graph_add_all V E B enc vertices heads)).
Proof.
  intros Henc Hwidth; induction Hwidth as [|v rest Hv Hrest IH]; intro heads.
  - change (64 <= 64 + (256 + 32 * width) * 0 + 0); lia.
  - cbn [audit_rpo_graph_add_all].
    pose proof (audit_rpo_graph_add_work V E B enc weight v heads) as Hadd.
    destruct (audit_finset_add enc v heads) as [next events]; cbn [fst snd] in Hadd.
    rewrite Henc in Hadd.
    specialize (IH next).
    destruct (audit_rpo_graph_add_all enc rest next) as [result later]; cbn [snd] in IH |- *.
    change (64 + audit_rpo_graph_work weight (map RpoGraphSet events ++ later) <=
      64 + (256 + 32 * width) * length (v :: rest) +
      audit_rpo_graph_body_work weight (map RpoGraphSet events ++ later)).
    rewrite audit_rpo_graph_work_concat, audit_rpo_graph_body_concat; cbn [length]; nia.
Qed.

Lemma audit_rpo_collected_length V E (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) vertices :
  length (flat_map (fun y => map (Graph.target g)
    (filter (fun e => ancestor_b EV r (Graph.target g e) (Graph.source g e))
      (Graph.out g y))) vertices) <= length (flat_map (Graph.out g) vertices).
Proof.
  induction vertices as [|v rest IH].
  - reflexivity.
  - cbn [flat_map]; repeat rewrite length_app; rewrite length_map.
    pose proof (filter_length_le (fun e => ancestor_b EV r (Graph.target g e) (Graph.source g e))
      (Graph.out g v)); lia.
Qed.

Lemma audit_rpo_collected_width V E (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) vertices width :
  Forall (fun e => Pos.size_nat (encode EV (Graph.target g e)) <= width)
    (flat_map (Graph.out g) vertices) ->
  Forall (fun v => Pos.size_nat (encode EV v) <= width)
    (flat_map (fun y => map (Graph.target g)
      (filter (fun e => ancestor_b EV r (Graph.target g e) (Graph.source g e))
        (Graph.out g y))) vertices).
Proof.
  intros Hwidth; apply Forall_forall; intros x Hin.
  apply in_flat_map in Hin; destruct Hin as [v [Hv Hin]].
  apply in_map_iff in Hin; destruct Hin as [edge [Heq Hedge]]; subst x.
  apply filter_In in Hedge; destruct Hedge as [Hedge _].
  apply Forall_forall with (x := edge) in Hwidth; [exact Hwidth |].
  apply in_flat_map; exists v; split; assumption.
Qed.

(** Retreat traversal returns the original heads within its graph-derived budget. *)
Theorem audit_rpo_retreats_bound_correct : audit_rpo_retreats_bound_statement.
Proof.
  intros V E B EV g r cb weight Hcallbacks.
  set (edges := flat_map (Graph.out g) (Graph.nodes g)).
  set (keys := Graph.nodes g ++ map (Graph.source g) edges ++ map (Graph.target g) edges ++
    map fst (Map.elements (pre_num r)) ++ map fst (Map.elements (post_num r))).
  set (numbers := map snd (Map.elements (pre_num r)) ++ map snd (Map.elements (post_num r))).
  set (width := Nat.max (fold_right Nat.max 0 (map (fun v => Pos.size_nat (encode EV v)) keys))
    (fold_right Nat.max 0 (map Pos.size_nat numbers))).
  assert (Hkey : forall v, In v keys -> Pos.size_nat (encode EV v) <= width).
  { intros v Hin; unfold width; eapply Nat.le_trans; [|apply Nat.le_max_l].
    apply audit_rpo_max_member, in_map_iff; exists v; split; [reflexivity | exact Hin]. }
  assert (Hnumber : forall n, In n numbers -> Pos.size_nat n <= width).
  { intros n Hin; unfold width; eapply Nat.le_trans; [|apply Nat.le_max_r].
    apply audit_rpo_max_member, in_map_iff; exists n; split; [reflexivity | exact Hin]. }
  assert (Hpre : forall x n, Map.get EV x (pre_num r) = Some n -> Pos.size_nat n <= width).
  { intros x n Hget; destruct (audit_dfs_get_row EV (pre_num r) x n Hget) as [key Hin].
    apply Hnumber; unfold numbers; apply in_or_app; left.
    apply in_map_iff; exists (key, n); split; [reflexivity | exact Hin]. }
  assert (Hpost : forall x n, Map.get EV x (post_num r) = Some n -> Pos.size_nat n <= width).
  { intros x n Hget; destruct (audit_dfs_get_row EV (post_num r) x n Hget) as [key Hin].
    apply Hnumber; unfold numbers; apply in_or_app; right.
    apply in_map_iff; exists (key, n); split; [reflexivity | exact Hin]. }
  assert (Hedges : Forall (fun e => Pos.size_nat (encode EV (Graph.target g e)) <= width /\
    Pos.size_nat (encode EV (Graph.source g e)) <= width) edges).
  { apply Forall_forall; intros edge Hin; split; apply Hkey; unfold keys.
    - apply in_or_app; right; apply in_or_app; right; apply in_or_app; left.
      apply in_map_iff; exists edge; split; [reflexivity | exact Hin].
    - apply in_or_app; right; apply in_or_app; left.
      apply in_map_iff; exists edge; split; [reflexivity | exact Hin]. }
  assert (Htargets : Forall (fun e => Pos.size_nat (encode EV (Graph.target g e)) <= width) edges).
  { eapply Forall_impl; [|exact Hedges]; intros edge [Ht _]; exact Ht. }
  pose proof (audit_rpo_collect_work V E B EV g cb weight r (Graph.nodes g) width
    Hcallbacks Hpre Hpost Hedges) as Hcollect_work.
  pose proof (audit_rpo_graph_collect_erases V E B EV g cb r (Graph.nodes g) Hcallbacks)
    as Hcollect_result.
  pose proof (audit_rpo_collected_length V E EV g r (Graph.nodes g)) as Hlength.
  pose proof (audit_rpo_collected_width V E EV g r (Graph.nodes g) width Htargets) as Hwidth.
  unfold audit_rpo_schedule_retreats.
  destruct (audit_rpo_graph_collect cb r (Graph.nodes g)) as [vertices events]
    eqn:Hcollect_call; cbn [fst snd] in Hcollect_result, Hcollect_work.
  rewrite <- Hcollect_result in Hlength, Hwidth.
  pose proof (audit_rpo_add_all_work V E B EV (audit_rpo_graph_encode cb) weight vertices width
    (proj1 Hcallbacks) Hwidth FinSet.empty) as Hadd.
  destruct (audit_rpo_graph_add_all (audit_rpo_graph_encode cb) vertices FinSet.empty)
    as [result adds] eqn:Hadd_call; cbn [snd] in Hadd |- *.
  pose proof (audit_rpo_schedule_retreats_erases V E B EV g r cb Hcallbacks) as Hresult.
  unfold audit_rpo_schedule_retreats in Hresult; rewrite Hcollect_call, Hadd_call in Hresult.
  cbn [fst] in Hresult.
  split; [exact Hresult |].
  rewrite audit_rpo_graph_work_concat, audit_rpo_graph_body_concat.
  unfold audit_rpo_graph_budget; fold edges keys numbers width.
  fold edges in Hcollect_work, Hlength.
  nia.
Qed.

(** * Captured retreat callback receipts *)

Definition audit_rpo_graph_receipt {V E B} (cb : audit_rpo_graph_callbacks V E B)
    (event : audit_rpo_graph_event V E B) : Prop :=
  match event with
  | RpoGraphOut v result body => audit_rpo_graph_out cb v = (result, body)
  | RpoGraphSource e result body => audit_rpo_graph_source cb e = (result, body)
  | RpoGraphTarget e result body => audit_rpo_graph_target cb e = (result, body)
  | RpoGraphRank (AuditMapGet key code _ _ body _)
  | RpoGraphRank (AuditMapSet key _ code _ _ body _)
  | RpoGraphRank (AuditMapRemove key code _ _ body _)
  | RpoGraphSet (AuditSetMem key code _ _ body _)
  | RpoGraphSet (AuditSetAdd key code _ _ body _)
  | RpoGraphSet (AuditSetRemove key code _ _ body _) =>
    audit_rpo_graph_encode cb key = (code, body)
  | RpoGraphSet (AuditSetFold _ _)
  | RpoGraphCompare _ _ _ _
  | RpoGraphCase _ => True
  end.

Lemma audit_rpo_rank_receipts V E B (cb : audit_rpo_graph_callbacks V E B) key input :
  Forall (audit_rpo_graph_receipt cb)
    (map RpoGraphRank (snd (audit_map_get (audit_rpo_graph_encode cb) key input))).
Proof.
  unfold audit_map_get.
  destruct (audit_rpo_graph_encode cb key) as [code body] eqn:Hcall.
  destruct (audit_map_code_get code input) as [found trace].
  cbn [snd map]; constructor; [exact Hcall | constructor].
Qed.

Lemma audit_rpo_set_receipts V E B (cb : audit_rpo_graph_callbacks V E B) key input :
  Forall (audit_rpo_graph_receipt cb)
    (map RpoGraphSet (snd (audit_finset_add (audit_rpo_graph_encode cb) key input))).
Proof.
  unfold audit_finset_add.
  destruct (audit_rpo_graph_encode cb key) as [code body] eqn:Hcall.
  destruct (audit_trie_set code (key, tt) input) as [output trace].
  cbn [snd map]; constructor; [exact Hcall | constructor].
Qed.

Lemma audit_rpo_ancestor_receipts V E B (cb : audit_rpo_graph_callbacks V E B)
    (r : dfs_result V E) u v :
  Forall (audit_rpo_graph_receipt cb)
    (snd (audit_rpo_graph_ancestor (audit_rpo_graph_encode cb) r u v)).
Proof.
  pose proof (audit_rpo_rank_receipts V E B cb u (pre_num r)) as Hfirst.
  unfold audit_rpo_graph_ancestor.
  destruct (audit_map_get (audit_rpo_graph_encode cb) u (pre_num r)) as [[a|] ea];
    cbn [snd] in Hfirst |- *; [|exact Hfirst].
  pose proof (audit_rpo_rank_receipts V E B cb v (pre_num r)) as Hsecond.
  destruct (audit_map_get (audit_rpo_graph_encode cb) v (pre_num r)) as [[b|] eb];
    cbn [snd] in Hsecond |- *.
  2: { rewrite map_app; apply Forall_app; split; assumption. }
  pose proof (audit_rpo_rank_receipts V E B cb u (post_num r)) as Hthird.
  destruct (audit_map_get (audit_rpo_graph_encode cb) u (post_num r)) as [[c|] ec];
    cbn [snd] in Hthird |- *.
  2: { repeat rewrite map_app; repeat rewrite Forall_app; repeat split; assumption. }
  pose proof (audit_rpo_rank_receipts V E B cb v (post_num r)) as Hfourth.
  destruct (audit_map_get (audit_rpo_graph_encode cb) v (post_num r)) as [[d|] ed];
    cbn [snd] in Hfourth |- *.
  2: { repeat rewrite map_app; repeat rewrite Forall_app; repeat split; assumption. }
  destruct (audit_positive_leb a b) as [first ef].
  destruct (audit_positive_leb d c) as [second es].
  cbn [snd]; repeat rewrite map_app; repeat rewrite Forall_app.
  repeat split; try assumption; constructor; [exact I | constructor; [exact I | constructor]].
Qed.

Lemma audit_rpo_filter_receipts V E B (cb : audit_rpo_graph_callbacks V E B)
    (r : dfs_result V E) edges :
  Forall (audit_rpo_graph_receipt cb) (snd (audit_rpo_graph_filter cb r edges)).
Proof.
  induction edges as [|edge rest IH].
  - cbn [audit_rpo_graph_filter snd]; constructor; [exact I | constructor].
  - cbn [audit_rpo_graph_filter].
    destruct (audit_rpo_graph_target cb edge) as [target tb] eqn:Htarget.
    destruct (audit_rpo_graph_source cb edge) as [source sb] eqn:Hsource.
    pose proof (audit_rpo_ancestor_receipts V E B cb r target source) as Hancestor.
    destruct (audit_rpo_graph_ancestor (audit_rpo_graph_encode cb) r target source)
      as [keep checks]; cbn [snd] in Hancestor.
    destruct (audit_rpo_graph_filter cb r rest) as [later events]; cbn [snd] in IH |- *.
    constructor; [exact I |].
    constructor; [exact Htarget |].
    constructor; [exact Hsource |].
    apply Forall_app; split; assumption.
Qed.

Lemma audit_rpo_targets_receipts V E B (cb : audit_rpo_graph_callbacks V E B) edges :
  Forall (audit_rpo_graph_receipt cb) (snd (audit_rpo_graph_targets cb edges)).
Proof.
  induction edges as [|edge rest IH].
  - cbn [audit_rpo_graph_targets snd]; constructor; [exact I | constructor].
  - cbn [audit_rpo_graph_targets].
    destruct (audit_rpo_graph_target cb edge) as [target body] eqn:Htarget.
    destruct (audit_rpo_graph_targets cb rest) as [later events]; cbn [snd] in IH |- *.
    constructor; [exact I |].
    constructor; [exact Htarget | exact IH].
Qed.

Lemma audit_rpo_collect_receipts V E B (cb : audit_rpo_graph_callbacks V E B)
    (r : dfs_result V E) vertices :
  Forall (audit_rpo_graph_receipt cb) (snd (audit_rpo_graph_collect cb r vertices)).
Proof.
  induction vertices as [|v rest IH].
  - cbn [audit_rpo_graph_collect snd]; constructor; [exact I | constructor].
  - cbn [audit_rpo_graph_collect].
    destruct (audit_rpo_graph_out cb v) as [outgoing body] eqn:Hout.
    pose proof (audit_rpo_filter_receipts V E B cb r outgoing) as Hfilter.
    destruct (audit_rpo_graph_filter cb r outgoing) as [retreats checks]; cbn [snd] in Hfilter.
    pose proof (audit_rpo_targets_receipts V E B cb retreats) as Htargets.
    destruct (audit_rpo_graph_targets cb retreats) as [targets target_events]; cbn [snd] in
      Htargets.
    destruct (audit_rpo_graph_collect cb r rest) as [later events]; cbn [snd] in IH |- *.
    constructor; [exact I |].
    constructor; [exact Hout |].
    repeat rewrite Forall_app; repeat split; assumption.
Qed.

Lemma audit_rpo_add_receipts V E B (cb : audit_rpo_graph_callbacks V E B) vertices :
  forall heads, Forall (audit_rpo_graph_receipt cb)
    (snd (audit_rpo_graph_add_all (audit_rpo_graph_encode cb) vertices heads)).
Proof.
  induction vertices as [|v rest IH]; intro heads.
  - cbn [audit_rpo_graph_add_all snd]; constructor; [exact I | constructor].
  - cbn [audit_rpo_graph_add_all].
    pose proof (audit_rpo_set_receipts V E B cb v heads) as Hadd.
    destruct (audit_finset_add (audit_rpo_graph_encode cb) v heads) as [next events];
      cbn [snd] in Hadd.
    specialize (IH next).
    destruct (audit_rpo_graph_add_all (audit_rpo_graph_encode cb) rest next)
      as [result later]; cbn [snd] in IH |- *.
    constructor; [exact I |].
    apply Forall_app; split; assumption.
Qed.

Lemma audit_rpo_retreat_receipts V E B (cb : audit_rpo_graph_callbacks V E B)
    (g : Graph.t V E) (r : dfs_result V E) :
  Forall (audit_rpo_graph_receipt cb) (snd (audit_rpo_schedule_retreats cb g r)).
Proof.
  pose proof (audit_rpo_collect_receipts V E B cb r (Graph.nodes g)) as Hcollect.
  unfold audit_rpo_schedule_retreats.
  destruct (audit_rpo_graph_collect cb r (Graph.nodes g)) as [vertices events];
    cbn [snd] in Hcollect.
  pose proof (audit_rpo_add_receipts V E B cb vertices FinSet.empty) as Hadd.
  destruct (audit_rpo_graph_add_all (audit_rpo_graph_encode cb) vertices FinSet.empty)
    as [result adds]; cbn [snd] in Hadd |- *.
  apply Forall_app; split; assumption.
Qed.

Lemma audit_rpo_graph_receipt_budget V E B (cb : audit_rpo_graph_callbacks V E B)
    (weight : B -> nat) encode_source out_source source_source target_source
    encode_budget out_budget source_budget target_budget event :
  audit_graph_external_callback_adapter (audit_rpo_graph_encode cb) weight encode_source
    encode_budget ->
  audit_graph_external_callback_adapter (audit_rpo_graph_out cb) weight out_source out_budget ->
  audit_graph_external_callback_adapter (audit_rpo_graph_source cb) weight source_source
    source_budget ->
  audit_graph_external_callback_adapter (audit_rpo_graph_target cb) weight target_source
    target_budget ->
  audit_rpo_graph_receipt cb event ->
  audit_rpo_graph_event_body weight event <=
    audit_rpo_graph_event_budget encode_budget out_budget source_budget target_budget event.
Proof.
  intros Hencode Hout Hsource Htarget Hreceipt.
  destruct event as [site | v result body | e result body | e result body | item | item |
    left right result trace].
  - reflexivity.
  - exact (proj2 (audit_graph_external_callback_source _ _ _ _ Hout v result body Hreceipt)).
  - exact (proj2 (audit_graph_external_callback_source _ _ _ _ Hsource e result body Hreceipt)).
  - exact (proj2 (audit_graph_external_callback_source _ _ _ _ Htarget e result body Hreceipt)).
  - destruct item; cbn [audit_rpo_graph_receipt audit_rpo_graph_event_body
      audit_rpo_graph_event_budget] in *;
      exact (proj2 (audit_graph_external_callback_source _ _ _ _ Hencode _ _ _ Hreceipt)).
  - destruct item; cbn [audit_rpo_graph_receipt audit_rpo_graph_event_body
      audit_rpo_graph_event_budget] in *; try reflexivity;
      exact (proj2 (audit_graph_external_callback_source _ _ _ _ Hencode _ _ _ Hreceipt)).
  - reflexivity.
Qed.

Lemma audit_rpo_graph_receipts_budget V E B (cb : audit_rpo_graph_callbacks V E B)
    (weight : B -> nat) encode_source out_source source_source target_source
    encode_budget out_budget source_budget target_budget events :
  audit_graph_external_callback_adapter (audit_rpo_graph_encode cb) weight encode_source
    encode_budget ->
  audit_graph_external_callback_adapter (audit_rpo_graph_out cb) weight out_source out_budget ->
  audit_graph_external_callback_adapter (audit_rpo_graph_source cb) weight source_source
    source_budget ->
  audit_graph_external_callback_adapter (audit_rpo_graph_target cb) weight target_source
    target_budget ->
  Forall (audit_rpo_graph_receipt cb) events ->
  audit_rpo_graph_body_work weight events <=
    fold_right (fun event n => audit_rpo_graph_event_budget encode_budget out_budget source_budget
      target_budget event + n) 0 events.
Proof.
  intros Hencode Hout Hsource Htarget Hreceipts; induction Hreceipts as [|event rest Hreceipt _ IH].
  - reflexivity.
  - pose proof (audit_rpo_graph_receipt_budget V E B cb weight encode_source out_source
      source_source target_source encode_budget out_budget source_budget target_budget event
      Hencode Hout Hsource Htarget Hreceipt) as Hbody.
    change (audit_rpo_graph_event_body weight event + audit_rpo_graph_body_work weight rest <=
      audit_rpo_graph_event_budget encode_budget out_budget source_budget target_budget event +
      fold_right (fun event n => audit_rpo_graph_event_budget encode_budget out_budget source_budget
        target_budget event + n) 0 rest).
    lia.
Qed.

(** The retreat bound charges each actual graph callback body to its input budget. *)
Theorem audit_rpo_retreats_adapted_correct : audit_rpo_retreats_adapted_statement.
Proof.
  intros V E B EV g r cb weight encode_source out_source source_source target_source
    encode_budget out_budget source_budget target_budget Hcallbacks Hencode Hout Hsource Htarget.
  pose proof (audit_rpo_retreats_bound_correct V E B EV g r cb weight Hcallbacks) as Hbound.
  pose proof (audit_rpo_retreat_receipts V E B cb g r) as Hreceipts.
  pose proof (audit_rpo_graph_receipts_budget V E B cb weight encode_source out_source
    source_source target_source encode_budget out_budget source_budget target_budget
    (snd (audit_rpo_schedule_retreats cb g r)) Hencode Hout Hsource Htarget Hreceipts) as Hbody.
  destruct (audit_rpo_schedule_retreats cb g r) as [result events]; cbn [fst snd] in *.
  destruct Hbound as [Hresult Hwork]; split; [exact Hresult | lia].
Qed.

(** * Receipt counts *)

Lemma audit_rpo_positions_count V B (enc : V -> positive * list B) vertices :
  forall next, length (snd (audit_rpo_schedule_positions enc vertices next)) =
    1 + 3 * length vertices.
Proof.
  induction vertices as [|v rest IH]; intro next.
  - reflexivity.
  - cbn [audit_rpo_schedule_positions].
    destruct (audit_positive_succ next) as [next' successor_events].
    specialize (IH next').
    destruct (audit_rpo_schedule_positions enc rest next') as [middle events]; cbn [snd] in IH.
    unfold audit_map_set.
    destruct (enc v) as [code body].
    destruct (audit_trie_set code (v, next) middle) as [output trace].
    cbn [snd map app length]; rewrite length_app; cbn [length]; lia.
Qed.

Lemma audit_rpo_zero_body B (body : list B) :
  fold_right (fun _ n => 0 + n) 0 body = 0.
Proof.
  induction body as [|item rest IH]; [reflexivity | exact IH].
Qed.

Lemma audit_rpo_graph_zero_body V E B (events : list (audit_rpo_graph_event V E B)) :
  audit_rpo_graph_body_work (fun _ => 0) events = 0.
Proof.
  induction events as [|event rest IH].
  - reflexivity.
  - change (audit_rpo_graph_event_body (fun _ => 0) event +
      audit_rpo_graph_body_work (fun _ => 0) rest = 0).
    rewrite IH; destruct event as [site | v output body | e output body | e output body |
      item | item | left right result trace]; cbn [audit_rpo_graph_event_body];
      try (rewrite audit_rpo_zero_body; reflexivity); try reflexivity;
      destruct item; cbn [audit_rpo_graph_event_body];
      try (rewrite audit_rpo_zero_body; reflexivity); reflexivity.
Qed.

Lemma audit_rpo_graph_length_work V E B (weight : B -> nat)
    (events : list (audit_rpo_graph_event V E B)) :
  length events <= audit_rpo_graph_work weight events.
Proof.
  induction events as [|event rest IH].
  - reflexivity.
  - change (S (length rest) <= audit_rpo_graph_event_work weight event +
      audit_rpo_graph_work weight rest).
    unfold audit_rpo_graph_event_work; lia.
Qed.
